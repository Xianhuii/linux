// SPDX-License-Identifier: GPL-2.0
/*
 * This file contains the procedures for the handling of select and poll
 *
 * Created for Linux based loosely upon Mathius Lattner's minix
 * patches by Peter MacDonald. Heavily edited by Linus.
 *
 *  4 February 1994
 *     COFF/ELF binary emulation. If the process has the STICKY_TIMEOUTS
 *     flag set in its personality we do *not* modify the given timeout
 *     parameter to reflect time remaining.
 *
 *  24 January 2000
 *     Changed sys_poll()/do_poll() to use PAGE_SIZE chunk-based allocation 
 *     of fds to overcome nfds < 16390 descriptors limit (Tigran Aivazian).
 */

#include <linux/compat.h>
#include <linux/kernel.h>
#include <linux/sched/signal.h>
#include <linux/sched/rt.h>
#include <linux/syscalls.h>
#include <linux/export.h>
#include <linux/slab.h>
#include <linux/poll.h>
#include <linux/personality.h> /* for STICKY_TIMEOUTS */
#include <linux/file.h>
#include <linux/fdtable.h>
#include <linux/fs.h>
#include <linux/rcupdate.h>
#include <linux/hrtimer.h>
#include <linux/freezer.h>
#include <net/busy_poll.h>
#include <linux/vmalloc.h>

#include <linux/uaccess.h>


/*
 * Estimate expected accuracy in ns from a timeval.
 *
 * After quite a bit of churning around, we've settled on
 * a simple thing of taking 0.1% of the timeout as the
 * slack, with a cap of 100 msec.
 * "nice" tasks get a 0.5% slack instead.
 *
 * Consider this comment an open invitation to come up with even
 * better solutions..
 */

#define MAX_SLACK	(100 * NSEC_PER_MSEC)

static long __estimate_accuracy(struct timespec64 *tv)
{
	long slack;
	int divfactor = 1000;

	if (tv->tv_sec < 0)
		return 0;

	if (task_nice(current) > 0)
		divfactor = divfactor / 5;

	if (tv->tv_sec > MAX_SLACK / (NSEC_PER_SEC/divfactor))
		return MAX_SLACK;

	slack = tv->tv_nsec / divfactor;
	slack += tv->tv_sec * (NSEC_PER_SEC/divfactor);

	if (slack > MAX_SLACK)
		return MAX_SLACK;

	return slack;
}

u64 select_estimate_accuracy(struct timespec64 *tv)
{
	u64 ret;
	struct timespec64 now;

	/*
	 * Realtime tasks get a slack of 0 for obvious reasons.
	 */

	if (rt_task(current))
		return 0;

	ktime_get_ts64(&now);
	now = timespec64_sub(*tv, now);
	ret = __estimate_accuracy(&now);
	if (ret < current->timer_slack_ns)
		return current->timer_slack_ns;
	return ret;
}



struct poll_table_page {
	struct poll_table_page * next; // jxh: 指向下一个申请的物理页
	struct poll_table_entry * entry; // jxh: 指向entries[]中首个待分配(空的) poll_table_entry地址
	struct poll_table_entry entries[]; // jxh: 该page页后面剩余的空间都是待分配的poll_table_entry结构体
};

#define POLL_TABLE_FULL(table) \
	((unsigned long)((table)->entry+1) > PAGE_SIZE + (unsigned long)(table))

/*
 * Ok, Peter made a complicated, but straightforward multiple_wait() function.
 * I have rewritten this, taking some shortcuts: This code may not be easy to
 * follow, but it should be free of race-conditions, and it's practical. If you
 * understand what I'm doing here, then you understand how the linux
 * sleep/wakeup mechanism works.
 *
 * Two very simple procedures, poll_wait() and poll_freewait() make all the
 * work.  poll_wait() is an inline-function defined in <linux/poll.h>,
 * as all select/poll functions have to call it to add an entry to the
 * poll table.
 */
static void __pollwait(struct file *filp, wait_queue_head_t *wait_address,
		       poll_table *p);

// jxh: 初始化poll队列
void poll_initwait(struct poll_wqueues *pwq)
{
	// jxh: poll_wqueues.poll_table.qproc函数指针初始化，该函数是驱动程序中poll函数（fop->poll）实现中必须要调用的poll_wait()中使用的函数。
	init_poll_funcptr(&pwq->pt, __pollwait);
	pwq->polling_task = current; // jxh: 当前调用的进程
	pwq->triggered = 0; // jxh: 是否已经触发
	pwq->error = 0; // jxh: 是否错误
	pwq->table = NULL;
	pwq->inline_index = 0;
}
EXPORT_SYMBOL(poll_initwait);

static void free_poll_entry(struct poll_table_entry *entry)
{
	remove_wait_queue(entry->wait_address, &entry->wait);
	fput(entry->filp);
}

void poll_freewait(struct poll_wqueues *pwq)
{
	struct poll_table_page * p = pwq->table;
	int i;
	for (i = 0; i < pwq->inline_index; i++)
		free_poll_entry(pwq->inline_entries + i);
	while (p) {
		struct poll_table_entry * entry;
		struct poll_table_page *old;

		entry = p->entry;
		do {
			entry--;
			free_poll_entry(entry);
		} while (entry > p->entries);
		old = p;
		p = p->next;
		free_page((unsigned long) old);
	}
}
EXPORT_SYMBOL(poll_freewait);

static struct poll_table_entry *poll_get_entry(struct poll_wqueues *p)
{
	struct poll_table_page *table = p->table;

	if (p->inline_index < N_INLINE_POLL_ENTRIES)
		return p->inline_entries + p->inline_index++;

	if (!table || POLL_TABLE_FULL(table)) {
		struct poll_table_page *new_table;

		new_table = (struct poll_table_page *) __get_free_page(GFP_KERNEL);
		if (!new_table) {
			p->error = -ENOMEM;
			return NULL;
		}
		new_table->entry = new_table->entries;
		new_table->next = table;
		p->table = new_table;
		table = new_table;
	}

	return table->entry++;
}

static int __pollwake(wait_queue_entry_t *wait, unsigned mode, int sync, void *key)
{
	struct poll_wqueues *pwq = wait->private;
	DECLARE_WAITQUEUE(dummy_wait, pwq->polling_task);

	/*
	 * Although this function is called under waitqueue lock, LOCK
	 * doesn't imply write barrier and the users expect write
	 * barrier semantics on wakeup functions.  The following
	 * smp_wmb() is equivalent to smp_wmb() in try_to_wake_up()
	 * and is paired with smp_store_mb() in poll_schedule_timeout.
	 */
	smp_wmb();
	pwq->triggered = 1;

	/*
	 * Perform the default wake up operation using a dummy
	 * waitqueue.
	 *
	 * TODO: This is hacky but there currently is no interface to
	 * pass in @sync.  @sync is scheduled to be removed and once
	 * that happens, wake_up_process() can be used directly.
	 */
	return default_wake_function(&dummy_wait, mode, sync, key);
}

static int pollwake(wait_queue_entry_t *wait, unsigned mode, int sync, void *key)
{
	struct poll_table_entry *entry;

	entry = container_of(wait, struct poll_table_entry, wait);
	if (key && !(key_to_poll(key) & entry->key))
		return 0;
	return __pollwake(wait, mode, sync, key);
}

/* Add a new entry */
/**
 * 将poll_table_entry挂载到资源文件的监听队列
 * @param filp 被监听的资源文件
 * @param wait_address 被监听的资源文件的等待队列头
 * @param p 在poll_initwait()中设置的poll_tbale
 */
static void __pollwait(struct file *filp, wait_queue_head_t *wait_address,
				poll_table *p)
{
	// jxh: 获取 poll_wqueues
	struct poll_wqueues *pwq = container_of(p, struct poll_wqueues, pt);
	// jxh: 获取 poll_table_entry
	struct poll_table_entry *entry = poll_get_entry(pwq);
	if (!entry) // jxh: 如果获取不到直接返回
		return;
	// jxh: 增加资源文件引用计数并关联到entry的filp属性
	entry->filp = get_file(filp);
	// jxh: 保存资源文件到队列头
	entry->wait_address = wait_address;
	// jxh: 赋值监听事件给entry的key
	entry->key = p->_key;
	// jxh: 初始化一个等待队列节点，其中唤醒函数设置为pollwake(重点)
	init_waitqueue_func_entry(&entry->wait, pollwake);
	entry->wait.private = pwq;
	// jxh: 添加到监听队列
	add_wait_queue(wait_address, &entry->wait);
}

static int poll_schedule_timeout(struct poll_wqueues *pwq, int state,
			  ktime_t *expires, unsigned long slack)
{
	int rc = -EINTR;

	set_current_state(state);
	if (!pwq->triggered)
		rc = schedule_hrtimeout_range(expires, slack, HRTIMER_MODE_ABS);
	__set_current_state(TASK_RUNNING);

	/*
	 * Prepare for the next iteration.
	 *
	 * The following smp_store_mb() serves two purposes.  First, it's
	 * the counterpart rmb of the wmb in pollwake() such that data
	 * written before wake up is always visible after wake up.
	 * Second, the full barrier guarantees that triggered clearing
	 * doesn't pass event check of the next iteration.  Note that
	 * this problem doesn't exist for the first iteration as
	 * add_wait_queue() has full barrier semantics.
	 */
	smp_store_mb(pwq->triggered, 0);

	return rc;
}

/**
 * poll_select_set_timeout - helper function to setup the timeout value
 * @to:		pointer to timespec64 variable for the final timeout
 * @sec:	seconds (from user space)
 * @nsec:	nanoseconds (from user space)
 *
 * Note, we do not use a timespec for the user space value here, That
 * way we can use the function for timeval and compat interfaces as well.
 *
 * Returns -EINVAL if sec/nsec are not normalized. Otherwise 0.
 */
int poll_select_set_timeout(struct timespec64 *to, time64_t sec, long nsec)
{
	struct timespec64 ts = {.tv_sec = sec, .tv_nsec = nsec};

	if (!timespec64_valid(&ts))
		return -EINVAL;

	/* Optimize for the zero timeout value here */
	if (!sec && !nsec) {
		to->tv_sec = to->tv_nsec = 0;
	} else {
		ktime_get_ts64(to);
		*to = timespec64_add_safe(*to, ts);
	}
	return 0;
}

enum poll_time_type {
	PT_TIMEVAL = 0,
	PT_OLD_TIMEVAL = 1,
	PT_TIMESPEC = 2,
	PT_OLD_TIMESPEC = 3,
};

static int poll_select_finish(struct timespec64 *end_time,
			      void __user *p,
			      enum poll_time_type pt_type, int ret)
{
	struct timespec64 rts;

	restore_saved_sigmask_unless(ret == -ERESTARTNOHAND);

	if (!p)
		return ret;

	if (current->personality & STICKY_TIMEOUTS)
		goto sticky;

	/* No update for zero timeout */
	if (!end_time->tv_sec && !end_time->tv_nsec)
		return ret;

	ktime_get_ts64(&rts);
	rts = timespec64_sub(*end_time, rts);
	if (rts.tv_sec < 0)
		rts.tv_sec = rts.tv_nsec = 0;


	switch (pt_type) {
	case PT_TIMEVAL:
		{
			struct __kernel_old_timeval rtv;

			if (sizeof(rtv) > sizeof(rtv.tv_sec) + sizeof(rtv.tv_usec))
				memset(&rtv, 0, sizeof(rtv));
			rtv.tv_sec = rts.tv_sec;
			rtv.tv_usec = rts.tv_nsec / NSEC_PER_USEC;
			if (!copy_to_user(p, &rtv, sizeof(rtv)))
				return ret;
		}
		break;
	case PT_OLD_TIMEVAL:
		{
			struct old_timeval32 rtv;

			rtv.tv_sec = rts.tv_sec;
			rtv.tv_usec = rts.tv_nsec / NSEC_PER_USEC;
			if (!copy_to_user(p, &rtv, sizeof(rtv)))
				return ret;
		}
		break;
	case PT_TIMESPEC:
		if (!put_timespec64(&rts, p))
			return ret;
		break;
	case PT_OLD_TIMESPEC:
		if (!put_old_timespec32(&rts, p))
			return ret;
		break;
	default:
		BUG();
	}
	/*
	 * If an application puts its timeval in read-only memory, we
	 * don't want the Linux-specific update to the timeval to
	 * cause a fault after the select has completed
	 * successfully. However, because we're not updating the
	 * timeval, we can't restart the system call.
	 */

sticky:
	if (ret == -ERESTARTNOHAND)
		ret = -EINTR;
	return ret;
}

/*
 * Scalable version of the fd_set.
 */

typedef struct { // jxh: 指针都是用来指向描述符集合
	unsigned long *in, *out, *ex; // jxh: 输入的文件描述符集事件
	unsigned long *res_in, *res_out, *res_ex; // jxh: 响应的文件描述符集事件
} fd_set_bits;

/*
 * How many longwords for "nr" bits?
 */
#define FDS_BITPERLONG	(8*sizeof(long))
#define FDS_LONGS(nr)	(((nr)+FDS_BITPERLONG-1)/FDS_BITPERLONG)
#define FDS_BYTES(nr)	(FDS_LONGS(nr)*sizeof(long))

/*
 * Use "unsigned long" accesses to let user-mode fd_set's be long-aligned.
 */
static inline
int get_fd_set(unsigned long nr, void __user *ufdset, unsigned long *fdset)
{
	nr = FDS_BYTES(nr);
	if (ufdset)
		return copy_from_user(fdset, ufdset, nr) ? -EFAULT : 0;

	memset(fdset, 0, nr);
	return 0;
}

static inline unsigned long __must_check
set_fd_set(unsigned long nr, void __user *ufdset, unsigned long *fdset)
{
	if (ufdset)
		return __copy_to_user(ufdset, fdset, FDS_BYTES(nr));
	return 0;
}

static inline
void zero_fd_set(unsigned long nr, unsigned long *fdset)
{
	memset(fdset, 0, FDS_BYTES(nr));
}

#define FDS_IN(fds, n)		(fds->in + n)
#define FDS_OUT(fds, n)		(fds->out + n)
#define FDS_EX(fds, n)		(fds->ex + n)

#define BITS(fds, n)	(*FDS_IN(fds, n)|*FDS_OUT(fds, n)|*FDS_EX(fds, n))

static int max_select_fd(unsigned long n, fd_set_bits *fds)
{
	unsigned long *open_fds;
	unsigned long set;
	int max;
	struct fdtable *fdt;

	/* handle last in-complete long-word first */
	set = ~(~0UL << (n & (BITS_PER_LONG-1)));
	n /= BITS_PER_LONG;
	fdt = files_fdtable(current->files);
	open_fds = fdt->open_fds + n;
	max = 0;
	if (set) {
		set &= BITS(fds, n);
		if (set) {
			if (!(set & ~*open_fds))
				goto get_max;
			return -EBADF;
		}
	}
	while (n) {
		open_fds--;
		n--;
		set = BITS(fds, n);
		if (!set)
			continue;
		if (set & ~*open_fds)
			return -EBADF;
		if (max)
			continue;
get_max:
		do {
			max++;
			set >>= 1;
		} while (set);
		max += n * BITS_PER_LONG;
	}

	return max;
}

#define POLLIN_SET (EPOLLRDNORM | EPOLLRDBAND | EPOLLIN | EPOLLHUP | EPOLLERR |\
			EPOLLNVAL)
#define POLLOUT_SET (EPOLLWRBAND | EPOLLWRNORM | EPOLLOUT | EPOLLERR |\
			 EPOLLNVAL)
#define POLLEX_SET (EPOLLPRI | EPOLLNVAL)

static inline void wait_key_set(poll_table *wait, unsigned long in,
				unsigned long out, unsigned long bit,
				__poll_t ll_flag)
{
	wait->_key = POLLEX_SET | ll_flag;
	if (in & bit)
		wait->_key |= POLLIN_SET;
	if (out & bit)
		wait->_key |= POLLOUT_SET;
}

/**
 * select 的具体实现
 * @param n 指定被监听文件描述符的总数
 * @param fds 文件描述符位图
 * @param end_time 超时时间
 * @return
 */
static noinline_for_stack int do_select(int n, fd_set_bits *fds, struct timespec64 *end_time)
{
	ktime_t expire, *to = NULL;
	struct poll_wqueues table; // jxh: 定义一个poll_wqueues变量
	poll_table *wait;
	int retval, i, timed_out = 0; // jxh: 超时标识
	u64 slack = 0;
	__poll_t busy_flag = net_busy_loop_on() ? POLL_BUSY_LOOP : 0;
	unsigned long busy_start = 0;

	rcu_read_lock();
	retval = max_select_fd(n, fds); // jxh: 根据设置的fd位图fds，检查确认所有位置对应的fd确实被打开了，并返回最大的fd
	rcu_read_unlock();

	if (retval < 0) // jxh: 如果为负值直接返回
		return retval;
	n = retval;

	// jxh: 初始化 poll_wqueues （重点）
	poll_initwait(&table);
	wait = &table.pt; // jxh: poll_table封装在poll_wqueues中

	// jxh: 判断是否超时
	if (end_time && !end_time->tv_sec && !end_time->tv_nsec) {
		wait->_qproc = NULL;
		timed_out = 1;
	}

	// jxh: 重新估算时间
	if (end_time && !timed_out)
		slack = select_estimate_accuracy(end_time);

	retval = 0;
	for (;;) { // jxh: 死循环
		unsigned long *rinp, *routp, *rexp, *inp, *outp, *exp; // jxh: 六种类型指针
		bool can_busy_loop = false;

		// jxh: 给上面指针赋值，指向fds对应的类型
		inp = fds->in; outp = fds->out; exp = fds->ex;
		rinp = fds->res_in; routp = fds->res_out; rexp = fds->res_ex;

		// jxh: 遍历所有的fd（n个文件描述符）
		for (i = 0; i < n; ++rinp, ++routp, ++rexp) {
			unsigned long in, out, ex, all_bits, bit = 1, j;
			unsigned long res_in = 0, res_out = 0, res_ex = 0;
			__poll_t mask;

			// jxh: 先取出当前循环周期中的32（设long占32位）个文件描述符对应的bitmaps
			in = *inp++; out = *outp++; ex = *exp++;
			all_bits = in | out | ex; // jxh: 按位或，组合所有类型
			if (all_bits == 0) { // jxh: 当前位图块没有需要处理的文件描述符(关心的fd)，则结束本块fd，调到下一个fd位图块
				i += BITS_PER_LONG; // jxh: BITS_PER_LONG 位图宏定义
				continue;
			}

			// jxh: 遍历当前所有位
			for (j = 0; j < BITS_PER_LONG; ++j, ++i, bit <<= 1) {
				struct fd f;
				if (i >= n) // jxh: i超出n范围直接跳出
					break;
				if (!(bit & all_bits)) // jxh: 跳过不关心的bit
					continue;
				mask = EPOLLNVAL;
				f = fdget(i); // jxh: 获取当前文件描述符的file结构指针
				if (f.file) { // jxh: （重点主线）如果文件存在
					// jxh: 设置poll_table智能柜想要监听的事件
					wait_key_set(wait, in, out, bit,
						     busy_flag);
					// jxh: （重点）调用文件的poll操作，返回准备好的事件
					mask = vfs_poll(f.file, wait);
					// jxh: 关闭文件监听
					fdput(f);
				}

				// jxh: events验证，其中retval表示就绪的资源数
				if ((mask & POLLIN_SET) && (in & bit)) { // jxh: 可读
					res_in |= bit; // jxh: 设置响应
					retval++;
					wait->_qproc = NULL;
				}
				if ((mask & POLLOUT_SET) && (out & bit)) { // jxh: 可写
					res_out |= bit;
					retval++;
					wait->_qproc = NULL;
				}
				if ((mask & POLLEX_SET) && (ex & bit)) { // jxh: 异常
					res_ex |= bit;
					retval++;
					wait->_qproc = NULL;
				}
				/* got something, stop busy polling */
				if (retval) {
					can_busy_loop = false;
					busy_flag = 0;

				/*
				 * only remember a returned
				 * POLL_BUSY_LOOP if we asked for it
				 */
				} else if (busy_flag & mask)
					can_busy_loop = true;

			}

			// jxh: 写出结果，注意写出的目的地是传进来的fd_set_bits
			if (res_in)
				*rinp = res_in;
			if (res_out)
				*routp = res_out;
			if (res_ex)
				*rexp = res_ex;

			// jxh: 主动让出cpu等待下次循环
			cond_resched();
		} // jxh: 遍历完n个fd

		wait->_qproc = NULL;

		// jxh: 如果当前这轮循环有准备好的事件|超时|（中断）检测到有信号则系统调用退出，返回用户空间执行信号处理函数 跳出死循环
		if (retval || timed_out || signal_pending(current))
			break;
		// jxh: 存在错误
		if (table.error) {
			retval = table.error;
			break;
		}

		/* only if found POLL_BUSY_LOOP sockets && not out of time */
		if (can_busy_loop && !need_resched()) {
			if (!busy_start) {
				busy_start = busy_loop_current_time();
				continue;
			}
			if (!busy_loop_timeout(busy_start))
				continue;
		}
		busy_flag = 0;

		/*
		 * If this is the first loop and we have a timeout
		 * given, then we convert to ktime_t and set the to
		 * pointer to the expiry value.
		 */
		if (end_time && !to) {
			expire = timespec64_to_ktime(*end_time);
			to = &expire;
		}

		// jxh: 能够到达这一步就说明没有发生就绪、中断以及超时
		/*
		 * 判断poll_wqueues是否已触发，如果还没有触发，那就设置当前运行状态为可中断阻塞并进行睡眠，等待被唤醒...
		 * 被唤醒之后重新进行迭代，获取资源就绪情况...
		 * 在向资源注册监听与判断poll_wqueues是否已触发这段时间内，可能资源异步就绪了，如果没有触发标志，那么可能就
		 * 会丢失资源就绪这个事件，可能导致select()永久沉睡...
		 * 这就是为什么需要poll_wqueues.triggered字段的原因...
		 */
		if (!poll_schedule_timeout(&table, TASK_INTERRUPTIBLE,
					   to, slack))
			timed_out = 1;
	}

	// jxh: 卸载安装到资源监听队列上的poll_table_entry；释放poll_wqueues占用的资源
	poll_freewait(&table);

	// jxh: 返回就绪的资源数
	return retval;
}

/*
 * We can actually return ERESTARTSYS instead of EINTR, but I'd
 * like to be certain this leads to no problems. So I return
 * EINTR just for safety.
 *
 * Update: ERESTARTSYS breaks at least the xview clock binary, so
 * I'm trying ERESTARTNOHAND which restart only when you want to.
 */
/**
 * 核心系统调用select
 * @param n 指定被监听文件描述符的总数
 * @param __user 用户空间宏定义 表示后面的指针是用户空间的数据
 * @param inp 读描述符集指针
 * @param outp 写描述符集指针
 * @param exp 异常描述符集指针
 * @param 超时时间指针（已复制到内核空间）
 * @return 返回可以操作的文件描述符数
 */
int core_sys_select(int n, fd_set __user *inp, fd_set __user *outp,
			   fd_set __user *exp, struct timespec64 *end_time)
{
	fd_set_bits fds; // jxh: 文件描述符集位图
	void *bits;
	int ret, max_fds; // jxh: 最大文件描述符
	size_t size, alloc_size;
	struct fdtable *fdt; // jxh: 文件描述符表
	/* Allocate small arguments on the stack to save memory and be faster */ // jxh: 在栈上分配一段内存
	long stack_fds[SELECT_STACK_ALLOC/sizeof(long)];

	ret = -EINVAL;
	if (n < 0) // jxh: 参数验证小于0直接返回
		goto out_nofds;

	/* max_fds can increase, so grab it once to avoid race */
	// jxh: 获得当前进程打开的文件 fd 表，获取最大的 fd
	rcu_read_lock();
	fdt = files_fdtable(current->files); // jxh: 读取文件描述符表
	max_fds = fdt->max_fds; // jxh: 从files结构中获取最大值（当前进程能够处理的最大文件数目）
	rcu_read_unlock();
	if (n > max_fds) // jxh: 防止n超过最大的fds
		n = max_fds;

	/*
	 * We need 6 bitmaps (in/out/ex for both incoming and outgoing),
	 * since we used fdset we need to allocate memory in units of
	 * long-words. 
	 */
	// jxh: 根据传入的需要监控的fd数量获取其需要分配的字节大小
	size = FDS_BYTES(n);
	bits = stack_fds;
	/* jxh: 如果栈上的内存太小，那么就在堆上重新分配内存
     	 * 为什么是除以6呢？
     	 * 因为每个文件描述符要占6个bit（输入：可读，可写，异常；输出结果：可读，可写，异常）*/
	if (size > sizeof(stack_fds) / 6) {
		/* Not enough space in on-stack array; must use kmalloc */
		ret = -ENOMEM;
		if (size > (SIZE_MAX / 6))
			goto out_nofds;

		alloc_size = 6 * size;
		bits = kvmalloc(alloc_size, GFP_KERNEL); // jxh: 分配虚拟内存
		if (!bits) // jxh: 分配失败直接结束
			goto out_nofds;
	}
	// jxh: 设置好bitmap对应的内存地址
	fds.in      = bits;		// jxh: 可读
	fds.out     = bits +   size;	// jxh: 可写
	fds.ex      = bits + 2*size;	// jxh: 异常
	fds.res_in  = bits + 3*size;	// jxh: 返回结果，可读
	fds.res_out = bits + 4*size;	// jxh: 返回结果，可写
	fds.res_ex  = bits + 5*size;	// jxh: 返回结果，异常

	// jxh: 将fd从用户空间（用户进程）拷贝到内核空间
	if ((ret = get_fd_set(n, inp, fds.in)) ||
	    (ret = get_fd_set(n, outp, fds.out)) ||
	    (ret = get_fd_set(n, exp, fds.ex)))
		goto out;

	// jxh: 清空返回结果的文件描述符集
	zero_fd_set(n, fds.res_in);
	zero_fd_set(n, fds.res_out);
	zero_fd_set(n, fds.res_ex);

	// jxh: 执行select（主线）
	ret = do_select(n, &fds, end_time);

	if (ret < 0) // jxh: 错误结束
		goto out;
	if (!ret) { // jxh: 超时结束
		ret = -ERESTARTNOHAND;
		if (signal_pending(current)) // jxh: 检测到有信号则系统调用退出，返回用户空间执行信号处理函数
			goto out;
		ret = 0;
	}

	// jxh: 将fd拷贝到用户空间（用户进程）
	if (set_fd_set(n, inp, fds.res_in) ||
	    set_fd_set(n, outp, fds.res_out) ||
	    set_fd_set(n, exp, fds.res_ex))
		ret = -EFAULT;

out:
	if (bits != stack_fds) // jxh: 如果是堆内存需要主动释放
		kvfree(bits);
out_nofds:
	return ret;
}

/**
 * select调用入口
 * @param n 指定被监听文件描述符的总数
 * @param __user 用户空间宏定义 表示后面的指针是用户空间的数据
 * @param inp 读描述符集指针
 * @param outp 写描述符集指针
 * @param exp 异常描述符集指针
 * @param tvp 超时时间指针
 * @return 返回可以操作的文件描述符数
 */
static int kern_select(int n, fd_set __user *inp, fd_set __user *outp,
		       fd_set __user *exp, struct __kernel_old_timeval __user *tvp)
{
	struct timespec64 end_time, *to = NULL; // jxh: 超时结构体
	struct __kernel_old_timeval tv; // jxh: 旧版本超时结构体
	int ret;

	if (tvp) {
		// jxh: 将超时参数从用户空间的数据拷贝到内核空间
		if (copy_from_user(&tv, tvp, sizeof(tv)))
			return -EFAULT;

		// jxh: 将超时时间设置给end_time变量
		to = &end_time;
		if (poll_select_set_timeout(to,
				tv.tv_sec + (tv.tv_usec / USEC_PER_SEC),
				(tv.tv_usec % USEC_PER_SEC) * NSEC_PER_USEC))
			return -EINVAL;
	}

	// jxh: 调用select
	ret = core_sys_select(n, inp, outp, exp, to);
	// jxh: 将剩余时间写回
	return poll_select_finish(&end_time, tvp, PT_TIMEVAL, ret);
}

// jxh: select()系统调用，在一段时间内，监听用户感兴趣的文件描述符上的可读、可写和异常事件。
SYSCALL_DEFINE5(select, int, n, fd_set __user *, inp, fd_set __user *, outp,
		fd_set __user *, exp, struct __kernel_old_timeval __user *, tvp)
{
	return kern_select(n, inp, outp, exp, tvp);
}

static long do_pselect(int n, fd_set __user *inp, fd_set __user *outp,
		       fd_set __user *exp, void __user *tsp,
		       const sigset_t __user *sigmask, size_t sigsetsize,
		       enum poll_time_type type)
{
	struct timespec64 ts, end_time, *to = NULL;
	int ret;

	if (tsp) {
		switch (type) {
		case PT_TIMESPEC:
			if (get_timespec64(&ts, tsp))
				return -EFAULT;
			break;
		case PT_OLD_TIMESPEC:
			if (get_old_timespec32(&ts, tsp))
				return -EFAULT;
			break;
		default:
			BUG();
		}

		to = &end_time;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	ret = set_user_sigmask(sigmask, sigsetsize);
	if (ret)
		return ret;

	ret = core_sys_select(n, inp, outp, exp, to);
	return poll_select_finish(&end_time, tsp, type, ret);
}

/*
 * Most architectures can't handle 7-argument syscalls. So we provide a
 * 6-argument version where the sixth argument is a pointer to a structure
 * which has a pointer to the sigset_t itself followed by a size_t containing
 * the sigset size.
 */
struct sigset_argpack {
	sigset_t __user *p;
	size_t size;
};

static inline int get_sigset_argpack(struct sigset_argpack *to,
				     struct sigset_argpack __user *from)
{
	// the path is hot enough for overhead of copy_from_user() to matter
	if (from) {
		if (!user_read_access_begin(from, sizeof(*from)))
			return -EFAULT;
		unsafe_get_user(to->p, &from->p, Efault);
		unsafe_get_user(to->size, &from->size, Efault);
		user_read_access_end();
	}
	return 0;
Efault:
	user_access_end();
	return -EFAULT;
}

SYSCALL_DEFINE6(pselect6, int, n, fd_set __user *, inp, fd_set __user *, outp,
		fd_set __user *, exp, struct __kernel_timespec __user *, tsp,
		void __user *, sig)
{
	struct sigset_argpack x = {NULL, 0};

	if (get_sigset_argpack(&x, sig))
		return -EFAULT;

	return do_pselect(n, inp, outp, exp, tsp, x.p, x.size, PT_TIMESPEC);
}

#if defined(CONFIG_COMPAT_32BIT_TIME) && !defined(CONFIG_64BIT)

SYSCALL_DEFINE6(pselect6_time32, int, n, fd_set __user *, inp, fd_set __user *, outp,
		fd_set __user *, exp, struct old_timespec32 __user *, tsp,
		void __user *, sig)
{
	struct sigset_argpack x = {NULL, 0};

	if (get_sigset_argpack(&x, sig))
		return -EFAULT;

	return do_pselect(n, inp, outp, exp, tsp, x.p, x.size, PT_OLD_TIMESPEC);
}

#endif

#ifdef __ARCH_WANT_SYS_OLD_SELECT
struct sel_arg_struct {
	unsigned long n;
	fd_set __user *inp, *outp, *exp;
	struct __kernel_old_timeval __user *tvp;
};

SYSCALL_DEFINE1(old_select, struct sel_arg_struct __user *, arg)
{
	struct sel_arg_struct a;

	if (copy_from_user(&a, arg, sizeof(a)))
		return -EFAULT;
	return kern_select(a.n, a.inp, a.outp, a.exp, a.tvp);
}
#endif

struct poll_list {
	struct poll_list *next;
	unsigned int len;
	struct pollfd entries[];
};

#define POLLFD_PER_PAGE  ((PAGE_SIZE-sizeof(struct poll_list)) / sizeof(struct pollfd))

/*
 * Fish for pollable events on the pollfd->fd file descriptor. We're only
 * interested in events matching the pollfd->events mask, and the result
 * matching that mask is both recorded in pollfd->revents and returned. The
 * pwait poll_table will be used by the fd-provided poll handler for waiting,
 * if pwait->_qproc is non-NULL.
 */
/**
 * 调用fd驱动函数
 * @param pollfd pollfd结构体
 * @param pwait
 * @param can_busy_poll
 * @param busy_flag
 * @return 返回准备好的事件
 */
static inline __poll_t do_pollfd(struct pollfd *pollfd, poll_table *pwait,
				     bool *can_busy_poll,
				     __poll_t busy_flag)
{
	int fd = pollfd->fd; // jxh: 文件描述符
	__poll_t mask = 0, filter;
	struct fd f;

	if (fd < 0) // jxh: fd无效直接返回
		goto out;
	mask = EPOLLNVAL;

	// jxh: 获取真正的文件
	f = fdget(fd);
	if (!f.file) // jxh: 验证文件有效性
		goto out;

	/* userland u16 ->events contains POLL... bitmap */
	filter = demangle_poll(pollfd->events) | EPOLLERR | EPOLLHUP;
	pwait->_key = filter | busy_flag;

	// jxh: (核心)调用file的驱动 vfs_poll 返回该文件已经准备好的事件
	mask = vfs_poll(f.file, pwait);
	if (mask & busy_flag)
		*can_busy_poll = true;
	mask &= filter;		/* Mask out unneeded events. */
	fdput(f);

out:
	/* ... and so does ->revents */
	pollfd->revents = mangle_poll(mask);
	return mask;
}

/**
 * 核心调用poll
 * @param list fd列表的链表
 * @param wait 调度控制块
 * @param end_time 超时时间
 * @return 返回准备好的fd个数
 */
static int do_poll(struct poll_list *list, struct poll_wqueues *wait,
		   struct timespec64 *end_time)
{
	poll_table* pt = &wait->pt; // jxh: 获取poll_table
	ktime_t expire, *to = NULL; // jxh: 时间
	int timed_out = 0, count = 0;
	u64 slack = 0;
	__poll_t busy_flag = net_busy_loop_on() ? POLL_BUSY_LOOP : 0;
	unsigned long busy_start = 0;

	/* Optimise the no-wait case */ // jxh: 判断是否超时
	if (end_time && !end_time->tv_sec && !end_time->tv_nsec) {
		pt->_qproc = NULL;
		timed_out = 1;
	}

	if (end_time && !timed_out) // jxh: 预估时间
		slack = select_estimate_accuracy(end_time);

	for (;;) { // jxh: 死循环遍历
		// jxh: 当前遍历的链表节点（节点中包含pollfd数组）
		struct poll_list *walk;
		bool can_busy_loop = false;

		// jxh: 遍历链表
		for (walk = list; walk != NULL; walk = walk->next) { // jxh: walk = walk->next链表移动
			struct pollfd * pfd, * pfd_end;

			pfd = walk->entries;
			pfd_end = pfd + walk->len;
			// jxh: 遍历当前节点的所有fd
			for (; pfd != pfd_end; pfd++) {
				/*
				 * Fish for events. If we found one, record it
				 * and kill poll_table->_qproc, so we don't
				 * needlessly register any other waiters after
				 * this. They'll get immediately deregistered
				 * when we break out and return.
				 */
				// jxh: (主线) 调用do_pollfd 返回触发的事件
				if (do_pollfd(pfd, pt, &can_busy_loop,
					      busy_flag)) {
					count++;
					pt->_qproc = NULL;
					/* found something, stop busy polling */
					busy_flag = 0;
					can_busy_loop = false;
				}
			}
		}
		/*
		 * All waiters have already been registered, so don't provide
		 * a poll_table->_qproc to them on the next loop iteration.
		 */
		pt->_qproc = NULL;
		if (!count) {
			count = wait->error;
			if (signal_pending(current))
				count = -ERESTARTNOHAND;
		}
		// jxh: 有准备好的fd或者超时则跳出死循环
		if (count || timed_out)
			break;

		/* only if found POLL_BUSY_LOOP sockets && not out of time */
		if (can_busy_loop && !need_resched()) {
			if (!busy_start) {
				busy_start = busy_loop_current_time();
				continue;
			}
			if (!busy_loop_timeout(busy_start))
				continue;
		}
		busy_flag = 0;

		/*
		 * If this is the first loop and we have a timeout
		 * given, then we convert to ktime_t and set the to
		 * pointer to the expiry value.
		 */
		if (end_time && !to) {
			expire = timespec64_to_ktime(*end_time);
			to = &expire;
		}

		// jxh: 判断是否超时
		if (!poll_schedule_timeout(wait, TASK_INTERRUPTIBLE, to, slack))
			timed_out = 1;
	}
	return count;
}

#define N_STACK_PPS ((sizeof(stack_pps) - sizeof(struct poll_list))  / \
			sizeof(struct pollfd))

/**
 * poll系统调用核心：
 * - 分配链表空间
 * - 初始化 poll_wqueues 控制块
 * - 调用 do_poll 方法
 * @param __user
 * @return 返回
 */
static int do_sys_poll(struct pollfd __user *ufds, unsigned int nfds,
		struct timespec64 *end_time)
{
	struct poll_wqueues table; // jxh: 定义一个poll调用控制块（表）
	int err = -EFAULT, fdcount;
	/* Allocate small arguments on the stack to save memory and be
	   faster - use long to make sure the buffer is aligned properly
	   on 64 bit archs to avoid unaligned access */
	long stack_pps[POLL_STACK_ALLOC/sizeof(long)]; // jxh: 优先在栈上分配空间
	struct poll_list *const head = (struct poll_list *)stack_pps;
 	struct poll_list *walk = head;
	unsigned int todo = nfds;
	unsigned int len;

	if (nfds > rlimit(RLIMIT_NOFILE)) // jxh: 检查是否超出长度限制
		return -EINVAL;

	len = min_t(unsigned int, nfds, N_STACK_PPS); // jxh: 获取分配的空间长度

	// jxh: 为每一个节点（pollfd）进行分配空间
	for (;;) {
		walk->next = NULL;
		walk->len = len;
		if (!len) // jxh: 所需长度为0则可跳出循环
			break;

		// jxh: 复制文件描述符到内核空间
		if (copy_from_user(walk->entries, ufds + nfds-todo,
					sizeof(struct pollfd) * walk->len))
			goto out_fds;

		if (walk->len >= todo)
			break;
		todo -= walk->len;

		len = min(todo, POLLFD_PER_PAGE);

		// jxh: 在堆区分配空间
		walk = walk->next = kmalloc(struct_size(walk, entries, len),
					    GFP_KERNEL);
		if (!walk) {
			err = -ENOMEM;
			goto out_fds;
		}
	}

	// jxh: 初始化poll控制块
	poll_initwait(&table);
	// jxh: (主线）执行poll调用
	fdcount = do_poll(head, &table, end_time);
	// jxh: 释放poll控制块
	poll_freewait(&table);

	if (!user_write_access_begin(ufds, nfds * sizeof(*ufds))) // jxh: 如果用户没有写入权限
		goto out_fds;

	for (walk = head; walk; walk = walk->next) {
		struct pollfd *fds = walk->entries;
		unsigned int j;

		for (j = walk->len; j; fds++, ufds++, j--)
			unsafe_put_user(fds->revents, &ufds->revents, Efault);
  	}
	user_write_access_end();

	err = fdcount;
out_fds:
	walk = head->next;
	while (walk) {
		struct poll_list *pos = walk;
		walk = walk->next;
		kfree(pos);
	}

	return err;

Efault:
	user_write_access_end();
	err = -EFAULT;
	goto out_fds;
}

static long do_restart_poll(struct restart_block *restart_block)
{
	struct pollfd __user *ufds = restart_block->poll.ufds;
	int nfds = restart_block->poll.nfds;
	struct timespec64 *to = NULL, end_time;
	int ret;

	if (restart_block->poll.has_timeout) {
		end_time.tv_sec = restart_block->poll.tv_sec;
		end_time.tv_nsec = restart_block->poll.tv_nsec;
		to = &end_time;
	}

	ret = do_sys_poll(ufds, nfds, to);

	if (ret == -ERESTARTNOHAND)
		ret = set_restart_fn(restart_block, do_restart_poll);

	return ret;
}

// jxh: poll()系统调用
/**
* poll系统调用
* @param ufds 用户空间poll文件描述符
* @param nfds ufds的长度
* @param timeout_msecs 超时参数
*/
SYSCALL_DEFINE3(poll, struct pollfd __user *, ufds, unsigned int, nfds,
		int, timeout_msecs)
{
	struct timespec64 end_time, *to = NULL; // jxh: 超时时间
	int ret; // jxh: 响应结果

	if (timeout_msecs >= 0) { // jxh: 计算超时时间
		to = &end_time;
		poll_select_set_timeout(to, timeout_msecs / MSEC_PER_SEC,
			NSEC_PER_MSEC * (timeout_msecs % MSEC_PER_SEC));
	}

	// jxh: (主线)核心调用
	ret = do_sys_poll(ufds, nfds, to);

	// jxh: 错误码（系统错误）-ERESTARTNOHAND表明,被中断的系统调用
	if (ret == -ERESTARTNOHAND) {
		struct restart_block *restart_block;

		restart_block = &current->restart_block;
		restart_block->poll.ufds = ufds;
		restart_block->poll.nfds = nfds;

		// jxh: 是否超时
		if (timeout_msecs >= 0) {
			restart_block->poll.tv_sec = end_time.tv_sec;
			restart_block->poll.tv_nsec = end_time.tv_nsec;
			restart_block->poll.has_timeout = 1;
		} else
			restart_block->poll.has_timeout = 0;

		// jxh: 重启服务
		ret = set_restart_fn(restart_block, do_restart_poll);
	}
	return ret;
}

SYSCALL_DEFINE5(ppoll, struct pollfd __user *, ufds, unsigned int, nfds,
		struct __kernel_timespec __user *, tsp, const sigset_t __user *, sigmask,
		size_t, sigsetsize)
{
	struct timespec64 ts, end_time, *to = NULL;
	int ret;

	if (tsp) {
		if (get_timespec64(&ts, tsp))
			return -EFAULT;

		to = &end_time;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	ret = set_user_sigmask(sigmask, sigsetsize);
	if (ret)
		return ret;

	ret = do_sys_poll(ufds, nfds, to);
	return poll_select_finish(&end_time, tsp, PT_TIMESPEC, ret);
}

#if defined(CONFIG_COMPAT_32BIT_TIME) && !defined(CONFIG_64BIT)

SYSCALL_DEFINE5(ppoll_time32, struct pollfd __user *, ufds, unsigned int, nfds,
		struct old_timespec32 __user *, tsp, const sigset_t __user *, sigmask,
		size_t, sigsetsize)
{
	struct timespec64 ts, end_time, *to = NULL;
	int ret;

	if (tsp) {
		if (get_old_timespec32(&ts, tsp))
			return -EFAULT;

		to = &end_time;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	ret = set_user_sigmask(sigmask, sigsetsize);
	if (ret)
		return ret;

	ret = do_sys_poll(ufds, nfds, to);
	return poll_select_finish(&end_time, tsp, PT_OLD_TIMESPEC, ret);
}
#endif

#ifdef CONFIG_COMPAT
#define __COMPAT_NFDBITS       (8 * sizeof(compat_ulong_t))

/*
 * Ooo, nasty.  We need here to frob 32-bit unsigned longs to
 * 64-bit unsigned longs.
 */
static
int compat_get_fd_set(unsigned long nr, compat_ulong_t __user *ufdset,
			unsigned long *fdset)
{
	if (ufdset) {
		return compat_get_bitmap(fdset, ufdset, nr);
	} else {
		zero_fd_set(nr, fdset);
		return 0;
	}
}

static
int compat_set_fd_set(unsigned long nr, compat_ulong_t __user *ufdset,
		      unsigned long *fdset)
{
	if (!ufdset)
		return 0;
	return compat_put_bitmap(ufdset, fdset, nr);
}


/*
 * This is a virtual copy of sys_select from fs/select.c and probably
 * should be compared to it from time to time
 */

/*
 * We can actually return ERESTARTSYS instead of EINTR, but I'd
 * like to be certain this leads to no problems. So I return
 * EINTR just for safety.
 *
 * Update: ERESTARTSYS breaks at least the xview clock binary, so
 * I'm trying ERESTARTNOHAND which restart only when you want to.
 */
static int compat_core_sys_select(int n, compat_ulong_t __user *inp,
	compat_ulong_t __user *outp, compat_ulong_t __user *exp,
	struct timespec64 *end_time)
{
	fd_set_bits fds;
	void *bits;
	int size, max_fds, ret = -EINVAL;
	struct fdtable *fdt;
	long stack_fds[SELECT_STACK_ALLOC/sizeof(long)];

	if (n < 0)
		goto out_nofds;

	/* max_fds can increase, so grab it once to avoid race */
	rcu_read_lock();
	fdt = files_fdtable(current->files);
	max_fds = fdt->max_fds;
	rcu_read_unlock();
	if (n > max_fds)
		n = max_fds;

	/*
	 * We need 6 bitmaps (in/out/ex for both incoming and outgoing),
	 * since we used fdset we need to allocate memory in units of
	 * long-words.
	 */
	size = FDS_BYTES(n);
	bits = stack_fds;
	if (size > sizeof(stack_fds) / 6) {
		bits = kmalloc_array(6, size, GFP_KERNEL);
		ret = -ENOMEM;
		if (!bits)
			goto out_nofds;
	}
	fds.in      = (unsigned long *)  bits;
	fds.out     = (unsigned long *) (bits +   size);
	fds.ex      = (unsigned long *) (bits + 2*size);
	fds.res_in  = (unsigned long *) (bits + 3*size);
	fds.res_out = (unsigned long *) (bits + 4*size);
	fds.res_ex  = (unsigned long *) (bits + 5*size);

	if ((ret = compat_get_fd_set(n, inp, fds.in)) ||
	    (ret = compat_get_fd_set(n, outp, fds.out)) ||
	    (ret = compat_get_fd_set(n, exp, fds.ex)))
		goto out;
	zero_fd_set(n, fds.res_in);
	zero_fd_set(n, fds.res_out);
	zero_fd_set(n, fds.res_ex);

	ret = do_select(n, &fds, end_time);

	if (ret < 0)
		goto out;
	if (!ret) {
		ret = -ERESTARTNOHAND;
		if (signal_pending(current))
			goto out;
		ret = 0;
	}

	if (compat_set_fd_set(n, inp, fds.res_in) ||
	    compat_set_fd_set(n, outp, fds.res_out) ||
	    compat_set_fd_set(n, exp, fds.res_ex))
		ret = -EFAULT;
out:
	if (bits != stack_fds)
		kfree(bits);
out_nofds:
	return ret;
}

static int do_compat_select(int n, compat_ulong_t __user *inp,
	compat_ulong_t __user *outp, compat_ulong_t __user *exp,
	struct old_timeval32 __user *tvp)
{
	struct timespec64 end_time, *to = NULL;
	struct old_timeval32 tv;
	int ret;

	if (tvp) {
		if (copy_from_user(&tv, tvp, sizeof(tv)))
			return -EFAULT;

		to = &end_time;
		if (poll_select_set_timeout(to,
				tv.tv_sec + (tv.tv_usec / USEC_PER_SEC),
				(tv.tv_usec % USEC_PER_SEC) * NSEC_PER_USEC))
			return -EINVAL;
	}

	ret = compat_core_sys_select(n, inp, outp, exp, to);
	return poll_select_finish(&end_time, tvp, PT_OLD_TIMEVAL, ret);
}

COMPAT_SYSCALL_DEFINE5(select, int, n, compat_ulong_t __user *, inp,
	compat_ulong_t __user *, outp, compat_ulong_t __user *, exp,
	struct old_timeval32 __user *, tvp)
{
	return do_compat_select(n, inp, outp, exp, tvp);
}

struct compat_sel_arg_struct {
	compat_ulong_t n;
	compat_uptr_t inp;
	compat_uptr_t outp;
	compat_uptr_t exp;
	compat_uptr_t tvp;
};

COMPAT_SYSCALL_DEFINE1(old_select, struct compat_sel_arg_struct __user *, arg)
{
	struct compat_sel_arg_struct a;

	if (copy_from_user(&a, arg, sizeof(a)))
		return -EFAULT;
	return do_compat_select(a.n, compat_ptr(a.inp), compat_ptr(a.outp),
				compat_ptr(a.exp), compat_ptr(a.tvp));
}

static long do_compat_pselect(int n, compat_ulong_t __user *inp,
	compat_ulong_t __user *outp, compat_ulong_t __user *exp,
	void __user *tsp, compat_sigset_t __user *sigmask,
	compat_size_t sigsetsize, enum poll_time_type type)
{
	struct timespec64 ts, end_time, *to = NULL;
	int ret;

	if (tsp) {
		switch (type) {
		case PT_OLD_TIMESPEC:
			if (get_old_timespec32(&ts, tsp))
				return -EFAULT;
			break;
		case PT_TIMESPEC:
			if (get_timespec64(&ts, tsp))
				return -EFAULT;
			break;
		default:
			BUG();
		}

		to = &end_time;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	ret = set_compat_user_sigmask(sigmask, sigsetsize);
	if (ret)
		return ret;

	ret = compat_core_sys_select(n, inp, outp, exp, to);
	return poll_select_finish(&end_time, tsp, type, ret);
}

struct compat_sigset_argpack {
	compat_uptr_t p;
	compat_size_t size;
};
static inline int get_compat_sigset_argpack(struct compat_sigset_argpack *to,
					    struct compat_sigset_argpack __user *from)
{
	if (from) {
		if (!user_read_access_begin(from, sizeof(*from)))
			return -EFAULT;
		unsafe_get_user(to->p, &from->p, Efault);
		unsafe_get_user(to->size, &from->size, Efault);
		user_read_access_end();
	}
	return 0;
Efault:
	user_access_end();
	return -EFAULT;
}

COMPAT_SYSCALL_DEFINE6(pselect6_time64, int, n, compat_ulong_t __user *, inp,
	compat_ulong_t __user *, outp, compat_ulong_t __user *, exp,
	struct __kernel_timespec __user *, tsp, void __user *, sig)
{
	struct compat_sigset_argpack x = {0, 0};

	if (get_compat_sigset_argpack(&x, sig))
		return -EFAULT;

	return do_compat_pselect(n, inp, outp, exp, tsp, compat_ptr(x.p),
				 x.size, PT_TIMESPEC);
}

#if defined(CONFIG_COMPAT_32BIT_TIME)

COMPAT_SYSCALL_DEFINE6(pselect6_time32, int, n, compat_ulong_t __user *, inp,
	compat_ulong_t __user *, outp, compat_ulong_t __user *, exp,
	struct old_timespec32 __user *, tsp, void __user *, sig)
{
	struct compat_sigset_argpack x = {0, 0};

	if (get_compat_sigset_argpack(&x, sig))
		return -EFAULT;

	return do_compat_pselect(n, inp, outp, exp, tsp, compat_ptr(x.p),
				 x.size, PT_OLD_TIMESPEC);
}

#endif

#if defined(CONFIG_COMPAT_32BIT_TIME)
COMPAT_SYSCALL_DEFINE5(ppoll_time32, struct pollfd __user *, ufds,
	unsigned int,  nfds, struct old_timespec32 __user *, tsp,
	const compat_sigset_t __user *, sigmask, compat_size_t, sigsetsize)
{
	struct timespec64 ts, end_time, *to = NULL;
	int ret;

	if (tsp) {
		if (get_old_timespec32(&ts, tsp))
			return -EFAULT;

		to = &end_time;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	ret = set_compat_user_sigmask(sigmask, sigsetsize);
	if (ret)
		return ret;

	ret = do_sys_poll(ufds, nfds, to);
	return poll_select_finish(&end_time, tsp, PT_OLD_TIMESPEC, ret);
}
#endif

/* New compat syscall for 64 bit time_t*/
COMPAT_SYSCALL_DEFINE5(ppoll_time64, struct pollfd __user *, ufds,
	unsigned int,  nfds, struct __kernel_timespec __user *, tsp,
	const compat_sigset_t __user *, sigmask, compat_size_t, sigsetsize)
{
	struct timespec64 ts, end_time, *to = NULL;
	int ret;

	if (tsp) {
		if (get_timespec64(&ts, tsp))
			return -EFAULT;

		to = &end_time;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	ret = set_compat_user_sigmask(sigmask, sigsetsize);
	if (ret)
		return ret;

	ret = do_sys_poll(ufds, nfds, to);
	return poll_select_finish(&end_time, tsp, PT_TIMESPEC, ret);
}

#endif
