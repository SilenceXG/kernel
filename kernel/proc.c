#include "types.h"
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "pstat.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

typedef struct q{
    struct proc* p;
    struct q* next;
} q;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void dequeue(struct proc** pq, int pq_num, int index);
int check_promote(struct proc* proc);

// 4 level priorities
struct proc* lv0[NPROC];
struct proc* lv1[NPROC];
struct proc* lv2[NPROC];
struct proc* lv3[NPROC];
// number of proc in each queue
int lv0_num = 0;
int lv1_num = 0;
int lv2_num = 0;
int lv3_num = 0;
// initial time ticks
const int LV1_TIME = 32;
const int LV2_TIME = 16;
const int LV3_TIME = 8;

int q_status = 3;

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;
  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  //modified for MLFQ
  p -> priority = 3;
  for(int i = 0; i < NLAYER; ++i){
      p -> ticks[i] = 0;
      p -> wait_ticks[i] = 0;
  }
  release(&ptable.lock);

  // Allocate kernel stack if possible.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;
  
  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;
  
  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];
  
  p = allocproc();
  acquire(&ptable.lock);
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;
  
  // modified for MLFQ
  //p->priority = 3;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  
  sz = proc->sz;
  if(n > 0){
    if((sz = allocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  proc->sz = sz;
  switchuvm(proc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;

  // Allocate process.
  if((np = allocproc()) == 0)
    return -1;

  // Copy process state from p.
  if((np->pgdir = copyuvm(proc->pgdir, proc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = proc->sz;
  np->parent = proc;
  *np->tf = *proc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(proc->ofile[i])
      np->ofile[i] = filedup(proc->ofile[i]);
  np->cwd = idup(proc->cwd);
 
  pid = np->pid;
  np->state = RUNNABLE;
  safestrcpy(np->name, proc->name, sizeof(proc->name));
  // modified for MLFQ
  // p->priority = 3;
  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *p;
  int fd;

  if(proc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(proc->ofile[fd]){
      fileclose(proc->ofile[fd]);
      proc->ofile[fd] = 0;
    }
  }

  iput(proc->cwd);
  proc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(proc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == proc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  proc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;

  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for zombie children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != proc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->state = UNUSED;
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || proc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(proc, &ptable.lock);  //DOC: wait-sleep
  }
}

int
check_promote(struct proc* proc){

    // increment wait time for other RUNNABLE proc
    struct proc *pa;

    for(pa = ptable.proc; pa < &ptable.proc[NPROC]; pa++){
        if(pa->state != RUNNABLE || pa == proc)
            continue;
        pa -> wait_ticks[pa -> priority]++;
        // check for promotion
        if(pa -> priority == 2 && pa -> wait_ticks[2] >= 10 * LV2_TIME){
            pa->priority++;
            // logics in lv2 loop will handle the decrement of lv2_num
            // add the proc to pq3
            lv3[lv3_num] = proc; 
            lv3_num++;
            // if we are not in lv3, then jump to lv3 RR loop
            if(q_status != 3)
                return 1;
        }
        else if(pa -> priority == 1 && pa -> wait_ticks[1] >= 10 * LV1_TIME){
            pa->priority++;
            // logics in lv1 loop will handle the decrement of lv1_num
            // add the proc to pq2
            lv2[lv2_num] = proc; 
            lv2_num++;
            // if we are not in lv3 or lv2, jump to lv2 RR loop
            if(q_status != 3 || q_status != 2)
                return 1;
        }
        else if(pa -> priority == 0 && pa -> wait_ticks[0] >= 500){
            pa->priority++;
            // logics in lv0 loop will handle the decrement of lv0_num
            // add the proc to pq1
            lv1[lv1_num] = proc; 
            lv1_num++;
            // if we are in lv0, then jump to lv1 RR loop
            if(q_status == 0)
                return 1;
        }
    }
    return 0; 

}



void
dequeue(struct proc** pq, int pq_num, int index){
    pq_num--;
    for(int i = index; i < pq_num; ++i)
        pq[i] = pq[i+1];
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  
  // Code for mlfq

  for(;;){
      // Enable interrupts on this processor.
    sti();

    
    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
         continue;
        
      // we add newly arrived proc to q3
      lv3[lv3_num] = p;
      lv3_num++;
      }

      // while lv3 is non empty, do RR
      while(lv3_num > 0){
        LV3_START: q_status = 3;
        for(int i = 0; i < lv3_num; ++i){
            if(lv3[i] -> state != RUNNABLE || lv3[i] -> priority != 3){
                // remove that proc from q3
                dequeue(lv3, lv3_num, i);
            }
            // Switch to chosen process.  It is the process's job
            // to release ptable.lock and then reacquire it
            // before jumping back to us.
        
            proc = lv3[i];

            switchuvm(proc);
            proc -> state = RUNNING;
            swtch(&cpu->scheduler, proc->context);
            //kernel regain control since here
            // increment ticks
            (proc -> ticks[3])++;
            if(proc -> ticks[3] >= LV3_TIME){
                proc -> priority = 2;
                // add the proc to pq2
                lv2[lv2_num] = proc; 
                lv2_num++;
            }
            check_promote(proc);
            /*
            // increment wait time for other RUNNABLE proc
            struct proc *pa;

            for(pa = ptable.proc; pa < &ptable.proc[NPROC]; pa++){
                if(pa->state != RUNNABLE || pa == proc)
                    continue;
                pa -> wait_ticks[pa -> priority]++;
                // check for promotion
                if(pa -> priority == 2 && pa -> wait_ticks[2] >= 10 * LV2_TIME){
                    pa->priority++;
                    lv3_num++;
                    // logics in lv2 loop will handle the decrement of lv2_num
                    // add the proc to pq3
                    lv3[lv3_num] = proc; 
                }
                else if(pa -> priority == 1 && pa -> wait_ticks[1] >= 10 * LV1_TIME){
                    pa->priority++;
                    lv2_num++;
                    // logics in lv1 loop will handle the decrement of lv1_num
                    // add the proc to pq2
                    lv2[lv2_num] = proc; 
                }
                else if(pa -> priority == 0 && pa -> wait_ticks[0] >= 500){
                    pa->priority++;
                    lv1_num++;
                    // logics in lv0 loop will handle the decrement of lv0_num
                    // add the proc to pq1
                    lv1[lv1_num] = proc; 
                }
            }   
            */
            // clear the wait time for proc
            proc -> wait_ticks[3] = 0;
            switchkvm();

            // Process is done running for now.
            // It should have changed its p->state before coming back.
            proc = 0;
        }
    }
     // while lv2 is non empty, do RR
     while(lv2_num > 0){
       LV2_START: q_status = 2;
       int jump_status = 0;
       for(int i = 0; i < lv2_num; ++i){
           if(lv2[i] -> state != RUNNABLE || lv2[i] -> priority != 2){
               // remove that proc from q2
               dequeue(lv2, lv2_num, i);
           }

           // Switch to chosen process.  It is the process's job
           // to release ptable.lock and then reacquire it
           // before jumping back to us.
       
           proc = lv2[i];

           switchuvm(proc);
           proc -> state = RUNNING;
           swtch(&cpu->scheduler, proc->context);
           //kernel regain control since here
           // increment ticks
           (proc -> ticks[2])++;
           if(proc -> ticks[2] >= LV2_TIME){
               proc -> priority = 1;
               // add the proc to lv1
               lv1[lv1_num] = proc;
               lv1_num++;
           }
            
           jump_status = check_promote(proc);
           // clear the wait time for proc
           proc -> wait_ticks[2] = 0;

           switchkvm();

           // Process is done running for now.
           // It should have changed its p->state before coming back.
           proc = 0;
           //if proc in lv2 gets promoted, jump to lv3
           if(jump_status)
               goto LV3_START;
       }
    }

    // while lv1 is non empty, do RR
    while(lv1_num > 0){
      LV1_START: q_status = 1;
      int jump_status = 0;
      for(int i = 0; i < lv1_num; ++i){
          if(lv1[i]-> state != RUNNABLE || lv1[i] -> priority != 1){
              // remove that proc from q1
              dequeue(lv1, lv1_num, i);
          }

          // Switch to chosen process.  It is the process's job
          // to release ptable.lock and then reacquire it
          // before jumping back to us.
      
          proc = lv1[i];

          switchuvm(proc);
          proc -> state = RUNNING;
          swtch(&cpu->scheduler, proc->context);
          //kernel regain control since here
          // increment ticks
          (proc -> ticks[1])++;
          if(proc -> ticks[1] >= LV1_TIME){
              proc -> priority = 0;
              // add the proc to lv0
              lv0[lv0_num] = proc;
              lv0_num++;
          }

          jump_status = check_promote(proc);
          // clear the wait time for proc
          proc -> wait_ticks[1] = 0;

          switchkvm();
          // Process is done running for now.
          // It should have changed its p->state before coming back.
          proc = 0;

          //if any proc in lv1 gets promoted, jump to lv2
          if(jump_status)
            goto LV2_START;
      }
    }
    // while lv0 is not empty, do FIFO
    while(lv0_num > 0){
      q_status = 0;
      int jump_status = 0;
      for(int i = 0; i < lv0_num; ++i){
          if(lv0[i] -> state != RUNNABLE || lv0[i] -> priority != 0){
              // remove that proc from q1
              dequeue(lv0, lv0_num, i);
          }

          // Switch to chosen process.  It is the process's job
          // to release ptable.lock and then reacquire it
          // before jumping back to us.
      
          proc = lv0[i];
          // execute until completion
          while(proc -> state == RUNNABLE){
            switchuvm(proc);
            proc -> state = RUNNING;
            swtch(&cpu->scheduler, proc->context);
            //kernel regain control since here
            // increment ticks
            (proc -> ticks[0])++;
            // increment the waiting time of other proc
            check_promote(proc);
            // clear the wait time for proc
            proc -> wait_ticks[0] = 0;

            switchkvm();
          }
          // Process is done running for now.
          // It should have changed its p->state before coming back.
          proc = 0;
          //if any proc in lv0 gets promoted, jump to lv1
          if(jump_status)
            goto LV1_START;
      }
    }

    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state.
void
sched(void)
{
  int intena;

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(cpu->ncli != 1)
    panic("sched locks");
  if(proc->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = cpu->intena;
  swtch(&proc->context, cpu->scheduler);
  cpu->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  proc->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);
  
  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  if(proc == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }

  // Go to sleep.
  proc->chan = chan;
  proc->state = SLEEPING;
  sched();

  // Tidy up.
  proc->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];
  
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}


int
getpinfo(struct pstat* pstat)
{
    struct proc *p;
    int i;
    // Fill in the pstat
    acquire(&ptable.lock); 
    for(int i = 0; i < NPROC; ++i){
        p = &ptable.proc[i];
        pstat -> pid[i] = p -> pid;
        pstat -> priority[i] = p -> priority;
        pstat -> state[i] = p -> state;

        if(p -> state == UNUSED)
            pstat -> inuse[i] = 0;
        else
            pstat -> inuse[i] = 1;

        for(int j = 0; j < 4; ++j){
            pstat -> ticks[i][j] = p -> ticks[j];
            pstat -> wait_ticks[i][j] = p -> wait_ticks[j];
        }
    }
    
    release(&ptable.lock);
    return 1;
}

