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

int q_pri = 3;

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
// /*
  //modified for MLFQ
  p -> priority = 3;
  for(int i = 0; i < NLAYER; ++i){
      p -> ticks[i] = 0;
      p -> wait_ticks[i] = 0;
      p -> ticks_op[i] = 0;
      p -> wait_ticks_op[i] = 0;
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
 //*/ 

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

// update the waitting time of other process
int
check_promote(struct proc* proc){
    // we clear the proc's waitting time before intering the routine
    // The wait time of proc shouldn't be incremented at all
    // However, for simplicity, the procs wait_ticks will be incremented to one with following loops
    // Which doesn't matter since time_ticks == 1 doesn't trigger any promotion
    // We clear the proc's waiting time again when exitting the routine to compensate it
    
    // update lv3, no need to promoted
    for(int i = 0; i < lv3_num; ++i){
        (lv3[i] -> wait_ticks[3])++;
        (lv3[i] -> wait_ticks_op[3])++;
    }

    // update lv2
    for(int i = 0; i < lv2_num; ++i){
        (lv2[i] -> wait_ticks[2])++;
        (lv2[i] -> wait_ticks_op[2])++;
        // if the wait time is greater than 10 * LV2_TIME, promote
        if( (lv2[i] -> wait_ticks_op[2]) >= 10 * LV2_TIME ){
            (lv2[i] -> priority)++;
            cprintf("lv2 promote to lv3\n");
            // clear ticks and wait_ticks of the prev priority
            (lv2[i] -> ticks_op[2]) = 0;
            (lv2[i] -> wait_ticks_op[2]) = 0;
            // remove process from lv2, put it to lv3
            lv3[lv3_num] = lv2[i];
            lv3_num++;
            dequeue(lv2, lv2_num, i);
            lv2_num--;
        }
    }
    // update lv1
    for(int i = 0; i < lv1_num; ++i){
        (lv1[i] -> wait_ticks[1])++;
        (lv1[i] -> wait_ticks_op[1])++;
        // if the wait time is greater than 10 * LV1_TIME, promote
        if( (lv1[i] -> wait_ticks_op[1]) >= 10 * LV1_TIME ){
            (lv1[i] -> priority)++;
            // clear ticks and wait_ticks of the prev priority
            (lv1[i] -> ticks_op[1]) = 0;
            (lv1[i] -> wait_ticks_op[1]) = 0;
            // remove process from lv1, put it to lv2
            lv2[lv2_num] = lv1[i];
            lv2_num++;
            dequeue(lv1, lv1_num, i);
            lv1_num--;
        }
    }
    // update lv0
    for(int i = 0; i < lv0_num; ++i){
        (lv0[i] -> wait_ticks[0])++;
        (lv0[i] -> wait_ticks_op[0])++;
        // if the wait time is greater than 500, promote
        if( (lv0[i] -> wait_ticks_op[0]) >= 500 ){
            (lv0[i] -> priority)++;
            // clear ticks and wait_ticks of the prev priority
            (lv0[i] -> ticks_op[0]) = 0;
            (lv0[i] -> wait_ticks_op[0]) = 0;
            // remove process from lv0, put it to lv1
            lv1[lv1_num] = lv0[i];
            lv1_num++;
            dequeue(lv0, lv0_num, i);
            lv0_num--;
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
  for(;;){
      // Enable interrupts on this processor.
    sti();

    
    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        if(p->state != RUNNABLE)
            continue;
        // if you find a runnable
        // add to lv3
        lv3[lv3_num] = p;
        lv3_num++;
    }

    // search four priority queue until find a runnable proc
    // search lv3 first
    // if find, execute 
    // After exexuting, goto the start of the proc search (start from lv3)
    SEARCH:
    while(lv3_num > 0){

    for(int lv3i = 0; lv3i < lv3_num; lv3i++){
         // Switch to chosen process.  It is the process's job
         // to release ptable.lock and then reacquire it
         // before jumping back to us.
            //int temp_ticks = 0;
            proc = lv3[lv3i];
            switchuvm(lv3[lv3i]);
            lv3[lv3i]->state = RUNNING;
            swtch(&cpu->scheduler, proc->context);
            switchkvm();
            // kernel regain control
            // 
            // clear the wait time for proc
            lv3[lv3i] -> wait_ticks_op[3] = 0;
            lv3[lv3i] -> wait_ticks[3] = 0;
            // update wait time for other proc
            check_promote(lv3[lv3i]);
            // increment wait by 1 (See check_promote routine)
            lv3[lv3i] -> wait_ticks_op[3] = 0;
            lv3[lv3i] -> wait_ticks[3] = 0;

            // increment ticks
            //cprintf("[PID %d] has done running on level 3, ticks %d\n ", pp -> pid, pp -> ticks[3]);
            (lv3[lv3i] -> ticks_op[3])++;
            (lv3[lv3i] -> ticks[3])++;

            /*
            // check if proc is not RUNNABLE
            // if not, deque from lv3
            if(lv3[lv3i] -> state != RUNNABLE){
                dequeue(lv3, lv3_num, lv3i);
                lv3_num--;
                proc = 0;
                continue;
            }
            */

            if( (lv3[lv3i] -> ticks_op[3]) >= LV3_TIME){
                lv3[lv3i] -> priority = 2;
                lv3[lv3i] -> ticks_op[3] = 0;
                lv3[lv3i] -> wait_ticks_op[3] = 0;
                lv3[lv3i] -> wait_ticks[3] = 0;
                // check if proc is not RUNNABLE
                // if not, deque from lv3
                if(lv3[lv3i] -> state != RUNNABLE){
                    dequeue(lv3, lv3_num, lv3i);
                    lv3_num--;
                    proc = 0;
                    continue;
                }
                // add the proc to lv2
                // remove the proc from lv3
                lv2[lv2_num] = lv3[lv3i];
                lv2_num++;
                dequeue(lv3, lv3_num, lv3i);
                lv3_num--;
                //
            }
            // check if proc is not RUNNABLE
            // if not, deque from lv3
            else if(lv3[lv3i] -> state != RUNNABLE){
                dequeue(lv3, lv3_num, lv3i);
                lv3_num--;
            }
         // Process is done running for now.
         // It should have changed its p->state before coming back.
         //
         proc = 0;
         //search again
    }
    }
    while(lv2_num > 0){
    for(int lv2i = 0; lv2i < lv2_num; lv2i++ ){
        // Switch to chosen process.  It is the process's job
        // to release ptable.lock and then reacquire it
        // before jumping back to us.
           proc = lv2[lv2i];
           switchuvm(lv2[lv2i]);
           lv2[lv2i]->state = RUNNING;
           swtch(&cpu->scheduler, proc->context);
           switchkvm();
           // kernel regain control
           // 
           // clear the wait time for proc
           lv2[lv2i] -> wait_ticks_op[2] = 0;
           lv2[lv2i] -> wait_ticks[2] = 0;
           // update wait time for other proc
           check_promote(lv2[lv2i]);
           // increment wait by 1 (See check_promote routine)
           lv2[lv2i] -> wait_ticks_op[2] = 0;
           lv2[lv2i] -> wait_ticks[2] = 0;
           // increment ticks
           (lv2[lv2i] -> ticks_op[2])++;
           (lv2[lv2i] -> ticks[2])++;
           // check if proc is not RUNNABLE
           // if not, deque from lv1
           /*
           if(lv2[lv2i] -> state != RUNNABLE){
                dequeue(lv2, lv2_num, lv2i);
                lv2_num--;
                proc = 0;
                goto SEARCH;
           }
           */

           if( (lv2[lv2i] -> ticks_op[2]) >= LV2_TIME){
               // de-mote proc priority
               lv2[lv2i] -> priority = 1;
               lv2[lv2i] -> ticks_op[2] = 0;
               lv2[lv2i] -> wait_ticks_op[2] = 0;
               lv2[lv2i] -> wait_ticks[2] = 0;
               // check if proc is not RUNNABLE
               // if not, deque from lv2
               if(lv2[lv2i] -> state != RUNNABLE){
                   dequeue(lv2, lv2_num, lv2i);
                   lv2_num--;
                   proc = 0;
                   continue;
               }
               // add the proc to lv1
               // remove the proc from lv2
               lv1[lv1_num] = lv2[lv2i];
               lv1_num++;
               dequeue(lv2, lv2_num, lv2i);
               lv2_num--;
           }
               //
               // check if proc is not RUNNABLE
            // if not, deque from lv1
           else if(lv2[lv2i] -> state != RUNNABLE){
                dequeue(lv2, lv2_num, lv2i);
                lv2_num--;
           }
        // Process is done running for now.
        // It should have changed its p->state before coming back.
        //
        proc = 0;
        //search again
        goto SEARCH;
    }
    }
    while(lv1_num > 0){ 
    for(int lv1i = 0; lv1i < lv1_num; lv1i++ ){
        // Switch to chosen process.  It is the process's job
        // to release ptable.lock and then reacquire it
        // before jumping back to us.
           proc = lv1[lv1i];
           switchuvm(lv1[lv1i]);
           lv1[lv1i]->state = RUNNING;
           swtch(&cpu->scheduler, proc->context);
           switchkvm();
           // kernel regain control
           //
           // clear the wait time for proc
           lv1[lv1i] -> wait_ticks_op[1] = 0;
           lv1[lv1i] -> wait_ticks[1] = 0;
           // update wait time for other proc
           check_promote(lv1[lv1i]);
           // increment wait by 1 (See check_promote routine)
           lv1[lv1i] -> wait_ticks_op[1] = 0;
           lv1[lv1i] -> wait_ticks[1] = 0;
           // increment ticks
           (lv1[lv1i] -> ticks_op[1])++;
           (lv1[lv1i] -> ticks[1])++;

           /*
           // check if proc is not RUNNABLE
           // if not, deque from lv1
           if(lv1[lv1i] -> state != RUNNABLE){
                dequeue(lv1, lv1_num, lv1i);
                lv1_num--;
                proc = 0;
                goto SEARCH;
           }
           */
           if( (lv1[lv1i] -> ticks_op[1]) >= LV1_TIME){
               // de-mote proc priority
               lv1[lv1i] -> priority = 0;
               lv1[lv1i] -> ticks_op[1] = 0;
               lv1[lv1i] -> wait_ticks_op[1] = 0;
               lv1[lv1i] -> wait_ticks[1] = 0;
               // check if proc is not RUNNABLE
               // if not, deque from lv2
               if(lv1[lv1i] -> state != RUNNABLE){
                   dequeue(lv1, lv1_num, lv1i);
                   lv1_num--;
                   proc = 0;
                   continue;
               }

               // add the proc to lv0
               // remove the proc from lv1
               lv0[lv0_num] = lv1[lv1i];
               lv0_num++;
               dequeue(lv1, lv1_num, lv1i);
               lv1_num--;
           }
           // check if proc is not RUNNABLE
           // if not, deque from lv1
           else if(lv1[lv1i] -> state != RUNNABLE){
                dequeue(lv1, lv1_num, lv1i);
                lv1_num--;
           }
        // Process is done running for now.
        // It should have changed its p->state before coming back.
        //
        proc = 0;
        //search again
        goto SEARCH;
    }
    }

    // every time in lv0, start with the first proc (FIFO)
    while(lv0_num > 0){
           // Switch to chosen process.  It is the process's job
           // to release ptable.lock and then reacquire it
           // before jumping back to us.
           int lv0i = 0;
           proc = lv0[lv0i];
           switchuvm(lv0[lv0i]);
           lv0[lv0i]->state = RUNNING;
           // while proc is RUNNING, keep scheduling it till it finishes (FIFO)
           swtch(&cpu->scheduler, proc->context);
           switchkvm();
           // kernel regain control
           // clear the wait time for proc
           lv0[lv0i] -> wait_ticks_op[0] = 0;
           lv0[lv0i] -> wait_ticks[0] = 0;
           // update wait time for other proc
           check_promote(lv0[lv0i]);
           // increment wait by 1 (See check_promote routine)
           lv0[lv0i] -> wait_ticks_op[0] = 0;
           // increment ticks
           (lv0[lv0i] -> ticks_op[0])++;
           (lv0[lv0i] -> ticks[0])++;
           // check if proc is not RUNNABLE
           // if not, deque from lv0
           if(lv0[lv0i] -> state != RUNNABLE){
                dequeue(lv0, lv0_num, lv0i);
                lv0_num--;
                proc = 0;
                goto SEARCH;
           }
        // Process is done running for now.
        // It should have changed its p->state before coming back.
        proc = 0;
        //search again
        goto SEARCH;
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
    if(p->state == SLEEPING && p->chan == chan){
      p->state = RUNNABLE;
      if(p -> priority == 3){
        lv3[lv3_num] = p;
        lv3_num++;
      }
      else if(p -> priority == 2){
        lv2[lv2_num] = p;
        lv2_num++;
      }
      else if(p -> priority == 1){
        lv1[lv1_num] = p;
        lv1_num++;
      }
      else if(p -> priority == 0){
        lv0[lv0_num] = p;
        lv0_num++;
      }
    }
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
      if(p->state == SLEEPING){
        p->state = RUNNABLE;
        /*
      // we add newly arrived proc to its priority level
      if(p -> priority == 3){
        lv3[lv3_num] = p;
        lv3_num++;
      }
      else if(p -> priority == 2){
        lv2[lv2_num] = p;
        lv2_num++;
      }
      else if(p -> priority == 1){
        lv1[lv1_num] = p;
        lv1_num++;
      }
      else if(p -> priority == 0){
        lv0[lv0_num] = p;
        lv0_num++;
      }
      */
      }
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
    return 0;
}

