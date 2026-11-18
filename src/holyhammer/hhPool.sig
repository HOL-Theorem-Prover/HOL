signature hhPool =
sig
  (* A bounded pool of one-shot worker threads.  Every job runs on its own
     thread, started when one of the workers slots is free; at most
     `workers` jobs run at once and the others wait in submission order.
     All bookkeeping is protected by one mutex that is never held while a
     job runs or while a thread is waited for (ConditionVar.wait releases
     it).  The pool and its jobs are owned by the thread that created the
     pool. *)
  type pool
  type 'a job

  (* Starts a thread for a job.  The thread must run its function with
     interrupts deferred (the pool enables them for the job itself). *)
  type fork = (unit -> unit) -> Thread.thread
  val default_fork : fork

  (* with_pool {workers, fork} f applies f to a fresh pool of workers >= 1
     slots and, however f exits (an interrupt included), cancels every job
     that is still waiting or running, waits until all worker threads have
     finished and discards what the unconsumed jobs left, before returning
     or raising. *)
  val with_pool : {workers : int, fork : fork} -> (pool -> 'a) -> 'a

  (* submit pool {run, discard} admits a job and starts it as soon as a slot
     is free.  run is executed on a worker; an exception it raises is
     recorded for await.  discard is the owner's cleanup of what the job
     leaves behind; it runs on the thread that abandons or awaits the job,
     once the worker has stopped, and never while the worker can still
     write: on abandon (or the closing of the pool), and after an await
     that raises.  It must be idempotent and must not raise.  Raises if the pool is closed or the
     thread cannot be started (the job is then not admitted). *)
  val submit : pool -> {run : unit -> 'a, discard : unit -> unit} -> 'a job

  (* await job waits for the job to finish (interruptibly) and returns its
     result or raises its exception.  The result then belongs to the
     caller.  Await at most once per job. *)
  val await : 'a job -> 'a

  (* abandon job cancels a waiting job, interrupts a running one, waits for
     the worker to stop (not interruptibly) and discards what it left.  It
     is idempotent (the discard runs again, harmlessly) and may also follow
     an await, to clean up when the result was not safely received. *)
  val abandon : 'a job -> unit

  (* Jobs running now, jobs waiting for a slot, and the most that ever ran
     at once. *)
  val stats : pool -> {running : int, waiting : int, max_running : int}
end
