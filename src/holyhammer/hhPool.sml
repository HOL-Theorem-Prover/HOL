(* ========================================================================= *)
(* FILE          : hhPool.sml                                                *)
(* DESCRIPTION   : bounded pool of one-shot worker threads                   *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

structure hhPool :> hhPool =
struct

datatype 'a state =
    Waiting
  | Running of Thread.thread
  | Finished of 'a Exn.result
  | Taken

type pool =
  {lock : Mutex.mutex, changed : ConditionVar.conditionVar, limit : int,
   fork : (unit -> unit) -> Thread.thread,
   running : int ref, max_running : int ref, next : int ref,
   threads : Thread.thread list ref,
   waiting : (int * (unit -> unit)) list ref,
   abandoners : (unit -> unit) list ref, closed : bool ref}

type fork = (unit -> unit) -> Thread.thread

type 'a job =
  {pool : pool, id : int, state : 'a state ref, cancelled : bool ref,
   discard : unit -> unit}

fun default_fork f =
  Thread.fork (f,
    [Thread.InterruptState Thread.InterruptDefer,
     Thread.EnableBroadcastInterrupt false])

(* Interrupts are deferred (not refused: a broadcast Ctrl-C is held, not
   dropped) while the mutex is held, so no update of the bookkeeping is cut
   short, and one that arrived is raised once the mutex has been released.
   A wait is the only place where a pending interrupt can be taken, and only
   if interruptible: it then arrives with the mutex held, which is released
   before the exception propagates.  An uninterruptible wait runs to
   completion and answers an interrupt afterwards. *)
fun locked_wait ({lock, changed, ...} : pool) interruptible check =
  Thread_Attributes.uninterruptible_defer (fn restore => fn () =>
    let
      val _ = Mutex.lock lock
      fun wait () =
        if interruptible then
          Exn.capture (restore (fn () =>
            Multithreading.sync_wait NONE changed lock)) ()
        else Exn.capture (fn () =>
          (ConditionVar.wait (changed, lock); Exn.Res true)) ()
      fun loop () =
        case Exn.capture check () of
            Exn.Exn exn => (Mutex.unlock lock; raise exn)
          | Exn.Res (SOME value) => (Mutex.unlock lock; value)
          | Exn.Res NONE =>
              (case wait () of
                   Exn.Res (Exn.Res _) => loop ()
                 | Exn.Res (Exn.Exn exn) => (Mutex.unlock lock; raise exn)
                 | Exn.Exn exn => (Mutex.unlock lock; raise exn))
    in
      loop ()
    end) ()

fun locked pool f = locked_wait pool false (fn () => SOME (f ()))

fun broadcast ({changed, ...} : pool) = ConditionVar.broadcast changed

(* Called with the mutex held.  Starts the thread and registers the job in
   one step; the thread first takes the mutex, so it cannot run before it
   is registered.  The slot is counted only once the thread exists. *)
fun start (pool as {running, max_running, fork, ...} : pool) state run =
  let
    val thread = fork (fn () => worker pool state run)
  in
    state := Running thread;
    #threads pool := thread :: !(#threads pool);
    running := !running + 1;
    max_running := Int.max (!max_running, !running)
  end

(* The always-run finalizer of a worker: it records the outcome, frees the
   slot, hands the slot to the next waiting job and wakes every waiter, all
   in one locked step, whatever the job did. *)
and worker pool state run =
  let
    val _ = locked pool (fn () => ())
    val outcome = Exn.capture (fn () =>
      Thread_Attributes.with_attributes Thread_Attributes.private_interrupts
        (fn _ => run ())) ()
  in
    locked pool (fn () =>
      (state := Finished outcome;
       #running pool := !(#running pool) - 1;
       start_waiting pool;
       broadcast pool))
  end

and start_waiting (pool as {running, limit, waiting, closed, ...} : pool) =
  case !waiting of
      (_, launch) :: rest =>
        if !closed orelse !running >= limit then ()
        else (waiting := rest; launch (); start_waiting pool)
    | [] => ()

(* A job leaves the bookkeeping exactly once, as Taken.  release_state
   returns NONE while the worker has not finished (the first such call
   interrupts a running job and the caller waits for the worker to
   finish) and SOME () once the job is taken.  abandon discards even a job
   that was awaited: an interrupt can strike between the hand-over of a
   result and its registration by the owner, who then abandons it. *)
fun release_state ({pool, id, state, cancelled, ...} : 'a job) =
  case !state of
      Waiting =>
        (#waiting pool := List.filter (fn (other, _) => other <> id)
           (!(#waiting pool));
         state := Taken; SOME ())
    | Running thread =>
        (if !cancelled then ()
         else (cancelled := true;
               Thread.interrupt thread handle Thread _ => ());
         NONE)
    | Finished _ => (state := Taken; SOME ())
    | Taken => SOME ()

fun abandon (job as {pool, discard, ...} : 'a job) =
  let
    val waited = Exn.capture (fn () =>
      locked_wait pool false (fn () => release_state job)) ()
    val _ = discard () handle _ => ()
  in
    ignore (Exn.release waited)
  end

fun submit (pool as {next, waiting, running, limit, closed, abandoners, ...}
              : pool) {run, discard} =
  locked pool (fn () =>
    let
      val _ = if !closed then raise Fail "hhPool: the pool is closed" else ()
      val id = !next
      val _ = next := id + 1
      val state = ref Waiting
      val job = {pool = pool, id = id, state = state,
                 cancelled = ref false, discard = discard}
      fun launch () =
        start pool state run
        handle exn => state := Finished (Exn.Exn exn)
    in
      if !running < limit then start pool state run
      else waiting := !waiting @ [(id, launch)];
      abandoners := (fn () => abandon job) :: !abandoners;
      job
    end)

fun await (job as {pool, state, discard, ...} : 'a job) =
  let
    val outcome = locked_wait pool true (fn () =>
      case !state of
          Finished outcome => (state := Taken; SOME outcome)
        | Taken => raise Fail "hhPool.await: result already consumed"
        | _ => NONE)
  in
    case outcome of
        Exn.Res value => value
      | Exn.Exn exn => ((discard () handle _ => ()); raise exn)
  end

fun stats pool =
  locked pool (fn () =>
    {running = !(#running pool), waiting = length (!(#waiting pool)),
     max_running = !(#max_running pool)})

(* No new job starts, every admitted job is abandoned (so every job has
   finished and its leftovers are discarded) and then every thread that was
   started is joined (polled until it is no longer active, with interrupts
   deferred) before the pool is dropped.  An interrupt that arrives meanwhile
   is raised only after all of that; a job's own exception is not. *)
fun close (pool as {closed, abandoners, threads, ...} : pool) =
  Thread_Attributes.uninterruptible_defer (fn _ => fn () =>
    let
      val jobs = locked pool (fn () => (closed := true; !abandoners))
      val results = map (fn abandon_job => Exn.capture abandon_job ()) jobs
      val started = locked pool (fn () => !threads)
      val joined = Exn.capture (fn () =>
        Multithreading.join_threads (fn g => fn y => SOME (g y)) (fn () => ())
          started) ()
    in
      app (ignore o Exn.release) results; Exn.release joined
    end) ()

fun with_pool {workers, fork} f =
  Portable.bracket
    (fn () =>
       {lock = Mutex.mutex (), changed = ConditionVar.conditionVar (),
        limit = Int.max (1, workers), fork = fork, running = ref 0,
        max_running = ref 0, next = ref 0, threads = ref [], waiting = ref [],
        abandoners = ref [], closed = ref false} : pool)
    close f

end
