(* Kept outside the public [ParList] signature so [selftest.sml] can act
   from inside a fork's masked window, or from inside the mandatory join's
   poll.  Production leaves both at [NONE]. *)
structure ParList_Test =
struct
  val fork_hook = ref (NONE : (unit -> unit) option)
  val join_hook = ref (NONE : (unit -> unit) option)
end;

structure ParList :> ParList =
struct

fun get_first f =
  let
    fun first [] = NONE
      | first (x :: xs) =
          (case Exn.capture f x of
               Exn.Res (SOME y) => SOME y
             | Exn.Res NONE => first xs
             | Exn.Exn error =>
                 if Exn.is_interrupt error then Exn.reraise error
                 else first xs)
  in
    first
  end;

(* Defined in [Thread_Attributes]; re-exported for its existing callers. *)
val uninterruptible_wait = Thread_Attributes.uninterruptible_wait;

(* Losing workers are interrupted, never killed.  A worker can hold a
   process-global lock across an uninterruptible section, and Thread.kill
   terminates without unwinding, so a kill would leak that lock for the
   rest of the session.

   The join is mandatory: a straggler outliving the call would go on
   mutating state the caller has moved on from.  So the poll sleeps through
   [observe] instead of under a plain mask -- the caller waits exactly as
   long either way, but a Ctrl-C arriving mid-join is recorded rather than
   lost.  The caller already holds the mask; this runs under it.

   A job is free to answer its interrupt with [handle _], so [cancel] closes
   the job queue before the interrupts go out: swallowing one then costs the
   caller a job apiece, not the whole of the work that is left. *)
fun stop_threads observe cancel threads =
  let
    val _ = cancel ()
    val _ = List.app Standard_Thread.interrupt_unsynchronized threads
    fun poll () = Option.app (fn hook => hook ()) (!ParList_Test.join_hook)
  in
    Multithreading.join_threads observe poll threads
  end;

(* Run a bounded set of local workers without consulting the process-global
   thread policy.  [publish] and [finished] are called with [lock] held.
   Every claimed job is published, including exceptions, so [remaining]
   accurately describes the jobs that have not completed. *)
fun run_workers name worker_count f xs publish finished =
  let
    val lock = Mutex.mutex ();
    val ready = ConditionVar.conditionVar ();
    val interrupted = ref false;
    val cancelled = ref false;
    val remaining = ref (List.length xs);
    val indexed = ListPair.zip
      (List.tabulate (List.length xs, fn n => n), xs);
    val forked = ref ([] : Thread.thread list);
    val workers = Int.min (List.length xs, worker_count);
    val initial = List.take (indexed, workers);
    val pending = ref (List.drop (indexed, workers));

    fun synchronized e = Multithreading.with_lock lock e;

    (* Never cleared: [take] is the only place a job is handed out, so once
       the caller has stopped waiting no worker claims another one. *)
    fun cancel () = synchronized (fn () => cancelled := true);

    fun take () =
      synchronized (fn () =>
        if !cancelled orelse !interrupted orelse finished () then NONE
        else
          case !pending of
              [] => NONE
            | job :: rest => (pending := rest; SOME job));

    fun publish_result (index, result) =
      synchronized (fn () =>
        (case result of
             Exn.Exn error =>
               if Exn.is_interrupt error then interrupted := true
               else publish (index, result)
           | Exn.Res _ => publish (index, result);
         remaining := !remaining - 1;
         if !interrupted orelse finished () orelse !remaining = 0 then
           ConditionVar.signal ready
         else ()));

    fun perform (index, x) = publish_result (index, Exn.capture f x);

    fun take_later () =
      case take () of
          NONE => ()
        | SOME job => (perform job; take_later ());

    (* Each worker owns one initial job.  In particular, when the requested
       count equals the number of jobs, a fast worker cannot consume another
       backend's job before that backend's worker has started. *)
    fun worker job = (perform job; take_later ());

    (* Forking and recording each handle are atomic with respect to caller
       interrupts, so cleanup sees every worker even after a partial fork.
       Deferred rather than refused: a Ctrl-C landing between the two is
       answered once the handle is recorded, instead of being dropped. *)
    fun fork_one job =
      Thread_Attributes.uninterruptible_defer (fn _ => fn () =>
        let
          val _ = Option.app (fn hook => hook ()) (!ParList_Test.fork_hook)
          val thread =
            Standard_Thread.fork
              {name = name, stack_limit = NONE, interrupts = false}
              (fn () => Thread_Attributes.with_attributes
                Thread_Attributes.private_interrupts (fn _ => worker job));
          val _ = forked := thread :: !forked
        in
          ()
        end) ();

    fun fork_workers [] = ()
      | fork_workers (job :: jobs) =
          (fork_one job; fork_workers jobs);

    fun await () =
      synchronized (fn () =>
        let
          fun wait () =
            if !interrupted then raise Interrupt
            else if finished () orelse !remaining = 0 then ()
            else
              (ignore (Exn.release
                 (Multithreading.sync_wait NONE ready lock));
               wait ())
        in
          wait ()
        end);
  in
    (* Once waiting has returned or raised, mask interrupts until every local
       worker has unwound; no loser can outlive the operation.  [observe]
       covers both phases, so an interrupt in either is answered once the
       join is done rather than dropped. *)
    uninterruptible_wait (fn observe => fn () =>
      let
        val result = Exn.capture
          (observe (fn () => (fork_workers initial; await ()))) ()
        val _ = stop_threads observe cancel (!forked)
      in
        ignore (Exn.release result)
      end) ()
  end;

fun check_worker_count count =
  if count > 0 then ()
  else raise Fail "ParList: worker count must be positive";

fun map_with_workers worker_count f xs =
  let
    val _ = check_worker_count worker_count
  in
    case xs of
        [] => []
      | [x] => [f x]
      | _ =>
          let
            val results = ref []
            fun publish entry = results := entry :: !results
            val _ = run_workers "ParList.map_with_workers" worker_count f xs
              publish (fn () => false)
            fun release index =
              case List.find (fn (old_index, _) => old_index = index)
                     (!results) of
                  SOME (_, result) => Exn.release result
                | NONE => raise Fail "ParList: missing map result"
          in
            List.tabulate (List.length xs, release)
          end
  end;

fun get_some_with_workers worker_count f xs =
  let
    val _ = check_worker_count worker_count
  in
    case xs of
        [] => NONE
      | [x] => get_first f [x]
      | _ =>
          let
            val answer = ref NONE
            fun publish (_, Exn.Res (SOME y)) =
                  (case !answer of
                       NONE => answer := SOME y
                     | SOME _ => ())
              | publish _ = ()
            val _ = run_workers "ParList.get_some_with_workers" worker_count
              f xs publish (fn () => isSome (!answer))
          in
            !answer
          end
  end;

end;
