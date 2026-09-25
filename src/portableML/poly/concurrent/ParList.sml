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

(* Masking interrupts the plain way does not defer a Ctrl-C, it loses one.
   Poly/ML retains a directed [Thread.interrupt] and delivers it when the
   mask lifts, but HOL raises Ctrl-C as [Thread.broadcastInterrupt], and a
   broadcast simply skips a thread whose broadcast flag is clear, recording
   nothing; [Thread_Attributes.no_interrupts] clears that flag along with
   the rest.  A wait that must run to completion therefore has to stay
   observant while it waits.

   [uninterruptible_defer f x] is [Thread_Attributes.uninterruptible] with
   the broadcast flag left as the caller had it: interrupts are deferred
   rather than refused, so a broadcast arriving inside the masked region is
   held and delivered when the caller's attributes come back, at a [restore]
   step or on the way out.  Poly/ML has no attribute constant for that
   combination, hence the raw [Thread.setAttributes]; it writes the
   interrupt-state bits only. *)
fun uninterruptible_defer f x =
  let
    val saved = Thread_Attributes.get_attributes ()
    val _ =
      Thread.setAttributes [Thread.InterruptState Thread.InterruptDefer]
    fun restore g y = Thread_Attributes.with_attributes saved (fn _ => g y)
    val result = Exn.capture (f restore) x
    val _ = Thread_Attributes.set_attributes saved
  in
    Exn.release result
  end;

(* [Multithreading.synchronized] masks with the plain [uninterruptible], so
   the [Mutex.lock] a caller queues on is one more place its Ctrl-C is lost;
   this is otherwise the same function without the tracing. *)
fun with_lock lock e =
  Exn.release (uninterruptible_defer (fn restore => fn () =>
    let
      val _ = Mutex.lock lock
      val result = Exn.capture (restore e) ()
      val _ = Mutex.unlock lock
    in
      result
    end) ());

(* [uninterruptible_wait f x] runs [f observe x] masked, as
   [Thread_Attributes.uninterruptible] does, except that [observe g y] runs
   [g y] under the caller's own attributes, so a broadcast arriving during
   that step is delivered.  [observe] answers [SOME] with the result, or
   records the interrupt and answers [NONE]; once one is recorded, later
   steps run masked, one being all that is needed.  A recorded interrupt is
   raised after [f] has returned, so the wait still runs to completion.  An
   exception from [f] itself wins and the recorded interrupt is dropped: it
   is [f]'s own outcome the caller is waiting on, and control is leaving for
   the top level under either exception anyway. *)
fun uninterruptible_wait f =
  Thread_Attributes.uninterruptible (fn restore => fn x =>
    let
      val pending = ref false
      fun observe g y =
        if !pending then SOME (g y)
        else
          (SOME (restore g y)
           handle Interrupt => (pending := true; NONE))
      val result = Exn.capture (f observe) x
    in
      case result of
          Exn.Res value => if !pending then raise Interrupt else value
        | Exn.Exn _ => Exn.release result
    end);

(* Losing workers are interrupted, never killed.  A worker can hold a
   process-global lock across an uninterruptible section (Refute's theory
   bracket is one), and Thread.kill terminates without unwinding, so a kill
   would leak that lock for the rest of the session.

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
    fun poll () =
      (Option.app (fn hook => hook ()) (!ParList_Test.join_hook);
       OS.Process.sleep (Time.fromReal 0.001))
    fun await thread =
      if not (Thread.isActive thread) then ()
      else (ignore (observe poll ()); await thread)
  in
    List.app await threads
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

    fun split 0 rest front = (List.rev front, rest)
      | split count (job :: rest) front =
          split (count - 1) rest (job :: front)
      | split _ [] front = (List.rev front, []);
    val (initial, later) = split workers indexed [];
    val pending = ref later;

    fun synchronized e = with_lock lock e;

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
      uninterruptible_defer (fn _ => fn () =>
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

fun get_some f [] = NONE
  | get_some f [x] = get_first f [x]
  | get_some f xs =
      if Multithreading.max_threads () <= 1 then get_first f xs
      else get_some_with_workers (Multithreading.max_threads ()) f xs;

end;
