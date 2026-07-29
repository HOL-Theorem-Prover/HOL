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

(* Losing workers are interrupted, never killed.  A worker can hold a
   process-global lock across an uninterruptible section (Refute's theory
   bracket is one), and Thread.kill terminates without unwinding, so a kill
   would leak that lock for the rest of the session. *)
fun stop_threads threads =
  Thread_Attributes.uninterruptible (fn _ => fn () =>
    let
      val _ = List.app Standard_Thread.interrupt_unsynchronized threads
      fun await thread =
        if not (Thread.isActive thread) then ()
        else (OS.Process.sleep (Time.fromReal 0.001); await thread)
    in
      List.app await threads
    end) ();

fun get_some f [] = NONE
  | get_some f [x] = get_first f [x]
  | get_some f xs =
      if Multithreading.max_threads () <= 1 then get_first f xs
      else
        let
          val lock = Mutex.mutex ();
          val ready = ConditionVar.conditionVar ();
          val answer = ref NONE;
          val interrupted = ref false;
          val remaining = ref (List.length xs);
          val pending = ref (ListPair.zip
            (List.tabulate (List.length xs, fn n => n), xs));
          val forked = ref ([] : Thread.thread list);
          val workers = Int.min (List.length xs, Multithreading.max_threads ());

          fun synchronized e =
            Multithreading.synchronized "ParList.get_some" lock e;

          fun take () =
            synchronized (fn () =>
              case !answer of
                  SOME _ => NONE
                | NONE =>
                    if !interrupted then NONE
                    else
                      (case !pending of
                           [] => NONE
                         | job :: rest => (pending := rest; SOME job)));

          fun publish (result, was_interrupted) =
            synchronized (fn () =>
              (if was_interrupted then interrupted := true
               else
                 case result of
                     SOME y =>
                       (case !answer of
                            NONE => answer := SOME y
                          | SOME _ => ())
                   | NONE => ();
               remaining := !remaining - 1;
               if isSome (!answer) orelse !interrupted orelse
                  !remaining = 0 then
                 ConditionVar.signal ready
               else ()));

          fun worker () =
            case take () of
                NONE => ()
              | SOME (_, x) =>
                  let
                    (* Every claimed job must be published.  In particular,
                       letting [Interrupt] escape here would leave [remaining]
                       positive and make the parent wait forever. *)
                    val result = Exn.capture f x
                    val _ =
                      case result of
                          Exn.Res value => publish (value, false)
                        | Exn.Exn error =>
                            publish (NONE, Exn.is_interrupt error)
                  in
                    worker ()
                  end;

          (* Forking and publishing handles are atomic with respect to caller
             interrupts, so cleanup always sees every started worker. *)
          fun fork_one () =
            Thread_Attributes.uninterruptible (fn _ => fn () =>
              let
                val thread =
                  Standard_Thread.fork
                    {name = "ParList.get_some", stack_limit = NONE,
                     interrupts = false}
                    (fn () => Thread_Attributes.with_attributes
                      Thread_Attributes.private_interrupts (fn _ => worker ()));
                val _ = forked := thread :: !forked
              in
                ()
              end) ();

          fun fork_workers 0 = ()
            | fork_workers count = (fork_one (); fork_workers (count - 1));

          fun await () =
            synchronized (fn () =>
              let
                fun wait () =
                  case !answer of
                      SOME y => SOME y
                    | NONE =>
                        if !interrupted then raise Interrupt
                        else if !remaining = 0 then NONE
                        else
                          (ignore (Exn.release
                             (Multithreading.sync_wait NONE ready lock));
                           wait ())
              in
                wait ()
              end);
        in
          (* Once wait has returned or raised, mask interrupts until every
             local worker has unwound; no loser can outlive this race. *)
          Thread_Attributes.uninterruptible (fn restore => fn () =>
            let
              val result = Exn.capture
                (restore (fn () => (fork_workers workers; await ()))) ()
              val _ = stop_threads (!forked)
            in
              Exn.release result
            end) ()
        end;

end;
