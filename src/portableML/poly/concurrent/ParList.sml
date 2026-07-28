structure ParList :> ParList =
struct

fun get_first f =
  let
    fun first [] = NONE
      | first (x :: xs) =
          (case (f x handle Interrupt => raise Interrupt | _ => NONE) of
             SOME y => SOME y
           | NONE => first xs)
  in
    first
  end;

(* Losing workers are interrupted, never killed.  A worker can hold a
   process-global lock across an uninterruptible section (Refute's theory
   bracket is one), and Thread.kill terminates without unwinding, so a kill
   would leak that lock for the rest of the session.  A worker that has not
   exited when the grace period runs out is left to finish on its own. *)
val grace = Time.fromReal 5.0;

fun stop_threads threads =
  let
    val _ = List.app Standard_Thread.interrupt_unsynchronized threads
    val deadline = Time.now () + grace
    fun await thread =
      if not (Thread.isActive thread) then true
      else if Time.now () >= deadline then false
      else (OS.Process.sleep (Time.fromReal 0.001); await thread)
    val stragglers = List.length (List.filter (not o await) threads)
  in
    if stragglers = 0 then ()
    else
      Multithreading.tracing 1 (fn () =>
        "ParList.get_some: " ^ Int.toString stragglers ^
        " worker(s) still running after " ^ Time.toString grace ^ "s")
  end;

fun get_some f [] = NONE
  | get_some f [x] = get_first f [x]
  | get_some f xs =
      let
        val lock = Mutex.mutex ();
        val ready = ConditionVar.conditionVar ();
        val answer = ref NONE;
        val remaining = ref (List.length xs);
        val winner = ref (NONE: int option);
        val forked = ref ([] : (int * Thread.thread) list);

        fun synchronized e =
          Multithreading.synchronized "ParList.get_some" lock e;

        fun publish n result =
          synchronized (fn () =>
            (case result of
               SOME y =>
                 (case !answer of
                    NONE => (answer := SOME y; winner := SOME n)
                  | SOME _ => ())
             | NONE => ();
             remaining := !remaining - 1;
             if isSome (!answer) orelse !remaining = 0 then
               ConditionVar.signal ready
             else ()));

        (* Record each thread as it appears, so a failed fork - and any
           exception out of the wait below - can still stop the workers
           already running. *)
        fun fork_all _ [] = ()
          | fork_all n (x :: rest) =
              let
                val thread =
                  Standard_Thread.fork
                    {name = "ParList.get_some", stack_limit = NONE,
                     interrupts = true}
                    (fn () => publish n (f x handle _ => NONE));
                val _ = forked := (n, thread) :: !forked
              in
                fork_all (n + 1) rest
              end;

        fun stop keep =
          stop_threads (List.map #2
            (List.filter (fn (n, _) => keep <> SOME n) (!forked)));

        fun await () =
          synchronized (fn () =>
            let
              fun wait () =
                (case !answer of
                   SOME y => SOME y
                 | NONE =>
                     if !remaining = 0 then NONE
                     else
                       (ignore (Exn.release
                          (Multithreading.sync_wait NONE ready lock));
                        wait ()));
            in
              wait ()
            end);

        val _ = fork_all 0 xs handle exn => (stop NONE; raise exn);
        val result = await () handle exn => (stop NONE; raise exn);
        val _ = stop (!winner);
      in
        result
      end;

end;
