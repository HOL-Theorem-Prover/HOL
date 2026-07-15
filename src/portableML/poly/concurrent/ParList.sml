structure ParList :> ParList =
struct

fun get_first f =
  let
    fun first [] = NONE
      | first (x :: xs) =
          (case (f x handle _ => NONE) of
             SOME y => SOME y
           | NONE => first xs)
  in
    first
  end;

fun interruptkill thread =
  let
    val _ = Standard_Thread.interrupt_unsynchronized thread
    fun wait 0 =
          if Thread.isActive thread then Thread.kill thread else ()
      | wait n =
          if Thread.isActive thread then
            (OS.Process.sleep (Time.fromReal 0.001); wait (n - 1))
          else ()
  in
    wait 1000
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

        fun fork_all _ [] = []
          | fork_all n (x :: rest) =
              let
                val thread =
                  Standard_Thread.fork
                    {name = "ParList.get_some", stack_limit = NONE,
                     interrupts = true}
                    (fn () => publish n (f x handle _ => NONE));
              in
                (n, thread) :: fork_all (n + 1) rest
              end;

        fun await () =
          synchronized (fn () =>
            let
              fun wait () =
                (case !answer of
                   SOME y => SOME y
                 | NONE =>
                     if !remaining = 0 then NONE
                     else (ConditionVar.wait (ready, lock); wait ()));
            in
              wait ()
            end);

        val workers = fork_all 0 xs;
        val result = await ();
        fun stop (n, thread) =
          (case !winner of
             SOME m => if n = m then () else interruptkill thread
           | NONE => ());
        val _ = (case result of SOME _ => List.app stop workers | NONE => ());
      in
        result
      end;

end;
