(* Interrupt regressions for [ParList].  HOL delivers Ctrl-C as
   [Thread.broadcastInterrupt], which a thread whose broadcast flag is clear
   does not even record, so each test plants the broadcast in the window it
   is about through [ParList_Test] rather than racing it. *)

fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure);

fun tprint s = print (StringCvt.padRight #" " 70 s);

fun ok () = print "OK\n";

fun sleep secs = OS.Process.sleep (Time.fromReal secs);

fun wait_until p = if p () then () else (sleep 0.001; wait_until p);

(* Each test runs with the attributes HOL's REPL gives the top level.
   Between tests the top level defers with the broadcast flag clear, so a
   broadcast still in flight cannot land on an unrelated step. *)
val deferred =
  [Thread.EnableBroadcastInterrupt false,
   Thread.InterruptState Thread.InterruptDefer];

val _ = Thread.setAttributes deferred;

fun clear_pending () =
  (Thread.setAttributes [Thread.InterruptState Thread.InterruptSynch];
   (Thread.testInterrupt () handle Interrupt => ());
   Thread.setAttributes deferred);

fun as_repl e =
  Thread_Attributes.with_attributes Thread_Attributes.public_interrupts
    (fn _ => Exn.capture e ());

fun check_interrupt what outcome =
  case outcome of
      Exn.Exn error =>
        if Exn.is_interrupt error then ()
        else die ("Unexpected exception: " ^ General.exnMessage error)
    | Exn.Res _ => die what;

(* A broadcast arriving while [fork_one] holds its mask must survive it.
   Under a mask that clears the broadcast flag nothing records the Ctrl-C
   and the whole map runs to completion. *)
val _ = tprint "Ctrl-C inside the fork window is not lost";

val fork_window =
  let
    val _ = ParList_Test.fork_hook :=
      SOME (fn () => Thread.broadcastInterrupt ())
    val outcome = as_repl (fn () =>
      ParList.map_with_workers 2 (fn n => n) (List.tabulate (8, fn n => n)))
    val _ = ParList_Test.fork_hook := NONE
    val _ = clear_pending ()
  in
    outcome
  end;

val _ = check_interrupt "the fork window dropped the broadcast" fork_window;
val _ = ok ();

(* A job that swallows its interrupt must not go on draining the queue: the
   caller's Ctrl-C closes it, so each worker costs one more job at most.
   Every job blocks until the join is under way, which puts the whole queue
   behind the point where the caller has given up waiting. *)
val _ = tprint "Ctrl-C at the join stops jobs being handed out";

val (join_window, handed_out) =
  let
    val total = 200
    val counter = Mutex.mutex ()
    val started = ref 0
    val go = ref false
    val stop = ref false
    fun bump () =
      (Mutex.lock counter; started := !started + 1; Mutex.unlock counter)
    fun job n =
      (Thread.setAttributes [Thread.InterruptState Thread.InterruptDefer];
       bump ();
       wait_until (fn () => !go);
       n)
    fun ctrl_c () =
      if !stop then ()
      else (Thread.broadcastInterrupt (); sleep 0.005; ctrl_c ())
    val _ = ParList_Test.join_hook := SOME (fn () => go := true)
    val user = Standard_Thread.fork
      {name = "ParList.selftest", stack_limit = NONE, interrupts = false}
      (fn () => (wait_until (fn () => !started >= 2); ctrl_c ()))
    val outcome = as_repl (fn () =>
      ParList.map_with_workers 2 job (List.tabulate (total, fn n => n)))
    val _ = stop := true
    val _ = ParList_Test.join_hook := NONE
    val _ = wait_until (fn () => not (Thread.isActive user))
    val _ = clear_pending ()
  in
    (outcome, !started)
  end;

val _ = check_interrupt "the caller's Ctrl-C was swallowed" join_window;
val _ =
  if handed_out = 2 then ok ()
  else die ("jobs kept being handed out: " ^ Int.toString handed_out ^
            " started, expected 2");

val _ = tprint "map_with_workers keeps input order";
val _ =
  if ParList.map_with_workers 3 (fn n => n * n) (List.tabulate (20, fn n => n))
     = List.tabulate (20, fn n => n * n)
  then ok () else die "wrong results";

val _ = tprint "get_some_with_workers finds an answer";
val _ =
  case ParList.get_some_with_workers 3
         (fn n => if n = 17 then SOME n else NONE)
         (List.tabulate (20, fn n => n)) of
      SOME 17 => ok ()
    | _ => die "wrong answer";
