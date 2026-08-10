open HolKernel boolLib
local open smlExecute smlInfix smlLexer smlOpen smlParser smlPrettify
  smlRedirect smlTimeout smlParallel in end

(*
local open smlParallel in
  val l1 = List.tabulate (10,I);
  val _ = parmap_queue_extern 2 examplespec () l1;
end
*)

local open aiLib smlTimeout in
  fun f () = 5;
  val (_,t1) = add_time (timeout 1.0 f) ();
  fun loop () = loop ();
  fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => ();
  val (_,t2) = add_time g ();

  val cleanup_done = ref false;
  fun cleanup_worker () =
    (loop () handle Interrupt =>
      (OS.Process.sleep (Time.fromReal 0.05);
       cleanup_done := true;
       raise Interrupt));
  val _ = (timeout 0.01 cleanup_worker () handle FunctionTimeout => ());
  val _ = if !cleanup_done then ()
          else raise Fail "timeout interrupted worker cleanup";
end
