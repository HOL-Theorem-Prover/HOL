local open smlExecute smlInfix smlLexer smlOpen smlParser smlPrettify
  smlRedirect smlTimeout smlParallel in end

local open smlParallel in
  val l1 = List.tabulate (100,I);
  val _ = parmap_queue_extern 2 idspec () l1;
end

local open aiLib smlTimeout in
  fun f () = 5;
  val (_,t1) = add_time (timeout 1.0 f) ();
  fun loop () = loop ();
  fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => ();
  val (_,t2) = add_time g ();
end
