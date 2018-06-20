(* do some modifications *)
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val _ = Feedback.set_trace "Unicode" 1;
val _ = print "\n\nInitialisation complete ...\n\n";
