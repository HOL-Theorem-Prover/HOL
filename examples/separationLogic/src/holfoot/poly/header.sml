(* do some modifications *)
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val _ = HOLFlags.set_bflag (Parse.avoid_unicode, false);
val _ = print "\n\nInitialisation complete ...\n\n";
