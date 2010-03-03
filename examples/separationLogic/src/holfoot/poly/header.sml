(* load the state *)
val _ = HOL_Interactive.toggle_quietdec();
val state_file = (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/poly/holfoot.state");
val _ = PolyML.SaveState.loadState state_file handle Interrupt => raise Interrupt
                                                   | _ => (print
("Error: File '"^state_file^
  "'\ncould not be opened. Please run Holmake in directory\n'" ^
  Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/poly'!"))


(* do some modifications *)
val _ = HOL_Interactive.toggle_quietdec();
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val _ = Feedback.set_trace "Unicode" 1;
val _ = print "\n\nInitialisation complete ...\n\n";

(* done *)
val _ = HOL_Interactive.toggle_quietdec();
