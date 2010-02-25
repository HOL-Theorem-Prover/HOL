(* load the state *)
val _ = HOL_Interactive.toggle_quietdec();
val state_file = (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/holfoot.state");
val _ = PolyML.SaveState.loadState state_file;

(* do some modifications *)
val _ = HOL_Interactive.toggle_quietdec();
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val _ = print "\n\nInitialisation complete ...\n\n";

(* done *)
val _ = HOL_Interactive.toggle_quietdec();
