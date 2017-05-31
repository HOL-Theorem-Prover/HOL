(* load the state *)
val _ = PolyML.print_depth 0;
let
  val state_file = Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/poly/holfoot.state"
  val _ = PolyML.SaveState.loadState state_file handle _ => (
    print ("Error: File '"^state_file^ " could not be opened.");
    OS.Process.exit OS.Process.failure);
in
  ()
end;

(* do some modifications *)
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val _ = Feedback.set_trace "Unicode" 1;
val _ = print "\n\nInitialisation complete ...\n\n";
