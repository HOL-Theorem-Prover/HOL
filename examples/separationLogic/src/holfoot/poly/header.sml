(* load the state *)
val _ = PolyML.print_depth 0
val state_file = "holfoot.state"
val _ = PolyML.SaveState.loadState "holfoot.state"
        handle _ => (print
                       ("Error: File '"^state_file^ " could not be opened.");
                     OS.Process.exit OS.Process.failure);

(* do some modifications *)
val _ = Parse.current_backend := PPBackEnd.emacs_terminal;
val _ = Feedback.set_trace "Unicode" 1;
val _ = print "\n\nInitialisation complete ...\n\n";
