val _ = HOL_Interactive.toggle_quietdec();

val _ = loadPath := 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) :: 
            !loadPath;

val _ = map load ["holfootParser", "holfoot_pp_print", "holfootLib"];
open holfootParser;
open holfoot_pp_print;
open holfootLib;

val _ = Feedback.set_trace "PPBackEnd use styles" 1;
val _ = Feedback.set_trace "PPBackEnd show types" 0;
val _ = Feedback.set_trace "metis" 0

val examplesDir = 
    concat [Globals.HOLDIR, 
            "/examples/separationLogic/src/holfoot/EXAMPLES"];

val _ = print "\n\nInitialisation complete ...\n\n";

(* done *)
val _ = HOL_Interactive.toggle_quietdec();
