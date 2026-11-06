val _ = HOL_Interactive.toggle_quietdec();

val _ = loadPath :=
            concat [Globals.HOLDIR, "/examples/separationLogic/src"] ::
            concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"] ::
            !loadPath

val _ = map load ["holfootParser", "holfoot_pp_print", "holfootLib"];
open holfootParser;
open holfoot_pp_print;
open holfootLib;

val _ = HOLFlags.set_trace "PPBackEnd.use_styles" 1;
val _ = HOLFlags.set_trace "PPBackEnd.show_types" 0;
val _ = HOLFlags.set_trace "metis.trace" 0

val examplesDir =
    concat [Globals.HOLDIR,
            "/examples/separationLogic/src/holfoot/EXAMPLES"];

val _ = print "\n\nInitialisation complete ...\n\n";

(* done *)
val _ = HOL_Interactive.toggle_quietdec();
