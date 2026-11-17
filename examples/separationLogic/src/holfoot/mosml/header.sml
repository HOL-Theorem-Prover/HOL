val _ = HOL_Interactive.toggle_quietdec();

val _ = loadPath :=
            concat [Globals.HOLDIR, "/examples/separationLogic/src"] ::
            concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"] ::
            !loadPath

val _ = map load ["holfootParser", "holfoot_pp_print", "holfootLib"];
open holfootParser;
open holfoot_pp_print;
open holfootLib;

val _ = HOLFlags.set_bflag (PPBackEnd.use_styles, true);
val _ = HOLFlags.set_bflag (PPBackEnd.show_types, false);
val _ = HOLFlags.set_flag (metisTools.metis_trace, 0)

val examplesDir =
    concat [Globals.HOLDIR,
            "/examples/separationLogic/src/holfoot/EXAMPLES"];

val _ = print "\n\nInitialisation complete ...\n\n";

(* done *)
val _ = HOL_Interactive.toggle_quietdec();
