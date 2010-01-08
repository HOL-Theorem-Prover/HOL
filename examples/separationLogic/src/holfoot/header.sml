(******************************************************************************)
(* Standard initialisation                                                    *)
(******************************************************************************)

(*
val _ = loadPath := 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) :: 
            !loadPath;

val _ = map load ["holfootParser", "holfoot_pp_print", "holfootLib"];
open holfootParser;
open holfoot_pp_print;
open holfootLib;

val _ = Feedback.set_trace "Unicode" 0

val examplesDir = 
    concat [Globals.HOLDIR, 
            "/examples/separationLogic/src/holfoot/EXAMPLES"];


val _ = holfoot_auto_verify_spec true (examplesDir ^ "/automatic/list.sf")

val _ = holfoot_interactive_verify_spec true    
               {do_case_splits = true,
                fast = false,
                use_asms = true,
                do_prop_simps = true,
                generate_vcs = false} ([],[],[])
           (examplesDir ^ "/automatic/mergesort.sf")
*)


(******************************************************************************)
(* for PolyML one can save and load states much more efficiently              *)
(******************************************************************************)

val state_file = (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/holfoot.state");

(* save
val _ = PolyML.SaveState.saveState state_file
*)

val _ = PolyML.SaveState.loadState state_file;

val _ = print "\n\nInitialisation complete ...\n\n";

