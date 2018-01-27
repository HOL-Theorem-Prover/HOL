(* ========================================================================== *)
(* FILE          : hhsSetup.sml                                               *)
(* DESCRIPTION   : Flags and global parameters for TacticToe recording and    *) 
(* search                                                                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsSetup :> hhsSetup =
struct

open HolKernel boolLib Abbrev hhsExec hhsTools

(* ----------------------------------------------------------------------
   Recording
   ---------------------------------------------------------------------- *)

val hhs_record_flag   = ref true
val hhs_recprove_flag = ref false
val hhs_reclet_flag   = ref false

(* ----------------------------------------------------------------------
   Learning
   ---------------------------------------------------------------------- *)

val hhs_ortho_flag = ref false
val hhs_ortho_number = ref 20
val hhs_selflearn_flag = ref false

(* ----------------------------------------------------------------------
   Evaluation
   ---------------------------------------------------------------------- *)

(* val hhs_evletonly_flag = ref false *)
val hhs_eval_flag     = ref false
val hhs_evprove_flag  = ref false
val hhs_evlet_flag    = ref false
val hh_only_flag      = ref false

val one_in_option = ref NONE
val one_in_counter = ref 0
fun one_in_n () = case !one_in_option of
    NONE => true
  | SOME (offset,freq) =>
    let val b = (!one_in_counter) mod freq = offset in
      (incr one_in_counter; b)
    end

val test_eval_hook = ref (fn s:string => true) 

(* ----------------------------------------------------------------------
   Preselection
   ---------------------------------------------------------------------- *)

val hhs_maxselect_pred = ref 500

(* ----------------------------------------------------------------------
   Search
   ---------------------------------------------------------------------- *)

val hhs_cache_flag  = ref true
val hhs_mc_flag = ref false
val hhs_mcrecord_flag = ref false
val hhs_mcnoeval_flag = ref false
val hhs_mc_radius = ref 0
val hhs_mc_coeff = ref 2.0
val hhs_width_coeff = ref 1.0
val hhs_selflearn_flag = ref false

(* ----------------------------------------------------------------------
   Metis
   ---------------------------------------------------------------------- *)

val hhs_namespacethm_flag = ref true
val hhs_metisexec_flag    = ref false
val hhs_metisrecord_flag  = ref false
val hhs_metishammer_flag  = ref false
val hhs_metis_time    = ref 0.1
val hhs_metis_npred   = ref 16

(* ----------------------------------------------------------------------
   HolyHammer
   ---------------------------------------------------------------------- *)

val hhs_hhhammer_flag = ref false
val hhs_hhhammer_time = ref 5
val hhs_async_limit = ref 1

(* ----------------------------------------------------------------------
   Tactic abstraction + argument instantiation
   ---------------------------------------------------------------------- *)

val hhs_thmlarg_flag = ref false
val hhs_thmlarg_number = ref 16
val hhs_termarg_flag = ref false

(* ----------------------------------------------------------------------
   Proof presentation
   ---------------------------------------------------------------------- *)

val hhs_minimize_flag = ref false
val hhs_prettify_flag = ref false

(* ----------------------------------------------------------------------
   Setting flags
   ---------------------------------------------------------------------- *)


(* set esearch should be moved inside set_erecord *)
fun set_esearch () = 
  (
  (* predicting *)
  hhs_maxselect_pred := 500;
  (* searching *)
  hhs_search_time    := Time.fromReal 60.0;
  hhs_tactic_time    := 0.02;
  hhs_cache_flag     := true;
  hhs_width_coeff    := 1.0;
  hhs_mc_flag        := true;
  hhs_mcrecord_flag  := true;
  hhs_mcnoeval_flag  := false;
  hhs_mc_radius      := 10;
  hhs_mc_coeff       := Math.sqrt 2.0;
  (* metis *)
  hhs_metisexec_flag   := can load "metisTools";
  if !hhs_metisexec_flag then update_metis_tac () else ();
  hhs_metis_npred      := 16;
  hhs_metis_time       := 0.1;
  hhs_metishammer_flag := (true andalso !hhs_metisexec_flag);
  (* eprover parameters *)
  hhs_hhhammer_flag := (true andalso can update_hh_stac ());
  hhs_hhhammer_time := 5;
  hhs_async_limit   := 1;
  (* synthesis *)
  hhs_thmlarg_flag   := true;
  hhs_thmlarg_number := 16;
  hhs_termarg_flag   := false; (* not helpful *)
  (* result *)
  hhs_minimize_flag := true;
  hhs_prettify_flag := true
  )

fun set_erecord () =
  (
  (* recording *)
  hhs_namespacethm_flag := true;
  hhs_recprove_flag := true;
  hhs_reclet_flag   := false;
  (* learning *)
  hhs_ortho_flag      := true;
  hhs_ortho_number    := 20;
  hhs_selflearn_flag  := false; 
  (* Self-learning issue: 
     metis should declare it is using local variables by 
     adding a local_tag but it would affect holyhammer 
     where you don't want a local tag. *)
  (* metis learning *)
  hhs_metisexec_flag   := can load "metisTools"; 
  hhs_metisrecord_flag := true;
  (* evaluation *)
  hhs_eval_flag    := true;
  hhs_evprove_flag := false;
  hhs_evlet_flag   := false;
  (* hhs_evletonly_flag := true; *)
  one_in_option    := SOME (0,10);
  hh_only_flag     := 
     (false andalso can update_hh_stac () andalso can load "metisTools")
  )

val set_isearch_hook = ref (fn () => ())
fun set_isearch () = (set_esearch (); !set_isearch_hook ())
fun set_irecord () = (set_erecord (); hhs_eval_flag := false)

end (* struct *)
