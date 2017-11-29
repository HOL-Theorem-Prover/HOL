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

val hhs_norecord_flag    = ref false
val hhs_internalthm_flag = ref false

(* set following flag to true to simulate version 2 *)
val hhs_norecprove_flag  = ref false
val hhs_nolet_flag      = ref false

(* ----------------------------------------------------------------------
   Learning
   ---------------------------------------------------------------------- *)

val hhs_ortho_flag = ref false
val hhs_ortho_number = ref 20
val hhs_ortho_metis = ref false
val hhs_ortho_deep = ref false

val hhs_thmortho_flag = ref false

val hhs_selflearn_flag = ref false
val hhs_succrate_flag = ref false

(* ----------------------------------------------------------------------
   Evaluation
   ---------------------------------------------------------------------- *)

val hhs_eval_flag        = ref false
val hh_only_flag         = ref false
val hhs_noprove_flag    = ref false

val one_in_option = ref NONE
val one_in_counter = ref 0

fun one_in_n () = case !one_in_option of
    NONE => true
  | SOME (offset,freq) =>
    let val b = (!one_in_counter) mod freq = offset in
      (incr one_in_counter; b)
    end

(* ----------------------------------------------------------------------
   Preselection
   ---------------------------------------------------------------------- *)

val hhs_maxselect_pred = ref 500

(* ----------------------------------------------------------------------
   Search
   ---------------------------------------------------------------------- *)

val hhs_cache_flag  = ref true
val hhs_astar_flag = ref false
val hhs_astar_radius = ref 0
val hhs_astar_coeff = ref 8.0
val hhs_timedepth_flag = ref false
val hhs_width_coeff = ref 1.0
val hhs_selflearn_flag = ref false
val hhs_mc_flag = ref false

(* ----------------------------------------------------------------------
   Metis + HolyHammer
   ---------------------------------------------------------------------- *)

val hhs_thmortho_flag = ref false (* set at the recording level *)

val hhs_metis_flag    = ref false
val hhs_metis_time    = ref 0.1
val hhs_metis_npred   = ref 16
val hhs_stacpred_flag = ref false
val hhs_stacpred_number = ref 16
  (* synthetizing arguments (theorems) of tactics *)
val hh_stac_flag      = ref false (* predict dependencies using holyhammer *)

fun can_update_hh n = ((update_hh_stac n; true) handle _ => false)

(* ----------------------------------------------------------------------
   Minimize flags
   ---------------------------------------------------------------------- *)

val hhs_minimize_flag = ref false
val hhs_prettify_flag = ref false

(* ----------------------------------------------------------------------
   Setting flags
   ---------------------------------------------------------------------- *)
val test_eval_hook = ref (fn s:string => true) 

fun set_irecord () = 
  (
  (* recording *)
  hhs_norecord_flag    := false;
  hhs_internalthm_flag := false;
  hhs_norecprove_flag  := false;
  hhs_nolet_flag       := false;
  (* learning *)
  hhs_ortho_flag     := false;
  hhs_ortho_number   := 20;
  hhs_ortho_metis    := false;
  hhs_ortho_deep     := false;
  hhs_selflearn_flag := false;
  hhs_succrate_flag  := false;
  hhs_thmortho_flag  := false;
  (* evaluation *)
  hhs_eval_flag := false
  )

val set_isearch_hook = ref (fn () => ()) 
    
fun set_isearch () =
  (
  (* predicting *)
  hhs_maxselect_pred := 500;
  (* searching (search time is not set to be easily modifiable) *)
  hhs_tactic_time    := 0.02;
  hhs_cache_flag     := true;
  hhs_width_coeff    := 1.0;
  hhs_astar_flag     := false;
  hhs_astar_radius   := 8;
  hhs_astar_coeff    := 8.0;
  hhs_timedepth_flag := false;
  (* metis + holyhammer + new arguments *)
  hhs_metis_flag  := (true andalso can load "metisTools");
  hhs_metis_npred := 16;
  hhs_metis_time  := 0.1;
  hh_stac_flag    := false;
  hhs_stacpred_flag := false;
  hhs_stacpred_number := 16;
  (* result *)
  hhs_minimize_flag := true;
  hhs_prettify_flag := true;
  (* hook *)
  !set_isearch_hook ();
  if !hh_stac_flag then update_hh_stac 5 else ()
  )




fun set_esearch () = 
  (
  (* predicting *)
  hhs_maxselect_pred := 500;
  (* searching *)
  hhs_search_time    := Time.fromReal 5.0;
  hhs_tactic_time    := 0.02;
  hhs_cache_flag     := true;
  hhs_width_coeff    := 1.0;
  hhs_astar_flag     := false;
  hhs_astar_radius   := 8;
  hhs_astar_coeff    := 8.0;
  hhs_timedepth_flag := false;
  (* metis + holyhammer + new arguments *)
  hhs_metis_flag    := (true andalso can load "metisTools");
  hhs_metis_npred   := 16;
  hhs_metis_time    := 0.1;
  hh_stac_flag      := (false andalso can_update_hh 5);
  hhs_stacpred_flag := false;
  hhs_stacpred_number := 16;
  (* result *)
  hhs_minimize_flag := false;
  hhs_prettify_flag := false
  ) 



fun set_erecord () =
  (
  hhs_internalthm_flag := true;
  hhs_norecprove_flag  := true;
  hhs_nolet_flag       := true;
  (* learning *)
  hhs_ortho_flag     := true;
  hhs_ortho_number   := 20;
  hhs_ortho_metis    := true;
  hhs_ortho_deep     := false;
  hhs_selflearn_flag := false;
  hhs_succrate_flag  := false;
  hhs_thmortho_flag  := true;
  (* evaluation *)
  hhs_eval_flag    := true;
  hhs_noprove_flag := true;
  one_in_option    := SOME (0,10);
  hh_only_flag     := (false andalso can_update_hh 60)
  )

end (* struct *)
