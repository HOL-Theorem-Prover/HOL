(* ========================================================================== *)
(* FILE          : tttSetup.sml                                               *)
(* DESCRIPTION   : Flags and global parameters for TacticToe recording and    *)
(* search                                                                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttSetup :> tttSetup =
struct

open HolKernel boolLib Abbrev tttExec tttTools

(* ==========================================================================
   Recording
   ========================================================================== *)

val ttt_recprove_flag = ref true
val ttt_reclet_flag   = ref false
val ttt_rectac_time   = ref 2.0
val ttt_recproof_time = ref 20.0

(* Default parameters *)
fun set_recording () =
  (
  ttt_recprove_flag  := true;
  ttt_reclet_flag    := false;
  ttt_rectac_time    := 2.0;
  ttt_recproof_time  := 20.0
  )

(* ==========================================================================
   Training
   ========================================================================== *)

(* Orthogonalization *)
val ttt_ortho_flag = ref false
val ttt_ortho_radius = ref 20

(* Abstraction *)
val ttt_thmlarg_flag = ref false
val ttt_thmlarg_radius = ref 16

(* Theorems space *)
val ttt_namespacethm_flag = ref true

(* Default parameters *)
fun set_training () =
  (
  (* tactics *)
  ttt_tactic_time    := 0.05;
  (* theorems *)
  ttt_namespacethm_flag := true;
  (* orthogonalization *)
  ttt_ortho_flag     := true;
  ttt_ortho_radius   := 20;
  (* abstraction *)
  ttt_thmlarg_flag   := true;
  ttt_thmlarg_radius := 16
  )

(* Additional parameters *)
val ttt_recgl_flag = ref false
 
(* ==========================================================================
   Evaluation
   ========================================================================== *)

(* Evaluated theorems *)
val ttt_evprove_flag  = ref false
val ttt_evlet_flag    = ref false

val one_in_option = ref NONE
val one_in_counter = ref 0
fun one_in_n () = case !one_in_option of
    NONE => true
  | SOME (offset,freq) =>
    let val b = (!one_in_counter) mod freq = offset in
      (incr one_in_counter; b)
    end

val evaluation_filter = ref (fn s:string => true)

(* Preselection *)
val ttt_presel_radius = ref 500

(* --------------------------------------------------------------------------
   ATPs
   -------------------------------------------------------------------------- *)

(* Metis *)
val ttt_metisexec_flag    = ref false
val ttt_metis_flag  = ref false
val ttt_metis_time    = ref 0.1
val ttt_metis_radius   = ref 16
(* dependency of metisTools *)
val metistools_thyl = ["sat", "marker", "combin", "min", "bool", "normalForms"];

(* --------------------------------------------------------------------------
   Search
   -------------------------------------------------------------------------- *)
   
val ttt_mcpol_coeff = ref 0.5
val ttt_mcevnone_flag = ref false
val ttt_mcevtriv_flag = ref true
val ttt_mcev_radius = ref 0
val ttt_mcevinit_flag = ref false
val ttt_mcevfail_flag = ref true
val ttt_mcev_coeff = ref 2.0 
val ttt_mcev_pint = ref 2

(* Warning: requires ttt_recgl_flag during training if neither 
   mcnoeval nor mctriveval are set to true. *)

(* --------------------------------------------------------------------------
   Proof presentation
   -------------------------------------------------------------------------- *)

val ttt_minimize_flag = ref false
val ttt_prettify_flag = ref false

(* --------------------------------------------------------------------------
   Default paramaters
   -------------------------------------------------------------------------- *)

fun set_evaluation cthy =
  (
  (* evaluated theorems *)
  ttt_evprove_flag := false;
  ttt_evlet_flag   := false;
  one_in_option    := SOME (0,1);
  (* additional theorems *)
  ttt_namespacethm_flag := true;
  (* preselection *)
  ttt_presel_radius := 1000;
  (* timeout *)
  ttt_search_time    := Time.fromReal 10.0;
  ttt_tactic_time    := 0.05;
  (* search *)
    (* policy *)
    ttt_mcpol_coeff   := 0.5;
    (* evaluation (only trivial for now) *)
    ttt_mcevnone_flag   := false;
    ttt_mcevtriv_flag := true;
    ttt_mcevinit_flag   := false;
    ttt_mcevfail_flag   := true;
  (* atps *)
    (* metis *)
    ttt_metisexec_flag := (not (mem cthy metistools_thyl) 
                             andalso can load "metisTools");
    if !ttt_metisexec_flag then update_metis_tac () else ();
    ttt_metis_flag := (true andalso !ttt_metisexec_flag);
    ttt_metis_radius := 16;
    ttt_metis_time  := 0.1;
  (* proof presentation *)
  ttt_minimize_flag := true;
  ttt_prettify_flag := true
  )

(* --------------------------------------------------------------------------
   Additionnal parameters
   -------------------------------------------------------------------------- *)

(* Argument instantiation *)
val ttt_termarg_flag = ref false
val ttt_termarg_radius = ref 16
val ttt_termarg_pint = ref 2

(* Eprover with translation from HolyHammer *)
val ttt_eprover_flag = ref false
val ttt_eprover_time = ref 5
val ttt_eprover_radius = ref 128 (* can not be changed yet *)
val ttt_eprover_async = ref 1
(* evaluate Eprover instead of TacticToe *)
val ttt_eprovereval_flag  = ref false 

(* Usage 
  ttt__flag := 
    (true andalso !ttt_metisexec_flag andalso can update_hh_stac ());
  ttt_eprovereval_flag := 
    (true andalso !ttt_metisexec_flag andalso can update_hh_stac ());
*)

(* Self-learning (not working) *)
val ttt_selflearn_flag = ref false

end (* struct *)
