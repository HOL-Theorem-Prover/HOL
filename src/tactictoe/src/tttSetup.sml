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

(* ----------------------------------------------------------------------
   Recording
   ---------------------------------------------------------------------- *)

val ttt_record_flag   = ref true
val ttt_recprove_flag = ref false
val ttt_reclet_flag   = ref false

(* ----------------------------------------------------------------------
   Learning
   ---------------------------------------------------------------------- *)

val ttt_ortho_flag = ref false
val ttt_ortho_number = ref 20
val ttt_selflearn_flag = ref false

(* ----------------------------------------------------------------------
   Evaluation
   ---------------------------------------------------------------------- *)

val ttt_eval_flag     = ref false
val ttt_evprove_flag  = ref false
val ttt_evlet_flag    = ref false
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

val ttt_maxselect_pred = ref 500

(* ----------------------------------------------------------------------
   Search
   ---------------------------------------------------------------------- *)

val ttt_policy_coeff = ref 0.5
val ttt_mcrecord_flag = ref false
val ttt_mcnoeval_flag = ref false
val ttt_mctriveval_flag = ref false
val ttt_mc_radius = ref 0
val ttt_evalinit_flag = ref true
val ttt_evalfail_flag = ref true
val ttt_mc_coeff = ref 2.0
val ttt_mcpresim_int = ref 2
val ttt_selflearn_flag = ref false

(* ----------------------------------------------------------------------
   Metis
   ---------------------------------------------------------------------- *)

val ttt_namespacethm_flag = ref true
val ttt_metisexec_flag    = ref false
val ttt_metisrecord_flag  = ref false
val ttt_metishammer_flag  = ref false
val ttt_metis_time    = ref 0.1
val ttt_metis_npred   = ref 16

(* ----------------------------------------------------------------------
   HolyHammer
   ---------------------------------------------------------------------- *)

val ttt_hhhammer_flag = ref false
val ttt_hhhammer_time = ref 5
val ttt_async_limit = ref 1

(* ----------------------------------------------------------------------
   Tactic abstraction + argument instantiation
   ---------------------------------------------------------------------- *)

val ttt_thmlarg_flag = ref false
val ttt_thmlarg_number = ref 16
val ttt_termarg_flag = ref false
val ttt_termarg_number = ref 16
val ttt_termpresim_int = ref 2

(* ----------------------------------------------------------------------
   Proof presentation
   ---------------------------------------------------------------------- *)

val ttt_minimize_flag = ref false
val ttt_prettify_flag = ref false

(* ----------------------------------------------------------------------
   Setting flags
   ---------------------------------------------------------------------- *)

(* theories appearing in metisTools *)
val thyl = ["sat", "marker", "combin", "min", "bool", "normalForms"];

val set_record_hook = ref (fn () => ())

fun set_record cthy =
  (
  (* recording *)
  ttt_namespacethm_flag := true;
  ttt_recprove_flag := true;
  ttt_reclet_flag   := false;
  (* learning *)
  ttt_ortho_flag      := true;
  ttt_ortho_number    := 20;
  ttt_selflearn_flag  := false; (* Self-learning issue: local tags *)
  (* predicting *)
  ttt_maxselect_pred := 500;
  (* searching *)
  ttt_search_time    := Time.fromReal 10.0;
  ttt_tactic_time    := 0.05;
  (* mc *)
  ttt_policy_coeff   := 0.5; (* between 0 and 1 *)
  ttt_mcnoeval_flag  := false;
  ttt_mctriveval_flag := false;
  ttt_mcrecord_flag  := true;
  ttt_evalinit_flag  := false;
  ttt_evalfail_flag  := true;
  ttt_mc_radius      := 10;
  ttt_mc_coeff       := 2.0;
  ttt_mcpresim_int   := 2;
  (* metis *)
  ttt_metisrecord_flag := true;
  ttt_metisexec_flag   := (not (mem cthy thyl) andalso can load "metisTools");
  if !ttt_metisexec_flag then update_metis_tac () else ();
  ttt_metishammer_flag := (true andalso !ttt_metisexec_flag);
  ttt_metis_npred      := 16;
  ttt_metis_time       := 0.1;
  (* eprover parameters (todo: add number of premises) *)
  ttt_hhhammer_flag := (false andalso can update_hh_stac ());
  ttt_hhhammer_time := 5;
  ttt_async_limit   := 1;
  (* synthesis *)
  ttt_thmlarg_flag   := true;
  ttt_thmlarg_number := 16;
  ttt_termarg_flag   := false;
  ttt_termarg_number := 16;
  ttt_termpresim_int := 2;
  (* result *)
  ttt_minimize_flag := true;
  ttt_prettify_flag := true;
  (* evaluation *)
  ttt_eval_flag    := false;
  ttt_evprove_flag := false;
  ttt_evlet_flag   := false; (* ttt_evletonly_flag := true; *)
  one_in_option    := SOME (0,1);
  hh_only_flag     :=
    (false andalso !ttt_metisexec_flag andalso can update_hh_stac ());
  (* hook *)
  (!set_record_hook) ()
  )

end (* struct *)
