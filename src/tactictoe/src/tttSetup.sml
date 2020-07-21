(* ========================================================================= *)
(* FILE          : tttSetup.sml                                              *)
(* DESCRIPTION   : global parameters for TacticToe                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttSetup :> tttSetup =
struct

open HolKernel Abbrev boolLib aiLib smlExecute smlRedirect
  mlThmData mlTacticData

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

val infix_file = HOLDIR ^ "/src/AI/sml_inspection/infix_file.sml"
val tactictoe_dir = HOLDIR ^ "/src/tactictoe"
val ttt_eval_dir = tactictoe_dir ^ "/eval"

(* -------------------------------------------------------------------------
   Nearest neighbor parameters
   ------------------------------------------------------------------------- *)

val ttt_thmlarg_radius = ref 16
val ttt_ortho_radius   = ref 10
val ttt_presel_radius  = ref 500

(* -------------------------------------------------------------------------
   Recording
   ------------------------------------------------------------------------- *)

val ttt_savestate_flag  = ref false
val ttt_ortho_flag      = ref true
val ttt_recprove_flag   = ref true
val ttt_reclet_flag     = ref false
val ttt_recproof_time   = ref 20.0

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val ttt_metis_time   = ref 0.1
val ttt_metis_radius = ref 16
val ttt_tactic_time  = ref 0.04 (* also used in tttLearn *)
val ttt_search_time  = ref 10.0
val ttt_policy_coeff = ref 0.5
val ttt_ex_flag = ref false

end (* struct *)
