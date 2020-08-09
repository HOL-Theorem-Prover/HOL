(* ========================================================================= *)
(* FILE          : tttSetup.sml                                              *)
(* DESCRIPTION   : global parameters for TacticToe                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttSetup :> tttSetup =
struct

open HolKernel Abbrev boolLib aiLib
  smlExecute smlRedirect mlThmData mlTacticData

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

val record_savestate_flag  = ref false
val record_ortho_flag      = ref true
val record_prove_flag   = ref true
val record_let_flag     = ref false
val record_tactic_time  = ref 2.0
val record_proof_time = ref 2.0
val learn_tactic_time = ref 0.04
val learn_abstract_term = ref false

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val ttt_metis_time   = ref 0.1
val ttt_metis_radius = ref 16 (* not used *)
val ttt_tactic_time  = ref 0.04
val ttt_search_time  = ref 10.0
val ttt_policy_coeff = ref 0.5
val ttt_explo_coeff = ref 2.0
val ttt_ex_flag = ref false


end (* struct *)
