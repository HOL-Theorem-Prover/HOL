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

val alt_search_flag = ref true

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

val infix_file = HOLDIR ^ "/src/AI/sml_inspection/infix_file.sml"
val tactictoe_dir = HOLDIR ^ "/src/tactictoe"
val ttt_debugdir = tactictoe_dir ^ "/debug"
val ttt_eval_updir = tactictoe_dir ^ "/eval"
val ttt_eval_dir = ref (ttt_eval_updir ^ "/default")

(* -------------------------------------------------------------------------
   Nearest neighbor parameters
   ------------------------------------------------------------------------- *)

val ttt_thmlarg_radius = ref 16
val ttt_ortho_radius   = ref 10
val ttt_presel_radius  = ref 500

(* -------------------------------------------------------------------------
   Recording
   ------------------------------------------------------------------------- *)

val ttt_recprove_flag   = ref true
val ttt_reclet_flag     = ref false
val ttt_recproof_time   = ref 20.0

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun init_metis () = hide_out metistac_of_sml ()
  handle Interrupt => raise Interrupt | _ => ()

val ttt_metis_time   = ref 0.1
val ttt_metis_radius = ref 16
val ttt_tactic_time  = ref 0.04 (* also used in tttLearn *)
val ttt_search_time  = ref 10.0
val ttt_policy_coeff = ref 0.5
val ttt_ex_flag = ref false

(* -------------------------------------------------------------------------
   Evaluation. The function being evaluated should produced its own log.
   ------------------------------------------------------------------------- *)

val ttt_evalfun_glob = ref NONE
val ttt_hheval_flag  = ref false
val ttt_ttteval_flag = ref false


end (* struct *)
