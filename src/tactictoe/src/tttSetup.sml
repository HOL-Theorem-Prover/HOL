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
val tactictoe_session_id = Portable.unique_tmp_suffix ()
val tactictoe_cache_dir = tactictoe_cache_dir_ref
fun tactictoe_dir_of () = current_tactictoe_cache_dir ()
fun ttt_eval_dir_of () = tactictoe_dir_of () ^ "/eval"
fun tactictoe_scratch_dir_of () =
  tactictoe_dir_of () ^ "/tmp/" ^ tactictoe_session_id
fun set_tactictoe_cache_dir dir = tactictoe_cache_dir := dir

val tactictoe_dir = tactictoe_dir_of ()
val ttt_eval_dir = ttt_eval_dir_of ()
val tactictoe_scratch_dir = tactictoe_scratch_dir_of ()

fun with_saved_ref r v f =
  let val old = !r in
    r := v;
    (let val x = f () in r := old; x end
     handle e => (r := old; raise e))
  end

fun with_tactictoe_cache f =
  let val scratch = tactictoe_scratch_dir_of () in
  with_saved_ref sigobj_theories_dir (scratch ^ "/code")
  (fn () =>
  with_saved_ref smlOpen.open_dir
    (scratch ^ "/sml_inspection/open")
  (fn () =>
  with_saved_ref smlOpen.openscript_dir
    (scratch ^ "/sml_inspection/openscript")
  (fn () =>
  with_saved_ref smlExecScripts.heapname_dir
    (scratch ^ "/sml_inspection/heapname")
  (fn () =>
  with_saved_ref smlExecScripts.genscriptdep_dir
    (scratch ^ "/sml_inspection/genscriptdep")
  (fn () =>
  with_saved_ref smlExecScripts.buildheap_dir
    (scratch ^ "/sml_inspection/buildheap")
  (fn () =>
  with_saved_ref smlRedirect.hide_file
    (scratch ^ "/sml_inspection/hide_file")
    f))))))
  end

(* -------------------------------------------------------------------------
   Nearest neighbor parameters
   ------------------------------------------------------------------------- *)

val ttt_thmlarg_radius = ref 32
val ttt_ortho_radius = ref 10
val ttt_presel_radius = ref 500

(* -------------------------------------------------------------------------
   Recording
   ------------------------------------------------------------------------- *)

val record_flag = ref true
val record_savestate_flag = ref false
val record_ortho_flag = ref true
val record_prove_flag = ref true
val record_let_flag = ref false
val record_tactic_time = ref 2.0
val record_proof_time = ref 2.0
val learn_tactic_time = ref 0.04
val learn_abstract_term = ref false
val export_thmdata_flag = ref false

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val ttt_metis_flag = ref true
val ttt_metis_time = ref 0.1
val ttt_metis_radius = ref 16
val ttt_tactic_time = ref 0.04
val ttt_search_time = ref 10.0
val ttt_policy_coeff = ref 0.5
val ttt_explo_coeff = ref 2.0
val ttt_ex_flag = ref false


end (* struct *)
