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

fun absolute_dir dir =
  if OS.Path.isAbsolute dir then dir
  else OS.Path.mkAbsolute {path = dir, relativeTo = OS.FileSys.getDir ()}

(* Resolve environment configuration while still in the caller's working
   directory.  Recording children later change to a theory source directory. *)
val _ = if !tactictoe_cache_dir = "" then ()
        else tactictoe_cache_dir := absolute_dir (!tactictoe_cache_dir)

fun tactictoe_dir_of () =
  require_dir "tactictoe_dir_of" (!tactictoe_cache_dir)
fun ttt_eval_dir_of () = tactictoe_dir_of () ^ "/eval"
fun tactictoe_scratch_dir_of () =
  tactictoe_dir_of () ^ "/tmp/" ^ tactictoe_session_id
fun set_tactictoe_cache_dir dir = tactictoe_cache_dir := absolute_dir dir

(* Operations watched by tttUnfold because replaying them can create or
   otherwise mutate theory state.  tttRecord uses the same list to avoid
   re-evaluating a local reproduction string that would perform one of
   these operations a second time. *)
val watched_store_operations =
  ["store_thm","maybe_thm","Store_thm","asm_store_thm",
   "store_thm_at",
   "save_thm","new_specification",
   "new_definition","new_infixr_definition","new_infixl_definition",
   "new_type_definition",
   "prove","TAC_PROOF","tprove",
   "store_definition",
   "zDefine","qDefine","bDefine","tDefine","xDefine","dDefine",
   "export_rewrites",
   "save_defn","defnDefine","primDefine","Define","multiDefine","apiDefine",
   "apiDefineq","std_apiDefine","std_apiDefineq","xDefineSchema",
   "DefineSchema",
   "mk_fp_encoding",
   "Hol_reln","xHol_reln","Hol_mono_reln","add_mono_thm","export_mono",
   "add_rule_induction","export_rule_induction",
   "Hol_coreln","xHol_coreln","Hol_mono_coreln","new_coinductive_definition",
   "new_list_rec_definition",
   "define_new_type_bijections",
   "new_binder_definition",
   "new_recursive_definition","define_case_constant",
   "define_equivalence_type",
   "define_quotient_type","define_quotient_lifted_function",
   "define_quotient_types_rule","define_quotient_types_full",
   "define_quotient_types_full_rule","define_quotient_types_std",
   "define_quotient_types_std_rule","define_subset_types",
   "define_subset_types_rule"]

(* Give the SML-inspection machinery a scratch area private to this
   session, so that concurrent recording processes cannot collide.  All
   of its scratch subdirectories hang off aiLib.scratch_dir. *)
fun with_tactictoe_cache f =
  with_flag (scratch_dir, tactictoe_scratch_dir_of ()) f ()

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
