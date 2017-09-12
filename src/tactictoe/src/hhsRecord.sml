(* ========================================================================== *)
(* FILE          : hhsRecord.sml                                              *)
(* DESCRIPTION   : Hooks to prepare theories for recording                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsRecord :> hhsRecord =
struct

open HolKernel Abbrev hhsPrerecord hhsUnfold hhsTools hhsLearn hhsSearch tacticToe hhsData hhsMetis

val ERR = mk_HOL_ERR "hhsRecord"

(*---------------------------------------------------------------------------
  Cleaning files
  ---------------------------------------------------------------------------*)

fun start_thy cthy =
  (
  clean_feadata ();
  reset_profiling ();
  hhsExtract.pointer_cache_glob := dempty String.compare;
  (* search logs *)
  mkDir_err hhs_search_dir;
  mkDir_err (hhs_search_dir ^ "/proof");
  mkDir_err (hhs_search_dir ^ "/debug");
  mkDir_err (hhs_search_dir ^ "/search");
  erase_file (hhs_search_dir ^ "/proof/" ^ cthy);
  erase_file (hhs_search_dir ^ "/debug/" ^ cthy);
  erase_file (hhs_search_dir ^ "/search/" ^ cthy);
  (* feature data *)
  mkDir_err hhs_feature_dir;
  erase_file (hhs_feature_dir ^ "/" ^ cthy);
  (* record logs *)
  mkDir_err hhs_record_dir;
  mkDir_err (hhs_record_dir ^ "/" ^ cthy);
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/parse_err");
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/replay_err");  
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/record_err");
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/summary");  
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/fetch_thm");  
  (* Evaluating success of tactics *)   
  mkDir_err hhs_succrate_dir;
  erase_file (hhs_succrate_dir ^ "/" ^ cthy);
  (* Orthogonalization of theorems *)
  mkDir_err hhs_mdict_dir;
  erase_file (hhs_mdict_dir ^ "/" ^ cthy)
  )

(*---------------------------------------------------------------------------
  Short summary of tactic recording. Exporting feature vectors.
  ---------------------------------------------------------------------------*)

fun end_thy cthy = 
  let
    val _ = debug_t "export_succrate" export_succrate cthy
    val _ = debug_t "export_feavl" (export_feavl cthy) (!hhs_cthyfea)
    val _ = debug_t "export_mdict" export_mdict cthy
  in 
    mk_summary cthy
  end

end (* struct *)
