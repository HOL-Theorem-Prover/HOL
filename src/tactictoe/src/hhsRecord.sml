(* ========================================================================== *)
(* FILE          : hhsRecord.sml                                              *)
(* DESCRIPTION   : Hooks to prepare theories for recording                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsRecord :> hhsRecord =
struct

open HolKernel Abbrev hhsPrerecord hhsUnfold hhsTools hhsLearn hhsSearch

val ERR = mk_HOL_ERR "hhsRecord"

(*---------------------------------------------------------------------------
  Cleaning files
  ---------------------------------------------------------------------------*)

fun start_thy cthy =
  (
  reset_profiling ();
  hhsExtract.pointer_cache_glob := dempty String.compare;
  (* search logs *)
  mkDir_err hhs_search_dir;
  mkDir_err (hhs_search_dir ^ "/proof");
  mkDir_err (hhs_search_dir ^ "/debug");
  erase_file (hhs_search_dir ^ "/proof/" ^ cthy);
  erase_file (hhs_search_dir ^ "/debug/" ^ cthy);
  (* feature data *)
  mkDir_err hhs_feature_dir;
  mkDir_err hhs_tacfea_dir;
  erase_file (hhs_tacfea_dir ^ "/" ^ cthy);
  (* record logs *)
  mkDir_err hhs_record_dir;
  mkDir_err (hhs_record_dir ^ "/" ^ cthy);
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/parse_err");
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/replay_err");  
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/summary");  
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/fetch_thm"); 
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/fetch_thm_hidden");   
  (* Evaluating success of tactics *)   
  mkDir_err hhs_succrate_dir;
  erase_file (hhs_succrate_dir ^ "/" ^ cthy)
  )

(*---------------------------------------------------------------------------
  Short summary of tactic recording
  ---------------------------------------------------------------------------*)

fun end_thy cthy = 
  (
  export_succrate cthy;
  mk_summary cthy
  )

end (* struct *)
