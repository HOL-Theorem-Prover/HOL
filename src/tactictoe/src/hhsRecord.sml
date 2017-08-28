(* ========================================================================== *)
(* FILE          : hhsRecord.sml                                              *)
(* DESCRIPTION   : Hooks to prepare theories for recording                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsRecord :> hhsRecord =
struct

open HolKernel Abbrev hhsPrerecord hhsUnfold hhsTools hhsLearn hhsSearch tacticToe hhsData

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
  erase_file (hhs_succrate_dir ^ "/" ^ cthy)
  )

(*---------------------------------------------------------------------------
  Short summary of tactic recording. Exporting feature vectors.
  ---------------------------------------------------------------------------*)

fun end_thy cthy = 
  (
  let
    val file = tactictoe_dir ^ "/record_log/" ^ cthy ^ "/summary"
    fun f i s = append_endline file (int_to_string i ^ " " ^ s) 
    fun g s r = append_endline file (s ^ ": " ^ Real.toString r)
    val _ = if !hhs_eval_flag then export_succrate cthy else ()
    val (_,t) = add_time (export_feavl cthy) (!hhs_cthyfea)
  in 
    mk_summary cthy;
    g "export" t
  end
  )

end (* struct *)
