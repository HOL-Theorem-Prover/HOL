(* ========================================================================== *)
(* FILE          : hhsRecord.sml                                              *)
(* DESCRIPTION   : Recording theories at the tactic level                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsRecord :> hhsRecord =
struct

open HolKernel Abbrev hhsPrerecord hhsUnfold hhsTools hhsSearch

val ERR = mk_HOL_ERR "hhsRecord"

fun mkDir_err dir = OS.FileSys.mkDir dir handle _ => ()

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
  mkDir_err (hhs_feature_dir ^ "/tactic");
  erase_file (hhs_feature_dir ^ "/tactic/" ^ cthy);
  (* record logs *)
  mkDir_err hhs_record_dir;
  mkDir_err (hhs_record_dir ^ "/" ^ cthy);
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/parse_err");
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/replay_err");  
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/summary");  
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/fetch_thm"); 
  erase_file (hhs_record_dir ^ "/" ^ cthy ^ "/fetch_thm_hidden");   
  (* Evaluating success of tactics *)   
  mkDir_err (tactictoe_dir ^ "/tactic_success");
  erase_file (tactictoe_dir ^ "/tactic_success/" ^ cthy)
  )

(*---------------------------------------------------------------------------
  Extracting name of the theory and filename from the file path.
  ---------------------------------------------------------------------------*)

fun thy_of_file filename =
  if String.isPrefix HOLDIR filename then 
    let 
      val suffix = last (String.tokens (fn x => x = #"/") filename)
      val cthy = String.substring (suffix, 0, 
        String.size suffix - String.size "Script.sml")
    in
      cthy
    end
  else raise ERR "thy_of_file" filename 

fun buildfile_of filename =
  if String.isPrefix HOLDIR filename then 
    let 
      val suffix = last (String.tokens (fn x => x = #"/") filename)
    in
      tactictoe_dir ^ "/build/" ^ suffix
    end
  else raise ERR "buildfile_of" filename 

(*---------------------------------------------------------------------------
  Short summary of tactic recording
  ---------------------------------------------------------------------------*)

fun export_success cthy =
  let 
    val l = dlist (!succ_cthy_dict)
    fun f (stac,(succ,try)) = 
      "(" ^ mlquote stac ^ ", (" ^ 
      int_to_string succ ^ "," ^ int_to_string try ^ ") )"
  in
    writel (tactictoe_dir ^ "/tactic_success/" ^ cthy) (map f l)
  end

fun end_thy cthy = 
  (
  export_success cthy;
  mk_summary cthy
  )

end (* struct *)
