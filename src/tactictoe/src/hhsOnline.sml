(* ========================================================================== *)
(* FILE          : hhsOnline.sml                                              *)
(* DESCRIPTION   : Online SML code substitution                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsOnline :> hhsOnline =
struct

open HolKernel boolLib Abbrev hhsTools hhsExec

val ERR = mk_HOL_ERR "hhsOnline"

val thm_counter = ref 0

fun string_db_fetch thy name =
  String.concatWith " " ["(","DB.fetch",mlquote thy,mlquote name,")"]

fun save_tactictoe_thm thm =
  let 
    val name = "tactictoe_thm" ^ int_to_string (!thm_counter)
    val _    = incr thm_counter
    val cthy = current_theory ()
  in
    save_thm (name,thm); 
    string_db_fetch cthy name
  end

fun depid_of_thm thm = (Dep.depid_of o Tag.dep_of o Thm.tag) thm

fun name_of_thm thm =
  let 
    val (thy,n) = depid_of_thm thm
    val thml = DB.thms thy
    val thmdict = dnew goal_compare (map (fn (a,b) => (dest_thm b,a)) thml)
    val thmname = dfind (dest_thm thm) thmdict
  in
    string_db_fetch thy thmname
  end
  handle _ => save_tactictoe_thm thm 

fun fetch_thm s reps =
  let 
    val file = 
    tactictoe_dir ^ "/record_log/" ^ current_theory () ^ "/fetch_thm"
  in
    hhsRedirect.hide (file ^ "_hidden") 
      string_of_sml ("hhsOnline.name_of_thm " ^ s)
    handle _ => (if reps = "" then (append_file file s; s) else reps)
  end
    
end (* struct *)
