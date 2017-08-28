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

val hhs_time_flag = ref false

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

val fetch_thm_time = ref 0.0

fun fetch_thm_aux s reps =
  let 
    val file = hhs_record_dir ^ "/" ^ current_theory () ^ "/fetch_thm"
  in
    hhsRedirect.hide (file ^ "_hidden") 
      string_of_sml ("hhsOnline.name_of_thm " ^ s)
    handle _ => (if reps = "" then (append_file file s; s) else reps)
  end
  
val fetch_thm = total_time fetch_thm_time fetch_thm_aux

fun try_tac tac1 tac2 g =
  tac1 g handle _ => (debug_record "Error: recording"; tac2 g)

(* Change hhsUnfold at the same time
fun try_tac s tac1 tac2 g =
  if not (!hhs_time_flag) 
  then tac1 g handle _ => (debug_record "Error: recording"; tac2 g)
  else 
    let val (r,t) = add_time tac2 g in
      debug_proof s;
      debug_proof ("original proof time: " ^ Real.toString t);
      r
    end
*)

end (* struct *)
