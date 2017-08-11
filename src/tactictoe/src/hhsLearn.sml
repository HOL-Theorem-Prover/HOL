(* ========================================================================== *)
(* FILE          : hhsLearn.sml                                               *)
(* DESCRIPTION   : Learning from tactic calls during search and recording     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsLearn :> hhsLearn =
struct

open HolKernel boolLib Abbrev hhsTools hhsPredict hhsExec hhsMinimize hhsTimeout

val ERR = mk_HOL_ERR "hhsLearn"

val hhs_ortho_flag = ref false
val hhs_succrate_flag = ref false

(*----------------------------------------------------------------------------
 * Orthogonalization
 *----------------------------------------------------------------------------*)

(* should move hhs_tactic_time to tools *)
fun is_better_lbl (_,t1,g1,gl1) (_,t2,g2,gl2) =  
  t1 < !hhs_tactic_time andalso g1 = g2 andalso all (fn x => mem x gl2) gl1 

fun find_better_stac (lbl2 as (stac2,t2,g2,gl2)) stacl =
  if null stacl then lbl2 else
    let 
      val lbl1 =
        let 
          val stac1 = hd stacl
          val ((gl1,_),t1) = 
            add_time (timeOut (!hhs_tactic_time) (tactic_of_sml stac1)) g2 
        in
          (stac1,t1,g2,gl1)
        end
        handle _ => ("Error", !hhs_tactic_time + 100.0,g2,gl2) (* dirty trick *)
    in  
      if is_better_lbl lbl1 lbl2 
      then lbl1 
      else find_better_stac lbl2 (tl stacl)
    end  

fun orthogonalize (lbl as (_,t,g,gl),fea) =
  if !hhs_ortho_flag 
  then
    let 
      val feavectl = stacknn_ext 20 (!hhs_stacfea) fea
      val stacl    = map (#1 o fst) feavectl
    in
      find_better_stac lbl stacl
    end
  else lbl

(* ---------------------------------------------------------------------------
   Success rates of each tactic.
   -------------------------------------------------------------------------- *)

val succ_cthy_dict = ref (dempty String.compare)
val succ_glob_dict = ref (dempty String.compare)

fun count_try stac = 
  let 
    val (succ1,try1) = dfind stac (!succ_cthy_dict) handle _ => (0,0)
    val (succ2,try2) = dfind stac (!succ_glob_dict) handle _ => (0,0)
  in
    succ_cthy_dict := dadd stac (succ1,try1 + 1) (!succ_cthy_dict);
    succ_glob_dict := dadd stac (succ2,try2 + 1) (!succ_glob_dict)
  end
  
fun count_succ stac = 
  let 
    val (succ1,try1) = dfind stac (!succ_cthy_dict) handle _ => (0,0)
    val (succ2,try2) = dfind stac (!succ_glob_dict) handle _ => (0,0)
  in
    succ_cthy_dict := dadd stac (succ1 + 1,try1) (!succ_cthy_dict);
    succ_glob_dict := dadd stac (succ2 + 1,try2) (!succ_glob_dict)
  end

fun inv_succrate stac =
  if !hhs_succrate_flag
  then
    let 
      val (succ,try) = dfind stac (!succ_glob_dict)
    in
      Real.fromInt (10 + try) / Real.fromInt (succ + 1)
    end
  else 1.0

(*----------------------------------------------------------------------------
 * I/O success rates
 *----------------------------------------------------------------------------*)

val succrate_reader = ref []

fun mk_string_list sl = "[" ^ String.concatWith "," sl ^ "]"

fun read_succrate thy =
  if mem thy ["min","bool"] then () else
  let
    val sl = readl (hhs_succrate_dir ^ "/" ^ thy) 
             handle _ => (print (thy ^ "\n"); [])
    val b =
      if sl = [] 
        then true
        else
        hhsExec.exec_sml "data"
        ("hhsLearn.succrate_reader := " ^ mk_string_list sl ^ 
        " @ (!hhsLearn.succrate_reader)")
  in
    if b then () else print (thy ^ "\n")
  end

fun import_succrate thyl =
  (
  debug "Reading success rates...";
  app read_succrate thyl;
  !succrate_reader
  )

fun export_succrate cthy =
  let 
    val l = dlist (!succ_cthy_dict)
    fun f (stac,(succ,try)) = 
      "(" ^ mlquote stac ^ ", (" ^ 
      int_to_string succ ^ "," ^ int_to_string try ^ ") )"
  in
    writel (hhs_succrate_dir ^ "/" ^ cthy) (map f l)
  end
  

end (* struct *)
