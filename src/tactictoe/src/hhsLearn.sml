(* ========================================================================== *)
(* FILE          : hhsLearn.sml                                               *)
(* DESCRIPTION   : Learning from tactic calls during search and recording     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsLearn :> hhsLearn =
struct

open HolKernel boolLib Abbrev hhsTools hhsPredict hhsExec hhsMinimize 
hhsTimeout hhsFeature hhsMetis hhsSetup

val ERR = mk_HOL_ERR "hhsLearn"

(*----------------------------------------------------------------------------
 * Calculating the height of the proof tree needed to solve a goal 
 * with respect to a list of labels.
 *----------------------------------------------------------------------------*)

fun update_solved_lvl psolved solved lvl lbls = 
  let
    fun f (_,_,g,gl) = 
      if dmem g (!solved) 
      then ()
      else 
        if all (fn x => dmem x psolved) gl
        then solved := dadd g lvl (!solved)
        else ()
  in
    app f lbls
  end
  
fun update_solved_loop solved lvl lbls =
  let val psolved = !solved in
    update_solved_lvl psolved solved lvl lbls;
    if dlength (!solved) <= dlength psolved 
      then debug ("Maximal height: " ^ int_to_string (lvl - 1)) 
      else update_solved_loop solved (lvl + 1) lbls
  end
  
fun create_solved lbls =
  let val solved = ref (dempty goal_compare) in
    update_solved_loop solved 1 lbls;
    !solved
  end

(*----------------------------------------------------------------------------
 * Orthogonalization
 *----------------------------------------------------------------------------*)

(* todo : timeout tactic_of_sml as the construction of the tactic may loop *)
fun test_stac g gl stac =
  let val ((new_gl,_),t) = 
    (
    debug ("test_stac " ^ stac);
    add_time (timeOut (!hhs_tactic_time) (tactic_of_sml stac)) g
    )
  in
    if all (fn x => mem x gl) new_gl
    then SOME (stac,t,g,gl)
    else NONE
  end
  handle _ => NONE

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in 
    String.concatWith " " ["(","DB.fetch",mlquote a,mlquote b,")"] 
  end

fun orthogonalize lbls (lbl as (ostac,t,g,gl),fea) =
  if !hhs_ortho_flag
  then
    let
      val feavectl = stacknn_ext (!hhs_ortho_number) (dlist (!hhs_stacfea)) fea
      val _ = debug (string_of_goal g)
      val stacl    = map (#1 o fst) feavectl
      val stacl2   = filter (fn x => not (x = ostac)) stacl
      
      val solved = create_solved lbls (* could be local or global labels *)
      val ext_gl = 
        if !hhs_ortho_deep andalso dmem g solved then 
          let 
            val n = dfind g solved 
            fun is_shorter g' = dfind g' solved < n handle _ => false
            val new_gl = filter is_shorter (dkeys solved)
          in
            mk_fast_set goal_compare (gl @ new_gl)
          end
        else gl
      
      val testl    = lbl :: (List.mapPartial (test_stac g ext_gl) stacl2)
      fun score x  = dfind (#1 x) (!hhs_ndict) handle _ => 0
      fun n_compare (x,y) = Int.compare (score y, score x) 
      val sortedl  = dict_sort n_compare testl
    in
      hd sortedl
    end
  else lbl

(* ---------------------------------------------------------------------------
   Success rates of each tactic. To be removed.
   -------------------------------------------------------------------------- *)

val succ_cthy_dict = ref (dempty String.compare)
val succ_glob_dict = ref (dempty String.compare)

fun count_try stac = 
  if !hhs_succrate_flag then 
  let 
    val (succ1,try1) = dfind stac (!succ_cthy_dict) handle _ => (0,0)
    val (succ2,try2) = dfind stac (!succ_glob_dict) handle _ => (0,0)
  in
    succ_cthy_dict := dadd stac (succ1,try1 + 1) (!succ_cthy_dict);
    succ_glob_dict := dadd stac (succ2,try2 + 1) (!succ_glob_dict)
  end
  else ()
  
fun count_succ stac = 
  if !hhs_succrate_flag then 
  let 
    val (succ1,try1) = dfind stac (!succ_cthy_dict) handle _ => (0,0)
    val (succ2,try2) = dfind stac (!succ_glob_dict) handle _ => (0,0)
  in
    succ_cthy_dict := dadd stac (succ1 + 1,try1) (!succ_cthy_dict);
    succ_glob_dict := dadd stac (succ2 + 1,try2) (!succ_glob_dict)
  end
  else ()

fun inv_succrate stac =
  if !hhs_succrate_flag
  then
    let val (succ,try) = dfind stac (!succ_glob_dict) in
      Real.fromInt (10 + try) / Real.fromInt (succ + 1)
    end
  else 1.0

(*----------------------------------------------------------------------------
 * I/O success rates. To be removed.
 *----------------------------------------------------------------------------*)

val succrate_reader = ref []

fun mk_string_list sl = "[" ^ String.concatWith "," sl ^ "]"

fun read_succrate thy =
  if mem thy ["min","bool"] then () else
  let
    val sl = readl (hhs_succrate_dir ^ "/" ^ thy) 
             handle _ => (print_endline ("File not found:" ^ thy); [])
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
  print_endline "Reading success rates...";
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
