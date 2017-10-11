(* ========================================================================== *)
(* FILE          : hhsLearn.sml                                               *)
(* DESCRIPTION   : Learning from tactic calls during search and recording     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsLearn :> hhsLearn =
struct

open HolKernel boolLib Abbrev hhsTools hhsPredict hhsExec hhsMinimize 
hhsTimeout hhsFeature hhsMetis hhsSetup hhsLexer

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
        then 
          let val nodes = sum_int (map (fn x => snd (dfind x psolved)) gl) in
            solved := dadd g (lvl,nodes) (!solved)
          end
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

fun add_astar gl b =
  let val fea = fea_of_gl gl in
    if (dfind fea (!hhs_astar) handle _ => false)
    then ()
    else 
      (hhs_astar_cthy := dadd fea b (!hhs_astar_cthy);
       hhs_astar := dadd fea b (!hhs_astar))
  end  

(* deep ortho 
  val solved = create_solved lbls
  val ext_gl = 
    if !hhs_astar_flag andalso dmem g solved then 
      let      
        val (h,n) = dfind g solved 
        fun is_shorter g' = fst (dfind g' solved) < h handle _ => false
        val new_gl = filter is_shorter (dkeys solved)
      in
        mk_fast_set goal_compare (gl @ new_gl)
      end
    else gl
*)
(* closest first *)

(*----------------------------------------------------------------------------
 * Recognizing theorem list and abstracting them from the tactic.
 *----------------------------------------------------------------------------*)

val thm_cache = ref (dempty String.compare)

fun is_thm_cache s =
  dfind s (!thm_cache) handle _ => 
    let val b = is_thm s in
      thm_cache := dadd s b (!thm_cache);
      b
    end
 
val pattern_thml = "tactictoe_pattern_thml"
 
fun is_pattern_stac stac = mem pattern_thml (hhs_lex stac)
 
fun change_thml el e =
  if is_thm_cache (String.concatWith " " e)
  then SOME ["[",pattern_thml,"]"]
  else NONE
    
fun abstract_loop l = case l of
    []       => []
  | "[" :: m => 
    let val (el,cont) = split_level "]" m
        val e = fst (split_level "," el) handle _ => el
    in
      case change_thml el e of
        NONE => "[" :: abstract_loop m
      | SOME x => x @ abstract_loop cont
    end
  | a :: m => a :: abstract_loop m

fun abstract_stac stac = 
  let 
    val sl1 = hhs_lex stac
    val sl2 = abstract_loop sl1
    val r = String.concatWith " " sl2
  in
    if sl1 <> sl2 then debug ("abstraction: " ^ r) else (); 
    r
  end

fun inst_stac_loop thmls l = 
  let fun f x = if x = pattern_thml then thmls else x in
    map f l
  end

fun inst_stac thmls stac =
  let val tokenl = hhs_lex stac in
    if mem pattern_thml tokenl
    then 
      let val r = String.concatWith " " (inst_stac_loop thmls tokenl) in
        debug ("instantiation: " ^ r); r
      end
    else stac
  end

(* 
val s = "METIS_TAC [arithmeticTheory.LESS_EQ]";
val s1 = abstract_stac s;
val s2 = inst_stac "bonjour" s1;
*)

(*----------------------------------------------------------------------------
 * Orthogonalization. Astar and stacpred not compatible.
 *----------------------------------------------------------------------------*)

fun test_stac g gl (stac, inst_stac) =
  let val ((new_gl,_),t) = 
    (
    debug ("test_stac " ^ stac ^ "\n  " ^ inst_stac);
    let val tac = timeOut (!hhs_tactic_time) tactic_of_sml inst_stac in
      add_time (timeOut (!hhs_tactic_time) tac) g
    end
    )
  in
    if all (fn x => mem x gl) new_gl
    then SOME (stac,t,g,gl)
    else NONE
  end
  handle _ => NONE

(* need timeout tactic_of_sml here and instantiation *)
fun test_astar g gl stac =
  let val ((new_gl,_),t) = 
    (
    debug ("test_astar " ^ stac);
    add_time (timeOut (!hhs_tactic_time) (tactic_of_sml stac)) g
    )
  in
    if all (fn x => mem x gl) new_gl
    then (add_astar new_gl true; SOME (stac,t,g,gl))
    else (add_astar new_gl false; NONE)
  end
  handle _ => NONE

fun add_pattern_one stac =
  if is_pattern_stac stac then [stac] else 
    let val new_stac = abstract_stac stac in
      if is_pattern_stac new_stac
      then [new_stac,stac] (* more general pattern first *)
      else [stac]
    end  

fun add_only_pattern stac =
  if is_pattern_stac stac orelse not (!hhs_stacpred_flag) then [] else 
    let val new_stac = abstract_stac stac in
      if is_pattern_stac new_stac
      then [new_stac]
      else []
    end  

fun add_pattern stacl = List.concat (map add_pattern_one stacl)

fun duplicate_stacl g stacl =
  if !hhs_stacpred_flag 
  then
    let
      val stacl' = mk_sameorder_set String.compare (add_pattern stacl)     
      val thml   = predict_for_metis (!hhs_stacpred_number) g
      val thmls  = String.concatWith " , " (map dbfetch_of_string thml)
    in
      map (fn x => (x, inst_stac thmls x)) stacl'
    end
  else map (fn x => (x,x)) stacl

(* to do abstract ostac itself *)
fun orthogonalize lbls (lbl as (ostac,t,g,gl),fea) =
  if !hhs_ortho_flag
  then
    let
      val _ = debug (string_of_goal g)
      val feavectl = stacknn_ext (!hhs_ortho_number) (dlist (!hhs_stacfea)) fea
      val stacl = mk_sameorder_set String.compare (map (#1 o fst) feavectl)
      val stacl2 = filter (fn x => not (x = ostac)) stacl
      val _ = 
        if !hhs_astar_flag 
        then ignore (findSome (test_astar g gl) stacl)
        else ()           
      (* order tactics by frequency *)
      fun score x = dfind x (!hhs_ndict) handle _ => 0
      val oscore  = score ostac
      val stacl3  = filter (fn x => score x > oscore) stacl2
      fun n_compare (x,y) = Int.compare (score y, score x) 
      val stacl4 = dict_sort n_compare stacl3
      (* abstract and instantiate tactics *)
      val stacl5 = duplicate_stacl g (stacl4 @ add_only_pattern ostac)
      val testo  = findSome (test_stac g gl) stacl5
    in
      case testo of
        NONE => lbl
      | SOME newlbl => newlbl
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
