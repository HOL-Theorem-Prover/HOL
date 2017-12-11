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
 * Recognizing theorem list and abstracting them from the tactic.
 *----------------------------------------------------------------------------*)

val thm_cache = ref (dempty String.compare)

fun is_thm_cache s =
  dfind s (!thm_cache) handle _ => 
  let val b = is_thm s in
    thm_cache := dadd s b (!thm_cache);
    b
  end

val thmlarg_placeholder = "tactictoe_thmlarg"

fun is_thmlarg_stac stac = mem thmlarg_placeholder (hhs_lex stac)
 
fun change_thml el e =
  if is_thm_cache (String.concatWith " " e)
  then SOME ["[",thmlarg_placeholder,"]"]
  else NONE
    
fun abstract_thmlarg_loop l = case l of
    []       => []
  | "[" :: m => 
    let val (el,cont) = split_level "]" m
        val e = fst (split_level "," el) handle _ => el
    in
      case change_thml el e of
        NONE => "[" :: abstract_thmlarg_loop m
      | SOME x => x @ abstract_thmlarg_loop cont
    end
  | a :: m => a :: abstract_thmlarg_loop m

fun abstract_thmlarg stac = 
  if is_thmlarg_stac stac then stac else 
  let 
    val sl1 = hhs_lex stac
    val sl2 = abstract_thmlarg_loop sl1
  in
    if sl2 = sl1 then stac else String.concatWith " " sl2
  end

(*----------------------------------------------------------------------------
 * Instantiating tactics with predicted theorems
 *----------------------------------------------------------------------------*)

fun inst_thmlarg_loop thmls l = 
  let fun f x = if x = thmlarg_placeholder then thmls else x in
    map f l
  end

fun inst_thmlarg thmls stac =
  let val sl = hhs_lex stac in
    if mem thmlarg_placeholder sl
    then String.concatWith " " (inst_thmlarg_loop thmls sl)
    else stac
  end

(* 
val s = "METIS_TAC [arithmeticTheory.LESS_EQ]";
val s1 = abstract_stac s;
val s2 = inst_thmlarg "bonjour" s1;
*)

(*----------------------------------------------------------------------------
 * Abstracting term
 *----------------------------------------------------------------------------*)

val termarg_placeholder = "tactictoe_termarg"

fun is_termarg_stac stac = mem termarg_placeholder (hhs_lex stac)

fun abstract_termarg_loop l = case l of
    []       => []
  | "[" :: "HolKernel.QUOTE" :: s :: "]" :: m => 
    let val new_s = ["(",termarg_placeholder,s,")"] in
      ["[","HolKernel.QUOTE"] @ new_s @ ["]"] @ abstract_termarg_loop m
    end
  | a :: m => a :: abstract_termarg_loop m

fun abstract_termarg stac =
  if is_termarg_stac stac then stac else 
  let 
    val sl1 = hhs_lex stac
    val sl2 = abstract_termarg_loop sl1
  in
    if sl2 = sl1 then stac else String.concatWith " " sl2
  end

(*----------------------------------------------------------------------------
 * Instantiating tactics with predicted term
 *----------------------------------------------------------------------------*)

fun with_types f x =
  let 
    val mem = !show_types
    val _ = show_types := true
    val r = f x
    val _ = show_types := mem
  in
    r
  end
  
fun predict_termarg g s =
  let
    val term = Parse.Term [QUOTE (unquote_string s)] 
    val new_term = closest_subterm g term
    val new_s = if new_term = term 
                then s 
                else "\"" ^ with_types term_to_string new_term ^ "\""       
  in
    new_s
  end          

fun inst_termarg_loop g l = case l of
    [] => []
  | "(" :: termlarg_placeholder :: s :: ")" :: m =>
    predict_termarg g s :: inst_termarg_loop g m
  | a :: m => a :: inst_termarg_loop g m  

fun inst_termarg g stac =
  let val sl = hhs_lex stac in
    if mem termarg_placeholder sl
    then String.concatWith " " (inst_termarg_loop g sl)
    else stac
  end

(* 
load "hhsLearn";
val s = 
"boolLib.SPEC_TAC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 119422*)m:num\""
^ " ] ) , ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 119435*)m:num\" ] ) )";
val goal:goal = ([],``!x. x = x``);
val s1 = abstract_termarg s;
val s2 = inst_termarg g s1;
*)

(*----------------------------------------------------------------------------
   Combining abstractions and instantiations
 *----------------------------------------------------------------------------*)

fun is_absarg_stac s = is_termarg_stac s orelse is_thmlarg_stac s

fun abstract_stac stac =
  let 
    val stac1 = if !hhs_thmlarg_flag then abstract_thmlarg stac else stac
    val stac2 = if !hhs_termarg_flag then abstract_termarg stac1 else stac1
  in
    if stac2 <> stac then SOME stac2 else NONE
  end

fun prefix_absstac stac = [abstract_stac stac, SOME stac]

fun concat_absstacl ostac stacl = 
  let val l = List.concat (map prefix_absstac stacl) @ [abstract_stac ostac] in
    mk_sameorder_set String.compare (List.mapPartial I l)
  end

fun inst_stac thmls g stac =
  let 
    val stac1 = if !hhs_thmlarg_flag then inst_thmlarg thmls stac else stac
    val stac2 = if !hhs_termarg_flag then inst_termarg g stac1 else stac1
  in
    stac2
  end

fun inst_stacl thmls g stacl = map (fn x => (x, inst_stac thmls g x)) stacl

(*----------------------------------------------------------------------------
 * Orthogonalization.
 *----------------------------------------------------------------------------*)

fun test_stac g gl (stac, istac) =
  let val ((new_gl,_),t) = 
    (
    (* debug ("test_stac " ^ stac ^ "\n" ^ istac); *)
    let val tac = timeOut (!hhs_tactic_time) tactic_of_sml istac in
      add_time (timeOut (!hhs_tactic_time) tac) g
    end
    )
  in
    if all (fn x => mem x gl) new_gl
    then SOME (stac,t,g,new_gl)
    else NONE
  end
  handle _ => NONE

fun orthogonalize (lbl as (ostac,t,g,gl),fea) =
  if !hhs_ortho_flag
  then
    let
      (* predict tactics *)
      val feavl0 = dlist (!hhs_stacfea)
      val feavl1 = stacknn_ext hhs_predict_dir (!hhs_ortho_number) feavl0 fea
      val stacl1 = mk_sameorder_set String.compare (map (#1 o fst) feavl1)
      val stacl2 = filter (fn x => not (x = ostac)) stacl1     
      (* order tactics by frequency *)
      fun score x = dfind x (!hhs_ndict) handle _ => 0
      val oscore  = score ostac
      val stacl3  = filter (fn x => score x > oscore) stacl2
      fun n_compare (x,y) = Int.compare (score y, score x) 
      val stacl4 = dict_sort n_compare stacl3
      (* try abstracted tactic x before x *)
      val stacl5 = concat_absstacl ostac stacl4
      (* predicting theorems only once *)
      val thml   = theorem_predictor (!hhs_thmorthoarg_flag)
        (!hhs_thmlarg_number) g
      val thmls  = String.concatWith " , " (map dbfetch_of_string thml)
      (* instantiate arguments *)
      val stacl6 = inst_stacl thmls g stacl5
      (* test produced tactics *)
      val testo  = findSome (test_stac g gl) stacl6
    in
      case testo of
        NONE => lbl
      | SOME newlbl => newlbl
    end
  else lbl

end (* struct *)
