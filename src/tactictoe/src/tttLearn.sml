(* ========================================================================== *)
(* FILE          : tttLearn.sml                                               *)
(* DESCRIPTION   : Learning from tactic calls during search and recording     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttLearn :> tttLearn =
struct

open HolKernel boolLib Abbrev tttTools tttPredict tttExec tttMinimize
tttTimeout tttFeature tttThmData tttGoallistData tttSetup tttLexer

val ERR = mk_HOL_ERR "tttLearn"

(*----------------------------------------------------------------------------
 * Abstracting theorem list in tactics
 *----------------------------------------------------------------------------*)

val thm_cache = ref (dempty String.compare)

fun is_thm_cache s =
  dfind s (!thm_cache) handle _ =>
  let val b = hide_out is_thm s in
    thm_cache := dadd s b (!thm_cache);
    b
  end

val thmlarg_placeholder = "tactictoe_thmlarg"

fun is_thmlarg_stac stac = mem thmlarg_placeholder (ttt_lex stac)

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
    val sl1 = ttt_lex stac
    val sl2 = abstract_thmlarg_loop sl1
  in
    if sl2 = sl1 then stac else String.concatWith " " sl2
  end

(*----------------------------------------------------------------------------
 * Instantiating tactics with theorem list
 *----------------------------------------------------------------------------*)

fun inst_thmlarg_loop thmls l =
  let fun f x = if x = thmlarg_placeholder then thmls else x in
    map f l
  end

fun inst_thmlarg thmls stac =
  let val sl = ttt_lex stac in
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
 * Abstracting term (first occurence)
 *----------------------------------------------------------------------------*)

val termarg_placeholder = "tactictoe_termarg"

fun abs_termarg_loop l = case l of
    []       => ([], NONE)
  | "[" :: "HolKernel.QUOTE" :: s :: "]" :: m =>
    (termarg_placeholder :: m, SOME s)
  | "[" :: "QUOTE" :: s :: "]" :: m =>
    (termarg_placeholder :: m, SOME s)
  | a :: m =>
    let val (sl,so) = abs_termarg_loop m in (a :: sl, so) end

fun abs_termarg stac =
  let
    val sl1 = ttt_lex stac
    val (sl2,so) = abs_termarg_loop sl1
  in
    case so of
      NONE => NONE
    | SOME s =>
    let
      val qtacs = String.concatWith " "
        (["fn", termarg_placeholder,"=>", "Tactical.VALID","("] @ sl2 @ [")"])
      val qtac = qtactic_of_sml qtacs
    in
      if is_stype s then NONE else SOME (term_of_sml s, qtac)
    end
  end
  handle _ => (debug ("Error: abs_termarg: " ^ stac); NONE)

(*----------------------------------------------------------------------------
 * Instantiate tactics with term
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

fun inst_termarg_loop term l = case l of
    [] => []
  | "[" :: "HolKernel.QUOTE" :: _ :: "]" :: m =>
    "[" :: "HolKernel.QUOTE" :: mlquote (with_types term_to_string term) :: "]" :: m
  | "[" :: "QUOTE" :: s :: "]" :: m =>
    "[" :: "QUOTE" :: mlquote (with_types term_to_string term) :: "]" :: m
  | a :: m => a :: inst_termarg_loop term m

fun inst_termarg stac term =
  String.concatWith " " (inst_termarg_loop term (ttt_lex stac))

(*
load "tttLearn";
val stac =
"boolLib.SPEC_TAC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 119422*)m:num\""
^ " ] ) , ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 119435*)m:num\" ] ) )";
val stac2 = tttLearn.inst_termarg stac ``v:num``;
val tac = tttExec.tactic_of_sml stac2;

val s = mlquote (term_to_string ``A /\ B``);
val s1 = "SPEC_TAC (Term [QUOTE \"x:bool\"],Term[QUOTE" ^ s ^ "])";
val tac = tttExec.tactic_of_sml s1;
*)

(*----------------------------------------------------------------------------
   Combining abstractions and instantiations
 *----------------------------------------------------------------------------*)

fun is_absarg_stac s = is_thmlarg_stac s

fun abstract_stac stac =
  let
    val stac1 =
      if !ttt_thmlarg_flag
      then abstract_thmlarg stac
      else stac
  in
    if stac1 <> stac then SOME stac1 else NONE
  end

fun prefix_absstac stac = [abstract_stac stac, SOME stac]

fun concat_absstacl ostac stacl =
  let val l = List.concat (map prefix_absstac stacl) @ [abstract_stac ostac] in
    mk_sameorder_set String.compare (List.mapPartial I l)
  end

fun inst_stac thmls g stac =
  if !ttt_thmlarg_flag then inst_thmlarg thmls stac else stac

fun inst_stacl thmls g stacl = map (fn x => (x, inst_stac thmls g x)) stacl

(*----------------------------------------------------------------------------
 * Orthogonalization.
 *----------------------------------------------------------------------------*)

fun record_glfea b (g,gl) =
  if !ttt_recgl_flag 
  then update_glfea (fea_of_goallist gl) (b,(hash_goal g))
  else ()
  
val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun test_stac g gl (stac, istac) =
  let val (new_gl,_) =
    (
    debug ("test_stac " ^ stac ^ "\n" ^ istac);
    let val tac = timed_tactic_of_sml istac
      handle _ => (debug ("Warning: infinite stac: " ^ stac); NO_TAC)
    in
      timeOut (!ttt_tactic_time) (TC_OFF tac) g
    end
    )
  in
    if all (fn x => mem x gl) new_gl
    then (record_glfea true (g,new_gl); SOME (stac,0.0,g,new_gl))
    else (record_glfea false (g,new_gl); NONE)
  end
  handle _ => NONE

fun orthogonalize (lbl as (ostac,t,g,gl),fea) =
  if !ttt_ortho_flag
  then
    let
      (* predict tactics *)
      val _ = debug "predict tactics"
      val feavl0 = dlist (!ttt_tacfea)
      val symweight = learn_tfidf feavl0
      val lbls = stacknn symweight (!ttt_ortho_radius) feavl0 fea
      val stacl1 = mk_sameorder_set String.compare (map #1 lbls)
      val stacl2 = filter (fn x => not (x = ostac)) stacl1
      (* order tactics by frequency *)
      val _ = debug "order tactics"
      fun score x = dfind x (!ttt_taccov) handle _ => 0
      val oscore  = score ostac
      val stacl3  = filter (fn x => score x > oscore) stacl2
      fun n_compare (x,y) = Int.compare (score y, score x)
      val stacl4 = dict_sort n_compare stacl3
      (* try abstracted tactic x before x *)
      val _ = debug "concat abstract tactics"
      val stacl5 = concat_absstacl ostac stacl4
      (* predicting theorems only once *)
      val _ = debug "predict theorems"
      val thml =
        if !ttt_thmlarg_flag
        then thmknn_std (!ttt_thmlarg_radius) g
        else []
      val thmls  = String.concatWith " , " (map dbfetch_of_string thml)
      (* instantiate arguments *)
      val _ = debug "instantiate argument"
      val stacl6 = inst_stacl thmls g stacl5
      (* test produced tactics *)
      val _ = debug "test tactics"
      val testo  = findSome (test_stac g gl) stacl6
    in
      case testo of
        NONE => lbl
      | SOME newlbl => newlbl
    end
  else lbl

end (* struct *)
