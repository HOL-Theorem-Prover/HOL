(* ========================================================================= *)
(* FILE          : tttLearn.sml                                              *)
(* DESCRIPTION   : Learning from tactic calls during search and recording    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttLearn :> tttLearn =
struct

open HolKernel Abbrev boolLib aiLib
  smlTimeout smlLexer smlExecute
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  psMinimize tttSetup

val ERR = mk_HOL_ERR "tttLearn"
fun debug s = debug_in_dir ttt_debugdir "tttLearn" s

(* -------------------------------------------------------------------------
   Abstracting theorem list in tactics
   ------------------------------------------------------------------------- *)

val thmlarg_placeholder = "tactictoe_thmlarg"

fun is_thmlarg_stac stac =
  mem thmlarg_placeholder (partial_sml_lexer stac)

fun change_thml thml = case thml of
    [] => NONE
  | a :: m => (if is_thm (String.concatWith " " a) then SOME thml else NONE)

fun abstract_thmlarg_loop thmlacc l = case l of
    []       => []
  | "[" :: m =>
    let
      val (el,cont) = split_level "]" m
      val thml = rpt_split_level "," el
    in
      case change_thml thml of
        NONE => "[" :: abstract_thmlarg_loop thmlacc m
      | SOME x =>
        (
        thmlacc := map (String.concatWith " ") thml :: !thmlacc;
        ["[",thmlarg_placeholder,"]"] @
          abstract_thmlarg_loop thmlacc cont
        )
    end
  | a :: m => a :: abstract_thmlarg_loop thmlacc m

fun abstract_thmlarg stac =
  if is_thmlarg_stac stac then stac else
  let
    val sl1 = partial_sml_lexer stac
    val sl2 = abstract_thmlarg_loop (ref []) sl1
  in
    if sl2 = sl1 then stac else String.concatWith " " sl2
  end

(* -------------------------------------------------------------------------
   Instantiating abstracted tactic with a list of theorems
   ------------------------------------------------------------------------- *)

fun inst_thmlarg_loop thmls l =
  let fun f x = if x = thmlarg_placeholder then thmls else x in
    map f l
  end

fun inst_thmlarg thmls stac =
  let val sl = partial_sml_lexer stac in
    if mem thmlarg_placeholder sl
    then String.concatWith " " (inst_thmlarg_loop thmls sl)
    else stac
  end

(* -------------------------------------------------------------------------
   Combining abstractions and instantiations
   ------------------------------------------------------------------------- *)

fun abstract_stac stac =
  let val absstac = abstract_thmlarg stac in
    if absstac <> stac then SOME absstac else NONE
  end

fun prefix_absstac stac = [abstract_stac stac, SOME stac]

fun concat_absstacl ostac stacl =
  let
    val l = List.concat (map prefix_absstac stacl) @ [abstract_stac ostac]
  in
    mk_sameorder_set String.compare (List.mapPartial I l)
  end

fun inst_stac thmidl stac =
  let val thmls = String.concatWith " , " (map dbfetch_of_thmid thmidl) in
    inst_thmlarg thmls stac
  end

fun inst_stacl thmidl stacl = map_assoc (inst_stac thmidl) stacl

(* -------------------------------------------------------------------------
   Orthogonalization
   ------------------------------------------------------------------------- *)

fun pred_stac tacdata ostac gfea =
  let
    val tacfea = dlist (#tacfea tacdata)
    val symweight = learn_tfidf tacfea
    val stacl = stacknn_uniq (symweight,tacfea) (!ttt_ortho_radius) gfea
  in
    filter (fn x => not (x = ostac)) stacl
  end

fun order_stac tacdata ostac stacl =
   let
     fun covscore x = dfind x (#taccov tacdata) handle NotFound => 0
     val oscore  = covscore ostac
     val stacl'  = filter (fn x => covscore x > oscore) stacl
     fun covcmp (x,y) = Int.compare (covscore y, covscore x)
   in
     dict_sort covcmp stacl'
   end

fun op_subset eqf l1 l2 = null (op_set_diff eqf l1 l2)
fun test_stac g gl (stac, istac) =
  let val glo =
    (
    debug ("test_stac " ^ stac ^ "\n" ^ istac);
    let val tac = tactic_of_sml istac
      handle Interrupt => raise Interrupt
      | _ => (debug ("Warning: tactic_of_sml: " ^ istac); NO_TAC)
    in
      timeout_tactic (!ttt_tactic_time) tac g
    end
    )
  in
    case glo of NONE => NONE | SOME newgl =>
      (if op_subset goal_eq newgl gl then
         SOME (stac,0.0,g,newgl)
       else NONE)
  end

val ortho_predstac_time = ref 0.0
val ortho_predthm_time = ref 0.0
val ortho_teststac_time = ref 0.0

fun orthogonalize (thmdata,tacdata) (lbl as (ostac,t,g,gl)) =
  let
    val gfea = feahash_of_goal g
    val _ = debug "predict tactics"
    val stacl1 = total_time ortho_predstac_time
      (pred_stac tacdata ostac) gfea
    val _ = debug "order tactics"
    val stacl2 = order_stac tacdata ostac stacl1
    val _ = debug "concat abstract tactics"
    val stacl3 = concat_absstacl ostac stacl2
    val _ = debug "predict theorems"
    val thml = total_time ortho_predthm_time
      (thmknn thmdata (!ttt_thmlarg_radius)) gfea
    val _ = debug "instantiate arguments"
    val stacl4 = inst_stacl thml stacl3
    val _ = debug "test tactics"
    val testo = total_time ortho_teststac_time
      (findSome (test_stac g gl)) stacl4
  in
    case testo of NONE => lbl | SOME newlbl => newlbl
  end


end (* struct *)

(* test
load "tttLearn"; open tttLearn;
val s0 = "METIS_TAC [arithmeticTheory.LESS_EQ]";
val s1 = abstract_stac s0;
val s2 = inst_stac "foo" (valOf s1);
*)
