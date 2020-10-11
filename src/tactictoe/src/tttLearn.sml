(* ========================================================================= *)
(* FILE          : tttLearn.sml                                              *)
(* DESCRIPTION   : Re-addressing tactic ownership of goals during recording  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttLearn :> tttLearn =
struct

open HolKernel Abbrev boolLib aiLib
  smlTimeout smlLexer smlParser smlExecute
  mlFeature mlThmData mlTacticData mlNearestNeighbor mlTreeNeuralNetwork
  psMinimize tttSetup tttToken

val ERR = mk_HOL_ERR "tttLearn"

(* -------------------------------------------------------------------------
   Combining multiple abstractions
   ------------------------------------------------------------------------- *)

fun abstract_stac stac =
  (
  if is_thmlstac stac orelse is_termstac stac then NONE else
  case abstract_thml stac of
    SOME (thmlstac,_) => SOME thmlstac
  | NONE => 
    (if not (!learn_abstract_term) then NONE else
    case abstract_term stac of
      SOME (termstac,_) => SOME termstac
    | NONE => NONE)
  )
  handle Interrupt => raise Interrupt | _ =>
    (debug ("error: abstract_stac: " ^ stac); NONE)

fun concat_absstacl gfea stac stacl =
  let
    fun f x = [abstract_stac x, SOME x]
    val l = List.concat (map f stacl) @ [abstract_stac stac]
  in
    mk_sameorder_set String.compare (List.mapPartial I l)
  end

(* -------------------------------------------------------------------------
   Predictions + re-ordering according to coverage
   ------------------------------------------------------------------------- *)

fun pred_stac (tacsymweight,tacfea) ostac fea =
  let val stacl = tacknn (tacsymweight,tacfea) (!ttt_ortho_radius) fea in
    filter (fn x => not (x = ostac)) stacl
  end

fun pred_thmid thmdata fea =
  thmknn thmdata (!ttt_thmlarg_radius) fea

fun unterm_var v =
  let val (vs,ty) = dest_var v in vs end

fun respace s = String.concatWith " " (partial_sml_lexer s)

fun unterm_var_alt v =
  let val (vs,ty) = dest_var v in [vs, respace vs] end

fun pred_svar n goal = 
  first_n n (map unterm_var (find_terms is_var (snd goal)))

fun pred_svar_alt n goal = 
  let 
    val vl1 = find_terms is_var (snd goal)
    val vl2 = List.concat (map unterm_var_alt vl1)
  in
    first_n (2 * n) vl2 
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

(* -------------------------------------------------------------------------
   Instantiations (* todo: speedup by preparsing tokenl *)
   ------------------------------------------------------------------------- *)

fun inst_arg (thmidl,sterml) stac =
  if is_thmlstac stac then 
    [(stac, inst_thml thmidl stac)]
  else if is_termstac stac then  
    map (fn x => (stac, inst_term x stac)) sterml
  else [(stac,stac)]

(* -------------------------------------------------------------------------
   Testing if a predicted tactic as a "better effect" than the original
   ------------------------------------------------------------------------- *)

fun op_subset eqf l1 l2 = null (op_set_diff eqf l1 l2)
val goal_subset = op_subset goal_eq

fun test_stac g gl (stac, istac) =
  let
    val _ = debug "test_stac"
    val glo = app_stac (!learn_tactic_time) istac g
  in
    case glo of NONE => NONE | SOME newgl =>
      (if goal_subset newgl gl then SOME stac else NONE)
  end

(* -------------------------------------------------------------------------
   Updates the original label if a better tactic is found
   ------------------------------------------------------------------------- *)

val ortho_predstac_time = ref 0.0
val ortho_predthm_time = ref 0.0
val ortho_teststac_time = ref 0.0

fun orthogonalize (thmdata,tacdata,(tacsymweight,tacfea))
  (call as {stac,ortho,time,ig,ogl,loc,fea}) =
  let
    val _ = debug "predict tactics"
    val stacl1 = total_time ortho_predstac_time
      (pred_stac (tacsymweight,tacfea) stac) fea
    val _ = debug "order tactics"
    val stacl2 = order_stac tacdata stac stacl1
    val _ = debug "abstract tactics"
    val stacl3 = concat_absstacl fea stac stacl2
    val _ = debug "predict arguments"
    val thmidl = total_time ortho_predthm_time (pred_thmid thmdata) fea
    val sterml = pred_svar 8 ig
    val _ = debug "instantiate arguments"
    val stacl4 = List.concat (map (inst_arg (thmidl,sterml)) stacl3)
    val _ = debug "test tactics"
    val (neworthoo,t) = add_time (findSome (test_stac ig ogl)) stacl4
    val _ = debug ("test time: " ^ rts t)
    val _ = ortho_teststac_time := !ortho_teststac_time + t
  in
    case neworthoo of NONE => call | SOME newortho =>
      {stac = stac, ortho = newortho, time = time,
       ig = ig, ogl = ogl, loc = loc, fea = fea}
  end
  handle Interrupt => raise Interrupt | _ =>
    (debug "error: orthogonalize"; call)

fun abstract_only_thml thmdata fea (thmlstac,sll) =
  let 
    val thmidl = total_time ortho_predthm_time (pred_thmid thmdata) fea
    val sthmli = List.concat sll
    val sthmlp = map dbfetch_of_thmid thmidl
    val (thmli,thmlp) = part_n (length sthmli) 
      (valOf (thml_of_sml (sthmli @ sthmlp))) 
      handle Interrupt => raise Interrupt | _ =>
      (debug "error: thml_of_sml"; raise ERR "" "break")
  in
    if goal_subset (map dest_thm thmli) (map dest_thm thmlp)
    then SOME thmlstac
    else NONE
  end
    
fun abstract_only_term ig (termstac,sterm) =
  let 
    val sterm1 = respace sterm
    val sterml2 = pred_svar_alt 8 ig
  in
    if mem sterm1 sterml2 then SOME termstac else NONE
  end

fun abstract_only thmdata
  (call as {stac,ortho,time,ig,ogl,loc,fea}) =
  let val neworthoo = 
    case abstract_thml stac of
      SOME x => abstract_only_thml thmdata fea x 
    | NONE => 
    (if not (!learn_abstract_term) then NONE else
    case abstract_term stac of
      SOME x => abstract_only_term ig x
    | NONE => NONE)
  in
    case neworthoo of NONE => call | SOME newortho =>
    {stac = stac, ortho = newortho, time = time,
     ig = ig, ogl = ogl, loc = loc, fea = fea}
  end
  handle Interrupt => raise Interrupt | _ =>
    (debug "error: abstract_only"; call)



end (* struct *)
