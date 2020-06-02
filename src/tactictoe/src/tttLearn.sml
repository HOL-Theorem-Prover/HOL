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
fun debug_err s1 s2 = (debug (s1 ^ " : " ^ s2); raise ERR s1 s2)

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
        thmlarg_placeholder :: abstract_thmlarg_loop thmlacc cont
        )
    end
  | a :: m => a :: abstract_thmlarg_loop thmlacc m

fun abstract_thmlarg stac =
  if is_thmlarg_stac stac then NONE else
  let
    val sl1 = partial_sml_lexer stac
    val thmllref = ref []
    val sl2 = abstract_thmlarg_loop thmllref sl1
  in
    if null (!thmllref)
    then NONE
    else SOME (String.concatWith " " sl2, !thmllref)
  end

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
   Abstracting first term in tactics
   ------------------------------------------------------------------------- *)

val termarg_placeholder = "tactictoe_termarg"

fun is_termarg_stac stac =
  mem termarg_placeholder (partial_sml_lexer stac)

fun is_quoted s = 
  let val n = String.size s in
    String.sub (s,0) = #"\"" andalso String.sub (s, n - 1) = #"\""
  end

fun abstract_termarg_loop termref l = case l of
    [] => []
  | "[" :: a :: b :: "]" :: m => 
    if drop_sig a = "QUOTE" andalso is_quoted b 
      then 
        (
        termref := SOME b;  
        "[" :: a :: "(" :: termarg_placeholder :: b :: ")" :: "]" ::  m
        )
      else hd l :: abstract_termarg_loop termref (tl l) 
  | a :: m => a :: abstract_termarg_loop termref m 

fun abstract_termarg stac =
  if is_termarg_stac stac then NONE else
  let
    val sl1 = partial_sml_lexer stac
    val termref = ref NONE
    val sl2 = abstract_termarg_loop termref sl1
  in
    if isSome (!termref)
    then SOME (String.concatWith " " sl2, valOf (!termref))
    else NONE
  end
  handle Interrupt => raise Interrupt | _ => 
    debug_err "Error: abstract_termarg" stac

fun pred_ssubterm (asl,w) stm =
  let 
    val tm = Parse.Term [QUOTE 
      (valOf (String.fromString (aiLib.unquote_string stm)))]
      handle Interrupt => raise Interrupt | _ => 
        debug_err "Error: pred_ssubterm" stm
    val mem = !show_types
    val tmll = map (find_terms (fn _ => true)) (w :: asl)
    val tml1 = mk_term_set (List.concat tmll)
    val tmfea = map_assoc (fn x => ~ (length tml1) :: feahash_of_term x) tml1
    val symweight = learn_tfidf tmfea
    val tml2 = termknn (symweight,tmfea) 1 (feahash_of_term tm)   
    val r = (show_types := true; term_to_string (hd tml2))
  in
    show_types := mem; r
  end
  handle Interrupt => raise Interrupt | _ => 
    debug_err "Error: pred_ssubterm" "unexpected"

fun inst_termarg_loop g l = case l of
    [] => []
  | "[" :: a :: "(" :: termarg_placeholder :: b :: ")" :: "]" ::  m => 
    "[" :: a :: mlquote (pred_ssubterm g b) :: "]" :: m 
  | a :: m => a :: inst_termarg_loop g m

fun inst_termarg g stac = 
  let val sl = partial_sml_lexer stac in
    if mem termarg_placeholder sl
    then String.concatWith " " (inst_termarg_loop g sl)
    else stac
  end

(* 
load "tttUnfold"; open tttUnfold;
load "tttLearn"; open tttLearn;
val stac = "EXISTS_TAC ``1:num``";
val stac' = unquote_string stac;
val (astac,sterm) = valOf (abstract_termarg stac');
val (asl,w) :goal = ([],``?x.x>0``);
val sl = ["0","3","2","1"];
val ((gl,_),s) = apply_termarg_stac_aux astac g sl;
val sl = pred_ssubterm (asl,w) "y:num";
*)

(* -------------------------------------------------------------------------
   Combining abstractions
   ------------------------------------------------------------------------- *)

fun abstract_stac stac = 
  let val a1 = abstract_thmlarg stac in
    if not (!learn_abstract_term) then Option.map fst a1 else
    let
      val a2 = abstract_termarg (if isSome a1 then fst (valOf a1) else stac)
    in
      if isSome a1 orelse isSome a2 
      then Option.map fst a2
      else NONE
    end
  end

fun concat_absstacl gfea stac stacl =
  let
    fun f x = [abstract_stac x, SOME x]
    val l = List.concat (map f stacl) @ [abstract_stac stac]
  in
    mk_sameorder_set String.compare (List.mapPartial I l)
  end

fun inst_stac (thmls,g) stac =
  let 
    val stac1 = inst_thmlarg thmls stac
    val stac2 = inst_termarg g stac1
  in
    (stac,stac2)
  end
  handle Interrupt => raise Interrupt | _ =>
    debug_err "Error: inst_stac" stac

fun inst_stacl (thmidl,g) stacl = 
  let val thmls = 
    "[ " ^ String.concatWith " , " (map dbfetch_of_thmid thmidl) ^ " ]"
  in
    mapfilter (inst_stac (thmls,g)) stacl
  end

(* -------------------------------------------------------------------------
   Orthogonalization
   ------------------------------------------------------------------------- *)

fun pred_stac tacdata ostac gfea =
  let
    val tacfea = map (fn x => (#ortho x,#fea x)) (#calls tacdata)
    val symweight = learn_tfidf tacfea
    val stacl = tacknn (symweight,tacfea) (!ttt_ortho_radius) gfea
    val no = List.find (fn x => fst x = ostac) (number_snd 0 stacl)
    val ns = case no of NONE => "none" | SOME (_,i) => its i
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
  let
    val _ = debug "test_stac"
    val (glo,t) = add_time (app_stac (!learn_tactic_time) istac) g
  in
    case glo of NONE => NONE | SOME newgl =>
      (if op_subset goal_eq newgl gl then SOME stac else NONE)
  end

val ortho_predstac_time = ref 0.0
val ortho_predthm_time = ref 0.0
val ortho_teststac_time = ref 0.0

fun orthogonalize (thmdata,tacdata) 
  (call as {stac,ortho,time,ig,ogl,loc,fea}) =
  let
    val _ = debug "predict tactics"
    val stacl1 = total_time ortho_predstac_time 
      (pred_stac tacdata stac) fea
    val _ = debug "order tactics"
    val stacl2 = order_stac tacdata stac stacl1
    val _ = debug "abstract tactics"
    val stacl3 = concat_absstacl fea stac stacl2
    val _ = debug "predict theorems"
    val thmidl = total_time ortho_predthm_time 
      (thmknn thmdata (!ttt_thmlarg_radius)) fea
    val _ = debug "instantiate arguments"
    val stacl4 = inst_stacl (thmidl,ig) stacl3
    val _ = debug "test tactics"
    val (neworthoo,t) = add_time (findSome (test_stac ig ogl)) stacl4
    val _ = debug ("test time: " ^ rts t)
    val _ = ortho_teststac_time := !ortho_teststac_time + t
  in
    case neworthoo of NONE => call | SOME newortho =>
      {stac = stac, ortho = newortho, 
       time = time, 
       ig = ig, ogl = ogl,
       loc = loc, fea = fea}
  end


end (* struct *)
