(* ------------------------------------------------------------------------- *)
(* Some miscellaneous tools for reasoning about boolean sequences.           *)
(* ------------------------------------------------------------------------- *)

structure boolean_sequenceTools :> boolean_sequenceTools = 
struct

open HolKernel Parse boolLib;
open bossLib prob_extraTheory boolean_sequenceTheory probUtil;

infixr 0 ++ || ORELSEC ## THENC;
infix 1 >>;
nonfix THEN ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Error handling.                                                           *)
(* ------------------------------------------------------------------------- *)

val ERROR = mk_HOL_ERR "boolean_sequenceTools";
fun assert_false f s = raise ERROR f s;
fun assert b f s = if b then () else assert_false f s;

(* ------------------------------------------------------------------------- *)
(* A sequence `cases' tactic.                                                *)
(* ------------------------------------------------------------------------- *)

fun POP_ALL_THEN (tac:tactic) ([], g) = tac ([], g)
  | POP_ALL_THEN tac (a::al, g)
  = (POP_ASSUM MP_TAC ++ POP_ALL_THEN tac ++ (DISCH_TAC || ALL_TAC))
    (a::al, g);

fun SEQ_CASES_TAC v (al, g)
  = let val vtm = parse_with_goal v (al, g)
    in (KNOW_TAC `?h t. ^vtm = SCONS h t` >> PROVE_TAC [SCONS_SURJ]
	++ POP_ASSUM (fn th => POP_ALL_THEN (PURE_REWRITE_TAC [th]))) (al, g)
    end;

end;
