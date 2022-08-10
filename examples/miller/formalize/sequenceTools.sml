(* ------------------------------------------------------------------------- *)
(* Some miscellaneous tools for reasoning about boolean sequences.           *)
(* ------------------------------------------------------------------------- *)

structure sequenceTools :> sequenceTools =
struct

open HolKernel Parse boolLib;
open bossLib sequenceTheory hurdUtils;

infixr 0 ++ || ORELSEC ## THENC;
infix 1 >>;
nonfix THEN ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* A sequence `cases' tactic.                                                *)
(* ------------------------------------------------------------------------- *)

fun POP_ALL_THEN (tac:tactic) ([], g) = tac ([], g)
  | POP_ALL_THEN tac (a::al, g)
  = (POP_ASSUM MP_TAC ++ POP_ALL_THEN tac ++ (DISCH_TAC || ALL_TAC))
    (a::al, g);

fun SEQUENCE_CASES_TAC vtm =
  MP_TAC (ISPEC vtm SCONS_SURJ)
  ++ STRIP_TAC
  ++ POP_ASSUM (fn th => POP_ALL_THEN (PURE_REWRITE_TAC [th]));

val SEQ_CASES_TAC = Q_TAC SEQUENCE_CASES_TAC;

end;
