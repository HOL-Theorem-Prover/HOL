(* non-interactive mode
*)
structure realContext :> realContext =
struct
open HolKernel Parse boolLib;

(* interactive mode
if !show_assums then () else
 (loadPath := ".."::"../../prob"::(!loadPath);
  load "bossLib";
  load "pred_setTheory";
  load "millerTools";
  load "miller_extraTheory";
  show_assums := true);
*)

open bossLib pairTheory pred_setTheory extra_pred_setTheory
     res_quanTheory hurdUtils ho_basicTools ho_proverTools res_quanTools
     subtypeTools extra_realTheory numContext;

infixr 0 ++ || ORELSEC ## THENC THEN_TCL ORELSE_TCL;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op!! = op REPEAT;
val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* --------------------------------------------------------------------- *)
(* Subtype checking.                                                     *)
(* --------------------------------------------------------------------- *)

val real_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [POSREAL_ALT, NEGREAL_ALT, REAL_ZERO_SUBTYPE] @
  map SC_SUBTYPE
  [REAL_OF_NUM_SUBTYPE, NEG_SUBTYPE, INV_SUBTYPE, SQRT_SUBTYPE,
   REAL_ADD_SUBTYPE, REAL_SUB_SUBTYPE, REAL_MULT_SUBTYPE, REAL_DIV_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

(* Rules *)

(* Congruences *)

(* Rewrites *)

(* The module *)

val real_pc = precontext_add
  ("real",
   map C_SUBTYPE real_sc)
  num_pc;

val real_c = precontext_compile real_pc;

(* non-interactive mode
*)
end;
