(* non-interactive mode
*)
structure arithContext :> arithContext =
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

open bossLib pairTheory pred_setTheory extra_pred_setTheory gcdTheory
     dividesTheory
     res_quanTheory arithmeticTheory extra_arithTheory
     hurdUtils ho_basicTools ho_proverTools res_quanTools
     subtypeTools numContext;

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

val arith1_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [PRIME_SUBSET_GTNUM1] @
  map SC_SUBTYPE
  [GCD_SUBTYPE];

val arith_sc = arith1_sc;

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

(* Rules *)

(* Congruences *)

(* Rewrites *)

(* The module *)

val arith1_pc =
  precontext_add
  ("arith1",
   map C_SUBTYPE arith1_sc @
   map C_THM
   [ALL_DIVIDES_0,
    DIVIDES_REFL,
    ONE_DIVIDES_ALL,
    DIVIDES_ONE_UNIQUE,
    DIVIDES_UPL,
    DIVIDES_UPR,
    DIVIDES_CANCEL,
    GCD_EQ_0])
  num_pc;

val arith2_pc = precontext_add
  ("arith2",
   map C_THM
   [NOT_PRIME_0,
    NOT_PRIME_1,
    PRIME_2,
    GCD_0L,
    GCD_0R,
    GCD_1L,
    GCD_1R,
    DIVIDES_PRIME,
    DIVIDES_PRIME_POWER,
    PRIME_EXP])
  arith1_pc;

val arith3_pc = precontext_add
  ("arith3",
   map C_THM
   [GCD_MULT,
    GCD_DIVIDESR,
    GCD_DIVIDESL,
    GCD_REF])
  arith2_pc;

val arith4_pc = precontext_add
  ("arith4",
   map C_THM
   [DIV_CANCEL,
    PRIME_EXPONENT_1,
    DIVIDES_LCM_L,
    DIVIDES_LCM_R,
    LCM_REFL])
  arith3_pc;

val arith_pc = arith4_pc;
val arith_c = precontext_compile arith_pc;

(* non-interactive mode
*)
end;
