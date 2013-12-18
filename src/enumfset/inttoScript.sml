(* file inttoScript.sml, split off from totoScript 12/13/13 to be the  *)
(* only theory that loads intLib. *)

structure inttoScript = struct

(* app load ["totoTheory", "intLib"]; *)

open HolKernel boolLib Parse;

val _ = set_trace "Unicode" 0;
open pred_setLib pred_setTheory relationTheory pairTheory;
open bossLib PairRules arithmeticTheory numeralTheory Defn;
open totoTheory intLib;

val _ = new_theory "intto";

(* My habitual abbreviations: *)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val _ = intLib.deprecate_int ();

val _ = Defn.def_suffix := ""; (* replacing default "_def" *)

(* ***************************************************************** *)
(* Following switch, BigSig, allows "maybe_thm" to act either as     *)
(* store_thm or as prove, thus maximizing or minimizing the output   *)
(* from print_theory and the stuff known to DB.match, DB.find        *)
(* ***************************************************************** *)

val BigSig = false;

fun maybe_thm (s, tm, tac) = if BigSig then store_thm (s, tm, tac)
                                       else prove (tm, tac);

(* **************************************************************** *)
(* Theorems to support intto_CONV, for comparing at type int.       *)
(* **************************************************************** *)

(* integer parsing remains deprecated; note use of suffix i below. *)

(* An integer ground term is, as well as I can see, either a application of
   ``$&`` to a num ground term (which is either ``0`` or an application
   of NUMERAL to a pile of ZERO, BIT0, and BIT1) or an application of
   numeric_negate:int -> int to such a &-application. ``-0`` is possible. *)

val intOrd = Define`intOrd = TO_of_LinearOrder ($< :int reln)`;

val StrongLinearOrder_int_lt = maybe_thm ("StrongLinearOrder_int_lt",
``StrongLinearOrder ($< :int reln)``,
SRW_TAC [][StrongLinearOrder,
 StrongOrder_ALT, trichotomous, Order, irreflexive_def, transitive_def] THENL
[IMP_RES_TAC integerTheory.INT_LT_TRANS
,STRIP_ASSUME_TAC (SPECL [``a:int``, ``b:int``] integerTheory.INT_LT_TOTAL)
 THEN AR]);

val TO_intOrd = maybe_thm ("TO_intOrd", ``TotOrd intOrd``,
REWRITE_TAC [intOrd] THEN MATCH_MP_TAC TotOrd_TO_of_Strong THEN
ACCEPT_TAC StrongLinearOrder_int_lt);

val intto = Define`intto = TO intOrd`;

val apintto_thm = store_thm ("apintto_thm", ``apto intto = intOrd``,
REWRITE_TAC [intto, GSYM TO_apto_TO_ID, TO_intOrd]);

val pos_pos_thm = store_thm ("pos_pos_thm",
``!m:num n:num. intOrd (&m) (&n) = numOrd m n``,
 SRW_TAC [] [TO_of_LinearOrder, intOrd, numOrd]);

val neg_neg_thm = store_thm ("neg_neg_thm",
``!m:num n:num. intOrd (numeric_negate (&m)) (numeric_negate (&n)) =
                numOrd n m``,
 SRW_TAC [] [TO_of_LinearOrder, intOrd, numOrd]);

val BIT1_nz = store_thm ("BIT1_nz",
``!n. BIT1 n <> 0``,
SRW_TAC [] [arithmeticTheory.NOT_ZERO_LT_ZERO, numeralTheory.numeral_lt,
                    GSYM arithmeticTheory.ALT_ZERO]);

val BIT2_nz = store_thm ("BIT2_nz",
``!n. BIT2 n <> 0``,
SRW_TAC [] [arithmeticTheory.NOT_ZERO_LT_ZERO, numeralTheory.numeral_lt,
                    GSYM arithmeticTheory.ALT_ZERO]);

val neg_lt_BIT1_thm = store_thm ("neg_lt_BIT1_thm",
``!m:num n:num. intOrd (numeric_negate (&m)) (& (BIT1 n)) = LESS``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT1_nz]);

val neg_lt_BIT2_thm = store_thm ("neg_lt_BIT2_thm",
``!m:num n:num. intOrd (numeric_negate (&m)) (& (BIT2 n)) = LESS``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT2_nz]);

val neg_BIT1_lt_thm = store_thm ("neg_BIT1_lt_thm",
``!m:num n:num. intOrd (numeric_negate (& (BIT1 m))) (& n) = LESS``,
SRW_TAC [] [TO_of_LinearOrder, intOrd,  BIT1_nz]);

val neg_BIT2_lt_thm = store_thm ("neg_BIT2_lt_thm",
``!m:num n:num. intOrd (numeric_negate (& (BIT2 m))) (& n) = LESS``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT2_nz]);

val neg_ZERO_eq_ZERO_thm = store_thm ("neg_ZERO_eq_ZERO_thm",
``intOrd (numeric_negate (& ZERO)) (& ZERO) = EQUAL``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, GSYM arithmeticTheory.ALT_ZERO]);

val BIT1_gt_neg_thm = store_thm ("BIT1_gt_neg_thm",
``!m:num n:num. intOrd (& (BIT1 m)) (numeric_negate (&n)) = GREATER``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT1_nz]);

val BIT2_gt_neg_thm = store_thm ("BIT2_gt_neg_thm",
``!m:num n:num. intOrd (& (BIT2 m)) (numeric_negate (&n)) = GREATER``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT2_nz]);

val gt_neg_BIT1_thm = store_thm ("gt_neg_BIT1_thm",
``!m:num n:num. intOrd (& m) (numeric_negate (& (BIT1 n))) = GREATER``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT1_nz]);

val gt_neg_BIT2_thm = store_thm ("gt_neg_BIT2_thm",
``!m:num n:num. intOrd (& m) (numeric_negate (& (BIT2 n))) = GREATER``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, BIT2_nz]);

val ZERO_eq_neg_ZERO_thm = store_thm ("ZERO_eq_neg_ZERO_thm",
``intOrd (& ZERO) (numeric_negate (& ZERO)) = EQUAL``,
SRW_TAC [] [TO_of_LinearOrder, intOrd, GSYM arithmeticTheory.ALT_ZERO]);

val _ = export_theory ();
val _ = print_theory "-";

end;
