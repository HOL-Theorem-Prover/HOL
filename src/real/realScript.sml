(*---------------------------------------------------------------------------*)
(* Develop the theory of reals                                               *)
(*---------------------------------------------------------------------------*)


structure realScript =
struct

(*
app load ["numLib",
          "EquivType",
          "Let_conv",
          "listTheory",
          "mesonLib",
          "tautLib",
          "pred_setTheory",
          "arithLib",
          "simpLib",
          "boolSimps",
          "pairSimps",
          "arithSimps",
          "Ho_rewrite",
          "AC",
          "jrhUtils",
          "realaxTheory"];
 *)

open HolKernel Parse basicHol90Lib;
infix THEN THENL ORELSE ORELSEC ##;

(*
*)
open Psyntax
     hol88Lib
     numLib
     reduceLib
     pairTheory
     arithmeticTheory
     numTheory
     prim_recTheory
     Let_conv
     listTheory
     mesonLib
     tautLib
     arithLib
     simpLib
     Ho_rewrite
     Arithconv
     jrhUtils
     Canon_Port
     AC
     hratTheory
     hrealTheory
     realaxTheory;

val _ = new_theory "real";

val num_EQ_CONV = Arithconv.NEQ_CONV;

(*---------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism &:num->real.                        *)
(*---------------------------------------------------------------------------*)

val real_of_num = new_prim_rec_definition("real_of_num",
  (--`(real_of_num 0 = real_0) /\
      (real_of_num(SUC n) = real_of_num n + real_1)`--));

val _ = add_numeral_form(#"r", SOME "real_of_num");

val REAL_0 = prove_thm("REAL_0",
  (--`real_0 = &0`--),
  REWRITE_TAC[real_of_num]);

val REAL_1 = prove_thm("REAL_1",
  (--`real_1 = & 1`--),
  REWRITE_TAC[num_CONV (--`1:num`--), real_of_num, REAL_ADD_LID]);

local val reeducate = REWRITE_RULE[REAL_0, REAL_1]
in
  val REAL_10 = save_thm("REAL_10",reeducate(REAL_10))
  val REAL_ADD_SYM = save_thm("REAL_ADD_SYM",reeducate(REAL_ADD_SYM))
  val REAL_ADD_ASSOC = save_thm("REAL_ADD_ASSOC",reeducate(REAL_ADD_ASSOC))
  val REAL_ADD_LID = save_thm("REAL_ADD_LID",reeducate(REAL_ADD_LID))
  val REAL_ADD_LINV = save_thm("REAL_ADD_LINV",reeducate(REAL_ADD_LINV))
  val REAL_LDISTRIB = save_thm("REAL_LDISTRIB",reeducate(REAL_LDISTRIB))
  val REAL_LT_TOTAL = save_thm("REAL_LT_TOTAL",reeducate(REAL_LT_TOTAL))
  val REAL_LT_REFL = save_thm("REAL_LT_REFL",reeducate(REAL_LT_REFL))
  val REAL_LT_TRANS = save_thm("REAL_LT_TRANS",reeducate(REAL_LT_TRANS))
  val REAL_LT_IADD = save_thm("REAL_LT_IADD",reeducate(REAL_LT_IADD))
  val REAL_SUP_ALLPOS = save_thm("REAL_SUP_ALLPOS",reeducate(REAL_SUP_ALLPOS))
  val REAL_MUL_SYM = save_thm("REAL_MUL_SYM",reeducate(REAL_MUL_SYM))
  val REAL_MUL_ASSOC = save_thm("REAL_MUL_ASSOC",reeducate(REAL_MUL_ASSOC))
  val REAL_MUL_LID = save_thm("REAL_MUL_LID",reeducate(REAL_MUL_LID))
  val REAL_MUL_LINV = save_thm("REAL_MUL_LINV",reeducate(REAL_MUL_LINV))
  val REAL_LT_MUL = save_thm("REAL_LT_MUL",reeducate(REAL_LT_MUL))
  val REAL_INV_0 = save_thm("REAL_INV_0",reeducate REAL_INV_0)
end;

(*---------------------------------------------------------------------------*)
(* Define subtraction, division and the other orderings                      *)
(*---------------------------------------------------------------------------*)

val real_sub = new_infixl_definition("real_sub",
  (--`$real_sub x y = x + ~y`--), 500);

val real_lte = new_infixr_definition("real_lte",
  (--`$real_lte x y = ~(y < x)`--), 450);

val real_gt = new_infixr_definition("real_gt",
  (--`$real_gt x y = y < x`--), 450);

val real_ge = new_infixr_definition("real_ge",
  (--`$real_ge x y = (y real_lte x)`--), 450);

val real_div = new_infixl_definition("real_div",
  (--`$/ x y = x * inv y`--), 600);

val natsub = Term`$-`;
val natlte = Term`$<=`;
val natgt = Term`$>`;
val natge = Term`$>=`;

val _ = overload_on ("-",  natsub);
val _ = overload_on ("<=", natlte);
val _ = overload_on (">",  natgt);
val _ = overload_on (">=", natge);

val _ = overload_on ("-",  Term`$real_sub`);
val _ = overload_on ("<=", Term`$real_lte`);
val _ = overload_on (">",  Term`$real_gt`);
val _ = overload_on (">=", Term`$real_ge`);

(*---------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                       *)
(*---------------------------------------------------------------------------*)

val REAL_ADD_RID = prove_thm("REAL_ADD_RID",
  (--`!x. x + 0 = x`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LID);

val REAL_ADD_RINV = prove_thm("REAL_ADD_RINV",
  (--`!x:real. x + ~x = 0`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LINV);

val REAL_MUL_RID = prove_thm("REAL_MUL_RID",
  (--`!x. x * 1 = x`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LID);

val REAL_MUL_RINV = prove_thm("REAL_MUL_RINV",
  (--`!x. ~(x = 0) ==> (x * inv x = 1)`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LINV);

val REAL_RDISTRIB = prove_thm("REAL_RDISTRIB",
  (--`!x y z. (x + y) * z = (x * z) + (y * z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LDISTRIB);

val REAL_EQ_LADD = prove_thm("REAL_EQ_LADD",
  (--`!x y z. (x + y = x + z) = (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$+ ~x`--)) THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val REAL_EQ_RADD = prove_thm("REAL_EQ_RADD",
  (--`!x y z. (x + z = y + z) = (x = y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_EQ_LADD);

val REAL_ADD_LID_UNIQ = prove_thm("REAL_ADD_LID_UNIQ",
  (--`!x y. (x + y = y) = (x = 0)`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ADD_LID] THEN
  MATCH_ACCEPT_TAC REAL_EQ_RADD);

val REAL_ADD_RID_UNIQ = prove_thm("REAL_ADD_RID_UNIQ",
  (--`!x y. (x + y = x) = (y = 0)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LID_UNIQ);

val REAL_LNEG_UNIQ = prove_thm("REAL_LNEG_UNIQ",
  (--`!x y. (x + y = 0) = (x = ~y)`--),
  REPEAT GEN_TAC THEN SUBST1_TAC (SYM(SPEC (--`y:real`--) REAL_ADD_LINV)) THEN
  MATCH_ACCEPT_TAC REAL_EQ_RADD);

val REAL_RNEG_UNIQ = prove_thm("REAL_RNEG_UNIQ",
  (--`!x y. (x + y = 0) = (y = ~x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LNEG_UNIQ);

val REAL_NEG_ADD = prove_thm("REAL_NEG_ADD",
  (--`!x y. ~(x + y) = ~x + ~y`--),
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (a + c) + (b + d):real`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_MUL_LZERO = prove_thm("REAL_MUL_LZERO",
  (--`!x. 0 * x = 0`--),
  GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`&0 * x`--), (--`&0 * x`--)] REAL_ADD_LID_UNIQ))
  THEN REWRITE_TAC[GSYM REAL_RDISTRIB, REAL_ADD_LID]);

val REAL_MUL_RZERO = prove_thm("REAL_MUL_RZERO",
  (--`!x. x * 0 = 0`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LZERO);

val REAL_NEG_LMUL = prove_thm("REAL_NEG_LMUL",
  (--`!x y. ~(x * y) = ~x * y`--),
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ, GSYM REAL_RDISTRIB,
              REAL_ADD_LINV, REAL_MUL_LZERO]);

val REAL_NEG_RMUL = prove_thm("REAL_NEG_RMUL",
  (--`!x y. ~(x * y) = x * ~y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_NEG_LMUL);

val REAL_NEGNEG = prove_thm("REAL_NEGNEG",
  (--`!x. ~~x = x`--),
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ, REAL_ADD_RINV]);

val REAL_NEG_MUL2 = prove_thm("REAL_NEG_MUL2",
  (--`!x y. ~x * ~y = x * y`--),
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL, REAL_NEGNEG]);

val REAL_ENTIRE = prove_thm("REAL_ENTIRE",
  (--`!x y. (x * y = 0) = (x = 0) \/ (y = 0)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC (--`x = 0`--) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(MATCH_MP REAL_MUL_LINV) THEN
    DISCH_THEN(MP_TAC o AP_TERM (--`$* (inv x)`--)) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RZERO],
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO]]);

val REAL_LT_LADD = prove_thm("REAL_LT_LADD",
  (--`!x y z. (x + y) < (x + z) = y < z`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC (--`~x`--) o MATCH_MP REAL_LT_IADD) THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
    MATCH_ACCEPT_TAC REAL_LT_IADD]);

val REAL_LT_RADD = prove_thm("REAL_LT_RADD",
  (--`!x y z. (x + z) < (y + z) = x < y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LADD);

val REAL_NOT_LT = prove_thm("REAL_NOT_LT",
  (--`!x y. ~(x < y) = y <= x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte]);

val REAL_LT_ANTISYM = prove_thm("REAL_LT_ANTISYM",
  (--`!x y. ~(x < y /\ y < x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
  REWRITE_TAC[REAL_LT_REFL]);

val REAL_LT_GT = prove_thm("REAL_LT_GT",
  (--`!x y. x < y ==> ~(y < x)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
  REWRITE_TAC[REAL_LT_ANTISYM]);

val REAL_NOT_LE = prove_thm("REAL_NOT_LE",
  (--`!x y. ~(x <= y) = y < x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte]);

val REAL_LE_TOTAL = prove_thm("REAL_LE_TOTAL",
  (--`!x y. x <= y \/ y <= x`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_lte, GSYM DE_MORGAN_THM, REAL_LT_ANTISYM]);

val REAL_LET_TOTAL = prove_thm("REAL_LET_TOTAL",
  (--`!x y. x <= y \/ y < x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  BOOL_CASES_TAC (--`y < x`--) THEN REWRITE_TAC[]);

val REAL_LTE_TOTAL = prove_thm("REAL_LTE_TOTAL",
  (--`!x y. x < y \/ y <= x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  BOOL_CASES_TAC (--`x < y`--) THEN REWRITE_TAC[]);

val REAL_LE_REFL = prove_thm("REAL_LE_REFL",
  (--`!x. x <= x`--),
  GEN_TAC THEN REWRITE_TAC[real_lte, REAL_LT_REFL]);

val REAL_LE_LT = prove_thm("REAL_LE_LT",
  (--`!x y. x <= y = x < y \/ (x = y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry op THEN (MATCH_MP_TAC REAL_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC REAL_LT_REFL]);

val REAL_LT_LE = prove_thm("REAL_LT_LE",
  (--`!x y. x < y = x <= y /\ ~(x = y)`--),
  let val lemma = TAUT_CONV (--`~(a /\ ~a)`--) in
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR, lemma]
  THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL] end);

val REAL_LT_IMP_LE = prove_thm("REAL_LT_IMP_LE",
  (--`!x y. x < y ==> x <= y`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_LT]);

val REAL_LTE_TRANS = prove_thm("REAL_LTE_TRANS",
  (--`!x y z. x < y /\ y <= z ==> x < z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, LEFT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN REWRITE_TAC[]);

val REAL_LET_TRANS = prove_thm("REAL_LET_TRANS",
  (--`!x y z. x <= y /\ y < z ==> x < z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)));

val REAL_LE_TRANS = prove_thm("REAL_LE_TRANS",
  (--`!x y z. x <= y /\ y <= z ==> x <= z`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
  THEN REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME (--`y < z`--))) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE o MATCH_MP REAL_LET_TRANS));

val REAL_LE_ANTISYM = prove_thm("REAL_LE_ANTISYM",
  (--`!x y. x <= y /\ y <= x = (x = y)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[real_lte] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]]);

val REAL_LET_ANTISYM = prove_thm("REAL_LET_ANTISYM",
  (--`!x y. ~(x < y /\ y <= x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  BOOL_CASES_TAC (--`x < y`--) THEN REWRITE_TAC[]);

val REAL_LTE_ANTSYM = prove_thm("REAL_LTE_ANTSYM",
  (--`!x y. ~(x <= y /\ y < x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LET_ANTISYM);

val REAL_NEG_LT0 = prove_thm("REAL_NEG_LT0",
  (--`!x. ~x < 0 = 0 < x`--),
  GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`~x`--), (--`0`--), (--`x:real`--)] REAL_LT_RADD))
  THEN REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_NEG_GT0 = prove_thm("REAL_NEG_GT0",
  (--`!x. 0 < ~x = x < 0`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEGNEG]);

val REAL_NEG_LE0 = prove_thm("REAL_NEG_LE0",
  (--`!x. ~x <= 0 = 0 <= x`--),
  GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  REWRITE_TAC[REAL_NEG_GT0]);

val REAL_NEG_GE0 = prove_thm("REAL_NEG_GE0",
  (--`!x. 0 <= ~x = x <= 0`--),
  GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  REWRITE_TAC[REAL_NEG_LT0]);

val REAL_LT_NEGTOTAL = prove_thm("REAL_LT_NEGTOTAL",
  (--`!x. (x = 0) \/ (0 < x) \/ (0 < ~x)`--),
  GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [(--`x:real`--), (--`0`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[SYM(REWRITE_RULE[REAL_NEGNEG]
                         (SPEC (--`~x`--) REAL_NEG_LT0))]);

val REAL_LE_NEGTOTAL = prove_thm("REAL_LE_NEGTOTAL",
  (--`!x. 0 <= x \/ 0 <= ~x`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
          (SPEC (--`x:real`--) REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[]);

val REAL_LE_MUL = prove_thm("REAL_LE_MUL",
  (--`!x y. 0 <= x /\ 0 <= y ==> 0 <= (x * y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  MAP_EVERY ASM_CASES_TAC [(--`0 = x`--), (--`0 = y`--)] THEN
  ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[]);

val REAL_LE_SQUARE = prove_thm("REAL_LE_SQUARE",
  (--`!x. 0 <= x * x`--),
  GEN_TAC THEN DISJ_CASES_TAC (SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THEN
  POP_ASSUM(MP_TAC o MATCH_MP REAL_LE_MUL o W CONJ) THEN
  REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM REAL_NEG_LMUL, REAL_NEGNEG]);

val REAL_LE_01 = prove_thm("REAL_LE_01",
  (--`0 <= &1`--),
  SUBST1_TAC(SYM(SPEC (--`&1`--) REAL_MUL_LID)) THEN
  MATCH_ACCEPT_TAC REAL_LE_SQUARE);

val REAL_LT_01 = prove_thm("REAL_LT_01",
  (--`0 < &1`--),
  REWRITE_TAC[REAL_LT_LE, REAL_LE_01] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_10]);

val REAL_LE_LADD = prove_thm("REAL_LE_LADD",
  (--`!x y z. (x + y) <= (x + z) = y <= z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LADD);

val REAL_LE_RADD = prove_thm("REAL_LE_RADD",
  (--`!x y z. (x + z) <= (y + z) = x <= y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_RADD);

val REAL_LT_ADD2 = prove_thm("REAL_LT_ADD2",
  (--`!w x y z. w < x /\ y < z ==> (w + y) < (x + z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`w + z`--) THEN
  ASM_REWRITE_TAC[REAL_LT_LADD, REAL_LT_RADD]);

val REAL_LE_ADD2 = prove_thm("REAL_LE_ADD2",
  (--`!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`w + z`--) THEN
  ASM_REWRITE_TAC[REAL_LE_LADD, REAL_LE_RADD]);

val REAL_LE_ADD = prove_thm("REAL_LE_ADD",
  (--`!x y. 0 <= x /\ 0 <= y ==> 0 <= (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2) THEN
  REWRITE_TAC[REAL_ADD_LID]);

val REAL_LT_ADD = prove_thm("REAL_LT_ADD",
  (--`!x y. 0 < x /\ 0 < y ==> 0 < (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_ADD_LID]);

val REAL_LT_ADDNEG = prove_thm("REAL_LT_ADDNEG",
  (--`!x y z. y < x + ~z = y+z < x`--),
  REPEAT GEN_TAC THEN  SUBST1_TAC
  (SYM(SPECL [(--`y:real`--), (--`x + ~z`--), (--`z:real`--)] REAL_LT_RADD))
  THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

val REAL_LT_ADDNEG2 = prove_thm("REAL_LT_ADDNEG2",
  (--`!x y z. (x + ~y) < z = x < (z + y)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x + ~y`--), (--`z:real`--), (--`y:real`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

val REAL_LT_ADD1 = prove_thm("REAL_LT_ADD1",
  (--`!x y. x <= y ==> x < (y + &1)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [POP_ASSUM(MP_TAC o MATCH_MP REAL_LT_ADD2 o C CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_ADD_RID],
    POP_ASSUM SUBST1_TAC THEN
    GEN_REWR_TAC LAND_CONV  [GSYM REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_LT_LADD, REAL_LT_01]]);

val REAL_SUB_ADD = prove_thm("REAL_SUB_ADD",
  (--`!x y. (x - y) + y = x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC,
    REAL_ADD_LINV, REAL_ADD_RID]);

val REAL_SUB_ADD2 = prove_thm("REAL_SUB_ADD2",
  (--`!x y. y + (x - y) = x`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_SUB_ADD);

val REAL_SUB_REFL = prove_thm("REAL_SUB_REFL",
  (--`!x. x - x = 0`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, REAL_ADD_RINV]);

val REAL_SUB_0 = prove_thm("REAL_SUB_0",
  (--`!x y. (x - y = 0) = (x = y)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM (--`y:real`--) o AP_TERM (--`$+`--)) THEN
    REWRITE_TAC[REAL_SUB_ADD, REAL_ADD_LID],
    DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_SUB_REFL]);

val REAL_LE_DOUBLE = prove_thm("REAL_LE_DOUBLE",
  (--`!x. 0 <= x + x = 0 <= x`--),
  GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ),
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2 o W CONJ)] THEN
  REWRITE_TAC[REAL_ADD_LID]);

val REAL_LE_NEGL = prove_thm("REAL_LE_NEGL",
  (--`!x. (~x <= x) = (0 <= x)`--),
  GEN_TAC THEN SUBST1_TAC
  (SYM(SPECL [(--`x:real`--), (--`~x`--), (--`x:real`--)] REAL_LE_LADD))
  THEN REWRITE_TAC[REAL_ADD_RINV, REAL_LE_DOUBLE]);

val REAL_LE_NEGR = prove_thm("REAL_LE_NEGR",
  (--`!x. (x <= ~x) = (x <= 0)`--),
  GEN_TAC THEN SUBST1_TAC(SYM(SPEC (--`x:real`--) REAL_NEGNEG)) THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEGL] THEN REWRITE_TAC[REAL_NEG_GE0] THEN
  REWRITE_TAC[REAL_NEGNEG]);

val REAL_NEG_EQ0 = prove_thm("REAL_NEG_EQ0",
  (--`!x. (~x = 0) = (x = 0)`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$+ x`--)),
    DISCH_THEN(MP_TAC o AP_TERM (--`$+ ~x`--))] THEN
  REWRITE_TAC[REAL_ADD_RINV, REAL_ADD_LINV, REAL_ADD_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);

val REAL_NEG_0 = prove_thm("REAL_NEG_0",
  (--`~0 = 0`--),
  REWRITE_TAC[REAL_NEG_EQ0]);

val REAL_NEG_SUB = prove_thm("REAL_NEG_SUB",
  (--`!x y. ~(x - y) = y - x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_SUB_LT = prove_thm("REAL_SUB_LT",
  (--`!x y. 0 < x - y = y < x`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`0`--), (--`x - y`--), (--`y:real`--)]
                       REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD, REAL_ADD_LID]);

val REAL_SUB_LE = prove_thm("REAL_SUB_LE",
  (--`!x y. 0 <= (x - y) = y <= x`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`0`--), (--`x - y`--), (--`y:real`--)]
                      REAL_LE_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD, REAL_ADD_LID]);

val REAL_ADD_SUB = prove_thm("REAL_ADD_SUB",
  (--`!x y. (x + y) - x = y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_RID]);

val REAL_EQ_LMUL = prove_thm("REAL_EQ_LMUL",
  (--`!x y z. (x * y = x * z) = (x = 0) \/ (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$* (inv x)`--)) THEN
    ASM_CASES_TAC (--`x = 0`--) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(fn th => REWRITE_TAC[REAL_MUL_ASSOC, MATCH_MP REAL_MUL_LINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID],
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO]]);

val REAL_EQ_RMUL = prove_thm("REAL_EQ_RMUL",
  (--`!x y z. (x * z = y * z) = (z = 0) \/ (x = y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_EQ_LMUL);

val REAL_SUB_LDISTRIB = prove_thm("REAL_SUB_LDISTRIB",
  (--`!x y z. x * (y - z) = (x * y) - (x * z)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_LDISTRIB, REAL_NEG_RMUL]);

val REAL_SUB_RDISTRIB = prove_thm("REAL_SUB_RDISTRIB",
  (--`!x y z. (x - y) * z = (x * z) - (y * z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_SUB_LDISTRIB);

val REAL_NEG_EQ = prove_thm("REAL_NEG_EQ",
  (--`!x y. (~x = y) = (x = ~y)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_NEGNEG]);

val REAL_NEG_MINUS1 = prove_thm("REAL_NEG_MINUS1",
  (--`!x. ~x = ~1 * x`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_INV_NZ = prove_thm("REAL_INV_NZ",
  (--`!x. ~(x = 0) ==> ~(inv x = 0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM (--`x:real`--) o AP_TERM (--`$*`--)) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_10]);

val REAL_INVINV = prove_thm("REAL_INVINV",
  (--`!x. ~(x = 0) ==> (inv (inv x) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_MUL_RINV) THEN
  ASM_CASES_TAC (--`inv x = 0`--) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO, GSYM REAL_10] THEN
  MP_TAC(SPECL [(--`inv(inv x)`--), (--`x:real`--), (--`inv x`--)] REAL_EQ_RMUL)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  FIRST_ASSUM ACCEPT_TAC);

val REAL_LT_IMP_NE = prove_thm("REAL_LT_IMP_NE",
  (--`!x y. x < y ==> ~(x = y)`--),
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_LT_REFL]);

val REAL_INV_POS = prove_thm("REAL_INV_POS",
  (--`!x. 0 < x ==> 0 < inv x`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT_TCL DISJ_CASES_THEN
   MP_TAC (SPECL [(--`inv x`--), (--`0`--)] REAL_LT_TOTAL) THENL
   [POP_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_NZ o
              GSYM o MATCH_MP REAL_LT_IMP_NE) THEN ASM_REWRITE_TAC[],
    ONCE_REWRITE_TAC[GSYM REAL_NEG_GT0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL o C CONJ (ASSUME (--`0 < x`--))) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    POP_ASSUM(fn th => REWRITE_TAC
     [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_NEG_GT0] THEN DISCH_THEN(MP_TAC o CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_LT_ANTISYM],
    REWRITE_TAC[]]);

val REAL_LT_LMUL_0 = prove_thm("REAL_LT_LMUL_0",
  (--`!x y. 0 < x ==> (0 < (x * y) = 0 < y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_INV_POS th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC
      [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_MUL_LID],
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);

val REAL_LT_RMUL_0 = prove_thm("REAL_LT_RMUL_0",
  (--`!x y. 0 < y ==> (0 < (x * y) = 0 < x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL_0);

val REAL_LT_LMUL = prove_thm("REAL_LT_LMUL",
  (--`!x y z. 0 < x ==> ((x * y) < (x * z) = y < z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LMUL_0);

val REAL_LT_RMUL = prove_thm("REAL_LT_RMUL",
  (--`!x y z. 0 < z ==> ((x * z) < (y * z) = x < y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL);

val REAL_LT_RMUL_IMP = prove_thm("REAL_LT_RMUL_IMP",
  (--`!x y z. x < y /\ 0 < z ==> (x * z) < (y * z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fn th => REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_RMUL th)]));

val REAL_LT_LMUL_IMP = prove_thm("REAL_LT_LMUL_IMP",
  (--`!x y z. y < z  /\ 0 < x ==> (x * y) < (x * z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fn th => REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_LMUL th)]));

val REAL_LINV_UNIQ = prove_thm("REAL_LINV_UNIQ",
  (--`!x y. (x * y = &1) ==> (x = inv y)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`x = 0`--) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, GSYM REAL_10] THEN
  DISCH_THEN(MP_TAC o AP_TERM (--`$* (inv x)`--)) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_INVINV);

val REAL_RINV_UNIQ = prove_thm("REAL_RINV_UNIQ",
  (--`!x y. (x * y = &1) ==> (y = inv x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LINV_UNIQ);

val REAL_INV_INV = prove_thm("REAL_INV_INV",
 Term`!x. inv(inv x) = x`,
  GEN_TAC THEN ASM_CASES_TAC (Term `x = 0`) THEN
  ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_REWRITE_TAC[]);;

val REAL_INV_EQ_0 = prove_thm("REAL_INV_EQ_0",
 Term`!x. (inv(x) = 0) = (x = 0)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN ASM_REWRITE_TAC[REAL_INV_0]);;

val REAL_NEG_INV = prove_thm("REAL_NEG_INV",
  (--`!x. ~(x = 0) ==> (~inv x = inv (~x))`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_NEGNEG]);

val REAL_INV_1OVER = prove_thm("REAL_INV_1OVER",
  (--`!x. inv x = &1 / x`--),
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_LID]);

val REAL_LT_INV_EQ = prove_thm("REAL_LT_INV_EQ",
 Term`!x. 0 < inv x = 0 < x`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[REAL_INV_POS] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[REAL_INV_POS]);;

val REAL_LE_INV_EQ = prove_thm("REAL_LE_INV_EQ",
 Term`!x. 0 <= inv x = 0 <= x`,
  REWRITE_TAC[REAL_LE_LT, REAL_LT_INV_EQ, REAL_INV_EQ_0] THEN
  MESON_TAC[REAL_INV_EQ_0]);;

val REAL_LE_INV = prove_thm("REAL_LE_INV",
 Term `!x. 0 <= x ==> 0 <= inv(x)`,
  REWRITE_TAC[REAL_LE_INV_EQ]);;

val REAL_LE_ADDR = prove_thm("REAL_LE_ADDR",
  (--`!x y. x <= x + y = 0 <= y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`0`--), (--`y:real`--)] REAL_LE_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]);

val REAL_LE_ADDL = prove_thm("REAL_LE_ADDL",
  (--`!x y. y <= x + y = 0 <= x`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LE_ADDR);

val REAL_LT_ADDR = prove_thm("REAL_LT_ADDR",
  (--`!x y. x < x + y = 0 < y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`0`--), (--`y:real`--)] REAL_LT_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]);

val REAL_LT_ADDL = prove_thm("REAL_LT_ADDL",
  (--`!x y. y < x + y = 0 < x`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_ADDR);

(*---------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                 *)
(*---------------------------------------------------------------------------*)

val REAL = prove_thm("REAL",
  (--`!n. &(SUC n) = &n + &1`--),
  GEN_TAC THEN REWRITE_TAC[real_of_num] THEN
  REWRITE_TAC[REAL_1]);

val REAL_POS = prove_thm("REAL_POS",
  (--`!n. 0 <= &n`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`&n`--) THEN ASM_REWRITE_TAC[REAL] THEN
  REWRITE_TAC[REAL_LE_ADDR, REAL_LE_01]);

val REAL_LE = prove_thm("REAL_LE",
  (--`!m n. &m <= &n = m <= n`--),
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
   [REAL, REAL_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&n`--) THEN
    ASM_REWRITE_TAC[ZERO_LESS_EQ, REAL_LE_ADDR, REAL_LE_01],
    DISCH_THEN(MP_TAC o C CONJ (SPEC (--`m:num`--) REAL_POS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    REWRITE_TAC[REAL_NOT_LE, REAL_LT_ADDR, REAL_LT_01]]);

val REAL_LT = prove_thm("REAL_LT",
  (--`!m n. &m < &n = m < n`--),
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC
    ((REWRITE_RULE[] o AP_TERM (--`$~:bool->bool`--) o
    REWRITE_RULE[GSYM NOT_LESS, GSYM REAL_NOT_LT]) (SPEC_ALL REAL_LE)));

val REAL_INJ = prove_thm("REAL_INJ",
  (--`!m n. (&m = &n) = (m = n)`--),
  let val th = PROVE((--`(m:num = n) = m <= n /\ n <= m`--),
                 EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[th, GSYM REAL_LE_ANTISYM, REAL_LE] end);

val REAL_ADD = prove_thm("REAL_ADD",
  (--`!m n. &m + &n = &(m + n)`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL, ADD, REAL_ADD_LID] THEN
  RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val REAL_MUL = prove_thm("REAL_MUL",
  (--`!m n. &m * &n = &(m * n)`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, MULT_CLAUSES, REAL,
    GSYM REAL_ADD, REAL_RDISTRIB] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

(*---------------------------------------------------------------------------*)
(* Now more theorems                                                         *)
(*---------------------------------------------------------------------------*)

val REAL_INV1 = prove_thm("REAL_INV1",
  (--`inv(&1) = &1`--),
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_OVER1 = prove_thm("REAL_OVER1",
  (--`!x. x / &1 = x`--),
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_INV1, REAL_MUL_RID]);

val REAL_DIV_REFL = prove_thm("REAL_DIV_REFL",
  (--`!x. ~(x = 0) ==> (x / x = &1)`--),
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_RINV]);

val REAL_DIV_LZERO = prove_thm("REAL_DIV_LZERO",
  (--`!x. 0 / x = 0`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_LZERO]);

val REAL_LT_NZ = prove_thm("REAL_LT_NZ",
  (--`!n. ~(&n = 0) = (0 < &n)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC (--`&n = 0`--) THEN ASM_REWRITE_TAC[REAL_LE_REFL, REAL_POS]);

val REAL_NZ_IMP_LT = prove_thm("REAL_NZ_IMP_LT",
  (--`!n. ~(n = 0) ==> 0 < &n`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_INJ, REAL_LT_NZ]);

val REAL_LT_RDIV_0 = prove_thm("REAL_LT_RDIV_0",
  (--`!y z. 0 < z ==> (0 < (y / z) = 0 < y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_0 THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);

val REAL_LT_RDIV = prove_thm("REAL_LT_RDIV",
  (--`!x y z. 0 < z ==> ((x / z) < (y / z) = x < y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);

val REAL_LT_FRACTION_0 = prove_thm("REAL_LT_FRACTION_0",
  (--`!n d. ~(n = 0) ==> (0 < (d / &n) = 0 < d)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_RDIV_0 THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_NZ, REAL_INJ]);

val REAL_LT_MULTIPLE = prove_thm("REAL_LT_MULTIPLE",
  (--`!(n:num) d. 1 < n ==> (d < (&n * d) = 0 < d)`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[num_CONV (--`1:num`--), NOT_LESS_0],
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC (--`1 < n:num`--) THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[REAL, REAL_LDISTRIB, REAL_MUL_RID, REAL_LT_ADDL] THEN
      MATCH_MP_TAC REAL_LT_RMUL_0 THEN REWRITE_TAC[REAL_LT] THEN
      MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`1:num`--) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[num_CONV (--`1:num`--), LESS_0],
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LESS_LEMMA1) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL, REAL_LDISTRIB, REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_LT_ADDL]]]);

val REAL_LT_FRACTION = prove_thm("REAL_LT_FRACTION",
  (--`!(n:num) d. 1<n ==> ((d / &n) < d = 0 < d)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`n = 0:num`--) THEN
  ASM_REWRITE_TAC[NOT_LESS_0] THEN DISCH_TAC THEN
  UNDISCH_TAC (--`1 < n:num`--) THEN
  FIRST_ASSUM(fn th => let val th1 = REWRITE_RULE[GSYM REAL_INJ] th in
    MAP_EVERY ASSUME_TAC [th1, REWRITE_RULE[REAL_LT_NZ] th1] end) THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o LAND_CONV)
                                    [GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_MULTIPLE);

val REAL_LT_HALF1 = prove_thm("REAL_LT_HALF1",
  (--`!d. 0 < (d / &2) = 0 < d`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION_0 THEN
  REWRITE_TAC[num_CONV (--`2:num`--), NOT_SUC]);

val REAL_LT_HALF2 = prove_thm("REAL_LT_HALF2",
  (--`!d. (d / &2) < d = 0 < d`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION THEN
  CONV_TAC(RAND_CONV num_CONV) THEN
  REWRITE_TAC[LESS_SUC_REFL]);

val REAL_DOUBLE = prove_thm("REAL_DOUBLE",
  (--`!x. x + x = &2 * x`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV (--`2:num`--), REAL] THEN
  REWRITE_TAC[REAL_RDISTRIB, REAL_MUL_LID]);

val REAL_DIV_LMUL = prove_thm("REAL_DIV_LMUL",
  (--`!x y. ~(y = 0) ==> (y * (x / y) = x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_MUL_RID]);

val REAL_DIV_RMUL = prove_thm("REAL_DIV_RMUL",
  (--`!x y. ~(y = 0) ==> ((x / y) * y = x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_DIV_LMUL);

val REAL_HALF_DOUBLE = prove_thm("REAL_HALF_DOUBLE",
  (--`!x. (x / &2) + (x / &2) = x`--),
  GEN_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV num_EQ_CONV) THEN REWRITE_TAC[]);

val REAL_DOWN = prove_thm("REAL_DOWN",
  (--`!x. 0 < x ==> ?y. 0 < y /\ y < x`--),
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (--`x / &2`--) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2]);

val REAL_DOWN2 = prove_thm("REAL_DOWN2",
  (--`!x y. 0 < x /\ 0 < y ==> ?z. 0 < z /\ z < x /\ z < y`--),
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[REAL_DOWN],
    DISCH_THEN(X_CHOOSE_TAC (--`z:real`--) o MATCH_MP REAL_DOWN o CONJUNCT1),
    DISCH_THEN(X_CHOOSE_TAC (--`z:real`--) o MATCH_MP REAL_DOWN o CONJUNCT2)] THEN
  EXISTS_TAC (--`z:real`--) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_TRANS THENL
   [EXISTS_TAC (--`x:real`--), EXISTS_TAC (--`y:real`--)] THEN
  ASM_REWRITE_TAC[]);

val REAL_SUB_SUB = prove_thm("REAL_SUB_SUB",
  (--`!x y. (x - y) - x = ~y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + c = (c + a) + b`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_LT_ADD_SUB = prove_thm("REAL_LT_ADD_SUB",
  (--`!x y z. (x + y) < z = x < (z - y)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`z - y`--), (--`y:real`--)]
                       REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD]);

val REAL_LT_SUB_RADD = prove_thm("REAL_LT_SUB_RADD",
  (--`!x y z. (x - y) < z = x < z + y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x - y`--), (--`z:real`--), (--`y:real`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD]);

val REAL_LT_SUB_LADD = prove_thm("REAL_LT_SUB_LADD",
  (--`!x y z. x < (y - z) = (x + z) < y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x + z`--), (--`y:real`--), (--`~z`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_RID]);

val REAL_LE_SUB_LADD = prove_thm("REAL_LE_SUB_LADD",
  (--`!x y z. x <= (y - z) = (x + z) <= y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT, REAL_LT_SUB_RADD]);

val REAL_LE_SUB_RADD = prove_thm("REAL_LE_SUB_RADD",
  (--`!x y z. (x - y) <= z = x <= z + y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT, REAL_LT_SUB_LADD]);

val REAL_LT_NEG = prove_thm("REAL_LT_NEG",
  (--`!x y. ~x < ~y = y < x`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL[(--`~x`--), (--`~y`--), (--`x + y`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_LID]);

val REAL_LE_NEG = prove_thm("REAL_LE_NEG",
  (--`!x y. ~x <= ~y = y <= x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_LT_NEG]);

val REAL_ADD2_SUB2 = prove_thm("REAL_ADD2_SUB2",
  (--`!a b c d. (a + b) - (c + d) = (a - c) + (b - d)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val REAL_SUB_LZERO = prove_thm("REAL_SUB_LZERO",
  (--`!x. 0 - x = ~x`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, REAL_ADD_LID]);

val REAL_SUB_RZERO = prove_thm("REAL_SUB_RZERO",
  (--`!x. x - 0 = x`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_0, REAL_ADD_RID]);

val REAL_LET_ADD2 = prove_thm("REAL_LET_ADD2",
  (--`!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC (--`w + z`--) THEN
  ASM_REWRITE_TAC[REAL_LE_RADD, REAL_LT_LADD]);

val REAL_LTE_ADD2 = prove_thm("REAL_LTE_ADD2",
  (--`!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LET_ADD2);

val REAL_LET_ADD = prove_thm("REAL_LET_ADD",
  (--`!x y. 0 <= x /\ 0 < y ==> 0 < (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC (--`0`--) REAL_ADD_LID)) THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN
  ASM_REWRITE_TAC[]);

val REAL_LTE_ADD = prove_thm("REAL_LTE_ADD",
  (--`!x y. 0 < x /\ 0 <= y ==> 0 < (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC (--`0`--) REAL_ADD_LID)) THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN
  ASM_REWRITE_TAC[]);

val REAL_LT_MUL2 = prove_thm("REAL_LT_MUL2",
  (--`!x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN (--`!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))`--)
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID],
    DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, GSYM REAL_SUB_RDISTRIB] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x1:real`--) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);

val REAL_LT_INV = prove_thm("REAL_LT_INV",
  (--`!x y. 0 < x /\ x < y ==> inv y < inv x`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN (--`0 < y`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`0 < (x * y)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`(inv y) < (inv x) =
                ((x * y) * (inv y)) < ((x * y) * (inv x))`--) SUBST1_TAC
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN (--`(x * (inv x) = &1) /\ (y * (inv y) = &1)`--)
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`x * (y * z) = (x * z) * y`--)] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);

val REAL_SUB_LNEG = prove_thm("REAL_SUB_LNEG",
  (--`!x y. ~x - y = ~(x + y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD]);

val REAL_SUB_RNEG = prove_thm("REAL_SUB_RNEG",
  (--`!x y. x - ~y = x + y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEGNEG]);

val REAL_SUB_NEG2 = prove_thm("REAL_SUB_NEG2",
  (--`!x y. ~x - ~y = y - x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUB_LNEG] THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_SUB_TRIANGLE = prove_thm("REAL_SUB_TRIANGLE",
  (--`!a b c. (a - b) + (b - c) = a - c`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_EQ_SUB_LADD = prove_thm("REAL_EQ_SUB_LADD",
  (--`!x y z. (x = y - z) = (x + z = y)`--),
  REPEAT GEN_TAC THEN (SUBST1_TAC o SYM o C SPECL REAL_EQ_RADD)
   [(--`x:real`--), (--`y - z`--), (--`z:real`--)] THEN REWRITE_TAC[REAL_SUB_ADD]);

val REAL_EQ_SUB_RADD = prove_thm("REAL_EQ_SUB_RADD",
  (--`!x y z. (x - y = z) = (x = z + y)`--),
  REPEAT GEN_TAC THEN CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC REAL_EQ_SUB_LADD);

val REAL_INV_MUL = prove_thm("REAL_INV_MUL",
  (--`!x y. ~(x = 0) /\ ~(y = 0) ==>
             (inv(x * y) = inv(x) * inv(y))`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`(a * b) * (c * d) = (c * a) * (d * b)`--)] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  BINOP_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]);

(* Stronger version
val REAL_INV_MUL = prove_thm("REAL_INV_MUL",
 Term`!x y. inv(x * y) = inv(x) * inv(y)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [Term`x = 0`, Term`y = 0`] THEN
  ASM_REWRITE_TAC[REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
  ONCE_REWRITE_TAC
     [AC REAL_MUL_AC (Term`(a * b) * (c * d) = (a * c) * (b * d)`)] THEN
  EVERY_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_MUL_LID])
*)

val REAL_LE_LMUL = prove_thm("REAL_LE_LMUL",
  (--`!x y z. 0 < x ==> ((x * y) <= (x * z) = y <= z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]);

val REAL_LE_RMUL = prove_thm("REAL_LE_RMUL",
  (--`!x y z. 0 < z ==> ((x * z) <= (y * z) = x <= y)`--),
   REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_ACCEPT_TAC REAL_LE_LMUL);

val REAL_SUB_INV2 = prove_thm("REAL_SUB_INV2",
  (--`!x y. ~(x = 0) /\ ~(y = 0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div, REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN (--`inv(x * y) = inv(x) * inv(y)`--) SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_SUB_SUB2 = prove_thm("REAL_SUB_SUB2",
  (--`!x y. x - (x - y) = y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEGNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_NEG_SUB, REAL_SUB_SUB]);

val REAL_ADD_SUB2 = prove_thm("REAL_ADD_SUB2",
  (--`!x y. x - (x + y) = ~y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_ADD_SUB]);

val REAL_MEAN = prove_thm("REAL_MEAN",
  (--`!x y. x < y ==> ?z. x < z /\ z < y`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_DOWN o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT])
  THEN DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`x + d`--) THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_SUB_LADD]);

val REAL_EQ_LMUL2 = prove_thm("REAL_EQ_LMUL2",
  (--`!x y z. ~(x = 0) ==> ((y = z) = (x * y = x * z))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`x:real`--), (--`y:real`--), (--`z:real`--)] REAL_EQ_LMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);

val REAL_LE_MUL2 = prove_thm("REAL_LE_MUL2",
  (--`!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LE_LT) THEN
  ASM_CASES_TAC (--`x1:real = x2`--) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC (--`0 <= x2`--) THEN
    DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
     [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]),
      SUBST1_TAC(SYM(ASSUME (--`0 = x2`--))) THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]], ALL_TAC] THEN
  UNDISCH_TAC (--`y1 <= y2`--) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC (--`0 <= y1`--) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    SUBST1_TAC(SYM(ASSUME (--`0 = y2`--))) THEN
    REWRITE_TAC[REAL_MUL_RZERO, REAL_LE_REFL]]);

val REAL_LE_LDIV = prove_thm("REAL_LE_LDIV",
  (--`!x y z. 0 < x /\ y <= (z * x) ==> (y / x) <= z`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  SUBGOAL_THEN (--`y = (y / x) * x`--) MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(fn t => GEN_REWR_TAC (funpow 2 LAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN POP_ASSUM ACCEPT_TAC]);

val REAL_LE_RDIV = prove_thm("REAL_LE_RDIV",
  (--`!x y z. 0 < x /\ (y * x) <= z ==> y <= (z / x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  SUBGOAL_THEN (--`z = (z / x) * x`--) MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(fn t => GEN_REWR_TAC (LAND_CONV o RAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN POP_ASSUM ACCEPT_TAC]);

val REAL_LT_DIV = prove_thm("REAL_LT_DIV",
 Term`!x y. 0 < x /\ 0 < y ==> 0 < x / y`,
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ]);

val REAL_LE_DIV = prove_thm("REAL_LE_DIV",
 Term`!x y. 0 <= x /\ 0 <= y ==> 0 <= x / y`,
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ]);

val REAL_LT_1 = prove_thm("REAL_LT_1",
  (--`!x y. 0 <= x /\ x < y ==> (x / y) < &1`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(x / y) < &1 = ((x / y) * y) < (&1 * y)`--) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[],
    SUBGOAL_THEN (--`(x / y) * y = x`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[REAL_MUL_LID]]]);

val REAL_LE_LMUL_IMP = prove_thm("REAL_LE_LMUL_IMP",
  (--`!x y z. 0 <= x /\ y <= z ==> (x * y) <= (x * z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]),
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_ACCEPT_TAC REAL_LE_REFL]);

val REAL_LE_RMUL_IMP = prove_thm("REAL_LE_RMUL_IMP",
  (--`!x y z. 0 <= x /\ y <= z ==> (y * x) <= (z * x)`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_LE_LMUL_IMP);

val REAL_EQ_IMP_LE = prove_thm("REAL_EQ_IMP_LE",
  (--`!x y. (x = y) ==> x <= y`--),
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC REAL_LE_REFL);

val REAL_INV_LT1 = prove_thm("REAL_INV_LT1",
  (--`!x. 0 < x /\ x < &1 ==> &1 < inv(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_POS) THEN
  GEN_REWR_TAC I [TAUT_CONV (--`a = ~~a:bool`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [(--`inv(x)`--), (--`&1`--), (--`x:real`--), (--`&1`--)] REAL_LT_MUL2) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`0 < 0`--) THEN
      REWRITE_TAC[REAL_LT_REFL]],
    DISCH_THEN(MP_TAC o AP_TERM (--`inv`--)) THEN REWRITE_TAC[REAL_INV1] THEN
    SUBGOAL_THEN (--`inv(inv x) = x`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`&1 < &1`--) THEN
      REWRITE_TAC[REAL_LT_REFL]]]);

val REAL_POS_NZ = prove_thm("REAL_POS_NZ",
  (--`!x. 0 < x ==> ~(x = 0)`--),
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC);

val REAL_EQ_RMUL_IMP = prove_thm("REAL_EQ_RMUL_IMP",
  (--`!x y z. ~(z = 0) /\ (x * z = y * z) ==> (x = y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[REAL_EQ_RMUL]);

val REAL_EQ_LMUL_IMP = prove_thm("REAL_EQ_LMUL_IMP",
  (--`!x y z. ~(x = 0) /\ (x * y = x * z) ==> (y = z)`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RMUL_IMP);

val REAL_FACT_NZ = prove_thm("REAL_FACT_NZ",
  (--`!n. ~(&(FACT n) = 0)`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

val REAL_DIFFSQ = prove_thm("REAL_DIFFSQ",
  (--`!x y. (x + y) * (x - y) = (x * x) - (y * y)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_LDISTRIB, REAL_RDISTRIB, real_sub, GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`a + (b + (c + d)) = (b + c) + (a + d)`--)] THEN
  REWRITE_TAC[REAL_ADD_LID_UNIQ, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_LNEG_UNIQ] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);

val REAL_POSSQ = prove_thm("REAL_POASQ",
  (--`!x. 0 < (x * x) = ~(x = 0)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C CONJ (SPEC (--`x:real`--) REAL_LE_SQUARE)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM, REAL_ENTIRE],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]]);

val REAL_SUMSQ = prove_thm("REAL_SUMSQ",
  (--`!x y. ((x * x) + (y * y) = 0) = (x = 0) /\ (y = 0)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC REAL_POS_NZ THENL
     [MATCH_MP_TAC REAL_LTE_ADD, MATCH_MP_TAC REAL_LET_ADD] THEN
    ASM_REWRITE_TAC[REAL_POSSQ, REAL_LE_SQUARE],
    DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID]]);

val REAL_EQ_NEG = prove_thm("REAL_EQ_NEG",
  (--`!x y. (~x = ~y) = (x = y)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM, REAL_LE_NEG] THEN
  MATCH_ACCEPT_TAC CONJ_SYM);

val REAL_DIV_MUL2 = prove_thm("REAL_DIV_MUL2",
  (--`!x z. ~(x = 0) /\ ~(z = 0) ==> !y. y / z = (x * y) / (x * z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`(a * b) * (c * d) = (c * a) * (b * d)`--)] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_MIDDLE1 = prove_thm("REAL_MIDDLE1",
  (--`!a b. a <= b ==> a <= (a + b) / &2`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_RDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE, REAL_LE_LADD] THEN
  REWRITE_TAC[num_CONV (--`2:num`--), REAL_LT, LESS_0]);

val REAL_MIDDLE2 = prove_thm("REAL_MIDDLE2",
  (--`!a b. a <= b ==> ((a + b) / &2) <= b`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE, REAL_LE_RADD] THEN
  REWRITE_TAC[num_CONV (--`2:num`--), REAL_LT, LESS_0]);

(*---------------------------------------------------------------------------*)
(* Define usual norm (absolute distance) on the real line                    *)
(*---------------------------------------------------------------------------*)

val abs = new_definition("abs",
  (--`abs(x) = (if (0 <= x) then x else ~x)`--));

val ABS_ZERO = prove_thm("ABS_ZERO",
  (--`!x. (abs(x) = 0) = (x = 0)`--),
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_NEG_EQ0]);

val ABS_0 = prove_thm("ABS_0",
  (--`abs(0) = 0`--),
  REWRITE_TAC[ABS_ZERO]);

val ABS_1 = prove_thm("ABS_1",
  (--`abs(&1) = &1`--),
  REWRITE_TAC[abs, REAL_LE, ZERO_LESS_EQ]);

val ABS_NEG = prove_thm("ABS_NEG",
  (--`!x. abs~x = abs(x)`--),
  GEN_TAC THEN REWRITE_TAC[abs, REAL_NEGNEG, REAL_NEG_GE0] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MP_TAC(CONJ (ASSUME (--`0 <= x`--)) (ASSUME (--`x <= 0`--))) THEN
    REWRITE_TAC[REAL_LE_ANTISYM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_NEG_0],
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    W(MP_TAC o end_itlist CONJ o map ASSUME o fst) THEN
    REWRITE_TAC[REAL_LT_ANTISYM]]);

val ABS_TRIANGLE = prove_thm("ABS_TRIANGLE",
  (--`!x y. abs(x + y) <= abs(x) + abs(y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[abs] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_LE_REFL, REAL_LE_LADD, REAL_LE_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_NEG_ADD, REAL_LE_NEGL, REAL_LE_NEGR] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(UNDISCH_TAC (--`(x + y) < 0`--)) THEN SUBST1_TAC(SYM(SPEC (--`0`--) REAL_ADD_LID))
  THEN REWRITE_TAC[REAL_NOT_LT] THEN
  MAP_FIRST MATCH_MP_TAC [REAL_LT_ADD2, REAL_LE_ADD2] THEN
  ASM_REWRITE_TAC[]);

val ABS_POS = prove_thm("ABS_POS",
  (--`!x. 0 <= abs(x)`--),
  GEN_TAC THEN ASM_CASES_TAC (--`0 <= x`--) THENL
   [ALL_TAC,
    MP_TAC(SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[abs]);

val ABS_MUL = prove_thm("ABS_MUL",
  (--`!x y. abs(x * y) = abs(x) * abs(y)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`0 <= x`--) THENL
   [ALL_TAC,
    MP_TAC(SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    GEN_REWR_TAC LAND_CONV  [GSYM ABS_NEG] THEN
    GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [GSYM ABS_NEG]
    THEN REWRITE_TAC[REAL_NEG_LMUL]] THEN
  (ASM_CASES_TAC (--`0 <= y`--) THENL
    [ALL_TAC,
     MP_TAC(SPEC (--`y:real`--) REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
     GEN_REWR_TAC LAND_CONV  [GSYM ABS_NEG] THEN
     GEN_REWR_TAC (RAND_CONV o RAND_CONV)
                     [GSYM ABS_NEG] THEN
     REWRITE_TAC[REAL_NEG_RMUL]]) THEN
  ASSUM_LIST(ASSUME_TAC o MATCH_MP REAL_LE_MUL o LIST_CONJ o rev) THEN
  ASM_REWRITE_TAC[abs]);

val ABS_LT_MUL2 = prove_thm("ABS_LT_MUL2",
  (--`!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS]);

val ABS_SUB = prove_thm("ABS_SUB",
  (--`!x y. abs(x - y) = abs(y - x)`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[ABS_NEG]);

val ABS_NZ = prove_thm("ABS_NZ",
  (--`!x. ~(x = 0) = 0 < abs(x)`--),
  GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABS_ZERO] THEN
    REWRITE_TAC[TAUT_CONV (--`~a ==> b = b \/ a`--)] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_LE_LT, ABS_POS],
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[abs, REAL_LT_REFL, REAL_LE_REFL]]);

val ABS_INV = prove_thm("ABS_INV",
  (--`!x. ~(x = 0) ==> (abs(inv x) = inv(abs(x)))`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[abs, REAL_LE] THEN
  REWRITE_TAC[num_CONV (--`1:num`--), GSYM NOT_LESS, NOT_LESS_0]);

val ABS_ABS = prove_thm("ABS_ABS",
  (--`!x. abs(abs(x)) = abs(x)`--),
  GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV  [abs] THEN
  REWRITE_TAC[ABS_POS]);

val ABS_LE = prove_thm("ABS_LE",
  (--`!x. x <= abs(x)`--),
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_LE_NEGR] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_NOT_LE]);

val ABS_REFL = prove_thm("ABS_REFL",
  (--`!x. (abs(x) = x) = 0 <= x`--),
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  ASM_CASES_TAC (--`0 <= x`--) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  REWRITE_TAC[REAL_DOUBLE, REAL_ENTIRE, REAL_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV num_EQ_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_LE_REFL]);

val ABS_N = prove_thm("ABS_N",
  (--`!n. abs(&n) = &n`--),
  GEN_TAC THEN REWRITE_TAC[ABS_REFL, REAL_LE, ZERO_LESS_EQ]);

val ABS_BETWEEN = prove_thm("ABS_BETWEEN",
  (--`!x y d. 0 < d /\ ((x - d) < y) /\ (y < (x + d)) = abs(y - x) < d`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[abs] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN REWRITE_TAC[REAL_NEG_SUB] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_SUB_RADD] THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [REAL_ADD_SYM] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN (--`x < (x + d)`--) MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`y:real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`y:real`--) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR],
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN (--`y < (y + d)`--) MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR]]);

val ABS_BOUND = prove_thm("ABS_BOUND",
  (--`!x y d. abs(x - y) < d ==> y < (x + d)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  ONCE_REWRITE_TAC[GSYM ABS_BETWEEN] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);

val ABS_STILLNZ = prove_thm("ABS_STILLNZ",
  (--`!x y. abs(x - y) < abs(y) ==> ~(x = 0)`--),
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL]);

val ABS_CASES = prove_thm("ABS_CASES",
  (--`!x. (x = 0) \/ 0 < abs(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
  BOOL_CASES_TAC (--`x = 0`--) THEN ASM_REWRITE_TAC[]);

val ABS_BETWEEN1 = prove_thm("ABS_BETWEEN1",
  (--`!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z`--),
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LET_TOTAL) THENL
   [ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
    REWRITE_TAC[real_sub, REAL_LT_RADD] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2),
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[]]);

val ABS_SIGN = prove_thm("ABS_SIGN",
  (--`!x y. abs(x - y) < y ==> 0 < x`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ABS_BOUND) THEN
  REWRITE_TAC[REAL_LT_ADDL]);

val ABS_SIGN2 = prove_thm("ABS_SIGN2",
  (--`!x y. abs(x - y) < ~y ==> x < 0`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`~x`--), (--`~y`--)] ABS_SIGN) THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEGNEG]);

val ABS_DIV = prove_thm("ABS_DIV",
  (--`!y. ~(y = 0) ==> !x. abs(x / y) = abs(x) / abs(y)`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[real_div] THEN
  REWRITE_TAC[ABS_MUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]));

val ABS_CIRCLE = prove_thm("ABS_CIRCLE",
  (--`!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(x) + abs(h)`--) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC (--`abs(x)`--) REAL_LE_REFL)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD2) THEN
  REWRITE_TAC[REAL_SUB_ADD2]);

val REAL_SUB_ABS = prove_thm("REAL_SUB_ABS",
  (--`!x y. (abs(x) - abs(y)) <= abs(x - y)`--),
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`(abs(x - y) + abs(y)) - abs(y)`--) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[real_sub] THEN REWRITE_TAC[REAL_LE_RADD] THEN
    SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`y:real`--)] REAL_SUB_ADD)) THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)  [REAL_SUB_ADD] THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE,
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_ADD_SUB, REAL_LE_REFL]]);

val ABS_SUB_ABS = prove_thm("ABS_SUB_ABS",
  (--`!x y. abs(abs(x) - abs(y)) <= abs(x - y)`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)  [abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_SUB_ABS] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  REWRITE_TAC[REAL_SUB_ABS]);

val ABS_BETWEEN2 = prove_thm("ABS_BETWEEN2",
  (--`!x0 x y0 y.
        x0 < y0 /\
        abs(x - x0) < (y0 - x0) / &2 /\
        abs(y - y0) < (y0 - x0) / &2
        ==> x < y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`x < y0 /\ x0 < y`--) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [(--`x0:real`--), (--`x:real`--),
                    (--`y0 - x0`--)] ABS_BOUND) THEN
      REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[ABS_SUB] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (--`(y0 - x0) / &2`--) THEN
      ASM_REWRITE_TAC[REAL_LT_HALF2] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT],
      GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
      PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
       (--`(y0 + ~x0) + (x0 + ~y) = (~x0 + x0) + (y0 + ~y)`--)) THEN
      REWRITE_TAC[GSYM real_sub, REAL_ADD_LINV, REAL_ADD_LID] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [(--`y0 - x0`--),
                    (--`x0 - y`--)] REAL_LE_ADDR) THEN
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN (--`~(y0 <= y)`--) ASSUME_TAC THENL
       [REWRITE_TAC[REAL_NOT_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`y0 - x0`--) THEN
        ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_SUB_LT], ALL_TAC] THEN
      UNDISCH_TAC (--`abs(y - y0) < (y0 - x0) / &2`--) THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN DISCH_TAC THEN
      SUBGOAL_THEN (--`(y0 - x0) < (y0 - x0) / &2`--)
                   MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (--`y0 - y`--) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[REAL_LT_HALF2] THEN ASM_REWRITE_TAC[REAL_SUB_LT]],
    ALL_TAC] THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`abs(x0 - y) < (y0 - x0) / &2`--) ASSUME_TAC
  THENL
   [REWRITE_TAC[abs, REAL_SUB_LE] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`x - x0`--) THEN
    REWRITE_TAC[real_sub, REAL_LE_RADD] THEN
    ASM_REWRITE_TAC[GSYM real_sub] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs(x - x0)`--) THEN
    ASM_REWRITE_TAC[ABS_LE], ALL_TAC] THEN
  SUBGOAL_THEN
      (--`abs(y0 - x0) < ((y0 - x0) / &2) + ((y0 - x0) / &2)`--)
      MP_TAC
  THENL
   [ALL_TAC,
    REWRITE_TAC[REAL_HALF_DOUBLE, REAL_NOT_LT, ABS_LE]] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`abs(y0 - y) + abs(y - x0)`--) THEN
  CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_LT_ADD2 THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN (--`y0 - x0 = (y0 - y) + (y - x0)`--) SUBST1_TAC THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val ABS_BOUNDS = prove_thm("ABS_BOUNDS",
  (--`!x k. abs(x) <= k = ~k <= x /\ x <= k`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG] THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[TAUT_CONV (--`(a = b /\ a) = a ==> b`--)] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[REAL_LE_NEGL],
    REWRITE_TAC[TAUT_CONV (--`(a = a /\ b) = a ==> b`--)] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`~x`--) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_NEGR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE]]);

(*---------------------------------------------------------------------------*)
(* Define integer powers                                                     *)
(*---------------------------------------------------------------------------*)

val pow = new_prim_rec_definition("pow",
  (--`($pow x 0 = &1) /\
      ($pow x (SUC n) = x * ($pow x n))`--));
val _ = set_fixity "pow" (Infixr 700);

val POW_0 = prove_thm("POW_0",
  (--`!n. 0 pow (SUC n) = 0`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_MUL_LZERO]);

val POW_NZ = prove_thm("POW_NZ",
  (--`!c n. ~(c = 0) ==> ~(c pow n = 0)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[pow, REAL_10, REAL_ENTIRE]);

val POW_INV = prove_thm("POW_INV",
  (--`!c. ~(c = 0) ==> !n. (inv(c pow n) = (inv c) pow n)`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[pow, REAL_INV1] THEN
  MP_TAC(SPECL [(--`c:real`--), (--`c pow n`--)] REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN (--`~(c pow n = 0)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC POW_NZ THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[]);

val POW_ABS = prove_thm("POW_ABS",
  (--`!c n. abs(c) pow n = abs(c pow n)`--),
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, ABS_1, ABS_MUL]);

val POW_PLUS1 = prove_thm("POW_PLUS1",
  (--`!e. 0 < e ==> !n. (&1 + (&n * e)) <= (&1 + e) pow n`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`(&1 + e) * (&1 + (&n * e))`--) THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LDISTRIB, REAL_RDISTRIB, REAL, REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_ADD_ASSOC, REAL_LE_ADDR] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
    SUBGOAL_THEN (--`0 < (&1 + e)`--)
      (fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]) THEN
    GEN_REWR_TAC LAND_CONV  [GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT] THEN REWRITE_TAC[num_CONV (--`1:num`--), LESS_0]]);

val POW_ADD = prove_thm("POW_ADD",
  (--`!c m n. c pow (m + n) = (c pow m) * (c pow n)`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, ADD_CLAUSES, REAL_MUL_RID] THEN
  CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)));

val POW_1 = prove_thm("POW_1",
  (--`!x. x pow 1 = x`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV (--`1:num`--)] THEN
  REWRITE_TAC[pow, REAL_MUL_RID]);

val POW_2 = prove_thm("POW_2",
  (--`!x. x pow 2 = x * x`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV (--`2:num`--)] THEN
  REWRITE_TAC[pow, POW_1]);

val POW_ONE = prove_thm("POW_ONE",
 Term`!n. &1 pow n = &1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[pow, REAL_MUL_LID]);

val POW_POS = prove_thm("POW_POS",
  (--`!x. 0 <= x ==> !n. 0 <= (x pow n)`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_LE_01] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);

val POW_LE = prove_thm("POW_LE",
  (--`!n x y. 0 <= x /\ x <= y ==> (x pow n) <= (y pow n)`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LE_REFL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val POW_M1 = prove_thm("POW_M1",
  (--`!n. abs(~1 pow n) = 1`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, ABS_NEG, ABS_1] THEN
  ASM_REWRITE_TAC[ABS_MUL, ABS_NEG, ABS_1, REAL_MUL_LID]);

val POW_MUL = prove_thm("POW_MUL",
  (--`!n x y. (x * y) pow n = (x pow n) * (y pow n)`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_MUL_LID] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)));

val REAL_LE_POW2 = prove_thm("REAL_LE_POW2",
  (--`!x. 0 <= x pow 2`--),
  GEN_TAC THEN REWRITE_TAC[POW_2, REAL_LE_SQUARE]);

val ABS_POW2 = prove_thm("ABS_POW2",
  (--`!x. abs(x pow 2) = x pow 2`--),
  GEN_TAC THEN REWRITE_TAC[ABS_REFL, REAL_LE_POW2]);

val REAL_POW2_ABS = prove_thm("REAL_POW2_ABS",
  (--`!x. abs(x) pow 2 = x pow 2`--),
  GEN_TAC THEN REWRITE_TAC[POW_2, POW_MUL] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  REWRITE_TAC[GSYM POW_2, ABS_POW2]);

val REAL_LE1_POW2 = prove_thm("REAL_LE1_POW2",
  (--`!x. &1 <= x ==> &1 <= (x pow 2)`--),
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01]);

val REAL_LT1_POW2 = prove_thm("REAL_LT1_POW2",
  (--`!x. &1 < x ==> &1 < (x pow 2)`--),
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01]);

val POW_POS_LT = prove_thm("POW_POS_LT",
  (--`!x n. 0 < x ==> 0 < (x pow (SUC n))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[],
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC POW_NZ THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[]]);

val POW_2_LE1 = prove_thm("POW_2_LE1",
  (--`!n. &1 <= &2 pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LE_REFL] THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE] THEN
  REWRITE_TAC[ZERO_LESS_EQ, num_CONV (--`2:num`--), LESS_EQ_SUC_REFL]);

val POW_2_LT = prove_thm("POW_2_LT",
  (--`!n. &n < &2 pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LT_01] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, GSYM REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[POW_2_LE1]);

val POW_MINUS1 = prove_thm("POW_MINUS1",
  (--`!n. ~1 pow (2 * n) = 1`--),
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES, pow] THEN
  REWRITE_TAC(map num_CONV [Term`2:num`,Term`1:num`] @ [ADD_CLAUSES]) THEN
  REWRITE_TAC[pow] THEN
  REWRITE_TAC[SYM(num_CONV (--`2:num`--)), SYM(num_CONV (--`1:num`--))] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_NEGNEG]);

val POW_LT = prove_thm("POW_LT",
  (--`!n x y. 0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))`--),
  REPEAT STRIP_TAC THEN SPEC_TAC((--`n:num`--),(--`n:num`--))
   THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[pow, REAL_MUL_RID],
    ONCE_REWRITE_TAC[pow] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[]]);

val REAL_POW_LT = prove_thm("REAL_POW_LT",
 Term`!x n. 0 < x ==> 0 < (x pow n)`,
  REPEAT STRIP_TAC THEN SPEC_TAC(Term`n:num`,Term`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

val POW_EQ = prove_thm("POW_EQ",
  (--`!n x y. 0 <= x /\ 0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)`--),
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`x pow (SUC n) = y pow (SUC n)`--) THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THENL
   [ALL_TAC, CONV_TAC(RAND_CONV SYM_CONV)] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  MATCH_MP_TAC POW_LT THEN ASM_REWRITE_TAC[]);

val POW_ZERO = prove_thm("POW_ZERO",
  (--`!n x. (x pow n = 0) ==> (x = 0)`--),
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[pow] THEN
  REWRITE_TAC[REAL_10, REAL_ENTIRE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val POW_ZERO_EQ = prove_thm("POW_ZERO_EQ",
  (--`!n x. (x pow (SUC n) = 0) = (x = 0)`--),
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POW_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[POW_0]);

val REAL_POW_LT2 = prove_thm("REAL_POW_LT2",
 Term `!n x y. ~(n = 0) /\ 0 <= x /\ x < y ==> x pow n < y pow n`,
 INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, pow] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC (Term `n = 0:num`) THEN ASM_REWRITE_TAC[pow, REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

val LT_EXISTS = prove
 (Term`!m n. m < n = ?d. n = m + SUC d`,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [IMP_RES_TAC LESS_ADD_1 THEN ASM_REWRITE_TAC[]
     THEN EXISTS_TAC (Term`p:num`) THEN REWRITE_TAC [ADD1],
   ASM_REWRITE_TAC[LESS_ADD_SUC]]);

val REAL_POW_MONO_LT = prove_thm("REAL_POW_MONO_LT",
 Term`!m n x. &1 < x /\ m < n ==> x pow m < x pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LT_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL_IMP THEN CONJ_TAC THENL
   [SPEC_TAC(Term`d:num`,Term`d:num`) THEN
    INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [ASM_REWRITE_TAC[pow, REAL_MUL_RID], ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
    MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (Term`&1`) THEN
    ASM_REWRITE_TAC[REAL_LT,prim_recTheory.LESS_0, ONE]]);

val REAL_POW_POW = prove_thm("REAL_POW_POW",
 Term `!x m n. (x pow m) pow n = x pow (m * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, MULT_CLAUSES, POW_ADD]);;


(*---------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set        *)
(*---------------------------------------------------------------------------*)

val REAL_SUP_SOMEPOS = prove_thm("REAL_SUP_SOMEPOS",
  (--`!P. (?x. P x /\ 0 < x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) = y < s)`--),
  let val lemma = TAUT_CONV (--`a /\ b ==> b`--) in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC (--`\x. P x /\ 0 < x`--) REAL_SUP_ALLPOS) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[lemma] THEN
  SUBGOAL_THEN
  (--`?z. !x. P x /\ 0 < x ==> x < z`--) (SUBST1_TAC o EQT_INTRO)
  THENL
   [POP_ASSUM(X_CHOOSE_TAC (--`z:real`--) o CONJUNCT2) THEN
   EXISTS_TAC (--`z:real`--) THEN
    GEN_TAC THEN
    DISCH_THEN(curry op THEN (FIRST_ASSUM MATCH_MP_TAC) o ASSUME_TAC) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN (--`s:real`--) MP_TAC) THEN
  DISCH_THEN(curry op THEN (EXISTS_TAC (--`s:real`--) THEN GEN_TAC) o
                   (SUBST1_TAC o SYM o SPEC (--`y:real`--))) THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPECL [(--`y:real`--), (--`0`--)]
                                             REAL_LT_TOTAL)
    THENL
     [DISCH_THEN SUBST1_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      POP_ASSUM(X_CHOOSE_TAC (--`x:real`--) o CONJUNCT1) THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o CONJ th o CONJUNCT2)) THEN
      DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
      DISCH_THEN(K ALL_TAC) THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
      EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (--`y:real`--) THEN ASM_REWRITE_TAC[]],
    DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
    EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[]] end);

val SUP_LEMMA1 = prove_thm("SUP_LEMMA1",
  (--`!P s d. (!y. (?x. (\x. P(x + d)) x /\ y < x) = y < s)
     ==> (!y. (?x. P x /\ y < x) = y < (s + d))`--),
  REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  POP_ASSUM(MP_TAC o SPEC (--`y + ~d`--)) THEN
  REWRITE_TAC[REAL_LT_ADDNEG2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THENL
   [EXISTS_TAC (--`x + ~d`--) THEN
    ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID],
    EXISTS_TAC (--`x + d`--) THEN POP_ASSUM ACCEPT_TAC]);

val SUP_LEMMA2 = prove_thm("SUP_LEMMA2",
  (--`!P. (?x. P x) ==> ?d. ?x. (\x. P(x + d)) x /\ 0 < x`--),
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN BETA_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPECL [(--`x:real`--), (--`0`--)]
                                           REAL_LT_TOTAL)
  THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [(--`~1`--), (--`1`--)] THEN
    ASM_REWRITE_TAC[REAL_ADD_RINV, REAL_LT_01],
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [(--`x + x`--), (--`~x`--)] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID, REAL_NEG_GT0],
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(--`0`--), (--`x:real`--)] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID]]);

val SUP_LEMMA3 = prove_thm("SUP_LEMMA3",
  (--`!d. (?z. !x. P x ==> x < z) ==>
                (?z. !x. (\x. P(x + d)) x ==> x < z)`--),
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`z:real`--)) THEN
  EXISTS_TAC (--`z + ~d`--) THEN GEN_TAC THEN BETA_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[REAL_LT_ADDNEG]);

val REAL_SUP_EXISTS = prove_thm("REAL_SUP_EXISTS",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) = y < s)`--),
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC (--`d:real`--) o MATCH_MP SUP_LEMMA2) MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SPEC (--`d:real`--) SUP_LEMMA3)) THEN
  POP_ASSUM(fn th => DISCH_THEN(MP_TAC o MATCH_MP REAL_SUP_SOMEPOS o CONJ th))
  THEN
  DISCH_THEN(X_CHOOSE_TAC (--`s:real`--)) THEN
  EXISTS_TAC (--`s + d`--) THEN
  MATCH_MP_TAC SUP_LEMMA1 THEN POP_ASSUM ACCEPT_TAC);

val sup = new_definition("sup",
  (--`sup P = @s. !y. (?x. P x /\ y < x) = y < s`--));

val REAL_SUP = prove_thm("REAL_SUP",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) = y < sup P)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o SELECT_RULE o MATCH_MP REAL_SUP_EXISTS)
  THEN REWRITE_TAC[GSYM sup]);

val REAL_SUP_UBOUND = prove_thm("REAL_SUP_UBOUND",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC (--`sup P`--) o MATCH_MP REAL_SUP) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  X_GEN_TAC (--`x:real`--) THEN RULE_ASSUM_TAC(SPEC (--`x:real`--)) THEN
  DISCH_THEN (SUBST_ALL_TAC o EQT_INTRO) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_NOT_LT]);

val SETOK_LE_LT = prove_thm("SETOK_LE_LT",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) =
       (?x. P x) /\ (?z. !x. P x ==> x < z)`--),
  GEN_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC (--`z:real`--))
  THENL (map EXISTS_TAC [(--`z + &1`--), (--`z:real`--)]) THEN
  GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REAL_LT_ADD1, REAL_LT_IMP_LE]);

val REAL_SUP_LE = prove_thm("REAL_SUP_LE",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) = y < sup P)`--),
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT, REAL_SUP]);

val REAL_SUP_UBOUND_LE = prove_thm("REAL_SUP_UBOUND_LE",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)`--),
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT, REAL_SUP_UBOUND]);

(*---------------------------------------------------------------------------*)
(* Prove the Archimedean property                                            *)
(*---------------------------------------------------------------------------*)

val REAL_ARCH = prove_thm("REAL_ARCH",
  (--`!x. 0 < x ==> !y. ?n. y < &n * x`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV (--`a = ~(~a):bool`--)] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`\z. ?n. z = &n * x`--) REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN(fn th => REWRITE_TAC[th]) o funpow 2 (fst o dest_imp) o snd)
  THENL [CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [(--`&n * x`--), (--`n:num`--)] THEN REFL_TAC,
    EXISTS_TAC (--`y:real`--) THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC (--`sup(\z. ?n. z = &n * x) - x`--))
  THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`n:num`--)) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWR_TAC (funpow 3 RAND_CONV) [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC (--`sup(\z. ?n. z = &n * x)`--)) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN EXISTS_TAC (--`(&n + &1) * x`--)
  THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC (--`n + 1:num`--) THEN
  REWRITE_TAC[REAL_ADD]);

val REAL_ARCH_LEAST = prove_thm("REAL_ARCH_LEAST",
  (--`!y. 0 < y
          ==> !x. 0 <= x
          ==> ?n. (&n * y) <= x
                  /\ x < (&(SUC n) * y)`--),
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_ARCH) THEN
  GEN_TAC THEN POP_ASSUM(ASSUME_TAC o SPEC (--`x:real`--)) THEN
  POP_ASSUM(X_CHOOSE_THEN (--`n:num`--) MP_TAC o CONV_RULE EXISTS_LEAST_CONV)
  THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SPEC (--`PRE n`--))) THEN
  DISCH_TAC THEN EXISTS_TAC (--`PRE n`--) THEN
  SUBGOAL_THEN (--`SUC(PRE n) = n`--) ASSUME_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC (CHOOSE_THEN SUBST_ALL_TAC)
        (SPEC (--`n:num`--) num_CASES) THENL
     [UNDISCH_TAC (--`x < 0 * y`--) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO, GSYM REAL_NOT_LE],
      REWRITE_TAC[PRE]],
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PRE, LESS_SUC_REFL]]);

(*---------------------------------------------------------------------------*)
(* Now define finite sums; NB: sum(m,n) f = f(m) + f(m+1) + ... + f(m+n-1)   *)
(*---------------------------------------------------------------------------*)

val sumc = new_prim_rec_definition("sumc",
  (--`(sumc n 0 f = 0) /\
      (sumc n (SUC m) f = sumc n m f + f(n + m))`--));

val SUM_DEF = new_definition("SUM_DEF",
  (--`sum(m,n) f = sumc m n f`--));

val sum = prove_thm("sum",
  (--`!f n m. (sum(n,0) f = 0) /\
              (sum(n,SUC m) f = sum(n,m) f + f(n + m))`--),
  REWRITE_TAC[SUM_DEF, sumc]);

(*---------------------------------------------------------------------------*)
(* Useful manipulative theorems for sums                                     *)
(*---------------------------------------------------------------------------*)

val SUM_TWO = prove_thm("SUM_TWO",
  (--`!f n p. sum(0,n) f + sum(n,p) f = sum(0,n + p) f`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_ADD_RID, ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_ADD_ASSOC]);

val SUM_DIFF = prove_thm("SUM_DIFF",
  (--`!f m n. sum(m,n) f = sum(0,m + n) f - sum(0,m) f`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN MATCH_ACCEPT_TAC SUM_TWO);

val ABS_SUM = prove_thm("ABS_SUM",
  (--`!f m n. abs(sum(m,n) f) <= sum(m,n) (\n. abs(f n))`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, ABS_0, REAL_LE_REFL] THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`abs(sum(m,n) f) + abs(f(m + n))`--) THEN
  ASM_REWRITE_TAC[ABS_TRIANGLE, REAL_LE_RADD]);

val SUM_LE = prove_thm("SUM_LE",
  (--`!f g m n. (!r. m <= r /\ r < (n + m) ==> f(r) <= g(r))
        ==> (sum(m,n) f <= sum(m,n) g)`--),
  EVERY(replicate GEN_TAC 3) THEN
  INDUCT_TAC THEN REWRITE_TAC[sum, REAL_LE_REFL] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`n + m:num`--),
    GEN_REWR_TAC (RAND_CONV o RAND_CONV)  [ADD_SYM]] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES, LESS_EQ_ADD, LESS_SUC_REFL]);

val SUM_EQ = prove_thm("SUM_EQ",
  (--`!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (sum(m,n) f = sum(m,n) g)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN GEN_TAC THEN
  DISCH_THEN(fn th => MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN REFL_TAC);

val SUM_POS = prove_thm("SUM_POS",
  (--`!f. (!n. 0 <= f(n)) ==> !m n. 0 <= sum(m,n) f`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[]);

val SUM_POS_GEN = prove_thm("SUM_POS_GEN",
  (--`!f m. (!n. m <= n ==> 0 <= f(n)) ==>
        !n. 0 <= sum(m,n) f`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_ACCEPT_TAC LESS_EQ_ADD);

val SUM_ABS = prove_thm("SUM_ABS",
  (--`!f m n. abs(sum(m,n) (\m. abs(f m))) = sum(m,n) (\m. abs(f m))`--),
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[ABS_REFL] THEN
  GEN_TAC THEN MATCH_MP_TAC SUM_POS THEN BETA_TAC THEN
  REWRITE_TAC[ABS_POS]);

val SUM_ABS_LE = prove_thm("SUM_ABS_LE",
  (--`!f m n. abs(sum(m,n) f) <= sum(m,n)(\n. abs(f n))`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, ABS_0, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`abs(sum(m,n) f) + abs(f(m + n))`--) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_RADD]);

val SUM_ZERO = prove_thm("SUM_ZERO",
  (--`!f N. (!n. n >= N ==> (f(n) = 0))
              ==>
            (!m n. m >= N ==> (sum(m,n) f = 0))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [--`m:num`--, --`n:num`--] THEN
  REWRITE_TAC[GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD)
  THEN
  SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN INDUCT_TAC THEN REWRITE_TAC[sum]
  THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GREATER_EQ, GSYM ADD_ASSOC, LESS_EQ_ADD]);

val SUM_ADD = prove_thm("SUM_ADD",
  (--`!f g m n.
      sum(m,n) (\n. f(n) + g(n))
      =
      sum(m,n) f + sum(m,n) g`--),
  EVERY(replicate GEN_TAC 3) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_ADD_LID] THEN BETA_TAC THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val SUM_CMUL = prove_thm("SUM_CMUL",
  (--`!f c m n. sum(m,n) (\n. c * f(n)) = c * sum(m,n) f`--),
  EVERY(replicate GEN_TAC 3) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_MUL_RZERO] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_LDISTRIB]);

val SUM_NEG = prove_thm("SUM_NEG",
  (--`!f n d. sum(n,d) (\n. ~(f n)) = ~(sum(n,d) f)`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_NEG_0] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_NEG_ADD]);

val SUM_SUB = prove_thm("SUM_SUB",
  (--`!f g m n.
      sum(m,n)(\n. (f n) - (g n))
    = sum(m,n) f - sum(m,n) g`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, GSYM SUM_NEG, GSYM SUM_ADD] THEN
  BETA_TAC THEN REFL_TAC);

val SUM_SUBST = prove_thm("SUM_SUBST",
  (--`!f g m n. (!p. m <= p /\ p < (m + n) ==> (f p = g p))
        ==> (sum(m,n) f = sum(m,n) g)`--),
  EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN BINOP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC THEN
    MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[LESS_EQ_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    MATCH_MP_TAC LESS_MONO_ADD THEN REWRITE_TAC[LESS_SUC_REFL]]);

val SUM_NSUB = prove_thm("SUM_NSUB",
  (--`!n f c.
      sum(0,n) f - (&n * c)
        =
      sum(0,n)(\p. f(p) - c)`--),
  INDUCT_TAC THEN REWRITE_TAC[sum, REAL_MUL_LZERO, REAL_SUB_REFL] THEN
  REWRITE_TAC[ADD_CLAUSES, REAL, REAL_RDISTRIB] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN POP_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_MUL_LID] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val SUM_BOUND = prove_thm("SUM_BOUND",
  (--`!f k m n. (!p. m <= p /\ p < (m + n) ==> (f(p) <= k))
        ==> (sum(m,n) f <= (&n * k))`--),
  EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_MUL_LZERO, REAL_LE_REFL] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL, REAL_RDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_ACCEPT_TAC LESS_SUC,
    REWRITE_TAC[REAL_MUL_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ADD_CLAUSES, LESS_EQ_ADD] THEN
    MATCH_ACCEPT_TAC LESS_SUC_REFL]);

val SUM_GROUP = prove_thm("SUM_GROUP",
  (--`!n k f. sum(0,n)(\m. sum(m * k,k) f) = sum(0,n * k) f`--),
  INDUCT_TAC THEN REWRITE_TAC[sum, MULT_CLAUSES] THEN
  REPEAT GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES, SUM_TWO]);

val SUM_1 = prove_thm("SUM_1",
  (--`!f n. sum(n,1) f = f(n)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV (--`1:num`--), sum, ADD_CLAUSES, REAL_ADD_LID]);

val SUM_2 = prove_thm("SUM_2",
  (--`!f n. sum(n,2) f = f(n) + f(n + 1)`--),
  REPEAT GEN_TAC THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[sum, ADD_CLAUSES, REAL_ADD_LID]);

val SUM_OFFSET = prove_thm("SUM_OFFSET",
  (--`!f n k.
      sum(0,n)(\m. f(m + k))
    = sum(0,n + k) f - sum(0,k) f`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[GSYM SUM_TWO, REAL_ADD_SUB] THEN
  SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN
  INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC ADD_SYM);

val SUM_REINDEX = prove_thm("SUM_REINDEX",
  (--`!f m k n. sum(m + k,n) f = sum(m,n)(\r. f(r + k))`--),
  EVERY(replicate GEN_TAC 3) THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  ASM_REWRITE_TAC[REAL_EQ_LADD] THEN BETA_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(AC_CONV(ADD_ASSOC,ADD_SYM)));

val SUM_0 = prove_thm("SUM_0",
  (--`!m n. sum(m,n)(\r. 0) = 0`--),
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID]);

val SUM_PERMUTE_0 = prove_thm("SUM_PERMUTE_0",
  (--`!n p. (!y. y < n ==> ?!x. x < n /\ (p(x) = y))
        ==> !f. sum(0,n)(\n. f(p n)) = sum(0,n) f`--),
  INDUCT_TAC THEN GEN_TAC THEN TRY(REWRITE_TAC[sum] THEN NO_TAC) THEN
  DISCH_TAC THEN GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC (--`n:num`--)) THEN
  REWRITE_TAC[LESS_SUC_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) STRIP_ASSUME_TAC) THEN
  GEN_REWR_TAC RAND_CONV  [sum] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ABBREV_TAC (--`q:num->num = \r. if r < k then p(r) else p(SUC r)`--) THEN
  SUBGOAL_THEN (--`!y:num. y < n ==> ?!x. x < n /\ (q x = y)`--) MP_TAC
  THENL
   [X_GEN_TAC (--`y:num`--) THEN DISCH_TAC THEN
    (MP_TAC o ASSUME) (--`!y. y<SUC n ==> ?!x. x<SUC n /\ (p x = y)`--) THEN
    DISCH_THEN(MP_TAC o SPEC (--`y:num`--)) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`n:num`--) THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL],
      DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MP th))] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`x:num`--) STRIP_ASSUME_TAC o CONJUNCT1) THEN
    CONJ_TAC THENL
     [DISJ_CASES_TAC(SPECL [(--`x:num`--), (--`k:num`--)] LESS_CASES) THENL
       [EXISTS_TAC (--`x:num`--) THEN EXPAND_TAC "q" THEN BETA_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_LT] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC (--`&k`--) THEN ASM_REWRITE_TAC[REAL_LE, REAL_LT] THEN
        UNDISCH_TAC (--`k < SUC n`--) THEN
        REWRITE_TAC[LESS_EQ, LESS_EQ_MONO],
        MP_TAC(ASSUME (--`k <= x:num`--)) THEN REWRITE_TAC[LESS_OR_EQ] THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
         [EXISTS_TAC (--`x - 1:num`--) THEN EXPAND_TAC "q" THEN BETA_TAC THEN
          UNDISCH_TAC (--`k < x:num`--) THEN
          DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) MP_TAC o MATCH_MP LESS_ADD_1)
          THEN
          REWRITE_TAC[GSYM ADD1, ADD_CLAUSES] THEN
          DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_EQ]) THEN
          ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
          UNDISCH_TAC (--`(k + d) < k:num`--) THEN
          REWRITE_TAC[LESS_EQ] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[GSYM NOT_LESS, REWRITE_RULE[ADD_CLAUSES] LESS_ADD_SUC],
          SUBST_ALL_TAC(ASSUME (--`(p:num->num) x = n`--)) THEN
          UNDISCH_TAC (--`y < n:num`--) THEN ASM_REWRITE_TAC[LESS_REFL]]],
      SUBGOAL_THEN
       (--`!z. q z :num = p(if z < k then z else SUC z)`--) MP_TAC THENL
       [GEN_TAC THEN EXPAND_TAC "q" THEN BETA_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[],
        DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
      MAP_EVERY X_GEN_TAC [(--`x1:num`--), (--`x2:num`--)] THEN STRIP_TAC THEN
      UNDISCH_TAC (--`!y. y < SUC n ==> ?!x. x < SUC n /\ (p x = y)`--) THEN
      DISCH_THEN(MP_TAC o SPEC (--`y:num`--)) THEN
      REWRITE_TAC[MATCH_MP LESS_SUC (ASSUME (--`y < n:num`--))] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
      DISCH_THEN(MP_TAC
                 o SPECL [(--`if x1 < (k:num) then x1 else SUC x1`--),
                          (--`if x2 < (k:num) then x2 else SUC x2`--)]
                 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
       [CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LESS_MONO_EQ] THEN
        MATCH_MP_TAC LESS_SUC THEN ASM_REWRITE_TAC[],
        DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
        REPEAT COND_CASES_TAC THEN REWRITE_TAC[INV_SUC_EQ] THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`~(x2 < k:num)`--) THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
          EXISTS_TAC (--`SUC x2`--) THEN ASM_REWRITE_TAC[LESS_SUC_REFL],
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
          UNDISCH_TAC (--`~(x1 < k:num)`--) THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
          EXISTS_TAC (--`SUC x1`--) THEN ASM_REWRITE_TAC[LESS_SUC_REFL]]]],
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC(RAND_CONV o ONCE_DEPTH_CONV)[GSYM th])THEN
    BETA_TAC THEN UNDISCH_TAC (--`k < SUC n`--) THEN
    REWRITE_TAC[LESS_EQ, LESS_EQ_MONO] THEN
    DISCH_THEN(X_CHOOSE_TAC (--`d:num`--) o MATCH_MP LESS_EQUAL_ADD) THEN
    GEN_REWR_TAC (RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
                     [ASSUME (--`n = k + d:num`--)] THEN
    REWRITE_TAC[GSYM SUM_TWO] THEN
    GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME (--`n = k + d:num`--)] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUC] THEN
    REWRITE_TAC[GSYM SUM_TWO, sum, ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (--`r:num`--) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
      BETA_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[],
      GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
      REWRITE_TAC[ASSUME (--`(p:num->num) k = n`--), REAL_EQ_LADD] THEN
      REWRITE_TAC[ADD1, SUM_REINDEX] THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (--`r:num`--) THEN BETA_TAC THEN
      REWRITE_TAC[GSYM NOT_LESS] THEN DISCH_TAC THEN
      EXPAND_TAC "q" THEN BETA_TAC THEN ASM_REWRITE_TAC[ADD1]]]);

val SUM_CANCEL = prove_thm("SUM_CANCEL",
  (--`!f n d.
      sum(n,d) (\n. f(SUC n) - f(n))
    = f(n + d) - f(n)`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, ADD_CLAUSES, REAL_SUB_REFL] THEN
  BETA_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

(* ------------------------------------------------------------------------- *)
(* Theorems to be compatible with hol-light.                                 *)
(* ------------------------------------------------------------------------- *)

val REAL_MUL_RNEG = prove_thm("REAL_MUL_RNEG",
  Term`!x y. x * ~y = ~(x * y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL REAL_EQ_RADD)))) THEN
  EXISTS_TAC (Term`x:real * y`) THEN
  REWRITE_TAC[GSYM REAL_LDISTRIB, REAL_ADD_LINV, REAL_MUL_RZERO]);

val REAL_MUL_LNEG = prove_thm ("REAL_MUL_LNEG",
Term`!x y. ~x * y = ~(x * y)`,
  MESON_TAC[REAL_MUL_SYM, REAL_MUL_RNEG]);

val real_lt = prove_thm ("real_lt",
Term`!y x. x < y = ~(y <= x)`,
  let
    val th1 = TAUT_PROVE (Term`!t u:bool. (t = ~u) ==> (u = ~t)`)
    val th2 = SPECL [``y <= x``,``x < y``] th1
    val th3 = SPECL [``y:real``,``x:real``] real_lte
  in
    ACCEPT_TAC (GENL [``y:real``, ``x:real``] (MP th2 th3))
  end);

val REAL_LE_LADD_IMP = save_thm ("REAL_LE_LADD_IMP",
  let
    val th1 = GSYM (SPEC_ALL REAL_LE_LADD)
    val th2 = TAUT_PROVE ``(x:bool = y) ==> (x ==> y)``
  in
    GEN ``x:real`` (GEN ``y:real`` (GEN ``z:real`` (MATCH_MP th2 th1)))
  end);

val REAL_LE_LNEG = prove_thm ("REAL_LE_LNEG",
  ``!x y. ~x <= y = 0 <= x + y``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THENL
   [DISCH_THEN(MP_TAC o SPEC ``x:real``) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV],
    DISCH_THEN(MP_TAC o SPEC ``~x``) THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_ASSOC, REAL_ADD_LID,
        ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]]);

val REAL_LE_NEG2 = save_thm ("REAL_LE_NEG2", REAL_LE_NEG);

val REAL_NEG_NEG = save_thm ("REAL_NEG_NEG", REAL_NEGNEG);

val REAL_LE_RNEG = prove_thm ("REAL_LE_RNEG",
  ``!x y. x <= ~y = x + y <= 0``,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG, GSYM REAL_NEG_ADD] THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_LE_NEG2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_LINV] THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_NEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_ADD_LDISTRIB = save_thm ("REAL_ADD_LDISTRIB", REAL_LDISTRIB);

val REAL_ADD_RDISTRIB = save_thm ("REAL_ADD_RDISTRIB", REAL_RDISTRIB);

val REAL_OF_NUM_ADD = save_thm ("REAL_OF_NUM_ADD", REAL_ADD);

val REAL_OF_NUM_LE = save_thm ("REAL_OF_NUM_LE", REAL_LE);

val REAL_OF_NUM_MUL = save_thm ("REAL_OF_NUM_MUL", REAL_MUL);

val REAL_OF_NUM_SUC = prove_thm (
  "REAL_OF_NUM_SUC",
  ``!n. &n + &1 = &(SUC n)``,
  REWRITE_TAC[ADD1, REAL_ADD]);

val REAL_OF_NUM_EQ = save_thm ("REAL_OF_NUM_EQ", REAL_INJ);

val REAL_EQ_MUL_LCANCEL = prove_thm (
  "REAL_EQ_MUL_LCANCEL",
  ``!x y z. (x * y = x * z) = (x = 0) \/ (y = z)``,
  REWRITE_TAC [REAL_EQ_LMUL]);

val REAL_ABS_0 = save_thm ("REAL_ABS_0", ABS_0);

val REAL_ABS_TRIANGLE = save_thm ("REAL_ABS_TRIANGLE", ABS_TRIANGLE);

val REAL_ABS_MUL = save_thm ("REAL_ABS_MUL", ABS_MUL);

val REAL_ABS_POS = save_thm ("REAL_ABS_POS", ABS_POS);

val _ = export_theory();

end;

