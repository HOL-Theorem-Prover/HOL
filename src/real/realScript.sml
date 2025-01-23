(*---------------------------------------------------------------------------*)
(* Develop the theory of reals                                               *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open numLib reduceLib pairLib arithmeticTheory numTheory prim_recTheory
     whileTheory mesonLib tautLib simpLib Arithconv jrhUtils Canon_Port
     BasicProvers TotalDefn metisLib hurdUtils pred_setTheory;

open realaxTheory RealArith;

local open markerTheory in end; (* for unint *)

val _ = new_theory "real";

val TAUT_CONV   = jrhUtils.TAUT_CONV; (* conflict with tautLib.TAUT_CONV *)
val GEN_ALL     = hol88Lib.GEN_ALL;   (* it has old reverted variable order *)
val NUM_EQ_CONV = NEQ_CONV;

(*---------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism &:num->real. (moved to realax)      *)
(*---------------------------------------------------------------------------*)

val real_of_num = save_thm("real_of_num", real_of_num);

val REAL_0 = save_thm("REAL_0", REAL_0);
val REAL_1 = save_thm("REAL_1", REAL_1);

(* These are primitive real theorems being re-exported here *)
val REAL_10         = save_thm("REAL_10",        REAL_10');
val REAL_ADD_SYM    = save_thm("REAL_ADD_SYM",   REAL_ADD_SYM);
val REAL_ADD_COMM   = save_thm("REAL_ADD_COMM",  REAL_ADD_SYM);
val REAL_ADD_ASSOC  = save_thm("REAL_ADD_ASSOC", REAL_ADD_ASSOC);
val REAL_ADD_LID    = save_thm("REAL_ADD_LID",   REAL_ADD_LID');
val REAL_ADD_LINV   = save_thm("REAL_ADD_LINV",  REAL_ADD_LINV');
val REAL_LDISTRIB   = save_thm("REAL_LDISTRIB",  REAL_LDISTRIB);
val REAL_LT_TOTAL   = save_thm("REAL_LT_TOTAL",  REAL_LT_TOTAL);
val REAL_LT_REFL    = save_thm("REAL_LT_REFL",   REAL_LT_REFL);
val REAL_LT_TRANS   = save_thm("REAL_LT_TRANS",  REAL_LT_TRANS);
val REAL_LT_IADD    = save_thm("REAL_LT_IADD",   REAL_LT_IADD);
val REAL_SUP_ALLPOS = save_thm("REAL_SUP_ALLPOS",REAL_SUP_ALLPOS');
val REAL_MUL_SYM    = save_thm("REAL_MUL_SYM",   REAL_MUL_SYM);
val REAL_MUL_COMM   = save_thm("REAL_MUL_COMM",  REAL_MUL_SYM);
val REAL_MUL_ASSOC  = save_thm("REAL_MUL_ASSOC", REAL_MUL_ASSOC);
val REAL_MUL_LID    = save_thm("REAL_MUL_LID",   REAL_MUL_LID');
val REAL_MUL_LINV   = save_thm("REAL_MUL_LINV",  REAL_MUL_LINV');
val REAL_LT_MUL     = save_thm("REAL_LT_MUL",    REAL_LT_MUL');
val REAL_INV_0      = save_thm("REAL_INV_0",     REAL_INV_0');

val _ = export_rewrites
        ["REAL_ADD_LID", "REAL_ADD_LINV", "REAL_LT_REFL", "REAL_MUL_LID",
         "REAL_INV_0"]

(*---------------------------------------------------------------------------*)
(* Define subtraction, division and the other orderings (moved to realax)    *)
(*---------------------------------------------------------------------------*)

val real_sub = save_thm("real_sub", real_sub);
val real_lte = save_thm("real_lte", real_lte);
val real_gt  = save_thm("real_gt",  real_gt);
val real_ge  = save_thm("real_ge",  real_ge);
val real_div = save_thm("real_div", real_div);

(*---------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                       *)
(*---------------------------------------------------------------------------*)

(* |- !x. x + 0 = x *)
val REAL_ADD_RID = save_thm("REAL_ADD_RID", REAL_ADD_RID);
val _ = export_rewrites ["REAL_ADD_RID"]

val REAL_ADD_RINV = save_thm("REAL_ADD_RINV", REAL_ADD_RINV);
val _ = export_rewrites ["REAL_ADD_RINV"]

(* |- !x. x * 1 = x *)
val REAL_MUL_RID = save_thm("REAL_MUL_RID", REAL_MUL_RID);
val _ = export_rewrites ["REAL_MUL_RID"]

val REAL_MUL_RINV = store_thm("REAL_MUL_RINV",
  “!x. ~(x = 0) ==> (x * inv x = 1)”,
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LINV);

(* |- !x y z. (x + y) * z = x * z + y * z *)
val REAL_RDISTRIB = save_thm("REAL_RDISTRIB", REAL_RDISTRIB);

val REAL_EQ_LADD = save_thm("REAL_EQ_LADD", REAL_EQ_ADD_LCANCEL);
val _ = export_rewrites ["REAL_EQ_LADD"]

val REAL_EQ_RADD = save_thm("REAL_EQ_RADD", REAL_EQ_ADD_RCANCEL);
val _ = export_rewrites ["REAL_EQ_RADD"]

(* also known as REAL_EQ_ADD_LCANCEL_0 *)
val REAL_ADD_LID_UNIQ = store_thm("REAL_ADD_LID_UNIQ",
  “!x y. (x + y = y) <=> (x = 0)”,
  REAL_ARITH_TAC);

(* also known as REAL_EQ_ADD_RCANCEL_0 *)
val REAL_ADD_RID_UNIQ = store_thm("REAL_ADD_RID_UNIQ",
  “!x y. (x + y = x) <=> (y = 0)”,
  REAL_ARITH_TAC);

(* |- !x y. (x + y = 0) <=> (x = -y) *)
val REAL_LNEG_UNIQ = save_thm("REAL_LNEG_UNIQ", REAL_LNEG_UNIQ);

(* |- !x y. (x + y = 0) <=> (y = -x) *)
val REAL_RNEG_UNIQ = save_thm("REAL_RNEG_UNIQ", REAL_RNEG_UNIQ);

(* |- !x y. -(x + y) = -x + -y *)
val REAL_NEG_ADD = save_thm("REAL_NEG_ADD", REAL_NEG_ADD);

(* |- !x. 0 * x = 0 *)
val REAL_MUL_LZERO = save_thm("REAL_MUL_LZERO", REAL_MUL_LZERO);
val _ = export_rewrites ["REAL_MUL_LZERO"]

(* |- !x. x * 0 = 0 *)
val REAL_MUL_RZERO = save_thm("REAL_MUL_RZERO", REAL_MUL_RZERO);
val _ = export_rewrites ["REAL_MUL_RZERO"]

(* |- !x y. -(x * y) = -x * y *)
val REAL_NEG_LMUL = save_thm("REAL_NEG_LMUL", REAL_NEG_LMUL);

(* |- !x y. -(x * y) = x * -y *)
val REAL_NEG_RMUL = save_thm("REAL_NEG_RMUL", REAL_NEG_RMUL);

(* |- !x. --x = x *)
val REAL_NEGNEG = save_thm("REAL_NEGNEG", REAL_NEG_NEG);
val _ = export_rewrites ["REAL_NEGNEG"]

val REAL_NEG_MUL2 = store_thm("REAL_NEG_MUL2",
  “!x y. ~x * ~y = x * y”,
  REAL_ARITH_TAC);

(* |- !x y. (x * y = 0) <=> (x = 0) \/ (y = 0) *)
val REAL_ENTIRE = save_thm("REAL_ENTIRE", REAL_ENTIRE);
val _ = export_rewrites ["REAL_ENTIRE"]

(* |- !x y z. x + y < x + z <=> y < z *)
val REAL_LT_LADD = save_thm("REAL_LT_LADD", REAL_LT_LADD);
val _ = export_rewrites ["REAL_LT_LADD"]

(* |- !x y z. x + z < y + z <=> x < y *)
val REAL_LT_RADD = save_thm("REAL_LT_RADD", REAL_LT_RADD);
val _ = export_rewrites ["REAL_LT_RADD"]

(* |- !x y. ~(x < y) <=> y <= x *)
val REAL_NOT_LT = save_thm("REAL_NOT_LT", REAL_NOT_LT);

(* |- !x y. ~(x < y /\ y < x) *)
val REAL_LT_ANTISYM = save_thm("REAL_LT_ANTISYM", REAL_LT_ANTISYM);

(* |- !x y. x < y ==> ~(y < x) *)
val REAL_LT_GT = save_thm("REAL_LT_GT", REAL_LT_GT);

(* |- !x y. ~(x <= y) <=> y < x *)
val REAL_NOT_LE = save_thm("REAL_NOT_LE", REAL_NOT_LE);

(* |- !x y. x <= y \/ y <= x *)
val REAL_LE_TOTAL = save_thm("REAL_LE_TOTAL", REAL_LE_TOTAL);

(* |- !x y. x <= y \/ y < x *)
val REAL_LET_TOTAL = save_thm("REAL_LET_TOTAL", REAL_LET_TOTAL);

(* |- !x y. x < y \/ y <= x *)
val REAL_LTE_TOTAL = save_thm("REAL_LTE_TOTAL", REAL_LTE_TOTAL);

(* |- !x. x <= x *)
val REAL_LE_REFL = save_thm("REAL_LE_REFL", REAL_LE_REFL);
val _ = export_rewrites ["REAL_LE_REFL"]

(* |- !x y. x <= y <=> x < y \/ (x = y) *)
val REAL_LE_LT = save_thm("REAL_LE_LT", REAL_LE_LT);

(* |- !x y. x < y <=> x <= y /\ x <> y *)
val REAL_LT_LE = save_thm("REAL_LT_LE", REAL_LT_LE);

(* |- !x y. x < y ==> x <= y *)
val REAL_LT_IMP_LE = save_thm("REAL_LT_IMP_LE", REAL_LT_IMP_LE);

(* |- !x y z. x < y /\ y <= z ==> x < z *)
val REAL_LTE_TRANS = save_thm("REAL_LTE_TRANS", REAL_LTE_TRANS);

(* |- !x y z. x <= y /\ y < z ==> x < z *)
val REAL_LET_TRANS = save_thm("REAL_LET_TRANS", REAL_LET_TRANS);

(* |- !x y z. x <= y /\ y <= z ==> x <= z *)
val REAL_LE_TRANS = save_thm("REAL_LE_TRANS", REAL_LE_TRANS);

(* |- !x y. x <= y /\ y <= x <=> (x = y) *)
val REAL_LE_ANTISYM = save_thm("REAL_LE_ANTISYM", REAL_LE_ANTISYM);

val REAL_LET_ANTISYM = store_thm("REAL_LET_ANTISYM",
  “!x y. ~(x < y /\ y <= x)”,
  REAL_ARITH_TAC);

(* |- !x y. ~(x <= y /\ y < x) *)
val REAL_LTE_ANTISYM = save_thm("REAL_LTE_ANTISYM", REAL_LTE_ANTISYM);

(* old name with typo *)
Theorem REAL_LTE_ANTSYM = REAL_LTE_ANTISYM;

(* |- !x. -x < 0 <=> 0 < x *)
Theorem REAL_NEG_LT0[simp] = REAL_NEG_LT0

val REAL_NEG_GT0 = store_thm("REAL_NEG_GT0",
  “!x. 0 < ~x <=> x < 0”,
  REAL_ARITH_TAC);
val _ = export_rewrites ["REAL_NEG_GT0"]

val REAL_NEG_LE0 = store_thm("REAL_NEG_LE0",
  “!x. ~x <= 0 <=> 0 <= x”,
  REAL_ARITH_TAC);
val _ = export_rewrites ["REAL_NEG_LE0"]

val REAL_NEG_GE0 = store_thm("REAL_NEG_GE0",
  “!x. 0 <= ~x <=> x <= 0”,
  REAL_ARITH_TAC);
val _ = export_rewrites ["REAL_NEG_GE0"]

(* |- !x. (x = 0) \/ 0 < x \/ 0 < -x *)
Theorem REAL_LT_NEGTOTAL = REAL_LT_NEGTOTAL

(* |- !x. 0 <= x \/ 0 <= -x *)
Theorem REAL_LE_NEGTOTAL = REAL_LE_NEGTOTAL

(* |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x * y *)
val REAL_LE_MUL = save_thm("REAL_LE_MUL", REAL_LE_MUL);

(* |- !x. 0 <= x * x *)
val REAL_LE_SQUARE = save_thm("REAL_LE_SQUARE", REAL_LE_SQUARE);

(* |- 0 <= 1 *)
val REAL_LE_01 = save_thm("REAL_LE_01", REAL_LE_01);

(* |- 0 < 1 *)
val REAL_LT_01 = save_thm("REAL_LT_01", REAL_LT_01);

(* |- !x y z. x + y <= x + z <=> y <= z *)
val REAL_LE_LADD = save_thm("REAL_LE_LADD", REAL_LE_LADD);
val _ = export_rewrites ["REAL_LE_LADD"]

(* |- !x y z. x + z <= y + z <=> x <= y *)
val REAL_LE_RADD = save_thm("REAL_LE_RADD", REAL_LE_RADD);
val _ = export_rewrites ["REAL_LE_RADD"]

val REAL_LT_ADD2 = store_thm("REAL_LT_ADD2",
  “!w x y z. w < x /\ y < z ==> (w + y) < (x + z)”,
  REAL_ARITH_TAC);

val REAL_LE_ADD2 = store_thm("REAL_LE_ADD2",
  “!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)”,
  REAL_ARITH_TAC);

(* |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x + y *)
val REAL_LE_ADD = save_thm("REAL_LE_ADD", REAL_LE_ADD);

(* |- !x y. 0 < x /\ 0 < y ==> 0 < x + y *)
val REAL_LT_ADD = save_thm("REAL_LT_ADD", REAL_LT_ADD);

val REAL_LT_ADDNEG = store_thm("REAL_LT_ADDNEG",
  “!x y z. y < x + ~z <=> y + z < x”,
  REAL_ARITH_TAC);

val REAL_LT_ADDNEG2 = store_thm("REAL_LT_ADDNEG2",
  “!x y z. (x + ~y) < z <=> x < (z + y)”,
  REAL_ARITH_TAC);

val REAL_LT_ADD1 = store_thm("REAL_LT_ADD1",
  “!x y. x <= y ==> x < (y + &1)”,
  REAL_ARITH_TAC);

val REAL_SUB_ADD = store_thm("REAL_SUB_ADD",
  “!x y. (x - y) + y = x”,
  REAL_ARITH_TAC);

val REAL_SUB_ADD2 = store_thm("REAL_SUB_ADD2",
  “!x y. y + (x - y) = x”,
  REAL_ARITH_TAC);

val REAL_SUB_REFL = store_thm("REAL_SUB_REFL",
  “!x. x - x = 0”,
  REAL_ARITH_TAC);
val _ = export_rewrites ["REAL_SUB_REFL"]

(* |- !x y. (x - y = 0) <=> (x = y) *)
val REAL_SUB_0 = save_thm("REAL_SUB_0", REAL_SUB_0);
val _ = export_rewrites ["REAL_SUB_0"]

val REAL_LE_DOUBLE = store_thm("REAL_LE_DOUBLE",
  “!x. 0 <= x + x <=> 0 <= x”,
  REAL_ARITH_TAC);

val REAL_LE_NEGL = store_thm("REAL_LE_NEGL",
  “!x. (~x <= x) <=> (0 <= x)”,
  REAL_ARITH_TAC);

val REAL_LE_NEGR = store_thm("REAL_LE_NEGR",
  “!x. (x <= ~x) <=> (x <= 0)”,
  REAL_ARITH_TAC);

Theorem REAL_NEG_EQ0[simp]:
  !x. (-x = 0) <=> (x = 0)
Proof
  REAL_ARITH_TAC
QED

(* |- -0 = 0 *)
val REAL_NEG_0 = save_thm("REAL_NEG_0", REAL_NEG_0);
val _ = export_rewrites ["REAL_NEG_0"]

(* |- !x y. -(x - y) = y - x *)
val REAL_NEG_SUB = save_thm("REAL_NEG_SUB", REAL_NEG_SUB);

(* |- !x y. 0 < x - y <=> y < x *)
val REAL_SUB_LT = save_thm("REAL_SUB_LT", REAL_SUB_LT);

(* |- !x y. 0 <= x - y <=> y <= x *)
val REAL_SUB_LE = save_thm("REAL_SUB_LE", REAL_SUB_LE);

val REAL_ADD_SUB = store_thm("REAL_ADD_SUB",
  “!x y. (x + y) - x = y”,
  REAL_ARITH_TAC);

val REAL_SUB_LDISTRIB = store_thm("REAL_SUB_LDISTRIB",
  “!x y z. x * (y - z) = (x * y) - (x * z)”,
  REAL_ARITH_TAC);

val REAL_SUB_RDISTRIB = store_thm("REAL_SUB_RDISTRIB",
  “!x y z. (x - y) * z = (x * z) - (y * z)”,
  REAL_ARITH_TAC);

val REAL_SUB_LZERO = store_thm("REAL_SUB_LZERO",
  “!x. 0 - x = ~x”, REAL_ARITH_TAC);
val _ = export_rewrites ["REAL_SUB_LZERO"]

val REAL_SUB_RZERO = store_thm("REAL_SUB_RZERO",
  “!x. x - 0 = x”, REAL_ARITH_TAC);
val _ = export_rewrites ["REAL_SUB_RZERO"]

(* also known as REAL_EQ_MUL_LCANCEL *)
val REAL_EQ_LMUL = store_thm("REAL_EQ_LMUL",
  “!x y z. (x * y = x * z) <=> (x = 0) \/ (y = z)”,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH “(x = y) <=> (x - y = &0)”] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, REAL_ENTIRE, REAL_SUB_RZERO]);
val _ = export_rewrites ["REAL_EQ_LMUL"]

(* also known as REAL_EQ_MUL_RCANCEL *)
val REAL_EQ_RMUL = store_thm("REAL_EQ_RMUL",
  “!x y z. (x * z = y * z) <=> (z = 0) \/ (x = y)”,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_EQ_LMUL] THEN
  MESON_TAC[]);
val _ = export_rewrites ["REAL_EQ_RMUL"]

val REAL_NEG_EQ = store_thm("REAL_NEG_EQ",
  “!x y:real. (~x = y) <=> (x = ~y)”,
  REAL_ARITH_TAC);

val REAL_NEG_MINUS1 = store_thm("REAL_NEG_MINUS1",
  “!x. ~x = ~1 * x”,
  REAL_ARITH_TAC);

val REAL_INV_NZ = store_thm("REAL_INV_NZ",
  “!x. ~(x = 0) ==> ~(inv x = 0)”,
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM “x:real” o AP_TERM “$*”) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_10]);

val REAL_INVINV = store_thm("REAL_INVINV",
  “!x. ~(x = 0) ==> (inv (inv x) = x)”,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_MUL_RINV) THEN
  ASM_CASES_TAC “inv x = 0” THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO, GSYM REAL_10] THEN
  MP_TAC(SPECL [“inv(inv x)”, “x:real”, “inv x”] REAL_EQ_RMUL)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  FIRST_ASSUM ACCEPT_TAC);

val REAL_LT_IMP_NE = store_thm("REAL_LT_IMP_NE",
  “!x y. x < y ==> ~(x = y)”,
  REAL_ARITH_TAC);

val REAL_INV_POS = store_thm("REAL_INV_POS",
  “!x. 0 < x ==> 0 < inv x”,
  GEN_TAC THEN DISCH_TAC THEN REPEAT_TCL DISJ_CASES_THEN
   MP_TAC (SPECL [“inv x”, “0”] REAL_LT_TOTAL) THENL
   [POP_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_NZ o
              GSYM o MATCH_MP REAL_LT_IMP_NE) THEN ASM_REWRITE_TAC[],
    ONCE_REWRITE_TAC[GSYM REAL_NEG_GT0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL o C CONJ (ASSUME “0 < x”)) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    POP_ASSUM(fn th => REWRITE_TAC
     [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_NEG_GT0] THEN DISCH_THEN(MP_TAC o CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_LT_ANTISYM],
    REWRITE_TAC[]]);

val REAL_LT_LMUL_0 = store_thm("REAL_LT_LMUL_0",
  “!x y. 0 < x ==> (0 < (x * y) <=> 0 < y)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_INV_POS th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC
      [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_MUL_LID],
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);

val REAL_LT_RMUL_0 = store_thm("REAL_LT_RMUL_0",
  “!x y. 0 < y ==> (0 < (x * y) <=> 0 < x)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL_0);

(* also known as REAL_LT_LMUL_EQ *)
val REAL_LT_LMUL = store_thm("REAL_LT_LMUL",
  “!x y z. 0 < x ==> ((x * y) < (x * z) <=> y < z)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LMUL_0);

(* also known as REAL_LT_RMUL_EQ *)
val REAL_LT_RMUL = store_thm("REAL_LT_RMUL",
  “!x y z. 0 < z ==> ((x * z) < (y * z) <=> x < y)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL);

val REAL_LT_RMUL_IMP = store_thm("REAL_LT_RMUL_IMP",
  “!x y z. x < y /\ 0 < z ==> (x * z) < (y * z)”,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fn th => REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_RMUL th)]));

val REAL_LT_LMUL_IMP = store_thm("REAL_LT_LMUL_IMP",
  “!x y z. y < z  /\ 0 < x ==> (x * y) < (x * z)”,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fn th => REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_LMUL th)]));

(* also known as REAL_LE_LMUL_LOCAL *)
Theorem REAL_LE_LMUL:
  !x y z. 0 < x ==> ((x * y) <= (x * z) <=> y <= z)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]
QED

(* also known as REAL_LE_RMUL_EQ *)
val REAL_LE_RMUL = store_thm("REAL_LE_RMUL",
  “!x y z. 0 < z ==> ((x * z) <= (y * z) <=> x <= y)”,
   REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_ACCEPT_TAC REAL_LE_LMUL);

(* recovered from transc.ml *)
Theorem REAL_LE_LCANCEL_IMP :
    !x y z. 0 < x /\ x * y <= x * z ==> y <= z
Proof
    rpt STRIP_TAC
 >> drule (GSYM REAL_LE_LMUL)
 >> DISCH_THEN (fn th => ASM_REWRITE_TAC [th])
QED

(* dual theorem of the above *)
Theorem REAL_LE_RCANCEL_IMP :
    !x y z. 0 < z /\ x * z <= y * z ==> x <= y
Proof
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_LE_LCANCEL_IMP]
QED

val REAL_LINV_UNIQ = store_thm("REAL_LINV_UNIQ",
  “!x y. (x * y = &1) ==> (x = inv y)”,
  REPEAT GEN_TAC THEN ASM_CASES_TAC “x = 0” THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, GSYM REAL_10] THEN
  DISCH_THEN(MP_TAC o AP_TERM “$* (inv x)”) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_INVINV);

val REAL_RINV_UNIQ = store_thm("REAL_RINV_UNIQ",
  “!x y. (x * y = &1) ==> (y = inv x)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LINV_UNIQ);

(* cf. REAL_INVINV *)
val REAL_INV_INV = store_thm("REAL_INV_INV",
 Term`!x. inv(inv x) = x`,
  GEN_TAC THEN ASM_CASES_TAC (Term `x = 0`) THEN
  ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_REWRITE_TAC[]);;

Theorem REAL_INV_EQ_0[simp]:
 !x. (inv(x) = 0) <=> (x = 0)
Proof
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN ASM_REWRITE_TAC[REAL_INV_0]
QED

Theorem REAL_INV_EQ_0'[simp]:
  !x. (0 = inv x) <=> (x = 0)
Proof metis_tac[REAL_INV_EQ_0]
QED

val REAL_NEG_INV = store_thm("REAL_NEG_INV",
  “!x. ~(x = 0) ==> (~inv x = inv (~x))”,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_NEGNEG]);

Theorem REAL_NEG_INV':
  -inv x = inv (-x)
Proof
  Cases_on ‘x = 0’ >> simp[REAL_NEG_INV]
QED

(* |- !x. inv (-x) = -inv x (HOL-Light compatible name and statements) *)
Theorem REAL_INV_NEG = GEN_ALL (SYM REAL_NEG_INV')

val REAL_INV_1OVER = store_thm("REAL_INV_1OVER",
  “!x. inv x = &1 / x”,
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_LID]);

Theorem REAL_LT_INV_EQ[simp]:
  !x. 0 < inv x <=> 0 < x
Proof
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[REAL_INV_POS] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[REAL_INV_POS]
QED

Theorem REAL_LE_INV_EQ[simp]:
  !x. 0 <= inv x <=> 0 <= x
Proof
  REWRITE_TAC[REAL_LE_LT, REAL_LT_INV_EQ, REAL_INV_EQ_0] THEN
  MESON_TAC[REAL_INV_EQ_0]
QED

val REAL_LE_INV = store_thm("REAL_LE_INV",
 Term `!x. 0 <= x ==> 0 <= inv(x)`,
  REWRITE_TAC[REAL_LE_INV_EQ]);;

Theorem REAL_LE_ADDR[simp] = REAL_LE_ADDR

Theorem REAL_LE_ADDL[simp]:
  !x y. y <= x + y <=> 0 <= x
Proof
  REAL_ARITH_TAC
QED

(* |- !x y. x < x + y <=> 0 < y *)
Theorem REAL_LT_ADDR[simp] = REAL_LT_ADDR

Theorem REAL_LT_ADDL[simp]:
  !x y. y < x + y <=> 0 < x
Proof
  REAL_ARITH_TAC
QED

(*---------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                 *)
(*---------------------------------------------------------------------------*)

(* |- !n. &SUC n = &n + 1 *)
val REAL = save_thm("REAL", REAL);

(* !n. 0 <= &n *)
val REAL_POS = save_thm("REAL_POS", REAL_POS);
val _ = export_rewrites ["REAL_POS"]

(* !n. 0 < &SUC n *)
Theorem REAL_POS_LT = REAL_POS_LT;

(* |- !m n. &m <= &n <=> m <= n *)
val REAL_LE = save_thm("REAL_LE", REAL_LE);
val _ = export_rewrites ["REAL_LE"]

val REAL_LT = store_thm("REAL_LT",
  “!m n. &m < &n <=> m < n”,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC
    ((REWRITE_RULE[] o AP_TERM “$~:bool->bool” o
    REWRITE_RULE[GSYM NOT_LESS, GSYM REAL_NOT_LT]) (SPEC_ALL REAL_LE)));
val _ = export_rewrites ["REAL_LT"]

val REAL_INJ = save_thm("REAL_INJ", REAL_INJ);
val _ = export_rewrites ["REAL_INJ"]

(* |- !m n. &m + &n = &(m + n) *)
val REAL_ADD = save_thm("REAL_ADD", REAL_ADD);
val _ = export_rewrites ["REAL_ADD"]

(* |- !m n. &m * &n = &(m * n) *)
val REAL_MUL = save_thm("REAL_MUL", REAL_MUL);
val _ = export_rewrites ["REAL_MUL"]

(*---------------------------------------------------------------------------*)
(* Now more theorems                                                         *)
(*---------------------------------------------------------------------------*)

Theorem REAL_INV1[simp]:
  inv(&1) = &1
Proof
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[REAL_MUL_LID]
QED

(* HOL-Light compatible name *)
Theorem REAL_INV_1 = REAL_INV1

val REAL_OVER1 = store_thm("REAL_OVER1",
  “!x. x / &1 = x”,
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_INV1, REAL_MUL_RID]);
val _ = export_rewrites ["REAL_OVER1"]

val REAL_DIV_REFL = store_thm("REAL_DIV_REFL",
  “!x. ~(x = 0) ==> (x / x = &1)”,
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_RINV]);

val REAL_DIV_LZERO = store_thm("REAL_DIV_LZERO",
  “!x. 0 / x = 0”,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_LZERO]);

(* |- !n. &n <> 0 <=> 0 < &n *)
val REAL_LT_NZ = save_thm("REAL_LT_NZ", REAL_LT_NZ);

val REAL_NZ_IMP_LT = store_thm("REAL_NZ_IMP_LT",
  “!n. ~(n = 0) ==> 0 < &n”,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_INJ, REAL_LT_NZ]);

val REAL_LT_RDIV_0 = store_thm("REAL_LT_RDIV_0",
  “!y z. 0 < z ==> (0 < (y / z) <=> 0 < y)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_0 THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);

val REAL_LT_RDIV = store_thm("REAL_LT_RDIV",
  “!x y z. 0 < z ==> ((x / z) < (y / z) <=> x < y)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);

val REAL_LT_FRACTION_0 = store_thm("REAL_LT_FRACTION_0",
  “!n d. ~(n = 0) ==> (0 < (d / &n) <=> 0 < d)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_RDIV_0 THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_NZ, REAL_INJ]);

val REAL_LT_MULTIPLE = store_thm("REAL_LT_MULTIPLE",
  “!(n:num) d. 1 < n ==> (d < (&n * d) <=> 0 < d)”,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[num_CONV “1:num”, NOT_LESS_0],
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC “1 < n:num” THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[REAL, REAL_LDISTRIB, REAL_MUL_RID, REAL_LT_ADDL] THEN
      MATCH_MP_TAC REAL_LT_RMUL_0 THEN REWRITE_TAC[REAL_LT] THEN
      MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC “1:num” THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[num_CONV “1:num”, LESS_0],
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LESS_LEMMA1) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL, REAL_LDISTRIB, REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_LT_ADDL]]]);

val REAL_LT_FRACTION = store_thm("REAL_LT_FRACTION",
  “!(n:num) d. 1 < n ==> ((d / &n) < d <=> 0 < d)”,
  REPEAT GEN_TAC THEN ASM_CASES_TAC “n = 0:num” THEN
  ASM_REWRITE_TAC[NOT_LESS_0] THEN DISCH_TAC THEN
  UNDISCH_TAC “1 < n:num” THEN
  FIRST_ASSUM(fn th => let val th1 = REWRITE_RULE[GSYM REAL_INJ] th in
    MAP_EVERY ASSUME_TAC [th1, REWRITE_RULE[REAL_LT_NZ] th1] end) THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o LAND_CONV)
                                    [GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_MULTIPLE);

val REAL_LT_HALF1 = store_thm("REAL_LT_HALF1",
  “!d. 0 < (d / &2) <=> 0 < d”,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION_0 THEN
  REWRITE_TAC[num_CONV “2:num”, NOT_SUC]);

val REAL_LT_HALF2 = store_thm("REAL_LT_HALF2",
  “!d. (d / &2) < d <=> 0 < d”,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION THEN
  CONV_TAC(RAND_CONV num_CONV) THEN
  REWRITE_TAC[LESS_SUC_REFL]);

val REAL_DOUBLE = store_thm("REAL_DOUBLE",
  “!x. x + x = &2 * x”,
  REAL_ARITH_TAC);

val REAL_DIV_LMUL = store_thm("REAL_DIV_LMUL",
  “!x y. ~(y = 0) ==> (y * (x / y) = x)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_MUL_RID]);

val REAL_DIV_RMUL = store_thm("REAL_DIV_RMUL",
  “!x y. ~(y = 0) ==> ((x / y) * y = x)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_DIV_LMUL);

val REAL_HALF_DOUBLE = store_thm("REAL_HALF_DOUBLE",
  “!x. (x / &2) + (x / &2) = x”,
  GEN_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[]);

val REAL_DOWN = store_thm("REAL_DOWN",
  “!x. 0 < x ==> ?y. 0 < y /\ y < x”,
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC “x / &2” THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2]);

val REAL_DOWN2 = store_thm("REAL_DOWN2",
  “!x y. 0 < x /\ 0 < y ==> ?z. 0 < z /\ z < x /\ z < y”,
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[REAL_DOWN],
    DISCH_THEN(X_CHOOSE_TAC “z:real” o MATCH_MP REAL_DOWN o CONJUNCT1),
    DISCH_THEN(X_CHOOSE_TAC “z:real” o MATCH_MP REAL_DOWN o CONJUNCT2)] THEN
  EXISTS_TAC “z:real” THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_TRANS THENL
   [EXISTS_TAC “x:real”, EXISTS_TAC “y:real”] THEN
  ASM_REWRITE_TAC[]);

val REAL_SUB_SUB = store_thm("REAL_SUB_SUB",
  “!x y. (x - y) - x = ~y”,
  REAL_ARITH_TAC);

val REAL_LT_ADD_SUB = store_thm("REAL_LT_ADD_SUB",
  “!x y z. (x + y) < z <=> x < (z - y)”,
  REAL_ARITH_TAC);

val REAL_LT_SUB_RADD = store_thm("REAL_LT_SUB_RADD",
  “!x y z. (x - y) < z <=> x < z + y”,
  REAL_ARITH_TAC);

val REAL_LT_SUB_LADD = store_thm("REAL_LT_SUB_LADD",
  “!x y z. x < (y - z) <=> (x + z) < y”,
  REAL_ARITH_TAC);

val REAL_LE_SUB_LADD = store_thm("REAL_LE_SUB_LADD",
  “!x y z. x <= (y - z) <=> (x + z) <= y”,
  REAL_ARITH_TAC);

val REAL_LE_SUB_RADD = store_thm("REAL_LE_SUB_RADD",
  “!x y z. (x - y) <= z <=> x <= z + y”,
  REAL_ARITH_TAC);

Theorem REAL_LT_NEG[simp]:
  !x y. ~x < ~y <=> y < x
Proof
  REAL_ARITH_TAC
QED

(* |- !x y. -x <= -y <=> y <= x *)
val REAL_LE_NEG = save_thm("REAL_LE_NEG", REAL_LE_NEG2);
val _ = export_rewrites ["REAL_LE_NEG"]

val REAL_ADD2_SUB2 = store_thm("REAL_ADD2_SUB2",
  “!a b c d. (a + b) - (c + d) = (a - c) + (b - d)”,
  REAL_ARITH_TAC);

val REAL_LET_ADD2 = store_thm("REAL_LET_ADD2",
  “!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)”,
  REAL_ARITH_TAC);

val REAL_LTE_ADD2 = store_thm("REAL_LTE_ADD2",
  “!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)”,
  REAL_ARITH_TAC);

(* |- !x y. 0 <= x /\ 0 < y ==> 0 < x + y *)
val REAL_LET_ADD = save_thm("REAL_LET_ADD", REAL_LET_ADD);

(* |- !x y. 0 < x /\ 0 <= y ==> 0 < x + y *)
val REAL_LTE_ADD = save_thm("REAL_LTE_ADD", REAL_LTE_ADD);

(* also known as REAL_LT_MUL2_ALT *)
val REAL_LT_MUL2 = store_thm("REAL_LT_MUL2",
  “!x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN “!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))”
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      “(a + b) + (c + d) = (b + c) + (a + d)”] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID],
    DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, GSYM REAL_SUB_RDISTRIB] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x1:real” THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);

val REAL_LT_INV = store_thm("REAL_LT_INV",
  “!x y. 0 < x /\ x < y ==> inv y < inv x”,
  REPEAT GEN_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN “0 < y” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC “x:real” THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN “0 < (x * y)” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN “(inv y) < (inv x) <=>
                ((x * y) * (inv y)) < ((x * y) * (inv x))” SUBST1_TAC
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN “(x * (inv x) = &1) /\ (y * (inv y) = &1)”
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “x * (y * z) = (x * z) * y”] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);

val REAL_SUB_LNEG = store_thm("REAL_SUB_LNEG",
  “!x y. ~x - y = ~(x + y)”,
  REAL_ARITH_TAC);

val REAL_SUB_RNEG = store_thm("REAL_SUB_RNEG",
  “!x y. x - ~y = x + y”,
  REAL_ARITH_TAC);

val REAL_SUB_NEG2 = store_thm("REAL_SUB_NEG2",
  “!x y. ~x - ~y = y - x”,
  REAL_ARITH_TAC);

val REAL_SUB_TRIANGLE = store_thm("REAL_SUB_TRIANGLE",
  “!a b c. (a - b) + (b - c) = a - c”,
  REAL_ARITH_TAC);

val REAL_EQ_SUB_LADD = store_thm("REAL_EQ_SUB_LADD",
  “!x y z. (x = y - z) = (x + z = y)”,
  REAL_ARITH_TAC);

val REAL_EQ_SUB_RADD = store_thm("REAL_EQ_SUB_RADD",
  “!x y z. (x - y = z) = (x = z + y)”,
  REAL_ARITH_TAC);

(* also known as REAL_INV_MUL_WEAK *)
val REAL_INV_MUL = store_thm("REAL_INV_MUL",
  “!x y. ~(x = 0) /\ ~(y = 0) ==>
             (inv(x * y) = inv(x) * inv(y))”,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “(a * b) * (c * d) = (c * a) * (d * b)”] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  BINOP_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]);

(* Stronger version *)
Theorem REAL_INV_MUL':
  !x y. inv(x * y) = inv(x) * inv(y)
Proof
  REPEAT GEN_TAC THEN
  MAP_EVERY Cases_on [‘x = 0’, ‘y = 0’] THEN
  ASM_REWRITE_TAC[REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  MATCH_MP_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC []
QED

Theorem REAL_INV_DIV :
    !x y. x <> 0 /\ y <> 0 ==> (inv (x / y) = y * inv x)
Proof
    rpt STRIP_TAC
 >> ‘inv y <> 0’ by PROVE_TAC [REAL_INV_NZ]
 >> ASM_SIMP_TAC std_ss [real_div, REAL_INV_MUL, REAL_INVINV]
 >> PROVE_TAC [REAL_MUL_COMM]
QED

(* HOL-Light compatible *)
Theorem REAL_INV_DIV' :
    !x y. inv (x / y) = y * inv x
Proof
    REWRITE_TAC [real_div, REAL_INV_MUL', REAL_INV_INV, Once REAL_MUL_COMM]
QED

val REAL_SUB_INV2 = store_thm("REAL_SUB_INV2",
  “!x y. ~(x = 0) /\ ~(y = 0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))”,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div, REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN “inv(x * y) = inv(x) * inv(y)” SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_SUB_SUB2 = store_thm("REAL_SUB_SUB2",
  “!x y. x - (x - y) = y”,
  REAL_ARITH_TAC);

val REAL_ADD_SUB2 = store_thm("REAL_ADD_SUB2",
  “!x y. x - (x + y) = ~y”,
  REAL_ARITH_TAC);

val REAL_MEAN = store_thm("REAL_MEAN",
  “!x y. x < y ==> ?z. x < z /\ z < y”,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_DOWN o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT])
  THEN DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “x + d” THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_SUB_LADD]);

val REAL_EQ_LMUL2 = store_thm("REAL_EQ_LMUL2",
  “!x y z. ~(x = 0) ==> ((y = z) <=> (x * y = x * z))”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [“x:real”, “y:real”, “z:real”] REAL_EQ_LMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);

(* also known as REAL_LE_MUL2V *)
val REAL_LE_MUL2 = store_thm("REAL_LE_MUL2",
  “!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)”,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SPECL [“x1:real”, “x2:real”] REAL_LE_LT) THEN
  ASM_CASES_TAC “x1:real = x2” THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC “0 <= x2” THEN
    DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
     [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]),
      SUBST1_TAC(SYM(ASSUME “0 = x2”)) THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]], ALL_TAC] THEN
  UNDISCH_TAC “y1 <= y2” THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC “0 <= y1” THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    SUBST1_TAC(SYM(ASSUME “0 = y2”)) THEN
    REWRITE_TAC[REAL_MUL_RZERO, REAL_LE_REFL]]);

val REAL_LE_LDIV = store_thm("REAL_LE_LDIV",
  “!x y z. 0 < x /\ y <= (z * x) ==> (y / x) <= z”,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
  SUBGOAL_THEN “y = (y / x) * x” MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(fn t => GEN_REWR_TAC (funpow 2 LAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN POP_ASSUM ACCEPT_TAC]);

val REAL_LE_RDIV = store_thm("REAL_LE_RDIV",
  “!x y z. 0 < x /\ (y * x) <= z ==> y <= (z / x)”,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
  SUBGOAL_THEN “z = (z / x) * x” MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(fn t => GEN_REWR_TAC (LAND_CONV o RAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN POP_ASSUM ACCEPT_TAC]);

val REAL_LT_DIV = store_thm("REAL_LT_DIV",
 Term`!x y. 0 < x /\ 0 < y ==> 0 < x / y`,
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ]);

val REAL_LE_DIV = store_thm("REAL_LE_DIV",
 Term`!x y. 0 <= x /\ 0 <= y ==> 0 <= x / y`,
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ]);

val REAL_LT_1 = store_thm("REAL_LT_1",
  “!x y. 0 <= x /\ x < y ==> (x / y) < &1”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “(x / y) < &1 <=> ((x / y) * y) < (&1 * y)” SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x:real” THEN
    ASM_REWRITE_TAC[],
    SUBGOAL_THEN “(x / y) * y = x” SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[REAL_MUL_LID]]]);

Theorem REAL_LE_LMUL_IMP :
    !x y z. 0 <= x /\ y <= z ==> x * y <= x * z
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, REAL_SUB_RZERO, REAL_LE_MUL]
QED

(* HOL-light compatibility, moved from iterateTheory *)
Theorem REAL_LE_LMUL1 = REAL_LE_LMUL_IMP

Theorem REAL_LE_RMUL_IMP :
    !x y z. 0 <= x /\ y <= z ==> y * x <= z * x
Proof
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_LE_LMUL_IMP
QED

(* HOL-light compatibility, moved from iterateTheory *)
Theorem REAL_LE_RMUL1 = REAL_LE_RMUL_IMP

val REAL_EQ_IMP_LE = store_thm("REAL_EQ_IMP_LE",
  “!x y. (x = y) ==> x <= y”,
  REAL_ARITH_TAC);

val REAL_INV_LT1 = store_thm("REAL_INV_LT1",
  “!x. 0 < x /\ x < &1 ==> &1 < inv(x)”,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_POS) THEN
  GEN_REWR_TAC I [TAUT_CONV “a = ~~a:bool”] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [“inv(x)”, “&1”, “x:real”, “&1”] REAL_LT_MUL2) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC “0 < 0” THEN
      REWRITE_TAC[REAL_LT_REFL]],
    DISCH_THEN(MP_TAC o AP_TERM “inv”) THEN REWRITE_TAC[REAL_INV1] THEN
    SUBGOAL_THEN “inv(inv x) = x” SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC “&1 < &1” THEN
      REWRITE_TAC[REAL_LT_REFL]]]);

val REAL_POS_NZ = store_thm("REAL_POS_NZ",
  “!x. 0 < x ==> ~(x = 0)”,
  REAL_ARITH_TAC);

val REAL_EQ_RMUL_IMP = store_thm("REAL_EQ_RMUL_IMP",
  “!x y z. ~(z = 0) /\ (x * z = y * z) ==> (x = y)”,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[REAL_EQ_RMUL]);

val REAL_EQ_LMUL_IMP = store_thm("REAL_EQ_LMUL_IMP",
  “!x y z. ~(x = 0) /\ (x * y = x * z) ==> (y = z)”,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RMUL_IMP);

val REAL_FACT_NZ = store_thm("REAL_FACT_NZ",
  “!n. ~(&(FACT n) = 0)”,
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

val REAL_DIFFSQ = store_thm("REAL_DIFFSQ",
  “!x y. (x + y) * (x - y) = (x * x) - (y * y)”,
  REAL_ARITH_TAC);

Theorem REAL_POSSQ[simp]:
  !x. 0 < (x * x) <=> ~(x = 0)
Proof
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C CONJ (SPEC “x:real” REAL_LE_SQUARE)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM, REAL_ENTIRE],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]]
QED

val REAL_SUMSQ = store_thm("REAL_SUMSQ",
  “!x y. ((x * x) + (y * y) = 0) <=> (x = 0) /\ (y = 0)”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC REAL_POS_NZ THENL
     [MATCH_MP_TAC REAL_LTE_ADD, MATCH_MP_TAC REAL_LET_ADD] THEN
    ASM_REWRITE_TAC[REAL_POSSQ, REAL_LE_SQUARE],
    DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID]]);

Theorem REAL_EQ_NEG[simp]:
  !x y. (-x = -y) <=> (x = y)
Proof
  REAL_ARITH_TAC
QED

val REAL_DIV_MUL2 = store_thm("REAL_DIV_MUL2",
  “!x z. ~(x = 0) /\ ~(z = 0) ==> !y. y / z = (x * y) / (x * z)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “(a * b) * (c * d) = (c * a) * (b * d)”] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID]);

Theorem REAL_DIV_PROD:
  !a b c (d :real). a / b * (c / d) = (a * c) / (b * d)
Proof
    rpt STRIP_TAC
 >> simp[real_div,REAL_INV_MUL'] >> metis_tac[REAL_MUL_ASSOC,REAL_MUL_SYM]
QED

Theorem REAL_DIV_LT:
  !a b c (d :real). 0 < b * d ==> (a / b < c / d <=> a * d < c * b)
Proof
  rw[real_div]
  >> ‘b<>0 /\ d<>0’ by (CCONTR_TAC >> gs[])
  >> ‘a * inv b <c * inv d <=> a * inv b * (b*d) < c * inv d * (b*d)’ by simp[REAL_LT_RMUL]
  >> ‘a * inv b * (b*d) = a*d * (inv b * b)’ by metis_tac[REAL_MUL_ASSOC,REAL_MUL_SYM]
  >> ‘_ = a*d’ by simp[REAL_MUL_RID,REAL_MUL_LINV]
  >> ‘c * inv d * (b*d) = c*b * (inv d * d)’ by metis_tac[REAL_MUL_ASSOC,REAL_MUL_SYM]
  >> ‘_ = c*b’ by simp[REAL_MUL_RID,REAL_MUL_LINV]
  >> simp[]
QED

val REAL_MIDDLE1 = store_thm("REAL_MIDDLE1",
  “!a b. a <= b ==> a <= (a + b) / &2”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_RDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE, REAL_LE_LADD] THEN
  REWRITE_TAC[num_CONV “2:num”, REAL_LT, LESS_0]);

val REAL_MIDDLE2 = store_thm("REAL_MIDDLE2",
  “!a b. a <= b ==> ((a + b) / &2) <= b”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE, REAL_LE_RADD] THEN
  REWRITE_TAC[num_CONV “2:num”, REAL_LT, LESS_0]);

(*---------------------------------------------------------------------------*)
(* Define usual norm (absolute distance) on the real line                    *)
(*---------------------------------------------------------------------------*)

val abs = save_thm("abs", real_abs); (* moved to realaxTheory *)

Theorem ABS_ZERO[simp]:
   !x. (abs(x) = 0) <=> (x = 0)
Proof
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_NEG_EQ0]
QED

(* HOL-Light compatible name *)
val REAL_ABS_ZERO = ABS_ZERO;

Theorem ABS_0[simp]:      abs(0) = 0
Proof REWRITE_TAC[ABS_ZERO]
QED

Theorem ABS_1[simp]:      abs(&1) = &1
Proof REWRITE_TAC[abs, REAL_LE, ZERO_LESS_EQ]
QED

Theorem ABS_NEG[simp] = REAL_ABS_NEG

val ABS_TRIANGLE = store_thm("ABS_TRIANGLE",
  “!x y. abs(x + y) <= abs(x) + abs(y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_LE_REFL, REAL_LE_LADD, REAL_LE_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_NEG_ADD, REAL_LE_NEGL, REAL_LE_NEGR] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(UNDISCH_TAC “(x + y) < 0”) THEN SUBST1_TAC(SYM(SPEC “0” REAL_ADD_LID))
  THEN REWRITE_TAC[REAL_NOT_LT] THEN
  MAP_FIRST MATCH_MP_TAC [REAL_LT_ADD2, REAL_LE_ADD2] THEN
  ASM_REWRITE_TAC[]);

(* |- !x y. abs(x - y) <= abs(x) + abs(y) *)
val ABS_TRIANGLE_NEG = save_thm
  ("ABS_TRIANGLE_NEG",
   ((Q.GENL [`x`, `y`]) o (REWRITE_RULE [ABS_NEG, GSYM real_sub]) o
    (Q.SPECL [`x`, `-y`])) ABS_TRIANGLE);

val ABS_TRIANGLE_SUB = store_thm ("ABS_TRIANGLE_SUB",
 ``!x y:real. abs(x) <= abs(y) + abs(x - y)``,
  MESON_TAC[ABS_TRIANGLE, REAL_SUB_ADD2]);

val ABS_TRIANGLE_LT = store_thm ("ABS_TRIANGLE_LT",
  ``!x y. abs(x) + abs(y) < e ==> abs(x + y) < e:real``,
  MESON_TAC[REAL_LET_TRANS, ABS_TRIANGLE]);

Theorem ABS_POS[simp]:      !x. 0 <= abs(x)
Proof
  GEN_TAC THEN ASM_CASES_TAC “0 <= x” THENL
   [ALL_TAC,
    MP_TAC(SPEC “x:real” REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[abs]
QED

val ABS_MUL = store_thm("ABS_MUL",
  “!x y. abs(x * y) = abs(x) * abs(y)”,
  REPEAT GEN_TAC THEN ASM_CASES_TAC “0 <= x” THENL
   [ALL_TAC,
    MP_TAC(SPEC “x:real” REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    GEN_REWR_TAC LAND_CONV  [GSYM ABS_NEG] THEN
    GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [GSYM ABS_NEG]
    THEN REWRITE_TAC[REAL_NEG_LMUL]] THEN
  (ASM_CASES_TAC “0 <= y” THENL
    [ALL_TAC,
     MP_TAC(SPEC “y:real” REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
     GEN_REWR_TAC LAND_CONV  [GSYM ABS_NEG] THEN
     GEN_REWR_TAC (RAND_CONV o RAND_CONV)
                     [GSYM ABS_NEG] THEN
     REWRITE_TAC[REAL_NEG_RMUL]]) THEN
  ASSUM_LIST(ASSUME_TAC o MATCH_MP REAL_LE_MUL o LIST_CONJ o rev) THEN
  ASM_REWRITE_TAC[abs]);

val ABS_LT_MUL2 = store_thm("ABS_LT_MUL2",
  “!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS]);

val ABS_SUB = store_thm("ABS_SUB",
  “!x y. abs(x - y) = abs(y - x)”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[ABS_NEG]);

val ABS_NZ = store_thm("ABS_NZ",
  “!x. ~(x = 0) <=> 0 < abs(x)”,
  GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABS_ZERO] THEN
    REWRITE_TAC[TAUT_CONV “~a ==> b <=> b \/ a”] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_LE_LT, ABS_POS],
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[abs, REAL_LT_REFL, REAL_LE_REFL]]);

Theorem ABS_NZ'[simp] = GSYM ABS_NZ

val ABS_INV = store_thm("ABS_INV",
  “!x. ~(x = 0) ==> (abs(inv x) = inv(abs(x)))”,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[abs, REAL_LE] THEN
  REWRITE_TAC[num_CONV “1:num”, GSYM NOT_LESS, NOT_LESS_0]);

Theorem ABS_ABS[simp]:
  !x. abs(abs(x)) = abs(x)
Proof
  GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV  [abs] THEN
  REWRITE_TAC[ABS_POS]
QED

val ABS_LE = store_thm("ABS_LE",
  “!x. x <= abs(x)”,
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_LE_NEGR] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_NOT_LE]);

Theorem ABS_REFL[simp]:
  !x. (abs(x) = x) <=> 0 <= x
Proof
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  ASM_CASES_TAC “0 <= x” THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  REWRITE_TAC[REAL_DOUBLE, REAL_ENTIRE, REAL_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_LE_REFL]
QED

(* |- !n. abs (&n) = &n *)
Theorem ABS_N[simp] = REAL_ABS_NUM

val ABS_BETWEEN = store_thm("ABS_BETWEEN",
  “!x y d. 0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d”,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN REWRITE_TAC[REAL_NEG_SUB] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_SUB_RADD] THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [REAL_ADD_SYM] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN “x < (x + d)” MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “y:real” THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “y:real” THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR],
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN “y < (y + d)” MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC “x:real” THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR]]);

val ABS_BOUND = store_thm("ABS_BOUND",
  “!x y d. abs(x - y) < d ==> y < (x + d)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  ONCE_REWRITE_TAC[GSYM ABS_BETWEEN] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);

val ABS_STILLNZ = store_thm("ABS_STILLNZ",
  “!x y. abs(x - y) < abs(y) ==> ~(x = 0)”,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL]);

val ABS_CASES = store_thm("ABS_CASES",
  “!x. (x = 0) \/ 0 < abs(x)”,
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
  BOOL_CASES_TAC “x = 0” THEN ASM_REWRITE_TAC[]);

val ABS_BETWEEN1 = store_thm("ABS_BETWEEN1",
  “!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z”,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [“x:real”, “y:real”] REAL_LET_TOTAL) THENL
   [ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
    REWRITE_TAC[real_sub, REAL_LT_RADD] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2),
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[]]);

val ABS_SIGN = store_thm("ABS_SIGN",
  “!x y. abs(x - y) < y ==> 0 < x”,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ABS_BOUND) THEN
  REWRITE_TAC[REAL_LT_ADDL]);

val ABS_SIGN2 = store_thm("ABS_SIGN2",
  “!x y. abs(x - y) < ~y ==> x < 0”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(Q.SPECL [‘~x’, ‘~y’] ABS_SIGN) THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEGNEG]);

val ABS_DIV = store_thm("ABS_DIV",
  “!y. ~(y = 0) ==> !x. abs(x / y) = abs(x) / abs(y)”,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[real_div] THEN
  REWRITE_TAC[ABS_MUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]));

(* HOL-Light compatible, use with cautions *)
Theorem REAL_ABS_DIV :
    !x y. abs (x / y) = abs x / abs y
Proof
    rpt GEN_TAC
 >> reverse (Cases_on ‘y = 0’)
 >- (MATCH_MP_TAC ABS_DIV >> ASM_REWRITE_TAC [])
 >> POP_ASSUM (fn th => REWRITE_TAC [th, ABS_0, real_div, REAL_INV_0, REAL_MUL_RZERO])
QED

val ABS_CIRCLE = store_thm("ABS_CIRCLE",
  “!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “abs(x) + abs(h)” THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC “abs(x)” REAL_LE_REFL)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD2) THEN
  REWRITE_TAC[REAL_SUB_ADD2]);

val REAL_SUB_ABS = store_thm("REAL_SUB_ABS",
  “!x y. (abs(x) - abs(y)) <= abs(x - y)”,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “(abs(x - y) + abs(y)) - abs(y)” THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[real_sub] THEN REWRITE_TAC[REAL_LE_RADD] THEN
    SUBST1_TAC(SYM(SPECL [“x:real”, “y:real”] REAL_SUB_ADD)) THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)  [REAL_SUB_ADD] THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE,
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_ADD_SUB, REAL_LE_REFL]]);

val ABS_SUB_ABS = store_thm("ABS_SUB_ABS",
  “!x y. abs(abs(x) - abs(y)) <= abs(x - y)”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)  [abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_SUB_ABS] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  REWRITE_TAC[REAL_SUB_ABS]);

val ABS_BETWEEN2 = store_thm("ABS_BETWEEN2",
  “!x0 x y0 y.
        x0 < y0 /\
        abs(x - x0) < (y0 - x0) / &2 /\
        abs(y - y0) < (y0 - x0) / &2
        ==> x < y”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN “x < y0 /\ x0 < y” STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [“x0:real”, “x:real”,
                    “y0 - x0”] ABS_BOUND) THEN
      REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[ABS_SUB] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC “(y0 - x0) / &2” THEN
      ASM_REWRITE_TAC[REAL_LT_HALF2] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT],
      GEN_REWR_TAC I  [TAUT_CONV “a = ~~a:bool”] THEN
      PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
       “(y0 + ~x0) + (x0 + ~y) = (~x0 + x0) + (y0 + ~y)”) THEN
      REWRITE_TAC[GSYM real_sub, REAL_ADD_LINV, REAL_ADD_LID] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [“y0 - x0”,
                    “x0 - y”] REAL_LE_ADDR) THEN
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN “~(y0 <= y)” ASSUME_TAC THENL
       [REWRITE_TAC[REAL_NOT_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “y0 - x0” THEN
        ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_SUB_LT], ALL_TAC] THEN
      UNDISCH_TAC “abs(y - y0) < (y0 - x0) / &2” THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN DISCH_TAC THEN
      SUBGOAL_THEN “(y0 - x0) < (y0 - x0) / &2”
                   MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC “y0 - y” THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[REAL_LT_HALF2] THEN ASM_REWRITE_TAC[REAL_SUB_LT]],
    ALL_TAC] THEN
  GEN_REWR_TAC I  [TAUT_CONV “a = ~~a:bool”] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN “abs(x0 - y) < (y0 - x0) / &2” ASSUME_TAC
  THENL
   [REWRITE_TAC[abs, REAL_SUB_LE] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “x - x0” THEN
    REWRITE_TAC[real_sub, REAL_LE_RADD] THEN
    ASM_REWRITE_TAC[GSYM real_sub] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs(x - x0)” THEN
    ASM_REWRITE_TAC[ABS_LE], ALL_TAC] THEN
  SUBGOAL_THEN
      “abs(y0 - x0) < ((y0 - x0) / &2) + ((y0 - x0) / &2)”
      MP_TAC
  THENL
   [ALL_TAC,
    REWRITE_TAC[REAL_HALF_DOUBLE, REAL_NOT_LT, ABS_LE]] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “abs(y0 - y) + abs(y - x0)” THEN
  CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_LT_ADD2 THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN “y0 - x0 = (y0 - y) + (y - x0)” SUBST1_TAC THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN REAL_ARITH_TAC);

val ABS_BOUNDS = store_thm("ABS_BOUNDS",
  “!x k. abs(x) <= k <=> ~k <= x /\ x <= k”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG] THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[TAUT_CONV “(a <=> b /\ a) <=> a ==> b”] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[REAL_LE_NEGL],
    REWRITE_TAC[TAUT_CONV “(a <=> a /\ b) <=> a ==> b”] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC ‘-x’ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_NEGR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE]]);

Theorem ABS_BOUNDS_LT :
    !(x :real) k. abs(x) < k <=> -k < x /\ x < k
Proof
    RW_TAC std_ss [abs]
 >| [ (* goal 1 (of 2) *)
      EQ_TAC >> RW_TAC std_ss [] \\
      MATCH_MP_TAC REAL_LTE_TRANS \\
      Q.EXISTS_TAC ‘-x’ \\
      RW_TAC std_ss [REAL_LT_NEG, REAL_LE_NEGL],
      (* goal 2 (of 2) *)
      FULL_SIMP_TAC std_ss [REAL_NOT_LE] \\
     ‘-x < k <=> -k < x’ by METIS_TAC [REAL_LT_NEG, REAL_NEGNEG] \\
      EQ_TAC >> RW_TAC std_ss [] \\
     ‘-k < 0’ by PROVE_TAC [REAL_LT_TRANS] \\
     ‘0 < k’ by METIS_TAC [REAL_LT_NEG, REAL_NEGNEG, REAL_NEG_0] \\
      MATCH_MP_TAC REAL_LT_TRANS \\
      Q.EXISTS_TAC ‘0’ >> ASM_REWRITE_TAC [] ]
QED

(*---------------------------------------------------------------------------*)
(* Define integer powers                                                     *)
(*---------------------------------------------------------------------------*)

(* |- (!x. x pow 0 = 1) /\ !x n. x pow SUC n = x * x pow n *)
Theorem pow = real_pow

(* from arithmeticTheory.EXP *)
val _ = overload_on (UnicodeChars.sup_2, “\x. x pow 2”);
val _ = overload_on (UnicodeChars.sup_3, “\x. x pow 3”);

Theorem REAL_POW : (* from examples/miller *)
    !m n. &m pow n = &(m EXP n)
Proof
    REWRITE_TAC [REAL_OF_NUM_POW]
QED

Theorem pow0[simp] = CONJUNCT1 pow;

val POW_0 = store_thm("POW_0",
  “!n. 0 pow (SUC n) = 0”,
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_MUL_LZERO]);

val POW_NZ = store_thm("POW_NZ",
  “!c n. ~(c = 0) ==> ~(c pow n = 0)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(“n:num”,“n:num”) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[pow, REAL_10, REAL_ENTIRE]);

val POW_INV = store_thm("POW_INV",
  “!c. ~(c = 0) ==> !n. (inv(c pow n) = (inv c) pow n)”,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[pow, REAL_INV1] THEN
  MP_TAC(SPECL [“c:real”, “c pow n”] REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN “~(c pow n = 0)” ASSUME_TAC THENL
   [MATCH_MP_TAC POW_NZ THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[]);

val POW_ABS = store_thm("POW_ABS",
  “!c n. abs(c) pow n = abs(c pow n)”,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, ABS_1, ABS_MUL]);

val POW_PLUS1 = store_thm("POW_PLUS1",
  “!e. 0 < e ==> !n. (&1 + (&n * e)) <= (&1 + e) pow n”,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “(&1 + e) * (&1 + (&n * e))” THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LDISTRIB, REAL_RDISTRIB, REAL, REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_ADD_ASSOC, REAL_LE_ADDR] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
    SUBGOAL_THEN “0 < (&1 + e)”
      (fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]) THEN
    GEN_REWR_TAC LAND_CONV  [GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT] THEN REWRITE_TAC[num_CONV “1:num”, LESS_0]]);

val POW_ADD = store_thm("POW_ADD",
  “!c m n. c pow (m + n) = (c pow m) * (c pow n)”,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, ADD_CLAUSES, REAL_MUL_RID] THEN
  CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)));

Theorem POW_1[simp]:
  !x. x pow 1 = x
Proof
  REWRITE_TAC[ONE, pow] >> simp[]
QED

(* |- !x. x pow 2 = x * x *)
val POW_2 = save_thm("POW_2", REAL_POW_2);

Theorem POW_ONE[simp]:
 !n. &1 pow n = &1
Proof
  Induct THEN ASM_REWRITE_TAC[pow, REAL_MUL_LID]
QED

val POW_POS = store_thm("POW_POS",
  “!x. 0 <= x ==> !n. 0 <= (x pow n)”,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_LE_01] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);

val POW_LE = store_thm("POW_LE",
  “!n x y. 0 <= x /\ x <= y ==> (x pow n) <= (y pow n)”,
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LE_REFL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

Theorem POW_M1[simp]:
  !n. abs(~1 pow n) = 1
Proof
  INDUCT_TAC THEN REWRITE_TAC[pow, ABS_NEG, ABS_1] THEN
  ASM_REWRITE_TAC[ABS_MUL, ABS_NEG, ABS_1, REAL_MUL_LID]
QED

val POW_MUL = store_thm("POW_MUL",
  “!n x y. (x * y) pow n = (x pow n) * (y pow n)”,
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_MUL_LID] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)));

val REAL_LE_POW2 = store_thm("REAL_LE_POW2",
  “!x. 0 <= x pow 2”,
  GEN_TAC THEN REWRITE_TAC[POW_2, REAL_LE_SQUARE]);

Theorem ABS_POW2[simp]:
  !x. abs(x pow 2) = x pow 2
Proof
  GEN_TAC THEN REWRITE_TAC[ABS_REFL, REAL_LE_POW2]
QED

Theorem REAL_POW2_ABS[simp]:
  !x. abs(x) pow 2 = x pow 2
Proof
  GEN_TAC THEN REWRITE_TAC[POW_2, POW_MUL] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  REWRITE_TAC[GSYM POW_2, ABS_POW2]
QED

val REAL_LE1_POW2 = store_thm("REAL_LE1_POW2",
  “!x. &1 <= x ==> &1 <= (x pow 2)”,
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01]);

val REAL_LT1_POW2 = store_thm("REAL_LT1_POW2",
  “!x. &1 < x ==> &1 < (x pow 2)”,
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01]);

val POW_POS_LT = store_thm("POW_POS_LT",
  “!x n. 0 < x ==> 0 < (x pow (SUC n))”,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[],
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC POW_NZ THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[]]);

val POW_2_LE1 = store_thm("POW_2_LE1",
  “!n. &1 <= &2 pow n”,
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LE_REFL] THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE] THEN
  REWRITE_TAC[ZERO_LESS_EQ, num_CONV “2:num”, LESS_EQ_SUC_REFL]);

val POW_2_LT = store_thm("POW_2_LT",
  “!n. &n < &2 pow n”,
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LT_01] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, GSYM REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[POW_2_LE1]);

Theorem POW_MINUS1[simp]:
  !n. ~1 pow (2 * n) = 1
Proof
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES, pow] THEN
  REWRITE_TAC(map num_CONV [Term`2:num`,Term`1:num`] @ [ADD_CLAUSES]) THEN
  REWRITE_TAC[pow] THEN
  REWRITE_TAC[SYM(num_CONV “2:num”), SYM(num_CONV “1:num”)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_NEGNEG]
QED

Theorem POW_MINUS1_ODD:    !n. ~1 pow (2 * n + 1) = ~1
Proof simp[POW_ADD]
QED

Theorem NEGATED_POW[simp]:
  ((-x) pow NUMERAL (BIT1 n) = -(x pow NUMERAL (BIT1 n))) /\
  ((-x) pow NUMERAL (BIT2 n) = x pow NUMERAL (BIT2 n))
Proof
  reverse conj_tac >> ONCE_REWRITE_TAC [REAL_NEG_MINUS1] >>
  REWRITE_TAC [POW_MUL]
  >- (‘NUMERAL (BIT2 n) = 2 * (n + 1)’ suffices_by
        (disch_then SUBST_ALL_TAC >> simp[]) >>
      CONV_TAC (LAND_CONV (REWRITE_CONV [NUMERAL_DEF, BIT2])) >>
      simp[]) >>
  ‘NUMERAL (BIT1 n) = 2 * n + 1’ suffices_by
     (disch_then SUBST_ALL_TAC >> simp[POW_MINUS1_ODD]) >>
  CONV_TAC (LAND_CONV (REWRITE_CONV [NUMERAL_DEF, BIT1])) >>
  simp[]
QED

val POW_LT = store_thm("POW_LT",
  “!n x y. 0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))”,
  REPEAT STRIP_TAC THEN SPEC_TAC(“n:num”,“n:num”)
   THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[pow, REAL_MUL_RID],
    ONCE_REWRITE_TAC[pow] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[]]);

val REAL_POW_LT = store_thm("REAL_POW_LT",
 Term`!x n. 0 < x ==> 0 < (x pow n)`,
  REPEAT STRIP_TAC THEN SPEC_TAC(Term`n:num`,Term`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

Theorem REAL_POW_LE_1 :
    !(n:num) (x:real). (&1:real) <= x ==> (&1:real) <= x pow n
Proof
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pow, REAL_LE_REFL],
    GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [pow] THEN
    GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]
QED

Theorem REAL_POW_1_LE :
    !n x:real. &0 <= x /\ x <= &1 ==> x pow n <= &1
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [``n:num``, ``x:real``, ``&1:real``] POW_LE) THEN
  ASM_REWRITE_TAC[POW_ONE]
QED

val POW_EQ = store_thm("POW_EQ",
  “!n x y. 0 <= x /\ 0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)”,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC “x pow (SUC n) = y pow (SUC n)” THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THENL
   [ALL_TAC, CONV_TAC(RAND_CONV SYM_CONV)] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  MATCH_MP_TAC POW_LT THEN ASM_REWRITE_TAC[]);

val POW_ZERO = store_thm("POW_ZERO",
  “!n x. (x pow n = 0) ==> (x = 0)”,
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[pow] THEN
  REWRITE_TAC[REAL_10, REAL_ENTIRE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

Theorem REAL_POW_EQ_0 :
   !x n. (x pow n = &0) <=> (x = &0) /\ ~(n = 0)
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_SUC, real_pow, REAL_ENTIRE] THENL
  [ REAL_ARITH_TAC, TAUT_TAC ]
QED

val POW_ZERO_EQ = store_thm("POW_ZERO_EQ",
  “!n x. (x pow (SUC n) = 0) <=> (x = 0)”,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POW_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[POW_0]);

val REAL_POW_LT2 = store_thm("REAL_POW_LT2",
 Term `!n x y. ~(n = 0) /\ 0 <= x /\ x < y ==> x pow n < y pow n`,
 INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, pow] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC (Term `n = 0:num`) THEN ASM_REWRITE_TAC[pow, REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

Theorem REAL_POW_INV :
    !x n. (inv x) pow n = inv(x pow n)
Proof
  Induct_on `n` THEN REWRITE_TAC [pow] THENL
  [REWRITE_TAC [REAL_INV1],
   GEN_TAC THEN Cases_on `x = 0r` THENL
   [POP_ASSUM SUBST_ALL_TAC
     THEN REWRITE_TAC [REAL_INV_0,REAL_MUL_LZERO],
    `~(x pow n = 0)` by PROVE_TAC [POW_NZ] THEN
    IMP_RES_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC []]]
QED

Theorem REAL_POW_DIV :
    !x y n. (x / y) pow n = (x pow n) / (y pow n)
Proof
  REWRITE_TAC[real_div, POW_MUL, REAL_POW_INV]
QED

Theorem REAL_POW_ADD :
    !x m n. x pow (m + n) = x pow m * x pow n
Proof
  Induct_on `m` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES, pow, REAL_MUL_LID, REAL_MUL_ASSOC]
QED

Theorem REAL_POW_MONO :
    !m n x. &1 <= x /\ m <= n ==> x pow m <= x pow n
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “d:num” SUBST1_TAC) THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL_IMP THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “&1” THEN
    RW_TAC arith_ss [REAL_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]]
QED

Theorem REAL_POW_MONO_LT :
    !m n x. &1 < x /\ m < n ==> x pow m < x pow n
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[LT_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL_IMP THEN CONJ_TAC THENL
   [SPEC_TAC(Term`d:num`,Term`d:num`) THEN
    INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [ASM_REWRITE_TAC[pow, REAL_MUL_RID], ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
    MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (Term`&1`) THEN
    ASM_REWRITE_TAC[REAL_LT,prim_recTheory.LESS_0, ONE]]
QED

Theorem REAL_POW_POW :
    !x m n. (x pow m) pow n = x pow (m * n)
Proof
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, MULT_CLAUSES, POW_ADD]
QED

(*---------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set        *)
(*---------------------------------------------------------------------------*)

(* cf. REAL_SUP_ALLPOS *)
val REAL_SUP_SOMEPOS = store_thm("REAL_SUP_SOMEPOS",
  “!P. (?x. P x /\ 0 < x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) <=> y < s)”,
  let val lemma = TAUT_CONV “a /\ b ==> b” in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC “\x. P x /\ 0 < x” REAL_SUP_ALLPOS) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[lemma] THEN
  SUBGOAL_THEN
  “?z. !x. P x /\ 0 < x ==> x < z” (SUBST1_TAC o EQT_INTRO)
  THENL
   [POP_ASSUM(X_CHOOSE_TAC “z:real” o CONJUNCT2) THEN
   EXISTS_TAC “z:real” THEN
    GEN_TAC THEN
    DISCH_THEN(curry op THEN (FIRST_ASSUM MATCH_MP_TAC) o ASSUME_TAC) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN “s:real” MP_TAC) THEN
  DISCH_THEN(curry op THEN (EXISTS_TAC “s:real” THEN GEN_TAC) o
                   (SUBST1_TAC o SYM o SPEC “y:real”)) THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPECL [“y:real”, “0”]
                                             REAL_LT_TOTAL)
    THENL
     [DISCH_THEN SUBST1_TAC THEN DISCH_THEN(X_CHOOSE_TAC “x:real”) THEN
      EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[],
      POP_ASSUM(X_CHOOSE_TAC “x:real” o CONJUNCT1) THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o CONJ th o CONJUNCT2)) THEN
      DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
      DISCH_THEN(K ALL_TAC) THEN
      EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[],
      POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_TAC “x:real”) THEN
      EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC “y:real” THEN ASM_REWRITE_TAC[]],
    DISCH_THEN(X_CHOOSE_TAC “x:real”) THEN
    EXISTS_TAC “x:real” THEN
    ASM_REWRITE_TAC[]] end);

val SUP_LEMMA1 = store_thm("SUP_LEMMA1",
  “!P s d. (!y. (?x. (\x. P(x + d)) x /\ y < x) <=> y < s)
     ==> (!y. (?x. P x /\ y < x) <=> y < (s + d))”,
  REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  POP_ASSUM(MP_TAC o SPEC “y + ~d”) THEN
  REWRITE_TAC[REAL_LT_ADDNEG2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC “x:real”) THENL
   [EXISTS_TAC “x + ~d” THEN
    ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID],
    EXISTS_TAC “x + d” THEN POP_ASSUM ACCEPT_TAC]);

Theorem SUP_LEMMA2:
  !P. (?x. P x) ==> ?d. ?x. (\x. P(x + d)) x /\ 0 < x
Proof
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC “x:real”) THEN BETA_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPECL [“x:real”, “0”]
                                           REAL_LT_TOTAL)
  THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [“~1”, “1”] THEN
    ASM_REWRITE_TAC[REAL_ADD_RINV, REAL_LT_01],
    DISCH_TAC THEN
    qexistsl_tac [‘x + x’, ‘~x’] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID, REAL_NEG_GT0],
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [“0”, “x:real”] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID]]
QED

val SUP_LEMMA3 = store_thm("SUP_LEMMA3",
  “!d. (?z. !x. P x ==> x < z) ==>
                (?z. !x. (\x. P(x + d)) x ==> x < z)”,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC “z:real”) THEN
  EXISTS_TAC “z + ~d” THEN GEN_TAC THEN BETA_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[REAL_LT_ADDNEG]);

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)

val REAL_SUP_EXISTS = store_thm("REAL_SUP_EXISTS",
  “!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) <=> y < s)”,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC “d:real” o MATCH_MP SUP_LEMMA2) MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SPEC “d:real” SUP_LEMMA3)) THEN
  POP_ASSUM(fn th => DISCH_THEN(MP_TAC o MATCH_MP REAL_SUP_SOMEPOS o CONJ th))
  THEN
  DISCH_THEN(X_CHOOSE_TAC “s:real”) THEN
  EXISTS_TAC “s + d” THEN
  MATCH_MP_TAC SUP_LEMMA1 THEN POP_ASSUM ACCEPT_TAC);

Theorem REAL_SUP_EXISTS' :
    !P. P <> {} /\ (?z. !x. x IN P ==> x < z) ==>
        (?s. !y. (?x. x IN P /\ y < x) <=> y < s)
Proof
    REWRITE_TAC [IN_APP, REAL_SUP_EXISTS, GSYM MEMBER_NOT_EMPTY]
QED

val sup = new_definition("sup",
   “sup P = @s. !y. (?x. P x /\ y < x) <=> y < s”);

val REAL_SUP = store_thm("REAL_SUP",
  “!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) <=> y < sup P)”,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SELECT_RULE o MATCH_MP REAL_SUP_EXISTS)
  THEN REWRITE_TAC[GSYM sup]);

Theorem REAL_SUP' :
    !P. P <> {} /\ (?z. !x. x IN P ==> x < z) ==>
        (!y. (?x. x IN P /\ y < x) <=> y < sup P)
Proof
    REWRITE_TAC [IN_APP, REAL_SUP, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_SUP_UBOUND = store_thm("REAL_SUP_UBOUND",
  “!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)”,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC “sup P” o MATCH_MP REAL_SUP) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  X_GEN_TAC “x:real” THEN RULE_ASSUM_TAC(SPEC “x:real”) THEN
  DISCH_THEN (SUBST_ALL_TAC o EQT_INTRO) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_NOT_LT]);

Theorem REAL_SUP_UBOUND' :
    !P. P <> {} /\ (?z. !x. x IN P ==> x < z) ==>
        (!y. y IN P ==> y <= sup P)
Proof
    REWRITE_TAC [IN_APP, REAL_SUP_UBOUND, GSYM MEMBER_NOT_EMPTY]
QED

val SETOK_LE_LT = store_thm("SETOK_LE_LT",
  “!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) <=>
       (?x. P x) /\ (?z. !x. P x ==> x < z)”,
  GEN_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC “z:real”)
  THENL (map EXISTS_TAC [“z + &1”, “z:real”]) THEN
  GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REAL_LT_ADD1, REAL_LT_IMP_LE]);

val REAL_SUP_LE = store_thm("REAL_SUP_LE",
  “!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) <=> y < sup P)”,
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT, REAL_SUP]);

Theorem REAL_SUP_LE' :
    !P. P <> {} /\ (?z. !x. x IN P ==> x <= z) ==>
        (!y. (?x. x IN P /\ y < x) <=> y < sup P)
Proof
    REWRITE_TAC [IN_APP, REAL_SUP_LE, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_SUP_UBOUND_LE = store_thm("REAL_SUP_UBOUND_LE",
  “!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)”,
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT, REAL_SUP_UBOUND]);

Theorem REAL_SUP_UBOUND_LE' :
    !P. P <> {} /\ (?z. !x. x IN P ==> x <= z) ==>
        (!y. y IN P ==> y <= sup P)
Proof
    REWRITE_TAC [IN_APP, REAL_SUP_UBOUND_LE, GSYM MEMBER_NOT_EMPTY]
QED

(*---------------------------------------------------------------------------*)
(* Prove the Archimedean property                                            *)
(*---------------------------------------------------------------------------*)

val REAL_ARCH = store_thm("REAL_ARCH",
  “!x. 0 < x ==> !y. ?n. y < &n * x”,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV “a = ~(~a):bool”] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC “\z. ?n. z = &n * x” REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN(fn th => REWRITE_TAC[th]) o funpow 2 (fst o dest_imp) o snd)
  THENL [CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [“&n * x”, “n:num”] THEN REFL_TAC,
    EXISTS_TAC “y:real” THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC “sup(\z. ?n. z = &n * x) - x”)
  THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN “z:real” MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC “n:num”) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWR_TAC (funpow 3 RAND_CONV) [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC “sup(\z. ?n. z = &n * x)”) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN EXISTS_TAC “(&n + &1) * x”
  THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC “n + 1:num” THEN
  REWRITE_TAC[REAL_ADD]);

val REAL_ARCH_LEAST = store_thm("REAL_ARCH_LEAST",
  “!y. 0 < y
          ==> !x. 0 <= x
          ==> ?n. (&n * y) <= x
                  /\ x < (&(SUC n) * y)”,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_ARCH) THEN
  GEN_TAC THEN POP_ASSUM(ASSUME_TAC o SPEC “x:real”) THEN
  POP_ASSUM(X_CHOOSE_THEN “n:num” MP_TAC o CONV_RULE EXISTS_LEAST_CONV)
  THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SPEC “PRE n”)) THEN
  DISCH_TAC THEN EXISTS_TAC “PRE n” THEN
  SUBGOAL_THEN “SUC(PRE n) = n” ASSUME_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC (CHOOSE_THEN SUBST_ALL_TAC)
        (SPEC “n:num” num_CASES) THENL
     [UNDISCH_TAC “x < 0 * y” THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO, GSYM REAL_NOT_LE],
      REWRITE_TAC[PRE]],
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PRE, LESS_SUC_REFL]]);

Theorem SIMP_REAL_ARCH :
    !x:real. ?n. x <= &n
Proof
    REWRITE_TAC [REAL_LE_LT]
 >> FULL_SIMP_TAC std_ss [EXISTS_OR_THM]
 >> RW_TAC std_ss []
 >> DISJ1_TAC
 >> MP_TAC (Q.SPEC `1` REAL_ARCH)
 >> REWRITE_TAC [REAL_LT_01, REAL_MUL_RID]
 >> RW_TAC std_ss []
QED

Theorem REAL_BIGNUM :
    !r : real. ?n : num. r < &n
Proof
   GEN_TAC
   THEN MP_TAC (Q.SPEC `1` REAL_ARCH)
   THEN REWRITE_TAC [REAL_LT_01, REAL_MUL_RID]
   THEN PROVE_TAC []
QED

Theorem REAL_ARCH_INV :
    !e. &0 < e <=> ?n. ~(n = 0) /\ &0:real < inv(&n) /\ inv(&n) < e:real
Proof
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC[REAL_LT_TRANS]] THEN
  DISCH_TAC THEN MP_TAC(SPEC ``inv(e:real)`` REAL_BIGNUM) THEN
  STRIP_TAC THEN EXISTS_TAC ``n:num`` THEN
  ASM_MESON_TAC[REAL_LT_INV, REAL_INV_INV, REAL_LT_INV_EQ, REAL_LT_TRANS,
                REAL_LT_ANTISYM]
QED

(*---------------------------------------------------------------------------*)
(* Now define finite sums; NB: sum(m,n) f = f(m) + f(m+1) + ... + f(m+n-1)   *)
(*---------------------------------------------------------------------------*)

val sum = Lib.with_flag (boolLib.def_suffix, "") Define`
   (sum (n,0) f = 0) /\
   (sum (n,SUC m) f = sum (n,m) f + f (n + m): real)`

(*---------------------------------------------------------------------------*)
(* Useful manipulative theorems for sums                                     *)
(*---------------------------------------------------------------------------*)

val SUM_TWO = store_thm("SUM_TWO",
  “!f n p. sum(0,n) f + sum(n,p) f = sum(0,n + p) f”,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_ADD_RID, ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_ADD_ASSOC]);

val SUM_DIFF = store_thm("SUM_DIFF",
  “!f m n. sum(m,n) f = sum(0,m + n) f - sum(0,m) f”,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN MATCH_ACCEPT_TAC SUM_TWO);

val ABS_SUM = store_thm("ABS_SUM",
  “!f m n. abs(sum(m,n) f) <= sum(m,n) (\n. abs(f n))”,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, ABS_0, REAL_LE_REFL] THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “abs(sum(m,n) f) + abs(f(m + n))” THEN
  ASM_REWRITE_TAC[ABS_TRIANGLE, REAL_LE_RADD]);

val SUM_LE = store_thm("SUM_LE",
  “!f g m n. (!r. m <= r /\ r < (n + m) ==> f(r) <= g(r))
        ==> (sum(m,n) f <= sum(m,n) g)”,
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[sum, REAL_LE_REFL] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC “n + m:num”,
    GEN_REWR_TAC (RAND_CONV o RAND_CONV)  [ADD_SYM]] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES, LESS_EQ_ADD, LESS_SUC_REFL]);

(* moved here from seqTheory *)
Theorem SUM_LT :
    !f g m n.
       (!r. m <= r /\ r < n + m ==> f r < g r) /\ 0 < n ==>
       sum (m,n) f < sum (m,n) g
Proof
    RW_TAC std_ss []
 >> POP_ASSUM MP_TAC
 >> Cases_on `n` >- RW_TAC arith_ss []
 >> RW_TAC arith_ss []
 >> Induct_on `n'` >- RW_TAC arith_ss [sum, REAL_ADD_LID]
 >> ONCE_REWRITE_TAC [sum]
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_LT_ADD2
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM `a ==> b` MATCH_MP_TAC >> RW_TAC arith_ss [])
 >> RW_TAC arith_ss []
QED

(* moved here from seqTheory *)
Theorem SUM_PICK :
    !n k x. sum (0, n) (\m. if m = k then x else 0) = if k < n then x else 0
Proof
    Induct >- RW_TAC arith_ss [sum]
 >> RW_TAC arith_ss [sum, REAL_ADD_RID, REAL_ADD_LID]
 >> Suff `F` >- PROVE_TAC []
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> DECIDE_TAC
QED

val SUM_EQ = store_thm("SUM_EQ",
  “!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (sum(m,n) f = sum(m,n) g)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN GEN_TAC THEN
  DISCH_THEN(fn th => MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN REFL_TAC);

val SUM_POS = store_thm("SUM_POS",
  “!f. (!n. 0 <= f(n)) ==> !m n. 0 <= sum(m,n) f”,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[]);

val SUM_POS_GEN = store_thm("SUM_POS_GEN",
  “!f m. (!n. m <= n ==> 0 <= f(n)) ==>
        !n. 0 <= sum(m,n) f”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_ACCEPT_TAC LESS_EQ_ADD);

val SUM_ABS = store_thm("SUM_ABS",
  “!f m n. abs(sum(m,n) (\m. abs(f m))) = sum(m,n) (\m. abs(f m))”,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[ABS_REFL] THEN
  GEN_TAC THEN MATCH_MP_TAC SUM_POS THEN BETA_TAC THEN
  REWRITE_TAC[ABS_POS]);

val SUM_ABS_LE = store_thm("SUM_ABS_LE",
  “!f m n. abs(sum(m,n) f) <= sum(m,n)(\n. abs(f n))”,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, ABS_0, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “abs(sum(m,n) f) + abs(f(m + n))” THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_RADD]);

val SUM_ZERO = store_thm("SUM_ZERO",
  “!f N. (!n. n >= N ==> (f(n) = 0))
              ==>
            (!m n. m >= N ==> (sum(m,n) f = 0))”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [“m:num”, “n:num”] THEN
  REWRITE_TAC[GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN “d:num” SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD)
  THEN
  SPEC_TAC(“n:num”,“n:num”) THEN INDUCT_TAC THEN REWRITE_TAC[sum]
  THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GREATER_EQ, GSYM ADD_ASSOC, LESS_EQ_ADD]);

val SUM_ADD = store_thm("SUM_ADD",
  “!f g m n.
      sum(m,n) (\n. f(n) + g(n))
      =
      sum(m,n) f + sum(m,n) g”,
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_ADD_LID] THEN BETA_TAC THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val SUM_CMUL = store_thm("SUM_CMUL",
  “!f c m n. sum(m,n) (\n. c * f(n)) = c * sum(m,n) f”,
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_MUL_RZERO] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_LDISTRIB]);

val SUM_NEG = store_thm("SUM_NEG",
  “!f n d. sum(n,d) (\n. ~(f n)) = ~(sum(n,d) f)”,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_NEG_0] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_NEG_ADD]);

val SUM_SUB = store_thm("SUM_SUB",
  “!f g m n.
      sum(m,n)(\n. (f n) - (g n))
    = sum(m,n) f - sum(m,n) g”,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, GSYM SUM_NEG, GSYM SUM_ADD] THEN
  BETA_TAC THEN REFL_TAC);

val SUM_SUBST = store_thm("SUM_SUBST",
  “!f g m n. (!p. m <= p /\ p < (m + n) ==> (f p = g p))
        ==> (sum(m,n) f = sum(m,n) g)”,
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN BINOP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC THEN
    MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[LESS_EQ_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    MATCH_MP_TAC LESS_MONO_ADD THEN REWRITE_TAC[LESS_SUC_REFL]]);

val SUM_NSUB = store_thm("SUM_NSUB",
  “!n f c.
      sum(0,n) f - (&n * c)
        =
      sum(0,n)(\p. f(p) - c)”,
  INDUCT_TAC THEN REWRITE_TAC[sum, REAL_MUL_LZERO, REAL_SUB_REFL] THEN
  REWRITE_TAC[ADD_CLAUSES, REAL, REAL_RDISTRIB] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN POP_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_MUL_LID] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val SUM_BOUND = store_thm("SUM_BOUND",
  “!f k m n. (!p. m <= p /\ p < (m + n) ==> (f(p) <= k))
        ==> (sum(m,n) f <= (&n * k))”,
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN
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

val SUM_GROUP = store_thm("SUM_GROUP",
  “!n k f. sum(0,n)(\m. sum(m * k,k) f) = sum(0,n * k) f”,
  INDUCT_TAC THEN REWRITE_TAC[sum, MULT_CLAUSES] THEN
  REPEAT GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES, SUM_TWO]);

val SUM_1 = store_thm("SUM_1",
  “!f n. sum(n,1) f = f(n)”,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV “1:num”, sum, ADD_CLAUSES, REAL_ADD_LID]);

val SUM_2 = store_thm("SUM_2",
  “!f n. sum(n,2) f = f(n) + f(n + 1)”,
  REPEAT GEN_TAC THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[sum, ADD_CLAUSES, REAL_ADD_LID]);

val SUM_OFFSET = store_thm("SUM_OFFSET",
  “!f n k.
      sum(0,n)(\m. f(m + k))
    = sum(0,n + k) f - sum(0,k) f”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[GSYM SUM_TWO, REAL_ADD_SUB] THEN
  SPEC_TAC(“n:num”,“n:num”) THEN
  INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC ADD_SYM);

val SUM_REINDEX = store_thm("SUM_REINDEX",
  “!f m k n. sum(m + k,n) f = sum(m,n)(\r. f(r + k))”,
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  ASM_REWRITE_TAC[REAL_EQ_LADD] THEN BETA_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(AC_CONV(ADD_ASSOC,ADD_SYM)));

val SUM_0 = store_thm("SUM_0",
  “!m n. sum(m,n)(\r. 0) = 0”,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID]);

(* moved here from integralTheory *)
val SUM_EQ_0 = store_thm("SUM_EQ_0",
  ``(!r. m <= r /\ r < m + n ==> (f(r) = &0)) ==> (sum(m,n) f = &0)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``sum(m,n) (\r. &0)`` THEN
  CONJ_TAC THENL [ALL_TAC, REWRITE_TAC[SUM_0]] THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);

val SUM_PERMUTE_0 = store_thm("SUM_PERMUTE_0",
  “!n p. (!y. y < n ==> ?!x. x < n /\ (p(x) = y))
        ==> !f. sum(0,n)(\n. f(p n)) = sum(0,n) f”,
  INDUCT_TAC THEN GEN_TAC THEN TRY(REWRITE_TAC[sum] THEN NO_TAC) THEN
  DISCH_TAC THEN GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC “n:num”) THEN
  REWRITE_TAC[LESS_SUC_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “k:num” STRIP_ASSUME_TAC) THEN
  GEN_REWR_TAC RAND_CONV  [sum] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ABBREV_TAC “q:num->num = \r. if r < k then p(r) else p(SUC r)” THEN
  SUBGOAL_THEN “!y:num. y < n ==> ?!x. x < n /\ (q x = y)” MP_TAC
  THENL
   [X_GEN_TAC “y:num” THEN DISCH_TAC THEN
    (MP_TAC o ASSUME) “!y. y<SUC n ==> ?!x. x<SUC n /\ (p x = y)” THEN
    DISCH_THEN(MP_TAC o SPEC “y:num”) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC “n:num” THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL],
      DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MP th))] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN “x:num” STRIP_ASSUME_TAC o CONJUNCT1) THEN
    CONJ_TAC THENL
     [DISJ_CASES_TAC(SPECL [“x:num”, “k:num”] LESS_CASES) THENL
       [EXISTS_TAC “x:num” THEN EXPAND_TAC "q" THEN BETA_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_LT] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC “&k” THEN ASM_REWRITE_TAC[REAL_LE, REAL_LT] THEN
        UNDISCH_TAC “k < SUC n” THEN
        REWRITE_TAC[LESS_EQ, LESS_EQ_MONO],
        MP_TAC(ASSUME “k <= x:num”) THEN REWRITE_TAC[LESS_OR_EQ] THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
         [EXISTS_TAC “x - 1:num” THEN EXPAND_TAC "q" THEN BETA_TAC THEN
          UNDISCH_TAC “k < x:num” THEN
          DISCH_THEN(X_CHOOSE_THEN “d:num” MP_TAC o MATCH_MP LESS_ADD_1)
          THEN
          REWRITE_TAC[GSYM ADD1, ADD_CLAUSES] THEN
          DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_EQ]) THEN
          ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
          UNDISCH_TAC “(k + d) < k:num” THEN
          REWRITE_TAC[LESS_EQ] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[GSYM NOT_LESS, REWRITE_RULE[ADD_CLAUSES] LESS_ADD_SUC],
          SUBST_ALL_TAC(ASSUME “(p:num->num) x = n”) THEN
          UNDISCH_TAC “y < n:num” THEN ASM_REWRITE_TAC[LESS_REFL]]],
      SUBGOAL_THEN
       “!z. q z :num = p(if z < k then z else SUC z)” MP_TAC THENL
       [GEN_TAC THEN EXPAND_TAC "q" THEN BETA_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[],
        DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
      MAP_EVERY X_GEN_TAC [“x1:num”, “x2:num”] THEN STRIP_TAC THEN
      UNDISCH_TAC “!y. y < SUC n ==> ?!x. x < SUC n /\ (p x = y)” THEN
      DISCH_THEN(MP_TAC o SPEC “y:num”) THEN
      REWRITE_TAC[MATCH_MP LESS_SUC (ASSUME “y < n:num”)] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
      DISCH_THEN(MP_TAC
                 o SPECL [“if x1 < (k:num) then x1 else SUC x1”,
                          “if x2 < (k:num) then x2 else SUC x2”]
                 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
       [CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LESS_MONO_EQ] THEN
        MATCH_MP_TAC LESS_SUC THEN ASM_REWRITE_TAC[],
        DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
        REPEAT COND_CASES_TAC THEN REWRITE_TAC[INV_SUC_EQ] THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC “~(x2 < k:num)” THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
          EXISTS_TAC “SUC x2” THEN ASM_REWRITE_TAC[LESS_SUC_REFL],
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
          UNDISCH_TAC “~(x1 < k:num)” THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
          EXISTS_TAC “SUC x1” THEN ASM_REWRITE_TAC[LESS_SUC_REFL]]]],
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC(RAND_CONV o ONCE_DEPTH_CONV)[GSYM th])THEN
    BETA_TAC THEN UNDISCH_TAC “k < SUC n” THEN
    REWRITE_TAC[LESS_EQ, LESS_EQ_MONO] THEN
    DISCH_THEN(X_CHOOSE_TAC “d:num” o MATCH_MP LESS_EQUAL_ADD) THEN
    GEN_REWR_TAC (RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
                     [ASSUME “n = k + d:num”] THEN
    REWRITE_TAC[GSYM SUM_TWO] THEN
    GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME “n = k + d:num”] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUC] THEN
    REWRITE_TAC[GSYM SUM_TWO, sum, ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC “r:num” THEN
      REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
      BETA_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[],
      GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
      REWRITE_TAC[ASSUME “(p:num->num) k = n”, REAL_EQ_LADD] THEN
      REWRITE_TAC[ADD1, SUM_REINDEX] THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC “r:num” THEN BETA_TAC THEN
      REWRITE_TAC[GSYM NOT_LESS] THEN DISCH_TAC THEN
      EXPAND_TAC "q" THEN BETA_TAC THEN ASM_REWRITE_TAC[ADD1]]]);

val SUM_CANCEL = store_thm("SUM_CANCEL",
  “!f n d.
      sum(n,d) (\n. f(SUC n) - f(n))
    = f(n + d) - f(n)”,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, ADD_CLAUSES, REAL_SUB_REFL] THEN
  BETA_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

(* moved here from integralTheory, added missing quantifier ‘m’ *)
Theorem SUM_SPLIT :
    !f m n p. sum(m,n) f + sum(m + n,p) f = sum(m,n + p) f
Proof
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC(LAND_CONV o LAND_CONV) empty_rewrites [SUM_DIFF] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV) empty_rewrites [SUM_DIFF] THEN
  CONV_TAC SYM_CONV THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [SUM_DIFF] THEN
  RW_TAC arith_ss[] THEN
  SUBGOAL_THEN “!a b c. b-a + (c-b)=c-a”
     (fn th => ONCE_REWRITE_TAC[GEN_ALL th])
  >| [ REWRITE_TAC [Once REAL_ADD_COMM, REAL_SUB_TRIANGLE],
       REWRITE_TAC[] ]
QED

(* moved here from integralTheory, added missing quantifier ‘d’ *)
Theorem SUM_DIFFS :
    !d m n. sum(m,n) (\i. d(SUC i) - d(i)) = d(m + n) - d m
Proof
  NTAC 2 GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, ADD_CLAUSES, REAL_SUB_REFL] THEN REWRITE_TAC[sum] THEN
  RW_TAC arith_ss[ETA_AX] THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN“!a b c d. a-b+(c-a) = -b+a+(c-a)”
        (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ASM_SIMP_TAC arith_ss[GSYM REAL_ADD_SYM],
        SUBGOAL_THEN“!a b c d. a+b+(c-b) = a+c”
          (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
         [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
          REWRITE_TAC[REAL_EQ_LADD] THEN
          REWRITE_TAC[REAL_SUB_ADD2], REWRITE_TAC[real_sub] THEN
          GEN_REWR_TAC LAND_CONV [REAL_ADD_COMM] THEN PROVE_TAC[]]]
QED

(* ------------------------------------------------------------------------- *)
(* Theorems to be compatible with hol-light.                                 *)
(* ------------------------------------------------------------------------- *)

(* |- !x y. x * -y = -(x * y) *)
val REAL_MUL_RNEG = save_thm("REAL_MUL_RNEG", REAL_MUL_RNEG);

(* |- !x y. -x * y = -(x * y) *)
val REAL_MUL_LNEG = save_thm("REAL_MUL_LNEG", REAL_MUL_LNEG);

Theorem REAL_LE_LMUL_NEG:
  !x y z. x < 0 ==> (x * y <= x * z <=> z <= y)
Proof
  rpt strip_tac >>
  ‘0 < -x’ by simp[] >>
  Cases_on ‘z <= y’
  >- (‘-x * z <= -x * y’ by simp[REAL_LE_LMUL] >>
      fs[REAL_LE_NEG, REAL_MUL_LNEG]) >>
  fs[REAL_NOT_LE] >>
  ‘-x * y < -x * z’ by simp[REAL_LT_LMUL] >>
  fs[REAL_LT_NEG, REAL_MUL_LNEG] >>
  metis_tac[REAL_LET_ANTISYM]
QED

Theorem REAL_LT_LMUL_NEG:
  !x y z. x < 0 ==> (x * y < x * z <=> z < y)
Proof
  rpt strip_tac >>
  ‘0 < -x’ by simp[] >>
  Cases_on ‘z < y’
  >- (‘-x * z < -x * y’ by simp[REAL_LT_LMUL] >>
      fs[REAL_LT_NEG, REAL_MUL_LNEG]) >>
  ‘y <= z’ by fs[REAL_NOT_LT] >>
  ‘-x * y <= -x * z’ by simp[REAL_LE_LMUL] >>
  fs[REAL_LE_NEG, REAL_MUL_LNEG] >> metis_tac[REAL_LET_ANTISYM]
QED

(* |- !y x. x < y <=> ~(y <= x)

   NOTE: the order of quantifiers is first ‘y’ then ‘x’. Don't "fix".
 *)
val real_lt = save_thm ("real_lt", real_lt);

(* |- !x y z. y <= z ==> x + y <= x + z *)
val REAL_LE_LADD_IMP = save_thm ("REAL_LE_LADD_IMP", REAL_LE_LADD_IMP);

(* |- !x y. -x <= y <=> 0 <= x + y *)
Theorem REAL_LE_LNEG = REAL_LE_LNEG

(* |- !x y. -x <= -y <=> y <= x *)
Theorem REAL_LE_NEG2 = REAL_LE_NEG2

(* |- !x. --x = x *)
Theorem REAL_NEG_NEG = REAL_NEG_NEG

val SIMP_REAL_ARCH_NEG = store_thm (* from extrealTheory *)
  ("SIMP_REAL_ARCH_NEG",
  ``!x:real. ?n. - &n <= x``,
    RW_TAC std_ss []
 >> `?n. -x <= &n` by PROVE_TAC [SIMP_REAL_ARCH]
 >> Q.EXISTS_TAC `n`
 >> PROVE_TAC [REAL_LE_NEG, REAL_NEG_NEG]);

(* |- !x y. x <= -y <=> x + y <= 0 *)
val REAL_LE_RNEG = save_thm ("REAL_LE_RNEG", REAL_LE_RNEG);

val REAL_LT_RNEG = store_thm (* from real_topologyTheory *)
  ("REAL_LT_RNEG",
  ``!x y. x < -y <=> x + y < &0:real``,
    SIMP_TAC std_ss [real_lt, REAL_LE_LNEG, REAL_ADD_ASSOC, REAL_ADD_SYM]);

val REAL_LE_RDIV_EQ = Q.store_thm
("REAL_LE_RDIV_EQ",
 `!x y z. &0 < z ==> (x <= y / z <=> x * z <= y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
    GEN_REWRITE_TAC LAND_CONV empty_rewrites
                   [GSYM(MATCH_MP REAL_LE_RMUL th)]) THEN
  RW_TAC bool_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV,
               REAL_MUL_RID, REAL_POS_NZ]);

val REAL_LE_LDIV_EQ = Q.store_thm
("REAL_LE_LDIV_EQ",
 `!x y z. &0 < z ==> (x / z <= y <=> x <= y * z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
    GEN_REWRITE_TAC LAND_CONV empty_rewrites
             [GSYM(MATCH_MP REAL_LE_RMUL th)]) THEN
  RW_TAC bool_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV,
               REAL_MUL_RID, REAL_POS_NZ]);

val REAL_LT_RDIV_EQ = Q.store_thm
("REAL_LT_RDIV_EQ",
 `!x y z. &0 < z ==> (x < y / z <=> x * z < y)`,
 RW_TAC bool_ss [GSYM REAL_NOT_LE, REAL_LE_LDIV_EQ]);

val REAL_LT_LDIV_EQ = Q.store_thm
("REAL_LT_LDIV_EQ",
 `!x y z. &0 < z ==> (x / z < y <=> x < y * z)`,
  RW_TAC bool_ss [GSYM REAL_NOT_LE, REAL_LE_RDIV_EQ]);

val REAL_EQ_RDIV_EQ = Q.store_thm
("REAL_EQ_RDIV_EQ",
 `!x y z. &0 < z ==> ((x = y / z) <=> (x * z = y))`,
 REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
 RW_TAC bool_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ]);

val REAL_EQ_LDIV_EQ = Q.store_thm
("REAL_EQ_LDIV_EQ",
 `!x y z. &0 < z ==> ((x / z = y) <=> (x = y * z))`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  RW_TAC bool_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ]);

(* !x n. &x pow n = &(x ** n) *)
val REAL_OF_NUM_POW = save_thm ("REAL_OF_NUM_POW", REAL_OF_NUM_POW);

(* |- !z y x. x * (y + z) = x * y + x * z *)
val REAL_ADD_LDISTRIB = save_thm ("REAL_ADD_LDISTRIB", REAL_LDISTRIB);

(* |- !x y z. (x + y) * z = x * z + y * z *)
val REAL_ADD_RDISTRIB = save_thm ("REAL_ADD_RDISTRIB", REAL_RDISTRIB);

(* !m n. &m + &n = &(m + n) *)
val REAL_OF_NUM_ADD = save_thm ("REAL_OF_NUM_ADD", REAL_ADD);

(* |- !m n. &m <= &n <=> m <= n *)
val REAL_OF_NUM_LE = save_thm ("REAL_OF_NUM_LE", REAL_LE);
val REAL_OF_NUM_LT = save_thm ("REAL_OF_NUM_LT", REAL_LT);

(* |- !m n. &m * &n = &(m * n) *)
val REAL_OF_NUM_MUL = save_thm ("REAL_OF_NUM_MUL", REAL_MUL);

val REAL_OF_NUM_SUC = store_thm (
  "REAL_OF_NUM_SUC",
  ``!n. &n + &1 = &(SUC n)``,
  REWRITE_TAC[ADD1, REAL_ADD]);

val REAL_OF_NUM_EQ = save_thm ("REAL_OF_NUM_EQ", REAL_INJ);

val REAL_EQ_MUL_LCANCEL = store_thm (
  "REAL_EQ_MUL_LCANCEL",
  ``!x y z. (x * y = x * z) <=> (x = 0) \/ (y = z)``,
  REWRITE_TAC [REAL_EQ_LMUL]);

val REAL_ABS_0 = save_thm ("REAL_ABS_0", ABS_0);
val _ = export_rewrites ["REAL_ABS_0"]

val REAL_ABS_TRIANGLE = save_thm ("REAL_ABS_TRIANGLE", ABS_TRIANGLE);

val REAL_ABS_MUL = save_thm ("REAL_ABS_MUL", ABS_MUL);

val REAL_ABS_POS = save_thm ("REAL_ABS_POS", ABS_POS);

val REAL_LE_EPSILON = store_thm
  ("REAL_LE_EPSILON",
   ``!x y : real. (!e. 0 < e ==> x <= y + e) ==> x <= y``,
   RW_TAC boolSimps.bool_ss []
   THEN (SUFF_TAC ``~(0r < x - y)``
         THEN1 RW_TAC boolSimps.bool_ss
               [REAL_NOT_LT, REAL_LE_SUB_RADD, REAL_ADD_LID])
   THEN STRIP_TAC
   THEN Q.PAT_X_ASSUM `!e. P e` MP_TAC
   THEN RW_TAC boolSimps.bool_ss []
   THEN (KNOW_TAC ``!a b c : real. ~(a <= b + c) <=> c < a - b``
         THEN1 (RW_TAC boolSimps.bool_ss [REAL_LT_SUB_LADD, REAL_NOT_LE]
                THEN PROVE_TAC [REAL_ADD_SYM]))
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN PROVE_TAC [REAL_DOWN]);

val REAL_INV_LT_ANTIMONO = store_thm
  ("REAL_INV_LT_ANTIMONO",
   ``!x y : real. 0 < x /\ 0 < y ==> (inv x < inv y <=> y < x)``,
   RW_TAC boolSimps.bool_ss []
   THEN (REVERSE EQ_TAC THEN1 PROVE_TAC [REAL_LT_INV])
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_INV_INV]
   THEN MATCH_MP_TAC REAL_LT_INV
   THEN RW_TAC boolSimps.bool_ss [REAL_INV_POS]);

Theorem REAL_INV_INJ[simp]:   !x y : real. (inv x = inv y) <=> (x = y)
Proof PROVE_TAC [REAL_INV_INV]
QED

val REAL_DIV_RMUL_CANCEL = store_thm
  ("REAL_DIV_RMUL_CANCEL",
   ``!c a b : real. ~(c = 0) ==> ((a * c) / (b * c) = a / b)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN Cases_on `b = 0`
   THEN RW_TAC boolSimps.bool_ss
      [REAL_MUL_LZERO, REAL_INV_0, REAL_INV_MUL, REAL_MUL_RZERO,
       REAL_EQ_MUL_LCANCEL, GSYM REAL_MUL_ASSOC]
   THEN DISJ2_TAC
   THEN (KNOW_TAC ``!a b c : real. a * (b * c) = (a * c) * b``
         THEN1 PROVE_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_RINV, REAL_MUL_LID]);

val REAL_DIV_LMUL_CANCEL = store_thm
  ("REAL_DIV_LMUL_CANCEL",
   ``!c a b : real. ~(c = 0) ==> ((c * a) / (c * b) = a / b)``,
   METIS_TAC [REAL_DIV_RMUL_CANCEL, REAL_MUL_SYM]);

val REAL_DIV_ADD = store_thm
  ("REAL_DIV_ADD",
   ``!x y z : real. y / x + z / x = (y + z) / x``,
   RW_TAC boolSimps.bool_ss [real_div, REAL_ADD_RDISTRIB]);

Theorem REAL_DIV_SUB :
    !x y z :real. y / x - z / x = (y - z) / x
Proof
    RW_TAC bool_ss [real_div, REAL_SUB_RDISTRIB]
QED

val REAL_ADD_RAT = store_thm
  ("REAL_ADD_RAT",
   ``!a b c d : real.
       ~(b = 0) /\ ~(d = 0) ==>
       (a / b + c / d = (a * d + b * c) / (b * d))``,
   RW_TAC boolSimps.bool_ss
   [GSYM REAL_DIV_ADD, REAL_DIV_RMUL_CANCEL, REAL_DIV_LMUL_CANCEL]);

val REAL_SUB_RAT = store_thm
  ("REAL_SUB_RAT",
   ``!a b c d : real.
       ~(b = 0) /\ ~(d = 0) ==>
       (a / b - c / d = (a * d - b * c) / (b * d))``,
   RW_TAC boolSimps.bool_ss [real_sub, real_div, REAL_NEG_LMUL]
   THEN RW_TAC boolSimps.bool_ss [GSYM real_div]
   THEN METIS_TAC [REAL_ADD_RAT, REAL_NEG_LMUL, REAL_NEG_RMUL]);

val REAL_SUB = store_thm
  ("REAL_SUB",
   ``!m n : num.
       (& m : real) - & n = if m - n = 0 then ~(& (n - m)) else & (m - n)``,
   RW_TAC old_arith_ss [REAL_EQ_SUB_RADD, REAL_ADD]
   THEN ONCE_REWRITE_TAC [REAL_ADD_SYM]
   THEN RW_TAC old_arith_ss [GSYM real_sub, REAL_EQ_SUB_LADD, REAL_ADD]);

Theorem REAL_SUB_NUMERAL[simp] =
        REAL_SUB |> SPECL [“NUMERAL m”, “NUMERAL n”]

(* ------------------------------------------------------------------------- *)
(* Define a constant for extracting "the positive part" of real numbers.     *)
(* ------------------------------------------------------------------------- *)

val pos_def = Define `pos (x : real) = if 0 <= x then x else 0`;

val REAL_POS_POS = store_thm
  ("REAL_POS_POS",
   ``!x. 0 <= pos x``,
   RW_TAC boolSimps.bool_ss [pos_def, REAL_LE_REFL]);

val REAL_POS_ID = store_thm
  ("REAL_POS_ID",
   ``!x. 0 <= x ==> (pos x = x)``,
   RW_TAC boolSimps.bool_ss [pos_def]);

val REAL_POS_INFLATE = store_thm
  ("REAL_POS_INFLATE",
   ``!x. x <= pos x``,
   RW_TAC boolSimps.bool_ss [pos_def, REAL_LE_REFL]
   THEN PROVE_TAC [REAL_LE_TOTAL]);

val REAL_POS_MONO = store_thm
  ("REAL_POS_MONO",
   ``!x y. x <= y ==> pos x <= pos y``,
   RW_TAC boolSimps.bool_ss [pos_def, REAL_LE_REFL]
   THEN PROVE_TAC [REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_POS_EQ_ZERO = store_thm
  ("REAL_POS_EQ_ZERO",
   ``!x. (pos x = 0) <=> x <= 0``,
   RW_TAC boolSimps.bool_ss [pos_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL])

val REAL_POS_LE_ZERO = store_thm
  ("REAL_POS_LE_ZERO",
   ``!x. (pos x <= 0) <=> x <= 0``,
   RW_TAC boolSimps.bool_ss [pos_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL])

(* ------------------------------------------------------------------------- *)
(* Define the minimum of two real numbers                                    *)
(* ------------------------------------------------------------------------- *)

val min_def = save_thm("min_def", real_min); (* moved to realaxTheory *)

val REAL_MIN_REFL = store_thm
  ("REAL_MIN_REFL",
   ``!x. min x x = x``,
   RW_TAC boolSimps.bool_ss [min_def]);

val REAL_LE_MIN = store_thm
  ("REAL_LE_MIN",
   ``!z x y. z <= min x y <=> z <= x /\ z <= y``,
   RW_TAC boolSimps.bool_ss [min_def]
   THEN PROVE_TAC [REAL_LE_TRANS, REAL_LE_TOTAL]);

val REAL_MIN_LE = store_thm
  ("REAL_MIN_LE",
   ``!z x y. min x y <= z <=> x <= z \/ y <= z``,
   RW_TAC boolSimps.bool_ss [min_def, REAL_LE_REFL]
   THEN PROVE_TAC [REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_MIN_LE1 = store_thm
  ("REAL_MIN_LE1",
   ``!x y. min x y <= x``,
   RW_TAC boolSimps.bool_ss [REAL_MIN_LE, REAL_LE_REFL]);

val REAL_MIN_LE2 = store_thm
  ("REAL_MIN_LE2",
   ``!x y. min x y <= y``,
   RW_TAC boolSimps.bool_ss [REAL_MIN_LE, REAL_LE_REFL]);

val REAL_LT_MIN = store_thm
  ("REAL_LT_MIN",
   ``!x y z. z < min x y <=> z < x /\ z < y``,
   RW_TAC boolSimps.bool_ss [min_def]
   THEN PROVE_TAC [REAL_LTE_TRANS, REAL_LT_TRANS, REAL_NOT_LE]);

val REAL_MIN_LT = store_thm
  ("REAL_MIN_LT",
   ``!x y z:real. min x y < z <=> x < z \/ y < z``,
   RW_TAC boolSimps.bool_ss [min_def]
   THEN PROVE_TAC [REAL_LTE_TRANS, REAL_LT_TRANS, REAL_NOT_LE]);

val REAL_MIN_ALT = store_thm
  ("REAL_MIN_ALT",
   ``!x y. (x <= y ==> (min x y = x)) /\ (y <= x ==> (min x y = y))``,
   RW_TAC boolSimps.bool_ss [min_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM]);

val REAL_MIN_LE_LIN = store_thm
  ("REAL_MIN_LE_LIN",
   ``!z x y. 0 <= z /\ z <= 1 ==> min x y <= z * x + (1 - z) * y``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (Q.SPECL [`x`, `y`] REAL_LE_TOTAL)
   THEN (STRIP_TAC THEN RW_TAC boolSimps.bool_ss [REAL_MIN_ALT])
   THENL [MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `z * x + (1 - z) * x`
          THEN (CONJ_TAC THEN1
                RW_TAC boolSimps.bool_ss
                [GSYM REAL_RDISTRIB, REAL_SUB_ADD2, REAL_LE_REFL, REAL_MUL_LID])
          THEN MATCH_MP_TAC REAL_LE_ADD2
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_REFL])
          THEN MATCH_MP_TAC REAL_LE_LMUL_IMP
          THEN ASM_REWRITE_TAC [REAL_SUB_LE],
          MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `z * y + (1 - z) * y`
          THEN (CONJ_TAC THEN1
                RW_TAC boolSimps.bool_ss
                [GSYM REAL_RDISTRIB, REAL_SUB_ADD2, REAL_LE_REFL, REAL_MUL_LID])
          THEN MATCH_MP_TAC REAL_LE_ADD2
          THEN (REVERSE CONJ_TAC THEN1 PROVE_TAC [REAL_LE_REFL])
          THEN MATCH_MP_TAC REAL_LE_LMUL_IMP
          THEN ASM_REWRITE_TAC []]);

val REAL_MIN_ADD = store_thm
  ("REAL_MIN_ADD",
   ``!z x y. min (x + z) (y + z) = min x y + z``,
   RW_TAC boolSimps.bool_ss [min_def, REAL_LE_RADD]);

val REAL_MIN_SUB = store_thm
  ("REAL_MIN_SUB",
   ``!z x y. min (x - z) (y - z) = min x y - z``,
   RW_TAC boolSimps.bool_ss [min_def, REAL_LE_SUB_RADD, REAL_SUB_ADD]);

val REAL_IMP_MIN_LE2 = store_thm
  ("REAL_IMP_MIN_LE2",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2``,
   RW_TAC boolSimps.bool_ss [REAL_LE_MIN]
   THEN RW_TAC boolSimps.bool_ss [REAL_MIN_LE]);

(* from real_topologyTheory *)
val REAL_MIN_ACI = store_thm
  ("REAL_MIN_ACI",
  ``!x y z. (min x y = min y x) /\
            (min (min x y) z = min x (min y z)) /\
            (min x (min y z) = min y (min x z)) /\
            (min x x = x) /\
            (min x (min x y) = min x y)``,
    RW_TAC bool_ss [min_def]
 >> FULL_SIMP_TAC bool_ss [] (* 7 subgoals *)
 >| [ PROVE_TAC [REAL_LE_ANTISYM],
      PROVE_TAC [REAL_NOT_LE, REAL_LT_ANTISYM],
      REV_FULL_SIMP_TAC bool_ss [],
      Cases_on `y <= z`
      >- ( FULL_SIMP_TAC bool_ss [] \\
           PROVE_TAC [REAL_LE_TRANS] ) \\
      FULL_SIMP_TAC bool_ss [] >> FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
      `x <= y` by PROVE_TAC [REAL_LET_TRANS, REAL_LT_IMP_LE] \\
      FULL_SIMP_TAC bool_ss [] \\
      PROVE_TAC [REAL_LTE_ANTISYM],
      REVERSE (Cases_on `(y <= z)`)
      >- ( FULL_SIMP_TAC bool_ss [] >> REV_FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
           PROVE_TAC [REAL_LTE_ANTISYM, REAL_LTE_TRANS] ) \\
      FULL_SIMP_TAC bool_ss [] \\
      FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
      `x <= z` by PROVE_TAC [REAL_LE_TRANS] \\
      FULL_SIMP_TAC bool_ss [] >> PROVE_TAC [REAL_LE_ANTISYM],
      FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
      PROVE_TAC [REAL_LT_ANTISYM],
      REV_FULL_SIMP_TAC bool_ss [] ]);

(* ------------------------------------------------------------------------- *)
(* Define the maximum of two real numbers                                    *)
(* ------------------------------------------------------------------------- *)

val max_def = save_thm("max_def", real_max); (* moved to realaxTheory *)

val REAL_MAX_REFL = store_thm
  ("REAL_MAX_REFL",
   ``!x. max x x = x``,
   RW_TAC boolSimps.bool_ss [max_def]);

val REAL_LE_MAX = store_thm
  ("REAL_LE_MAX",
   ``!z x y. z <= max x y <=> z <= x \/ z <= y``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_LE_MAX1 = store_thm
  ("REAL_LE_MAX1",
   ``!x y. x <= max x y``,
   RW_TAC boolSimps.bool_ss [REAL_LE_MAX, REAL_LE_REFL]);

val REAL_LE_MAX2 = store_thm
  ("REAL_LE_MAX2",
   ``!x y. y <= max x y``,
   RW_TAC boolSimps.bool_ss [REAL_LE_MAX, REAL_LE_REFL]);

val REAL_MAX_LE = store_thm
  ("REAL_MAX_LE",
   ``!z x y. max x y <= z <=> x <= z /\ y <= z``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LE_TRANS, REAL_LE_TOTAL]);

val REAL_LT_MAX = store_thm
  ("REAL_LT_MAX",
   ``!x y z. z < max x y <=> z < x \/ z < y``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LT_TRANS, REAL_LTE_TRANS, REAL_NOT_LE]);

val REAL_MAX_LT = store_thm
  ("REAL_MAX_LT",
   ``!x y z. max x y < z <=> x < z /\ y < z``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LT_TRANS, REAL_LTE_TRANS, REAL_NOT_LE]);

val REAL_MAX_ALT = store_thm
  ("REAL_MAX_ALT",
   ``!x y. (x <= y ==> (max x y = y)) /\ (y <= x ==> (max x y = x))``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM]);

val REAL_MAX_MIN = store_thm
  ("REAL_MAX_MIN",
   ``!x y. max x y = ~min (~x) (~y)``,
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPECL [`x`, `y`] REAL_LE_TOTAL)
   THEN STRIP_TAC
   THEN RW_TAC boolSimps.bool_ss
        [REAL_MAX_ALT, REAL_MIN_ALT, REAL_LE_NEG2, REAL_NEGNEG]);

val REAL_MIN_MAX = store_thm
  ("REAL_MIN_MAX",
   ``!x y. min x y = ~max (~x) (~y)``,
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPECL [`x`, `y`] REAL_LE_TOTAL)
   THEN STRIP_TAC
   THEN RW_TAC boolSimps.bool_ss
        [REAL_MAX_ALT, REAL_MIN_ALT, REAL_LE_NEG2, REAL_NEGNEG]);

val REAL_LIN_LE_MAX = store_thm
  ("REAL_LIN_LE_MAX",
   ``!z x y. 0 <= z /\ z <= 1 ==> z * x + (1 - z) * y <= max x y``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (Q.SPECL [`z`, `~x`, `~y`] REAL_MIN_LE_LIN)
   THEN RW_TAC boolSimps.bool_ss
        [REAL_MIN_MAX, REAL_NEGNEG, REAL_MUL_RNEG, GSYM REAL_NEG_ADD,
         REAL_LE_NEG2]);

val REAL_MAX_ADD = store_thm
  ("REAL_MAX_ADD",
   ``!z x y. max (x + z) (y + z) = max x y + z``,
   RW_TAC boolSimps.bool_ss [max_def, REAL_LE_RADD]);

val REAL_MAX_SUB = store_thm
  ("REAL_MAX_SUB",
   ``!z x y. max (x - z) (y - z) = max x y - z``,
   RW_TAC boolSimps.bool_ss [max_def, REAL_LE_SUB_RADD, REAL_SUB_ADD]);

val REAL_IMP_MAX_LE2 = store_thm
  ("REAL_IMP_MAX_LE2",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2``,
   RW_TAC boolSimps.bool_ss [REAL_MAX_LE]
   THEN RW_TAC boolSimps.bool_ss [REAL_LE_MAX]);

(* from real_topologyTheory *)
val REAL_MAX_ACI = store_thm
  ("REAL_MAX_ACI",
  ``!x y z. (max x y = max y x) /\
            (max (max x y) z = max x (max y z)) /\
            (max x (max y z) = max y (max x z)) /\
            (max x x = x) /\
            (max x (max x y) = max x y)``,
    RW_TAC bool_ss [max_def]
 >> FULL_SIMP_TAC bool_ss [] (* 7 subgoals *)
 >| [ PROVE_TAC [REAL_LE_ANTISYM],
      PROVE_TAC [REAL_NOT_LE, REAL_LT_ANTISYM],
      REVERSE (Cases_on `(y <= z)`)
      >- ( FULL_SIMP_TAC bool_ss [] >> FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
           PROVE_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS] ) \\
      FULL_SIMP_TAC bool_ss [] \\
      FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
      `~(x <= y)` by PROVE_TAC [REAL_LET_TRANS, REAL_NOT_LE] \\
      FULL_SIMP_TAC bool_ss [] \\
      PROVE_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS],
      REV_FULL_SIMP_TAC bool_ss [],
      REV_FULL_SIMP_TAC bool_ss [],
      PROVE_TAC [REAL_LE_ANTISYM],
      Cases_on `y <= z`
      >- ( FULL_SIMP_TAC bool_ss [] >> REV_FULL_SIMP_TAC bool_ss [] \\
           FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
           PROVE_TAC [REAL_LT_ANTISYM, REAL_LTE_TRANS] ) \\
      FULL_SIMP_TAC bool_ss [] >> FULL_SIMP_TAC bool_ss [REAL_NOT_LE] \\
      PROVE_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS] ]);

(* extracted from integrationTheory *)
Theorem REAL_MIN_LE_MAX :
    !x:real y. min x y <= max x y
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘x’
 >> REWRITE_TAC [REAL_MIN_LE1, REAL_LE_MAX1]
QED

(* extracted from integrationTheory *)
Theorem REAL_MAX_SUB_MIN :
    !x:real y. max x y - min x y = abs (y - x)
Proof
    RW_TAC std_ss [min_def, max_def, abs, REAL_SUB_LE, REAL_NEG_SUB]
QED

(* extracted from integrationTheory *)
Theorem ABS_BOUNDS_MIN_MAX :
   !a b x B:real. abs(x) <= B ==> min a (-B) <= x /\ x <= max b B
Proof
    rpt GEN_TAC
 >> DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [ABS_BOUNDS])
 >> PROVE_TAC [REAL_LE_MAX, REAL_MIN_LE]
QED

(* ------------------------------------------------------------------------- *)
(* More theorems about sup, and corresponding theorems about an inf operator *)
(* ------------------------------------------------------------------------- *)

val inf_def = Define `inf p = ~(sup (\r. p (~r)))`;

Theorem inf_alt :
    !p. inf p = ~(sup (IMAGE $~ p))
Proof
    RW_TAC std_ss [inf_def]
 >> Suff `(\r. p (-r)) = (IMAGE numeric_negate p)` >- rw []
 >> SET_EQ_TAC
 >> RW_TAC std_ss [IN_IMAGE, IN_APP]
 >> EQ_TAC >> RW_TAC std_ss []
 >- (Q.EXISTS_TAC `-x` >> rw [REAL_NEG_NEG])
 >> rw [REAL_NEG_NEG]
QED

Theorem INF_DEF_ALT :
    !p. inf p = ~(sup (\r. ~r IN p)):real
Proof
    RW_TAC std_ss []
 >> PURE_REWRITE_TAC [inf_def, IMAGE_DEF]
 >> Suff `(\r. p (-r)) = (\r. -r IN p)`
 >- RW_TAC std_ss []
 >> RW_TAC std_ss [FUN_EQ_THM, SPECIFICATION]
QED

(* dual theorem of REAL_SUP *)
Theorem REAL_INF :
    !P. (?x. P x) /\ (?z. !x. P x ==> z < x) ==>
        (!y. (?x. P x /\ x < y) <=> inf P < y)
Proof
    RW_TAC std_ss [inf_def]
 >> Know ‘-sup (\r. P (-r)) < --y <=> -y < sup (\r. P (-r))’
 >- REWRITE_TAC [REAL_LT_NEG]
 >> REWRITE_TAC [REAL_NEG_NEG]
 >> Rewr'
 >> MP_TAC (BETA_RULE (Q.SPEC ‘\x. P (~x)’ REAL_SUP))
 >> Know ‘(?x. P (-x)) /\ (?z. !x. P (-x) ==> x < z)’
 >- (CONJ_TAC >- (Q.EXISTS_TAC ‘-x’ >> rw [REAL_NEG_NEG]) \\
     Q.EXISTS_TAC ‘-z’ >> rpt STRIP_TAC >> rename1 ‘P (-y)’ \\
     Q.PAT_X_ASSUM ‘!x. P x ==> z < x’ (MP_TAC o (Q.SPEC ‘-y’)) \\
     RW_TAC std_ss [] \\
     Know ‘y < -z <=> --y < -z’ >- REWRITE_TAC [REAL_NEG_NEG] >> Rewr' \\
     ASM_REWRITE_TAC [REAL_LT_NEG])
 >> Rewr
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o (ONCE_REWRITE_RULE [EQ_SYM_EQ]))
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      rename1 ‘w < y’ >> Q.EXISTS_TAC ‘-w’ \\
      ASM_REWRITE_TAC [REAL_NEG_NEG, REAL_LT_NEG],
      (* goal 2 (of 2) *)
      rename1 ‘-y < w’ >> Q.EXISTS_TAC ‘-w’ \\
      ASM_REWRITE_TAC [] \\
      Know ‘-w < y <=> -w < --y’ >- REWRITE_TAC [REAL_NEG_NEG] >> Rewr' \\
      ASM_REWRITE_TAC [REAL_LT_NEG] ]
QED

Theorem REAL_INF' :
    !P. P <> {} /\ (?z. !x. x IN P ==> z < x) ==>
        (!y. (?x. x IN P /\ x < y) <=> inf P < y)
Proof
    REWRITE_TAC [IN_APP, REAL_INF, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_SUP_EXISTS_UNIQUE = store_thm
  ("REAL_SUP_EXISTS_UNIQUE",
   ``!p : real -> bool.
       (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
       ?!s. !y. (?x. p x /\ y < x) <=> y < s``,
   REPEAT STRIP_TAC
   THEN CONV_TAC EXISTS_UNIQUE_CONV
   THEN (RW_TAC boolSimps.bool_ss []
         THEN1 (MP_TAC (Q.SPEC `p` REAL_SUP_LE) THEN PROVE_TAC []))
   THEN REWRITE_TAC [GSYM REAL_LE_ANTISYM, GSYM REAL_NOT_LT]
   THEN REPEAT STRIP_TAC
   THENL [(SUFF_TAC ``!x : real. p x ==> ~(s' < x)`` THEN1 PROVE_TAC [])
          THEN REPEAT STRIP_TAC
          THEN (SUFF_TAC ``~((s' : real) < s')`` THEN1 PROVE_TAC [])
          THEN REWRITE_TAC [REAL_LT_REFL],
          (SUFF_TAC ``!x : real. p x ==> ~(s < x)`` THEN1 PROVE_TAC [])
          THEN REPEAT STRIP_TAC
          THEN (SUFF_TAC ``~((s : real) < s)`` THEN1 PROVE_TAC [])
          THEN REWRITE_TAC [REAL_LT_REFL]]);

Theorem REAL_SUP_EXISTS_UNIQUE' :
    !p : real -> bool.
       p <> {} /\ (?z. !x. x IN p ==> x <= z) ==>
       ?!s. !y. (?x. x IN p /\ y < x) <=> y < s
Proof
    REWRITE_TAC [IN_APP, REAL_SUP_EXISTS_UNIQUE, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_SUP_MAX = store_thm
  ("REAL_SUP_MAX",
   ``!p z. p z /\ (!x. p x ==> x <= z) ==> (sup p = z)``,
    REPEAT STRIP_TAC
    THEN (KNOW_TAC ``!y : real. (?x. p x /\ y < x) <=> y < z``
          THEN1 (STRIP_TAC
                 THEN REVERSE EQ_TAC THEN1 PROVE_TAC []
                 THEN REPEAT STRIP_TAC
                 THEN PROVE_TAC [REAL_LTE_TRANS]))
    THEN STRIP_TAC
    THEN (KNOW_TAC ``!y. (?x. p x /\ y < x) <=> y < sup p``
          THEN1 PROVE_TAC [REAL_SUP_LE])
    THEN STRIP_TAC
    THEN (KNOW_TAC ``(?x : real. p x) /\ (?z. !x. p x ==> x <= z)``
          THEN1 PROVE_TAC [])
    THEN STRIP_TAC
    THEN ASSUME_TAC ((SPEC ``p:real->bool`` o CONV_RULE
                    (DEPTH_CONV EXISTS_UNIQUE_CONV)) REAL_SUP_EXISTS_UNIQUE)
    THEN RES_TAC);

Theorem REAL_SUP_MAX' :
    !p z. z IN p /\ (!x. x IN p ==> x <= z) ==> (sup p = z)
Proof
    REWRITE_TAC [IN_APP, REAL_SUP_MAX]
QED

val REAL_IMP_SUP_LE = store_thm
  ("REAL_IMP_SUP_LE",
   ``!p x. (?r. p r) /\ (!r. p r ==> r <= x) ==> sup p <= x``,
   RW_TAC boolSimps.bool_ss []
   THEN REWRITE_TAC [GSYM REAL_NOT_LT]
   THEN STRIP_TAC
   THEN MP_TAC (SPEC ``p:real->bool`` REAL_SUP_LE)
   THEN RW_TAC boolSimps.bool_ss []
   THENL [PROVE_TAC [],
          PROVE_TAC [],
          EXISTS_TAC ``x:real``
          THEN RW_TAC boolSimps.bool_ss []
          THEN PROVE_TAC [real_lte]]);

Theorem REAL_IMP_SUP_LE' :
    !p x. p <> {} /\ (!r. r IN p ==> r <= x) ==> sup p <= x
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_SUP_LE, GSYM MEMBER_NOT_EMPTY]
QED

(* NOTE: removed unnecessary ‘(?r. p r)’ from antecedents *)
Theorem REAL_IMP_LE_SUP :
    !p x. (?z. !r. p r ==> r <= z) /\ (?r. p r /\ x <= r) ==> x <= sup p
Proof
    RW_TAC bool_ss []
 >> (SUFF_TAC ``!y. p y ==> y <= sup p`` >- PROVE_TAC [REAL_LE_TRANS])
 >> MATCH_MP_TAC REAL_SUP_UBOUND_LE
 >> PROVE_TAC []
QED

Theorem REAL_IMP_LE_SUP' :
    !p x. (?z. !r. r IN p ==> r <= z) /\ (?r. r IN p /\ x <= r) ==> x <= sup p
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_LE_SUP]
QED

Theorem REAL_IMP_LT_SUP :
    !p x. (?z. !r. p r ==> r <= z) /\ ~p (sup p) /\ p x ==> x < sup p
Proof
    reverse (RW_TAC bool_ss [REAL_LT_LE])
 >- (CCONTR_TAC >> FULL_SIMP_TAC bool_ss [])
 >> MATCH_MP_TAC REAL_IMP_LE_SUP
 >> reverse CONJ_TAC
 >- (Q.EXISTS_TAC ‘x’ >> ASM_REWRITE_TAC [REAL_LE_REFL])
 >> Q.EXISTS_TAC ‘z’ >> RW_TAC bool_ss []
QED

Theorem REAL_IMP_LT_SUP' :
    !p x. (?z. !r. r IN p ==> r <= z) /\ sup p NOTIN p /\ p x ==> x < sup p
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_LT_SUP]
QED

val REAL_INF_MIN = store_thm
  ("REAL_INF_MIN",
   ``!p z. p z /\ (!x. p x ==> z <= x) ==> (inf p = z)``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (SPECL [``(\r. (p:real->bool) (~r))``, ``~(z:real)``]
                REAL_SUP_MAX)
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG, inf_def]
   THEN (SUFF_TAC ``!x : real. p ~x ==> x <= ~z`` THEN1 PROVE_TAC [REAL_NEGNEG])
   THEN REPEAT STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN ONCE_REWRITE_TAC [REAL_LE_NEG]
   THEN REWRITE_TAC [REAL_NEGNEG]
   THEN PROVE_TAC []);

Theorem REAL_INF_MIN' :
    !p z. z IN p /\ (!x. x IN p ==> z <= x) ==> (inf p = z)
Proof
    REWRITE_TAC [IN_APP, REAL_INF_MIN]
QED

val REAL_IMP_LE_INF = store_thm
  ("REAL_IMP_LE_INF",
   ``!p r. (?x. p x) /\ (!x. p x ==> r <= x) ==> r <= inf p``,
   RW_TAC boolSimps.bool_ss [inf_def]
   THEN POP_ASSUM MP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN Q.SPEC_TAC (`~r`, `r`)
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG, REAL_LE_NEG]
   THEN MATCH_MP_TAC REAL_IMP_SUP_LE
   THEN RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC [REAL_NEGNEG]);

Theorem REAL_IMP_LE_INF' :
    !p r. p <> {} /\ (!x. x IN p ==> r <= x) ==> r <= inf p
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_LE_INF, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_IMP_INF_LE = store_thm
  ("REAL_IMP_INF_LE",
   ``!p r. (?z. !x. p x ==> z <= x) /\ (?x. p x /\ x <= r) ==> inf p <= r``,
   RW_TAC boolSimps.bool_ss [inf_def]
   THEN POP_ASSUM MP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN Q.SPEC_TAC (`~r`, `r`)
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG, REAL_LE_NEG]
   THEN MATCH_MP_TAC REAL_IMP_LE_SUP
   THEN RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

Theorem REAL_IMP_INF_LE' :
    !p r. (?z. !x. x IN p ==> z <= x) /\ (?x. x IN p /\ x <= r) ==> inf p <= r
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_INF_LE]
QED

val REAL_INF_LT = store_thm
  ("REAL_INF_LT",
   ``!p z. (?x. p x) /\ inf p < z ==> (?x. p x /\ x < z)``,
   RW_TAC boolSimps.bool_ss []
   THEN (SUFF_TAC ``~(!x. p x ==> ~(x < z))`` THEN1 PROVE_TAC [])
   THEN REWRITE_TAC [GSYM real_lte]
   THEN STRIP_TAC
   THEN Q.PAT_X_ASSUM `inf p < z` MP_TAC
   THEN RW_TAC boolSimps.bool_ss [GSYM real_lte]
   THEN MATCH_MP_TAC REAL_IMP_LE_INF
   THEN PROVE_TAC []);

Theorem REAL_INF_LT' :
    !p z. p <> {} /\ inf p < z ==> ?x. x IN p /\ x < z
Proof
    REWRITE_TAC [IN_APP, REAL_INF_LT, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_INF_CLOSE = store_thm
  ("REAL_INF_CLOSE",
   ``!p e. (?x. p x) /\ 0 < e ==> (?x. p x /\ x < inf p + e)``,
   RW_TAC boolSimps.bool_ss []
   THEN MATCH_MP_TAC REAL_INF_LT
   THEN (CONJ_TAC THEN1 PROVE_TAC [])
   THEN RW_TAC boolSimps.bool_ss [REAL_LT_ADDR]);

Theorem REAL_INF_CLOSE' :
    !p e. p <> {} /\ 0 < e ==> ?x. x IN p /\ x < inf p + e
Proof
    REWRITE_TAC [IN_APP, REAL_INF_CLOSE, GSYM MEMBER_NOT_EMPTY]
QED

val SUP_EPSILON = store_thm
  ("SUP_EPSILON",
   ``!p e.
       0 < e /\ (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
       ?x. p x /\ sup p <= x + e``,
   REPEAT GEN_TAC
   THEN REPEAT DISCH_TAC
   THEN REWRITE_TAC [GSYM REAL_NOT_LT]
   THEN MP_TAC (Q.SPEC `p` REAL_SUP_LE)
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
   THEN POP_ASSUM MP_TAC
   THEN RW_TAC boolSimps.bool_ss [GSYM IMP_DISJ_THM, REAL_NOT_LT]
   THEN (SUFF_TAC
         ``?n : num.
             ?x : real. p x /\ z - &(SUC n) * e <= x /\ x <= z - & n * e /\
             !y. p y ==> y <= z - &n * e``
         THEN1 (RW_TAC boolSimps.bool_ss []
                THEN Q.EXISTS_TAC `x'`
                THEN RW_TAC boolSimps.bool_ss []
                THEN Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x''`)
                THEN RW_TAC boolSimps.bool_ss []
                THEN MATCH_MP_TAC REAL_LE_TRANS
                THEN Q.EXISTS_TAC `z - &n * e`
                THEN RW_TAC boolSimps.bool_ss []
                THEN (SUFF_TAC ``(z:real) - &n * e = z - &(SUC n) * e + 1 * e``
                      THEN1 RW_TAC boolSimps.bool_ss
                            [REAL_MUL_LID, REAL_LE_RADD])
                THEN RW_TAC boolSimps.bool_ss
                     [real_sub, GSYM REAL_ADD_ASSOC, REAL_EQ_LADD]
                THEN ONCE_REWRITE_TAC [GSYM REAL_EQ_NEG]
                THEN RW_TAC boolSimps.bool_ss
                     [REAL_NEGNEG, REAL_NEG_ADD, GSYM REAL_MUL_LNEG,
                      GSYM REAL_ADD_RDISTRIB, REAL_EQ_RMUL]
                THEN DISJ2_TAC
                THEN RW_TAC boolSimps.bool_ss
                     [REAL_EQ_SUB_LADD, GSYM real_sub, REAL_ADD, REAL_INJ,
                      arithmeticTheory.ADD1]))
   THEN (KNOW_TAC ``?n : num. ?x : real. p x /\ z - &(SUC n) * e <= x``
         THEN1 (MP_TAC (Q.SPEC `(z - x) / e` REAL_BIGNUM)
                THEN STRIP_TAC
                THEN Q.EXISTS_TAC `n`
                THEN Q.EXISTS_TAC `x`
                THEN RW_TAC boolSimps.bool_ss [REAL_LE_SUB_RADD]
                THEN ONCE_REWRITE_TAC [REAL_ADD_SYM]
                THEN REWRITE_TAC [GSYM REAL_LE_SUB_RADD]
                THEN (KNOW_TAC ``((z - x) / e) * e = (z:real) - x``
                      THEN1 (MATCH_MP_TAC REAL_DIV_RMUL
                             THEN PROVE_TAC [REAL_LT_LE]))
                THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
                THEN RW_TAC boolSimps.bool_ss [REAL_LE_RMUL]
                THEN MATCH_MP_TAC REAL_LE_TRANS
                THEN Q.EXISTS_TAC `&n`
                THEN REWRITE_TAC [REAL_LE]
                THEN PROVE_TAC
                     [arithmeticTheory.LESS_EQ_SUC_REFL, REAL_LT_LE]))
   THEN DISCH_THEN (MP_TAC o HO_MATCH_MP LEAST_EXISTS_IMP)
   THEN Q.SPEC_TAC (`$LEAST (\n. ?x. p x /\ z - & (SUC n) * e <= x)`, `m`)
   THEN RW_TAC boolSimps.bool_ss [GSYM IMP_DISJ_THM]
   THEN Q.EXISTS_TAC `m`
   THEN Q.EXISTS_TAC `x'`
   THEN ASM_REWRITE_TAC []
   THEN (Cases_on `m`
         THEN1 RW_TAC boolSimps.bool_ss [REAL_MUL_LZERO, REAL_SUB_RZERO])
   THEN POP_ASSUM (MP_TAC o Q.SPEC `n`)
   THEN RW_TAC boolSimps.bool_ss [prim_recTheory.LESS_SUC_REFL, GSYM real_lt]
   THEN PROVE_TAC [REAL_LT_LE]);

Theorem SUP_EPSILON' :
    !p e.
       0 < e /\ p <> {} /\ (?z. !x. x IN p ==> x <= z) ==>
       ?x. x IN p /\ sup p <= x + e
Proof
    REWRITE_TAC [IN_APP, SUP_EPSILON, GSYM MEMBER_NOT_EMPTY]
QED

(* This theorem is slightly more general than SUP_EPSILON (in sense of REAL_LT_IMP_LE)
   but actually can be proved as a corollary of SUP_EPSILON.
 *)
Theorem SUP_LT_EPSILON :
    !p e. 0 < e /\ (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
          ?x. p x /\ sup p < x + e
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘e / 2’] SUP_EPSILON)
 >> KNOW_TAC “0 < e / 2”
 >- (MATCH_MP_TAC REAL_LT_DIV >> RW_TAC arith_ss [REAL_LT])
 >> KNOW_TAC “?(x :real). p x”
 >- (Q.EXISTS_TAC ‘x’ >> ASM_REWRITE_TAC [])
 >> KNOW_TAC “?(z :real). !x. p x ==> x <= z”
 >- (Q.EXISTS_TAC ‘z’ >> RW_TAC std_ss [])
 >> RW_TAC std_ss []
 >> rename1 ‘sup p <= y + e / 2’
 >> Q.EXISTS_TAC ‘y’ >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘y + e / 2’ >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC REAL_LT_IADD
 >> ASM_REWRITE_TAC [REAL_LT_HALF2]
QED

Theorem SUP_LT_EPSILON' :
    !p e. 0 < e /\ p <> {} /\ (?z. !x. x IN p ==> x <= z) ==>
          ?x. x IN p /\ sup p < x + e
Proof
    REWRITE_TAC [IN_APP, SUP_LT_EPSILON, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_LE_SUP = store_thm
  ("REAL_LE_SUP",
   ``!p x : real.
       (?y. p y) /\ (?y. !z. p z ==> z <= y) ==>
       (x <= sup p <=> !y. (!z. p z ==> z <= y) ==> x <= y)``,
   RW_TAC boolSimps.bool_ss []
   THEN EQ_TAC
   THENL [RW_TAC boolSimps.bool_ss []
          THEN MATCH_MP_TAC REAL_LE_EPSILON
          THEN RW_TAC boolSimps.bool_ss [GSYM REAL_LE_SUB_RADD]
          THEN (KNOW_TAC ``(x:real) - e < sup p``
                THEN1 (MATCH_MP_TAC REAL_LTE_TRANS
                       THEN Q.EXISTS_TAC `x`
                       THEN RW_TAC boolSimps.bool_ss
                            [REAL_LT_SUB_RADD, REAL_LT_ADDR]))
          THEN Q.PAT_X_ASSUM `0 < e` (K ALL_TAC)
          THEN Q.PAT_X_ASSUM `x <= sup p` (K ALL_TAC)
          THEN Q.SPEC_TAC (`x - e`, `x`)
          THEN GEN_TAC
          THEN MP_TAC (Q.SPEC `p` REAL_SUP_LE)
          THEN MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
          THEN (CONJ_TAC THEN1 PROVE_TAC [])
          THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
          THEN STRIP_TAC
          THEN MATCH_MP_TAC REAL_LE_TRANS
          THEN PROVE_TAC [REAL_LT_LE],
          RW_TAC boolSimps.bool_ss []
          THEN MATCH_MP_TAC REAL_LE_EPSILON
          THEN RW_TAC boolSimps.bool_ss [GSYM REAL_LE_SUB_RADD]
          THEN (SUFF_TAC ``(x:real) - e < sup p`` THEN1 PROVE_TAC [REAL_LT_LE])
          THEN Q.PAT_X_ASSUM `!y. P y` (MP_TAC o Q.SPEC `x - e`)
          THEN (KNOW_TAC ``!a b : real. a <= a - b <=> ~(0 < b)``
                THEN1 (RW_TAC boolSimps.bool_ss [real_lt, REAL_LE_SUB_LADD]
                       THEN PROVE_TAC [REAL_ADD_RID, REAL_LE_LADD]))
          THEN DISCH_THEN (fn th => ASM_REWRITE_TAC [th])
          THEN POP_ASSUM (K ALL_TAC)
          THEN Q.SPEC_TAC (`x - e`, `x`)
          THEN GEN_TAC
          THEN RW_TAC boolSimps.bool_ss []
          THEN MP_TAC (Q.SPEC `p` REAL_SUP_LE)
          THEN MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
          THEN (CONJ_TAC THEN1 PROVE_TAC [])
          THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
          THEN PROVE_TAC [real_lt]]);

Theorem REAL_LE_SUP' :
    !p x : real.
       p <> {} /\ (?y. !z. z IN p ==> z <= y) ==>
       (x <= sup p <=> !y. (!z. z IN p ==> z <= y) ==> x <= y)
Proof
    REWRITE_TAC [IN_APP, REAL_LE_SUP, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_INF_LE = store_thm
  ("REAL_INF_LE",
   ``!p x : real.
       (?y. p y) /\ (?y. !z. p z ==> y <= z) ==>
       (inf p <= x <=> !y. (!z. p z ==> y <= z) ==> y <= x)``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (Q.SPECL [`\r. p ~r`, `~x`] REAL_LE_SUP)
   THEN MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG])
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN REWRITE_TAC [GSYM inf_def]
   THEN REWRITE_TAC [REAL_LE_NEG]
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG]
   THEN POP_ASSUM (K ALL_TAC)
   THEN EQ_TAC
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_X_ASSUM `!a. (!b. P a b) ==> Q a` (MP_TAC o Q.SPEC `~y''`)
   THEN PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

Theorem REAL_INF_LE' :
    !p x : real.
       p <> {} /\ (?y. !z. z IN p ==> y <= z) ==>
       (inf p <= x <=> !y. (!z. z IN p ==> y <= z) ==> y <= x)
Proof
    REWRITE_TAC [IN_APP, REAL_INF_LE, GSYM MEMBER_NOT_EMPTY]
QED

val REAL_SUP_CONST = store_thm
  ("REAL_SUP_CONST",
   ``!x : real. sup (\r. r = x) = x``,
   RW_TAC boolSimps.bool_ss []
   THEN ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   THEN CONJ_TAC
   THENL [MATCH_MP_TAC REAL_IMP_SUP_LE
          THEN PROVE_TAC [REAL_LE_REFL],
          MATCH_MP_TAC REAL_IMP_LE_SUP
          THEN PROVE_TAC [REAL_LE_REFL]]);

(* ------------------------------------------------------------------------- *)
(* Theorems to put in the real simpset                                       *)
(* ------------------------------------------------------------------------- *)

val REAL_MUL_SUB2_CANCEL = store_thm
  ("REAL_MUL_SUB2_CANCEL",
   ``!z x y : real. x * y + (z - x) * y = z * y``,
   RW_TAC boolSimps.bool_ss [GSYM REAL_RDISTRIB, REAL_SUB_ADD2]);

val REAL_MUL_SUB1_CANCEL = store_thm
  ("REAL_MUL_SUB1_CANCEL",
   ``!z x y : real. y * x + y * (z - x) = y * z``,
   RW_TAC boolSimps.bool_ss [GSYM REAL_LDISTRIB, REAL_SUB_ADD2]);

val REAL_NEG_HALF = store_thm
  ("REAL_NEG_HALF",
   ``!x : real. x - x / 2 = x / 2``,
   STRIP_TAC
   THEN (SUFF_TAC ``((x:real) - x / 2) + x / 2 = x / 2 + x / 2``
         THEN1 RW_TAC boolSimps.bool_ss [REAL_EQ_RADD])
   THEN RW_TAC boolSimps.bool_ss [REAL_SUB_ADD, REAL_HALF_DOUBLE]);

val REAL_NEG_THIRD = store_thm
  ("REAL_NEG_THIRD",
   ``!x : real. x - x / 3 = (2 * x) / 3``,
   STRIP_TAC
   THEN MATCH_MP_TAC REAL_EQ_LMUL_IMP
   THEN Q.EXISTS_TAC `3`
   THEN (KNOW_TAC ``~(3r = 0)``
         THEN1 (REWRITE_TAC [REAL_INJ] THEN numLib.ARITH_TAC))
   THEN RW_TAC boolSimps.bool_ss [REAL_SUB_LDISTRIB, REAL_DIV_LMUL]
   THEN (KNOW_TAC ``!x y z : real. (y = 1 * x + z) ==> (y - x = z)``
         THEN1 RW_TAC boolSimps.bool_ss [REAL_MUL_LID, REAL_ADD_SUB])
   THEN DISCH_THEN MATCH_MP_TAC
   THEN RW_TAC boolSimps.bool_ss [GSYM REAL_ADD_RDISTRIB, REAL_ADD,
                                  REAL_EQ_RMUL, REAL_INJ]
   THEN DISJ2_TAC
   THEN numLib.ARITH_TAC);

val REAL_DIV_DENOM_CANCEL = store_thm
  ("REAL_DIV_DENOM_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((y / x) / (z / x) = y / z)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN (Cases_on `y = 0` THEN1 RW_TAC boolSimps.bool_ss [REAL_MUL_LZERO])
   THEN (Cases_on `z = 0`
         THEN1 RW_TAC boolSimps.bool_ss
               [REAL_INV_0, REAL_MUL_RZERO, REAL_MUL_LZERO])
   THEN RW_TAC boolSimps.bool_ss [REAL_INV_MUL, REAL_INV_EQ_0, REAL_INVINV]
   THEN (KNOW_TAC ``!a b c d : real. a * b * (c * d) = (a * c) * (b * d)``
         THEN1 metisLib.METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_DENOM_CANCEL2 = save_thm
  ("REAL_DIV_DENOM_CANCEL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_DENOM_CANCEL));

val REAL_DIV_DENOM_CANCEL3 = save_thm
  ("REAL_DIV_DENOM_CANCEL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_DENOM_CANCEL));

val REAL_DIV_INNER_CANCEL = store_thm
  ("REAL_DIV_INNER_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((y / x) * (x / z) = y / z)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN (KNOW_TAC ``!a b c d : real. a * b * (c * d) = (a * d) * (b * c)``
         THEN1 metisLib.METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_INNER_CANCEL2 = save_thm
  ("REAL_DIV_INNER_CANCEL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_INNER_CANCEL));

val REAL_DIV_INNER_CANCEL3 = save_thm
  ("REAL_DIV_INNER_CANCEL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_INNER_CANCEL));

val REAL_DIV_OUTER_CANCEL = store_thm
  ("REAL_DIV_OUTER_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((x / y) * (z / x) = z / y)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN (KNOW_TAC ``!a b c d : real. a * b * (c * d) = (a * d) * (c * b)``
         THEN1 metisLib.METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_RINV, REAL_MUL_LID]);

val REAL_DIV_OUTER_CANCEL2 = save_thm
  ("REAL_DIV_OUTER_CANCEL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_OUTER_CANCEL));

val REAL_DIV_OUTER_CANCEL3 = save_thm
  ("REAL_DIV_OUTER_CANCEL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_OUTER_CANCEL));

val REAL_DIV_REFL2 = save_thm
  ("REAL_DIV_REFL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_REFL));

val REAL_DIV_REFL3 = save_thm
  ("REAL_DIV_REFL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_REFL));

val REAL_HALF_BETWEEN = store_thm
  ("REAL_HALF_BETWEEN",
   ``((0:real) <  1 / 2 /\ 1 / 2 <  (1:real)) /\
     ((0:real) <= 1 / 2 /\ 1 / 2 <= (1:real))``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TOTAL, real_lt])
   THEN RW_TAC boolSimps.bool_ss [real_lt]
   THEN MP_TAC (Q.SPEC `2` REAL_LE_LMUL)
   THEN (KNOW_TAC ``0r < 2 /\ ~(2r = 0)``
         THEN1 (REWRITE_TAC [REAL_LT, REAL_INJ] THEN numLib.ARITH_TAC))
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   THEN ONCE_REWRITE_TAC [REAL_MUL_SYM]
   THEN RW_TAC boolSimps.bool_ss [real_div, GSYM REAL_MUL_ASSOC]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_INJ]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL, REAL_LE]
   THEN numLib.ARITH_TAC);

val REAL_THIRDS_BETWEEN = store_thm
  ("REAL_THIRDS_BETWEEN",
   ``((0:real) <  1 / 3 /\ 1 / 3 <  (1:real) /\
      (0:real) <  2 / 3 /\ 2 / 3 <  (1:real)) /\
     ((0:real) <= 1 / 3 /\ 1 / 3 <= (1:real) /\
      (0:real) <= 2 / 3 /\ 2 / 3 <= (1:real))``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TOTAL, real_lt])
   THEN RW_TAC boolSimps.bool_ss [real_lt]
   THEN MP_TAC (Q.SPEC `3` REAL_LE_LMUL)
   THEN (KNOW_TAC ``0r < 3 /\ ~(3r = 0)``
         THEN1 (REWRITE_TAC [REAL_LT, REAL_INJ] THEN numLib.ARITH_TAC))
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   THEN ONCE_REWRITE_TAC [REAL_MUL_SYM]
   THEN RW_TAC boolSimps.bool_ss [real_div, GSYM REAL_MUL_ASSOC]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_INJ]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL, REAL_LE]
   THEN numLib.ARITH_TAC);

val REAL_LE_SUB_CANCEL2 = store_thm
  ("REAL_LE_SUB_CANCEL2",
   ``!x y z : real. x - z <= y - z <=> x <= y``,
   RW_TAC boolSimps.bool_ss [REAL_LE_SUB_RADD, REAL_SUB_ADD]);

(* |- !x y z :real. z - x <= z - y <=> y <= x *)
Theorem REAL_LE_SUB_CANCEL1 =
        REAL_LE_SUB_CANCEL2 |> (Q.SPECL [‘-x’, ‘-y’, ‘-z’])
                            |> (REWRITE_RULE [REAL_SUB_NEG2, REAL_LE_NEG])
                            |> (Q.GENL [‘x’, ‘y’, ‘z’]);

val REAL_ADD_SUB_ALT = store_thm
  ("REAL_ADD_SUB_ALT",
   ``!x y : real. (x + y) - y = x``,
   RW_TAC boolSimps.bool_ss [REAL_EQ_SUB_RADD]);

Theorem INFINITE_REAL_UNIV[simp] :
    INFINITE univ(:real)
Proof
  REWRITE_TAC [] THEN STRIP_TAC THEN
  `FINITE (IMAGE real_of_num univ(:num))`
     by METIS_TAC [SUBSET_FINITE, SUBSET_UNIV] THEN
  FULL_SIMP_TAC (srw_ss()) [INJECTIVE_IMAGE_FINITE]
QED

(* ----------------------------------------------------------------------
   theorems for calculating with the reals; naming scheme taken from
   Joe Hurd's development of the positive reals with an infinity
  ---------------------------------------------------------------------- *)

val ui = markerTheory.unint_def

val add_rat = store_thm(
  "add_rat",
  ``x / y + u / v =
      if y = 0 then unint (x/y) + u/v
      else if v = 0 then x/y + unint (u/v)
      else if y = v then (x + u) / v
      else (x * v + u * y) / (y * v)``,
  SRW_TAC [][ui, REAL_DIV_LZERO, REAL_DIV_ADD] THEN
  SRW_TAC [][REAL_ADD_RAT, REAL_MUL_COMM]);

val add_ratl = store_thm(
  "add_ratl",
  ``x / y + z =
      if y = 0 then unint(x/y) + z
      else (x + z * y) / y``,
  SRW_TAC [][ui, REAL_DIV_LZERO] THEN
  `z = z/1` by SRW_TAC [][] THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  SRW_TAC [][REAL_ADD_RAT, REAL_MUL_COMM]);

val add_ratr = store_thm(
  "add_ratr",
  ``x + y / z =
      if z = 0 then x + unint (y/z)
      else (x * z + y) / z``,
  ONCE_REWRITE_TAC [REAL_ADD_COMM] THEN
  SRW_TAC [][add_ratl, REAL_DIV_LZERO]);

val add_ints = store_thm(
  "add_ints",
  ``(&n + &m = &(n + m)) /\
    (~&n + &m = if n <= m then &(m - n) else ~&(n - m)) /\
    (&n + ~&m = if n < m then ~&(m - n) else &(n - m)) /\
    (~&n + ~&m = ~&(n + m))``,
  `!x y. ~x + y = y + ~x` by SRW_TAC [][REAL_ADD_COMM] THEN
  SRW_TAC [][GSYM REAL_NEG_ADD, GSYM real_sub, REAL_SUB] THEN
  FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss) [] THEN
  `m = n` by SRW_TAC [old_ARITH_ss][] THEN SRW_TAC [][])

val mult_rat = store_thm(
  "mult_rat",
  ``(x / y) * (u / v) =
       if y = 0 then unint (x/y) * (u/v)
       else if v = 0 then (x/y) * unint(u/v)
       else (x * u) / (y * v)``,
  SRW_TAC [][ui, REAL_DIV_LZERO] THEN
  SRW_TAC [][REAL_DIV_LZERO] THEN
  MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN
  Q.EXISTS_TAC `y * v` THEN ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_ENTIRE] THEN
  SRW_TAC [][REAL_DIV_LMUL, REAL_ENTIRE] THEN
  `y * v * (x / y) * (u / v) = (y * (x / y)) * (v * (u / v))`
     by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  SRW_TAC [][REAL_DIV_LMUL]);

val mult_ratl = store_thm(
  "mult_ratl",
  ``(x / y) * z = if y = 0 then unint (x/y) * z else (x * z) / y``,
  SRW_TAC [][ui] THEN
  SRW_TAC [][REAL_DIV_LZERO] THEN
  `z = z / 1` by SRW_TAC [][] THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) THEN
  REWRITE_TAC [mult_rat] THEN SRW_TAC [][]);

val mult_ratr = store_thm(
  "mult_ratr",
  ``x * (y/z) = if z = 0 then x * unint (y/z) else (x * y) / z``,
  CONV_TAC (LAND_CONV (REWR_CONV REAL_MUL_COMM)) THEN
  SRW_TAC [][mult_ratl] THEN SRW_TAC [][ui, REAL_MUL_COMM]);

val mult_ints = store_thm(
  "mult_ints",
  ``(&a * &b = &(a * b)) /\
    (~&a * &b = ~&(a * b)) /\
    (&a * ~&b = ~&(a * b)) /\
    (~&a * ~&b = &(a * b))``,
  SRW_TAC [][REAL_MUL_LNEG, REAL_MUL_RNEG]);

val pow_rat = store_thm(
  "pow_rat",
  ``(x pow 0 = 1) /\
    (0 pow (NUMERAL (BIT1 n)) = 0) /\
    (0 pow (NUMERAL (BIT2 n)) = 0) /\
    (&(NUMERAL a) pow (NUMERAL n) = &(NUMERAL a EXP NUMERAL n)) /\
    (~&(NUMERAL a) pow (NUMERAL n) =
      (if ODD (NUMERAL n) then (~) else (\x.x))
      (&(NUMERAL a EXP NUMERAL n))) /\
    ((x / y) pow n = (x pow n) / (y pow n))``,
  SIMP_TAC bool_ss [pow, NUMERAL_DEF, BIT1, BIT2, POW_ADD,
                    ALT_ZERO, ADD_CLAUSES, REAL_MUL, MULT_CLAUSES,
                    REAL_MUL_RZERO, REAL_OF_NUM_POW, REAL_POW_DIV, EXP] THEN
  Induct_on `n` THEN ASM_SIMP_TAC bool_ss [pow, ODD, EXP] THEN
  Cases_on `ODD n` THEN
  ASM_SIMP_TAC bool_ss [REAL_MUL, REAL_MUL_LNEG,
                        REAL_MUL_RNEG, REAL_NEG_NEG]);

Theorem neg_rat:
  (-(x / y) = -x / y) /\ (x / -y = -x/y)
Proof
  Cases_on ‘y = 0’ >> simp[] >- simp[real_div] >>
  SRW_TAC [][ui] >>
  SRW_TAC [][real_div, GSYM REAL_NEG_INV, REAL_MUL_LNEG, REAL_MUL_RNEG]
QED

Theorem eq_rat:
  (x / y = u / v) <=> if y = 0 then (u = 0) \/ (v = 0)
                    else if v = 0 then x = 0
                    else if y = v then x = u
                    else x * v = y * u
Proof
  SRW_TAC [][ui] THENL [
    simp[real_div],
    simp[real_div],
    METIS_TAC [REAL_DIV_LMUL, REAL_EQ_LMUL],
    `~(y * v = 0)` by SRW_TAC [][REAL_ENTIRE] THEN
    `(x/y = u/v) = ((y * v) * (x/y) = (y * v) * (u/v))`
       by METIS_TAC [REAL_EQ_LMUL2] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `((y * v) * (x/y) = v * (y * (x/y))) /\
     ((y * v) * (u/v) = y * (v * (u/v)))`
       by (CONJ_TAC THEN
           CONV_TAC (AC_CONV(REAL_MUL_ASSOC, REAL_MUL_COMM))) THEN
    ASM_REWRITE_TAC [] THEN SRW_TAC [][REAL_DIV_LMUL] THEN
    SRW_TAC [][REAL_MUL_COMM]
  ]
QED

val eq_ratl = store_thm(
  "eq_ratl",
  ``(x/y = z) <=> if y = 0 then unint(x/y) = z else x = y * z``,
  SRW_TAC [][ui] THEN METIS_TAC [REAL_DIV_LMUL, REAL_EQ_LMUL]);

val eq_ratr = store_thm(
  "eq_ratr",
  ``(z = x/y) <=> if y = 0 then z = unint(x/y) else y * z = x``,
  METIS_TAC [eq_ratl]);

val eq_ints = store_thm(
  "eq_ints",
  ``((&n = &m) <=> (n = m)) /\
    ((~&n = &m) <=> (n = 0) /\ (m = 0)) /\
    ((&n = ~&m) <=> (n = 0) /\ (m = 0)) /\
    ((~&n = ~&m) <=> (n = m))``,
  REWRITE_TAC [REAL_INJ, REAL_EQ_NEG] THEN
  Q_TAC SUFF_TAC `!n m. (&n = ~&m) <=> (n = 0) /\ (m = 0)` THEN1
      METIS_TAC [] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN
    `&n <= ~&m` by METIS_TAC [REAL_LE_ANTISYM] THEN
    `0 <= ~&m` by METIS_TAC [REAL_LE_TRANS, REAL_LE,
                             arithmeticTheory.ZERO_LESS_EQ] THEN
    `m <= 0` by METIS_TAC [REAL_LE, REAL_NEG_GE0] THEN
    `m = 0` by SRW_TAC [old_ARITH_ss][] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][]
  ]);

val REALMUL_AC = CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM))

Theorem div_ratr:
  x / (y / z) = x * z / y
Proof
  Cases_on ‘y = 0’ >- simp[real_div] >>
  Cases_on ‘z = 0’ >- simp[real_div] >>
  SRW_TAC [][ui] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][real_div, REAL_INV_MUL, REAL_INV_EQ_0, REAL_INV_INV] THEN
  REALMUL_AC
QED

val div_ratl = store_thm(
  "div_ratl",
  ``(x/y) / z = if y = 0 then unint(x/y) / z
                else if z = 0 then unint((x/y)/ z)
                else x / (y * z)``,
  SRW_TAC [][ui, real_div, REAL_INV_MUL, REAL_INV_EQ_0, REAL_INV_INV] THEN
  REALMUL_AC);



val div_rat = store_thm(
  "div_rat",
  ``(x/y) / (u/v) =
      if (u = 0) \/ (v = 0) then (x/y) / unint (u/v)
      else if y = 0 then unint(x/y) / (u/v)
      else (x * v) / (y * u)``,
  SRW_TAC [][ui] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][real_div, REAL_INV_MUL, REAL_INV_EQ_0, REAL_INV_INV] THEN
  REALMUL_AC);

val le_rat = store_thm(
  "le_rat",
  ``x / &n <= u / &m <=> if n = 0 then unint(x/0) <= u / &m
                       else if m = 0 then x/ &n <= unint(u/0)
                       else &m * x <= &n * u``,
  SRW_TAC [][ui] THEN
  `0 < m /\ 0 < n` by SRW_TAC [old_ARITH_ss][] THEN
  `0 < &m * &n` by SRW_TAC [][REAL_LT_MUL] THEN
  POP_ASSUM (ASSUME_TAC o MATCH_MP REAL_LE_LMUL) THEN
  POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
  `&m * &n * (x / &n) = &m * (&n * (x/ &n))` by REALMUL_AC THEN
  `&m * &n * (u / &m) = &n * (&m * (u / &m))` by REALMUL_AC THEN
  SRW_TAC [][REAL_DIV_LMUL]);

val le_ratl = save_thm(
  "le_ratl",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``m:num`` |-> ``1n``] le_rat));

val le_ratr = save_thm(
  "le_ratr",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``n:num`` |-> ``1n``] le_rat));

val le_int = store_thm(
  "le_int",
  ``(&n <= &m <=> n <= m) /\
    (~&n <= &m <=> T) /\
    (&n <= ~&m <=> (n = 0) /\ (m = 0)) /\
    (~&n <= ~&m <=> m <= n)``,
  SRW_TAC [][REAL_LE_NEG] THENL [
    MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [][REAL_NEG_LE0],
    Cases_on `m` THEN SRW_TAC [][REAL_NEG_LE0] THEN
    SRW_TAC [][REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [][REAL_NEG_LT0]
  ]);

val lt_rat = store_thm(
  "lt_rat",
  ``x / &n < u / &m <=> if n = 0 then unint(x/0) < u / &m
                      else if m = 0 then x / & n < unint(u/0)
                      else &m * x < &n * u``,
  SRW_TAC [][ui] THEN
  `0 < m /\ 0 < n` by SRW_TAC [old_ARITH_ss][] THEN
  `0 < &m * &n` by SRW_TAC [][REAL_LT_MUL] THEN
  POP_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_LMUL) THEN
  POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
  `&m * &n * (x / &n) = &m * (&n * (x / &n))` by REALMUL_AC THEN
  `&m * &n * (u / &m) = &n * (&m * (u / &m))` by REALMUL_AC THEN
  SRW_TAC [][REAL_DIV_LMUL]);

val lt_ratl = save_thm(
  "lt_ratl",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``m:num`` |-> ``1n``] lt_rat));

val lt_ratr = save_thm(
  "lt_ratr",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``n:num`` |-> ``1n``] lt_rat));

val lt_int = store_thm(
  "lt_int",
  ``(&n < &m <=> n < m) /\
    (~&n < &m <=> ~(n = 0) \/ ~(m = 0)) /\
    (&n < ~&m <=> F) /\
    (~&n < ~&m <=> m < n)``,
  SRW_TAC [][REAL_LT_NEG] THENL [
    Cases_on `m` THEN SRW_TAC [old_ARITH_ss][REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `0` THEN
    SRW_TAC [old_ARITH_ss][REAL_NEG_LE0],
    SRW_TAC [][REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [][REAL_NEG_LE0]
  ]);

(*---------------------------------------------------------------------------*)
(* Floor and ceiling (nums) (NOTE: Their definitions are moved to realax)    *)
(*---------------------------------------------------------------------------*)

Theorem NUM_FLOOR_def   = NUM_FLOOR_def
Theorem NUM_CEILING_def = NUM_CEILING_def

val lem = SIMP_RULE arith_ss [REAL_POS,REAL_ADD_RID]
              (Q.SPECL[`y`,`&n`,`0r`,`1r`] REAL_LTE_ADD2);

val add1_gt_exists = prove(
  ``!y : real. ?n. & (n + 1) > y``,
  GEN_TAC THEN Q.SPEC_THEN `1` MP_TAC REAL_ARCH THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `n` THEN
  SIMP_TAC arith_ss [GSYM REAL_ADD,real_gt,REAL_LT_ADDL,REAL_LT_ADDR] THEN
  METIS_TAC [lem]);

val lt_add1_exists = prove(
  ``!y: real. ?n. y < &(n + 1)``,
  GEN_TAC THEN Q.SPEC_THEN `1` MP_TAC REAL_ARCH THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `n` THEN
  SIMP_TAC bool_ss [GSYM REAL_ADD] THEN METIS_TAC [lem]);

val NUM_FLOOR_LE = store_thm
("NUM_FLOOR_LE",
  ``0 <= x ==> &(NUM_FLOOR x) <= x``,
  SRW_TAC [][NUM_FLOOR_def] THEN
  LEAST_ELIM_TAC THEN
  SRW_TAC [][add1_gt_exists] THEN
  Cases_on `n` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [old_ARITH_ss] [real_gt, REAL_NOT_LT, ADD1]);

val NUM_FLOOR_LE2 = store_thm
("NUM_FLOOR_LE2",
 ``0 <= y ==> (x <= NUM_FLOOR y <=> &x <= y)``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][lt_add1_exists, real_gt,REAL_NOT_LT, EQ_IMP_THM]
  THENL [
    Cases_on `n` THENL [
      FULL_SIMP_TAC (srw_ss()) [],
      FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
      FULL_SIMP_TAC (bool_ss ++ old_ARITH_ss)
                    [ADD1, GSYM REAL_ADD, GSYM REAL_LE] THEN
      METIS_TAC [REAL_LE_TRANS]
    ],
    `&x < &(n + 1):real` by PROVE_TAC [REAL_LET_TRANS] THEN
    FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss) []
  ]);

Theorem NUM_FLOOR_MONO :
    !x y. 0 <= x /\ 0 <= y /\ x <= y ==> NUM_FLOOR x <= NUM_FLOOR y
Proof
    rpt STRIP_TAC
 >> ASM_SIMP_TAC std_ss [NUM_FLOOR_LE2]
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘x’
 >> ASM_SIMP_TAC std_ss [NUM_FLOOR_LE]
QED

val NUM_FLOOR_LET = store_thm
("NUM_FLOOR_LET",
 ``(NUM_FLOOR x <= y) <=> (x < &y + 1)``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][lt_add1_exists, real_gt,REAL_NOT_LT, EQ_IMP_THM]
  THENL [
    FULL_SIMP_TAC bool_ss [GSYM REAL_LE,GSYM REAL_ADD] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `&n + 1` THEN SRW_TAC [][],
    Cases_on `n` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
    FULL_SIMP_TAC (bool_ss ++ old_ARITH_ss) [ADD1] THEN
    STRIP_TAC THEN
    `&(n' + 1) < &(y + 1):real` by METIS_TAC [REAL_LET_TRANS] THEN
    FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss) []
  ]);

Theorem NUM_FLOOR_LT :
    !x :real. x - 1 < &(NUM_FLOOR x)
Proof
    RW_TAC std_ss [REAL_LT_SUB_RADD, GSYM NUM_FLOOR_LET]
QED

val NUM_FLOOR_DIV = store_thm
("NUM_FLOOR_DIV",
  ``0 <= x /\ 0 < y ==> &(NUM_FLOOR (x / y)) * y <= x``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][add1_gt_exists] THEN
  Cases_on `n` THEN1 SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [old_ARITH_ss] [real_gt,REAL_NOT_LT,ADD1,REAL_LE_RDIV_EQ]);

val NUM_FLOOR_DIV_LOWERBOUND = store_thm
("NUM_FLOOR_DIV_LOWERBOUND",
 ``0 <= x:real /\ 0 < y:real ==> x < &(NUM_FLOOR (x/y) + 1) * y ``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][add1_gt_exists] THEN Cases_on `n` THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][real_gt, REAL_LT_LDIV_EQ]);

val NUM_FLOOR_BASE = Q.store_thm("NUM_FLOOR_BASE",
  `!r. r < 1 ==> (NUM_FLOOR r = 0)`,
  SRW_TAC [] [NUM_FLOOR_def]
  THEN numLib.LEAST_ELIM_TAC
  THEN SRW_TAC [] []
  THEN1 (Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC std_ss [real_gt])
  THEN Cases_on `n = 0`
  THEN1 ASM_REWRITE_TAC []
  THEN `0 < n` by DECIDE_TAC
  THEN RES_TAC
  THEN FULL_SIMP_TAC arith_ss [real_gt]
  )

val lem =
  metisLib.METIS_PROVE [REAL_LT_01, REAL_LET_TRANS]
    ``!r: real. r <= 0 ==> r < 1``

val NUM_FLOOR_NEG = Q.prove(
  `NUM_FLOOR (~real_of_num n) = 0`,
  MATCH_MP_TAC NUM_FLOOR_BASE
  THEN MATCH_MP_TAC lem
  THEN REWRITE_TAC [REAL_NEG_LE0, REAL_POS])

val NUM_FLOOR_NEGQ = Q.prove(
  `0 < m ==> (NUM_FLOOR (~real_of_num n / real_of_num m) = 0)`,
  ONCE_REWRITE_TAC [GSYM REAL_LT]
  THEN STRIP_TAC
  THEN MATCH_MP_TAC NUM_FLOOR_BASE
  THEN ASM_SIMP_TAC std_ss [REAL_LT_LDIV_EQ, REAL_MUL_LID, lt_int]
  THEN FULL_SIMP_TAC arith_ss [REAL_LT]
  )

val NUM_FLOOR_EQNS = store_thm(
 "NUM_FLOOR_EQNS",
  ``(NUM_FLOOR (real_of_num n) = n) /\
    (NUM_FLOOR (~real_of_num n) = 0) /\
    (0 < m ==> (NUM_FLOOR (real_of_num n / real_of_num m) = n DIV m)) /\
    (0 < m ==> (NUM_FLOOR (~real_of_num n / real_of_num m) = 0))``,
  REWRITE_TAC [NUM_FLOOR_NEG, NUM_FLOOR_NEGQ]
  THEN SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THENL [
    SIMP_TAC (srw_ss()) [real_gt, REAL_LT] THEN
    CONJ_TAC THENL
     [Q.EXISTS_TAC `n` THEN RW_TAC old_arith_ss [],
      Cases THEN FULL_SIMP_TAC old_arith_ss []
        THEN STRIP_TAC
        THEN Q.PAT_X_ASSUM `$! M` (MP_TAC o Q.SPEC `n''`)
        THEN RW_TAC old_arith_ss []],
    ASM_SIMP_TAC (srw_ss()) [real_gt, REAL_LT_LDIV_EQ] THEN
    CONJ_TAC THENL [
      Q.EXISTS_TAC `n` THEN
      SRW_TAC [][RIGHT_ADD_DISTRIB] THEN
      MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
      Q.EXISTS_TAC `n * m` THEN
      SRW_TAC [old_ARITH_ss][] THEN
      CONV_TAC (LAND_CONV (REWR_CONV (GSYM MULT_RIGHT_1))) THEN
      SRW_TAC [old_ARITH_ss][],
      Q.HO_MATCH_ABBREV_TAC
         `!p:num. (!i. i < p ==> ~(n < (i + 1) * m)) /\ n < (p + 1) * m
                   ==> (p = n DIV m)` THEN
      REPEAT STRIP_TAC THEN
      CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
      MATCH_MP_TAC DIV_UNIQUE THEN
      `(p = 0) \/ (?p0. p = SUC p0)`
         by PROVE_TAC [arithmeticTheory.num_CASES] THEN
      FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss)
                    [ADD1,RIGHT_ADD_DISTRIB] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `p0` MP_TAC) THEN
      SRW_TAC [old_ARITH_ss][NOT_LESS] THEN
      Q.EXISTS_TAC `n - (m + p0 * m)` THEN
      SRW_TAC [old_ARITH_ss][]
    ]
  ]);

val NUM_FLOOR_LOWER_BOUND = store_thm(
  "NUM_FLOOR_LOWER_BOUND",
  ``(x:real < &n) <=> (NUM_FLOOR(x+1) <= n)``,
  MP_TAC (Q.INST [`x` |-> `x + 1`, `y` |-> `n`] NUM_FLOOR_LET) THEN
  SIMP_TAC (srw_ss()) []);

val NUM_FLOOR_upper_bound = store_thm(
  "NUM_FLOOR_upper_bound",
  ``(&n <= x:real) <=> (n < NUM_FLOOR(x + 1))``,
  MP_TAC (AP_TERM negation NUM_FLOOR_LOWER_BOUND) THEN
  PURE_REWRITE_TAC [REAL_NOT_LT, NOT_LESS_EQUAL,IMP_CLAUSES]);

Theorem NUM_FLOOR_upper_bound' :
    !x n. 1 < x ==> (n < NUM_FLOOR x <=> &n <= x - 1)
Proof
    rpt STRIP_TAC
 >> rw [NUM_FLOOR_upper_bound, REAL_SUB_ADD]
QED

Theorem NUM_FLOOR_POS :
    !x. 0 < NUM_FLOOR x <=> 1 <= x
Proof
    Q.X_GEN_TAC ‘x’
 >> EQ_TAC
 >- (DISCH_TAC >> CCONTR_TAC \\
    ‘x < 1’ by rw [real_lt] \\
    ‘flr x = 0’ by rw [NUM_FLOOR_BASE] \\
     fs [])
 >> DISCH_TAC
 >> ‘x = 1 \/ 1 < x’ by PROVE_TAC [REAL_LE_LT]
 >- rw [NUM_FLOOR_EQNS]
 >> rw [NUM_FLOOR_upper_bound', REAL_SUB_LE]
QED

Theorem NUM_FLOOR_lower_bound :
    !x. 1 <= x ==> x / 2 < &NUM_FLOOR(x)
Proof
    rpt STRIP_TAC
 >> SRW_TAC [] [NUM_FLOOR_def]
 >> numLib.LEAST_ELIM_TAC
 >> RW_TAC arith_ss [add1_gt_exists, real_gt]
 >> Cases_on ‘n = 0’ >- (FULL_SIMP_TAC arith_ss [] \\
                         PROVE_TAC [REAL_LET_ANTISYM])
 >> ‘0 < n’ by DECIDE_TAC
 >> ‘0 < (2 :real)’ by SRW_TAC [][]
 >> Cases_on ‘n = 1’
 >- (FULL_SIMP_TAC arith_ss [REAL_LT_LDIV_EQ, REAL_MUL_LID])
 >> ‘1 < n’ by DECIDE_TAC
 >> RW_TAC arith_ss [REAL_LT_LDIV_EQ]
 >> MATCH_MP_TAC REAL_LT_TRANS
 >> Q.EXISTS_TAC ‘&(n + 1)’
 >> RW_TAC arith_ss [REAL_MUL, REAL_LT, real_of_num]
QED

Theorem NUM_FLOOR_MUL_LOWERBOUND : (* cf. NUM_FLOOR_DIV_LOWERBOUND *)
    !(n :num) (x :real). 1 < n /\ 1 <= x ==> x < &(n * flr x)
Proof
    RW_TAC std_ss [GSYM REAL_MUL]
 >> ‘0 <= x’ by PROVE_TAC [REAL_LE_01, REAL_LE_TRANS]
 >> MATCH_MP_TAC REAL_LTE_TRANS
 >> Q.EXISTS_TAC ‘2 * &flr x’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_LE_RMUL_IMP \\
     RW_TAC arith_ss [REAL_LE])
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> ‘0 < (2 :real)’ by SRW_TAC [][]
 >> ASM_SIMP_TAC std_ss [GSYM REAL_LT_LDIV_EQ]
 >> MATCH_MP_TAC NUM_FLOOR_lower_bound
 >> ASM_REWRITE_TAC []
QED

val NUM_CEILING_NUM_FLOOR = Q.store_thm("NUM_CEILING_NUM_FLOOR",
  `!r. NUM_CEILING r =
       let n = NUM_FLOOR r in
       if r <= 0 \/ (r = real_of_num n) then n else n + 1`,
  SRW_TAC [boolSimps.LET_ss] [NUM_CEILING_def, NUM_FLOOR_BASE]
  THEN1 (IMP_RES_TAC lem
         THEN ASM_SIMP_TAC std_ss [NUM_FLOOR_BASE]
         THEN numLib.LEAST_ELIM_TAC
         THEN CONJ_TAC
         THEN1 METIS_TAC []
         THEN SRW_TAC [] []
         THEN FULL_SIMP_TAC std_ss [REAL_NOT_LE]
         THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
         THEN `0 < n` by DECIDE_TAC
         THEN METIS_TAC [REAL_LTE_ANTSYM])
  THEN1 (POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th])))
         THEN SRW_TAC [] [NUM_FLOOR_LET, NUM_FLOOR_def, real_gt])
  THEN FULL_SIMP_TAC std_ss [REAL_NOT_LE]
  THEN numLib.LEAST_ELIM_TAC
  THEN CONJ_TAC
  THEN1 (Q.EXISTS_TAC `flr r + 1`
         THEN Cases_on `r < 1`
         THEN1 SRW_TAC [] [NUM_FLOOR_BASE, REAL_LT_IMP_LE]
         THEN `0 <= r` by METIS_TAC [REAL_NOT_LT, REAL_LE_01, REAL_LE_TRANS]
         THEN METIS_TAC
              [NUM_FLOOR_DIV_LOWERBOUND
               |> Q.INST [`y` |-> `1r`]
               |> SIMP_RULE (srw_ss()) [],
              REAL_LT_IMP_LE])
  THEN SRW_TAC [] []
  THEN Q.PAT_X_ASSUM `x <> y` MP_TAC
  THEN SIMP_TAC std_ss [NUM_FLOOR_def]
  THEN numLib.LEAST_ELIM_TAC
  THEN CONJ_TAC
  THEN1 (Q.EXISTS_TAC `n`
         THEN ASM_SIMP_TAC std_ss [real_gt, GSYM REAL_ADD, REAL_LT_ADD1])
  THEN SRW_TAC [] [real_gt]
  THEN FULL_SIMP_TAC std_ss [REAL_NOT_LE, REAL_NOT_LT]
  THEN Cases_on `n' + 1 < n`
  THEN1 METIS_TAC [REAL_LT_ANTISYM]
  THEN Cases_on `n' + 1 = n`
  THEN1 ASM_REWRITE_TAC []
  THEN `n < n' + 1` by DECIDE_TAC
  THEN Cases_on `n = 0`
  THEN FULL_SIMP_TAC std_ss []
  THEN1 METIS_TAC [REAL_LET_ANTISYM]
  THEN `n - 1 < n'` by DECIDE_TAC
  THEN RES_TAC
  THEN FULL_SIMP_TAC arith_ss []
  THEN REV_FULL_SIMP_TAC std_ss [DECIDE ``n <> 0n ==> (n - 1 + 1 = n)``]
  THEN IMP_RES_TAC REAL_LE_ANTISYM
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN `n' - 1 < n'` by DECIDE_TAC
  THEN RES_TAC
  THEN FULL_SIMP_TAC arith_ss []
  )

(*---------------------------------------------------------------------------*)
(* Ceiling function                                                          *)
(*---------------------------------------------------------------------------*)

val LE_NUM_CEILING = store_thm
("LE_NUM_CEILING",
 ``!x. x <= &(clg x)``,
 RW_TAC std_ss [NUM_CEILING_def]
   THEN numLib.LEAST_ELIM_TAC
   THEN Q.SPEC_THEN `1` MP_TAC REAL_ARCH
   THEN SIMP_TAC (srw_ss()) []
   THEN METIS_TAC [REAL_LT_IMP_LE]);

Theorem NUM_CEILING_BASE:
    !x. x <= 0 ==> clg x = 0
Proof
    metis_tac[NUM_FLOOR_BASE, REAL_LT_ADD1, REAL_ADD_LID,
      REWRITE_RULE [boolTheory.LET_THM] NUM_CEILING_NUM_FLOOR]
QED

val NUM_CEILING_LE = store_thm
("NUM_CEILING_LE",
 ``!x n. x <= &n ==> clg(x) <= n``,
 RW_TAC std_ss [NUM_CEILING_def]
   THEN numLib.LEAST_ELIM_TAC
   THEN METIS_TAC [NOT_LESS_EQUAL]);

Theorem NUM_CEILING_UPPER_BOUND :
    !x. 0 <= x ==> &(clg x) < x + 1
Proof
    RW_TAC std_ss [NUM_CEILING_def]
 >> numLib.LEAST_ELIM_TAC
 >> REWRITE_TAC [SIMP_REAL_ARCH]
 >> RW_TAC arith_ss []
 >> FULL_SIMP_TAC arith_ss [GSYM real_lt]
 >> Q.PAT_X_ASSUM `!m. P` (MP_TAC o Q.SPEC `n-1`)
 >> RW_TAC arith_ss []
 >> Cases_on `n = 0` >- METIS_TAC [REAL_LET_ADD2, REAL_LT_01, REAL_ADD_RID]
 >> `0 < n` by RW_TAC arith_ss []
 >> `&(n - 1) < x:real` by RW_TAC arith_ss []
 >> `0 <= n-1` by RW_TAC arith_ss []
 >> `0:real <= (&(n-1))` by SRW_TAC[][]
 >> `0 < x` by METIS_TAC [REAL_LET_TRANS]
 >> Cases_on `n = 1`
 >- METIS_TAC [REAL_LE_REFL, REAL_ADD_RID, REAL_LTE_ADD2, REAL_ADD_COMM]
 >> `0 <> n-1` by RW_TAC arith_ss []
 >> `&n - 1 < x` by RW_TAC arith_ss [REAL_SUB]
 >> FULL_SIMP_TAC std_ss [REAL_LT_SUB_RADD]
QED

(* backward compatible name of NUM_CEILING_UPPER_BOUND *)
Theorem CLG_UBOUND = NUM_CEILING_UPPER_BOUND

Theorem NUM_CEILING_NUM[simp]:
  clg (&n) = n
Proof
  simp[NUM_CEILING_def]
QED

Theorem NUM_CEILING_MONO:
  !r s. r <= s ==> clg r <= clg s
Proof
  rpt strip_tac >> irule NUM_CEILING_LE >> simp[NUM_CEILING_def] >>
  numLib.LEAST_ELIM_TAC >> simp[SIMP_REAL_ARCH] >>
  metis_tac[REAL_LE_TRANS]
QED

(* ----------------------------------------------------------------------
    nonzerop : real -> real

    a helper for normalisation: x * inv x = nonzerop x
   ---------------------------------------------------------------------- *)

Definition nonzerop_def:
  nonzerop r = if r = 0r then 0r else 1r
End
Overload NZ = “nonzerop”

Theorem nonzerop_mulXX[simp]:
  nonzerop r * nonzerop r = nonzerop r
Proof
  rw[nonzerop_def]
QED

Theorem nonzerop_0[simp]:
  nonzerop 0 = 0
Proof
  rw[nonzerop_def]
QED

Theorem nonzerop_NUMERAL[simp]:
  (NZ (&NUMERAL (BIT1 n)) = 1) /\ (NZ (&NUMERAL (BIT2 n)) = 1)
Proof
  REWRITE_TAC[NUMERAL_DEF, BIT1, BIT2, ALT_ZERO, ADD_CLAUSES,
              nonzerop_def, REAL_OF_NUM_EQ, NOT_SUC]
QED

Theorem REAL_INV_nonzerop:
  (x * inv x = nonzerop x) /\ (inv x * x = nonzerop x)
Proof
  rw[nonzerop_def, REAL_MUL_LINV, REAL_MUL_RINV]
QED

Theorem nonzerop_mult[simp]:
   nonzerop (x * y) = nonzerop x * nonzerop y
Proof
  rw[nonzerop_def]
QED

Theorem nonzerop_nonzerop[simp]:
  NZ (NZ x) = NZ x
Proof
  rw[nonzerop_def] >> fs[]
QED

Theorem nonzerop_EQ0[simp]:
  (NZ r = 0) <=> (r = 0)
Proof
  rw[nonzerop_def]
QED

Theorem nonzerop_EQ1_I[simp]:
  r <> 0 ==> (nonzerop r = 1)
Proof
  rw[nonzerop_def]
QED

Theorem nonzerop_inv[simp]:
  nonzerop (inv x) = nonzerop x
Proof
  rw[nonzerop_def] >> fs[REAL_INV_EQ_0, REAL_INV_0]
QED

Theorem pow_eq0[simp]:
  (x pow y = 0) <=> (x = 0) /\ 0 < y
Proof
  Induct_on ‘y’ >> simp[pow, EQ_IMP_THM, DISJ_IMP_THM]
QED

Theorem nonzerop_pow[simp]:
  nonzerop (x pow n) = nonzerop x pow n
Proof
  simp[nonzerop_def, pow] >> Cases_on ‘x = 0’ >> simp[] >> rw[] >>
  Cases_on ‘n’ >> simp[pow]
QED

Theorem nonzerop_nonzero_pow:
  0 < n ==> (nonzerop x pow n = nonzerop x)
Proof
  Induct_on ‘n’ >> simp[pow] >> Cases_on ‘0 < n’ >> fs[]
QED

Theorem pow_inv_mul:
  0 < n ==> (x pow n * inv x = x pow (n - 1) * NZ x)
Proof
  Cases_on ‘n’ >> simp[pow] >>
  metis_tac[REAL_MUL_ASSOC, REAL_MUL_COMM, REAL_INV_nonzerop]
QED

Theorem POW_0':
  0 < n ==> (0 pow n = 0)
Proof
  Cases_on ‘n’ >> simp[POW_0]
QED

Theorem pow_inv_mul_powlt:
  !x m n. m < n ==> (x pow m * inv x pow n = inv x pow (n - m))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘d = n - m’ >> ‘0 < d’ by simp[Abbr‘d’] >>
  ‘n = m + d’ by simp[Abbr‘d’] >>
  Cases_on ‘x = 0’ >>
  simp[nonzerop_EQ1_I, REAL_INV_0, REAL_POW_INV, REAL_POW_ADD,
       REAL_INV_MUL, POW_0'] >>
  qmatch_abbrev_tac ‘XM * (XDi * inv XM) = XDi’ >>
  ‘XM * (XDi * inv XM) = (XM * inv XM) * XDi’
    by simp[simpLib.AC REAL_MUL_ASSOC REAL_MUL_COMM] >>
  ‘XM <> 0’ by simp[Abbr‘XM’] >>
  simp[REAL_MUL_RINV]
QED

Theorem pow_inv_mul_invlt:
  !x m n. n < m ==> (x pow m * inv x pow n = x pow (m - n))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘d = m - n’ >> ‘0 < d /\ (m = n + d)’ by simp[Abbr‘d’] >>
  Cases_on ‘x = 0’ >>
  simp[nonzerop_EQ1_I, REAL_INV_0, REAL_POW_INV, REAL_POW_ADD,
       REAL_INV_MUL, POW_0'] >>
  ‘x pow n <> 0’ by simp[] >>
  metis_tac[REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_MUL_RID]
QED

Theorem pow_inv_eq:
  x pow m * inv x pow m = NZ x pow m
Proof
  Cases_on ‘x = 0’ >> simp[nonzerop_EQ1_I, REAL_POW_INV, REAL_MUL_RINV] >>
  Cases_on ‘m’ >> simp[pow]
QED

Theorem ZERO_LT_POW[simp]:
  (0 < x pow NUMERAL (BIT2 n) <=> x <> 0) /\
  (0 < x pow NUMERAL (BIT1 n) <=> 0 < x)
Proof
  REWRITE_TAC[NUMERAL_DEF, BIT2, BIT1, ADD_CLAUSES] >>
  simp[EQ_IMP_THM] >> rpt strip_tac
  >- fs[pow]
  >- (‘SUC (SUC (2 * n)) = 2 * (n + 1)’ by simp[] >>
      simp[GSYM REAL_POW_POW, POW_2, REAL_POW_LT])
  >- (fs[pow] >> Cases_on ‘x = 0’ >> fs[] >>
      ‘0 < x pow (2 * n)’ suffices_by metis_tac[REAL_LT_RMUL_0] >>
      simp[GSYM REAL_POW_POW, POW_2, REAL_POW_LT]) >>
  simp[pow] >> ‘0 < x pow (2 * n)’ suffices_by metis_tac[REAL_LT_RMUL_0] >>
  simp[GSYM REAL_POW_POW, POW_2, REAL_POW_LT]
QED

Theorem REAL_INV_LT0[simp]:
  inv x < 0 <=> x < 0
Proof
  PURE_ONCE_REWRITE_TAC[DECIDE “(p <=> q) <=> (~p <=> ~q)”] >>
  PURE_REWRITE_TAC [REAL_NOT_LT] >> simp[]
QED

Theorem REAL_POW_POS:
  0 < x pow n <=> (n = 0) \/ 0 < x \/ x < 0 /\ EVEN n
Proof
  Induct_on ‘n’ >> simp[pow] >> eq_tac >> simp[EVEN] >>
  Cases_on ‘EVEN n’ >> fs[]
  >- (Cases_on ‘0 < x pow n’ >> simp[REAL_LT_RMUL_0] >> rfs[] >>
      fs[REAL_NOT_LT] >> ‘x = 0’ by metis_tac[REAL_LE_ANTISYM] >>
      simp[])
  >- (Cases_on ‘0 < x pow n’ >> simp[REAL_LT_RMUL_0] >> rfs[] >>
      fs[REAL_NOT_LT] >> fs[REAL_LE_LT])
  >- simp[REAL_LT_LMUL_0]
  >- (strip_tac >> simp[REAL_LT_LMUL_0] >>
      Cases_on ‘0 < x pow n’ >> simp[REAL_LT_RMUL_0] >> rfs[] >> fs[] >>
      fs[REAL_NOT_LT] >> fs[REAL_LE_LT] >> fs[] >> rfs[] >>
      metis_tac[REAL_NEG_GT0, REAL_NEG_MUL2, REAL_LT_MUL])
QED

(* cf. realaxTheory.REAL_POW_NEG (different statements) *)
Theorem REAL_POW_NEG[simp] :
  x pow n < 0 <=> ODD n /\ x < 0
Proof
  ‘!r. r < 0 <=> r <> 0 /\ ~(0 < r)’
    by metis_tac[REAL_LT_NEGTOTAL,REAL_NEG_GT0,REAL_LT_REFL,REAL_LT_ANTISYM] >>
  pop_assum (fn th => simp[SimpLHS, th]) >>
  simp[REAL_POW_POS] >> csimp[REAL_NOT_LT, arithmeticTheory.ODD_EVEN] >>
  csimp[REAL_LE_LT] >>
  metis_tac[REAL_LT_REFL, arithmeticTheory.EVEN, REAL_LT_ANTISYM]
QED

(* !x n. -x pow n = if EVEN n then x pow n else -(x pow n) *)
Theorem REAL_POW_NEG2 = realaxTheory.REAL_POW_NEG;

Theorem REAL_POW_GE0[simp]:
  0 <= x pow n <=> 0 <= x \/ EVEN n
Proof
  PURE_ONCE_REWRITE_TAC[DECIDE “(p <=> q) <=> (~p <=> ~q)”] >>
  PURE_REWRITE_TAC[REAL_NOT_LE] >>
  simp[REAL_POW_NEG, REAL_NOT_LE, arithmeticTheory.ODD_EVEN, CONJ_COMM]
QED

(* recovered from transc.ml *)
Theorem REAL_POW_LE :
    !x n. 0 <= x ==> 0 <= x pow n
Proof
    RW_TAC std_ss [REAL_POW_GE0]
QED

Theorem REAL_POW_LE0:
  x pow n <= 0 <=> 0 < n /\ (x = 0) \/ x < 0 /\ ODD n
Proof
  PURE_ONCE_REWRITE_TAC[DECIDE “(p <=> q) <=> (~p <=> ~q)”] >>
  PURE_REWRITE_TAC[REAL_NOT_LE] >>
  simp[REAL_POW_POS] >>
  csimp[arithmeticTheory.ODD_EVEN, REAL_NOT_LT, REAL_LE_LT] >>
  Cases_on ‘n = 0’ >> simp[] >> Cases_on ‘0 < x’ >> csimp[]
  >- (strip_tac >> fs[]) >>
  fs[REAL_NOT_LT, REAL_LE_LT] >> metis_tac[REAL_LT_REFL]
QED

Theorem ZERO_LT_invx[simp]:
  0 < inv x pow n <=> 0 < x pow n
Proof
  simp[REAL_POW_POS]
QED

Theorem REAL_ABS_LE0:
  !v.
   (abs v <= 0) <=> (v = 0)
Proof
  fs[ABS_BOUNDS] >> rpt strip_tac >> EQ_TAC >> strip_tac
  >> metis_tac[REAL_LE_ANTISYM]
QED

Theorem REAL_INV_LE_ANTIMONO:
  ! x y.
    0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)
Proof
  rpt strip_tac
  >> `inv x < inv y <=> y < x`
    by (match_mp_tac REAL_INV_LT_ANTIMONO >> fs [])
  >> EQ_TAC
  >> fs [REAL_LE_LT]
  >> strip_tac
  >> fs [REAL_INV_INJ]
QED

(* NOTE: ‘0 < x’ is not necessary *)
Theorem REAL_INV_LE_ANTIMONO_IMPR:
  ! x y.
    0 < x /\ 0 < y /\ y <= x ==> inv x <= inv y
Proof
  rpt strip_tac >> fs[REAL_INV_LE_ANTIMONO]
QED

(* for HOL-Light compatibility *)
Theorem REAL_LE_INV2 :
    !x y. (&0:real) < x /\ x <= y ==> inv(y) <= inv(x)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC REAL_INV_LE_ANTIMONO_IMPR
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC REAL_LTE_TRANS
 >> Q.EXISTS_TAC ‘x’
 >> ASM_REWRITE_TAC []
QED

Theorem REAL_INV_LE_1 :
    !x:real. &1 <= x ==> inv(x) <= &1
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]
QED

Theorem REAL_INV_1_LE :
    !x:real. &0 < x /\ x <= &1 ==> &1 <= inv(x)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]
QED

(* NOTE: ‘y < 0’ is not necessary *)
Theorem REAL_INV_LE_ANTIMONO_IMPL:
  ! x y.
    x < 0 /\ y < 0 /\ y <= x ==> inv x <= inv y
Proof
  rpt strip_tac
  >> once_rewrite_tac [GSYM REAL_LE_NEG]
  >> `- inv y = inv (- y)` by (irule REAL_NEG_INV >> CCONTR_TAC >> fs[])
  >> `- inv x = inv (- x)` by (irule REAL_NEG_INV >> CCONTR_TAC >> fs[])
  >> ntac 2(FIRST_X_ASSUM (fn thm => once_rewrite_tac [ thm]))
  >> irule REAL_INV_LE_ANTIMONO_IMPR >> fs[]
QED

Theorem REAL_LE_LMUL_NEG_IMP:
  ! a b c.
    a <= 0 /\ b <= c ==> a * c <= a * b
Proof
  rpt strip_tac
  >> once_rewrite_tac [SYM (SPEC ``a:real`` REAL_NEG_NEG)]
  >> once_rewrite_tac [SYM (SPECL [``a:real``, ``c:real``] REAL_MUL_LNEG)]
  >> once_rewrite_tac [REAL_LE_NEG]
  >> `0 <= - (a:real)`
    by (once_rewrite_tac [SYM (SPEC ``-(a:real)`` REAL_NEG_LE0)]
        >> fs [REAL_NEG_NEG])
  >> match_mp_tac REAL_LE_LMUL_IMP >> fs[]
QED

Theorem REAL_DIV_ZERO:
  !a b.
    (a / b = 0) <=> ((a = 0) \/ (b = 0))
Proof
  rpt strip_tac \\ EQ_TAC \\ fs[REAL_DIV_LZERO, real_div]
QED

(* cf. REAL_POW_MONO *)
Theorem REAL_POW_ANTIMONO :
    !(m :num) n (x :real). 0 < x /\ x <= 1 /\ m <= n ==> x pow n <= x pow m
Proof
    rpt STRIP_TAC
 >> KNOW_TAC “(x :real) pow n <= x pow m <=> inv (x pow m) <= inv (x pow n)”
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC REAL_INV_LE_ANTIMONO \\
     rw [REAL_POW_POS])
 >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
 >> ‘x <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ASM_SIMP_TAC std_ss [POW_INV]
 >> MATCH_MP_TAC REAL_POW_MONO
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC REAL_INV_1_LE
 >> ASM_REWRITE_TAC []
QED

(* cf. REAL_POW_MONO_LT *)
Theorem REAL_POW_ANTIMONO_LT :
    !(m :num) n (x :real). 0 < x /\ x < 1 /\ m < n ==> x pow n < x pow m
Proof
    rpt STRIP_TAC
 >> KNOW_TAC “(x :real) pow n < x pow m <=> inv (x pow m) < inv (x pow n)”
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC REAL_INV_LT_ANTIMONO \\
     rw [REAL_POW_POS])
 >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
 >> ‘x <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ASM_SIMP_TAC std_ss [POW_INV]
 >> MATCH_MP_TAC REAL_POW_MONO_LT
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC REAL_INV_LT1
 >> ASM_REWRITE_TAC []
QED

(* cf. REAL_LT_RDIV *)
Theorem REAL_LE_RDIV_CANCEL :
    !x y (z :real). 0 < z ==> (x / z <= y / z <=> x <= y)
Proof
    rpt STRIP_TAC
 >> ‘0 < inv z’ by PROVE_TAC [REAL_INV_POS]
 >> ASM_SIMP_TAC bool_ss [real_div, REAL_LE_RMUL]
QED

(* ------------------------------------------------------------------------- *)
(* More variants of the Archimedian property and useful consequences.        *)
(* ------------------------------------------------------------------------- *)

Theorem REAL_POW_LBOUND :
    !x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n
Proof
    Q.X_GEN_TAC ‘x’
 >> SIMP_TAC arith_ss [RIGHT_FORALL_IMP_THM]
 >> DISCH_TAC
 >> INDUCT_TAC
 >> REWRITE_TAC [pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL]
 >> REWRITE_TAC [GSYM REAL_OF_NUM_SUC]
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘(&1 + x) * (&1 + &n * x)’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_LE_LMUL_IMP >> ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> ASM_REWRITE_TAC [REAL_LE_01, REAL_LE_ADDR])
 >> SIMP_TAC arith_ss [REAL_ADD_RDISTRIB, REAL_ADD_LDISTRIB, REAL_ADD_ASSOC,
                       REAL_MUL_LID, REAL_MUL_RID]
 >> REWRITE_TAC [GSYM REAL_ADD_ASSOC]
 >> MATCH_MP_TAC REAL_LE_LADD_IMP
 >> REWRITE_TAC [REAL_ADD_ASSOC, REAL_LE_ADDR]
 >> MATCH_MP_TAC REAL_LE_MUL >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC REAL_LE_MUL
 >> ASM_SIMP_TAC arith_ss [real_of_num, REAL_OF_NUM_LE]
QED

Theorem REAL_ARCH_POW :
    !x y. &1 < x ==> ?n. y < x pow n
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPEC ‘x - &1’ REAL_ARCH)
 >> ASM_REWRITE_TAC [REAL_SUB_LT]
 >> DISCH_THEN (MP_TAC o SPEC ``y:real``)
 >> HO_MATCH_MP_TAC MONO_EXISTS
 >> Q.X_GEN_TAC ‘n’
 >> DISCH_TAC
 >> MATCH_MP_TAC REAL_LTE_TRANS
 >> Q.EXISTS_TAC ‘&1 + &n * (x - &1)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC REAL_LT_TRANS \\
     Q.EXISTS_TAC ‘1 + y’ \\
     reverse CONJ_TAC >- (ASM_REWRITE_TAC [REAL_LT_LADD]) \\
     REWRITE_TAC [REAL_LT_ADDL, REAL_LT_01])
 >> MATCH_MP_TAC (REWRITE_RULE [REAL_SUB_ADD2]
                               (Q.SPECL [‘x - 1’, ‘n’] REAL_POW_LBOUND))
 >> REWRITE_TAC [REAL_SUB_LE]
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> ASM_REWRITE_TAC []
QED

Theorem REAL_ARCH_POW_INV :
    !x:real y. &0 < y /\ x < &1 ==> ?n. x pow n < y
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘0 < x’)
 >- ASM_MESON_TAC[POW_1, REAL_LET_TRANS, REAL_NOT_LT]
 >> KNOW_TAC “inv(&1) < inv(x:real)”
 >- (MATCH_MP_TAC REAL_LT_INV >> ASM_REWRITE_TAC [])
 >> REWRITE_TAC [REAL_INV1]
 >> DISCH_THEN (MP_TAC o (Q.SPEC ‘inv y’) o (MATCH_MP REAL_ARCH_POW))
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘n’
 >> GEN_REWR_TAC BINOP_CONV [GSYM REAL_INV_INV]
 >> ASM_SIMP_TAC std_ss [GSYM REAL_POW_INV, REAL_LT_INV_EQ, REAL_LT_INV]
QED

Theorem REAL_ARCH_POW2 : (* was: REAL_ARCH_POW *)
    !x. ?n. x < &2 pow n
Proof
    SIMP_TAC arith_ss[REAL_ARCH_POW, REAL_LT]
QED

(* moved here from util_probTheory, needed below and also in metricTheory *)
Theorem ADD_POW_2 :
    !x y :real. (x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y
Proof
    RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                   GSYM REAL_DOUBLE]
 >> REWRITE_TAC [GSYM REAL_ADD_ASSOC, REAL_EQ_LADD]
 >> ‘y * x = x * y’ by PROVE_TAC [REAL_MUL_COMM] >> POP_ORW
 >> ‘x * y + y * y = y * y + x * y’ by PROVE_TAC [REAL_ADD_COMM] >> POP_ORW
 >> REWRITE_TAC [REAL_ADD_ASSOC, REAL_EQ_RADD]
 >> METIS_TAC [REAL_ADD_COMM]
QED

(* moved here from util_probTheory *)
Theorem SUB_POW_2 :
    !x y :real. (x - y) pow 2 = x pow 2 + y pow 2 - 2 * x * y
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [SIMP_RULE (srw_ss()) [GSYM real_sub]
                           (Q.SPECL [‘x’, ‘-y’] ADD_POW_2),
                 real_sub]
 >> AP_TERM_TAC
 >> REWRITE_TAC [REAL_MUL_RNEG]
QED

(* ------------------------------------------------------------------------- *)
(* The sign of a real number, as a real number. (ported from HOL-Light)      *)
(* ------------------------------------------------------------------------- *)

Definition real_sgn :
  (real_sgn:real->real) x =
        if &0 < x then &1 else if x < &0 then ~&1 else &0
End

Overload sgn = “real_sgn”

Theorem REAL_SGN_0 :
   real_sgn(&0) = &0
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGN_NEG :
   !x. real_sgn(~x) = ~(real_sgn x)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGN_ABS :
   !x. real_sgn(x) * abs(x) = x
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGN_ABS_ALT :
   !x. real_sgn x * x = abs x
Proof
  GEN_TAC THEN REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_EQ_SGN_ABS :
   !x y:real. x = y <=> real_sgn x = real_sgn y /\ abs x = abs y
Proof
  MESON_TAC[REAL_SGN_ABS]
QED

Theorem REAL_ABS_SGN :
   !x. abs(real_sgn x) = real_sgn(abs x)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGN :
   !x. real_sgn x = x / abs x
Proof
    GEN_TAC THEN ASM_CASES_TAC “x = &0”
 >- ASM_REWRITE_TAC[real_div, REAL_MUL_LZERO, REAL_SGN_0]
 >> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) empty_rewrites [GSYM REAL_SGN_ABS]
 >> ASM_SIMP_TAC std_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_ABS_ZERO,
                         REAL_MUL_RINV, REAL_MUL_RID]
QED

Theorem REAL_SGN_MUL :
   !x y. real_sgn(x * y) = real_sgn(x) * real_sgn(y)
Proof
  REWRITE_TAC[REAL_SGN, REAL_ABS_MUL, real_div, REAL_INV_MUL'] THEN
  REAL_ARITH_TAC
QED

Theorem REAL_SGN_INV :
   !x. real_sgn(inv x) = real_sgn x
Proof
  REWRITE_TAC[real_sgn, REAL_LT_INV_EQ, GSYM REAL_INV_NEG,
              REAL_ARITH “x < &0 <=> &0 < ~x”]
QED

Theorem REAL_SGN_DIV :
   !x y. real_sgn(x / y) = real_sgn(x) / real_sgn(y)
Proof
  REWRITE_TAC[REAL_SGN, REAL_ABS_DIV] THEN
  REWRITE_TAC[real_div, REAL_INV_MUL', REAL_INV_INV] THEN
  REAL_ARITH_TAC
QED

Theorem REAL_SGN_EQ :
   (!x. real_sgn x = &0 <=> x = &0) /\
   (!x. real_sgn x = &1 <=> x > &0) /\
   (!x. real_sgn x = ~ &1 <=> x < &0)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGN_CASES :
   !x. real_sgn x = &0 \/ real_sgn x = &1 \/ real_sgn x = ~&1
Proof
  REWRITE_TAC[real_sgn] THEN METIS_TAC[] (* was: MESON_TAC *)
QED

Theorem REAL_SGN_INEQS :
   (!x. &0 <= real_sgn x <=> &0 <= x) /\
   (!x. &0 < real_sgn x <=> &0 < x) /\
   (!x. &0 >= real_sgn x <=> &0 >= x) /\
   (!x. &0 > real_sgn x <=> &0 > x) /\
   (!x. &0 = real_sgn x <=> &0 = x) /\
   (!x. real_sgn x <= &0 <=> x <= &0) /\
   (!x. real_sgn x < &0 <=> x < &0) /\
   (!x. real_sgn x >= &0 <=> x >= &0) /\
   (!x. real_sgn x > &0 <=> x > &0) /\
   (!x. real_sgn x = &0 <=> x = &0)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGN_POW :
   !x n. real_sgn(x pow n) = real_sgn(x) pow n
Proof
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_SGN_MUL, real_pow] THEN
  REWRITE_TAC[real_sgn, REAL_LT_01]
QED

val REAL_LE_POW_2 = REAL_LE_POW2;

Theorem REAL_SGN_POW_2 :
   !x. real_sgn(x pow 2) = real_sgn(abs x)
Proof
  REWRITE_TAC[real_sgn] THEN
  SIMP_TAC arith_ss [GSYM REAL_NOT_LE, REAL_ABS_POS, REAL_LE_POW_2,
                     REAL_ARITH “&0 <= x ==> (x <= &0 <=> x = &0)”] THEN
  SIMP_TAC arith_ss [REAL_POW_EQ_0, REAL_ABS_ZERO]
QED

Theorem REAL_SGN_REAL_SGN :
   !x. real_sgn(real_sgn x) = real_sgn x
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_INV_SGN :
   !x. inv(real_sgn x) = real_sgn x
Proof
  GEN_TAC THEN REWRITE_TAC[real_sgn] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_INV_0, REAL_INV_1, REAL_INV_NEG]
QED

(* NOTE: REAL_ARITH_TAC takes quite long steps to prove this theorem *)
Theorem REAL_SGN_EQ_INEQ :
   !x y. real_sgn x = real_sgn y <=>
         x = y \/ abs(x - y) < max (abs x) (abs y)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGNS_EQ :
   !x y. real_sgn x = real_sgn y <=>
         (x = &0 <=> y = &0) /\
         (x > &0 <=> y > &0) /\
         (x < &0 <=> y < &0)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

Theorem REAL_SGNS_EQ_ALT :
   !x y. real_sgn x = real_sgn y <=>
         (x = &0 ==> y = &0) /\
         (x > &0 ==> y > &0) /\
         (x < &0 ==> y < &0)
Proof
  REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC
QED

(*---------------------------------------------------------------------------*)
(* Some properties of (square) roots (without transcendental functions)      *)
(*---------------------------------------------------------------------------*)

val sqrt_def = new_definition
  ("sqrt_def", “sqrt x = @u. (0 < x ==> 0 < u) /\ (u pow 2 = x)”);

Theorem SQRT_0 :
    sqrt(&0) = &0
Proof
    rw [sqrt_def]
QED

Theorem SQRT_1 :
    sqrt(&1) = &1
Proof
    REWRITE_TAC [sqrt_def]
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.EXISTS_TAC ‘1’ >> rw [])
 >> CCONTR_TAC
 >> ‘x < 1 \/ 1 < x’ by METIS_TAC [REAL_LT_TOTAL]
 >| [ (* goal 1 (of 2) *)
      Know ‘x pow SUC 1 < 1 pow SUC 1’
      >- (MATCH_MP_TAC POW_LT >> rw [REAL_LT_IMP_LE]) >> rw [],
      (* goal 2 (of 2) *)
      Know ‘1 pow SUC 1 < x pow SUC 1’
      >- (MATCH_MP_TAC POW_LT >> rw []) >> rw [] ]
QED

(* NOTE: adding quantifier may break isqrtLib *)
Theorem POW_2_SQRT :
    &0 <= x ==> (sqrt(x pow 2) = x)
Proof
    RW_TAC std_ss [sqrt_def]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (Q.EXISTS_TAC ‘x’ >> rw [REAL_LT_LE])
 >> Q.X_GEN_TAC ‘y’
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC POW_EQ
 >> Q.EXISTS_TAC ‘1’ >> rw []
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- fs [pow_rat]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC REAL_POW_LT >> rw []
QED

Theorem SQRT_POS_UNIQ :
    !x y. &0 <= x /\ &0 <= y /\ (y pow 2 = x) ==> (sqrt x = y)
Proof
    RW_TAC std_ss [sqrt_def]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (Q.EXISTS_TAC ‘y’ >> rw [REAL_LT_LE])
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC POW_EQ
 >> Q.EXISTS_TAC ‘1’ >> rw []
 >> ‘(y = 0) \/ 0 < y’ by METIS_TAC [REAL_LE_LT]
 >- fs [pow_rat]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC REAL_POW_LT >> rw []
QED

(* Elementary proof (without using transcTheory) by Chun Tian *)
Theorem SQRT_EXISTS[local] :
    !c. 0 < c ==> ?x. 0 < x /\ (x pow 2 = c)
Proof
    rpt STRIP_TAC
 >> Suff ‘?x. 0 <= x /\ (x pow 2 = c)’
 >- (STRIP_TAC >> Q.EXISTS_TAC ‘x’ >> rw [] \\
     fs [REAL_LE_LT] >> PROVE_TAC [])
 >> Q.ABBREV_TAC ‘s = (\y. 0 < y /\ c <= y pow 2)’
 >> Know ‘?x. s x’
 >- (rw [Abbr ‘s’] \\
     Cases_on ‘c < 1’
     >- (Q.EXISTS_TAC ‘1’ >> rw [] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> rw []) \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lt])) \\
     Q.EXISTS_TAC ‘c’ >> rw [POW_2] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites
                     [GSYM REAL_MUL_RID] \\
     MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘g = inf s’
 >> Q.EXISTS_TAC ‘g’
 >> STRONG_CONJ_TAC (* ‘0 <= g’ is useful later  *)
 >- (Q.UNABBREV_TAC ‘g’ >> MATCH_MP_TAC REAL_IMP_LE_INF \\
     rw [Abbr ‘s’] >> MATCH_MP_TAC REAL_LT_IMP_LE >> rw [])
 >> DISCH_TAC
 (* stage work, now "reductio ad absurdum" *)
 >> CCONTR_TAC
 >> ‘g pow 2 < c \/ c < g pow 2’ by PROVE_TAC [REAL_LT_TOTAL]
 >| [ (* goal 1 (of 2) *)
      MP_TAC (Q.SPEC ‘c - g pow 2’ REAL_ARCH) \\
      ASM_SIMP_TAC std_ss [REAL_SUB_LT, real_lt] \\
      Q.EXISTS_TAC ‘1 + 2 * g’ >> Q.X_GEN_TAC ‘n’ \\
     ‘(n = 0) \/ 0 < n’ by RW_TAC arith_ss []
      >- (rw [] >> MATCH_MP_TAC REAL_LE_ADD >> rw [] \\
          MATCH_MP_TAC REAL_LE_MUL >> rw []) \\
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [REAL_MUL_COMM] \\
      Know ‘(c - g pow 2) * &n <= 1 + 2 * g <=>
             c - g pow 2 <= (1 + 2 * g) / &n’
      >- (MATCH_MP_TAC (GSYM REAL_LE_RDIV_EQ) >> rw []) >> Rewr' \\
      SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [GSYM real_lt, real_div]) \\
      Know ‘(g + inv (&n)) pow 2 < c’
      >- (rw [ADD_POW_2, GSYM REAL_ADD_ASSOC] \\
         ‘c = g pow 2 + (c - g pow 2)’ by PROVE_TAC [REAL_SUB_ADD2] >> POP_ORW \\
          MATCH_MP_TAC REAL_LT_IADD \\
          MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘1 * inv (&n) + 2 * g * inv (&n)’ \\
          CONJ_TAC >- (RW_TAC std_ss [REAL_LE_RADD, POW_2] \\
                       MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [REAL_LE_INV_EQ] \\
                       MATCH_MP_TAC REAL_INV_LE_1 >> rw []) \\
          rw [GSYM REAL_ADD_RDISTRIB]) >> DISCH_TAC \\
      Know ‘!x. s x ==> g + inv (&n) < x’
      >- (Q.PAT_X_ASSUM ‘?x. s x’ K_TAC \\
          rw [Abbr ‘s’] \\
         ‘(g + inv (&n)) pow 2 < x pow 2’ by PROVE_TAC [REAL_LTE_TRANS] \\
          SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [real_lt])) \\
         ‘x pow 2 <= (g + inv (&n)) pow 2’ by METIS_TAC [REAL_LT_IMP_LE, POW_LE] \\
          METIS_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC \\
      Suff ‘?x. s x /\ x < g + inv (&n)’ >- METIS_TAC [REAL_LT_ANTISYM] \\
      MATCH_MP_TAC REAL_INF_LT >> rw [],
      (* goal 2 (of 2) *)
     ‘(g = 0) \/ 0 < g’ by METIS_TAC [REAL_LE_LT]
      >- (fs [pow_rat] >> METIS_TAC [REAL_LT_ANTISYM]) \\
      STRIP_ASSUME_TAC (REWRITE_RULE [ASSUME “0 < (g :real)”]
                                     (Q.SPEC ‘g’ REAL_ARCH_INV)) \\
      MP_TAC (Q.SPEC ‘g pow 2 - c’ REAL_ARCH) \\
      ASM_SIMP_TAC std_ss [REAL_SUB_LT, real_lt] \\
      Q.EXISTS_TAC ‘2 * g’ >> Q.X_GEN_TAC ‘m’ \\
     ‘(m = 0) \/ 0 < m’ by RW_TAC arith_ss []
      >- (rw [] >> MATCH_MP_TAC REAL_LE_MUL >> rw []) \\
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [REAL_MUL_COMM] \\
      Know ‘(g pow 2 - c) * &m <= 2 * g <=>
             g pow 2 - c <= (2 * g) / &m’
      >- (MATCH_MP_TAC (GSYM REAL_LE_RDIV_EQ) >> rw []) >> Rewr' \\
      SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [GSYM real_lt, real_div]) \\
      Q.ABBREV_TAC ‘N = MAX m n’ \\
      Know ‘c < (g - inv (&N)) pow 2’
      >- (rw [SUB_POW_2] \\
          REWRITE_TAC [real_sub, GSYM REAL_ADD_ASSOC] \\
          REWRITE_TAC [GSYM real_sub] \\
          ONCE_REWRITE_TAC [REAL_ADD_COMM] \\
          REWRITE_TAC [GSYM REAL_LT_SUB_RADD] \\
          ONCE_REWRITE_TAC [GSYM REAL_LT_NEG] \\
          REWRITE_TAC [REAL_NEG_SUB] \\
          MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘2 * g * inv (&m)’ >> rw [REAL_LE_SUB_RADD] \\
          MATCH_MP_TAC REAL_LE_TRANS \\
          Q.EXISTS_TAC ‘2 * g * inv (&m)’ \\
          CONJ_TAC >- (MATCH_MP_TAC REAL_LE_LMUL_IMP \\
                       CONJ_TAC >- (MATCH_MP_TAC REAL_LE_MUL >> rw []) \\
                       MATCH_MP_TAC REAL_LE_INV2 >> rw [Abbr ‘N’, REAL_LE_MAX]) \\
          rw [REAL_LE_ADDR]) >> DISCH_TAC \\
      Know ‘s (g - inv (&N))’
      >- (rw [Abbr ‘s’, REAL_SUB_LT] >| (* 2 subgoals *)
          [ (* goal 2.1 (of 2) *)
            MATCH_MP_TAC REAL_LET_TRANS \\
            Q.EXISTS_TAC ‘inv (&n)’ >> rw [] \\
            MATCH_MP_TAC REAL_LE_INV2 >> rw [Abbr ‘N’, REAL_LE_MAX],
            (* goal 2.2 (of 2) *)
            MATCH_MP_TAC REAL_LT_IMP_LE >> rw [] ]) >> DISCH_TAC \\
      Suff ‘inf s <= g - inv (&N)’
      >- (simp [GSYM real_lt, REAL_LT_SUB_RADD, Abbr ‘N’, REAL_LT_MAX]) \\
      MATCH_MP_TAC REAL_IMP_INF_LE \\
      CONJ_TAC >- (Q.EXISTS_TAC ‘0’ >> rw [Abbr ‘s’] \\
                   MATCH_MP_TAC REAL_LT_IMP_LE >> rw []) \\
      Q.EXISTS_TAC ‘g - inv (&N)’ >> rw [] ]
QED

Theorem SQRT_POS_LT :
    !x. &0 < x ==> &0 < sqrt(x)
Proof
    RW_TAC std_ss [sqrt_def]
 >> SELECT_ELIM_TAC
 >> rw [SQRT_EXISTS]
QED

Theorem SQRT_POS_NE :
    !(x :real). &0 < x ==> sqrt(x) <> &0
Proof
    Q.X_GEN_TAC ‘x’
 >> DISCH_THEN (ASSUME_TAC o (MATCH_MP SQRT_POS_LT))
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC REAL_LT_IMP_NE
 >> ASM_REWRITE_TAC []
QED

Theorem SQRT_POS_LE :
   !x. &0 <= x ==> &0 <= sqrt(x)
Proof
    rpt STRIP_TAC
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- rw [SQRT_0]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> MATCH_MP_TAC SQRT_POS_LT >> rw []
QED

Theorem SQRT_POW2 :
    !x. (sqrt(x) pow 2 = x) <=> &0 <= x
Proof
    GEN_TAC
 >> EQ_TAC >> RW_TAC std_ss []
 >- (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [GSYM real_lt]) \\
     ASSUME_TAC (Q.SPEC ‘sqrt x’ REAL_LE_POW2) \\
    ‘x < sqrt x pow 2’ by PROVE_TAC [REAL_LTE_TRANS] \\
     METIS_TAC [REAL_LT_IMP_NE])
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- rw [SQRT_0]
 >> REWRITE_TAC [sqrt_def]
 >> SELECT_ELIM_TAC
 >> rw [SQRT_EXISTS]
QED

Theorem SQRT_POW_2 :
    !x. &0 <= x ==> (sqrt(x) pow 2 = x)
Proof
    REWRITE_TAC[SQRT_POW2]
QED

Theorem SQRT_MUL :
    !x y. &0 <= x /\ &0 <= y ==> (sqrt(x * y) = sqrt x * sqrt y)
Proof
    rpt STRIP_TAC
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT] >- rw [SQRT_0]
 >> ‘(y = 0) \/ 0 < y’ by METIS_TAC [REAL_LE_LT] >- rw [SQRT_0]
 >> REWRITE_TAC [sqrt_def]
 >> SELECT_ELIM_TAC (* 1st *)
 >> ‘0 < x * y’ by PROVE_TAC [REAL_LT_MUL]
 >> rw [SQRT_EXISTS]
 >> rename1 ‘c pow 2 = x * y’
 >> SELECT_ELIM_TAC (* 2nd *)
 >> rw [SQRT_EXISTS]
 >> rename1 ‘0 < a pow 2 * y’
 >> SELECT_ELIM_TAC (* 3rd *)
 >> rw [SQRT_EXISTS]
 >> fs [GSYM POW_MUL]
 >> MATCH_MP_TAC POW_EQ
 >> Q.EXISTS_TAC ‘1’ >> rw []
 >- (MATCH_MP_TAC REAL_LT_IMP_LE >> rw [])
 >> MATCH_MP_TAC REAL_LE_MUL
 >> CONJ_TAC
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> rw []
QED

Theorem SQRT_INV :
    !x. &0 <= x ==> (sqrt (inv x) = inv(sqrt x))
Proof
    rpt STRIP_TAC
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- rw [SQRT_0]
 >> RW_TAC std_ss [sqrt_def]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (‘0 < inv x’ by PROVE_TAC [REAL_INV_POS] \\
     MP_TAC (MATCH_MP (Q.SPEC ‘inv x’ SQRT_EXISTS) (ASSUME “0 < inv x”)) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘y’ >> rw [])
 >> Q.X_GEN_TAC ‘y’
 >> rw [REAL_LT_INV_EQ]
 >> SELECT_ELIM_TAC
 >> rw [SQRT_EXISTS]
 >> rename1 ‘y = inv z’
 >> fs [GSYM REAL_POW_INV]
 >> CCONTR_TAC
 >> ‘y < inv z \/ inv z < y’ by METIS_TAC [REAL_LT_TOTAL]
 >| [ (* goal 1 (of 2) *)
      Know ‘y pow SUC 1 < (inv z) pow SUC 1’
      >- (MATCH_MP_TAC POW_LT >> rw [REAL_LT_IMP_LE]) >> rw [],
      (* goal 2 (of 2) *)
      Know ‘(inv z) pow SUC 1 < y pow SUC 1’
      >- (MATCH_MP_TAC POW_LT >> rw [REAL_LE_LT]) >> rw [] ]
QED

Theorem SQRT_MONO_LE :
    !x y. &0 <= x /\ x <= y ==> sqrt(x) <= sqrt(y)
Proof
    rpt STRIP_TAC
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- rw [SQRT_0, SQRT_POS_LE]
 >> REWRITE_TAC [sqrt_def]
 >> SELECT_ELIM_TAC
 >> rw [SQRT_EXISTS] >> rename1 ‘0 < x’
 >> SELECT_ELIM_TAC
 >> ‘0 < y’ by PROVE_TAC [REAL_LTE_TRANS]
 >> rw [SQRT_EXISTS] >> rename1 ‘0 < z’
 >> SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lt]))
 >> Know ‘z pow (SUC 1) < x pow (SUC 1)’
 >- (MATCH_MP_TAC POW_LT >> rw [REAL_LT_IMP_LE])
 >> rw [real_lt]
QED

Theorem SQRT_MONO_LT :
    !x y. &0 <= x /\ x < y ==> sqrt(x) < sqrt(y)
Proof
    rpt STRIP_TAC
 >> fs [REAL_LT_LE]
 >> CONJ_TAC >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [])
 >> ‘0 <= y’ by PROVE_TAC [REAL_LE_TRANS]
 >> CCONTR_TAC >> fs []
 >> METIS_TAC [SQRT_POW2]
QED

Theorem SQRT_DIV :
    !x y. &0 <= x /\ &0 <= y ==> (sqrt (x / y) = sqrt x / sqrt y)
Proof
    rpt STRIP_TAC
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- rw [SQRT_0, REAL_DIV_LZERO]
 >> ‘(y = 0) \/ 0 < y’ by METIS_TAC [REAL_LE_LT]
 >- rw [SQRT_0, real_div, REAL_INV_0]
 >> REWRITE_TAC [sqrt_def]
 >> SELECT_ELIM_TAC (* 1st *)
 >> ‘0 < x / y’ by PROVE_TAC [REAL_LT_DIV]
 >> rw [SQRT_EXISTS]
 >> rename1 ‘z pow 2 = x / y’
 >> SELECT_ELIM_TAC (* 2nd *)
 >> rw [SQRT_EXISTS]
 >> rename1 ‘z pow 2 = u pow 2 / y’
 >> SELECT_ELIM_TAC (* 3rd *)
 >> rw [SQRT_EXISTS]
 >> fs [GSYM REAL_POW_DIV]
 >> ‘0 < u / x’ by PROVE_TAC [REAL_LT_DIV]
 >> CCONTR_TAC
 >> ‘z < u / x \/ u / x < z’ by METIS_TAC [REAL_LT_TOTAL]
 >| [ (* goal 1 (of 2) *)
      Know ‘z pow SUC 1 < (u / x) pow SUC 1’
      >- (MATCH_MP_TAC POW_LT  >> rw [REAL_LT_IMP_LE]) >> rw [],
      (* goal 2 (of 2) *)
      Know ‘(u / x) pow SUC 1 < z pow SUC 1’
      >- (MATCH_MP_TAC POW_LT >> rw [REAL_LE_LT]) >> rw [] ]
QED

Theorem SQRT_EQ :
    !x y. (x pow 2 = y) /\ &0 <= x ==> (x = sqrt y)
Proof
    rpt STRIP_TAC
 >> ‘(x = 0) \/ 0 < x’ by METIS_TAC [REAL_LE_LT]
 >- fs [pow_rat, SQRT_0]
 >> REWRITE_TAC [sqrt_def]
 >> SELECT_ELIM_TAC
 >> Know ‘0 < y’
 >- (Q.PAT_X_ASSUM ‘x pow 2 = y’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [REAL_POW_LT, REAL_LT_IMP_NE])
 >> rw [SQRT_EXISTS]
 >> rename1 ‘y pow 2 = x pow 2’
 >> MATCH_MP_TAC POW_EQ
 >> Q.EXISTS_TAC ‘1’ >> rw [REAL_LT_IMP_LE]
QED

(*---------------------------------------------------------------------------*)
(* Miscellaneous Results (generally for use in descendent theories)          *)
(*---------------------------------------------------------------------------*)

Theorem REAL_MUL_SIGN:
    (!x y. 0 <= x * y <=> (0 <= x /\ 0 <= y) \/ (x <= 0 /\ y <= 0)) /\
    (!x y. x * y <= 0 <=> (0 <= x /\ y <= 0) \/ (x <= 0 /\ 0 <= y))
Proof
    rw[] >> eq_tac >> rw[] >> fs[GSYM REAL_NEG_GE0,Excl "REAL_NEG_GE0"] >>
    TRY $ dxrule_all_then assume_tac $ REAL_LE_MUL >>
    fs[REAL_MUL_LNEG,REAL_MUL_RNEG,REAL_MUL_COMM] >>
    pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> rw[] >> fs[real_lte,REAL_LT_GT] >>
    fs[GSYM REAL_NEG_GT0,Excl "REAL_NEG_GT0"] >>
    dxrule_all_then assume_tac $ REAL_LT_MUL >>
    fs[REAL_MUL_LNEG,REAL_MUL_RNEG,REAL_MUL_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Various handy lemmas (for REAL_ARITH2_TAC).                               *)
(* ------------------------------------------------------------------------- *)

(* cf. REAL_ADD_RAT *)
Theorem RAT_LEMMA1 :
   ~(y1 = &0) /\ ~(y2 = &0) ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))
Proof
    RW_TAC std_ss [GSYM REAL_MUL_ASSOC, GSYM REAL_INV_MUL, GSYM real_div]
 >> METIS_TAC [REAL_ADD_RAT, REAL_MUL_COMM]
QED

Theorem RAT_LEMMA2 :
    &0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))
Proof
    METIS_TAC [REAL_LT_IMP_NE, RAT_LEMMA1]
QED

(* cf. REAL_SUB_RAT *)
Theorem RAT_LEMMA3 :
    &0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) - (x2 / y2) = (x1 * y2 - x2 * y1) * inv(y1) * inv(y2))
Proof
  DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP RAT_LEMMA2) THEN
  REWRITE_TAC[real_div] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[real_sub, GSYM REAL_MUL_LNEG]
QED

val lemma = Q.prove
   (`!x y. &0 < y ==> (&0 <= x * y <=> &0 <= x)`,
    rpt GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
    [ (* goal 1 (of 2) *)
      Q.SUBGOAL_THEN `&0 <= x * (y * inv y)` MP_TAC THENL
      [ (* goal 1.1 (of 2) *)
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
        (* goal 1.2 (of 2) *)
        Q.SUBGOAL_THEN `y * inv y = &1` (fn th =>
          REWRITE_TAC[th, REAL_MUL_RID]) THEN
        MATCH_MP_TAC REAL_MUL_RINV THEN
        Q.UNDISCH_TAC `&0 < y` THEN REAL_ARITH_TAC ],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[] ]);

(* These are HOL-Light compatible names (locally used):
   |- !x y. 0 < x /\ x < y ==> realinv y < realinv x
 *)
Theorem REAL_LT_INV2 = REAL_LT_INV

(* |- !x. 0 < x ==> 0 < inv x *)
Theorem REAL_LT_INV' = REAL_INV_POS

Theorem RAT_LEMMA4 :
   &0 < y1 /\ &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)
Proof
  ONCE_REWRITE_TAC[CONJ_SYM] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``a <= b <=> &0 <= b - a``] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP RAT_LEMMA3 th]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `&0 <= (x2 * y1 - x1 * y2) * inv y2` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN CONJ_TAC THEN
  MATCH_MP_TAC lemma THEN MATCH_MP_TAC REAL_LT_INV' THEN
  ASM_REWRITE_TAC[]
QED

Theorem RAT_LEMMA5 :
   &0 < y1 /\ &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))
Proof
  REPEAT DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') ==> (a /\ b <=> a' /\ b')`) THEN
  CONJ_TAC THEN MATCH_MP_TAC RAT_LEMMA4 THEN ASM_REWRITE_TAC[]
QED

Theorem RAT_LEMMA5_BETTER:
  y1 <> 0:real /\ y2 <> 0 ==> (x1 / y1 = x2 / y2 <=> x1 * y2 = x2 * y1)
Proof
    rw[]
 >> ‘y1*y2 <> 0’ by simp[] >> simp[real_div]
 >> ‘x1 * inv y1 = x2 * inv y2 <=>
     x1 * inv y1 * (y1 * y2) = x2 * inv y2 * (y1 * y2)’ by simp[REAL_EQ_RMUL]
 >> ‘x1 * inv y1 * (y1 * y2) = x2 * inv y2 * (y1 * y2) <=>
     x1 * y2 * (inv y1 * y1) = x2 * y1 * (inv y2 * y2)’ by
    metis_tac[REAL_MUL_ASSOC, REAL_MUL_SYM]
 >> ‘x1 * y2 * (inv y1 * y1) = x2 * y1 * (inv y2 * y2) <=>
     x1 * y2 = x2 * y1’ by simp[REAL_MUL_LINV]
 >> metis_tac[]
QED

(* The following common used HALF theorems were moved from seqTheory *)
Theorem HALF_POS :
    0:real < 1/2
Proof
    PROVE_TAC [REAL_LT_01, REAL_LT_HALF1]
QED

Theorem HALF_LT_1 :
    1 / 2 < 1:real
Proof
    ONCE_REWRITE_TAC [GSYM REAL_INV_1OVER, GSYM REAL_INV1]
 >> MATCH_MP_TAC REAL_LT_INV
 >> RW_TAC arith_ss [REAL_LT]
QED

Theorem HALF_CANCEL :
    2 * (1 / 2) = 1:real
Proof
    Suff `2 * inv 2 = 1:real` >- PROVE_TAC [REAL_INV_1OVER]
 >> PROVE_TAC [REAL_MUL_RINV, REAL_ARITH ``~(2:real = 0)``]
QED

Theorem X_HALF_HALF :
    !x:real. 1/2 * x + 1/2 * x = x
Proof
    STRIP_TAC
 >> MATCH_MP_TAC (REAL_ARITH ``(2 * (a:real) = 2 * b) ==> (a = b)``)
 >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
 >> REAL_ARITH_TAC
QED

Theorem ONE_MINUS_HALF :
    (1:real) - 1 / 2 = 1 / 2
Proof
    MP_TAC (Q.SPEC `1` X_HALF_HALF)
 >> RW_TAC std_ss [REAL_MUL_RID]
 >> MATCH_MP_TAC (REAL_ARITH ``((x:real) + 1 / 2 = y + 1 / 2) ==> (x = y)``)
 >> RW_TAC std_ss [REAL_SUB_ADD]
QED

Theorem POW_HALF_POS :
    !n. 0:real < (1/2) pow n
Proof
    STRIP_TAC
 >> Cases_on `n` >- PROVE_TAC [REAL_LT_01, pow]
 >> PROVE_TAC [HALF_POS, POW_POS_LT]
QED

(* NOTE: This theorem shows that the ring of real numbers is an intergal domain. *)
Theorem REAL_INTEGRAL :
    (!(x :real). &0 * x = &0) /\
    (!(x :real) y z. (x + y = x + z) <=> (y = z)) /\
    (!(w :real) x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))
Proof
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_ENTIRE] THEN REAL_ARITH_TAC
QED

(* NOTE: Perhaps this theorem is related to "Rabinowitsch trick". See also
   https://en.wikipedia.org/wiki/Rabinowitsch_trick
 *)
Theorem REAL_RABINOWITSCH :
    !x y:real. ~(x = y) <=> ?z. (x - y) * z = &1
Proof
    REWRITE_TAC[EQ_IMP_THM]
 >> rpt strip_tac
 >> FULL_SIMP_TAC std_ss [EQ_IMP_THM, REAL_SUB_REFL, REAL_MUL_LZERO, REAL_10]
 >> irule_at Any REAL_MUL_RINV
 >> ASM_REWRITE_TAC [REAL_SUB_0]
QED

val _ = export_theory();
