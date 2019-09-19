(* interactive mode
loadPath := ["../ho_prover","../subtypes","../rsa"] @ !loadPath;
app load ["bossLib","realLib","transcTheory","subtypeTheory",
          "hurdUtils","extra_boolTheory",
          "boolContext","extra_pred_setTools","sumTheory"];

open HolKernel Parse boolLib bossLib realTheory realLib
     hurdUtils subtypeTheory extra_numTheory transcTheory
     pred_setTheory arithmeticTheory seqTheory combinTheory pairTheory
     extra_pred_setTheory extra_boolTheory extra_pred_setTools
     sumTheory;


loadPath := ["../subtypes"] @ !loadPath;
app load ["bossLib","realLib","transcTheory","subtypeTheory",
          "hurdUtils","extra_boolTheory",
          "extra_pred_setTheory","sumTheory"];

quietdec := true;
*)

open HolKernel Parse boolLib bossLib realTheory realLib
     hurdUtils subtypeTheory extra_numTheory transcTheory
     pred_setTheory arithmeticTheory seqTheory combinTheory pairTheory
     extra_pred_setTheory extra_boolTheory real_sigmaTheory
     sumTheory limTheory listTheory rich_listTheory;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "extra_real";

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val Reverse = Tactical.REVERSE;
val REVERSE = Tactical.REVERSE;
val Strip = rpt (POP_ASSUM MP_TAC) >> rpt STRIP_TAC;
val Simplify = RW_TAC arith_ss;
val Suff = PARSE_TAC SUFF_TAC;
val Know = PARSE_TAC KNOW_TAC;
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val STRONG_DISJ_TAC = CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) >> STRIP_TAC;
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond >| [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val inf_def = Define `inf p = ~(sup (IMAGE $~ p))`;

val zreal_def = Define `zreal (x : real) = (x = 0)`;
val nzreal_def = Define `nzreal (x : real) = ~(x = 0)`;
val posreal_def = Define `posreal (x : real) = 0 < x`;
val nnegreal_def = Define `nnegreal (x : real) = 0 <= x`;
val negreal_def = Define `negreal (x : real) = 0 < ~x`;
val nposreal_def = Define `nposreal (x : real) = 0 <= ~x`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val INF_DEF_ALT = store_thm
  ("INF_DEF_ALT",
   ``!p. inf p = ~(sup (\r. ~r IN p))``,
   RW_TAC std_ss []
   >> PURE_REWRITE_TAC [inf_def, IMAGE_DEF]
   >> Suff `{~x | x IN p} = (\r:real. ~r IN p)`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [EXTENSION]
   >> RW_TAC std_ss [GSPECIFICATION, SPECIFICATION]
   >> PROVE_TAC [REAL_NEGNEG]);

val REAL_LE_EQ = store_thm
  ("REAL_LE_EQ",
   ``!(x:real) y. x <= y /\ y <= x ==> (x = y)``,
   REAL_ARITH_TAC);

val REAL_SUP_EXISTS_UNIQUE = store_thm
  ("REAL_SUP_EXISTS_UNIQUE",
   ``!P. (?(x:real). P x) /\ (?z. !x. P x ==> x <= z)
         ==> (?!s. !y. (?x. P x /\ y < x) = y < s)``,
   REPEAT STRIP_TAC
   >> CONV_TAC EXISTS_UNIQUE_CONV
   >> RW_TAC std_ss [] >|
   [ASSUME_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
    >> PROVE_TAC [],
    Suff `~((s:real) < s') /\ ~(s' < s)`
      >- (KILL_TAC >> REAL_ARITH_TAC)
    >> REPEAT STRIP_TAC >|
    [Suff `!(x:real). P x ==> ~(s < x)` >- PROVE_TAC []
     >> REPEAT STRIP_TAC
     >> Suff `~((s:real) < s)` >- PROVE_TAC []
     >> KILL_TAC
     >> REAL_ARITH_TAC,
     Suff `!(x:real). P x ==> ~(s' < x)` >- PROVE_TAC []
     >> REPEAT STRIP_TAC
     >> Suff `~((s':real) < s')` >- PROVE_TAC []
     >> KILL_TAC
     >> REAL_ARITH_TAC]]);

val REAL_SUP_MAX = store_thm
  ("REAL_SUP_MAX",
   ``!P z. P z /\ (!x. P x ==> x <= z) ==> (sup P = z)``,
    REPEAT STRIP_TAC
    >> Know `!(y:real). (?x. P x /\ y < x) = y < z`
    >- (STRIP_TAC
        >> EQ_TAC >|
        [REPEAT STRIP_TAC
         >> PROVE_TAC [REAL_ARITH ``(y:real) < x /\ x <= z ==> y < z``],
         PROVE_TAC []])
    >> STRIP_TAC
    >> Know `!y. (?x. P x /\ y < x) = y < sup P`
    >- PROVE_TAC [REAL_SUP_LE]
    >> STRIP_TAC
    >> Know `(?(x:real). P x) /\ (?z. !x. P x ==> x <= z)`
    >- PROVE_TAC []
    >> STRIP_TAC
    >> ASSUME_TAC ((SPEC ``P:real->bool`` o CONV_RULE
                      (DEPTH_CONV EXISTS_UNIQUE_CONV)) REAL_SUP_EXISTS_UNIQUE)
    >> RES_TAC);

val REAL_INF_MIN = store_thm
  ("REAL_INF_MIN",
   ``!p z. z IN p /\ (!x. x IN p ==> z <= x) ==> (inf p = z)``,
   RW_TAC std_ss [SPECIFICATION]
   >> MP_TAC (SPECL [``(\r. (p:real->bool) (~r))``, ``~(z:real)``]
              REAL_SUP_MAX)
   >> RW_TAC std_ss [REAL_NEGNEG, INF_DEF_ALT, SPECIFICATION]
   >> Suff `!x. p ~x ==> x <= ~z`
   >- PROVE_TAC [REAL_ARITH ``~~(x:real) = x``]
   >> REPEAT STRIP_TAC
   >> Suff `z <= ~x` >- (KILL_TAC >> REAL_ARITH_TAC)
   >> PROVE_TAC []);

val HALF_POS = store_thm
  ("HALF_POS",
   ``0 < 1/2``,
   PROVE_TAC [REAL_ARITH ``0:real < 1``, REAL_LT_HALF1]);

val HALF_CANCEL = store_thm
  ("HALF_CANCEL",
   ``2 * (1 / 2) = 1``,
   Suff `2 * inv 2 = 1` >- PROVE_TAC [REAL_INV_1OVER]
   >> PROVE_TAC [REAL_MUL_RINV, REAL_ARITH ``~(2:real = 0)``]);

val POW_HALF_POS = store_thm
  ("POW_HALF_POS",
   ``!n. 0 < (1/2) pow n``,
   STRIP_TAC
   >> Cases_on `n` >- PROVE_TAC [REAL_ARITH ``0:real < 1``, pow]
   >> PROVE_TAC [HALF_POS, POW_POS_LT]);

val POW_HALF_MONO = store_thm
  ("POW_HALF_MONO",
   ``!m n. m <= n ==> (1/2) pow n <= (1/2) pow m``,
   REPEAT STRIP_TAC
   >> Induct_on `n` >|
   [STRIP_TAC
    >> Know `m:num = 0` >- DECIDE_TAC
    >> PROVE_TAC [REAL_ARITH ``a:real <= a``],
    Cases_on `m = SUC n` >- PROVE_TAC [REAL_ARITH ``a:real <= a``]
    >> ONCE_REWRITE_TAC [pow]
    >> STRIP_TAC
    >> Know `m:num <= n` >- DECIDE_TAC
    >> STRIP_TAC
    >> Suff `2 * ((1/2) * (1/2) pow n) <= 2 * (1/2) pow m`
    >- PROVE_TAC [REAL_ARITH ``0:real < 2``, REAL_LE_LMUL]
    >> Suff `(1/2) pow n <= 2 * (1/2) pow m`
    >- (KILL_TAC
        >> PROVE_TAC [GSYM REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID])
    >> PROVE_TAC [REAL_ARITH ``!x y. 0:real < x /\ x <= y ==> x <= 2 * y``,
                  POW_HALF_POS]]);

val POW_HALF_TWICE = store_thm
  ("POW_HALF_TWICE",
   ``!n. (1 / 2) pow n = 2 * (1 / 2) pow (SUC n)``,
   RW_TAC std_ss [pow, REAL_MUL_ASSOC]
   >> PROVE_TAC [HALF_CANCEL, REAL_MUL_LID]);

val X_HALF_HALF = store_thm
  ("X_HALF_HALF",
   ``!x. 1/2 * x + 1/2 * x = x``,
   STRIP_TAC
   >> MATCH_MP_TAC (REAL_ARITH ``(2 * (a:real) = 2 * b) ==> (a = b)``)
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
   >> REAL_ARITH_TAC);

val REAL_SUP_LE_X = store_thm
  ("REAL_SUP_LE_X",
   ``!P x. (?r. P r) /\ (!r. P r ==> r <= x) ==> sup P <= x``,
   RW_TAC real_ss []
   >> Suff `~(x < sup P)` >- REAL_ARITH_TAC
   >> STRIP_TAC
   >> MP_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
   >> RW_TAC real_ss [] >|
   [PROVE_TAC [],
    PROVE_TAC [],
    EXISTS_TAC ``x:real``
    >> RW_TAC real_ss []
    >> PROVE_TAC [real_lte]]);

val REAL_X_LE_SUP = store_thm
  ("REAL_X_LE_SUP",
   ``!P x. (?r. P r) /\ (?z. !r. P r ==> r <= z) /\ (?r. P r /\ x <= r)
           ==> x <= sup P``,
   RW_TAC real_ss []
   >> Suff `!y. P y ==> y <= sup P` >- PROVE_TAC [REAL_LE_TRANS]
   >> MATCH_MP_TAC REAL_SUP_UBOUND_LE
   >> PROVE_TAC []);

val REAL_INVINV_ALL = store_thm
  ("REAL_INVINV_ALL",
   ``!x. inv (inv x) = x``,
   STRIP_TAC
   >> Reverse (Cases_on `x = 0`) >- RW_TAC std_ss [REAL_INVINV]
   >> RW_TAC std_ss [REAL_INV_0]);

val ABS_BETWEEN_LE = store_thm
  ("ABS_BETWEEN_LE",
   ``!x y d. 0 <= d /\ x - d <= y /\ y <= x + d = abs (y - x) <= d``,
   RW_TAC std_ss [abs] >|
   [EQ_TAC >- REAL_ARITH_TAC
    >> STRIP_TAC
    >> Know `0 <= d` >- PROVE_TAC [REAL_LE_TRANS]
    >> STRIP_TAC
    >> RW_TAC std_ss [] >|
    [Suff `x <= y`
     >- (POP_ASSUM MP_TAC >> KILL_TAC >> REAL_ARITH_TAC)
     >> Q.PAT_ASSUM `0 <= y - x` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC,
     Q.PAT_ASSUM `y - x <= d` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC],
    EQ_TAC >- REAL_ARITH_TAC
    >> Know `y - x <= 0` >- PROVE_TAC [REAL_NOT_LE, REAL_LT_LE]
    >> STRIP_TAC
    >> Know `~0 <= ~(y - x)` >- PROVE_TAC [REAL_LE_NEG]
    >> KILL_TAC
    >> REWRITE_TAC [REAL_NEG_SUB, REAL_NEG_0]
    >> NTAC 2 STRIP_TAC
    >> Know `0 <= d` >- PROVE_TAC [REAL_LE_TRANS]
    >> STRIP_TAC
    >> RW_TAC std_ss [] >|
    [Q.PAT_ASSUM `x - y <= d` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC,
     Suff `y <= x`
     >- (POP_ASSUM MP_TAC >> KILL_TAC >> REAL_ARITH_TAC)
     >> Q.PAT_ASSUM `0 <= x - y` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC]]);

val ONE_MINUS_HALF = store_thm
  ("ONE_MINUS_HALF",
   ``1 - 1 / 2 = 1 / 2``,
   MP_TAC (Q.SPEC `1` X_HALF_HALF)
   >> RW_TAC real_ss []
   >> MATCH_MP_TAC (REAL_ARITH ``(x + 1 / 2 = y + 1 / 2) ==> (x = y)``)
   >> RW_TAC std_ss [REAL_SUB_ADD]);

val HALF_LT_1 = store_thm
  ("HALF_LT_1",
   ``1 / 2 < 1``,
   ONCE_REWRITE_TAC [GSYM REAL_INV_1OVER, GSYM REAL_INV1]
   >> MATCH_MP_TAC REAL_LT_INV
   >> RW_TAC arith_ss [REAL_LT]);

val REAL_POW = store_thm
  ("REAL_POW",
   ``!m n. &m pow n = &(m EXP n)``,
   STRIP_TAC
   >> Induct >- RW_TAC real_ss [pow, EXP]
   >> RW_TAC real_ss [pow, EXP, REAL_MUL]);

val POW_HALF_EXP = store_thm
  ("POW_HALF_EXP",
   ``!n. (1 / 2) pow n = inv (&(2 EXP n))``,
   RW_TAC std_ss [GSYM REAL_POW, GSYM REAL_INV_1OVER]
   >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
   >> MATCH_MP_TAC POW_INV
   >> REAL_ARITH_TAC);

val REAL_LE_INV_LE = store_thm
  ("REAL_LE_INV_LE",
   ``!x y. 0 < x /\ x <= y ==> inv y <= inv x``,
   RW_TAC std_ss []
   >> Know `0 < inv x` >- PROVE_TAC [REAL_INV_POS]
   >> STRIP_TAC
   >> Suff `~(inv x < inv y)` >- PROVE_TAC [REAL_NOT_LT]
   >> STRIP_TAC
   >> Know `inv (inv y) < inv (inv x)` >- PROVE_TAC [REAL_LT_INV]
   >> RW_TAC std_ss [REAL_INVINV_ALL, REAL_NOT_LT]);

val INV_SUC_POS = store_thm
  ("INV_SUC_POS",
   ``!n. 0 < 1 / & (SUC n)``,
   RW_TAC real_ss [GSYM REAL_INV_1OVER, REAL_LT_INV_EQ, REAL_LT]);

val INV_SUC_MAX = store_thm
  ("INV_SUC_MAX",
   ``!n. 1 / & (SUC n) <= 1``,
   REWRITE_TAC [GSYM REAL_INV_1OVER]
   >> Induct
   >- RW_TAC std_ss [GSYM ONE, REAL_INV1, REAL_LE_REFL]
   >> Suff `inv (& (SUC (SUC n))) <= inv (& (SUC n))`
   >- PROVE_TAC [REAL_LE_TRANS]
   >> Suff `inv (& (SUC (SUC n))) < inv (& (SUC n))` >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LT_INV
   >> RW_TAC arith_ss [REAL_LT]);

val INV_SUC = store_thm
  ("INV_SUC",
   ``!n. 0 < 1 / & (SUC n) /\ 1 / & (SUC n) <= 1``,
   PROVE_TAC [INV_SUC_POS, INV_SUC_MAX])

val ABS_UNIT_INTERVAL = store_thm
  ("ABS_UNIT_INTERVAL",
   ``!x y. 0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1 ==> abs (x - y) <= 1``,
   REAL_ARITH_TAC);

val REAL_LE_LT_MUL = store_thm
  ("REAL_LE_LT_MUL",
   ``!x y : real. 0 <= x /\ 0 < y ==> 0 <= x * y``,
   rpt STRIP_TAC
   >> MP_TAC (Q.SPECL [`0`, `x`, `y`] REAL_LE_RMUL)
   >> RW_TAC std_ss [REAL_MUL_LZERO]);

val REAL_LT_LE_MUL = store_thm
  ("REAL_LT_LE_MUL",
   ``!x y : real. 0 < x /\ 0 <= y ==> 0 <= x * y``,
   PROVE_TAC [REAL_LE_LT_MUL, REAL_MUL_SYM]);

val REAL_INV_NEG = store_thm
  ("REAL_INV_NEG",
   ``!x. 0 < ~x ==> 0 < ~inv x``,
   rpt STRIP_TAC
   >> Know `~(x = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [REAL_NEG_INV]
   >> PROVE_TAC [REAL_INV_POS]);

val IN_ZREAL = store_thm
  ("IN_ZREAL",
   ``!x. x IN zreal = (x = 0)``,
   RW_TAC std_ss [zreal_def, SPECIFICATION]);

val IN_NZREAL = store_thm
  ("IN_NZREAL",
   ``!x. x IN nzreal = ~(x = 0)``,
   RW_TAC std_ss [nzreal_def, SPECIFICATION]);

val IN_POSREAL = store_thm
  ("IN_POSREAL",
   ``!x. x IN posreal = 0 < x``,
   RW_TAC std_ss [posreal_def, SPECIFICATION]);

val IN_NNEGREAL = store_thm
  ("IN_NNEGREAL",
   ``!x. x IN nnegreal = 0 <= x``,
   RW_TAC std_ss [nnegreal_def, SPECIFICATION]);

val IN_NEGREAL = store_thm
  ("IN_NEGREAL",
   ``!x. x IN negreal = 0 < ~x``,
   RW_TAC std_ss [negreal_def, SPECIFICATION]);

val IN_NPOSREAL = store_thm
  ("IN_NPOSREAL",
   ``!x. x IN nposreal = 0 <= ~x``,
   RW_TAC std_ss [nposreal_def, SPECIFICATION]);

val POSREAL_ALT = store_thm
  ("POSREAL_ALT",
   ``posreal = nnegreal INTER nzreal``,
   RW_TAC std_ss [SET_EQ, IN_INTER, IN_POSREAL, IN_NNEGREAL, IN_NZREAL]
   >> REAL_ARITH_TAC);

val NEGREAL_ALT = store_thm
  ("NEGREAL_ALT",
   ``negreal = nposreal INTER nzreal``,
   RW_TAC std_ss [SET_EQ, IN_INTER, IN_NEGREAL, IN_NPOSREAL, IN_NZREAL]
   >> REAL_ARITH_TAC);

val REAL_ZERO_SUBTYPE = store_thm
  ("REAL_ZERO_SUBTYPE",
   ``0 IN zreal``,
   RW_TAC std_ss [IN_ZREAL, SPECIFICATION]);

val REAL_OF_NUM_SUBTYPE = store_thm
  ("REAL_OF_NUM_SUBTYPE",
   ``real_of_num IN ((UNIV -> nnegreal) INTER (gtnum 0 -> posreal))``,
   RW_TAC std_ss [IN_INTER, IN_FUNSET, IN_NNEGREAL, REAL_POS, IN_GTNUM,
                  IN_ZREAL, IN_POSREAL]
   >> Suff `~(& x = 0)`
   >- (Know `0 <= & x` >- RW_TAC std_ss [REAL_POS]
       >> REAL_ARITH_TAC)
   >> Cases_on `x` >- DECIDE_TAC
   >> RW_TAC std_ss [REAL]
   >> Know `0 <= & n` >- RW_TAC std_ss [REAL_POS]
   >> REAL_ARITH_TAC);

val NEG_SUBTYPE = store_thm
  ("NEG_SUBTYPE",
   ``real_neg IN
     ((negreal -> posreal) INTER (posreal -> negreal) INTER
      (nnegreal -> nposreal) INTER (nposreal -> nnegreal) INTER
      (nzreal -> nzreal) INTER (zreal -> zreal))``,
   RW_TAC std_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL]
   >> TRY (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val INV_SUBTYPE = store_thm
  ("INV_SUBTYPE",
   ``inv IN
     ((nzreal -> nzreal) INTER (posreal -> posreal) INTER
      (negreal -> negreal))``,
   RW_TAC std_ss [IN_NZREAL, REAL_INV_NZ, IN_FUNSET, IN_INTER, IN_POSREAL,
                  IN_NEGREAL, REAL_INV_POS, REAL_INV_NEG]
   >> REAL_ARITH_TAC);

val SQRT_SUBTYPE = store_thm
  ("SQRT_SUBTYPE",
   ``sqrt IN ((nnegreal -> nnegreal) INTER (posreal -> posreal))``,
   RW_TAC std_ss [IN_INTER, IN_FUNSET, IN_NNEGREAL, SQRT_POS_LE, IN_POSREAL,
                  SQRT_POS_LT]);

val REAL_ADD_SUBTYPE = store_thm
  ("REAL_ADD_SUBTYPE",
   ``!x. $+ IN ((posreal -> nnegreal -> posreal) INTER
                (nnegreal -> posreal -> posreal) INTER
                (nnegreal -> nnegreal -> nnegreal) INTER
                (negreal -> nposreal -> negreal) INTER
                (nposreal -> negreal -> negreal) INTER
                (nposreal -> nposreal -> nposreal) INTER
                (zreal -> x -> x) INTER
                (x -> zreal -> x))``,
   RW_TAC std_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val REAL_SUB_SUBTYPE = store_thm
  ("REAL_SUB_SUBTYPE",
   ``!x. $- IN ((posreal -> nposreal -> posreal) INTER
                (nnegreal -> negreal -> posreal) INTER
                (nnegreal -> nposreal -> nnegreal) INTER
                (negreal -> nnegreal -> negreal) INTER
                (nposreal -> posreal -> negreal) INTER
                (nposreal -> nnegreal -> nposreal) INTER
                (x -> zreal -> x))``,
   RW_TAC std_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL,
                  REAL_SUB_RZERO]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val REAL_MULT_SUBTYPE = store_thm
  ("REAL_MULT_SUBTYPE",
   ``$* IN ((posreal -> nnegreal -> nnegreal) INTER
            (nnegreal -> posreal -> nnegreal) INTER
            (posreal -> posreal -> posreal) INTER
            (negreal -> nposreal -> nnegreal) INTER
            (nposreal -> negreal -> nnegreal) INTER
            (negreal -> negreal -> posreal) INTER
            (posreal -> nposreal -> nposreal) INTER
            (nnegreal -> negreal -> nposreal) INTER
            (posreal -> negreal -> negreal) INTER
            (negreal -> nnegreal -> nposreal) INTER
            (nposreal -> posreal -> nposreal) INTER
            (negreal -> posreal -> negreal) INTER
            (zreal -> UNIV -> zreal) INTER
            (UNIV -> zreal -> zreal) INTER
            (nzreal -> nzreal -> nzreal))``,
   RW_TAC std_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL,
                  REAL_ENTIRE, IN_UNIV]
   >> PROVE_TAC [REAL_LE_MUL, REAL_LT_MUL, REAL_NEGNEG, REAL_MUL_LNEG,
                 REAL_MUL_RNEG, REAL_LE_LT_MUL, REAL_LT_LE_MUL]);

val REAL_DIV_SUBTYPE = store_thm
  ("REAL_DIV_SUBTYPE",
   ``$/ IN ((nnegreal -> posreal -> nnegreal) INTER
            (posreal -> posreal -> posreal) INTER
            (nposreal -> negreal -> nnegreal) INTER
            (negreal -> negreal -> posreal) INTER
            (nnegreal -> negreal -> nposreal) INTER
            (posreal -> negreal -> negreal) INTER
            (nposreal -> posreal -> nposreal) INTER
            (negreal -> posreal -> negreal) INTER
            (zreal -> nzreal -> zreal) INTER
            (nzreal -> nzreal -> nzreal))``,
   MP_TAC INV_SUBTYPE
   >> MP_TAC REAL_MULT_SUBTYPE
   >> RW_TAC std_ss [IN_FUNSET, IN_INTER, real_div, IN_UNIV]);

val REAL_MULT_EQ_CANCEL = store_thm
  ("REAL_MULT_EQ_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((x * y = z) = (y = inv x * z))``,
   Strip
   >> Suff `(x * y = z) = (x = 0) \/ (y = inv x * z)` >- PROVE_TAC []
   >> REWRITE_TAC [GSYM REAL_EQ_MUL_LCANCEL]
   >> RW_TAC std_ss [REAL_MUL_ASSOC, REAL_MUL_RINV]
   >> RW_TAC real_ss []);

val REAL_MULT_LE_CANCEL = store_thm
  ("REAL_MULT_LE_CANCEL",
   ``!x y z : real. 0 < x ==> ((x * y <= z) = (y <= inv x * z))``,
   Strip
   >> Suff `(x * y <= z) = (x * y <= x * (inv x * z))`
   >- PROVE_TAC [REAL_LE_LMUL]
   >> RW_TAC std_ss [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NE]
   >> RW_TAC real_ss []);

val INV_DIFF_SUC = store_thm
  ("INV_DIFF_SUC",
   ``!n : num. 0 < n ==> (1 / &n - 1 / (&n + 1) = 1 / &(n * (n + 1)))``,
   RW_TAC std_ss [GSYM REAL_INV_1OVER]
   >> Know `~(&n = 0) /\ ~(&n + 1 = 0)`
   >- RW_TAC arith_ss [REAL_LT_NZ, REAL_NZ_IMP_LT, GSYM REAL]
   >> RW_TAC std_ss [REAL_SUB_INV2]
   >> Know `&n + 1 - &n = 1` >- REAL_ARITH_TAC
   >> RW_TAC std_ss [GSYM REAL_INV_1OVER]
   >> RW_TAC std_ss [GSYM REAL, REAL_MUL, GSYM ADD1]);

val SUMS_EQ = store_thm
  ("SUMS_EQ",
   ``!f x. f sums x = summable f /\ (suminf f = x)``,
   PROVE_TAC [SUM_SUMMABLE, SUM_UNIQ, summable]);

val SER_POS = store_thm
  ("SER_POS",
   ``!f. summable f /\ (!n. 0 <= f n) ==> 0 <= suminf f``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`f`, `0`] SER_POS_LE)
   >> RW_TAC std_ss [sum]);

val SER_POS_MONO = store_thm
  ("SER_POS_MONO",
   ``!f. (!n. 0 <= f n) ==> mono (\n. sum (0, n) f)``,
   RW_TAC std_ss [mono]
   >> DISJ1_TAC
   >> HO_MATCH_MP_TAC TRIANGLE_2D_NUM
   >> Induct >- RW_TAC arith_ss [REAL_LE_REFL]
   >> RW_TAC std_ss [ADD_CLAUSES]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `sum (0, d + n) f`
   >> RW_TAC real_ss [sum]
   >> Q.PAT_ASSUM `!n. 0 <= f n` (MP_TAC o Q.SPEC `d + n`)
   >> REAL_ARITH_TAC);

val POS_SUMMABLE = store_thm
  ("POS_SUMMABLE",
   ``!f. (!n. 0 <= f n) /\ (?x. !n. sum (0, n) f <= x) ==> summable f``,
   RW_TAC std_ss [summable, sums, GSYM convergent]
   >> MATCH_MP_TAC SEQ_BCONV
   >> RW_TAC std_ss [SER_POS_MONO, netsTheory.MR1_BOUNDED]
   >> Q.EXISTS_TAC `x + 1`
   >> Q.EXISTS_TAC `N`
   >> RW_TAC arith_ss []
   >> RW_TAC std_ss [abs, SUM_POS]
   >> Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`)
   >> REAL_ARITH_TAC);

val SUMMABLE_LE = store_thm
  ("SUMMABLE_LE",
   ``!f x. summable f /\ (!n. sum (0, n) f <= x) ==> suminf f <= x``,
   Strip
   >> Suff `0 < suminf f - x ==> F` >- REAL_ARITH_TAC
   >> Strip
   >> Know `(\n. sum (0, n) f) --> suminf f`
   >- RW_TAC std_ss [GSYM sums, SUMMABLE_SUM]
   >> RW_TAC std_ss [SEQ]
   >> Q.EXISTS_TAC `suminf f - x`
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `N`
   >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   >> RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> Know `0 <= suminf f - sum (0, N) f`
   >- (rpt (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [abs]
   >> rpt (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val LE_INF = store_thm
  ("LE_INF",
   ``!p r. (?x. x IN p) /\ (!x. x IN p ==> r <= x) ==> r <= inf p``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   >> Q.SPEC_TAC (`~r`, `r`)
   >> RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   >> MATCH_MP_TAC REAL_SUP_LE_X
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_NEGNEG]);

val INF_LE = store_thm
  ("INF_LE",
   ``!p r.
       (?z. !x. x IN p ==> z <= x) /\ (?x. x IN p /\ x <= r) ==> inf p <= r``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   >> Q.SPEC_TAC (`~r`, `r`)
   >> RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   >> MATCH_MP_TAC REAL_X_LE_SUP
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

val REAL_LE_EPSILON = store_thm
  ("REAL_LE_EPSILON",
   ``!x y : real. (!e. 0 < e ==> x <= y + e) ==> x <= y``,
   RW_TAC std_ss []
   >> Suff `~(0 < x - y)` >- REAL_ARITH_TAC
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `!e. P e` MP_TAC
   >> RW_TAC std_ss []
   >> Know `!a b c : real. ~(a <= b + c) = c < a - b` >- REAL_ARITH_TAC
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> PROVE_TAC [REAL_DOWN]);

val SER_POS_COMPARE = store_thm
  ("SER_POS_COMPARE",
   ``!f g.
       (!n. 0 <= f n) /\ summable g /\ (!n. f n <= g n) ==>
       summable f /\ suminf f <= suminf g``,
   Reverse (rpt (STRONG_CONJ_TAC ORELSE STRIP_TAC))
   >- PROVE_TAC [SER_LE]
   >> MATCH_MP_TAC SER_COMPAR
   >> Q.EXISTS_TAC `g`
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `0`
   >> RW_TAC arith_ss [abs]);

val INF_GREATER = store_thm
  ("INF_GREATER",
   ``!p z.
       (?x. x IN p) /\ inf p < z ==>
       (?x. x IN p /\ x < z)``,
   RW_TAC std_ss []
   >> Suff `~(!x. x IN p ==> ~(x < z))` >- PROVE_TAC []
   >> REWRITE_TAC [GSYM real_lte]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `inf p < z` MP_TAC
   >> RW_TAC std_ss [GSYM real_lte]
   >> MATCH_MP_TAC LE_INF
   >> PROVE_TAC []);

val INF_CLOSE = store_thm
  ("INF_CLOSE",
   ``!p e.
       (?x. x IN p) /\ 0 < e ==> (?x. x IN p /\ x < inf p + e)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC INF_GREATER
   >> CONJ_TAC >- PROVE_TAC []
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val SUMINF_POS = store_thm
  ("SUMINF_POS",
   ``!f. (!n. 0 <= f n) /\ summable f ==> 0 <= suminf f``,
   RW_TAC std_ss []
   >> Know `0 = sum (0, 0) f` >- RW_TAC std_ss [sum]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC SER_POS_LE
   >> RW_TAC std_ss []);

val POW_HALF_SER = store_thm
  ("POW_HALF_SER",
   ``(\n. (1 / 2) pow (n + 1)) sums 1``,
   Know `(\n. (1 / 2) pow n) sums inv (1 - (1 / 2))`
   >- (MATCH_MP_TAC GP
       >> RW_TAC std_ss [abs, HALF_POS, REAL_LT_IMP_LE, HALF_LT_1])
   >> RW_TAC std_ss [ONE_MINUS_HALF, REAL_INV_INV, GSYM REAL_INV_1OVER,
                     GSYM ADD1, pow]
   >> Know `1 = inv 2 * 2`
   >- RW_TAC arith_ss [REAL_MUL_LINV, REAL_INJ]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> HO_MATCH_MP_TAC SER_CMUL
   >> RW_TAC std_ss []);

val SUMINF_ADD = store_thm
  ("SUMINF_ADD",
   ``!f g.
       summable f /\ summable g ==>
       summable (\n. f n + g n) /\
       (suminf f + suminf g = suminf (\n. f n + g n))``,
   RW_TAC std_ss [] \\
 ( Know `f sums suminf f /\ g sums suminf g` >- PROVE_TAC [SUMMABLE_SUM]
   >> STRIP_TAC
   >> Know `(\n. f n + g n) sums (suminf f + suminf g)`
   >- RW_TAC std_ss [SER_ADD]
   >> RW_TAC std_ss [SUMS_EQ] ));

val ABS_TRIANGLE = store_thm
  ("ABS_TRIANGLE",
   ``!x y z. abs (x - z) <= abs (x - y) + abs (y - z)``,
   RW_TAC std_ss [abs]
   >> rpt (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val ABS_TRANS = store_thm
  ("ABS_TRANS",
   ``!x y z e. abs (x - y) + abs (y - z) < e ==> abs (x - z) < e``,
   rpt GEN_TAC
   >> MP_TAC (Q.SPECL [`x`, `y`, `z`] ABS_TRIANGLE)
   >> REAL_ARITH_TAC);

val INCREASING_SEQ = store_thm
  ("INCREASING_SEQ",
   ``!f l.
       (!n. f n <= f (SUC n)) /\
       (!n. f n <= l) /\
       (!e. 0 < e ==> ?n. l < f n + e) ==>
       f --> l``,
   RW_TAC std_ss [SEQ, GREATER_EQ]
   >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `n`
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> Reverse (RW_TAC std_ss [abs])
   >- (Q.PAT_X_ASSUM `~x` MP_TAC
       >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n'`)
       >> REAL_ARITH_TAC)
   >> Know `?d. n' = n + d` >- PROVE_TAC [LESS_EQ_EXISTS]
   >> RW_TAC std_ss []
   >> Suff `l < f (n + d) + e` >- REAL_ARITH_TAC
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> Induct_on `d` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [ADD_CLAUSES]
   >> Q.PAT_X_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `n + d`)
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val SUM_PICK = store_thm
  ("SUM_PICK",
   ``!n k x. sum (0, n) (\m. if m = k then x else 0) = if k < n then x else 0``,
   Induct >- RW_TAC arith_ss [sum]
   >> RW_TAC arith_ss [sum, REAL_ADD_RID, REAL_ADD_LID]
   >> Suff `F` >- PROVE_TAC []
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> DECIDE_TAC);

val SUM_LT = store_thm
  ("SUM_LT",
   ``!f g m n.
       (!r. m <= r /\ r < n + m ==> f r < g r) /\ 0 < n ==>
       sum (m,n) f < sum (m,n) g``,
   RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> Cases_on `n` >- RW_TAC arith_ss []
   >> RW_TAC arith_ss []
   >> Induct_on `n'` >- RW_TAC arith_ss [sum, REAL_ADD_LID]
   >> ONCE_REWRITE_TAC [sum]
   >> Strip
   >> MATCH_MP_TAC REAL_LT_ADD2
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `a ==> b` MATCH_MP_TAC
       >> RW_TAC arith_ss [])
   >> RW_TAC arith_ss []);

val SUM_CONST = store_thm
  ("SUM_CONST",
   ``!n r. sum (0,n) (K r) = &n * r``,
   Induct >- RW_TAC real_ss [sum]
   >> RW_TAC bool_ss [sum, ADD1, K_THM, GSYM REAL_ADD, REAL_ADD_RDISTRIB]
   >> RW_TAC real_ss []);

val SUMINF_2D = store_thm
  ("SUMINF_2D",
   ``!f g h.
       (!m n. 0 <= f m n) /\ (!n. f n sums g n) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       (UNCURRY f o h) sums suminf g``,
   RW_TAC std_ss []
   >> RW_TAC std_ss [sums]
   >> Know `g sums suminf g` >- PROVE_TAC [SUMMABLE_SUM]
   >> Q.PAT_X_ASSUM `!n. P n` MP_TAC
   >> RW_TAC std_ss [SUMS_EQ, FORALL_AND_THM]
   >> MATCH_MP_TAC INCREASING_SEQ
   >> CONJ_TAC
   >- (RW_TAC std_ss [sum, o_THM, ADD_CLAUSES]
       >> Cases_on `h n`
       >> RW_TAC std_ss [UNCURRY_DEF]
       >> Q.PAT_X_ASSUM `!m n. 0 <= f m n` (MP_TAC o Q.SPECL [`q`, `r`])
       >> REAL_ARITH_TAC)
   >> Know `!m. 0 <= g m`
   >- (STRIP_TAC
       >> Suff `0 <= suminf (f m)` >- PROVE_TAC []
       >> MATCH_MP_TAC SER_POS
       >> PROVE_TAC [])
   >> STRIP_TAC
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> MP_TAC (Q.SPECL [`h`, `n`] NUM_2D_BIJ_BIG_SQUARE)
       >> ASM_REWRITE_TAC []
       >> STRIP_TAC
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0,k) g`
       >> Reverse CONJ_TAC
       >- (MATCH_MP_TAC SER_POS_LE
           >> PROVE_TAC [])
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0,k) (\m. sum (0,k) (f m))`
       >> Reverse CONJ_TAC
       >- (MATCH_MP_TAC SUM_LE
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM)
           >> MATCH_MP_TAC SER_POS_LE
           >> PROVE_TAC [])
       >> Suff
          `!j.
             j <= n ==>
             (sum (0, j) (UNCURRY f o h) =
              sum (0, k)
              (\m. sum (0, k)
               (\n. if (?i. i < j /\ (h i = (m, n))) then f m n else 0)))`
       >- (DISCH_THEN (MP_TAC o Q.SPEC `n`)
           >> REWRITE_TAC [LESS_EQ_REFL]
           >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
           >> MATCH_MP_TAC SUM_LE
           >> RW_TAC std_ss []
           >> MATCH_MP_TAC SUM_LE
           >> RW_TAC std_ss [REAL_LE_REFL])
       >> Induct >- RW_TAC arith_ss [sum, SUM_0]
       >> RW_TAC std_ss [sum]
       >> Q.PAT_X_ASSUM `p ==> q` MP_TAC
       >> RW_TAC arith_ss []
       >> Know
          `!m n.
             (?i. i < SUC j /\ (h i = (m,n))) =
             (?i. i < j /\ (h i = (m,n))) \/ (h j = (m, n))`
       >- (RW_TAC std_ss []
           >> Suff `!i. i < SUC j = i < j \/ (i = j)`
           >- PROVE_TAC []
           >> DECIDE_TAC)
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> Know
          `!m n.
             (if (?i. i < j /\ (h i = (m,n))) \/ (h j = (m,n)) then f m n
              else 0) =
             (if (?i. i < j /\ (h i = (m,n))) then f m n else 0) +
             (if (h j = (m,n)) then f m n else 0)`
       >- (Strip
           >> Suff `(?i. i < j /\ (h i = (m,n'))) ==> ~(h j = (m,n'))`
           >- PROVE_TAC [REAL_ADD_LID, REAL_ADD_RID]
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `BIJ a b c` MP_TAC
           >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]
           >> PROVE_TAC [prim_recTheory.LESS_REFL])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> RW_TAC std_ss [SUM_ADD]
       >> POP_ASSUM K_TAC
       >> Suff
          `(UNCURRY f o h) j =
           sum (0,k)
           (\m. sum (0,k) (\n. (if h j = (m,n) then f m n else 0)))`
       >- (KILL_TAC
           >> Q.SPEC_TAC
              (`(sum (0,k)
                 (\m.
                  sum (0,k)
                  (\n. if ?i. i < j /\ (h i = (m,n)) then f m n else 0)))`,
               `r1`)
           >> Q.SPEC_TAC
              (`sum (0,k)
                (\m. sum (0,k) (\n. (if h j = (m,n) then f m n else 0)))`,
               `r2`)
           >> RW_TAC std_ss [])
       >> Cases_on `h j`
       >> RW_TAC std_ss [o_THM, UNCURRY_DEF]
       >> Know
          `!m n.
             (if (q = m) /\ (r = n) then f m n else 0) =
             (if (n = r) then if (m = q) then f m n else 0 else 0)`
       >- PROVE_TAC []
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> Q.PAT_X_ASSUM `a SUBSET b` MP_TAC
       >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, IN_CROSS]
       >> Suff `q < k /\ r < k`
       >- RW_TAC std_ss [SUM_PICK]
       >> POP_ASSUM (MP_TAC o Q.SPEC `h (j:num)`)
       >> Suff `j < n`
       >- (RW_TAC std_ss []
           >> PROVE_TAC [])
       >> DECIDE_TAC)
   >> RW_TAC std_ss []
   >> Know `?M. 0 < M /\ suminf g < sum (0, M) g + e / 2`
   >- (Know `g sums suminf g` >- PROVE_TAC [SUMMABLE_SUM]
       >> RW_TAC std_ss [sums, SEQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `e / 2`)
       >> RW_TAC std_ss [REAL_LT_HALF1, GREATER_EQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `SUC N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> Know `sum (0, SUC N) g <= suminf g`
       >- (MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [])
       >> Reverse (RW_TAC arith_ss [abs])
       >- (Suff `F` >- PROVE_TAC []
           >> POP_ASSUM K_TAC
           >> POP_ASSUM MP_TAC
           >> POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> Q.EXISTS_TAC `SUC N`
       >> CONJ_TAC >- DECIDE_TAC
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss []
   >> Suff `?k. sum (0, M) g < sum (0, k) (UNCURRY f o h) + e / 2`
   >- (Strip
       >> Q.EXISTS_TAC `k`
       >> Know
          `sum (0, M) g + e / 2 < sum (0, k) (UNCURRY f o h) + (e / 2 + e / 2)`
       >- (POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> REWRITE_TAC [REAL_HALF_DOUBLE]
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> Know `!m. ?N. g m < sum (0, N) (f m) + (e / 2) / & M`
   >- (Know `!m. f m sums g m`
       >- RW_TAC std_ss [SUMS_EQ]
       >> RW_TAC std_ss [sums, SEQ]
       >> POP_ASSUM (MP_TAC o Q.SPECL [`m`, `(e / 2) / & M`])
       >> Know `0 < (e / 2) / & M`
       >- RW_TAC arith_ss [REAL_LT_DIV, REAL_NZ_IMP_LT]
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> RW_TAC std_ss [GREATER_EQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> Know `sum (0, N) (f m) <= g m`
       >- (Q.PAT_X_ASSUM `!n. P n = Q n` (REWRITE_TAC o wrap o GSYM)
           >> MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [])
       >> Reverse (RW_TAC arith_ss [abs])
       >- (POP_ASSUM K_TAC
           >> Suff `F` >- PROVE_TAC []
           >> NTAC 2 (POP_ASSUM MP_TAC)
           >> REAL_ARITH_TAC)
       >> Q.EXISTS_TAC `N`
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
   >> RW_TAC std_ss []
   >> Know `?c. M <= c /\ !m. m < M ==> N m <= c`
   >- (KILL_TAC
       >> Induct_on `M` >- RW_TAC arith_ss []
       >> Strip
       >> Q.EXISTS_TAC `MAX (SUC c) (N M)`
       >> RW_TAC arith_ss [X_LE_MAX, LT_SUC]
       >> PROVE_TAC [LESS_EQ_REFL, LE])
   >> Strip
   >> MP_TAC (Q.SPECL [`h`, `c`] NUM_2D_BIJ_SMALL_SQUARE)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (Q.X_CHOOSE_TAC `k`)
   >> Q.EXISTS_TAC `k`
   >> MATCH_MP_TAC REAL_LTE_TRANS
   >> Q.EXISTS_TAC `sum (0, M) (\m. sum (0, N m) (f m) + e / 2 / &M)`
   >> CONJ_TAC
   >- (MATCH_MP_TAC SUM_LT
       >> RW_TAC arith_ss [])
   >> RW_TAC std_ss [SUM_ADD, GSYM K_PARTIAL, SUM_CONST]
   >> Know `!x. & M * (x / & M) = x`
   >- (RW_TAC std_ss [real_div]
       >> Suff `(& M * inv (& M)) * x = x`
       >- PROVE_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM]
       >> Suff `~(& M = 0)` >- RW_TAC std_ss [REAL_MUL_RINV, REAL_MUL_LID]
       >> RW_TAC arith_ss [REAL_INJ])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [REAL_LE_RADD]
   >> Suff
      `sum (0,M) (\m. sum (0,N m) (f m)) =
       sum (0, k)
       (\k.
          if ?m n. m < M /\ n < N m /\ (h k = (m, n)) then (UNCURRY f o h) k
          else 0)`
   >- (RW_TAC std_ss []
       >> MATCH_MP_TAC SUM_LE
       >> RW_TAC std_ss [o_THM, REAL_LE_REFL]
       >> Cases_on `h r`
       >> RW_TAC std_ss [UNCURRY_DEF])
   >> NTAC 3 (POP_ASSUM MP_TAC)
   >> Q.PAT_X_ASSUM `BIJ h a b` MP_TAC
   >> KILL_TAC
   >> RW_TAC std_ss []
   >> Induct_on `M` >- RW_TAC arith_ss [sum, SUM_ZERO]
   >> RW_TAC arith_ss [sum, LT_SUC]
   >> Q.PAT_X_ASSUM `a ==> b` K_TAC
   >> Know
      `!k'.
         (?m n. (m < M \/ (m = M)) /\ n < N m /\ (h k' = (m, n))) =
         (?m n. m < M /\ n < N m /\ (h k' = (m, n))) \/
         (?n. n < N M /\ (h k' = (M, n)))`
   >- PROVE_TAC []
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Know
      `!k'.
         (if (?m n. m < M /\ n < N m /\ (h k' = (m,n))) \/
             (?n. n < N M /\ (h k' = (M,n)))
          then UNCURRY f (h k')
          else 0) =
         (if (?m n. m < M /\ n < N m /\ (h k' = (m,n))) then UNCURRY f (h k')
          else 0) +
         (if (?n. n < N M /\ (h k' = (M,n))) then UNCURRY f (h k')
          else 0)`
   >- (STRIP_TAC
       >> Suff
          `(?m n. m < M /\ n < N m /\ (h k' = (m,n))) ==>
           ~(?n. n < N M /\ (h k' = (M,n)))`
       >- PROVE_TAC [REAL_ADD_RID, REAL_ADD_LID]
       >> Cases_on `h k'`
       >> RW_TAC arith_ss [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [SUM_ADD, REAL_EQ_LADD]
   >> Know `N M <= c` >- PROVE_TAC []
   >> POP_ASSUM K_TAC
   >> Q.SPEC_TAC (`N M`, `l`)
   >> Induct >- RW_TAC real_ss [sum, SUM_0]
   >> RW_TAC arith_ss [sum, LT_SUC]
   >> Q.PAT_X_ASSUM `a ==> b` K_TAC
   >> Know
      `!k'.
         (?n. (n < l \/ (n = l)) /\ (h k' = (M,n))) =
         (?n. n < l /\ (h k' = (M,n))) \/ (h k' = (M, l))`
   >- PROVE_TAC []
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Know
      `!k'.
         (if (?n. n < l /\ (h k' = (M,n))) \/ (h k' = (M, l)) then
            UNCURRY f (h k')
          else 0) =
         (if (?n. n < l /\ (h k' = (M,n))) then UNCURRY f (h k') else 0) +
         (if (h k' = (M, l)) then UNCURRY f (h k') else 0)`
   >- (STRIP_TAC
       >> Suff `(?n. n < l /\ (h k' = (M,n))) ==> ~(h k' = (M, l))`
       >- PROVE_TAC [REAL_ADD_LID, REAL_ADD_RID]
       >> Cases_on `h k'`
       >> RW_TAC arith_ss [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [SUM_ADD, REAL_EQ_LADD]
   >> Q.PAT_X_ASSUM `a SUBSET b` MP_TAC
   >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_COUNT, IN_IMAGE]
   >> POP_ASSUM (MP_TAC o Q.SPEC `(M, l)`)
   >> RW_TAC arith_ss []
   >> Suff `!k'. (h k' = (M, l)) = (k' = x')`
   >- (RW_TAC std_ss [SUM_PICK, o_THM]
       >> Q.PAT_X_ASSUM `(M,l) = a` (REWRITE_TAC o wrap o GSYM)
       >> RW_TAC std_ss [UNCURRY_DEF])
   >> Q.PAT_X_ASSUM `BIJ h a b` MP_TAC
   >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]
   >> PROVE_TAC []);

val REAL_INV_INJ = store_thm
  ("REAL_INV_INJ",
   ``!x y. (inv x = inv y) = (x = y)``,
   RW_TAC std_ss []
   >> Reverse EQ_TAC >- RW_TAC std_ss []
   >> RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_INV_INV]
   >> RW_TAC std_ss []);

val POW_HALF_SMALL = store_thm
  ("POW_HALF_SMALL",
   ``!e. 0 < e ==> ?n. (1 / 2) pow n < e``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `1 / 2` SEQ_POWER)
   >> RW_TAC std_ss [abs, HALF_LT_1, HALF_POS, REAL_LT_IMP_LE, SEQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss [REAL_SUB_RZERO, POW_HALF_POS, REAL_LT_IMP_LE,
                      GREATER_EQ]
   >> PROVE_TAC [LESS_EQ_REFL]);

val LOG2_SUC = store_thm
  ("LOG2_SUC",
   ``!n t.
       0 < n /\ 2 * log2 (n + 1) <= t ==>
       (1 / 2) pow t <= 1 / &n - 1 / (&n + 1)``,
   REPEAT STRIP_TAC
   >> RW_TAC std_ss [INV_DIFF_SUC, POW_HALF_EXP, GSYM REAL_INV_1OVER]
   >> MATCH_MP_TAC REAL_LE_INV_LE
   >> REPEAT STRIP_TAC
   >- (MATCH_MP_TAC REAL_NZ_IMP_LT
       >> RW_TAC arith_ss [GSYM ADD1, MULT])
   >> RW_TAC std_ss [REAL_LE]
   >> Suff `(n + 1) * (n + 1) <= 2 EXP t`
   >- (Suff `n * (n + 1) <= (n + 1) * (n + 1)` >- DECIDE_TAC
       >> RW_TAC std_ss [GSYM ADD1, MULT]
       >> DECIDE_TAC)
   >> Suff `(n + 1) EXP 2 <= (2 EXP log2 (n + 1)) EXP 2`
   >- (RW_TAC bool_ss [TWO, EXP, EXP_1, EXP_MULT]
       >> POP_ASSUM MP_TAC
       >> ONCE_REWRITE_TAC [MULT_COMM]
       >> RW_TAC std_ss [GSYM TWO]
       >> MATCH_MP_TAC LESS_EQ_TRANS
       >> Q.EXISTS_TAC `2 EXP (2 * log2 (n + 1))`
       >> CONJ_TAC >- RW_TAC std_ss []
       >> MATCH_MP_TAC EXP1_MONO_LE
       >> RW_TAC arith_ss [])
   >> MATCH_MP_TAC EXP2_MONO_LE
   >> MP_TAC (Q.SPEC `n + 1` LOG2_LOWER)
   >> RW_TAC arith_ss []);

val LE_SEQ_IMP_LE_LIM = store_thm
  ("LE_SEQ_IMP_LE_LIM",
   ``!x y f. (!n. x <= f n) /\ f --> y ==> x <= y``,
   RW_TAC std_ss [SEQ]
   >> MATCH_MP_TAC REAL_LE_EPSILON
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o Q.SPEC `N`)
   >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   >> RW_TAC arith_ss [abs]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val SER_POS_COMPAR = store_thm
  ("SER_POS_COMPAR",
   ``!f g. (!n. 0 <= f n) /\ summable g /\ (!n. f n <= g n) ==> summable f``,
   PROVE_TAC [SER_POS_COMPARE]);

val SUM_SUMINF = store_thm
  ("SUM_SUMINF",
   ``!p f n.
       (summable (\m. if m < n then f m else 0) ==>
        p (suminf (\m. if m < n then f m else 0))) ==>
       p (sum (0, n) f)``,
   RW_TAC std_ss []
   >> Suff `(\m. (if m < n then f m else 0)) sums (sum (0, n) f)`
   >- (RW_TAC std_ss [SUMS_EQ]
       >> PROVE_TAC [])
   >> Suff `sum (0, n) f = sum (0, n) (\m. (if m < n then f m else 0))`
   >- (Rewr
       >> MATCH_MP_TAC SER_0
       >> RW_TAC arith_ss [])
   >> MATCH_MP_TAC SUM_EQ
   >> RW_TAC arith_ss []);

val SUMS_PICK = store_thm
  ("SUMS_PICK",
   ``!k x. (\n. if n = k then x else 0) sums x``,
   RW_TAC std_ss []
   >> Know `sum (0, SUC k) (\n. if n = k then x else 0) = x`
   >- RW_TAC arith_ss [SUM_PICK]
   >> DISCH_THEN (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV o wrap o SYM)
   >> MATCH_MP_TAC SER_0
   >> RW_TAC arith_ss []);

val SUM_REORDER_LE = store_thm
  ("SUM_REORDER_LE",
   ``!f n1 n2 j1 j2.
       (!n. 0 <= f n) /\ INJ j1 (count n1) UNIV /\
       IMAGE j1 (count n1) SUBSET IMAGE j2 (count n2) ==>
       sum (0, n1) (f o j1) <= sum (0, n2) (f o j2)``,
   Induct_on `n1`
   >- (RW_TAC std_ss [sum, COUNT_ZERO, EMPTY_SUBSET, IMAGE_EMPTY]
       >> Suff `!n. 0 <= (f o j2) n` >- RW_TAC std_ss [SUM_POS]
       >> RW_TAC std_ss [o_THM])
   >> RW_TAC std_ss [sum, o_THM, INSERT_SUBSET, COUNT_SUC, IMAGE_INSERT,
                     IN_IMAGE, IN_COUNT]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `f (j1 n1) + sum (0,n2) ((\a. if a = j1 n1 then 0 else f a) o j2)`
   >> CONJ_TAC
   >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [REAL_ADD_COMM]))
       >> RW_TAC std_ss [REAL_LE_LADD]
       >> Know
          `sum (0, n1) (f o j1) =
           sum (0, n1) ((\a. (if a = j2 x then 0 else f a)) o j1)`
       >- (MATCH_MP_TAC SUM_EQ
           >> RW_TAC arith_ss [o_THM]
           >> Suff `F` >- PROVE_TAC []
           >> Q.PAT_X_ASSUM `INJ j1 X Y` MP_TAC
           >> RW_TAC std_ss [INJ_DEF, IN_INSERT, IN_COUNT, IN_UNIV]
           >> PROVE_TAC [prim_recTheory.LESS_NOT_EQ])
       >> Rewr
       >> Q.PAT_X_ASSUM `!f n2. P f n2` MATCH_MP_TAC
       >> RW_TAC std_ss [REAL_LE_REFL]
       >> Q.PAT_X_ASSUM `INJ j1 X Y` MP_TAC
       >> RW_TAC bool_ss [INJ_DEF, IN_INSERT, IN_COUNT, IN_UNIV])
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `f (j1 n1) + sum (0, n2) (\i. if i = x then 0 else f (j2 i))`
   >> CONJ_TAC
   >- (RW_TAC std_ss [REAL_LE_LADD]
       >> MATCH_MP_TAC SUM_LE
       >> RW_TAC arith_ss [o_THM, REAL_LE_REFL])
   >> Know
      `f o j2 =
       (\i. (if i = x then 0 else f (j2 i)) +
            (if i = x then f (j2 i) else 0))`
   >- (FUN_EQ_TAC
       >> RW_TAC real_ss [o_THM])
   >> Rewr
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [REAL_ADD_COMM]))
   >> RW_TAC real_ss [SUM_ADD, SUM_PICK, REAL_LE_LADD, REAL_LE_REFL]);

val SER_BIJ_COMPRESS1 = store_thm
  ("SER_BIJ_COMPRESS1",
   ``!f h s.
       (!n. 0 <= f n) /\ summable f /\ BIJ h UNIV s /\
       (!n. ~(n IN s) ==> (f n = 0)) ==>
       (f o h) sums suminf f``,
   RW_TAC std_ss [sums, SEQ]
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> RW_TAC std_ss [abs]
   >> Know `!n. sum (0, n) (f o h) <= suminf f`
   >- (Know `!n. ?N. !m. m < n ==> h m < N`
       >- (Induct >- RW_TAC arith_ss []
           >> POP_ASSUM MP_TAC
           >> STRIP_TAC
           >> Q.EXISTS_TAC `SUC (MAX N (h n))`
           >> STRIP_TAC
           >> DISCH_THEN (MP_TAC o REWRITE_RULE [LT_SUC])
           >> Know `!a b. a < SUC b = a <= b`
           >- (Cases >> STRIP_TAC >> KILL_TAC >> DECIDE_TAC)
           >> RW_TAC std_ss [X_LE_MAX]
           >> PROVE_TAC [LESS_IMP_LESS_OR_EQ, LESS_EQ_REFL])
       >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
       >> STRIP_TAC
       >> STRIP_TAC
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0, N n) f`
       >> REVERSE CONJ_TAC
       >- (MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [])
       >> Know `sum (0, N n) f = sum (0, N n) (f o I)`
       >- RW_TAC std_ss [I_o_ID]
       >> Rewr
       >> MATCH_MP_TAC SUM_REORDER_LE
       >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
       >> RW_TAC std_ss [INJ_DEF, BIJ_DEF, IN_UNIV, IN_COUNT, SUBSET_DEF,
                         I_THM, IN_IMAGE]
       >> PROVE_TAC [])
   >> STRIP_TAC
   >> Know `!n. 0 <= suminf f - sum (0, n) (f o h)`
   >- (STRIP_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> REAL_ARITH_TAC)
   >> Rewr
   >> Know `f sums suminf f` >- PROVE_TAC [SUMMABLE_SUM]
   >> RW_TAC std_ss [sums, SEQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss [GREATER_EQ]
   >> (MP_TAC o
       Q.SPECL [`h`, `s`, `count N INTER s`] o
       INST_TYPE [alpha |-> ``:num``])
      BIJ_FINITE_SUBSET
   >> Know `FINITE (count N INTER s)`
   >- PROVE_TAC [FINITE_COUNT, FINITE_INTER, INTER_COMM]
   >> Rewr
   >> RW_TAC std_ss [INTER_SUBSET, IN_INTER]
   >> Q.EXISTS_TAC `N'`
   >> RW_TAC std_ss []
   >> Suff `suminf f - e < sum (0, n) (f o h)` >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LTE_TRANS
   >> Q.EXISTS_TAC `sum (0, N) f`
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `!n. P n ==> Q n < e` (MP_TAC o Q.SPEC `N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> RW_TAC arith_ss [abs]
       >- (POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> Suff `F` >- PROVE_TAC []
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> Suff `sum (0, N) f <= suminf f` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC SER_POS_LE
       >> RW_TAC std_ss [])
   >> Know
      `sum (0, N) f =
       sum (0, N) ((\x. sum_CASE x f (K 0)) o
                   (\n. if n IN s then INL n else INR n))`
   >- (MATCH_MP_TAC SUM_EQ
       >> RW_TAC std_ss [sum_case_def, o_THM, K_DEF])
   >> Rewr
   >> Know
      `sum (0, n) (f o h) =
       sum (0, n + N)
       ((\x. sum_CASE x f (K 0)) o
        (\i. if i < n then INL (h i) else INR (i - n)))`
   >- (KILL_TAC
       >> REVERSE (Induct_on `N`)
       >- RW_TAC arith_ss [sum, o_THM, ADD_CLAUSES, K_THM, REAL_ADD_RID]
       >> RW_TAC arith_ss []
       >> MATCH_MP_TAC SUM_EQ
       >> RW_TAC arith_ss [sum_case_def, o_THM])
   >> Rewr
   >> MATCH_MP_TAC SUM_REORDER_LE
   >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
   >> ASM_SIMP_TAC (srw_ss()) [sumTheory.FORALL_SUM]
   >> BasicProvers.NORM_TAC std_ss [SUBSET_DEF, IN_IMAGE, INJ_DEF, IN_UNIV,
                                    IN_COUNT, INJ_DEF, BIJ_DEF, SURJ_DEF] >|
   [Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `n'`)
    >> RW_TAC std_ss []
    >> Q.EXISTS_TAC `y`
    >> RW_TAC std_ss []
    >> Suff `y < n` >- RW_TAC arith_ss []
    >> Q.PAT_X_ASSUM `!n. P n ==> Q n` (MP_TAC o Q.SPEC `y`)
    >> RW_TAC std_ss [IN_COUNT]
    >> POP_ASSUM MP_TAC
    >> Q.PAT_X_ASSUM `N' <= n` MP_TAC
    >> KILL_TAC
    >> DECIDE_TAC,
    Q.EXISTS_TAC `n' + n`
    >> RW_TAC arith_ss []]);

val SER_BIJ_COMPRESS2 = store_thm
  ("SER_BIJ_COMPRESS2",
   ``!f h s.
       (!n. 0 <= f n) /\ summable (f o h) /\ BIJ h UNIV s /\
       (!n. ~(n IN s) ==> (f n = 0)) ==>
       f sums suminf (f o h)``,
   RW_TAC std_ss [sums, SEQ]
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> RW_TAC std_ss [abs]
   >> Know `!n. sum (0, n) f <= suminf (f o h)`
   >- (STRIP_TAC
       >> (MP_TAC o
           Q.SPECL [`h`, `s`, `count n INTER s`] o
           INST_TYPE [alpha |-> ``:num``])
           BIJ_FINITE_SUBSET
       >> Know `FINITE (count n INTER s)`
       >- PROVE_TAC [FINITE_COUNT, FINITE_INTER, INTER_COMM]
       >> Rewr
       >> RW_TAC std_ss [INTER_SUBSET, IN_INTER]
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0, N) (f o h)`
       >> REVERSE CONJ_TAC
       >- (MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [o_THM])
       >> Know
       `sum (0, n) f =
        sum (0, n) ((\x. sum_CASE x f (K 0)) o
                    (\n. if n IN s then INL n else INR n))`
        >- (MATCH_MP_TAC SUM_EQ
            >> RW_TAC std_ss [sum_case_def, o_THM, K_DEF])
       >> Rewr
       >> Know
       `sum (0, N) (f o h) =
        sum (0, N + n)
        ((\x. sum_CASE x f (K 0)) o
         (\i. if i < N then INL (h i) else INR (i - N)))`
       >- (KILL_TAC
           >> REVERSE (Induct_on `n`)
           >- RW_TAC arith_ss [sum, o_THM, ADD_CLAUSES, K_THM, REAL_ADD_RID]
           >> RW_TAC arith_ss []
           >> MATCH_MP_TAC SUM_EQ
           >> RW_TAC arith_ss [sum_case_def, o_THM])
       >> Rewr
       >> MATCH_MP_TAC SUM_REORDER_LE
       >> ASM_SIMP_TAC (srw_ss()) [sumTheory.FORALL_SUM]
       >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
       >> BasicProvers.NORM_TAC std_ss [SUBSET_DEF, IN_IMAGE, INJ_DEF, IN_UNIV,
                                        IN_COUNT, INJ_DEF, BIJ_DEF, SURJ_DEF] >|
       [Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `n'`)
        >> RW_TAC std_ss []
        >> Q.EXISTS_TAC `y`
        >> Suff `y < N` >- RW_TAC arith_ss []
        >> Q.PAT_X_ASSUM `!n'. N <= n' ==> P n'` (MP_TAC o Q.SPEC `y`)
        >> RW_TAC std_ss [IN_COUNT]
        >> POP_ASSUM MP_TAC
        >> KILL_TAC
        >> DECIDE_TAC,
        Q.EXISTS_TAC `n' + N`
        >> RW_TAC arith_ss []])
   >> STRIP_TAC
   >> Know `!n. 0 <= suminf (f o h) - sum (0, n) f`
   >- (STRIP_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> REAL_ARITH_TAC)
   >> Rewr
   >> Know `(f o h) sums suminf (f o h)` >- PROVE_TAC [SUMMABLE_SUM]
   >> RW_TAC std_ss [sums, SEQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss [GREATER_EQ]
   >> Know `!n. ?N. !m. m < n ==> h m < N`
   >- (Induct >- RW_TAC arith_ss []
       >> POP_ASSUM MP_TAC
       >> STRIP_TAC
       >> Q.EXISTS_TAC `SUC (MAX N' (h n))`
       >> STRIP_TAC
       >> DISCH_THEN (MP_TAC o REWRITE_RULE [LT_SUC])
       >> Know `!a b. a < SUC b = a <= b`
       >- (Cases >> STRIP_TAC >> KILL_TAC >> DECIDE_TAC)
       >> RW_TAC std_ss [X_LE_MAX]
       >> PROVE_TAC [LESS_IMP_LESS_OR_EQ, LESS_EQ_REFL])
   >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
   >> STRIP_TAC
   >> Q.EXISTS_TAC `N' N`
   >> RW_TAC std_ss []
   >> Suff `suminf (f o h) - e < sum (0, n) f` >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LTE_TRANS
   >> Q.EXISTS_TAC `sum (0, N) (f o h)`
   >> CONJ_TAC
   >- (Suff `suminf (f o h) - sum (0, N) (f o h) < e` >- REAL_ARITH_TAC
       >> Q.PAT_X_ASSUM `!n. N <= n ==> P n` (MP_TAC o Q.SPEC `N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> RW_TAC arith_ss [abs]
       >> Suff `F` >- PROVE_TAC []
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> Suff `sum (0, N) (f o h) <= suminf (f o h)` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC SER_POS_LE
       >> RW_TAC std_ss [o_THM])
   >> Know `sum (0, n) f = sum (0, n) (f o I)`
   >- RW_TAC std_ss [I_o_ID]
   >> Rewr
   >> MATCH_MP_TAC SUM_REORDER_LE
   >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
   >> RW_TAC std_ss [INJ_DEF, BIJ_DEF, IN_UNIV, IN_COUNT, SUBSET_DEF,
                     I_THM, IN_IMAGE]
   >> Q.PAT_X_ASSUM `N' N <= n` MP_TAC
   >> Suff `h x' < N' N` >- (KILL_TAC >> DECIDE_TAC)
   >> PROVE_TAC []);

val SER_BIJ_COMPRESS = store_thm
  ("SER_BIJ_COMPRESS",
   ``!f h s l.
       (!n. 0 <= f n) /\ BIJ h UNIV s /\ (!n. ~(n IN s) ==> (f n = 0)) ==>
       ((f o h) sums l = f sums l)``,
   RW_TAC std_ss [SUMS_EQ]
   >> EQ_TAC >|
   [STRIP_TAC
    >> REWRITE_TAC [GSYM SUMS_EQ]
    >> RW_TAC std_ss []
    >> PROVE_TAC [SER_BIJ_COMPRESS2],
    STRIP_TAC
    >> REWRITE_TAC [GSYM SUMS_EQ]
    >> RW_TAC std_ss []
    >> PROVE_TAC [SER_BIJ_COMPRESS1]]);

val SER_BIJ = store_thm
  ("SER_BIJ",
   ``!f g h l.
       (!n. 0 <= f n) /\ BIJ h UNIV UNIV ==>
       ((f o h) sums l = f sums l)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC SER_BIJ_COMPRESS
   >> Q.EXISTS_TAC `UNIV`
   >> RW_TAC std_ss [IN_UNIV]);

val SUMS_ZERO = store_thm
  ("SUMS_ZERO",
   ``(K 0) sums 0``,
   RW_TAC real_ss [sums, SEQ, SUM_CONST, abs, REAL_SUB_REFL, REAL_LE_REFL]);

val REAL_MUL_IDEMPOT = store_thm
  ("REAL_MUL_IDEMPOT",
   ``!r : real. (r * r = r) = (r = 0) \/ (r = 1)``,
   GEN_TAC
   >> Reverse EQ_TAC
   >- (RW_TAC real_ss [] >> RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_LID])
   >> RW_TAC std_ss []
   >> Know `r * r = 1 * r` >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_EQ_RMUL]);

val GP_REC = store_thm
  ("GP_REC",
   ``!a b x : real. abs b < 1 /\ (x = a + b * x) ==> (x = a / (1 - b))``,
   RW_TAC std_ss []
   >> Know `x * (1 - b) = a`
   >- (RW_TAC std_ss [REAL_SUB_LDISTRIB, REAL_MUL_RID]
       >> ONCE_REWRITE_TAC [REAL_MUL_SYM]
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> Know `~(1 - b = 0)`
   >- (POP_ASSUM MP_TAC
       >> RW_TAC real_ss [abs]
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> REPEAT STRIP_TAC
   >> Suff `x * (1 - b) = (a / (1 - b)) * (1 - b)`
   >- (POP_ASSUM K_TAC
       >> RW_TAC std_ss [REAL_EQ_RMUL])
   >> RW_TAC std_ss [real_div, GSYM REAL_INV_1OVER, GSYM REAL_MUL_ASSOC,
                     REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_EQ = store_thm
  ("REAL_DIV_EQ",
   ``!a b c d : real.
       ~(b = 0) /\ ~(d = 0) /\ (a * d = c * b) ==> (a / b = c / d)``,
   RW_TAC std_ss [real_div]
   >> Suff `(a * inv b) * b = (c * inv d) * b`
   >- RW_TAC std_ss [REAL_EQ_RMUL]
   >> RW_TAC std_ss [GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID]
   >> Suff `a * d = (c * (inv d * b)) * d`
   >- RW_TAC std_ss [REAL_EQ_RMUL]
   >> Know `inv d * b = b * inv d` >- PROVE_TAC [REAL_MUL_SYM]
   >> Rewr
   >> RW_TAC std_ss [GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_ADD = store_thm
  ("REAL_DIV_ADD",
   ``!x y z : real. x / z + y / z = (x + y) / z``,
   RW_TAC std_ss [real_div, GSYM REAL_ADD_RDISTRIB]);

val REAL_DIV_MUL = store_thm
  ("REAL_DIV_MUL",
   ``!x y z. ~(x = 0) /\ ~(z = 0) ==> ((x * y) / (x * z) = y / z)``,
   PROVE_TAC [REAL_DIV_MUL2]);

val REAL_LDIV_EQ = store_thm
  ("REAL_LDIV_EQ",
   ``!x y z. ~(y = 0) /\ (x = y * z) ==> (x / y = z)``,
   REPEAT STRIP_TAC
   >> Know `z = z / 1` >- RW_TAC std_ss [REAL_OVER1]
   >> Rewr'
   >> MATCH_MP_TAC REAL_DIV_EQ
   >> RW_TAC real_ss []
   >> REAL_ARITH_TAC);

val ADD1_HALF_MULT = store_thm
  ("ADD1_HALF_MULT",
   ``!x y. x + (1 / 2) * y = (1 / 2) * (2 * x + y)``,
   RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC]
   >> Know `(1 / 2) * 2 = 2 * (1 / 2)` >- PROVE_TAC [REAL_MUL_SYM]
   >> Rewr
   >> RW_TAC std_ss [HALF_CANCEL, REAL_MUL_LID]);

val ADD2_HALF_MULT = store_thm
  ("ADD2_HALF_MULT",
   ``!x y. (1 / 2) * y + x = (1 / 2) * (y + 2 * x)``,
   PROVE_TAC [ADD1_HALF_MULT, REAL_ADD_SYM]);

val HALF_CANCEL_REV = store_thm
  ("HALF_CANCEL_REV",
   ``(1 / 2) * 2 = 1``,
   PROVE_TAC [HALF_CANCEL, REAL_MUL_SYM]);

val HALF_CANCEL_MULT = store_thm
  ("HALF_CANCEL_MULT",
   ``!x. 2 * ((1 / 2) * x) = x``,
   RW_TAC std_ss [HALF_CANCEL, REAL_MUL_ASSOC, REAL_MUL_LID]);

val HALF_CANCEL_MULT_REV = store_thm
  ("HALF_CANCEL_MULT_REV",
   ``!x. (1 / 2) * (2 * x) = x``,
   RW_TAC std_ss [HALF_CANCEL_REV, REAL_MUL_ASSOC, REAL_MUL_LID]);

val ABS_EQ = store_thm
  ("ABS_EQ",
   ``!x y. (!e. 0 < e ==> abs (x - y) < e) ==> (x = y)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC SEQ_UNIQ
   >> Q.EXISTS_TAC `\n. x`
   >> RW_TAC std_ss [SEQ_CONST]
   >> RW_TAC std_ss [SEQ]);

val SEQ_SANDWICH = store_thm
  ("SEQ_SANDWICH",
   ``!f g h l.
       f --> l /\ h --> l /\ (!n. f n <= g n /\ g n <= h n) ==> g --> l``,
   RW_TAC std_ss [SEQ, GREATER_EQ]
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `e`)
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `MAX N N'`
   >> RW_TAC std_ss [MAX_LE_X]
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `n`)
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `n`)
   >> RW_TAC std_ss []
   >> REPEAT (POP_ASSUM MP_TAC)
   >> DISCH_THEN (MP_TAC o Q.SPEC `n`)
   >> RW_TAC std_ss [abs]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val POW_LE_1 = store_thm
  ("POW_LE_1",
   ``!p n. 0 < p /\ p <= 1 ==> p pow n <= 1``,
   STRIP_TAC
   >> Induct
   >> RW_TAC std_ss [pow, REAL_LE_REFL]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `p * 1`
   >> Reverse CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_LE_LMUL]);

val POW_LE_1_MONO = store_thm
  ("POW_LE_1_MONO",
   ``!p m n. 0 < p /\ p <= 1 /\ m <= n ==> p pow n <= p pow m``,
   RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`n`, `n`)
   >> Q.SPEC_TAC (`m`, `m`)
   >> HO_MATCH_MP_TAC TRIANGLE_2D_NUM
   >> Induct >- RW_TAC real_ss [REAL_LE_REFL]
   >> RW_TAC std_ss [ADD_CLAUSES, pow]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `1 * p pow (d + m)`
   >> Reverse CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_LE_RMUL, REAL_POW_LT]);

val REAL_LE_MUL_EPSILON = store_thm
  ("REAL_LE_MUL_EPSILON",
   ``!x y. (!z. 0 < z /\ z < 1 ==> z * x <= y) ==>
                x <= y``,
    REPEAT STRIP_TAC
    >> Cases_on `x = 0`
    >- (Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `1/2`) >> RW_TAC real_ss [REAL_HALF_BETWEEN])
    >> Cases_on `0 < x`
    >- (MATCH_MP_TAC REAL_LE_EPSILON
        >> RW_TAC std_ss [GSYM REAL_LE_SUB_RADD]
        >> Cases_on `e < x`
        >- (MATCH_MP_TAC REAL_LE_TRANS
            >> Q.EXISTS_TAC `(1-(e/x))*x`
            >> CONJ_TAC
            >- (RW_TAC real_ss [REAL_SUB_RDISTRIB] >> METIS_TAC [REAL_DIV_RMUL, REAL_LE_REFL])
            >> Q.PAT_X_ASSUM `!z. P z` MATCH_MP_TAC
            >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_DIV, REAL_LT_SUB_LADD, REAL_LT_1, REAL_LT_IMP_LE])
        >> FULL_SIMP_TAC std_ss [REAL_NOT_LT]
        >> MATCH_MP_TAC REAL_LE_TRANS
        >> Q.EXISTS_TAC `0`
        >> RW_TAC real_ss [REAL_LE_SUB_RADD]
        >> MATCH_MP_TAC REAL_LE_TRANS
        >> Q.EXISTS_TAC `(1/2)*x`
        >> RW_TAC real_ss [REAL_LE_MUL, REAL_LT_IMP_LE])
    >> MATCH_MP_TAC REAL_LE_TRANS
    >> Q.EXISTS_TAC `(1/2)*x`
    >> RW_TAC real_ss []
    >> RW_TAC std_ss [Once (GSYM REAL_LE_NEG), GSYM REAL_MUL_RNEG]
    >> Suff `1/2 * ~x <= 1 * ~x` >- RW_TAC real_ss []
    >> METIS_TAC [REAL_NEG_GT0, REAL_LT_TOTAL, REAL_LE_REFL, REAL_HALF_BETWEEN, REAL_LE_RMUL]);

(* ------------------------------------------------------------------------- *)
(* ----- Defining real-valued power, log, and log base 2 functions --------- *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "powr" (Infixr 700);

val powr_def = Define
        `x powr a = exp (a * ln x)`;

val logr_def = Define
        `logr a x = ln x / ln a`;

val lg_def = Define
        `lg x = logr 2 x`;


val lg_1 = store_thm
  ("lg_1",
   ``lg 1 = 0``,
   RW_TAC real_ss [lg_def, logr_def, LN_1]);


val logr_1 = store_thm
  ("logr_1",
   ``!b. logr b 1 = 0``,
   RW_TAC real_ss [logr_def, LN_1]);


val lg_nonzero = store_thm
  ("lg_nonzero",
   ``!x. (~(x = 0)) /\ (0 <= x) ==>
                ((~(lg x = 0)) = (~(x = 1)))``,
   RW_TAC std_ss [REAL_ARITH ``(~(x = 0)) /\ (0 <= x) = 0 < x``]
   >> RW_TAC std_ss [GSYM lg_1]
   >> RW_TAC std_ss [lg_def, logr_def, real_div, REAL_EQ_RMUL, REAL_INV_EQ_0]
   >> (MP_TAC o Q.SPECL [`2`, `1`]) LN_INJ >> RW_TAC real_ss [LN_1]
   >> RW_TAC std_ss [GSYM LN_1]
   >> MATCH_MP_TAC LN_INJ
   >> RW_TAC real_ss []);

val lg_mul = store_thm
  ("lg_mul",
   ``!x y. 0 < x /\ 0 < y ==> (lg (x * y) = lg x + lg y)``,
   RW_TAC real_ss [lg_def, logr_def, LN_MUL]);

val logr_mul = store_thm
  ("logr_mul",
   ``!b x y. 0 < x /\ 0 < y ==> (logr b (x * y) = logr b x + logr b y)``,
   RW_TAC real_ss [logr_def, LN_MUL]);

val lg_2 = store_thm
  ("lg_2",
   ``lg 2 = 1``,
   RW_TAC real_ss [lg_def, logr_def]
   >> MATCH_MP_TAC REAL_DIV_REFL
   >> (ASSUME_TAC o Q.SPECL [`1`, `2`]) LN_MONO_LT
   >> FULL_SIMP_TAC real_ss [LN_1]
   >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
   >> MATCH_MP_TAC REAL_LT_IMP_NE
   >> ASM_REWRITE_TAC []);

val lg_inv = store_thm
  ("lg_inv",
   ``!x. 0 < x ==> (lg (inv x) = ~ lg x)``,
   RW_TAC real_ss [lg_def, logr_def, LN_INV, real_div]);


val logr_inv = store_thm
  ("logr_inv",
   ``!b x. 0 < x ==> (logr b (inv x) = ~ logr b x)``,
   RW_TAC real_ss [logr_def, LN_INV, real_div]);


val logr_div = store_thm
  ("logr_div",
   ``!b x y. 0 < x /\ 0 < y ==>
        (logr b (x/y) = logr b x - logr b y)``,
   RW_TAC real_ss [real_div, logr_mul, logr_inv, GSYM real_sub]);


val neg_lg = store_thm
  ("neg_lg",
  ``!x. 0 < x ==> ((~(lg x)) = lg (inv x))``,
   RW_TAC real_ss [lg_def, logr_def, real_div]
   >> `~(ln x * inv (ln 2)) = (~ ln x) * inv (ln 2)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC real_ss [REAL_EQ_RMUL]
   >> DISJ2_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC LN_INV
   >> RW_TAC std_ss []);

val neg_logr = store_thm
  ("neg_logr",
  ``!b x. 0 < x ==> ((~(logr b x)) = logr b (inv x))``,
   RW_TAC real_ss [logr_def, real_div]
   >> `~(ln x * inv (ln b)) = (~ ln x) * inv (ln b)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC real_ss [REAL_EQ_RMUL]
   >> DISJ2_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC LN_INV
   >> RW_TAC std_ss []);


val lg_pow = store_thm
  ("lg_pow",
   ``!n. lg (2 pow n) = &n``,
   RW_TAC real_ss [lg_def, logr_def, LN_POW]
   >> `~(ln 2 = 0)`
        by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC REAL_LT_IMP_NE
            >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `ln 1` >> RW_TAC real_ss [LN_POS, LN_MONO_LT])
   >> RW_TAC real_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_RINV]);


(* ------------------------------------------------------------------------- *)
(* --------------------- exp is a convex function -------------------------- *)
(* ------------------------------------------------------------------------- *)

val convex_fn = Define
        `convex_fn = {f | !x y t. (0 <= t /\ t <= 1) ==> f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y}`;

val concave_fn = Define
        `concave_fn = {f | (\x. ~ (f x)) IN convex_fn}`;

val exp_convex_lemma1 = store_thm
  ("exp_convex_lemma1",
   ``!t. (t + (1 - t) * exp 0 - exp ((1 - t) * 0) = 0) /\
         (t * exp 0 + (1 - t) - exp (t * 0) = 0)``,
   RW_TAC real_ss [EXP_0] >> REAL_ARITH_TAC);

val exp_convex_lemma2 = store_thm
  ("exp_convex_lemma2",
   ``!t x. ((\x. (1 - t) * exp x - exp ((1 - t) * x)) diffl (\x. (1-t) * exp x - (1 - t)*exp ((1-t)*x)) x) x``,
   RW_TAC std_ss []
   >> `(\x. (1 - t) * exp x - exp ((1 - t) * x)) =
       (\x. (\x. (1 - t) * exp x) x - (\x. exp ((1 - t) * x)) x)`
        by RW_TAC std_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `((1 - t) * exp x - (1 - t) * exp ((1 - t) * x)) =
       (\x. (1 - t) * exp x) x - (\x. (1-t) * exp ((1- t) * x)) x`
        by RW_TAC std_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Suff `((\x. (1 - t) * exp x) diffl (\x. (1 - t) * exp x) x) x /\
                ((\x. exp ((1 - t) * x)) diffl (\x. (1 - t) * exp ((1 - t) * x)) x) x`
   >- METIS_TAC [DIFF_SUB]
   >> CONJ_TAC
   >- (`(\x. (1 - t) * exp x) x = 0 * exp x + (exp x) * (\x. 1 - t) x` by RW_TAC real_ss [REAL_MUL_COMM]
       >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> Q.ABBREV_TAC `foo = (0 * exp x + exp x * (\x. 1 - t) x)`
       >> `(\x. (1 - t) * exp x) = (\x. (\x. 1 - t) x * exp x)` by RW_TAC std_ss [FUN_EQ_THM]
       >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> Q.UNABBREV_TAC `foo`
       >> MATCH_MP_TAC DIFF_MUL
       >> RW_TAC std_ss [DIFF_CONST, DIFF_EXP])
   >> `(\x. exp ((1 - t) * x)) = (\x. exp ((\x. (1-t)*x) x))` by RW_TAC std_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `(\x. (1 - t) * exp ((1 - t) * x)) x = exp ((\x. (1-t)*x) x) * (1-t)`
        by RW_TAC real_ss [REAL_MUL_COMM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Suff `((\x. (1 - t) * x) diffl (1-t)) x` >- METIS_TAC [DIFF_COMPOSITE]
   >> `(1 - t) = (1 - t) * 1` by RW_TAC real_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `(\x. (1 - t) * 1 * x) = (\x. (1-t) * (\x. x) x)` by RW_TAC real_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC DIFF_CMUL
   >> RW_TAC std_ss [DIFF_X]);

val exp_convex_lemma3 = store_thm
  ("exp_convex_lemma3",
   ``!t x. (\x. (1-t) * exp x - exp ((1-t)*x)) contl x``,
   METIS_TAC [DIFF_CONT, exp_convex_lemma2]);

val exp_convex_lemma4 = store_thm
  ("exp_convex_lemma4",
   ``!x. 0 < x /\ 0 < t /\ t < 1 ==> 0 < (\x. (1-t) * exp x - (1 - t)*exp ((1-t)*x)) x``,
   RW_TAC real_ss [REAL_LT_SUB_LADD] >> MATCH_MP_TAC REAL_LT_LMUL_IMP
   >> RW_TAC real_ss [REAL_LT_SUB_LADD, EXP_MONO_LT, REAL_SUB_RDISTRIB]
   >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR] >> MATCH_MP_TAC REAL_LT_MUL
   >> RW_TAC real_ss []);

val exp_convex_lemma5 = store_thm
  ("exp_convex_lemma5",
   ``!f f' i j. (!x. (f diffl f' x) x) /\
                (!x. f contl x) /\
                (0 <= i /\ i < j) /\
                (!x. i < x /\ x < j ==> 0 < f' x) ==>
                        f i < f j``,
   REPEAT STRIP_TAC
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `0 + f i` >> CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC real_ss [GSYM REAL_LT_SUB_LADD]
   >> `?l z. i < z /\ z < j /\ (f diffl l) z /\ (f j - f i = (j - i) * l)`
        by (MATCH_MP_TAC MVT >> METIS_TAC [differentiable])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC REAL_LT_MUL
   >> RW_TAC real_ss [REAL_LT_SUB_LADD]
   >> `l = f' z`
        by (MATCH_MP_TAC DIFF_UNIQ >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `z` >> RW_TAC std_ss [])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Q.PAT_X_ASSUM `!x. i < x /\ x < j ==> 0 < f' x` MATCH_MP_TAC >> RW_TAC std_ss []);

val exp_convex_lemma6 = store_thm
  ("exp_convex_lemma6",
   ``!x y t. 0 < t /\ t < 1 /\ x < y ==>
                exp (t * x + (1 - t) * y) <= t * exp x + (1 - t) * exp y``,
   REPEAT STRIP_TAC
   >> Q.ABBREV_TAC `z = y - x`
   >> `0 < z` by (Q.UNABBREV_TAC `z` >> RW_TAC real_ss [REAL_LT_SUB_LADD])
   >> Suff `exp (t * x + (1 - t) * (x+z)) <= t * exp x + (1 - t) * exp (x+z)`
   >- (Q.UNABBREV_TAC `z` >> RW_TAC real_ss [])
   >> `t * x + (1 - t) * (x + z) = x + (1 - t) * z` by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> PURE_REWRITE_TAC [transcTheory.EXP_ADD]
   >> `t * exp x + (1 - t) * (exp x * exp z) = exp x * (t + (1 - t) * exp z)`
                by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> MATCH_MP_TAC REAL_LE_LMUL_IMP >> CONJ_TAC >- SIMP_TAC std_ss [EXP_POS_LE]
   >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `0 + exp ((1 - t) * z)` >> CONJ_TAC >- RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_SUB_LADD]
   >> MATCH_MP_TAC REAL_LT_IMP_LE
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `t + (1 - t) * exp 0 - exp ((1 - t) * 0)`
   >> CONJ_TAC >- RW_TAC real_ss [exp_convex_lemma1]
   >> `t + (1 - t) * exp 0 - exp ((1 - t) * 0) = ((1 - t) * exp 0 - exp ((1 - t) * 0)) + t`
                by REAL_ARITH_TAC >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> ONCE_REWRITE_TAC [REAL_LT_ADD_SUB]
   >> `t + (1 - t) * exp z - exp ((1 - t) * z) - t = (1 - t) * exp z - exp ((1 - t) * z)`
                by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> Q.ABBREV_TAC `f = (\x. (1-t) * exp x - exp ((1-t)*x))`
   >> Suff `f 0 < f z` >- (Q.UNABBREV_TAC `f` >> RW_TAC std_ss [])
   >> MATCH_MP_TAC exp_convex_lemma5
   >> Q.EXISTS_TAC `(\x. (1-t) * exp x - (1 - t)*exp ((1-t)*x))`
   >> Q.UNABBREV_TAC `f`
   >> RW_TAC real_ss [exp_convex_lemma2, exp_convex_lemma3, exp_convex_lemma4]);

val exp_convex = store_thm
  ("exp_convex",
   ``exp IN convex_fn``,
   RW_TAC std_ss [convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]
   >> Cases_on `t = 0` >- RW_TAC real_ss []
   >> Cases_on `t = 1` >- RW_TAC real_ss []
   >> `0 < t /\ t < 1` by METIS_TAC [REAL_LT_LE]
   >> Cases_on `x = y` >- RW_TAC real_ss []
   >> (MP_TAC o Q.SPECL [`x`, `y`]) REAL_LT_TOTAL >> RW_TAC std_ss []
   >- (MATCH_MP_TAC exp_convex_lemma6 >> RW_TAC std_ss [])
   >> Q.ABBREV_TAC `t' = 1 - t`
   >> `t = 1 - t'` by (Q.UNABBREV_TAC `t'` >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `0 < t'` by (Q.UNABBREV_TAC `t'` >> RW_TAC real_ss [REAL_LT_SUB_LADD])
   >> `t' < 1` by (Q.UNABBREV_TAC `t'` >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR])
   >> ONCE_REWRITE_TAC [REAL_ADD_COMM]
   >> MATCH_MP_TAC exp_convex_lemma6 >> RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* ------------ ln and lg are concave on (0,infty] ------------------------- *)
(* ------------------------------------------------------------------------- *)

val pos_convex_fn = Define
        `pos_convex_fn = {f | !x y t. (0 < x /\ 0 < y /\ 0 <= t /\ t <= 1) ==>
                                f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y}`;

val pos_concave_fn = Define
        `pos_concave_fn = {f | (\x. ~ (f x)) IN pos_convex_fn}`;

val pos_concave_ln = store_thm
  ("pos_concave_ln",
   ``ln IN pos_concave_fn``,
   RW_TAC std_ss [pos_concave_fn, pos_convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]
   >> Cases_on `t = 0` >- RW_TAC real_ss []
   >> Cases_on `t = 1` >- RW_TAC real_ss []
   >> `0 < t /\ t < 1` by RW_TAC std_ss [REAL_LT_LE]
   >> `t * ~ln x + (1 - t) * ~ln y = ~ (t * ln x + (1 - t)* ln y)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC std_ss [REAL_LE_NEG, ln]
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> RW_TAC std_ss [] >- (MATCH_MP_TAC EXP_TOTAL
                           >> MATCH_MP_TAC REAL_LT_ADD >> CONJ_TAC >> MATCH_MP_TAC REAL_LT_MUL
                           >> RW_TAC real_ss [GSYM REAL_LT_ADD_SUB])
   >> Suff `(\v. t * v + (1 - t) * (@u. exp u = y) <= x') (@u. exp u = x)`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> RW_TAC std_ss [] >- (MATCH_MP_TAC EXP_TOTAL >> RW_TAC std_ss [])
   >> Suff `(\v. t * x'' + (1 - t) * v <= x') (@u. exp u = y)`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> RW_TAC std_ss [] >- (MATCH_MP_TAC EXP_TOTAL >> RW_TAC std_ss [])
   >> ONCE_REWRITE_TAC [GSYM EXP_MONO_LE]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MP_TAC exp_convex >> RW_TAC std_ss [convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]);

val pos_concave_lg = store_thm
  ("pos_concave_lg",
   ``lg IN pos_concave_fn``,
   RW_TAC std_ss [lg_def, logr_def, pos_concave_fn, pos_convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]
   >> `~(ln (t * x + (1 - t) * y) / ln 2) =
       (inv (ln 2))*(~(ln (t * x + (1 - t) * y)))` by (RW_TAC real_ss [real_div] >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `t * ~(ln x / ln 2) + (1 - t) * ~(ln y / ln 2) =
       (inv (ln 2)) * (t * ~ ln x + (1-t) * ~ln y)`  by (RW_TAC real_ss [real_div] >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC REAL_LE_LMUL_IMP
   >> CONJ_TAC >- (RW_TAC real_ss [REAL_LE_INV_EQ] >> MATCH_MP_TAC LN_POS >> RW_TAC real_ss [])
   >> MP_TAC pos_concave_ln
   >> RW_TAC std_ss [pos_concave_fn, pos_convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]);


val pos_concave_logr = store_thm
  ("pos_concave_logr",
   ``!b. 1 <= b ==> (logr b) IN pos_concave_fn``,
   RW_TAC std_ss [logr_def, pos_concave_fn, pos_convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]
   >> `~(ln (t * x + (1 - t) * y) / ln b) =
       (inv (ln b))*(~(ln (t * x + (1 - t) * y)))` by (RW_TAC real_ss [real_div] >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `t * ~(ln x / ln b) + (1 - t) * ~(ln y / ln b) =
       (inv (ln b)) * (t * ~ ln x + (1-t) * ~ln y)`  by (RW_TAC real_ss [real_div] >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC REAL_LE_LMUL_IMP
   >> CONJ_TAC >- (RW_TAC real_ss [REAL_LE_INV_EQ] >> MATCH_MP_TAC LN_POS >> RW_TAC real_ss [])
   >> MP_TAC pos_concave_ln
   >> RW_TAC std_ss [pos_concave_fn, pos_convex_fn, EXTENSION, MEM, NOT_IN_EMPTY, GSPECIFICATION]);

(* ------------------------------------------------------------------------- *)
(* ---- jensen's inequality                                     ------------ *)
(* ------------------------------------------------------------------------- *)

val jensen_convex_SIGMA = store_thm
  ("jensen_convex_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  f IN convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s``,
   Suff `!s. FINITE s ==>
             (\s. !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  f IN convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s) s`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
   >> Cases_on `g e = 0` >- FULL_SIMP_TAC real_ss []
   >> Cases_on `g e = 1`
   >- ( FULL_SIMP_TAC real_ss []
        >> Know `!s. FINITE s ==>
                (\s. !g. (SIGMA g s = 0) /\ (!x. x IN s ==> 0 <= g x /\ g x <= 1) ==>
                            (!x. x IN s ==> (g x = 0))) s`
        >- (MATCH_MP_TAC FINITE_INDUCT
            >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM,
                               FORALL_AND_THM, NOT_IN_EMPTY] (* 2 sub-goals *)
            >- (Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
                >- REAL_ARITH_TAC
                >> PROVE_TAC [REAL_SUM_IMAGE_POS])
            >>
            ( Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
              >- REAL_ARITH_TAC
              >> Q.PAT_X_ASSUM `!g. (SIGMA g s' = 0) /\ (!x. x IN s' ==> 0 <= g x /\ g x <= 1) ==>
                                !x. x IN s' ==> (g x = 0)`
                (MP_TAC o Q.SPEC `g'`)
              >> PROVE_TAC [REAL_SUM_IMAGE_POS] ))
        >> Know `!x:real. (1 + x = 1) = (x = 0)` >- REAL_ARITH_TAC
        >> STRIP_TAC >> FULL_SIMP_TAC real_ss []
        >> POP_ASSUM (K ALL_TAC)
        >> (ASSUME_TAC o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF
        >> POP_ORW
        >> DISCH_TAC
        >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o (REWRITE_RULE [GSYM AND_IMP_INTRO]) o
                      (Q.SPEC `g`) o UNDISCH o (Q.SPEC `s`))
        >> `(\x. (if x IN s then (\x. g x * g' x) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> `(\x. (if x IN s then (\x. g x * f (g' x)) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> Suff `SIGMA (\x. 0) s = 0` >- RW_TAC real_ss []
        >> (MP_TAC o Q.SPECL [`(\x. 0)`, `0`] o
                UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
        >> RW_TAC real_ss [])

   >> Suff `(SIGMA (\x. g x * g' x) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * g' x) s) /\
            (SIGMA (\x. g x * f(g' x)) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * f(g' x)) s)`
   >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [convex_fn, GSPECIFICATION]
       >> Q.PAT_X_ASSUM `!f' g'' g'''.
        (SIGMA g'' s = 1) /\
        (!x. x IN s ==> 0 <= g'' x /\ g'' x <= 1) /\
        (!x y t.
           0 <= t /\ t <= 1 ==>
           f' (t * x + (1 - t) * y) <= t * f' x + (1 - t) * f' y) ==>
        f' (SIGMA (\x. g'' x * g''' x) s) <=
        SIGMA (\x. g'' x * f' (g''' x)) s` (MP_TAC o Q.SPECL [`f`, `(\x. g x / (1 - g e))`, `g'`])
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x y t. P`
                (MP_TAC o Q.SPECL [`g' e`, `SIGMA (\x. g x / (1 - g e) * g' x) s`, `g e`])
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `g e * f (g' e) + (1 - g e) * f (SIGMA (\x. g x / (1 - g e) * g' x) s)`
       >> RW_TAC real_ss [REAL_LE_LADD]
       >> Cases_on `g e = 1` >- RW_TAC real_ss []
       >> Know `0 < 1 - g e`
       >- (Q.PAT_X_ASSUM `g e <= 1` MP_TAC >> Q.PAT_X_ASSUM `~ (g e = 1)` MP_TAC >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> Suff `f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
                SIGMA (\x. g x / (1 - g e) * f (g' x)) s`
       >- PROVE_TAC [REAL_LE_LMUL]
       >> Q.PAT_X_ASSUM `(SIGMA (\x. g x / (1 - g e)) s = 1) /\
                        (!x. x IN s ==> 0 <= g x / (1 - g e) /\ g x / (1 - g e) <= 1) ==>
                        f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
                        SIGMA (\x. g x / (1 - g e) * f (g' x)) s` MATCH_MP_TAC
       >> CONJ_TAC
       >- ((MP_TAC o Q.SPECL [`g`, `inv (1- g e)`] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL
           >> RW_TAC real_ss [real_div] >> ASM_REWRITE_TAC [Once REAL_MUL_COMM]
           >> RW_TAC std_ss [Once REAL_MUL_COMM, GSYM real_div]
           >> Suff `SIGMA g s = 1 * (1 - g e)`
           >- PROVE_TAC [REAL_EQ_LDIV_EQ]
           >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` MP_TAC
           >> REAL_ARITH_TAC)
       >> RW_TAC std_ss [] >- PROVE_TAC [REAL_LE_DIV, REAL_LT_IMP_LE]
       >> Suff `g x <= 1 * (1 - g e)` >- PROVE_TAC [REAL_LE_LDIV_EQ]
       >> Suff `g e + g x <= 1` >- REAL_ARITH_TAC
       >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` (fn thm => ONCE_REWRITE_TAC [GSYM thm])
       >> MATCH_MP_TAC REAL_LE_ADD2
       >> PROVE_TAC [REAL_LE_REFL, REAL_SUM_IMAGE_POS_MEM_LE])
   >> Know `~(1-g e = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [(REWRITE_RULE [Once EQ_SYM_EQ] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL,
                     REAL_MUL_ASSOC, REAL_DIV_LMUL]);

val jensen_concave_SIGMA = store_thm
  ("jensen_concave_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  f IN concave_fn ==>
                         SIGMA (\x. g x * f (g' x)) s <= f (SIGMA (\x. g x * g' x) s)``,
   REPEAT STRIP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_NEG2]
   >> RW_TAC std_ss [(REWRITE_RULE [Once EQ_SYM_EQ]) REAL_SUM_IMAGE_NEG]
   >> Suff `(\x. ~ f x) (SIGMA (\x. g x * g' x) s) <=
            SIGMA (\x. g x * (\x. ~ f x) (g' x)) s`
   >- RW_TAC real_ss []
   >> Q.ABBREV_TAC `f' = (\x. ~f x)`
   >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) jensen_convex_SIGMA
   >> Q.UNABBREV_TAC `f'`
   >> FULL_SIMP_TAC std_ss [concave_fn, GSPECIFICATION]);

val jensen_pos_convex_SIGMA = store_thm
  ("jensen_pos_convex_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  (!x. x IN s ==> (0 < g x ==> 0 < g' x)) /\
                  f IN pos_convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s``,
   Suff `!s. FINITE s ==>
             (\s. !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  (!x. x IN s ==> (0 < g x ==> 0 < g' x)) /\
                  f IN pos_convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s) s`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
   >> Cases_on `g e = 0` >- FULL_SIMP_TAC real_ss []
   >> Cases_on `g e = 1`
   >- ( FULL_SIMP_TAC real_ss []
        >> Know `!s. FINITE s ==>
                (\s. !g. (SIGMA g s = 0) /\ (!x. x IN s ==> 0 <= g x /\ g x <= 1) ==>
                            (!x. x IN s ==> (g x = 0))) s`
        >- (MATCH_MP_TAC FINITE_INDUCT
            >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM,
                               FORALL_AND_THM, NOT_IN_EMPTY] (* 2 sub-goals *)
            >- (Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
                >- REAL_ARITH_TAC
                >> PROVE_TAC [REAL_SUM_IMAGE_POS])
            >>
            ( Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
              >- REAL_ARITH_TAC
              >> Q.PAT_X_ASSUM `!g. (SIGMA g s' = 0) /\ (!x. x IN s' ==> 0 <= g x /\ g x <= 1) ==>
                                !x. x IN s' ==> (g x = 0)`
                (MP_TAC o Q.SPEC `g''`)
              >> PROVE_TAC [REAL_SUM_IMAGE_POS] ))
        >> Know `!x:real. (1 + x = 1) = (x = 0)` >- REAL_ARITH_TAC
        >> STRIP_TAC >> FULL_SIMP_TAC real_ss []
        >> POP_ASSUM (K ALL_TAC)
        >> (ASSUME_TAC o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF
        >> POP_ORW
        >> DISCH_TAC
        >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                      (Q.SPEC `g`) o UNDISCH o (Q.SPEC `s`))
        >> `(\x. (if x IN s then (\x. g x * g' x) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> `(\x. (if x IN s then (\x. g x * f (g' x)) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> Suff `SIGMA (\x. 0) s = 0` >- RW_TAC real_ss []
        >> (MP_TAC o Q.SPECL [`(\x. 0)`, `0`] o
                UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
        >> RW_TAC real_ss [])
   >> Suff `(SIGMA (\x. g x * g' x) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * g' x) s) /\
            (SIGMA (\x. g x * f(g' x)) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * f(g' x)) s)`
   >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [pos_convex_fn, GSPECIFICATION]
       >> Q.PAT_X_ASSUM `!f' g'' g'''.
        (SIGMA g'' s = 1) /\
        (!x. x IN s ==> 0 <= g'' x /\ g'' x <= 1) /\
        (!x. x IN s ==> 0 < g'' x ==> 0 < g''' x) /\
        (!x y t.
           0 < x /\ 0 < y /\ 0 <= t /\ t <= 1 ==>
           f' (t * x + (1 - t) * y) <= t * f' x + (1 - t) * f' y) ==>
        f' (SIGMA (\x. g'' x * g''' x) s) <=
        SIGMA (\x. g'' x * f' (g''' x)) s` (MP_TAC o Q.SPECL [`f`, `(\x. g x / (1 - g e))`, `g'`])
       >> RW_TAC std_ss []
       >> Know `0 < 1 - g e`
       >- (Q.PAT_X_ASSUM `g e <= 1` MP_TAC >> Q.PAT_X_ASSUM `~ (g e = 1)` MP_TAC >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> Know `SIGMA (\x. g x / (1 - g e)) s = 1`
       >- ((MP_TAC o Q.SPECL [`g`, `inv (1- g e)`] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL
           >> RW_TAC real_ss [real_div] >> ASM_REWRITE_TAC [Once REAL_MUL_COMM]
           >> RW_TAC std_ss [Once REAL_MUL_COMM, GSYM real_div]
           >> Suff `SIGMA g s = 1 * (1 - g e)`
           >- PROVE_TAC [REAL_EQ_LDIV_EQ]
           >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` MP_TAC
           >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> FULL_SIMP_TAC std_ss []
       >> Cases_on `s = {}` >- FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_THM]
       >> Know `0 < SIGMA (\x. g x / (1 - g e) * g' x) s`
       >- ( RW_TAC std_ss [REAL_LT_LE]
            >- ((MATCH_MP_TAC o UNDISCH o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                        Q.SPECL [`(\x. g x / (1 - g e) * g' x)`,`s`]) REAL_SUM_IMAGE_POS
                >> RW_TAC real_ss [] >> Cases_on `g x = 0` >- RW_TAC real_ss []
                >> MATCH_MP_TAC REAL_LE_MUL
                >> Reverse CONJ_TAC >- PROVE_TAC [REAL_LT_IMP_LE, REAL_LT_LE]
                >> RW_TAC real_ss [] >> MATCH_MP_TAC REAL_LE_DIV
                >> RW_TAC real_ss [] >> PROVE_TAC [REAL_LT_IMP_LE])
            >> Q.PAT_X_ASSUM `SIGMA (\x. g x * g' x) s =
                                (1 - g e) * SIGMA (\x. g x / (1 - g e) * g' x) s`
                (MP_TAC o REWRITE_RULE [Once REAL_MUL_COMM] o GSYM)
            >> RW_TAC std_ss [GSYM REAL_EQ_RDIV_EQ]
            >> RW_TAC std_ss [real_div, REAL_ENTIRE, REAL_INV_EQ_0, REAL_LT_IMP_NE]
            >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
            >> Know `!s. FINITE s ==>
                    (\s. !g g'. (!x. x IN s ==> 0 <= g x) /\ (!x. x IN s ==> 0 < g x ==> 0 < g' x) /\
                                (SIGMA (\x. g x * g' x) s = 0) ==>
                                (!x. x IN s ==> (g x = 0))) s`
            >- ( REPEAT (POP_ASSUM (K ALL_TAC))
                 >> MATCH_MP_TAC FINITE_INDUCT
                 >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_IN_EMPTY, DELETE_NON_ELEMENT,
                                   IN_INSERT, Once DISJ_IMP_THM, Once FORALL_AND_THM]
                 >- ( SPOSE_NOT_THEN STRIP_ASSUME_TAC
                      >> Cases_on `SIGMA (\x. g x * g' x) s = 0`
                      >- ( FULL_SIMP_TAC real_ss [REAL_ENTIRE] \\
                           PROVE_TAC [REAL_LT_IMP_NE, REAL_LT_LE] )
                      >> `0 < g e * g' e + SIGMA (\x. g x * g' x) s`
                                by (MATCH_MP_TAC REAL_LT_ADD
                                    >> CONJ_TAC
                                    >- (MATCH_MP_TAC REAL_LT_MUL >> PROVE_TAC [REAL_LT_LE])
                                    >> RW_TAC std_ss [REAL_LT_LE]
                                    >> (MATCH_MP_TAC o UNDISCH o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                                        Q.SPECL [`(\x. g x * g' x)`,`s`]) REAL_SUM_IMAGE_POS
                                    >> RW_TAC std_ss []
                                    >> Cases_on `g x = 0` >- RW_TAC real_ss []
                                    >> PROVE_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LT_LE])
                      >> PROVE_TAC [REAL_LT_IMP_NE] )
                 >> Cases_on `SIGMA (\x. g x * g' x) s = 0`
                 >- METIS_TAC []
                 >> Cases_on `g e = 0`
                 >- FULL_SIMP_TAC real_ss []
                 >> `0 < g e * g' e + SIGMA (\x. g x * g' x) s`
                        by (MATCH_MP_TAC REAL_LT_ADD
                            >> CONJ_TAC
                            >- (MATCH_MP_TAC REAL_LT_MUL >> METIS_TAC [REAL_LT_LE])
                            >> RW_TAC std_ss [REAL_LT_LE]
                            >> (MATCH_MP_TAC o UNDISCH o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                                Q.SPECL [`(\x. g x * g' x)`,`s`]) REAL_SUM_IMAGE_POS
                            >> RW_TAC std_ss []
                            >> Cases_on `g x' = 0` >- RW_TAC real_ss []
                            >> PROVE_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LT_LE])
                 >> METIS_TAC [REAL_LT_IMP_NE] )
            >> DISCH_TAC
            >> POP_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC `s`)
            >> FULL_SIMP_TAC std_ss [IMP_CONJ_THM, Once FORALL_AND_THM]
            >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                          (Q.SPECL [`g`,`g'`]))
            >> (ASSUME_TAC o Q.SPECL [`(\x. if x IN s then g x else 0)`, `0`] o
                UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
            >> `SIGMA (\x. (if x IN s then g x else 0)) s = SIGMA g s`
                  by METIS_TAC [GSYM REAL_SUM_IMAGE_IN_IF]
            >> FULL_SIMP_TAC real_ss [] )
       >> DISCH_TAC
       >> Q.PAT_X_ASSUM `!x y t. P`
              (MP_TAC o Q.SPECL [`g' e`, `SIGMA (\x. g x / (1 - g e) * g' x) s`, `g e`])
       >> Know `0 < g' e` >- METIS_TAC [REAL_LT_LE]
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `g e * f (g' e) + (1 - g e) * f (SIGMA (\x. g x / (1 - g e) * g' x) s)`
       >> RW_TAC real_ss [REAL_LE_LADD]
       >> Suff `f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
                SIGMA (\x. g x / (1 - g e) * f (g' x)) s`
       >- PROVE_TAC [REAL_LE_LMUL]
       >> Q.PAT_X_ASSUM `(!x. x IN s ==> 0 <= g x / (1 - g e) /\ g x / (1 - g e) <= 1) /\
       (!x. x IN s ==> 0 < g x / (1 - g e) ==> 0 < g' x) ==>
       f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
       SIGMA (\x. g x / (1 - g e) * f (g' x)) s` MATCH_MP_TAC
       >> RW_TAC std_ss [] (* 3 sub-goals *)
       >| [PROVE_TAC [REAL_LE_DIV, REAL_LT_IMP_LE],
           Suff `g x <= 1 * (1 - g e)` >- PROVE_TAC [REAL_LE_LDIV_EQ]
           >> Suff `g e + g x <= 1` >- REAL_ARITH_TAC
           >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` (fn thm => ONCE_REWRITE_TAC [GSYM thm])
           >> MATCH_MP_TAC REAL_LE_ADD2
           >> PROVE_TAC [REAL_LE_REFL, REAL_SUM_IMAGE_POS_MEM_LE],
           Cases_on `g x = 0` >- FULL_SIMP_TAC real_ss []
           >> PROVE_TAC [REAL_LT_LE] ])
   >> Know `~(1-g e = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [(REWRITE_RULE [Once EQ_SYM_EQ] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL,
                     REAL_MUL_ASSOC, REAL_DIV_LMUL]);

val jensen_pos_concave_SIGMA = store_thm
  ("jensen_pos_concave_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  (!x. x IN s ==> (0 < g x ==> 0 < g' x)) /\
                  f IN pos_concave_fn ==>
                        SIGMA (\x. g x * f (g' x)) s <= f (SIGMA (\x. g x * g' x) s)``,
   REPEAT STRIP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_NEG2]
   >> RW_TAC std_ss [(REWRITE_RULE [Once EQ_SYM_EQ]) REAL_SUM_IMAGE_NEG]
   >> Suff `(\x. ~ f x) (SIGMA (\x. g x * g' x) s) <=
            SIGMA (\x. g x * (\x. ~ f x) (g' x)) s`
   >- RW_TAC real_ss []
   >> Q.ABBREV_TAC `f' = (\x. ~f x)`
   >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) jensen_pos_convex_SIGMA
   >> Q.UNABBREV_TAC `f'`
   >> FULL_SIMP_TAC std_ss [pos_concave_fn, GSPECIFICATION]);

val _ = export_theory ();
