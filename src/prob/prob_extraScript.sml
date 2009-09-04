open HolKernel Parse boolLib;

val _ = new_theory "prob_extra";

(* interactive mode
if !show_assums then () else (
  load "bossLib";
  load "realLib";
  load "arithmeticTheory";
  load "pred_setTheory";
  load "ind_typeTheory";
  load "rich_listTheory";
  load "pairTheory";
  load "probTools";
  show_assums := true
);
*)

open bossLib arithmeticTheory realTheory seqTheory pred_setTheory pairLib
     listTheory rich_listTheory pairTheory realLib probTools realSimps;

infixr 0 ++ << || ORELSEC ##;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

type term = Term.term
type sequent = term list * term
type tactic = Abbrev.tactic
type conv = Abbrev.conv

(* ------------------------------------------------------------------------- *)
(* Extra definitions/theorems from boolTheory.                               *)
(* ------------------------------------------------------------------------- *)

val EQ_EXT_EQ = save_thm("EQ_EXT_EQ", GSYM boolTheory.FUN_EQ_THM);

val RAND_THM = store_thm
  ("RAND_THM",
   ``!f x y. (x = y) ==> (f x = f y)``,
   RW_TAC std_ss []);

val BOOL_BOOL_CASES_THM = store_thm
  ("BOOL_BOOL_CASES_THM",
   ``!f. (f = (\b. F)) \/ (f = (\b. T)) \/ (f = (\b. b)) \/ (f = (\b. ~b))``,
   RW_TAC std_ss [GSYM EQ_EXT_EQ]
   ++ (Cases_on `f T` ++ Cases_on `f F`) <<
   [DISJ2_TAC
    ++ DISJ1_TAC
    ++ (Cases ++ RW_TAC std_ss []),
    DISJ2_TAC
    ++ DISJ2_TAC
    ++ DISJ1_TAC
    ++ (Cases ++ RW_TAC std_ss []),
    DISJ2_TAC
    ++ DISJ2_TAC
    ++ DISJ2_TAC
    ++ (Cases ++ RW_TAC std_ss []),
    DISJ1_TAC
    ++ (Cases ++ RW_TAC std_ss [])]);

val BOOL_BOOL_CASES = store_thm
  ("BOOL_BOOL_CASES",
   ``!P. P (\b. F) /\ P (\b. T) /\ P (\b. b) /\ P (\b. ~b) ==> (!f. P f)``,
   REPEAT STRIP_TAC
   ++ MP_TAC (SPEC ``f:bool->bool`` BOOL_BOOL_CASES_THM)
   ++ (STRIP_TAC ++ RW_TAC std_ss []));

(* ------------------------------------------------------------------------- *)
(* Extra definitions/theorems from arithmeticTheory.                         *)
(* ------------------------------------------------------------------------- *)

val EVEN_ODD_BASIC = store_thm
  ("EVEN_ODD_BASIC",
   ``EVEN 0 /\ ~EVEN 1 /\ EVEN 2 /\ ~ODD 0 /\ ODD 1 /\ ~ODD 2``,
   CONV_TAC (TOP_DEPTH_CONV Num_conv.num_CONV)
   ++ RW_TAC arith_ss [EVEN, ODD]);

val EVEN_ODD_EXISTS_EQ = store_thm
  ("EVEN_ODD_EXISTS_EQ",
   ``!n. (EVEN n = ?m. n = 2 * m) /\ (ODD n = ?m. n = SUC (2 * m))``,
   PROVE_TAC [EVEN_ODD_EXISTS, EVEN_DOUBLE, ODD_DOUBLE]);

val DIV_THEN_MULT = store_thm
  ("DIV_THEN_MULT",
   ``!p q. SUC q * (p DIV SUC q) <= p``,
   NTAC 2 STRIP_TAC
   ++ KNOW_TAC `?r. p = (p DIV SUC q) * SUC q + r`
   >> PROVE_TAC [DIVISION, DECIDE ``0 < SUC q``]
   ++ SUFF_TAC `p = SUC q * (p DIV SUC q) + r`
   >> (KILL_ALL_TAC ++ DECIDE_TAC)
   ++ PROVE_TAC [MULT_COMM]);

val DIV_TWO_UNIQUE = store_thm
  ("DIV_TWO_UNIQUE",
   ``!n q r. (n = 2 * q + r) /\ ((r = 0) \/ (r = 1))
             ==> (q = n DIV 2) /\ (r = n MOD 2)``,
   NTAC 3 STRIP_TAC
   ++ MP_TAC (Q.SPECL [`2`, `n`, `q`] DIV_UNIQUE)
   ++ MP_TAC (Q.SPECL [`2`, `n`, `r`] MOD_UNIQUE)
   ++ KNOW_TAC `((r = 0) \/ (r = 1)) = r < 2` >> DECIDE_TAC
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [MULT_COMM]);

val DIVISION_TWO = store_thm
  ("DIVISION_TWO",
   ``!n. (n = 2 * (n DIV 2) + (n MOD 2)) /\ ((n MOD 2 = 0) \/ (n MOD 2 = 1))``,
   STRIP_TAC
   ++ MP_TAC (Q.SPEC `2` DIVISION)
   ++ KNOW_TAC `0:num < 2` >> DECIDE_TAC
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ DISCH_THEN (MP_TAC o Q.SPEC `n`)
   ++ RW_TAC std_ss [] <<
   [PROVE_TAC [MULT_COMM],
    `n MOD 2 < 2` by RW_TAC arith_ss [] ++ DECIDE_TAC]);

val DIV_TWO = store_thm
  ("DIV_TWO",
   ``!n. n = 2 * (n DIV 2) + (n MOD 2)``,
   PROVE_TAC [DIVISION_TWO]);

val MOD_TWO = store_thm
  ("MOD_TWO",
   ``!n. n MOD 2 = if EVEN n then 0 else 1``,
   STRIP_TAC
   ++ MP_TAC (Q.SPEC `n` DIVISION_TWO)
   ++ STRIP_TAC <<
   [RW_TAC std_ss []
    ++ KNOW_TAC `n = 2 * (n DIV 2)` >> DECIDE_TAC
    ++ PROVE_TAC [EVEN_DOUBLE, ODD_EVEN],
    RW_TAC std_ss []
    ++ KNOW_TAC `n = SUC (2 * (n DIV 2))` >> DECIDE_TAC
    ++ PROVE_TAC [ODD_DOUBLE, ODD_EVEN]]);

val DIV_TWO_BASIC = store_thm
  ("DIV_TWO_BASIC",
   ``(0 DIV 2 = 0) /\ (1 DIV 2 = 0) /\ (2 DIV 2 = 1)``,
   KNOW_TAC `(0:num = 2 * 0 + 0) /\ (1:num = 2 * 0 + 1) /\ (2:num = 2 * 1 + 0)`
   >> RW_TAC arith_ss []
   ++ PROVE_TAC [DIV_TWO_UNIQUE]);

val DIV_TWO_MONO = store_thm
  ("DIV_TWO_MONO",
   ``!m n. m DIV 2 < n DIV 2 ==> m < n``,
   NTAC 2 STRIP_TAC
   ++ (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV) [DIV_TWO]
   ++ Q.SPEC_TAC (`m DIV 2`, `p`)
   ++ Q.SPEC_TAC (`n DIV 2`, `q`)
   ++ REPEAT STRIP_TAC
   ++ KNOW_TAC `(m MOD 2 = 0) \/ (m MOD 2 = 1)` >> PROVE_TAC [MOD_TWO]
   ++ KNOW_TAC `(n MOD 2 = 0) \/ (n MOD 2 = 1)` >> PROVE_TAC [MOD_TWO]
   ++ DECIDE_TAC);

val DIV_TWO_MONO_EVEN = store_thm
  ("DIV_TWO_MONO_EVEN",
   ``!m n. EVEN n ==> (m DIV 2 < n DIV 2 = m < n)``,
   RW_TAC std_ss []
   ++ EQ_TAC >> PROVE_TAC [DIV_TWO_MONO]
   ++ (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [DIV_TWO]
   ++ Q.SPEC_TAC (`m DIV 2`, `p`)
   ++ Q.SPEC_TAC (`n DIV 2`, `q`)
   ++ REPEAT STRIP_TAC
   ++ KNOW_TAC `n MOD 2 = 0` >> PROVE_TAC [MOD_TWO]
   ++ KNOW_TAC `(m MOD 2 = 0) \/ (m MOD 2 = 1)` >> PROVE_TAC [MOD_TWO]
   ++ DECIDE_TAC);

val DIV_TWO_CANCEL = store_thm
  ("DIV_TWO_CANCEL",
   ``!n. (2 * n DIV 2 = n) /\ (SUC (2 * n) DIV 2 = n)``,
   RW_TAC std_ss [] <<
   [MP_TAC (Q.SPEC `2 * n` DIV_TWO)
    ++ RW_TAC arith_ss [MOD_TWO, EVEN_DOUBLE],
    MP_TAC (Q.SPEC `SUC (2 * n)` DIV_TWO)
    ++ RW_TAC arith_ss [MOD_TWO, ODD_DOUBLE]]);

val EXP_DIV_TWO = store_thm
  ("EXP_DIV_TWO",
   ``!n. 2 EXP SUC n DIV 2 = 2 EXP n``,
   RW_TAC std_ss [EXP, DIV_TWO_CANCEL]);

val EVEN_EXP_TWO = store_thm
  ("EVEN_EXP_TWO",
   ``!n. EVEN (2 EXP n) = ~(n = 0)``,
   Cases >> RW_TAC arith_ss [EXP, EVEN_ODD_BASIC]
   ++ RW_TAC arith_ss [EXP, EVEN_DOUBLE]);

val DIV_TWO_EXP = store_thm
  ("DIV_TWO_EXP",
   ``!n k. k DIV 2 < 2 EXP n = k < 2 EXP SUC n``,
   RW_TAC std_ss []
   ++ (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [GSYM EXP_DIV_TWO]
   ++ MATCH_MP_TAC DIV_TWO_MONO_EVEN
   ++ RW_TAC std_ss [EVEN_EXP_TWO]);

(* ------------------------------------------------------------------------- *)
(* Extra definitions/theorems from realTheory.                               *)
(* ------------------------------------------------------------------------- *)

val inf_def = Define `inf P = ~(sup (IMAGE $~ P))`;

val INF_DEF_ALT = store_thm
  ("INF_DEF_ALT",
   ``!P. inf P = ~(sup (\r. P (~r)))``,
   STRIP_TAC
   ++ PURE_REWRITE_TAC [inf_def, IMAGE_DEF]
   ++ SUFF_TAC `{~x | x IN P} = (\r:real. P (~r))`
     >> RW_TAC std_ss []
   ++ SUFF_TAC `!v. v IN {~x | x IN P} = (\r:real. P (~r)) v`
     >> (REWRITE_TAC [SPECIFICATION]
	 ++ PROVE_TAC [EQ_EXT])
   ++ RW_TAC list_ss [GSPECIFICATION]
   ++ RW_TAC list_ss [SPECIFICATION]
   ++ PROVE_TAC [REAL_ARITH ``(x:real) = ~~x``]);

val REAL_LE_EQ = store_thm
  ("REAL_LE_EQ",
   ``!(x:real) y. x <= y /\ y <= x ==> (x = y)``,
   REAL_ARITH_TAC);

val REAL_SUP_EXISTS_UNIQUE = store_thm
  ("REAL_SUP_EXISTS_UNIQUE",
   ``!P. (?(x:real). P x) /\ (?z. !x. P x ==> x <= z)
         ==> (?!s. !y. (?x. P x /\ y < x) = y < s)``,
   REPEAT STRIP_TAC
   ++ CONV_TAC EXISTS_UNIQUE_CONV
   ++ RW_TAC std_ss [] <<
   [ASSUME_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
    ++ PROVE_TAC [],
    SUFF_TAC `~((s:real) < s') /\ ~(s' < s)`
      >> (KILL_ALL_TAC ++ REAL_ARITH_TAC)
    ++ REPEAT STRIP_TAC <<
    [SUFF_TAC `!(x:real). P x ==> ~(s < x)` >> PROVE_TAC []
     ++ REPEAT STRIP_TAC
     ++ SUFF_TAC `~((s:real) < s)` >> PROVE_TAC []
     ++ KILL_ALL_TAC
     ++ REAL_ARITH_TAC,
     SUFF_TAC `!(x:real). P x ==> ~(s' < x)` >> PROVE_TAC []
     ++ REPEAT STRIP_TAC
     ++ SUFF_TAC `~((s':real) < s')` >> PROVE_TAC []
     ++ KILL_ALL_TAC
     ++ REAL_ARITH_TAC]]);

val REAL_SUP_MAX = store_thm
  ("REAL_SUP_MAX",
   ``!P z. P z /\ (!x. P x ==> x <= z) ==> (sup P = z)``,
    REPEAT STRIP_TAC
    ++ KNOW_TAC `!(y:real). (?x. P x /\ y < x) = y < z`
      >> (STRIP_TAC
	  ++ EQ_TAC <<
	  [REPEAT STRIP_TAC
	   ++ PROVE_TAC [REAL_ARITH ``(y:real) < x /\ x <= z ==> y < z``],
	   PROVE_TAC []])

    ++ KNOW_TAC `!y. (?x. P x /\ y < x) = y < sup P`
      >> PROVE_TAC [REAL_SUP_LE]
    ++ KNOW_TAC `(?(x:real). P x) /\ (?z. !x. P x ==> x <= z)`
      >> PROVE_TAC []
    ++ ASSUME_TAC ((SPEC ``P:real->bool`` o CONV_RULE
		      (DEPTH_CONV EXISTS_UNIQUE_CONV)) REAL_SUP_EXISTS_UNIQUE)
    ++ RES_TAC);

val REAL_INF_MIN = store_thm
  ("REAL_INF_MIN",
   ``!P z. P z /\ (!x. P x ==> z <= x) ==> (inf P = z)``,
   REPEAT STRIP_TAC
   ++ MP_TAC (SPECL [``(\r. (P:real->bool) (~r))``, ``~(z:real)``]
		REAL_SUP_MAX)
   ++ RW_TAC std_ss [REAL_ARITH ``~~(x:real) = x``, INF_DEF_ALT]
   ++ SUFF_TAC `!x. P ~x ==> x <= ~z`
     >> PROVE_TAC [REAL_ARITH ``~~(x:real) = x``]
   ++ REPEAT STRIP_TAC
   ++ SUFF_TAC `z <= ~x` >> (KILL_ALL_TAC ++ REAL_ARITH_TAC)
   ++ PROVE_TAC []);

val HALF_POS = store_thm
  ("HALF_POS",
   ``0 < 1/2``,
   PROVE_TAC [REAL_ARITH ``0:real < 1``, REAL_LT_HALF1]);

val HALF_CANCEL = store_thm
  ("HALF_CANCEL",
   ``2 * (1 / 2) = 1``,
   SUFF_TAC `2 * inv 2 = 1` >> PROVE_TAC [REAL_INV_1OVER]
   ++ PROVE_TAC [REAL_MUL_RINV, REAL_ARITH ``~(2:real = 0)``]);

val POW_HALF_POS = store_thm
  ("POW_HALF_POS",
   ``!n. 0 < (1/2) pow n``,
   STRIP_TAC
   ++ Cases_on `n` >> PROVE_TAC [REAL_ARITH ``0:real < 1``, pow]
   ++ PROVE_TAC [HALF_POS, POW_POS_LT]);

val POW_HALF_MONO = store_thm
  ("POW_HALF_MONO",
   ``!m n. m <= n ==> (1/2) pow n <= (1/2) pow m``,
   REPEAT STRIP_TAC
   ++ Induct_on `n` <<
   [STRIP_TAC
    ++ KNOW_TAC `m:num = 0` >> DECIDE_TAC
    ++ PROVE_TAC [REAL_ARITH ``a:real <= a``],
    Cases_on `m = SUC n` >> PROVE_TAC [REAL_ARITH ``a:real <= a``]
    ++ ONCE_REWRITE_TAC [pow]
    ++ STRIP_TAC
    ++ KNOW_TAC `m:num <= n` >> DECIDE_TAC
    ++ SUFF_TAC `2 * ((1/2) * (1/2) pow n) <= 2 * (1/2) pow m`
      >> PROVE_TAC [REAL_ARITH ``0:real < 2``, REAL_LE_LMUL]
    ++ SUFF_TAC `(1/2) pow n <= 2 * (1/2) pow m`
      >> (KILL_ALL_TAC
	  ++ PROVE_TAC [GSYM REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID])
    ++ PROVE_TAC [REAL_ARITH ``!x y. 0:real < x /\ x <= y ==> x <= 2 * y``,
		    POW_HALF_POS]]);

val POW_HALF_TWICE = store_thm
  ("POW_HALF_TWICE",
   ``!n. (1 / 2) pow n = 2 * (1 / 2) pow (SUC n)``,
   RW_TAC std_ss [pow, REAL_MUL_ASSOC]
   ++ PROVE_TAC [HALF_CANCEL, REAL_MUL_LID]);

val X_HALF_HALF = store_thm
  ("X_HALF_HALF",
   ``!x. 1/2 * x + 1/2 * x = x``,
   STRIP_TAC
   ++ MATCH_MP_TAC (REAL_ARITH ``(2 * (a:real) = 2 * b) ==> (a = b)``)
   ++ RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
   ++ REAL_ARITH_TAC);

val REAL_SUP_LE_X = store_thm
  ("REAL_SUP_LE_X",
   ``!P x. (?r. P r) /\ (!r. P r ==> r <= x) ==> sup P <= x``,
   RW_TAC real_ac_ss []
   ++ SUFF_TAC `~(x < sup P)` >> REAL_ARITH_TAC
   ++ STRIP_TAC
   ++ MP_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
   ++ RW_TAC real_ac_ss [] <<
   [PROVE_TAC [],
    PROVE_TAC [],
    EXISTS_TAC ``x:real``
    ++ RW_TAC real_ac_ss []
    ++ PROVE_TAC [real_lte]]);

val REAL_X_LE_SUP = store_thm
  ("REAL_X_LE_SUP",
   ``!P x. (?r. P r) /\ (?z. !r. P r ==> r <= z) /\ (?r. P r /\ x <= r)
           ==> x <= sup P``,
   RW_TAC real_ac_ss []
   ++ SUFF_TAC `!y. P y ==> y <= sup P` >> PROVE_TAC [REAL_LE_TRANS]
   ++ MATCH_MP_TAC REAL_SUP_UBOUND_LE
   ++ PROVE_TAC []);

val REAL_INVINV_ALL = store_thm
  ("REAL_INVINV_ALL",
   ``!x. inv (inv x) = x``,
   STRIP_TAC
   ++ REVERSE (Cases_on `x = 0`) >> RW_TAC std_ss [REAL_INVINV]
   ++ RW_TAC std_ss [REAL_INV_0]);

val ABS_BETWEEN_LE = store_thm
  ("ABS_BETWEEN_LE",
   ``!x y d. 0 <= d /\ x - d <= y /\ y <= x + d = abs (y - x) <= d``,
   RW_TAC std_ss [abs] <<
   [EQ_TAC >> REAL_ARITH_TAC
    ++ STRIP_TAC
    ++ KNOW_TAC `0 <= d` >> PROVE_TAC [REAL_LE_TRANS]
    ++ RW_TAC std_ss [] <<
    [SUFF_TAC `x <= y`
     >> (POP_ASSUM MP_TAC ++ KILL_ALL_TAC ++ REAL_ARITH_TAC)
     ++ Q.PAT_ASSUM `0 <= y - x` MP_TAC
     ++ KILL_ALL_TAC
     ++ REAL_ARITH_TAC,
     Q.PAT_ASSUM `y - x <= d` MP_TAC
     ++ KILL_ALL_TAC
     ++ REAL_ARITH_TAC],
    EQ_TAC >> REAL_ARITH_TAC
    ++ KNOW_TAC `y - x <= 0` >> PROVE_TAC [REAL_NOT_LE, REAL_LT_LE]
    ++ KNOW_TAC `~0 <= ~(y - x)` >> PROVE_TAC [REAL_LE_NEG]
    ++ POP_ASSUM MP_TAC
    ++ KILL_ALL_TAC
    ++ REWRITE_TAC [REAL_NEG_SUB, REAL_NEG_0]
    ++ NTAC 2 STRIP_TAC
    ++ KNOW_TAC `0 <= d` >> PROVE_TAC [REAL_LE_TRANS]
    ++ RW_TAC std_ss [] <<
    [Q.PAT_ASSUM `x - y <= d` MP_TAC
     ++ KILL_ALL_TAC
     ++ REAL_ARITH_TAC,
     SUFF_TAC `y <= x`
     >> (POP_ASSUM MP_TAC ++ KILL_ALL_TAC ++ REAL_ARITH_TAC)
     ++ Q.PAT_ASSUM `0 <= x - y` MP_TAC
     ++ KILL_ALL_TAC
     ++ REAL_ARITH_TAC]]);

val ONE_MINUS_HALF = store_thm
  ("ONE_MINUS_HALF",
   ``1 - 1 / 2 = 1 / 2``,
   MP_TAC (Q.SPEC `1` X_HALF_HALF)
   ++ RW_TAC real_ac_ss []
   ++ MATCH_MP_TAC (REAL_ARITH ``(x + 1 / 2 = y + 1 / 2) ==> (x = y)``)
   ++ RW_TAC std_ss [REAL_SUB_ADD]);

val HALF_LT_1 = store_thm
  ("HALF_LT_1",
   ``1 / 2 < 1``,
   ONCE_REWRITE_TAC [GSYM REAL_INV_1OVER, GSYM REAL_INV1]
   ++ MATCH_MP_TAC REAL_LT_INV
   ++ RW_TAC arith_ss [REAL_LT]);

val REAL_POW = store_thm
  ("REAL_POW",
   ``!m n. &m pow n = &(m EXP n)``,
   STRIP_TAC
   ++ Induct >> RW_TAC real_ac_ss [pow, EXP]
   ++ RW_TAC real_ac_ss [pow, EXP, REAL_MUL]);

val POW_HALF_EXP = store_thm
  ("POW_HALF_EXP",
   ``!n. (1 / 2) pow n = inv (&(2 EXP n))``,
   RW_TAC std_ss [GSYM REAL_POW, GSYM REAL_INV_1OVER]
   ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
   ++ MATCH_MP_TAC POW_INV
   ++ REAL_ARITH_TAC);

val REAL_LE_INV_LE = store_thm
  ("REAL_LE_INV_LE",
   ``!x y. 0 < x /\ x <= y ==> inv y <= inv x``,
   RW_TAC std_ss []
   ++ KNOW_TAC `0 < inv x` >> PROVE_TAC [REAL_INV_POS]
   ++ SUFF_TAC `~(inv x < inv y)` >> PROVE_TAC [REAL_NOT_LT]
   ++ STRIP_TAC
   ++ KNOW_TAC `inv (inv y) < inv (inv x)` >> PROVE_TAC [REAL_LT_INV]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [REAL_INVINV_ALL, REAL_NOT_LT]);

val INV_SUC_POS = store_thm
  ("INV_SUC_POS",
   ``!n. 0 < 1 / & (SUC n)``,
   RW_TAC real_ac_ss [GSYM REAL_INV_1OVER, REAL_LT_INV_EQ, REAL_LT]);

val INV_SUC_MAX = store_thm
  ("INV_SUC_MAX",
   ``!n. 1 / & (SUC n) <= 1``,
   REWRITE_TAC [GSYM REAL_INV_1OVER]
   ++ Induct >> RW_TAC arith_ss [DECIDE ``SUC 0 = 1``, REAL_INV1, REAL_LE_REFL]
   ++ SUFF_TAC `inv (& (SUC (SUC n))) <= inv (& (SUC n))`
   >> PROVE_TAC [REAL_LE_TRANS]
   ++ SUFF_TAC `inv (& (SUC (SUC n))) < inv (& (SUC n))` >> REAL_ARITH_TAC
   ++ MATCH_MP_TAC REAL_LT_INV
   ++ RW_TAC arith_ss [REAL_LT]);

val INV_SUC = store_thm
  ("INV_SUC",
   ``!n. 0 < 1 / & (SUC n) /\ 1 / & (SUC n) <= 1``,
   PROVE_TAC [INV_SUC_POS, INV_SUC_MAX])

val ABS_UNIT_INTERVAL = store_thm
  ("ABS_UNIT_INTERVAL",
   ``!x y. 0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1 ==> abs (x - y) <= 1``,
   REAL_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* Extra definitions/theorems from (rich_)listTheory.                        *)
(* ------------------------------------------------------------------------- *)

val MEM_NIL = store_thm
  ("MEM_NIL",
   ``!l. (!(x:'a). ~MEM x l) = (l = [])``,
   Cases >> RW_TAC std_ss [MEM]
   ++ RW_TAC std_ss [MEM]
   ++ PROVE_TAC []);

val MAP_ID = store_thm
  ("MAP_ID",
   ``!(l:'a list). MAP (\x. x) l = l``,
   Induct >> RW_TAC list_ss []
   ++ RW_TAC list_ss []);

val MAP_MEM = store_thm
  ("MAP_MEM",
   ``!(f:'a->'b) l x. MEM x (MAP f l) = ?y. MEM y l /\ (x = f y)``,
   Induct_on `l` >> RW_TAC list_ss [MEM]
   ++ RW_TAC list_ss [MEM]
   ++ EQ_TAC <<
   [RW_TAC list_ss [] <<
    [PROVE_TAC [],
     PROVE_TAC []],
    PROVE_TAC []]);

val APPEND_MEM = store_thm
  ("APPEND_MEM",
   ``!(x:'a) l1 l2. MEM x (APPEND l1 l2) = (MEM x l1 \/ MEM x l2)``,
   Induct_on `l1` >> RW_TAC list_ss [MEM]
   ++ RW_TAC list_ss [MEM]
   ++ PROVE_TAC []);

val MEM_NIL_MAP_CONS = store_thm
  ("MEM_NIL_MAP_CONS",
   ``!(x:'a) l. ~MEM [] (MAP (CONS x) l)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [MEM]
   ++ RW_TAC list_ss [MEM]);

val FILTER_TRUE = store_thm
  ("FILTER_TRUE",
   ``!(l:'a list). FILTER (\x. T) l = l``,
   Induct >> RW_TAC list_ss [FILTER]
   ++ RW_TAC list_ss [FILTER]);

val FILTER_FALSE = store_thm
  ("FILTER_FALSE",
   ``!(l:'a list). FILTER (\x. F) l = []``,
   Induct >> RW_TAC list_ss [FILTER]
   ++ RW_TAC list_ss [FILTER]);

val LENGTH_FILTER = store_thm
  ("LENGTH_FILTER",
   ``!P (l:'a list). LENGTH (FILTER P l) <= LENGTH l``,
   GEN_TAC
   ++ Induct_on `l`
   ++ RW_TAC list_ss [FILTER]);

val FILTER_MEM = store_thm
  ("FILTER_MEM",
   ``!P (x:'a) l. MEM x (FILTER P l) ==> P x``,
   NTAC 2 STRIP_TAC
   ++ Induct >> RW_TAC std_ss [MEM, FILTER]
   ++ (RW_TAC std_ss [MEM, FILTER] ++ PROVE_TAC []));

val MEM_FILTER = store_thm
  ("MEM_FILTER",
   ``!P l (x:'a). MEM x (FILTER P l) ==> MEM x l``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [FILTER]
   ++ RW_TAC list_ss [FILTER, MEM]
   ++ PROVE_TAC []);

val FILTER_OUT_ELT = store_thm
  ("FILTER_OUT_ELT",
   ``!(x:'a) l. MEM x l \/ (FILTER (\y. ~(y = x)) l = l)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [FILTER]
   ++ (RW_TAC list_ss [MEM, FILTER]
	 ++ PROVE_TAC []));

val IS_PREFIX_NIL = store_thm
  ("IS_PREFIX_NIL",
   ``!(x:'a list). IS_PREFIX x [] /\ (IS_PREFIX [] x = (x = []))``,
   STRIP_TAC
   ++ Cases_on `x`
   ++ RW_TAC list_ss [IS_PREFIX]);

val IS_PREFIX_REFL = store_thm
  ("IS_PREFIX_REFL",
   ``!(x:'a list). IS_PREFIX x x``,
   Induct ++ RW_TAC list_ss [IS_PREFIX]);

val IS_PREFIX_ANTISYM = store_thm
  ("IS_PREFIX_ANTISYM",
   ``!(x:'a list) y. IS_PREFIX y x /\ IS_PREFIX x y ==> (x = y)``,
    Induct >> RW_TAC list_ss [IS_PREFIX_NIL]
    ++ Cases_on `y` >> RW_TAC list_ss [IS_PREFIX_NIL]
    ++ ONCE_REWRITE_TAC [IS_PREFIX]
    ++ PROVE_TAC []);

val IS_PREFIX_TRANS = store_thm
  ("IS_PREFIX_TRANS",
   ``!(x:'a list) y z. IS_PREFIX x y /\ IS_PREFIX y z ==> IS_PREFIX x z``,
   Induct >> PROVE_TAC [IS_PREFIX_NIL]
   ++ Cases_on `y` >> RW_TAC list_ss [IS_PREFIX_NIL, IS_PREFIX]
   ++ Cases_on `z` >> RW_TAC list_ss [IS_PREFIX_NIL, IS_PREFIX]
   ++ RW_TAC list_ss [IS_PREFIX]
   ++ PROVE_TAC []);

val IS_PREFIX_BUTLAST = store_thm
  ("IS_PREFIX_BUTLAST",
   ``!x:'a y. IS_PREFIX (x::y) (BUTLAST (x::y))``,
   Induct_on `y`
     >> RW_TAC list_ss [BUTLAST_CONS, IS_PREFIX]
   ++ RW_TAC list_ss [BUTLAST_CONS, IS_PREFIX]);

val IS_PREFIX_LENGTH = store_thm
  ("IS_PREFIX_LENGTH",
   ``!(x:'a list) y. IS_PREFIX y x ==> LENGTH x <= LENGTH y``,
   Induct >> RW_TAC list_ss [LENGTH]
   ++ Cases_on `y` >> RW_TAC list_ss [IS_PREFIX_NIL]
   ++ RW_TAC list_ss [IS_PREFIX, LENGTH]);

val IS_PREFIX_LENGTH_ANTI = store_thm
  ("IS_PREFIX_LENGTH_ANTI",
   ``!(x:'a list) y. IS_PREFIX y x /\ (LENGTH x = LENGTH y) ==> (x = y)``,
   Induct >> PROVE_TAC [LENGTH_NIL]
   ++ Cases_on `y` >> RW_TAC list_ss [LENGTH_NIL]
   ++ RW_TAC list_ss [IS_PREFIX, LENGTH]);

val IS_PREFIX_SNOC = store_thm
  ("IS_PREFIX_SNOC",
   ``!(x:'a) y z. IS_PREFIX (SNOC x y) z = IS_PREFIX y z \/ (z = SNOC x y)``,
   Induct_on `y`
     >> (Cases_on `z`
	 ++ RW_TAC list_ss [SNOC, IS_PREFIX_NIL, IS_PREFIX]
	 ++ PROVE_TAC [])
   ++ Cases_on `z` >> RW_TAC list_ss [IS_PREFIX]
   ++ RW_TAC list_ss [SNOC, IS_PREFIX]
   ++ PROVE_TAC []);

val FOLDR_MAP = store_thm
  ("FOLDR_MAP",
   ``!(f :'b -> 'c -> 'c) (e :'c) (g :'a -> 'b) (l :'a list).
         FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l``,
   RW_TAC list_ss []
   ++ Induct_on `l` >> RW_TAC list_ss [MAP, FOLDR]
   ++ RW_TAC list_ss [MAP, FOLDR]);

val LAST_MEM = store_thm
  ("LAST_MEM",
   ``!(h:'a) t. MEM (LAST (h::t)) (h::t)``,
   Induct_on `t` >> RW_TAC list_ss [MEM, LAST_CONS]
   ++ RW_TAC std_ss [LAST_CONS]
   ++ ONCE_REWRITE_TAC [MEM]
   ++ RW_TAC std_ss []);

val LAST_MAP_CONS = store_thm
  ("LAST_MAP_CONS",
   ``!(b:bool) h t. ?x. LAST (MAP (CONS b) (h::t)) = b::x``,
   Induct_on `t` >> RW_TAC list_ss [LAST_CONS]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC list_ss [LAST_CONS]);

val EXISTS_LONGEST = store_thm
  ("EXISTS_LONGEST",
   ``!(x:'a list) y. ?z. MEM z (x::y)
                    /\ (!w. MEM w (x::y) ==> LENGTH w <= LENGTH z)``,
   Induct_on `y` >> RW_TAC list_ss [MEM]
   ++ ONCE_REWRITE_TAC [MEM]
   ++ REPEAT STRIP_TAC
   ++ POP_ASSUM (MP_TAC o SPEC ``h:'a list``)
   ++ STRIP_TAC
   ++ EXISTS_TAC ``if LENGTH z <= LENGTH x then x else (z:'a list)``
   ++ ZAP_TAC std_ss [LESS_EQ_TRANS]);


(* ------------------------------------------------------------------------- *)
(* Extra definitions/theorems from pred_setTheory.                           *)
(* ------------------------------------------------------------------------- *)

val SET_EQ_EXT = store_thm
  ("SET_EQ_EXT",
   ``!(s:'a->bool) t. (s = t) = (!v. v IN s = v IN t)``,
   RW_TAC std_ss [SPECIFICATION]
   ++ PROVE_TAC [EQ_EXT]);

val UNION_DEF_ALT = store_thm
  ("UNION_DEF_ALT",
   ``!s t. s UNION t = (\x:'a. s x \/ t x)``,
   REPEAT STRIP_TAC
   ++ SUFF_TAC `!v:'a. v IN (s UNION t) = v IN (\x. s x \/ t x)`
     >> (PURE_REWRITE_TAC [SPECIFICATION]
         ++ PROVE_TAC [EQ_EXT])
   ++ RW_TAC std_ss [UNION_DEF, GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION]);

val INTER_UNION_RDISTRIB = store_thm
  ("INTER_UNION_RDISTRIB",
   ``!(p:'a->bool) q r. (p UNION q) INTER r = p INTER r UNION q INTER r``,
   RW_TAC std_ss [SET_EQ_EXT, IN_UNION, IN_INTER]
   ++ PROVE_TAC []);

val SUBSET_EQ = store_thm
  ("SUBSET_EQ",
   ``!(s:'a->bool) t. (s = t) = (s SUBSET t /\ t SUBSET s)``,
   REWRITE_TAC [SUBSET_DEF, SPECIFICATION]
   ++ PROVE_TAC [EQ_EXT]);

val SUBSET_EQ_DECOMP = store_thm
  ("SUBSET_EQ_DECOMP",
   ``!(s:'a->bool) t. s SUBSET t /\ t SUBSET s ==> (s = t)``,
   PROVE_TAC [SUBSET_EQ]);

val INTER_IS_EMPTY = store_thm
  ("INTER_IS_EMPTY",
   ``!(s:'a->bool) t. (s INTER t = {}) = (!x. ~s x \/ ~t x)``,
   RW_TAC std_ss [INTER_DEF, SET_EQ_EXT, GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION, EMPTY_DEF]);

val UNION_DISJOINT_SPLIT = store_thm
  ("UNION_DISJOINT_SPLIT",
   ``!(s:'a->bool) t u. (s UNION t = s UNION u)
                        /\ (s INTER t = {}) /\ (s INTER u = {})
                        ==> (t = u)``,
   RW_TAC std_ss [UNION_DEF_ALT, SET_EQ_EXT, INTER_IS_EMPTY, SPECIFICATION]
   ++ PROVE_TAC []);

val IN_COMPL = store_thm
  ("IN_COMPL",
   ``!(x:'a) s. x IN COMPL s = ~(x IN s)``,
   RW_TAC std_ss [COMPL_DEF, IN_DIFF, IN_UNIV]);

val IN_EMPTY = store_thm
  ("IN_EMPTY",
   ``!(x:'a). ~(x IN {})``,
   RW_TAC std_ss [EMPTY_DEF, SPECIFICATION]);

val GSPEC_DEF_ALT = store_thm
  ("GSPEC_DEF_ALT",
   ``!(f:'a -> 'b # bool). GSPEC f = (\v. ?x. (v, T) = f x)``,
   RW_TAC std_ss [SET_EQ_EXT, GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION]);

val COMPL_COMPL = store_thm
  ("COMPL_COMPL",
   ``!(s:'a->bool). COMPL (COMPL s) = s``,
   RW_TAC std_ss [SET_EQ_EXT, COMPL_DEF, UNIV_DEF, DIFF_DEF,
		  GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION]);

val COMPL_CLAUSES = store_thm
  ("COMPL_CLAUSES",
   ``!(s:'a->bool). (COMPL s INTER s = {})
                    /\ (COMPL s UNION s = UNIV)``,
   RW_TAC std_ss [SET_EQ_EXT, COMPL_DEF, UNIV_DEF, DIFF_DEF,
		  GSPECIFICATION, UNION_DEF, INTER_DEF, EMPTY_DEF]
   ++ RW_TAC std_ss [SPECIFICATION]);

val COMPL_SPLITS = store_thm
  ("COMPL_SPLITS",
   ``!(p:'a->bool) q. p INTER q UNION COMPL p INTER q = q``,
   RW_TAC std_ss [SET_EQ_EXT, IN_UNION, IN_COMPL, IN_INTER]
   ++ PROVE_TAC []);

val INTER_UNION_COMPL = store_thm
  ("INTER_UNION_COMPL",
   ``!(s:'a->bool) t. s INTER t
                      = COMPL (COMPL s UNION COMPL t)``,
   RW_TAC std_ss [COMPL_DEF, SET_EQ_EXT, GSPECIFICATION, DIFF_DEF,
		  UNION_DEF, INTER_DEF]
   ++ RW_TAC std_ss [SPECIFICATION, UNIV_DEF]);

val _ = export_theory ();
