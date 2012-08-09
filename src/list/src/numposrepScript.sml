open HolKernel boolLib Parse BasicProvers

open simpLib numLib TotalDefn metisLib
open listTheory rich_listTheory logrootTheory arithmeticTheory

val ARITH_ss = numSimps.ARITH_ss
val _ = new_theory "numposrep"

val l2n_def = Define`
  (l2n b [] = 0) /\
  (l2n b (h::t) = h MOD b + b * l2n b t)`;

val n2l_def = Define`
  n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b)`;

val num_from_bin_list_def = Define `num_from_bin_list = l2n 2`;
val num_from_oct_list_def = Define `num_from_oct_list = l2n 8`;
val num_from_dec_list_def = Define `num_from_dec_list = l2n 10`;
val num_from_hex_list_def = Define `num_from_hex_list = l2n 16`;

val num_to_bin_list_def = Define `num_to_bin_list = n2l 2`;
val num_to_oct_list_def = Define `num_to_oct_list = n2l 8`;
val num_to_dec_list_def = Define `num_to_dec_list = n2l 10`;
val num_to_hex_list_def = Define `num_to_hex_list = n2l 16`;

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val LENGTH_n2l = Q.store_thm("LENGTH_n2l",
  `!b n. 1 < b ==> (LENGTH (n2l b n) = if n = 0 then 1 else SUC (LOG b n))`,
  completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, LOG_RWT]
    \\ SRW_TAC [ARITH_ss] [LOG_RWT]
    \\ `0 < n DIV b` by SRW_TAC [ARITH_ss] [X_LT_DIV]
    \\ DECIDE_TAC);

val LOG_DIV_LESS = Q.prove(
  `!b n. b <= n /\ 1 < b ==> LOG b (n DIV b) < LOG b n`,
  SRW_TAC [] [] \\ IMP_RES_TAC LOG_DIV \\ DECIDE_TAC);

val l2n_n2l = Q.store_thm("l2n_n2l",
  `!b n. 1 < b ==> (l2n b (n2l b n) = n)`,
  completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, l2n_def]
    \\ `LOG b (n DIV b) < LOG b n` by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
    \\ SRW_TAC [ARITH_ss] [(GSYM o ONCE_REWRITE_RULE [MULT_COMM]) DIVISION]);

val l2n_lt = Q.store_thm("l2n_lt",
  `!l b. 0 < b ==> l2n b l < b ** LENGTH l`,
  Induct \\ SRW_TAC [] [l2n_def, arithmeticTheory.EXP]
  \\ RES_TAC
  \\ IMP_RES_TAC arithmeticTheory.LESS_ADD_1
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM SUBST1_TAC
  \\ SRW_TAC [] [arithmeticTheory.LEFT_ADD_DISTRIB]
  \\ SRW_TAC [ARITH_ss]
       [arithmeticTheory.MOD_LESS, DECIDE ``a < b:num ==> (a < b + c)``])

(* ......................................................................... *)

val LENGTH_l2n = Q.store_thm("LENGTH_l2n",
  `!b l. 1 < b /\ EVERY ($> b) l /\ ~(l2n b l = 0) ==>
     (SUC (LOG b (l2n b l)) <= LENGTH l)`,
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [l2n_def, GREATER_DEF]
    << [ALL_TAC, `~(h = 0)` by (`0 < b` by DECIDE_TAC \\ STRIP_TAC
          \\ IMP_RES_TAC ZERO_MOD \\ FULL_SIMP_TAC arith_ss [])]
    \\ `0 < h + b * l2n b l`
    by (IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss [LESS_MULT2]
         ``1 < b /\ ~(c = 0) ==> 0 < b * c``) \\ SRW_TAC [ARITH_ss] [])
    \\ SRW_TAC [ARITH_ss] [LOG_RWT, LESS_DIV_EQ_ZERO,
         SIMP_RULE arith_ss [] ADD_DIV_ADD_DIV]
    << [Cases_on `l` \\ FULL_SIMP_TAC (arith_ss++listSimps.LIST_ss) [l2n_def],
        SRW_TAC [ARITH_ss] [(GSYM o REWRITE_RULE [GSYM SUC_ONE_ADD]) LOG_DIV],
        `~(l2n b l = 0)` by (STRIP_TAC \\ FULL_SIMP_TAC arith_ss [])
          \\ SRW_TAC [] []]);

val EL_TAKE = Q.store_thm("EL_TAKE",
  `!x n l. x < n /\ n <= LENGTH l ==> (EL x (TAKE n l) = EL x l)`,
  Induct_on `l` \\ Cases_on `x` \\ SRW_TAC [ARITH_ss] []);

val l2n_DIGIT = Q.store_thm("l2n_DIGIT",
  `!b l x. 1 < b /\ EVERY ($> b) l /\ x < LENGTH l ==>
      ((l2n b l DIV b ** x) MOD b = EL x l)`,
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [l2n_def, GREATER_DEF]
    \\ Cases_on `x`
    \\ SRW_TAC [ARITH_ss]
        [EXP, GSYM DIV_DIV_DIV_MULT, ZERO_LT_EXP, LESS_DIV_EQ_ZERO,
         SIMP_RULE arith_ss [] (CONJ MOD_TIMES ADD_DIV_ADD_DIV)]);

val DIV_0_IMP_LT = Q.store_thm("DIV_0_IMP_LT",
  `!b n. 1 < b /\ (n DIV b = 0) ==> n < b`,
  REPEAT STRIP_TAC \\ SPOSE_NOT_THEN ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [NOT_LESS]
    \\ IMP_RES_TAC LESS_EQUAL_ADD
    \\ `0 < b` by DECIDE_TAC
    \\ IMP_RES_TAC ADD_DIV_ADD_DIV
    \\ POP_ASSUM (Q.SPECL_THEN [`1`,`p`] (ASSUME_TAC o SIMP_RULE std_ss []))
    \\ FULL_SIMP_TAC arith_ss []);

val lem = Q.prove(
  `!b n. 1 < b ==> PRE (LENGTH (n2l b n)) <= LENGTH (n2l b (n DIV b))`,
  SRW_TAC [ARITH_ss] [LENGTH_n2l]
    << [
      `0 <= n DIV b /\ 0 < n` by DECIDE_TAC
        \\ IMP_RES_TAC DIV_0_IMP_LT
        \\ SRW_TAC [ARITH_ss] [LOG_RWT],
      IMP_RES_TAC (METIS_PROVE [LESS_DIV_EQ_ZERO,NOT_LESS_EQUAL]
         ``!b n. 1 < b /\ ~(n DIV b = 0) ==> b <= n``)
        \\ SRW_TAC [ARITH_ss] [LOG_DIV]]);

val EL_n2l = Q.store_thm("EL_n2l",
  `!b x n. 1 < b /\ x < LENGTH (n2l b n) ==>
     (EL x (n2l b n) = (n DIV (b ** x)) MOD b)`,
  completeInduct_on `LOG b n`
    \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [n2l_def]
    \\ SRW_TAC [ARITH_ss] []
    << [
      IMP_RES_TAC LENGTH_n2l
        \\ Cases_on `n = 0`
        \\ FULL_SIMP_TAC arith_ss []
        << [ALL_TAC, `LOG b n = 0` by SRW_TAC [ARITH_ss] [LOG_RWT]]
        \\ `x = 0` by DECIDE_TAC \\ SRW_TAC [ARITH_ss] [EXP],
      Cases_on `x = 0`
        \\ SRW_TAC [ARITH_ss] [EXP, EL_CONS]
        \\ `LOG b (n DIV b) < LOG b n /\ PRE x < x /\ 0 < x`
        by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
        \\ `PRE x < LENGTH (n2l b (n DIV b))`
        by METIS_TAC [lem, INV_PRE_LESS, LESS_LESS_EQ_TRANS]
        \\ RES_TAC
        \\ POP_ASSUM (Q.SPECL_THEN [`n DIV b`,`b`]
             (ASSUME_TAC o SIMP_RULE std_ss []))
        \\ POP_ASSUM (Q.SPEC_THEN `PRE x` IMP_RES_TAC)
        \\ SRW_TAC [ARITH_ss] [GSYM EXP, DIV_DIV_DIV_MULT,
             DECIDE ``!n. 0 < n ==> (SUC (PRE n) = n)``]]);

val LIST_EQ = Q.prove(
  `!a b. (LENGTH a = LENGTH b) /\
         (!x. x < LENGTH a ==> (EL x a = EL x b)) ==>
         (a = b)`,
  Induct_on `a` \\ Induct_on `b` \\ SRW_TAC [] []
    \\ METIS_TAC [prim_recTheory.LESS_0, LESS_MONO_EQ, EL, HD, TL]);

val n2l_l2n = Q.prove(
  `!b n l. 1 < b /\ EVERY ($> b) l /\ (n = l2n b l) ==>
      (n2l b n = if n = 0 then [0] else TAKE (SUC (LOG b n)) l)`,
  SRW_TAC [] [] >> SRW_TAC [ARITH_ss] [Once n2l_def]
    \\ MATCH_MP_TAC LIST_EQ \\ IMP_RES_TAC LENGTH_l2n
    \\ SRW_TAC [ARITH_ss] [LENGTH_n2l,LENGTH_TAKE,EL_TAKE,EL_n2l,l2n_DIGIT]);

val n2l_l2n = save_thm("n2l_l2n",
  n2l_l2n |> Q.SPECL [`b`,`l2n b l`,`l`]
          |> REWRITE_RULE []
          |> Q.GEN `l` |> Q.GEN `b`);

(* ------------------------------------------------------------------------- *)

val n2l_BOUND = Q.store_thm("n2l_BOUND",
  `!b n. 0 < b ==> EVERY ($> b) (n2l b n)`,
  NTAC 2 STRIP_TAC \\ completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, GREATER_DEF]
    \\ `LOG b (n DIV b) < LOG b n` by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
    \\ SRW_TAC [ARITH_ss] []);

val _ = export_theory()
