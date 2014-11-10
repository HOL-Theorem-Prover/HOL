open HolKernel boolLib Parse BasicProvers

open simpLib numLib TotalDefn metisLib
open listTheory rich_listTheory logrootTheory arithmeticTheory bitTheory

val ARITH_ss = numSimps.ARITH_ss

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = new_theory "numposrep"

(* ------------------------------------------------------------------------- *)

val () = computeLib.auto_import_definitions := false

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

val BOOLIFY_def = Define`
   (BOOLIFY 0 m a = a) /\
   (BOOLIFY (SUC n) m a = BOOLIFY n (DIV2 m) (ODD m::a))`

(* ------------------------------------------------------------------------- *)

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

local
  val simp = ASM_SIMP_TAC (srw_ss()++ARITH_ss)
  val fs = FULL_SIMP_TAC (srw_ss()++ARITH_ss)
  val rw = SRW_TAC[ARITH_ss]
  val op >> = op THEN
  val op >- = op THEN1
in
val l2n_eq_0 = store_thm("l2n_eq_0",
  ``!b. 0 < b ==> !l. (l2n b l = 0) <=> EVERY ($= 0 o combin$C $MOD b) l``,
  NTAC 2 STRIP_TAC THEN Induct THEN simp[l2n_def] THEN
  Q.X_GEN_TAC`z` THEN Cases_on`0=z MOD b` THEN simp[])

val l2n_SNOC_0 = store_thm("l2n_SNOC_0",
  ``!b ls. 0 < b ==> (l2n b (SNOC 0 ls) = l2n b ls)``,
  GEN_TAC THEN Induct THEN simp[l2n_def])

val MOD_EQ_0_0 = prove(
  ``!n b. 0 < b ==> (n MOD b = 0) ==> n < b ==> (n = 0)``,
  SRW_TAC[][MOD_EQ_0_DIVISOR] THEN Cases_on`d` THEN FULL_SIMP_TAC(srw_ss())[])

val LOG_l2n = store_thm("LOG_l2n",
  ``!b. 1 < b ==> !l. l <> [] /\ 0 < LAST l /\ EVERY ($> b) l ==>
        (LOG b (l2n b l) = PRE (LENGTH l))``,
  NTAC 2 STRIP_TAC THEN Induct THEN simp[l2n_def] THEN
  rw[] THEN fs[LAST_DEF] THEN
  Cases_on`l=[]` THEN fs[l2n_def] THEN1 (
    simp[LOG_EQ_0] ) THEN
  Q.MATCH_ASSUM_ABBREV_TAC`LOG b z = d` THEN
  `h + b * z = b * z + h` by simp[] THEN POP_ASSUM SUBST1_TAC THEN
  Q.SPECL_THEN[`b`,`h`,`z`]MP_TAC LOG_add_digit THEN
  simp[Abbr`d`] THEN
  Q_TAC SUFF_TAC`0 < z` THEN1 (
    simp[] THEN Cases_on`l` THEN fs[] ) THEN
  simp[Abbr`z`] THEN
  Cases_on`l2n b l = 0` THEN simp[] THEN
  `0 < b` by simp[] THEN
  fs[l2n_eq_0] THEN
  `?z. MEM z l /\ 0 < z` by (
    Q.EXISTS_TAC`LAST l` THEN simp[] THEN
    Cases_on`l` THEN simp[rich_listTheory.MEM_LAST] THEN
    fs[] ) THEN
  fs[EVERY_MEM] THEN
  RES_TAC THEN
  `z = 0` by METIS_TAC[MOD_EQ_0_0,GREATER_DEF] THEN
  fs[])

val l2n_dropWhile_0 = store_thm("l2n_dropWhile_0",
  ``!b ls.
      0 < b ==> (l2n b (REVERSE (dropWhile ($= 0) (REVERSE ls))) = l2n b ls)``,
  GEN_TAC >> HO_MATCH_MP_TAC SNOC_INDUCT >>
  simp[dropWhile_def,REVERSE_SNOC] >> rw[] >>
  rw[] >> rw[l2n_SNOC_0] >> rw[SNOC_APPEND])

val LOG_l2n_dropWhile = store_thm("LOG_l2n_dropWhile",
  ``!b l. 1 < b /\ EXISTS ($<> 0) l /\ EVERY ($>b) l ==>
          (LOG b (l2n b l) = PRE (LENGTH (dropWhile ($= 0) (REVERSE l))))``,
  Tactical.REPEAT STRIP_TAC >>
  `0 < b` by simp[] >>
  simp[Once(GSYM l2n_dropWhile_0)] >>
  Q.MATCH_ABBREV_TAC`x = PRE (LENGTH y)` >>
  Q_TAC SUFF_TAC`x = PRE (LENGTH (REVERSE y))` >- rw[] >>
  markerLib.UNABBREV_ALL_TAC >>
  MATCH_MP_TAC (MP_CANON LOG_l2n) >>
  simp[dropWhile_eq_nil,rich_listTheory.EXISTS_REVERSE,
       rich_listTheory.EVERY_REVERSE,combinTheory.o_DEF] >>
  fs[EVERY_MEM] >>
  Tactical.REVERSE CONJ_TAC >- METIS_TAC[MEM_dropWhile_IMP,MEM_REVERSE] >>
  Q.MATCH_ABBREV_TAC`0:num < LAST (REVERSE ls)` >>
  Cases_on`ls = []` >- (
    fs[Abbr`ls`,dropWhile_eq_nil,EVERY_MEM,EXISTS_MEM] >>
    METIS_TAC[] ) >>
  simp[LAST_REVERSE] >>
  Q_TAC SUFF_TAC`~ (($= 0) (HD ls))` >- simp[] >>
  Q.UNABBREV_TAC`ls` >>
  MATCH_MP_TAC HD_dropWhile >>
  fs[EXISTS_MEM] >> METIS_TAC[])

end

(* ------------------------------------------------------------------------- *)

val n2l_BOUND = Q.store_thm("n2l_BOUND",
  `!b n. 0 < b ==> EVERY ($> b) (n2l b n)`,
  NTAC 2 STRIP_TAC \\ completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, GREATER_DEF]
    \\ `LOG b (n DIV b) < LOG b n` by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
    \\ SRW_TAC [ARITH_ss] []);

(* ------------------------------------------------------------------------- *)

val l2n_pow2_compute = Q.store_thm("l2n_pow2_compute",
   `(!p. l2n (2 ** p) [] = 0) /\
    (!p h t. l2n (2 ** p) (h::t) =
             MOD_2EXP p h + TIMES_2EXP p (l2n (2 ** p) t))`,
   SRW_TAC [ARITH_ss] [l2n_def, TIMES_2EXP_def, MOD_2EXP_def])

val lem = (GEN_ALL o REWRITE_RULE [EXP] o Q.SPECL [`n`,`0`] o
           REWRITE_RULE [DECIDE ``1 < 2``] o Q.SPEC `2`) EXP_BASE_LT_MONO

val n2l_pow2_compute = Q.store_thm("n2l_pow2_compute",
   `!p n. 0 < p ==>
         (n2l (2 ** p) n =
          let (q,r) = DIVMOD_2EXP p n in
            if q = 0 then [r] else r::n2l (2 ** p) q)`,
   SRW_TAC [] [Once n2l_def, DIVMOD_2EXP_def,
               DECIDE ``x < 2 = (x = 0) \/ (x = 1)``]
   \\ SRW_TAC [ARITH_ss] [LESS_DIV_EQ_ZERO]
   \\ FULL_SIMP_TAC arith_ss [lem, DIV_0_IMP_LT])

val l2n2_def = new_definition ("l2n2", ``l2n2 = l2n 2``)

val l2n2_empty = Q.prove(
   `l2n2 [] = ZERO`,
   REWRITE_TAC [l2n2_def, l2n_def, arithmeticTheory.ALT_ZERO]
   )

val l2n_2 =
   SIMP_RULE arith_ss [bitTheory.MOD_2EXP_def, bitTheory.TIMES_2EXP_def]
      (Q.SPEC `1` (Thm.CONJUNCT2 l2n_pow2_compute))

val l2n2_cons0 = Q.prove(
   `!t. l2n2 (0::t) = numeral$iDUB (l2n2 t)`,
   SIMP_TAC arith_ss [l2n2_def, l2n_2]
   \\ METIS_TAC [arithmeticTheory.MULT_COMM, arithmeticTheory.TIMES2,
                 numeralTheory.iDUB]
   )

val l2n2_cons1 = Q.prove(
   `!t. l2n2 (1::t) = arithmetic$BIT1 (l2n2 t)`,
   SIMP_TAC arith_ss [l2n2_def, l2n_2]
   \\ METIS_TAC [numLib.DECIDE ``2 * a + 1 = a + (a + SUC 0)``,
                 arithmeticTheory.BIT1]
   )

val l2n2 = Q.prove(
   `(!t. l2n 2 (0::t) = NUMERAL (l2n2 (0::t))) /\
    (!t. l2n 2 (1::t) = NUMERAL (l2n2 (1::t)))`,
   REWRITE_TAC [l2n2_def, arithmeticTheory.NUMERAL_DEF]
   )

val l2n_2_thms = save_thm("l2n_2_thms",
   LIST_CONJ (CONJUNCTS l2n2 @ [l2n2_empty, l2n2_cons0, l2n2_cons1]))

val () = Parse.remove_ovl_mapping "l2n2" {Thy = "numposrep", Name = "l2n2"}

(* ------------------------------------------------------------------------- *)

val BIT_num_from_bin_list = Q.store_thm("BIT_num_from_bin_list",
   `!x l. EVERY ($> 2) l /\ x < LENGTH l ==>
          (BIT x (num_from_bin_list l) = (EL x l = 1))`,
   SRW_TAC [ARITH_ss]
     [num_from_bin_list_def, l2n_DIGIT, SUC_SUB, BIT_def, BITS_THM])

val EL_num_to_bin_list = Q.store_thm("EL_num_to_bin_list",
   `!x n.
     x < LENGTH (num_to_bin_list n) ==> (EL x (num_to_bin_list n) = BITV n x)`,
   SRW_TAC [ARITH_ss]
     [num_to_bin_list_def, EL_n2l, SUC_SUB, BITV_def, BIT_def, BITS_THM])

val tac =
   SRW_TAC [ARITH_ss]
    [FUN_EQ_THM, l2n_n2l,
     num_from_bin_list_def, num_from_oct_list_def, num_from_dec_list_def,
     num_from_hex_list_def, num_to_bin_list_def, num_to_oct_list_def,
     num_to_dec_list_def, num_to_hex_list_def]

val num_bin_list = Q.store_thm("num_bin_list",
  `num_from_bin_list o num_to_bin_list = I`, tac)
val num_oct_list = Q.store_thm("num_oct_list",
  `num_from_oct_list o num_to_oct_list = I`, tac)
val num_dec_list = Q.store_thm("num_dec_list",
  `num_from_dec_list o num_to_dec_list = I`, tac)
val num_hex_list = Q.store_thm("num_hex_list",
  `num_from_hex_list o num_to_hex_list = I`, tac)

(* ------------------------------------------------------------------------- *)

val _ = export_theory()
