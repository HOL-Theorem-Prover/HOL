open HolKernel boolLib Parse BasicProvers

open simpLib boolSimps numLib TotalDefn metisLib
open listTheory rich_listTheory logrootTheory arithmeticTheory bitTheory

val ARITH_ss = numSimps.ARITH_ss

val _ = new_theory "numposrep"

val simp = ASM_SIMP_TAC (srw_ss()++ARITH_ss)
val fs = FULL_SIMP_TAC (srw_ss()++ARITH_ss)
val rw = SRW_TAC[ARITH_ss]

(* ------------------------------------------------------------------------- *)

Definition l2n_def:
  (l2n b [] = 0) /\
  (l2n b (h::t) = h MOD b + b * l2n b t)
End

Definition n2l_def:
  n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b)
End

(* related version that gives MS-digit first, using an accumulator, and passes
   each digit through a function *)
Definition n2lA_def[nocompute]:
  n2lA A f b n = if n < b \/ b < 2 then f (n MOD b)::A
                 else n2lA (f (n MOD b) :: A) f b (n DIV b)
End

Definition num_from_bin_list_def: num_from_bin_list = l2n 2 o REVERSE
End
Definition num_from_oct_list_def: num_from_oct_list = l2n 8 o REVERSE
End
Definition num_from_dec_list_def: num_from_dec_list = l2n 10 o REVERSE
End
Definition num_from_hex_list_def: num_from_hex_list = l2n 16 o REVERSE
End

Theorem n2lA_10[compute]:
  n2lA A f 10 n = if n < 10 then f n::A
                  else n2lA (f (n MOD 10) :: A) f 10 (n DIV 10)
Proof
  simp[Once n2lA_def, SimpLHS]
QED

Theorem n2lA_n2l:
  !A n. n2lA A f b n = MAP f (REVERSE (n2l b n)) ++ A
Proof
  completeInduct_on ‘n’ >> simp_tac (srw_ss()) [Once n2lA_def, Once n2l_def] >>
  rw[] >> simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]
QED

Theorem n2l_n2lA:
  n2l b n = REVERSE (n2lA [] I b n)
Proof simp[n2lA_n2l]
QED



Definition num_to_bin_list_def: num_to_bin_list = REVERSE o n2l 2
End
Definition num_to_oct_list_def: num_to_oct_list = REVERSE o n2l 8
End
Definition num_to_dec_list_def: num_to_dec_list = REVERSE o n2l 10
End
Definition num_to_hex_list_def: num_to_hex_list = REVERSE o n2l 16
End

Definition BOOLIFY_def:
   (BOOLIFY 0 m a = a) /\
   (BOOLIFY (SUC n) m a = BOOLIFY n (DIV2 m) (ODD m::a))
End

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

Theorem LENGTH_l2n:
  !b l. 1 < b /\ EVERY ($> b) l /\ ~(l2n b l = 0) ==>
        SUC (LOG b (l2n b l)) <= LENGTH l
Proof
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [l2n_def, GREATER_DEF] \\
  Cases_on ‘h MOD b = 0’ \\ FULL_SIMP_TAC (srw_ss()) []
  >- (REV_FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [MOD_EQ_0_DIVISOR] \\
      FULL_SIMP_TAC (srw_ss()) [LT_MULT_CANCEL_RBARE] \\ SRW_TAC[][] \\
      SRW_TAC[ARITH_ss][LOG_MULT]) \\
  ‘h <> 0’ by (STRIP_TAC \\ SRW_TAC[][] \\ REV_FULL_SIMP_TAC (srw_ss()) []) \\
  ‘0 < h + b * l2n b l’ by DECIDE_TAC \\
  Cases_on ‘l2n b l = 0’
  >- (SRW_TAC[][] \\ SRW_TAC[ARITH_ss][LOG_RWT]) \\
  SRW_TAC[][LOG_RWT] \\
  ‘(h + b * l2n b l) DIV b = l2n b l’
     by METIS_TAC[DIV_MULT, MULT_COMM, ADD_COMM] \\
  SRW_TAC[][]
QED

val l2n_DIGIT = Q.store_thm("l2n_DIGIT",
  `!b l x. 1 < b /\ EVERY ($> b) l /\ x < LENGTH l ==>
      ((l2n b l DIV b ** x) MOD b = EL x l)`,
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [l2n_def, GREATER_DEF]
    \\ Cases_on `x`
    \\ SRW_TAC [ARITH_ss]
        [EXP, GSYM DIV_DIV_DIV_MULT, ZERO_LT_EXP, LESS_DIV_EQ_ZERO,
         SIMP_RULE arith_ss [] (CONJ MOD_TIMES ADD_DIV_ADD_DIV)]);

val lem = Q.prove(
  `!b n. 1 < b ==> PRE (LENGTH (n2l b n)) <= LENGTH (n2l b (n DIV b))`,
  SRW_TAC [ARITH_ss] [LENGTH_n2l]
    >| [
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
    >| [
      IMP_RES_TAC LENGTH_n2l
        \\ Cases_on `n = 0`
        \\ FULL_SIMP_TAC arith_ss []
        >| [ALL_TAC, `LOG b n = 0` by SRW_TAC [ARITH_ss] [LOG_RWT]]
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

Theorem LIST_EQ[local] = iffRL LIST_EQ_REWRITE

Theorem n2l_l2n[local]:
  !b n l. 1 < b /\ EVERY ($> b) l /\ (n = l2n b l) ==>
          (n2l b n = if n = 0 then [0] else TAKE (SUC (LOG b n)) l)
Proof
  SRW_TAC [] [] >- SRW_TAC [ARITH_ss] [Once n2l_def]
    \\ MATCH_MP_TAC LIST_EQ \\ IMP_RES_TAC LENGTH_l2n
    \\ SRW_TAC [ARITH_ss] [LENGTH_n2l,LENGTH_TAKE,EL_TAKE,EL_n2l,l2n_DIGIT]
QED

Theorem n2l_l2n =
  n2l_l2n |> Q.SPECL [`b`,`l2n b l`,`l`]
          |> REWRITE_RULE []
          |> Q.GEN `l` |> Q.GEN `b`

Theorem l2n_eq_0:
  !b. 0 < b ==> !l. (l2n b l = 0) <=> EVERY ($= 0 o combin$C $MOD b) l
Proof
  NTAC 2 STRIP_TAC THEN Induct THEN simp[l2n_def] THEN
  Q.X_GEN_TAC`z` THEN Cases_on`0=z MOD b` THEN simp[]
QED

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

Theorem n2l_pow2_compute:
   !p n. 0 < p ==>
         (n2l (2 ** p) n =
          let (q,r) = DIVMOD_2EXP p n in
            if q = 0 then [r] else r::n2l (2 ** p) q)
Proof
   SRW_TAC [] [Once n2l_def, DIVMOD_2EXP_def,
               DECIDE ``x < 2 <=> (x = 0) \/ (x = 1)``]
   \\ SRW_TAC [ARITH_ss] [LESS_DIV_EQ_ZERO]
   \\ FULL_SIMP_TAC arith_ss [lem, DIV_0_IMP_LT]
QED

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

Theorem BIT_l2n_2:
  !x l. EVERY ($> 2) l ==>
        (BIT x (l2n 2 l) <=> x < LENGTH l /\ EL x l = 1)
Proof
  rpt strip_tac >> Cases_on ‘x < LENGTH l’ >>
  SRW_TAC [ARITH_ss] [l2n_DIGIT, SUC_SUB, BIT_def, BITS_THM] >>
  Q.RENAME_TAC [‘l2n 2 l DIV 2 ** x’] >>
  Q_TAC SUFF_TAC ‘l2n 2 l DIV 2 ** x = 0’ >> simp[] >>
  MATCH_MP_TAC LESS_DIV_EQ_ZERO >>
  MATCH_MP_TAC LESS_LESS_EQ_TRANS >> Q.EXISTS_TAC ‘2 ** LENGTH l’ >>
  SRW_TAC[ARITH_ss][l2n_lt]
QED

Theorem BIT_num_from_bin_list:
  !x l. EVERY ($> 2) l /\ x < LENGTH l ==>
        (BIT x (num_from_bin_list l) = (EL x (REVERSE l) = 1))
Proof
   simp[num_from_bin_list_def, BIT_l2n_2]
QED

Theorem EL_num_to_bin_list:
  !x n.
    x < LENGTH (num_to_bin_list n) ==>
    EL x (REVERSE (num_to_bin_list n)) = BITV n x
Proof
   SRW_TAC [ARITH_ss]
     [num_to_bin_list_def, EL_n2l, SUC_SUB, BITV_def, BIT_def, BITS_THM]
QED

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

val l2n_APPEND = Q.store_thm("l2n_APPEND",
  `!b l1 l2. l2n b (l1 ++ l2) = l2n b l1 + b ** (LENGTH l1) * l2n b l2`,
  Induct_on `l1` \\ SRW_TAC [ARITH_ss] [EXP, l2n_def]);

val EXP_MONO = Q.prove(
  `!b m n x. 1 < b /\ m < n /\ x < b ** m ==> (b ** m + x < b ** n)`,
  Induct_on `n`
    \\ SRW_TAC [ARITH_ss] [EXP]
    \\ Cases_on `m = n`
    \\ SRW_TAC [ARITH_ss] []
    >| [
      `?p. b ** m = p + x` by METIS_TAC [LESS_ADD]
         \\ `?q. b = 1 + (q + 1)` by METIS_TAC [LESS_ADD_1]
         \\ FULL_SIMP_TAC arith_ss [LEFT_ADD_DISTRIB],
      `m < n` by DECIDE_TAC \\ RES_TAC
        \\ `b ** n < b * b ** n` by SRW_TAC [ARITH_ss] []
        \\ DECIDE_TAC]);

val l2n_b_1 = Q.prove(
  `!b. 1 < b ==> (l2n b [1] = 1)`,
  SRW_TAC [] [l2n_def]);

val l2n_11 = Q.store_thm("l2n_11",
  `!b l1 l2.
      1 < b /\ EVERY ($> b) l1 /\ EVERY ($> b) l2 ==>
      ((l2n b (l1 ++ [1]) = l2n b (l2 ++ [1])) = (l1 = l2))`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ SRW_TAC [] []
    \\ MATCH_MP_TAC LIST_EQ
    \\ sg `LENGTH l1 = LENGTH l2`
    \\ SRW_TAC [] []
    >| [
      SPOSE_NOT_THEN STRIP_ASSUME_TAC
        \\ Q.PAT_X_ASSUM `l2n b x = l2n b y` MP_TAC
        \\ ASM_SIMP_TAC (srw_ss()++ARITH_ss) [l2n_APPEND, l2n_b_1]
        \\ `(LENGTH l1 < LENGTH l2) \/ (LENGTH l2 < LENGTH l1)`
        by METIS_TAC [LESS_LESS_CASES]
        >| [MATCH_MP_TAC (DECIDE ``a < b ==> ~(a = b + x)``),
            MATCH_MP_TAC (DECIDE ``b < a ==> ~(a + x = b)``)]
        \\ MATCH_MP_TAC EXP_MONO
        \\ ASM_SIMP_TAC (srw_ss()++ARITH_ss) [l2n_lt],
      `x < LENGTH l1` by DECIDE_TAC
        \\ IMP_RES_TAC (GSYM l2n_DIGIT)
        \\ NTAC 2 (POP_ASSUM SUBST1_TAC)
        \\ FULL_SIMP_TAC (srw_ss()) [l2n_APPEND]]);

Theorem BITWISE_l2n_2:
  LENGTH l1 = LENGTH l2 ==>
  BITWISE (LENGTH l1) op (l2n 2 l1) (l2n 2 l2) =
  l2n 2 (MAP2 (\x y. bool_to_bit $ op (ODD x) (ODD y)) l1 l2)
Proof
  Q.ID_SPEC_TAC`l2`
  \\ Induct_on`l1`
  \\ simp[BITWISE_EVAL]
  >- simp[BITWISE_def, l2n_def]
  \\ Q.X_GEN_TAC`b`
  \\ Cases \\ fs[BITWISE_EVAL]
  \\ strip_tac
  \\ fs[l2n_def]
  \\ simp[SBIT_def, ODD_ADD, ODD_MULT, GSYM bool_to_bit_def]
QED

Theorem l2n_2_neg:
  !ls.
  EVERY ($> 2) ls ==>
  l2n 2 (MAP (\x. 1 - x) ls) = 2 ** LENGTH ls - SUC (l2n 2 ls)
Proof
  Induct
  \\ rw[l2n_def]
  \\ fs[EXP, ADD1]
  \\ simp[LEFT_SUB_DISTRIB, LEFT_ADD_DISTRIB, SUB_RIGHT_ADD]
  \\ Q.SPECL_THEN[`ls`,`2`]mp_tac l2n_lt
  \\ simp[]
QED

Theorem l2n_max:
  0 < b ==>
  !ls. (l2n b ls = b ** (LENGTH ls) - 1) <=>
       (EVERY ((=) (b - 1) o flip $MOD b) ls)
Proof
  strip_tac
  \\ Induct
  \\ rw[l2n_def]
  \\ rw[EXP]
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`b * l + a`
  \\ Q.MATCH_GOALSUB_ABBREV_TAC`b ** n`
  \\ fs[EQ_IMP_THM]
  \\ conj_tac
  >- (
    strip_tac
    \\ Cases_on`n=0` \\ fs[] >- (fs[Abbr`n`] \\ rw[])
    \\ `0 < b * b ** n` by simp[]
    \\ `a + b * l + 1 = b * b ** n` by simp[]
    \\ `(b * b ** n) DIV b = b ** n` by simp[MULT_TO_DIV]
    \\ `(b * l + (a + 1)) DIV b = b ** n` by fs[]
    \\ `(b * l) MOD b = 0` by simp[]
    \\ `(b * l + (a + 1)) DIV b = (b * l) DIV b + (a + 1) DIV b`
    by ( irule ADD_DIV_RWT \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ `(a + 1) DIV b = if a = b - 1 then 1 else 0`
    by (
      rw[]
      \\ `a + 1 < b` suffices_by rw[DIV_EQ_0]
      \\ simp[Abbr`a`]
      \\ `h MOD b < b - 1` suffices_by simp[]
      \\ `h MOD b < b` by simp[]
      \\ fs[] )
    \\ `b * l DIV b = l` by simp[MULT_TO_DIV]
    \\ pop_assum SUBST_ALL_TAC
    \\ pop_assum SUBST_ALL_TAC
    \\ `l < b ** n` by ( map_every Q.UNABBREV_TAC[`l`,`n`]
                         \\ irule l2n_lt \\ simp[] )
    \\ Cases_on`a = b - 1` \\ fs[] )
  \\ strip_tac
  \\ rewrite_tac[LEFT_SUB_DISTRIB]
  \\ Q.PAT_X_ASSUM`_ = a`(SUBST1_TAC o SYM)
  \\ fs[SUB_LEFT_ADD] \\ rw[]
  \\ Cases_on`n=0` \\ fs[]
  \\ `b ** n <= b ** 0` by simp[]
  \\ fs[EXP_BASE_LE_IFF]
QED

Theorem l2n_PAD_RIGHT_0[simp]:
  0 < b ==> l2n b (PAD_RIGHT 0 h ls) = l2n b ls
Proof
  Induct_on`ls` \\ rw[l2n_def, PAD_RIGHT, l2n_eq_0, EVERY_GENLIST]
  \\ fs[PAD_RIGHT, l2n_APPEND]
  \\ fs[l2n_eq_0, EVERY_GENLIST]
QED

val _ = export_theory()
