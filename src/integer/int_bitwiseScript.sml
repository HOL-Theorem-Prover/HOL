open HolKernel Parse boolLib bossLib lcsymtacs;
open integerTheory arithmeticTheory bitTheory intLib listTheory;

infix \\
val op \\ = op THEN;

val _ = new_theory "int_bitwise";

val int_not_def = Define `
  int_not i = 0 - i - 1`;

val int_not_not = store_thm("int_not_not",
  ``!i. int_not (int_not i) = i``,
  srw_tac [] [int_not_def] \\ fs [] \\ intLib.COOPER_TAC);

val int_bit_def = Define `
  int_bit b (i:int) =
    if i < 0 then ~(BIT b (Num (int_not i))) else BIT b (Num i)`;

val int_bit_not = store_thm("int_bit_not",
  ``!b i. int_bit b (int_not i) = ~(int_bit b i)``,
  srw_tac [] [int_bit_def,int_not_not]
  \\ fs [int_not_def] \\ `F` by intLib.COOPER_TAC);

val bits_of_num_def = Define `
  bits_of_num (n:num) =
    if n = 0 then []
    else ODD n :: bits_of_num (n DIV 2)`;

val bits_of_int_def = Define `
  bits_of_int i =
    if i < 0 then
      (MAP (~) (bits_of_num (Num (int_not i))),T)
    else
      (bits_of_num (Num i), F)`;

val num_of_bits_def = Define `
  (num_of_bits [] = 0:num) /\
  (num_of_bits (F::bs) = 2 * num_of_bits bs) /\
  (num_of_bits (T::bs) = 1 + 2 * num_of_bits bs)`;

val int_of_bits_def = Define `
  int_of_bits (bs,rest) =
    if rest then
      int_not (& (num_of_bits (MAP (~) bs)))
    else & (num_of_bits bs)`;

val bits_bitwise_def = Define `
  (bits_bitwise f ([],r1) ([],r2) = ([],f r1 r2)) /\
  (bits_bitwise f ([],r1) (b2::bs2,r2) =
     let (bs,r) = bits_bitwise f ([],r1) (bs2,r2) in
       (f r1 b2 :: bs, r)) /\
  (bits_bitwise f (b1::bs1,r1) ([],r2) =
     let (bs,r) = bits_bitwise f (bs1,r1) ([],r2) in
       (f b1 r2 :: bs, r)) /\
  (bits_bitwise f (b1::bs1,r1) (b2::bs2,r2) =
     let (bs,r) = bits_bitwise f (bs1,r1) (bs2,r2) in
       (f b1 b2 :: bs, r))`

val int_bitwise_def = Define `
  int_bitwise f i j =
    int_of_bits (bits_bitwise f (bits_of_int i) (bits_of_int j))`;

val int_and_def = Define `
  int_and = int_bitwise (/\)`;

val int_or_def = Define `
  int_or = int_bitwise (\/)`;

val int_xor_def = Define `
  int_xor = int_bitwise (<>)`;

val MOD2 = prove(
  ``n MOD 2 = if ODD n then 1 else 0``,
  srw_tac [] [] \\ fs [ODD_EVEN,EVEN_MOD2]
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0<2:num``)))
  \\ decide_tac);

val num_of_bits_bits_of_num = prove(
  ``!n. num_of_bits (bits_of_num n) = n``,
  completeInduct_on `n`
  \\ ONCE_REWRITE_TAC [bits_of_num_def]
  \\ Cases_on `n = 0` \\ fs [num_of_bits_def]
  \\ Cases_on `ODD n` \\ fs [num_of_bits_def]
  \\ `n DIV 2 < n` by (fs [DIV_LT_X] \\ decide_tac)
  \\ res_tac \\ fs []
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0<2:num``)))
  \\ Q.PAT_ASSUM `n = kkk:num` (fn th => CONV_TAC
       (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ ASSUME_TAC MOD2
  \\ fs [AC MULT_COMM MULT_ASSOC, AC ADD_ASSOC ADD_COMM]);

val bits_bitwise_NIL = prove(
  ``!xs rest f. bits_bitwise f ([],F) (xs,rest) = (MAP (f F) xs,f F rest)``,
  Induct \\ fs [bits_bitwise_def,LET_DEF]);

val int_not = store_thm("int_not",
  ``int_not = int_bitwise (\x y. ~y) 0``,
  fs [int_bitwise_def,FUN_EQ_THM,EVAL ``bits_of_int 0``]
  \\ fs [bits_of_int_def] \\ srw_tac [] [bits_bitwise_NIL]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,int_of_bits_def,num_of_bits_bits_of_num]
  \\ fs [int_not_def] \\ intLib.COOPER_TAC);

val int_shift_left_def = Define `
  int_shift_left n i =
    let (bs,r) = bits_of_int i in
      int_of_bits (GENLIST (K F) n ++ bs,r)`;

val int_shift_right_def = Define `
  int_shift_right n i =
    let (bs,r) = bits_of_int i in
      int_of_bits (DROP n bs,r)`;

val int_not_lemma = prove(
  ``!n. int_not (& n) < 0``,
  fs [int_not_def] \\ intLib.COOPER_TAC);

val BIT_lemmas = prove(
  ``(BIT 0 (2 * k) = F) /\
    (BIT 0 (1 + 2 * k) = T) /\
    (BIT (SUC n) (2 * k) = BIT n k) /\
    (BIT (SUC n) (1 + 2 * k) = BIT n k)``,
  fs [GSYM BIT_DIV2]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ fs [DIV_MULT,MULT_DIV]
  \\ fs [BIT_def,BITS_THM]
  \\ fs [MOD_TIMES,MOD_EQ_0]);

val BIT_num_of_bits = prove(
  ``!bs n. BIT n (num_of_bits bs) = n < LENGTH bs /\ EL n bs``,
  Induct \\ srw_tac [] [num_of_bits_def,BIT_ZERO]
  \\ Cases_on `h` \\ srw_tac [] [num_of_bits_def]
  \\ Cases_on `n` \\ fs [BIT_lemmas]);

val int_bit_int_of_bits = store_thm("int_bit_int_of_bits",
  ``int_bit n (int_of_bits b) =
      if n < LENGTH (FST b) then EL n (FST b) else SND b``,
  Cases_on `b` \\ Cases_on `r` \\ fs [int_of_bits_def]
  \\ fs [int_bit_def,int_not_not]
  \\ fs [int_not_def,int_not_lemma,BIT_num_of_bits]
  \\ Cases_on `n < LENGTH q` \\ fs [EL_MAP]);

val int_of_bits_bits_of_int = store_thm("int_of_bits_bits_of_int",
  ``!i. int_of_bits (bits_of_int i) = i``,
  srw_tac [] [int_of_bits_def,bits_of_int_def]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,int_of_bits_def,num_of_bits_bits_of_num]
  \\ fs [int_not_def] \\ intLib.COOPER_TAC);

val int_bit_bitwise = store_thm("int_bit_bitwise",
  ``!n f i j. int_bit n (int_bitwise f i j) = f (int_bit n i) (int_bit n j)``,
  fs [int_bitwise_def,int_bit_int_of_bits] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM int_of_bits_bits_of_int]))
  \\ fs [int_bit_int_of_bits]
  \\ Q.SPEC_TAC (`n`,`n`)
  \\ Q.SPEC_TAC (`f`,`f`)
  \\ Q.SPEC_TAC (`bits_of_int j`,`ys`)
  \\ Q.SPEC_TAC (`bits_of_int i`,`xs`)
  \\ fs [pairTheory.FORALL_PROD]
  \\ Induct THEN1
   (fs [LENGTH] \\ Induct_on `p_1'` \\ fs [bits_bitwise_def]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `bits_bitwise f ([],p_2) (p_1',p_2')`
    \\ fs [LET_DEF] \\ Cases_on `n` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`p_2`,`p_2'`,`f`,`n'`])
    \\ fs [])
  \\ Cases_on `p_1'`
  \\ fs [bits_bitwise_def] \\ REPEAT STRIP_TAC THEN1
   (Cases_on `bits_bitwise f (p_1,p_2) ([],p_2')`
    \\ fs [LET_DEF] \\ Cases_on `n` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`p_2`,`[]`,`p_2'`,`f`,`n'`]) \\ fs [])
  THEN1
   (Cases_on `bits_bitwise f (p_1,p_2) (t,p_2')`
    \\ fs [LET_DEF] \\ Cases_on `n` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`p_2`,`t`,`p_2'`,`f`,`n'`]) \\ fs []));

val int_bit_and = save_thm("int_bit_and",
  ``int_bit n (int_and i j)``
  |> SIMP_CONV std_ss [int_and_def,int_bit_bitwise] |> Q.GENL [`j`,`i`,`n`]);

val int_bit_or = save_thm("int_bit_or",
  ``int_bit n (int_or i j)``
  |> SIMP_CONV std_ss [int_or_def,int_bit_bitwise] |> Q.GENL [`j`,`i`,`n`]);

val int_bit_xor = save_thm("int_bit_xor",
  ``int_bit n (int_xor i j)``
  |> SIMP_CONV std_ss [int_xor_def,int_bit_bitwise] |> Q.GENL [`j`,`i`,`n`]);

val LAST_bits_of_num = prove(
  ``!n. LENGTH (bits_of_num n) <> 0 ==>
        EL (LENGTH (bits_of_num n) - 1) (bits_of_num n)``,
  HO_MATCH_MP_TAC (fetch "-" "bits_of_num_ind")
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [bits_of_num_def]
  \\ Cases_on `n = 0` \\ fs [EVAL ``LENGTH (bits_of_num 0)``]
  \\ Cases_on `LENGTH (bits_of_num (n DIV 2))` \\ fs []
  \\ Cases_on `n = 1` \\ fs []
  \\ Q.PAT_ASSUM `kk = 0:num` MP_TAC
  \\ ONCE_REWRITE_TAC [bits_of_num_def]
  \\ `~(n < 2)` by decide_tac
  \\ fs [DIV_EQ_X]);

val int_not_lemma = prove(
  ``(int_not (& n) <> & m) /\ ((int_not i = int_not j) <=> (i = j))``,
  fs [int_not_def] \\ COOPER_TAC);

val int_of_bits_11_lemma = prove(
  ``(int_of_bits (bits_of_int i) = int_of_bits (bits_of_int j)) <=>
    (bits_of_int i = bits_of_int j)``,
  eq_tac \\ srw_tac [] [] \\ fs [bits_of_int_def]
  \\ srw_tac [] [] \\ fs [] \\ fs [int_of_bits_def,int_not_lemma]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,int_of_bits_def,num_of_bits_bits_of_num]);

val bits_of_int_LAST = prove(
  ``!i bs r. (bits_of_int i = (bs,r)) /\ (bs <> []) ==>
             EL (LENGTH bs - 1) bs <> r``,
  srw_tac [] [bits_of_int_def,EL_MAP,LENGTH_MAP]
  \\ fs [MAP_EQ_NIL] \\ fs [GSYM LENGTH_NIL]
  \\ imp_res_tac (DECIDE ``n <> 0 ==> n - 1 < n:num``)
  \\ fs [bits_of_int_def,EL_MAP,LENGTH_MAP]
  \\ match_mp_tac LAST_bits_of_num \\ fs []);

val int_bit_equiv = store_thm("int_bit_equiv",
  ``!i j. (i = j) <=> !n. int_bit n i = int_bit n j``,
  ONCE_REWRITE_TAC [GSYM int_of_bits_bits_of_int]
  \\ fs [int_bit_int_of_bits,int_of_bits_11_lemma]
  \\ srw_tac [] [] \\ Cases_on `bits_of_int i` \\ Cases_on `bits_of_int j`
  \\ fs [] \\ eq_tac \\ REVERSE (srw_tac [] [])
  \\ `r' = r` by (POP_ASSUM (MP_TAC o Q.SPEC `LENGTH (q:bool list) +
                                              LENGTH (q':bool list)`)
         \\ fs [DECIDE ``~(m+n<n) /\ ~(m+n<m:num)``])
  \\ srw_tac [] []
  \\ REVERSE (`LENGTH q' = LENGTH q` by ALL_TAC)
  THEN1 (fs [] \\ match_mp_tac LIST_EQ
         \\ fs [] \\ rpt strip_tac
         \\ first_x_assum (mp_tac o Q.SPEC `x`)
         \\ fs [])
  \\ CCONTR_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH bs2 <> LENGTH bs1` []
  \\ `LENGTH bs1 < LENGTH bs2 \/ LENGTH bs2 < LENGTH bs1` by DECIDE_TAC
  \\ IMP_RES_TAC bits_of_int_LAST
  THEN1 (Cases_on `bs2 = []` \\ fs [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `LENGTH (bs2:bool list) - 1`)
    \\ fs [] \\ srw_tac [] [] \\ `F` by intLib.COOPER_TAC)
  THEN1 (Cases_on `bs1 = []` \\ fs [LENGTH]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `LENGTH (bs1:bool list) - 1`)
    \\ fs [] \\ srw_tac [] [] \\ `F` by intLib.COOPER_TAC));

val int_bit_shift_left_lemma1 = prove(
  ``!b n i. int_bit (b + n) (int_shift_left n i) = int_bit b i``,
  fs [int_shift_left_def] \\ rpt strip_tac
  \\ Cases_on `bits_of_int i`
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM int_of_bits_bits_of_int]))
  \\ fs [LET_DEF,int_bit_int_of_bits]
  \\ srw_tac [] [LENGTH_GENLIST,rich_listTheory.EL_APPEND2]);

val int_bit_shift_left_lemma2 = prove(
  ``!b n i. b < n ==> ~int_bit b (int_shift_left n i)``,
  fs [int_shift_left_def] \\ rpt strip_tac
  \\ Cases_on `bits_of_int i`
  \\ fs [LET_DEF,int_bit_int_of_bits]
  \\ `b < n + LENGTH q` by decide_tac \\ fs []
  \\ qpat_assum `EL n xx` MP_TAC
  \\ fs [rich_listTheory.EL_APPEND1,LENGTH_GENLIST]);

val int_bit_shift_left = store_thm("int_bit_shift_left",
  ``!b n i. int_bit b (int_shift_left n i) = n <= b /\ int_bit (b - n) i``,
  REPEAT STRIP_TAC \\ Cases_on `b < n`
  \\ fs [int_bit_shift_left_lemma2] THEN1 decide_tac
  \\ fs [NOT_LESS] \\ imp_res_tac LESS_EQUAL_ADD
  \\ fs [] \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ fs [int_bit_shift_left_lemma1]);

val int_bit_shift_right = store_thm("int_bit_shift_right",
  ``!b n i. int_bit b (int_shift_right n i) = int_bit (b + n) i``,
  fs [int_shift_right_def] \\ rpt strip_tac
  \\ Cases_on `bits_of_int i`
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM int_of_bits_bits_of_int]))
  \\ fs [LET_DEF,int_bit_int_of_bits]
  \\ srw_tac [] [rich_listTheory.EL_DROP]
  \\ fs [NOT_LESS] \\ `F` by decide_tac);

val _ = export_theory();
