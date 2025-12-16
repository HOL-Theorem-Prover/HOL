Theory address
Ancestors
  words alignment bit arithmetic fcp pred_set prog
Libs
  wordsLib

val _ = ParseExtras.temp_loose_equality()


val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* definitions *)

Definition ALIGNED_def:   ALIGNED (x:word32) = (x && 3w = 0w)
End

Definition ADDR32_def:   ADDR32 (x:word30) = (w2w x << 2):word32
End
Definition ADDR30_def:   ADDR30 (x:word32) = ((31 >< 2) x):word30
End

Definition CONTAINER_def:   CONTAINER x = x:bool
End
Definition GUARD_def:   GUARD (n:num) x = x:bool
End
Definition DUMMY_EQ_def:   DUMMY_EQ x y = (x = y:'a)
End

Definition SING_SET_def:   SING_SET x = {x}
End


(* theorems *)

Theorem ALIGNED_eq_aligned:
  ALIGNED = aligned 2
Proof rw[ALIGNED_def,FUN_EQ_THM,aligned_bitwise_and]
QED

Theorem WORD_EQ_XOR_ZERO:
    !v w. (v ?? w = 0w) = (v = w:'a word)
Proof
  SIMP_TAC std_ss [fcpTheory.CART_EQ,word_xor_def,fcpTheory.FCP_BETA,word_0]
QED

Theorem ZERO_word30:
    1073741824w = 0w:word30
Proof
  SRW_TAC [WORD_ARITH_EQ_ss] []
QED

val lem = (GEN_ALL o SIMP_RULE std_ss [AND_IMP_INTRO] o
   Q.DISCH `dimindex (:'b) - 1 = h` o
   SIMP_RULE (arith_ss++WORD_EXTRACT_ss) [] o
   Q.DISCH `dimindex(:'b) < dimindex(:'a)` o SPEC_ALL) WORD_w2w_OVER_ADD;

Theorem lower_ADDR32_ADD:
    !w x. (1 >< 0) (ADDR32 x + w) = ((1 >< 0) w):word2
Proof
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss] [lem, ADDR32_def]
QED

Theorem ADDR32_eq_0:
    !x. (1 >< 0) (ADDR32 x) = 0w:word2
Proof
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss] [ADDR32_def]
QED

Theorem ADDR32_n2w:
    !n. (ADDR32 (n2w n)  = n2w (4 * n))
Proof
  SIMP_TAC (std_ss++WORD_MUL_LSL_ss) [GSYM word_mul_n2w, ADDR32_def]
    \\ SRW_TAC [WORD_BIT_EQ_ss] [n2w_def]
QED

Theorem n2w_and_1:
    !n. (n2w n) && 1w = n2w (n MOD 2):'a word
Proof
  SIMP_TAC std_ss [(SIMP_RULE std_ss [] o GSYM o Q.SPEC `0`) BITS_ZERO3]
    \\ SRW_TAC [WORD_BIT_EQ_ss, BIT_ss] [n2w_def]
    \\ Cases_on `i = 0`
    \\ SRW_TAC [ARITH_ss] [BIT_def, BITS_ZERO, BITS_COMP_THM2]
QED

Theorem n2w_and_3:
    !n. (n2w n) && 3w = n2w (n MOD 4):'a word
Proof
  SIMP_TAC std_ss [(SIMP_RULE std_ss [] o GSYM o Q.SPEC `1`) BITS_ZERO3]
    \\ SRW_TAC [WORD_BIT_EQ_ss, BIT_ss] [n2w_def]
    \\ Cases_on `i = 0` \\ Cases_on `i = 1`
    \\ SRW_TAC [ARITH_ss] [BIT_def, BITS_ZERO, BITS_COMP_THM2]
QED

Theorem n2w_and_7:
    !n. (n2w n) && 7w = n2w (n MOD 8):'a word
Proof
  SIMP_TAC std_ss [(SIMP_RULE std_ss [] o GSYM o Q.SPEC `2`) BITS_ZERO3]
    \\ SRW_TAC [WORD_BIT_EQ_ss, BIT_ss] [n2w_def]
    \\ Cases_on `i = 0` \\ Cases_on `i = 1` \\ Cases_on `i = 2`
    \\ SRW_TAC [ARITH_ss] [BIT_def, BITS_ZERO, BITS_COMP_THM2]
QED

Theorem ALIGNED_n2w:
    !n. ALIGNED (n2w n) = (n MOD 4 = 0)
Proof
  STRIP_TAC \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_and_3,ALIGNED_def,n2w_11]
  \\ `n MOD 4 < 4` by METIS_TAC [DIVISION,DECIDE ``0<4``]
  \\ `n MOD 4 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD]
QED

Theorem ALIGNED_MULT:
    !x y. ALIGNED x ==> ALIGNED (x + 4w * y)
Proof
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [word_add_n2w,word_mul_n2w,ALIGNED_def,n2w_and_3]
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [MOD_TIMES]
QED

Theorem ADDR32_and_3w:
    !x. (ADDR32 x) && 3w = 0w
Proof
  wordsLib.Cases_word \\ REWRITE_TAC [ADDR32_n2w,n2w_and_3]
  \\ SIMP_TAC std_ss [RW1 [MULT_COMM] MOD_EQ_0]
QED

Theorem ALIGNED_ADDR32:
    !x. ALIGNED (ADDR32 x)
Proof
  REWRITE_TAC [ALIGNED_def, ADDR32_and_3w]
QED

Theorem ADDR30_n2w:
    !n. ADDR30 (n2w n) = n2w (n DIV 4)
Proof
  SRW_TAC [SIZES_ss] [ADDR30_def, word_extract_n2w, BITS_THM]
QED

Theorem ADDR30_ADDR32_ADD:
    !x y. ADDR30 (ADDR32 x + y) = x + ADDR30 y
Proof
  wordsLib.Cases_word \\ wordsLib.Cases_word
  \\ REWRITE_TAC [ADDR30_n2w,ADDR32_n2w,word_add_n2w]
  \\ SIMP_TAC std_ss [ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]
QED

val ADDR30_ADDR32_LEMMA = prove(
  ``!a. (ADDR30 (ADDR32 a + 0w) = a) /\
        (ADDR30 (ADDR32 a + 1w) = a) /\
        (ADDR30 (ADDR32 a + 2w) = a) /\
        (ADDR30 (ADDR32 a + 3w) = a)``,
  SIMP_TAC std_ss [ADDR30_ADDR32_ADD,ADDR30_n2w,WORD_ADD_0]);

Theorem ADDR30_ADDR32:
    !x. (ADDR30 (ADDR32 x) = x) /\
        (ADDR30 (ADDR32 x + 0w) = x) /\
        (ADDR30 (ADDR32 x + 1w) = x) /\
        (ADDR30 (ADDR32 x + 2w) = x) /\
        (ADDR30 (ADDR32 x + 3w) = x)
Proof
  REWRITE_TAC
    [REWRITE_RULE [WORD_ADD_0] ADDR30_ADDR32_LEMMA,ADDR30_ADDR32_LEMMA]
QED

Theorem EXISTS_ADDR30:
    !x. (x && 3w = 0w) ==> ?y. x = ADDR32 y
Proof
  SRW_TAC [] [ADDR32_def] \\ Q.EXISTS_TAC `(31 >< 2) x`
    \\ SRW_TAC [WORD_EXTRACT_ss] []
    \\ FULL_SIMP_TAC (std_ss++WORD_BIT_EQ_ss++wordsLib.BIT_ss) [n2w_def]
QED

Theorem ADDR32_ADDR30:
    !x. (x && 3w = 0w) ==> (ADDR32 (ADDR30 x) = x)
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_ADDR30
    \\ ASM_REWRITE_TAC [ADDR30_ADDR32]
QED

Theorem ADDR32_ADD:
    !v w. (ADDR32 (v + w)  = ADDR32 v + ADDR32 w)
Proof
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [ADDR32_n2w,word_add_n2w,LEFT_ADD_DISTRIB]
QED

Theorem ADDR32_NEG:
    !w. ADDR32 (- w) = - (ADDR32 w)
Proof
  wordsLib.Cases_word \\ REWRITE_TAC [ADDR32_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_2comp_n2w]
  \\ `(4 * n) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_2comp_n2w,ADDR32_n2w,LEFT_SUB_DISTRIB]
QED

Theorem ADDR32_SUB:
    !v w. (ADDR32 (v - w)  = ADDR32 v - ADDR32 w)
Proof
  REWRITE_TAC [word_sub_def,ADDR32_ADD,ADDR32_NEG]
QED

Theorem ADDR32_SUC:
    !p. ADDR32 (p + 1w) = ADDR32 p + 4w
Proof
  SIMP_TAC std_ss [ADDR32_ADD,ADDR32_n2w]
QED

Theorem ADDR30_ADD:
    !x m. ADDR30 x + n2w m = ADDR30 (x + n2w (4 * m))
Proof
  Cases_word \\ REWRITE_TAC [ADDR30_n2w,word_add_n2w]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM ADD_DIV_ADD_DIV,AC MULT_COMM MULT_ASSOC]
QED

val ADD_LSL = save_thm("ADD_LSL", WORD_ADD_LSL);

Theorem ADDR32_11:
    !a b. ((ADDR32 a = ADDR32 b) = (a = b)) /\
          ((ADDR32 a = ADDR32 b + 0w) = (a = b)) /\
          ((ADDR32 a + 0w = ADDR32 b) = (a = b)) /\
          ((ADDR32 a + 0w = ADDR32 b + 0w) = (a = b)) /\
          ((ADDR32 a + 1w = ADDR32 b + 1w) = (a = b)) /\
          ((ADDR32 a + 2w = ADDR32 b + 2w) = (a = b)) /\
          ((ADDR32 a + 3w = ADDR32 b + 3w) = (a = b))
Proof
  SRW_TAC [] [WORD_EQ_ADD_RCANCEL,
    simpLib.SIMP_PROVE (std_ss++WORD_BIT_EQ_ss) [ADDR32_def]
      ``(ADDR32 a = ADDR32 b) = (a = b)``]
QED

Theorem ADDR32_EQ_0:
    !a. (ADDR32 a = 0w) = (a = 0w)
Proof
  REWRITE_TAC [SIMP_RULE std_ss [ADDR32_n2w] (Q.SPECL [`a`,`0w`] ADDR32_11)]
QED

val lem = Q.prove(
   `(!a. ADDR32 a && 1w = 0w) /\
    (!a. ADDR32 a && 2w = 0w) /\
    (!a. ADDR32 a && 3w = 0w)`,
  SRW_TAC [WORD_BIT_EQ_ss] [ADDR32_def]);

Theorem ADDR32_NEQ_ADDR32:
    !a b. ~(ADDR32 a + 0w = ADDR32 b + 1w) /\
          ~(ADDR32 a + 0w = ADDR32 b + 2w) /\
          ~(ADDR32 a + 0w = ADDR32 b + 3w) /\
          ~(ADDR32 a + 1w = ADDR32 b + 2w) /\
          ~(ADDR32 a + 1w = ADDR32 b + 3w) /\
          ~(ADDR32 a + 2w = ADDR32 b + 3w) /\
          ~(ADDR32 a + 1w = ADDR32 b + 0w) /\
          ~(ADDR32 a + 2w = ADDR32 b + 0w) /\
          ~(ADDR32 a + 3w = ADDR32 b + 0w) /\
          ~(ADDR32 a + 2w = ADDR32 b + 1w) /\
          ~(ADDR32 a + 3w = ADDR32 b + 1w) /\
          ~(ADDR32 a + 3w = ADDR32 b + 2w) /\
          ~(ADDR32 a + 1w = ADDR32 b) /\
          ~(ADDR32 a + 2w = ADDR32 b) /\
          ~(ADDR32 a + 3w = ADDR32 b) /\
          ~(ADDR32 a = ADDR32 b + 1w) /\
          ~(ADDR32 a = ADDR32 b + 2w) /\
          ~(ADDR32 a = ADDR32 b + 3w)
Proof
  SRW_TAC [] [lem, WORD_ADD_OR] \\ SRW_TAC [WORD_BIT_EQ_ss] [ADDR32_def]
QED

Theorem EXISTS_ADDR32:
    !p. ?a. (p = ADDR32 a + 0w) \/ (p = ADDR32 a + 1w) \/
            (p = ADDR32 a + 2w) \/ (p = ADDR32 a + 3w)
Proof
  STRIP_TAC \\ Q.EXISTS_TAC `(31 >< 2) p`
    \\ SRW_TAC [] [lem, WORD_ADD_OR]
    \\ SRW_TAC [WORD_BIT_EQ_ss] [ADDR32_def]
    \\ DECIDE_TAC
QED

Theorem ADDR32_ABSORB_CONST:
    (ADDR32 x + 0w  = ADDR32 x) /\
    (ADDR32 x + 4w  = ADDR32 (x + 1w)) /\
    (ADDR32 x + 8w  = ADDR32 (x + 2w)) /\
    (ADDR32 x + 12w = ADDR32 (x + 3w)) /\
    (ADDR32 x + 16w = ADDR32 (x + 4w)) /\
    (ADDR32 x + 20w = ADDR32 (x + 5w)) /\
    (ADDR32 x + 24w = ADDR32 (x + 6w)) /\
    (ADDR32 x + 28w = ADDR32 (x + 7w)) /\
    (ADDR32 x + 32w = ADDR32 (x + 8w)) /\
    (ADDR32 x + 36w = ADDR32 (x + 9w)) /\
    (ADDR32 x + 40w = ADDR32 (x + 10w)) /\
    (ADDR32 x - 0w  = ADDR32 (x - 0w)) /\
    (ADDR32 x - 4w  = ADDR32 (x - 1w)) /\
    (ADDR32 x - 8w  = ADDR32 (x - 2w)) /\
    (ADDR32 x - 12w = ADDR32 (x - 3w)) /\
    (ADDR32 x - 16w = ADDR32 (x - 4w)) /\
    (ADDR32 x - 20w = ADDR32 (x - 5w)) /\
    (ADDR32 x - 24w = ADDR32 (x - 6w)) /\
    (ADDR32 x - 28w = ADDR32 (x - 7w)) /\
    (ADDR32 x - 32w = ADDR32 (x - 8w)) /\
    (ADDR32 x - 36w = ADDR32 (x - 9w)) /\
    (ADDR32 x - 40w = ADDR32 (x - 10w))
Proof
  SIMP_TAC std_ss [ADDR32_ADD,ADDR32_SUB,ADDR32_n2w,WORD_ADD_0]
QED

Theorem ADDRESS_ROTATE:
    !q:word32 z:word30. q #>> (8 * w2n ((1 >< 0) (ADDR32 z):word2)) = q
Proof
  SIMP_TAC std_ss [ADDR32_eq_0,word_0_n2w] \\ STRIP_TAC \\ EVAL_TAC
QED

Theorem ADDR30_THM:
    !x. ADDR30 x = n2w (w2n x DIV 4)
Proof
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,ADDR30_n2w]
QED

Theorem ADDR32_THM:
    !x. ADDR32 x = n2w (4 * w2n x)
Proof
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,ADDR32_n2w]
QED

Theorem ALIGNED_THM:
    !p. ALIGNED p = ?k. p = k * 4w
Proof
  SRW_TAC [] [ALIGNED_def] \\ EQ_TAC \\ SRW_TAC [WORD_MUL_LSL_ss] []
  THENL [Q.EXISTS_TAC `(31 >< 2) p`, ALL_TAC]
  \\ FULL_SIMP_TAC (std_ss++WORD_BIT_EQ_ss++wordsLib.BIT_ss) [n2w_def]
QED

val ALIGNED_NEG_lemma = prove(
  ``!x. ALIGNED x ==> ALIGNED (- x)``,
  ASM_SIMP_TAC std_ss  [ALIGNED_THM,w2n_n2w,LESS_MOD]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n2w (2**30) - k`
  \\ ASM_SIMP_TAC (std_ss++WORD_ARITH_EQ_ss) [WORD_RIGHT_SUB_DISTRIB]
  \\ ASM_SIMP_TAC (std_ss++WORD_ss) []);

Theorem ALIGNED_NEG:
    !x. ALIGNED (- x) = ALIGNED x
Proof
  METIS_TAC [ALIGNED_NEG_lemma,WORD_NEG_NEG]
QED

Theorem ALIGNED_and_1:
    !x. ALIGNED x ==> (x && 1w = 0w)
Proof
  REWRITE_TAC [ALIGNED_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_EQ_0]
QED

Theorem ALIGNED_add_1_and_1:
    !x. ALIGNED x ==> ~(x + 1w && 1w = 0w)
Proof
  REWRITE_TAC [ALIGNED_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES]
QED

val tac =
  REWRITE_TAC [ALIGNED_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_3,n2w_11]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES];

Theorem ALIGNED_add_1_and_3:
    !x. ALIGNED x ==> (x + 1w && 3w = 1w)
Prooftac
QED
Theorem ALIGNED_add_2_and_3:
    !x. ALIGNED x ==> (x + 2w && 3w = 2w)
Prooftac
QED
Theorem ALIGNED_add_3_and_3:
    !x. ALIGNED x ==> (x + 3w && 3w = 3w)
Prooftac
QED

Theorem ALIGNED_ADD:
    !x y. ALIGNED x /\ ALIGNED y ==> ALIGNED (x + y)
Proof
  REWRITE_TAC [ALIGNED_THM] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [GSYM WORD_RIGHT_ADD_DISTRIB] \\ METIS_TAC []
QED

Theorem ALIGNED_SUB:
    !x y. ALIGNED x /\ ALIGNED y ==> ALIGNED (x - y)
Proof
  SIMP_TAC std_ss [word_sub_def] \\ METIS_TAC [ALIGNED_ADD,ALIGNED_NEG]
QED


Theorem word_arith_lemma1:
    !n m. (n2w n + n2w m = n2w (n + m):'a word) /\
          (x + n2w n + n2w m = x + n2w (n + m):'a word) /\
          (x - n2w n - n2w m = x - n2w (n + m):'a word)
Proof
  REWRITE_TAC [GSYM WORD_SUB_PLUS,word_add_n2w,GSYM WORD_ADD_ASSOC]
QED

Theorem word_arith_lemma2:
    !n m. n2w n - (n2w m) :'a word =
      if n < m then (- (n2w (m-n))) else n2w (n-m)
Proof
  REPEAT STRIP_TAC \\ Cases_on `n < m` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS,LESS_EQ]
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,ADD1,DECIDE ``n+1+p-n = 1+p:num``]
  \\ REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_REFL]
  \\ REWRITE_TAC [GSYM WORD_SUB_PLUS]
  \\ REWRITE_TAC [word_sub_def,WORD_ADD_0,DECIDE ``m+p-m=p:num``]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_ADD]
QED

Theorem word_arith_lemma3:
    !x n m. x - n2w m + n2w n :'a word = if n < m then x - (n2w (m-n)) else x + n2w (n-m)
Proof
  REWRITE_TAC [word_sub_def,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM (RW1 [WORD_ADD_COMM] word_sub_def),word_arith_lemma2]
  \\ REPEAT STRIP_TAC \\ Cases_on `n<m` \\ ASM_REWRITE_TAC []
QED

Theorem word_arith_lemma4:
    !x n m. x + n2w n - n2w m :'a word = if n < m then x - (n2w (m-n)) else x + n2w (n-m)
Proof
  REWRITE_TAC [word_sub_def,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM word_sub_def,word_arith_lemma2]
  \\ REPEAT STRIP_TAC \\ Cases_on `n<m` \\ ASM_REWRITE_TAC [word_sub_def]
QED

Theorem word_arith_lemma5:
    !x y m n. (x + n2w n = y + n2w m) =
              if n < m then (x = y + n2w m - n2w n) else (x + n2w n - n2w m = y)
Proof
  ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO]
  \\ SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_SUB_SUB]
  \\ METIS_TAC [WORD_SUB_PLUS,WORD_ADD_COMM]
QED

val ADDR32_ADD_EQ_ZERO_LEMMA = prove(
  ``!x m. 0 < m /\ w2n x + m < dimword (:'a) ==> ~((x:'a word) + n2w m = 0w)``,
  Cases_word
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,word_add_n2w,n2w_11,ZERO_LT_dimword]
  \\ DECIDE_TAC);

Theorem ADDR32_ADD_EQ_ZERO:
    !x. ~(ADDR32 x + 1w = 0w) /\ ~(ADDR32 x + 2w = 0w) /\ ~(ADDR32 x + 3w = 0w)
Proof
  Cases_word \\ REWRITE_TAC [ADDR32_n2w] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ REWRITE_TAC [] \\ MATCH_MP_TAC ADDR32_ADD_EQ_ZERO_LEMMA
  \\ `4 * n < 4 * dimword (:30)` by DECIDE_TAC
  \\ FULL_SIMP_TAC (bool_ss++SIZES_ss) [w2n_n2w,LESS_MOD,EVAL ``4 * 1073741824``]
  \\ DECIDE_TAC
QED

Theorem word_add_and_3w:
    !w. (w + n2w n) && 3w = (w + n2w (n MOD 4)) && 3w
Proof
  Cases_word \\ SIMP_TAC std_ss [n2w_and_3,word_add_n2w]
  \\ `n = n DIV 4 * 4 + n MOD 4` by METIS_TAC [DIVISION,EVAL ``0<4``]
  \\ ONCE_ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [DECIDE ``m + (k + l) = k + (m + l:num)``]
  \\ SIMP_TAC std_ss [MOD_TIMES]
QED

Theorem ALIGNED_CLAUSES:
    !x a. (ALIGNED (a + 4w * x) = ALIGNED a) /\ (ALIGNED (4w * x + a) = ALIGNED a) /\
          (ALIGNED (a + x * 4w) = ALIGNED a) /\ (ALIGNED (x * 4w + a) = ALIGNED a) /\
          (ALIGNED (a + 4w) = ALIGNED a) /\ (ALIGNED (4w + a) = ALIGNED a)
Proof
  Cases_word \\ SIMP_TAC std_ss [ALIGNED_def,word_mul_n2w]
  \\ ONCE_REWRITE_TAC [word_add_and_3w] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ONCE_REWRITE_TAC [word_add_and_3w]
  \\ SIMP_TAC std_ss [MOD_EQ_0,RW1 [MULT_COMM] MOD_EQ_0,WORD_ADD_0]
QED

Theorem NOT_ALIGNED:
    !a. ALIGNED a ==> ~(ALIGNED (a + 1w)) /\  ~(ALIGNED (a + 2w)) /\ ~(ALIGNED (a + 3w))
Proof
  Cases_word \\ SIMP_TAC std_ss [ALIGNED_n2w,word_add_n2w]
  \\ ONCE_REWRITE_TAC [(GSYM MOD_PLUS)]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [ADD] \\ EVAL_TAC
QED

Theorem word32_add_n2w:
    !x n. x + (n2w n):word32 =
          if n < 2**31 then x + n2w n else x - n2w (2**32 - n MOD 2**32)
Proof
  Cases_word \\ STRIP_TAC
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_sub_def,word_2comp_n2w]
  \\ Cases_on `n' < 2147483648` \\ ASM_REWRITE_TAC []
  \\ `n' MOD 4294967296 < 4294967296` by METIS_TAC [arithmeticTheory.DIVISION,EVAL ``0 < 4294967296``]
  \\ Cases_on `n' MOD 4294967296 = 0` THENL [
    ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [],
    `(4294967296 - n' MOD 4294967296) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ `4294967296 - (4294967296 - n' MOD 4294967296) = n' MOD 4294967296` by DECIDE_TAC
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []]
QED

val two64 = (snd o dest_eq o concl o EVAL) ``(2**64):num``
val two63 = (snd o dest_eq o concl o EVAL) ``(2**63):num``
Theorem word64_add_n2w:
    !x n. x + (n2w n):word64 =
          if n < 2**63 then x + n2w n else x - n2w (2**64 - n MOD 2**64)
Proof
  Cases_word \\ STRIP_TAC
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_sub_def,word_2comp_n2w]
  \\ Cases_on `n' < ^two63` \\ ASM_REWRITE_TAC []
  \\ `n' MOD ^two64 < ^two64` by METIS_TAC [arithmeticTheory.DIVISION,EVAL ``0 < ^two64``]
  \\ Cases_on `n' MOD ^two64 = 0` THENL [
    ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [],
    `(^two64 - n' MOD ^two64) < ^two64` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ `^two64 - (^two64 - n' MOD ^two64) = n' MOD ^two64` by DECIDE_TAC
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []]
QED

val MOD_EQ_0_IMP = prove(
  ``!n m. 0 < m ==> ((n MOD m = 0) = ?k. n = k * m)``,
  METIS_TAC [DIVISION,ADD_0,MOD_EQ_0]);

Theorem ALIGNED_BITS:
    !x. ALIGNED x = ~(x ' 0) /\ ~(x ' 1)
Proof
  Cases_word \\ ONCE_REWRITE_TAC [word_index_n2w]
  \\ Cases_on `n MOD 4 = 0` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ALIGNED_n2w,bitTheory.BIT_def] THENL [
    ASM_SIMP_TAC std_ss [bitTheory.BITS_THM2]
    \\ `0 < 4` by EVAL_TAC
    \\ IMP_RES_TAC MOD_EQ_0_IMP
    \\ ASM_SIMP_TAC std_ss []
    \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
    \\ SIMP_TAC std_ss [MOD_EQ_0],
    ASM_SIMP_TAC std_ss [bitTheory.BITS_THM,GSYM bitTheory.NOT_MOD2_LEM]
    \\ Cases_on `n MOD 2 = 0` \\ ASM_SIMP_TAC std_ss []
    \\ `0 < 2` by EVAL_TAC \\ `?k. n = k * 2` by METIS_TAC [MOD_EQ_0_IMP]
    \\ FULL_SIMP_TAC std_ss [MOD_EQ_0_IMP,MULT_DIV]
    \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``2*2``),MULT_ASSOC]
    \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``SUC 1``),MULT_SUC_EQ]]
QED

Theorem ALIGNED_OR:
    !x y. ALIGNED (x || y) = ALIGNED x /\ ALIGNED y
Proof
  SIMP_TAC (std_ss++SIZES_ss) [ALIGNED_BITS,word_or_def,fcpTheory.FCP_BETA]
  \\ METIS_TAC []
QED

Theorem ADDR32_LESS_EQ:
    !x y. ADDR32 x <=+ ADDR32 y = x <=+ y
Proof
  Cases_word \\ Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ADDR32_n2w,WORD_LS,w2n_n2w]
  \\ `4 * n' < 4294967296 /\ 4 * n < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ADDR32_n2w,WORD_LS,w2n_n2w]
QED

Theorem ADDR32_LESS:
    !x y. ADDR32 x <+ ADDR32 y = x <+ y
Proof
  Cases_word \\ Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ADDR32_n2w,WORD_LO,w2n_n2w]
  \\ `4 * n' < 4294967296 /\ 4 * n < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ADDR32_n2w,WORD_LS,w2n_n2w]
QED

Theorem ALIGNED_LESS_ADD:
    !x. ALIGNED x /\ ~(x + 4w = 0w) ==> x <+ x + 4w
Proof
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (RW [GSYM ALIGNED_def] EXISTS_ADDR30)
  \\ FULL_SIMP_TAC std_ss [GSYM ADDR32_SUC,
       ADDR32_LESS,GSYM (EVAL ``ADDR32 0w``),ADDR32_11]
  \\ Q.PAT_X_ASSUM `~(y + 1w = 0w)` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`y`,`y`) \\ Cases_word
  \\ ASM_SIMP_TAC std_ss [word_add_n2w,n2w_11,ZERO_LT_dimword,WORD_LO,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [MOD_EQ_0_IMP]
  \\ REPEAT STRIP_TAC
  \\ `~(n + 1 = 1 * 1073741824)` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss []
  \\ `n + 1 < 1073741824` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC
QED

Theorem CONTAINER_IF_T:
    !x y z. CONTAINER x ==> ((if x then y else z) = y:'a)
Proof
  SIMP_TAC std_ss [CONTAINER_def]
QED

Theorem CONTAINER_IF_F:
    !x y z. CONTAINER ~x ==> ((if x then y else z) = z:'a)
Proof
  SIMP_TAC std_ss [CONTAINER_def]
QED

val ALIGNED_ADD_EQ_LEMMA = prove(
  ``!x y. ALIGNED x ==> (ALIGNED (x + y) = ALIGNED y)``,
  Cases_word \\ Cases_word
  \\ SIMP_TAC std_ss [word_add_n2w,ALIGNED_n2w]
  \\ ONCE_REWRITE_TAC [(GSYM MOD_PLUS)]
  \\ ASM_SIMP_TAC bool_ss [ADD] \\ SIMP_TAC std_ss [MOD_MOD]);

Theorem ALIGNED_ADD_EQ:
    !x y. ALIGNED x ==> (ALIGNED (x + y) = ALIGNED y) /\
                        (ALIGNED (x - y) = ALIGNED y) /\
                        (ALIGNED (y + x) = ALIGNED y) /\
                        (ALIGNED (y - x) = ALIGNED y)
Proof
  REWRITE_TAC [word_sub_def]
  \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ_LEMMA,ALIGNED_NEG]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ_LEMMA,ALIGNED_NEG]
QED

Theorem ALIGNED_MOD_4:
    !a n. (ALIGNED (a + n2w n) = ALIGNED (a + n2w (n MOD 4))) /\
          (ALIGNED (a - n2w n) = ALIGNED (a - n2w (n MOD 4)))
Proof
  NTAC 2 STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DA (DECIDE ``0 < 4``)))
  \\ ASM_SIMP_TAC std_ss [MOD_MULT]
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_PLUS,GSYM word_mul_n2w,
       WORD_ADD_ASSOC,ALIGNED_CLAUSES]
  \\ REWRITE_TAC [word_sub_def]
  \\ ONCE_REWRITE_TAC [RW1[WORD_MULT_COMM]WORD_NEG_MUL]
  \\ REWRITE_TAC [GSYM WORD_MULT_ASSOC,ALIGNED_CLAUSES]
QED

Theorem ALIGNED_0:
    !a. (ALIGNED (a + 0w) = ALIGNED a) /\ (ALIGNED (a - 0w) = ALIGNED a)
Proof
  SIMP_TAC std_ss [WORD_ADD_0,WORD_SUB_RZERO]
QED

Theorem ALIGNED_SUB_4:
    !a. ALIGNED (a - 4w) = ALIGNED a
Proof
  ONCE_REWRITE_TAC [ALIGNED_MOD_4] \\ SIMP_TAC std_ss [WORD_SUB_RZERO]
QED

Theorem ALIGNED_INTRO:
    !a. ((a && 3w = 0w) = ALIGNED a) /\ ((3w && a = 0w) = ALIGNED a) /\
        ((0w = a && 3w) = ALIGNED a) /\ ((0w = 3w && a) = ALIGNED a) /\
        ((w2n a MOD 4 = 0) = ALIGNED a) /\ ((0 = w2n a MOD 4) = ALIGNED a)
Proof
  Cases_word \\ ASM_SIMP_TAC std_ss [w2n_n2w,GSYM ALIGNED_n2w]
  \\ REWRITE_TAC [ALIGNED_def] \\ METIS_TAC [WORD_AND_COMM]
QED

val BIT_LEMMA = prove(
  ``!x. (NUMERAL (BIT2 (BIT1 x)) = 4 * (x + 1)) /\
        (NUMERAL (BIT2 (BIT2 x)) = 4 * (x + 1) + 2) /\
        (NUMERAL (BIT1 (BIT2 x)) = 4 * (x + 1) + 1) /\
        (NUMERAL (BIT1 (BIT1 x)) = 4 * x + 3)``,
  REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [NUMERAL_DEF]))
  \\ NTAC 2 (CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [BIT1,BIT2])))
  \\ DECIDE_TAC);

val ALIGNED_SUB_CLAUSES = prove(
  ``ALIGNED (a - 4w * x) = ALIGNED a``,
  ONCE_REWRITE_TAC [GSYM ALIGNED_NEG]
  \\ SIMP_TAC std_ss [WORD_NEG_SUB, word_sub_def, ALIGNED_CLAUSES]);

Theorem ALIGNED:
    !a x.
      (ALIGNED 0w = T) /\
      (ALIGNED (n2w (NUMERAL (BIT2 (BIT1 x)))) = T) /\
      (ALIGNED (n2w (NUMERAL (BIT1 (BIT2 x)))) = F) /\
      (ALIGNED (n2w (NUMERAL (BIT2 (BIT2 x)))) = F) /\
      (ALIGNED (n2w (NUMERAL (BIT1 (BIT1 (BIT1 x))))) = F) /\
      (ALIGNED (n2w (NUMERAL (BIT1 (BIT1 (BIT2 x))))) = F) /\
      (ALIGNED (a + 0w) = ALIGNED a) /\
      (ALIGNED (a + n2w (NUMERAL (BIT2 (BIT1 x)))) = ALIGNED a) /\
      (ALIGNED (a + n2w (NUMERAL (BIT1 (BIT2 x)))) = ALIGNED (a + 1w)) /\
      (ALIGNED (a + n2w (NUMERAL (BIT2 (BIT2 x)))) = ALIGNED (a + 2w)) /\
      (ALIGNED (a + n2w (NUMERAL (BIT1 (BIT1 (BIT1 x))))) = ALIGNED (a + 3w)) /\
      (ALIGNED (a + n2w (NUMERAL (BIT1 (BIT1 (BIT2 x))))) = ALIGNED (a + 3w)) /\
      (ALIGNED (a - 0w) = ALIGNED a) /\
      (ALIGNED (a - n2w (NUMERAL (BIT2 (BIT1 x)))) = ALIGNED a) /\
      (ALIGNED (a - n2w (NUMERAL (BIT1 (BIT2 x)))) = ALIGNED (a - 1w)) /\
      (ALIGNED (a - n2w (NUMERAL (BIT2 (BIT2 x)))) = ALIGNED (a - 2w)) /\
      (ALIGNED (a - n2w (NUMERAL (BIT1 (BIT1 (BIT1 x))))) = ALIGNED (a - 3w)) /\
      (ALIGNED (a - n2w (NUMERAL (BIT1 (BIT1 (BIT2 x))))) = ALIGNED (a - 3w))
Proof
  PURE_ONCE_REWRITE_TAC [BIT_LEMMA] \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_SUB_PLUS,
        ALIGNED_CLAUSES,ALIGNED_SUB_CLAUSES,GSYM word_mul_n2w,ALIGNED_0]
  \\ SIMP_TAC std_ss [ALIGNED_n2w,
       RW [WORD_ADD_0] (Q.SPECL [`x`,`0w`] ALIGNED_CLAUSES)]
QED

val WORD_CMP_NORMALISE = save_thm("WORD_CMP_NORMALISE",let
  val rw = METIS_PROVE [] ``!x:'a y z:'b q. ~(x = y) /\ ~(z = q) = ~(x = y) /\ ~(q = z)``
  val nzcv_thm = RW1 [rw] nzcv_def
  val rw = [nzcv_thm,LET_DEF,GSYM word_add_n2w,n2w_w2n,GSYM word_sub_def,WORD_EQ_SUB_ZERO]
  val th = SIMP_RULE std_ss (WORD_GREATER_EQ::rw) word_ge_def
  val th = prove(
  ``((word_msb (a - b) = ~(word_msb a = word_msb b) /\ ~(word_msb a = word_msb (a - b))) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb b = word_msb a) /\ ~(word_msb a = word_msb (a - b))) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb a = word_msb b) /\ ~(word_msb (a - b) = word_msb a)) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb b = word_msb a) /\ ~(word_msb (a - b) = word_msb a)) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb a = word_msb (a - b)) /\ ~(word_msb a = word_msb b)) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb a = word_msb (a - b)) /\ ~(word_msb b = word_msb a)) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb (a - b) = word_msb a) /\ ~(word_msb a = word_msb b)) = b <= a) /\
    ((word_msb (a - b) = ~(word_msb (a - b) = word_msb a) /\ ~(word_msb b = word_msb a)) = b <= a) /\
    ((~(word_msb a = word_msb b) /\ ~(word_msb a = word_msb (a - b)) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb b = word_msb a) /\ ~(word_msb a = word_msb (a - b)) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb a = word_msb b) /\ ~(word_msb (a - b) = word_msb a) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb b = word_msb a) /\ ~(word_msb (a - b) = word_msb a) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb a = word_msb (a - b)) /\ ~(word_msb a = word_msb b) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb a = word_msb (a - b)) /\ ~(word_msb b = word_msb a) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb (a - b) = word_msb a) /\ ~(word_msb a = word_msb b) = word_msb (a - b)) = b <= a) /\
    ((~(word_msb (a - b) = word_msb a) /\ ~(word_msb b = word_msb a) = word_msb (a - b)) = b <= a:('a word))``,
  REWRITE_TAC [th] THEN METIS_TAC [])
  val lemma1 = prove(``!a:'a word b. (b <=+ a) /\ ~(a = b) = b <+ a``,
    REWRITE_TAC [WORD_LOWER_OR_EQ] THEN METIS_TAC [WORD_LOWER_NOT_EQ])
  val lemma2 = prove(``!a:'a word b. ~(a = b) /\ (b <=+ a) = b <+ a``,
    REWRITE_TAC [WORD_LOWER_OR_EQ] THEN METIS_TAC [WORD_LOWER_NOT_EQ])
  val lemma3 = prove(``!a:'a word b. (b <= a) /\ ~(a = b) = b < a``,
    REWRITE_TAC [WORD_LESS_OR_EQ] THEN METIS_TAC [WORD_LESS_NOT_EQ])
  val lemma4 = prove(``!a:'a word b. ~(a = b) /\ (b <= a) = b < a``,
    REWRITE_TAC [WORD_LESS_OR_EQ] THEN METIS_TAC [WORD_LESS_NOT_EQ])
  val ys = [WORD_GREATER_EQ,WORD_GREATER,WORD_NOT_LOWER_EQUAL]
  val zs = [WORD_NOT_LOWER,GSYM WORD_LOWER_OR_EQ,WORD_NOT_LESS,WORD_NOT_LESS_EQUAL]
  val qs1 = [GSYM WORD_LESS_OR_EQ, GSYM (RW1 [DISJ_COMM] WORD_LESS_OR_EQ)]
  val qs2 = [GSYM WORD_LOWER_OR_EQ, GSYM (RW1 [DISJ_COMM] WORD_LOWER_OR_EQ)]
  val ls = [lemma1,lemma2,lemma3,lemma4,WORD_EQ_SUB_ZERO,WORD_SUB_RZERO]
  in Q.GEN `a` (Q.GEN `b` (LIST_CONJ (map SPEC_ALL ([th] @ ys @ zs @ qs1 @ qs2 @ ls)))) end)

Theorem word_LSL_n2w:
    !m k. ((n2w m):'a word) << k = n2w (m * 2 ** k)
Proof
  SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,WORD_MUL_LSL,word_mul_n2w]
QED

Theorem WORD_EQ_ADD_CANCEL:
    !v w x. ((v + w = x + w) = (v = x)) /\ ((w + v = x + w) = (v = x)) /\
            ((v + w = w + x) = (v = x)) /\ ((w + v = w + x) = (v = x)) /\
            ((w = x + w) = (x = 0w)) /\ ((v + w = w) = (v = 0w)) /\
            ((w = w + x) = (x = 0w)) /\ ((w + v = w) = (v = 0w: 'a word))
Proof
  METIS_TAC [WORD_ADD_0,WORD_ADD_COMM,WORD_EQ_ADD_LCANCEL]
QED

Theorem NOT_IF:
    !b x y:'a. (if ~b then x else y) = if b then y else x
Proof
  Cases THEN REWRITE_TAC []
QED

Theorem IF_IF:
    !b c x y:'a.
      ((if b then (if c then x else y) else y) = if b /\  c then x else y) /\
      ((if b then (if c then y else x) else y) = if b /\ ~c then x else y) /\
      ((if b then x else (if c then x else y)) = if b \/  c then x else y) /\
      ((if b then x else (if c then y else x)) = if b \/ ~c then x else y)
Proof
  Cases THEN Cases THEN REWRITE_TAC []
QED

Theorem SING_SET_INTRO:
    !x:'a s. x INSERT s = SING_SET x UNION s
Proof
  REWRITE_TAC [INSERT_UNION_EQ,UNION_EMPTY,SING_SET_def]
QED

Theorem UNION_CANCEL:
    !x s:'a set. x UNION (x UNION s) = x UNION s
Proof
  REWRITE_TAC [UNION_ASSOC,UNION_IDEMPOT]
QED

Theorem FLATTEN_IF:
    !b x y. (if b then x else y) = (b /\ x) \/ (~b /\ y)
Proof
  Cases THEN REWRITE_TAC []
QED

Theorem PUSH_IF_LEMMA:
    !b g x y. (b /\ (if g then x else y) = if g then b /\ x else b /\ y) /\
              ((if g then x else y) /\ b = if g then b /\ x else b /\ y)
Proof
  REPEAT Cases THEN REWRITE_TAC []
QED

Theorem GUARD_EQ_ZERO:
    !n b. GUARD n b = GUARD 0 b
Proof
  REWRITE_TAC [GUARD_def]
QED

Theorem extract_byte:
    !w. (7 >< 0) w = (w2w:word32->word8) w
Proof
  Cases_word
  \\ SIMP_TAC (std_ss++SIZES_ss) [wordsTheory.word_extract_n2w,
       wordsTheory.w2w_def,bitTheory.BITS_THM,
       wordsTheory.w2n_n2w,wordsTheory.n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``256 * 16777216``)]
  \\ SIMP_TAC bool_ss [arithmeticTheory.MOD_MULT_MOD,EVAL ``0 < 256``,
       EVAL ``0 < 16777216``]
QED

Theorem WORD_TIMES2:
    !w:'a word. 2w * w = w + w
Proof
  Cases_word
  THEN REWRITE_TAC [word_add_n2w,word_mul_n2w,arithmeticTheory.TIMES2]
QED

Theorem WORD_SUB_INTRO:
    !x y:'a word.
     ((- y) + x = x - y) /\
     (x + (- y) = x - y) /\
     ((-1w) * y + x = x - y) /\
     (y * (-1w) + x = x - y) /\
     (x + (-1w) * y = x - y) /\
     (x + y * (-1w) = x - y)
Proof
  SIMP_TAC (std_ss++wordsLib.WORD_ss) []
QED

val WORD_ADD_LEMMA = prove(
  ``!(x:'a word) n. x + n2w n * x = n2w (n + 1) * x``,
  Cases_word
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,RIGHT_ADD_DISTRIB,MULT_CLAUSES]
  \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]);

Theorem WORD_ADD_FOLD:
    !(x:'a word) n p.
      (x + n2w n * x = n2w (n + 1) * x) /\
      (x + x * n2w n = n2w (n + 1) * x) /\
      (n2w n * x + x = n2w (n + 1) * x) /\
      (n2w n * x + x = n2w (n + 1) * x) /\
      (p + x + n2w n * x = p + n2w (n + 1) * x) /\
      (p + x + x * n2w n = p + n2w (n + 1) * x) /\
      (p + n2w n * x + x = p + n2w (n + 1) * x) /\
      (p + n2w n * x + x = p + n2w (n + 1) * x)
Proof
  REWRITE_TAC [GSYM WORD_ADD_LEMMA]
  \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,
                      AC WORD_MULT_ASSOC WORD_MULT_COMM]
QED

Theorem EXISTS_EQ_LEMMA:
    !v P. (!i. ~(i = v) ==> ~(P i)) ==> ((?i. P i) = P v)
Proof
  METIS_TAC []
QED

Theorem w2w_eq_n2w:
    !w:word8. (!m. m < 256 ==> ((w2w w = (n2w m):word32) = (w = n2w m))) /\
              (w2w ((w2w w):word32) = w)
Proof
  Cases_word
  THEN FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,w2n_n2w,n2w_11]
  THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC (DECIDE ``k < 256 ==> k < 4294967296``)
  THEN FULL_SIMP_TAC std_ss []
QED

Theorem w2w_CLAUSES:
    !b1 b2 h1 h2.
      ((w2w b1 = (w2w b2):word32) = (b1 = b2:word8)) /\
      ((w2w h1 = (w2w h2):word32) = (h1 = h2:word16)) /\
      (w2w ((w2w b1):word32) = b1) /\ (w2w ((w2w h1):word32) = h1)
Proof
  REPEAT Cases_word
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
  \\ IMP_RES_TAC (DECIDE ``n < 256 ==> n < 4294967296:num``)
  \\ IMP_RES_TAC (DECIDE ``n < 65536 ==> n < 4294967296:num``)
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

Theorem LESS_SUB_MOD:
    !n m k. n < k ==> ((n - m) MOD k = n - m)
Proof
  REPEAT STRIP_TAC THEN `n - m < k` by DECIDE_TAC THEN ASM_SIMP_TAC std_ss []
QED

