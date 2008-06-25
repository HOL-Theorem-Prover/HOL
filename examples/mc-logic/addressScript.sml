
open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib bitTheory arithmeticTheory fcpTheory;

val _ = new_theory "address";

infix \\ 
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* definitions *)

val ALIGNED_def = Define `ALIGNED (x:word32) = (x && 3w = 0w)`;

val ADDR32_def = Define `ADDR32 (x:word30) = (w2w x << 2):word32`;
val ADDR30_def = Define `ADDR30 (x:word32) = ((31 >< 2) x):word30`;

val CONTAINER_def = Define `CONTAINER x = x:bool`;

(* theorems *)

val ZERO_word30 = store_thm("ZERO_word30",
  ``1073741824w = 0w:word30``,
  SRW_TAC [WORD_ARITH_EQ_ss] []);

val lem = (GEN_ALL o SIMP_RULE std_ss [AND_IMP_INTRO] o
   Q.DISCH `dimindex (:'b) - 1 = h` o
   SIMP_RULE (arith_ss++WORD_EXTRACT_ss) [] o
   Q.DISCH `dimindex(:'b) < dimindex(:'a)` o SPEC_ALL) WORD_w2w_OVER_ADD;

val lower_ADDR32_ADD = store_thm("lower_ADDR32_ADD",
  ``!w x. (1 >< 0) (ADDR32 x + w) = ((1 >< 0) w):word2``,
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss] [lem, ADDR32_def]);

val ADDR32_eq_0 = store_thm("ADDR32_eq_0",
  ``!x. (1 >< 0) (ADDR32 x) = 0w:word2``,
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss] [ADDR32_def]);

val ADDR32_n2w = store_thm ("ADDR32_n2w", 
  ``!n. (ADDR32 (n2w n)  = n2w (4 * n))``,
  SIMP_TAC (std_ss++WORD_MUL_LSL_ss) [GSYM word_mul_n2w, ADDR32_def]
    \\ SRW_TAC [WORD_BIT_EQ_ss] [n2w_def]);

val n2w_and_1 = store_thm("n2w_and_1",
  ``!n. (n2w n) && 1w = n2w (n MOD 2):'a word``,
  SIMP_TAC std_ss [(SIMP_RULE std_ss [] o GSYM o Q.SPEC `0`) BITS_ZERO3]
    \\ SRW_TAC [WORD_BIT_EQ_ss, BIT_ss] [n2w_def]
    \\ Cases_on `i = 0`
    \\ SRW_TAC [ARITH_ss] [BIT_def, BITS_ZERO, BITS_COMP_THM2]);
  
val n2w_and_3 = store_thm("n2w_and_3",
  ``!n. (n2w n) && 3w = n2w (n MOD 4):'a word``,
  SIMP_TAC std_ss [(SIMP_RULE std_ss [] o GSYM o Q.SPEC `1`) BITS_ZERO3]
    \\ SRW_TAC [WORD_BIT_EQ_ss, BIT_ss] [n2w_def]
    \\ Cases_on `i = 0` \\ Cases_on `i = 1`
    \\ SRW_TAC [ARITH_ss] [BIT_def, BITS_ZERO, BITS_COMP_THM2]);

val ALIGNED_n2w = store_thm("ALIGNED_n2w",
  ``!n. ALIGNED (n2w n) = (n MOD 4 = 0)``,
  STRIP_TAC \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_and_3,ALIGNED_def,n2w_11]
  \\ `n MOD 4 < 4` by METIS_TAC [DIVISION,DECIDE ``0<4``]
  \\ `n MOD 4 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD]);

val ALIGNED_MULT = store_thm("ALIGNED_MULT",
  ``!x y. ALIGNED x ==> ALIGNED (x + 4w * y)``,
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [word_add_n2w,word_mul_n2w,ALIGNED_def,n2w_and_3]
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM] 
  \\ SIMP_TAC std_ss [MOD_TIMES]);

val ADDR32_and_3w = store_thm("ADDR32_and_3w",
  ``!x. (ADDR32 x) && 3w = 0w``,
  wordsLib.Cases_word \\ REWRITE_TAC [ADDR32_n2w,n2w_and_3]
  \\ SIMP_TAC std_ss [RW1 [MULT_COMM] MOD_EQ_0]);

val ALIGNED_ADDR32 = store_thm("ALIGNED_ADDR32",
  ``!x. ALIGNED (ADDR32 x)``,
  REWRITE_TAC [ALIGNED_def, ADDR32_and_3w]);

val ADDR30_n2w = store_thm("ADDR30_n2w",
  ``!n. ADDR30 (n2w n) = n2w (n DIV 4)``,
  SRW_TAC [SIZES_ss] [ADDR30_def, word_extract_n2w, BITS_THM]);

val ADDR30_ADDR32_ADD = store_thm("ADDR30_ADDR32_ADD",
  ``!x y. ADDR30 (ADDR32 x + y) = x + ADDR30 y``,
  wordsLib.Cases_word \\ wordsLib.Cases_word
  \\ REWRITE_TAC [ADDR30_n2w,ADDR32_n2w,word_add_n2w]
  \\ SIMP_TAC std_ss [ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]);

val ADDR30_ADDR32_LEMMA = prove(
  ``!a. (ADDR30 (ADDR32 a + 0w) = a) /\ 
        (ADDR30 (ADDR32 a + 1w) = a) /\ 
        (ADDR30 (ADDR32 a + 2w) = a) /\ 
        (ADDR30 (ADDR32 a + 3w) = a)``,
  SIMP_TAC std_ss [ADDR30_ADDR32_ADD,ADDR30_n2w,WORD_ADD_0]);

val ADDR30_ADDR32 = store_thm("ADDR30_ADDR32",
  ``!x. (ADDR30 (ADDR32 x) = x) /\
        (ADDR30 (ADDR32 x + 0w) = x) /\ 
        (ADDR30 (ADDR32 x + 1w) = x) /\ 
        (ADDR30 (ADDR32 x + 2w) = x) /\ 
        (ADDR30 (ADDR32 x + 3w) = x)``,
  REWRITE_TAC
    [REWRITE_RULE [WORD_ADD_0] ADDR30_ADDR32_LEMMA,ADDR30_ADDR32_LEMMA]);

val EXISTS_ADDR30 = store_thm("EXISTS_ADDR30",
  ``!x. (x && 3w = 0w) ==> ?y. x = ADDR32 y``,
  SRW_TAC [] [ADDR32_def] \\ Q.EXISTS_TAC `(31 >< 2) x`
    \\ SRW_TAC [WORD_EXTRACT_ss] []
    \\ FULL_SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

val add32_ADDR30 = store_thm("ADDR32_ADDR30",
  ``!x. (x && 3w = 0w) ==> (ADDR32 (ADDR30 x) = x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_ADDR30
    \\ ASM_REWRITE_TAC [ADDR30_ADDR32]);

val ADDR32_ADD = store_thm ("ADDR32_ADD", 
  ``!v w. (ADDR32 (v + w)  = ADDR32 v + ADDR32 w)``,
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [ADDR32_n2w,word_add_n2w,LEFT_ADD_DISTRIB]);

val ADDR32_NEG = store_thm("ADDR32_NEG",
  ``!w. ADDR32 ($- w) = $- (ADDR32 w)``,
  wordsLib.Cases_word \\ REWRITE_TAC [ADDR32_n2w] 
  \\ wordsLib.WORD_EVAL_TAC \\ REWRITE_TAC [ADDR32_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss)
       [n2w_11,LEFT_SUB_DISTRIB,MOD_COMMON_FACTOR]);

val ADDR32_SUB = store_thm ("ADDR32_SUB", 
  ``!v w. (ADDR32 (v - w)  = ADDR32 v - ADDR32 w)``,
  REWRITE_TAC [word_sub_def,ADDR32_ADD,ADDR32_NEG]);
  
val ADDR32_SUC = store_thm("ADDR32_SUC",
  ``!p. ADDR32 (p + 1w) = ADDR32 p + 4w``,
  SIMP_TAC std_ss [ADDR32_ADD,ADDR32_n2w]);

val ADDR30_ADD = store_thm("ADDR30_ADD",
  ``!x m. ADDR30 x + n2w m = ADDR30 (x + n2w (4 * m))``,
  Cases_word \\ REWRITE_TAC [ADDR30_n2w,word_add_n2w]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM ADD_DIV_ADD_DIV,AC MULT_COMM MULT_ASSOC]);  

val ADD_LSL = save_thm("ADD_LSL", WORD_ADD_LSL);

val ADDR32_11 = store_thm("ADDR32_11",
  ``!a b. ((ADDR32 a = ADDR32 b) = (a = b)) /\ 
          ((ADDR32 a = ADDR32 b + 0w) = (a = b)) /\ 
          ((ADDR32 a + 0w = ADDR32 b) = (a = b)) /\ 
          ((ADDR32 a + 0w = ADDR32 b + 0w) = (a = b)) /\ 
          ((ADDR32 a + 1w = ADDR32 b + 1w) = (a = b)) /\ 
          ((ADDR32 a + 2w = ADDR32 b + 2w) = (a = b)) /\ 
          ((ADDR32 a + 3w = ADDR32 b + 3w) = (a = b))``,
  SRW_TAC [] [WORD_EQ_ADD_RCANCEL,
    simpLib.SIMP_PROVE (std_ss++WORD_BIT_EQ_ss) [ADDR32_def]
      ``(ADDR32 a = ADDR32 b) = (a = b)``]);

val ADDR32_EQ_0 = store_thm("ADDR32_EQ_0",
  ``!a. (ADDR32 a = 0w) = (a = 0w)``,
  REWRITE_TAC [SIMP_RULE std_ss [ADDR32_n2w] (Q.SPECL [`a`,`0w`] ADDR32_11)]);

val lem = Q.prove(
   `(!a. ADDR32 a && 1w = 0w) /\
    (!a. ADDR32 a && 2w = 0w) /\
    (!a. ADDR32 a && 3w = 0w)`,
  SRW_TAC [WORD_BIT_EQ_ss] [ADDR32_def]);

val ADDR32_NEQ_ADDR32 = store_thm("ADDR32_NEQ_ADDR32",
  ``!a b. ~(ADDR32 a + 0w = ADDR32 b + 1w) /\ 
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
          ~(ADDR32 a = ADDR32 b + 3w)``, 
  SRW_TAC [] [lem, WORD_ADD_OR] \\ SRW_TAC [WORD_BIT_EQ_ss] [ADDR32_def]);

val EXISTS_ADDR32 = store_thm("EXISTS_ADDR32",
  ``!p. ?a. (p = ADDR32 a + 0w) \/ (p = ADDR32 a + 1w) \/ 
            (p = ADDR32 a + 2w) \/ (p = ADDR32 a + 3w)``,
  STRIP_TAC \\ Q.EXISTS_TAC `(31 >< 2) p`
    \\ SRW_TAC [] [lem, WORD_ADD_OR]
    \\ SRW_TAC [WORD_BIT_EQ_ss] [ADDR32_def]
    \\ DECIDE_TAC);

val ADDR32_ABSORB_CONST = store_thm("ADDR32_ABSORB_CONST",
  ``(ADDR32 x + 0w  = ADDR32 x) /\ 
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
    (ADDR32 x - 40w = ADDR32 (x - 10w))``,    
  SIMP_TAC std_ss [ADDR32_ADD,ADDR32_SUB,ADDR32_n2w,WORD_ADD_0]);

val ADDRESS_ROTATE = store_thm("ADDRESS_ROTATE",
  ``!q:word32 z:word30. q #>> (8 * w2n ((1 >< 0) (ADDR32 z):word2)) = q``,
  SIMP_TAC std_ss [ADDR32_eq_0,word_0_n2w] \\ STRIP_TAC \\ EVAL_TAC);

val ADDR30_THM = store_thm("ADDR30_THM",
  ``!x. ADDR30 x = n2w (w2n x DIV 4)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,ADDR30_n2w]);

val ADDR32_THM = store_thm("ADDR32_THM",
  ``!x. ADDR32 x = n2w (4 * w2n x)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,ADDR32_n2w]);

val ALIGNED_THM = store_thm("ALIGNED_THM",
  ``!p. ALIGNED p = ?k. p = k * 4w``,
  SRW_TAC [] [ALIGNED_def] \\ EQ_TAC \\ SRW_TAC [WORD_MUL_LSL_ss] []
  THENL [Q.EXISTS_TAC `(31 >< 2) p`, ALL_TAC]
  \\ FULL_SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

val ALIGNED_NEG_lemma = prove(
  ``!x. ALIGNED x ==> ALIGNED ($- x)``,
  ASM_SIMP_TAC std_ss  [ALIGNED_THM,w2n_n2w,LESS_MOD]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n2w (2**30) - k` 
  \\ ASM_SIMP_TAC (std_ss++WORD_ARITH_EQ_ss) [WORD_RIGHT_SUB_DISTRIB]            
  \\ ASM_SIMP_TAC (std_ss++WORD_ss) []);

val ALIGNED_NEG = store_thm("ALIGNED_NEG",
  ``!x. ALIGNED ($- x) = ALIGNED x``,
  METIS_TAC [ALIGNED_NEG_lemma,WORD_NEG_NEG]);

val ALIGNED_and_1 = store_thm("ALIGNED_and_1",
  ``!x. ALIGNED x ==> (x && 1w = 0w)``,        
  REWRITE_TAC [ALIGNED_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_EQ_0]);

val ALIGNED_add_1_and_1 = store_thm("ALIGNED_add_1_and_1",
  ``!x. ALIGNED x ==> ~(x + 1w && 1w = 0w)``,        
  REWRITE_TAC [ALIGNED_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES]);

val tac = 
  REWRITE_TAC [ALIGNED_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_3,n2w_11]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES];

val ALIGNED_add_1_and_3 = store_thm("ALIGNED_add_1_and_3",
  ``!x. ALIGNED x ==> (x + 1w && 3w = 1w)``,tac);
val ALIGNED_add_2_and_3 = store_thm("ALIGNED_add_2_and_3",
  ``!x. ALIGNED x ==> (x + 2w && 3w = 2w)``,tac);
val ALIGNED_add_3_and_3 = store_thm("ALIGNED_add_3_and_3",
  ``!x. ALIGNED x ==> (x + 3w && 3w = 3w)``,tac);

val ALIGNED_ADD = store_thm("ALIGNED_ADD",
  ``!x y. ALIGNED x /\ ALIGNED y ==> ALIGNED (x + y)``,
  REWRITE_TAC [ALIGNED_THM] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [GSYM WORD_RIGHT_ADD_DISTRIB] \\ METIS_TAC []);
  
val word_arith_lemma1 = store_thm("word_arith_lemma1",
  ``!n m. (n2w n + n2w m = n2w (n + m):'a word) /\
          (x + n2w n + n2w m = x + n2w (n + m):'a word) /\
          (x - n2w n - n2w m = x - n2w (n + m):'a word)``,
  REWRITE_TAC [GSYM WORD_SUB_PLUS,word_add_n2w,GSYM WORD_ADD_ASSOC]);

val word_arith_lemma2 = store_thm("word_arith_lemma2",
  ``!n m. n2w n - (n2w m) :'a word =
      if n < m then $- (n2w (m-n)) else n2w (n-m)``,
  REPEAT STRIP_TAC \\ Cases_on `n < m` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS,LESS_EQ]
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,ADD1,DECIDE ``n+1+p-n = 1+p:num``]
  \\ REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_REFL] 
  \\ REWRITE_TAC [GSYM WORD_SUB_PLUS] 
  \\ REWRITE_TAC [word_sub_def,WORD_ADD_0,DECIDE ``m+p-m=p:num``]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_ADD]);
  
val word_arith_lemma3 = store_thm("word_arith_lemma3",
  ``!x n m. x - n2w m + n2w n :'a word = if n < m then x - (n2w (m-n)) else x + n2w (n-m)``,
  REWRITE_TAC [word_sub_def,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM (RW1 [WORD_ADD_COMM] word_sub_def),word_arith_lemma2] 
  \\ REPEAT STRIP_TAC \\ Cases_on `n<m` \\ ASM_REWRITE_TAC []);

val word_arith_lemma4 = store_thm("word_arith_lemma4",
  ``!x n m. x + n2w n - n2w m :'a word = if n < m then x - (n2w (m-n)) else x + n2w (n-m)``,
  REWRITE_TAC [word_sub_def,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM word_sub_def,word_arith_lemma2]
  \\ REPEAT STRIP_TAC \\ Cases_on `n<m` \\ ASM_REWRITE_TAC [word_sub_def]);

val word_arith_lemma5 = store_thm("word_arith_lemma5",
  ``!x y m n. (x + n2w n = y + n2w m) = 
              if n < m then (x = y + n2w m - n2w n) else (x + n2w n - n2w m = y)``,
  ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO]
  \\ SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_SUB_SUB]
  \\ METIS_TAC [WORD_SUB_PLUS,WORD_ADD_COMM]);

val ADDR32_ADD_EQ_ZERO_LEMMA = prove(
  ``!x m. 0 < m /\ w2n x + m < dimword (:'a) ==> ~((x:'a word) + n2w m = 0w)``,
  Cases_word
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,word_add_n2w,n2w_11,ZERO_LT_dimword] 
  \\ DECIDE_TAC);

val ADDR32_ADD_EQ_ZERO = store_thm("ADDR32_ADD_EQ_ZERO",
  ``!x. ~(ADDR32 x + 1w = 0w) /\ ~(ADDR32 x + 2w = 0w) /\ ~(ADDR32 x + 3w = 0w)``,
  Cases_word \\ REWRITE_TAC [ADDR32_n2w] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC 
  \\ REWRITE_TAC [] \\ MATCH_MP_TAC ADDR32_ADD_EQ_ZERO_LEMMA
  \\ `4 * n < 4 * dimword (:30)` by DECIDE_TAC       
  \\ FULL_SIMP_TAC (bool_ss++SIZES_ss) [w2n_n2w,LESS_MOD,EVAL ``4 * 1073741824``]
  \\ DECIDE_TAC);

val word_add_and_3w = store_thm("word_add_and_3w",
  ``!w. (w + n2w n) && 3w = (w + n2w (n MOD 4)) && 3w``,
  Cases_word \\ SIMP_TAC std_ss [n2w_and_3,word_add_n2w]
  \\ `n = n DIV 4 * 4 + n MOD 4` by METIS_TAC [DIVISION,EVAL ``0<4``]
  \\ ONCE_ASM_REWRITE_TAC []  
  \\ ONCE_REWRITE_TAC [DECIDE ``m + (k + l) = k + (m + l:num)``]
  \\ SIMP_TAC std_ss [MOD_TIMES]);

val ALIGNED_CLAUSES = store_thm("ALIGNED_CLAUSES",
  ``!x a. (ALIGNED (a + 4w * x) = ALIGNED a) /\ (ALIGNED (4w * x + a) = ALIGNED a) /\
          (ALIGNED (a + x * 4w) = ALIGNED a) /\ (ALIGNED (x * 4w + a) = ALIGNED a) /\
          (ALIGNED (a + 4w) = ALIGNED a) /\ (ALIGNED (4w + a) = ALIGNED a)``,
  Cases_word \\ SIMP_TAC std_ss [ALIGNED_def,word_mul_n2w] 
  \\ ONCE_REWRITE_TAC [word_add_and_3w] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] 
  \\ ONCE_REWRITE_TAC [word_add_and_3w] 
  \\ SIMP_TAC std_ss [MOD_EQ_0,RW1 [MULT_COMM] MOD_EQ_0,WORD_ADD_0]);    

val NOT_ALIGNED = store_thm("NOT_ALIGNED",
  ``!a. ALIGNED a ==> ~(ALIGNED (a + 1w)) /\  ~(ALIGNED (a + 2w)) /\ ~(ALIGNED (a + 3w))``,
  Cases_word \\ SIMP_TAC std_ss [ALIGNED_n2w,word_add_n2w] 
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0<4``)]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [ADD] \\ EVAL_TAC);

val word32_add_n2w = store_thm("word32_add_n2w",
  ``!x n. x + (n2w n):word32 = 
          if n < 2**31 then x + n2w n else x - n2w (2**32 - n MOD 2**32)``,
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
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []]);

val CONTAINER_IF_T = store_thm("CONTAINER_IF_T",
  ``!x y z. CONTAINER x ==> ((if x then y else z) = y:'a)``,
  SIMP_TAC std_ss [CONTAINER_def]);

val CONTAINER_IF_F = store_thm("CONTAINER_IF_F",
  ``!x y z. CONTAINER ~x ==> ((if x then y else z) = z:'a)``,
  SIMP_TAC std_ss [CONTAINER_def]);

val _ = export_theory();
