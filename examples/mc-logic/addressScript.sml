(* load "wordsLib"; *)

open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib bitTheory arithmeticTheory fcpTheory;

val _ = new_theory "address";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


val aligned_def = Define `aligned (x:word32) = (x && 3w = 0w)`;

val addr32_def = Define `addr32 (x:word30) = (w2w x << 2):word32`;
val addr30_def = Define `addr30 (x:word32) = ((31 >< 2) x):word30`;

val ZERO_word30 = store_thm("ZERO_word30",
  ``1073741824w = 0w:word30``,
  SRW_TAC [WORD_ARITH_EQ_ss] []);

val lem = (GEN_ALL o SIMP_RULE std_ss [AND_IMP_INTRO] o
   Q.DISCH `dimindex (:'b) - 1 = h` o
   SIMP_RULE (arith_ss++WORD_EXTRACT_ss) [] o
   Q.DISCH `dimindex(:'b) < dimindex(:'a)` o SPEC_ALL) WORD_w2w_OVER_ADD;

val lower_addr32_ADD = store_thm("lower_addr32_ADD",
  ``!w x. (1 >< 0) (addr32 x + w) = ((1 >< 0) w):word2``,
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss] [lem, addr32_def]);

val addr32_eq_0 = store_thm("addr32_eq_0",
  ``!x. (1 >< 0) (addr32 x) = 0w:word2``,
  SRW_TAC [ARITH_ss, WORD_EXTRACT_ss] [addr32_def]);

val addr32_n2w = store_thm ("addr32_n2w", 
  ``!n. (addr32 (n2w n)  = n2w (4 * n))``,
  SIMP_TAC (std_ss++WORD_MUL_LSL_ss) [GSYM word_mul_n2w, addr32_def]
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

val aligned_MULT = store_thm("aligned_MULT",
  ``!x y. aligned x ==> aligned (x + 4w * y)``,
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [word_add_n2w,word_mul_n2w,aligned_def,n2w_and_3]
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM] 
  \\ SIMP_TAC std_ss [MOD_TIMES]);

val addr32_and_3w = store_thm("addr32_and_3w",
  ``!x. (addr32 x) && 3w = 0w``,
  wordsLib.Cases_word \\ REWRITE_TAC [addr32_n2w,n2w_and_3]
  \\ SIMP_TAC std_ss [RW1 [MULT_COMM] MOD_EQ_0]);

val aligned_addr32 = store_thm("aligned_addr32",
  ``!x. aligned (addr32 x)``,
  REWRITE_TAC [aligned_def, addr32_and_3w]);

val addr30_n2w = store_thm("addr30_n2w",
  ``!n. addr30 (n2w n) = n2w (n DIV 4)``,
  SRW_TAC [SIZES_ss] [addr30_def, word_extract_n2w, BITS_THM]);

val addr30_addr32_ADD = store_thm("addr30_addr32_ADD",
  ``!x y. addr30 (addr32 x + y) = x + addr30 y``,
  wordsLib.Cases_word \\ wordsLib.Cases_word
  \\ REWRITE_TAC [addr30_n2w,addr32_n2w,word_add_n2w]
  \\ SIMP_TAC std_ss [ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]);

val addr30_addr32_LEMMA = prove(
  ``!a. (addr30 (addr32 a + 0w) = a) /\ 
        (addr30 (addr32 a + 1w) = a) /\ 
        (addr30 (addr32 a + 2w) = a) /\ 
        (addr30 (addr32 a + 3w) = a)``,
  SIMP_TAC std_ss [addr30_addr32_ADD,addr30_n2w,WORD_ADD_0]);

val addr30_addr32 = store_thm("addr30_addr32",
  ``!x. (addr30 (addr32 x) = x) /\
        (addr30 (addr32 x + 0w) = x) /\ 
        (addr30 (addr32 x + 1w) = x) /\ 
        (addr30 (addr32 x + 2w) = x) /\ 
        (addr30 (addr32 x + 3w) = x)``,
  REWRITE_TAC
    [REWRITE_RULE [WORD_ADD_0] addr30_addr32_LEMMA,addr30_addr32_LEMMA]);

val EXISTS_addr30 = store_thm("EXISTS_addr30",
  ``!x. (x && 3w = 0w) ==> ?y. x = addr32 y``,
  SRW_TAC [] [addr32_def] \\ Q.EXISTS_TAC `(31 >< 2) x`
    \\ SRW_TAC [WORD_EXTRACT_ss] []
    \\ FULL_SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

val add32_addr30 = store_thm("addr32_addr30",
  ``!x. (x && 3w = 0w) ==> (addr32 (addr30 x) = x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_addr30
    \\ ASM_REWRITE_TAC [addr30_addr32]);

val addr32_ADD = store_thm ("addr32_ADD", 
  ``!v w. (addr32 (v + w)  = addr32 v + addr32 w)``,
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [addr32_n2w,word_add_n2w,LEFT_ADD_DISTRIB]);

val addr32_NEG = store_thm("addr32_NEG",
  ``!w. addr32 ($- w) = $- (addr32 w)``,
  wordsLib.Cases_word \\ REWRITE_TAC [addr32_n2w] 
  \\ wordsLib.WORD_EVAL_TAC \\ REWRITE_TAC [addr32_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss)
       [n2w_11,LEFT_SUB_DISTRIB,MOD_COMMON_FACTOR]);

val addr32_SUB = store_thm ("addr32_SUB", 
  ``!v w. (addr32 (v - w)  = addr32 v - addr32 w)``,
  REWRITE_TAC [word_sub_def,addr32_ADD,addr32_NEG]);
  
val addr32_SUC = store_thm("addr32_SUC",
  ``!p. addr32 (p + 1w) = addr32 p + 4w``,
  SIMP_TAC std_ss [addr32_ADD,addr32_n2w]);

val addr30_ADD = store_thm("addr30_ADD",
  ``!x m. addr30 x + n2w m = addr30 (x + n2w (4 * m))``,
  Cases_word \\ REWRITE_TAC [addr30_n2w,word_add_n2w]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM ADD_DIV_ADD_DIV,AC MULT_COMM MULT_ASSOC]);  

val ADD_LSL = save_thm("ADD_LSL", WORD_ADD_LSL);

val addr32_11 = store_thm("addr32_11",
  ``!a b. ((addr32 a = addr32 b) = (a = b)) /\ 
          ((addr32 a = addr32 b + 0w) = (a = b)) /\ 
          ((addr32 a + 0w = addr32 b) = (a = b)) /\ 
          ((addr32 a + 0w = addr32 b + 0w) = (a = b)) /\ 
          ((addr32 a + 1w = addr32 b + 1w) = (a = b)) /\ 
          ((addr32 a + 2w = addr32 b + 2w) = (a = b)) /\ 
          ((addr32 a + 3w = addr32 b + 3w) = (a = b))``,
  SRW_TAC [] [WORD_EQ_ADD_RCANCEL,
    simpLib.SIMP_PROVE (std_ss++WORD_BIT_EQ_ss) [addr32_def]
      ``(addr32 a = addr32 b) = (a = b)``]);

val addr32_EQ_0 = store_thm("addr32_EQ_0",
  ``!a. (addr32 a = 0w) = (a = 0w)``,
  REWRITE_TAC [SIMP_RULE std_ss [addr32_n2w] (Q.SPECL [`a`,`0w`] addr32_11)]);

val lem = Q.prove(
   `(!a. addr32 a && 1w = 0w) /\
    (!a. addr32 a && 2w = 0w) /\
    (!a. addr32 a && 3w = 0w)`,
  SRW_TAC [WORD_BIT_EQ_ss] [addr32_def]);

val addr32_NEQ_addr32 = store_thm("addr32_NEQ_addr32",
  ``!a b. ~(addr32 a + 0w = addr32 b + 1w) /\ 
          ~(addr32 a + 0w = addr32 b + 2w) /\ 
          ~(addr32 a + 0w = addr32 b + 3w) /\ 
          ~(addr32 a + 1w = addr32 b + 2w) /\ 
          ~(addr32 a + 1w = addr32 b + 3w) /\ 
          ~(addr32 a + 2w = addr32 b + 3w) /\
          ~(addr32 a + 1w = addr32 b + 0w) /\ 
          ~(addr32 a + 2w = addr32 b + 0w) /\ 
          ~(addr32 a + 3w = addr32 b + 0w) /\ 
          ~(addr32 a + 2w = addr32 b + 1w) /\ 
          ~(addr32 a + 3w = addr32 b + 1w) /\ 
          ~(addr32 a + 3w = addr32 b + 2w) /\ 
          ~(addr32 a + 1w = addr32 b) /\ 
          ~(addr32 a + 2w = addr32 b) /\ 
          ~(addr32 a + 3w = addr32 b) /\
          ~(addr32 a = addr32 b + 1w) /\ 
          ~(addr32 a = addr32 b + 2w) /\ 
          ~(addr32 a = addr32 b + 3w)``, 
  SRW_TAC [] [lem, WORD_ADD_OR] \\ SRW_TAC [WORD_BIT_EQ_ss] [addr32_def]);

val EXISTS_addr32 = store_thm("EXISTS_addr32",
  ``!p. ?a. (p = addr32 a + 0w) \/ (p = addr32 a + 1w) \/ 
            (p = addr32 a + 2w) \/ (p = addr32 a + 3w)``,
  STRIP_TAC \\ Q.EXISTS_TAC `(31 >< 2) p`
    \\ SRW_TAC [] [lem, WORD_ADD_OR]
    \\ SRW_TAC [WORD_BIT_EQ_ss] [addr32_def]
    \\ DECIDE_TAC);

val addr32_ABSORB_CONST = store_thm("addr32_ABSORB_CONST",
  ``(addr32 x + 0w  = addr32 x) /\ 
    (addr32 x + 4w  = addr32 (x + 1w)) /\ 
    (addr32 x + 8w  = addr32 (x + 2w)) /\ 
    (addr32 x + 12w = addr32 (x + 3w)) /\ 
    (addr32 x + 16w = addr32 (x + 4w)) /\ 
    (addr32 x + 20w = addr32 (x + 5w)) /\
    (addr32 x + 24w = addr32 (x + 6w)) /\
    (addr32 x + 28w = addr32 (x + 7w)) /\
    (addr32 x + 32w = addr32 (x + 8w)) /\
    (addr32 x + 36w = addr32 (x + 9w)) /\
    (addr32 x + 40w = addr32 (x + 10w)) /\
    (addr32 x - 0w  = addr32 (x - 0w)) /\
    (addr32 x - 4w  = addr32 (x - 1w)) /\ 
    (addr32 x - 8w  = addr32 (x - 2w)) /\ 
    (addr32 x - 12w = addr32 (x - 3w)) /\ 
    (addr32 x - 16w = addr32 (x - 4w)) /\ 
    (addr32 x - 20w = addr32 (x - 5w)) /\
    (addr32 x - 24w = addr32 (x - 6w)) /\
    (addr32 x - 28w = addr32 (x - 7w)) /\
    (addr32 x - 32w = addr32 (x - 8w)) /\
    (addr32 x - 36w = addr32 (x - 9w)) /\
    (addr32 x - 40w = addr32 (x - 10w))``,    
  SIMP_TAC std_ss [addr32_ADD,addr32_SUB,addr32_n2w,WORD_ADD_0]);

val ADDRESS_ROTATE = store_thm("ADDRESS_ROTATE",
  ``!q:word32 z:word30. q #>> (8 * w2n ((1 >< 0) (addr32 z):word2)) = q``,
  SIMP_TAC std_ss [addr32_eq_0,word_0_n2w] \\ STRIP_TAC \\ EVAL_TAC);

val addr30_THM = store_thm("addr30_THM",
  ``!x. addr30 x = n2w (w2n x DIV 4)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,addr30_n2w]);

val addr32_THM = store_thm("addr32_THM",
  ``!x. addr32 x = n2w (4 * w2n x)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,addr32_n2w]);

val aligned_THM = store_thm("aligned_THM",
  ``!p. aligned p = ?k. p = k * 4w``,
  SRW_TAC [] [aligned_def] \\ EQ_TAC \\ SRW_TAC [WORD_MUL_LSL_ss] []
    << [Q.EXISTS_TAC `(31 >< 2) p`, ALL_TAC]
    \\ FULL_SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

val aligned_NEG_lemma = prove(
  ``!x. aligned x ==> aligned ($- x)``,
  ASM_SIMP_TAC std_ss  [aligned_THM,w2n_n2w,LESS_MOD]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n2w (2**30) - k` 
  \\ ASM_SIMP_TAC (std_ss++WORD_ARITH_EQ_ss) [WORD_RIGHT_SUB_DISTRIB]            
  \\ ASM_SIMP_TAC (std_ss++WORD_ss) []);

val aligned_NEG = store_thm("aligned_NEG",
  ``!x. aligned ($- x) = aligned x``,
  METIS_TAC [aligned_NEG_lemma,WORD_NEG_NEG]);

val aligned_and_1 = store_thm("aligned_and_1",
  ``!x. aligned x ==> (x && 1w = 0w)``,        
  REWRITE_TAC [aligned_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_EQ_0]);

val aligned_add_1_and_1 = store_thm("aligned_add_1_and_1",
  ``!x. aligned x ==> ~(x + 1w && 1w = 0w)``,        
  REWRITE_TAC [aligned_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES]);

val aligned_ADD = store_thm("aligned_ADD",
  ``!x y. aligned x /\ aligned y ==> aligned (x + y)``,
  REWRITE_TAC [aligned_THM] \\ REPEAT STRIP_TAC
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



val _ = export_theory();
