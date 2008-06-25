
open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib bitTheory arithmeticTheory fcpTheory;
open systemTheory arm_evalTheory;

val _ = new_theory "address";

infix \\ 
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* definitions *)

val CONTAINER_def = Define `CONTAINER x = x:bool`;

(* theorems *)

val ZERO_word30 = store_thm("ZERO_word30",
  ``1073741824w = 0w:word30``,
  SRW_TAC [WORD_ARITH_EQ_ss] []);

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

val n2w_and_1 = save_thm("n2w_and_1",
  (SIMP_RULE std_ss [] o SPEC ``1``) WORD_AND_EXP_SUB1);

val n2w_and_3 = save_thm("n2w_and_3",
  (SIMP_RULE std_ss [] o SPEC ``2``) WORD_AND_EXP_SUB1);

val aligned_add_1_and_1 = store_thm("aligned_add_1_and_1",
  ``!x. aligned x ==> ~(x + 1w && 1w = 0w)``,        
  REWRITE_TAC [aligned_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_1,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES]);

val tac = 
  REWRITE_TAC [aligned_THM] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`k`,`k`) \\ Cases
  \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,n2w_and_3,n2w_11]
  \\ SIMP_TAC (std_ss++SIZES_ss) [MOD_TIMES];

val aligned_add_1_and_3 = store_thm("aligned_add_1_and_3",
  ``!x. aligned x ==> (x + 1w && 3w = 1w)``,tac);
val aligned_add_2_and_3 = store_thm("aligned_add_2_and_3",
  ``!x. aligned x ==> (x + 2w && 3w = 2w)``,tac);
val aligned_add_3_and_3 = store_thm("aligned_add_3_and_3",
  ``!x. aligned x ==> (x + 3w && 3w = 3w)``,tac);

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

val addr32_ADD_EQ_ZERO_LEMMA = prove(
  ``!x m. 0 < m /\ w2n x + m < dimword (:'a) ==> ~((x:'a word) + n2w m = 0w)``,
  Cases_word
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,word_add_n2w,n2w_11,ZERO_LT_dimword] 
  \\ DECIDE_TAC);

val addr32_ADD_EQ_ZERO = store_thm("addr32_ADD_EQ_ZERO",
  ``!x. ~(addr32 x + 1w = 0w) /\ ~(addr32 x + 2w = 0w) /\ ~(addr32 x + 3w = 0w)``,
  Cases_word \\ REWRITE_TAC [addr32_n2w] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC 
  \\ REWRITE_TAC [] \\ MATCH_MP_TAC addr32_ADD_EQ_ZERO_LEMMA
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

val aligned_CLAUSES = store_thm("aligned_CLAUSES",
  ``!x a. (aligned (a + 4w * x) = aligned a) /\ (aligned (4w * x + a) = aligned a) /\
          (aligned (a + x * 4w) = aligned a) /\ (aligned (x * 4w + a) = aligned a) /\
          (aligned (a + 4w) = aligned a) /\ (aligned (4w + a) = aligned a)``,
  Cases_word \\ SIMP_TAC std_ss [aligned_def,word_mul_n2w] 
  \\ ONCE_REWRITE_TAC [word_add_and_3w] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] 
  \\ ONCE_REWRITE_TAC [word_add_and_3w] 
  \\ SIMP_TAC std_ss [MOD_EQ_0,RW1 [MULT_COMM] MOD_EQ_0,WORD_ADD_0]);    

val NOT_aligned = store_thm("NOT_aligned",
  ``!a. aligned a ==> ~(aligned (a + 1w)) /\  ~(aligned (a + 2w)) /\ ~(aligned (a + 3w))``,
  Cases_word \\ SIMP_TAC std_ss [aligned_n2w,word_add_n2w] 
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
