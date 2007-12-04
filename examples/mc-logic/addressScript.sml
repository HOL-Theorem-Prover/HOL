
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

val lower_addr32_ADD = store_thm("lower_addr32_ADD",
  ``!w x. (1 >< 0) (addr32 x + w) = ((1 >< 0) w):word2``,
  wordsLib.Cases_word
  \\ REWRITE_TAC [addr32_def,EVAL ``dimindex (:32)``,w2w_def,word_lsl_n2w]
  \\ EVAL_TAC \\ REWRITE_TAC [BITS_def,MOD_2EXP_def,DIV_2EXP_def]
  \\ EVAL_TAC \\ REWRITE_TAC [DIV_1]
  \\ REWRITE_TAC [(GSYM o EVAL) ``4 * 1073741824``]
  \\ `0 < 4 /\ 0 < 1073741824` by EVAL_TAC
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT_MOD,MOD_MOD,MOD_TIMES]);

val addr32_eq_0 = store_thm("addr32_eq_0",
  ``!x. (1 >< 0) (addr32 x) = 0w:word2``,
  ONCE_REWRITE_TAC [(GSYM o REWRITE_CONV [WORD_ADD_0]) ``addr32 x + 0w``]
  \\ REWRITE_TAC [lower_addr32_ADD] \\ EVAL_TAC);

val addr32_n2w = store_thm ("addr32_n2w", 
  ``!n. (addr32 (n2w n)  = n2w (4 * n))``,
  REWRITE_TAC [addr32_def, DECIDE ``2 = 1 + 1``, GSYM LSL_ADD, 
               LSL_ONE,w2w_def, word_add_n2w, n2w_11, dimword_32]
  \\ `!n. n + n + (n + n) = 4*n` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [w2n_n2w, dimword_30, MOD_COMMON_FACTOR]);

val n2w_and_3w = store_thm("n2w_and_3",
  ``!n. (n2w n) && 3w = n2w (n MOD 4):'a word``,
  REWRITE_TAC [CART_EQ] \\ ONCE_REWRITE_TAC [word_index_n2w]
  \\ SIMP_TAC bool_ss [word_and_def,FCP_BETA] \\ REPEAT STRIP_TAC 
  \\ ONCE_REWRITE_TAC [word_index_n2w] \\ ASM_REWRITE_TAC []
  \\ `(i = 0) \/ (i = 1) \/ (2 <= i)` by DECIDE_TAC << [  
    ASM_SIMP_TAC std_ss [BIT_def,BITS_THM2]
    \\ SIMP_TAC bool_ss [GSYM (EVAL ``2*2``),MOD_MULT_MOD,EVAL ``0<2``],
    ASM_SIMP_TAC std_ss [BIT_def,BITS_THM2],
    REWRITE_TAC [BIT_def,BITS_THM,GSYM (EVAL ``2**2``)]
    \\ `2**2 <= 2**i` by ASM_SIMP_TAC std_ss [EXP_BASE_LE_MONO]
    \\ `n MOD (2**2) < 2**2` by ASM_SIMP_TAC std_ss [MOD_LESS]        
    \\ `3 < 2**2` by EVAL_TAC
    \\ IMP_RES_TAC LESS_LESS_EQ_TRANS
    \\ ASM_SIMP_TAC bool_ss [LESS_DIV_EQ_ZERO,ZERO_MOD,ZERO_LT_TWOEXP,EVAL ``0 = 1``]]);

val aligned_MULT = store_thm("aligned_MULT",
  ``!x y. aligned x ==> aligned (x + 4w * y)``,
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [word_add_n2w,word_mul_n2w,aligned_def,n2w_and_3w]
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM] 
  \\ SIMP_TAC std_ss [MOD_TIMES]);

val addr32_and_3w = store_thm("addr32_and_3w",
  ``!x. (addr32 x) && 3w = 0w``,
  wordsLib.Cases_word \\ REWRITE_TAC [addr32_n2w,n2w_and_3w]
  \\ SIMP_TAC std_ss [RW1 [MULT_COMM] MOD_EQ_0]);

val aligned_addr32 = store_thm("aligned_addr32",
  ``!x. aligned (addr32 x)``,
  REWRITE_TAC [aligned_def,addr32_and_3w]);

val addr30_n2w = store_thm("addr30_n2w",
  ``!n. addr30 (n2w n) = n2w (n DIV 4)``,
  REWRITE_TAC [addr30_def] \\ EVAL_TAC
  \\ REWRITE_TAC [(GSYM o EVAL) ``1073741824 * 4``]
  \\ `0 < 4 /\ 0 < 1073741824` by EVAL_TAC
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT_MOD,MOD_MOD,MOD_TIMES]
  \\ REWRITE_TAC [BITS_def,MOD_2EXP_def,DIV_2EXP_def]
  \\ EVAL_TAC \\ ASM_SIMP_TAC bool_ss [MOD_MOD]);

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
  REWRITE_TAC [REWRITE_RULE [WORD_ADD_0] addr30_addr32_LEMMA,addr30_addr32_LEMMA]);

val EXISTS_addr30 = store_thm("EXISTS_addr30",
  ``!x. (x && 3w = 0w) ==> ?y. x = addr32 y``,
  wordsLib.Cases_word \\ REWRITE_TAC [n2w_and_3w]  
  \\ `4 < dimword (:32)` by EVAL_TAC
  \\ `n MOD 4 < 4` by ASM_SIMP_TAC std_ss [MOD_LESS]
  \\ `n MOD 4 < dimword (:32)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [n2w_11,ZERO_LT_dimword,LESS_MOD]
  \\ STRIP_TAC \\ Q.EXISTS_TAC `n2w (n DIV 4)`
  \\ REWRITE_TAC [addr32_n2w] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [MATCH_MP DIVISION (DECIDE ``0<4``)]))
  \\ ASM_SIMP_TAC std_ss []);

val add32_addr30 = store_thm("addr32_addr30",
  ``!x. (x && 3w = 0w) ==> (addr32 (addr30 x) = x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_addr30 \\ ASM_REWRITE_TAC [addr30_addr32]);

val addr32_ADD = store_thm ("addr32_ADD", 
  ``!v w. (addr32 (v + w)  = addr32 v + addr32 w)``,
  Cases_word \\ Cases_word
  \\ REWRITE_TAC [addr32_n2w,word_add_n2w,LEFT_ADD_DISTRIB]);

val addr32_NEG = store_thm("addr32_NEG",
  ``!w. addr32 ($- w) = $- (addr32 w)``,
  wordsLib.Cases_word \\ REWRITE_TAC [addr32_n2w] 
  \\ wordsLib.WORDS_TAC \\ REWRITE_TAC [addr32_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11,LEFT_SUB_DISTRIB,MOD_COMMON_FACTOR]);

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

val ADD_LSL = store_thm("ADD_LSL",
  ``!v w n. (v + w) << n = (v << n) + (w << n)``,
  Induct_on `n` \\ SIMP_TAC std_ss [SHIFT_ZERO,SUC_ONE_ADD,GSYM LSL_ADD,LSL_ONE]
  \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val addr32_11 = store_thm("addr32_11",
  ``!a b. ((addr32 a = addr32 b) = (a = b)) /\ 
          ((addr32 a = addr32 b + 0w) = (a = b)) /\ 
          ((addr32 a + 0w = addr32 b) = (a = b)) /\ 
          ((addr32 a + 0w = addr32 b + 0w) = (a = b)) /\ 
          ((addr32 a + 1w = addr32 b + 1w) = (a = b)) /\ 
          ((addr32 a + 2w = addr32 b + 2w) = (a = b)) /\ 
          ((addr32 a + 3w = addr32 b + 3w) = (a = b))``,
  wordsLib.Cases_word \\ wordsLib.Cases_word 
  \\ REWRITE_TAC [WORD_EQ_ADD_RCANCEL,WORD_ADD_0]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [addr32_n2w,n2w_11]
  \\ `4 * n < 4294967296 /\ 4 * n' < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,EQ_MULT_LCANCEL]);

val addr32_EQ_0 = store_thm("addr32_EQ_0",
  ``!a. (addr32 a = 0w) = (a = 0w)``,
  REWRITE_TAC [SIMP_RULE std_ss [addr32_n2w] (Q.SPECL [`a`,`0w`] addr32_11)]);

val addr32_NEQ_addr32_LEMMA = prove(
  ``!a b. ~(addr32 a = addr32 b + 1w) /\ 
          ~(addr32 a = addr32 b + 2w) /\ 
          ~(addr32 a = addr32 b + 3w) /\ 
          ~(addr32 a + 1w = addr32 b + 2w) /\ 
          ~(addr32 a + 1w = addr32 b + 3w) /\ 
          ~(addr32 a + 2w = addr32 b + 3w)``,
  wordsLib.Cases_word \\ wordsLib.Cases_word
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [addr32_n2w,word_add_n2w,n2w_11]
  \\ REWRITE_TAC [GSYM (EVAL ``4 * 1073741824``)]
  \\ `0 < 4 /\ 0 < 1073741824` by EVAL_TAC
  \\ `4 * n' + 1 < 4 * 1073741824` by DECIDE_TAC
  \\ `4 * n' + 2 < 4 * 1073741824` by DECIDE_TAC
  \\ `4 * n' + 3 < 4 * 1073741824` by DECIDE_TAC
  \\ `4 * n + 1 < 4 * 1073741824` by DECIDE_TAC
  \\ `4 * n + 2 < 4 * 1073741824` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [GSYM MOD_COMMON_FACTOR,LESS_MOD]
  \\ ONCE_REWRITE_TAC [MULT_SYM]
  \\ `!k. (k * 4) MOD 4 = 0` by SIMP_TAC std_ss [MOD_EQ_0]
  \\ `!k. (k * 4 + 1) MOD 4 = 1` by SIMP_TAC std_ss [MOD_MULT]
  \\ `!k. (k * 4 + 2) MOD 4 = 2` by SIMP_TAC std_ss [MOD_MULT]
  \\ `!k. (k * 4 + 3) MOD 4 = 3` by SIMP_TAC std_ss [MOD_MULT]
  \\ METIS_TAC [EVAL ``0 = 1``,EVAL ``0 = 2``,EVAL ``0 = 3``,
                EVAL ``1 = 2``,EVAL ``1 = 3``,EVAL ``2 = 3``]);

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
  REWRITE_TAC [WORD_ADD_0,addr32_NEQ_addr32_LEMMA,GSYM addr32_NEQ_addr32_LEMMA]);  

val EXISTS_addr32 = store_thm("EXISTS_addr32",
  ``!p. ?a. (p = addr32 a + 0w) \/ (p = addr32 a + 1w) \/ 
            (p = addr32 a + 2w) \/ (p = addr32 a + 3w)``,
  wordsLib.Cases_word
  \\ STRIP_ASSUME_TAC (REWRITE_RULE [EVAL ``0 < 4``] (Q.SPECL [`n`,`4`] DA))
  \\ ASM_REWRITE_TAC [] \\ Q.EXISTS_TAC `n2w q` \\ REWRITE_TAC [addr32_n2w,word_add_n2w]
  \\ ONCE_REWRITE_TAC [DECIDE ``4 * n = n * 4``]
  \\ Cases_on `r` \\ ASM_REWRITE_TAC []
  \\ Cases_on `n'` \\ ASM_REWRITE_TAC [EVAL ``SUC 0``]
  \\ Cases_on `n''` \\ ASM_REWRITE_TAC [EVAL ``SUC (SUC 0)``]
  \\ Cases_on `n'` \\ ASM_REWRITE_TAC [EVAL ``SUC (SUC (SUC 0))``]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ `n'' < 0` by DECIDE_TAC \\ FULL_SIMP_TAC bool_ss [EVAL ``n < 0``]);

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
  SIMP_TAC std_ss [addr32_eq_0,EVAL ``w2n (0w:word2)``] \\ STRIP_TAC \\ EVAL_TAC);

val addr30_THM = store_thm("addr30_THM",
  ``!x. addr30 x = n2w (w2n x DIV 4)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,addr30_n2w]);

val addr32_THM = store_thm("addr32_THM",
  ``!x. addr32 x = n2w (4 * w2n x)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD,addr32_n2w]);

val aligned_THM = store_thm("aligned_THM",
  ``!p. aligned p = ?k. p = k * 4w``,
  Cases_word \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [n2w_and_3w,aligned_def] << [
    ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0 < 4``)))
    \\ REPEAT STRIP_TAC \\ ONCE_ASM_REWRITE_TAC []
    \\ REWRITE_TAC [GSYM word_add_n2w,GSYM word_mul_n2w]
    \\ Q.PAT_ASSUM `b /\ c` (fn th => ALL_TAC)
    \\ ASM_REWRITE_TAC [WORD_ADD_0] \\ METIS_TAC [],
    Q.UNDISCH_TAC `n2w n = k * 4w`
    \\ Q.SPEC_TAC (`k`,`k`) \\ Cases_word
    \\ ASM_SIMP_TAC bool_ss [word_mul_n2w,n2w_11,LESS_MOD]
    \\ REWRITE_TAC [EVAL ``dimword (:32)``]
    \\ REWRITE_TAC [GSYM (EVAL ``4 * 1073741824``)]
    \\ SIMP_TAC bool_ss 
        [MOD_MULT_MOD,DECIDE ``0 < 1073741824``,DECIDE ``0<4``,MOD_EQ_0]]);

val aligned_ADD = store_thm("aligned_ADD",
  ``!x y. aligned x /\ aligned y ==> aligned (x + y)``,
  REWRITE_TAC [aligned_THM] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [GSYM WORD_RIGHT_ADD_DISTRIB] \\ METIS_TAC []);
  

val _ = export_theory();
