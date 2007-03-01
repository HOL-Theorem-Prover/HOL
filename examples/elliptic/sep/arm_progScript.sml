(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/elliptic/arm";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
  loadPath := "/home/mom22/machine-code" :: !loadPath;
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open arm_evalTheory armTheory listTheory bsubstTheory pairTheory systemTheory fcpTheory bitTheory; 
open combinTheory
open set_sepLib

open set_sepTheory progTheory;


(*
  quietdec := false;
*)


val _ = new_theory "arm_prog";

val _ = Parse.hide "regs"

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;


(* ----------------------------------------------------------------------------- *)
(* Definition and lemmas for addr32 and addr30                                   *)
(* ----------------------------------------------------------------------------- *)

val word_app0_def = Define `word_app0 (x:'a word) = (w2w x << 1):('a + one) word`;
val word_cut1_def = Define `word_cut1 (x:('a + one) word) = ((word_len x >< 1) x) :'a word`;

val word_app0_n2w = prove(
  ``!n. word_app0 ((n2w n):'a word) = n2w (2 * n)``,
  REWRITE_TAC [word_app0_def,LSL_ONE,w2w_def,word_add_n2w,n2w_11,w2n_n2w,
    DECIDE ``n + n = 2 * n``,dimword_def,EVAL ``dimindex(:'a + one)``]
  \\ Cases_on `FINITE (UNIV :'a -> bool)` \\ ASM_REWRITE_TAC [finite_one] << [
    REWRITE_TAC [GSYM ADD1,EXP]
    \\ ASSUME_TAC (REWRITE_RULE [DECIDE ``1 = SUC 0``,GSYM LESS_EQ] DIMINDEX_GE_1)
    \\ ASM_SIMP_TAC std_ss [GSYM MOD_COMMON_FACTOR],
    ASSUME_TAC DIMINDEX_GE_1
    \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,EXP_ADD,EVAL ``2**1``]
    \\ ONCE_REWRITE_TAC [MULT_COMM] \\ SIMP_TAC std_ss [MOD_EQ_0]]);

val word_cut1_n2w = prove(
  ``FINITE (UNIV :'a -> bool) ==> 
    !n. (word_cut1 (n2w n)):'a word = n2w (n DIV 2)``,
  SIMP_TAC std_ss [word_cut1_def,word_extract_def,word_bits_n2w,
    REWRITE_RULE [finite_one] (EVAL ``dimindex (:'a + unit)``),word_len_def,
    w2w_def,n2w_11,w2n_n2w,dimword_def] \\ STRIP_TAC
  \\ `!n. (n + 1 < n) = F` by DECIDE_TAC
  \\ ASM_REWRITE_TAC [ADD_SUB,EVAL ``1-1``,MIN_DEF,EVAL ``1 < 0``]
  \\ REWRITE_TAC [GSYM ADD1,EXP] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ ASSUME_TAC (REWRITE_RULE [DECIDE ``1 = SUC 0``,GSYM LESS_EQ] DIMINDEX_GE_1)
  \\ ASM_SIMP_TAC std_ss [MOD_MULT_MOD,BITS_def,MOD_2EXP_def,DIV_2EXP_def]);

val word_cut1_app0 = prove(
  ``!w:'a word. FINITE (UNIV :'a -> bool) ==> (word_cut1 (word_app0 w) = w)``,  
  Cases_word \\ SIMP_TAC bool_ss [word_cut1_n2w,word_app0_n2w]
  \\ ONCE_REWRITE_TAC [MULT_COMM] \\ SIMP_TAC std_ss [MULT_DIV]);


val addr32_def = Define `addr32 (x:word30) = (w2w x << 2):word32`;
val addr30_def = Define `addr30 (x:word32) = ((31 >< 2) x):word30`;

val w2n_mod = prove(
  ``!x. (w2n (x:word30)) MOD (2**30) = w2n x``,
  ASSUME_TAC (INST_TYPE [``:'a``|->``:30``] w2n_lt)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []);

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

val addr32_and_3w = store_thm("addr32_and_3w",
  ``!x. (addr32 x) && 3w = 0w``,
  wordsLib.Cases_word
  \\ SIMP_TAC bool_ss [CART_EQ,word_0,word_and_def,FCP_BETA,addr32_n2w]
  \\ ONCE_REWRITE_TAC [(Q.INST_TYPE [`:'a`|->`:32`] word_index_n2w)]
  \\ SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [BIT_def,BITS_def,DIV_2EXP_def,MOD_2EXP_def]
  \\ REWRITE_TAC [DECIDE ``!i. SUC i - i = 1``,EVAL ``2**1``]
  \\ Cases_on `i` \\ EVAL_TAC \\ REWRITE_TAC [DIV_1] 
  \\ `0 < 2 /\ ~(0 = 1)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [DECIDE ``4*n = (2*n)*2``,MOD_EQ_0]
  \\ Cases_on `n'` \\ EVAL_TAC
  \\ ASM_SIMP_TAC bool_ss [DECIDE ``4*n = (2*n)*2``,MULT_DIV]
  \\ ONCE_REWRITE_TAC [MULT_COMM] \\ ASM_SIMP_TAC bool_ss [MOD_EQ_0]
  \\ REWRITE_TAC [EXP,MULT_ASSOC] \\ SIMP_TAC std_ss []
  \\ DISJ2_TAC \\ MATCH_MP_TAC (DECIDE ``(m = 0) ==> ~(m = 1)``)
  \\ `0 < 2 ** n''` by ASM_SIMP_TAC std_ss [ZERO_LT_EXP,EVAL ``0 < 2``]
  \\ `3 < 4 * 2 ** n''` by DECIDE_TAC 
  \\ ASM_SIMP_TAC bool_ss [LESS_DIV_EQ_ZERO] \\ SIMP_TAC std_ss [ZERO_MOD]);    

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
  wordsLib.Cases_word
  \\ STRIP_ASSUME_TAC (REWRITE_RULE [EVAL ``0 < 4``] (Q.SPECL [`n`,`4`] DA))
  \\ Cases_on `r` \\ ASM_REWRITE_TAC []
  THEN1 (REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n2w q` 
         \\ REWRITE_TAC [ADD_0,addr32_n2w] \\ METIS_TAC [MULT_COMM])
  \\ SIMP_TAC bool_ss [CART_EQ,word_0,word_and_def,FCP_BETA,addr32_n2w]
  \\ ONCE_REWRITE_TAC [(Q.INST_TYPE [`:'a`|->`:32`] word_index_n2w)] \\ SIMP_TAC bool_ss []
  \\ REWRITE_TAC [BIT_def,BITS_def,DIV_2EXP_def,MOD_2EXP_def]
  \\ REWRITE_TAC [DECIDE ``!i. SUC i - i = 1``,EVAL ``2**1``]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [] \\ Cases_on `n'` << [ 
    Q.PAT_ASSUM `!i.b` (ASSUME_TAC o REWRITE_RULE [EVAL ``0 < 32``] o Q.SPEC `0`)
    \\ FULL_SIMP_TAC bool_ss [EVAL ``~((3 DIV 2 ** 0) MOD 2 = 1)``,EVAL ``2**0``,DIV_1]
    \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``2*2``),MULT_ASSOC]
    \\ `SUC 0 < 2` by DECIDE_TAC \\ FULL_SIMP_TAC bool_ss [MOD_MULT,EVAL ``SUC 0``],
    Cases_on `n''` << [
      Q.PAT_ASSUM `!i.b` (ASSUME_TAC o REWRITE_RULE [EVAL ``1 < 32``] o Q.SPEC `1`)
      \\ FULL_SIMP_TAC bool_ss [EVAL ``~((3 DIV 2 ** 1) MOD 2 = 1)``,EVAL ``2**1``]
      \\ `q * 4 + 2 = (q * 2 + 1) * 2` by SIMP_TAC std_ss [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC]
      \\ FULL_SIMP_TAC bool_ss [EVAL ``SUC (SUC 0)``,EVAL ``0<2``,
            MULT_DIV,EVAL ``1 < 2``,MOD_MULT],        
      Cases_on `n'` << [
        Q.PAT_ASSUM `!i.b` (ASSUME_TAC o REWRITE_RULE [EVAL ``1 < 32``] o Q.SPEC `1`)
        \\ FULL_SIMP_TAC bool_ss [EVAL ``~((3 DIV 2 ** 1) MOD 2 = 1)``,EVAL ``2**1``]
        \\ `q * 4 + 3 = (q * 2 + 1) * 2 + 1` by 
             SIMP_TAC std_ss [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC,GSYM ADD_ASSOC]
        \\ `1 < 2` by DECIDE_TAC
        \\ FULL_SIMP_TAC bool_ss [DIV_MULT,EVAL ``SUC (SUC (SUC 0))``,MOD_MULT],
        FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC] \\ `~(n'' + 4 < 4)` by DECIDE_TAC]]]);

val add32_addr30 = store_thm("addr32_addr30",
  ``!x. (x && 3w = 0w) ==> (addr32 (addr30 x) = x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_addr30 \\ ASM_REWRITE_TAC [addr30_addr32]);

val addr32_ADD = store_thm ("addr32_ADD", 
  ``!v w. (addr32 (v + w)  = addr32 v + addr32 w)``,
  SIMP_TAC std_ss [addr32_def]
  \\ wordsLib.WORDS_TAC
  \\ SIMP_TAC arith_ss 
       [word_add_def, w2n_n2w, dimword_30, bitTheory.TIMES_2EXP_def,
        GSYM LEFT_ADD_DISTRIB, MOD_COMMON_FACTOR]);

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
  SRW_TAC [] [addr32_ADD,addr32_n2w]);

val ADD_LSL = store_thm("ADD_LSL",
  ``!v w n. (v + w) << n = (v << n) + (w << n)``,
  Induct_on `n` 
  \\ SIMP_TAC std_ss [SHIFT_ZERO,SUC_ONE_ADD,GSYM LSL_ADD,LSL_ONE]
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
  \\ `!k. (k * 4) MOD 4 = 0` by METIS_TAC [MOD_EQ_0]
  \\ `!k. (k * 4 + 1) MOD 4 = 1` by METIS_TAC [MOD_MULT,EVAL ``1 < 4``]
  \\ `!k. (k * 4 + 2) MOD 4 = 2` by METIS_TAC [MOD_MULT,EVAL ``2 < 4``]
  \\ `!k. (k * 4 + 3) MOD 4 = 3` by METIS_TAC [MOD_MULT,EVAL ``3 < 4``]
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
    (addr32 x - 0w  = addr32 (x - 0w)) /\
    (addr32 x - 4w  = addr32 (x - 1w)) /\ 
    (addr32 x - 8w  = addr32 (x - 2w)) /\ 
    (addr32 x - 12w = addr32 (x - 3w)) /\ 
    (addr32 x - 16w = addr32 (x - 4w)) /\ 
    (addr32 x - 20w = addr32 (x - 5w))``,    
  SIMP_TAC std_ss [addr32_ADD,addr32_SUB,addr32_n2w,WORD_ADD_0]);

val ADDRESS_ROTATE = store_thm("ADDRESS_ROTATE",
  ``!q:word32 z:word30. q #>> (8 * w2n ((1 >< 0) (addr32 z):word2)) = q``,
  SIMP_TAC std_ss [addr32_eq_0,EVAL ``w2n (0w:word2)``] \\ STRIP_TAC \\ EVAL_TAC);


(* ----------------------------------------------------------------------------- *)
(* Some abbreviating definitions for ARM                                         *)
(* ----------------------------------------------------------------------------- *)

val state_mode_def = Define `
  state_mode s = DECODE_MODE ((4 >< 0) (CPSR_READ s.psrs))`;

val reg_def = Define `
  reg r s = if r = 15w then s.registers r15 else REG_READ s.registers (state_mode s) r`;

val mem_def = Define `mem a s = s.memory a`;
val mem_byte_def = Define `mem_byte a s = GET_BYTE ((1 >< 0) a) (mem (addr30 a) s)`;

val statusN_def = Define `statusN s = CPSR_READ s.psrs %% 31`;
val statusZ_def = Define `statusZ s = CPSR_READ s.psrs %% 30`;
val statusC_def = Define `statusC s = CPSR_READ s.psrs %% 29`;
val statusV_def = Define `statusV s = CPSR_READ s.psrs %% 28`;
val status_def = Define `status s = (statusN s,statusZ s,statusC s,statusV s)`;

val set_status_def = Define `
  set_status (n,z,c,v) s = CPSR_WRITE s.psrs (SET_NZCV (n,z,c,v) (CPSR_READ s.psrs))`;

val status_THM = store_thm("status_THM",
  ``!s. status s = NZCV (CPSR_READ s.psrs)``,
  REWRITE_TAC [status_def,NZCV_def,statusN_def,statusZ_def,statusC_def,statusV_def]);

val concat8 =
  (SIMP_RULE (std_ss++SIZES_ss) [fcpTheory.index_sum] o
   Q.SPECL [`15`,`7`,`0`] o
   Q.INST_TYPE [`:'a` |-> `:32`, `:'b` |-> `:8`,
                `:'c` |-> `:8`, `:'d` |-> `:16`])
  wordsTheory.CONCAT_EXTRACT;

val concat16 =
  (SIMP_RULE (std_ss++SIZES_ss) [fcpTheory.index_sum] o
   Q.SPECL [`23`,`15`,`0`] o
   Q.INST_TYPE [`:'a` |-> `:32`, `:'b` |-> `:8`,
                `:'c` |-> `:16`, `:'d` |-> `:24`])
  wordsTheory.CONCAT_EXTRACT;

val concat24 =
  (SIMP_RULE (std_ss++SIZES_ss)
    [fcpTheory.index_sum,WORD_FULL_EXTRACT] o
   Q.SPECL [`31`,`23`,`0`] o
   Q.INST_TYPE [`:'a` |-> `:32`, `:'b` |-> `:8`,
                `:'c` |-> `:24`, `:'d` |-> `:32`])
  wordsTheory.CONCAT_EXTRACT;

val concat_bytes = prove(
  ``!w:word32. ((31 >< 24) w):word8 @@
              (((23 >< 16) w):word8 @@
               (((15 >< 8) w):word8 @@
                 ((7 >< 0) w):word8):word16):word24 = w``,
  SIMP_TAC std_ss [concat8,concat16,concat24]);

val mem_byte_addr32 = store_thm("mem_byte_addr32",
  ``!a s. (mem_byte (addr32 a + 3w) s = (31 >< 24) (mem a s)) /\ 
          (mem_byte (addr32 a + 2w) s = (23 >< 16) (mem a s)) /\ 
          (mem_byte (addr32 a + 1w) s = (15 ><  8) (mem a s)) /\ 
          (mem_byte (addr32 a + 0w) s = (7  ><  0) (mem a s))``,
  REWRITE_TAC [mem_byte_def,lower_addr32_ADD,addr30_addr32]
  \\ REWRITE_TAC [EVAL ``((1 >< 0) (0w:word32)):word2``] 
  \\ REWRITE_TAC [EVAL ``((1 >< 0) (1w:word32)):word2``] 
  \\ REWRITE_TAC [EVAL ``((1 >< 0) (2w:word32)):word2``] 
  \\ REWRITE_TAC [EVAL ``((1 >< 0) (3w:word32)):word2``] 
  \\ SRW_TAC [] [GET_BYTE_def,EVAL ``dimword (:2)``]);
    
val mem_byte_EQ_mem = store_thm("mem_byte_EQ_mem",
  ``!h a s.
      ((31 >< 24) h = mem_byte (addr32 a + 3w) s) /\
      ((23 >< 16) h = mem_byte (addr32 a + 2w) s) /\
      ((15 >< 8) h = mem_byte (addr32 a + 1w) s) /\
      ((7 >< 0) h = mem_byte (addr32 a + 0w) s) = (mem a s = h)``,
  REWRITE_TAC [mem_byte_addr32] \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC bool_ss []
  \\ STRIP_TAC \\ ONCE_REWRITE_TAC [GSYM concat_bytes] \\ ASM_REWRITE_TAC []);

val word2_CASES = prove(
  ``!w:word2. (w = 0w) \/ (w = 1w) \/ (w = 2w) \/ (w = 3w)``,
  wordsLib.Cases_word 
  \\ STRIP_ASSUME_TAC ((REWRITE_RULE [EVAL ``0 < 4``] o Q.SPECL [`n`,`4`]) DA)
  \\ ASM_SIMP_TAC (bool_ss++wordsLib.SIZES_ss) [n2w_11,EVAL ``2*2``]
  \\ ASM_SIMP_TAC std_ss [MOD_MULT]
  \\ Cases_on `r` \\ ASM_SIMP_TAC std_ss [ADD1] 
  \\ Cases_on `n'` \\ ASM_SIMP_TAC std_ss [ADD1] 
  \\ Cases_on `n''` \\ ASM_SIMP_TAC std_ss [ADD1] 
  \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [ADD1] 
  \\ DECIDE_TAC);

val GET_BYTE_0 = prove(
  ``(GET_BYTE 0w (SET_BYTE 1w x y) = GET_BYTE 0w y) /\
    (GET_BYTE 0w (SET_BYTE 2w x y) = GET_BYTE 0w y) /\
    (GET_BYTE 0w (SET_BYTE 3w x y) = GET_BYTE 0w y)``,    
  ONCE_REWRITE_TAC [CART_EQ]
  \\ SIMP_TAC (srw_ss()++wordsLib.SIZES_ss) [GET_BYTE_def,SET_BYTE_def,EVAL ``dimword (:bool)``,
    word_extract_def,word_bits_def,word_modify_def,FCP_BETA,w2w]
  \\ REPEAT STRIP_TAC \\ `i < 32` by DECIDE_TAC \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ CCONTR_TAC \\ DECIDE_TAC);

val GET_BYTE_1 = prove(
  ``(GET_BYTE 1w (SET_BYTE 0w x y) = GET_BYTE 1w y) /\
    (GET_BYTE 1w (SET_BYTE 2w x y) = GET_BYTE 1w y) /\
    (GET_BYTE 1w (SET_BYTE 3w x y) = GET_BYTE 1w y)``,    
  ONCE_REWRITE_TAC [CART_EQ]
  \\ SIMP_TAC (srw_ss()++wordsLib.SIZES_ss) [GET_BYTE_def,SET_BYTE_def,EVAL ``dimword (:bool)``,
    word_extract_def,word_bits_def,word_modify_def,FCP_BETA,w2w]
  \\ REPEAT STRIP_TAC \\ `i < 32` by DECIDE_TAC \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ `i + 8 < 32` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] << [
    CCONTR_TAC \\ DECIDE_TAC,
    DISJ2_TAC \\ DISJ1_TAC \\ DECIDE_TAC,
    CCONTR_TAC \\ DECIDE_TAC,
    DISJ2_TAC \\ DISJ1_TAC \\ DECIDE_TAC,
    CCONTR_TAC \\ DECIDE_TAC,
    DISJ2_TAC \\ DISJ1_TAC \\ DECIDE_TAC]);

val GET_BYTE_2 = prove(
  ``(GET_BYTE 2w (SET_BYTE 0w x y) = GET_BYTE 2w y) /\
    (GET_BYTE 2w (SET_BYTE 1w x y) = GET_BYTE 2w y) /\
    (GET_BYTE 2w (SET_BYTE 3w x y) = GET_BYTE 2w y)``,    
  ONCE_REWRITE_TAC [CART_EQ]
  \\ SIMP_TAC (srw_ss()++wordsLib.SIZES_ss) [GET_BYTE_def,SET_BYTE_def,EVAL ``dimword (:bool)``,
    word_extract_def,word_bits_def,word_modify_def,FCP_BETA,w2w]
  \\ REPEAT STRIP_TAC \\ `i < 32` by DECIDE_TAC \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ `i + 16 < 32` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] << [
    CCONTR_TAC \\ DECIDE_TAC,
    DISJ2_TAC \\ DISJ2_TAC \\ DISJ1_TAC \\ DECIDE_TAC,
    CCONTR_TAC \\ DECIDE_TAC,
    DISJ2_TAC \\ DISJ2_TAC \\ DISJ1_TAC \\ DECIDE_TAC,
    CCONTR_TAC \\ DECIDE_TAC,
    DISJ2_TAC \\ DISJ2_TAC \\ DISJ1_TAC \\ DECIDE_TAC]);

val GET_BYTE_3 = prove(
  ``(GET_BYTE 3w (SET_BYTE 0w x y) = GET_BYTE 3w y) /\
    (GET_BYTE 3w (SET_BYTE 1w x y) = GET_BYTE 3w y) /\
    (GET_BYTE 3w (SET_BYTE 2w x y) = GET_BYTE 3w y)``,    
  ONCE_REWRITE_TAC [CART_EQ]
  \\ SIMP_TAC (srw_ss()++wordsLib.SIZES_ss) [GET_BYTE_def,SET_BYTE_def,EVAL ``dimword (:bool)``,
    word_extract_def,word_bits_def,word_modify_def,FCP_BETA,w2w]
  \\ REPEAT STRIP_TAC \\ `i < 32` by DECIDE_TAC \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ `i + 24 < 32` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ CCONTR_TAC \\ DECIDE_TAC);

val GET_BYTE_SET_BYTE = store_thm("GET_BYTE_SET_BYTE",
  ``!n x y. GET_BYTE n (SET_BYTE n x y) = x``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` word2_CASES)
  \\ FULL_SIMP_TAC (srw_ss()) [GET_BYTE_def,SET_BYTE_def]
  \\ ONCE_REWRITE_TAC [CART_EQ]
  \\ SIMP_TAC (srw_ss()++wordsLib.SIZES_ss) [GET_BYTE_def,SET_BYTE_def,EVAL ``dimword (:bool)``,
    word_extract_def,word_bits_def,word_modify_def,FCP_BETA,w2w]
  \\ REPEAT STRIP_TAC \\ `i < 32` by DECIDE_TAC \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA] \\ REPEAT STRIP_TAC << [
    `i <= 7 /\ i <= 31` by DECIDE_TAC \\ ASM_REWRITE_TAC []
    \\ Cases_on `x %% i` \\ ASM_REWRITE_TAC []
    \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC,
    `i + 8 < 32` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA] \\ REPEAT STRIP_TAC
    \\ `i + 8 <= 15 /\ i + 8 <= 31` by DECIDE_TAC \\ ASM_REWRITE_TAC []
    \\ Cases_on `x %% i` \\ ASM_REWRITE_TAC []
    \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC,    
    `i + 16 < 32` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA] \\ REPEAT STRIP_TAC
    \\ `i + 16 <= 23 /\ i + 16 <= 31` by DECIDE_TAC \\ ASM_REWRITE_TAC []
    \\ Cases_on `x %% i` \\ ASM_REWRITE_TAC []
    \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC,
    `i + 24 < 32` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [FCP_BETA] \\ REPEAT STRIP_TAC
    \\ `i + 24 <= 31` by DECIDE_TAC \\ ASM_REWRITE_TAC []
    \\ Cases_on `x %% i` \\ ASM_REWRITE_TAC []
    \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC]);

val GET_BYTE_SET_BYTE_NEQ = store_thm("GET_BYTE_SET_BYTE_NEQ",
  ``!n m x y. ~(n = m) ==> (GET_BYTE n (SET_BYTE m x y) = GET_BYTE n y)``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `m` word2_CASES)
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` word2_CASES)
  \\ FULL_SIMP_TAC bool_ss [GET_BYTE_0,GET_BYTE_1,GET_BYTE_2,GET_BYTE_3]);



(* ----------------------------------------------------------------------------- *)
(* The ARM set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  ARMel =  Reg of word4 => word32
         | Mem of word32 => word8  
         | Status of bool # bool # bool # bool
         | Undef of bool
         | Rest of 'a arm_sys_state`;

val ARMel_11 = DB.fetch "-" "ARMel_11";
val ARMel_distinct = DB.fetch "-" "ARMel_distinct";

val _ = Parse.type_abbrev("ARMset",``:'a ARMel set``);

val ARMel_type = ``:'a ARMel``;


(* ----------------------------------------------------------------------------- *)
(* Converting from ARM to ARMset                                                 *)
(* ----------------------------------------------------------------------------- *)

(* Erasing registers *)

val REG_OWRT_def = Define `
  (REG_OWRT 0 regs m = regs) /\ 
  (REG_OWRT (SUC n) regs m = REG_OWRT n (REG_WRITE regs m (n2w n) 0w) m)`;

val REG_OWRT_LEMMA = prove(
  ``!n k regs. 
       w2n k < n ==> 
        (REG_OWRT n (REG_WRITE regs m k x) m = REG_OWRT n regs m)``,
  Induct_on `n` << [
    `!n. ~(n<0)` by DECIDE_TAC
    \\ ASM_REWRITE_TAC [REG_OWRT_def],
    REPEAT STRIP_TAC
    \\ REWRITE_TAC [REG_OWRT_def]
    \\ Cases_on `n = w2n k` << [
      ASM_REWRITE_TAC [n2w_w2n,REG_WRITE_WRITE],
      `w2n k < n` by DECIDE_TAC
      \\ Cases_on `n2w n = k` << [
         ASM_REWRITE_TAC [REG_WRITE_WRITE],
         METIS_TAC [REG_WRITE_WRITE_COMM]]]]);
    
val REG_OWRT_WRITE = prove(
  ``!regs m k x. REG_OWRT 16 (REG_WRITE regs m k x) m = REG_OWRT 16 regs m``,
  ASSUME_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:4``] w2n_lt))
  \\ METIS_TAC [REG_OWRT_LEMMA]);

val REG_OWRT_WRITEL = prove(
  ``!xs regs m. REG_OWRT 16 (REG_WRITEL regs m xs) m = REG_OWRT 16 regs m``,
  Induct \\ REWRITE_TAC [REG_WRITEL_def,REG_OWRT_WRITE] \\ Cases_on `h`
  \\ ASM_REWRITE_TAC [REG_WRITEL_def,REG_OWRT_WRITE]);

val REG_OWRT_WRITE_PC = prove(
  ``!regs m. REG_OWRT 16 (REG_WRITE regs usr 15w z) m = REG_OWRT 16 regs m``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [REG_OWRT_def,GSYM (EVAL ``SUC 15``)]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x m = f y m)``)
  \\ SIMP_TAC std_ss [REG_WRITE_def,mode_reg2num_def,EVAL ``w2n (15w:word4)``]
  \\ SIMP_TAC std_ss [LET_DEF,num2register_thm]
  \\ SRW_TAC [] [FUN_EQ_THM,UPDATE_def]);
    
val REG_OWRT_INC_PC = prove(
  ``!regs m. REG_OWRT 16 (INC_PC regs) m = REG_OWRT 16 regs m``,
  REWRITE_TAC [INC_PC,REG_OWRT_WRITE_PC]);

val REG_OWRT_ALL = save_thm("REG_OWRT_ALL",
  GEN_ALL (CONJ (SPEC_ALL REG_OWRT_INC_PC) 
                (CONJ (SPEC_ALL REG_OWRT_WRITE_PC) 
                      (CONJ (SPEC_ALL REG_OWRT_WRITE) 
                            (SPEC_ALL REG_OWRT_WRITEL)))));

val REG_OWRT_ALL_EQ_REG_WRITEL = prove( 
  ``REG_OWRT 16 regs m = 
    REG_WRITEL regs m [(0w,0w);(1w,0w);(2w,0w);(3w,0w);(4w,0w);(5w,0w);(6w,0w);
                       (7w,0w);(8w,0w);(9w,0w);(10w,0w);(11w,0w);(12w,0w);(13w,0w);
                       (14w,0w);(15w,0w)]``,
  REWRITE_TAC [REG_WRITEL_def]
  \\ REWRITE_TAC [GSYM (EVAL ``SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 
                              (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))))))``)]
  \\ REWRITE_TAC [REG_OWRT_def]
  \\ SIMP_TAC std_ss []);

val owrt_visible_regs_def = Define `
  owrt_visible_regs s = REG_OWRT 16 s.registers (state_mode s)`;

val owrt_visible_def = Define `
  owrt_visible s = <| registers := owrt_visible_regs s;
                      psrs := set_status (F,F,F,F) s;
                      memory := (\a. 0w); 
                      undefined := F;
                      cp_state := s.cp_state |>`;


(* Main definition *)

val arm2set_def = Define `
  arm2set s =
    { Reg a (reg a s) |a| T } UNION
    { Mem a (mem_byte a s) |a| T } UNION
    { Status (status s); Undef s.undefined; Rest (owrt_visible s) }`;


(* ----------------------------------------------------------------------------- *)
(* Converting from ARMset to ARM                                                 *)
(* ----------------------------------------------------------------------------- *)

val ARMsets_def = Define `ARMsets = { arm2set s |s| T } :'a ARMel set set`;

val set2undef_def = Define `
  set2undef set = @u. Undef u IN set`;

val set2psrs_def = Define `
  set2psrs set = set_status (@s. Status s IN set) (@r. Rest r IN set)`;

val set2mem_byte_def = Define `
  set2mem_byte set = @f. !a x. Mem a x IN set ==> (f a = x)`;

val set2mem_def = Define `
  set2mem set = 
    \a. set2mem_byte set (addr32 a + 3w) @@ 
        (set2mem_byte set (addr32 a + 2w) @@ 
        (set2mem_byte set (addr32 a + 1w) @@ 
        (set2mem_byte set (addr32 a + 0w)):word8):word16):word24`;

val set2mode_def = Define `
  set2mode set = state_mode (@r. Rest r IN set)`;

val set2reg_def = Define `
  set2reg r set = @x. Reg r x IN set`;

val set2regs_def = Define `
  set2regs set = 
    REG_WRITEL (@r. Rest r IN set).registers (set2mode set)
      (MAP (\x. (x,set2reg x set)) 
        [15w;14w;13w;12w;11w;10w;9w;8w;7w;6w;5w;4w;3w;2w;1w;0w])`;

val set2cp_state_def = Define `
  set2cp_state set = (@r. Rest r IN set).cp_state`;

val set2arm_def = Define `
  set2arm set = <| registers := set2regs set;
                   psrs := set2psrs set;
                   memory := set2mem set; 
                   undefined := set2undef set; 
                   cp_state := set2cp_state set |>`;

val set2undef_arm2set = prove(
  ``!s. set2undef (arm2set s) = s.undefined``,
  SRW_TAC [] [set2undef_def,arm2set_def]);

val set2mem_arm2set = prove(
  ``!s. set2mem (arm2set s) = s.memory``,
  SRW_TAC [] [set2mem_byte_def,arm2set_def,set2mem_def]
  \\ ONCE_REWRITE_TAC [GSYM (BETA_CONV ``(\a. mem_byte a s) a``)]
  \\ REWRITE_TAC [GSYM FUN_EQ_THM,SELECT_REFL]
  \\ SIMP_TAC std_ss [mem_byte_addr32,concat_bytes,mem_def]
  \\ SIMP_TAC std_ss [FUN_EQ_THM]);

val set2psrs_arm2set = prove(
  ``!s. set2psrs (arm2set s) = s.psrs``,
  SRW_TAC [] [set2psrs_def,arm2set_def]
  \\ SRW_TAC [] [set_status_def,status_def,statusN_def,
                 statusZ_def,statusC_def,statusV_def,owrt_visible_def]
  \\ CONV_TAC arm_rulesLib.PSR_CONV
  \\ REWRITE_TAC []);

val set2mode_arm2set = prove(
  ``!s. set2mode (arm2set s) = state_mode s``,
  SRW_TAC [] [set2mode_def,arm2set_def]
  \\ SRW_TAC [] [state_mode_def,owrt_visible_def,set_status_def]
  \\ CONV_TAC arm_rulesLib.PSR_CONV
  \\ REWRITE_TAC []);
  
val set2cp_regs_arm2set = prove(
  ``!s. set2cp_state (arm2set s) = s.cp_state``,
  SRW_TAC [] [set2cp_state_def,arm2set_def,owrt_visible_def]);
  
val REG_WRITE_ELIM = prove(
  ``!s x. REG_WRITE s.registers (state_mode s) x (reg x s) = s.registers``,
  REPEAT STRIP_TAC
  \\ Cases_on `x = 15w`
  \\ ASM_SIMP_TAC std_ss [reg_def] << [
    SRW_TAC [] [REG_WRITE_def,mode_reg2num_def,EVAL ``w2n (15w:word4)``]
    \\ Q.UNABBREV_TAC `n`
    \\ SRW_TAC [] [UPDATE_def,FUN_EQ_THM,num2register_thm],
    ASM_REWRITE_TAC [REG_READ_def]
    \\ ASM_REWRITE_TAC [REG_WRITE_def,UPDATE_def]
    \\ SRW_TAC [] [FUN_EQ_THM]]);

fun MK_WRITE_WRITE_COMM x y =
  let 
    val th = SPEC_ALL REG_WRITE_WRITE_COMM
    val th = Q.INST [`n1`|->y,`n2`|->x] th
    val th = CONV_RULE (RATOR_CONV EVAL) th
  in
    BETA_RULE th
  end;

fun MK_WRITE_WRITEs [] = []
  | MK_WRITE_WRITEs (x::xs) =
    let
      val rw = map (fn y => MK_WRITE_WRITE_COMM x y) xs 
    in
      rw @ MK_WRITE_WRITEs xs
    end;

val WRITE_WRITE_ss = 
  rewrites(MK_WRITE_WRITEs 
           [`0w`,`1w`,`2w`,`3w`,`4w`,`5w`,`6w`,`7w`,`8w`,`9w`,`10w`,`11w`,`12w`,`13w`,`14w`,`15w`]);

val set2regs_arm2set_LEMMA = prove(
  ``REG_WRITEL
      (REG_WRITEL s.registers (state_mode s)
         [(0w,0w); (1w,0w); (2w,0w); (3w,0w); (4w,0w); (5w,0w); (6w,0w);
          (7w,0w); (8w,0w); (9w,0w); (10w,0w); (11w,0w); (12w,0w); (13w,0w);
          (14w,0w); (15w,0w)]) (state_mode s)
      [(15w,reg 15w s); (14w,reg 14w s); (13w,reg 13w s); (12w,reg 12w s);
       (11w,reg 11w s); (10w,reg 10w s); (9w,reg 9w s); (8w,reg 8w s);
       (7w,reg 7w s); (6w,reg 6w s); (5w,reg 5w s); (4w,reg 4w s);
       (3w,reg 3w s); (2w,reg 2w s); (1w,reg 1w s); (0w,reg 0w s)] =
    REG_WRITEL s.registers (state_mode s)
      [(0w,reg 0w s); (1w,reg 1w s); (2w,reg 2w s); (3w,reg 3w s);
       (4w,reg 4w s); (5w,reg 5w s); (6w,reg 6w s); (7w,reg 7w s);
       (8w,reg 8w s); (9w,reg 9w s); (10w,reg 10w s); (11w,reg 11w s);
       (12w,reg 12w s); (13w,reg 13w s); (14w,reg 14w s); (15w,reg 15w s)]``,
  SIMP_TAC (bool_ss++WRITE_WRITE_ss) [REG_WRITE_WRITE,REG_WRITEL_def]);
  
val set2regs_arm2set = prove(
  ``!s. set2regs (arm2set s) = s.registers``,
  SRW_TAC [] [set2regs_def,set2mode_arm2set]
  \\ SRW_TAC [] [arm2set_def,owrt_visible_regs_def,owrt_visible_def,set2reg_def]
  \\ REWRITE_TAC [REG_OWRT_ALL_EQ_REG_WRITEL]
  \\ REWRITE_TAC [set2regs_arm2set_LEMMA] (* alternatively use: REG_WRITEL_CONV *)
  \\ REWRITE_TAC [REG_WRITEL_def,REG_WRITE_ELIM]);



(* lemmas *)

val set2arm_arm2set = store_thm("set2arm_arm2set",
  ``!s. set2arm (arm2set s) = s``,
  SRW_TAC [] [set2arm_def,set2undef_arm2set,set2mem_arm2set,
              set2regs_arm2set,set2psrs_arm2set,set2cp_regs_arm2set]
  \\ SRW_TAC [] [arm_sys_state_component_equality]);

val arm2set_set2arm = store_thm("arm2set_set2arm",
  ``!s::ARMsets. arm2set (set2arm s) = s``,
  SRW_TAC [] [RES_FORALL,ARMsets_def] \\ REWRITE_TAC [set2arm_arm2set]);



(* ----------------------------------------------------------------------------- *)
(* Definitions of partial arm2set                                                *)
(* ----------------------------------------------------------------------------- *)

val arm2set'_def = Define `
  arm2set' (rs,ns,st,ud,rt) s =
    { Reg a (reg a s) | a IN rs } UNION
    { Mem a (mem_byte a s) | a IN ns } UNION
    (if st then { Status (status s) } else {}) UNION
    (if ud then { Undef s.undefined } else {}) UNION
    (if rt then { Rest (owrt_visible s) } else {})`;

val arm2set''_def = Define `
  arm2set'' x s = arm2set s DIFF arm2set' x s`;


(* lemmas with INSERT, IN and DELETE ------------------------------------------- *)

val PUSH_IN_INTO_IF = prove(
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``,
  METIS_TAC []);

val IN_arm2set = store_thm("IN_arm2set",``
  (!r x s. Reg r x IN (arm2set s) = (x = reg r s)) /\
  (!p x s. Mem p x IN (arm2set s) = (x = mem_byte p s)) /\
  (!x s. Status x IN (arm2set s) = (x = status s)) /\
  (!x s. Undef x IN (arm2set s) = (x = s.undefined)) /\
  (!x s. Rest x IN (arm2set s) = (x = owrt_visible s))``,
  SRW_TAC [] [arm2set_def,IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]);

val IN_arm2set' = store_thm("IN_arm2set'",``
  (!r x s. Reg r x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = reg r s) /\ (r IN rs))) /\
  (!p x s. Mem p x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = mem_byte p s) /\ (p IN ns))) /\
  (!x s. Status x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = status s) /\ st)) /\
  (!x s. Undef x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = s.undefined) /\ ud)) /\
  (!x s. Rest x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = owrt_visible s) /\ rt))``,
  SRW_TAC [] [arm2set'_def,IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,
              PUSH_IN_INTO_IF] \\ METIS_TAC []);

val IN_arm2set'' = store_thm("IN_arm2set''",``
  (!r x s. Reg r x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = reg r s) /\ ~(r IN rs))) /\
  (!p x s. Mem p x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = mem_byte p s) /\ ~(p IN ns))) /\
  (!x s. Status x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = status s) /\ ~st)) /\
  (!x s. Undef x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = s.undefined) /\ ~ud)) /\
  (!x s. Rest x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = owrt_visible s) /\ ~rt))``,
  SRW_TAC [] [arm2set'_def,arm2set''_def,arm2set_def,IN_UNION,GSPECIFICATION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

val INSERT_arm2set' = store_thm("INSERT_arm2set'",``
  (!r x s. arm2set' (r INSERT rs,ns,st,ud,rt) s = 
           Reg r (reg r s) INSERT arm2set' (rs,ns,st,ud,rt) s) /\
  (!p x s. arm2set' (rs,p INSERT ns,st,ud,rt) s = 
           Mem p (mem_byte p s) INSERT arm2set' (rs,ns,st,ud,rt) s) /\
  (!x s. arm2set' (rs,ns,T,ud,rt) s = 
           Status (status s) INSERT arm2set' (rs,ns,F,ud,rt) s) /\
  (!x s. arm2set' (rs,ns,st,T,rt) s = 
           Undef (s.undefined) INSERT arm2set' (rs,ns,st,F,rt) s) /\
  (!x s. arm2set' (rs,ns,st,ud,T) s = 
           Rest (owrt_visible s) INSERT arm2set' (rs,ns,st,ud,F) s) /\
  (!s. arm2set' ({},{},F,F,F) s = {})``,
  SRW_TAC [] [EXTENSION] \\ Cases_on `x` \\  SRW_TAC [] [IN_arm2set']
  \\ METIS_TAC []);

val DELETE_arm2set' = store_thm("DELETE_arm2set'",``
  (!r p s. (arm2set' (rs,ns,st,ud,rt) s) DELETE Reg r (reg r s) = 
           (arm2set' (rs DELETE r,ns,st,ud,rt) s)) /\
  (!r p s. (arm2set' (rs,ns,st,ud,rt) s) DELETE Mem p (mem_byte p s) = 
           (arm2set' (rs,ns DELETE p,st,ud,rt) s)) /\
  (!x s.   (arm2set' (rs,ns,st,ud,rt) s) DELETE Status (status s) = 
            arm2set' (rs,ns,F,ud,rt) s) /\
  (!x s.   (arm2set' (rs,ns,st,ud,rt) s) DELETE Undef (s.undefined) = 
            arm2set' (rs,ns,st,F,rt) s) /\
  (!x s.   (arm2set' (rs,ns,st,ud,rt) s) DELETE Rest (owrt_visible s) = 
            arm2set' (rs,ns,st,ud,F) s)``,
  SRW_TAC [] [arm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val arm2set''_THM = prove(
  ``arm2set'' (rs,ns,st,ud,rt) s =
    {Reg a (reg a s) |a| ~(a IN rs)} UNION 
    {Mem a (mem_byte a s) |a| ~(a IN ns)} UNION
    (if ~ st then {Status (status s)} else {}) UNION
    (if ~ ud then {Undef s.undefined} else {}) UNION
    (if ~ rt then {Rest (owrt_visible s)} else {})``,
  REWRITE_TAC [arm2set''_def,arm2set'_def,EXTENSION,arm2set_def]
  \\ FULL_SIMP_TAC bool_ss 
        [IN_UNION,IN_DIFF,IN_INSERT,NOT_IN_EMPTY,GSPECIFICATION,PAIR_EQ]
  \\ STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [
    METIS_TAC [],
    METIS_TAC [],
    Cases_on `st` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    Cases_on `ud` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    Cases_on `rt` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    `!k. ?a. x = Reg a (reg a s)` by METIS_TAC []
    \\ SRW_TAC [] [] \\ METIS_TAC [],    
    `!k. ?a. x = Mem a (mem_byte a s)` by METIS_TAC []
    \\ SRW_TAC [] [] \\ METIS_TAC [],
    Cases_on `st` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] [],
    Cases_on `ud` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] [],    
    Cases_on `rt` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] []]);

val arm2set''_EQ = store_thm ("arm2set''_EQ", 
  ``!rs ns st ud rt s s'.
      (arm2set'' (rs,ns,st,ud,rt) s = arm2set'' (rs,ns,st,ud,rt) s') = 
	(!r. (~(r IN rs)) ==> (reg r s = reg r s')) /\
	(!p. (~(p IN ns)) ==> (mem_byte p s = mem_byte p s')) /\
	((~st) ==> (status s = status s')) /\
	((~ud) ==> (s.undefined = s'.undefined)) /\
	((~rt) ==> (owrt_visible s = owrt_visible s'))``,
  SIMP_TAC std_ss [arm2set''_THM, EXTENSION, IN_UNION, IN_DIFF, IN_INSERT, 
    NOT_IN_EMPTY, GSPECIFICATION, 
    prove (``x IN (if c then S1 else S2) = if c then x IN S1 else x IN S2``, PROVE_TAC[])] 
  \\ REPEAT GEN_TAC \\ EQ_TAC << [
    REPEAT STRIP_TAC \\ CCONTR_TAC \\ Q.PAT_ASSUM `!x. P x` MP_TAC \\ SIMP_TAC std_ss [] << [
      Q.EXISTS_TAC `Reg r (reg r s)` 
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q.EXISTS_TAC `Mem p (mem_byte p s)`
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q.EXISTS_TAC `Status (status s)`
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q.EXISTS_TAC `Undef s.undefined`
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q.EXISTS_TAC `Rest (owrt_visible s)` 
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct]],
    SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC 
    \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [ARMel_11, ARMel_distinct]]);


(* lemmas with SPLIT and STAR -------------------------------------------------- *)
 
val SPLIT_DIFF = prove(
  ``!s u. u SUBSET s ==> SPLIT s (u,s DIFF u)``,
  SRW_TAC [] [SPLIT_def,SUBSET_DEF,EXTENSION,IN_UNION,IN_DIFF,DISJOINT_DEF] 
  \\ METIS_TAC []);

val arm2set'_SUBSET_arm2set = prove(
  ``!x s. arm2set' x s SUBSET arm2set s``,
  REWRITE_TAC [SUBSET_DEF]
  \\ STRIP_TAC 
  \\ `?rs ms st ud rt. x = (rs,ms,st,ud,rt)` by METIS_TAC [PAIR]  
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [arm2set'_def,arm2set_def,SUBSET_DEF]);  
  
val SPLIT_arm2set = prove(
  ``!x s. SPLIT (arm2set s) (arm2set' x s, arm2set'' x s)``,
  METIS_TAC [arm2set''_def,SPLIT_DIFF,arm2set'_SUBSET_arm2set]);

val SUBSET_arm2set = prove(
  ``!u s. u SUBSET arm2set s = ?y. u = arm2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [arm2set'_SUBSET_arm2set]
  \\ Q.EXISTS_TAC `
       ({ a |a| ?x. Reg a x IN u },{ a |a| ?x. Mem a x IN u },
        (?x. Status x IN u),(?x. Undef x IN u),(?x. Rest x IN u))`
  \\ FULL_SIMP_TAC std_ss [arm2set'_def,arm2set_def,EXTENSION,SUBSET_DEF,
                           IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]  
  \\ STRIP_TAC
  \\ `!g y. x IN (if g then {y} else {}) = g /\ (x = y)` by METIS_TAC [NOT_IN_EMPTY,IN_INSERT]
  \\ ASM_REWRITE_TAC []
  \\ PAT_ASSUM ``!g y. x`` (fn th => ALL_TAC)
  \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a. b:bool`` (IMP_RES_TAC)
  \\ FULL_SIMP_TAC std_ss [ARMel_11,ARMel_distinct]);

val SPLIT_arm2set_EXISTS = prove(
  ``!s u v. SPLIT (arm2set s) (u,v) = ?y. (u = arm2set' y s) /\ (v = arm2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [SPLIT_arm2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,arm2set'_def,arm2set''_def]
  \\ `u SUBSET (arm2set s)` by 
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_arm2set]
  \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]  
  \\ METIS_TAC []);

val STAR_arm2set = prove(
  ``!P Q s. (P * Q) (arm2set s) = ?y. P (arm2set' y s) /\ Q (arm2set'' y s)``,
  SIMP_TAC std_ss [STAR_def,SPLIT_arm2set_EXISTS]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `y` \\ METIS_TAC [])
  \\ METIS_TAC []);


(* lemmas with equality -------------------------------------------------------- *)

val arm2set'_EQ_arm2set' = prove(
  ``!y y' s s'. (arm2set' y' s' = arm2set' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st ud rt. y = (r,m,st,ud,rt)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud' rt'. y' = (r',m',st',ud',rt')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] << [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Reg a x IN arm2set' y s) = (?x. Reg a x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Mem a x IN arm2set' y s) = (?x. Mem a x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `~((?x. Status x IN arm2set' y s) = (?x. Status x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `~((?x. Undef x IN arm2set' y s) = (?x. Undef x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `~((?x. Rest x IN arm2set' y s) = (?x. Rest x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC []]);

val arm2set''_EQ_arm2set'' = prove(
  ``!y y' s s'. (arm2set'' y' s' = arm2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st ud rt. y = (r,m,st,ud,rt)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud' rt'. y' = (r',m',st',ud',rt')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] << [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Reg a x IN arm2set'' y s) = (?x. Reg a x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Mem a x IN arm2set'' y s) = (?x. Mem a x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `~((?x. Status x IN arm2set'' y s) = (?x. Status x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `~((?x. Undef x IN arm2set'' y s) = (?x. Undef x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `~((?x. Rest x IN arm2set'' y s) = (?x. Rest x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC []]);

val arm2set'_11 = prove(
  ``!x y (s: 'a arm_sys_state). (arm2set' x s = arm2set' y s) ==> (x = y)``,
  REPEAT STRIP_TAC
  \\ `?r m st ud rt. x = (r,m,st,ud,rt)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud' rt'. y = (r',m',st',ud',rt')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [arm2set'_def,PAIR_EQ,EXTENSION]  
  \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [] << [
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC 
     `Reg x' (reg x' (s: 'a arm_sys_state))`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC 
     `Mem x' (mem_byte x' (s: 'a arm_sys_state))`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC 
     `Status (status (s: 'a arm_sys_state))`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC 
     `Undef ((s: 'a arm_sys_state).undefined)`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC 
     `Rest (owrt_visible (s: 'a arm_sys_state))`)]
  \\ FULL_SIMP_TAC (srw_ss()) [IN_UNION,GSPECIFICATION,NOT_IN_EMPTY,
       IN_INSERT,PUSH_IN_INTO_IF]);


(* ----------------------------------------------------------------------------- *)
(* Describe the subsets of arm2set                                               *)
(* ----------------------------------------------------------------------------- *)

val WD_Reg_def    = Define `WD_Reg s = !a x y. Reg a x IN s /\ Reg a y IN s ==> (x = y)`;
val WD_Mem_def    = Define `WD_Mem s = !a x y. Mem a x IN s /\ Mem a y IN s ==> (x = y)`;
val WD_Status_def = Define `WD_Status s = !x y. Status x IN s /\ Status y IN s ==> (x = y)`;
val WD_Undef_def  = Define `WD_Undef s = !x y. Undef x IN s /\ Undef y IN s ==> (x = y)`;
val WD_Rest_def   = Define `WD_Rest s = !x y. Rest x IN s /\ Rest y IN s ==> (x = y)`;
val WD_ARM_def = Define `WD_ARM s = WD_Reg s /\ WD_Mem s /\ WD_Status s /\ WD_Undef s /\ WD_Rest s`;

fun WD_TAC x y = 
  SRW_TAC [] [WD_ARM_def,arm2set_def,SUBSET_DEF,
              WD_Reg_def,WD_Mem_def,WD_Status_def,WD_Undef_def,WD_Rest_def]
  \\ PAT_ASSUM ``!x:'a. b`` 
     (fn th => (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC x) th \\ 
               (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC y) th)
  \\ SRW_TAC [] [];

val WD_Reg = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Reg t``, WD_TAC `Reg a x` `Reg a y`);

val WD_Mem = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Mem t``, WD_TAC `Mem a x` `Mem a y`);

val WD_Status = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Status t``, WD_TAC `Status x` `Status y`);

val WD_Undef = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Undef t``, WD_TAC `Undef x` `Undef y`);

val WD_Rest = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Rest t``, WD_TAC `Rest x` `Rest y`);

val WD_ARM_THM = store_thm("WD_ARM_THM",
  ``!t s. t SUBSET (arm2set s) ==> WD_ARM t``,
  METIS_TAC [WD_Reg,WD_Mem,WD_Status,WD_Undef,WD_Rest,WD_ARM_def]);

val WD_ARM_SUBSET = store_thm("WD_ARM_SUBSET",
  ``!t s. (WD_ARM s /\ t SUBSET s) ==> WD_ARM t``,  
  SIMP_TAC std_ss [WD_ARM_def, WD_Reg_def, WD_Mem_def, WD_Status_def,
                   WD_Undef_def, WD_Rest_def, SUBSET_DEF] \\ METIS_TAC []);

val WD_ARM_DELETE = store_thm("WD_ARM_DELETE",
  ``!s e. WD_ARM s ==> WD_ARM (s DELETE e)``,
  REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC WD_ARM_SUBSET
  \\ Q_TAC EXISTS_TAC `s`
  \\ ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE]);

val WD_ARM_DIFF = store_thm("WD_ARM_DIFF",
  ``!s t. WD_ARM s ==> WD_ARM (s DIFF t)``,
  REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC WD_ARM_SUBSET 
  \\ Q_TAC EXISTS_TAC `s`
  \\ ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_DIFF]);

val arm2set'_SUBSET_arm2set = store_thm ("arm2set'_SUBSET_arm2set",
  ``!x s. arm2set' x s SUBSET arm2set s``,
  REPEAT STRIP_TAC
  \\ `?x1 x2 x3 x4 x5. x = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [arm2set'_def,arm2set_def,EXTENSION,GSPECIFICATION,IN_UNION,SUBSET_DEF]);

val WD_ARM_arm2set' = store_thm ("WD_ARM_arm2set'",
  ``!x s. WD_ARM (arm2set' x s)``,
  METIS_TAC [arm2set'_SUBSET_arm2set,WD_ARM_THM]);


(* ----------------------------------------------------------------------------- *)
(* Specialising processorTheory                                                  *)
(* ----------------------------------------------------------------------------- *)

val R_def = Define `R r x = one (Reg r x)`;
val S_def = Define `S x = one (Status x)`;

val byte_def = Define `byte a x = one (Mem a x)`
val M_def = Define `M a x = byte (addr32 a + 3w) ((31 >< 24) x) * 
                            byte (addr32 a + 2w) ((23 >< 16) x) * 
                            byte (addr32 a + 1w) ((15 >< 8) x) * 
                            byte (addr32 a + 0w) ((7 >< 0) (x:word32))`;

val R30_def = Define `R30 r x = R r (addr32 x)`; 
val M30_def = Define `M30 a x = M a (addr32 x)`;

val ms_def = Define `
  (ms a [] = emp) /\ 
  (ms a (x::xs) = M a x * ms (a + 1w) xs)`;

val blank_ms_def = Define `
  (blank_ms a 0 = emp) /\ 
  (blank_ms a (SUC n) = ~M a * blank_ms (a + 1w) n)`;

val PASS_def = Define `PASS c x = (cond (CONDITION_PASSED2 x c))
  :'a ARMel set->bool`;

val nPASS_def = Define `nPASS c x = (cond ~(CONDITION_PASSED2 x c))
  :'a ARMel set->bool`;

val ARMnext_def = Define `ARMnext s = arm2set (NEXT_ARM_MEM (set2arm s))`;
val ARMi_def    = Define `ARMi (a,x) = M a x`;
val ARMpc_def   = Define `ARMpc p = R30 15w p * one (Undef F)`;
val ARMproc_def = Define `ARMproc = (ARMsets,ARMnext,ARMpc,ARMi)
  :('a ARMel,30,word32) processor`;

val ARM_RUN_def   = Define `ARM_RUN   = RUN ARMproc`; 
val ARM_GPROG_def = Define `ARM_GPROG = GPROG ARMproc`;
val ARM_PROG_def  = Define `ARM_PROG  = PROG ARMproc`;
val ARM_PROC_def  = Define `ARM_PROC P Q C = PROC ARMproc (R30 14w) P (Q * ~R 14w) C`;

val ARM_PROG2_def = Define `
  ARM_PROG2 c P cs (Q:'a ARMset -> bool) Z = 
    ARM_PROG P cs {} Q Z /\ 
    !x. ARM_PROG (S x * nPASS c x) cs {} ((S x):'a ARMset -> bool) {}`;


(* lemmas about mpool and msequence -------------------------------------------- *)

val M_THM = store_thm("M_THM",
  ``!a x s. 
      (M a x) s = 
      (s = {Mem (addr32 a + 3w) ((31 >< 24) x);
            Mem (addr32 a + 2w) ((23 >< 16) x);
            Mem (addr32 a + 1w) ((15 >< 8) x);
            Mem (addr32 a + 0w) ((7 >< 0) x)})``,
  ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [emp_STAR] ``(M a x * emp) s``)]
  \\ REWRITE_TAC [M_def,byte_def,one_STAR,GSYM STAR_ASSOC]
  \\ SIMP_TAC std_ss [emp_def,IN_INSERT,IN_DELETE,ARMel_11,NOT_IN_EMPTY]
  \\ REWRITE_TAC [addr32_NEQ_addr32]
  \\ ASSUME_TAC (EVAL ``0w = 1w:word32``)
  \\ ASSUME_TAC (EVAL ``0w = 2w:word32``)
  \\ ASSUME_TAC (EVAL ``0w = 3w:word32``)
  \\ ASSUME_TAC (EVAL ``1w = 2w:word32``)
  \\ ASSUME_TAC (EVAL ``1w = 3w:word32``)
  \\ ASSUME_TAC (EVAL ``2w = 3w:word32``)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [EXTENSION,IN_DELETE,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [IN_INSERT,DELETE_INSERT,ARMel_11,WORD_EQ_ADD_LCANCEL,EMPTY_DELETE]);

val SPLIT_IMP_EQ = prove(
  ``!s v w. SPLIT s (v,w) ==> (w = s DIFF v) /\ v SUBSET s``,
  SRW_TAC [] [SPLIT_def,EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ METIS_TAC []);

val SPLIT_DIFF = prove(
  ``!s v w. v SUBSET s ==> SPLIT s (v,s DIFF v)``,
  SRW_TAC [] [SPLIT_def,EXTENSION,DISJOINT_DEF,SUBSET_DEF] \\ METIS_TAC []);

val M_STAR = store_thm("M_STAR",
  ``!P s a x.
      (M a x * P) s = 
      {Mem (addr32 a + 3w) ((31 >< 24) x); Mem (addr32 a + 2w) ((23 >< 16) x);
       Mem (addr32 a + 1w) ((15 >< 8) x); Mem (addr32 a + 0w) ((7 >< 0) x)} SUBSET s /\
      P (s DIFF
      {Mem (addr32 a + 3w) ((31 >< 24) x); Mem (addr32 a + 2w) ((23 >< 16) x);
       Mem (addr32 a + 1w) ((15 >< 8) x); Mem (addr32 a + 0w) ((7 >< 0) x)})``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [STAR_def,M_THM]
  \\ Q.ABBREV_TAC `y = 
      {Mem (addr32 a + 3w) ((31 >< 24) x); Mem (addr32 a + 2w) ((23 >< 16) x);
       Mem (addr32 a + 1w) ((15 >< 8) x); Mem (addr32 a + 0w) ((7 >< 0) x)}`
  \\ POP_ASSUM (fn th => ALL_TAC)
  \\ EQ_TAC \\ STRIP_TAC
  \\ IMP_RES_TAC SPLIT_IMP_EQ \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `s DIFF y` \\ FULL_SIMP_TAC std_ss [SPLIT_DIFF]);

val ARMi_11 = prove(
  ``!a b x y. (ARMi (a,x) = ARMi (b,y)) ==> (a = b)``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] 
  \\ SIMP_TAC std_ss [ARMi_def,M_THM]
  \\ REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ PAT_ASSUM ``!x':'a. b`` (ASSUME_TAC o 
       Q.SPEC `{Mem (addr32 a + 3w) ((31 >< 24) x);
                Mem (addr32 a + 2w) ((23 >< 16) x);
                Mem (addr32 a + 1w) ((15 >< 8) x);
                Mem (addr32 a + 0w) ((7 >< 0) (x:word32))}`) 
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,NOT_IN_EMPTY]
  \\ Q.PAT_ASSUM `!x'.b` 
        (ASSUME_TAC o Q.SPEC `Mem (addr32 a + 0w) ((7 >< 0) (x:word32))`)
  \\ FULL_SIMP_TAC std_ss [ARMel_11,WORD_ADD_0,addr32_11,addr32_NEQ_addr32]);

val ARM_mpool_eq_msequence = 
  let
    val th = Q.INST_TYPE [`:'a`|->`:'a ARMel`,`:'b`|->`:30`,`:'c`|->`:word32`] mpool_eq_msequence
    val th = Q.SPECL [`xs`,`f`,`a`,`ARMi`] th
    val th = SIMP_RULE (bool_ss++SIZES_ss) [GSYM AND_IMP_INTRO] (REWRITE_RULE [dimword_def] th)
    val th = MATCH_MP th ARMi_11 
  in
    (Q.GEN `xs` o Q.GEN `f` o Q.GEN `a`) th 
  end;

val msequence_eq_ms = prove(
  ``!a xs. msequence ARMi a xs = ms a xs``,
  Induct_on `xs` \\ SRW_TAC [] [msequence_def,ms_def,ARMi_def]);

val mpool_eq_ms = store_thm("mpool_eq_ms",
  ``!xs (f:word30->word30) a. LENGTH xs <= 2**30 ==> (mpool ARMi a {(xs,f)} = ms (f a) xs)``,
  SIMP_TAC bool_ss [GSYM msequence_eq_ms,ARM_mpool_eq_msequence]);


(* various lemmas -------------------------------------------------------------- *)

val ARMproc_IN_PROCESSORS = prove(
  ``ARMproc IN PROCESSORS``,
  REWRITE_TAC [GSPECIFICATION,PROCESSORS_def]
  \\ Q.EXISTS_TAC `ARMproc`
  \\ SIMP_TAC std_ss [ARMproc_def]
  \\ SIMP_TAC bool_ss [ARMnext_def,RES_FORALL]
  \\ REPEAT STRIP_TAC  
  \\ SRW_TAC [] [ARMsets_def]
  \\ METIS_TAC []);

val PASS_CASES = store_thm("PASS_CASES",
  ``!n z c v.
      (PASS EQ (n,z,c,v) = cond z) /\
      (PASS CS (n,z,c,v) = cond c) /\
      (PASS MI (n,z,c,v) = cond n) /\
      (PASS VS (n,z,c,v) = cond v) /\
      (PASS HI (n,z,c,v) = cond (c /\ ~z)) /\
      (PASS GE (n,z,c,v) = cond (n = v)) /\
      (PASS GT (n,z,c,v) = cond (~z /\ (n = v))) /\
      (PASS AL (n,z,c,v) = emp) /\
      (PASS NE (n,z,c,v) = cond ~z) /\
      (PASS CC (n,z,c,v) = cond ~c) /\
      (PASS PL (n,z,c,v) = cond ~n) /\
      (PASS VC (n,z,c,v) = cond ~v) /\
      (PASS LS (n,z,c,v) = cond (~c \/ z)) /\
      (PASS LT (n,z,c,v) = cond ~(n = v)) /\
      (PASS LE (n,z,c,v) = cond (z \/ ~(n = v))) /\
      (PASS NV (n,z,c,v) = SEP_F) /\
      (nPASS EQ (n,z,c,v) = cond ~z) /\
      (nPASS CS (n,z,c,v) = cond ~c) /\
      (nPASS MI (n,z,c,v) = cond ~n) /\
      (nPASS VS (n,z,c,v) = cond ~v) /\
      (nPASS HI (n,z,c,v) = cond ~(c /\ ~z)) /\
      (nPASS GE (n,z,c,v) = cond ~(n = v)) /\
      (nPASS GT (n,z,c,v) = cond ~(~z /\ (n = v))) /\
      (nPASS AL (n,z,c,v) = SEP_F) /\
      (nPASS NE (n,z,c,v) = cond ~~z) /\
      (nPASS CC (n,z,c,v) = cond ~~c) /\
      (nPASS PL (n,z,c,v) = cond ~~n) /\
      (nPASS VC (n,z,c,v) = cond ~~v) /\
      (nPASS LS (n,z,c,v) = cond ~(~c \/ z)) /\
      (nPASS LT (n,z,c,v) = cond ~~(n = v)) /\
      (nPASS LE (n,z,c,v) = cond ~(z \/ ~(n = v))) /\
      (nPASS NV (n,z,c,v) = emp)``,
  SRW_TAC [] [CONDITION_PASSED2_def,nPASS_def,PASS_def,SEP_cond_CLAUSES]);

fun QGENL xs th = foldr (uncurry Q.GEN) th xs;
fun GENL_save_thm (name,vars,th) = save_thm(name,QGENL vars th);

val ARM_RUN_THM = GENL_save_thm("ARM_RUN_THM",[`P`,`Q`],  
  REWRITE_CONV [ARM_RUN_def,RUN_def,ARMproc_def] ``ARM_RUN P Q``);

val ARM_GPROG_THM = GENL_save_thm("ARM_GPROG_THM",[`Y`,`C`,`Z`],  
  (REWRITE_CONV [ARM_GPROG_def,ARMproc_def,GPROG_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_RUN_def]) ``ARM_GPROG Y C Z``);

val ARM_PROG_THM = GENL_save_thm("ARM_PROG_THM",[`P`,`cs`,`C`,`Q`,`Z`],  
  (REWRITE_CONV [ARM_PROG_def,ARMproc_def,PROG_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_GPROG_def]) ``ARM_PROG P cs C Q Z``);

val ARM_PROC_THM = GENL_save_thm("ARM_PROC_THM",[`P`,`Q`,`C`],  
  (REWRITE_CONV [ARM_PROC_def,PROC_def,ARMproc_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_PROG_def]) ``ARM_PROC P Q C``);

val run_arm2set = prove(
  ``!k s. run ARMnext (k,arm2set s) = arm2set (STATE_ARM_MEM k s)``,
  Induct_on `k` \\ FULL_SIMP_TAC std_ss [run_def,STATE_ARM_MEM_def,STATE_ARM_MMU_def]
  \\ `!k s. run ARMnext (k,ARMnext s) = ARMnext (run ARMnext (k,s))` by 
        (Induct \\ FULL_SIMP_TAC std_ss [run_def])
  \\ ASM_REWRITE_TAC [ARMnext_def,set2arm_arm2set,NEXT_ARM_MEM_def]);


(* theorems for ARM_RUN -------------------------------------------------------- *)

fun ARM_RUN_INST th = 
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.ISPEC `ARMproc` th
    val th = MATCH_MP th ARMproc_IN_PROCESSORS
    val th = BETA_RULE th
  in
    REWRITE_RULE [GSYM ARM_RUN_def, GSYM ARM_PROG_def] th
  end;

fun save_ARM_RUN name rule = save_thm(name,ARM_RUN_INST rule);

val _ = save_ARM_RUN "ARM_RUN_FRAME" RUN_FRAME;
val _ = save_ARM_RUN "ARM_RUN_STRENGTHEN_PRE" RUN_STRENGTHEN_PRE;
val _ = save_ARM_RUN "ARM_RUN_WEAKEN_POST" RUN_WEAKEN_POST;
val _ = save_ARM_RUN "ARM_RUN_COMPOSE" RUN_COMPOSE;
val _ = save_ARM_RUN "ARM_RUN_HIDE_PRE" RUN_HIDE_PRE;
val _ = save_ARM_RUN "ARM_RUN_HIDE_POST" RUN_HIDE_POST;
val _ = save_ARM_RUN "ARM_RUN_LOOP" RUN_LOOP;

val ARM_RUN_SEMANTICS = store_thm("ARM_RUN_SEMANTICS",
  ``ARM_RUN P Q =
    !y s. P (arm2set' y s) ==>
          ?k. let s' = STATE_ARM_MEM k s in
              Q (arm2set' y s') /\ (arm2set'' y s = arm2set'' y s')``,
  SIMP_TAC std_ss [ARM_RUN_THM,RES_FORALL,ARMsets_def,GSPECIFICATION]
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    ASSUME_TAC (Q.EXISTS (`?s'. arm2set s = arm2set s'`,`s`) (REFL ``arm2set s``))
    \\ Q.PAT_ASSUM `!s. b` 
          (STRIP_ASSUME_TAC o Q.SPEC `\s'. s' = arm2set'' y s` o 
           UNDISCH o Q.SPEC `arm2set s`)   
    \\ FULL_SIMP_TAC std_ss [run_arm2set,STAR_arm2set,LET_DEF]
    \\ `?k y'. Q (arm2set' y' (STATE_ARM_MEM k s)) /\
               (arm2set'' y' (STATE_ARM_MEM k s) = arm2set'' y s)` by METIS_TAC []
    \\ Q.EXISTS_TAC `k` \\ METIS_TAC [arm2set''_EQ_arm2set''],
    PAT_ASSUM ``s = arm2set s'`` (fn th => FULL_SIMP_TAC bool_ss [th,STAR_arm2set])
    \\ PAT_ASSUM ``!y:'a. b:bool`` 
        (STRIP_ASSUME_TAC o SIMP_RULE std_ss [LET_DEF] o UNDISCH o Q.SPECL [`y`,`s'`])
    \\ Q.EXISTS_TAC `k` \\ REWRITE_TAC [run_arm2set,STAR_arm2set]
    \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC [] \\ METIS_TAC []]);

val IMP_ARM_RUN = store_thm ("IMP_ARM_RUN",
  ``!x P Q.
      (!t s. t SUBSET arm2set s /\ P t ==> (t = arm2set' x s)) /\     (* cond 1 *)
      (!s. ?k. (P (arm2set' x s) ==> 
           (arm2set'' x s = arm2set'' x (STATE_ARM_MEM k s)) /\       (* cond 2 *)
           Q (arm2set' x (STATE_ARM_MEM k s)))) ==>                   (* cond 3 *)
      ARM_RUN P Q``,
   REWRITE_TAC [ARM_RUN_SEMANTICS] \\ REPEAT STRIP_TAC
   \\ `x = y` by METIS_TAC [arm2set'_11,arm2set'_SUBSET_arm2set]
   \\ FULL_SIMP_TAC bool_ss []
   \\ Q.PAT_ASSUM `!s. ?k. b:bool` (STRIP_ASSUME_TAC o Q.SPEC `s`)  
   \\ Q.EXISTS_TAC `k` \\ FULL_SIMP_TAC std_ss [LET_DEF]);

val ARM_RUN_R_11 = store_thm("ARM_RUN_R_11",
  ``!P Q. ARM_RUN P Q = ARM_RUN (P /\ SEP_FORALL a x y. SEP_NOT (R a x * R a y * SEP_T)) Q``,
  SIMP_TAC std_ss [ARM_RUN_SEMANTICS,SEP_CONJ_def,SEP_FORALL]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!y.b` MATCH_MP_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SEP_NOT_def] \\ CCONTR_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC,R_def,one_STAR,SEP_T_def]
  \\ `?rs ns st ud rt. y = (rs,ns,st,ud,rt)` by 
       (Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r` \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [IN_arm2set']
  \\ `Reg y' y''' IN arm2set' (rs,ns,st,ud,rt) s DELETE Reg y' (reg y' s)` by METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss [DELETE_arm2set',IN_arm2set'] 
  \\ FULL_SIMP_TAC bool_ss [IN_DELETE]);

val ARM_RUN_byte_11 = store_thm("ARM_RUN_byte_11",
  ``!P Q. ARM_RUN P Q = ARM_RUN (P /\ SEP_FORALL a x y. SEP_NOT (byte a x * byte a y * SEP_T)) Q``,
  SIMP_TAC std_ss [ARM_RUN_SEMANTICS,SEP_CONJ_def,SEP_FORALL]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!y.b` MATCH_MP_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SEP_NOT_def] \\ CCONTR_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC,byte_def,SEP_T_def,one_STAR]
  \\ `?rs ns st ud rt. y = (rs,ns,st,ud,rt)` by 
       (Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r` \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [IN_arm2set']
  \\ `Mem y' y''' IN arm2set' (rs,ns,st,ud,rt) s DELETE Mem y' (mem_byte y' s)` by METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss [DELETE_arm2set',IN_arm2set'] 
  \\ FULL_SIMP_TAC bool_ss [IN_DELETE]);

val ARM_RUN_M_11 = store_thm("ARM_RUN_M_11",
  ``!P Q. ARM_RUN P Q = ARM_RUN (P /\ SEP_FORALL a x y. SEP_NOT (M a x * M a y * SEP_T)) Q``,
  SIMP_TAC std_ss [ARM_RUN_SEMANTICS,SEP_CONJ_def,SEP_FORALL]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!y.b` MATCH_MP_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SEP_NOT_def] \\ CCONTR_TAC
  \\ FULL_SIMP_TAC bool_ss [M_def]
  \\ ASM_MOVE_STAR_TAC `b1*b2*b3*b4*(b5*b6*b7*b8)*t` `b4*(b8*(b2*b3*b1*b6*b7*b5*t))`
  \\ FULL_SIMP_TAC bool_ss [byte_def,one_STAR,WORD_ADD_0]
  \\ `?rs ns st ud rt. y = (rs,ns,st,ud,rt)` by 
       (Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r` \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [IN_arm2set']
  \\ `Mem (addr32 y') ((7 >< 0) (y''':word32)) IN
      arm2set' (rs,ns,st,ud,rt) s DELETE Mem (addr32 y') (mem_byte (addr32 y') s)` by METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss [DELETE_arm2set',IN_arm2set'] 
  \\ FULL_SIMP_TAC bool_ss [IN_DELETE]);


(* theorems for ARM_GPROG ------------------------------------------------------ *)

fun ARM_GPROG_INST th = 
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.ISPEC `ARMproc` th
    val th = MATCH_MP th ARMproc_IN_PROCESSORS
    val th = BETA_RULE th
  in
    REWRITE_RULE [GSYM ARM_GPROG_def, GSYM ARM_GPROG_def] th
  end;

fun save_ARM_GPROG name rule = save_thm(name,ARM_GPROG_INST rule);

val _ = save_ARM_GPROG "ARM_GPROG_FRAME" GPROG_FRAME;
val _ = save_ARM_GPROG "ARM_GPROG_EMPTY_CODE" GPROG_EMPTY_CODE;
val _ = save_ARM_GPROG "ARM_GPROG_ADD_CODE" GPROG_ADD_CODE;
val _ = save_ARM_GPROG "ARM_GPROG_STRENGTHEN_PRE" GPROG_STRENGTHEN_PRE;
val _ = save_ARM_GPROG "ARM_GPROG_WEAKEN_POST" GPROG_WEAKEN_POST;
val _ = save_ARM_GPROG "ARM_GPROG_FALSE_PRE" GPROG_FALSE_PRE;
val _ = save_ARM_GPROG "ARM_GPROG_FALSE_POST" GPROG_FALSE_POST;
val _ = save_ARM_GPROG "ARM_GPROG_SHIFT" GPROG_SHIFT;
val _ = save_ARM_GPROG "ARM_GPROG_MERGE_CODE" GPROG_MERGE_CODE;
val _ = save_ARM_GPROG "ARM_GPROG_MERGE_PRE" GPROG_MERGE_PRE;
val _ = save_ARM_GPROG "ARM_GPROG_MERGE_POST" GPROG_MERGE_POST;
val _ = save_ARM_GPROG "ARM_GPROG_COMPOSE" GPROG_COMPOSE;
val _ = save_ARM_GPROG "ARM_GPROG_LOOP" GPROG_LOOP;

val INSERT_BIGDISJ_PAIR = prove(
  ``SEP_BIGDISJ { g P' f' |(P',f')| (P',f') IN (P,f) INSERT Y} =
    g P f \/ SEP_BIGDISJ { g P' f' |(P',f')| (P',f') IN Y}``,
  `{ g P' f' |(P',f')| (P',f') IN (P,f) INSERT Y} = 
   g P f INSERT { g P' f' |(P',f')| (P',f') IN Y}` by 
    (ONCE_REWRITE_TAC [EXTENSION] \\ SIMP_TAC std_ss [IN_INSERT,GSPECIFICATION]    
     \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [     
       Cases_on `x'` \\ FULL_SIMP_TAC std_ss [PAIR_EQ]
       \\ DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
       Q.EXISTS_TAC `P,f` \\ FULL_SIMP_TAC std_ss [PAIR_EQ],
       Cases_on `x'` \\ FULL_SIMP_TAC std_ss [PAIR_EQ]
       \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []])
  \\ ASM_REWRITE_TAC [SEP_BIGDISJ_CLAUSES]);

val SEP_CONJ_OVER_DISJ = prove(
  ``!P Q Z. (P \/ Q) /\ Z = P /\ Z \/ Q /\ Z:'a set -> bool``,
  SIMP_TAC bool_ss [FUN_EQ_THM,SEP_CONJ_def,SEP_DISJ_def] \\ METIS_TAC []);

val SPLIT_SPLIT = prove(
  ``SPLIT x (u,v) ==> SPLIT u (u',v') ==> SPLIT x (u',v' UNION v)``,
  REWRITE_TAC [SPLIT_def,DISJOINT_DEF,EXTENSION,IN_UNION,IN_INTER,NOT_IN_EMPTY]
  \\ METIS_TAC []);

val ARM_GPROG_11_LEMMA = 
  (SIMP_RULE std_ss [STAR_ASSOC] o 
   Q.INST [`P1`|->`P1*P2`,`Q`|->`\a x y. Q1 a x * Q2 a y`] o prove) (
  ``(P /\ SEP_FORALL a x y. SEP_NOT (Q a x y * SEP_T)) * P1 /\ 
         (SEP_FORALL a x y. SEP_NOT (Q a x y * SEP_T)) =
    P * P1 /\ SEP_FORALL a x y. SEP_NOT (Q a x y * SEP_T)``,
  SIMP_TAC std_ss [STAR_def,SEP_NOT_def,SEP_T_def,FUN_EQ_THM,SEP_CONJ_def,SEP_FORALL] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] << [  
    Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `v` \\ ASM_REWRITE_TAC []
    \\ REPEAT STRIP_TAC \\ Cases_on `Q y y' y'' u'` \\ ASM_REWRITE_TAC []
    \\ Q.PAT_ASSUM `!x.b` (ASSUME_TAC o Q.SPECL [`y`,`y'`,`y''`,`u'`])
    \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
    \\ `~SPLIT x (u',v' UNION v)` by METIS_TAC []
    \\ IMP_RES_TAC SPLIT_SPLIT,METIS_TAC []]);

val ARM_GPROG_R_11 = store_thm("ARM_GPROG_R_11",
  ``!P f Y C Z.
      ARM_GPROG ((P,f) INSERT Y) C Z = 
      ARM_GPROG ((P /\ (SEP_FORALL a x y. SEP_NOT (R a x * R a y * SEP_T)),f) INSERT Y) C Z``,
  REWRITE_TAC [ARM_GPROG_THM] \\ ONCE_REWRITE_TAC [ARM_RUN_R_11]
  \\ ONCE_REWRITE_TAC [GSYM 
      (SIMP_CONV std_ss [] ``(\P' f'. P' * mpool ARMi p C * ARMpc (f' p)) P' f'``)]
  \\ REWRITE_TAC [INSERT_BIGDISJ_PAIR]
  \\ SIMP_TAC std_ss [SEP_CONJ_OVER_DISJ,ARM_GPROG_11_LEMMA]);

val ARM_GPROG_byte_11 = store_thm("ARM_GPROG_byte_11",
  ``!P f Y C Z.
      ARM_GPROG ((P,f) INSERT Y) C Z = 
      ARM_GPROG ((P /\ (SEP_FORALL a x y. SEP_NOT (byte a x * byte a y * SEP_T)),f) INSERT Y) C Z``,
  REWRITE_TAC [ARM_GPROG_THM] \\ ONCE_REWRITE_TAC [ARM_RUN_byte_11]
  \\ ONCE_REWRITE_TAC [GSYM 
      (SIMP_CONV std_ss [] ``(\P' f'. P' * mpool ARMi p C * ARMpc (f' p)) P' f'``)]
  \\ REWRITE_TAC [INSERT_BIGDISJ_PAIR]
  \\ SIMP_TAC std_ss [SEP_CONJ_OVER_DISJ,ARM_GPROG_11_LEMMA]);

val ARM_GPROG_M_11 = store_thm("ARM_GPROG_M_11",
  ``!P f Y C Z.
      ARM_GPROG ((P,f) INSERT Y) C Z = 
      ARM_GPROG ((P /\ (SEP_FORALL a x y. SEP_NOT (M a x * M a y * SEP_T)),f) INSERT Y) C Z``,
  REWRITE_TAC [ARM_GPROG_THM] \\ ONCE_REWRITE_TAC [ARM_RUN_M_11]
  \\ ONCE_REWRITE_TAC [GSYM 
      (SIMP_CONV std_ss [] ``(\P' f'. P' * mpool ARMi p C * ARMpc (f' p)) P' f'``)]
  \\ REWRITE_TAC [INSERT_BIGDISJ_PAIR]
  \\ SIMP_TAC std_ss [SEP_CONJ_OVER_DISJ,ARM_GPROG_11_LEMMA]);


(* theorems for ARM_PROG ------------------------------------------------------- *)

fun ARM_PROG_INST th = 
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.ISPEC `ARMproc` th
    val th = MATCH_MP th ARMproc_IN_PROCESSORS
    val th = BETA_RULE th
  in
    REWRITE_RULE [GSYM ARM_PROG_def, GSYM ARM_PROG_def] th
  end;

fun save_ARM_PROG name rule = save_thm(name,ARM_PROG_INST rule);

val _ = save_ARM_PROG "ARM_PROG_FRAME" PROG_FRAME;
val _ = save_ARM_PROG "ARM_PROG_MERGE" PROG_MERGE;
val _ = save_ARM_PROG "ARM_PROG_MERGE_POST" PROG_MERGE_POST;
val _ = save_ARM_PROG "ARM_PROG_MERGE_CODE" PROG_MERGE_CODE;
val _ = save_ARM_PROG "ARM_PROG_ABSORB_POST" PROG_ABSORB_POST;
val _ = save_ARM_PROG "ARM_PROG_FALSE_POST" PROG_FALSE_POST;
val _ = save_ARM_PROG "ARM_PROG_STRENGTHEN_PRE" PROG_STRENGTHEN_PRE;
val _ = save_ARM_PROG "ARM_PROG_WEAKEN_POST" PROG_WEAKEN_POST;
val _ = save_ARM_PROG "ARM_PROG_WEAKEN_POST1" PROG_WEAKEN_POST1;
val _ = save_ARM_PROG "ARM_PROG_ADD_CODE" PROG_ADD_CODE;
val _ = save_ARM_PROG "ARM_PROG_APPEND_CODE" PROG_APPEND_CODE;
val _ = save_ARM_PROG "ARM_PROG_MOVE_COND" PROG_MOVE_COND;
val _ = save_ARM_PROG "ARM_PROG_HIDE_PRE" PROG_HIDE_PRE;
val _ = save_ARM_PROG "ARM_PROG_HIDE_POST1" PROG_HIDE_POST1;
val _ = save_ARM_PROG "ARM_PROG_HIDE_POST" PROG_HIDE_POST;
val _ = save_ARM_PROG "ARM_PROG_EXISTS_PRE" PROG_EXISTS_PRE;
val _ = save_ARM_PROG "ARM_PROG_COMPOSE" PROG_COMPOSE;
val _ = save_ARM_PROG "ARM_PROG_LOOP" PROG_LOOP;
val _ = save_ARM_PROG "ARM_PROG_LOOP_MEASURE" PROG_LOOP_MEASURE;
val _ = save_ARM_PROG "ARM_PROG_EXTRACT_POST" PROG_EXTRACT_POST;
val _ = save_ARM_PROG "ARM_PROG_EXTRACT_CODE" PROG_EXTRACT_CODE;

val ARM_PROG_INTRO = save_thm("ARM_PROG_INTRO", let 
  val th = Q.ISPECL [`ARMsets`,`ARMnext`,`ARMpc`,`ARMi`] PROG_INTRO
  val th = REWRITE_RULE [GSYM ARM_RUN_def,GSYM ARM_PROG_def,GSYM ARMproc_def,dimword_def] th
  val th = SIMP_RULE (bool_ss++SIZES_ss) [GSYM AND_IMP_INTRO,msequence_eq_ms] th
  in MATCH_MP th ARMi_11 end);

val ARM_PROG_INTRO1 = save_thm("ARM_PROG_INTRO1",let 
  val th = Q.SPECL [`P`,`cs`,`Q`,`SEP_F`,`f`] ARM_PROG_INTRO
  val th = REWRITE_RULE [F_STAR,SEP_DISJ_CLAUSES,ARM_PROG_INST PROG_FALSE_POST] th
  in (Q.GEN `P` o Q.GEN `cs` o Q.GEN `Q`) th end);

val ARM_PROG_HIDE_STATUS = store_thm("ARM_PROG_HIDE_STATUS",
  ``!P cs C Q Z.
      (!n z c v. ARM_PROG (P * S (n,z,c,v)) cs C Q Z) = ARM_PROG (P * ~S) cs C Q Z``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM (ARM_PROG_INST PROG_HIDE_PRE)]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ ASM_REWRITE_TAC []);

val ARM_PROG_R_11 = store_thm("ARM_PROG_R_11",
  ``!P f Y C Z.
      ARM_PROG P cs C Q Z = 
      ARM_PROG (P /\ SEP_FORALL a x y. SEP_NOT (R a x * R a y * SEP_T)) cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,GSYM ARM_GPROG_R_11]);

val ARM_PROG_byte_11 = store_thm("ARM_PROG_byte_11",
  ``!P f Y C Z.
      ARM_PROG P cs C Q Z = 
      ARM_PROG (P /\ SEP_FORALL a x y. SEP_NOT (byte a x * byte a y * SEP_T)) cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,GSYM ARM_GPROG_byte_11]);

val ARM_PROG_M_11 = store_thm("ARM_PROG_M_11",
  ``!P f Y C Z.
      ARM_PROG P cs C Q Z = 
      ARM_PROG (P /\ SEP_FORALL a x y. SEP_NOT (M a x * M a y * SEP_T)) cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,GSYM ARM_GPROG_M_11]);


(* theorems for ARM_PROC ------------------------------------------------------- *)

val ARM_PROC_CALL = store_thm("ARM_PROC_CALL",
  ``!cs P Q C k.
      CALL ARMproc (R30 14w) ((~(R 14w)):^(ty_antiq ARMel_type) set -> bool) cs (pcADD k) /\ 
      ARM_PROC P (Q:^(ty_antiq ARMel_type) set -> bool) C ==>
      ARM_PROG (P * ~R 14w) cs (setADD k C) (Q * ~R 14w) {}``,
  REWRITE_TAC [setADD_def,ARM_PROG_def,ARM_PROC_def,CALL_def] 
  \\ REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC (MATCH_MP (SIMP_RULE bool_ss [RES_FORALL] PROC_CALL) ARMproc_IN_PROCESSORS)
  \\ Q.EXISTS_TAC `R30 14w` \\ ASM_REWRITE_TAC []);

val _ = save_thm("ARM_PROC_RECURSION",PROC_RECURSION);


(* ----------------------------------------------------------------------------- *)
(* Theorems for collections of "R r x", "~R r" and "M a x"                       *)
(* ----------------------------------------------------------------------------- *)

val reg_spec_def = Define `
  reg_spec l = FOLDR (\(r, v) P. R r v * P) emp l`

val ereg_spec_def = Define `
  ereg_spec l = FOLDR (\r P. (SEP_EXISTS v. R r v) * P) emp l`

val reg_spec_thm = store_thm ("reg_spec_thm",
  ``!l P s. ALL_DISTINCT l ==>
            ((((reg_spec l) * P) s) =
             (((EVERY (\(r, v). ((Reg r v) IN s)) l)) /\
             (P (s DIFF (LIST_TO_SET (MAP (\(r, v). Reg r v) l))))))``,
  Induct_on `l` << [
    SIMP_TAC list_ss 
      [reg_spec_def, emp_STAR, containerTheory.LIST_TO_SET_THM, DIFF_EMPTY],
    REPEAT GEN_TAC THEN
    Cases_on `h` THEN
    SIMP_TAC list_ss [reg_spec_def, containerTheory.LIST_TO_SET_THM, GSYM STAR_ASSOC] THEN
    ASM_SIMP_TAC std_ss [GSYM reg_spec_def, R_def, one_STAR, IN_DELETE,
                         ARMel_11, DIFF_INSERT, GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (prove (``((a /\ c) ==> (b = b')) ==> ((a:bool /\ b /\ c) = (a /\ b' /\ c))``, PROVE_TAC[])) THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC std_ss [listTheory.EVERY_MEM] THEN 
    EQ_TAC THEN REPEAT STRIP_TAC THEN 
    RES_TAC THEN
    Cases_on `e` THEN
    FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC []]);

val ereg_spec_thm = store_thm ("ereg_spec_thm",
  ``!l P s. (ALL_DISTINCT l /\ WD_ARM s) ==>
            ((((ereg_spec l) * P) s) =
            (((EVERY (\r. ?v. ((Reg r v) IN s)) l)) /\
            (P (s DIFF (BIGUNION (LIST_TO_SET (MAP (\r. (\x. ?v. (x = Reg r v))) l)))))))``,
  Induct_on `l` THENL [
    SIMP_TAC list_ss [ereg_spec_def, emp_STAR, containerTheory.LIST_TO_SET_THM, DIFF_EMPTY, BIGUNION_EMPTY],
    SIMP_TAC list_ss [ereg_spec_def, containerTheory.LIST_TO_SET_THM, GSYM STAR_ASSOC] THEN
    ASM_SIMP_TAC std_ss [GSYM ereg_spec_def, R_def, one_STAR, IN_DELETE, WD_ARM_DELETE,
        ARMel_11, DIFF_INSERT, GSYM CONJ_ASSOC, SEP_EXISTS_ABSORB_STAR, SEP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC[],
    Q.PAT_ASSUM `EVERY X l` MP_TAC THEN
    MATCH_MP_TAC EVERY_MONOTONIC THEN
    SIMP_TAC std_ss [] THEN
    PROVE_TAC[],
    SIMP_TAC std_ss [BIGUNION_INSERT] THEN
    POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC (prove (``(s1 = s2) ==> (P s1 ==> P s2)``, SIMP_TAC std_ss [])) THEN
    MATCH_MP_TAC (prove (``(s DELETE x = s DIFF x') ==> (s DELETE x DIFF y = s DIFF (x' UNION y))``, SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, IN_UNION] THEN METIS_TAC[])) THEN
    FULL_SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, WD_ARM_def, WD_Reg_def] THEN
    GEN_TAC THEN
    Cases_on `x IN s` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC std_ss [IN_DEF] THEN
    METIS_TAC[],		
    Q_TAC EXISTS_TAC `v` THEN
    REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC[],
      FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
      REPEAT STRIP_TAC THEN
      METIS_TAC[],
      POP_ASSUM MP_TAC THEN
      SIMP_TAC std_ss [BIGUNION_INSERT] THEN
      MATCH_MP_TAC (prove (``(s2 = s1) ==> (P s1 ==> P s2)``, SIMP_TAC std_ss [])) THEN
      MATCH_MP_TAC (prove (``(s DELETE x = s DIFF x') ==> (s DELETE x DIFF y = s DIFF (x' UNION y))``, SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, IN_UNION] THEN METIS_TAC[])) THEN
      FULL_SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, WD_ARM_def, WD_Reg_def] THEN
      GEN_TAC THEN
      Cases_on `x IN s` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [IN_DEF] THEN
      METIS_TAC[]]]]);

val ENUMERATE_def = Define `
  (ENUMERATE n [] = []) /\
  (ENUMERATE n (h::l) = (n, h)::(ENUMERATE (SUC n) l))`;

val ENUMERATE___MEM_FST_RANGE = store_thm ("ENUMERATE___MEM_FST_RANGE",
  ``!n e m l. MEM (n, e) (ENUMERATE m l) ==> (m <= n /\ n < m + LENGTH l)``,
  Induct_on `l` THENL [
    SIMP_TAC list_ss [ENUMERATE_def],
    ASM_SIMP_TAC list_ss [ENUMERATE_def, DISJ_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    RES_TAC THEN
    ASM_SIMP_TAC arith_ss []]);

val MEM_ENUMERATE = store_thm ("MEM_ENUMERATE",
  ``!x m l. MEM x (ENUMERATE m l) =
            ((m <= FST x) /\ (FST x < m + LENGTH l) /\
            (SND x = EL (FST x - m) l))``,
  Cases_on `x` THEN
  Induct_on `l` THENL [
    SIMP_TAC list_ss [ENUMERATE_def] THEN
    GEN_TAC THEN
    Cases_on `m <= q` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC arith_ss [],
    ASM_SIMP_TAC list_ss [ENUMERATE_def] THEN
    REPEAT GEN_TAC THEN
    Cases_on `(q = m) /\ (r = h)` THEN ASM_SIMP_TAC list_ss [] THEN
    Cases_on `q` THEN1 FULL_SIMP_TAC list_ss [] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC arith_ss [] THENL [
      FULL_SIMP_TAC list_ss [arithmeticTheory.SUB],
      CCONTR_TAC THEN
      `m = SUC n` by DECIDE_TAC THEN
      FULL_SIMP_TAC list_ss [],
      Cases_on `n < m` THEN 
      FULL_SIMP_TAC list_ss [arithmeticTheory.SUB]]]);

(*
val ms_STAR = store_thm ("ms_STAR", 
  ``!n p l P s.
	(n + LENGTH l < 2**30) ==>
	((ms (p + n2w n) l * P)  s = ((LIST_TO_SET (MAP (\(n, i). Mem (p + n2w n) i) (ENUMERATE n l))) SUBSET s /\ P (s DIFF (LIST_TO_SET (MAP (\(n, i). Mem (p + n2w n) i) (ENUMERATE n l))))))``,
  Induct_on `l` THENL [
    SIMP_TAC list_ss 
      [ENUMERATE_def, ms_def, containerTheory.LIST_TO_SET_THM, LET_THM, 
       EMPTY_SUBSET,DIFF_EMPTY, emp_STAR],
    ASM_SIMP_TAC list_ss [ENUMERATE_def, ms_def, containerTheory.LIST_TO_SET_THM, LET_THM, M_def, GSYM STAR_ASSOC, one_STAR, GSYM WORD_ADD_ASSOC, word_add_n2w] THEN
    SIMP_TAC arith_ss [GSYM DIFF_INSERT, INSERT_SUBSET, SUBSET_DELETE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC arith_ss [SUC_ONE_ADD] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC list_ss [MEM_MAP] THEN
    Cases_on `y` THEN
    SIMP_TAC std_ss [ARMel_11, WORD_EQ_ADD_LCANCEL] THEN
    Cases_on `MEM (q,r) (ENUMERATE (n + 1) l)` THEN ASM_REWRITE_TAC[] THEN
    IMP_RES_TAC ENUMERATE___MEM_FST_RANGE THEN
    ASM_SIMP_TAC arith_ss [n2w_11, dimword_30]]);

val ms_STAR___ZERO = save_thm ("ms_STAR___ZERO",     
  REWRITE_RULE [ADD, WORD_ADD_0] (SPEC ``0:num`` ms_STAR));

val DELETE_EQ_ELIM = store_thm ("DELETE_EQ_ELIM",
  ``!X Y z. z IN Y ==> ((X = Y DELETE z) =
            ((z INSERT X = Y) /\ ~(z IN X)))``,
  SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_INSERT] \\ METIS_TAC []);

val DIFF_EQ_ELIM = store_thm ("DIFF_EQ_ELIM",
  ``!X Y Z. Z SUBSET Y ==> ((X = Y DIFF Z) =
            ((X UNION Z = Y) /\ (DISJOINT X Z)))``,
  SIMP_TAC std_ss [EXTENSION, IN_DIFF, IN_UNION, DISJOINT_DEF, IN_INTER, 
     NOT_IN_EMPTY, SUBSET_DEF] \\ METIS_TAC [])
*)

val _ = export_theory();
