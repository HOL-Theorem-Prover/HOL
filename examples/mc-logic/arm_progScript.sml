(*
  quietdec := true;
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open arm_evalTheory armTheory listTheory bsubstTheory pairTheory systemTheory fcpTheory bitTheory; 
open combinTheory rich_listTheory;
open set_sepLib addressTheory;

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

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


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

val WORD_FULL_EXTRACT_32 = 
  (SIMP_RULE (arith_ss++SIZES_ss) [] o
   RW [LESS_EQ_REFL,w2w_def,n2w_w2n] o Q.SPEC `dimindex (:32) - 1` o
  INST_TYPE [``:'b``|->``:32``,``:'a``|->``:32``]) EXTRACT_ALL_BITS;

val concat24 =
  (SIMP_RULE (std_ss++SIZES_ss) [fcpTheory.index_sum,WORD_FULL_EXTRACT_32] o
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

val arm2set'_SUBSET_arm2set = store_thm ("arm2set'_SUBSET_arm2set",
  ``!x s. arm2set' x s SUBSET arm2set s``,
  REPEAT STRIP_TAC
  \\ `?x1 x2 x3 x4 x5. x = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [arm2set'_def,arm2set_def,EXTENSION,GSPECIFICATION,IN_UNION,SUBSET_DEF]);


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

val blank_def = Define `
  (blank a 0 = emp) /\
  (blank a (SUC n) = ~ M a * blank (a-1w) n)`;

val stack_def = Define `stack a xs n = R30 13w a * ms a xs * blank (a - 1w) n`;

val PASS_def = Define `PASS c x = (cond (CONDITION_PASSED2 x c)) :'a ARMel set->bool`;
val nPASS_def = Define `nPASS c x = (cond ~(CONDITION_PASSED2 x c)) :'a ARMel set->bool`;

val ARMnext_def = Define `ARMnext s = arm2set (NEXT_ARM_MEM (set2arm s))`;
val ARMnext_rel_def = Define `ARMnext_rel = \s s'. (ARMnext s = s')`;
val ARMi_def    = Define `ARMi (a,x) = M a x`;
val ARMpc_def   = Define `ARMpc p = R30 15w p * one (Undef F)`;
val ARMproc_def = Define `ARMproc = (ARMsets,ARMnext_rel,ARMpc,ARMi)
  :('a ARMel,30,word32) processor`;

val ARMi2_def = Define `ARMi2 (a,x) = ARMi (addr30 a,x)`;
val ARMpc2_def   = Define `ARMpc2 p = R 15w p * one (Undef F) * cond (p && 3w = 0w)`;
val ARM_MODEL_def = Define `ARM_MODEL = (ARMsets,ARMnext_rel,ARMpc2,ARMi2)
  :('a ARMel,32,word32) processor`;

val ARM_RUN_def   = Define `ARM_RUN   = RUN ARMproc`; 
val ARM_GPROG_def = Define `ARM_GPROG = GPROG ARMproc`;
val ARM_PROG_def  = Define `ARM_PROG  = PROG ARMproc`;
val ARM_PROC_def  = Define `ARM_PROC P Q C = PROC ARMproc (R30 14w) P (Q * ~R 14w) C`;

val ARM_PROG2_def = Define `
  ARM_PROG2 c P cs C (Q:'a ARMset -> bool) Z = 
    ARM_PROG P cs C Q Z /\ 
    !x. ARM_PROG (S x * nPASS c x) cs C ((S x):'a ARMset -> bool) {}`;


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

val blank_ms_SNOC = prove(
  ``!n a. blank_ms a (SUC n) = blank_ms a n * ~ M (a + n2w n)``,
  Induct THEN1 REWRITE_TAC [blank_ms_def,WORD_ADD_0,emp_STAR]
  \\ ONCE_REWRITE_TAC [blank_ms_def]
  \\ ASM_REWRITE_TAC [RW1[ADD_COMM]ADD1,word_add_n2w,GSYM WORD_ADD_ASSOC,STAR_ASSOC]);

val blank_ms_EQ_blank = store_thm("blank_ms_EQ_blank",
  ``!n a. blank_ms (a - n2w n) n = blank (a - 1w) n``,
  Induct THEN1 REWRITE_TAC [blank_ms_def,blank_def]
  \\ REWRITE_TAC [blank_ms_SNOC,blank_def,RW1[ADD_COMM]ADD1,GSYM word_add_n2w]
  \\ ASM_REWRITE_TAC [WORD_SUB_PLUS,WORD_SUB_ADD]
  \\ SIMP_TAC (bool_ss++star_ss) []);


(* various lemmas -------------------------------------------------------------- *)

val ARMproc_IN_PROCESSORS = prove(
  ``ARMproc IN PROCESSORS``,
  REWRITE_TAC [GSPECIFICATION,PROCESSORS_def] \\ Q.EXISTS_TAC `ARMproc`
  \\ SIMP_TAC std_ss [ARMproc_def,ARMnext_rel_def]
  \\ SIMP_TAC bool_ss [ARMnext_def,RES_FORALL]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [ARMsets_def] \\ METIS_TAC []);

val ARM_MODEL_IN_PROCESSORS = prove(
  ``ARM_MODEL IN PROCESSORS``,
  REWRITE_TAC [GSPECIFICATION,PROCESSORS_def] \\ Q.EXISTS_TAC `ARM_MODEL`
  \\ SIMP_TAC std_ss [ARM_MODEL_def,ARMnext_rel_def]
  \\ SIMP_TAC bool_ss [ARMnext_def,RES_FORALL]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [ARMsets_def] \\ METIS_TAC []);

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

val WORD_CMP_NORMALISE = save_thm("WORD_CMP_NORMALISE",let
  val rw = METIS_PROVE [] ``!x:'a y z:'b q. ~(x = y) /\ ~(z = q) =  ~(x = y) /\ ~(q = z)``
  val nzcv_thm = RW1 [rw] nzcv_def
  val rw = [nzcv_thm,LET_DEF,GSYM word_add_n2w,n2w_w2n,GSYM word_sub_def,WORD_EQ_SUB_ZERO]
  val f = (GSYM o SIMP_RULE std_ss rw) 
  val lemma1 = prove(``!a:'a word b. (b <=+ a) /\ ~(a = b) = b <+ a``,
    REWRITE_TAC [WORD_LOWER_OR_EQ] \\ METIS_TAC [WORD_LOWER_NOT_EQ])
  val lemma2 = prove(``!a:'a word b. ~(a = b) /\ (b <=+ a) = b <+ a``,
    REWRITE_TAC [WORD_LOWER_OR_EQ] \\ METIS_TAC [WORD_LOWER_NOT_EQ])
  val lemma3 = prove(``!a:'a word b. (b <= a) /\ ~(a = b) = b < a``,
    REWRITE_TAC [WORD_LESS_OR_EQ] \\ METIS_TAC [WORD_LESS_NOT_EQ])
  val lemma4 = prove(``!a:'a word b. ~(a = b) /\ (b <= a) = b < a``,
    REWRITE_TAC [WORD_LESS_OR_EQ] \\ METIS_TAC [WORD_LESS_NOT_EQ])
  val xs = map f [word_gt_def,word_lt_def,word_le_def,word_ge_def]
  val ys = [WORD_GREATER_EQ,WORD_GREATER,WORD_NOT_LOWER_EQUAL]
  val zs = [WORD_NOT_LOWER,GSYM WORD_LOWER_OR_EQ,WORD_NOT_LESS,WORD_NOT_LESS_EQUAL] 
  val qs1 = [GSYM WORD_LESS_OR_EQ, GSYM (RW1 [DISJ_COMM] WORD_LESS_OR_EQ)] 
  val qs2 = [GSYM WORD_LOWER_OR_EQ, GSYM (RW1 [DISJ_COMM] WORD_LOWER_OR_EQ)] 
  val ls = [lemma1,lemma2,lemma3,lemma4]
  in LIST_CONJ (xs @ ys @ zs @ qs1 @ qs2 @ ls) end);

fun QGENL xs th = foldr (uncurry Q.GEN) th xs;
fun GENL_save_thm (name,vars,th) = save_thm(name,QGENL vars th);

val ARM_RUN_THM = GENL_save_thm("ARM_RUN_THM",[`P`,`Q`],  
  (REWRITE_CONV [ARM_RUN_def,RUN_def,ARMproc_def] THENC
   REWRITE_CONV [GSYM ARMproc_def,ARMproc_IN_PROCESSORS] THENC
   REWRITE_CONV [ARMnext_rel_def,rel_sequence_EQ_EXISTS_run]) ``ARM_RUN P Q``);

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

val wLENGTH_CONS = store_thm("wLENGTH_CONS",
  ``!x xs. wLENGTH (x::xs) = 1w + wLENGTH xs``,
  REWRITE_TAC [wLENGTH_def,LENGTH,RW1[ADD_COMM]ADD1,word_add_n2w]);

val SNOC_blank_ms = store_thm("SNOC_blank_ms",
  ``(!a. blank_ms a 0 = emp) /\
    (!a i. blank_ms a (SUC i) = blank_ms a i * ~M (a + n2w i))``,
  STRIP_TAC THEN1 REWRITE_TAC [blank_ms_def]
  \\ Induct_on `i` THEN1 FULL_SIMP_TAC bool_ss [blank_ms_def,emp_STAR,WORD_ADD_0]
  \\ ONCE_REWRITE_TAC [blank_ms_def] 
  \\ ASM_REWRITE_TAC [RW1[ADD_COMM]ADD1,word_add_n2w,GSYM WORD_ADD_ASSOC,STAR_ASSOC]);

val SNOC_ms = store_thm("SNOC_ms",
  ``(!a. ms a [] = emp) /\
    (!a x xs. ms a (SNOC x xs) = ms a xs * M (a + wLENGTH xs) x)``,
  STRIP_TAC THEN1 REWRITE_TAC [ms_def] \\ Induct_on `xs`
  THEN1 FULL_SIMP_TAC bool_ss [wLENGTH_def,LENGTH,WORD_ADD_0,SNOC,ms_def,emp_STAR]
  \\ ASM_REWRITE_TAC [SNOC,ms_def,STAR_ASSOC,wLENGTH_CONS,WORD_ADD_ASSOC]);

val blank_ms_EQ_ms = store_thm("blank_ms_EQ_ms",
  ``!a n. blank_ms a n = SEP_EXISTS xs. ms a xs * cond (LENGTH xs = n)``,
  Induct_on `n`
  \\ ASM_SIMP_TAC (bool_ss++sep2_ss) [blank_ms_def,LENGTH_NIL,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,ms_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [  
    FULL_SIMP_TAC (bool_ss++sep2_ss) [SEP_HIDE_THM]    
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `y'::y` \\ ASM_REWRITE_TAC [LENGTH,ADD1,EQ_ADD_RCANCEL,ms_def],    
    Cases_on `y` \\ FULL_SIMP_TAC bool_ss [LENGTH,ADD1,EQ_ADD_RCANCEL,SEP_HIDE_THM] 
    THEN1 `F` by DECIDE_TAC \\ Q.EXISTS_TAC `t` \\ ASM_SIMP_TAC (bool_ss++sep2_ss) []
    \\ FULL_SIMP_TAC bool_ss [ms_def,SEP_EXISTS] \\ Q.EXISTS_TAC `h`
    \\ ASM_REWRITE_TAC []]);

val SEP_IMP_ms_blank_ms = store_thm("SEP_IMP_ms_blank_ms",
  ``!xs a. SEP_IMP (ms a xs) (blank_ms a (LENGTH xs))``,
  Induct \\ FULL_SIMP_TAC std_ss [ms_def,blank_ms_def,LENGTH] THEN1 REWRITE_TAC [SEP_IMP_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SEP_IMP_STAR \\ ASM_REWRITE_TAC [SEP_HIDE_THM] 
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []);


(* theorems for ARM_RUN -------------------------------------------------------- *)

fun ARM_RUN_INST th = 
  REWRITE_RULE [GSYM ARM_RUN_def, GSYM ARM_PROG_def] (Q.ISPEC `ARMproc` th);

fun save_ARM_RUN name rule = save_thm(name,ARM_RUN_INST rule);

val _ = save_ARM_RUN "ARM_RUN_FRAME" RUN_FRAME;
val _ = save_ARM_RUN "ARM_RUN_STRENGTHEN_PRE" RUN_STRENGTHEN_PRE;
val _ = save_ARM_RUN "ARM_RUN_WEAKEN_POST" RUN_WEAKEN_POST;
val _ = save_ARM_RUN "ARM_RUN_COMPOSE" RUN_COMPOSE;
val _ = save_ARM_RUN "ARM_RUN_HIDE_PRE" RUN_HIDE_PRE;
val _ = save_ARM_RUN "ARM_RUN_HIDE_POST" RUN_HIDE_POST;
val _ = save_ARM_RUN "ARM_RUN_LOOP" RUN_LOOP;

val ARM_RUN_REFL = store_thm("ARM_RUN_REFL",
  ``!P. ARM_RUN P P``,
  REWRITE_TAC [ARM_RUN_def] \\ STRIP_TAC
  \\ MATCH_MP_TAC RUN_REFL \\ REWRITE_TAC [ARMproc_IN_PROCESSORS]);

val ARM_RUN_SEMANTICS = store_thm("ARM_RUN_SEMANTICS",
  ``ARM_RUN P Q =
    !y s. P (arm2set' y s) ==>
          ?k. let s' = STATE_ARM_MEM k s in
              Q (arm2set' y s') /\ (arm2set'' y s = arm2set'' y s')``,
  SIMP_TAC std_ss [ARM_RUN_THM,GSPECIFICATION,ARMsets_def,RES_FORALL]
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
  ``!P P' Q a x y. ARM_RUN (R a x * R a y * P \/ P') Q = ARM_RUN P' Q``,
  SIMP_TAC std_ss [ARM_RUN_SEMANTICS,R_def,one_STAR,GSYM STAR_ASSOC,SEP_DISJ_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC THEN1 METIS_TAC []
  \\ Cases_on `y'` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ REWRITE_TAC [IN_arm2set',GSYM AND_IMP_INTRO]
  \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set',IN_arm2set',IN_DELETE]
  \\ METIS_TAC []);

val ARM_RUN_byte_11 = store_thm("ARM_RUN_byte_11",
  ``!P P' Q a x y. ARM_RUN (byte a x * byte a y * P \/ P') Q = ARM_RUN P' Q``,
  SIMP_TAC std_ss [ARM_RUN_SEMANTICS,byte_def,one_STAR,GSYM STAR_ASSOC,SEP_DISJ_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC THEN1 METIS_TAC []
  \\ Cases_on `y'` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ REWRITE_TAC [IN_arm2set',GSYM AND_IMP_INTRO]
  \\ ASM_SIMP_TAC bool_ss [DELETE_arm2set',IN_arm2set',IN_DELETE]
  \\ METIS_TAC []);

val ARM_RUN_M_11 = store_thm("ARM_RUN_M_11",
  ``!P P' Q a x y. ARM_RUN (M a x * M a y * P \/ P') Q = ARM_RUN P' Q``,
  REWRITE_TAC [M_def]
  \\ MOVE_STAR_TAC `b1*b2*b3*b4*(b5*b6*b7*b8)*t` `b4*b8*(b2*b3*b1*b6*b7*b5*t)`
  \\ REWRITE_TAC [ARM_RUN_byte_11]);

val M_NEQ_M = store_thm("M_NEQ_M",
  ``!a x b y. ~(a = b) ==> ~(M a x = M b y)``,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [M_def,byte_def,one_def,STAR_def,SPLIT_def]
  \\ REWRITE_TAC [INSERT_UNION_EQ,UNION_EMPTY]
  \\ REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ Q.PAT_ASSUM `!x.b` (ASSUME_TAC o Q.SPEC `
         {Mem (addr32 a + 3w) ((31 >< 24) (x:word32));
          Mem (addr32 a + 2w) ((23 >< 16) x);
          Mem (addr32 a + 1w) ((15 >< 8) x);
          Mem (addr32 a + 0w) ((7 >< 0) x)}`)
  \\ FULL_SIMP_TAC bool_ss [SET_EQ_SUBSET,INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY]
  \\ SRW_TAC [] []
  \\ Q.PAT_ASSUM `~(a = b)` ASSUME_TAC
  \\ FULL_SIMP_TAC bool_ss [addr32_NEQ_addr32,addr32_11]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [])

val M_NEQ_M2 = store_thm("M_NEQ_M2",
  ``!a x y. ~(x = y) ==> ~(M a x = M a y)``,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [M_def,byte_def,one_def,STAR_def,SPLIT_def]
  \\ REWRITE_TAC [INSERT_UNION_EQ,UNION_EMPTY]
  \\ REPEAT STRIP_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ Q.PAT_ASSUM `!x.b` (ASSUME_TAC o Q.SPEC `
         {Mem (addr32 a + 3w) ((31 >< 24) (x:word32));
          Mem (addr32 a + 2w) ((23 >< 16) x);
          Mem (addr32 a + 1w) ((15 >< 8) x);
          Mem (addr32 a + 0w) ((7 >< 0) x)}`)
  \\ FULL_SIMP_TAC bool_ss [SET_EQ_SUBSET,INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY]
  \\ SRW_TAC [] []
  \\ Q.PAT_ASSUM `~(x = y)` ASSUME_TAC
  \\ FULL_SIMP_TAC bool_ss [addr32_NEQ_addr32,addr32_11]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ METIS_TAC [concat_bytes]);

val M_EQ_M = store_thm("M_EQ_M",
  ``!a b x y. (M a x = M b y) = (a = b) /\ (x = y)``,
  METIS_TAC [M_NEQ_M,M_NEQ_M2]);


(* theorems for ARM_GPROG ------------------------------------------------------ *)

fun ARM_GPROG_INST th = 
  REWRITE_RULE [GSYM ARM_GPROG_def, GSYM ARM_GPROG_def] (Q.ISPEC `ARMproc` th);

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


(* theorems for ARM_PROG ------------------------------------------------------- *)

fun ARM_PROG_INST th = 
  REWRITE_RULE [GSYM ARM_PROG_def, GSYM ARM_PROG_def] (Q.ISPEC `ARMproc` th);

fun save_ARM_PROG name rule = save_thm(name,ARM_PROG_INST rule);

val _ = save_ARM_PROG "ARM_PROG_FRAME" PROG_FRAME;
val _ = save_ARM_PROG "ARM_PROG_MERGE" PROG_MERGE;
val _ = save_ARM_PROG "ARM_PROG_MERGE_POST" PROG_MERGE_POST;
val _ = save_ARM_PROG "ARM_PROG_MERGE_CODE" PROG_MERGE_CODE;
val _ = save_ARM_PROG "ARM_PROG_ABSORB_POST" PROG_ABSORB_POST;
val _ = save_ARM_PROG "ARM_PROG_FALSE_PRE" PROG_FALSE_PRE;
val _ = save_ARM_PROG "ARM_PROG_FALSE_POST" PROG_FALSE_POST;
val _ = save_ARM_PROG "ARM_PROG_STRENGTHEN_PRE" PROG_STRENGTHEN_PRE;
val _ = save_ARM_PROG "ARM_PROG_WEAKEN_POST" PROG_WEAKEN_POST;
val _ = save_ARM_PROG "ARM_PROG_WEAKEN_POST1" PROG_WEAKEN_POST1;
val _ = save_ARM_PROG "ARM_PROG_PART_STRENGTHEN_PRE" PROG_PART_STRENGTHEN_PRE;
val _ = save_ARM_PROG "ARM_PROG_PART_WEAKEN_POST" PROG_PART_WEAKEN_POST;
val _ = save_ARM_PROG "ARM_PROG_PART_WEAKEN_POST1" PROG_PART_WEAKEN_POST1;
val _ = save_ARM_PROG "ARM_PROG_ADD_CODE" PROG_ADD_CODE;
val _ = save_ARM_PROG "ARM_PROG_APPEND_CODE" PROG_APPEND_CODE;
val _ = save_ARM_PROG "ARM_PROG_MOVE_COND" PROG_MOVE_COND;
val _ = save_ARM_PROG "ARM_PROG_HIDE_PRE" PROG_HIDE_PRE;
val _ = save_ARM_PROG "ARM_PROG_HIDE_POST1" PROG_HIDE_POST1;
val _ = save_ARM_PROG "ARM_PROG_HIDE_POST" PROG_HIDE_POST;
val _ = save_ARM_PROG "ARM_PROG_EXISTS_PRE" PROG_EXISTS_PRE;
val _ = save_ARM_PROG "ARM_PROG_COMPOSE" PROG_COMPOSE;
val _ = save_ARM_PROG "ARM_PROG_COMPOSE_0" PROG_COMPOSE_0;
val _ = save_ARM_PROG "ARM_PROG_COMPOSE_I" PROG_COMPOSE_I;
val _ = save_ARM_PROG "ARM_PROG_LOOP" PROG_LOOP;
val _ = save_ARM_PROG "ARM_PROG_LOOP_MEASURE" PROG_LOOP_MEASURE;
val _ = save_ARM_PROG "ARM_PROG_EXTRACT_POST" PROG_EXTRACT_POST;
val _ = save_ARM_PROG "ARM_PROG_EXTRACT_CODE" PROG_EXTRACT_CODE;

val ARM_PROG_HIDE_PRE = save_ARM_PROG "ARM_PROG_HIDE_PRE" PROG_HIDE_PRE;

val ARM_PROG_EMPTY = store_thm("ARM_PROG_EMPTY",
  ``ARM_PROG emp [] {} emp {}``,
  REWRITE_TAC [ARM_PROG_def] \\ MATCH_MP_TAC PROG_EMPTY 
  \\ REWRITE_TAC [ARMproc_IN_PROCESSORS]);

val ARM_PROG_INTRO = save_thm("ARM_PROG_INTRO", let 
  val th = Q.ISPECL [`ARMsets`,`ARMnext_rel`,`ARMpc`,`ARMi`] PROG_INTRO
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
  ``!P cs C Q Z a x y. ARM_PROG (R a x * R a y * P) cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,ARM_GPROG_THM,GPROG_DISJ_CLAUSES]
  \\ MOVE_STAR_TAC `a1*a2*p*m*pc` `a1*a2*(p*m*pc)` 
  \\ REWRITE_TAC [RW [SEP_DISJ_CLAUSES] (Q.SPECL [`P`,`SEP_F`] ARM_RUN_R_11)]
  \\ REWRITE_TAC [ARM_RUN_def,RUN_def,RUN_FALSE_PRE]);

val ARM_PROG_byte_11 = store_thm("ARM_PROG_byte_11",
  ``!P cs C Q Z a x y. ARM_PROG (byte a x * byte a y * P) cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,ARM_GPROG_THM,GPROG_DISJ_CLAUSES]
  \\ MOVE_STAR_TAC `a1*a2*p*m*pc` `a1*a2*(p*m*pc)` 
  \\ REWRITE_TAC [RW [SEP_DISJ_CLAUSES] (Q.SPECL [`P`,`SEP_F`] ARM_RUN_byte_11)]
  \\ REWRITE_TAC [ARM_RUN_def,RUN_def,RUN_FALSE_PRE]);

val ARM_PROG_M_11 = store_thm("ARM_PROG_M_11",
  ``!P cs C Q Z a x y. ARM_PROG (M a x * M a y * P) cs C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,ARM_GPROG_THM,GPROG_DISJ_CLAUSES]
  \\ MOVE_STAR_TAC `a1*a2*p*m*pc` `a1*a2*(p*m*pc)` 
  \\ REWRITE_TAC [RW [SEP_DISJ_CLAUSES] (Q.SPECL [`P`,`SEP_F`] ARM_RUN_M_11)]
  \\ REWRITE_TAC [ARM_RUN_def,RUN_def,RUN_FALSE_PRE]);

val ARM_PROG_RR = store_thm("ARM_PROG_RR",
  ``!a x y P code C Q Z. ARM_PROG (P * R a x * R a y) code C Q Z``,
  MOVE_STAR_TAC `p*x*y` `x*y*p` \\ REWRITE_TAC [ARM_PROG_R_11]);

val ARM_PROG_R15 = store_thm("ARM_PROG_R15",
  ``!x P code C Q Z. ARM_PROG (P * R 15w x) code C Q Z``,
  REWRITE_TAC [ARM_PROG_THM,ARM_GPROG_THM,GPROG_DISJ_CLAUSES,ARMpc_def,R30_def]
  \\ MOVE_STAR_TAC `p*r*m*(u*f)` `r*u*(p*m*f)` 
  \\ REWRITE_TAC [RW [SEP_DISJ_CLAUSES] (Q.SPECL [`P`,`SEP_F`] ARM_RUN_R_11)]
  \\ REWRITE_TAC [ARM_RUN_def,RUN_def,RUN_FALSE_PRE]);

val ARM_PROG_CONTAINS_M_STAR_M = store_thm("ARM_PROG_CONTAINS_M_STAR_M",
  ``!xs a P C Q Z.
      SEP_CONTAINS (M i x * M i y) P ==> (ARM_PROG P code C Q Z = T)``,
  REWRITE_TAC [SEP_CONTAINS_def] \\ REPEAT STRIP_TAC 
  \\ ASM_REWRITE_TAC [ARM_PROG_M_11]);

val SUC_LE_LENGTH = prove(
  ``!xs m. SUC m <= LENGTH xs ==> ?ys z zs. (xs = ys ++ z::zs) /\ (LENGTH ys = m)``,
  Induct \\ REWRITE_TAC [LENGTH,DECIDE ``~(n+1 <= 0)``,ADD1,LE_ADD_RCANCEL]
  \\ STRIP_TAC \\ Cases \\ STRIP_TAC << [  
    Q.EXISTS_TAC `[]` \\ Q.EXISTS_TAC `h` \\ Q.EXISTS_TAC `xs`
    \\ REWRITE_TAC [APPEND_NIL,LENGTH,APPEND],
    Q.PAT_ASSUM `!x.b` IMP_RES_TAC \\ ASM_REWRITE_TAC []
    \\ Q.EXISTS_TAC `h::ys` \\ Q.EXISTS_TAC `z` \\ Q.EXISTS_TAC `zs`
    \\ ASM_REWRITE_TAC [APPEND,LENGTH]]);

val ms_APPEND = store_thm("ms_APPEND",
  ``!xs ys a. ms a (xs ++ ys) = ms a xs * ms (a + wLENGTH xs) ys``,
  Induct \\ REWRITE_TAC [APPEND_NIL,ms_def,emp_STAR,wLENGTH_def,LENGTH,WORD_ADD_0]
  \\ REWRITE_TAC [ONCE_REWRITE_RULE[ADD_COMM]ADD1,
      GSYM word_add_n2w,WORD_ADD_ASSOC,GSYM STAR_ASSOC]
  \\ ASM_REWRITE_TAC [APPEND,ms_def,wLENGTH_def]);

val ARM_PROG_CONTAINS_ms = store_thm("ARM_PROG_CONTAINS_ms",
  ``!xs a P C Q Z.
      SEP_CONTAINS (ms a xs) P ==>
      ((LENGTH xs <= 2**30 ==> ARM_PROG P code C Q Z) = ARM_PROG P code C Q Z)``,
  NTAC 6 STRIP_TAC \\ Cases_on `LENGTH xs <= 2**30` \\ ASM_REWRITE_TAC [] 
  \\ FULL_SIMP_TAC bool_ss [NOT_LEQ] \\ IMP_RES_TAC SUC_LE_LENGTH
  \\ Cases_on `ys` THEN1 FULL_SIMP_TAC std_ss [LENGTH]
  \\ ASM_REWRITE_TAC [ms_APPEND,wLENGTH_def]
  \\ `n2w (2**30) = 0w:word30` by 
   (ONCE_REWRITE_TAC [GSYM n2w_mod] \\ REWRITE_TAC [dimword_def]
    \\ SIMP_TAC (bool_ss++wordsLib.SIZES_ss) []
    \\ SIMP_TAC bool_ss [DIVMOD_ID,LESS_MOD,EVAL ``0<2**30``])
  \\ ASM_REWRITE_TAC [WORD_ADD_0]
  \\ REWRITE_TAC [ms_def]
  \\ REPEAT STRIP_TAC
  \\ `SEP_CONTAINS (M a h * M a z) P` by ALL_TAC << [
    FULL_SIMP_TAC bool_ss [SEP_CONTAINS_def]
    \\ Q.EXISTS_TAC `ms (a + 1w) t * ms (a + 1w) zs * F'`
    \\ SIMP_TAC (bool_ss++star_ss) [],
    IMP_RES_TAC ARM_PROG_CONTAINS_M_STAR_M \\ ASM_REWRITE_TAC []]);

val ARM_PROG_HIDE_PRE_ms = store_thm("ARM_PROG_HIDE_PRE_ms",
  ``!a P. ARM_PROG (P * blank_ms a n) code C Q Z =
          !xs. (LENGTH xs = n) ==> ARM_PROG (P * ms a xs) code C Q Z``,
  Induct_on `n` \\ ASM_SIMP_TAC bool_ss [LENGTH_NIL,blank_ms_def,ms_def,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Cases_on `xs` 
    \\ FULL_SIMP_TAC bool_ss [LENGTH,DECIDE ``~(0 = n + 1)``,ADD1,EQ_ADD_RCANCEL]
    \\ Q.PAT_ASSUM `!xs. b ==> c` 
      (ASSUME_TAC o RW [GSYM ARM_PROG_HIDE_PRE] o 
       MOVE_STAR_RULE `x*y*z` `x*z*y` o UNDISCH o Q.SPEC `t`)       
    \\ REWRITE_TAC [ms_def]
    \\ MOVE_STAR_TAC `x*(y*z)` `x*z*y`
    \\ ASM_REWRITE_TAC [],
    MOVE_STAR_TAC `x*y*z` `x*z*y`
    \\ REWRITE_TAC [GSYM ARM_PROG_HIDE_PRE] \\ REPEAT STRIP_TAC
    \\ MOVE_STAR_TAC `x*y*z` `x*(z*y)`
    \\ REWRITE_TAC [GSYM ms_def]
    \\ `LENGTH (y::xs) = SUC n` by ASM_REWRITE_TAC [LENGTH]
    \\ METIS_TAC []]);

val mset_SING = prove(
  ``mset ARMi p ([y],g) = {M (g p) y}``,
  ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [mset_def,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ARMi_def,LENGTH,DECIDE ``k<1=(k=0)``]  
  THEN1 (Cases_on `x'` \\ FULL_SIMP_TAC std_ss [EL,HD,WORD_ADD_0])
  \\ Q.EXISTS_TAC `(y,0)`  \\ SIMP_TAC std_ss [EL,HD,WORD_ADD_0]);

val IMP_ARM_RUN_mpool = store_thm("IMP_ARM_RUN_mpool",
  ``ARM_RUN ((M (f p) x * M (g p) y * P):'a ARMset -> bool) (M (f p) x * M (g p) y * Q) ==>
    ((f p = g p) /\ (x = y) ==> ARM_RUN (M (f p) x * P) (M (f p) x * Q)) ==>
    ARM_RUN (mpool ARMi p {([x],f);([y],g)} * P) 
            (mpool ARMi p {([x],f);([y],g)} * Q)``,
  `BIGUNION {mset ARMi p z | z IN {([x],f); ([y],g)}} = {M (f p) x; M (g p) y}` by 
   (`{mset ARMi p z | z IN {([x],f); ([y],g)}} = {{M (f p) x}; {M (g p) y}}` by 
       (ONCE_REWRITE_TAC [EXTENSION]
        \\ SIMP_TAC std_ss [GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]
        \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
        \\ ASM_SIMP_TAC std_ss [mset_SING] \\ METIS_TAC [mset_SING])
    \\ ASM_REWRITE_TAC [BIGUNION_INSERT,INSERT_UNION_EQ,UNION_EMPTY,BIGUNION_EMPTY])        
  \\ Cases_on `M (f p) x = M (g p) y`
  \\ ASM_SIMP_TAC std_ss [INSERT_INSERT,BIGSTAR_ONE,mpool_def,GSYM M_EQ_M] 
  \\ `~(M (f p) x IN {M (g p) y})` by ASM_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
  \\ ASM_SIMP_TAC bool_ss [BIGSTAR_INSERT,BIGSTAR_ONE]);


(* theorems for the lib files -------------------------------------------------- *)

val ARM_PROG_EMPTY_CODE = store_thm("ARM_PROG_EMPTY_CODE",
  ``ARM_PROG P cs (([],f) INSERT C) Q Z = ARM_PROG P cs C (Q:('a ARMset -> bool)) Z``,
  REWRITE_TAC [ARM_PROG_THM] \\ ONCE_REWRITE_TAC [INSERT_COMM,ARM_GPROG_def]
  \\ REWRITE_TAC [GPROG_EMPTY_CODE]);

val ARM_PROG_ABSORB_POST_LEMMA = store_thm("ARM_PROG_ABSORB_POST_LEMMA",
  ``ARM_PROG (P:'a ARMset -> bool) cs C SEP_F ((Q,pcADD x) INSERT Z) ==>
    (x = wLENGTH cs) ==> ARM_PROG P cs C Q Z``,
  REPEAT STRIP_TAC 
  \\ FULL_SIMP_TAC bool_ss [GSYM PROG_EXTRACT_POST,GSYM pcINC_def,ARM_PROG_def]);

val STATUS_MOVE = store_thm("STATUS_MOVE",
  ``!P Q x. (S x * P = P * S x) /\ (P * S x * Q = P * Q * (S x):'a ARMset -> bool)``,
  SIMP_TAC (bool_ss++star_ss) []);

val ARRANGE_COMPOSE_LEMMA = store_thm("ARRANGE_COMPOSE_LEMMA",
  ``!P:('a ARMset -> bool) M M' Q cs cs' C C' Z Z'.
      ARM_PROG P cs C M Z /\ ARM_PROG M' cs' C' Q Z' ==> (M = M') ==> 
      ARM_PROG P (cs ++ cs') (C UNION setINC cs C') Q (Z UNION setINC cs Z')``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC PROG_COMPOSE 
  \\ Q.EXISTS_TAC `M'` \\ FULL_SIMP_TAC std_ss []);

val FALSE_COMPOSE_LEMMA = store_thm("FALSE_COMPOSE_LEMMA",
  ``ARM_PROG (P1:('a ARMset -> bool)) code1 C1 SEP_F Z1 /\ 
    ARM_PROG (P2:('b ARMset -> bool)) code2 C Q Z ==>
    ARM_PROG P1 (code1++code2) C1 SEP_F Z1``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC PROG_APPEND_CODE \\ ASM_REWRITE_TAC []);

val ARM_PROG_COMPOSE_FRAME = store_thm("ARM_PROG_COMPOSE_FRAME",
  ``ARM_PROG (Q1 * P2:('a ARMset -> bool)) c2 cc2 Q3 Z2 ==>
    ARM_PROG P1 c1 cc1 (Q1 * Q2) Z1 ==> 
    ARM_PROG (P1 * P2) (c1 ++ c2) 
      (cc1 UNION setINC c1 cc2) (Q3 * Q2) 
      (setSTAR P2 Z1 UNION setINC c1 (setSTAR Q2 Z2))``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC PROG_COMPOSE
  \\ Q.EXISTS_TAC `Q1 * P2 * Q2` \\ STRIP_TAC
  << [MOVE_STAR_TAC `q*t*p` `(q*p)*t`,ALL_TAC] \\ METIS_TAC [PROG_FRAME]);

val ARM_PROG_DUPLICATE_COND_LEMMA = store_thm("ARM_PROG_DUPLICATE_COND_LEMMA",
  ``ARM_PROG (P * cond h) code C (Q:('a ARMset -> bool)) Z ==>
    ARM_PROG (P * cond h) code C (Q * cond h) (setSTAR (cond h) Z)``,
  REWRITE_TAC [ARM_PROG_def,PROG_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (bool_ss++sep2_ss) []  
  \\ `setSTAR emp Z = Z` by ALL_TAC THENL [ALL_TAC,METIS_TAC []] 
  \\ SIMP_TAC std_ss [EXTENSION,setSTAR_def,GSPECIFICATION,emp_STAR]  
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `x` \\ Cases_on `x` \\ ASM_SIMP_TAC std_ss []);

val ARM_PROG_COMPOSE_FRAME2 = store_thm("ARM_PROG_COMPOSE_FRAME2",
  ``(b ==> ARM_PROG (Q1 * P2) cs2 cc2 Q3 Z2) ==>
    ARM_PROG (P1:'a ARMset -> bool) cs1 cc1 (Q1 * Q2) Z1 ==> b ==>
    ARM_PROG (P1 * P2) (cs1 ++ cs2) 
      (cc1 UNION setINC cs1 cc2) (Q3 * Q2) 
      (setSTAR P2 Z1 UNION setINC cs1 (setSTAR Q2 Z2))``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC PROG_COMPOSE
  \\ Q.PAT_ASSUM `b ==> bbb` IMP_RES_TAC
  \\ Q.EXISTS_TAC `Q1 * P2 * Q2` \\ STRIP_TAC
  << [MOVE_STAR_TAC `q*t*p` `(q*p)*t`,ALL_TAC] \\ METIS_TAC [PROG_FRAME]);

val EQ_IMP_IMP = store_thm("EQ_IMP_IMP",``(x:bool=y:bool) ==> x ==> y``,METIS_TAC []);

val EXPAND_PAIR = store_thm("EXPAND_PAIR",
  ``!x:'a y:'b z. ((x,y) = z) = (x = FST z) /\ (y = SND z)``,
  Cases_on `z` \\ REWRITE_TAC [PAIR_EQ,FST,SND]);

val COMPILER_STEP_LEMMA = store_thm("COMPILER_STEP_LEMMA",
  ``!P cc cs Q Q' c b f Z. 
      ARM_PROG (P: 'a ARMset -> bool) cs cc Q ((Q' * cond c * sidecond b,f) INSERT Z) ==>
      (c ==> (b' = b)) ==> ARM_PROG P cs cc Q ((Q' * cond c * sidecond b',f) INSERT Z)``,
  Cases_on `c` \\ SIMP_TAC (bool_ss++sep2_ss) []);

val sidecond_CONJ = store_thm("sidecond_CONJ",
  ``sidecond (p /\ q) = sidecond p * (cond q):'a ARMset -> bool``,
  SIMP_TAC (bool_ss++sep2_ss) [sidecond_def]);

val ARM_PROG_SUBSET_CODE = store_thm("ARM_PROG_SUBSET_CODE",
  ``!P:('a ARMset -> bool) code C1 Q Z.
      ARM_PROG P code C1 Q Z ==> !C2. C1 SUBSET C2 ==> ARM_PROG P code C2 Q Z``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC
  \\ `?X. C2 = C1 UNION X` by ALL_TAC << [ 
    Q.EXISTS_TAC `C2` \\ FULL_SIMP_TAC bool_ss [EXTENSION,IN_UNION,SUBSET_DEF] 
    \\ METIS_TAC [],
    ASM_REWRITE_TAC [] \\ MATCH_MP_TAC PROG_ADD_CODE \\ ASM_REWRITE_TAC []]);

val ARM_PROG_APPEND_CODE_SET = store_thm("ARM_PROG_APPEND_CODE_SET",
  ``ARM_PROG (P:'a ARMset -> bool) cs1 {(cs2,pcADD x)} SEP_F Z ==>
    (wLENGTH cs1 = x) ==> ARM_PROG P (cs1 ++ cs2) {} SEP_F Z``,
  REWRITE_TAC [ARM_PROG_def] \\ ONCE_REWRITE_TAC [PROG_EXTRACT_CODE]
  \\ ONCE_REWRITE_TAC [GSYM PROG_MERGE_CODE]
  \\ SIMP_TAC std_ss [pcINC_def]);

val ARM_PROG_PREPEND_CODE = store_thm("ARM_PROG_PREPEND_CODE",
  ``ARM_PROG (P:'a ARMset -> bool) [] {(cs1,f)} Q Z ==> 
    !cs2. ARM_PROG P [] {(cs2 ++ cs1,pcADD (0w - wLENGTH cs2) o f)} Q Z``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o RW [INSERT_UNION_EQ,UNION_EMPTY] o RW1 [UNION_COMM] o Q.SPEC `{(cs2,pcADD (0w - wLENGTH cs2) o f)}` o MATCH_MP PROG_ADD_CODE)
  \\ ONCE_REWRITE_TAC [GSYM PROG_MERGE_CODE]
  \\ REWRITE_TAC [pcINC_def,pcADD_pcADD]
  \\ `!x:word30 f:word30->word30. pcADD x o pcADD (0w - x) o f = f` by
    (SIMP_TAC std_ss [FUN_EQ_THM,pcADD_def,WORD_SUB_LZERO,WORD_ADD_ASSOC]
     \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_REFL,WORD_ADD_0])
  \\ ASM_REWRITE_TAC []);

val ARM_PROG_MERGE_CODE_pcADD = store_thm("ARM_PROG_MERGE_CODE_pcADD",
  ``ARM_PROG (P:'a ARMset -> bool) code ((cs1,pcADD x) INSERT (cs2,pcADD y) INSERT C) Q Z ==>
    (wLENGTH cs1 = y - x) ==>
    ARM_PROG P code ((cs1 ++ cs2,pcADD x) INSERT C) Q Z``,
  REWRITE_TAC [ARM_PROG_def] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [GSYM PROG_MERGE_CODE,pcINC_def,pcADD_pcADD,WORD_SUB_ADD]);


(* theorems for ARM_PROC ------------------------------------------------------- *)

val ARM_PROC_CALL = store_thm("ARM_PROC_CALL",
  ``!cs P Q C k.
      CALL ARMproc (R30 14w) ((~(R 14w)):^(ty_antiq ARMel_type) set -> bool) cs (pcADD k) /\ 
      ARM_PROC P (Q:^(ty_antiq ARMel_type) set -> bool) C ==>
      ARM_PROG (P * ~R 14w) cs (setADD k C) (Q * ~R 14w) {}``,
  REWRITE_TAC [setADD_def,ARM_PROG_def,ARM_PROC_def,CALL_def] 
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC PROC_CALL
  \\ Q.EXISTS_TAC `R30 14w` \\ ASM_REWRITE_TAC []);

val _ = save_thm("ARM_PROC_RECURSION",PROC_RECURSION);

(* spec model *)

val ARM_SPEC2_def = Define `
  ARM_SPEC2 c (P,p) C (Q,q) =
    SPEC (ARM_MODEL :('a ARMel, 32, bool[32]) processor)
      (P,p) C (Q,q) /\
    !x. SPEC (ARM_MODEL :('a ARMel, 32, bool[32]) processor)
        (S x * nPASS c x,p) C (S x,p + 4w)`;

val RUN_ARM_MODEL_LEMMA = prove(
  ``!P Q. RUN ARMproc P Q = RUN ARM_MODEL P Q``,
  REWRITE_TAC [ARMproc_def,ARM_MODEL_def,RUN_def]
  \\ REWRITE_TAC [GSYM ARMproc_def,GSYM ARM_MODEL_def]
  \\ REWRITE_TAC [ARMproc_IN_PROCESSORS,ARM_MODEL_IN_PROCESSORS]);

val mpool_LEMMA = prove(
  ``mpool g p {([c],f)} = g (f p,c)``,
  SIMP_TAC std_ss [mpool_def,IN_INSERT,NOT_IN_EMPTY]
  \\ `{mset g p z | z = ([c],f)} = {mset g p ([c],f)}` by ALL_TAC << [  
    ONCE_REWRITE_TAC [EXTENSION]
    \\ REWRITE_TAC [IN_INSERT,NOT_IN_EMPTY,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    THEN1 (Cases_on `x'` \\ FULL_SIMP_TAC bool_ss [PAIR_EQ])
    \\ Q.EXISTS_TAC `([c],f)` \\ ASM_SIMP_TAC std_ss [],
    `g (f p,c) = BIGSTAR (BIGUNION {{g (f p,c)}})` by ALL_TAC << [    
      REWRITE_TAC [BIGUNION_INSERT,BIGUNION_EMPTY,UNION_EMPTY]
      \\ REWRITE_TAC [BIGSTAR_ONE],  
      ONCE_ASM_REWRITE_TAC []
      \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> 
          (BIGSTAR (BIGUNION {x}) = BIGSTAR (BIGUNION {y}))``)
      \\ REWRITE_TAC [mset_def,LENGTH,DECIDE ``n < SUC 0 = (n = 0)``]
      \\ ONCE_REWRITE_TAC [EXTENSION]
      \\ REWRITE_TAC [IN_INSERT,NOT_IN_EMPTY,GSPECIFICATION]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      THEN1 (Cases_on `x'` \\ FULL_SIMP_TAC std_ss [EL,HD,WORD_ADD_0])
      \\ Q.EXISTS_TAC `(c,0)` \\ ASM_SIMP_TAC std_ss [EL,HD,WORD_ADD_0]]]);

val SPEC_ARM_MODEL_INTRO = store_thm("SPEC_ARM_MODEL_INTRO",
  ``ARM_PROG P [c] {} Q {} ==>
    !p:word32. SPEC ARM_MODEL (P,p) {([c],p)} (Q,p + 4w)``,
  REWRITE_TAC [ARM_PROG_THM,ARM_MODEL_def,ARM_GPROG_def]
  \\ SIMP_TAC std_ss [SPEC_def,setAPP_CLAUSES,pcINC_def,pcADD_def,fix_pos_def,set_apply_CLAUSES]
  \\ REWRITE_TAC [GPROG_def,ARMproc_def,ARM_MODEL_def]  
  \\ REWRITE_TAC [GSYM ARMproc_def,GSYM ARM_MODEL_def,RUN_ARM_MODEL_LEMMA]  
  \\ REWRITE_TAC [GPROG_DISJ_CLAUSES]
  \\ REWRITE_TAC [ARMpc_def,ARMpc2_def]
  \\ SIMP_TAC (std_ss++sep2_ss) [mpool_LEMMA,GSYM RUN_MOVE_COND]
  \\ SIMP_TAC std_ss [wLENGTH_def,LENGTH,ARMi_def,ARMi2_def,R30_def]
  \\ SIMP_TAC (bool_ss++sep2_ss) [GSYM aligned_def,
       SIMP_RULE std_ss [word_mul_n2w] (Q.SPECL [`x`,`1w`] aligned_MULT)]
  \\ SIMP_TAC std_ss [addr32_ADD,addr32_n2w]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [WORD_ADD_COMM]))
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GSYM (RW [GSYM aligned_def] addr32_addr30))
  \\ ONCE_ASM_REWRITE_TAC []  
  \\ Q.PAT_ASSUM `x = y` (fn th => ALL_TAC)
  \\ ASM_REWRITE_TAC [addr30_addr32]);

val SPEC_ARM_MODEL_INTRO_pcSET = store_thm("SPEC_ARM_MODEL_INTRO_pcSET",
  ``ARM_PROG P [c] {} SEP_F {(Q,pcSET (addr30 x))} ==>
    !p:word32. SPEC ARM_MODEL (P * cond (x && 3w = 0w),p) {([c],p)} (Q,x)``,
  REWRITE_TAC [ARM_PROG_THM,ARM_MODEL_def,ARM_GPROG_def,GPROG_FALSE_POST]
  \\ SIMP_TAC std_ss [SPEC_def,setAPP_CLAUSES,pcINC_def,pcADD_def,fix_pos_def,set_apply_CLAUSES]
  \\ REWRITE_TAC [GPROG_def,ARMproc_def,ARM_MODEL_def]  
  \\ REWRITE_TAC [GSYM ARMproc_def,GSYM ARM_MODEL_def,RUN_ARM_MODEL_LEMMA]  
  \\ REWRITE_TAC [GPROG_DISJ_CLAUSES]
  \\ REWRITE_TAC [ARMpc_def,ARMpc2_def]
  \\ SIMP_TAC (std_ss++sep2_ss) [mpool_LEMMA,GSYM RUN_MOVE_COND]
  \\ SIMP_TAC std_ss [wLENGTH_def,LENGTH,ARMi_def,ARMi2_def,R30_def,pcSET_def]
  \\ SIMP_TAC (bool_ss++sep2_ss) [GSYM aligned_def,
       SIMP_RULE std_ss [word_mul_n2w] (Q.SPECL [`x`,`1w`] aligned_MULT)]
  \\ SIMP_TAC std_ss [addr32_ADD,addr32_n2w]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [WORD_ADD_COMM]))
  \\ REPEAT STRIP_TAC 
  \\ IMP_RES_TAC (GSYM (RW [GSYM aligned_def] addr32_addr30))
  \\ ONCE_ASM_REWRITE_TAC []  
  \\ NTAC 2 (Q.PAT_ASSUM `x = y` (fn th => ALL_TAC))
  \\ ASM_REWRITE_TAC [addr30_addr32]);

val SPEC_ARM_MODEL_INTRO_pcADD = store_thm("SPEC_ARM_MODEL_INTRO_pcSET",
  ``ARM_PROG P [c] {} SEP_F {(Q,pcADD x)} ==>
    !p:word32. SPEC ARM_MODEL (P,p) {([c],p)} (Q,p + addr32 x)``,
  REWRITE_TAC [ARM_PROG_THM,ARM_MODEL_def,ARM_GPROG_def,GPROG_FALSE_POST]
  \\ SIMP_TAC std_ss [SPEC_def,setAPP_CLAUSES,pcINC_def,pcADD_def,fix_pos_def,set_apply_CLAUSES]
  \\ REWRITE_TAC [GPROG_def,ARMproc_def,ARM_MODEL_def]  
  \\ REWRITE_TAC [GSYM ARMproc_def,GSYM ARM_MODEL_def,RUN_ARM_MODEL_LEMMA]  
  \\ REWRITE_TAC [GPROG_DISJ_CLAUSES]
  \\ REWRITE_TAC [ARMpc_def,ARMpc2_def]
  \\ SIMP_TAC (std_ss++sep2_ss) [mpool_LEMMA,GSYM RUN_MOVE_COND]
  \\ SIMP_TAC std_ss [wLENGTH_def,LENGTH,ARMi_def,ARMi2_def,R30_def,pcSET_def]
  \\ SIMP_TAC (bool_ss++sep2_ss) [GSYM aligned_def,
       SIMP_RULE std_ss [word_mul_n2w] (Q.SPECL [`x`,`1w`] aligned_MULT)]
  \\ SIMP_TAC std_ss [addr32_ADD,addr32_n2w]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [WORD_ADD_COMM]))
  \\ REPEAT STRIP_TAC 
  \\ IMP_RES_TAC (GSYM (RW [GSYM aligned_def] addr32_addr30))
  \\ ONCE_ASM_REWRITE_TAC []  
  \\ SIMP_TAC (bool_ss++sep2_ss) [GSYM addr32_ADD,aligned_addr32]
  \\ Q.PAT_ASSUM `z = y` (fn th => ALL_TAC)
  \\ ASM_REWRITE_TAC [addr30_addr32,addr32_ADD]);

val ARM_SPEC2_INTRO1 = store_thm("ARM_SPEC2_INTRO1",
  ``ARM_PROG2 c P [cmd] {} Q {} ==> ARM_SPEC2 c (P,p) {([cmd],p)} (Q,p+4w)``,
  SIMP_TAC bool_ss [ARM_PROG2_def,ARM_SPEC2_def,SPEC_ARM_MODEL_INTRO]);  

val ARM_SPEC2_INTRO2 = store_thm("ARM_SPEC2_INTRO2",
  ``ARM_PROG2 c P [cmd] {} SEP_F {(Q,pcSET (addr30 x))} ==> 
    ARM_SPEC2 c (P * cond (x && 3w = 0w),p) {([cmd],p)} (Q,x)``,
  SIMP_TAC bool_ss [ARM_PROG2_def,ARM_SPEC2_def,SPEC_ARM_MODEL_INTRO]
  \\ SIMP_TAC bool_ss [SPEC_ARM_MODEL_INTRO_pcSET]);  

val ARM_SPEC2_INTRO3 = store_thm("ARM_SPEC2_INTRO3",
  ``ARM_PROG2 c P [cmd] {} SEP_F {(Q,pcADD x)} ==>
    ARM_SPEC2 c (P,p) {([cmd],p)} (Q,p + addr32 x)``,
  SIMP_TAC bool_ss [ARM_PROG2_def,ARM_SPEC2_def,SPEC_ARM_MODEL_INTRO]
  \\ SIMP_TAC bool_ss [SPEC_ARM_MODEL_INTRO_pcADD]);  

val SPEC_ARM_MODEL_EMPTY = store_thm("SPEC_ARM_MODEL_EMPTY",
  ``!p. SPEC ARM_MODEL (emp,p) {} (emp,p)``,
  REWRITE_TAC [ARM_MODEL_def,SPEC_def,set_apply_CLAUSES]
  \\ REWRITE_TAC [GPROG_def,ARM_MODEL_def,fix_pos_def,GPROG_DISJ_CLAUSES]
  \\ REWRITE_TAC [emp_STAR,RUN_def,rel_sequence_def]
  \\ SIMP_TAC std_ss [GSYM ARM_MODEL_def,ARM_MODEL_IN_PROCESSORS,RES_FORALL]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `0` \\ ASM_REWRITE_TAC []);

val SPEC_ARM_MODEL_EQ_ARM_RUN = store_thm("SPEC_ARM_MODEL_EQ_ARM_RUN",
  ``SPEC ARM_MODEL (P,p) {([C],c)} (Q,q) =
    ARM_RUN (P * R 15w p * M (addr30 c) C * one (Undef F) * cond (p && 3w = 0w)) 
            (Q * R 15w q * M (addr30 c) C * one (Undef F) * cond (q && 3w = 0w))``,
  REWRITE_TAC [SPEC_def,GPROG_def,ARM_MODEL_def]
  \\ REWRITE_TAC [GSYM ARM_MODEL_def,ARM_RUN_def,RUN_ARM_MODEL_LEMMA]
  \\ REWRITE_TAC [GPROG_DISJ_CLAUSES,set_apply_CLAUSES,fix_pos_def,ARMpc2_def]
  \\ REWRITE_TAC [mpool_LEMMA,ARMi2_def,ARMi_def]  
  \\ SIMP_TAC (bool_ss++star_ss) []);



val _ = export_theory();
