(* ========================================================================= *)
(* FILE          : simScript.sml                                             *)
(* DESCRIPTION   : Theorems used to speed up execution                       *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["onestepTheory", "wordsTheory", "armTheory", "coreTheory",
            "lemmasTheory", "typesLib", "wordsLib", "bsubstTheory"];
*)

open HolKernel boolLib bossLib;
open Parse Q arithmeticTheory whileTheory bitTheory wordsTheory wordsLib;
open listTheory rich_listTheory my_listTheory;
open onestepTheory armTheory coreTheory lemmasTheory bsubstTheory;

val _ = new_theory "sim";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val tt = set_trace "types";

val word_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss++
  rewrites [n2w_def,word_extract_def,word_bits_n2w,w2w,
    BIT_def,BITS_THM,DIVMOD_2EXP_def,DIV_2EXP_def,DIV_1,
    DIV2_def,ODD_MOD2_LEM,DIV_DIV_DIV_MULT,MOD_2EXP_def];

val REDUCE_RULE = numLib.REDUCE_RULE;

(* ------------------------------------------------------------------------- *)

val SUC2NUM = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val MOD_DIMINDEX_32 = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
   Thm.INST_TYPE [alpha |-> ``:i32``]) MOD_DIMINDEX;

val DECODE_INST = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_bit,
    word_bits_n2w,word_bit_n2w,n2w_11,BITS_COMP_THM2,BITS_ZERO2,MOD_DIMINDEX_32,
    EVAL ``BITS 31 0 1``,EVAL ``BITS 31 0 2``,EVAL ``BITS 31 0 4``] o
  SPEC `n2w n`) DECODE_INST_def;

val DECODE_TAC = SIMP_TAC std_ss [DECODE_PSR_def,DECODE_BRANCH_def,
      DECODE_DATAP_def,DECODE_MRS_def,DECODE_MSR_def,DECODE_LDR_STR_def,
      DECODE_MLA_MUL_def,DECODE_LDM_STM_def,DECODE_SWP_def,DECODE_LDC_STC_def,
      SHIFT_IMMEDIATE_def,SHIFT_REGISTER_def,NZCV_def,DECODE_INST,
      REGISTER_LIST_def,SUC2NUM  rich_listTheory.GENLIST,rich_listTheory.SNOC,
      word_extract_def]
 \\ SIMP_TAC word_ss [];

val DECODE_PSR_THM = store_thm("DECODE_PSR_THM",
  `!n.  DECODE_PSR (n2w n) =
     let (q0,m) = DIVMOD_2EXP 5 n in
     let (q1,i) = DIVMOD_2EXP 1 (DIV2 q0) in
     let (q2,f) = DIVMOD_2EXP 1 q1 in
     let (q3,V) = DIVMOD_2EXP 1 (DIV_2EXP 20 q2) in
     let (q4,C) = DIVMOD_2EXP 1 q3 in
     let (q5,Z) = DIVMOD_2EXP 1 q4 in
       ((ODD q5,Z=1,C=1,V=1),f = 1,i = 1,n2w m)`, DECODE_TAC);

val DECODE_BRANCH_THM = store_thm("DECODE_BRANCH_THM",
  `!n. DECODE_BRANCH (n2w n) =
         let (L,offset) = DIVMOD_2EXP 24 n in (ODD L,n2w offset)`, DECODE_TAC);

val DECODE_DATAP_THM = store_thm("DECODE_DATAP_THM",
  `!n. DECODE_DATAP (n2w n) =
     let (q0,opnd2) = DIVMOD_2EXP 12 n in
     let (q1,Rd) = DIVMOD_2EXP 4 q0 in
     let (q2,Rn) = DIVMOD_2EXP 4 q1 in
     let (q3,S) = DIVMOD_2EXP 1 q2 in
     let (q4,opcode) = DIVMOD_2EXP 4 q3 in
       (ODD q4,n2w opcode,S = 1,n2w Rn,n2w Rd,n2w opnd2)`, DECODE_TAC);

val DECODE_MRS_THM = store_thm("DECODE_MRS_THM",
  `!n. DECODE_MRS (n2w n) =
     let (q,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 12 n) in
      (ODD (DIV_2EXP 6 q),n2w Rd)`, DECODE_TAC);

val DECODE_MSR_THM = store_thm("DECODE_MSR_THM",
  `!n. DECODE_MSR (n2w n) =
     let (q0,opnd) = DIVMOD_2EXP 12 n in
     let (q1,bit16) = DIVMOD_2EXP 1 (DIV_2EXP 4 q0) in
     let (q2,bit19) = DIVMOD_2EXP 1 (DIV_2EXP 2 q1) in
     let (q3,R) = DIVMOD_2EXP 1 (DIV_2EXP 2 q2) in
       (ODD (DIV_2EXP 2 q3),R = 1,bit19 = 1,bit16 = 1,
        n2w (MOD_2EXP 4 opnd),n2w opnd)`,
  DECODE_TAC \\ `4096 = 16 * 256` by numLib.ARITH_TAC
    \\ ASM_REWRITE_TAC [] \\ SIMP_TAC arith_ss [MOD_MULT_MOD]);

val DECODE_LDR_STR_THM = store_thm("DECODE_LDR_STR_THM",
  `!n. DECODE_LDR_STR (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 12 n in
    let (q1,Rd) = DIVMOD_2EXP 4 q0 in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,L) = DIVMOD_2EXP 1 q2 in
    let (q4,W) = DIVMOD_2EXP 1 q3 in
    let (q5,B) = DIVMOD_2EXP 1 q4 in
    let (q6,U) = DIVMOD_2EXP 1 q5 in
    let (q7,P) = DIVMOD_2EXP 1 q6 in
      (ODD q7,P = 1,U = 1,B = 1,W = 1,L = 1,n2w Rn,n2w Rd,n2w offset)`,
   DECODE_TAC);

val DECODE_MLA_MUL_THM = store_thm("DECODE_MLA_MUL_THM",
  `!n. DECODE_MLA_MUL (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rs) = DIVMOD_2EXP 4 (DIV_2EXP 4 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,Rd) = DIVMOD_2EXP 4 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
      (ODD q4,S = 1,n2w Rd,n2w Rn,n2w Rs,n2w Rm)`, DECODE_TAC);

val DECODE_LDM_STM_THM = store_thm("DECODE_LDM_STM_THM",
  `!n. DECODE_LDM_STM (n2w n) =
    let (q0,list) = DIVMOD_2EXP 16 n in
    let (q1,Rn) = DIVMOD_2EXP 4 q0 in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,U) = DIVMOD_2EXP 1 q4 in
      (ODD q5, U = 1, S = 1, W = 1, L = 1,n2w Rn,n2w list)`, DECODE_TAC);

val DECODE_SWP_THM = store_thm("DECODE_SWP_THM",
  `!n. DECODE_SWP (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
      (ODD (DIV_2EXP 2 q2),n2w Rn,n2w Rd,n2w Rm)`, DECODE_TAC);

val DECODE_LDC_STC_THM = store_thm("DECODE_LDC_STC_THM",
  `!n. DECODE_LDC_STC (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 8 n in
    let (q1,Rn) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,U) = DIVMOD_2EXP 1 (DIV2 q3) in
      (ODD q4,U = 1,W = 1,L = 1,n2w Rn,n2w offset)`, DECODE_TAC);

(* ------------------------------------------------------------------------- *)

fun w2w_n2w_sizes a b = (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
  Thm.INST_TYPE [alpha |-> a, beta |-> b]) w2w_n2w;

val SHIFT_IMMEDIATE_THM = store_thm("SHIFT_IMMEDIATE_THM",
  `!reg mode C opnd2.
     SHIFT_IMMEDIATE reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let shift = MOD_2EXP 5 q1 in
       let rm = REG_READ reg mode (n2w Rm) in
         SHIFT_IMMEDIATE2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:i12``) [``:i8``, ``:i4``, ``:i2``])
    \\ DECODE_TAC);

val SHIFT_REGISTER_THM = store_thm("SHIFT_REGISTER_THM",
  `!reg mode C opnd2.
     SHIFT_REGISTER reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let Rs = MOD_2EXP 4 (DIV2 q1) in
       let shift = MOD_2EXP 8 (w2n (REG_READ reg mode (n2w Rs)))
       and rm = REG_READ (INC_PC reg) mode (n2w Rm) in
         SHIFT_REGISTER2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC [w2w_n2w_sizes ``:i32`` ``:i8``]
    \\ ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:i12``)
          [``:i8``, ``:i4``, ``:i2``])
    \\ SIMP_TAC std_ss [SHIFT_REGISTER_def,word_extract_def,
         (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [n2w_w2n,BITS_THM,DIV_1,
            (GSYM o SIMP_RULE std_ss [] o SPEC `8`) MOD_2EXP_def] o
          SPECL [`7`,`0`,`w2n (a:word32)`] o 
          Thm.INST_TYPE [alpha |-> ``:i32``]) word_bits_n2w]
    \\ SIMP_TAC word_ss []);

(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!n. REGISTER_LIST (n2w n) =
       let (q0,b0) = DIVMOD_2EXP 1 n in
       let (q1,b1) = DIVMOD_2EXP 1 q0 in
       let (q2,b2) = DIVMOD_2EXP 1 q1 in
       let (q3,b3) = DIVMOD_2EXP 1 q2 in
       let (q4,b4) = DIVMOD_2EXP 1 q3 in
       let (q5,b5) = DIVMOD_2EXP 1 q4 in
       let (q6,b6) = DIVMOD_2EXP 1 q5 in
       let (q7,b7) = DIVMOD_2EXP 1 q6 in
       let (q8,b8) = DIVMOD_2EXP 1 q7 in
       let (q9,b9) = DIVMOD_2EXP 1 q8 in
       let (q10,b10) = DIVMOD_2EXP 1 q9 in
       let (q11,b11) = DIVMOD_2EXP 1 q10 in
       let (q12,b12) = DIVMOD_2EXP 1 q11 in
       let (q13,b13) = DIVMOD_2EXP 1 q12 in
       let (q14,b14) = DIVMOD_2EXP 1 q13 in
       MAP SND (FILTER FST
         [(b0 = 1,0w); (b1 = 1,1w); (b2 = 1,2w); (b3 = 1,3w);
          (b4 = 1,4w); (b5 = 1,5w); (b6 = 1,6w); (b7 = 1,7w);
          (b8 = 1,8w); (b9 = 1,9w); (b10 = 1,10w); (b11 = 1,11w);
          (b12 = 1,12w); (b13 = 1,13w); (b14 = 1,14w); (ODD q14,15w)])`,
  DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val DECODE_INST_THM = store_thm("DECODE_INST_THM",
  `!n. DECODE_INST (n2w n) = 
        let (q0,r4) = DIVMOD_2EXP 1 (DIV_2EXP 4 n) in
        let (q1,r65) = DIVMOD_2EXP 2 q0 in
        let (q2,r7) = DIVMOD_2EXP 1 q1 in
        let (q3,r20) = DIVMOD_2EXP 1 (DIV_2EXP 12 q2) in
        let (q4,r21) = DIVMOD_2EXP 1 q3 in
        let (q5,r23) = DIVMOD_2EXP 1 (DIV2 q4) in
        let (q6,r24) = DIVMOD_2EXP 1 q5 in
        let (q7,r25) = DIVMOD_2EXP 1 q6 in
        let bits2726 = MOD_2EXP 2 q7 in
        let (bit25,bit24,bit23,bit21,bit20,bit7,bits65,bit4) =
             (r25 = 1,r24 = 1,r23 = 1,r21 = 1,r20 = 1,r7 = 1,r65,r4 = 1) in
          if bits2726 = 0 then
            if bit24 /\ ~bit23 /\ ~bit20 then
                if bit25 \/ ~bit4 then
                  mrs_msr
                else
                  if ~bit21 /\ (BITS 11 5 n = 4) then swp else cdp_und
            else
              if ~bit25 /\ bit4 then
                if ~bit7 then
                  reg_shift
                else
                  if ~bit24 /\ (bits65 = 0) then mla_mul else cdp_und
              else
                data_proc
          else
            if bits2726 = 1 then
              if bit25 /\ bit4 then
                cdp_und
              else
                if bit20 then ldr else str
            else
              if bits2726 = 2 then
                if bit25 then br else
                  if bit20 then ldm else stm
              else
                if bit25 then
                  if bit24 then swi_ex else
                    if bit4 then
                      if bit20 then mrc else mcr
                    else
                      cdp_und
                  else
                    if bit20 then ldc else stc`, DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val word_ss = armLib.fcp_ss ++ wordsLib.SIZES_ss ++ ARITH_ss;

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val lem = prove(
  `!w:word32 i. i < 5 ==> (((4 >< 0) w) :word5 %% i = w %% i)`,
  RW_TAC word_ss [word_extract_def,word_bits_def,w2w]);
  
val PSR_CONS = store_thm("PSR_CONS",
   `!w:word32. w =
       let m = DECODE_MODE ((4 >< 0) w) in
         if m = safe then
           SET_NZCV (w %% 31, w %% 30, w %% 29, w %% 28) ((27 -- 0) w)
         else
           SET_NZCV (w %% 31, w %% 30, w %% 29, w %% 28)
             (SET_IFMODE (w %% 7) (w %% 6) m (0xFFFFF20w && w))`,
  RW_TAC word_ss [SET_IFMODE_def,SET_NZCV_def,word_modify_def,n2w_def]
    \\ RW_TAC word_ss [word_bits_def]
    << [
      `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/ (i < 28)`
        by DECIDE_TAC
        \\ ASM_SIMP_TAC arith_ss [],
      `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/
       (7 < i /\ i < 28) \/ (i = 7) \/ (i = 6) \/ (i = 5) \/ (i < 5)`
        by DECIDE_TAC
        \\ ASM_SIMP_TAC (word_ss++ARITH_ss) [word_and_def]
        << [
          FULL_SIMP_TAC std_ss [LESS_THM]
            \\ FULL_SIMP_TAC arith_ss [] \\ EVAL_TAC,
          EVAL_TAC, 
          `~(mode_num m = 0w)`
            by (Cases_on `m` \\ RW_TAC std_ss [mode_num_def] \\ EVAL_TAC)
            \\ POP_ASSUM MP_TAC \\ UNABBREV_TAC `m`
            \\ RW_TAC (word_ss++ARITH_ss)
                 [DECODE_MODE_def,mode_num_def,n2w_def,lem]
            \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC word_ss []]]);

val REG_WRITE_PSR = save_thm("REG_WRITE_PSR",
  SIMP_CONV std_ss [SET_NZCV_def,SET_IFMODE_def]
  ``REG_WRITE reg mode Rd (SET_NZCV (n,z,c,v) x)``);

val REG_WRITE_PSR2 = save_thm("REG_WRITE_PSR2",
  SIMP_CONV std_ss [SET_NZCV_def,SET_IFMODE_def]
  ``REG_WRITE reg mode Rd (SET_NZCV (n,z,c,v) (SET_IFMODE imask fmask m x))``);

val word_modify_PSR = save_thm("word_modify_PSR",
  SIMP_CONV std_ss [SET_NZCV_def,SET_IFMODE_def]
  ``word_modify f (SET_NZCV (n,z,c,v) x)``);

val word_modify_PSR2 = save_thm("word_modify_PSR2",
  SIMP_CONV std_ss [SET_NZCV_def,SET_IFMODE_def]
  ``word_modify f (SET_NZCV (n,z,c,v) (SET_IFMODE imask fmask m x))``);

val CPSR_WRITE_n2w = save_thm("CPSR_WRITE_n2w", GEN_ALL
  ((PURE_ONCE_REWRITE_CONV [PSR_CONS] THENC PURE_REWRITE_CONV [CPSR_WRITE_def])
   ``CPSR_WRITE psr (n2w n)``));

val SPSR_WRITE_n2w = save_thm("SPSR_WRITE_n2w", GEN_ALL
  ((PURE_ONCE_REWRITE_CONV [PSR_CONS] THENC PURE_REWRITE_CONV [SPSR_WRITE_def])
   ``SPSR_WRITE psr mode (n2w n)``));

(*
val word_ss = armLib.fcp_ss ++ wordsLib.SIZES_ss;

val mode_num_11 = store_thm("mode_num_11",
  `!m1 m2. (mode_num m1 = mode_num m2) = (m1 = m2)`,
  Cases \\ Cases \\ RW_TAC std_ss [mode_num_def] \\ EVAL_TAC);

fun Cases_on_nzcv tm =
  FULL_STRUCT_CASES_TAC (SPEC tm (armLib.tupleCases
  ``(n,z,c,v):bool#bool#bool#bool``));

val PSR_EQ = store_thm("PSR_EQ",
  `(SET_NZCV flags1 (SET_IFMODE i1 f1 m1 w1) =
    SET_NZCV flags2 (SET_IFMODE i2 f2 m2 w2)) =
   ((flags1 = flags2) /\ (i1 = i2) /\ (f1 = f2) /\ (m1 = m2) /\
    ((27 -- 8) w1 = (27 -- 8) w2)) /\ (w1 %% 5 = w2 %% 5)`,
  Cases_on_nzcv `flags1` \\ Cases_on_nzcv `flags2`
    \\ EQ_TAC
    \\ RW_TAC word_ss
         [SET_NZCV_def,SET_IFMODE_def,word_modify_def,word_bits_def]
    << [
      POP_ASSUM (SPEC_THEN `31` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      POP_ASSUM (SPEC_THEN `30` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      POP_ASSUM (SPEC_THEN `29` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      POP_ASSUM (SPEC_THEN `28` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      POP_ASSUM (SPEC_THEN `7` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      POP_ASSUM (SPEC_THEN `6` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      `!i. i < 5 ==> (mode_num m1 %% i = mode_num m2 %% i)`
        by (STRIP_TAC \\ POP_ASSUM (SPEC_THEN `i` ASSUME_TAC)
              \\ STRIP_TAC \\ FULL_SIMP_TAC arith_ss [])
        \\ `mode_num m1 = mode_num m2` by RW_TAC word_ss [mode_num_def]
        \\ ASM_REWRITE_TAC [GSYM mode_num_11],
      PAT_ASSUM `!i. P` (SPEC_THEN `i + 8` ASSUME_TAC)
        \\ Cases_on `i + 8 <= 27 /\ i + 8 <= 31`
        \\ FULL_SIMP_TAC arith_ss [],
      POP_ASSUM (SPEC_THEN `5` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [])),
      PAT_ASSUM `!i. P` (SPEC_THEN `i - 8` ASSUME_TAC)
        \\ `(i = 31) \/ (i = 30) \/ (i = 29) \/ (i = 28) \/
            (7 < i /\ i < 28) \/ (i = 7) \/ (i = 6) \/ (i = 5) \/ (i < 5)`
        by DECIDE_TAC
        \\ FULL_SIMP_TAC arith_ss []]);
*)

(* ------------------------------------------------------------------------- *)

val if_swp = PROVE [] ``!a b c. (if ~a then b else c) = (if a then c else b)``;

val LEAST16_def = Define `LEAST16 n = WHILE ($~ o (\b. n %% b)) SUC 16`;

val LEASTBIT_EVAL =
  SIMP_RULE arith_ss [if_swp,GSYM LEAST16_def,LEAST_DEF,Ntimes WHILE 16]
    LEASTBIT_def;

val NUMERAL_LEASTBIT16 = save_thm("NUMERAL_LEASTBIT16",
  (GEN_ALL o SIMP_RULE (arith_ss++SIZES_ss) [word_bit,word_bit_n2w] o
   ISPEC `(n2w (NUMERAL n)):word16`) LEASTBIT_EVAL);

val SPEC_BIT_BITS_THM =
  (GEN_ALL o SYM o REWRITE_RULE [BITS_ZERO2,BIT_ZERO] o INST [`b` |-> `0`] o
   SPEC_ALL) BIT_BITS_THM;

val EXTEND_ONE_BIT = prove(
  `!h l n. l < h /\ (l2 = SUC l) ==>
       (~(BITS h l2 n = 0) \/ BIT l n = ~(BITS h l n = 0))`,
  RW_TAC bool_ss [GSYM LESS_EQ,SPEC_BIT_BITS_THM]
    \\ EQ_TAC \\ RW_TAC arith_ss []
    << [
      EXISTS_TAC `x` \\ ASM_SIMP_TAC arith_ss [],
      EXISTS_TAC `l` \\ ASM_SIMP_TAC arith_ss [],
      Cases_on `l = x` >> ASM_REWRITE_TAC []
        \\ DISJ1_TAC \\ EXISTS_TAC `x` \\ ASM_SIMP_TAC arith_ss []]);

val MLA_MUL_DUR = save_thm("MLA_MUL_DUR",
  (GEN_ALL o SIMP_RULE std_ss [if_swp,EXTEND_ONE_BIT] o
   SIMP_RULE (arith_ss++SIZES_ss)
    [GSYM BIT_def,MOD_DIMINDEX_32,BITS_COMP_THM2,n2w_11] o
   SIMP_RULE (arith_ss++SIZES_ss) [LEAST_DEF,MLA_MUL_DONE_def,BORROW2_def,
     BIT_def,MIN_DEF,word_bits_n2w,word_bit_n2w,word_bit,Ntimes WHILE 17] o
   SPEC `n2w n`) MLA_MUL_DUR_def);

val MLA_MUL_DUR_n2w = store_thm("MLA_MUL_DUR_n2w",
  `!n. MLA_MUL_DUR (n2w n) =
        let n = BITS 31 1 n in
        (if n = 0 then
            1
         else let n = DIV_2EXP 2 n in if n = 0 then
            2
         else let n = DIV_2EXP 2 n in if n = 0 then
            3
         else let n = DIV_2EXP 2 n in if n = 0 then
            4
         else let n = DIV_2EXP 2 n in if n = 0 then
            5
         else let n = DIV_2EXP 2 n in if n = 0 then
            6
         else let n = DIV_2EXP 2 n in if n = 0 then
            7
         else let n = DIV_2EXP 2 n in if n = 0 then
            8
         else let n = DIV_2EXP 2 n in if n = 0 then
            9
         else let n = DIV_2EXP 2 n in if n = 0 then
            10
         else let n = DIV_2EXP 2 n in if n = 0 then
            11
         else let n = DIV_2EXP 2 n in if n = 0 then
            12
         else let n = DIV_2EXP 2 n in if n = 0 then
            13
         else let n = DIV_2EXP 2 n in if n = 0 then
            14
         else if DIV_2EXP 2 n = 0 then
            15
         else
            16)`,
  SIMP_TAC bool_ss [LET_THM,MLA_MUL_DUR,BITS_THM2,DIV_2EXP_def,
         DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,GSYM EXP_ADD]
    \\ CONV_TAC (DEPTH_CONV reduceLib.ADD_CONV)
    \\ REWRITE_TAC []);

(* ------------------------------------------------------------------------- *)

val Sa_def = Define `Sa = $:-`;
val Sb_def = Define `Sb = $:-`;

val Sab_EQ = store_thm("Sab_EQ",
  `(Sb a e (Sa a d m) = Sa a e m) /\
   (Sb a e (Sb a d m) = Sb a e m) /\
   (Sa a e (Sa a d m) = Sa a e m)`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_EQ]);

(*
val Sa_EVAL = store_thm("Sa_EVAL",
  `!a w b. Sa a w m b = if a = b then w else m b`,
  RW_TAC std_ss [Sa_def,SUBST_def]);

val Sb_EVAL = store_thm("Sb_EVAL",
  `!a w b. Sb a w m b = if a = b then w else m b`,
  RW_TAC std_ss [Sb_def,SUBST_def]);
*)

val SUBST_EVAL = store_thm("SUBST_EVAL",
  `!a w b. (a :- w) m b = if a = b then w else m b`,
  RW_TAC std_ss [SUBST_def]);

(* --- *)

val SUBST_COMMUTES4 = store_thm("SUBST_COMMUTES4",
  `!m a b d e. register2num a < register2num b ==>
     ((a :- e) ((b :- d) m) = (b :- d) ((a :- e) m))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM]
    \\ IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
    \\ RW_TAC bool_ss [SUBST_def]
    \\ FULL_SIMP_TAC bool_ss [register2num_11]);

val Sa_RULE4 = store_thm("Sa_RULE4",
  `!m a b d e. Sa a e (Sa b d m) =
     if register2num a < register2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sa b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES4]);

val Sb_RULE4 = store_thm("Sb_RULE4",
  `!m a b d e. Sa a e (Sb b d m) =
     if register2num a < register2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sb b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES4]);

(* --- *)

val SUBST_COMMUTES_PSR = store_thm("SUBST_COMMUTES_PSR",
  `!m a b d e. psrs2num b < psrs2num a ==>
     ((a :- e) ((b :- d) m) = (b :- d) ((a :- e) m))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM]
    \\ IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
    \\ RW_TAC bool_ss [SUBST_def]
    \\ FULL_SIMP_TAC bool_ss [psrs2num_11]);

val Sa_RULE_PSR = store_thm("Sa_RULE_PSR",
  `!m a b d e. Sa a e (Sa b d m) =
     if psrs2num a < psrs2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sa b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES_PSR]);

val Sb_RULE_PSR = store_thm("Sb_RULE_PSR",
  `!m a b d e. Sa a e (Sb b d m) =
     if psrs2num a < psrs2num b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sb b d m)`,
  METIS_TAC [Sa_def,Sb_def,SUBST_COMMUTES_PSR]);

(* ------------------------------------------------------------------------- *)

val tm1 = `!a b x y m. (a ::-> y) ((b ::-> x) m) =
     let lx = LENGTH x and ly = LENGTH y in
        if a <=+ b then
          if w2n b - w2n a <= ly then
            if ly - (w2n b - w2n a) < lx then
              (a ::-> y ++ BUTFIRSTN (ly - (w2n b - w2n a)) x) m
            else
              (a ::-> y) m
          else
            (a ::-< y) ((b ::-> x) m)
        else (* b <+ a *)
          if w2n a - w2n b < lx then
            (b ::-> JOIN (w2n a - w2n b) x y) m
          else
            (b ::-> x) ((a ::-> y) m)`

val tm2 = `!a b x y m. (a ::-> y) ((b ::-< x) m) =
     let lx = LENGTH x and ly = LENGTH y in
        if a <=+ b then
          if w2n b - w2n a <= ly then
            if ly - (w2n b - w2n a) < lx then
              (a ::-> y ++ BUTFIRSTN (ly - (w2n b - w2n a)) x) m
            else
              (a ::-> y) m
          else
            (a ::-< y) ((b ::-< x) m)
        else (* b <+ a *)
          if w2n a - w2n b < lx then
            (b ::-> JOIN (w2n a - w2n b) x y) m
          else
            (b ::-> x) ((a ::-> y) m)`

val BSa_RULE = store_thm("BSa_RULE", tm1,
  METIS_TAC [BSa_def,BSb_def,BSUBST_BSUBST]);

val BSb_RULE = store_thm("BSb_RULE", tm2,
  METIS_TAC [BSa_def,BSb_def,BSUBST_BSUBST]);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
