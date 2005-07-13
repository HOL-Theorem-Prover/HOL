(* app load ["onestepTheory","word32Theory","armTheory","coreTheory","lemmasTheory"]; *)
open HolKernel boolLib bossLib Q arithmeticTheory whileTheory onestepTheory
     bitsTheory word32Theory armTheory coreTheory lemmasTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "sim";

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val _ = intLib.deprecate_int();

(* -------------------------------------------------------- *)

val REDUCE_RULE = numLib.REDUCE_RULE;

val DECODE_PSR_THM = store_thm("DECODE_PSR_THM",
  `!n.  DECODE_PSR (n2w n) =
     let (q0,m) = DIVMOD_2EXP 5 n in
     let (q1,i) = DIVMOD_2EXP 1 (DIV2 q0) in
     let (q2,f) = DIVMOD_2EXP 1 q1 in
     let (q3,V) = DIVMOD_2EXP 1 (DIV_2EXP 20 q2) in
     let (q4,C) = DIVMOD_2EXP 1 q3 in
     let (q5,Z) = DIVMOD_2EXP 1 q4 in
       ((ODD q5,Z=1,C=1,V=1),f = 1,i = 1,m)`,
   SIMP_TAC arith_ss [DECODE_PSR_def,NZCV_def,w2n_EVAL,MOD_WL_THM,HB_def,BIT_def,BITS_COMP_THM2]
     THEN SIMP_TAC arith_ss [DIV_2EXP_def,DIVMOD_2EXP_def,DIV2_def,BITS_THM,
                             DIV_DIV_DIV_MULT,ODD_MOD2_LEM,DIV_1,EXP]
);

val DECODE_BRANCH_THM = store_thm("DECODE_BRANCH_THM",
  `!n. DECODE_BRANCH n =
         let (L,offset) = DIVMOD_2EXP 24 n in (ODD L,offset)`,
  SIMP_TAC arith_ss [DECODE_BRANCH_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                      DIV_1,ODD_MOD2_LEM,LET_THM]
);

val DECODE_DATAP_THM = store_thm("DECODE_DATAP_THM",
  `!n. DECODE_DATAP n =
     let (q0,opnd2) = DIVMOD_2EXP 12 n in
     let (q1,Rd) = DIVMOD_2EXP 4 q0 in
     let (q2,Rn) = DIVMOD_2EXP 4 q1 in
     let (q3,S) = DIVMOD_2EXP 1 q2 in
     let (q4,opcode) = DIVMOD_2EXP 4 q3 in
       (ODD q4,opcode,S = 1,Rn,Rd,opnd2)`,
  SIMP_TAC arith_ss [DECODE_DATAP_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                     EXP,DIV_1,ODD_MOD2_LEM,LET_THM,DIV_DIV_DIV_MULT]
);

val DECODE_MRS_THM = store_thm("DECODE_MRS_THM",
  `!n. DECODE_MRS n =
     let (q,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 12 n) in
      (ODD (DIV_2EXP 6 q),Rd)`,
  SIMP_TAC arith_ss [DECODE_MRS_def,DIV_2EXP_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                     EXP,DIV_1,ODD_MOD2_LEM,LET_THM,DIV_DIV_DIV_MULT]
);

(*
val th1 = REDUCE_RULE (SPECL [`31`,`0`,`31`,`28`] BITS_COMP_THM);
val th2 = REDUCE_RULE (SPECL [`31`,`0`,`27`,`8`] BITS_COMP_THM);
val th3 = REDUCE_RULE (SPECL [`31`,`0`,`7`,`0`] BITS_COMP_THM);

val SPLIT_WORD_THM = store_thm("SPLIT_WORD_THM",
  `!n. SPLIT_WORD (w32 n) =
      let (q0,r0) = DIVMOD_2EXP 8 n in
      let (q1,r1) = DIVMOD_2EXP 20 q0 in
        (q1 MOD 16,r1,r0)`,
  STRIP_TAC
    THEN SIMP_TAC arith_ss [SPLIT_WORD_def,BITS_EVAL,MOD_WL_THM,HB_def,th1,th2,th3]
    THEN SIMP_TAC arith_ss [DIVMOD_2EXP_def,BITS_THM,DIV_1,EXP,DIV_DIV_DIV_MULT]
);
*)

val lem = prove(
  `!n. BITS 7 0 n = SLICE 7 7 n + SLICE 6 6 n + SLICE 5 5 n + BITS 4 0 n`,
  SIMP_TAC std_ss [GSYM SLICE_ZERO_THM,SLICE_COMP_RWT]
);

val ADD_ss = simpLib.SSFRAG
  {convs = [{name="ADD_CONV",trace = 3,conv=K (K reduceLib.ADD_CONV),key= SOME([],``(a:num) + b``)}],
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

val lem2 = prove(
  `!n. BITS 31 28 n = (SBIT (BIT 31 n) 3 + SBIT (BIT 30 n) 2 +
                       SBIT (BIT 29 n) 1 + SBIT (BIT 28 n) 0)`,
  STRIP_TAC
    THEN ONCE_REWRITE_TAC [(GEN_ALL o SYM o ONCE_REWRITE_RULE [MULT_COMM] o
           SIMP_RULE bool_ss [ZERO_LT_TWOEXP,DECIDE ``0 < a ==> (SUC (a - 1) = a)``] o
           INST [`n` |-> `2 ** 28 - 1`] o SPEC_ALL) MULT_MONO_EQ]
    THEN SIMP_TAC (bool_ss++ADD_ss) [BIT_SLICE_THM,GSYM SLICE_THM,RIGHT_ADD_DISTRIB,SBIT_MULT]
    THEN SIMP_TAC std_ss [SLICE_COMP_RWT,GSYM RIGHT_ADD_DISTRIB]
);

val SPLIT_WORD_THM = store_thm("SPLIT_WORD_THM",
  `(!a b c d n. BITS 7 0 (w2n (SET_NZCV (a,b,c,d) n)) = BITS 7 0 (w2n n)) /\
   (!a b c d n. BITS 27 8 (w2n (SET_NZCV (a,b,c,d) n)) = BITS 27 8 (w2n n)) /\
   (!a b c d n. BITS 31 28 (w2n (SET_NZCV (a,b,c,d) n)) = SBIT a 3 + SBIT b 2 + SBIT c 1 + SBIT d 0) /\
   (!a b c n. BITS 7 0 (w2n (SET_IFMODE a b c n)) = SBIT a 7 + SBIT b 6 + SBIT (BIT 5 (w2n n)) 5 + mode_num c) /\
   (!a b c n. BITS 27 8 (w2n (SET_IFMODE a b c n)) = BITS 27 8 (w2n n)) /\
   (!a b c n. BITS 31 28 (w2n (SET_IFMODE a b c n)) = BITS 31 28 (w2n n))`,
  RW_TAC bool_ss [DECODE_NZCV_SET_NZCV,DECODE_IFMODE_SET_IFMODE,
                  DECODE_IFMODE_SET_NZCV,DECODE_NZCV_SET_IFMODE,
                  SLICE_THM,GSYM BITV_def,SBIT_MULT,BITV_THM,ADD,lem,lem2]
);

val DECODE_MSR_THM = store_thm("DECODE_MSR_THM",
  `!n. DECODE_MSR n =
         let (q0,opnd) = DIVMOD_2EXP 12 n in
         let (q1,bit16) = DIVMOD_2EXP 1 (DIV_2EXP 4 q0) in
         let (q2,bit19) = DIVMOD_2EXP 1 (DIV_2EXP 2 q1) in
         let (q3,R) = DIVMOD_2EXP 1 (DIV_2EXP 2 q2) in
           (ODD (DIV_2EXP 2 q3),R = 1,bit19 = 1,bit16 = 1,MOD_2EXP 4 opnd,opnd)`,
  STRIP_TAC
    THEN SIMP_TAC arith_ss [DECODE_MSR_def,DIVMOD_2EXP_def,
                            DIV_2EXP_def,MOD_2EXP_def,BITS_THM,BIT_def,
                            DIV_1,EXP,ODD_MOD2_LEM,DIV_DIV_DIV_MULT]
    THEN `4096 = 16 * 256` by numLib.ARITH_TAC
    THEN ASM_REWRITE_TAC []
    THEN SIMP_TAC arith_ss [MOD_MULT_MOD]
);

val DECODE_LDR_STR_THM = store_thm("DECODE_LDR_STR_THM",
  `!n. DECODE_LDR_STR n =
        let (q0,offset) = DIVMOD_2EXP 12 n in
        let (q1,Rd) = DIVMOD_2EXP 4 q0 in
        let (q2,Rn) = DIVMOD_2EXP 4 q1 in
        let (q3,L) = DIVMOD_2EXP 1 q2 in
        let (q4,W) = DIVMOD_2EXP 1 q3 in
        let (q5,B) = DIVMOD_2EXP 1 q4 in
        let (q6,U) = DIVMOD_2EXP 1 q5 in
        let (q7,P) = DIVMOD_2EXP 1 q6 in
          (ODD q7,P = 1,U = 1,B = 1,W = 1,L = 1,Rn,Rd,offset)`,
   SIMP_TAC arith_ss [DECODE_LDR_STR_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                      DIV_1,EXP,ODD_MOD2_LEM,DIV_DIV_DIV_MULT]
);

val DECODE_MLA_MUL_THM = store_thm("DECODE_MLA_MUL_THM",
  `!n. DECODE_MLA_MUL n =
        let (q0,Rm) = DIVMOD_2EXP 4 n in
        let (q1,Rs) = DIVMOD_2EXP 4 (DIV_2EXP 4 q0) in
        let (q2,Rn) = DIVMOD_2EXP 4 q1 in
        let (q3,Rd) = DIVMOD_2EXP 4 q2 in
        let (q4,S) = DIVMOD_2EXP 1 q3 in
          (ODD q4,S = 1,Rd,Rn,Rs,Rm)`,
   SIMP_TAC arith_ss [DECODE_MLA_MUL_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                      DIV_2EXP_def,DIV_1,EXP,ODD_MOD2_LEM,DIV_DIV_DIV_MULT]
);

val DECODE_LDM_STM_THM = store_thm("DECODE_LDM_STM_THM",
  `!n. DECODE_LDM_STM n =
     let (q0,bit15) = DIVMOD_2EXP 1 (DIV_2EXP 15 n) in
     let (q1,Rn) = DIVMOD_2EXP 4 q0 in
     let (q2,L) = DIVMOD_2EXP 1 q1 in
     let (q3,W) = DIVMOD_2EXP 1 q2 in
     let (q4,S) = DIVMOD_2EXP 1 q3 in
     let (q5,U) = DIVMOD_2EXP 1 q4 in
       (ODD q5, U = 1, S = 1, W = 1, L = 1, Rn, bit15 = 1)`,
  SIMP_TAC arith_ss [DECODE_LDM_STM_def,DIV_2EXP_def,DIVMOD_2EXP_def,
                    BITS_THM,BIT_def,DIV_DIV_DIV_MULT,ODD_MOD2_LEM,DIV_1,EXP]
);

val DECODE_SWP_THM = store_thm("DECODE_SWP_THM",
  `!n. DECODE_SWP n =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
      (ODD (DIV_2EXP 2 q2),Rn,Rd,Rm)`,
  SIMP_TAC arith_ss [DECODE_SWP_def,DIV_2EXP_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                     EXP,DIV_1,ODD_MOD2_LEM,LET_THM,DIV_DIV_DIV_MULT]
);

(* -------------------------------------------------------- *)

val SHIFT_IMMEDIATE_THM = store_thm("SHIFT_IMMEDIATE_THM",
  `!r m c opnd2. SHIFT_IMMEDIATE r m C opnd2 =
                   let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
                   let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
                   let shift = MOD_2EXP 5 q1 in
                   let rm = REG_READ r m Rm in
                     SHIFT_IMMEDIATE2 shift Sh rm C`,
  SIMP_TAC arith_ss [SHIFT_IMMEDIATE_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                     MOD_2EXP_def,DIV2_def,LET_THM,DIV_1,EXP,ODD_MOD2_LEM,DIV_DIV_DIV_MULT]
);

val SHIFT_REGISTER_THM = store_thm("SHIFT_REGISTER_THM",
  `!reg mode C opnd2.
     SHIFT_REGISTER reg mode C opnd2 =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let Rs = MOD_2EXP 4 (DIV2 q1) in
       let shift = MOD_2EXP 8 (w2n (REG_READ reg mode Rs))
       and rm = REG_READ (INC_PC reg) mode Rm in
         SHIFT_REGISTER2 shift Sh rm C`,
  SIMP_TAC arith_ss [SHIFT_REGISTER_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,WORD_BITS_def,
                     MOD_2EXP_def,DIV2_def,LET_THM,DIV_1,EXP,ODD_MOD2_LEM,DIV_DIV_DIV_MULT]
);

(* -------------------------------------------------------- *)

val SUC2NUM = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!n. REGISTER_LIST n =
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
         [(b0 = 1,0); (b1 = 1,1); (b2 = 1,2); (b3 = 1,3);
          (b4 = 1,4); (b5 = 1,5); (b6 = 1,6); (b7 = 1,7);
          (b8 = 1,8); (b9 = 1,9); (b10 = 1,10); (b11 = 1,11);
          (b12 = 1,12); (b13 = 1,13); (b14 = 1,14); (ODD q14,15)])`,
  SIMP_TAC arith_ss [REGISTER_LIST_def,DIV_2EXP_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                     EXP,DIV_1,ODD_MOD2_LEM,LET_THM,DIV_DIV_DIV_MULT,rich_listTheory.SNOC,
                     SUC2NUM  rich_listTheory.GENLIST]
);

(* -------------------------------------------------------- *)

val DECODE_INST_THM = store_thm("DECODE_INST_THM",
  `!n. DECODE_INST n = 
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
                if bit25 /\ bit24 then swi_ex else cdp_und`,
  SIMP_TAC arith_ss [DECODE_INST_def,DIVMOD_2EXP_def,BITS_THM,BIT_def,
                     MOD_2EXP_def,DIV_2EXP_def,DIV2_def,LET_THM,DIV_1,EXP,DIV_DIV_DIV_MULT]
);

(* -------------------------------------------------------- *)

val lem1a = prove(
  `(!n. BIT 24 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in P) /\
   (!n. BIT 23 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in U) /\
   (!n. BIT 22 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in S) /\
   (!n. BIT 21 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in W) /\
   (!n. BIT 20 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in L) /\
   (!n. BITS 19 16 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in Rn) /\
   (!n. BIT 15 n = let (P,U,S,W,L,Rn,pc_in_list) = DECODE_LDM_STM n in pc_in_list)`,
  RW_TAC (std_ss++boolSimps.LET_ss) [DECODE_LDM_STM_def]
);

val lem1b = prove(
  `(!n. BIT 25 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in I) /\
   (!n. BIT 24 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in P) /\
   (!n. BIT 23 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in U) /\
   (!n. BIT 22 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in B) /\
   (!n. BIT 21 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in W) /\
   (!n. BIT 20 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in L) /\
   (!n. BITS 19 16 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in Rn) /\
   (!n. BITS 15 12 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in Rd) /\
   (!n. BITS 11 0 n = let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR n in offset)`,
  RW_TAC (std_ss++boolSimps.LET_ss) [DECODE_LDR_STR_def]);

val lem1c = prove(
  `(!n. BIT 22 n = let (B,Rn,Rd,Rm) = DECODE_SWP n in B) /\
   (!n. BITS 19 16 n = let (B,Rn,Rd,Rm) = DECODE_SWP n in Rn) /\
   (!n. BITS 15 12 n = let (B,Rn,Rd,Rm) = DECODE_SWP n in Rd) /\
   (!n. BITS 3 0 n = let (B,Rn,Rd,Rm) = DECODE_SWP n in Rm)`,
  RW_TAC (std_ss++boolSimps.LET_ss) [DECODE_SWP_def]
);

val PBETA_CONV_ss = simpLib.SSFRAG
  {convs = [{name="PBETA_CONV",trace = 3,conv=K (K PairRules.PBETA_CONV),key= SOME([],``(\(x,y). s1) s2``)}],
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

val lem2a = prove(
  `!j b f g. (let (a,b,c,d,e,f,g) = j in (x = y a b c d e f g)) =
           (x = let (a,b,c,d,e,f,g) = j in y a b c d e f g)`,
  RW_TAC (std_ss++PBETA_CONV_ss) []
);

val lem2b = prove(
  `!j b f g. (let (a,b,c,d,e,f,g,h,i) = j in (x = y a b c d e f g h i)) =
           (x = let (a,b,c,d,e,f,g,h,i) = j in y a b c d e f g h i)`,
  RW_TAC (std_ss++PBETA_CONV_ss) []
);

val lem2c = prove(
  `!j b f g. (let (a,b,c,d) = j in (x = y a b c d)) =
           (x = let (a,b,c,d) = j in y a b c d)`,
  RW_TAC (std_ss++PBETA_CONV_ss) []
);

val lem2a = (GEN_ALL o ISPEC `DECODE_LDM_STM n`) lem2a;
val lem2b = (GEN_ALL o ISPEC `DECODE_LDR_STR n`) lem2b;
val lem2c = (GEN_ALL o ISPEC `DECODE_SWP n`) lem2c;

fun STATE_OUT_CONV t l = (SIMP_RULE bossLib.std_ss [lem2a,lem2b,lem2c] o pairLib.LET_INTRO o
         CONV_RULE (RATOR_CONV (ONCE_DEPTH_CONV SYM_CONV)) o
         SIMP_RULE std_ss [] o
         DISCH t o SIMP_RULE bossLib.std_ss [l] o
         SIMP_CONV (srw_ss()++boolSimps.LET_ss) [SWP_def,LDR_STR_def,LDM_STM_def,
           ADDR_MODE4_def,ADDR_MODE2_def,WB_ADDRESS_def,FIRST_ADDRESS_def,DECODE_SWP_def,
           DECODE_LDR_STR_def,DECODE_LDM_STM_def]);

val LDM_STM_STATE = save_thm("LDM_STM_STATE",
  STATE_OUT_CONV `DECODE_LDM_STM n = (a,b,c,d,e,f,g)` lem1a
    ``(LDM_STM (ARM reg psr) mode dabort_t data n).state``
);
val LDM_STM_OUT   = save_thm("LDM_STM_OUT",
  STATE_OUT_CONV `DECODE_LDM_STM n = (a,b,c,d,e,f,g)` lem1a
    ``(LDM_STM (ARM reg psr) mode dabort_t data n).out``
);
val LDR_STR_STATE = save_thm("LDR_STR_STATE",
  STATE_OUT_CONV `DECODE_LDR_STR n = (a,b,c,d,e,f,g,h,i)` lem1b
    ``(LDR_STR (ARM reg psr) C mode isdabort data n).state``
);
val LDR_STR_OUT   = save_thm("LDR_STR_OUT",
  STATE_OUT_CONV `DECODE_LDR_STR n = (a,b,c,d,e,f,g,h,i)` lem1b
    ``(LDR_STR (ARM reg psr) C mode isdabort data n).out``
);
val SWP_STATE     = save_thm("SWP_STATE",
  STATE_OUT_CONV `DECODE_SWP n = (a,b,c,d)` lem1c
    ``(SWP (ARM reg psr) mode isdabort data n).state``
);
val SWP_OUT       = save_thm("SWP_OUT",
  STATE_OUT_CONV `DECODE_SWP n = (a,b,c,d)` lem1c
    ``(SWP (ARM reg psr) mode isdabort data n).out``
);

(* -------------------------------------------------------- *)

val Sa_def = Define`Sa = SUBST`;
val Sb_def = Define`Sb = SUBST`;

val Sab_EQ = store_thm("Sab_EQ",
  `(Sb (Sa m a d) a e = Sa m a e) /\
   (Sb (Sb m a d) a e = Sb m a e) /\
   (Sa (Sa m a d) a e = Sa m a e)`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_EQ]
);

val Sa_EVAL = store_thm("Sa_EVAL",
  `!a w b. Sa m a w b = if a = b then w else m b`,
  RW_TAC std_ss [Sa_def,SUBST_def]
);

val Sb_EVAL = store_thm("Sb_EVAL",
  `!a w b. Sb m a w b = if a = b then w else m b`,
  RW_TAC std_ss [Sb_def,SUBST_def]
);

val Sa_RULE = store_thm("Sa_RULE",
  `!m (a:num) b d e. Sa (Sa m b d) a e =
     if a < b then Sb (Sa m a e) b d else Sb (Sa m b d) a e`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_COMMUTES]
);

val Sb_RULE = store_thm("Sb_RULE",
  `!m (a:num) b d e. Sa (Sb m b d) a e =
     if a < b then Sb (Sa m a e) b d else Sb (Sb m b d) a e`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_COMMUTES]
);

(* --- *)

val SUBST_COMMUTES4 = store_thm("SUBST_COMMUTES4",
  `!m a b d e. register2num a < register2num b ==>
     (SUBST (SUBST m b d) a e = SUBST (SUBST m a e) b d)`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
    THEN RW_TAC bool_ss [SUBST_def]
    THEN FULL_SIMP_TAC bool_ss [register2num_11]
);

val Sa_RULE4 = store_thm("Sa_RULE4",
  `!m a b d e. Sa (Sa m b d) a e =
     if register2num a < register2num b then
       Sb (Sa m a e) b d
     else
       Sb (Sa m b d) a e`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_COMMUTES4]
);

val Sb_RULE4 = store_thm("Sb_RULE4",
  `!m a b d e. Sa (Sb m b d) a e =
     if register2num a < register2num b then
       Sb (Sa m a e) b d
     else
       Sb (Sb m b d) a e`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_COMMUTES4]
);

(* --- *)

val SUBST_COMMUTES_PSR = store_thm("SUBST_COMMUTES_PSR",
  `!m a b d e. psrs2num b < psrs2num a ==>
     (SUBST (SUBST m b d) a e = SUBST (SUBST m a e) b d)`,
  REPEAT STRIP_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
    THEN RW_TAC bool_ss [SUBST_def]
    THEN FULL_SIMP_TAC bool_ss [psrs2num_11]
);

val Sa_RULE_PSR = store_thm("Sa_RULE_PSR",
  `!m a b d e. Sa (Sa m b d) a e =
     if psrs2num b < psrs2num a then
       Sb (Sa m a e) b d
     else
       Sb (Sa m b d) a e`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_COMMUTES_PSR]
);

val Sb_RULE_PSR = store_thm("Sb_RULE_PSR",
  `!m a b d e. Sa (Sb m b d) a e =
     if psrs2num b < psrs2num a then
       Sb (Sa m a e) b d
     else
       Sb (Sb m b d) a e`,
  RW_TAC std_ss [Sa_def,Sb_def,SUBST_COMMUTES_PSR]
);

(* -------------------------------------------------------- *)

val if_swp = PROVE [] ``!a b c. (if ~a then b else c) = (if a then c else b)``;

val LEAST16_def = Define`LEAST16 n = WHILE ($~ o (\b. BIT b n)) SUC 16`;

val LEASTBIT_EVAL =
  SIMP_RULE arith_ss [if_swp,GSYM LEAST16_def]
    (funpow 16 (ONCE_REWRITE_RULE [WHILE]) (REWRITE_RULE [LEAST_DEF] LEASTBIT_def));

val NUMERAL_LEASTBIT = save_thm("NUMERAL_LEASTBIT", (GEN_ALL o SPEC `NUMERAL n`) LEASTBIT_EVAL);

(* -------------------------------------------------------- *)

val SPEC_BIT_BITS_THM =
  (GEN_ALL o SYM o REWRITE_RULE [BITS_ZERO2,BIT_ZERO] o INST [`b` |-> `0`] o SPEC_ALL) BIT_BITS_THM;

val EXTEND_ONE_BIT = prove(
  `!h l n. l < h /\ (l2 = SUC l) ==> (~(BITS h l2 n = 0) \/ BIT l n = ~(BITS h l n = 0))`,
  RW_TAC bool_ss [GSYM LESS_EQ,SPEC_BIT_BITS_THM]
    THEN EQ_TAC THEN RW_TAC arith_ss []
    THENL [
      EXISTS_TAC `x` THEN ASM_SIMP_TAC arith_ss [],
      EXISTS_TAC `l` THEN ASM_SIMP_TAC arith_ss [],
      Cases_on `l = x` THEN1 ASM_REWRITE_TAC []
        THEN DISJ1_TAC THEN EXISTS_TAC `x` THEN ASM_SIMP_TAC arith_ss []
    ]
);

val MLA_MUL_DUR_EVAL = save_thm("MLA_MUL_DUR_EVAL",
  (GEN_ALL o SIMP_RULE std_ss [if_swp,EXTEND_ONE_BIT] o
   SIMP_RULE arith_ss [HB_def,GSYM BIT_def,WL_def])
    (funpow 17 (ONCE_REWRITE_RULE [WHILE])
       ((SIMP_RULE arith_ss [LEAST_DEF,MLA_MUL_DONE_def,BORROW2_def,BIT_def,MIN_DEF,
                             BITS_EVAL,BIT_EVAL,MOD_WL_THM,BITS_COMP_THM2] o SPEC `n2w n`) MLA_MUL_DUR_def))
);

val MLA_MUL_DUR_EVAL2 = store_thm("MLA_MUL_DUR_EVAL2",
  `!n. MLA_MUL_DUR (w32 n) =
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
  SIMP_TAC bool_ss [LET_THM,MLA_MUL_DUR_EVAL,BITS_THM2,DIV_2EXP_def,DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,GSYM EXP_ADD]
    THEN CONV_TAC (DEPTH_CONV reduceLib.ADD_CONV)
    THEN REWRITE_TAC []
);

(* -------------------------------------------------------- *)

(*
val NUMERAL_SUM = save_thm("NUMERAL_SUM",
  let val conj2 = (GEN_ALL o CONJUNCT2) sum_numTheory.SUM_def in
    CONJ (CONJ (GEN_ALL (CONJUNCT1 sum_numTheory.SUM_def))
         ((CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV o REWRITE_RULE [ADD] o SPEC `0`) conj2))
          ((CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV o GEN_ALL o SPEC `NUMERAL n`) conj2)
  end
);
*)

(* -------------------------------------------------------- *)

val _ = export_theory();
