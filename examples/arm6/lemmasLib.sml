(* app load ["armTheory","coreTheory","lemmasTheory","blockTheory"]; *)
open HolKernel boolLib bossLib Q word32Theory armTheory coreTheory
     lemmasTheory blockTheory interruptsTheory;

(* -------------------------------------------------------- *)

val std_ss = std_ss ++ boolSimps.LET_ss;

val UNFOLD_NEXT = ONCE_REWRITE_TAC [numeralTheory.numeral_funpow]
   THEN CONV_TAC (DEPTH_CONV reduceLib.PRE_CONV)
   THEN PURE_REWRITE_TAC [CONJUNCT1 arithmeticTheory.FUNPOW,SNEXT_NEXT_ARM6,
                          pairTheory.FST,pairTheory.SND];

val finish_rws = [INIT_ARM6_def,DECODE_PSR_def,NXTIC_def,MASK_MASK,
                  TO_WRITE_READ6,REG_READ_WRITE,REG_WRITE_COMMUTE_PC,
                  REGISTER_RANGES,RP_LT_16,RP_LT_16_0,AREGN1_THM,AREGN1_BIJ];

fun FINISH_OFF n =
  ASM_SIMP_TAC compLib.stdi_ss []
    THEN POP_ASSUM_LIST (fn thl => MAP_EVERY ASSUME_TAC (List.take(thl,n)))
    THEN STRIP_TAC
    THEN POP_ASSUM (SUBST1_TAC o SYM)
    THEN RW_TAC std_ss finish_rws
    THEN FULL_SIMP_TAC std_ss [MASK_MASK];

val finish_rws2 =
  [TO_WRITE_READ6,READ_TO_READ6,REG_WRITE_WRITE,REGISTER_RANGES,REG_WRITE_READ,
   REG_READ_WRITE,REG_WRITE_COMMUTE_PC,CONJUNCT1 exception_BIJ,
   GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,REWRITE_RULE [word_0] WORD_ADD_0,ADD4_ADD4];

val UNFOLD_SPEC =
   (GEN_ALL o SIMP_RULE (srw_ss()) [GEN_ALL STATE_ARM_def] o
    numLib.REDUCE_RULE o SPECL [`0`,`<| state := a; inp := i|>`] o CONJUNCT2) STATE_ARM_def;

(* -------------------------------------------------------- *)
