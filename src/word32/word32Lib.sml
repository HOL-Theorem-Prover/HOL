structure word32Lib :> word32Lib =
struct

(* app load ["bossLib","bitsTheory","word32Theory"]; *)

open HolKernel boolLib computeLib bossLib 
     simpLib numLib bitsTheory word32Theory;


(* -------------------------------------------------------- *)

val word_compset =
  let val rws = reduceLib.num_compset()
      val _ = add_thms 
     [w_0,w_1,w_T,
      MODw_EVAL,
      ADD_EVAL2,
      MUL_EVAL2,
      REDUCE_RULE ONE_COMP_EVAL2,
      REDUCE_RULE TWO_COMP_EVAL2,
      word_sub,
      BITWISE_EVAL2,
      AND_EVAL2,
      OR_EVAL2,
      EOR_EVAL2,
      word_lsl,
      LSR_EVAL,
      ASR_THM,
      ROR_THM,
      REDUCE_RULE RRX_EVAL2,
      BITw_def,
      BITSw_def,
      SLICEw_def,
      NUMw_EVAL,
      MSB_EVAL2,
      LSB_EVAL2,
      numeralTheory.numeral_funpow,
      pairTheory.UNCURRY_DEF,
      TIMES_2EXP_def,DIV_2EXP_def,MOD_2EXP_def,DIVMOD_2EXP_def,
      SET_def,BITS_THM,BIT_def,SLICE_def,LET_THM] rws
in
   rws
end;

val WORD_CONV = CBV_CONV word_compset;
val WORD_RULE = CONV_RULE WORD_CONV;
val WORD_TAC = CONV_TAC WORD_CONV;

val WORD32_CONV = WORD_CONV
val WORD32_RULE = WORD_RULE
val WORD32_TAC = WORD_TAC

(* -------------------------------------------------------- *)

end
