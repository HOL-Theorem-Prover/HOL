structure word32Lib :> word32Lib =
struct

(* app load ["bossLib","bitsTheory","word32Theory"]; *)
open HolKernel boolLib bossLib computeLib simpLib numLib pairTheory
     bitsTheory word32Theory;

infix 8 by;
infix THEN THENC THENL ++;

(* -------------------------------------------------------- *)

fun armword_rws () =
  let val rws = reduceLib.num_compset()
      val _ = add_thms 
     [w_0,w_1,w_T,
      MODw_EVAL,
      ADD_EVAL2,
      MUL_EVAL2,
      REDUCE_RULE ONE_COMP_EVAL2,
      REDUCE_RULE TWO_COMP_EVAL2,
      SUBw_def,
      REWRITE_RULE [LSB_ODD] BITWISE_EVAL2,
      AND_EVAL2,
      OR_EVAL2,
      EOR_EVAL2,
      LSLw_def,
      LSR_EVAL,
      SIMP_RULE arith_ss [MSB_def,HB_def] ASR_EVAL,
      SIMP_RULE arith_ss [LSB_ODD,HB_def] ROR_EVAL,
      REDUCE_RULE RRX_EVAL2,
      BITw_def,
      BITSw_def,
      SLICEw_def,
      NUMw_EVAL,
      MSB_EVAL2,
      LSB_EVAL2,
      FUNPOW_EVAL,
      UNCURRY_DEF,
      TIMES_2EXP_def,DIV_2EXP_def,MOD_2EXP_def,DIVMOD_2EXP_def,
      SET_def,BITS_THM,BIT_def,SLICE_def,LET_THM] rws
in
   rws
end;

val word_compset = armword_rws();

val WORD_CONV = CBV_CONV word_compset;
val WORD_RULE = CONV_RULE WORD_CONV;
val WORD_TAC = CONV_TAC WORD_CONV;

(* -------------------------------------------------------- *)

end
