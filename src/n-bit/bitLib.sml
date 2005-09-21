structure bitLib :> bitLib =
struct

(* app load ["bitTheory","numeral_bitTheory"]; *)

open HolKernel Parse boolLib bossLib;
open Q computeLib arithmeticTheory;
open bitTheory numeral_bitTheory;

(* ------------------------------------------------------------------------- *)

fun NUMERAL_ONLY_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o Q.INST [n |-> `0`]) y)
          ((GEN_ALL o Q.INST [n |-> `NUMERAL n`]) y)
  end;

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

val thms =
  [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF,
   iBITWISE, NUMERAL_BITWISE, NUMERAL_DIV2, LSB_def, BITV_def,
   REWRITE_RULE [TIMES_2EXP1] SIGN_EXTEND_def,
   REWRITE_RULE [TIMES_2EXP1] SBIT_def,
   DIVMOD_2EXP, iMOD_2EXP, NUMERAL_MOD_2EXP,
   NUMERAL_DIV_2EXP, NUMERAL_TIMES_2EXP,
   NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF,
   NUMERAL_BIT_REVERSE, NUMERAL_BIT_REV,
   NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` BITS_def,
   NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` SLICE_def,
   NUMERAL_ONLY_RULE [BITS_ZERO2] `n`  BIT_def,
   numeral_log2,numeral_ilog2];

fun bits_compset () =
  let val compset = reduceLib.num_compset()
      val _ = add_thms thms compset
      val _ = add_thms thms computeLib.the_compset
in
  compset
end;

val BITS_CONV = CBV_CONV (bits_compset());
val BITS_TAC = CONV_TAC BITS_CONV;

end
