structure bitLib :> bitLib =
struct

open HolKernel Parse boolLib simpLib computeLib;
open bitTheory numeral_bitTheory

structure Parse = struct
  open Parse
  val (Type, Term) = parse_from_grammars bitTheory.bit_grammars
end
open Parse

(* ------------------------------------------------------------------------- *)

local
   val TIMES_2EXP1 =
      (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
       Q.SPECL [`x`, `1`]) bitTheory.TIMES_2EXP_def
   val rule = simpLib.SIMP_RULE (numLib.arith_ss++boolSimps.LET_ss)
   fun nrule l x =
      let
         val y = SPEC_ALL x
      in
         CONJ ((GEN_ALL o rule l o Q.INST [`n` |-> `0n`]) y)
              ((GEN_ALL o Q.INST [`n` |-> `NUMERAL n`]) y)
      end
   val BIT =
      (SIMP_RULE numLib.std_ss
         [GSYM ODD_MOD2_LEM, MOD_2EXP_def, BITS_def, SUC_SUB] o
          nrule [BITS_ZERO2]) BIT_def
   val thms =
      [pairTheory.UNCURRY_DEF, combinTheory.K_THM,
       iBITWISE, NUMERAL_BITWISE, BITV_def, SBIT_def,
       nrule [BIT_ZERO] SIGN_EXTEND_def,
       MOD_2EXP, numeral_imod_2exp, iDUB_NUMERAL,
       DIVMOD_2EXP, NUMERAL_DIV_2EXP, NUMERAL_TIMES_2EXP, NUMERAL_iDIV2,
       NUMERAL_SFUNPOW_iDIV2, NUMERAL_SFUNPOW_iDUB, NUMERAL_SFUNPOW_FDUB,
       FDUB_iDIV2, FDUB_iDUB, FDUB_FDUB,
       NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF,
       NUMERAL_BIT_REVERSE, NUMERAL_BIT_REV,
       nrule [NUMERAL_DIV_2EXP, numeral_bitTheory.MOD_2EXP] BITS_def,
       nrule [NUMERAL_DIV_2EXP, numeral_bitTheory.MOD_2EXP] SLICE_def,
       BIT, numLib.SUC_RULE MOD_2EXP_EQ, numLib.SUC_RULE MOD_2EXP_MAX_def,
       numeral_log2, numeral_ilog2, LOG_compute, LOWEST_SET_BIT_compute]
   fun mrw th = map (REWRITE_RULE [th])
   val thms =
      (mrw TIMES_2EXP1 o mrw (GSYM bitTheory.TIMES_2EXP_def) o
       mrw (GSYM bitTheory.MOD_2EXP_def)) thms
in
   fun add_bit_compset cmp = computeLib.add_thms thms cmp
end

val () = add_bit_compset computeLib.the_compset

(* ------------------------------------------------------------------------- *)

(* Testing...

open bitLib

val tst = Count.apply EVAL

tst ``DIV_2EXP 2 111``;
tst ``MOD_2EXP 23 11``;
tst ``DIVMOD_2EXP 3 111``;
tst ``TIMES_2EXP 3 111``;
tst ``SBIT T 4``;
tst ``BITS 4 1 213``;
tst ``SLICE 4 1 213``;
tst ``BITV 3 1``;
tst ``BIT 1 3``;
tst ``LOG2 123``
tst ``LOWEST_SET_BIT 120``
tst ``BIT_REVERSE 20 120``
tst ``BIT_MODIFY 12 (\i b. i > 3) 0``
tst ``SIGN_EXTEND 1 10 3``
tst ``MOD_2EXP_EQ 2 0b1111 0b11``
tst ``MOD_2EXP_MAX 2 0b1111``

*)

end
