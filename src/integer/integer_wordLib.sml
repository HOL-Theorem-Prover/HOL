structure integer_wordLib :> integer_wordLib =
struct

open HolKernel boolLib bossLib;

val WORD_DECIDE = wordsLib.WORD_DP wordsLib.WORD_CONV intLib.COOPER_PROVE

fun Cases_on_i2w t =
  Tactic.FULL_STRUCT_CASES_TAC
    (Q.ISPEC t integer_wordTheory.ranged_int_word_nchotomy);

local
  val int_min = SIMP_RULE (srw_ss()) [integer_wordTheory.INT_MAX_def]
                  integer_wordTheory.INT_MIN_def
in
  val INT_SIZES_CONV =
    (REWR_CONV int_min ORELSEC
     REWR_CONV integer_wordTheory.INT_MAX_def ORELSEC
     REWR_CONV integer_wordTheory.UINT_MAX_def)
    THENC Conv.DEPTH_CONV wordsLib.SIZES_CONV
    THENC intLib.REDUCE_CONV
end

val INT_SIZES_ss = simpLib.name_ss "int sizes"
 (simpLib.std_conv_ss
    {name = "INT_SIZES_CONV",
     conv = INT_SIZES_CONV,
     pats = [``integer_word$INT_MIN(:'a)``,
             ``integer_word$INT_MAX(:'a)``,
             ``integer_word$UINT_MAX(:'a)``]});

val _ = augment_srw_ss [INT_SIZES_ss];

end
