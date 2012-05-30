structure integer_wordLib :> integer_wordLib =
struct

open HolKernel boolLib bossLib;
open intLib wordsLib integer_wordSyntax;

val ERR = mk_HOL_ERR "integer_wordLib";

val WORD_DECIDE = wordsLib.WORD_DP wordsLib.WORD_CONV intLib.COOPER_PROVE

fun Cases_on_i2w t =
   Q.ISPEC_THEN t Tactic.FULL_STRUCT_CASES_TAC
     integer_wordTheory.ranged_int_word_nchotomy


fun INT_SIZES_CONV tm =
  if integer_wordSyntax.is_uint_max tm then
    (Conv.REWR_CONV integer_wordTheory.UINT_MAX
     THENC Conv.RAND_CONV wordsLib.SIZES_CONV) tm
  else if integer_wordSyntax.is_int_max tm then
    (Conv.REWR_CONV integer_wordTheory.INT_MAX
     THENC Conv.RAND_CONV wordsLib.SIZES_CONV) tm
  else if integer_wordSyntax.is_int_min tm then
    (Conv.REWR_CONV integer_wordTheory.INT_MIN
     THENC Conv.RAND_CONV (Conv.RAND_CONV wordsLib.SIZES_CONV)) tm
  else
    raise ERR "INT_SIZES_CONV" ""

val INT_SIZES_ss = simpLib.name_ss "int sizes"
 (simpLib.std_conv_ss
    {name = "INT_SIZES_CONV",
     conv = INT_SIZES_CONV,
     pats = [``integer_word$INT_MIN(:'a)``,
             ``integer_word$INT_MAX(:'a)``,
             ``integer_word$UINT_MAX(:'a)``]});

val _ = augment_srw_ss [INT_SIZES_ss];

end
