structure integer_wordLib :> integer_wordLib =
struct

open HolKernel boolLib bossLib
open intLib wordsLib integer_wordSyntax

(* ------------------------------------------------------------------------ *)

val ERR = mk_HOL_ERR "integer_wordLib"

val WORD_DECIDE = wordsLib.WORD_DP wordsLib.WORD_CONV intLib.COOPER_PROVE

fun Cases_on_i2w t =
   Q.ISPEC_THEN t Tactic.FULL_STRUCT_CASES_TAC
     integer_wordTheory.ranged_int_word_nchotomy


fun INT_SIZES_CONV tm =
   if integer_wordSyntax.is_uint_max tm
      then (Conv.REWR_CONV integer_wordTheory.UINT_MAX
            THENC Conv.RAND_CONV wordsLib.SIZES_CONV) tm
   else if integer_wordSyntax.is_int_max tm
      then (Conv.REWR_CONV integer_wordTheory.INT_MAX
            THENC Conv.RAND_CONV wordsLib.SIZES_CONV) tm
   else if integer_wordSyntax.is_int_min tm
      then (Conv.REWR_CONV integer_wordTheory.INT_MIN
            THENC Conv.RAND_CONV (Conv.RAND_CONV wordsLib.SIZES_CONV)) tm
   else raise ERR "INT_SIZES_CONV" ""

val INT_SIZES_ss = simpLib.name_ss "int sizes"
   (simpLib.std_conv_ss
      {name = "INT_SIZES_CONV",
       conv = INT_SIZES_CONV,
       pats = [``integer_word$INT_MIN(:'a)``,
               ``integer_word$INT_MAX(:'a)``,
               ``integer_word$UINT_MAX(:'a)``]})

val () = augment_srw_ss [INT_SIZES_ss]

val add_integer_word_compset =
   let
      open integer_wordTheory
   in
      computeLib.add_thms
       [toString_def, fromString_def, i2w_def, w2i_def, UINT_MAX_def,
        INT_MAX_def, INT_MIN_def, saturate_i2w_def, saturate_i2sw_def,
        saturate_sw2sw_def, saturate_w2sw_def, saturate_sw2w_def,
        signed_saturate_add_def, signed_saturate_sub_def,
        word_sdiv_def, word_smod_def]
   end

val integer_word_conv =
  computeLib.compset_conv (reduceLib.num_compset())
    [computeLib.Extenders
       [intReduce.add_int_compset, wordsLib.add_words_compset true,
        add_integer_word_compset]]

val is_numeric = Lib.can (fcpSyntax.dest_numeric_type o boolSyntax.dest_itself)
val ty_ok = Lib.can wordsSyntax.size_of

fun is_ground tm =
  case Lib.total boolSyntax.dest_strip_comb tm of
     SOME ("integer_word$toString", [a]) => intSyntax.is_int_literal a
   | SOME ("integer_word$fromString", [a]) => stringSyntax.is_string_literal a
   | SOME ("integer_word$i2w", [a]) =>
       intSyntax.is_int_literal a andalso ty_ok tm
   | SOME ("integer_word$w2i", [a]) =>
       wordsSyntax.is_word_literal a andalso ty_ok a
   | SOME ("integer_word$UINT_MAX", [a]) => is_numeric a
   | SOME ("integer_word$INT_MAX", [a]) => is_numeric a
   | SOME ("integer_word$INT_MIN", [a]) => is_numeric a
   | SOME ("integer_word$saturate_i2w", [a]) =>
       intSyntax.is_int_literal a andalso ty_ok tm
   | SOME ("integer_word$saturate_i2sw", [a]) =>
       intSyntax.is_int_literal a andalso ty_ok tm
   | SOME ("integer_word$saturate_w2sw", [a]) =>
       wordsSyntax.is_word_literal a andalso ty_ok a andalso ty_ok tm
   | SOME ("integer_word$saturate_sw2w", [a]) =>
       wordsSyntax.is_word_literal a andalso ty_ok a andalso ty_ok tm
   | SOME ("integer_word$saturate_sw2sw", [a]) =>
       wordsSyntax.is_word_literal a andalso ty_ok a andalso ty_ok tm
   | SOME ("integer_word$signed_saturate_add", [a, b]) =>
        wordsSyntax.is_word_literal a andalso wordsSyntax.is_word_literal b
        andalso ty_ok tm
   | SOME ("integer_word$signed_saturate_sub", [a, b]) =>
        wordsSyntax.is_word_literal a andalso wordsSyntax.is_word_literal b
        andalso ty_ok tm
   | SOME ("integer_word$word_sdiv", [a, b]) =>
        wordsSyntax.is_word_literal a andalso wordsSyntax.is_word_literal b
        andalso ty_ok tm
   | SOME ("integer_word$word_smod", [a, b]) =>
        wordsSyntax.is_word_literal a andalso wordsSyntax.is_word_literal b
        andalso ty_ok tm
   | _ => false

fun INT_WORD_GROUND_CONV tm =
  if is_ground tm then integer_word_conv tm
  else raise ERR "INT_WORD_GROUND_CONV" "not ground integer word operation"

(* ------------------------------------------------------------------------ *)

end
