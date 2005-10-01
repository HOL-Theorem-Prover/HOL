structure wordsLib :> wordsLib =
struct

(* interactive use:
  app load ["fcpLib", "numeral_bitTheory",
            "wordsTheory", "machine_wordsTheory"];
*)

open HolKernel Parse boolLib bossLib;
open computeLib;
open bitTheory numeral_bitTheory wordsTheory machine_wordsTheory;

(* ------------------------------------------------------------------------- *)

val machine_sizes = map snd (theorems "machine_words");

val SIZES_ss = rewrites machine_sizes;

fun NUMERAL_ONLY_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ
     ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o Q.INST [n |-> `0`]) y)
     ((GEN_ALL o Q.INST [n |-> `NUMERAL n`]) y)
  end;

val thms = machine_sizes @
  [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF,
   iBITWISE, NUMERAL_BITWISE, NUMERAL_DIV2, LSB_def, BITV_def,
   SIGN_EXTEND_def, SBIT_def,
   DIVMOD_2EXP, iMOD_2EXP, NUMERAL_MOD_2EXP,
   NUMERAL_DIV_2EXP, NUMERAL_TIMES_2EXP,
   NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF,
   NUMERAL_BIT_REVERSE, NUMERAL_BIT_REV,
   NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` BITS_def,
   NUMERAL_ONLY_RULE [NUMERAL_DIV_2EXP,iMOD_2EXP] `n` SLICE_def,
   NUMERAL_ONLY_RULE [BITS_ZERO2] `n`  BIT_def,
   numeral_log2,numeral_ilog2,
   n2w_11, n2w_w2n, w2n_n2w, w2w_def, sw2sw_def,
   word_L_def, word_H_def, word_T_def, fcpTheory.index_sum,
   word_concat_def, word_reverse_n2w, word_modify_n2w, word_log2_n2w,
   word_1comp_n2w, word_or_n2w, word_xor_n2w, word_and_n2w,
   word_2comp_n2w, word_add_n2w, word_sub_def, word_mul_n2w,
   word_asr_n2w, word_lsr_n2w, word_lsl_n2w,
   word_ror_n2w, word_rol_def, word_rrx_n2w,
   word_lsb_n2w, word_msb_n2w, word_bit_n2w,
   word_bits_n2w, word_slice_n2w, word_extract_def,
   word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
   word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w];

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

val thms =
  let fun mrw th = map (REWRITE_RULE [th])
in
    (mrw TIMES_2EXP1 o mrw (GSYM bitTheory.TIMES_2EXP_def) o
     mrw (GSYM bitTheory.MOD_2EXP_def)) thms
end;

fun words_compset () =
  let val compset = reduceLib.num_compset()
      val _ = add_thms thms compset
in
  compset
end;

val _ = add_thms thms computeLib.the_compset;

val mk_index_type = fcpLib.mk_index_type;

fun mk_word_type n =
  let val _ = mk_index_type n
      val sn = Int.toString n
      val TYPE = mk_type("cart", [bool, mk_type("i"^sn, [])])
  in
    type_abbrev("word"^sn, TYPE)
  end;

val WORDS_CONV = CBV_CONV (words_compset());
val WORDS_RULE = CONV_RULE WORDS_CONV;
val WORDS_TAC = CONV_TAC WORDS_CONV;

fun Cases_on_word tm = Q.ISPEC_THEN tm FULL_STRUCT_CASES_TAC word_nchotomy;

fun Cases_word (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_word" "not a forall")
  in (STRIP_TAC THEN STRUCT_CASES_TAC (Drule.ISPEC Bvar word_nchotomy)) g
  end;

end
