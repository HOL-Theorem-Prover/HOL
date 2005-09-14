structure wordsLib :> wordsLib =
struct

(* iinteractive use:
  app load ["fcpLib", "bitLib", "wordsTheory"];
*)

open HolKernel Parse boolLib bossLib;
open computeLib;
open bitLib wordsTheory;

(* ------------------------------------------------------------------------- *)

val thms =
  [n2w_11, n2w_w2n, w2n_n2w, w2w_def, sw2sw_def,
   word_L_def, word_H_def, word_T_def, fcpTheory.index_sum,
   word_concat_def, word_reverse_n2w, word_log2_n2w,
   word_1comp_n2w, word_or_n2w, word_xor_n2w, word_and_n2w,
   word_2comp_n2w, word_add_n2w, word_sub_def, word_mul_n2w,
   word_asr_n2w, word_lsr_n2w, word_lsl_n2w,
   word_ror_n2w, word_rol_def, word_rrx_n2w,
   word_msb_n2w, word_bit_n2w, word_bits_n2w, word_slice_n2w,
   word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
   word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w];

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def

val thms =
  let fun mrw th = map (REWRITE_RULE [th])
in
    (mrw TIMES_2EXP1 o mrw (GSYM bitTheory.TIMES_2EXP_def) o
     mrw (GSYM bitTheory.MOD_2EXP_def)) thms
end;

fun words_compset () =
  let val compset = bits_compset()
      val _ = add_thms thms compset
in
  compset
end;

val _ = add_thms thms computeLib.the_compset

val mk_index_type = fcpLib.mk_index_type;

end
