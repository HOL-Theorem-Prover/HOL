structure wordsLib :> wordsLib =
struct

(* interactive use:
  app load ["fcpLib", "numeral_bitTheory", "wordsTheory", "wordsSyntax"];
*)

open HolKernel Parse boolLib bossLib computeLib;
open bitTheory numeral_bitTheory wordsTheory wordsSyntax;

(* ------------------------------------------------------------------------- *)

fun is_fcp_thm s =
  String.isPrefix "finite_" s orelse String.isPrefix "dimindex_" s orelse
  String.isPrefix "dimword_" s orelse String.isPrefix "INT_MIN_"s;

val machine_sizes = (map snd o filter (is_fcp_thm o fst) o theorems) "words";

val SIZES_ss = rewrites machine_sizes;

fun NUM_RULE l n x =
  let val y = SPEC_ALL x
  in CONJ
     ((GEN_ALL o simpLib.SIMP_RULE bossLib.arith_ss l o Q.INST [n |-> `0`]) y)
     ((GEN_ALL o Q.INST [n |-> `NUMERAL n`]) y)
  end;

val MOD_WL = 
  (CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))));

val thms = machine_sizes @
  [numeralTheory.numeral_funpow, pairTheory.UNCURRY_DEF,
   iBITWISE, NUMERAL_BITWISE, LSB_def, BITV_def, SIGN_EXTEND_def, SBIT_def,
   DIVMOD_2EXP, NUMERAL_DIV_2EXP, NUMERAL_TIMES_2EXP,
   NUMERAL_BIT_MODIFY, NUMERAL_BIT_MODF,
   NUMERAL_BIT_REVERSE, NUMERAL_BIT_REV,
   NUM_RULE [NUMERAL_DIV_2EXP,numeralTheory.MOD_2EXP] `n` BITS_def,
   NUM_RULE [NUMERAL_DIV_2EXP,numeralTheory.MOD_2EXP] `n` SLICE_def,
   NUM_RULE [BITS_ZERO2] `n`  BIT_def, INT_MIN_SUM,
   numeral_log2,numeral_ilog2,
   n2w_11, n2w_w2n, w2n_n2w, w2w_def, sw2sw_def, word_len_def,
   word_L_def, word_H_def, word_T_def, fcpTheory.index_sum,
   word_join_def, word_concat_def,
   word_reverse_n2w, word_modify_n2w, word_log2_n2w,
   word_1comp_n2w, word_or_n2w, word_xor_n2w, word_and_n2w,
   word_2comp_n2w, word_sub_def, word_div_def, word_sdiv_def,
   MOD_WL word_add_n2w, MOD_WL word_mul_n2w,
   word_asr_n2w, word_lsr_n2w, word_lsl_n2w,
   (List.last o CONJUNCTS) SHIFT_ZERO, SPEC ``NUMERAL n`` word_ror_n2w,
   word_rol_def, word_rrx_n2w,
   word_lsb_n2w, word_msb_n2w, word_bit_n2w, word_index_n2w,
   word_bits_n2w, word_slice_n2w, fcp_n2w,
   SIMP_RULE std_ss [FUN_EQ_THM] word_extract_def,
   word_ge_n2w, word_gt_n2w, word_hi_n2w, word_hs_n2w,
   word_le_n2w, word_lo_n2w, word_ls_n2w, word_lt_n2w];

val TIMES_2EXP1 =
 (GSYM o REWRITE_RULE [arithmeticTheory.MULT_LEFT_1] o
  Q.SPECL [`x`,`1`]) bitTheory.TIMES_2EXP_def;

val thms =
  let fun mrw th = map (REWRITE_RULE [th])
in
    (mrw TIMES_2EXP1 o mrw (GSYM bitTheory.TIMES_2EXP_def) o
     mrw (GSYM arithmeticTheory.MOD_2EXP_def)) thms
end;

fun words_compset () =
  let val compset = reduceLib.num_compset()
      val _ = add_thms thms compset
in
  compset
end;

val _ = add_thms thms computeLib.the_compset;

fun mk_index_size n = (fcpLib.mk_index_type n;());

fun mk_word_size n =
  let val (_, _, dimindex_thm) = fcpLib.mk_index_type n
      val sn = Int.toString n
      val ityp = mk_type("i"^sn, [])
      val TYPE = mk_type("cart", [bool, ityp])
      val INT_MIN = save_thm("INT_MIN_" ^ sn,
                  (SIMP_RULE std_ss [dimindex_thm] o
                   Thm.INST_TYPE [``:'a`` |-> ityp]) INT_MIN_def)
      val dimword = save_thm("dimword_" ^ sn,
                  (SIMP_RULE std_ss [INT_MIN] o
                   Thm.INST_TYPE [``:'a`` |-> ityp]) dimword_IS_TWICE_INT_MIN)
      val _ = add_thms [INT_MIN,dimword] computeLib.the_compset
  in
    type_abbrev("word"^sn, TYPE)
  end;

val WORDS_CONV = CBV_CONV (words_compset());
val WORDS_RULE = CONV_RULE WORDS_CONV;
val WORDS_TAC = CONV_TAC WORDS_CONV;

(* ------------------------------------------------------------------------- *)

fun Cases_on_word tm =
   Q.ISPEC_THEN tm FULL_STRUCT_CASES_TAC ranged_word_nchotomy;

fun Cases_word (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_word" "not a forall")
  in (STRIP_TAC THEN STRUCT_CASES_TAC (Drule.ISPEC Bvar ranged_word_nchotomy)) g
  end;

(* ------------------------------------------------------------------------- *)

fun print_word base_map sys gravs d pps t = let
   open Portable term_pp_types
   val (n,x) = dest_n2w t
   val m = numSyntax.dest_numeral n
in
  add_string pps
   ((case base_map x of
       StringCvt.DEC => Arbnum.toString m
     | StringCvt.BIN => "0b"^(Arbnum.toBinString m)
     | StringCvt.OCT => "0" ^(Arbnum.toOctString m)
     | StringCvt.HEX => "0x"^(Arbnum.toHexString m)) ^ "w")
end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun pp_word base_map = Parse.temp_add_user_printer
  ({Tyop = "cart", Thy = "fcp"}, print_word base_map);

fun pp_word_bin() = pp_word (fn x => StringCvt.BIN);
fun pp_word_oct() = pp_word (fn x => StringCvt.OCT);
fun pp_word_hex() = pp_word (fn x => StringCvt.HEX);

fun pp_word_dec() = Parse.remove_user_printer {Tyop="cart", Thy="fcp"};

(* Example:
val _ = pp_word (fn x => if Type.compare(x,``:i32``) = EQUAL then
                           StringCvt.HEX else StringCvt.DEC);       *)

end
