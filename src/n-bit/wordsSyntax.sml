structure wordsSyntax :> wordsSyntax =
struct

open HolKernel Parse boolLib bossLib
open bitSyntax fcpSyntax fcpLib wordsTheory

val ERR = mk_HOL_ERR "wordsSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns "words" n d m

(*---------------------------------------------------------------------------*)
(* Word types                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_word_type ty = fcpSyntax.mk_cart_type (Type.bool, ty)

val mk_int_word_type = mk_word_type o fcpSyntax.mk_int_numeric_type

fun dest_word_type ty =
   let
      val (a, b) = fcpSyntax.dest_cart_type ty
      val _ = a = Type.bool orelse
                  raise ERR "dest_word_type" "not an instance of :bool['a]"
   in
      b
   end

val is_word_type = Lib.can dest_word_type
val dim_of = dest_word_type o Term.type_of
val size_of = fcpLib.index_to_num o dim_of

(*---------------------------------------------------------------------------*)
(* Terms, Constructors, Destructors and Discriminators                       *)
(*---------------------------------------------------------------------------*)

val fcp_index_tm = fcpSyntax.fcp_index_tm

fun mk_index (w, n) =
  Lib.with_exn HolKernel.list_mk_comb
    (Term.inst [Type.alpha |-> Type.bool, Type.beta |-> dim_of w] fcp_index_tm,
     [w, n])
    (ERR "mk_index" "")

val dest_index = fcpSyntax.dest_fcp_index
val is_index = Lib.can dest_index

val dimindex_tm = fcpSyntax.dimindex_tm
val mk_dimindex = fcpSyntax.mk_dimindex
val dest_dimindex = fcpSyntax.dest_dimindex
val is_dimindex = Lib.can dest_dimindex

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then dim_of tm2 else raise e)
   (fn tm => fn ty => Term.inst [Type.alpha |-> ty] tm)

val (word_T_tm, mk_word_T, dest_word_T, is_word_T) = s "word_T"
val (word_L_tm, mk_word_L, dest_word_L, is_word_L) = s "word_L"
val (word_H_tm, mk_word_H, dest_word_H, is_word_H) = s "word_H"
val (word_L2_tm, mk_word_L2, dest_word_L2, is_word_L2) = s "word_L2"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1
   (fn tm1 => fn e => boolSyntax.dest_itself o HolKernel.dest_monop tm1 e)
   (fn tm => fn ty =>
      Term.mk_comb (Term.inst [Type.alpha |-> ty] tm, boolSyntax.mk_itself ty))

val (dimword_tm, mk_dimword, dest_dimword, is_dimword) = s "dimword"
val (uint_max_tm, mk_uint_max, dest_uint_max, is_uint_max) = s "UINT_MAX"
val (int_min_tm, mk_int_min, dest_int_min, is_int_min) = s "INT_MIN"
val (int_max_tm, mk_int_max, dest_int_max, is_int_max) = s "INT_MAX"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop

val (w2n_tm, mk_w2n, dest_w2n, is_w2n) = s "w2n"
val (word_abs_tm, mk_word_abs, dest_word_abs, is_word_abs) = s "word_abs"
val (word_len_tm, mk_word_len, dest_word_len, is_word_len) = s "word_len"
val (word_log2_tm, mk_word_log2, dest_word_log2, is_word_log2) = s "word_log2"
val (word_msb_tm, mk_word_msb, dest_word_msb, is_word_msb) = s "word_msb"
val (word_lsb_tm, mk_word_lsb, dest_word_lsb, is_word_lsb) = s "word_lsb"
val (bit_count_tm, mk_bit_count, dest_bit_count, is_bit_count) = s "bit_count"
val (reduce_or_tm, mk_reduce_or, dest_reduce_or, is_reduce_or) = s "reduce_or"

val (reduce_and_tm, mk_reduce_and, dest_reduce_and, is_reduce_and) =
   s "reduce_and"

val (reduce_nand_tm, mk_reduce_nand, dest_reduce_nand, is_reduce_nand) =
   s "reduce_nand"

val (reduce_nor_tm, mk_reduce_nor, dest_reduce_nor, is_reduce_nor) =
   s "reduce_nor"

val (reduce_xnor_tm, mk_reduce_xnor, dest_reduce_xnor, is_reduce_xnor) =
   s "reduce_xnor"

val (reduce_xor_tm, mk_reduce_xor, dest_reduce_xor, is_reduce_xor) =
   s "reduce_xor"

val (word_1comp_tm, mk_word_1comp, dest_word_1comp, is_word_1comp) =
   s "word_1comp"

val (word_2comp_tm, mk_word_2comp, dest_word_2comp, is_word_2comp) =
   s "word_2comp"

val (word_reverse_tm, mk_word_reverse, dest_word_reverse, is_word_reverse) =
   s "word_reverse"

val (word_to_bin_list_tm, mk_word_to_bin_list,
     dest_word_to_bin_list, is_word_to_bin_list) = s "word_to_bin_list"

val (word_to_oct_list_tm, mk_word_to_oct_list,
     dest_word_to_oct_list, is_word_to_oct_list) = s "word_to_oct_list"

val (word_to_dec_list_tm, mk_word_to_dec_list,
     dest_word_to_dec_list, is_word_to_dec_list) = s "word_to_dec_list"

val (word_to_hex_list_tm, mk_word_to_hex_list,
     dest_word_to_hex_list, is_word_to_hex_list) = s "word_to_hex_list"

val (word_to_bin_string_tm, mk_word_to_bin_string,
     dest_word_to_bin_string, is_word_to_bin_string) = s "word_to_bin_string"

val (word_to_oct_string_tm, mk_word_to_oct_string,
     dest_word_to_oct_string, is_word_to_oct_string) = s "word_to_oct_string"

val (word_to_dec_string_tm, mk_word_to_dec_string,
     dest_word_to_dec_string, is_word_to_dec_string) = s "word_to_dec_string"

val (word_to_hex_string_tm, mk_word_to_hex_string,
     dest_word_to_hex_string, is_word_to_hex_string) = s "word_to_hex_string"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1
   (fn tm => fn e => pairSyntax.dest_pair o HolKernel.dest_monop tm e)
   (fn tm => fn (x, w) =>
       Term.mk_comb (Term.inst [Type.alpha |-> dim_of w] tm,
                     pairSyntax.mk_pair (x, w)))

val (word_rrx_tm, mk_word_rrx, dest_word_rrx, is_word_rrx) = s "word_rrx"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1
   (fn tm => fn e => fn x =>
      let
         val (a, y) = pairSyntax.dest_pair (HolKernel.dest_monop tm e x)
         val (b, c) = pairSyntax.dest_pair y
      in
         (a, b, c)
      end)
   (fn tm => fn (a, b, c) =>
       Term.mk_comb (Term.inst [Type.alpha |-> dim_of a] tm,
                     pairSyntax.list_mk_pair [a, b, c]))

val (add_with_carry_tm, mk_add_with_carry,
     dest_add_with_carry, is_add_with_carry) = s "add_with_carry"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1
   (fn tm1 => fn e => fn w => (HolKernel.dest_monop tm1 e w, dim_of w))
   (fn tm => fn (w, ty) => Term.mk_comb (Term.inst [Type.alpha |-> ty] tm, w))

val (n2w_tm, mk_n2w, dest_n2w, is_n2w) = s "n2w"

val (saturate_n2w_tm, mk_saturate_n2w, dest_saturate_n2w, is_saturate_n2w) =
   s "saturate_n2w"

val (word_from_bin_list_tm, mk_word_from_bin_list,
     dest_word_from_bin_list, is_word_from_bin_list) = s "word_from_bin_list"

val (word_from_oct_list_tm, mk_word_from_oct_list,
     dest_word_from_oct_list, is_word_from_oct_list) = s "word_from_oct_list"

val (word_from_dec_list_tm, mk_word_from_dec_list,
     dest_word_from_dec_list, is_word_from_dec_list) = s "word_from_dec_list"

val (word_from_hex_list_tm, mk_word_from_hex_list,
     dest_word_from_hex_list, is_word_from_hex_list) = s "word_from_hex_list"

val (word_from_bin_string_tm, mk_word_from_bin_string,
     dest_word_from_bin_string, is_word_from_bin_string) =
   s "word_from_bin_string"

val (word_from_oct_string_tm, mk_word_from_oct_string,
     dest_word_from_oct_string, is_word_from_oct_string) =
   s "word_from_oct_string"

val (word_from_dec_string_tm, mk_word_from_dec_string,
     dest_word_from_dec_string, is_word_from_dec_string) =
   s "word_from_dec_string"

val (word_from_hex_string_tm, mk_word_from_hex_string,
     dest_word_from_hex_string, is_word_from_hex_string) = s
   "word_from_hex_string"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1
   (fn tm1 => fn e => fn w => (HolKernel.dest_monop tm1 e w, dim_of w))
   (fn tm => fn (w, ty) =>
       Term.mk_comb
         (Term.inst [Type.alpha |-> dim_of w, Type.beta |-> ty] tm, w))

val (w2w_tm, mk_w2w, dest_w2w, is_w2w) = s "w2w"
val (sw2sw_tm, mk_sw2sw, dest_sw2sw, is_sw2sw) = s "sw2sw"

val (saturate_w2w_tm, mk_saturate_w2w, dest_saturate_w2w, is_saturate_w2w) =
   s "saturate_w2w"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 1
   (fn tm1 => fn e => fn w => (HolKernel.dest_monop tm1 e w, dim_of w))
   (fn tm => fn (l, ty) =>
      let
         val d = dest_word_type (listSyntax.dest_list_type (Term.type_of l))
      in
         Term.mk_comb (Term.inst [Type.alpha |-> d, Type.beta |-> ty] tm, l)
      end)

val (concat_word_list_tm, mk_concat_word_list,
     dest_concat_word_list, is_concat_word_list) = s "concat_word_list"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop

val (w2l_tm, mk_w2l, dest_w2l, is_w2l) = s "w2l"
val (nzcv_tm, mk_nzcv, dest_nzcv, is_nzcv) = s "nzcv"
val (word_lt_tm, mk_word_lt, dest_word_lt, is_word_lt) = s "word_lt"
val (word_le_tm, mk_word_le, dest_word_le, is_word_le) = s "word_le"
val (word_gt_tm, mk_word_gt, dest_word_gt, is_word_gt) = s "word_gt"
val (word_ge_tm, mk_word_ge, dest_word_ge, is_word_ge) = s "word_ge"
val (word_lo_tm, mk_word_lo, dest_word_lo, is_word_lo) = s "word_lo"
val (word_ls_tm, mk_word_ls, dest_word_ls, is_word_ls) = s "word_ls"
val (word_hi_tm, mk_word_hi, dest_word_hi, is_word_hi) = s "word_hi"
val (word_hs_tm, mk_word_hs, dest_word_hs, is_word_hs) = s "word_hs"
val (word_or_tm, mk_word_or, dest_word_or, is_word_or) = s "word_or"
val (word_and_tm, mk_word_and, dest_word_and, is_word_and) = s "word_and"
val (word_xor_tm, mk_word_xor, dest_word_xor, is_word_xor) = s "word_xor"
val (word_nor_tm, mk_word_nor, dest_word_nor, is_word_nor) = s "word_nor"
val (word_nand_tm, mk_word_nand, dest_word_nand, is_word_nand) = s "word_nand"
val (word_xnor_tm, mk_word_xnor, dest_word_xnor, is_word_xnor) = s "word_xnor"
val (word_add_tm, mk_word_add, dest_word_add, is_word_add) = s "word_add"
val (word_sub_tm, mk_word_sub, dest_word_sub, is_word_sub) = s "word_sub"
val (word_mul_tm, mk_word_mul, dest_word_mul, is_word_mul) = s "word_mul"
val (word_div_tm, mk_word_div, dest_word_div, is_word_div) = s "word_div"
val (word_mod_tm, mk_word_mod, dest_word_mod, is_word_mod) = s "word_mod"
val (word_sdiv_tm, mk_word_sdiv, dest_word_sdiv, is_word_sdiv) = s "word_sdiv"
val (word_srem_tm, mk_word_srem, dest_word_srem, is_word_srem) = s "word_srem"
val (word_smod_tm, mk_word_smod, dest_word_smod, is_word_smod) = s "word_smod"
val (word_smin_tm, mk_word_smin, dest_word_smin, is_word_smin) = s "word_smin"
val (word_smax_tm, mk_word_smax, dest_word_smax, is_word_smax) = s "word_smax"
val (word_min_tm, mk_word_min, dest_word_min, is_word_min) = s "word_min"
val (word_max_tm, mk_word_max, dest_word_max, is_word_max) = s "word_max"
val (word_lsl_tm, mk_word_lsl, dest_word_lsl, is_word_lsl) = s "word_lsl"
val (word_lsr_tm, mk_word_lsr, dest_word_lsr, is_word_lsr) = s "word_lsr"
val (word_asr_tm, mk_word_asr, dest_word_asr, is_word_asr) = s "word_asr"
val (word_ror_tm, mk_word_ror, dest_word_ror, is_word_ror) = s "word_ror"
val (word_rol_tm, mk_word_rol, dest_word_rol, is_word_rol) = s "word_rol"
val (word_bit_tm, mk_word_bit, dest_word_bit, is_word_bit) = s "word_bit"

val (word_lsl_bv_tm, mk_word_lsl_bv, dest_word_lsl_bv, is_word_lsl_bv) =
   s "word_lsl_bv"

val (word_lsr_bv_tm, mk_word_lsr_bv, dest_word_lsr_bv, is_word_lsr_bv) =
   s "word_lsr_bv"

val (word_asr_bv_tm, mk_word_asr_bv, dest_word_asr_bv, is_word_asr_bv) =
   s "word_asr_bv"

val (word_ror_bv_tm, mk_word_ror_bv, dest_word_ror_bv, is_word_ror_bv) =
   s "word_ror_bv"

val (word_rol_bv_tm, mk_word_rol_bv, dest_word_rol_bv, is_word_rol_bv) =
   s "word_rol_bv"

val (word_compare_tm, mk_word_compare, dest_word_compare, is_word_compare) =
   s "word_compare"

val (saturate_add_tm, mk_saturate_add, dest_saturate_add, is_saturate_add) =
   s "saturate_add"

val (saturate_sub_tm, mk_saturate_sub, dest_saturate_sub, is_saturate_sub) =
   s "saturate_sub"

val (saturate_mul_tm, mk_saturate_mul, dest_saturate_mul, is_saturate_mul) =
   s "saturate_mul"

val (word_modify_tm, mk_word_modify, dest_word_modify, is_word_modify) =
   s "word_modify"

val (word_reduce_tm, mk_word_reduce, dest_word_reduce, is_word_reduce) =
   s "word_reduce"

val (bit_count_upto_tm, mk_bit_count_upto,
     dest_bit_count_upto, is_bit_count_upto) = s "bit_count_upto"

val (word_sign_extend_tm, mk_word_sign_extend,
     dest_word_sign_extend, is_word_sign_extend) = s "word_sign_extend"

val (word_join_tm, mk_word_join, dest_word_join, is_word_join) = s "word_join"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 2
   (fn tm1 => fn e => fn w =>
      let val (n, l) = HolKernel.dest_binop tm1 e w in (n, l, dim_of w) end)
   (fn tm => fn (n, l, ty) =>
       Term.list_mk_comb (Term.inst [Type.alpha |-> ty] tm, [n, l]))

val (l2w_tm, mk_l2w, dest_l2w, is_l2w) = s "l2w"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 2 HolKernel.dest_binop
   (fn tm => fn (w1, w2) =>
      let
         val d1 = dim_of w1
         val d2 = dim_of w2
         val d3 = fcpLib.index_type
                    (Arbnum.+ (fcpLib.index_to_num d1, fcpLib.index_to_num d2))
                  handle HOL_ERR _ => Type.gamma
      in
         Term.list_mk_comb
            (Term.inst [Type.alpha |-> d1, Type.beta  |-> d2,
                        Type.gamma |-> d3] tm, [w1, w2])
      end)

val (word_concat_tm, mk_word_concat, dest_word_concat, is_word_concat) =
   s "word_concat"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 2 HolKernel.dest_binop
   (fn tm => fn (n, w) =>
      let
         val d1 = dim_of w
         val d2 = fcpLib.index_type
                    (Arbnum.* (fcpLib.index_to_num d1,
                               numSyntax.dest_numeral n))
                  handle HOL_ERR _ => Type.beta
      in
         Term.list_mk_comb
            (Term.inst [Type.alpha |-> d1, Type.beta |-> d2] tm, [n, w])
      end)

val (word_replicate_tm, mk_word_replicate,
     dest_word_replicate, is_word_replicate) = s "word_replicate"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop

val (word_bits_tm, mk_word_bits, dest_word_bits, is_word_bits) = s "word_bits"

val (word_slice_tm, mk_word_slice, dest_word_slice, is_word_slice) =
   s "word_slice"

val (w2s_tm, mk_w2s, dest_w2s, is_w2s) = s "w2s"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 3
   (fn tm1 => fn e => fn w =>
      let
         val (n1, n2, s) = HolKernel.dest_triop tm1 e w
      in
         (n1, n2, w, dim_of w)
      end)
   (fn tm => fn (n1, n2, n3, ty) =>
       Term.list_mk_comb (Term.inst [Type.alpha |-> ty] tm, [n1, n2, n3]))

val (s2w_tm, mk_s2w, dest_s2w, is_s2w) = s "s2w"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 3
   (fn tm1 => fn e => fn w =>
      let
         val (n1, n2, w1) = HolKernel.dest_triop tm1 e w
      in
         (n1, n2, w1, dim_of w)
      end)
   (fn tm => fn (n1, n2, w, ty) =>
       Term.list_mk_comb
          (Term.inst [Type.alpha |-> dim_of w, Type.beta |-> ty] tm,
           [n1, n2, w]))

val (word_extract_tm, mk_word_extract, dest_word_extract, is_word_extract) =
   s "word_extract"

(* - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop

val (bit_field_insert_tm, mk_bit_field_insert,
     dest_bit_field_insert, is_bit_field_insert) = s "bit_field_insert"

(*---------------------------------------------------------------------------*)

fun mk_word   (v, n) = mk_n2w (numSyntax.mk_numeral v, fcpLib.index_type n)
fun mk_wordi  (v, i) = mk_word (v, Arbnum.fromInt i)
fun mk_wordii (v, i) = mk_wordi (Arbnum.fromInt v, i)

val dest_word_literal = numSyntax.dest_numeral o fst o dest_n2w

val is_word_literal = Lib.can dest_word_literal

val uint_of_word = numSyntax.int_of_term o fst o dest_n2w

fun mod_2exp (m, n) =
   if n = Arbnum.zero orelse m = Arbnum.zero
      then Arbnum.zero
   else let
           val v = Arbnum.times2 (mod_2exp (Arbnum.div2 m, Arbnum.less1 n))
        in
           if Arbnum.mod2 m = Arbnum.zero then v else Arbnum.plus1 v
        end

fun dest_mod_word_literal tm =
   let
      val (tm1, ty) = dest_n2w tm
      val sz = fcpLib.index_to_num ty
   in
      (mod_2exp (numSyntax.dest_numeral tm1, sz), sz)
   end handle HOL_ERR _ => raise ERR "dest_mod_word_literal" ""

end
