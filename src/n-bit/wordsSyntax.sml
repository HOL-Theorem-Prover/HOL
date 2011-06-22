structure wordsSyntax :> wordsSyntax =
struct

open HolKernel Parse boolLib bossLib;
open wordsTheory fcpSyntax;

val ERR = mk_HOL_ERR "wordsSyntax";


(*---------------------------------------------------------------------------*)
(* Word types                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_word_type wty = fcpSyntax.mk_cart_type (Type.bool, wty);

val mk_int_word_type = mk_word_type o fcpSyntax.mk_int_numeric_type;

fun dest_word_type ty =
let
  val (a, b) = fcpSyntax.dest_cart_type ty
  val _ = a = Type.bool orelse
                raise ERR "dest_word_type" "not an instance of :bool['a]"
in b end

val is_word_type = Lib.can dest_word_type;

val dim_of = dest_word_type o type_of;

(*---------------------------------------------------------------------------*)
(* Constants for word operations                                             *)
(*---------------------------------------------------------------------------*)

fun mk_word_tm s = prim_mk_const{Name = s, Thy = "words"}

val fcp_index_tm        = fcpSyntax.fcp_index_tm
val dimindex_tm         = fcpSyntax.dimindex_tm
val dimword_tm          = mk_word_tm "dimword"
val word_T_tm           = mk_word_tm "word_T"
val word_L_tm           = mk_word_tm "word_L"
val word_H_tm           = mk_word_tm "word_H"
val word_L2_tm          = mk_word_tm "word_L2"
val uint_max_tm         = mk_word_tm "UINT_MAX"
val int_min_tm          = mk_word_tm "INT_MIN"
val int_max_tm          = mk_word_tm "INT_MAX"
val word_modify_tm      = mk_word_tm "word_modify"
val word_reverse_tm     = mk_word_tm "word_reverse"
val word_compare_tm     = mk_word_tm "word_compare"
val nzcv_tm             = mk_word_tm "nzcv"
val word_lt_tm          = mk_word_tm "word_lt"
val word_le_tm          = mk_word_tm "word_le"
val word_gt_tm          = mk_word_tm "word_gt"
val word_ge_tm          = mk_word_tm "word_ge"
val word_add_tm         = mk_word_tm "word_add"
val word_sub_tm         = mk_word_tm "word_sub"
val word_rrx_tm         = mk_word_tm "word_rrx"
val word_mul_tm         = mk_word_tm "word_mul"
val word_log2_tm        = mk_word_tm "word_log2"
val word_msb_tm         = mk_word_tm "word_msb"
val word_lsb_tm         = mk_word_tm "word_lsb"
val word_join_tm        = mk_word_tm "word_join"
val word_concat_tm      = mk_word_tm "word_concat"
val word_div_tm         = mk_word_tm "word_div"
val word_sdiv_tm        = mk_word_tm "word_sdiv"
val word_mod_tm         = mk_word_tm "word_mod"
val word_srem_tm        = mk_word_tm "word_srem"
val word_smod_tm        = mk_word_tm "word_smod"
val word_slice_tm       = mk_word_tm "word_slice"
val word_bit_tm         = mk_word_tm "word_bit"
val word_bits_tm        = mk_word_tm "word_bits"
val word_extract_tm     = mk_word_tm "word_extract"
val word_lsl_tm         = mk_word_tm "word_lsl"
val word_lsr_tm         = mk_word_tm "word_lsr"
val word_asr_tm         = mk_word_tm "word_asr"
val word_ror_tm         = mk_word_tm "word_ror"
val word_rol_tm         = mk_word_tm "word_rol"
val word_lsl_bv_tm      = mk_word_tm "word_lsl_bv"
val word_lsr_bv_tm      = mk_word_tm "word_lsr_bv"
val word_asr_bv_tm      = mk_word_tm "word_asr_bv"
val word_ror_bv_tm      = mk_word_tm "word_ror_bv"
val word_rol_bv_tm      = mk_word_tm "word_rol_bv"
val word_hi_tm          = mk_word_tm "word_hi"
val word_lo_tm          = mk_word_tm "word_lo"
val word_hs_tm          = mk_word_tm "word_hs"
val word_ls_tm          = mk_word_tm "word_ls"
val word_and_tm         = mk_word_tm "word_and"
val word_or_tm          = mk_word_tm "word_or"
val word_xor_tm         = mk_word_tm "word_xor"
val word_nand_tm        = mk_word_tm "word_nand"
val word_nor_tm         = mk_word_tm "word_nor"
val word_xnor_tm        = mk_word_tm "word_xnor"
val word_1comp_tm       = mk_word_tm "word_1comp"
val word_2comp_tm       = mk_word_tm "word_2comp"
val word_replicate_tm   = mk_word_tm "word_replicate"
val concat_word_list_tm = mk_word_tm "concat_word_list"
val bit_field_insert_tm = mk_word_tm "bit_field_insert"
val word_reduce_tm      = mk_word_tm "word_reduce"
val reduce_and_tm       = mk_word_tm "reduce_and"
val reduce_or_tm        = mk_word_tm "reduce_or"
val reduce_xor_tm       = mk_word_tm "reduce_xor"
val reduce_nand_tm      = mk_word_tm "reduce_nand"
val reduce_nor_tm       = mk_word_tm "reduce_nor"
val reduce_xnor_tm      = mk_word_tm "reduce_xnor"
val w2w_tm              = mk_word_tm "w2w"
val n2w_tm              = mk_word_tm "n2w"
val w2n_tm              = mk_word_tm "w2n"
val sw2sw_tm            = mk_word_tm "sw2sw"
val saturate_n2w_tm     = mk_word_tm "saturate_n2w"
val saturate_w2w_tm     = mk_word_tm "saturate_w2w"
val saturate_add_tm     = mk_word_tm "saturate_add"
val saturate_sub_tm     = mk_word_tm "saturate_sub"
val saturate_mul_tm     = mk_word_tm "saturate_mul"

(*---------------------------------------------------------------------------*)
(* Constructors                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_index (w, n) =
  list_mk_comb (inst [alpha |-> bool, beta |-> dim_of w] fcp_index_tm, [w, n])
    handle HOL_ERR _ => raise ERR "mk_index" "";

val mk_dimindex = fcpSyntax.mk_dimindex;

fun mk_dimword ty =
  mk_comb (inst [alpha |-> ty] dimword_tm, boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_dimword" "";

fun mk_word_T ty =
  inst [alpha |-> ty] word_T_tm
  handle HOL_ERR _ => raise ERR "mk_word_T" "";

fun mk_word_L ty =
  inst [alpha |-> ty] word_L_tm
  handle HOL_ERR _ => raise ERR "mk_word_L" "";

fun mk_word_H ty =
  inst [alpha |-> ty] word_H_tm
  handle HOL_ERR _ => raise ERR "mk_word_H" "";

fun mk_word_L2 ty =
  inst [alpha |-> ty] word_L2_tm
  handle HOL_ERR _ => raise ERR "mk_word_L2" "";

fun mk_uint_max ty =
  Term.mk_comb
    (Term.inst [Type.alpha |-> ty] uint_max_tm, boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_uint_max" "";

fun mk_int_min ty =
  Term.mk_comb
    (Term.inst [Type.alpha |-> ty] int_min_tm, boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_int_min" "";

fun mk_int_max ty =
  Term.mk_comb
    (Term.inst [Type.alpha |-> ty] int_max_tm, boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_int_max" "";

fun mk_word_modify (f, w) =
  list_mk_comb (inst [alpha |-> dim_of w] word_modify_tm, [f, w])
  handle HOL_ERR _ => raise ERR "mk_word_modify" "";

fun mk_word_reverse w =
  mk_comb (inst [alpha |-> dim_of w] word_reverse_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_reverse" "";

fun mk_word_compare (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_compare_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_compare" "";

fun mk_nzcv (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] nzcv_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_nzcv" "";

fun mk_word_lt (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_lt_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_lt" "";

fun mk_word_le (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_le_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_le" "";

fun mk_word_gt (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_gt_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_gt" "";

fun mk_word_ge (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_ge_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_ge" "";

fun mk_word_add (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_add_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_add" "";

fun mk_word_sub (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_sub_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_sub" "";

fun mk_word_mul (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_mul_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_mul" "";

fun mk_word_rrx (b, w) =
  mk_comb (inst [alpha |-> dim_of w] word_rrx_tm, pairSyntax.mk_pair (b, w))
  handle HOL_ERR _ => raise ERR "mk_word_rrx" "";

fun mk_word_join (w1, w2) =
  list_mk_comb
    (inst [alpha |-> dim_of w1, beta |-> dim_of w2] word_join_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_join" "";

fun mk_word_concat (w1, w2) =
let
  val wlen = fcpLib.index_to_num o dest_word_type o type_of
  val ty = fcpLib.index_type (Arbnum.+(wlen w1, wlen w2))
              handle HOL_ERR _ => gamma
in
  list_mk_comb
    (inst [alpha |-> dim_of w1,
           beta  |-> dim_of w2,
           gamma |-> ty] word_concat_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_concat" ""
end;

fun mk_word_div (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_div_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_div" "";

fun mk_word_sdiv (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_sdiv_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_sdiv" "";

fun mk_word_mod (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_mod_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_mod" "";

fun mk_word_srem (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_srem_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_srem" "";

fun mk_word_smod (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_smod_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_smod" "";

fun mk_word_log2 w =
  mk_comb (inst [alpha |-> dim_of w] word_log2_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_log2" "";

fun mk_word_msb w =
  mk_comb (inst [alpha |-> dim_of w] word_msb_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_msb" "";

fun mk_word_lsb w =
  mk_comb (inst [alpha |-> dim_of w] word_lsb_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_lsb" "";

fun mk_word_slice (n1, n2, w) =
  list_mk_comb (inst [alpha |-> dim_of w] word_slice_tm, [n1, n2, w])
  handle HOL_ERR _ => raise ERR "mk_word_slice" "";

fun mk_word_bits (n1, n2, w) =
  list_mk_comb (inst [alpha |-> dim_of w] word_bits_tm, [n1, n2, w])
  handle HOL_ERR _ => raise ERR "mk_word_bits" "";

fun mk_word_bit (n, w) =
  list_mk_comb (inst [alpha |-> dim_of w] word_bit_tm, [n, w])
  handle HOL_ERR _ => raise ERR "mk_word_bit" "";

fun mk_word_extract (n1, n2, w, ty) =
  list_mk_comb
    (inst [alpha |-> dim_of w, beta |-> ty] word_extract_tm, [n1, n2, w])
  handle HOL_ERR _ => raise ERR "mk_word_extract" "";

fun mk_word_lsl (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_lsl_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_lsl" "";

fun mk_word_lsr (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_lsr_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_lsr" "";

fun mk_word_asr (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_asr_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_asr" "";

fun mk_word_ror (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_ror_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_ror" "";

fun mk_word_rol (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_rol_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_rol" "";

fun mk_word_lsl_bv (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_lsl_bv_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_lsl_bv" "";

fun mk_word_lsr_bv (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_lsr_bv_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_lsr_bv" "";

fun mk_word_asr_bv (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_asr_bv_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_asr_bv" "";

fun mk_word_ror_bv (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_ror_bv_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_ror_bv" "";

fun mk_word_rol_bv (w, n) =
  list_mk_comb (inst [alpha |-> dim_of w] word_rol_bv_tm, [w, n])
  handle HOL_ERR _ => raise ERR "mk_word_rol_bv" "";

fun mk_word_hi (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_hi_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_hi" "";

fun mk_word_lo (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_lo_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_lo" "";

fun mk_word_hs (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_hs_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_hs" "";

fun mk_word_ls (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_ls_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_ls" "";

fun mk_word_and (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_and_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_and" "";

fun mk_word_or (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_or_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_or" "";

fun mk_word_xor (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_xor_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_xor" "";

fun mk_word_nand (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_nand_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_nand" "";

fun mk_word_nor (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_nor_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_nor" "";

fun mk_word_xnor (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] word_xnor_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_word_xnor" "";

fun mk_word_1comp w =
  mk_comb (inst [alpha |-> dim_of w] word_1comp_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_1comp" "";

fun mk_word_2comp w =
  mk_comb (inst [alpha |-> dim_of w] word_2comp_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_2comp" "";

fun mk_w2w (w, ty) =
  mk_comb (inst [alpha |-> dim_of w, beta |-> ty] w2w_tm, w)
  handle HOL_ERR _ => raise ERR "mk_w2w" "";

fun mk_n2w (n, ty) =
  mk_comb (inst [alpha |-> ty] n2w_tm, n)
  handle HOL_ERR _ => raise ERR "mk_n2w" "";

fun mk_w2n w =
  mk_comb (inst [alpha |-> dim_of w] w2n_tm, w)
  handle HOL_ERR _ => raise ERR "mk_w2n" "";

fun mk_sw2sw (w, ty) =
  mk_comb (inst [alpha |-> dim_of w, beta |-> ty] sw2sw_tm, w)
  handle HOL_ERR _ => raise ERR "mk_sw2sw" "";

fun mk_saturate_n2w (n, ty) =
  mk_comb (inst [alpha |-> ty] saturate_n2w_tm, n)
  handle HOL_ERR _ => raise ERR "mk_saturate_n2w" "";

fun mk_saturate_w2w (w, ty) =
  mk_comb (inst [alpha |-> dim_of w, beta |-> ty] saturate_w2w_tm, w)
  handle HOL_ERR _ => raise ERR "mk_saturate_w2w" "";

fun mk_saturate_add (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] saturate_add_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_saturate_add" "";

fun mk_saturate_sub (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] saturate_sub_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_saturate_sub" "";

fun mk_saturate_mul (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] saturate_mul_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_saturate_mul" "";

fun mk_word   (v, n) = mk_n2w (numSyntax.mk_numeral v, fcpLib.index_type n);
fun mk_wordi  (v, i) = mk_word (v, Arbnum.fromInt i);
fun mk_wordii (v, i) = mk_wordi (Arbnum.fromInt v, i);

fun mk_word_reduce (f, w) =
  list_mk_comb (inst [alpha |-> dim_of w] word_reduce_tm, [f, w])
  handle HOL_ERR _ => raise ERR "mk_word_reduce" "";

fun mk_reduce_and w =
  mk_comb (inst [alpha |-> dim_of w] reduce_and_tm, w)
  handle HOL_ERR _ => raise ERR "mk_reduce_and" "";

fun mk_reduce_or w =
  mk_comb (inst [alpha |-> dim_of w] reduce_or_tm, w)
  handle HOL_ERR _ => raise ERR "mk_reduce_or" "";

fun mk_reduce_xor w =
  mk_comb (inst [alpha |-> dim_of w] reduce_xor_tm, w)
  handle HOL_ERR _ => raise ERR "mk_reduce_xor" "";

fun mk_reduce_nand w =
  mk_comb (inst [alpha |-> dim_of w] reduce_nand_tm, w)
  handle HOL_ERR _ => raise ERR "mk_reduce_nand" "";

fun mk_reduce_nor w =
  mk_comb (inst [alpha |-> dim_of w] reduce_nor_tm, w)
  handle HOL_ERR _ => raise ERR "mk_reduce_nor" "";

fun mk_reduce_xnor w =
  mk_comb (inst [alpha |-> dim_of w] reduce_xnor_tm, w)
  handle HOL_ERR _ => raise ERR "mk_reduce_xnor" "";

fun mk_word_replicate (n, w) =
let
  val wlen = fcpLib.index_to_num o dest_word_type o type_of
  val ty = fcpLib.index_type (Arbnum.* (numSyntax.dest_numeral n, wlen w))
           handle HOL_ERR _ => beta
in
  list_mk_comb
    (inst [alpha |-> dim_of w, beta |-> ty] word_replicate_tm, [n, w])
  handle HOL_ERR _ => raise ERR "mk_word_replicate" ""
end;

fun mk_concat_word_list l =
  mk_comb (inst [alpha |-> (l |> type_of
                              |> listSyntax.dest_list_type
                              |> dest_word_type)] concat_word_list_tm, l)
  handle HOL_ERR _ => raise ERR "mk_concat_word_list" "";

fun mk_bit_field_insert (h, l, w1, w2) =
  list_mk_comb
   (inst [alpha |-> dim_of w2, beta |-> dim_of w1] bit_field_insert_tm,
    [h, l, w1, w2])
  handle HOL_ERR _ => raise ERR "mk_bit_field_insert" "";

(*---------------------------------------------------------------------------*)
(* Destructors                                                               *)
(*---------------------------------------------------------------------------*)

val dest_index    = fcpSyntax.dest_fcp_index;
val dest_dimindex = fcpSyntax.dest_dimindex;

fun dest_dimword tm =
  HolKernel.dest_monop dimword_tm (ERR "dest_dimword" "") tm
    |> boolSyntax.dest_itself;

fun dest_word_T tm =
  if same_const word_T_tm tm then dim_of tm else raise ERR "dest_word_T" "";

fun dest_word_L tm =
  if same_const word_L_tm tm then dim_of tm else raise ERR "dest_word_L" "";

fun dest_word_H tm =
  if same_const word_H_tm tm then dim_of tm else raise ERR "dest_word_H" "";

fun dest_word_L2 tm =
  if same_const word_L2_tm tm then dim_of tm else raise ERR "dest_word_L2" "";

val dest_uint_max =
  boolSyntax.dest_itself o
  HolKernel.dest_monop uint_max_tm (ERR "dest_uint_max" "");

val dest_int_min =
  boolSyntax.dest_itself o
  HolKernel.dest_monop int_min_tm (ERR "dest_int_min" "");

val dest_int_max =
  boolSyntax.dest_itself o
  HolKernel.dest_monop int_max_tm (ERR "dest_int_max" "");

val dest_word_modify =
  dest_binop word_modify_tm (ERR "dest_word_modify" "");

val dest_word_reverse =
  dest_monop word_reverse_tm (ERR "dest_word_reverse" "");

val dest_word_compare =
  dest_binop word_compare_tm (ERR "dest_word_compare" "");

val dest_nzcv = dest_binop nzcv_tm (ERR "dest_nzcv" "");

val dest_word_lt =
  dest_binop word_lt_tm (ERR "dest_word_lt" "");

val dest_word_le =
  dest_binop word_le_tm (ERR "dest_word_le" "");

val dest_word_gt =
  dest_binop word_gt_tm (ERR "dest_word_gt" "");

val dest_word_ge =
  dest_binop word_ge_tm (ERR "dest_word_ge" "");

val dest_word_add =
  dest_binop word_add_tm (ERR "dest_word_add" "");

val dest_word_sub =
  dest_binop word_sub_tm (ERR "dest_word_sub" "");

val dest_word_mul =
  dest_binop word_mul_tm (ERR "dest_word_mul" "");

val dest_word_rrx =
  dest_monop word_rrx_tm (ERR "dest_word_rrx" "");

val dest_word_join =
  dest_binop word_join_tm (ERR "dest_word_join" "");

val dest_word_concat =
  dest_binop word_concat_tm (ERR "dest_word_concat" "");

val dest_word_div =
  dest_binop word_div_tm (ERR "dest_word_div" "");

val dest_word_sdiv =
  dest_binop word_sdiv_tm (ERR "dest_word_sdiv" "");

val dest_word_mod =
  dest_binop word_mod_tm (ERR "dest_word_mod" "");

val dest_word_srem =
  dest_binop word_srem_tm (ERR "dest_word_srem" "");

val dest_word_smod =
  dest_binop word_smod_tm (ERR "dest_word_smod" "");

val dest_word_log2 =
  dest_monop word_log2_tm (ERR "dest_word_log2" "");

val dest_word_msb =
  dest_monop word_msb_tm (ERR "dest_word_msb" "");

val dest_word_lsb =
  dest_monop word_lsb_tm (ERR "dest_word_lsb" "");

val dest_word_slice =
  dest_triop word_slice_tm (ERR "dest_word_slice" "");

val dest_word_bits =
  dest_triop word_bits_tm (ERR "dest_word_bits" "");

val dest_word_bit =
  dest_binop word_bit_tm (ERR "dest_word_bit" "");

fun dest_word_extract tm =
  let
    val (n1,n2,w) = dest_triop word_extract_tm (ERR "dest_word_extract" "") tm
  in
    (n1, n2, w, dim_of tm)
  end

val dest_word_lsl =
  dest_binop word_lsl_tm (ERR "dest_word_lsl" "");

val dest_word_lsr =
  dest_binop word_lsr_tm (ERR "dest_word_lsr" "");

val dest_word_asr =
  dest_binop word_asr_tm (ERR "dest_word_asr" "");

val dest_word_ror =
  dest_binop word_ror_tm (ERR "dest_word_ror" "");

val dest_word_rol =
  dest_binop word_rol_tm (ERR "dest_word_rol" "");

val dest_word_lsl_bv =
  dest_binop word_lsl_bv_tm (ERR "dest_word_lsl_bv" "");

val dest_word_lsr_bv =
  dest_binop word_lsr_bv_tm (ERR "dest_word_lsr_bv" "");

val dest_word_asr_bv =
  dest_binop word_asr_bv_tm (ERR "dest_word_asr_bv" "");

val dest_word_ror_bv =
  dest_binop word_ror_bv_tm (ERR "dest_word_ror_bv" "");

val dest_word_rol_bv =
  dest_binop word_rol_bv_tm (ERR "dest_word_rol_bv" "");

val dest_word_hi =
  dest_binop word_hi_tm (ERR "dest_word_hi" "");

val dest_word_lo =
  dest_binop word_lo_tm (ERR "dest_word_lo" "");

val dest_word_hs =
  dest_binop word_hs_tm (ERR "dest_word_hs" "");

val dest_word_ls =
  dest_binop word_ls_tm (ERR "dest_word_ls" "");

val dest_word_and =
  dest_binop word_and_tm (ERR "dest_word_and" "");

val dest_word_xor =
  dest_binop word_xor_tm (ERR "dest_word_xor" "");

val dest_word_or =
  dest_binop word_or_tm (ERR "dest_word_or" "");

val dest_word_nand =
  dest_binop word_nand_tm (ERR "dest_word_nand" "");

val dest_word_xnor =
  dest_binop word_xnor_tm (ERR "dest_word_xnor" "");

val dest_word_nor =
  dest_binop word_nor_tm (ERR "dest_word_nor" "");

val dest_word_1comp =
  dest_monop word_1comp_tm (ERR "dest_word_1comp" "");

val dest_word_2comp =
  dest_monop word_2comp_tm (ERR "dest_word_2comp" "");

fun dest_w2w M =
  (dest_monop w2w_tm (ERR "dest_w2w" "") M, dim_of M);

fun dest_n2w M =
  (dest_monop n2w_tm (ERR "dest_n2w" "") M, dim_of M);

fun dest_sw2sw M =
  (dest_monop sw2sw_tm (ERR "dest_sw2sw" "") M, dim_of M);

val dest_w2n =
  dest_monop w2n_tm (ERR "dest_w2n" "");

fun dest_saturate_n2w M =
  (dest_monop saturate_n2w_tm (ERR "dest_saturate_n2w" "") M, dim_of M);

fun dest_saturate_w2w M =
  (dest_monop saturate_w2w_tm (ERR "dest_saturate_w2w" "") M, dim_of M);

val dest_saturate_add =
  dest_binop saturate_add_tm (ERR "dest_saturate_add" "");

val dest_saturate_sub =
  dest_binop saturate_sub_tm (ERR "dest_saturate_sub" "");

val dest_saturate_mul =
  dest_binop saturate_mul_tm (ERR "dest_saturate_mul" "");

val dest_word_reduce =
  dest_binop word_reduce_tm (ERR "dest_word_reduce" "");

val dest_reduce_and =
  dest_monop reduce_and_tm (ERR "dest_reduce_and" "");

val dest_reduce_or =
  dest_monop reduce_or_tm (ERR "dest_reduce_or" "");

val dest_reduce_xor =
  dest_monop reduce_xor_tm (ERR "dest_reduce_xor" "");

val dest_reduce_nand =
  dest_monop reduce_nand_tm (ERR "dest_reduce_nand" "");

val dest_reduce_nor =
  dest_monop reduce_nor_tm (ERR "dest_reduce_nor" "");

val dest_reduce_xnor =
  dest_monop reduce_xnor_tm (ERR "dest_reduce_xnor" "");

val dest_word_replicate =
  dest_binop word_replicate_tm (ERR "dest_word_replicate" "");

val dest_concat_word_list =
  dest_monop concat_word_list_tm (ERR "dest_concat_word_list" "");

fun dest_op4 c e tm =
  case with_exn strip_comb tm e of
    (t,[t1,t2,t3,t4]) => if same_const t c then (t1,t2,t3,t4) else raise e
  | _ => raise e;

val dest_bit_field_insert =
  dest_op4 bit_field_insert_tm (ERR "dest_bit_field_insert" "");

(*---------------------------------------------------------------------------*)
(* Discriminators                                                            *)
(*---------------------------------------------------------------------------*)

val is_index = Lib.can dest_index
val is_dimindex = Lib.can dest_dimindex
val is_dimword = Lib.can dest_dimword
val is_word_T = Lib.can dest_word_T
val is_word_L = Lib.can dest_word_L
val is_word_H = Lib.can dest_word_H
val is_word_L2 = Lib.can dest_word_L2;
val is_uint_max = Lib.can dest_uint_max
val is_int_min = Lib.can dest_int_min
val is_int_max = Lib.can dest_int_max
val is_word_modify = Lib.can dest_word_modify
val is_word_reverse = Lib.can dest_word_reverse
val is_word_compare = Lib.can dest_word_compare
val is_nzcv = Lib.can dest_nzcv
val is_word_lt = Lib.can dest_word_lt
val is_word_le = Lib.can dest_word_le
val is_word_gt = Lib.can dest_word_gt
val is_word_ge = Lib.can dest_word_ge
val is_word_add = Lib.can dest_word_add
val is_word_sub = Lib.can dest_word_sub
val is_word_mul = Lib.can dest_word_mul
val is_word_rrx = Lib.can dest_word_rrx
val is_word_concat = Lib.can dest_word_concat
val is_word_div = Lib.can dest_word_div
val is_word_sdiv = Lib.can dest_word_sdiv
val is_word_mod = Lib.can dest_word_mod
val is_word_srem = Lib.can dest_word_srem
val is_word_smod = Lib.can dest_word_smod
val is_word_log2 = Lib.can dest_word_log2
val is_word_msb = Lib.can dest_word_msb
val is_word_lsb = Lib.can dest_word_lsb
val is_word_slice = Lib.can dest_word_slice
val is_word_bits = Lib.can dest_word_bits
val is_word_bit = Lib.can dest_word_bit
val is_word_extract = Lib.can dest_word_extract
val is_word_lsl = Lib.can dest_word_lsl
val is_word_lsr = Lib.can dest_word_lsr
val is_word_asr = Lib.can dest_word_asr
val is_word_ror = Lib.can dest_word_ror
val is_word_rol = Lib.can dest_word_rol
val is_word_lsl_bv = Lib.can dest_word_lsl_bv
val is_word_lsr_bv = Lib.can dest_word_lsr_bv
val is_word_asr_bv = Lib.can dest_word_asr_bv
val is_word_ror_bv = Lib.can dest_word_ror_bv
val is_word_rol_bv = Lib.can dest_word_rol_bv
val is_word_hi = Lib.can dest_word_hi
val is_word_lo = Lib.can dest_word_lo
val is_word_hs = Lib.can dest_word_hs
val is_word_ls = Lib.can dest_word_ls
val is_word_and = Lib.can dest_word_and
val is_word_or = Lib.can dest_word_or
val is_word_xor = Lib.can dest_word_xor
val is_word_nand = Lib.can dest_word_nand
val is_word_nor = Lib.can dest_word_nor
val is_word_xnor = Lib.can dest_word_xnor
val is_word_1comp = Lib.can dest_word_1comp
val is_word_2comp = Lib.can dest_word_2comp
val is_word_reduce = Lib.can dest_word_reduce
val is_reduce_and = Lib.can dest_reduce_and
val is_reduce_or = Lib.can dest_reduce_or
val is_reduce_xor = Lib.can dest_reduce_xor
val is_reduce_nand = Lib.can dest_reduce_nand
val is_reduce_nor = Lib.can dest_reduce_nor
val is_reduce_xnor = Lib.can dest_reduce_xnor
val is_word_replicate = Lib.can dest_word_replicate
val is_concat_word_list = Lib.can dest_concat_word_list
val is_bit_field_insert = Lib.can dest_bit_field_insert
val is_w2w = Lib.can dest_w2w
val is_n2w = Lib.can dest_n2w
val is_w2n = Lib.can dest_w2n
val is_sw2sw = Lib.can dest_sw2sw
val is_saturate_n2w = Lib.can dest_saturate_n2w
val is_saturate_w2w = Lib.can dest_saturate_w2w
val is_saturate_add = Lib.can dest_saturate_add
val is_saturate_sub = Lib.can dest_saturate_sub
val is_saturate_mul = Lib.can dest_saturate_mul

val dest_word_literal = numSyntax.dest_numeral o fst o dest_n2w

val is_word_literal = Lib.can dest_word_literal

val uint_of_word = numSyntax.int_of_term o fst o dest_n2w

fun mod_2exp (m, n) =
  if n = Arbnum.zero orelse m = Arbnum.zero then Arbnum.zero else
    let val v = Arbnum.times2 (mod_2exp (Arbnum.div2 m, Arbnum.less1 n)) in
      if Arbnum.mod2 m = Arbnum.zero then v else Arbnum.plus1 v
    end

fun dest_mod_word_literal tm = let
  val (tm1, ty) = dest_n2w tm
  val sz = fcpLib.index_to_num ty
in
  (mod_2exp (numSyntax.dest_numeral tm1, sz), sz)
end handle HOL_ERR _ => raise ERR "dest_mod_word_literal" ""

end
