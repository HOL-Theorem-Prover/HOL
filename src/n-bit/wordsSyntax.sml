structure wordsSyntax :> wordsSyntax =
struct

open Abbrev HolKernel wordsTheory;

val ERR = mk_HOL_ERR "wordsSyntax";


(*---------------------------------------------------------------------------*)
(* Word types                                                                *)
(*---------------------------------------------------------------------------*)

fun mk_word_type wty = 
  Type.mk_thy_type{Tyop="cart",Thy="fcp",Args=[bool,wty]};

fun dest_word_type ty = 
  case total dest_thy_type ty
   of NONE => raise ERR "dest_word_type" ""
    | SOME {Tyop="cart",Thy="fcp",Args=[b,wty]} =>
        if bool = b then wty 
         else raise ERR "dest_word_type" "not an instance of bool ** 'a"
    | SOME other => raise ERR "dest_word_type" "not an instance of bool ** 'a";

val is_word_type = Lib.can dest_word_type;

fun dim_of tm = dest_word_type(type_of tm);

(*---------------------------------------------------------------------------*)
(* Constants for word operations                                             *)
(*---------------------------------------------------------------------------*)

val fcp_index_tm    = prim_mk_const{Name = "fcp_index", Thy = "fcp"}
val word_T_tm       = prim_mk_const{Name = "word_T", Thy = "words"}
val word_L_tm       = prim_mk_const{Name = "word_L", Thy = "words"}
val word_H_tm       = prim_mk_const{Name = "word_H", Thy = "words"}
val word_L2_tm      = prim_mk_const{Name = "word_L2", Thy = "words"};
val word_modify_tm  = prim_mk_const{Name = "word_modify", Thy = "words"}
val word_reverse_tm = prim_mk_const{Name = "word_reverse", Thy="words"}
val nzcv_tm         = prim_mk_const{Name = "nzcv", Thy = "words"}
val word_lt_tm      = prim_mk_const{Name = "word_lt", Thy="words"}
val word_le_tm      = prim_mk_const{Name = "word_le", Thy="words"}
val word_gt_tm      = prim_mk_const{Name = "word_gt", Thy="words"}
val word_ge_tm      = prim_mk_const{Name = "word_ge", Thy="words"}
val word_add_tm     = prim_mk_const{Name = "word_add", Thy="words"}
val word_sub_tm     = prim_mk_const{Name = "word_sub", Thy="words"}
val word_rrx_tm     = prim_mk_const{Name = "word_rrx", Thy="words"}
val word_mul_tm     = prim_mk_const{Name = "word_mul", Thy="words"}
val word_log2_tm    = prim_mk_const{Name = "word_log2", Thy="words"}
val word_msb_tm     = prim_mk_const{Name = "word_msb", Thy="words"}
val word_lsb_tm     = prim_mk_const{Name = "word_lsb", Thy="words"}
val word_join_tm    = prim_mk_const{Name = "word_join", Thy="words"}
val word_concat_tm  = prim_mk_const{Name = "word_concat", Thy="words"}
val word_slice_tm   = prim_mk_const{Name = "word_slice", Thy="words"}
val word_bit_tm     = prim_mk_const{Name = "word_bit", Thy="words"}
val word_bits_tm    = prim_mk_const{Name = "word_bits", Thy="words"}
val word_extract_tm = prim_mk_const{Name = "word_extract", Thy="words"}
val word_lsl_tm     = prim_mk_const{Name = "word_lsl", Thy="words"}
val word_lsr_tm     = prim_mk_const{Name = "word_lsr", Thy="words"}
val word_asr_tm     = prim_mk_const{Name = "word_asr", Thy="words"}
val word_ror_tm     = prim_mk_const{Name = "word_ror", Thy="words"}
val word_rol_tm     = prim_mk_const{Name = "word_rol", Thy="words"}
val word_hi_tm      = prim_mk_const{Name = "word_hi", Thy="words"}
val word_lo_tm      = prim_mk_const{Name = "word_lo", Thy="words"}
val word_hs_tm      = prim_mk_const{Name = "word_hs", Thy="words"}
val word_ls_tm      = prim_mk_const{Name = "word_ls", Thy="words"}
val word_and_tm     = prim_mk_const{Name = "word_and", Thy="words"}
val word_or_tm      = prim_mk_const{Name = "word_or", Thy="words"}
val word_xor_tm     = prim_mk_const{Name = "word_xor", Thy="words"}
val word_1comp_tm   = prim_mk_const{Name = "word_1comp", Thy = "words"}
val word_2comp_tm   = prim_mk_const{Name = "word_2comp", Thy="words"}
val w2w_tm          = prim_mk_const{Name = "w2w", Thy="words"}
val n2w_tm          = prim_mk_const{Name = "n2w", Thy="words"}
val w2n_tm          = prim_mk_const{Name = "w2n", Thy="words"}
val sw2sw_tm        = prim_mk_const{Name = "sw2sw", Thy="words"};

(*---------------------------------------------------------------------------*)
(* Constructors                                                              *)
(*---------------------------------------------------------------------------*)

fun mk_index(w,n) = 
  list_mk_comb(inst[alpha |-> bool, beta |-> dim_of w] fcp_index_tm,[w,n])
  handle HOL_ERR _ => raise ERR "mk_index" "";

fun mk_word_T ty = 
  inst[alpha |-> ty] word_T_tm
  handle HOL_ERR _ => raise ERR "mk_word_T" "";

fun mk_word_L ty = 
  inst[alpha |-> ty] word_L_tm
  handle HOL_ERR _ => raise ERR "mk_word_L" "";

fun mk_word_H ty = 
  inst[alpha |-> ty] word_H_tm
  handle HOL_ERR _ => raise ERR "mk_word_H" "";

fun mk_word_L2 ty =
  inst[alpha |-> ty] word_L2_tm
  handle HOL_ERR _ => raise ERR "mk_word_L2" "";

fun mk_word_modify(f,w) = 
  list_mk_comb(inst[alpha |-> dim_of w] word_modify_tm,[f,w])
  handle HOL_ERR _ => raise ERR "mk_word_modify" "";

fun mk_word_reverse w = 
  mk_comb(inst[alpha |-> dim_of w] word_reverse_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_reverse" "";

fun mk_nzcv(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]nzcv_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_nzcv" "";

fun mk_word_lt(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_lt_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_lt" "";

fun mk_word_le(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_le_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_le" "";

fun mk_word_gt(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_gt_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_gt" "";

fun mk_word_ge(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_ge_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_ge" "";

fun mk_word_add(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_add_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_add" "";

fun mk_word_sub(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_sub_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_sub" "";

fun mk_word_mul(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1]word_mul_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_mul" "";

fun mk_word_rrx(b,w) = 
  mk_comb(inst[alpha|->dim_of w]word_rrx_tm,pairSyntax.mk_pair(b,w))
  handle HOL_ERR _ => raise ERR "mk_word_rrx" "";

fun mk_word_join(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1, beta|->dim_of w2]word_join_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_join" "";

fun mk_word_concat(w1,w2) = 
  list_mk_comb(inst[alpha|->dim_of w1, beta|->dim_of w2]word_concat_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_concat" "";

fun mk_word_log2 w = 
  mk_comb(inst[alpha|->dim_of w]word_log2_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_log2" "";

fun mk_word_msb w = 
  mk_comb(inst[alpha|->dim_of w]word_msb_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_msb" "";

fun mk_word_lsb w = 
  mk_comb(inst[alpha|->dim_of w]word_lsb_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_lsb" "";

fun mk_word_slice(n1,n2,w) = 
  list_mk_comb(inst[alpha|->dim_of w]word_slice_tm,[n1,n2,w])
  handle HOL_ERR _ => raise ERR "mk_word_slice" "";

fun mk_word_bits(n1,n2,w) = 
  list_mk_comb(inst[alpha|->dim_of w]word_bits_tm,[n1,n2,w])
  handle HOL_ERR _ => raise ERR "mk_word_bits" "";

fun mk_word_bit (n,w) = 
  list_mk_comb(inst[alpha |-> dim_of w]word_bit_tm,[n,w])
  handle HOL_ERR _ => raise ERR "mk_word_bit" "";

fun mk_word_extract(n1,n2,w,ty) = 
  list_mk_comb(inst[alpha |-> dim_of w, beta|->ty]word_extract_tm,[n1,n2,w])
  handle HOL_ERR _ => raise ERR "mk_word_extract" "";

fun mk_word_lsl(w,n) = 
  list_mk_comb(inst[alpha|->dim_of w]word_lsl_tm,[w,n])
  handle HOL_ERR _ => raise ERR "mk_word_lsl" "";

fun mk_word_lsr(w,n) = 
  list_mk_comb(inst[alpha|->dim_of w]word_lsr_tm,[w,n])
  handle HOL_ERR _ => raise ERR "mk_word_lsr" "";

fun mk_word_asr(w,n) = 
  list_mk_comb(inst[alpha|->dim_of w]word_asr_tm,[w,n])
  handle HOL_ERR _ => raise ERR "mk_word_asr" "";

fun mk_word_ror(w,n) = 
  list_mk_comb(inst[alpha|->dim_of w]word_ror_tm,[w,n])
  handle HOL_ERR _ => raise ERR "mk_word_ror" "";

fun mk_word_rol(w,n) = 
  list_mk_comb(inst[alpha|->dim_of w]word_rol_tm,[w,n])
  handle HOL_ERR _ => raise ERR "mk_word_rol" "";

fun mk_word_hi(w1,w2) =
  list_mk_comb(inst[alpha |-> dim_of w1]word_hi_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_hi" "";

fun mk_word_lo(w1,w2) =
  list_mk_comb(inst[alpha |-> dim_of w1]word_lo_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_lo" "";

fun mk_word_hs(w1,w2) =
  list_mk_comb(inst[alpha |-> dim_of w1]word_hs_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_hs" "";

fun mk_word_ls(w1,w2) =
  list_mk_comb(inst[alpha |-> dim_of w1]word_ls_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_ls" "";

fun mk_word_and(w1,w2) =
  list_mk_comb(inst[alpha |-> dim_of w1]word_and_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_and" "";

fun mk_word_or(w1,w2) = 
  list_mk_comb(inst[alpha |-> dim_of w1]word_or_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_or" "";

fun mk_word_xor(w1,w2) = 
  list_mk_comb(inst[alpha |-> dim_of w1]word_xor_tm,[w1,w2])
  handle HOL_ERR _ => raise ERR "mk_word_xor" "";

fun mk_word_1comp w = 
  mk_comb(inst[alpha |-> dim_of w]word_1comp_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_1comp" "";

fun mk_word_2comp w = 
  mk_comb(inst[alpha |-> dim_of w]word_2comp_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_2comp" "";

fun mk_w2w(w,ty) = 
  mk_comb(inst[alpha |-> dim_of w,beta|->ty]w2w_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_w2w" "";

fun mk_n2w(n,ty) = 
  mk_comb(inst[alpha |-> ty]n2w_tm,n)
  handle HOL_ERR _ => raise ERR "mk_word_n2w" "";

fun mk_w2n w = 
  mk_comb(inst[alpha |-> dim_of w]w2n_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_w2n" "";

fun mk_sw2sw(w,ty) = 
  mk_comb(inst[alpha |-> dim_of w,beta|->ty]sw2sw_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_sw2sw" "";

fun mk_word   (v,n) = mk_n2w (numSyntax.mk_numeral v, fcpLib.index_type n);
fun mk_wordi  (v,i) = mk_word (v, Arbnum.fromInt i);
fun mk_wordii (v,i) = mk_wordi (Arbnum.fromInt v, i);

(*---------------------------------------------------------------------------*)
(* Destructors                                                               *)
(*---------------------------------------------------------------------------*)

val dest_index = dest_binop fcp_index_tm (ERR "dest_index" "");

fun dest_word_T tm = 
  if same_const word_T_tm tm 
   then dim_of tm 
    else raise ERR "dest_word_T" "";

fun dest_word_L tm = 
  if same_const word_L_tm tm 
   then dim_of tm 
    else raise ERR "dest_word_L" "";

fun dest_word_H tm = 
  if same_const word_H_tm tm 
   then dim_of tm 
    else raise ERR "dest_word_H" "";

fun dest_word_L2 tm =
  if same_const word_L2_tm tm
   then dim_of tm
    else raise ERR "dest_word_L2" "";

val dest_word_modify = 
  dest_binop word_modify_tm (ERR "dest_word_modify" "");

val dest_word_reverse = 
  dest_monop word_reverse_tm (ERR "dest_word_reverse" "");

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
 let val (n1,n2,w) = dest_triop word_extract_tm (ERR "dest_word_extract" "") tm
 in 
   (n1,n2,w,dim_of tm)
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


(*---------------------------------------------------------------------------*)
(* Discriminators                                                            *)
(*---------------------------------------------------------------------------*)

val is_index = Lib.can dest_index
val is_word_T = Lib.can dest_word_T
val is_word_L = Lib.can dest_word_L
val is_word_H = Lib.can dest_word_H
val is_word_L2 = Lib.can dest_word_L2;
val is_word_modify = Lib.can dest_word_modify
val is_word_reverse = Lib.can dest_word_reverse
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
val is_word_hi =Lib.can dest_word_hi
val is_word_lo =Lib.can dest_word_lo
val is_word_hs =Lib.can dest_word_hs
val is_word_ls =Lib.can dest_word_ls
val is_word_and =Lib.can dest_word_and
val is_word_or = Lib.can dest_word_or
val is_word_xor = Lib.can dest_word_xor
val is_word_1comp = Lib.can dest_word_1comp
val is_word_2comp = Lib.can dest_word_2comp
val is_w2w = Lib.can dest_w2w
val is_n2w = Lib.can dest_n2w
val is_w2n = Lib.can dest_w2n
val is_sw2sw = Lib.can dest_sw2sw

fun is_word_literal t =
  is_n2w t andalso numSyntax.is_numeral (fst (dest_n2w t));

end

