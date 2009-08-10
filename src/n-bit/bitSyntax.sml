structure bitSyntax :> bitSyntax =
struct

open Abbrev HolKernel bitTheory;

val ERR = mk_HOL_ERR "bitSyntax";

fun monop_systax_fns name thy =
let val tm = prim_mk_const{Name = name, Thy=thy}
    val n = String.map Char.toLower name
    val dest = dest_monop tm (ERR ("dest_"^n) "")
in
  (tm, fn v => mk_comb(tm,v) handle HOL_ERR _ => raise ERR ("mk_"^n) "",
   dest, can dest)
end;

val (lsb_tm,mk_lsb,dest_lsb,is_lsb)         = monop_systax_fns "LSB" "bit";
val (log2_tm,mk_log2,dest_log2,is_log2)     = monop_systax_fns "LOG2" "bit";
val (hex_tm,mk_hex,dest_hex,is_hex)         = monop_systax_fns "HEX" "bit";
val (unhex_tm,mk_unhex,dest_unhex,is_unhex) = monop_systax_fns "UNHEX" "bit";

val (num_from_bin_string_tm,mk_num_from_bin_string,
     dest_num_from_bin_string,is_num_from_bin_string) =
  monop_systax_fns "num_from_bin_string" "bit";

val (num_from_oct_string_tm,mk_num_from_oct_string,
     dest_num_from_oct_string,is_num_from_oct_string) =
  monop_systax_fns "num_from_oct_string" "bit";

val (num_from_dec_string_tm,mk_num_from_dec_string,
     dest_num_from_dec_string,is_num_from_dec_string) =
  monop_systax_fns "num_from_dec_string" "bit";

val (num_from_hex_string_tm,mk_num_from_hex_string,
     dest_num_from_hex_string,is_num_from_hex_string) =
  monop_systax_fns "num_from_hex_string" "bit";

val (num_to_bin_string_tm,mk_num_to_bin_string,
     dest_num_to_bin_string,is_num_to_bin_string) =
  monop_systax_fns "num_to_bin_string" "bit";

val (num_to_oct_string_tm,mk_num_to_oct_string,
     dest_num_to_oct_string,is_num_to_oct_string) =
  monop_systax_fns "num_to_oct_string" "bit";

val (num_to_dec_string_tm,mk_num_to_dec_string,
     dest_num_to_dec_string,is_num_to_dec_string) =
  monop_systax_fns "num_to_dec_string" "bit";

val (num_to_hex_string_tm,mk_num_to_hex_string,
     dest_num_to_hex_string,is_num_to_hex_string) =
  monop_systax_fns "num_to_hex_string" "bit";

val (num_from_bin_list_tm,mk_num_from_bin_list,
     dest_num_from_bin_list,is_num_from_bin_list) =
  monop_systax_fns "num_from_bin_list" "bit";

val (num_from_oct_list_tm,mk_num_from_oct_list,
     dest_num_from_oct_list,is_num_from_oct_list) =
  monop_systax_fns "num_from_oct_list" "bit";

val (num_from_dec_list_tm,mk_num_from_dec_list,
     dest_num_from_dec_list,is_num_from_dec_list) =
  monop_systax_fns "num_from_dec_list" "bit";

val (num_from_hex_list_tm,mk_num_from_hex_list,
     dest_num_from_hex_list,is_num_from_hex_list) =
  monop_systax_fns "num_from_hex_list" "bit";

val (num_to_bin_list_tm,mk_num_to_bin_list,
     dest_num_to_bin_list,is_num_to_bin_list) =
  monop_systax_fns "num_to_bin_list" "bit";

val (num_to_oct_list_tm,mk_num_to_oct_list,
     dest_num_to_oct_list,is_num_to_oct_list) =
  monop_systax_fns "num_to_oct_list" "bit";

val (num_to_dec_list_tm,mk_num_to_dec_list,
     dest_num_to_dec_list,is_num_to_dec_list) =
  monop_systax_fns "num_to_dec_list" "bit";

val (num_to_hex_list_tm,mk_num_to_hex_list,
     dest_num_to_hex_list,is_num_to_hex_list) =
  monop_systax_fns "num_to_hex_list" "bit";

fun binop_systax_fns name thy =
let val tm = prim_mk_const{Name = name, Thy=thy}
    val n = String.map Char.toLower name
    val dest = dest_binop tm (ERR ("dest_"^n) "")
in
  (tm,
   fn (v1,v2) => list_mk_comb(tm,[v1,v2])
     handle HOL_ERR _ => raise ERR ("mk_"^n) "",
   dest, can dest)
end;

val (bit_tm,mk_bit,dest_bit,is_bit)     = binop_systax_fns "BIT" "bit";
val (bitv_tm,mk_bitv,dest_bitv,is_bitv) = binop_systax_fns "BITV" "bit";
val (sbit_tm,mk_sbit,dest_sbit,is_sbit) = binop_systax_fns "SBIT" "bit";
val (l2n_tm,mk_l2n,dest_l2n,is_l2n)     = binop_systax_fns "l2n" "bit";
val (n2l_tm,mk_n2l,dest_n2l,is_n2l)     = binop_systax_fns "n2l" "bit";

val (divmod_2exp_tm,mk_divmod_2exp,dest_divmod_2exp,is_divmod_2exp) =
  binop_systax_fns "DIVMOD_2EXP" "bit";

val (times_2exp_tm,mk_times_2exp,dest_times_2exp,is_times_2exp) =
  binop_systax_fns "TIMES_2EXP" "bit";

val (bit_reverse_tm,mk_bit_reverse, dest_bit_reverse,is_bit_reverse) =
  binop_systax_fns "BIT_REVERSE" "bit";

fun triop_systax_fns name thy =
let val tm = prim_mk_const{Name = name, Thy=thy}
    val n = String.map Char.toLower name
    val dest = dest_triop tm (ERR ("dest_"^n) "")
in
  (tm,
   fn (v1,v2,v3) => list_mk_comb(tm,[v1,v2,v3])
     handle HOL_ERR _ => raise ERR ("mk_"^n) "",
   dest, can dest)
end;

val (mod_2exp_eq_tm,mk_mod_2exp_eq,dest_mod_2exp_eq,is_mod_2exp_eq) =
  triop_systax_fns "MOD_2EXP_EQ" "bit";

val (bits_tm,mk_bits,dest_bits,is_bits)     = triop_systax_fns "BITS" "bit";
val (slice_tm,mk_slice,dest_slice,is_slice) = triop_systax_fns "SLICE" "bit";
val (s2n_tm,mk_s2n,dest_s2n,is_s2n)         = triop_systax_fns "s2n" "bit";
val (n2s_tm,mk_n2s,dest_n2s,is_n2s)         = triop_systax_fns "n2s" "bit";

val (bit_modify_tm,mk_bit_modify,dest_bit_modify,is_bit_modify) =
  triop_systax_fns "BIT_MODIFY" "bit";

val (sign_extend_tm,mk_sign_extend,dest_sign_extend,is_sign_extend) =
  triop_systax_fns "SIGN_EXTEND" "bit";

fun dest_quadop c e tm =
  case with_exn strip_comb tm e of
    (t,[t1,t2,t3,t4]) => if same_const t c then (t1,t2,t3,t4) else raise e
  | _ => raise e;

val bitwise_tm = prim_mk_const{Name = "BITWISE", Thy="bit"};

fun mk_bitwise(n,f,x,y) =
  list_mk_comb(bitwise_tm,[n,f,x,y])
  handle HOL_ERR _ => raise ERR "mk_bitwise" "";

val dest_bitwise = dest_quadop bitwise_tm (ERR "dest_bitwise" "");

val is_bitwise = can dest_bitwise;

end
