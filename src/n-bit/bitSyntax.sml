structure bitSyntax :> bitSyntax =
struct

open Abbrev HolKernel bitTheory

(*---------------------------------------------------------------------------*)
(* Helper functions                                                          *)
(*---------------------------------------------------------------------------*)

local
   fun count n ty = count (n + 1) (snd (Type.dom_rng ty)) handle HOL_ERR _ => n
   val count_args = count 0 o Term.type_of
in
   fun syntax_fns thy n dest make =
      fn name =>
         let
            val ERR = mk_HOL_ERR (thy ^ "Syntax")
            val tm = Term.prim_mk_const {Name = name, Thy = thy}
            val () = ignore (count_args tm = n orelse
                             raise ERR "systax_fns" "bad number of arguments")
            val d = dest tm (ERR ("dest_" ^ name) "")
         in
            (tm, fn v => Lib.with_exn make (tm, v) (ERR ("mk_" ^ name) ""),
             d, can d)
         end
   fun dest_quadop c e tm =
      case with_exn strip_comb tm e of
        (t,[t1,t2,t3,t4]) => if same_const t c then (t1,t2,t3,t4) else raise e
      | _ => raise e
end

val monop_syntax_fns = syntax_fns "bit" 1 HolKernel.dest_monop Term.mk_comb
val binop_syntax_fns = syntax_fns "bit" 2 HolKernel.dest_binop
   (fn (tm, (v1, v2)) => Term.list_mk_comb (tm, [v1, v2]))
val triop_syntax_fns = syntax_fns "bit" 3 HolKernel.dest_triop
   (fn (tm, (v1, v2, v3)) => Term.list_mk_comb (tm, [v1, v2, v3]))
val quadop_syntax_fns = syntax_fns "bit" 4 dest_quadop
   (fn (tm, (v1, v2, v3, v4)) => Term.list_mk_comb (tm, [v1, v2, v3, v4]))

val (lsb_tm,mk_lsb,dest_lsb,is_lsb)         = monop_syntax_fns "LSB"
val (log2_tm,mk_log2,dest_log2,is_log2)     = monop_syntax_fns "LOG2"
val (hex_tm,mk_hex,dest_hex,is_hex)         = monop_syntax_fns "HEX"
val (unhex_tm,mk_unhex,dest_unhex,is_unhex) = monop_syntax_fns "UNHEX"

val (num_from_bin_string_tm,mk_num_from_bin_string,
     dest_num_from_bin_string,is_num_from_bin_string) =
  monop_syntax_fns "num_from_bin_string"

val (num_from_oct_string_tm,mk_num_from_oct_string,
     dest_num_from_oct_string,is_num_from_oct_string) =
  monop_syntax_fns "num_from_oct_string"

val (num_from_dec_string_tm,mk_num_from_dec_string,
     dest_num_from_dec_string,is_num_from_dec_string) =
  monop_syntax_fns "num_from_dec_string"

val (num_from_hex_string_tm,mk_num_from_hex_string,
     dest_num_from_hex_string,is_num_from_hex_string) =
  monop_syntax_fns "num_from_hex_string"

val (num_to_bin_string_tm,mk_num_to_bin_string,
     dest_num_to_bin_string,is_num_to_bin_string) =
  monop_syntax_fns "num_to_bin_string"

val (num_to_oct_string_tm,mk_num_to_oct_string,
     dest_num_to_oct_string,is_num_to_oct_string) =
  monop_syntax_fns "num_to_oct_string"

val (num_to_dec_string_tm,mk_num_to_dec_string,
     dest_num_to_dec_string,is_num_to_dec_string) =
  monop_syntax_fns "num_to_dec_string"

val (num_to_hex_string_tm,mk_num_to_hex_string,
     dest_num_to_hex_string,is_num_to_hex_string) =
  monop_syntax_fns "num_to_hex_string"

val (num_from_bin_list_tm,mk_num_from_bin_list,
     dest_num_from_bin_list,is_num_from_bin_list) =
  monop_syntax_fns "num_from_bin_list"

val (num_from_oct_list_tm,mk_num_from_oct_list,
     dest_num_from_oct_list,is_num_from_oct_list) =
  monop_syntax_fns "num_from_oct_list"

val (num_from_dec_list_tm,mk_num_from_dec_list,
     dest_num_from_dec_list,is_num_from_dec_list) =
  monop_syntax_fns "num_from_dec_list"

val (num_from_hex_list_tm,mk_num_from_hex_list,
     dest_num_from_hex_list,is_num_from_hex_list) =
  monop_syntax_fns "num_from_hex_list"

val (num_to_bin_list_tm,mk_num_to_bin_list,
     dest_num_to_bin_list,is_num_to_bin_list) =
  monop_syntax_fns "num_to_bin_list"

val (num_to_oct_list_tm,mk_num_to_oct_list,
     dest_num_to_oct_list,is_num_to_oct_list) =
  monop_syntax_fns "num_to_oct_list"

val (num_to_dec_list_tm,mk_num_to_dec_list,
     dest_num_to_dec_list,is_num_to_dec_list) =
  monop_syntax_fns "num_to_dec_list"

val (num_to_hex_list_tm,mk_num_to_hex_list,
     dest_num_to_hex_list,is_num_to_hex_list) =
  monop_syntax_fns "num_to_hex_list"

val (bit_tm,mk_bit,dest_bit,is_bit)     = binop_syntax_fns "BIT"
val (bitv_tm,mk_bitv,dest_bitv,is_bitv) = binop_syntax_fns "BITV"
val (sbit_tm,mk_sbit,dest_sbit,is_sbit) = binop_syntax_fns "SBIT"
val (l2n_tm,mk_l2n,dest_l2n,is_l2n)     = binop_syntax_fns "l2n"
val (n2l_tm,mk_n2l,dest_n2l,is_n2l)     = binop_syntax_fns "n2l"

val (divmod_2exp_tm,mk_divmod_2exp,dest_divmod_2exp,is_divmod_2exp) =
  binop_syntax_fns "DIVMOD_2EXP"

val (times_2exp_tm,mk_times_2exp,dest_times_2exp,is_times_2exp) =
  binop_syntax_fns "TIMES_2EXP"

val (bit_reverse_tm,mk_bit_reverse, dest_bit_reverse,is_bit_reverse) =
  binop_syntax_fns "BIT_REVERSE"

val (mod_2exp_eq_tm,mk_mod_2exp_eq,dest_mod_2exp_eq,is_mod_2exp_eq) =
  triop_syntax_fns "MOD_2EXP_EQ"

val (bits_tm,mk_bits,dest_bits,is_bits)     = triop_syntax_fns "BITS"
val (slice_tm,mk_slice,dest_slice,is_slice) = triop_syntax_fns "SLICE"
val (s2n_tm,mk_s2n,dest_s2n,is_s2n)         = triop_syntax_fns "s2n"
val (n2s_tm,mk_n2s,dest_n2s,is_n2s)         = triop_syntax_fns "n2s"

val (bit_modify_tm,mk_bit_modify,dest_bit_modify,is_bit_modify) =
  triop_syntax_fns "BIT_MODIFY"

val (sign_extend_tm,mk_sign_extend,dest_sign_extend,is_sign_extend) =
  triop_syntax_fns "SIGN_EXTEND"

val (bitwise_tm, mk_bitwise, dest_bitwise, is_bitwise) =
  quadop_syntax_fns "BITWISE"

end
