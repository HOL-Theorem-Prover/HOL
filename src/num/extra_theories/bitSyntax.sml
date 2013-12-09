structure bitSyntax :> bitSyntax =
struct

open Abbrev HolKernel bitTheory

val monop =
   HolKernel.syntax_fns "bit" 1 HolKernel.dest_monop (Lib.curry Term.mk_comb)

val binop =
   HolKernel.syntax_fns "bit" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "bit" 3 HolKernel.dest_triop HolKernel.mk_triop

val quadop =
   HolKernel.syntax_fns "bit" 4 HolKernel.dest_quadop HolKernel.mk_quadop

val (log2_tm,mk_log2,dest_log2,is_log2) = monop "LOG2"
val (bit_tm,mk_bit,dest_bit,is_bit)     = binop "BIT"
val (bitv_tm,mk_bitv,dest_bitv,is_bitv) = binop "BITV"
val (sbit_tm,mk_sbit,dest_sbit,is_sbit) = binop "SBIT"

val (divmod_2exp_tm,mk_divmod_2exp,dest_divmod_2exp,is_divmod_2exp) =
   binop "DIVMOD_2EXP"

val (times_2exp_tm,mk_times_2exp,dest_times_2exp,is_times_2exp) =
   binop "TIMES_2EXP"

val (div_2exp_tm,mk_div_2exp,dest_div_2exp,is_div_2exp) =
   binop "DIV_2EXP"

val (mod_2exp_tm,mk_mod_2exp,dest_mod_2exp,is_mod_2exp) =
   binop "MOD_2EXP"

val (bit_reverse_tm,mk_bit_reverse, dest_bit_reverse,is_bit_reverse) =
   binop "BIT_REVERSE"

val (mod_2exp_max_tm,mk_mod_2exp_max,dest_mod_2exp_max,is_mod_2exp_max) =
   binop "MOD_2EXP_MAX"

val (mod_2exp_eq_tm,mk_mod_2exp_eq,dest_mod_2exp_eq,is_mod_2exp_eq) =
   triop "MOD_2EXP_EQ"

val (bits_tm,mk_bits,dest_bits,is_bits)     = triop "BITS"
val (slice_tm,mk_slice,dest_slice,is_slice) = triop "SLICE"

val (bit_modify_tm,mk_bit_modify,dest_bit_modify,is_bit_modify) =
   triop "BIT_MODIFY"

val (sign_extend_tm,mk_sign_extend,dest_sign_extend,is_sign_extend) =
   triop "SIGN_EXTEND"

val (bitwise_tm, mk_bitwise, dest_bitwise, is_bitwise) = quadop "BITWISE"

end
