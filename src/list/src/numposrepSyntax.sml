structure numposrepSyntax :> numposrepSyntax =
struct

open Abbrev HolKernel numposrepTheory

val monop =
   HolKernel.syntax_fns "numposrep" 1 HolKernel.dest_monop HolKernel.mk_monop

val binop =
   HolKernel.syntax_fns "numposrep" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "numposrep" 3 HolKernel.dest_triop HolKernel.mk_triop

val (num_from_bin_list_tm,mk_num_from_bin_list,
     dest_num_from_bin_list,is_num_from_bin_list) = monop "num_from_bin_list"

val (num_from_oct_list_tm,mk_num_from_oct_list,
     dest_num_from_oct_list,is_num_from_oct_list) = monop "num_from_oct_list"

val (num_from_dec_list_tm,mk_num_from_dec_list,
     dest_num_from_dec_list,is_num_from_dec_list) = monop "num_from_dec_list"

val (num_from_hex_list_tm,mk_num_from_hex_list,
     dest_num_from_hex_list,is_num_from_hex_list) = monop "num_from_hex_list"

val (num_to_bin_list_tm,mk_num_to_bin_list,
     dest_num_to_bin_list,is_num_to_bin_list) = monop "num_to_bin_list"

val (num_to_oct_list_tm,mk_num_to_oct_list,
     dest_num_to_oct_list,is_num_to_oct_list) = monop "num_to_oct_list"

val (num_to_dec_list_tm,mk_num_to_dec_list,
     dest_num_to_dec_list,is_num_to_dec_list) = monop "num_to_dec_list"

val (num_to_hex_list_tm,mk_num_to_hex_list,
     dest_num_to_hex_list,is_num_to_hex_list) = monop "num_to_hex_list"

val (l2n_tm,mk_l2n,dest_l2n,is_l2n) = binop "l2n"
val (n2l_tm,mk_n2l,dest_n2l,is_n2l) = binop "n2l"
val (boolify_tm,mk_boolify,dest_boolify,is_boolify) = triop "BOOLIFY"

end
