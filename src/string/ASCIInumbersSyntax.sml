structure ASCIInumbersSyntax :> ASCIInumbersSyntax =
struct

open Abbrev HolKernel ASCIInumbersTheory

(*---------------------------------------------------------------------------*)
(* Helper functions                                                          *)
(*---------------------------------------------------------------------------*)

val monop =
   HolKernel.syntax_fns "ASCIInumbers" 1 HolKernel.dest_monop HolKernel.mk_monop

val binop =
   HolKernel.syntax_fns "ASCIInumbers" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "ASCIInumbers" 3 HolKernel.dest_triop HolKernel.mk_triop

val (hex_tm,mk_hex,dest_hex,is_hex)         = monop "HEX"
val (unhex_tm,mk_unhex,dest_unhex,is_unhex) = monop "UNHEX"
val (s2n_tm,mk_s2n,dest_s2n,is_s2n)         = triop "s2n"
val (n2s_tm,mk_n2s,dest_n2s,is_n2s)         = triop "n2s"

val (num_from_bin_string_tm,mk_num_from_bin_string,
     dest_num_from_bin_string,is_num_from_bin_string) =
  monop "num_from_bin_string"

val (num_from_oct_string_tm,mk_num_from_oct_string,
     dest_num_from_oct_string,is_num_from_oct_string) =
  monop "num_from_oct_string"

val (num_from_dec_string_tm,mk_num_from_dec_string,
     dest_num_from_dec_string,is_num_from_dec_string) =
  monop "num_from_dec_string"

val (num_from_hex_string_tm,mk_num_from_hex_string,
     dest_num_from_hex_string,is_num_from_hex_string) =
  monop "num_from_hex_string"

val (num_to_bin_string_tm,mk_num_to_bin_string,
     dest_num_to_bin_string,is_num_to_bin_string) =
  monop "num_to_bin_string"

val (num_to_oct_string_tm,mk_num_to_oct_string,
     dest_num_to_oct_string,is_num_to_oct_string) =
  monop "num_to_oct_string"

val (num_to_dec_string_tm,mk_num_to_dec_string,
     dest_num_to_dec_string,is_num_to_dec_string) =
  monop "num_to_dec_string"

val (num_to_hex_string_tm,mk_num_to_hex_string,
     dest_num_to_hex_string,is_num_to_hex_string) =
  monop "num_to_hex_string"

val (fromBinString_tm, mk_fromBinString, dest_fromBinString, is_fromBinString) =
  monop "fromBinString"

val (fromDecString_tm, mk_fromDecString, dest_fromDecString, is_fromDecString) =
  monop "fromDecString"

val (fromHexString_tm, mk_fromHexString, dest_fromHexString, is_fromHexString) =
  monop "fromHexString"

end
