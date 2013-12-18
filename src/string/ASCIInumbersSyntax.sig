signature ASCIInumbersSyntax =
sig

  include Abbrev

  val hex_tm : term
  val unhex_tm : term
  val s2n_tm : term
  val n2s_tm : term

  val fromBinString_tm : term
  val fromDecString_tm : term
  val fromHexString_tm : term
  val num_from_bin_string_tm : term
  val num_from_oct_string_tm : term
  val num_from_dec_string_tm : term
  val num_from_hex_string_tm : term
  val num_to_bin_string_tm : term
  val num_to_oct_string_tm : term
  val num_to_dec_string_tm : term
  val num_to_hex_string_tm : term

  val mk_hex : term -> term
  val mk_unhex : term -> term
  val mk_s2n : term * term * term -> term
  val mk_n2s : term * term * term -> term

  val mk_fromBinString : term -> term
  val mk_fromDecString : term -> term
  val mk_fromHexString : term -> term
  val mk_num_from_bin_string : term -> term
  val mk_num_from_oct_string : term -> term
  val mk_num_from_dec_string : term -> term
  val mk_num_from_hex_string : term -> term
  val mk_num_to_bin_string : term -> term
  val mk_num_to_oct_string : term -> term
  val mk_num_to_dec_string : term -> term
  val mk_num_to_hex_string : term -> term

  val dest_hex : term -> term
  val dest_unhex : term -> term
  val dest_s2n : term -> term * term * term
  val dest_n2s : term -> term * term * term

  val dest_fromBinString : term -> term
  val dest_fromDecString : term -> term
  val dest_fromHexString : term -> term
  val dest_num_from_bin_string : term -> term
  val dest_num_from_oct_string : term -> term
  val dest_num_from_dec_string : term -> term
  val dest_num_from_hex_string : term -> term
  val dest_num_to_bin_string : term -> term
  val dest_num_to_oct_string : term -> term
  val dest_num_to_dec_string : term -> term
  val dest_num_to_hex_string : term -> term

  val is_hex : term -> bool
  val is_unhex : term -> bool
  val is_s2n : term -> bool
  val is_n2s : term -> bool

  val is_fromBinString : term -> bool
  val is_fromDecString : term -> bool
  val is_fromHexString : term -> bool
  val is_num_from_bin_string : term -> bool
  val is_num_from_oct_string : term -> bool
  val is_num_from_dec_string : term -> bool
  val is_num_from_hex_string : term -> bool
  val is_num_to_bin_string : term -> bool
  val is_num_to_oct_string : term -> bool
  val is_num_to_dec_string : term -> bool
  val is_num_to_hex_string : term -> bool

end
