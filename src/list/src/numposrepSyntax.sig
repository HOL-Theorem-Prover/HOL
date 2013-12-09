signature numposrepSyntax =
sig
  include Abbrev

  val boolify_tm : term
  val l2n_tm : term
  val n2l_tm : term
  val num_from_bin_list_tm : term
  val num_from_oct_list_tm : term
  val num_from_dec_list_tm : term
  val num_from_hex_list_tm : term
  val num_to_bin_list_tm : term
  val num_to_oct_list_tm : term
  val num_to_dec_list_tm : term
  val num_to_hex_list_tm : term

  val mk_boolify : term * term * term -> term
  val mk_l2n : term * term -> term
  val mk_n2l : term * term -> term
  val mk_num_from_bin_list : term -> term
  val mk_num_from_oct_list : term -> term
  val mk_num_from_dec_list : term -> term
  val mk_num_from_hex_list : term -> term
  val mk_num_to_bin_list : term -> term
  val mk_num_to_oct_list : term -> term
  val mk_num_to_dec_list : term -> term
  val mk_num_to_hex_list : term -> term

  val dest_boolify : term -> term * term * term
  val dest_l2n : term -> term * term
  val dest_n2l : term -> term * term
  val dest_num_from_bin_list : term -> term
  val dest_num_from_oct_list : term -> term
  val dest_num_from_dec_list : term -> term
  val dest_num_from_hex_list : term -> term
  val dest_num_to_bin_list : term -> term
  val dest_num_to_oct_list : term -> term
  val dest_num_to_dec_list : term -> term
  val dest_num_to_hex_list : term -> term

  val is_boolify : term -> bool
  val is_l2n : term -> bool
  val is_n2l : term -> bool
  val is_num_from_bin_list : term -> bool
  val is_num_from_oct_list : term -> bool
  val is_num_from_dec_list : term -> bool
  val is_num_from_hex_list : term -> bool
  val is_num_to_bin_list : term -> bool
  val is_num_to_oct_list : term -> bool
  val is_num_to_dec_list : term -> bool
  val is_num_to_hex_list : term -> bool

end
