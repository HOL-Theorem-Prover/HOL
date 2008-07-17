signature bitSyntax =
sig

  include Abbrev

  val lsb_tm         : term
  val log2_tm        : term
  val hex_tm         : term
  val unhex_tm       : term
  val bit_tm         : term
  val bitv_tm        : term
  val sbit_tm        : term
  val l2n_tm         : term
  val n2l_tm         : term
  val bit_reverse_tm : term
  val divmod_2exp_tm : term
  val mod_2exp_eq_tm : term
  val times_2exp_tm  : term
  val bits_tm        : term
  val bit_modify_tm  : term
  val slice_tm       : term
  val sign_extend_tm : term
  val s2n_tm         : term
  val n2s_tm         : term
  val bitwise_tm     : term

  val num_from_bin_string_tm : term  
  val num_from_oct_string_tm : term  
  val num_from_dec_string_tm : term  
  val num_from_hex_string_tm : term  
  val num_from_bin_list_tm   : term
  val num_from_oct_list_tm   : term
  val num_from_dec_list_tm   : term
  val num_from_hex_list_tm   : term
  val num_to_bin_string_tm   : term
  val num_to_oct_string_tm   : term
  val num_to_dec_string_tm   : term
  val num_to_hex_string_tm   : term
  val num_to_bin_list_tm     : term
  val num_to_oct_list_tm     : term
  val num_to_dec_list_tm     : term
  val num_to_hex_list_tm     : term

  val mk_lsb         : term -> term
  val mk_log2        : term -> term
  val mk_hex         : term -> term
  val mk_unhex       : term -> term
  val mk_bit         : term * term -> term
  val mk_bitv        : term * term -> term
  val mk_sbit        : term * term -> term
  val mk_l2n         : term * term -> term
  val mk_n2l         : term * term -> term
  val mk_bit_reverse : term * term -> term
  val mk_divmod_2exp : term * term -> term
  val mk_times_2exp  : term * term -> term
  val mk_mod_2exp_eq : term * term * term -> term
  val mk_bits        : term * term * term -> term
  val mk_bit_modify  : term * term * term -> term
  val mk_slice       : term * term * term -> term
  val mk_sign_extend : term * term * term -> term
  val mk_s2n         : term * term * term -> term
  val mk_n2s         : term * term * term -> term
  val mk_bitwise     : term * term * term * term -> term

  val mk_num_from_bin_string : term -> term 
  val mk_num_from_oct_string : term -> term 
  val mk_num_from_dec_string : term -> term 
  val mk_num_from_hex_string : term -> term 
  val mk_num_from_bin_list   : term -> term
  val mk_num_from_oct_list   : term -> term
  val mk_num_from_dec_list   : term -> term
  val mk_num_from_hex_list   : term -> term
  val mk_num_to_bin_string   : term -> term
  val mk_num_to_oct_string   : term -> term
  val mk_num_to_dec_string   : term -> term
  val mk_num_to_hex_string   : term -> term
  val mk_num_to_bin_list     : term -> term
  val mk_num_to_oct_list     : term -> term
  val mk_num_to_dec_list     : term -> term
  val mk_num_to_hex_list     : term -> term

  val dest_lsb         : term -> term
  val dest_log2        : term -> term
  val dest_hex         : term -> term
  val dest_unhex       : term -> term
  val dest_bit         : term -> term * term
  val dest_bitv        : term -> term * term
  val dest_sbit        : term -> term * term
  val dest_l2n         : term -> term * term
  val dest_n2l         : term -> term * term
  val dest_bit_reverse : term -> term * term
  val dest_divmod_2exp : term -> term * term
  val dest_times_2exp  : term -> term * term
  val dest_mod_2exp_eq : term -> term * term * term
  val dest_bits        : term -> term * term * term
  val dest_bit_modify  : term -> term * term * term
  val dest_slice       : term -> term * term * term
  val dest_sign_extend : term -> term * term * term
  val dest_s2n         : term -> term * term * term
  val dest_n2s         : term -> term * term * term
  val dest_bitwise     : term -> term * term * term * term

  val dest_num_from_bin_string : term -> term 
  val dest_num_from_oct_string : term -> term 
  val dest_num_from_dec_string : term -> term 
  val dest_num_from_hex_string : term -> term 
  val dest_num_from_bin_list   : term -> term
  val dest_num_from_oct_list   : term -> term
  val dest_num_from_dec_list   : term -> term
  val dest_num_from_hex_list   : term -> term
  val dest_num_to_bin_string   : term -> term
  val dest_num_to_oct_string   : term -> term
  val dest_num_to_dec_string   : term -> term
  val dest_num_to_hex_string   : term -> term
  val dest_num_to_bin_list     : term -> term
  val dest_num_to_oct_list     : term -> term
  val dest_num_to_dec_list     : term -> term
  val dest_num_to_hex_list     : term -> term

  val is_lsb         : term -> bool
  val is_log2        : term -> bool
  val is_hex         : term -> bool
  val is_unhex       : term -> bool
  val is_bit         : term -> bool
  val is_bitv        : term -> bool
  val is_sbit        : term -> bool
  val is_l2n         : term -> bool
  val is_n2l         : term -> bool
  val is_bit_reverse : term -> bool
  val is_divmod_2exp : term -> bool
  val is_mod_2exp_eq : term -> bool
  val is_times_2exp  : term -> bool
  val is_bits        : term -> bool
  val is_bit_modify  : term -> bool
  val is_slice       : term -> bool
  val is_sign_extend : term -> bool
  val is_s2n         : term -> bool
  val is_n2s         : term -> bool
  val is_bitwise     : term -> bool

  val is_num_from_bin_string : term -> bool 
  val is_num_from_oct_string : term -> bool 
  val is_num_from_dec_string : term -> bool 
  val is_num_from_hex_string : term -> bool 
  val is_num_from_bin_list   : term -> bool
  val is_num_from_oct_list   : term -> bool
  val is_num_from_dec_list   : term -> bool
  val is_num_from_hex_list   : term -> bool
  val is_num_to_bin_string   : term -> bool
  val is_num_to_oct_string   : term -> bool
  val is_num_to_dec_string   : term -> bool
  val is_num_to_hex_string   : term -> bool
  val is_num_to_bin_list     : term -> bool
  val is_num_to_oct_list     : term -> bool
  val is_num_to_dec_list     : term -> bool
  val is_num_to_hex_list     : term -> bool

end
