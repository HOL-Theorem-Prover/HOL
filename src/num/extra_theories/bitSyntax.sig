signature bitSyntax =
sig

  include Abbrev

  val bit_modify_tm  : term
  val bit_reverse_tm : term
  val bit_tm         : term
  val bits_tm        : term
  val bitv_tm        : term
  val bitwise_tm     : term
  val div_2exp_tm    : term
  val divmod_2exp_tm : term
  val log2_tm        : term
  val mod_2exp_eq_tm : term
  val mod_2exp_tm    : term
  val mod_2exp_max_tm: term
  val sbit_tm        : term
  val sign_extend_tm : term
  val slice_tm       : term
  val times_2exp_tm  : term

  val mk_bit         : term * term -> term
  val mk_bit_modify  : term * term * term -> term
  val mk_bit_reverse : term * term -> term
  val mk_bits        : term * term * term -> term
  val mk_bitv        : term * term -> term
  val mk_bitwise     : term * term * term * term -> term
  val mk_div_2exp    : term * term -> term
  val mk_divmod_2exp : term * term -> term
  val mk_log2        : term -> term
  val mk_mod_2exp    : term * term -> term
  val mk_mod_2exp_eq : term * term * term -> term
  val mk_mod_2exp_max: term * term -> term
  val mk_sbit        : term * term -> term
  val mk_sign_extend : term * term * term -> term
  val mk_slice       : term * term * term -> term
  val mk_times_2exp  : term * term -> term

  val dest_bit         : term -> term * term
  val dest_bit_modify  : term -> term * term * term
  val dest_bit_reverse : term -> term * term
  val dest_bits        : term -> term * term * term
  val dest_bitv        : term -> term * term
  val dest_bitwise     : term -> term * term * term * term
  val dest_div_2exp    : term -> term * term
  val dest_divmod_2exp : term -> term * term
  val dest_log2        : term -> term
  val dest_mod_2exp    : term -> term * term
  val dest_mod_2exp_eq : term -> term * term * term
  val dest_mod_2exp_max: term -> term * term
  val dest_sbit        : term -> term * term
  val dest_sign_extend : term -> term * term * term
  val dest_slice       : term -> term * term * term
  val dest_times_2exp  : term -> term * term

  val is_bit         : term -> bool
  val is_bit_modify  : term -> bool
  val is_bit_reverse : term -> bool
  val is_bits        : term -> bool
  val is_bitv        : term -> bool
  val is_bitwise     : term -> bool
  val is_div_2exp    : term -> bool
  val is_divmod_2exp : term -> bool
  val is_log2        : term -> bool
  val is_mod_2exp    : term -> bool
  val is_mod_2exp_eq : term -> bool
  val is_mod_2exp_max: term -> bool
  val is_sbit        : term -> bool
  val is_sign_extend : term -> bool
  val is_slice       : term -> bool
  val is_times_2exp  : term -> bool

end
