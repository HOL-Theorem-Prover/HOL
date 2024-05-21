signature ringSyntax =
sig

  include Abbrev

  val ring_add_tm      : term
  val ring_sub_tm      : term
  val ring_mul_tm      : term
  val ring_pow_tm      : term
  val ring_neg_tm      : term
  val ring_of_num_tm   : term
  val ring_of_int_tm   : term
  val ring_carrier_tm  : term
  val ring_monomorphism_tm : term

  val is_ring_0        : term -> bool
  val is_ring_1        : term -> bool
  val is_ring_of_num   : term -> bool
  val is_ring_of_int   : term -> bool
  val is_ring_neg      : term -> bool
  val is_ring_pow      : term -> bool
  val is_ring_add      : term -> bool
  val is_ring_sub      : term -> bool
  val is_ring_mul      : term -> bool
  val is_ringconst     : term -> bool

  val dest_ring_of_num : term -> term * term
  val dest_ring_of_int : term -> term * term
  val dest_ring_neg    : term -> term * term
  val dest_ring_pow    : term -> term * term * term
  val dest_ring_add    : term -> term * term * term
  val dest_ring_sub    : term -> term * term * term
  val dest_ring_mul    : term -> term * term * term

end
