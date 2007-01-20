signature basicSizeSyntax = 
sig

  include Abbrev

  val bool_size_tm : term 
  val pair_size_tm : term 
  val sum_size_tm : term 
  val one_size_tm : term 
  val option_size_tm : term 

  val mk_bool_size : term -> term
  val mk_pair_size : term * term * term -> term
  val mk_sum_size : term * term * term -> term
  val mk_one_size : term -> term
  val mk_option_size : term * term -> term

  val dest_bool_size : term -> term
  val dest_pair_size : term -> term * term * term 
  val dest_sum_size : term -> term * term * term 
  val dest_one_size : term -> term
  val dest_option_size : term -> term * term

  val is_bool_size : term -> bool 
  val is_pair_size : term -> bool
  val is_sum_size : term -> bool
  val is_one_size : term -> bool
  val is_option_size : term -> bool

end
