signature Arith_cons =
sig
  include Abbrev
  type int = Arbint.int

  val num_ty : hol_type
  val mk_plus : term * term -> term
  val mk_minus : term * term -> term
  val mk_mult : term * term -> term
  val dest_plus : term -> term * term
  val dest_minus : term -> term * term
  val dest_mult : term -> term * term
  val is_plus : term -> bool
  val is_minus : term -> bool
  val is_mult : term -> bool
  val mk_less : term * term -> term
  val mk_leq : term * term -> term
  val mk_great : term * term -> term
  val mk_geq : term * term -> term
  val dest_less : term -> term * term
  val dest_leq : term -> term * term
  val dest_great : term -> term * term
  val dest_geq : term -> term * term
  val is_less : term -> bool
  val is_leq : term -> bool
  val is_great : term -> bool
  val is_geq : term -> bool
  val is_num_reln : term -> bool
  val mk_suc : term -> term
  val dest_suc : term -> term
  val is_suc : term -> bool
  val mk_pre : term -> term
  val dest_pre : term -> term
  val is_pre : term -> bool
  val is_num_const : term -> bool
  val is_zero : term -> bool
  val int_of_term : term -> int
  val term_of_int : int -> term
  val mk_num_var : string -> term
  val arg1 : term -> term
  val arg2 : term -> term
end
