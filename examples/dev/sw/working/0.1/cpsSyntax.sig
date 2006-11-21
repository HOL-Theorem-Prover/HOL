signature cpsSyntax =
sig
 include Abbrev

  val seq_tm : term
  val par_tm : term
  val ite_tm : term
  val rec_tm : term

  val mk_seq : term * term -> term
  val mk_par : term * term -> term
  val mk_ite : term * term * term -> term
  val mk_rec : term * term * term -> term

  val dest_seq : term -> term * term
  val dest_par : term -> term * term
  val dest_ite : term -> term * term * term
  val dest_rec : term -> term * term * term

  val is_seq : term -> bool
  val is_par : term -> bool
  val is_ite : term -> bool
  val is_rec : term -> bool

end