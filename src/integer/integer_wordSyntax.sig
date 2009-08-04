signature integer_wordSyntax = sig

  include Abbrev

  val i2w_tm   : term
  val w2i_tm   : term

  val mk_i2w   : term * hol_type -> term
  val mk_w2i   : term -> term

  val dest_i2w : term -> term
  val dest_w2i : term -> term

  val is_i2w   : term -> bool
  val is_w2i   : term -> bool

end
