signature CooperMath = sig

  type num = Arbnum.num
  type term = Term.term
  type thm = Thm.thm

  val cooper_compset : computeLib.compset
  val REDUCE_CONV    : term -> thm

  val extended_gcd   : num * num -> num * (Arbint.int * Arbint.int)
  val sum_var_coeffs : term -> term -> Arbint.int

  datatype dir = Left | Right
  datatype termtype = EQ | LT

  val dir_of_pair    : dir -> ('a * 'a) -> 'a
  val term_at        : dir -> term -> term
  val conv_at        : dir -> (term -> thm) -> (term -> thm)

  val move_terms_from: termtype -> dir -> (term -> bool) -> (term -> thm)
  val collect_terms  : term -> thm
  val collect_in_sum : term -> term -> thm

  val elim_sdivides  : term -> thm
  val simplify_constraints : term -> thm
  val factor_out : Arbint.int -> term -> term -> thm

end