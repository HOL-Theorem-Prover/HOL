signature syntaxLib =
sig

  val dest_ASM : Term.term -> Term.term * Term.term * Term.term
  val dest_IF : Term.term -> Term.term * Term.term * Term.term
  val dest_IMPL_INST : Term.term -> Term.term * Term.term * Term.term
  val dest_Inst : Term.term -> Term.term * Term.term * Term.term
  val dest_Jump : Term.term -> Term.term

end
