signature CooperSyntax = sig

  val not_tm  : Term.term
  val num_ty  : Type.hol_type
  val true_tm : Term.term
  val false_tm : Term.term

  val mk_abs_CONV : Term.term -> Term.term -> Thm.thm
  val cpis_conj : Term.term -> bool
  val cpis_disj : Term.term -> bool

  val cpstrip_conj : Term.term -> Term.term list
  val cpstrip_disj : Term.term -> Term.term list

  val cpEVERY_CONJ_CONV : (Term.term -> Thm.thm) -> (Term.term -> Thm.thm)
  val cpEVERY_DISJ_CONV : (Term.term -> Thm.thm) -> (Term.term -> Thm.thm)

  val has_exists : Term.term -> bool
  val has_forall : Term.term -> bool
  val has_quant : Term.term -> bool

  datatype qstatus = EITHER | NEITHER | qsUNIV | qsEXISTS
  datatype term_op = CONJN | DISJN | NEGN

  val goal_qtype : Term.term -> qstatus
  val bop_characterise : Term.term -> term_op option

  val move_quants_up : Term.term -> Thm.thm
  val flip_forall : Term.term -> Thm.thm
  val flip_foralls : Term.term -> Thm.thm

  val count_vars : Term.term -> (string * int) list

  val move_conj_left : (Term.term -> bool) -> Term.term -> Thm.thm

end