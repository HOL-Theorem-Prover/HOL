signature CooperSyntax = sig

  include Abbrev
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
  datatype reltype = rEQ | rDIV | rLT


  val goal_qtype : Term.term -> qstatus
  val bop_characterise : Term.term -> term_op option
  val categorise_leaf : term -> reltype

  val move_quants_up : Term.term -> Thm.thm
  val flip_forall : Term.term -> Thm.thm
  val flip_foralls : Term.term -> Thm.thm

  val count_vars : Term.term -> (string * int) list

  val move_conj_left : (Term.term -> bool) -> Term.term -> Thm.thm

  val mk_constraint : Term.term * Term.term -> Term.term
  val is_constraint : Term.term -> bool
  val is_vconstraint : Term.term -> Term.term -> bool

  val MK_CONSTRAINT : conv
  val UNCONSTRAIN : conv
  val IN_CONSTRAINT : conv -> conv
  val quick_cst_elim : conv

  val reduce_if_ground : conv
  val fixup_newvar : conv

  (* with ?x. p \/ q \/ r...          (with or's right associated)
     expand to (?x. p) \/ (?x.q) \/ (?x.r) ...
  *)
  val push_one_exists_over_many_disjs : conv

  val simple_divides : term -> term -> bool

  (* a "resquan" term is of the form
     low < x /\ x <= high
  *)
  val resquan_remove : conv
  val resquan_onestep : conv

  (* a "vacuous" existential is a term of the form ?x. x = e *)
  val remove_vacuous_existential : conv

  val push_in_exists_and_follow : conv -> conv
  val expand_right_and_over_or : conv

  (* applies the argument conversion to all arguments of relational binary
     operators in a standard Cooper formula
     (operators are =, < or int_divides) *)
  val ADDITIVE_TERMS_CONV : conv -> conv

end