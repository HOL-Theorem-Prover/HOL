signature CooperSyntax = sig

  include Abbrev
  val not_tm  : term
  val num_ty  : hol_type
  val true_tm : term
  val false_tm : term

  (* these are both basically the same function; given argument t0 they turn
       t
     into
       (\v. t[v/t0]) t0
     mk_abs_CONV only works if t0 is a var, and is more efficient because
     it doesn't need to do a substitution (the "v" above can just be t0) *)
  val mk_abs_CONV : term -> conv
  val UNBETA_CONV : term -> conv


  val cpis_conj : term -> bool
  val cpis_disj : term -> bool

  val cpstrip_conj : term -> term list
  val cpstrip_disj : term -> term list

  val cpEVERY_CONJ_CONV : (term -> Thm.thm) -> (term -> Thm.thm)
  val cpEVERY_DISJ_CONV : (term -> Thm.thm) -> (term -> Thm.thm)

  val has_exists : term -> bool
  val has_forall : term -> bool
  val has_quant : term -> bool

  (* finds sub-terms satisfying given predicate that do not have any of their
     free variables bound by binders higher in the same term *)
  val find_free_terms : (term -> bool) -> term -> term HOLset.set

  datatype qstatus = EITHER | NEITHER | qsUNIV | qsEXISTS
  datatype term_op = CONJN | DISJN | NEGN
  datatype reltype = rEQ | rDIV | rLT


  val goal_qtype : term -> qstatus
  val bop_characterise : term -> term_op option
  val categorise_leaf : term -> reltype

  val move_quants_up : term -> Thm.thm
  val flip_forall : term -> Thm.thm
  val flip_foralls : term -> Thm.thm

  val count_vars : term -> (string * int) list

  val move_conj_left : (term -> bool) -> term -> Thm.thm

  val mk_constraint : term * term -> term
  val is_constraint : term -> bool
  val is_vconstraint : term -> term -> bool

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
     operators in a standard Cooper formula (operators are =, < or
     int_divides).  Allows for the conv argument to be a QConv, and will
     also raise QConv.UNCHANGED itself *)
  val ADDITIVE_TERMS_CONV : conv -> conv

end