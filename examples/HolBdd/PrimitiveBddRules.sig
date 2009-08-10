signature PrimitiveBddRules = sig

  type assums = Term.term HOLset.set
  type varmap = Varmap.varmap
  type term_bdd

  exception BddAppallError
  exception nameError
  exception BddSupportContractVarmapError
  exception BddEqMpError
  exception BddForallError
  exception BddfindModelError
  exception BddReplaceError
  exception BddExtendVarmapError
  exception BddIteError
  exception BddExistsError
  exception BddThmOracleError
  exception BddVarError
  exception BddRestrictError
  exception BddSimplifyError
  exception BddAppexError
  exception BddComposeError
  exception BddOpError
  exception BddFreevarsContractVarmapError
  exception BddListComposeError

  val BddDisch : term_bdd -> term_bdd -> term_bdd
  val BddListCompose : (term_bdd * term_bdd) list -> term_bdd -> term_bdd
  val BddVar : bool -> varmap -> Term.term -> term_bdd
  val getTag : term_bdd -> Thm.tag
  val getAssums : term_bdd -> assums
  val BddThmOracle : term_bdd -> Thm.thm
  val getVarmap : term_bdd -> varmap
  val BddNot : term_bdd -> term_bdd
  val BddEqMp : Thm.thm -> term_bdd -> term_bdd
  val BddfindModel : term_bdd -> term_bdd
  val getTerm : term_bdd -> Term.term
  val dest_term_bdd : term_bdd -> Thm.tag * assums * varmap * Term.term * bdd.bdd
  val BddExists : Term.term list -> term_bdd -> term_bdd
  val BddAppex : Term.term list -> bdd.bddop * term_bdd * term_bdd -> term_bdd
  val getBdd : term_bdd -> bdd.bdd
  val name : Term.term -> string
  val inSupport : int -> bdd.bdd -> bool
  val BddForall : Term.term list -> term_bdd -> term_bdd
  val BddFreevarsContractVarmap : Term.term -> term_bdd -> term_bdd
  val BddAppall : Term.term list -> bdd.bddop * term_bdd * term_bdd -> term_bdd
  val BddCon : bool -> varmap -> term_bdd
  val BddExtendVarmap : varmap  -> term_bdd -> term_bdd
  val BddSimplify : term_bdd * term_bdd -> term_bdd
  val BddCompose : term_bdd * term_bdd -> term_bdd -> term_bdd
  val BddOp : bdd.bddop * term_bdd * term_bdd -> term_bdd
  val BddRestrict : (term_bdd * term_bdd) list -> term_bdd -> term_bdd
  val BddReplace : (term_bdd * term_bdd) list -> term_bdd -> term_bdd
  val BddSupportContractVarmap : Term.term -> term_bdd -> term_bdd
  val termApply : Term.term -> Term.term -> bdd.bddop -> Term.term
  val BddIte : term_bdd * term_bdd * term_bdd -> term_bdd
end
