signature DerivedBddRules = sig

  type thm = Thm.thm
  type term = Term.term
  type bdd = bdd.bdd
  type bddop = bdd.bddop
  type term_bdd = PrimitiveBddRules.term_bdd
  type varmap = Varmap.varmap

  exception findModelError
  exception dest_BddOpError
  exception computeTraceError
  exception termToTermBddError
  exception BddApRestrictError
  exception BddSatoneError
  exception BddApReplaceError
  exception fail
  exception BddApSubstError
  exception computeFixedpointError
  exception bddToTermError

  val isTRUE : term_bdd -> bool
  val MkPrevThm : thm -> thm
  val traceBack : varmap -> term_bdd list -> thm -> thm -> (term_bdd * (term_bdd * term_bdd) list) list
  val BddEqualTest : term_bdd -> term_bdd -> bool
  val TermBddToEqThm : term_bdd -> thm
  val statecount : bdd -> real
  val flatten_pair : term -> term list
  val BddSatone : term_bdd -> (term_bdd * term_bdd) list
  val bddToTerm : varmap -> bdd -> term
  val findTrace : varmap -> thm -> thm -> thm -> thm * thm list * thm
  val termToTermBddFun : (term -> term_bdd) ref
  val BddRhsOracle : (term -> term_bdd) -> varmap -> thm -> thm
  val computeTrace : (int -> term_bdd -> 'a) -> varmap -> thm -> thm * thm -> term_bdd list
  val findModel : term_bdd -> thm
  val MakeSimpRecThm : thm -> thm
  val GenTermToTermBdd :  (term -> term_bdd) -> varmap -> term -> term_bdd
  val iterate : ('a -> bool) -> (int -> 'a -> 'a) -> 'a -> 'a
  val BddSubst : (term_bdd * term_bdd) list -> term_bdd -> term_bdd
  val BddApReplace : term_bdd -> term -> term_bdd
  val eqToTermBdd : (term -> term_bdd) -> varmap -> thm -> term_bdd
  val extendVarmap : term list -> varmap -> varmap
  val isFALSE : term_bdd -> bool
  val showVarmap : unit -> (string * int) list
  val BddApConv : (term -> thm) -> term_bdd -> term_bdd
  val computeFixedpoint : (int -> term_bdd -> 'a) -> varmap -> thm * thm -> term_bdd * term_bdd
  val dest_BddOp : term -> bddop * term * term
  val BddApSubst : term_bdd -> term -> term_bdd
  val extendSat : term list -> varmap -> (term_bdd * term_bdd) list -> (term_bdd * term_bdd) list
  val failfn : 'a -> 'b
  val global_varmap : varmap ref
  val split_subst : (term_bdd * term_bdd) list -> (term_bdd * term_bdd) list * (term_bdd * term_bdd) list
  val BddAssume : term -> term_bdd
  val thmToTermBdd : thm -> term_bdd
  val BddApThm : thm -> term_bdd -> term_bdd
  val BddApRestrict : term_bdd -> term -> term_bdd
  val MkIterThms : thm -> term -> term -> thm * thm
  val termToTermBdd : term -> term_bdd
  val intToTerm :  int -> term
  val traceBackPrevThm : thm ref

end
