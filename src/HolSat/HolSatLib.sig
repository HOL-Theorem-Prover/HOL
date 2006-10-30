
signature HolSatLib = sig
  type sat_solver = SatSolvers.sat_solver 
  val tmp_name : string ref
  val prefix : string ref
  val sato : sat_solver
  val grasp  : sat_solver
  val zchaff  : sat_solver
  val minisat : sat_solver
  val minisatp : sat_solver
  val termToDimacsFile : string option -> int -> int -> Term.term array ->
			 string 
			 * (int * (Term.term, Term.term * int) Redblackmap.dict) 
			 * Term.term array
  val readDimacs :string -> Term.term 
  val satProve : sat_solver -> Term.term -> Thm.thm
  val satOracle : sat_solver -> Term.term -> Thm.thm
  exception Sat_counterexample of Thm.thm
  val SAT_TAUT_PROVE : Term.term -> Thm.thm

end
