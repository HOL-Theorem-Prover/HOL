
signature HolSatLib = sig
 datatype sat_solver = 
 SatSolver of
  {name           : string,
   URL            : string,
   executable     : string,    
   notime_run     : string -> string * string -> string,    
   time_run       : string -> (string * string) * int -> string,      
   only_true      : bool,
   failure_string : string,
   start_string   : string,  
   end_string     : string}
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
(*
  exception satSolveError
  exception lookup_sat_numError
  exception literalToIntError
  exception satCheckError
  exception stringToIntError
  exception substringToIntError
  val buildClause : int list -> Term.term
  val EQF_Imp1 : Thm.thm
  val sat_var_map : (int * (string * int) Binaryset.set) ref
  val satCheck : Term.term list -> Term.term -> Thm.thm
  val parseSat : string * string -> substring -> int list
  val lookup_sat_num : int -> string
  val substringToInt : substring -> int
  val stripPreamble : TextIO.instream -> string list
  val pcompare : (string * int) * (string * int) -> order
  val intToLiteral : int -> Term.term
  val literalToInt : Term.term -> bool * int
  val initSatVarMap : unit -> unit
  val invokeSat : sat_solver -> Term.term -> Term.term list option
  val print_all_term : Term.term -> unit
  val LiteralToString : bool * int -> string
  val substringContains : string -> substring -> bool
  val isSuccess : Process.status -> bool
  val EQT_Imp1 : Thm.thm
  val EQT_Imp2 : Thm.thm
  val stringToInt : string -> int
  val termToDimacs : Term.term -> (bool * int) list list
  val intToPrefixedLiteral : int -> Term.term
  val lookup_sat_var : string -> int
  val dimacsToTerm : int list -> Term.term
  val termToDimacsFile : Term.term -> string
*)
end
