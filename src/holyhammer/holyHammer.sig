signature holyHammer =
sig

  datatype prover = Eprover | Z3
  datatype predictor = KNN | Mepo
   
  (* Performs premise selection using the KNN algorithm *)
  val select_premises   : int -> term -> (string * string) list
  
  (* Export a HOL4 problem to THF TPTP files *)
  val export_problem    : prover -> (string * string) list -> term -> unit
  
  (* Translate the problem from THF to FOF via HOL/Light *)
  val translate_atp     : prover -> Process.status
  
  (* Calling an automated theorem prover such as "eprover" *)
  val launch_atp        : prover -> int -> Process.status
  
  (* Reconstruct and minimize the proof using Metis *)
  val reconstruct_atp   : prover -> term -> unit
  
  (* Main function and options *)
  val hh_atp            : prover -> int -> int -> term -> unit
  val hh_eprover        : term -> unit
  val hh_z3             : term -> unit
  val hh                : term -> unit (* eprover + z3 *)
  val clean_cache       : unit -> unit
  val set_timeout       : int -> unit
  val set_minimization  : bool -> unit
  val set_predictor     : predictor -> unit

end
