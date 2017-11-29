signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Satallax
  datatype predictor = KNN | Mepo
   
  (* Performs premise selection using the KNN algorithm *)
  val select_premises   : int -> term -> (string * string) list
  
  (* Export a problem to TT files *)
  val export_problem    : prover -> (string * string) list -> term -> unit
  
  (* Export theories to TT files *)
  val export_theories   : string list -> unit
  
  (* Export and translate a re-proving problem to THF *)
  val reproving_thf : string -> string * thm -> unit
  val reproving_thf_thyl : string list -> unit
  
  (* Translate the problem from THF to FOF via HOL/Light *)
  val translate_atp     : prover -> Process.status
  val translate_thf     : prover -> Process.status
  
  (* Calling an automated theorem prover such as "eprover" *)
  val launch_atp        : prover -> int -> Process.status
  
  (* Reconstruct and minimize the proof using Metis *)
  val reconstruct_atp   : prover -> term -> tactic
  
  (* Main function and options *)
  val hh_atp            : prover -> int -> int -> term -> tactic
  val hh_eprover        : term -> tactic
  val hh_z3             : term -> tactic
  val holyhammer        : term -> tactic (* eprover + z3 *)
  val hh_tac            : tactic
  val hh_stac           : goal -> string option
  val clean_cache       : unit -> unit
  val set_timeout       : int -> unit
  val set_minimization  : bool -> unit
  val set_predictor     : predictor -> unit

end
