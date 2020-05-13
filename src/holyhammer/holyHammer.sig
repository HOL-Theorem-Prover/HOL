signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Vampire

  val set_timeout : int -> unit

  val holyhammer  : term -> thm
  val hh          : tactic
  (* For running holyhammer in the backgroup with a high time limit *)
  val hh_fork     : goal -> Thread.thread
  (* string list is a list of premises of the form "fooTheory.bar" *)
  val hh_pb       : prover list -> string list -> goal -> tactic
  
  (* Evaluation of holyhammer (without premise selection) *)
  val hh_pb_eval_thm : prover list -> string * thm -> unit
  val hh_pb_eval_thy : prover list -> string -> unit

  (* Evaluation of holyhammer (with premise selection).
     This function is used inside the tactictoe evaluation framework. *)
  val hh_eval : mlThmData.thmdata * mlTacticData.tacdata -> goal -> unit

end
