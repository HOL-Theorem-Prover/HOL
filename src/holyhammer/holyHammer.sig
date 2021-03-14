signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Vampire

  val set_timeout : int -> unit
  val holyhammer  : term -> thm
  val hh          : tactic
  val hh_fork     : goal -> Thread.thread
  
  (* remove limits on the number of premises *)
  val dep_flag : bool ref  
  (* string list is a list of premises of the form "fooTheory.bar" *)
  val hh_pb  : string -> prover list -> string list -> goal -> tactic
  (* same as hh_pb but with all atps and premise selection *)
  val main_hh : string -> mlThmData.thmdata -> goal -> tactic
  val main_hh_lemmas : string -> mlThmData.thmdata -> goal -> string list option

  (* Evaluation of holyhammer (without premise selection) *)
  val hh_pb_eval_thm : prover list -> string * thm -> unit
  val hh_pb_eval_thy : prover list -> string -> unit

  (* Evaluation of holyhammer (with premise selection).
     This function is used inside the tactictoe evaluation framework. *)
  (* val hh_eval : mlThmData.thmdata * mlTacticData.tacdata -> goal -> unit *)

end
