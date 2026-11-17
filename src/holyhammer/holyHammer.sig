signature holyHammer =
sig

  include Abbrev
  datatype prover = datatype hhConfig.prover

  val set_timeout : int -> unit
  val holyhammer  : term -> thm
  val hh          : tactic
  val hh_fork     : goal -> Thread.thread
  (* string list is a list of premises of the form "fooTheory.bar" *)
  val hh_pb  : string -> prover list -> string list -> goal -> tactic

  (* For developers *)
  (* same as hh_pb but with all atps and premise selection *)
  val main_hh : string -> mlThmData.thmdata -> goal -> tactic
  val main_hh_lemmas : string -> mlThmData.thmdata -> goal -> string list option
  (* evaluation of holyhammer (with premise selection).
     This function is used inside the tactictoe evaluation framework. *)
  (* val hh_eval : mlThmData.thmdata * mlTacticData.tacdata -> goal -> unit *)

end
