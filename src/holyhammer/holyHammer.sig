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

  (* remembers how goals were proven *)
  val clean_hh_goaltac_cache : unit -> unit
  (* remembers features of goals (shared with tactictoe) *)
  val clean_goalfea_cache : unit -> unit

  (* Evaluation of holyhammer (without premise selection) *)
  val hh_pb_eval_thm : prover list -> string * thm -> unit
  val hh_pb_eval_thy : prover list -> string -> unit

  (* Evaluation of holyhammer (with premise selection).
     This function is used inside the tactictoe evaluation framework. *)
  val hh_eval : (mlThmData.thmdata * mlTacticData.tacdata) -> 
     (string * string) -> goal -> unit

end
