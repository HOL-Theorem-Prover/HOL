signature tacticToe =
sig

  include Abbrev

  (* TacticToe *)
  val ttt       : tactic
  val tactictoe : term -> tactic

  (* Settings *)
  val set_timeout     : real -> unit
  val set_record_hook : (unit -> unit) ref
    (* flags can only be changed inside this function *)

  (* Step by step exploration *)
  val next_tac : goal -> unit
  val next     : int -> tactic

  (* Recording *)
  val ttt_record        : unit -> unit
  val ttt_record_thy    : string -> unit
  val ttt_record_sigobj : unit -> unit
  val ttt_clean_all     : unit -> unit

  (* Evaluation *)
  val ttt_eval_thy     : string -> unit
  val eprover_eval_thy : string -> unit

  (* Used by tttRecord *)
  val init_tactictoe : unit -> unit
  val eval_tactictoe : string -> goal -> unit

end
