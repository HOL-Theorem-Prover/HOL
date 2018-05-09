signature tacticToe =
sig

  include Abbrev

  (* TacticToe *)
  val ttt       : tactic
  val tactictoe : term -> tactic

  (* Interactive exploration *)
  val next_tac_number : int ref
  val next_tac  : goal -> unit
  val next      : int -> tactic

  (* Settings *)
  val set_timeout : real -> unit

  (* Creating fof and thf files *)
  val create_fof_thy : string -> unit
  val create_fof_parallel : int -> string list -> unit
  val create_thf_thy : string -> unit
  val create_thf_parallel : int -> string list -> unit

  (* Recording *)
  val ttt_record          : unit -> unit
  val ttt_record_parallel : int -> unit
  val load_sigobj         : unit -> unit
  val ttt_clean_all       : unit -> unit

  (* Evaluation *)
  val eval_tactictoe        : goal -> unit
  val eval_eprover          : goal -> unit
  val ttt_eval_thy          : string -> unit
  val eprover_eval_thy      : string -> unit
  val ttt_eval_parallel     : int -> string list -> unit
  val eprover_eval_parallel : int -> string list -> unit

end
