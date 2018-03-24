signature tttUnfold =
sig

  include Abbrev
  datatype stack_t =
    Protect
  | Watch
  | Undecided
  | Replace      of string list
  | SReplace     of string list
  | Structure    of string
  | SValue       of string
  | SConstructor of string
  | SException   of string

  (* tools *)
  val find_script : string -> string

  (* recording *)
  val ttt_rewrite_thy : string -> unit
  val ttt_record_thy  : string -> unit
  val ttt_rewrite : unit -> string list
  val ttt_record : unit -> unit
  val ttt_record_parallel : int -> unit
  val load_sigobj : unit -> unit
  val ttt_clean_all : unit -> unit

  (* evaluation *)
  val ttt_eval_thy: string -> unit
  val eprover_eval_thy: string -> unit
  val ttt_eval_parallel: int -> string list -> unit
  val eprover_eval_parallel: int -> string list -> unit

end
