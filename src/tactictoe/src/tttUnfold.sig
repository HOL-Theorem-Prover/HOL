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
  
  val unquoteString        : string -> string
  val sigobj_scripts       : unit -> string list
  val sigobj_theories      : unit -> string list

  val open_structure : string -> (string * stack_t) list

  val find_script : string -> string 
  
  val ttt_record : unit -> unit
  val ttt_record_sigobj : unit -> unit
  val ttt_record_thy: string -> unit
  val ttt_clean_open : unit -> unit
  val ttt_eval_thy: string -> unit
  val eprover_eval_thy: string -> unit

end
