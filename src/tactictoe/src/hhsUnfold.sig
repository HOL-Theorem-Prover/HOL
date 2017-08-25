signature hhsUnfold =
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
  val all_files : unit -> string list
  val hhs_rewrite : string -> unit
  
  val open_struct : 
  (string, stack_t) Redblackmap.dict list -> string -> (string * stack_t) list

  
end
