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
  
  val unquoteString        : string -> string
  val hol_scripts          : unit -> string list
  val hol_examples_scripts : unit -> string list
  val cakeml_theories      : string -> string list
  val cakeml_scripts       : string -> string list
  val interactive_hook     : string ref
  val irewrite_script      : string -> unit
  val irecord_script       : string -> unit
  val erewrite_script      : string -> unit
  val erewrite_hol_scripts : unit -> unit
  
  val open_struct : 
    (string, stack_t) Redblackmap.dict list -> string -> (string * stack_t) list

end
