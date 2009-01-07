signature codegenLib =
sig

  include Abbrev

  val assemble        : string -> 'a Lib.frag list -> string list
  val generate_code   : string -> bool -> term -> string list * int

  val add_compiler_assignment : term -> term -> string -> int -> unit
  val add_compiled            : thm list -> unit
  val print_compiler_grammar  : unit -> unit

end
