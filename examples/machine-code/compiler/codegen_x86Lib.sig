signature codegen_x86Lib =
sig

  include Abbrev

  val x86_assign2assembly      : codegen_inputLib.assign_type -> string list 
  val x86_guard2assembly       : codegen_inputLib.guard_type -> string list * (string * string)

  val x86_cond_code            : Parse.term -> string * string
  val x86_conditionalise       : string -> string -> string
  val x86_remove_annotations   : string -> string

  val x86_encode_instruction   : string -> string * int
  val x86_encode_branch        : bool -> int -> string option -> string * int
  val x86_branch_to_string     : string option -> string

  val to_x86_regs              : unit -> {redex: Term.term, residue: Term.term} list
  val set_x86_regs             : (int * string) list -> unit
  val get_x86_regs             : unit -> (int * string) list

end
