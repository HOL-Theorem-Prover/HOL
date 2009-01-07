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

  val to_x86_regs              : {redex: Term.term, residue: Term.term} list
  val from_x86_regs            : {redex: Term.term, residue: Term.term} list

end
