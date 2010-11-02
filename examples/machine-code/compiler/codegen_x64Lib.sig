signature codegen_x64Lib =
sig

  include Abbrev

  val x64_assign2assembly      : codegen_inputLib.assign_type -> string list
  val x64_guard2assembly       : codegen_inputLib.guard_type -> string list * (string * string)

  val x64_cond_code            : Parse.term -> string * string
  val x64_conditionalise       : string -> string -> string
  val x64_remove_annotations   : string -> string

  val x64_encode_instruction   : string -> string * int
  val x64_encode_branch        : bool -> int -> string option -> string * int
  val x64_branch_to_string     : string option -> string

end
