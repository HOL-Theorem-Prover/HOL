signature codegen_armLib =
sig

  include Abbrev

  val arm_assign2assembly      : codegen_inputLib.assign_type -> string list 
  val arm_guard2assembly       : codegen_inputLib.guard_type -> string list * (string * string)

  val arm_cond_code            : Parse.term -> string * string
  val arm_conditionalise       : string -> string -> string
  val arm_remove_annotations   : string -> string

  val arm_encode_instruction   : string -> string * int
  val arm_encode_branch        : bool -> int -> string option -> string * int

end
