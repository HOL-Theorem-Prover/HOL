signature codegen_ppcLib =
sig

  include Abbrev

  val ppc_assign2assembly      : codegen_inputLib.assign_type -> string list
  val ppc_guard2assembly       : codegen_inputLib.guard_type -> string list * (string * string)

  val ppc_cond_code            : Parse.term -> string * string
  val ppc_conditionalise       : string -> string -> string
  val ppc_remove_annotations   : string -> string

  val ppc_encode_instruction   : string -> string * int
  val ppc_encode_branch        : bool -> int -> string option -> string * int
  val ppc_branch_to_string     : string option -> string

  val set_ppc_temp_reg         : int -> unit
  val get_ppc_temp_reg         : unit -> int

end
