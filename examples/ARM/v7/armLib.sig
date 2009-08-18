signature armLib =
sig

  include arm_parserLib arm_encoderLib arm_disassemblerLib arm_stepLib

  val arm_decode   : string -> arm_parserLib.arm_code
  val thumb_decode : int -> string -> arm_parserLib.arm_code

  val arm_steps_from_quote  : string -> string frag list ->
                              (Abbrev.thm * Abbrev.thm option) list

  val arm_steps_from_string : string -> string ->
                              (Abbrev.thm * Abbrev.thm option) list

  val arm_steps_from_file   : string -> string ->
                              (Abbrev.thm * Abbrev.thm option) list

  val print_arm_assemble_from_quote  : string -> string frag list -> unit
  val print_arm_assemble_from_string : string -> string -> unit
  val print_arm_assemble_from_file   : string -> string -> unit

  val arm_assemble_to_file_from_quote  : string -> string ->
                                         string frag list -> unit
  val arm_assemble_to_file_from_string : string -> string -> string -> unit
  val arm_assemble_to_file_from_file   : string -> string -> string -> unit

end
