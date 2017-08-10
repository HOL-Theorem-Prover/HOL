signature hhsExec =
sig

  include Abbrev
  
  val hhs_bool_glob    : bool ref
  val hhs_tacticl_glob : tactic list ref
  val hhs_string_glob  : string ref
  
  val exec_sml         : string -> string -> bool
  
  val is_thm           : string -> bool
  val is_tactic        : string -> bool
  val is_pointer_eq    : string -> string -> bool
  
  val tactic_of_sml    : string -> tactic
  val tacticl_of_sml   : string list -> tactic list
  val string_of_sml    : string -> string
  
  val type_of_sml      : string -> string

end
