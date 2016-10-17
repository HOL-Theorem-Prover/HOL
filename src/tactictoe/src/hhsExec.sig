signature hhsExec =
sig

  include Abbrev
  val exec_sml      : string -> string -> bool
  
  val is_thm        : string -> bool
  val is_tactic     : string -> bool
  val hhs_bool      : bool ref 
  val is_pointer_eq : string -> string -> bool
  val hhs_tactic    : tactic ref
  val valid_tactic_of_sml : string -> tactic
  val hhs_tacticl   : tactic list ref
  val valid_tacticl_of_sml : string list -> tactic list
  val hhs_thm       : string ref
  val thmname_of_sml : string -> string

end
