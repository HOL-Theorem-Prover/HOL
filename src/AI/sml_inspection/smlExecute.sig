signature smlExecute =
sig

  include Abbrev

  (* execution function *)
  val execprefix_glob  : string ref
  val exec_sml         : string -> string -> bool

  (* global references *)
  val sml_bool_glob     : bool ref
  val sml_tacticl_glob  : tactic list ref
  val sml_tactic_glob   : tactic ref
  val sml_string_glob   : string ref
  val sml_goal_glob     : goal ref
  val sml_thm_glob      : thm ref
  val sml_thml_glob     : thm list ref

  (* tests *)
  val is_thm_value     :
    (string * PolyML.NameSpace.Values.value) list -> string -> bool
  val is_local_value   : string -> bool

  val is_thm           : string -> bool
  val is_tactic        : string -> bool
  val is_string        : string -> bool
  val is_pointer_eq    : string -> string -> bool
  val is_stype         : string -> bool

  (* readers *)
  val thm_of_sml       : string -> (string * thm) option
  val thml_of_sml      : string list -> (string * thm) list option
  val tactic_of_sml    : string -> tactic
  val string_of_sml    : string -> string
  val goal_of_sml      : string -> goal

  (* applying a tactic string *)
  val app_stac   : real -> string -> goal -> goal list option

end
