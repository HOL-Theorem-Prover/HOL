signature smlExecute =
sig

  include Abbrev

  (* execution function *)
  val quse_string : string -> bool

  (* result slots of the thread running a compiled string, set by the
     strings the readers compile *)
  type 'a slot
  val put               : 'a slot -> 'a -> unit
  val sml_bool_slot     : bool slot
  val sml_tactic_slot   : tactic slot
  val sml_string_slot   : string slot
  val sml_goal_slot     : goal slot
  val sml_thm_slot      : thm slot
  val sml_thml_slot     : thm list slot

  (* tests *)
  val is_thm_value     :
    (string * PolyML.NameSpace.Values.value) list -> string -> bool
  val is_local_value   : string -> bool
  val is_thm           : string -> bool
  val is_thml          : string -> bool
  val is_tactic        : string -> bool
  val is_string        : string -> bool
  val is_simpset       : string -> bool
  val is_pointer_eq    : string -> string -> bool
  val is_stype         : string -> bool

  (* readers *)
  val thm_of_sml        : string -> (string * thm) option
  val thml_of_sml       : string list -> thm list option
  val tactic_of_sml     : real -> string -> tactic
  val tactic_of_sml_no_timeout : string -> tactic
  val string_of_sml     : string -> string
  val goal_of_sml       : string -> goal

  (* applying a tactic string *)
  val app_stac : real -> string -> goal -> goal list option

end
