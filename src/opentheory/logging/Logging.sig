signature Logging =
sig

val start_logging : unit -> unit
val export_thm    : Thm.thm -> Thm.thm
val stop_logging  : unit -> unit

type thy_tyop  = OpenTheoryMap.thy_tyop
type thy_const = OpenTheoryMap.thy_const
type otname    = OpenTheoryMap.otname

  val set_tyop_name_handler    : (thy_tyop -> otname) -> unit
  val reset_tyop_name_handler  : unit -> unit
  val set_const_name_handler   : (thy_const -> otname) -> unit
  val reset_const_name_handler : unit -> unit

(*
[start_logging()] creates a new article file based on the current theory name.
Calls to [log_thm] or [export_thm] that aren't between a call to
[start_logging] and a call to [stop_logging] won't write anything.

[stop_logging()] finishes writing and closes the article file currently being
logged.

[export_thm th] is like [log_thm th] except it also adds the theorem to the
list of article exports. It should be called on all theorems intended to be an
article export.

[set_tyop_name_handler h] installs h as the function used to create an OpenTheory name from a HOL4 type operator name when the OpenTheoryMap does not already have a mapping for the HOL4 name.
[set_const_name_handler h] is similar, for constants.
[reset_tyop_name_handler()] and [reset_const_name_handler()] remove these custom functions (reverting to the default behaviour of raising an exception when a mapping does not exist).
*)

end
