signature Logging =
sig

val raw_start_logging : TextIO.outstream -> unit
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
Calls to [export_thm] that aren't between a call to [start_logging] and a call
to [stop_logging] won't write anything.
[raw_start_logging out] is like [start_logging()] but will write the article to the stream [out] rather than a file based on the theory name.

[stop_logging()] finishes writing and closes the article file currently being
logged.

[export_thm th] writes article commands to make the virtual machine prove,
remember (in the dictionary), and export the theorem [th]. It should be called
on all theorems intended to be an article export.

[set_tyop_name_handler h] installs h as the function used to create an OpenTheory name from a HOL4 type operator name when the OpenTheoryMap does not already have a mapping for the HOL4 name.
[set_const_name_handler h] is similar, for constants.
[reset_tyop_name_handler()] and [reset_const_name_handler()] remove these custom functions (reverting to the default behaviour of raising an exception when a mapping does not exist).
*)

end
