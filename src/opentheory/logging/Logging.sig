signature Logging =
sig

val start_logging : unit -> unit
val export_thm    : Thm.thm -> Thm.thm
val log_definitions : unit -> unit
val stop_logging  : unit -> unit

(*
[start_logging()] creates a new article file based on the current theory name.
Calls to [log_thm] or [export_thm] that aren't between a call to
[start_logging] and a call to [stop_logging] won't write anything.

[stop_logging()] finishes writing and closes the article file currently being
logged.

[log_definitions()] logs any definitional theorems made since the last call to
[log_definitions] (or to [start_logging]). The theorems are not automatically
added to the article exports. [log_definitions] should be called immediately
after any definitions of constants or types (including by [new_specification])
to ensure the article defines constants before using them.

[export_thm th] is like [log_thm th] except it also adds the theorem to the
list of article exports. It should be called on all theorems intended to be an
article export.
*)

end
