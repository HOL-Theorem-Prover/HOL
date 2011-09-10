signature Logging =
sig

val start_logging : unit -> unit
val export_thm    : Thm.thm -> Thm.thm
val log_thm       : Thm.thm -> Thm.thm
val stop_logging  : unit -> unit

(*
[start_logging()] creates a new article file based on the current theory name.
Calls to [log_thm] or [export_thm] that aren't between a call to
[start_logging] and a call to [stop_logging] won't write anything.

[stop_logging()] finishes writing and closes the article file currently being
logged.

[log_thm th] writes article commands to make the virtual machine prove and
remember the theorem [th]. It should be used on all definitional theorems (e.g.
returned by Define or new_type_definition) as soon as they are proved, so the
constant will be available for virtual machine use. It is not necessary to call
log_thm for any other purpose.

[export_thm th] is like [log_thm th] except it also adds the theorem to the
list of article exports. It should be called on all theorems intended to be an
article export.
*)

end
