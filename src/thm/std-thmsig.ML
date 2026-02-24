signature Thm =
sig
  include FinalThm

  val trace_id      : thm -> int
  val trace_counter : int ref
  datatype trace_step = datatype trace_step_dtype.trace_step
  val trace_hook : ((thm, term, hol_type) trace_step -> unit) option ref
  val save_dep_log : (int * thm) list ref
  val trace_export_hook :
    (string -> string list -> (string * thm) list -> (int * thm) list -> unit)
    option ref
  val trace_export : string -> string list -> (string * thm) list -> unit
end
