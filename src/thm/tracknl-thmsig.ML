signature Thm =
sig
  include FinalThm

  val trace_id           : thm -> int
  val trace_get_types    : unit -> hol_type list
  val trace_get_terms    : unit -> term list
  val trace_lookup_type  : hol_type -> int
  val trace_lookup_term  : term -> int
  val trace_close_files  : unit -> unit
  val trace_step_count   : unit -> int
  val trace_steps_path   : unit -> string
  val trace_parents_path : unit -> string
  val trace_reset        : unit -> unit
  val trace_get_ext_cache : unit -> (int, term list * term) Redblackmap.dict
  val trace_cache_ext_thm : thm -> unit
  val trace_export : string -> string list -> (string * thm) list -> unit
end
