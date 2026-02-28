signature Thm =
sig
  include FinalThm

  val trace_id      : thm -> int
  val trace_counter : int ref
  datatype trace_step = datatype trace_step_dtype.trace_step
  val trace_hook : ((thm, term, hol_type) trace_step -> unit) option ref
  val trace_export_hook :
    (string -> string list -> (string * thm) list -> unit)
    option ref
  val trace_export : string -> string list -> (string * thm) list -> unit

  (* Replay-aware theory loading: when set, disk_thm substitutes
     replayed theorem values instead of creating DISK_THMs. *)
  val replay_thms :
    { named : (string * string, thm) Redblackmap.dict,
      anon  : (string * int, thm) Redblackmap.dict } option ref

  (* Term source registration for tracing: allows the compute library
     to register that a term is rand(concl(th)) so that intern_term
     can emit a derived T entry instead of a full recursive descent. *)
  val register_term_source : (term * int -> unit) ref
  val save_term_sources : (unit -> int) ref
  val restore_term_sources : (int -> unit) ref
end
