signature Tracing =
sig

val trace_theory : string -> ((string * Thm.thm) list * Thm.thm list) -> unit

end
