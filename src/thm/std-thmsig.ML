signature Thm =
sig
  include FinalThm
  val trace_export : string -> string list -> (string * thm) list -> unit
end
