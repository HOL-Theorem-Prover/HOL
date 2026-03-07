signature Tracing =
sig

val trace_theory : string ->
  { theory      : string,
    parents     : (string*string) list,
    types       : (string*int) list,
    constants   : (string*Type.hol_type) list,
    all_thms    : (string * Thm.thm * RawTheory_dtype.thminfo) list,
    mldeps      : string list } -> unit

end
