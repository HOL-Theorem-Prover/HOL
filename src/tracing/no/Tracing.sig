signature Tracing =
sig

val trace_theory : string ->
  { theory      : string,
    parents     : (string*string) list,
    types       : (string*int) list,
    constants   : (string*hol_type) list,
    all_thms    : (string * thm * thminfo) list,
    mldeps      : string list } -> unit

end
