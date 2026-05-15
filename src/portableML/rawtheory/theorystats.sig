signature theorystats =
sig

type raw_name = RawTheory_dtype.raw_name
type thykey = raw_name * string
structure RawTheorykey : KEY where type key = thykey
structure TheoryGraph : GRAPH where type key = thykey

type raw_nodedata = {exports : string RawTheory_dtype.raw_exports,
                     parents : raw_name list}
type thygraph_data = raw_nodedata TheoryGraph.T * (thykey * raw_name list) list

type theory_locn_map = string list Symtab.table

val die : string -> 'a
val println : string -> unit
val emit_scan_progress : (string -> unit) ref
val recurse_toDirs : (string -> 'a -> 'a) -> 'a -> string list -> 'a
val find_theory_files_action : string -> theory_locn_map -> theory_locn_map
val find_theory_action : string -> thygraph_data -> thygraph_data
val load_paths : string list -> thygraph_data -> thygraph_data
val load_with_ancestors : string list -> theory_locn_map -> thygraph_data ->
                          thygraph_data
val find_unused : (string * raw_nodedata) list ->
                  string Redblackset.set Symtab.table

end
