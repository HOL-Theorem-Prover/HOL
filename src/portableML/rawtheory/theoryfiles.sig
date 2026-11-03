signature theoryfiles =
sig

(* Locating built theory files on disk.
 *
 * Split out of `theorystats' so that a consumer wanting only the
 * directory scan does not pay for the rest.  `theorystats' exposes two
 * `Graph' instantiations in its signature, so merely loading it
 * elaborates them -- 0.146s, which a language server was paying at
 * every start for one 25-line function.  Nothing here needs a graph.
 *)

type theory_locn_map = string list Symtab.table

(* Depth-first, preorder *)
val recurse_toDirs : (string -> 'a -> 'a) -> 'a -> string list -> 'a

val find_theory_files_action : string -> theory_locn_map -> theory_locn_map

end
