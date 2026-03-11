structure PFTEmit :> PFTEmit = struct

open ProofTraceParser

datatype thm_ref = NamedThm of string | AnonThm of int

datatype target = ThyThm of string * string * bool
                | ThyAll of string * bool

(* --- Utilities ----------------------------------------------------------- *)

(* Extract theory name from a .tr.gz file path: fooTheory.tr.gz -> foo *)
fun thyname_of_path path = let
  val file = OS.Path.file path
in
  case String.tokens (fn c => c = #".") file of
    (base :: _) =>
      if String.isSuffix "Theory" base
      then String.substring(base, 0, String.size base - 6)
      else raise Fail ("PFTEmit: expected <thy>Theory.tr.gz, got " ^ file)
  | _ => raise Fail ("PFTEmit: bad trace filename " ^ file)
end

(* --- Phase 1: resolve ---------------------------------------------------- *)

(* Discover .tr.gz dependencies starting from targets, topsort them,
   and return (file_path, needed_thm_refs) in dependency order. *)
fun resolve {search_path, targets} =
  raise Fail "PFTEmit.resolve: not yet implemented"

(* --- Phase 2: emit ------------------------------------------------------- *)

(* Process topsorted theories and emit a single PFT trace.

   For each theory in order:
   1. Parse the .tr.gz file.
   2. Run ProofTraceWalk.walk from the needed roots to get refcounts,
      closedness, defs, and identifier caches.
   3. Emit types, terms, and theorems by traversing the proof DAG,
      converting de Bruijn/Clos terms to named VAR/CONST/COMB/ABS.
   4. Track PFT IDs per namespace with free-list reuse.
   5. Emit DEL when refcounts reach zero.
   6. At the end, SAVE target theorems (and optionally definitions).

   The header with peak namespace counts is prepended after all
   commands are written (via PFTWriter temp file support). *)
fun emit {resolved, targets, output, binary} =
  raise Fail "PFTEmit.emit: not yet implemented"

end
