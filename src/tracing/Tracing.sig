signature Tracing =
sig

val trace_theory : string ->
  { theory      : string,
    parents     : (string*string) list,
    types       : (string*int) list,
    constants   : (string*Type.hol_type) list,
    all_thms    : (string * Thm.thm * RawTheory_dtype.thminfo) list,
    anon_thms   : Thm.thm list,
    mldeps      : string list } -> unit

(* Low-level proof export: serialize the theorem's proof tree to a .tr.gz
   side file, then flip the proof ref to Exported_prf.
   - `file`: target path for the side file (e.g. ".hol/objs/foo.tr.gz")
   - `tag`: identifier stored in the Exported_prf stub (e.g. SavedName "lemma")
   Theory.export_proof provides a higher-level wrapper with automatic naming. *)
val export_proof : {file: string, tag: Thm.thm_id} -> Thm.thm -> unit

end
