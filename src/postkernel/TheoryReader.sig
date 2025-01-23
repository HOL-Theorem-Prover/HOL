signature TheoryReader =
sig

  exception TheoryReader of string
  type raw_theory = RawTheory_dtype.raw_theory
  type sharing_tables = RawTheory_dtype.sharing_tables
  type 'a raw_exports = 'a RawTheory_dtype.raw_exports
  type 'a raw_core = {tables : sharing_tables, exports : 'a raw_exports}
  val load_thydata : {thyname:string,path:string} ->
                     (Thm.thm * DB_dtype.thminfo) Symtab.table
  val core_decode : string raw_core HOLsexp.decoder

  val load_raw_thydata : {thyname:string,path:string} -> raw_theory


end

(* [load_thydata thyname fname] loads the filename and makes the appropriate
   changes to the theory hierarchy in response to the data stored there.  In
   other words, this is done mostly for the side-effects. The map returned
   allows <nm>Theory.sml files to then bind SML identifiers corresponding to
   theorem names to theorem values.
*)
