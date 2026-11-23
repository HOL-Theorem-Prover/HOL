signature TheoryReader =
sig

  exception TheoryReader of string
  type raw_theory = RawTheory_dtype.raw_theory
  type sharing_tables = RawTheory_dtype.sharing_tables
  type 'a raw_exports = 'a RawTheory_dtype.raw_exports
  type 'a raw_core = {tables : sharing_tables, exports : 'a raw_exports}
  val load_thydata : {thyname:string,path:string,hash:string} ->
                     (Thm.thm * DB_dtype.thminfo) Symtab.table
  val core_decode : string raw_core HOLsexp.decoder

  val load_raw_thydata : {path:string} -> raw_theory

  (* Hook for alternative theorem sources (e.g., proof trace replay).
     When set to something other than the default, load_thydata dispatches
     to this function instead of loading theorems from .dat files. *)
  val load_thydata_fn :
      ({thyname:string,path:string,hash:string} ->
       (Thm.thm * DB_dtype.thminfo) Symtab.table) ref

  (* Reusing a load: a theory's decoded data, from a load_thydata call
     made through capture_decoded (NONE if it didn't decode a .dat), and
     register_decoded to repeat that load's registration from it, under
     the theory hash its FooTheory.sml names, unless the data's parents
     aren't canonical or its references aren't current: then it
     registers nothing and returns false. *)
  type decoded
  val decoded_tag : decoded MLSYSPortable.persistent_tag
  (* A theory structure's theorem values, in its record's order. *)
  val values_tag : (string * Thm.thm vector) MLSYSPortable.persistent_tag
  (* The digest of the file a saved module's values were decoded from. *)
  val digest_tag : string MLSYSPortable.persistent_tag
  val decoded_name : decoded -> string
  val decoded_parents : decoded -> string list
  val decoded_theorems : decoded -> (string * Thm.thm * DB_dtype.thminfo) list
  val capture_decoded : ('a -> 'b) -> 'a -> 'b * decoded option
  val register_decoded : string -> decoded -> bool
  (* What a theory's load builds from its decoded data alone, made where
     its module is written (NONE when reading theory data there depends
     on more than the data, or fix_preparers wasn't called), and
     register_decoded using it when it was made from the same decoded
     value.  Only the theory data types there were at the last
     fix_preparers, which bossLib calls, are read. *)
  type prepared
  val prepared_tag : prepared option MLSYSPortable.persistent_tag
  val fix_preparers : unit -> unit
  val prepare : decoded -> prepared option
  val register_prepared : string -> decoded -> prepared option -> bool
  (* How many read theory data segments loads from prepared data were
     given, and how many of them they installed. *)
  val prepared_statistics : unit -> {offered : int, installed : int}
  (* Whether the other theories' kernel entries the decoded values refer
     to are still the ones they were decoded against: those theories are
     canonical and the entries unchanged. *)
  val refs_current : decoded -> bool
  (* Decodes a .dat as load_thydata does, linking the theory, adding its
     types and constants to the kernel signature and sealing it, but
     registering nothing else; the flag says whether the theory's kernel
     ids are canonical.  register_kernel repeats this much of a load from
     decoded data, refusing data whose parents aren't canonical or whose
     references aren't current.  Both refuse a sealed theory, and leave
     the context as it was when they fail. *)
  val decode_thydata : {thyname:string,path:string,hash:string} ->
                       decoded * bool
  val register_kernel : string -> decoded -> unit
  (* Whether a theory's kernel ids are the same in every process that
     shares the current saved state. *)
  val is_canonical : string -> bool
  val default_loader : unit -> bool

end

(* [load_thydata thyname fname] loads the filename and makes the appropriate
   changes to the theory hierarchy in response to the data stored there.  In
   other words, this is done mostly for the side-effects. The map returned
   allows <nm>Theory.sml files to then bind SML identifiers corresponding to
   theorem names to theorem values.
*)
