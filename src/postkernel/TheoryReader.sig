signature TheoryReader =
sig

  exception TheoryReader of string
  val load_thydata : string -> string -> (string, Thm.thm) Redblackmap.dict

end

(* [load_thydata thyname fname] loads the filename and makes the appropriate
   changes to the theory hierarchy in response to the data stored there.  In
   other words, this is done mostly for the side-effects. The map returned
   allows <nm>Theory.sml files to then bind SML identifiers corresponding to
   theorem names to theorem values.
*)
