(* Read-only parent compatibility checks, independent of build layouts.
   Only the parent header is checked, not the remaining theory data. *)
signature TheoryDat =
sig
  type parent = {thy : string, hash : string}
  datatype 'a result = Success of 'a | Failure of string

  (* A complete header, including the following core-data tag, is required.
     Duplicate parents and malformed non-bootstrap SHA1 identities fail.
     An empty parent list is a successful result, not a parse failure.
     Strings and comments follow HOLsexp syntax. The body is not read. *)
  val read_parents : string -> parent list result

  datatype resolution = Artifact of string
                      | Missing
                      | Ambiguous of string list
  datatype problem = HeaderError of string
                   | ResolverError of parent * string
                   | MissingParent of parent
                   | AmbiguousParent of parent * string list
                   | UnreadableParent of parent * string * string
                   | HashMismatch of parent * string

  (* Compare recorded identities with SHA1 of current parent .dat bytes.
     The bootstrap identity (min, "") needs no artifact or resolution.
     A nonempty min identity is a mismatch. Resolver exceptions are reported
     as ResolverError; callers should normally return Missing or Ambiguous. *)
  val validate : {path : string, resolve : string -> resolution} ->
                 problem list
end
