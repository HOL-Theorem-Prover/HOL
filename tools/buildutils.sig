signature buildutils =
sig

  val normPath : string -> string
  val fullPath : string list -> string
  val quote : string -> string
  val die : string -> 'a
  val warn : string -> unit

  val read_buildsequence :
      (string -> Substring.substring) -> (TextIO.instream -> string option) ->
      string -> (string * int) list

end
