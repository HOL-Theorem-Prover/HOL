signature buildutils =
sig

  val normPath : string -> string
  val fullPath : string list -> string
  val quote : string -> string
  val die : string -> 'a
  val warn : string -> unit

  val read_buildsequence :
      { ssfull : string -> Substring.substring,
        inputLine : TextIO.instream -> string option,
        kernelpath : string } ->
      string -> (string * int) list

end
