signature buildutils =
sig

  val help_mesg : string
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

  val cline_selftest : string list -> (int * string list)

  val read_earlier_options : (TextIO.instream -> string option) ->
                             string list
  val write_options : string list -> unit

  datatype buildtype =
           Normal of {kernelspec : string, seqname : string, rest : string list}
         | Clean of string

  val get_cline : {reader : TextIO.instream -> string option,
                   default_seq : string} ->
                  buildtype


end
