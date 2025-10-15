signature HolParser =
sig


structure ToSML: sig

  type args = {
    read: int -> string,
    filename: string,
    parseError: int * int -> string -> unit,
    quietOpen: bool
  }

  val mkPullTranslator: args -> unit -> string

end

type reader = {read : unit -> char option, eof : unit -> bool}
type args = {quietOpen: bool}

val inputFile : args -> string -> string
val fromString : args -> string -> string

val fileToReader : args -> string -> reader
val stringToReader : args -> string -> reader
val inputToReader : args -> string -> (int -> string) -> reader
val streamToReader : args -> string -> TextIO.instream -> reader

end
