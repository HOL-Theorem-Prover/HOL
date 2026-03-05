signature HolParser =
sig

type fileline = {file: string, line: int, col: int}

structure ToSML: sig

  type args = {
    read: int -> string,
    filename: string,
    parseError: string -> int * int -> string -> unit,
    quietOpen: bool
  }

  type printer = {str: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}

  val mkPushTranslator: args -> printer -> {fileline: int -> fileline, push: unit -> bool}
  val mkPullTranslator: args -> {fileline: unit -> fileline, read: unit -> string}

end

type reader = {read: unit -> char option, fileline: unit -> fileline, eof: unit -> bool}
type args = {quietOpen: bool}

val inputFile : args -> string -> string
val fromString : args -> string -> string

val fileToReader : args -> string -> reader
val stringToReader : args -> string -> reader
val inputToReader : args -> string -> (int -> string) -> reader
val streamToReader : args -> string -> TextIO.instream -> reader

end
