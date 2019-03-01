signature QFRead =
sig

type reader =
     {read : unit -> char option, reset : unit -> unit, eof : unit -> bool}

val inputFile : string -> string
val fromString : string -> string

val fileToReader : string -> reader
val stringToReader : string -> reader
val streamToReader : bool -> TextIO.instream -> reader
(* bool is true if the stream corresponds to an interactive session
   (stdin) or a Script file. In both such situations, the magic >- and
   Theorem-syntax transformations should be performed *)

end
