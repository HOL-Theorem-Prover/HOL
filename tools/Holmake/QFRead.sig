signature QFRead =
sig

val inputFile : string -> string
val fileToReader : string -> (unit -> char option)
val fileToReaderEOF : string -> ((unit -> char option) * (unit -> bool))

val fromString : string -> string
val stringToReader : string -> (unit -> char option)

val streamToReader : bool -> TextIO.instream -> (unit -> char option)
(* bool is true if the stream corresponds to an interactive session (stdin)
   or a Script file. In both such situations, the magic >- transformations
   should be performed *)

end
