signature QFRead =
sig

val inputFile : string -> string
val fileToReader : string -> (unit -> char option)
val fileToReaderEOF : string -> ((unit -> char option) * (unit -> bool))

val fromString : string -> string
val stringToReader : string -> (unit -> char option)

val streamToReader : TextIO.instream -> (unit -> char option)

end
