signature QFRead =
sig

type reader =
     {read : unit -> char option, reset : unit -> unit, eof : unit -> bool}

val inputFile : string -> string
val fromString : bool -> string -> string

val fileToReader : string -> reader
val stringToReader : bool -> string -> reader
val inputToReader : bool -> string -> (int -> string) -> reader
val streamToReader : bool -> string -> TextIO.instream -> reader
(* bool is true if the stream corresponds to an interactive session
   (stdin) or a Script file. In both such situations, the magic >- and
   Theorem-syntax transformations should be performed

   The strings in {input,stream}ToReader allow the specification of the
   filename associated with the stream; the quotation filter will quote
   this name back to the user with the #(FILE) directive.
*)

(* In inputFile and fileToReader, the determination is made on whether or
   not the filename ends in "Script.sml" *)

end
