signature JSONParser =
sig

  (* abstract type of JSON input *)
  type source = JSONSource.source

  (* open a text input stream as a source *)
  val openStream : TextIO.instream -> source

  (* open a text file as a source *)
  val openFile : string -> source

  (* open a string as a source *)
  val openString : string -> source

  (* close a source *)
  val close : source -> unit

  val parse : source -> JSON.value

  val parseFile : string -> JSON.value

end
