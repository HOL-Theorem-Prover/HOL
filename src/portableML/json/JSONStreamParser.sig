signature JSONStreamParser =
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

  (* callback functions for the different parsing events *)
    type 'ctx callbacks = {
        null : 'ctx -> 'ctx,
        boolean : 'ctx * bool -> 'ctx,
        integer : 'ctx * IntInf.int -> 'ctx,
        float : 'ctx * real -> 'ctx,
        string : 'ctx * string -> 'ctx,
        startObject : 'ctx -> 'ctx,
        objectKey : 'ctx * string -> 'ctx,
        endObject : 'ctx -> 'ctx,
        startArray : 'ctx -> 'ctx,
        endArray : 'ctx -> 'ctx,
        error : 'ctx * string -> unit
      }

    val parse : 'ctx callbacks -> (source * 'ctx) -> 'ctx

    val parseFile : 'ctx callbacks -> (string * 'ctx) -> 'ctx

  end
