signature Holdep_tokens =
sig

  exception LEX_ERROR of string
  val file_deps : string -> string Binaryset.set
  val stream_deps : string * TextIO.instream -> string Binaryset.set

end
