signature Holdep_tokens =
sig

  exception LEX_ERROR of string
  type result = (string,int) Binarymap.dict
  val file_deps : string -> result
  val stream_deps : string * TextIO.instream -> result
  val reader_deps : string * (unit -> char option) -> result

end
