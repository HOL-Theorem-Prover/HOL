signature HOLFileSys =
sig

  datatype CodeType = datatype HOLFS_dtype.CodeType
  datatype ArticleType = datatype HOLFS_dtype.ArticleType
  datatype File = datatype HOLFS_dtype.File

  val string_part : File -> string
  val toCodeType : string -> CodeType
  val toFile : string -> File
  val codeToString : CodeType -> string
  val articleToString : ArticleType -> string
  val fromFile : File -> string
  val fromFileNoSuf : File -> string
  val file_compare : File * File -> order
  val primary_dependent : File -> File option
  val exists_readable : string -> bool
  val extract_theory : string list -> string option


  val openIn : string -> TextIO.instream
  val inputAll : TextIO.instream -> string
  val inputLine : TextIO.instream -> string option
  val closeIn : TextIO.instream -> unit
  val input : TextIO.instream -> string

  val openOut : string -> TextIO.outstream
  val output : TextIO.outstream * string -> unit
  val flushOut : TextIO.outstream -> unit
  val closeOut : TextIO.outstream -> unit
  val stdErr : TextIO.outstream
  val stdOut : TextIO.outstream

  val stdErr_out : string -> unit (* includes a flush *)
  val print : string -> unit (* to stdOut *)
  val println : string -> unit (* adds \n *)

end
