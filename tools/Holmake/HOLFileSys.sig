signature HOLFileSys =
sig

  datatype CodeType = datatype HOLFS_dtype.CodeType
  datatype ArticleType = datatype HOLFS_dtype.ArticleType
  datatype File = datatype HOLFS_dtype.File
  type dirstream
  exception DirNotFound

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
  val openAppend : string -> TextIO.outstream
  val output : TextIO.outstream * string -> unit
  val flushOut : TextIO.outstream -> unit
  val closeOut : TextIO.outstream -> unit
  val stdErr : TextIO.outstream
  val stdOut : TextIO.outstream

  val stdErr_out : string -> unit (* includes a flush *)
  val print : string -> unit (* to stdOut *)
  val println : string -> unit (* adds \n *)

  val access : string * OS.FileSys.access_mode list -> bool
  val remove : string -> unit
  val rmDir : string -> unit
  val A_READ : OS.FileSys.access_mode
  val A_WRITE : OS.FileSys.access_mode
  val A_EXEC : OS.FileSys.access_mode
  val modTime : string -> Time.time
  val setTime : string * Time.time option -> unit

  val isLink : string -> bool
  val isDir : string -> bool
  val getDir : unit -> string
  val chDir : string -> unit
  val mkDir : string -> unit
  val rename : {old : string, new : string} -> unit
  val openDir : string -> dirstream
  val readDir : dirstream -> string option
  val closeDir : dirstream -> unit

  val read_files : {dirname: string} -> (string -> bool) -> (string -> unit) ->
                   unit
  val read_files_with_objs :
      {dirname: string} -> (string -> bool) -> (string -> unit) ->
      unit

end
