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


end
