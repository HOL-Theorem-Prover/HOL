signature HolParser =
sig

structure Simple: sig

  datatype decl = datatype HolLex.UserDeclarations.decl
  datatype decls = datatype HolLex.UserDeclarations.decls
  datatype antiq = datatype HolLex.UserDeclarations.antiq
  datatype qdecl = datatype HolLex.UserDeclarations.qdecl
  datatype qbody = datatype HolLex.UserDeclarations.qbody

  datatype topdecl
    = TopDecl of decl
    | EOF of int

  datatype type_kind =
      OverloadKind of {by_nametype: bool, inferior: bool}
    | TypeKind of {pp: bool}

  val destAttrs: substring -> (substring * substring list) list
  val destMLThmBinding: substring ->
    {attrs: substring, keyword: substring, name: substring, name_attrs: substring}
  val destNameAttrs: substring -> substring * substring
  val fromSS: int * substring -> int * int
  val killEnvelopingSpace: substring -> substring
  val kindToName: bool -> type_kind -> string
  val parseBeginType: int * string -> (int * int -> string -> unit) ->
    {attrs: unit, keyword: substring, kind: type_kind, local_: bool, tyname: substring}
  val parseDefinitionPfx: string ->
    {attrs: substring, keyword: substring, name: substring, name_attrs: substring}
  val parseDefnLabel: string ->
    {attrs: substring, name: (substring * bool) option, name_attrs: substring}
  val parseInductivePfx: string -> {isCo: bool, keyword: substring, thmname: substring}
  val parseQuoteEqnPfx: string -> {bind: substring, keyword: substring, name: substring}
  val parseQuotePfx: string -> {keyword: substring, name: substring}
  val parseTheoremPfx: string ->
    {attrs: substring, isTriv: bool, keyword: substring, name_attrs: substring, thmname: substring}

  val mkParser:
    {parseError: int * int -> string -> unit, pos: int, read: int -> string} ->
    unit -> topdecl

end

structure ToSML: sig

  type double_reader =
    {read: int -> string, readAt: int -> int -> (int * substring -> unit) -> unit}
  val mkDoubleReader: (int -> string) -> int -> double_reader

  val mkPullTranslator:
    {parseError: int * int -> string -> unit, read: int -> string} ->
    unit -> string

  type strcode = {
    aux: string -> unit,
    regular: int * substring -> unit,
    strcode: int * substring -> unit,
    strstr: int * substring -> unit
  }
  val mkStrcode: (string -> unit) -> strcode
  val mkPushTranslator:
    {parseError: int * int -> string -> unit, read: int -> string} ->
    strcode -> unit -> bool

end

type reader = {read : unit -> char option, eof : unit -> bool}

val inputFile : string -> string
val fromString : bool -> string -> string

val fileToReader : string -> reader
val stringToReader : bool -> string -> reader
val inputToReader : bool -> (int -> string) -> reader
val streamToReader : bool -> TextIO.instream -> reader
(* bool is true if the stream corresponds to an interactive session
   (stdin) or a Script file. In both such situations, the magic >- and
   Theorem-syntax transformations should be performed *)

(* In inputFile and fileToReader, the determination is made on whether or
   not the filename ends in "Script.sml" *)

end
