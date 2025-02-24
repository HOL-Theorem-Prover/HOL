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
    {keyword: substring, name: substring, attrs: substring, name_attrs: substring}
  val destNameAttrs: substring -> substring * substring
  val fromSS: int * substring -> int * int
  val killEnvelopingSpace: substring -> substring
  val kindToName: bool -> type_kind -> string
  val parseBeginType: int * string -> (int * int -> string -> unit) ->
    {local_: bool, kind: type_kind, keyword: substring, tyname: substring}
  val parseDefinitionPfx: string ->
    {keyword: substring, name: substring, attrs: substring, name_attrs: substring}
  val parseDefnLabel: string ->
    {name: substring option, attrs: substring, name_attrs: substring, tilde: bool}
  val parseInductivePfx: string -> {isCo: bool, keyword: substring, thmname: substring}
  val parseQuoteEqnPfx: string -> {bind: substring, keyword: substring, name: substring}
  val parseQuotePfx: string -> {keyword: substring, name: substring}
  val parseTheoremPfx: string ->
    {isTriv: bool, keyword: substring, thmname: substring, attrs: substring, name_attrs: substring}

  val mkParser:
    {parseError: int * int -> string -> unit, pos: int, read: int -> string} ->
    unit -> topdecl

end

structure ToSML: sig

  type double_reader =
    {read: int -> string, readAt: int -> int -> (int * substring -> unit) -> unit}
  val mkDoubleReader: (int -> string) -> int -> double_reader

  type args = {
    read: int -> string,
    filename: string,
    parseError: int * int -> string -> unit,
    quietOpen: bool
  }

  val mkPullTranslator: args -> unit -> string

  type strcode = {
    aux: string -> unit,
    regular: int * substring -> unit,
    strcode: int * substring -> unit,
    strstr: int * substring -> unit
  }
  val strstr: (string -> unit) -> int * substring -> unit
  val strcode: (string -> unit) -> int * substring -> unit
  val mkStrcode: (string -> unit) -> strcode

  val mkPushTranslatorCore:
    args -> strcode -> {
      doDecl: bool -> int -> Simple.decl -> int,
      feed: unit -> Simple.topdecl,
      finishThmVal: unit -> unit,
      regular: int * int -> unit
    }

  val mkPushTranslator: args -> strcode -> unit -> bool

end

type reader = {read : unit -> char option, eof : unit -> bool}
type args = {quietOpen: bool}

val inputFile : args -> string -> string
val fromString : args -> string -> string

val fileToReader : args -> string -> reader
val stringToReader : args -> string -> reader
val inputToReader : args -> string -> (int -> string) -> reader
val streamToReader : args -> string -> TextIO.instream -> reader

end
