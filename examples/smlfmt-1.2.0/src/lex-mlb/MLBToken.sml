(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure MLBToken :>
sig

  datatype reserved =
    Bas
  | Basis
  | Ann
  | UnderscorePrim (** This is MLton-specific *)

  datatype class = SMLPath | MLBPath | Reserved of reserved | SML of Token.class

  type t
  type token = t

  val getSource: token -> Source.t
  val getClass: token -> class

  val isComment: token -> bool
  val isWhitespace: token -> bool
  val isCommentOrWhitespace: token -> bool
  val isSMLPath: token -> bool
  val isMLBPath: token -> bool
  val isStringConstant: token -> bool
  val isBasDecStartToken: token -> bool

  structure Pretoken:
  sig
    type t
    type pretoken = t

    val getSource: pretoken -> Source.t
    val getClass: pretoken -> class

    val make: Source.t -> class -> pretoken
    val reserved: Source.t -> reserved -> pretoken
    val fromSMLPretoken: Token.Pretoken.t -> pretoken

    val makePathFromSource: Source.t -> pretoken option
  (* val makePathFromSourceString: Source.t -> string -> pretoken option *)
  end

  val fromPre: Pretoken.t -> token
  val makeGroup: Pretoken.t Seq.t -> token Seq.t

end =
struct

  datatype reserved =
    Bas
  | Basis
  | Ann
  | UnderscorePrim (** This is MLton-specific *)

  datatype class = SMLPath | MLBPath | Reserved of reserved | SML of Token.class

  type pretoken = class WithSource.t

  type token = {idx: int, context: pretoken Seq.t}
  type t = token

  fun make src class = WithSource.make {value = class, source = src}

  fun reserved src rclass =
    WithSource.make {value = Reserved rclass, source = src}

  fun fromSMLPretoken ptok =
    make (Token.Pretoken.getSource ptok) (SML (Token.Pretoken.getClass ptok))

  fun getClass ({idx, context}: token) =
    WithSource.valOf (Seq.nth context idx)

  fun getSource ({idx, context}: token) =
    WithSource.srcOf (Seq.nth context idx)

  fun isComment tok =
    case getClass tok of
      SML Token.Comment => true
    | _ => false

  fun isWhitespace tok =
    case getClass tok of
      SML Token.Whitespace => true
    | _ => false

  fun isCommentOrWhitespace tok = isComment tok orelse isWhitespace tok

  fun isSMLPath tok =
    case getClass tok of
      SMLPath => true
    | _ => false

  fun isMLBPath tok =
    case getClass tok of
      MLBPath => true
    | _ => false

  fun isStringConstant tok =
    case getClass tok of
      SML Token.StringConstant => true
    | _ => false

  val basDecStartTokens =
    [ SMLPath
    , MLBPath
    , Reserved Basis
    , Reserved Ann
    , Reserved UnderscorePrim
    , SML Token.StringConstant
    , SML (Token.Reserved Token.Open)
    , SML (Token.Reserved Token.Local)
    , SML (Token.Reserved Token.Structure)
    , SML (Token.Reserved Token.Signature)
    , SML (Token.Reserved Token.Functor)
    ]

  fun isBasDecStartToken tok =
    let val c = getClass tok
    in List.exists (fn c' => c' = c) basDecStartTokens
    end


  fun extensionOfPathInSource src =
    let
      fun findDot i =
        if i = 0 then
          NONE
        else
          case Source.nth src (i - 1) of
            #"." => SOME (i - 1)
          | #"/" => NONE
          | _ => findDot (i - 1)
    in
      case findDot (Source.length src) of
        NONE => NONE
      | SOME i =>
          SOME (Source.toString (Source.slice src (i, Source.length src - i)))
    end


  fun makePathFromSource src =
    case extensionOfPathInSource src of
      SOME ".mlb" => SOME (make src MLBPath)
    | SOME ".sml" => SOME (make src SMLPath)
    | SOME ".sig" => SOME (make src SMLPath)
    | SOME ".fun" => SOME (make src SMLPath)
    | _ => NONE


  (* fun makePathFromSourceString src str =
    case OS.Path.ext str of
      SOME "mlb" => SOME (make src MLBPath)
    | SOME "sml" => SOME (make src SMLPath)
    | SOME "sig" => SOME (make src SMLPath)
    | SOME "fun" => SOME (make src SMLPath)
    | _ => NONE *)


  fun makeGroup (s: pretoken Seq.t) : token Seq.t =
    Seq.tabulate (fn i => {idx = i, context = s}) (Seq.length s)

  fun fromPre (t: pretoken) =
    Seq.nth (makeGroup (Seq.singleton t)) 0


  structure Pretoken =
  struct
    type t = pretoken
    type pretoken = t

    fun getClass ptok = WithSource.valOf ptok
    fun getSource ptok = WithSource.srcOf ptok

    val make = make
    val reserved = reserved
    val fromSMLPretoken = fromSMLPretoken

    val makePathFromSource = makePathFromSource
  (* val makePathFromSourceString = makePathFromSourceString *)
  end

end
