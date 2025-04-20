(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Token :>
sig

  datatype reserved =
  (** ============ core ============ *)
    Abstype
  | And
  | Andalso
  | As
  | Case
  | Datatype
  | Do
  | Else
  | End
  | Exception
  | Fn
  | Fun
  | Handle
  | If
  | In
  | Infix
  | Infixr
  | Let
  | Local
  | Nonfix
  | Of
  | Op
  | Open
  | Orelse
  | Raise
  | Rec
  | Then
  | Type
  | Val
  | With
  | Withtype
  | While
  | OpenParen
  | CloseParen
  | OpenSquareBracket
  | CloseSquareBracket
  | OpenCurlyBracket
  | CloseCurlyBracket
  | Comma
  | Colon
  | Semicolon
  | DotDotDot
  | Underscore
  | Bar
  | Equal
  | FatArrow
  | Arrow
  | Hash
  (** ============ modules ============ *)
  | Eqtype
  | Functor
  | Include
  | Sharing
  | Sig
  | Signature
  | Struct
  | Structure
  | Where
  | ColonArrow

  datatype class =
    Comment
  | MLtonReserved
  | Reserved of reserved
  | IntegerConstant
  | WordConstant
  | RealConstant
  | CharConstant
  | StringConstant
  | Identifier
  | LongIdentifier
  | Whitespace

  type token
  type t = token

  val same: token * token -> bool
  val sameExceptForMultilineIndentation: {tabWidth: int}
                                         -> token * token
                                         -> bool

  val getClass: token -> class
  val getSource: token -> Source.t

  val toString: token -> string
  val reservedToString: reserved -> string
  val classToString: class -> string

  val nextToken: token -> token option
  val prevToken: token -> token option
  val nextTokenNotCommentOrWhitespace: token -> token option
  val prevTokenNotCommentOrWhitespace: token -> token option
  val hasCommentsAfter: token -> bool
  val hasCommentsBefore: token -> bool
  val commentsBefore: token -> token Seq.t
  val commentsAfter: token -> token Seq.t
  val commentsOrWhitespaceBefore: token -> token Seq.t
  val commentsOrWhitespaceAfter: token -> token Seq.t

  (** how many lines apart are these tokens?
    * raises Fail if not from the same file.
    *)
  val lineDifference: token * token -> int
  val effectiveOffset: {tabWidth: int} -> token -> int
  val spansMultipleLines: token -> bool

  val isReserved: token -> bool
  val isStringConstant: token -> bool
  val isComment: token -> bool
  val isWhitespace: token -> bool
  val isCommentOrWhitespace: token -> bool
  val isComma: token -> bool
  val isAndalso: token -> bool
  val isOrelse: token -> bool
  val isStar: token -> bool
  val isOpenParen: token -> bool
  val isSemicolon: token -> bool
  val isIdentifier: token -> bool
  val isValueIdentifier: token -> bool
  val isValueIdentifierNoEqual: token -> bool
  val isLongIdentifier: token -> bool
  val isSymbolicIdentifier: token -> bool
  val isMaybeLongIdentifier: token -> bool
  val isStrIdentifier: token -> bool
  val isMaybeLongStrIdentifier: token -> bool
  val isTyVar: token -> bool
  val isTyCon: token -> bool
  val isMaybeLongTyCon: token -> bool
  val isPatternConstant: token -> bool
  val isConstant: token -> bool
  val isHexIntegerConstant: token -> bool
  val isDecimalIntegerConstant: token -> bool
  val isRecordLabel: token -> bool
  val isDecStartToken: token -> bool
  val isStrDecStartToken: token -> bool
  val isFunDecStartToken: token -> bool
  val isSigDecStartToken: token -> bool
  val isSigSpecStartToken: token -> bool
  val isAtPatStartToken: token -> bool
  val endsCurrentExp: token -> bool

  (** Tokens have to be constructed from a group of "pretokens". This makes it
    * possible to implement functions like nextToken and prevToken, above.
    *)
  structure Pretoken:
  sig
    type t
    type pretoken = t

    val getSource: pretoken -> Source.t
    val getClass: pretoken -> class

    val make: Source.t -> class -> pretoken
    val reserved: Source.t -> reserved -> pretoken
    val mltonReserved: Source.t -> pretoken
    val longIdentifier: Source.t -> pretoken
    val identifier: Source.t -> pretoken
    val reservedOrIdentifier: Source.t -> pretoken
  end

  val fromPre: Pretoken.t -> token
  val makeGroup: Pretoken.t Seq.t -> token Seq.t

end =
struct
  local open Source in end

  datatype reserved =
  (** ============ core ============ *)
    Abstype
  | And
  | Andalso
  | As
  | Case
  | Datatype
  | Do
  | Else
  | End
  | Exception
  | Fn
  | Fun
  | Handle
  | If
  | In
  | Infix
  | Infixr
  | Let
  | Local
  | Nonfix
  | Of
  | Op
  | Open
  | Orelse
  | Raise
  | Rec
  | Then
  | Type
  | Val
  | With
  | Withtype
  | While
  | OpenParen
  | CloseParen
  | OpenSquareBracket
  | CloseSquareBracket
  | OpenCurlyBracket
  | CloseCurlyBracket
  | Comma
  | Colon
  | Semicolon
  | DotDotDot
  | Underscore
  | Bar
  | Equal
  | FatArrow
  | Arrow
  | Hash
  (** ============ modules ============ *)
  | Eqtype
  | Functor
  | Include
  | Sharing
  | Sig
  | Signature
  | Struct
  | Structure
  | Where
  | ColonArrow

  datatype class =
    Comment
  | MLtonReserved
  | Reserved of reserved
  | IntegerConstant
  | WordConstant
  | RealConstant
  | CharConstant
  | StringConstant
  | Identifier
  | LongIdentifier
  | Whitespace

  type pretoken = class WithSource.t

  type token = {idx: int, context: pretoken Seq.t}
  type t = token

  fun make src class = WithSource.make {value = class, source = src}

  fun reserved src rclass =
    WithSource.make {value = Reserved rclass, source = src}

  fun mltonReserved src = WithSource.make {value = MLtonReserved, source = src}

  fun longIdentifier src =
    WithSource.make {value = LongIdentifier, source = src}

  fun identifier src = WithSource.make {value = Identifier, source = src}

  fun getClass ({idx, context}: token) =
    WithSource.valOf (Seq.nth context idx)

  fun getSource ({idx, context}: token) =
    WithSource.srcOf (Seq.nth context idx)

  fun lineDifference (tok1, tok2) =
    let
      val src1 = getSource tok1
      val src2 = getSource tok2
      val {line = end1, ...} = Source.absoluteEnd (getSource tok1)
      val {line = start2, ...} = Source.absoluteStart (getSource tok2)
    in
      if FilePath.sameFile (Source.fileName src1, Source.fileName src2) then
        start2 - end1
      else
        raise Fail "Bug! lineDifference on tokens from different files"
    end

  fun spansMultipleLines tok =
    let
      val {line = lnStart, ...} = Source.absoluteStart (getSource tok)
      val {line = lnEnd, ...} = Source.absoluteEnd (getSource tok)
    in
      lnEnd <> lnStart
    end

  fun toString tok =
    let val src = getSource tok
    in CharVector.tabulate (Source.length src, Source.nth src)
    end

  fun tryReserved src =
    let
      val str = CharVector.tabulate (Source.length src, Source.nth src)
      fun r rclass = SOME rclass
    in
      case str of
      (** Symbolic *)
        ":" => r Colon
      | ":>" => r ColonArrow
      | "|" => r Bar
      | "=" => r Equal
      | "=>" => r FatArrow
      | "->" => r Arrow
      | "#" => r Hash
      (** Core *)
      | "abstype" => r Abstype
      | "and" => r And
      | "andalso" => r Andalso
      | "as" => r As
      | "case" => r Case
      | "datatype" => r Datatype
      | "do" => r Do
      | "else" => r Else
      | "end" => r End
      | "exception" => r Exception
      | "fn" => r Fn
      | "fun" => r Fun
      | "handle" => r Handle
      | "if" => r If
      | "in" => r In
      | "infix" => r Infix
      | "infixr" => r Infixr
      | "let" => r Let
      | "local" => r Local
      | "nonfix" => r Nonfix
      | "of" => r Of
      | "op" => r Op
      | "open" => r Open
      | "orelse" => r Orelse
      | "raise" => r Raise
      | "rec" => r Rec
      | "then" => r Then
      | "type" => r Type
      | "val" => r Val
      | "with" => r With
      | "withtype" => r Withtype
      | "while" => r While
      (** Modules *)
      | "eqtype" => r Eqtype
      | "functor" => r Functor
      | "include" => r Include
      | "sharing" => r Sharing
      | "sig" => r Sig
      | "signature" => r Signature
      | "struct" => r Struct
      | "structure" => r Structure
      | "where" => r Where

      | _ => NONE (* (print ("not reserved: " ^ other ^ "\n"); NONE) *)
    end

  fun reservedToString rc =
    case rc of
    (** Symbolic *)
      Colon => ":"
    | ColonArrow => ":>"
    | Bar => "|"
    | Equal => "="
    | FatArrow => "=>"
    | Arrow => "->"
    | Hash => "#"
    | OpenParen => "("
    | CloseParen => ")"
    | OpenSquareBracket => "["
    | CloseSquareBracket => "]"
    | OpenCurlyBracket => "{"
    | CloseCurlyBracket => "}"
    | Semicolon => ";"
    | Underscore => "_"
    | DotDotDot => "..."
    | Comma => ","
    (** Core *)
    | Abstype => "abstype"
    | And => "and"
    | Andalso => "andalso"
    | As => "as"
    | Case => "case"
    | Datatype => "datatype"
    | Do => "do"
    | Else => "else"
    | End => "end"
    | Exception => "exception"
    | Fn => "fn"
    | Fun => "fun"
    | Handle => "handle"
    | If => "if"
    | In => "in"
    | Infix => "infix"
    | Infixr => "infixr"
    | Let => "let"
    | Local => "local"
    | Nonfix => "nonfix"
    | Of => "of"
    | Op => "op"
    | Open => "open"
    | Orelse => "orelse"
    | Raise => "raise"
    | Rec => "rec"
    | Then => "then"
    | Type => "type"
    | Val => "val"
    | With => "with"
    | Withtype => "withtype"
    | While => "while"
    (** Modules *)
    | Eqtype => "eqtype"
    | Functor => "functor"
    | Include => "include"
    | Sharing => "sharing"
    | Sig => "sig"
    | Signature => "signature"
    | Struct => "struct"
    | Structure => "structure"
    | Where => "where"


  fun reservedOrIdentifier src =
    case tryReserved src of
      SOME r => reserved src r
    | NONE => identifier src

  fun isReserved (tok: token) =
    case getClass tok of
      Reserved _ => true
    | _ => false

  fun isStringConstant tok =
    case getClass tok of
      StringConstant => true
    | _ => false

  fun isComment tok =
    case getClass tok of
      Comment => true
    | _ => false

  fun isWhitespace tok =
    case getClass tok of
      Whitespace => true
    | _ => false

  fun isCommentOrWhitespace tok = isComment tok orelse isWhitespace tok

  fun isComma tok =
    case getClass tok of
      Reserved Comma => true
    | _ => false

  fun isAndalso tok =
    case getClass tok of
      Reserved Andalso => true
    | _ => false

  fun isOrelse tok =
    case getClass tok of
      Reserved Orelse => true
    | _ => false

  fun isStar tok =
    let val src = getSource tok
    in Source.length src = 1 andalso Source.nth src 0 = #"*"
    end

  fun isOpenParen tok =
    case getClass tok of
      Reserved OpenParen => true
    | _ => false

  fun isSemicolon tok =
    case getClass tok of
      Reserved Semicolon => true
    | _ => false

  fun isIdentifier tok =
    case getClass tok of
      Identifier => true
    | _ => false

  fun isValueIdentifier tok =
    case getClass tok of
      Identifier => Source.nth (getSource tok) 0 <> #"'"
    | Reserved Equal => true (** annoying edge case *)
    | _ => false

  fun isValueIdentifierNoEqual tok =
    case getClass tok of
      Identifier => Source.nth (getSource tok) 0 <> #"'"
    | _ => false

  fun isLongIdentifier tok =
    case getClass tok of
      LongIdentifier => true
    | _ => false

  fun isMaybeLongIdentifier tok =
    case getClass tok of
      Identifier => true
    | LongIdentifier => true
    | Reserved Equal => true (** annoying edge case *)
    | MLtonReserved => true (** another special case... *)
    | _ => false

  fun isSymbolicIdentifier tok =
    let
      val src = getSource tok
      val isSymb = LexUtils.isSymbolic (Source.nth src (Source.length src - 1))
    in
      case getClass tok of
        Identifier => isSymb
      | LongIdentifier => isSymb
      | Reserved Equal => true (* annoying edge case *)
      | _ => false
    end

  (** alphanumeric, not starting with prime *)
  fun isStrIdentifier tok =
    let
      val src = getSource tok
    in
      case getClass tok of
        Identifier =>
          Source.nth src 0 <> #"'"
          andalso
          Util.all (0, Source.length src) (fn i =>
            LexUtils.isAlphaNumPrimeOrUnderscore (Source.nth src i))

      | _ => false
    end

  fun isMaybeLongStrIdentifier tok =
    isStrIdentifier tok orelse isLongIdentifier tok

  (** tyvars are small identifiers that begin with a prime *)
  fun isTyVar tok =
    case getClass tok of
      Identifier => Source.nth (getSource tok) 0 = #"'"
    | _ => false

  (** tycons are maybe long identifiers that do not begin with a prime,
    * and are not "*"
    *)
  fun isTyCon tok =
    case getClass tok of
      Identifier =>
        not (isStar tok) andalso (Source.nth (getSource tok) 0 <> #"'")
    | _ => false

  fun isMaybeLongTyCon tok = isTyCon tok orelse isLongIdentifier tok

  (** SML permits ints, strings, words, and chars as constants in patterns,
    * but NOT reals.
    *)
  fun isPatternConstant tok =
    case getClass tok of
      IntegerConstant => true
    | WordConstant => true
    | StringConstant => true
    | CharConstant => true
    | _ => false

  fun isConstant tok =
    case getClass tok of
      IntegerConstant => true
    | WordConstant => true
    | StringConstant => true
    | CharConstant => true
    | RealConstant => true
    | _ => false

  fun isHexIntegerConstant tok =
    let
      val src = getSource tok
    in
      case getClass tok of
        IntegerConstant =>
          Source.length src > 2 andalso Source.nth src 0 = #"0"
          andalso Source.nth src 1 = #"x"
      | _ => false
    end

  fun isDecimalIntegerConstant tok =
    case getClass tok of
      IntegerConstant => not (isHexIntegerConstant tok)
    | _ => false

  fun isRecordLabel tok =
    case getClass tok of
      Identifier => Source.nth (getSource tok) 0 <> #"'"
    | IntegerConstant => Source.nth (getSource tok) 0 <> #"0"
    | _ => false

  val decStartTokens =
    [ Abstype
    , Datatype
    , Exception
    , Infix
    , Infixr
    , Nonfix
    , Type
    , Val
    , Fun
    , Open
    , Local
    ]

  val strDecStartTokens = [Structure, Local]

  val sigDecStartTokens = [Signature]

  val sigSpecStartTokens =
    [Val, Type, Eqtype, Datatype, Exception, Structure, Include]

  fun isDecStartToken tok =
    case getClass tok of
      Reserved rc => List.exists (fn rc' => rc = rc') decStartTokens
    | _ => false

  fun isStrDecStartToken tok =
    case getClass tok of
      Reserved rc => List.exists (fn rc' => rc = rc') strDecStartTokens
    | _ => false

  fun isFunDecStartToken tok =
    case getClass tok of
      Reserved Functor => true
    | _ => false

  fun isSigDecStartToken tok =
    case getClass tok of
      Reserved rc => List.exists (fn rc' => rc = rc') sigDecStartTokens
    | _ => false

  fun isSigSpecStartToken tok =
    case getClass tok of
      Reserved rc => List.exists (fn rc' => rc = rc') sigSpecStartTokens
    | _ => false

  fun classToString class =
    case class of
      Comment => "comment"
    | Reserved _ => "reserved"
    | IntegerConstant => "integer"
    | WordConstant => "word"
    | RealConstant => "real"
    | StringConstant => "string"
    | CharConstant => "char"
    | Identifier => "identifier"
    | LongIdentifier => "long identifier"
    | MLtonReserved => "MLton reserved"
    | Whitespace => "whitespace"


  (** effective offset of the beginning of this token within its line,
    * counting tab-widths appropriately.
    *)
  fun effectiveOffset {tabWidth: int} tok =
    let
      val src = getSource tok
      val {col, line = lineNum} = Source.absoluteStart src
      val len = col - 1
      val charsBeforeOnSameLine = Source.take (Source.wholeLine src lineNum) len
      fun loop effOff i =
        if i >= len then
          effOff
        else if #"\t" = Source.nth charsBeforeOnSameLine i then
          (* advance up to next tabstop *)
          loop (effOff + tabWidth - effOff mod tabWidth) (i + 1)
        else
          loop (effOff + 1) (i + 1)
    in
      loop 0 0
    end


  (** Check that the text of t1 exactly matches the text of t2. Useful for
    * comparing identifier names, e.g. for infix lookup.
    *)
  fun same (t1, t2) =
    let
      val s1 = getSource t1
      val s2 = getSource t2
      val n = Source.length s1

      fun loop i =
        if i >= n then true
        else (Source.nth s1 i = Source.nth s2 i) andalso loop (i + 1)
    in
      n = Source.length s2 andalso loop 0
    end


  fun piecesAsStrings {tabWidth} tok =
    let
      val effectiveOffset = effectiveOffset {tabWidth = tabWidth} tok

      fun strip line =
        let
          val {result, ...} =
            StripEffectiveWhitespace.strip
              {tabWidth = tabWidth, removeAtMost = effectiveOffset} line
        in
          result
        end

      val src = getSource tok
      val asString = CharVector.tabulate (Source.length src, Source.nth src)
    in
      Seq.map (fn (i, j) => strip (String.substring (asString, i, j - i)))
        (Source.lineRanges src)
    end


  (** Check that t1 and t2 have exactly the same text, similar to function
    * `same` above, except that this function also handles the possibility of a
    * multiline token (i.e. a multiline comment or string constant) whose
    * indentation might be different between t1 and t2 but otherwise is
    * identical.
    *)
  fun sameExceptForMultilineIndentation {tabWidth: int} (t1, t2) =
    if
      not
        (isComment t1 orelse isStringConstant t1 orelse isComment t2
         orelse isStringConstant t2)
    then
      same (t1, t2)
    else
      Seq.equal op=
        ( piecesAsStrings {tabWidth = tabWidth} t1
        , piecesAsStrings {tabWidth = tabWidth} t2
        )


  fun isAtPatStartToken tok =
    case getClass tok of
      Comment => false
    | Reserved rc =>
        List.exists (fn rc' => rc = rc')
          [OpenParen, OpenSquareBracket, OpenCurlyBracket, Underscore, Op]
    | _ => true


  (** This is used in Parser.consume_afterExp, to see if we should stop parsing
    * the current expression and pop up to the previous context.
    *)
  fun endsCurrentExp tok =
    isDecStartToken tok orelse isStrDecStartToken tok
    orelse isSigDecStartToken tok orelse isFunDecStartToken tok
    orelse
    case getClass tok of
      Reserved rc =>
        List.exists (fn rc' => rc = rc')
          [ CloseParen
          , CloseSquareBracket
          , CloseCurlyBracket
          , Comma
          , Semicolon
          , Bar
          , Then
          , Else
          , Do
          , Of
          , And
          , In
          , End
          ]
    | _ => false


  fun makeGroup (s: pretoken Seq.t) : token Seq.t =
    Seq.tabulate (fn i => {idx = i, context = s}) (Seq.length s)

  fun fromPre (t: pretoken) =
    Seq.nth (makeGroup (Seq.singleton t)) 0

  fun nextToken ({idx = i, context}: token) =
    if i + 1 < Seq.length context then SOME {idx = i + 1, context = context}
    else NONE

  fun prevToken ({idx = i, context}: token) =
    if i > 0 then SOME {idx = i - 1, context = context} else NONE

  fun prevTokenNotCommentOrWhitespace tok =
    case prevToken tok of
      NONE => NONE
    | SOME t' =>
        if isCommentOrWhitespace t' then prevTokenNotCommentOrWhitespace t'
        else SOME t'

  fun nextTokenNotCommentOrWhitespace tok =
    case nextToken tok of
      NONE => NONE
    | SOME t' =>
        if isCommentOrWhitespace t' then nextTokenNotCommentOrWhitespace t'
        else SOME t'

  fun commentsOrWhitespaceBefore tok =
    let
      fun loop acc t =
        case prevToken t of
          SOME t' =>
            if isCommentOrWhitespace t' then loop (t' :: acc) t' else acc
        | NONE => acc
    in
      Seq.fromList (loop [] tok)
    end

  fun commentsOrWhitespaceAfter tok =
    let
      fun loop acc t =
        case nextToken t of
          SOME t' =>
            if isCommentOrWhitespace t' then loop (t' :: acc) t' else acc
        | NONE => acc
    in
      Seq.fromRevList (loop [] tok)
    end


  fun hasCommentsBefore t =
    case prevToken t of
      SOME t' =>
        isComment t' orelse (isWhitespace t' andalso hasCommentsBefore t')
    | NONE => false


  fun hasCommentsAfter t =
    case nextToken t of
      SOME t' =>
        isComment t' orelse (isWhitespace t' andalso hasCommentsAfter t')
    | NONE => false


  fun commentsBefore tok =
    let
      fun loop acc t =
        case prevToken t of
          SOME t' =>
            if isWhitespace t' then loop acc t'
            else if isComment t' then loop (t' :: acc) t'
            else acc
        | NONE => acc
    in
      Seq.fromList (loop [] tok)
    end


  fun commentsAfter tok =
    let
      fun loop acc t =
        case nextToken t of
          SOME t' =>
            if isWhitespace t' then loop acc t'
            else if isComment t' then loop (t' :: acc) t'
            else acc
        | NONE => acc
    in
      Seq.fromRevList (loop [] tok)
    end


  structure Pretoken =
  struct
    type t = pretoken
    type pretoken = pretoken

    fun getSource p = WithSource.srcOf p
    fun getClass p = WithSource.valOf p

    val make = make
    val reserved = reserved
    val mltonReserved = mltonReserved
    val longIdentifier = longIdentifier
    val identifier = identifier
    val reservedOrIdentifier = reservedOrIdentifier
  end

end
