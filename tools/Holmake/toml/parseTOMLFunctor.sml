(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)

(* functor's input signature *)
signature TOML_VALUE =
sig
  type value
  type table
  structure Integer:
  sig
    type int
    val + : int * int -> int
    val * : int * int -> int
    val fromInt: Int.int -> int
    val fromString: string -> int option
  end
  val string: string -> value
  val integer: Integer.int -> value
  val float: string -> value
  val bool: bool -> value
  val datetime: string -> value
  val localDatetime: string -> value
  val date: string -> value
  val time: string -> value
  val array: value list -> value
  val subtable: table -> value
  val table: (string * value) list -> table
end

(* functor's output signature *)
signature PARSE_TOML =
sig
  type value
  type table
  type path = string list
  val parse: (char, 'strm) StringCvt.reader -> 'strm -> table
  val scan : (char, 'strm) StringCvt.reader -> (table, 'strm) StringCvt.reader
end


functor ParseToml(Handler: TOML_VALUE) :> PARSE_TOML
  where type value = Handler.value
  and type table = Handler.table =
struct
  open parseTOMLUtil
  structure E = TOMLerror
  type value = Handler.value
  type table = Handler.table
  fun UnexpectedEndOfInput expected =
    raise E.ParseError
      (E.UNEXPECTED {encountered = "end of input", expected = expected})
  fun UnexpectedChar (c, expected) =
    raise E.ParseError
      (E.UNEXPECTED {encountered = Char.toString c, expected = expected})
  fun DuplicateKey path =
    raise E.ParseError (E.DUPLICATE_KEY path)
  (*: val parse : (char, 'strm) StringCvt.reader -> 'strm -> table *)
  fun scan (getc: (char, 'strm) StringCvt.reader) =
    let
      (*: val expect : char * 'strm -> 'strm *)
      fun expect (c, strm) =
        case getc strm of
          NONE => UnexpectedEndOfInput (Char.toString c)
        | SOME (c', strm') =>
            if c = c' then strm' else UnexpectedChar (c', Char.toString c)
      (*: val skipWhiteSpace : 'strm -> 'strm *)
      fun skipWhiteSpace strm =
        case getc strm of
          NONE => strm
        | SOME (c, strm') =>
            if c = #" " orelse c = #"\t" then skipWhiteSpace strm' else strm
      (*: val skipWhiteSpaceAndGetc : 'strm -> (char * 'strm) option *)
      (* skipWhiteSpaceAndGetc strm = getc (skipWhiteSpace strm) *)
      fun skipWhiteSpaceAndGetc strm =
        case getc strm of
          SOME (#" ", strm') => skipWhiteSpaceAndGetc strm'
        | SOME (#"\t", strm') => skipWhiteSpaceAndGetc strm'
        | r => r
      (*: val skipUntilNewline : 'strm -> 'strm *)
      fun skipUntilNewline strm =
        case getc strm of
          NONE => strm
        | SOME (#"\n", strm') => strm'
        | SOME (#"\r", strm') => expect (#"\n", strm')
        | SOME (c, strm') =>
            if Char.isCntrl c then UnexpectedChar (c, "printable character")
            else skipUntilNewline strm'
      (*: val skipWhiteSpaceOrComment : 'strm -> 'strm *)
      fun skipWhiteSpaceOrComment strm =
        case getc strm of
          NONE => strm
        | SOME (#"#", strm') => skipUntilNewline strm'
        | SOME (#" ", strm') => skipWhiteSpaceOrComment strm'
        | SOME (#"\t", strm') => skipWhiteSpaceOrComment strm'
        | SOME (#"\r", strm') => expect (#"\n", strm')
        | SOME (#"\n", strm') => strm'
        | SOME (c, _) => UnexpectedChar (c, "whitespace or comment")
      (*: val skipWhiteSpaceOrCommentOrNewlineAndGetc : 'strm -> (char * 'strm) option *)
      fun skipWhiteSpaceOrCommentOrNewlineAndGetc strm =
        case getc strm of
          SOME (#"#", strm') =>
            skipWhiteSpaceOrCommentOrNewlineAndGetc (skipUntilNewline strm')
        | SOME (#" ", strm') => skipWhiteSpaceOrCommentOrNewlineAndGetc strm'
        | SOME (#"\t", strm') => skipWhiteSpaceOrCommentOrNewlineAndGetc strm'
        | SOME (#"\r", strm') =>
            skipWhiteSpaceOrCommentOrNewlineAndGetc (expect (#"\n", strm'))
        | SOME (#"\n", strm') => skipWhiteSpaceOrCommentOrNewlineAndGetc strm'
        | r => r
      (*: val skipOptionalNewline : 'strm -> 'strm *)
      fun skipOptionalNewline strm =
        case getc strm of
          SOME (#"\n", strm') => strm'
        | SOME (#"\r", strm') => expect (#"\n", strm')
        | _ => strm
      (*: val skipWhiteSpaceOrNewline : 'strm -> 'strm *)
      fun skipWhiteSpaceOrNewline strm =
        case getc strm of
          NONE => strm
        | SOME (#"\r", strm') => skipWhiteSpaceOrNewline (expect (#"\n", strm'))
        | SOME (c, strm') =>
            if c = #" " orelse c = #"\t" orelse c = #"\n" then
              skipWhiteSpaceOrNewline strm'
            else
              strm
      (*: val readHexDigit : 'strm -> int * 'strm *)
      fun readHexDigit strm =
        case getc strm of
          NONE => UnexpectedEndOfInput "hexadecimal digit"
        | SOME (c, strm') =>
            if #"0" <= c andalso c <= #"9" then
              (digitToInt c, strm')
            else if #"A" <= c andalso c <= #"F" then
              (Char.ord c - (Char.ord #"A" - 10), strm')
            else if #"a" <= c andalso c <= #"f" then
              (Char.ord c - (Char.ord #"a" - 10), strm')
            else
              UnexpectedChar (c, "hexadecimal digit")
      (*: val readFourHexDigit : 'strm -> int * 'strm *)
      fun readFourHexDigit strm =
        let
          val (c3, strm) = readHexDigit strm
          val (c2, strm) = readHexDigit strm
          val (c1, strm) = readHexDigit strm
          val (c0, strm) = readHexDigit strm
        in
          (((c3 * 16 + c2) * 16 + c1) * 16 + c0, strm)
        end
      local
        fun go (accum, strm) =
          case getc strm of
            NONE => UnexpectedEndOfInput "closing quote"
          | SOME (#"\"", strm') => (implodeRev accum, strm')
          | SOME (#"\\", strm') =>
              (case getc strm' of
                 NONE => UnexpectedEndOfInput "escape sequence"
               | SOME (#"\"", strm'') => go (#"\"" :: accum, strm'')
               | SOME (#"\\", strm'') => go (#"\\" :: accum, strm'')
               | SOME (#"b", strm'') => go (#"\b" :: accum, strm'')
               | SOME (#"f", strm'') => go (#"\f" :: accum, strm'')
               | SOME (#"n", strm'') => go (#"\n" :: accum, strm'')
               | SOME (#"r", strm'') => go (#"\r" :: accum, strm'')
               | SOME (#"t", strm'') => go (#"\t" :: accum, strm'')
               | SOME (#"u", strm'') =>
                   let val (i, strm''') = readFourHexDigit strm''
                   in go (revAppendUtf8 (Word.fromInt i, accum), strm''')
                   end
               | SOME (#"U", strm'') =>
                   let
                     val (hi, strm''') = readFourHexDigit strm''
                     val (lo, strm'''') = readFourHexDigit strm'''
                   in
                     if hi > 0x0010 then
                       raise E.ParseError E.INVALID_UNICODE_SCALAR
                     else
                       ();
                     go
                       ( revAppendUtf8 (Word.fromInt (hi * 65536 + lo), accum)
                       , strm''''
                       )
                   end
               | SOME (c, _) => UnexpectedChar (c, "escape sequence"))
          | SOME (c, strm') =>
              if (c < #" " andalso c <> #"\t") orelse c = #"\127" then
                UnexpectedChar (c, "printable character")
              else
                go (c :: accum, strm')
      in
        (*: val readBasicString : 'strm -> string * 'strm *)
        fun readBasicString strm = go ([], strm)
      end
      fun checkAllowedChar c =
        if (c < #" " andalso c <> #"\t" andalso c <> #"\n") orelse c = #"\127" then
          UnexpectedChar (c, "printable character")
        else
          c
      local
        fun go (accum, strm) =
          case getc strm of
            NONE => UnexpectedEndOfInput "closing triple quote"
          | SOME (#"\\", strm') => escape (accum, strm')
          | SOME (#"\"", strm') =>
              (case getc strm' of
                 SOME (#"\"", strm'') =>
                   (case getc strm'' of
                      SOME (#"\"", strm''') =>
                        (case getc strm''' of
                           SOME (#"\"", strm'''') =>
                             (case getc strm'''' of
                                SOME (#"\"", strm''''') =>
                                  ( implodeRev (#"\"" :: #"\"" :: accum)
                                  , strm'''''
                                  )
                              | _ => (implodeRev (#"\"" :: accum), strm''''))
                         | _ => (implodeRev accum, strm'''))
                    | SOME (#"\\", strm''') =>
                        escape (#"\"" :: #"\"" :: accum, strm''')
                    | SOME (#"\r", strm''') =>
                        go
                          ( #"\n" :: #"\r" :: #"\"" :: #"\"" :: accum
                          , expect (#"\n", strm''')
                          )
                    | SOME (c, strm''') =>
                        go
                          ( checkAllowedChar c :: #"\"" :: #"\"" :: accum
                          , strm'''
                          )
                    | NONE => UnexpectedEndOfInput "closing triple quote")
               | SOME (#"\\", strm'') => escape (#"\"" :: accum, strm'')
               | SOME (#"\r", strm'') =>
                   go (#"\n" :: #"\r" :: #"\"" :: accum, expect (#"\n", strm''))
               | SOME (c, strm''') =>
                   go (checkAllowedChar c :: #"\"" :: accum, strm''')
               | NONE => UnexpectedEndOfInput "closing triple quote")
          | SOME (#"\r", strm') =>
              go (#"\n" :: #"\r" :: accum, expect (#"\n", strm'))
          | SOME (c, strm') => go (checkAllowedChar c :: accum, strm')
        and escape (accum, strm) =
          case getc strm of
            NONE => UnexpectedEndOfInput "escape sequence"
          | SOME (#"\"", strm') => go (#"\"" :: accum, strm')
          | SOME (#"\\", strm') => go (#"\\" :: accum, strm')
          | SOME (#"b", strm') => go (#"\b" :: accum, strm')
          | SOME (#"f", strm') => go (#"\f" :: accum, strm')
          | SOME (#"n", strm') => go (#"\n" :: accum, strm')
          | SOME (#"r", strm') => go (#"\r" :: accum, strm')
          | SOME (#"t", strm') => go (#"\t" :: accum, strm')
          | SOME (#"u", strm') =>
              let val (i, strm'') = readFourHexDigit strm'
              in go (revAppendUtf8 (Word.fromInt i, accum), strm'')
              end
          | SOME (#"U", strm') =>
              let
                val (hi, strm'') = readFourHexDigit strm'
                val (lo, strm''') = readFourHexDigit strm''
              in
                go
                  ( revAppendUtf8 (Word.fromInt (hi * 65536 + lo), accum)
                  , strm'''
                  )
              end
          | SOME (c, strm') =>
              if c = #" " orelse c = #"\t" then
                case skipWhiteSpaceAndGetc strm' of
                  NONE => UnexpectedEndOfInput "newline"
                | SOME (#"\n", strm'') =>
                    go (accum, skipWhiteSpaceOrNewline strm'')
                | SOME (#"\r", strm'') =>
                    go (accum, skipWhiteSpaceOrNewline (expect (#"\n", strm'')))
                | SOME (c', _) => UnexpectedChar (c', "newline")
              else if c = #"\r" then
                go (accum, skipWhiteSpaceOrNewline (expect (#"\n", strm')))
              else if c = #"\n" then
                go (accum, skipWhiteSpaceOrNewline strm')
              else
                UnexpectedChar (c, "escape sequence")
      in
        (*: val readMultilineBasicString : 'strm -> string * 'strm *)
        fun readMultilineBasicString strm = go ([], strm)
      end
      local
        fun go (accum, strm) =
          case getc strm of
            NONE => UnexpectedEndOfInput "closing quote"
          | SOME (#"'", strm') => (implodeRev accum, strm')
          | SOME (c, strm') =>
              if (c < #" " andalso c <> #"\t") orelse c = #"\127" then
                UnexpectedChar (c, "printable character")
              else
                go (c :: accum, strm')
      in
        (*: val readLiteralString : 'strm -> string * 'strm *)
        fun readLiteralString strm = go ([], strm)
      end
      local
        fun go (accum, strm) =
          case getc strm of
            NONE => UnexpectedEndOfInput "closing triple quote"
          | SOME (#"'", strm') =>
              (case getc strm' of
                 SOME (#"'", strm'') =>
                   (case getc strm'' of
                      SOME (#"'", strm''') =>
                        (case getc strm''' of
                           SOME (#"'", strm'''') =>
                             (case getc strm'''' of
                                SOME (#"'", strm''''') =>
                                  ( implodeRev (#"'" :: #"'" :: accum)
                                  , strm'''''
                                  )
                              | _ => (implodeRev (#"'" :: accum), strm''''))
                         | _ => (implodeRev accum, strm'''))
                    | SOME (c, strm''') =>
                        go
                          (checkAllowedChar c :: #"'" :: #"'" :: accum, strm''')
                    | NONE => UnexpectedEndOfInput "closing triple quote")
               | SOME (c, strm'') =>
                   go (checkAllowedChar c :: #"'" :: accum, strm'')
               | NONE => UnexpectedEndOfInput "closing triple quote")
          | SOME (c, strm') => go (checkAllowedChar c :: accum, strm')
      in
        (*: val readMultilineLiteralString : 'strm -> string * 'strm *)
        fun readMultilineLiteralString strm = go ([], strm)
      end
      (*: val readHexInt : Handler.Integer.int * 'strm -> Handler.Integer.int * 'strm *)
      fun readHexInt (accum, strm) =
        case getc strm of
          NONE => UnexpectedEndOfInput "hexadecimal digit"
        | SOME (c, strm') =>
            if #"0" <= c andalso c <= #"9" then
              readHexIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 16)
                    , Handler.Integer.fromInt (digitToInt c)
                    )
                , strm'
                )
            else if #"A" <= c andalso c <= #"F" then
              readHexIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 16)
                    , Handler.Integer.fromInt
                        (Char.ord c - (Char.ord #"A" - 10))
                    )
                , strm'
                )
            else if #"a" <= c andalso c <= #"f" then
              readHexIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 16)
                    , Handler.Integer.fromInt
                        (Char.ord c - (Char.ord #"a" - 10))
                    )
                , strm'
                )
            else
              UnexpectedChar (c, "hexadecimal digit")
      and readHexIntUnderscore (accum, strm) =
        case getc strm of
          NONE => (accum, strm)
        | SOME (#"_", strm') =>
            readHexInt
              ( accum
              , strm'
              ) (* the next character must be a hexadecimal digit *)
        | SOME (c, strm') =>
            if #"0" <= c andalso c <= #"9" then
              readHexIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 16)
                    , Handler.Integer.fromInt (digitToInt c)
                    )
                , strm'
                )
            else if #"A" <= c andalso c <= #"F" then
              readHexIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 16)
                    , Handler.Integer.fromInt
                        (Char.ord c - (Char.ord #"A" - 10))
                    )
                , strm'
                )
            else if #"a" <= c andalso c <= #"f" then
              readHexIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 16)
                    , Handler.Integer.fromInt
                        (Char.ord c - (Char.ord #"a" - 10))
                    )
                , strm'
                )
            else
              (accum, strm)
      (*: val readOctInt : Handler.Integer.int * 'strm -> Handler.Integer.int * 'strm *)
      fun readOctInt (accum, strm) =
        case getc strm of
          NONE => UnexpectedEndOfInput "octal digit"
        | SOME (c, strm') =>
            if #"0" <= c andalso c <= #"7" then
              readOctIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 8)
                    , Handler.Integer.fromInt (digitToInt c)
                    )
                , strm'
                )
            else
              UnexpectedChar (c, "octal digit")
      and readOctIntUnderscore (accum, strm) =
        case getc strm of
          NONE => (accum, strm)
        | SOME (#"_", strm') =>
            readOctInt
              (accum, strm') (* the next character must be a oct digit *)
        | SOME (c, strm') =>
            if #"0" <= c andalso c <= #"7" then
              readOctIntUnderscore
                ( Handler.Integer.+
                    ( Handler.Integer.* (accum, Handler.Integer.fromInt 8)
                    , Handler.Integer.fromInt (digitToInt c)
                    )
                , strm'
                )
            else
              (accum, strm)
      (*: val readBinInt : Handler.Integer.int * 'strm -> Handler.Integer.int * 'strm *)
      fun readBinInt (accum, strm) =
        case getc strm of
          NONE => UnexpectedEndOfInput "binary digit"
        | SOME (#"0", strm') =>
            readBinIntUnderscore
              (Handler.Integer.* (accum, Handler.Integer.fromInt 2), strm')
        | SOME (#"1", strm') =>
            readBinIntUnderscore
              ( Handler.Integer.+
                  ( Handler.Integer.* (accum, Handler.Integer.fromInt 2)
                  , Handler.Integer.fromInt 1
                  )
              , strm'
              )
        | SOME (c, _) => UnexpectedChar (c, "binary digit")
      and readBinIntUnderscore (accum, strm) =
        case getc strm of
          NONE => (accum, strm)
        | SOME (#"_", strm') =>
            readBinInt
              (accum, strm') (* the next character must be a bin digit *)
        | SOME (#"0", strm') =>
            readBinIntUnderscore
              (Handler.Integer.* (accum, Handler.Integer.fromInt 2), strm')
        | SOME (#"1", strm') =>
            readBinIntUnderscore
              ( Handler.Integer.+
                  ( Handler.Integer.* (accum, Handler.Integer.fromInt 2)
                  , Handler.Integer.fromInt 1
                  )
              , strm'
              )
        | SOME (_, _) => (accum, strm)
      (*: val readDecInt : char list * bool * 'strm -> char list * bool * 'strm *)
      fun readDecInt (accum, hadUnderscore, strm) =
        case getc strm of
          NONE => UnexpectedEndOfInput "digit"
        | SOME (c, strm') =>
            if Char.isDigit c then
              readDecIntUnderscore (c :: accum, hadUnderscore, strm')
            else
              UnexpectedChar (c, "digit")
      and readDecIntUnderscore (accum, hadUnderscore, strm) =
        case getc strm of
          NONE => (accum, hadUnderscore, strm)
        | SOME (#"_", strm') => readDecInt (accum, true, strm')
        | SOME (c, strm') =>
            if Char.isDigit c then
              readDecIntUnderscore (c :: accum, hadUnderscore, strm')
            else
              (accum, hadUnderscore, strm)
      (*: val readExpPart : char list * char * 'strm -> value * 'strm *)
      fun readExpPart (accum', e, strm'') =
        let
          val (accum'', _, strm''') =
            case getc strm'' of
              NONE => UnexpectedEndOfInput "exponent part"
            | SOME (#"+", strm''') =>
                readDecInt (#"+" :: e :: accum', false, strm''')
            | SOME (#"-", strm''') =>
                readDecInt (#"-" :: e :: accum', false, strm''')
            | SOME (c, strm''') =>
                if Char.isDigit c then
                  readDecIntUnderscore (c :: e :: accum', false, strm''')
                else
                  UnexpectedChar (c, "digit or sign (+/-)")
        in
          (Handler.float (implodeRev accum''), strm''')
        end
      (*: val readSigned : char * char * 'strm -> value * 'strm *)
      (* dec-int / float *)
      fun readSigned (sign, d0, strm) =
        let
          val (accum, _, strm') = readDecIntUnderscore ([d0, sign], false, strm)
          fun checkPrefixZero () =
            case accum of
              [_, _] => ()
            | _ => if d0 = #"0" then raise E.ParseError E.PREFIX_ZERO else ()

        in
          case getc strm' of
            SOME (#".", strm'') =>
              let
                val () = checkPrefixZero () (* float *)
                val (accum', _, strm''') =
                  readDecInt (#"." :: accum, false, strm'')
              in
                case getc strm''' of
                  SOME (#"e", strm'''') => readExpPart (accum', #"e", strm'''')
                | SOME (#"E", strm'''') => readExpPart (accum', #"E", strm'''')
                | _ => (Handler.float (implodeRev accum'), strm''')
              end
          | SOME (#"e", strm'') =>
              ( checkPrefixZero ()
              ; readExpPart (accum, #"e", strm'')
              ) (* float *)
          | SOME (#"E", strm'') =>
              ( checkPrefixZero ()
              ; readExpPart (accum, #"E", strm'')
              ) (* float *)
          | _ =>
              ( checkPrefixZero ()
              ; ( Handler.integer (Option.valOf
                    (Handler.Integer.fromString (implodeRev accum)))
                , strm'
                )
              ) (* dec-int *)
        end
      fun readTwoDigit (accum, strm) =
        case getc strm of
          NONE => UnexpectedEndOfInput "digit"
        | SOME (c0, strm') =>
            if Char.isDigit c0 then
              case getc strm' of
                NONE => UnexpectedEndOfInput "digit"
              | SOME (c1, strm'') =>
                  if Char.isDigit c1 then
                    ( c1 :: c0 :: accum
                    , digitToInt c0 * 10 + digitToInt c1
                    , strm''
                    )
                  else
                    UnexpectedChar (c1, "digit")
            else
              UnexpectedChar (c0, "digit")
      local
        fun readDigits (accum, strm) =
          case getc strm of
            NONE => (accum, strm)
          | SOME (c, strm') =>
              if Char.isDigit c then readDigits (c :: accum, strm')
              else (accum, strm)
      in
        (*: val readMinSec : char list * 'strm -> char list * 'strm *)
        fun readMinSec (accum, strm) =
          let
            val (accum', min, strm') = readTwoDigit (accum, strm) (* minute *)
            val strm'' = expect (#":", strm')
            val (accum'', sec, strm''') =
              readTwoDigit (#":" :: accum', strm'') (* second *)
          in
            if min < 60 andalso sec <= 60 then ()
            else raise E.ParseError E.INVALID_TIME;
            case getc strm''' of
              SOME (#".", strm'''') =>
                readDigits (#"." :: accum'', strm'''') (* secfrac *)
            | _ => (accum'', strm''')
          end
      end
      fun readTimePart (accum, strm) =
        let
          val (accum', hour, strm') = readTwoDigit (accum, strm)
          val () = if hour < 24 then () else raise E.ParseError E.INVALID_TIME
          val (accum'', strm'') = readMinSec
            (#":" :: accum', expect (#":", strm'))
        in
          case getc strm'' of
            SOME (#"Z", strm''') =>
              ( Handler.datetime (implodeRev (#"Z" :: accum''))
              , strm'''
              ) (* offset-date-time *)
          | SOME (#"z", strm''') =>
              ( Handler.datetime (implodeRev (#"z" :: accum''))
              , strm'''
              ) (* offset-date-time *)
          | SOME (#"+", strm''') =>
              let
                val (accum''', offsetHour, strm'''') =
                  readTwoDigit (#"+" :: accum'', strm''') (* offset-date-time *)
                val strm''''' = expect (#":", strm'''')
                val (accum'''', offsetMin, strm'''''') =
                  readTwoDigit (#":" :: accum''', strm''''')
                val () =
                  if offsetHour < 24 andalso offsetMin < 60 then ()
                  else raise E.ParseError E.INVALID_TIME
              in
                (Handler.datetime (implodeRev accum''''), strm'''''')
              end
          | SOME (#"-", strm''') =>
              let
                val (accum''', offsetHour, strm'''') =
                  readTwoDigit (#"-" :: accum'', strm''') (* offset-date-time *)
                val strm''''' = expect (#":", strm'''')
                val (accum'''', offsetMin, strm'''''') =
                  readTwoDigit (#":" :: accum''', strm''''')
                val () =
                  if offsetHour < 24 andalso offsetMin < 60 then ()
                  else raise E.ParseError E.INVALID_TIME
              in
                (Handler.datetime (implodeRev accum''''), strm'''''')
              end
          | _ =>
              ( Handler.localDatetime (implodeRev accum'')
              , strm''
              ) (* local-date-time *)
        end
      (*: val readDate : char list * int * 'strm -> value * 'strm *)
      (* full-date: offset-date-time / local-date-time / local-date *)
      fun readDate (accum, year, strm) =
        let
          val (accum', month, strm') = readTwoDigit (accum, strm) (* month *)
          val strm'' = expect (#"-", strm')
          val (accum'', mday, strm''') =
            readTwoDigit (accum', strm'') (* mday; range is not checked *)
          val () =
            if isValidDate (year, month, mday) then ()
            else raise E.ParseError E.INVALID_DATE
        in
          case getc strm''' of
            SOME (#"T", strm'''') =>
              readTimePart
                ( #"T" :: accum''
                , strm''''
                ) (* offset-date-time / local-date-time *)
          | SOME (#"t", strm'''') =>
              readTimePart
                ( #"T" :: accum''
                , strm''''
                ) (* offset-date-time / local-date-time *)
          | SOME (#" ", strm'''') =>
              (case getc strm'''' of
                 SOME (c, _) =>
                   if Char.isDigit c then
                     readTimePart
                       ( #"T" :: accum''
                       , strm''''
                       ) (* offset-date-time / local-date-time *)
                   else
                     ( Handler.date (implodeRev accum'')
                     , strm'''
                     ) (* local-date *)
               | _ =>
                   (Handler.date (implodeRev accum''), strm''') (* local-date *))
          | _ => (Handler.date (implodeRev accum''), strm''') (* local-date *)
        end
      (*: val readUnsigned : char * 'strm -> value * 'strm *)
      (* dec-int / float / date-time / date / time *)
      fun readUnsigned (d0, strm) =
        let
          val (revDigits, hadUnderscore, strm') =
            readDecIntUnderscore ([d0], false, strm)
          fun checkPrefixZero () =
            case revDigits of
              [_] => ()
            | _ => if d0 = #"0" then raise E.ParseError E.PREFIX_ZERO else ()
        in
          case (revDigits, hadUnderscore, getc strm') of
            ([d3, d2, d1, _], false, SOME (#"-", strm'')) => (* full-date: offset-date-time / local-date-time / local-date *)
              let
                val year =
                  ((digitToInt d0 * 10 + digitToInt d1) * 10 + digitToInt d2)
                  * 10 + digitToInt d3
              in
                readDate (#"-" :: revDigits, year, strm'')
              end
          | ([d1, d0], false, SOME (#":", strm'')) =>
              let
                val hour = digitToInt d0 * 10 + digitToInt d1
                val () =
                  if hour < 24 then () else raise E.ParseError E.INVALID_TIME
                val (accum, strm''') =
                  readMinSec (#":" :: revDigits, strm'') (* partial-time *)
              in
                (Handler.time (implodeRev accum), strm''')
              end
          | (_, _, SOME (#".", strm'')) =>
              let
                val () = checkPrefixZero () (* float *)
                val (accum, _, strm''') =
                  readDecInt (#"." :: revDigits, false, strm'')
              in
                case getc strm''' of
                  SOME (#"e", strm'''') => readExpPart (accum, #"e", strm'''')
                | SOME (#"E", strm'''') => readExpPart (accum, #"E", strm'''')
                | _ => (Handler.float (implodeRev accum), strm''')
              end
          | (_, _, SOME (#"e", strm'')) =>
              ( checkPrefixZero ()
              ; readExpPart (revDigits, #"e", strm'')
              ) (* float *)
          | (_, _, SOME (#"E", strm'')) =>
              ( checkPrefixZero ()
              ; readExpPart (revDigits, #"E", strm'')
              ) (* float *)
          | (_, _, _) =>
              ( checkPrefixZero ()
              ; ( Handler.integer (Option.valOf
                    (Handler.Integer.fromString (implodeRev revDigits)))
                , strm'
                )
              ) (* dec-int *)
        end
      fun isValidUnquotedKey c =
        Char.isAlphaNum c orelse c = #"-" orelse c = #"_"
      (*: val readSimpleKey : (char * 'strm) option -> string * 'strm *)
      fun readSimpleKey NONE = UnexpectedEndOfInput "key"
        | readSimpleKey (SOME (#"\"", strm)) = readBasicString strm
        | readSimpleKey (SOME (#"'", strm)) = readLiteralString strm
        | readSimpleKey (SOME (c0, strm)) =
            let
              fun go (accum, strm') =
                case getc strm' of
                  NONE => (implodeRev accum, strm')
                | SOME (c, strm'') =>
                    if isValidUnquotedKey c then go (c :: accum, strm'')
                    else (implodeRev accum, strm')
            in
              if isValidUnquotedKey c0 then go ([c0], strm)
              else UnexpectedChar (c0, "quote, alphanum, '-', or '_'")
            end
      (*: val readKey : (char * 'strm) option -> key * 'strm *)
      fun readKey input =
        let
          fun go (accum, strm) =
            case getc strm of
              SOME (#".", strm') =>
                let
                  val (k, strm'') = readSimpleKey (skipWhiteSpaceAndGetc strm')
                in
                  go (k :: accum, skipWhiteSpace strm'')
                end
            | _ => (List.rev accum, strm)
          val (k0, strm) = readSimpleKey input
        in
          go ([k0], skipWhiteSpace strm)
        end
      datatype defined_by = EXACT_HEADER | IMPLICIT_HEADER | IMPLICIT_KEYVAL
      datatype partial_value =
        LEAF of value
      | PARTIAL_TABLE of defined_by * partial_table
      | PARTIAL_ARRAY of
          partial_table * partial_table list (* in reverse order *)
      withtype partial_table = (string * partial_value) list
      (*:
      val finalize : partial_table -> value
      val finalizeValue : partial_value -> value
      val finalizeTable : partial_table -> table
      *)
      fun finalize xs =
        Handler.subtable (finalizeTable xs)
      and finalizeValue (LEAF v) = v
        | finalizeValue (PARTIAL_TABLE (_, pt)) = finalize pt
        | finalizeValue (PARTIAL_ARRAY (last, xs)) =
            Handler.array (List.revAppend
              (List.map finalize xs, [finalize last]))
      and finalizeTable xs =
        Handler.table (List.map (fn (key, pv) => (key, finalizeValue pv)) xs)
      (*: val insert : path * partial_table * key * value -> partial_table *)
      fun insert (revPath, pt, keys as [key], v) =
            if List.exists (fn (key', _) => key = key') pt then
              DuplicateKey (List.revAppend (revPath, keys))
            else
              pt @ [(key, LEAF v)]
        | insert (revPath, pt, key :: keys, v) =
            let
              fun go (accum, []) =
                    List.revAppend
                      ( accum
                      , [( key
                         , PARTIAL_TABLE
                             ( IMPLICIT_KEYVAL
                             , insert (key :: revPath, [], keys, v)
                             )
                         )]
                      ) (* new key *)
                | go (accum, (p as (key', pv)) :: xs) =
                    if key = key' then
                      case pv of
                        LEAF _ => DuplicateKey (List.revAppend (revPath, [key]))
                      | PARTIAL_TABLE (EXACT_HEADER, _) =>
                          DuplicateKey (List.revAppend (revPath, [key]))
                      | PARTIAL_TABLE (definedBy, pt') =>
                          List.revAppend
                            ( accum
                            , ( key'
                              , PARTIAL_TABLE
                                  ( definedBy
                                  , insert (key :: revPath, pt', keys, v)
                                  )
                              ) :: xs
                            )
                      | PARTIAL_ARRAY _ =>
                          DuplicateKey (List.revAppend (revPath, [key]))
                    else
                      go (p :: accum, xs)
            in
              go ([], pt)
            end
        | insert (_, _, [], _) = raise Match (* should not occur *)
      (*:
      val readValue : path * (char * 'strm) option -> value * 'strm
      val readArray : path * value list * 'strm -> value * 'strm
      val readInlineTable : path * partial_table * (char * 'strm) option -> value * 'strm
      val readKeyval : path * (char * 'strm) option -> string list * value * 'strm
      *)
      fun readValue (_, NONE) = UnexpectedEndOfInput "value"
        | readValue (revPath, SOME (c, strm)) =
            case c of
              #"\"" =>
                (case getc strm of (* ml-basic-string / basic-string *)
                   NONE => UnexpectedEndOfInput "closing quote"
                 | SOME (#"\"", strm') =>
                     (case getc strm' of
                        SOME (#"\"", strm'') =>
                          let
                            val (s, strm''') =
                              readMultilineBasicString
                                (skipOptionalNewline strm'')
                          in
                            (Handler.string s, strm''')
                          end
                      | _ => (Handler.string "", strm'))
                 | _ =>
                     let val (s, strm') = readBasicString strm
                     in (Handler.string s, strm')
                     end)
            | #"'" =>
                (case getc strm of (* ml-literal-string / literal-string *)
                   NONE => UnexpectedEndOfInput "closing quote"
                 | SOME (#"'", strm') =>
                     (case getc strm' of
                        SOME (#"'", strm'') =>
                          let
                            val (s, strm''') =
                              readMultilineLiteralString
                                (skipOptionalNewline strm'')
                          in
                            (Handler.string s, strm''')
                          end
                      | _ => (Handler.string "", strm'))
                 | _ =>
                     let val (s, strm') = readLiteralString strm
                     in (Handler.string s, strm')
                     end)
            | #"[" => readArray ("[]" :: revPath, [], strm) (* array *)
            | #"{" =>
                (case skipWhiteSpaceAndGetc strm of (* inline-table *)
                   SOME (#"}", strm') =>
                     (Handler.subtable (Handler.table []), strm')
                 | r => readInlineTable (revPath, [], r))
            | #"t" =>
                ( Handler.bool true
                , expect (#"e", expect (#"u", expect (#"r", strm)))
                )
            | #"f" =>
                ( Handler.bool false
                , expect (#"e", expect (#"s", expect
                    (#"l", expect (#"a", strm))))
                )
            | #"i" => (Handler.float "inf", expect (#"f", expect (#"n", strm)))
            | #"n" => (Handler.float "nan", expect (#"n", expect (#"a", strm)))
            | #"+" =>
                (case getc strm of
                   NONE => UnexpectedEndOfInput "digit or 'inf' or 'nan'"
                 | SOME (#"i", strm') =>
                     (Handler.float "+inf", expect (#"f", expect (#"n", strm')))
                 | SOME (#"n", strm') =>
                     (Handler.float "+nan", expect (#"n", expect (#"a", strm')))
                 | SOME (c', strm') =>
                     if Char.isDigit c' then
                       readSigned (#"+", c', strm') (* float / integer *)
                     else
                       UnexpectedChar (c', "digit or 'inf' or 'nan'"))
            | #"-" =>
                (case getc strm of
                   NONE => UnexpectedEndOfInput "digit or 'inf' or 'nan'"
                 | SOME (#"i", strm') =>
                     (Handler.float "-inf", expect (#"f", expect (#"n", strm')))
                 | SOME (#"n", strm') =>
                     (Handler.float "-nan", expect (#"n", expect (#"a", strm')))
                 | SOME (c', strm') =>
                     if Char.isDigit c' then
                       readSigned (#"-", c', strm') (* float / integer *)
                     else
                       UnexpectedChar (c', "digit or 'inf' or 'nan'"))
            | #"0" =>
                (case getc strm of
                   NONE => (Handler.integer (Handler.Integer.fromInt 0), strm)
                 | SOME (#"x", strm') =>
                     let
                       val (x, strm'') =
                         readHexInt
                           (Handler.Integer.fromInt 0, strm') (* hex-int *)
                     in
                       (Handler.integer x, strm'')
                     end
                 | SOME (#"o", strm') =>
                     let
                       val (x, strm'') =
                         readOctInt
                           (Handler.Integer.fromInt 0, strm') (* oct-int *)
                     in
                       (Handler.integer x, strm'')
                     end
                 | SOME (#"b", strm') =>
                     let
                       val (x, strm'') =
                         readBinInt
                           (Handler.Integer.fromInt 0, strm') (* bin-int *)
                     in
                       (Handler.integer x, strm'')
                     end
                 | SOME (_, _) =>
                     readUnsigned
                       (#"0", strm) (* date-time / float / unsigned-dec-int *))
            | _ =>
                if Char.isDigit c then
                  readUnsigned (c, strm) (* date-time / float / integer *)
                else
                  UnexpectedChar (c, "value")
      and readArray (revPath, accum, strm) =
        (case skipWhiteSpaceOrCommentOrNewlineAndGetc strm of
           SOME (#"]", strm') => (Handler.array (List.rev accum), strm')
         | r =>
             let
               val (v, strm') = readValue (revPath, r)
             in
               case skipWhiteSpaceOrCommentOrNewlineAndGetc strm' of
                 NONE => UnexpectedEndOfInput "',' or ']'"
               | SOME (#",", strm'') => readArray (revPath, v :: accum, strm'')
               | SOME (#"]", strm'') =>
                   (Handler.array (List.rev (v :: accum)), strm'')
               | SOME (c, _) => UnexpectedChar (c, "',' or ']'")
             end)
      and readInlineTable (revPath, accum, r) =
        let
          val (key, v, strm) = readKeyval (revPath, r)
          val accum' = insert (revPath, accum, key, v)
        in
          case skipWhiteSpaceAndGetc strm of
            NONE => UnexpectedEndOfInput "',' or '}'"
          | SOME (#",", strm') =>
              readInlineTable (revPath, accum', skipWhiteSpaceAndGetc strm')
          | SOME (#"}", strm') => (finalize accum', strm')
          | SOME (c, _) => UnexpectedChar (c, "',' or '}'")
        end
      and readKeyval (revPath, r) =
        let
          val (key, strm') = readKey r
          val (v, strm'') =
            readValue (List.revAppend (key, revPath), skipWhiteSpaceAndGetc
              (expect (#"=", strm')))
        in
          (key, v, strm'')
        end
      datatype expression =
        KEYVAL of key * value
      | STD_TABLE of key
      | ARRAY_TABLE of key
      (*: val readExpression : string list * 'strm -> (expression * 'strm) option *)
      fun readExpression (revPath, strm) =
        case skipWhiteSpaceAndGetc strm of
          NONE => NONE
        | SOME (#"\n", strm') => readExpression (revPath, strm')
        | SOME (#"\r", strm') => readExpression (revPath, expect (#"\n", strm'))
        | SOME (#"#", strm') => readExpression (revPath, skipUntilNewline strm')
        | SOME (#"[", strm') => (* table *)
            (case getc strm' of
               SOME (#"[", strm'') =>
                 let
                   val (key, strm''') =
                     readKey (skipWhiteSpaceAndGetc strm'') (* array-table *)
                   val strm'''' = expect (#"]", expect (#"]", strm'''))
                 in
                   SOME (ARRAY_TABLE key, skipWhiteSpaceOrComment strm'''')
                 end
             | _ =>
                 let
                   val (key, strm'') =
                     readKey (skipWhiteSpaceAndGetc strm') (* std-table *)
                   val strm''' = expect (#"]", strm'')
                 in
                   SOME (STD_TABLE key, skipWhiteSpaceOrComment strm''')
                 end)
        | r =>
            let val (key, v, strm') = readKeyval (revPath, r) (* keyval *)
            in SOME (KEYVAL (key, v), skipWhiteSpaceOrComment strm')
            end
      (*: val insertKeyval : path * partial_table * key * key * value -> partial_table *)
      fun insertKeyval (revPath, pt, [], keys, v) =
            insert (revPath, pt, keys, v)
        | insertKeyval (revPath, pt, x0 :: xs, keys, v) =
            let
              fun go (accum, []) =
                    List.revAppend
                      ( accum
                      , [( x0
                         , PARTIAL_TABLE (IMPLICIT_HEADER, insertKeyval
                             (x0 :: revPath, [], xs, keys, v))
                         )]
                      ) (* should not occur *)
                | go (accum, (p as (key, pv)) :: ys) =
                    if x0 = key then
                      let
                        val updated =
                          case pv of
                            LEAF _ =>
                              DuplicateKey (List.revAppend (revPath, [key]))
                          | PARTIAL_TABLE (definedBy, pt') =>
                              PARTIAL_TABLE (definedBy, insertKeyval
                                (x0 :: revPath, pt', xs, keys, v))
                          | PARTIAL_ARRAY (last, rest) =>
                              PARTIAL_ARRAY
                                ( insertKeyval
                                    (x0 :: revPath, last, xs, keys, v)
                                , rest
                                )
                      in
                        List.revAppend (accum, (key, updated) :: ys)
                      end
                    else
                      go (p :: accum, ys)
            in
              go ([], pt)
            end
      fun insertTable (revPath, pt, [key]) =
            let
              fun go (accum, []) =
                    List.revAppend
                      ( accum
                      , [(key, PARTIAL_TABLE (EXACT_HEADER, []))]
                      ) (* new table (explicit) *)
                | go (accum, (p as (key', pv)) :: xs) =
                    if key = key' then
                      case pv of
                        LEAF _ => DuplicateKey (List.revAppend (revPath, [key]))
                      | PARTIAL_TABLE (IMPLICIT_HEADER, pt') =>
                          List.revAppend
                            ( accum
                            , (key', PARTIAL_TABLE (EXACT_HEADER, pt')) :: xs
                            ) (* convert implicit table into explicit one *)
                      | PARTIAL_TABLE (_, _) =>
                          DuplicateKey (List.revAppend (revPath, [key]))
                      | PARTIAL_ARRAY _ =>
                          DuplicateKey
                            (List.revAppend (revPath, [key])) (* previous: array, now: table *)
                    else
                      go (p :: accum, xs)
            in
              go ([], pt)
            end
        | insertTable (revPath, pt, key :: keys) =
            let
              fun go (accum, []) =
                    List.revAppend
                      ( accum
                      , [( key
                         , PARTIAL_TABLE
                             ( IMPLICIT_HEADER
                             , insertTable (key :: revPath, [], keys)
                             )
                         )]
                      ) (* new table (implicit) *)
                | go (accum, (p as (key', pv)) :: xs) =
                    if key = key' then
                      let
                        val updated =
                          case pv of
                            LEAF _ =>
                              DuplicateKey (List.revAppend (revPath, [key]))
                          | PARTIAL_TABLE (definedBy, pt') =>
                              PARTIAL_TABLE
                                ( definedBy
                                , insertTable (key :: revPath, pt', keys)
                                )
                          | PARTIAL_ARRAY (last, rest) =>
                              PARTIAL_ARRAY
                                (insertTable (key :: revPath, last, keys), rest)
                      in
                        List.revAppend (accum, (key', updated) :: xs)
                      end
                    else
                      go (p :: accum, xs)
            in
              go ([], pt)
            end
        | insertTable (_, _, []) = raise Match (* should not occur *)
      fun insertArrayTable (revPath, pt, [key]) =
            let
              fun go (accum, []) =
                    List.revAppend
                      ( accum
                      , [(key, PARTIAL_ARRAY ([], []))]
                      ) (* new array table *)
                | go (accum, (p as (key', pv)) :: xs) =
                    if key = key' then
                      case pv of
                        LEAF _ => DuplicateKey (List.revAppend (revPath, [key]))
                      | PARTIAL_TABLE _ =>
                          DuplicateKey (List.revAppend (revPath, [key]))
                      | PARTIAL_ARRAY (last, rest) =>
                          List.revAppend
                            ( accum
                            , (key, PARTIAL_ARRAY ([], last :: rest)) :: xs
                            )
                    else
                      go (p :: accum, xs)
            in
              go ([], pt)
            end
        | insertArrayTable (revPath, pt, key :: keys) =
            let
              fun go (accum, []) =
                    List.revAppend
                      ( accum
                      , [( key
                         , PARTIAL_TABLE
                             ( IMPLICIT_HEADER
                             , insertArrayTable (key :: revPath, [], keys)
                             )
                         )]
                      ) (* new table (implicit) *)
                | go (accum, (p as (key', pv)) :: xs) =
                    if key = key' then
                      let
                        val updated =
                          case pv of
                            LEAF _ =>
                              DuplicateKey (List.revAppend (revPath, [key]))
                          | PARTIAL_TABLE (definedBy, pt') =>
                              PARTIAL_TABLE
                                ( definedBy
                                , insertArrayTable (key :: revPath, pt', keys)
                                )
                          | PARTIAL_ARRAY (last, rest) =>
                              PARTIAL_ARRAY
                                ( insertArrayTable (key :: revPath, last, keys)
                                , rest
                                )
                      in
                        List.revAppend (accum, (key, updated) :: xs)
                      end
                    else
                      go (p :: accum, xs)
            in
              go ([], pt)
            end
        | insertArrayTable (_, _, []) = raise Match (* should not occur *)
      fun scan0 (accum, revPath, prefix, strm) =
        case readExpression (revPath, strm) of
          NONE => SOME (finalizeTable accum, strm)
        | SOME (ARRAY_TABLE key, strm') =>
            scan0
              ( insertArrayTable ([], accum, key)
              , "[]" :: List.rev key
              , key
              , strm'
              )
        | SOME (STD_TABLE key, strm') =>
            scan0 (insertTable ([], accum, key), List.rev key, key, strm')
        | SOME (KEYVAL (key, v), strm') =>
            scan0
              (insertKeyval ([], accum, prefix, key, v), revPath, prefix, strm')
    in
      fn strm => scan0 ([], [], [], strm)
    end
  fun parse getc st = #1 (valOf (scan getc st))
end
