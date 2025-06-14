(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Lexer:
sig
  (** Get the next token in the given source. If there isn't one, returns NONE.
    * raises Error if there's a problem.
    *)
  val next: AstAllows.t -> Source.t -> Token.Pretoken.t option

  (** Get all the tokens in the given source.
    * raises Error if there's a problem.
    *)
  val tokens: AstAllows.t -> Source.t -> Token.t Seq.t
end =
struct

  (** This is just to get around annoying bad syntax highlighting for SML... *)
  val backslash = #"\\" (* " *)

  fun success tok = SOME tok

  fun error {pos, what, explain} =
    raise Error.Error
      (Error.lineError
         {header = "SYNTAX ERROR", pos = pos, what = what, explain = explain})


  fun next allows (src: Source.t) : Token.Pretoken.t option =
    let
      val startOffset = Source.absoluteStartOffset src
      val src = Source.wholeFile src

      (** Some helpers for making source slices and tokens. *)
      fun slice (i, j) =
        Source.slice src (i, j - i)
      fun mk x (i, j) =
        Token.Pretoken.make (slice (i, j)) x
      fun mkr x (i, j) =
        Token.Pretoken.reserved (slice (i, j)) x

      fun get i = Source.nth src i

      fun isEndOfFileAt s = s >= Source.length src

      (** This silliness lets you write almost-English like this:
        *   if is #"x" at i          then ...
        *   if check isSymbolic at i then ...
        *)
      infix 5 at
      fun f at i = f i
      fun check f i =
        i < Source.length src andalso f (get i)
      fun is c =
        check (fn c' => c = c')


      fun isPrint c =
        let val i = Char.ord c
        in 32 <= i andalso i <= 126
        end

      fun isMaybeUnicode c =
        let val i = Char.ord c
        in (128 <= i andalso i <= 253) (* ?? *)
        end


      (** ====================================================================
        * STRING HANDLING
        *)
      datatype newcursor = EndOfChar of int | EndOfFormatEscape of int

      (** The follow functions implement a state machine to advance a cursor
        * within a string.
        *   advance_oneCharOrEscapeSequenceInString
        *   advance_inStringEscapeSequence
        *   advance_inStringThreeDigitEscapeSequence
        *   advance_inStringFourDigitEscapeSequence
        *   advance_inStringControlEscapeSequence
        *   advance_inStringFormatEscapeSequence
        *
        * All of these functions have the same return type newcursor option.
        *   - NONE means we're either at the end of the string or EOF
        *   - SOME(c) means we advanced up to the specific end-point.
        *
        * The "entry point" for the state machine is intended to be
        * advance_oneCharOrEscapeSequenceInString.
        *)

      fun advance_oneCharOrEscapeSequenceInString s (args as {stringStart}) =
        if
          is backslash at s
        then
          advance_inStringEscapeSequence (s + 1) args

        else if
          is #"\"" at s
        then
          NONE

        else if
          is #"\n" at s orelse isEndOfFileAt s
        then
          error
            { pos = slice (stringStart, stringStart + 1)
            , what = "Unclosed string."
            , explain = NONE
            }

        else if
          check isMaybeUnicode at s andalso not (AstAllows.extendedText allows)
        then
          error
            { pos = slice (s, s + 1)
            , what = "Invalid character."
            , explain = SOME
                "There might be a Unicode (UTF-8) byte here. In Standard ML, \
                \strings may only contain printable ASCII characters. However, \
                \SuccessorML allows for UTF-8. To enable this feature, \
                \use the command-line argument \
                \'-allow-extended-text-consts true'"
            }

        else if
          not (check isPrint at s) andalso not (check isMaybeUnicode at s)
          andalso AstAllows.extendedText allows
        then
          error
            { pos = slice (s, s + 1)
            , what = "Invalid character."
            , explain = SOME
                "There is an invalid byte here which may or may not be \
                \visible. The \
                \byte is invalid because it is not a printable ASCII \
                \character, and also because it does \
                \not appear to be UTF-8. \
                \(UTF-8 bytes are allowed here due to either the \
                \command-line argument '-allow-extended-text-consts true' or \
                \an MLB annotation \"allowExtendedTextConsts true\".) "
            }

        else if
          not (AstAllows.extendedText allows) andalso not (check isPrint at s)
        then
          error
            { pos = slice (s, s + 1)
            , what = "Invalid character."
            , explain = SOME
                "There is an invalid byte here which may or may not be \
                \visible. This byte is invalid because it is not a printable \
                \character (visible or whitespace)."
            }

        else
          SOME (EndOfChar (s + 1))


      (** Inside a string, immediately after a backslash *)
      and advance_inStringEscapeSequence s (args as {stringStart}) =
        if check LexUtils.isValidSingleEscapeChar at s then
          (** Includes e.g. \t, \n, \", \\, etc. *)
          SOME (EndOfChar (s + 1))
        else if check LexUtils.isValidFormatEscapeChar at s then
          advance_inStringFormatEscapeSequence (s + 1)
            {stringStart = stringStart, escapeStart = s - 1}
        else if is #"^" at s then
          advance_inStringControlEscapeSequence (s + 1) args
        else if is #"u" at s then
          advance_inStringFourDigitEscapeSequence (s + 1) args
        else if check LexUtils.isDecDigit at s then
          (** Note the `s` instead of `s+1`... intentional. *)
          advance_inStringThreeDigitEscapeSequence s args
        else if isEndOfFileAt s then
          error
            { pos = slice (stringStart, stringStart + 1)
            , what = "Unclosed string."
            , explain = NONE
            }
        else
          error
            { pos = slice (s - 1, s + 1)
            , what = "Invalid escape sequence."
            , explain = NONE
            }


      (** In a string, expecting to see \ddd
        * with s immediately after the backslash
        *)
      and advance_inStringThreeDigitEscapeSequence s _ =
        if
          check LexUtils.isDecDigit at s
          andalso check LexUtils.isDecDigit at s + 1
          andalso check LexUtils.isDecDigit at s + 2
        then
          SOME (EndOfChar (s + 3))
        else
          error
            { pos = slice (s - 1, s)
            , what = "Invalid escape sequence"
            , explain = SOME
                "Three-digit escape sequences must look like \
                \\\DDD where D is a decimal digit."
            }


      (** In a string, expecting to see \uxxxx
        * with s immediately after the u
        *)
      and advance_inStringFourDigitEscapeSequence s _ =
        if
          check LexUtils.isHexDigit at s
          andalso check LexUtils.isHexDigit at s + 1
          andalso check LexUtils.isHexDigit at s + 2
          andalso check LexUtils.isHexDigit at s + 3
        then
          SOME (EndOfChar (s + 4))
        else
          error
            { pos = slice (s - 2, s - 1)
            , what = "Invalid escape sequence."
            , explain = SOME
                "Four-digit escape sequences must look like \
                \\\uXXXX where X is a hexadecimal digit."
            }


      (** "...\^C
        *       ^
        *)
      and advance_inStringControlEscapeSequence s _ =
        if check LexUtils.isValidControlEscapeChar at s then
          SOME (EndOfChar (s + 1))
        else
          error
            { pos = slice (s - 2, s - 1)
            , what = "Invalid escape sequence."
            , explain = SOME
                "Control escape sequences should look like \\^C where C is \
                \one of the following characters: @ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_"
            }


      (** Inside a string, expecting to be inside a \f...f\
        * where each f is a format character (space, newline, tab, etc.)
        *)
      and advance_inStringFormatEscapeSequence s
        (args as {stringStart = _, escapeStart}) =
        if is backslash at s then
          SOME (EndOfFormatEscape (s + 1))
        else if check LexUtils.isValidFormatEscapeChar at s then
          advance_inStringFormatEscapeSequence (s + 1) args
        else if isEndOfFileAt s then
          error
            { pos = slice (escapeStart, escapeStart + 1)
            , what = "Unclosed format escape sequence."
            , explain = NONE
            }
        else
          error
            { pos = slice (s, s + 1)
            , what = "Invalid format escape character."
            , explain = SOME
                "Formatting escape sequences have to be enclosed by backslashes\
                \ and should only contain whitespace characters."
            }


      fun advance_toEndOfString s (args as {stringStart}) =
        case advance_oneCharOrEscapeSequenceInString s args of
          SOME (EndOfChar s') => advance_toEndOfString s' args
        | SOME (EndOfFormatEscape s') => advance_toEndOfString s' args
        | NONE =>
            if is #"\"" at s then
              s + 1
            else
              raise Error.Error
                { header = "BUG!"
                , content =
                    [ Error.Paragraph
                        "Bug found in lexer! Please report on GitHub..."
                    , Error.Paragraph
                        "Lexer.advance_toEndOfString: could not find end of string:"
                    , Error.SourceReference
                        (slice (stringStart, stringStart + 1))
                    , Error.Paragraph "Got up to here:"
                    , Error.SourceReference (slice (s, s + 1))
                    ]
                }

      fun advance_oneCharInString s args =
        case advance_oneCharOrEscapeSequenceInString s args of
          SOME (EndOfChar s') => SOME s'
        | SOME (EndOfFormatEscape s') => advance_oneCharInString s' args
        | NONE => NONE

      (** ====================================================================
        * STATE MACHINE
        *
        * This bunch of mutually-recursive functions implements an efficient
        * state machine. Each is named `loop_<STATE_NAME>`. The arguments
        * are always
        *   `loop_XXX s [args]`
        * where
        *   `s` is the current position, and
        *   `args` is a state-dependent state (haha)
        *)

      fun loop_topLevel s =
        if isEndOfFileAt s then
          NONE
        else
          case get s of
            #"(" => loop_afterOpenParen (s + 1)
          | #")" => success (mkr Token.CloseParen (s, s + 1))
          | #"[" => success (mkr Token.OpenSquareBracket (s, s + 1))
          | #"]" => success (mkr Token.CloseSquareBracket (s, s + 1))
          | #"{" => success (mkr Token.OpenCurlyBracket (s, s + 1))
          | #"}" => success (mkr Token.CloseCurlyBracket (s, s + 1))
          | #"," => success (mkr Token.Comma (s, s + 1))
          | #";" => success (mkr Token.Semicolon (s, s + 1))
          | #"_" => success (mkr Token.Underscore (s, s + 1))
          | #"\"" =>
              let val s' = advance_toEndOfString (s + 1) {stringStart = s}
              in success (mk Token.StringConstant (s, s'))
              end
          | #"~" => loop_afterTwiddle (s + 1)
          | #"'" =>
              loop_alphanumId (s + 1)
                {idStart = s, startsPrime = true, longStart = NONE}
          | #"0" => loop_afterZero (s + 1)
          | #"." => loop_afterDot (s + 1)
          | #"*" => loop_symbolicId (s + 1) {idStart = s, longStart = NONE}
          | #"#" =>
              if is #"\"" at s + 1 then loop_charConstant (s + 2)
              else loop_symbolicId (s + 1) {idStart = s, longStart = NONE}
          | c =>
              if LexUtils.isDecDigit c then
                loop_decIntegerConstant (s + 1) {constStart = s}
              else if LexUtils.isSymbolic c then
                loop_symbolicId (s + 1) {idStart = s, longStart = NONE}
              else if LexUtils.isLetter c then
                loop_alphanumId (s + 1)
                  {idStart = s, startsPrime = false, longStart = NONE}
              else if Char.isSpace c then
                loop_whitespace {start = s} (s + 1)
              else
                error
                  { pos = slice (s, s + 1)
                  , what = "Unexpected character."
                  , explain = SOME "Perhaps from unsupported character-set?"
                  }


      and loop_whitespace {start} i =
        if check Char.isSpace i then loop_whitespace {start = start} (i + 1)
        else success (mk Token.Whitespace (start, i))


      (** #"...
        *   ^
        *)
      and loop_charConstant s =
        case advance_oneCharInString s {stringStart = s - 1} of
          SOME s' =>
            if is #"\"" at s' then
              success (mk Token.CharConstant (s - 2, s' + 1))
            else
              error
                { pos = slice (s', s' + 1)
                , what = "Character constant contains more than one character."
                , explain = NONE
                }

        | NONE =>
            error
              { pos = slice (s - 2, s + 1)
              , what = "Character constant is empty."
              , explain = NONE
              }


      and loop_afterDot s =
        if (is #"." at s) andalso (is #"." at s + 1) then
          success (mkr Token.DotDotDot (s - 1, s + 2))
        else
          let
            val huh = if (is #"." at s) then s + 1 else s
          in
            error
              { pos = slice (huh, huh + 1)
              , what = "Unexpected character."
              , explain = SOME "Perhaps you meant: ..."
              }
          end


      and loop_symbolicId s (args as {idStart, longStart}) =
        if check LexUtils.isSymbolic at s then
          loop_symbolicId (s + 1) args
        else
          let
            val srcHere = slice (idStart, s)
            val tok = Token.Pretoken.reservedOrIdentifier srcHere
            val isQualified = Option.isSome longStart
          in
            if Token.isReserved (Token.fromPre tok) andalso isQualified then
              error
                { pos = srcHere
                , what = "Unexpected reserved symbol."
                , explain = SOME
                    "Reserved symbols cannot be used as identifiers."
                }
            else if not isQualified then
              success tok
            else
              success (mk Token.LongIdentifier (Option.valOf longStart, s))
          end


      and loop_alphanumId s (args as {idStart, startsPrime, longStart}) =
        if check LexUtils.isAlphaNumPrimeOrUnderscore at s then
          loop_alphanumId (s + 1) args
        else
          let
            val srcHere = slice (idStart, s)
            val tok = Token.Pretoken.reservedOrIdentifier srcHere
            val isQualified = Option.isSome longStart
          in
            if
              Token.isReserved (Token.fromPre tok)
              andalso (isQualified orelse is #"." at s)
            then
              error
                { pos = srcHere
                , what = "Unexpected reserved keyword."
                , explain = SOME
                    "Reserved keywords cannot be used as identifiers."
                }
            else if
              is #"." at s andalso startsPrime
            then
              error
                { pos = slice (s, s + 1)
                , what = "Unexpected dot."
                , explain = SOME "Qualifiers cannot start with a prime (')"
                }
            else if
              is #"." at s
            then
              loop_continueLongIdentifier (s + 1)
                {longStart = if isQualified then longStart else SOME idStart}
            else if
              not isQualified
            then
              success tok
            else
              success (mk Token.LongIdentifier (Option.valOf longStart, s))
          end


      and loop_continueLongIdentifier s {longStart} =
        if check LexUtils.isSymbolic at s then
          loop_symbolicId (s + 1) {idStart = s, longStart = longStart}
        else if check LexUtils.isLetter at s then
          loop_alphanumId (s + 1)
            {idStart = s, startsPrime = false, longStart = longStart}
        else
          error
            { pos = slice (s, s + 1)
            , what = "Unexpected character."
            , explain = SOME
                "Identifiers have to start with a letter or symbol."
            }


      (** After seeing a twiddle, we might be at the beginning of an integer
        * constant, or we might be at the beginning of a symbolic-id.
        *
        * Note that seeing "0" next is special, because of e.g. "0x" used to
        * indicate the beginning of hex format.
        *)
      and loop_afterTwiddle s =
        if is #"0" at s then
          loop_afterTwiddleThenZero (s + 1)
        else if check LexUtils.isDecDigit at s then
          loop_decIntegerConstant (s + 1) {constStart = s - 1}
        else if check LexUtils.isSymbolic at s then
          loop_symbolicId (s + 1) {idStart = s - 1, longStart = NONE}
        else
          success (mk Token.Identifier (s - 1, s))


      (** Comes after "~0"
        * This might be the middle or end of an integer constant. We have
        * to first figure out if the integer constant is hex format.
        *)
      and loop_afterTwiddleThenZero s =
        if is #"x" at s andalso check LexUtils.isHexDigit at s + 1 then
          loop_hexIntegerConstant (s + 2) {constStart = s - 2}
        else if is #"." at s then
          loop_realConstantAfterDot (s + 1) {constStart = s - 2}
        else if is #"e" at s orelse is #"E" at s then
          loop_realConstantAfterExponent (s + 1) {constStart = s - 2}
        else if check LexUtils.isDecDigit at s then
          loop_decIntegerConstant (s + 1) {constStart = s - 2}
        else
          success (mk Token.IntegerConstant (s - 2, s))


      (** After seeing "0", we're certainly at the beginning of some sort
        * of numeric constant. We need to figure out if this is an integer or
        * a word or a real, and if it is hex or decimal format.
        *)
      and loop_afterZero s =
        if is #"x" at s andalso check LexUtils.isHexDigit at s + 1 then
          loop_hexIntegerConstant (s + 2) {constStart = s - 1}
        else if is #"w" at s then
          loop_afterZeroDubya (s + 1)
        else if is #"." at s then
          loop_realConstantAfterDot (s + 1) {constStart = s - 1}
        else if is #"e" at s orelse is #"E" at s then
          loop_realConstantAfterExponent (s + 1) {constStart = s - 1}
        else if check LexUtils.isDecDigit at s then
          loop_decIntegerConstant (s + 1) {constStart = s - 1}
        else
          success (mk Token.IntegerConstant (s - 1, s))


      and loop_decIntegerConstant s (args as {constStart}) =
        if check LexUtils.isDecDigit at s then
          loop_decIntegerConstant (s + 1) args
        else if is #"." at s then
          loop_realConstantAfterDot (s + 1) args
        else if is #"e" at s orelse is #"E" at s then
          loop_realConstantAfterExponent (s + 1) args
        else
          success (mk Token.IntegerConstant (constStart, s))


      (** Immediately after the dot, we need to see at least one decimal digit *)
      and loop_realConstantAfterDot s (args as {constStart}) =
        if check LexUtils.isDecDigit at s then
          loop_realConstant (s + 1) args
        else
          error
            { pos = slice (constStart, s)
            , what = "Invalid real constant."
            , explain = SOME
                "After the dot, there needs to be at least one decimal digit."
            }


      (** Parsing the remainder of a real constant. This is already after the
        * dot, because the front of the real constant was already parsed as
        * an integer constant.
        *)
      and loop_realConstant s (args as {constStart}) =
        if check LexUtils.isDecDigit at s then
          loop_realConstant (s + 1) args
        else if is #"E" at s orelse is #"e" at s then
          loop_realConstantAfterExponent (s + 1) args
        else
          success (mk Token.RealConstant (constStart, s))


      (** Immediately after the "E" or "e", there might be a twiddle,
        * and then a bunch of decimal digits.
        *)
      and loop_realConstantAfterExponent s {constStart} =
        let
          fun walkThroughDigits i =
            if check LexUtils.isDecDigit at i then walkThroughDigits (i + 1)
            else i
          val s' = walkThroughDigits (if is #"~" at s then s + 1 else s)
        in
          success (mk Token.RealConstant (constStart, s'))
        end


      and loop_hexIntegerConstant s (args as {constStart}) =
        if check LexUtils.isHexDigit at s then
          loop_hexIntegerConstant (s + 1) args
        else
          success (mk Token.IntegerConstant (constStart, s))


      and loop_decWordConstant s (args as {constStart}) =
        if check LexUtils.isDecDigit at s then loop_decWordConstant (s + 1) args
        else success (mk Token.WordConstant (constStart, s))


      and loop_hexWordConstant s (args as {constStart}) =
        if check LexUtils.isHexDigit at s then loop_hexWordConstant (s + 1) args
        else success (mk Token.WordConstant (constStart, s))


      (** Comes after "0w"
        * It might be tempting to think that this is certainly a word constant,
        * but that's not necessarily true. Here's some possibilities:
        *   0w5       -- word constant 5
        *   0wx5      -- word constant 5, in hex format
        *   0w        -- integer constant 0 followed by alphanum-id "w"
        *   0wx       -- integer constant 0 followed by alphanum-id "wx"
        *)
      and loop_afterZeroDubya s =
        if is #"x" at s andalso check LexUtils.isHexDigit at s + 1 then
          loop_hexWordConstant (s + 2) {constStart = s - 2}
        else if check LexUtils.isDecDigit at s then
          loop_decWordConstant (s + 1) {constStart = s - 2}
        else
          success (mk Token.IntegerConstant (s - 2, s - 1))


      (** An open-paren could just be a normal paren, or it could be the
        * start of a comment.
        *)
      and loop_afterOpenParen s =
        if is #"*" at s then
          loop_inComment (s + 1) {commentStart = s - 1, nesting = 1}
        else
          success (mkr Token.OpenParen (s - 1, s))


      (** Inside a comment that started at `commentStart`
        * `nesting` is always >= 0 and indicates how many open-comments we've seen.
        *)
      and loop_inComment s {commentStart, nesting} =
        if nesting = 0 then
          success (mk Token.Comment (commentStart, s))
        else if is #"(" at s andalso is #"*" at s + 1 then
          loop_inComment (s + 2)
            {commentStart = commentStart, nesting = nesting + 1}
        else if is #"*" at s andalso is #")" at s + 1 then
          loop_inComment (s + 2)
            {commentStart = commentStart, nesting = nesting - 1}
        else if isEndOfFileAt s then
          error
            { pos = slice (commentStart, commentStart + 2)
            , what = "Unclosed comment."
            , explain = NONE
            }
        else
          loop_inComment (s + 1)
            {commentStart = commentStart, nesting = nesting}


    in
      loop_topLevel startOffset
    end


  fun tokens allows src =
    let
      val startOffset = Source.absoluteStartOffset src
      val endOffset = Source.absoluteEndOffset src
      val src = Source.wholeFile src

      fun tokEndOffset tok =
        Source.absoluteEndOffset (Token.Pretoken.getSource tok)

      fun finish acc =
        Token.makeGroup (Seq.rev (Seq.fromList acc))

      fun loop acc offset =
        if offset >= endOffset then
          finish acc
        else
          case next allows (Source.drop src offset) of
            NONE => finish acc
          | SOME tok => loop (tok :: acc) (tokEndOffset tok)
    in
      loop [] startOffset
    end

end
