(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure SyntaxHighlighter:
sig
  val highlightToken: Token.t -> TerminalColorString.t

  (** Use just lexing info to color a sequence of tokens from a single source.
    * Tokens must be in order as they appear in the source.
    *)
  val highlight: AstAllows.t -> Source.t -> TerminalColorString.t

  (** Similar to above, but always succeeds by skipping over characters as
    * necessary.
    *)
  val fuzzyHighlight: Source.t -> TerminalColorString.t
end =
struct

  structure TCS = TerminalColorString
  structure TC = TerminalColors
  open Palette

  fun tokColor class =
    case class of
      Token.StringConstant => TCS.foreground red
    | Token.CharConstant => TCS.foreground purple
    | Token.WordConstant => TCS.foreground yellow
    | Token.Comment => TCS.italic o TCS.foreground gray
    | Token.IntegerConstant => TCS.foreground lightblue
    | Token.RealConstant => TCS.foreground green
    | Token.Reserved _ => TCS.bold o TCS.foreground blue
    | Token.LongIdentifier => TCS.foreground pink
    | Token.Identifier => TCS.foreground darkgreen
    | Token.MLtonReserved => TCS.foreground darkgreen
    | Token.Whitespace => TCS.clear

  (* fun tokColorMLB class =
    case class of
      MLBToken.MLBPath =>
        lightblue
    | MLBToken.SMLPath =>
        red
    | MLBToken.Reserved _ =>
        TC.bold ^ blue
    | MLBToken.SML c =>
        tokColor c *)


  fun highlightToken tok =
    let
      val thisSrc = Token.getSource tok
      val class = Token.getClass tok
    in
      tokColor class (TCS.fromString (Source.toString thisSrc))
    end


  fun loop tokColor acc (wholeSrc, i, stop) (toks, j) =
    if
      i >= stop
    then
      acc
    else if
      j >= Seq.length toks
      orelse Source.absoluteStartOffset (Token.getSource (Seq.nth toks j)) > i
    then
      let
        val upper =
          if j >= Seq.length toks then
            stop
          else
            Int.min (stop, Source.absoluteStartOffset (Token.getSource
              (Seq.nth toks j)))
        val stuffUntilNextTok = Source.slice wholeSrc (i, upper - i)
        val acc = TCS.append
          (acc, TCS.fromString (Source.toString stuffUntilNextTok))
      in
        loop tokColor acc (wholeSrc, upper, stop) (toks, j)
      end
    else
      let
        val thisSrc = Token.getSource (Seq.nth toks j)
        val class = Token.getClass (Seq.nth toks j)
        val thisOne = tokColor class (TCS.fromString (Source.toString thisSrc))
        val acc = TCS.append (acc, thisOne)
      in
        loop tokColor acc (wholeSrc, Source.absoluteEndOffset thisSrc, stop)
          (toks, j + 1)
      end


  fun highlight allows source =
    let
      val toks = Lexer.tokens allows source
      val startOffset = Source.absoluteStartOffset source
      val endOffset = Source.absoluteEndOffset source
      val wholeSrc = Source.wholeFile source
    in
      loop tokColor TCS.empty (wholeSrc, startOffset, endOffset) (toks, 0)
    end


  fun fuzzyTokens src =
    let
      val smlLexerAllows = AstAllows.make
        { topExp = true
        , optBar = true
        , recordPun = true
        , orPat = true
        , extendedText = true
        , sigWithtype = true
        }

      val startOffset = Source.absoluteStartOffset src
      val endOffset = Source.absoluteEndOffset src
      val src = Source.wholeFile src

      fun tokEndOffset tok =
        Source.absoluteEndOffset (Token.Pretoken.getSource tok)

      fun finish acc =
        Token.makeGroup (Seq.fromRevList acc)

      fun loop acc offset =
        if offset >= endOffset then
          finish acc
        else
          ((case Lexer.next smlLexerAllows (Source.drop src offset) of
              NONE => finish acc
            | SOME tok => loop (tok :: acc) (tokEndOffset tok))
           handle _ => loop acc (offset + 1))

      val result = loop [] startOffset
    (*
          val _ = print ("fuzzyTokens\n")
          val _ = print (Source.toString originalSrc ^ "\n")
          val _ =
            print ("Tokens: " ^ Seq.toString Token.toString result ^ "\n")
    *)
    in
      result
    end


  fun fuzzyHighlight source =
    let
      val toks = fuzzyTokens source
      val startOffset = Source.absoluteStartOffset source
      val endOffset = Source.absoluteEndOffset source
      val wholeSrc = Source.wholeFile source
      val result =
        loop tokColor TCS.empty (wholeSrc, startOffset, endOffset) (toks, 0)
    in
      (* print (TCS.debugShow result ^ "\n"); *)
      result
    end

end
