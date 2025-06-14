(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParsePat:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t

  val pat: AstAllows.t
           -> tokens
           -> InfixDict.t
           -> ExpPatRestriction.t
           -> (int, Ast.Pat.pat) parser
end =
struct

  structure PC = ParserCombinators
  structure PS = ParseSimple
  structure PT = ParseTy
  structure Restriction = ExpPatRestriction

  type ('a, 'b) parser = ('a, 'b) PC.parser
  type tokens = Token.t Seq.t


  fun makeInfixPat infdict (left, id, right) =
    let
      val hp = InfixDict.higherPrecedence infdict
      val sp = InfixDict.samePrecedence infdict
      val aLeft = InfixDict.associatesLeft infdict
      val aRight = InfixDict.associatesRight infdict

      fun bothLeft (x, y) = aLeft x andalso aLeft y
      fun bothRight (x, y) = aRight x andalso aRight y

      val default = Ast.Pat.Infix {left = left, id = id, right = right}
    in
      case right of
        Ast.Pat.Infix {left = rLeft, id = rId, right = rRight} =>
          if hp (rId, id) orelse (sp (rId, id) andalso bothRight (rId, id)) then
            default
          else if hp (id, rId) orelse (sp (rId, id) andalso bothLeft (rId, id)) then
            Ast.Pat.Infix
              { left = makeInfixPat infdict (left, id, rLeft)
              , id = rId
              , right = rRight
              }
          else
            ParserUtils.error
              { pos = Token.getSource rId
              , what = "Ambiguous infix pattern."
              , explain = SOME
                  "You are not allowed to mix left- and right-associative \
                  \operators of same precedence"
              }

      | _ => default
    end


  fun pat allows toks infdict restriction start =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        i < numToks andalso f (tok i)
      fun isReserved rc i =
        check (fn t => Token.Reserved rc = Token.getClass t) i

      fun parse_longvid i = PS.longvid toks i
      fun parse_reserved rc i =
        PS.reserved toks rc i
      fun parse_oneOrMoreDelimitedByReserved x i =
        PC.oneOrMoreDelimitedByReserved toks x i
      fun parse_zeroOrMoreDelimitedByReserved x i =
        PC.zeroOrMoreDelimitedByReserved toks x i
      fun parse_ty i = PT.ty toks i

      fun consume_pat infdict restriction i =
        if not (Restriction.anyOkay restriction andalso AstAllows.orPat allows) then
          consume_onePat infdict restriction i
        else
          let
            val (i, {elems, delims}) =
              parse_oneOrMoreDelimitedByReserved
                { parseElem = consume_onePat infdict restriction
                , delim = Token.Bar
                } i
          in
            if Seq.length elems = 1 then (i, Seq.nth elems 0)
            else (i, Ast.Pat.Or {elems = elems, delims = delims})
          end

      and consume_onePat infdict restriction i =
        let
          val (i, pat) =
            if isReserved Token.Underscore i then
              (i + 1, Ast.Pat.Wild (tok i))
            else if check Token.isPatternConstant i then
              (i + 1, Ast.Pat.Const (tok i))
            else if check Token.isMaybeLongIdentifier i then
              consume_patValueIdentifier infdict NONE i
            else if isReserved Token.Op i then
              consume_patValueIdentifier infdict (SOME (tok i)) (i + 1)
            else if isReserved Token.OpenParen i then
              consume_patParensOrTupleOrUnit infdict (tok i) (i + 1)
            else if isReserved Token.OpenSquareBracket i then
              consume_patListLiteral infdict (tok i) (i + 1)
            else if isReserved Token.OpenCurlyBracket i then
              consume_patRecord infdict (tok i) (i + 1)
            else
              ParserUtils.tokError toks
                { pos = i
                , what =
                    "Unexpected token. Expected to see beginning of pattern."
                , explain = NONE
                }
        in
          consume_afterPat infdict restriction pat i
        end


      (** pat
        *    ^
        *
        * Multiple possibilities for what could be found after a pattern:
        *   [op]longvid atpat     -- identifiers might actually be constructors
        *   pat vid pat           -- infix constructor pattern
        *   pat : ty              -- type annotation
        *   [op]vid[: ty] as pat  -- layered
        *)
      and consume_afterPat infdict restriction pat i =
        let
          val (again, (i, pat)) =
            if
              (** Annoying edge case with '='... we can use it in an infix
                * expression as an equality predicate, but it is NEVER valid as
                * an infix constructor, because SML forbids rebinding '=' in
                * any program.
                *
                * Note to language designers... this is strange. Why not just
                * use something reasonable like "==" for equality predicate?
                * It makes the language more readable too...
                *)
              Restriction.infOkay restriction
              andalso check Token.isValueIdentifierNoEqual i
              andalso InfixDict.isInfix infdict (tok i)
            then
              (true, consume_patInfix infdict pat (tok i) (i + 1))

            else if
              Restriction.appOkay restriction andalso Ast.Pat.okayForConPat pat
              andalso check Token.isAtPatStartToken i
            then
              (true, consume_patCon infdict (Ast.Pat.unpackForConPat pat) i)

            else if
              isReserved Token.Colon i andalso Restriction.anyOkay restriction
            then
              (true, consume_patTyped infdict pat (tok i) (i + 1))

            else if
              isReserved Token.As i andalso Restriction.anyOkay restriction
              andalso Ast.Pat.okayForAsPat pat
            then
              ( true
              , consume_patAs infdict (Ast.Pat.unpackForAsPat pat) (tok i)
                  (i + 1)
              )

            else if
              isReserved Token.Bar i andalso Restriction.anyOkay restriction
              andalso not (AstAllows.orPat allows)
            then
              ParserUtils.tokError toks
                { pos = i
                , what = "Unexpected '|' after pattern."
                , explain = SOME
                    "This might be the beginning of an \"or-pattern\", written \
                    \`<pat1> | <pat2> | ...`, which matches any one of multiple \
                    \patterns. Or-patterns are disallowed in Standard ML, but \
                    \allowed in SuccessorML. To enable or-patterns, use the \
                    \command-line argument '-allow-or-pats true'."
                }

            else
              (false, (i, pat))
        in
          if again then consume_afterPat infdict restriction pat i else (i, pat)
        end


      (** { patrow [, ...] }
        *  ^
        *)
      and consume_patRecord infdict leftBracket i =
        let
          val (i, {elems, delims}) =
            parse_zeroOrMoreDelimitedByReserved
              { parseElem = consume_patRow infdict
              , delim = Token.Comma
              , shouldStop = isReserved Token.CloseCurlyBracket
              } i

          val (i, rightBracket) = parse_reserved Token.CloseCurlyBracket i
        in
          ( i
          , Ast.Pat.Record
              { left = leftBracket
              , elems = elems
              , delims = delims
              , right = rightBracket
              }
          )
        end


      (** A patrow is one of:
        *   ...
        *   lab = pat
        *   vid[: ty] [as pat]
        *)
      and consume_patRow infdict i =
        if
          isReserved Token.DotDotDot i
        then
          if isReserved Token.CloseCurlyBracket (i + 1) then
            (i + 1, Ast.Pat.DotDotDot (tok i))
          else
            ParserUtils.tokError toks
              { pos = i
              , what = "Unexpected token."
              , explain = SOME "This can only appear at the end of the record."
              }
        else if
          check Token.isRecordLabel i andalso isReserved Token.Equal (i + 1)
        then
          let
            val (i, lab) = (i + 1, tok i)
            val (i, eq) = (i + 1, tok i)
            val (i, pat) = consume_pat infdict Restriction.None i
          in
            (i, Ast.Pat.LabEqPat {lab = lab, eq = eq, pat = pat})
          end
        else if
          check Token.isValueIdentifierNoEqual i
        then
          let
            val (i, vid) = (i + 1, tok i)
            val (i, ty) =
              if not (isReserved Token.Colon i) then
                (i, NONE)
              else
                let
                  val (i, colon) = (i + 1, tok i)
                  val (i, ty) = parse_ty i
                in
                  (i, SOME {colon = colon, ty = ty})
                end

            val (i, aspat) =
              if not (isReserved Token.As i) then
                (i, NONE)
              else
                let
                  val (i, ass) = (i + 1, tok i)
                  val (i, pat) = consume_pat infdict Restriction.None i
                in
                  (i, SOME {ass = ass, pat = pat})
                end
          in
            (i, Ast.Pat.LabAsPat {id = vid, ty = ty, aspat = aspat})
          end
        else
          ParserUtils.tokError toks
            { pos = i
            , what = "Invalid token. Expected row of record pattern."
            , explain = NONE
            }


      (** [op]vid[: ty] as pat
        *                 ^
        *)
      and consume_patAs infdict {opp, id, ty} ass i =
        let
          val (i, pat) = consume_onePat infdict Restriction.None i
        in
          ( i
          , Ast.Pat.Layered {opp = opp, id = id, ty = ty, ass = ass, pat = pat}
          )
        end


      (** [op]longvid atpat
        *            ^
        *)
      and consume_patCon infdict {opp, id} i =
        let val (i, atpat) = consume_onePat infdict Restriction.At i
        in (i, Ast.Pat.Con {opp = opp, id = id, atpat = atpat})
        end


      (** pat : ty
        *      ^
        *)
      and consume_patTyped infdict pat colon i =
        let val (i, ty) = parse_ty i
        in (i, Ast.Pat.Typed {pat = pat, colon = colon, ty = ty})
        end


      (** pat vid pat
        *        ^
        *)
      and consume_patInfix infdict leftPat vid i =
        let val (i, rightPat) = consume_onePat infdict Restriction.Inf i
        in (i, makeInfixPat infdict (leftPat, vid, rightPat))
        end


      (** [op] longvid
        *     ^
        *)
      and consume_patValueIdentifier infdict opp i =
        let
          val (i, vid) = parse_longvid i
          val _ =
            ParserUtils.errorIfInfixNotOpped infdict opp
              (MaybeLongToken.getToken vid)
        in
          (i, Ast.Pat.Ident {opp = opp, id = vid})
        end


      (** [ ... ]
        *  ^
        *)
      and consume_patListLiteral infdict openBracket i =
        let
          fun finish elems delims closeBracket =
            Ast.Pat.List
              { left = openBracket
              , right = closeBracket
              , elems = elems
              , delims = delims
              }
        in
          if isReserved Token.CloseSquareBracket i then
            (i + 1, finish (Seq.empty ()) (Seq.empty ()) (tok i))
          else
            let
              val parseElem = consume_pat infdict Restriction.None
              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parseElem, delim = Token.Comma} i
              val (i, closeBracket) = parse_reserved Token.CloseSquareBracket i
            in
              (i, finish elems delims closeBracket)
            end
        end


      (** ( )
        *  ^
        * OR
        * ( pat )
        *  ^
        * OR
        * ( pat, pat [, pat ...] )
        *  ^
        *)
      and consume_patParensOrTupleOrUnit infdict leftParen i =
        if isReserved Token.CloseParen i then
          (i + 1, Ast.Pat.Unit {left = leftParen, right = tok i})
        else
          let
            val parseElem = consume_pat infdict Restriction.None
            val (i, {elems, delims}) =
              parse_oneOrMoreDelimitedByReserved
                {parseElem = parseElem, delim = Token.Comma} i
            val (i, rightParen) = parse_reserved Token.CloseParen i
            val result =
              if Seq.length elems = 1 then
                Ast.Pat.Parens
                  {left = leftParen, pat = Seq.nth elems 0, right = rightParen}
              else
                Ast.Pat.Tuple
                  { left = leftParen
                  , elems = elems
                  , delims = delims
                  , right = rightParen
                  }
          in
            (i, result)
          end

    in
      consume_pat infdict restriction start
    end

end
