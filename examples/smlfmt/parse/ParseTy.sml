(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParseTy:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t

  val ty: tokens -> (int, Ast.Ty.ty) parser
end =
struct
  local open ParserCombinators ParseSimple in end

  structure PC = ParserCombinators
  structure PS = ParseSimple

  type ('a, 'b) parser = ('a, 'b) PC.parser
  type tokens = Token.t Seq.t


  fun ty toks start =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        i < numToks andalso f (tok i)
      fun isReserved rc i =
        check (fn t => Token.Reserved rc = Token.getClass t) i

      fun parse_recordLabel i = PS.recordLabel toks i
      fun parse_reserved rc i =
        PS.reserved toks rc i
      fun parse_zeroOrMoreDelimitedByReserved x i =
        PC.zeroOrMoreDelimitedByReserved toks x i

      fun parse_tyWithRestriction restriction i =
        let
          val (i, ty) =
            if check Token.isTyVar i then
              (i + 1, Ast.Ty.Var (tok i))
            else if isReserved Token.OpenParen i then
              let
                val leftParen = tok i
                val (i, ty) =
                  parse_tyWithRestriction
                    {permitArrows = true, permitTuple = true} (i + 1)
              in
                parse_tyParensOrSequence leftParen [ty] [] i
              end
            else if isReserved Token.OpenCurlyBracket i then
              parse_tyRecord (tok i) (i + 1)
            else if check Token.isMaybeLongIdentifier i then
              ( i + 1
              , Ast.Ty.Con
                  {id = MaybeLongToken.make (tok i), args = Ast.SyntaxSeq.Empty}
              )
            else
              ParserUtils.tokError toks
                {pos = i, what = "Parser bug!", explain = NONE}
        in
          parse_afterTy restriction ty i
        end


      (** ty
        *   ^
        *
        * Multiple possibilities for what could be found after a type:
        *   ty -> ty        -- function type
        *   ty longtycon    -- type constructor
        *   ty * ...        -- tuple
        *)
      and parse_afterTy (restriction as {permitArrows: bool, permitTuple: bool})
        ty i =
        let
          val (again, (i, ty)) =
            if check Token.isMaybeLongTyCon i then
              ( true
              , ( i + 1
                , Ast.Ty.Con
                    { id = MaybeLongToken.make (tok i)
                    , args = Ast.SyntaxSeq.One ty
                    }
                )
              )
            else if permitArrows andalso isReserved Token.Arrow i then
              (true, parse_tyArrow ty (i + 1))
            else if permitTuple andalso check Token.isStar i then
              (true, parse_tyTuple [ty] [] (i + 1))
            else
              (false, (i, ty))
        in
          if again then parse_afterTy restriction ty i else (i, ty)
        end


      (** { label: ty [, ...] }
        *  ^
        *)
      and parse_tyRecord leftBracket i =
        let
          fun parseElem i =
            let
              val (i, lab) = parse_recordLabel i
              val (i, colon) = parse_reserved Token.Colon i
              val (i, ty) =
                parse_tyWithRestriction
                  {permitArrows = true, permitTuple = true} i
            in
              (i, {lab = lab, colon = colon, ty = ty})
            end

          val (i, {elems, delims}) =
            parse_zeroOrMoreDelimitedByReserved
              { parseElem = parseElem
              , delim = Token.Comma
              , shouldStop = isReserved Token.CloseCurlyBracket
              } i

          val (i, rightBracket) = parse_reserved Token.CloseCurlyBracket i
        in
          ( i
          , Ast.Ty.Record
              { left = leftBracket
              , elems = elems
              , delims = delims
              , right = rightBracket
              }
          )
        end


      (** ty -> ty
        *      ^
        *)
      and parse_tyArrow fromTy i =
        let
          val arrow = tok (i - 1)
          val (i, toTy) =
            parse_tyWithRestriction {permitArrows = true, permitTuple = true} i
        in
          (i, Ast.Ty.Arrow {from = fromTy, arrow = arrow, to = toTy})
        end


      (** [... *] ty * ...
        *             ^
        *)
      and parse_tyTuple tys delims i =
        let
          val star = tok (i - 1)
          val (i, ty) =
            parse_tyWithRestriction {permitArrows = false, permitTuple = false}
              i
          val tys = ty :: tys
          val delims = star :: delims
        in
          if check Token.isStar i then
            parse_tyTuple tys delims (i + 1)
          else
            ( i
            , Ast.Ty.Tuple
                {elems = Seq.fromRevList tys, delims = Seq.fromRevList delims}
            )
        end


      (** ( ty )
        *     ^
        * OR
        * ( ty [, ty ...] ) longtycon
        *     ^
        *)
      and parse_tyParensOrSequence leftParen tys delims i =
        if isReserved Token.CloseParen i then
          parse_tyEndParensOrSequence leftParen tys delims (i + 1)
        else if isReserved Token.Comma i then
          let
            val comma = tok i
            val (i, ty) =
              parse_tyWithRestriction {permitArrows = true, permitTuple = true}
                (i + 1)
          in
            parse_tyParensOrSequence leftParen (ty :: tys) (comma :: delims) i
          end
        else
          ParserUtils.tokError toks
            {pos = i, what = "Unexpected token.", explain = NONE}


      (** ( ty )
        *       ^
        * OR
        * ( ty, ... ) longtycon
        *            ^
        *)
      and parse_tyEndParensOrSequence leftParen tys delims i =
        let
          val rightParen = tok (i - 1)
        in
          case (tys, delims) of
            ([t], []) =>
              (i, Ast.Ty.Parens {left = leftParen, ty = t, right = rightParen})

          | _ =>
              if check Token.isMaybeLongTyCon i then
                ( i + 1
                , Ast.Ty.Con
                    { id = MaybeLongToken.make (tok i)
                    , args = Ast.SyntaxSeq.Many
                        { left = leftParen
                        , elems = Seq.fromRevList tys
                        , delims = Seq.fromRevList delims
                        , right = rightParen
                        }
                    }
                )
              else
                ParserUtils.tokError toks
                  { pos = i
                  , what = "Unexpected token."
                  , explain = SOME "Expected to see a type constructor."
                  }
        end

    in
      parse_tyWithRestriction {permitArrows = true, permitTuple = true} start
    end


end
