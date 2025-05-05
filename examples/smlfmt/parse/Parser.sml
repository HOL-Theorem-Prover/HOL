(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Parser:
sig
  (* Comments are implicit in our representation and are associated with normal
   * tokens. This results in an edge case here, where the input contains only
   * comments and nothing else. It's easy enough to handle, though. *)
  datatype parser_output =
    Ast of Ast.t
  | JustComments of Token.t Seq.t

  val parse: ParserContext.t -> Token.t Seq.t -> parser_output
  val parseWithInfdict: ParserContext.t
                        -> InfixDict.t
                        -> Token.t Seq.t
                        -> (InfixDict.t * parser_output)
end =
struct

  structure PC = ParserCombinators
  structure PS = ParseSimple
  structure PT = ParseTy
  structure PP = ParsePat

  datatype parser_output = Ast of Ast.t | JustComments of Token.t Seq.t

  structure Restriction = ExpPatRestriction

  type ('state, 'result) parser = 'state -> ('state * 'result)
  type 'state peeker = 'state -> bool

  fun parseWithInfdict ctx infdict allTokens =
    let
      val toks = Seq.filter (not o Token.isCommentOrWhitespace) allTokens
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i


      (** This silliness lets you write almost-English like this:
        *   if is Token.Identifier at i           then ...
        *   if isReserved Token.Val at i          then ...
        *   if check isTyVar at i                 then ...
        *)
      infix 5 at
      fun f at i = f i
      fun check f i =
        i < numToks andalso f (tok i)
      fun isReserved rc =
        check (fn t => Token.Reserved rc = Token.getClass t)


      fun parse_reserved rc i =
        PS.reserved toks rc i
      fun parse_sigid i = PS.sigid toks i
      fun parse_strid i = PS.strid toks i
      fun parse_funid i = PS.funid toks i
      fun parse_vid i = PS.vid toks i
      fun parse_longvid i = PS.longvid toks i
      fun parse_ty i = PT.ty toks i


      fun parse_oneOrMoreDelimitedByReserved x i =
        PC.oneOrMoreDelimitedByReserved toks x i
      fun parse_two (p1, p2) state =
        PC.two (p1, p2) state
      fun parse_zeroOrMoreWhile c p s =
        PC.zeroOrMoreWhile c p s

      fun consume_sigExp infdict i =
        ParseSigExpAndSpec.sigexp ctx toks infdict i
      fun consume_sigSpec infdict i =
        ParseSigExpAndSpec.spec ctx toks infdict i


      (** signature sigid = sigexp [and ...]
        *          ^
        *)
      fun consume_sigDec (i, infdict) : ((int * InfixDict.t) * Ast.topdec) =
        let
          val signaturee = tok (i - 1)

          fun parseOne i =
            let
              val (i, sigid) = parse_sigid i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, sigexp) = consume_sigExp infdict i
            in
              (i, {ident = sigid, eq = eq, sigexp = sigexp})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i

          val result: Ast.topdec = Ast.SigDec
            (Ast.Sig.Signature
               {signaturee = signaturee, elems = elems, delims = delims})
        in
          ((i, infdict), result)
        end

      (** ====================================================================
        * Structures and core declarations
        *
        * In the grammar, these are "strdecs" which include e.g.
        *   structure X = ...
        *   local <strdec> in <strdec> end
        * as well as core declarations including e.g.
        *   val x = ...
        *   infix ...
        *   type ...
        *)


      (** strexp : sigexp
        *         ^
        * also handles opaque constraints (strexp :> sigexp)
        *)
      fun consume_strexpConstraint infdict strexp colon i =
        let
          val (i, sigexp) = consume_sigExp infdict i
        in
          ( i
          , Ast.Str.Constraint {strexp = strexp, colon = colon, sigexp = sigexp}
          )
        end


      and consume_strexpStruct infdict structt i : (int * Ast.Str.strexp) =
        let
          val ((i, _), strdec) = consume_strdec (i, infdict)
          val (i, endd) = parse_reserved Token.End i
        in
          (i, Ast.Str.Struct {structt = structt, strdec = strdec, endd = endd})
        end


      (** funid ( strexp )
        *        ^
        * OR
        *
        * funid ( strdec )
        *        ^
        *)
      and consume_strexpFunApp infdict funid lparen i =
        if
          check Token.isDecStartToken i orelse check Token.isStrDecStartToken i
          orelse isReserved Token.CloseParen i
        then
          let
            val ((i, _), strdec) = consume_strdec (i, infdict)
            val (i, rparen) = parse_reserved Token.CloseParen i
          in
            ( i
            , Ast.Str.FunAppDec
                { funid = funid
                , lparen = lparen
                , strdec = strdec
                , rparen = rparen
                }
            )
          end
        else
          let
            val (i, strexp) = consume_strexp infdict i
            val (i, rparen) = parse_reserved Token.CloseParen i
          in
            ( i
            , Ast.Str.FunAppExp
                { funid = funid
                , lparen = lparen
                , strexp = strexp
                , rparen = rparen
                }
            )
          end


      (** let strdec in strexp end
        *    ^
        *)
      and consume_strexpLetInEnd infdict lett i =
        let
          val ((i, infdict'), strdec) = consume_strdec (i, infdict)
          val (i, inn) = parse_reserved Token.In i
          val (i, strexp) = consume_strexp infdict' i
          val (i, endd) = parse_reserved Token.End i
        in
          ( i
          , Ast.Str.LetInEnd
              { lett = lett
              , strdec = strdec
              , inn = inn
              , strexp = strexp
              , endd = endd
              }
          )
        end


      and consume_strexp infdict i =
        let
          val (i, strexp) =
            if
              isReserved Token.Struct i
            then
              consume_strexpStruct infdict (tok i) (i + 1)

            else if
              check Token.isStrIdentifier i
              andalso isReserved Token.OpenParen (i + 1)
            then
              consume_strexpFunApp infdict (tok i) (tok (i + 1)) (i + 2)

            else if
              check Token.isMaybeLongStrIdentifier i
            then
              (i + 1, Ast.Str.Ident (MaybeLongToken.make (tok i)))

            else if
              isReserved Token.Let i
            then
              consume_strexpLetInEnd infdict (tok i) (i + 1)

            else
              ParserUtils.tokError toks
                { pos = i
                , what = "Unexpected token."
                , explain = SOME "Expected structure expression."
                }
        in
          consume_afterStrexp infdict strexp i
        end


      and consume_afterStrexp infdict strexp i =
        let
          val (again, (i, strexp)) =
            if isReserved Token.Colon i orelse isReserved Token.ColonArrow i then
              (true, consume_strexpConstraint infdict strexp (tok i) (i + 1))
            else
              (false, (i, strexp))
        in
          if again then consume_afterStrexp infdict strexp i else (i, strexp)
        end


      (** structure strid [constraint] = strexp [and strid = ...]
        *          ^
        * where the optional constraint is either
        *   : sigexp       (transparent constraint)
        *   :> sigexp      (opaque constraint)
        *)
      and consume_strdecStructure infdict structuree i =
        let
          fun parse_maybeConstraint infdict i =
            if isReserved Token.Colon i orelse isReserved Token.ColonArrow i then
              let
                val (i, colon) = (i + 1, tok i)
                val (i, sigexp) = consume_sigExp infdict i
              in
                (i, SOME {colon = colon, sigexp = sigexp})
              end
            else
              (i, NONE)

          fun parseOne i =
            let
              val (i, strid) = parse_strid i
              val (i, constraint) = parse_maybeConstraint infdict i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, strexp) = consume_strexp infdict i
            in
              ( i
              , { strid = strid
                , constraint = constraint
                , eq = eq
                , strexp = strexp
                }
              )
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i
        in
          ( i
          , Ast.Str.DecStructure
              {structuree = structuree, elems = elems, delims = delims}
          )
        end


      (** local strdec in strdec end
        *      ^
        *)
      and consume_strdecLocalInEnd locall (i, infdict) =
        let
          val original_infdict = infdict

          val ((i, infdict), strdec1) = consume_strdec (i, infdict)
          val (i, inn) = parse_reserved Token.In i
          val ((i, _), strdec2) = consume_strdec (i, infdict)
          val (i, endd) = parse_reserved Token.End i
        in
          ( (i, original_infdict) (** TODO: check this? *)
          , Ast.Str.DecLocalInEnd
              { locall = locall
              , strdec1 = strdec1
              , inn = inn
              , strdec2 = strdec2
              , endd = endd
              }
          )
        end


      and consume_exactlyOneStrdec (i, infdict) :
        ((int * InfixDict.t) * Ast.Str.strdec) =
        if isReserved Token.Structure i then
          let val (i, dec) = consume_strdecStructure infdict (tok i) (i + 1)
          in ((i, infdict), dec)
          end
        else if isReserved Token.Local i then
          consume_strdecLocalInEnd (tok i) (i + 1, infdict)
        else
          let
            val ((i, infdict), dec) =
              ParseExpAndDec.dec {forceExactlyOne = true, ctx = ctx} toks
                (i, infdict)
          in
            ((i, infdict), Ast.Str.DecCore dec)
          end


      and consume_strdec (i, infdict) =
        let
          fun consume_maybeSemicolon (i, infdict) =
            if isReserved Token.Semicolon i then
              ((i + 1, infdict), SOME (tok i))
            else
              ((i, infdict), NONE)

          fun continue (i, _) =
            check Token.isDecStartToken i
            orelse check Token.isStrDecStartToken i

          (** While we see a strdec start-token, parse pairs of
            *   (dec, semicolon option)
            * The "state" in this computation is a pair (i, infdict), because
            * declarations can affect local infixity.
            *)
          val ((i, infdict), strdecs) =
            parse_zeroOrMoreWhile continue
              (parse_two (consume_exactlyOneStrdec, consume_maybeSemicolon))
              (i, infdict)

          fun makeDecMultiple () =
            Ast.Str.DecMultiple
              {elems = Seq.map #1 strdecs, delims = Seq.map #2 strdecs}

          val result =
            case Seq.length strdecs of
              0 => Ast.Str.DecEmpty
            | 1 =>
                let val (dec, semicolon) = Seq.nth strdecs 0
                in if isSome semicolon then makeDecMultiple () else dec
                end
            | _ => makeDecMultiple ()
        in
          ((i, infdict), result)
        end

      (** ====================================================================
        * Functors
        *)

      (** functor funid ( arg ) [constraint] = strexp [and ...]
        *        ^
        *
        * arg can be one of the following:
        *   sigid : sigexp
        *   spec
        *
        * constraint can be one of these:
        *   : sigexp
        *   :> sigexp
        *)
      fun consume_fundec infdict functorr i =
        let
          fun parse_maybeConstraint infdict i =
            if isReserved Token.Colon i orelse isReserved Token.ColonArrow i then
              let
                val (i, colon) = (i + 1, tok i)
                val (i, sigexp) = consume_sigExp infdict i
              in
                (i, SOME {colon = colon, sigexp = sigexp})
              end
            else
              (i, NONE)

          fun parse_funarg infdict i =
            if not (check Token.isStrIdentifier i) then
              let val (i, spec) = consume_sigSpec infdict i
              in (i, Ast.Fun.ArgSpec spec)
              end
            else
              let
                val (i, strid) = (i + 1, tok i)
                val (i, colon) = parse_reserved Token.Colon i
                val (i, sigexp) = consume_sigExp infdict i
              in
                ( i
                , Ast.Fun.ArgIdent
                    {strid = strid, colon = colon, sigexp = sigexp}
                )
              end

          fun parseOne i =
            let
              val (i, funid) = parse_funid i
              val (i, lparen) = parse_reserved Token.OpenParen i
              val (i, funarg) = parse_funarg infdict i
              val (i, rparen) = parse_reserved Token.CloseParen i
              val (i, constraint) = parse_maybeConstraint infdict i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, strexp) = consume_strexp infdict i
            in
              ( i
              , { funid = funid
                , lparen = lparen
                , funarg = funarg
                , rparen = rparen
                , constraint = constraint
                , eq = eq
                , strexp = strexp
                }
              )
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i
        in
          ( (i, infdict)
          , Ast.FunDec
              (Ast.Fun.DecFunctor
                 {functorr = functorr, elems = elems, delims = delims})
          )
        end


      fun consume_MLtonOverload underscore i =
        let
          fun err () =
            ParserUtils.error
              { pos = Token.getSource underscore
              , what = "Unexpected token."
              , explain = SOME "Expected beginning of top-level declaration."
              }
        in
          if i >= numToks then
            err ()
          else
            let
              val nextTok = tok i
              val isMLtonThing =
                Token.isIdentifier nextTok
                andalso
                case Source.toString (Token.getSource nextTok) of
                  "overload" => true
                | _ => false
              val _ = if isMLtonThing then () else err ()
              val (i, overload) = (i + 1, nextTok)
              val (i, prec) =
                if check Token.isDecimalIntegerConstant i then
                  (i + 1, tok i)
                else
                  ParserUtils.error
                    { pos = Token.getSource underscore
                    , what = "Unexpected token."
                    , explain = SOME "Expected integer literal."
                    }
              val (i, name) = parse_vid i
              val (i, colon) = parse_reserved Token.Colon i
              val (i, ty) = parse_ty i
              val (i, ass) = parse_reserved Token.As i

              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parse_longvid, delim = Token.And} i
            in
              ( i
              , Ast.Str.MLtonOverload
                  { underscore = underscore
                  , overload = overload
                  , prec = prec
                  , name = name
                  , colon = colon
                  , ty = ty
                  , ass = ass
                  , elems = elems
                  , delims = delims
                  }
              )
            end
        end


      (** ====================================================================
        * Top-level
        *)

      fun consume_topDecOne (i, infdict) : ((int * InfixDict.t) * Ast.topdec) =
        if
          isReserved Token.Signature at i
        then
          consume_sigDec (i + 1, infdict)
        else if
          isReserved Token.Functor at i
        then
          consume_fundec infdict (tok i) (i + 1)
        else if
          check Token.isStrDecStartToken at i
          orelse check Token.isDecStartToken at i
        then
          let val (xx, strdec) = consume_strdec (i, infdict)
          in (xx, Ast.StrDec strdec)
          end
        else if
          isReserved Token.Underscore i
        then
          let val (i, strdec) = consume_MLtonOverload (tok i) (i + 1)
          in ((i, infdict), Ast.StrDec strdec)
          end
        else if
          ParserContext.topExp ctx
        then
          let
            val (i, exp) =
              ParseExpAndDec.exp ctx toks infdict ExpPatRestriction.None i
            val (i, semicolon) = ParseSimple.reserved toks Token.Semicolon i
          in
            ((i, infdict), Ast.TopExp {exp = exp, semicolon = semicolon})
          end
        else
          ParserUtils.tokError toks
            { pos = i
            , what = "Unexpected token."
            , explain = SOME
                "Invalid start of top-level declaration. If you want to \
                \allow top-level expressions, use the command-line \
                \argument `-allow-top-level-exps true`."
            }

      fun parse_topDecMaybeSemicolon (i, infdict) =
        let
          val ((i, infdict), topdec) = consume_topDecOne (i, infdict)
          val (i, semicolon) = ParseSimple.maybeReserved toks Token.Semicolon i
        in
          ((i, infdict), {topdec = topdec, semicolon = semicolon})
        end

      val ((i, infdict), topdecs) =
        parse_zeroOrMoreWhile (fn (i, _) => i < numToks)
          parse_topDecMaybeSemicolon (0, infdict)

      val _ =
        if i >= numToks then
          ()
        else
          ParserUtils.error
            { pos = Token.getSource (tok i)
            , what = "Unexpected token."
            , explain = SOME "Invalid start of top-level declaration."
            }
    in
      if numToks > 0 then
        (infdict, Ast (Ast.Ast topdecs))
      else
        let
          val commentsOnly = Seq.filter Token.isComment allTokens
        in
          if Seq.length commentsOnly > 0 then
            (infdict, JustComments commentsOnly)
          else
            (infdict, Ast (Ast.Ast topdecs))
        end
    end


  fun parse ctx allTokens =
    let
      val (_, result) =
        parseWithInfdict ctx InfixDict.initialTopLevel allTokens
    in
      result
    end


end
