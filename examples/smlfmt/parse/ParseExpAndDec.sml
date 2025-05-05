(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParseExpAndDec:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t

  val dec: {forceExactlyOne: bool, ctx: ParserContext.t}
           -> tokens
           -> (int * InfixDict.t, Ast.Exp.dec) parser

  val exp: ParserContext.t
           -> tokens
           -> InfixDict.t
           -> ExpPatRestriction.t
           -> (int, Ast.Exp.exp) parser
end =
struct

  structure PC = ParserCombinators
  structure PS = ParseSimple
  structure PT = ParseTy
  structure PP = ParsePat

  structure Restriction = ExpPatRestriction

  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t


  (** ========================================================================
    * Handle infix expressions and patterns by rotating AST according to
    * operator precedence.
    *
    * TODO: DRY: makeInfixExp and makeInfixPat are nearly identical.
    *)

  fun makeInfixExp infdict (left, id, right) =
    let
      val hp = InfixDict.higherPrecedence infdict
      val sp = InfixDict.samePrecedence infdict
      val aLeft = InfixDict.associatesLeft infdict
      val aRight = InfixDict.associatesRight infdict

      fun bothLeft (x, y) = aLeft x andalso aLeft y
      fun bothRight (x, y) = aRight x andalso aRight y

      val default = Ast.Exp.Infix {left = left, id = id, right = right}
    in
      case right of
        Ast.Exp.Infix {left = rLeft, id = rId, right = rRight} =>
          if hp (rId, id) orelse (sp (rId, id) andalso bothRight (rId, id)) then
            default
          else if hp (id, rId) orelse (sp (rId, id) andalso bothLeft (rId, id)) then
            Ast.Exp.Infix
              { left = makeInfixExp infdict (left, id, rLeft)
              , id = rId
              , right = rRight
              }
          else
            ParserUtils.error
              { pos = Token.getSource rId
              , what = "Ambiguous infix expression."
              , explain = SOME
                  "You are not allowed to mix left- and right-associative \
                  \operators of same precedence"
              }

      | _ => default
    end


  fun updateInfixDict infdict dec =
    let
      fun parsePrec p =
        case p of
          NONE => 0
        | SOME x =>
            case Int.fromString (Token.toString x) of
              SOME y => y
            | NONE => raise Fail "Bug: updateInfixDict.parsePrec"
    in
      case dec of
        Ast.Exp.DecInfix {precedence, elems, ...} =>
          let
            val p = parsePrec precedence
            fun mk tok = (tok, p, InfixDict.AssocLeft)
          in
            Seq.iterate (fn (d, tok) => InfixDict.setInfix d (mk tok)) infdict
              elems
          end

      | Ast.Exp.DecInfixr {precedence, elems, ...} =>
          let
            val p = parsePrec precedence
            fun mk tok = (tok, p, InfixDict.AssocRight)
          in
            Seq.iterate (fn (d, tok) => InfixDict.setInfix d (mk tok)) infdict
              elems
          end

      | Ast.Exp.DecNonfix {elems, ...} =>
          Seq.iterate (fn (d, tok) => InfixDict.setNonfix d tok) infdict elems

      | _ => raise Fail "Bug: updateInfixDict: argument is not an infixity dec"
    end

  (** ========================================================================
    *)

  (** TODO: clean this shit up. This is a total mess.
    * See use in afterExp, below.
    *)
  fun endsCurrentExp infdict restrict tok =
    Token.endsCurrentExp tok
    orelse
    (not (Restriction.infOkay restrict) andalso Token.isValueIdentifier tok
     andalso InfixDict.isInfix infdict tok)
    orelse
    (not (Restriction.anyOkay restrict)
     andalso
     case Token.getClass tok of
       Token.Reserved rc =>
         List.exists (fn rc' => rc = rc')
           [Token.Colon, Token.Handle, Token.Andalso, Token.Orelse]
     | _ => false)

  (** ========================================================================
    *)


  fun dec {forceExactlyOne, ctx} toks (start, infdict) =
    let
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
      fun parse_tyvars i = PS.tyvars toks i
      fun parse_maybeReserved rc i =
        PS.maybeReserved toks rc i
      fun parse_vid i = PS.vid toks i
      fun parse_longvid i = PS.longvid toks i
      fun parse_tycon i = PS.tycon toks i
      fun parse_ty i = PT.ty toks i
      fun parse_pat infdict restriction i =
        PP.pat ctx toks infdict restriction i


      fun parse_oneOrMoreDelimitedByReserved x i =
        PC.oneOrMoreDelimitedByReserved toks x i
      fun parse_two (p1, p2) state =
        PC.two (p1, p2) state
      fun parse_zeroOrMoreWhile c p s =
        PC.zeroOrMoreWhile c p s

      fun consume_exp infdict restriction i =
        exp ctx toks infdict restriction i


      (* This function is duplicated in ParseSigExpAndSpec. *)
      fun parse_typbind i =
        let
          fun parseElem i =
            let
              val (i, tyvars) = parse_tyvars i
              val (i, tycon) = parse_tycon i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, ty) = parse_ty i
            in
              (i, {tyvars = tyvars, tycon = tycon, eq = eq, ty = ty})
            end

          val (i, typbind) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.And} i
        in
          (i, typbind)
        end


      and parse_datbind i =
        let
          fun parseConbind i =
            let
              val (i, opp) = parse_maybeReserved Token.Op i
              val (i, id) = parse_vid i
              val (i, arg) =
                if not (isReserved Token.Of at i) then
                  (i, NONE)
                else
                  let
                    val off = tok i
                    val (i, ty) = parse_ty (i + 1)
                  in
                    (i, SOME {off = off, ty = ty})
                  end
            in
              (i, {opp = opp, id = id, arg = arg})
            end

          fun parseElem i =
            let
              val (i, tyvars) = parse_tyvars i
              val (i, tycon) = parse_vid i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, optbar) = parse_maybeReserved Token.Bar i
              val _ = ParserUtils.checkOptBar ctx optbar
                "Unexpected bar on first branch of datatype declaration."

              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parseConbind, delim = Token.Bar} i
            in
              ( i
              , { tyvars = tyvars
                , tycon = tycon
                , eq = eq
                , elems = elems
                , delims = delims
                , optbar = optbar
                }
              )
            end

          val (i, datbind) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.And} i
        in
          (i, datbind)
        end


      fun consume_dec (i, infdict) =
        let
          fun consume_maybeSemicolon (i, infdict) =
            if isReserved Token.Semicolon at i then
              ((i + 1, infdict), SOME (tok i))
            else
              ((i, infdict), NONE)

          (** While we see a dec-start token, parse pairs of
            *   (dec, semicolon option)
            * The "state" in this computation is a pair (i, infdict), because
            * declarations can affect local infixity.
            *)
          val ((i, infdict), decs) =
            parse_zeroOrMoreWhile
              (fn (i, _) => check Token.isDecStartToken at i)
              (parse_two (consume_oneDec, consume_maybeSemicolon)) (i, infdict)

          fun makeDecMultiple () =
            Ast.Exp.DecMultiple
              {elems = Seq.map #1 decs, delims = Seq.map #2 decs}

          val result =
            case Seq.length decs of
              0 => Ast.Exp.DecEmpty
            | 1 =>
                let val (dec, semicolon) = Seq.nth decs 0
                in if isSome semicolon then makeDecMultiple () else dec
                end
            | _ => makeDecMultiple ()
        in
          ((i, infdict), result)
        end


      and consume_oneDec (i, infdict) =
        if isReserved Token.Val at i then
          consume_decVal (i + 1, infdict)
        else if isReserved Token.Type at i then
          consume_decType (i + 1, infdict)
        else if isReserved Token.Infix at i then
          consume_decInfix {isLeft = true} (i + 1, infdict)
        else if isReserved Token.Infixr at i then
          consume_decInfix {isLeft = false} (i + 1, infdict)
        else if isReserved Token.Nonfix at i then
          consume_decNonfix (i + 1, infdict)
        else if isReserved Token.Fun at i then
          consume_decFun (i + 1, infdict)
        else if isReserved Token.Exception at i then
          consume_decException (tok i) (i + 1, infdict)
        else if isReserved Token.Local at i then
          consume_decLocal (i + 1, infdict)
        else if isReserved Token.Datatype at i then
          consume_decDatatypeDeclarationOrReplication (i + 1, infdict)
        else if isReserved Token.Open at i then
          consume_decOpen (tok i) (i + 1, infdict)
        else if isReserved Token.Abstype at i then
          consume_decAbstype (tok i) (i + 1, infdict)
        else
          ParserUtils.tokError toks
            { pos = i
            , what = "Unexpected token."
            , explain = SOME "Expected to see the beginning of a declaration."
            }


      (** abstype datbind [withtype typbind] with dec end
        *        ^
        *)
      and consume_decAbstype abstypee (i, infdict) =
        let
          val (i, datbind) = parse_datbind i
          val (i, withtypeClause) =
            if isReserved Token.Withtype i then
              let
                val (i, withtypee) = (i + 1, tok i)
                val (i, typbind) = parse_typbind i
              in
                (i, SOME {withtypee = withtypee, typbind = typbind})
              end
            else
              (i, NONE)

          val (i, withh) = parse_reserved Token.With i
          val ((i, _), dec) = consume_dec (i, infdict)
          val (i, endd) = parse_reserved Token.End i
        in
          ( (i, infdict)
          , Ast.Exp.DecAbstype
              { abstypee = abstypee
              , datbind = datbind
              , withtypee = withtypeClause
              , withh = withh
              , dec = dec
              , endd = endd
              }
          )
        end


      (** open longstrid ... longstrid
        *     ^
        *)
      and consume_decOpen openn (i, infdict) =
        let
          val (i, elems) =
            PC.oneOrMoreWhile (check Token.isMaybeLongStrIdentifier)
              (fn i => (i + 1, MaybeLongToken.make (tok i))) i
        in
          ((i, infdict), Ast.Exp.DecOpen {openn = openn, elems = elems})
        end


      (** exception exbind
        *          ^
        *)
      and consume_decException exceptionn (i, infdict) =
        let
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = consume_decExbind, delim = Token.And} i
        in
          ( (i, infdict)
          , Ast.Exp.DecException
              {exceptionn = exceptionn, elems = elems, delims = delims}
          )
        end


      (**  [op] vid [of ty]
        * ^
        *
        * OR
        *
        *  [op] vid = [op] longvid
        * ^
        *)
      and consume_decExbind i =
        let
          val (i, opp) = parse_maybeReserved Token.Op i
          val (i, vid) = parse_vid i
        in
          if isReserved Token.Of at i then
            let
              val (i, off) = (i + 1, tok i)
              val (i, ty) = parse_ty i
            in
              ( i
              , Ast.Exp.ExnNew
                  {opp = opp, id = vid, arg = SOME {off = off, ty = ty}}
              )
            end

          else if isReserved Token.Equal at i then
            let
              val (i, eq) = (i + 1, tok i)
              val (i, opp) = parse_maybeReserved Token.Op i
              val (i, longvid) = parse_longvid i
            in
              ( i
              , Ast.Exp.ExnReplicate
                  {opp = opp, left_id = vid, eq = eq, right_id = longvid}
              )
            end

          else
            (i, Ast.Exp.ExnNew {opp = opp, id = vid, arg = NONE})
        end


      (** fun tyvarseq [op]vid atpat ... atpat [: ty] = exp [| ...] [and ...]
        *    ^
        *)
      and consume_decFun (i, infdict) =
        let
          (** [op]vid atpat .... atpat [: ty] = exp [| ...] *)
          fun parseElem i =
            let
              (** [op]vid atpat ... atpat [: ty] = exp *)
              fun parseBranch (*vid*) i =
                let
                  val (i, fname_args) =
                    ParseFunNameArgs.fname_args ctx toks infdict i

                  val (i, ty) =
                    if not (isReserved Token.Colon at i) then
                      (i, NONE)
                    else
                      let
                        val colon = tok i
                        val (i, ty) = parse_ty (i + 1)
                      in
                        (i, SOME {colon = colon, ty = ty})
                      end
                  val (i, eq) = parse_reserved Token.Equal i
                  val (i, exp) = consume_exp infdict Restriction.None i
                in
                  (i, {fname_args = fname_args, ty = ty, eq = eq, exp = exp})
                end

              val (i, optbar) = parse_maybeReserved Token.Bar i
              val _ = ParserUtils.checkOptBar ctx optbar
                "Unexpected bar on first branch of 'fun'."
              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parseBranch, delim = Token.Bar} i
            in
              (i, {elems = elems, delims = delims, optbar = optbar})
            end

          val funn = tok (i - 1)
          val (i, tyvars) = parse_tyvars i
          val (i, fvalbind) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.And} i

          val _ = Ast.Exp.checkValidFValBind fvalbind ParserUtils.error
        in
          ( (i, infdict)
          , Ast.Exp.DecFun {funn = funn, tyvars = tyvars, fvalbind = fvalbind}
          )
        end


      (** local dec1 in dec2 end
        *      ^
        *)
      and consume_decLocal (i, infdict) =
        let
          val original_infdict = infdict

          val locall = tok (i - 1)
          val ((i, infdict), dec1) = consume_dec (i, infdict)
          val (i, inn) = parse_reserved Token.In i
          val ((i, _), dec2) = consume_dec (i, infdict)
          val (i, endd) = parse_reserved Token.End i
        in
          ( (i, original_infdict)
          , Ast.Exp.DecLocal
              { locall = locall
              , left_dec = dec1
              , inn = inn
              , right_dec = dec2
              , endd = endd
              }
          )
        end


      (** infix [d] vid [vid ...]
        *      ^
        *)
      and consume_decInfix {isLeft} (i, infdict) =
        let
          val infixx = tok (i - 1)

          val (i, precedence) =
            if check Token.isDecimalIntegerConstant at i then
              (i + 1, SOME (tok i))
            else
              (i, NONE)

          fun loop acc i =
            if check Token.isValueIdentifier at i then
              loop (tok i :: acc) (i + 1)
            else
              (i, Seq.fromRevList acc)

          val (i, elems) = loop [] i

          val result =
            if Seq.length elems = 0 then
              ParserUtils.tokError toks
                { pos = i
                , what = "Unexpected token. Missing identifier."
                , explain = NONE
                }
            else if isLeft then
              Ast.Exp.DecInfix
                {infixx = infixx, precedence = precedence, elems = elems}
            else
              Ast.Exp.DecInfixr
                {infixrr = infixx, precedence = precedence, elems = elems}
        in
          ((i, updateInfixDict infdict result), result)
        end


      (** nonfix vid [vid ...]
        *       ^
        *)
      and consume_decNonfix (i, infdict) =
        let
          val nonfixx = tok (i - 1)

          fun loop acc i =
            if check Token.isValueIdentifier at i then
              loop (tok i :: acc) (i + 1)
            else
              (i, Seq.fromRevList acc)

          val (i, elems) = loop [] i

          val result =
            if Seq.length elems = 0 then
              ParserUtils.tokError toks
                { pos = i
                , what = "Unexpected token. Missing identifier."
                , explain = NONE
                }
            else
              Ast.Exp.DecNonfix {nonfixx = nonfixx, elems = elems}
        in
          ((i, updateInfixDict infdict result), result)
        end


      (** type tyvars tycon = ty [and tyvars tycon = ty ...]
        *     ^
        *)
      and consume_decType (i, infdict) =
        let
          val typee = tok (i - 1)
          val (i, typbind) = parse_typbind i
        in
          ((i, infdict), Ast.Exp.DecType {typee = typee, typbind = typbind})
        end


      (** datatype datbind <withtype typbind>
        *         ^
        * OR
        * datatype tycon = datatype longtycon
        *         ^
        *)
      and consume_decDatatypeDeclarationOrReplication (i, infdict) =
        if
          (isReserved Token.OpenParen at i (* datatype ('a, ...) foo *)
           orelse check Token.isTyVar at i (* datatype 'a foo *)
           orelse
           ( (* datatype foo = A *)
             check Token.isValueIdentifierNoEqual at i
             andalso isReserved Token.Equal at (i + 1)
             andalso not (isReserved Token.Datatype at (i + 2))))
        then
          let
            val datatypee = tok (i - 1)
            val (i, datbind) = parse_datbind i
            val (i, withtypee) =
              if not (isReserved Token.Withtype at i) then
                (i, NONE)
              else
                let
                  val withtypee = tok i
                  val (i, typbind) = parse_typbind (i + 1)
                in
                  (i, SOME {withtypee = withtypee, typbind = typbind})
                end
          in
            ( (i, infdict)
            , Ast.Exp.DecDatatype
                { datatypee = datatypee
                , datbind = datbind
                , withtypee = withtypee
                }
            )
          end
        else
          let
            val left_datatypee = tok (i - 1)
            val (i, left_id) = parse_vid i
            val (i, eq) = parse_reserved Token.Equal i
            val (i, right_datatypee) = parse_reserved Token.Datatype i
            val (i, right_id) = parse_longvid i
          in
            ( (i, infdict)
            , Ast.Exp.DecReplicateDatatype
                { left_datatypee = left_datatypee
                , left_id = left_id
                , eq = eq
                , right_datatypee = right_datatypee
                , right_id = right_id
                }
            )
          end


      (** val tyvarseq [rec] pat = exp [and [rec] pat = exp ...]
        *     ^
        *)
      and consume_decVal (i, infdict) =
        let
          (**  [rec] pat = exp
            * ^
            *)
          fun parseElem i =
            let
              val (i, recc) = parse_maybeReserved Token.Rec i
              val (i, pat) = parse_pat infdict Restriction.None i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, exp) = consume_exp infdict Restriction.None i
            in
              (i, {recc = recc, pat = pat, eq = eq, exp = exp})
            end

          val vall = tok (i - 1)
          val (i, tyvars) = parse_tyvars i
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.And} i
        in
          ( (i, infdict)
          , Ast.Exp.DecVal
              {vall = vall, tyvars = tyvars, elems = elems, delims = delims}
          )
        end

    in
      if forceExactlyOne then consume_oneDec (start, infdict)
      else consume_dec (start, infdict)
    end


  (* ======================================================================= *)
  (* ======================================================================= *)
  (* ======================================================================= *)


  and exp ctx toks infdict restriction start =
    let
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
      fun parse_maybeReserved rc i =
        PS.maybeReserved toks rc i
      fun parse_longvid i = PS.longvid toks i
      fun parse_recordLabel i = PS.recordLabel toks i
      fun parse_ty i = PT.ty toks i
      fun parse_pat infdict restriction i =
        PP.pat ctx toks infdict restriction i


      fun parse_zeroOrMoreDelimitedByReserved x i =
        PC.zeroOrMoreDelimitedByReserved toks x i
      fun parse_oneOrMoreDelimitedByReserved x i =
        PC.oneOrMoreDelimitedByReserved toks x i
      fun parse_zeroOrMoreWhile c p s =
        PC.zeroOrMoreWhile c p s


      fun consume_dec xx =
        dec {forceExactlyOne = false, ctx = ctx} toks xx


      fun consume_exp infdict restriction i =
        let
          val (i, exp) =
            if check Token.isConstant at i then
              (i + 1, Ast.Exp.Const (tok i))
            else if isReserved Token.OpenParen at i then
              consume_expParensOrTupleOrUnitOrSequence infdict (tok i) (i + 1)
            else if isReserved Token.OpenSquareBracket at i then
              consume_expListLiteral infdict (i + 1)
            else if isReserved Token.OpenCurlyBracket at i then
              consume_expRecord infdict (tok i) (i + 1)
            else if isReserved Token.Let at i then
              consume_expLetInEnd infdict (i + 1)
            else if isReserved Token.Op at i then
              consume_expValueIdentifier infdict (SOME (tok i)) (i + 1)
            else if check Token.isMaybeLongIdentifier at i then
              consume_expValueIdentifier infdict NONE i
            else if isReserved Token.Case at i then
              consume_expCase infdict (i + 1)
            else if isReserved Token.Hash at i then
              consume_expSelect (tok i) (i + 1)
            else if isReserved Token.If at i then
              if Restriction.anyOkay restriction then
                consume_expIfThenElse infdict (tok i) (i + 1)
              else
                ParserUtils.tokError toks
                  { pos = i
                  , what = "Unexpected if-then-else expression."
                  , explain = SOME
                      "Try using parentheses: (if ... then ... else ...)"
                  }

            else if isReserved Token.Raise at i then
              if Restriction.anyOkay restriction then
                consume_expRaise infdict (i + 1)
              else
                ParserUtils.tokError toks
                  { pos = i
                  , what = "Unexpected raise exception."
                  , explain = SOME "Try using parentheses: (raise ...)"
                  }

            else if isReserved Token.Fn at i then
              if Restriction.anyOkay restriction then
                consume_expFn infdict (i + 1)
              else
                ParserUtils.tokError toks
                  { pos = i
                  , what = "Unexpected beginning of anonymous function."
                  , explain = SOME "Try using parentheses: (fn ... => ...)"
                  }

            else if isReserved Token.While at i then
              if Restriction.anyOkay restriction then
                consume_expWhile infdict (i + 1)
              else
                ParserUtils.tokError toks
                  { pos = i
                  , what = "Unexpected beginning of while-loop."
                  , explain = SOME "Try using parentheses: (while ... do ...)"
                  }

            else if isReserved Token.Underscore i then
              consume_expAfterUnderscore (tok i) (i + 1)

            else
              ParserUtils.tokError toks
                { pos = i
                , what = "Unexpected token."
                , explain = SOME "Expected beginning of expression."
                }
        in
          consume_afterExp infdict restriction exp i
        end


      (** exp ...
        *    ^
        *
        * Multiple possibilities for what could be found after an expression:
        *   exp : ty              -- type annotation
        *   exp handle ...        -- handle exception
        *   infexp vid infexp     -- infix application
        *   appexp atexp          -- application
        *   exp andalso exp
        *   exp orelse exp
        *
        * Or, to definitely pop back up, we might see
        *   exp )            -- end of parens, tuple, etc.
        *   exp ,            -- continue tuple
        *   exp ;            -- continue sequence
        *   exp |            -- next in match
        *   exp (then|else)  -- if ... then ... else
        *   exp do           -- while ... do ...
        *   exp of           -- case ... of
        *)
      and consume_afterExp infdict restriction exp i =
        let
          val (again, (i, exp)) =
            if
              i >= numToks
              orelse check (endsCurrentExp infdict restriction) at i
            then (false, (i, exp))

            else if
              isReserved Token.Colon at i
            then (true, consume_expTyped exp (i + 1))

            else if
              isReserved Token.Handle at i
            then (true, consume_expHandle infdict exp (i + 1))

            else if
              isReserved Token.Andalso at i orelse isReserved Token.Orelse at i
            then (true, consume_expAndalsoOrOrelse infdict exp (i + 1))

            else if
              Restriction.infOkay restriction andalso Ast.Exp.isInfExp exp
              andalso check Token.isValueIdentifier at i
              andalso InfixDict.isInfix infdict (tok i)
            then (true, consume_expInfix infdict exp (i + 1))

            else if
              Restriction.appOkay restriction
            then (true, consume_expApp infdict exp i)

            else (false, (i, exp))
        in
          if again then consume_afterExp infdict restriction exp i else (i, exp)
        end


      (** _
        *  ^
        *
        * This is a bit awkward, but we're trying to handle MLton-specific
        * code here, e.g. _prim and _import.
        *)
      and consume_expAfterUnderscore underscore i =
        let
          fun err () =
            ParserUtils.error
              { pos = Token.getSource underscore
              , what = "Unexpected token."
              , explain = SOME "Expected beginning of expression."
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
                  "prim" => true
                | "import" => true
                | "command_line_const" => true
                | "build_const" => true
                | "const" => true
                | "symbol" => true
                | _ => false
              val _ =
                if isMLtonThing (*andalso Restriction.anyOkay restriction*) then
                  ()
                else
                  err ()
              val directive = nextTok
              val (i, contents) =
                parse_zeroOrMoreWhile (fn i => not (check Token.isSemicolon i))
                  (fn i => (i + 1, tok i)) (i + 1)
              val (i, semicolon) = (i + 1, tok i)
            in
              ( i
              , Ast.Exp.MLtonSpecific
                  { underscore = underscore
                  , directive = directive
                  , contents = contents
                  , semicolon = semicolon
                  }
              )

            (* consume_afterExp infdict restriction exp (i+1) *)
            end
        end


      (** { label = exp [, ...] }
        *  ^
        *)
      and consume_expRecord infdict left i =
        let
          fun parseElem i =
            let
              val (i, lab) = parse_recordLabel i
            in
              if
                isReserved Token.Comma at i
                orelse isReserved Token.CloseCurlyBracket at i
              then
                if ParserContext.recordPun ctx then
                  (i, Ast.Exp.RecordPun {id = lab})
                else
                  ParserUtils.error
                    { pos = Token.getSource lab
                    , what = "Incomplete row in record expression."
                    , explain = SOME
                        "In Standard ML, each element of a record expression must \
                        \look like: `<label> = <expression>`. Note that SuccessorML \
                        \allows for \"record punning\", where (for example) the syntax \
                        \`{x, y, z = foo}` is shorthand for `{x = x, y = y, z = foo}`. \
                        \To enable this feature, use the command-line argument \
                        \'-allow-record-pun-exps true'."
                    }
              else
                let
                  val (i, eq) = parse_reserved Token.Equal i
                  val (i, exp) = consume_exp infdict Restriction.None i
                in
                  (i, Ast.Exp.RecordRow {lab = lab, eq = eq, exp = exp})
                end
            end

          val (i, {elems, delims}) =
            parse_zeroOrMoreDelimitedByReserved
              { parseElem = parseElem
              , delim = Token.Comma
              , shouldStop = isReserved Token.CloseCurlyBracket
              } i

          val (i, right) = parse_reserved Token.CloseCurlyBracket i
        in
          ( i
          , Ast.Exp.Record
              {left = left, elems = elems, delims = delims, right = right}
          )
        end


      (** # lab
        *  ^
        *)
      and consume_expSelect hash i =
        let val (i, lab) = parse_recordLabel i
        in (i, Ast.Exp.Select {hash = hash, label = lab})
        end


      and consume_expIfThenElse infdict iff i =
        let
          val (i, exp1) = consume_exp infdict Restriction.None i
          val (i, thenn) = parse_reserved Token.Then i
          val (i, exp2) = consume_exp infdict Restriction.None i
          val (i, elsee) = parse_reserved Token.Else i
          val (i, exp3) = consume_exp infdict Restriction.None i

          val result = Ast.Exp.IfThenElse
            { iff = iff
            , exp1 = exp1
            , thenn = thenn
            , exp2 = exp2
            , elsee = elsee
            , exp3 = exp3
            }

          (** NOTE: this is technically a noop, because `raise` has low enough
            * precedence that the left rotation will never happen. But I like
            * keeping the code here because it's informative.
            *)
          val result = FixExpPrecedence.maybeRotateLeft result
        in
          (i, result)
        end


      (** [ ... ]
        *  ^
        *)
      and consume_expListLiteral infdict i =
        let
          val openBracket = tok (i - 1)

          fun finish elems delims closeBracket =
            Ast.Exp.List
              { left = openBracket
              , right = closeBracket
              , elems = elems
              , delims = delims
              }
        in
          if isReserved Token.CloseSquareBracket at i then
            (i + 1, finish (Seq.empty ()) (Seq.empty ()) (tok i))
          else
            let
              val parseElem = consume_exp infdict Restriction.None
              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parseElem, delim = Token.Comma} i
              val (i, closeBracket) = parse_reserved Token.CloseSquareBracket i
            in
              (i, finish elems delims closeBracket)
            end
        end


      (** case exp of match
        *     ^
        *)
      and consume_expCase infdict i =
        let
          val casee = tok (i - 1)
          val (i, exp) = consume_exp infdict Restriction.None i
          val (i, off) = parse_reserved Token.Of i
          val (i, optbar) = parse_maybeReserved Token.Bar i
          val _ = ParserUtils.checkOptBar ctx optbar
            "Unexpected bar on first branch of 'case'."

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = consume_matchElem infdict, delim = Token.Bar} i
        in
          ( i
          , Ast.Exp.Case
              { casee = casee
              , exp = exp
              , off = off
              , elems = elems
              , delims = delims
              , optbar = optbar
              }
          )
        end


      (**  pat => exp
        * ^
        *)
      and consume_matchElem infdict i =
        let
          val (i, pat) = parse_pat infdict Restriction.None i
          val (i, arrow) = parse_reserved Token.FatArrow i
          val (i, exp) = consume_exp infdict Restriction.None i
        in
          (i, {pat = pat, arrow = arrow, exp = exp})
        end


      (** fn pat => exp [| pat => exp ...]
        *   ^
        *)
      and consume_expFn infdict i =
        let
          val fnn = tok (i - 1)
          val (i, optbar) = parse_maybeReserved Token.Bar i
          val _ = ParserUtils.checkOptBar ctx optbar
            "Unexpected bar on first branch of anonymous function."

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = consume_matchElem infdict, delim = Token.Bar} i
        in
          ( i
          , Ast.Exp.Fn
              {fnn = fnn, elems = elems, delims = delims, optbar = optbar}
          )
        end


      (** [op] longvid
        *     ^
        *)
      and consume_expValueIdentifier infdict opp i =
        let
          val (i, vid) = parse_longvid i
          val _ =
            ParserUtils.errorIfInfixNotOpped infdict opp
              (MaybeLongToken.getToken vid)
        in
          (i, Ast.Exp.Ident {opp = opp, id = vid})
        end


      (** infexp1 vid infexp2
        *            ^
        *)
      and consume_expInfix infdict exp1 i =
        let
          (* val _ = print ("infix\n") *)

          val id = tok (i - 1)
          val (i, exp2) = consume_exp infdict Restriction.Inf i
        in
          (i, makeInfixExp infdict (exp1, id, exp2))
        end


      (** appexp atexp
        *       ^
        *)
      and consume_expApp infdict leftExp i =
        let
          (* val _ = print ("app\n") *)

          val (i, rightExp) = consume_exp infdict Restriction.At i
        in
          (i, Ast.Exp.App {left = leftExp, right = rightExp})
        end


      (** raise exp
        *      ^
        *)
      and consume_expRaise infdict i =
        let
          val raisee = tok (i - 1)
          val (i, exp) = consume_exp infdict Restriction.None i

          val result = Ast.Exp.Raise {raisee = raisee, exp = exp}

          (** NOTE: this is technically a noop, because `raise` has low enough
            * precedence that the left rotation will never happen. But I like
            * keeping the code here because it's informative.
            *)
          val result = FixExpPrecedence.maybeRotateLeft result
        in
          (i, result)
        end


      (** exp handle ...
        *           ^
        *)
      and consume_expHandle infdict exp i =
        let
          val handlee = tok (i - 1)
          val (i, optbar) = parse_maybeReserved Token.Bar i
          val _ = ParserUtils.checkOptBar ctx optbar
            "Unexpected bar on first branch of 'handle'."
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = consume_matchElem infdict, delim = Token.Bar} i

          val result = Ast.Exp.Handle
            { exp = exp
            , handlee = handlee
            , elems = elems
            , delims = delims
            , optbar = optbar
            }

          val result = FixExpPrecedence.maybeRotateLeft result
        in
          (i, result)
        end


      (** exp1 (andalso|orelse) exp2
        *                      ^
        *)
      and consume_expAndalsoOrOrelse infdict exp1 i =
        let
          val junct = tok (i - 1)
          val (i, exp2) = consume_exp infdict Restriction.None i

          val result =
            if Token.isAndalso junct then
              Ast.Exp.Andalso {left = exp1, andalsoo = junct, right = exp2}
            else if Token.isOrelse junct then
              Ast.Exp.Orelse {left = exp1, orelsee = junct, right = exp2}
            else
              raise Fail "Bug: Parser.parse.consume_expAndalsoOrOrelse"

          val result = FixExpPrecedence.maybeRotateLeft result
        in
          (i, result)
        end


      (** while exp1 do exp2
        *      ^
        *)
      and consume_expWhile infdict i =
        let
          val whilee = tok (i - 1)
          val (i, exp1) = consume_exp infdict Restriction.None i
          val (i, doo) = parse_reserved Token.Do i
          val (i, exp2) = consume_exp infdict Restriction.None i

          val result = Ast.Exp.While
            {whilee = whilee, exp1 = exp1, doo = doo, exp2 = exp2}

          val result = FixExpPrecedence.maybeRotateLeft result
        in
          (i, result)
        end


      (** exp : ty
        *      ^
        *)
      and consume_expTyped exp i =
        let
          (* val _ = print ("typed\n") *)

          val colon = tok (i - 1)
          val (i, ty) = parse_ty i
        in
          (i, Ast.Exp.Typed {exp = exp, colon = colon, ty = ty})
        end


      (** ================================================================= *)


      (** let dec in exp [; exp ...] end
        *    ^
        *)
      and consume_expLetInEnd infdict i =
        let
          val lett = tok (i - 1)
          val ((i, infdict), dec) = consume_dec (i, infdict)
          val (i, inn) =
            parse_reserved Token.In i
            handle Error.Error e =>
              if i >= numToks then
                raise Error.Error e
              else
                raise Error.Error
                  { header = "PARSE ERROR"
                  , content =
                      [ Error.Paragraph "Unexpected token."
                      , Error.SourceReference (Token.getSource (tok i))
                      , Error.Paragraph
                          "Expected to see 'in' or another declaration."
                      , Error.Paragraph
                          "The error\
                          \ occurred inside of this 'let':"
                      , Error.SourceReference (Token.getSource lett)
                      ]
                  }

          val parseElem = consume_exp infdict Restriction.None
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.Semicolon} i

          val (i, endd) = parse_reserved Token.End i
        in
          ( i
          , Ast.Exp.LetInEnd
              { lett = lett
              , dec = dec
              , inn = inn
              , exps = elems
              , delims = delims
              , endd = endd
              }
          )
        end


      (** ( )
        *  ^
        * OR
        * ( exp [, exp ...] )
        *  ^
        * OR
        * ( exp [; exp ...] )
        *  ^
        *)
      and consume_expParensOrTupleOrUnitOrSequence infdict leftParen i =
        if isReserved Token.CloseParen at i then
          (i + 1, Ast.Exp.Unit {left = leftParen, right = tok i})
        else
          let
            val parseElem = consume_exp infdict Restriction.None
            val (i, exp) = parseElem i
          in
            if isReserved Token.CloseParen at i then
              ( i + 1
              , Ast.Exp.Parens {left = leftParen, exp = exp, right = tok i}
              )
            else
              let
                val delimType =
                  if isReserved Token.Comma at i then
                    Token.Comma
                  else if isReserved Token.Semicolon at i then
                    Token.Semicolon
                  else
                    ParserUtils.error
                      { pos = Token.getSource leftParen
                      , what = "Unmatched paren."
                      , explain = NONE
                      }

                val (i, delim) = (i + 1, tok i)

                val (i, {elems, delims}) =
                  parse_oneOrMoreDelimitedByReserved
                    {parseElem = parseElem, delim = delimType} i

                val (i, rightParen) = parse_reserved Token.CloseParen i

                val stuff =
                  { left = leftParen
                  , elems = Seq.append (Seq.singleton exp, elems)
                  , delims = Seq.append (Seq.singleton delim, delims)
                  , right = rightParen
                  }
              in
                case delimType of
                  Token.Comma => (i, Ast.Exp.Tuple stuff)
                | _ => (i, Ast.Exp.Sequence stuff)
              end
          end

    in
      consume_exp infdict restriction start
    end

end
