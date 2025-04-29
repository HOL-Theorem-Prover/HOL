(** Copyright (c) 2021-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParseSigExpAndSpec:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t

  val spec: AstAllows.t -> tokens -> InfixDict.t -> (int, Ast.Sig.spec) parser
  val sigexp: AstAllows.t
              -> tokens
              -> InfixDict.t
              -> (int, Ast.Sig.sigexp) parser
end =
struct
  local open ParseSimple ParseTy ParsePat ExpPatRestriction in end

  structure PC = ParserCombinators
  structure PS = ParseSimple
  structure PT = ParseTy
  structure PP = ParsePat

  structure Restriction = ExpPatRestriction

  type ('state, 'result) parser = 'state -> ('state * 'result)
  type 'state peeker = 'state -> bool

  type tokens = Token.t Seq.t


  (** ========================================================================
    * sigexp
    *)

  fun parse_sigexp allows toks infdict i =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        i < numToks andalso f (tok i)
      fun isReserved rc =
        check (fn t => Token.Reserved rc = Token.getClass t)

      fun parse_reserved rc i =
        PS.reserved toks rc i
      fun parse_tyvars i = PS.tyvars toks i
      fun parse_sigid i = PS.sigid toks i
      fun parse_maybeLongTycon i = PS.maybeLongTycon toks i
      fun parse_ty i = PT.ty toks i


      fun parse_oneOrMoreWhile c p s =
        PC.oneOrMoreWhile c p s


      (** sigexp where type tyvarseq tycon = ty [and/where type ...]
        *       ^
        *)
      fun consume_sigExpWhereType sigexp i =
        let
          fun nextIsWhereOrAndType i =
            (isReserved Token.Where i orelse isReserved Token.And i)
            andalso (isReserved Token.Type (i + 1))

          fun parseOne i =
            let
              val (i, wheree) = (i + 1, tok i)
              val (i, typee) = parse_reserved Token.Type i
              val (i, tyvars) = parse_tyvars i
              val (i, tycon) = parse_maybeLongTycon i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, ty) = parse_ty i
            in
              ( i
              , { wheree = wheree
                , typee = typee
                , tyvars = tyvars
                , tycon = tycon
                , eq = eq
                , ty = ty
                }
              )
            end

          val (i, elems) = parse_oneOrMoreWhile nextIsWhereOrAndType parseOne i
        in
          (i, Ast.Sig.WhereType {sigexp = sigexp, elems = elems})
        end


      (** sig spec end
        *    ^
        *)
      and consume_sigExpSigEnd i =
        let
          val sigg = tok (i - 1)
          val (i, spec) = parse_spec allows toks infdict i
          val (i, endd) = parse_reserved Token.End i
        in
          (i, Ast.Sig.Spec {sigg = sigg, spec = spec, endd = endd})
        end


      and consume_sigExp i =
        let
          val (i, sigexp) =
            if isReserved Token.Sig i then
              consume_sigExpSigEnd (i + 1)
            else
              let val (i, sigid) = parse_sigid i
              in (i, Ast.Sig.Ident sigid)
              end
        in
          if isReserved Token.Where i then consume_sigExpWhereType sigexp i
          else (i, sigexp)
        end

    in
      consume_sigExp i
    end


  (** ========================================================================
    * ========================================================================
    *)


  and parse_spec allows toks infdict i =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i

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
      fun parse_tyvars i = PS.tyvars toks i
      fun parse_vid i = PS.vid toks i
      fun parse_longvid i = PS.longvid toks i
      fun parse_tycon i = PS.tycon toks i
      fun parse_maybeLongTycon i = PS.maybeLongTycon toks i
      fun parse_maybeLongStrid i = PS.maybeLongStrid toks i
      fun parse_ty i = PT.ty toks i


      fun parse_oneOrMoreDelimitedByReserved x i =
        PC.oneOrMoreDelimitedByReserved toks x i
      fun parse_two (p1, p2) state =
        PC.two (p1, p2) state
      fun parse_zeroOrMoreWhile c p s =
        PC.zeroOrMoreWhile c p s


      (* This function is duplicated in ParseExpAndDec. *)
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


      fun parse_datdesc i =
        let
          fun parse_condesc i =
            let
              val (i, vid) = parse_vid i
              val (i, arg) =
                if not (isReserved Token.Of i) then
                  (i, NONE)
                else
                  let
                    val off = tok i
                    val (i, ty) = parse_ty (i + 1)
                  in
                    (i, SOME {off = off, ty = ty})
                  end
            in
              (i, {vid = vid, arg = arg})
            end

          fun parseElem i =
            let
              val (i, tyvars) = parse_tyvars i
              val (i, tycon) = parse_vid i
              val (i, eq) = parse_reserved Token.Equal i
              val (i, optbar) = parse_maybeReserved Token.Bar i
              val _ = ParserUtils.checkOptBar allows optbar
                "Unexpected bar on first branch of datatype specification."

              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parse_condesc, delim = Token.Bar} i
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

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.And} i
        in
          (i, {elems = elems, delims = delims})
        end

      (** val vid : ty [and ...]
        *    ^
        *)
      fun consume_sigSpecVal i =
        let
          val vall = tok (i - 1)

          fun parseOne i =
            let
              val (i, vid) = parse_vid i
              val (i, colon) = parse_reserved Token.Colon i
              val (i, ty) = parse_ty i
            in
              (i, {vid = vid, colon = colon, ty = ty})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i
        in
          (i, Ast.Sig.Val {vall = vall, elems = elems, delims = delims})
        end


      (** type tyvarseq tycon = ty [and ...]
        *                         ^
        *)
      fun consume_sigSpecTypeAbbreviation typee firstElem i =
        if not (isReserved Token.And i) then
          ( i
          , Ast.Sig.TypeAbbreviation
              { typee = typee
              , typbind =
                  {elems = Seq.singleton firstElem, delims = Seq.empty ()}
              }
          )
        else
          let
            val (i, firstDelim) = (i + 1, tok i)
            val (i, {elems, delims}) = parse_typbind i
          in
            ( i
            , Ast.Sig.TypeAbbreviation
                { typee = typee
                , typbind =
                    { elems = Seq.append (Seq.singleton firstElem, elems)
                    , delims = Seq.append (Seq.singleton firstDelim, delims)
                    }
                }
            )
          end


      (** type tyvarseq tycon [and ...]
        *                    ^
        *)
      fun consume_sigSpecType typee firstElem i =
        if not (isReserved Token.And i) then
          ( i
          , Ast.Sig.Type
              { typee = typee
              , elems = Seq.singleton firstElem
              , delims = Seq.empty ()
              }
          )
        else
          let
            val (i, firstDelim) = (i + 1, tok i)

            fun parseOne i =
              let
                val (i, tyvars) = parse_tyvars i
                val (i, tycon) = parse_tycon i
              in
                (i, {tyvars = tyvars, tycon = tycon})
              end

            val (i, {elems, delims}) =
              parse_oneOrMoreDelimitedByReserved
                {parseElem = parseOne, delim = Token.And} i
          in
            ( i
            , Ast.Sig.Type
                { typee = typee
                , elems = Seq.append (Seq.singleton firstElem, elems)
                , delims = Seq.append (Seq.singleton firstDelim, delims)
                }
            )
          end


      fun consume_sigSpecTypeOrAbbreviation typee i =
        let
          val (i, tyvars) = parse_tyvars i
          val (i, tycon) = parse_tycon i
        in
          if isReserved Token.Equal i then
            let
              val (i, eq) = parse_reserved Token.Equal i
              val (i, ty) = parse_ty i
            in
              consume_sigSpecTypeAbbreviation typee
                {tyvars = tyvars, tycon = tycon, eq = eq, ty = ty} i
            end
          else
            consume_sigSpecType typee {tyvars = tyvars, tycon = tycon} i
        end


      (** eqtype tyvars tycon [and ...]
        *       ^
        *)
      fun consume_sigSpecEqtype i =
        let
          val eqtypee = tok (i - 1)

          fun parseOne i =
            let
              val (i, tyvars) = parse_tyvars i
              val (i, tycon) = parse_tycon i
            in
              (i, {tyvars = tyvars, tycon = tycon})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i
        in
          ( i
          , Ast.Sig.Eqtype {eqtypee = eqtypee, elems = elems, delims = delims}
          )
        end


      (** datatype datdesc <withtype typbind>
        *         ^
        * OR
        * datatype tycon = datatype longtycon
        *         ^
        *)
      fun consume_sigSpecDatatypeDeclarationOrReplication i =
        if
          (isReserved Token.OpenParen i (* datatype ('a, ...) foo *)
           orelse check Token.isTyVar i (* datatype 'a foo *)
           orelse
           ( (* datatype foo = A *)
             check Token.isValueIdentifierNoEqual i
             andalso isReserved Token.Equal (i + 1)
             andalso not (isReserved Token.Datatype (i + 2))))
        then
          let
            val datatypee = tok (i - 1)
            val (i, {elems, delims}) = parse_datdesc i
            val (i, withtypee) =
              if not (isReserved Token.Withtype at i) then
                (i, NONE)
              else if not (AstAllows.sigWithtype allows) then
                ParserUtils.tokError toks
                  { pos = i
                  , what = "Unexpected 'withtype' in signature."
                  , explain = SOME
                      "withtype in signatures is a disallowed SuccessorML \
                      \feature. To enable it, use the command-line argument \
                      \'-allow-sig-withtype true'."
                  }
              else
                let
                  val withtypee = tok i
                  val (i, typbind) = parse_typbind (i + 1)
                in
                  (i, SOME {withtypee = withtypee, typbind = typbind})
                end
          in
            ( i
            , Ast.Sig.Datatype
                { datatypee = datatypee
                , elems = elems
                , delims = delims
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
            ( i
            , Ast.Sig.ReplicateDatatype
                { left_datatypee = left_datatypee
                , left_id = left_id
                , eq = eq
                , right_datatypee = right_datatypee
                , right_id = right_id
                }
            )
          end


      (** exception vid [of ty] [and vid [of ty] ...]
        *          ^
        *)
      fun consume_sigSpecException i =
        let
          val exceptionn = tok (i - 1)
          fun parseOne i =
            let
              val (i, vid) = parse_vid i
              val (i, arg) =
                if not (isReserved Token.Of i) then
                  (i, NONE)
                else
                  let
                    val off = tok i
                    val (i, ty) = parse_ty (i + 1)
                  in
                    (i, SOME {off = off, ty = ty})
                  end
            in
              (i, {vid = vid, arg = arg})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i
        in
          ( i
          , Ast.Sig.Exception
              {exceptionn = exceptionn, elems = elems, delims = delims}
          )
        end


      (** spec sharing longstrid = ... = longstrid
        *             ^
        *)
      fun consume_sigSharing spec sharingg i =
        let
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_maybeLongStrid, delim = Token.Equal} i
        in
          ( i
          , Ast.Sig.Sharing
              {spec = spec, sharingg = sharingg, elems = elems, delims = delims}
          )
        end


      (** spec sharing type longtycon = ... = longtycon
        *                  ^
        *)
      fun consume_sigSharingType spec sharingg typee i =
        let
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_maybeLongTycon, delim = Token.Equal} i
        in
          ( i
          , Ast.Sig.SharingType
              { spec = spec
              , sharingg = sharingg
              , typee = typee
              , elems = elems
              , delims = delims
              }
          )
        end


      fun consume_afterSigSpec spec i =
        let
          val (again, (i, spec)) =
            if isReserved Token.Sharing i then
              if isReserved Token.Type (i + 1) then
                ( true
                , consume_sigSharingType spec (tok i) (tok (i + 1)) (i + 2)
                )
              else
                (true, consume_sigSharing spec (tok i) (i + 1))
            else
              (false, (i, spec))
        in
          if again then consume_afterSigSpec spec i else (i, spec)
        end


      (** structure strid : sigexp [and ...]
        *          ^
        *)
      fun consume_sigSpecStructure i =
        let
          val structuree = tok (i - 1)

          fun parseOne i =
            let
              val (i, id) = parse_vid i
              val (i, colon) = parse_reserved Token.Colon i
              val (i, sigexp) = parse_sigexp allows toks infdict i
            in
              (i, {id = id, colon = colon, sigexp = sigexp})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseOne, delim = Token.And} i
        in
          ( i
          , Ast.Sig.Structure
              {structuree = structuree, elems = elems, delims = delims}
          )
        end


      (** include sigexp
        *        ^
        * OR
        * include sigid ... sigid
        *        ^
        *)
      and consume_sigSpecInclude i =
        let
          val includee = tok (i - 1)
          val (i, sigexp) = parse_sigexp allows toks infdict i

          fun makeInclude i =
            (i, Ast.Sig.Include {includee = includee, sigexp = sigexp})

          fun makeIncludeIds firstId i =
            let
              val (i, ids) =
                PC.zeroOrMoreWhile (check Token.isStrIdentifier)
                  (fn i => (i + 1, tok i)) i
            in
              ( i
              , Ast.Sig.IncludeIds
                  { includee = includee
                  , sigids = Seq.append (Seq.singleton firstId, ids)
                  }
              )
            end

        in
          case sigexp of
            Ast.Sig.Ident id => makeIncludeIds id i
          | _ => makeInclude i
        end


      and consume_oneSigSpec i =
        let
          val (i, spec) =
            if isReserved Token.Val i then
              consume_sigSpecVal (i + 1)
            else if isReserved Token.Type i then
              consume_sigSpecTypeOrAbbreviation (tok i) (i + 1)
            else if isReserved Token.Eqtype i then
              consume_sigSpecEqtype (i + 1)
            else if isReserved Token.Datatype i then
              consume_sigSpecDatatypeDeclarationOrReplication (i + 1)
            else if isReserved Token.Exception i then
              consume_sigSpecException (i + 1)
            else if isReserved Token.Structure i then
              consume_sigSpecStructure (i + 1)
            else if isReserved Token.Include i then
              consume_sigSpecInclude (i + 1)
            else
              ParserUtils.tokError toks
                { pos = i
                , what = "Unexpected token."
                , explain = SOME "Expected element of signature."
                }
        in
          consume_afterSigSpec spec i
        end


      and consume_sigSpec i =
        let
          fun consume_maybeSemicolon i =
            if isReserved Token.Semicolon i then (i + 1, SOME (tok i))
            else (i, NONE)

          val (i, specs) =
            parse_zeroOrMoreWhile (fn i => check Token.isSigSpecStartToken i)
              (parse_two (consume_oneSigSpec, consume_maybeSemicolon)) i

          fun makeSpecMultiple () =
            Ast.Sig.Multiple
              {elems = Seq.map #1 specs, delims = Seq.map #2 specs}

          val result =
            case Seq.length specs of
              0 => Ast.Sig.EmptySpec
            | 1 =>
                let val (spec, semicolon) = Seq.nth specs 0
                in if isSome semicolon then makeSpecMultiple () else spec
                end
            | _ => makeSpecMultiple ()
        in
          (i, result)
        end

    in
      consume_sigSpec i
    end


  (** ========================================================================
    * ========================================================================
    *)

  fun spec allows toks infdict i =
    parse_spec allows toks infdict i
  fun sigexp allows toks infdict i =
    parse_sigexp allows toks infdict i


end
