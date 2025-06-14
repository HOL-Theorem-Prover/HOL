(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettyExpAndDec:
sig
  val showExp: Ast.Exp.exp -> TokenDoc.t
  val showDec: Ast.Exp.dec -> TokenDoc.t
end =
struct

  open TokenDoc
  open PrettyUtil

  infix 2 ++ $$ // +/+ +$+
  infix 1 \\
  fun x +/+ y = besideAndAbove (x, y)
  fun x +$+ y = besideAndAboveOrSpace (x, y)

  fun showTy ty = PrettyTy.showTy ty
  fun showPat pat = PrettyPat.showPat pat

  fun showTypbind (front, {elems, delims}) =
    let
      fun showOne (starter, {tyvars, tycon, ty, eq}) =
        separateWithSpaces
          [ SOME (token starter)
          , maybeShowSyntaxSeq tyvars token
          , SOME (token tycon)
          , SOME (token eq)
          ] \\ showTy ty
    in
      rigidVertically (showOne (front, Seq.nth elems 0)) (Seq.zipWith showOne
        (delims, Seq.drop elems 1))
    end


  fun showDatbind (front, datbind: Ast.Exp.datbind as {elems, delims}) =
    let
      fun showCon (starter, {opp, id, arg}) =
        starter ++ space
        ++
        group (separateWithSpaces
          [ Option.map token opp
          , SOME (token id)
          , Option.map (fn {off, ty} => token off \\ showTy ty) arg
          ])

      fun showOne (starter, {tyvars, tycon, eq, elems, delims, optbar}) =
        let
          val _ = if Option.isSome optbar then optBarFail () else ()

          val initial = group (separateWithSpaces
            [ SOME (token starter)
            , maybeShowSyntaxSeq tyvars token
            , SOME (token tycon)
            , SOME (token eq)
            ])
        in
          group
            (initial
             $$
             group
               (Seq.iterate op$$ (showCon (space, Seq.nth elems 0))
                  (Seq.zipWith showCon (Seq.map token delims, Seq.drop elems 1))))
        end
    in
      rigidVertically (showOne (front, Seq.nth elems 0)) (Seq.zipWith showOne
        (delims, Seq.drop elems 1))
    end


  (* returns SOME (left, token, right) if `<left> <token> <right>` can be
   * viewed as an infix expression.
   *)
  fun tryViewAsInfix exp =
    let
      open Ast.Exp
    in
      case exp of
        Infix {left, id, right} => SOME (left, id, right)
      | Orelse {left, orelsee, right} => SOME (left, orelsee, right)
      | Andalso {left, andalsoo, right} => SOME (left, andalsoo, right)
      | _ => NONE
    end


  fun showDecFun {funn, tyvars, fvalbind = {elems, delims}} =
    let
      open Ast.Exp

      fun showArgs args =
        if Seq.length args = 0 then
          empty
        else
          Seq.iterate (fn (prev, p) => prev ++ space ++ showPat p)
            (showPat (Seq.nth args 0)) (Seq.drop args 1)

      fun showInfixed larg id rarg =
        showPat larg ++ space ++ token id ++ space ++ showPat rarg

      fun showFNameArgs xx =
        case xx of
          PrefixedFun {opp, id, args} =>
            separateWithSpaces
              [Option.map token opp, SOME (token id), SOME (showArgs args)]
        | InfixedFun {larg, id, rarg} => showInfixed larg id rarg
        | CurriedInfixedFun {lparen, larg, id, rarg, rparen, args} =>
            separateWithSpaces
              [ SOME (token lparen ++ showInfixed larg id rarg ++ token rparen)
              , SOME (showArgs args)
              ]

      fun showColonTy {ty: Ast.Ty.t, colon: Token.t} =
        token colon ++ space ++ showTy ty

      fun showClause (align, indentExp) (front, {fname_args, ty, eq, exp}) =
        align
        ++
        group
          (separateWithSpaces
             [ SOME front
             , SOME (showFNameArgs fname_args)
             , Option.map showColonTy ty
             , SOME (token eq)
             ] $$ indentExp (showExp exp))

      fun mkFunction (starter, {elems = innerElems, delims, optbar}) =
        let
          val _ = if Option.isSome optbar then optBarFail () else ()

          fun firstIndentExp x =
            spaces (if Seq.length innerElems = 1 then 0 else 4) ++ indent x
          fun restIndentExp x = spaces 2 ++ indent x

          val firstParams = (empty, firstIndentExp)
          val restParams = (spaces 2, restIndentExp)
        in
          rigidVertically
            (showClause firstParams (starter, Seq.nth innerElems 0))
            (Seq.zipWith (showClause restParams)
               (Seq.map token delims, Seq.drop innerElems 1))
        end

      val front = separateWithSpaces
        [SOME (token funn), maybeShowSyntaxSeq tyvars token]
    in
      rigidVertically (mkFunction (front, Seq.nth elems 0))
        (Seq.zipWith mkFunction (Seq.map token delims, Seq.drop elems 1))
    end


  and showDec dec =
    let
      open Ast.Exp
    in
      case dec of
        DecVal {vall, tyvars, elems, delims} =>
          let
            fun mk (delim, {recc, pat, eq, exp}) =
              separateWithSpaces
                [ SOME (token delim)
                , Option.map token recc
                , SOME (showPat pat)
                , SOME (token eq)
                ] \\ showExp exp

            val first =
              let
                val {recc, pat, eq, exp} = Seq.nth elems 0
              in
                separateWithSpaces
                  [ SOME (token vall)
                  , maybeShowSyntaxSeq tyvars token
                  , Option.map token recc
                  , SOME (showPat pat)
                  , SOME (token eq)
                  ] \\ showExp exp
              end
          in
            rigidVertically first (Seq.map mk (Seq.zip
              (delims, Seq.drop elems 1)))
          end

      | DecFun args => showDecFun args

      | DecType {typee, typbind} => showTypbind (typee, typbind)

      | DecDatatype {datatypee, datbind, withtypee} =>
          let
            val datbinds = showDatbind (datatypee, datbind)
          in
            case withtypee of
              SOME {withtypee, typbind} =>
                datbinds $$ showTypbind (withtypee, typbind)

            | _ => datbinds
          end

      | DecInfix {infixx, precedence, elems} =>
          separateWithSpaces
            [ SOME (token infixx)
            , Option.map token precedence
            , SOME (seqWithSpaces elems token)
            ]

      | DecInfixr {infixrr, precedence, elems} =>
          separateWithSpaces
            [ SOME (token infixrr)
            , Option.map token precedence
            , SOME (seqWithSpaces elems token)
            ]

      | DecNonfix {nonfixx, elems} =>
          token nonfixx ++ space ++ seqWithSpaces elems token

      | DecException {exceptionn, elems, delims} =>
          let
            fun showExbind exbind =
              case exbind of
                ExnNew {opp, id, arg} =>
                  separateWithSpaces
                    [ Option.map token opp
                    , SOME (token id)
                    , Option.map
                        (fn {off, ty} => token off ++ space ++ showTy ty) arg
                    ]

              | ExnReplicate {opp, left_id, eq, right_id} =>
                  separateWithSpaces
                    [ Option.map token opp
                    , SOME (token left_id)
                    , SOME (token eq)
                    , SOME (token (MaybeLongToken.getToken right_id))
                    ]

            fun showOne (starter, elem) =
              token starter ++ space ++ showExbind elem
          in
            rigidVertically (showOne (exceptionn, Seq.nth elems 0))
              (Seq.zipWith showOne (delims, Seq.drop elems 1))
          end

      | DecLocal {locall, left_dec, inn, right_dec, endd} =>
          rigid
            (token locall $$ indent (showDec left_dec) $$ token inn
             $$ indent (showDec right_dec) $$ token endd)

      | DecMultiple {elems, delims} =>
          let
            fun f i =
              showDec (Seq.nth elems i)
              ++
              (case Seq.nth delims i of
                 NONE => empty
               | SOME semicolon => token semicolon)
          in
            rigid (Util.loop (0, Seq.length elems) empty (fn (prev, i) =>
              prev $$ f i))
          end

      | DecEmpty => empty

      | DecOpen {openn, elems} =>
          token openn ++ space
          ++ seqWithSpaces elems (token o MaybeLongToken.getToken)

      | DecAbstype {abstypee, datbind, withtypee, withh, dec, endd} =>
          let
            val datbinds = showDatbind (abstypee, datbind)

            val bottom = group
              (token withh $$ indent (showDec dec) $$ token endd)
          in
            group
              (case withtypee of
                 SOME {withtypee, typbind} =>
                   datbinds $$ showTypbind (withtypee, typbind) $$ bottom

               | _ => datbinds $$ bottom)
          end

      | DecReplicateDatatype
          {left_datatypee, left_id, eq, right_datatypee, right_id} =>
          seqWithSpaces
            (Seq.fromList
               [ left_datatypee
               , left_id
               , eq
               , right_datatypee
               , MaybeLongToken.getToken right_id
               ]) token
    end


  and showExp exp =
    let
      open Ast.Exp
    in
      case exp of
        Const tok => token tok
      | Unit {left, right} => token left ++ token right
      | Ident {opp, id} =>
          separateWithSpaces
            [Option.map token opp, SOME (token (MaybeLongToken.getToken id))]
      | Parens {left, exp, right} => token left ++ showExp exp ++ token right
      | Tuple {left, elems, delims, right} =>
          sequence left delims right (Seq.map showExp elems)
      | Sequence {left, elems, delims, right} =>
          sequence left delims right (Seq.map showExp elems)
      | List {left, elems, delims, right} =>
          sequence left delims right (Seq.map showExp elems)
      | Record {left, elems, delims, right} =>
          let
            fun showRow row =
              case row of
                RecordPun _ => recordPunFail ()
              | RecordRow {lab, eq, exp} =>
                  (token lab ++ space ++ token eq) \\ showExp exp
          in
            sequence left delims right (Seq.map showRow elems)
          end
      | Select {hash, label} => token hash ++ space ++ token label
      | App {left, right} => showExp left \\ showExp right
      | Infix {left, id, right} => showInfixedExp (left, id, right)
      | Andalso {left, andalsoo, right} =>
          showInfixedExp (left, andalsoo, right)
      | Orelse {left, orelsee, right} => showInfixedExp (left, orelsee, right)
      | Typed {exp, colon, ty} =>
          showExp exp ++ space ++ token colon ++ space ++ showTy ty
      | IfThenElse {iff, exp1, thenn, exp2, elsee, exp3} =>
          let
            val combinator =
              case exp3 of
                IfThenElse _ => besideAndAboveOrSpace
              | _ => aboveOrSpace
          in
            group (token iff $$ indent (showExp exp1) $$ token thenn)
            $$ indent (showExp exp2)
            $$ combinator (token elsee, indent (showExp exp3))
          end
      | While {whilee, exp1, doo, exp2} =>
          group
            (group (token whilee $$ indent (showExp exp1) $$ token doo)
             $$ indent (showExp exp2))

      | Raise {raisee, exp} => token raisee \\ showExp exp

      | Handle {optbar = SOME _, ...} => optBarFail ()

      | Handle {exp = expLeft, handlee, elems, delims, optbar = NONE} =>
          let
            fun showBranch {pat, arrow, exp} =
              showPat pat ++ space ++ token arrow \\ showExp exp
            fun mk (delim, branch) =
              token delim ++ space ++ showBranch branch
          in
            showExp expLeft
            \\
            (token handlee
             \\
             rigidVertically (indent (showBranch (Seq.nth elems 0)))
               (Seq.map mk (Seq.zip (delims, Seq.drop elems 1))))
          end

      | Case {optbar = SOME _, ...} => optBarFail ()

      | Case {casee, exp = expTop, off, elems, delims, optbar = NONE} =>
          let
            fun showBranch {pat, arrow, exp} =
              showPat pat ++ space ++ token arrow \\ showExp exp
            fun mk (delim, branch) =
              token delim ++ space ++ showBranch branch
          in
            rigid
              (token casee ++ space ++ showExp expTop ++ space ++ token off
               $$
               rigidVertically (indent (showBranch (Seq.nth elems 0)))
                 (Seq.map mk (Seq.zip (delims, Seq.drop elems 1))))
          end

      | Fn {optbar = SOME _, ...} => optBarFail ()

      | Fn {fnn, elems, delims, optbar = NONE} =>
          let
            fun mk (delim, {pat, arrow, exp}) =
              space
              ++
              ((token delim ++ space ++ showPat pat ++ space ++ token arrow)
               \\ showExp exp)

            val {pat, arrow, exp} = Seq.nth elems 0
            val initial =
              (token fnn ++ space ++ showPat pat ++ space ++ token arrow)
              \\ showExp exp
          in
            group (Seq.iterate op$$ initial (Seq.map mk (Seq.zip
              (delims, Seq.drop elems 1))))
          end

      | LetInEnd {lett, dec, inn, exps, delims, endd} =>
          let
            val prettyDec = showDec dec
            val numExps = Seq.length exps

            fun d i = Seq.nth delims i

            val withDelims =
              Seq.mapIdx
                (fn (i, e) =>
                   showExp e ++ (if i = numExps - 1 then empty else token (d i)))
                exps

            val topPart = token lett $$ indent prettyDec $$ token inn

            val topPart =
              if Ast.Exp.isMultipleDecs dec then topPart else group topPart
          in
            group
              (topPart $$ indent (group (Seq.iterate op$$ empty withDelims))
               $$ token endd)
          end

      | MLtonSpecific {underscore, directive, contents, semicolon} =>
          token underscore ++ token directive ++ space
          ++ seqWithSpaces contents token ++ token semicolon
    end


  (* TODO: This is still not quite right *)
  and showInfixedExp (l, t, r) =
    let
      open Ast.Exp

      fun tryLeft () =
        case tryViewAsInfix l of
          NONE => NONE
        | SOME (ll, lt, lr) =>
            if not (Token.same (t, lt)) then
              NONE
            else
              SOME (group
                (group (showInfixedExp (ll, lt, lr) $$ token t) +$+ showExp r))

      fun tryRight () =
        case tryViewAsInfix r of
          NONE => NONE
        | SOME (rl, rt, rr) =>
            if not (Token.same (t, rt)) then
              NONE
            else
              SOME (group
                (group (showExp l $$ token t) +$+ showInfixedExp (rl, rt, rr)))

      fun normal () =
        group (group (showExp l $$ token t) +$+ showExp r)
    in
      case tryLeft () of
        SOME x => x
      | NONE =>

          case tryRight () of
            SOME x => x
          | NONE => normal ()
    end

end
