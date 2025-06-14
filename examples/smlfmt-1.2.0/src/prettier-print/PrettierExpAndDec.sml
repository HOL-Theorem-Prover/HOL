(** Copyright (c) 2022-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierExpAndDec:
sig
  val showExp: Ast.Exp.exp PrettierUtil.shower
  val showDec: Ast.Exp.dec PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierTy
  open PrettierPat
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ====================================================================== *)

  fun ifThenElseChain acc exp =
    case exp of
      Ast.Exp.IfThenElse {iff, exp1, thenn, exp2, elsee, exp3} =>
        ifThenElseChain
          ({iff = iff, exp1 = exp1, thenn = thenn, exp2 = exp2, elsee = elsee}
           :: acc) exp3
    | _ => (Seq.fromRevList acc, exp)


  (* returns (function, curried args) *)
  fun appChain exp =
    let
      fun loop acc exp =
        case exp of
          Ast.Exp.App {left, right} => loop (right :: acc) left
        | _ => (exp, Seq.fromList acc)
    in
      loop [] exp
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

  fun decIsEmpty e =
    case e of
      Ast.Exp.DecEmpty => true
    | _ => false


  fun tryViewExpAsSimpleIdentifier e =
    case e of
      Ast.Exp.Ident {opp = NONE, id} =>
        if MaybeLongToken.isLong id then NONE
        else SOME (MaybeLongToken.getToken id)

    | _ => NONE


  fun appWantsToTouch left right =
    let
      open Ast.Exp

      val rightNice =
        case right of
          Ident {opp = NONE, id} =>
            not (MaybeLongToken.isLong id)
            andalso
            not (Token.isSymbolicIdentifier (MaybeLongToken.getToken id))
        | Tuple _ => true
        | List _ => true
        | Sequence _ => true
        | Parens _ => true
        | Record _ => true
        | Unit _ => true
        | _ => false
    in
      rightNice
      andalso
      case tryViewExpAsSimpleIdentifier left of
        SOME id =>
          Token.isSymbolicIdentifier id andalso not (Token.hasCommentsAfter id)
      | NONE => false
    end


  fun appWantsSpace left right =
    not (appWantsToTouch left right)


  fun tryViewAsSimpleApp exp =
    let
      open Ast.Exp
    in
      case exp of
        App {left, right} =>
          if appWantsToTouch left right then
            NONE
          else
            (case left of
               Ident {opp = NONE, id} =>
                 SOME (MaybeLongToken.getToken id, right)
             | _ => NONE)

      | _ => NONE
    end


  fun isBiggishExp exp =
    let
      open Ast.Exp

      (* kinda arbitrary, but seems about right. *)
      val singleTokBignessThreshold = 30
      fun tokIsBig t =
        Source.length (Token.getSource t) >= singleTokBignessThreshold
        orelse Token.spansMultipleLines t

      fun recordRowLabel row =
        case row of
          RecordPun {id} => id
        | RecordRow {lab, ...} => lab

      fun looksBig depth exp =
        depth >= 3
        orelse
        case exp of
          Parens {exp, ...} => looksBig (depth + 1) exp

        | Unit _ => false

        | Ident {id, ...} => tokIsBig (MaybeLongToken.getToken id)

        | Const t => tokIsBig t

        | Select _ => false

        | App {left, right} =>
            looksBig (depth + 1) left orelse looksBig (depth + 1) right

        | Infix {left, right, ...} =>
            looksBig (depth + 1) left orelse looksBig (depth + 1) right

        | Andalso {left, right, ...} =>
            looksBig (depth + 1) left orelse looksBig (depth + 1) right

        | Orelse {left, right, ...} =>
            looksBig (depth + 1) left orelse looksBig (depth + 1) right

        | Raise {exp, ...} => looksBig (depth + 1) exp

        | Typed {exp, ...} => looksBig (depth + 1) exp

        | Fn {elems, ...} =>
            Seq.length elems > 1
            orelse looksBig (depth + 1) (#exp (Seq.nth elems 0))

        | Tuple {elems, ...} =>
            Seq.length elems >= 5
            orelse
            Util.exists (0, Seq.length elems) (fn i =>
              looksBig (depth + 1) (Seq.nth elems i))

        | List {elems, ...} =>
            Seq.length elems >= 5
            orelse
            Util.exists (0, Seq.length elems) (fn i =>
              looksBig (depth + 1) (Seq.nth elems i))

        | Record {elems, ...} =>
            Seq.length elems >= 4
            orelse
            Util.exists (0, Seq.length elems) (fn i =>
              case Seq.nth elems i of
                RecordPun {id} => tokIsBig id
              | RecordRow {exp, ...} => looksBig (depth + 1) exp)
            orelse
            SeqBasis.foldl op+ 0 (0, Seq.length elems) (fn i =>
              Source.length (Token.getSource (recordRowLabel (Seq.nth elems i))))
            >= singleTokBignessThreshold

        | _ => true

    in
      looksBig 0 exp
    end


  (* This function should be "in sync" with `splitShowExpLeft` and
   * `splitShowExpRight`, below.
   *)
  fun isSplittableExp exp =
    let
      open Ast.Exp
    in
      case exp of
        Parens {exp, ...} => isSplittableExp exp
      | Fn {elems, ...} => Seq.length elems = 1
      | App {left, right} => isBiggishExp right
      | Tuple {elems, ...} =>
          isSplittableExp (Seq.nth elems (Seq.length elems - 1))
      | _ => false
    end


  fun isIdentLength1 exp =
    case exp of
      Ast.Exp.Ident {opp = NONE, id} =>
        1 = Source.length (Token.getSource (MaybeLongToken.getToken id))
    | _ => false


  fun decHasAtLeastTwoDecs dec =
    let
      open Ast.Exp
    in
      case dec of
        DecMultiple {elems, ...} => Seq.length elems >= 2
      | _ => false
    end

  (* ====================================================================== *)

  (* This function is duplicated in PrettierSig. *)
  fun showTypbind tab (front, typbind: Ast.Exp.typbind as {elems, delims}) =
    let
      fun showOne first (starter, {tyvars, tycon, ty, eq}) =
        at tab
          (token starter ++ showTokenSyntaxSeq tab tyvars ++ token tycon
           ++ token eq ++ withNewChild showTy tab ty)
    in
      Seq.iterate op++ (showOne true (front, Seq.nth elems 0))
        (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
    end


  fun showDatbind tab (front, datbind: Ast.Exp.datbind as {elems, delims}) =
    newTabWithStyle tab (Tab.Style.allowComments, fn tab =>
      let
        fun showCon (starter, {opp, id, arg}) =
          at tab
            (starter ++ showMaybeOpToken opp id
             ++
             showOption
               (fn {off, ty} =>
                  token off
                  ++ withNewChildWithStyle (indentedAtLeastBy 4) showTy tab ty)
               arg)

        fun showOne (starter, {tyvars, tycon, eq, elems, delims, optbar}) =
          let
            val initial = at tab
              (token starter ++ showTokenSyntaxSeq tab tyvars ++ token tycon
               ++ token eq)

            val skipper = cond tab {inactive = empty, active = space ++ space}
            fun dd delim = token delim ++ space

            val firstConFront =
              case optbar of
                NONE => skipper
              | SOME bar => dd bar
          in
            initial
            ++
            Seq.iterate op++ (showCon (firstConFront, Seq.nth elems 0))
              (Seq.zipWith showCon (Seq.map dd delims, Seq.drop elems 1))
          end
      in
        Seq.iterate op++ (showOne (front, Seq.nth elems 0)) (Seq.zipWith showOne
          (delims, Seq.drop elems 1))
      end)

  (* ====================================================================== *)

  fun showExp tab exp =
    let
      open Ast.Exp
    in
      case exp of
        Const tok => token tok

      | Unit {left, right} => token left ++ nospace ++ token right

      | Ident {opp, id} => showMaybeOpToken opp (MaybeLongToken.getToken id)

      | Parens {left, exp, right} =>
          token left ++ (if expStartsWithStar exp then empty else nospace)
          ++ withNewChild showExp tab exp ++ nospace ++ token right

      | Tuple {left, elems, delims, right} =>
          showSequence expStartsWithStar (withNewChild showExp) tab
            {openn = left, elems = elems, delims = delims, close = right}

      | Sequence {left, elems, delims, right} =>
          showSequence expStartsWithStar (withNewChild showExp) tab
            {openn = left, elems = elems, delims = delims, close = right}

      | List {left, elems, delims, right} =>
          showSequence expStartsWithStar (withNewChild showExp) tab
            {openn = left, elems = elems, delims = delims, close = right}

      | Record {left, elems, delims, right} =>
          let
            fun showRecordRow tab {lab, eq, exp} =
              if not (isSplittableExp exp) then
                token lab ++ token eq ++ (withNewChild showExp tab) exp
              else
                token lab ++ token eq
                ++
                newTab tab (fn expGhost =>
                  newTab tab (fn child =>
                    let
                      val expAtChild = at child (showExp child exp)
                    in
                      letdoc expAtChild (fn ec =>
                        cond expGhost
                          { inactive = cond child
                              { inactive = var ec
                              , active =
                                  at expGhost (splitShowExpLeft expGhost exp)
                                  ++ at child (splitShowExpRight child exp)
                              }
                          , active = var ec
                          })
                    end))

            fun showRow tab row =
              case row of
                RecordPun {id} => token id
              | RecordRow xxx => showRecordRow tab xxx
          in
            showSequence (fn _ => false) (withNewChild showRow) tab
              {openn = left, elems = elems, delims = delims, close = right}
          end

      | Select {hash, label} =>
          token hash
          ++
          (if
             Token.isSymbolicIdentifier label orelse Token.hasCommentsAfter hash
           then empty
           else nospace) ++ token label

      | App _ => showApp tab exp

      | Typed {exp, colon, ty} =>
          withNewChild showExp tab exp ++ token colon
          ++ withNewChild showTy tab ty

      | IfThenElse _ (*{iff, exp1, thenn, exp2, elsee, exp3}*) =>
          showIfThenElseAt tab exp

      | LetInEnd xxx => showLetInEndAt tab xxx

      | Fn {fnn, elems, delims, optbar} =>
          newTab tab (fn inner => (* do we need the newTab here? *)
            let
              fun mk (delim, {pat, arrow, exp}) =
                let
                  val stuff =
                    withNewChild showPat inner pat ++ token arrow
                    ++ withNewChild showExp inner exp
                in
                  case delim of
                    NONE => stuff
                  | SOME d =>
                      at inner
                        (cond inner {inactive = empty, active = space}
                         ++ token d ++ stuff)
                end

              val initial = token fnn ++ mk (optbar, Seq.nth elems 0)
            in
              at inner (Seq.iterate op++ initial (Seq.zipWith mk
                (Seq.map SOME delims, Seq.drop elems 1)))
            end)

      | Case {casee, exp = expTop, off, elems, delims, optbar} =>
          let
            val branchExpStyle =
              Tab.Style.combine (indentedAtLeastBy 4, Tab.Style.allowComments)
            fun showBranch inner1 {pat, arrow, exp} =
              withNewChild showPat inner1 pat ++ token arrow
              ++ withNewChildWithStyle branchExpStyle showExp inner1 exp
            fun mk inner1 (delim, branch) =
              at inner1
                ((case delim of
                    SOME d => token d
                  | _ => cond inner1 {active = space ++ space, inactive = empty})
                 ++ showBranch inner1 branch)

            val style =
              if Seq.length elems <= 1 then Tab.Style.inplace else rigidInplace

            val style = Tab.Style.combine (style, Tab.Style.allowComments)
          in
            newTabWithStyle tab (style, fn inner1 =>
              newTab inner1 (fn inner2 =>
                at inner1 (token casee) ++ at inner2 (showExp inner2 expTop)
                ++
                cond inner2
                  {inactive = token off, active = at inner1 (token off)}
                ++
                Seq.iterate op++ (mk inner1 (optbar, Seq.nth elems 0))
                  (Seq.zipWith (mk inner1)
                     (Seq.map SOME delims, Seq.drop elems 1))))
          end

      | Infix {left, id, right} => showInfixedExpAt tab (left, id, right)

      | Andalso {left, andalsoo, right} =>
          showInfixedExpAt tab (left, andalsoo, right)

      | Orelse {left, orelsee, right} =>
          showInfixedExpAt tab (left, orelsee, right)

      | While {whilee, exp1, doo, exp2} =>
          newTab tab (fn inner1 =>
            newTab tab (fn inner2 =>
              token whilee ++ at inner1 (showExp inner1 exp1)
              ++ cond inner1 {inactive = token doo, active = at tab (token doo)}
              ++ at inner2 (showExp inner2 exp2)))

      | Raise {raisee, exp} =>
          (case tryViewAsSimpleApp exp of
             NONE => token raisee ++ withNewChild showExp tab exp
           | SOME (id, exp') =>
               token raisee ++ newTab tab (fn inner => at inner (token id))
               ++ withNewChild showExp tab exp')

      | Handle (args as {exp = expLeft, handlee, elems, delims, optbar}) =>
          if Seq.length elems > 1 orelse Option.isSome optbar then
            showHandle tab args
          else
            newTab tab (fn inner =>
              let
                val {pat, arrow, exp} = Seq.nth elems 0
              in
                at tab (showExp tab expLeft)
                ++
                at tab (at inner
                  (token handlee ++ withNewChild showPat inner pat
                   ++ token arrow ++ withNewChild showExp inner exp))
              end)

      | MLtonSpecific {underscore, directive, contents, semicolon} =>
          token underscore ++ nospace ++ token directive
          ++ Seq.iterate op++ empty (Seq.map token contents) ++ nospace
          ++ token semicolon

    end


  (* This function has to be "in sync" with splitShowExpRight.
   * For any exp, it should be that
   *   `splitShowExpLeft tab1 exp ++ splitShowExpRight tab2 exp`
   * shows every token within `exp` exactly once.
   *)
  and splitShowExpLeft tab exp =
    let
      open Ast.Exp
    in
      if not (isSplittableExp exp) then
        empty
      else

        case exp of
          Parens {left, exp, right} =>
            token left ++ (if expStartsWithStar exp then empty else nospace)
            ++ withNewChild splitShowExpLeft tab exp

        | Fn {fnn, elems, delims, optbar} =>
            let
              val {pat, arrow, exp} = Seq.nth elems 0
            in
              token fnn ++ showOption token optbar
              ++ withNewChild showPat tab pat ++ token arrow
            end

        | App {left, right} => showExp tab left ++ splitShowExpLeft tab right

        | Tuple {left, elems, delims, right} =>
            let
              fun make (e, d) =
                withNewChild showExp tab e ++ nospace ++ token d
            in
              token left
              ++
              (if expStartsWithStar (Seq.nth elems 0) then empty else nospace)
              ++ Seq.iterate op++ empty (Seq.map make (Seq.zip (elems, delims)))
              ++ splitShowExpLeft tab (Seq.nth elems (Seq.length elems - 1))
            end

        | _ => empty
    end


  (* This function needs to be "in sync" with splitShowExpLeft; see above. *)
  and splitShowExpRight tab exp =
    let
      open Ast.Exp
    in
      if not (isSplittableExp exp) then
        showExp tab exp
      else

        case exp of
          Parens {left, exp, right} =>
            splitShowExpRight tab exp ++ nospace ++ token right

        | Fn {fnn, elems, delims, optbar} =>
            let val {pat, arrow, exp} = Seq.nth elems 0
            in showExp tab exp
            end

        | App {left, right} => splitShowExpRight tab right

        | Tuple {left, elems, delims, right} =>
            splitShowExpRight tab (Seq.nth elems (Seq.length elems - 1))
            ++ nospace ++ token right

        | _ => showExp tab exp
    end


  and showApp tab exp =
    let
      val (fExp, args) = appChain exp
      val nArgs = Seq.length args
      val (allButLastArg, lastArg) =
        (Seq.take args (nArgs - 1), Seq.nth args (nArgs - 1))

      (* This is a cool trick: we create a new "ghost" tab which contains the
       * content of this arg, and use it to determine whether or not the arg
       * should be moved to align with other arguments. This is a "ghost" tab
       * in the sense that the ghost is never visible: if the ghost is
       * activated, then it's not used.
       *
       * The result is that args are laid out left-to-right, but whenever an arg
       * cannot fit, we move down to the alignedArgsTab and then continue.
       *)
      fun makeArg alignedArgsTab allArgsGhost arg =
        newTab allArgsGhost (fn ghost =>
          let
            val contents = cond ghost
              { inactive = at ghost (showExp ghost arg)
              , active = at alignedArgsTab (showExp alignedArgsTab arg)
              }
          in
            letdoc contents (fn c =>
              cond allArgsGhost
                {inactive = at allArgsGhost (var c), active = var c})
          end)

      fun makeLastArg alignedArgsTab allArgsGhost arg =
        newTab tab (fn ghost1 =>
          newTab tab (fn ghost2 =>
            let
              val aligned = at alignedArgsTab (showExp alignedArgsTab arg)

              val flat = at ghost2 (showExp ghost2 arg)

              fun contents f a =
                cond ghost1
                  { inactive = cond ghost2
                      { inactive = var f
                      , active =
                          at ghost1 (splitShowExpLeft ghost1 arg)
                          ++
                          at alignedArgsTab
                            (splitShowExpRight alignedArgsTab arg)
                      }

                  , active = var a
                  }
            in
              letdoc aligned (fn a =>
                letdoc flat (fn f =>
                  cond allArgsGhost
                    { inactive = contents f a
                    , active = cond ghost2 {inactive = var f, active = var a}
                    }))
            end))

      val argsStyle =
        (* This is a funny edge case, where indented style would look strange,
         * for example:
         *   f
         *     arg1
         *     arg2
         *
         * So instead we use inplace style which allows for this:
         *   f arg1
         *     arg2
         *)
        if isIdentLength1 fExp then Tab.Style.inplace
        else Tab.Style.indented

      val argsStyle = Tab.Style.combine (Tab.Style.allowComments, argsStyle)
    in
      newTabWithStyle tab (argsStyle, fn alignedArgsTab =>
        newTab tab (fn allArgsGhost =>
          at tab (showExp tab fExp)
          ++ (if appWantsSpace fExp (Seq.nth args 0) then empty else nospace)
          ++
          Seq.iterate op++ empty
            (Seq.map (makeArg alignedArgsTab allArgsGhost) allButLastArg)
          ++ makeLastArg alignedArgsTab allArgsGhost lastArg))
    end


  and showHandle tab {exp = expLeft, handlee, elems, delims, optbar} =
    newTabWithStyle tab (Tab.Style.allowComments, fn inner =>
      let
        fun showBranch {pat, arrow, exp} =
          withNewChild showPat inner pat ++ token arrow
          ++ withNewChildWithStyle (indentedAtLeastBy 4) showExp inner exp
        fun mk (delim, branch) =
          at inner
            ((case delim of
                SOME d => token d
              | _ => cond inner {active = space ++ space, inactive = empty})
             ++ showBranch branch)
      in
        at tab (showExp tab expLeft) ++ at tab (at inner (token handlee))
        ++
        Seq.iterate op++ (mk (optbar, Seq.nth elems 0)) (Seq.zipWith mk
          (Seq.map SOME delims, Seq.drop elems 1))
      end)


  and showInfixedExpAt tab (l, t, r) =
    let
      open Ast.Exp
      fun def () =
        newTab tab (fn tab =>
          let
            fun infixChainLeft () =
              let
                fun loop acc exp =
                  case tryViewAsInfix exp of
                    NONE => (exp, acc)
                  | SOME (left, id, right) =>
                      if Token.same (t, id) then
                        loop ({id = id, right = right} :: acc) left
                      else
                        (exp, acc)
                val (exp, elems) = loop [{id = t, right = r}] l
              in
                (exp, Seq.fromList elems)
              end

            fun infixChainRight () =
              let
                fun loop acc (prevId, exp) =
                  case tryViewAsInfix exp of
                    NONE => {id = prevId, right = exp} :: acc
                  | SOME (left, id, right) =>
                      if not (Token.same (t, id)) then
                        {id = prevId, right = exp} :: acc
                      else
                        loop ({id = prevId, right = left} :: acc) (id, right)

                val elems = loop [] (t, r)
              in
                (l, Seq.fromRevList elems)
              end

            val (leftmostExp1, rightElems1) = infixChainLeft ()
            val (leftmostExp2, rightElems2) = infixChainRight ()

            fun showRightElem {id, right} =
              newTab tab (fn ghost =>
                cond ghost
                  { inactive = at ghost (token id ++ showExp ghost right)
                  , active = at tab
                      (token id
                       ++
                       newTab tab (fn ghostChild =>
                         cond ghostChild
                           { inactive = at ghostChild (showExp ghostChild right)
                           , active = at tab (showExp tab right)
                           }))
                  })
            (* at tab (token id) ++ withNewChild showExp tab right *)

            val (leftmostExp, rightElems) =
              if Seq.length rightElems1 >= Seq.length rightElems2 then
                (leftmostExp1, rightElems1)
              else
                (leftmostExp2, rightElems2)
          in
            at tab (withNewChild showExp tab leftmostExp)
            ++ Seq.iterate op++ empty (Seq.map showRightElem rightElems)
          end)
      val nonIndented =
        Tab.Style.combine (Tab.Style.indentedExactlyBy 0, Tab.Style.rigid)

      (* Return "( fn <pat> => <exp> )" where <pat> is a pattern and <exp> is an expression
         with the rest being tokens. *)
      fun tryViewAsParenSingleFn
            (Parens {left, exp = Fn {fnn, elems, ...}, right}) =
            (case Seq.toList elems of
               [{pat, arrow, exp}] => SOME (left, fnn, pat, arrow, exp, right)
             | _ => NONE)
        | tryViewAsParenSingleFn _ = NONE

      (* As long as the expression is an infix with a continuation on the right side,
         put the body on the next line with no indentation. *)
      fun showCPS tab (l, t, r) =
        case tryViewAsParenSingleFn r of
          SOME (left, fnn, pat, arrow, exp, right) =>
            newTab tab (fn tab =>
              at tab (withNewChild showExp tab l) ++ token t ++ token left
              ++ nospace ++ token fnn ++ showPat tab pat ++ token arrow
              ++
              newTabWithStyle tab (nonIndented, fn inner =>
                at inner
                  (case tryViewAsInfix exp of
                     SOME t => showCPS inner t
                   | NONE => showExp inner exp) ++ nospace ++ token right))
        | NONE => showInfixedExpAt tab (l, t, r)
    in
      case tryViewAsParenSingleFn r of
        SOME (_, _, _, _, exp, _) =>
          (case tryViewAsInfix exp of
             SOME (_, _, r') =>
               (case tryViewAsParenSingleFn r' of
                  SOME _ => showCPS tab (l, t, r)
                | NONE => def ())
           | NONE => def ())
      | NONE => def ()
    end

  and showLetInEndAt outerTab {lett, dec, inn, exps, delims, endd} =
    let
      val numExps = Seq.length exps
      fun d i = Seq.nth delims i
      fun withDelims innerTab =
        Seq.mapIdx
          (fn (i, e) =>
             at innerTab
               (showExp innerTab e
                ++ (if i = numExps - 1 then empty else nospace ++ token (d i))))
          exps

      val innerStyle =
        if decHasAtLeastTwoDecs dec then
          Tab.Style.combine (indentedAllowComments, Tab.Style.rigid)
        else
          indentedAllowComments
    in
      newTabWithStyle outerTab (innerStyle, fn inner =>
        showThingSimilarToLetInEnd outerTab
          { lett = lett
          , isEmpty1 = decIsEmpty dec
          , doc1 = at inner (showDec inner dec)
          , inn = inn
          , doc2 = Seq.iterate op++ empty (withDelims inner)
          , endd = endd
          })
    end


  and showIfThenElseAt outer exp =
    newTabWithStyle outer (Tab.Style.allowComments, fn outer =>
      newTabWithStyle outer (indentedAllowComments, fn inner2 =>
        newTabWithStyle outer (indentedAllowComments, fn inner1 =>
          let
            open Ast.Exp
            val (chain, last) = ifThenElseChain [] exp

            fun breakShowAt tab e =
              at tab (showExp tab e)

            fun f i =
              let
                val {iff, exp1, thenn, exp2, elsee} = Seq.nth chain i
              in
                token iff ++ breakShowAt inner1 exp1
                ++
                cond inner1
                  {inactive = token thenn, active = at outer (token thenn)}
                ++ breakShowAt inner2 exp2 ++ at outer (token elsee)
              end
          in
            at outer
              (Util.loop (0, Seq.length chain) empty (fn (d, i) => d ++ f i)
               ++ breakShowAt inner2 last)
          end)))


  and showDec tab dec =
    let
      open Ast.Exp
    in
      case dec of
        DecEmpty => empty

      | DecVal {vall, tyvars, elems, delims} =>
          let
            fun mkSplittable (starter, {recc, pat, eq, exp}) =
              newTab tab (fn flatGhost =>
                newTab tab (fn expGhost =>
                  newTabWithStyle tab (Tab.Style.allowComments, fn child =>
                    let
                      val patContents = withNewChild showPat tab pat

                      (* *)
                      val expAtChild = at child (showExp child exp)

                      fun expContents ec =
                        cond expGhost
                          { inactive = cond child
                              { inactive = var ec
                              , active =
                                  at expGhost (splitShowExpLeft expGhost exp)
                                  ++ at child (splitShowExpRight child exp)
                              }
                          , active = var ec
                          }
                    in
                      at tab (starter ++ showOption token recc)
                      ++
                      letdoc patContents (fn pc =>
                        cond flatGhost
                          {inactive = at flatGhost (var pc), active = var pc})
                      ++ token eq
                      ++
                      letdoc expAtChild (fn ec =>
                        cond flatGhost
                          {inactive = expContents ec, active = var ec})
                    end)))

            fun mkSimple (starter, {recc, pat, eq, exp}) =
              at tab
                (starter ++ showOption token recc
                 ++ withNewChild showPat tab pat ++ token eq
                 ++ withNewChild showExp tab exp)

            fun mk (starter, xxx as {recc, pat, eq, exp}) =
              if not (isSplittableExp exp) then mkSimple (starter, xxx)
              else mkSplittable (starter, xxx)

            val front = token vall ++ showTokenSyntaxSeq tab tyvars
          in
            Seq.iterate op++ (mk (front, Seq.nth elems 0)) (Seq.zipWith mk
              (Seq.map token delims, Seq.drop elems 1))
          end

      | DecFun args => showDecFunAt tab args

      | DecInfix {infixx, precedence, elems} =>
          token infixx ++ showOption token precedence
          ++ Seq.iterate op++ empty (Seq.map token elems)

      | DecInfixr {infixrr, precedence, elems} =>
          token infixrr ++ showOption token precedence
          ++ Seq.iterate op++ empty (Seq.map token elems)

      | DecNonfix {nonfixx, elems} =>
          token nonfixx ++ Seq.iterate op++ empty (Seq.map token elems)

      | DecMultiple {elems, delims} =>
          let
            fun mk first (elem, delim) =
              at tab
                (showDec tab elem
                 ++ showOption (fn d => nospace ++ token d) delim)

            val things = Seq.zip (elems, delims)
          in
            Seq.iterate op++ (mk true (Seq.nth things 0)) (Seq.map (mk false)
              (Seq.drop things 1))
          end

      | DecOpen {openn, elems} =>
          token openn
          ++
          Seq.iterate op++ empty
            (Seq.map (token o MaybeLongToken.getToken) elems)

      | DecType {typee, typbind} => showTypbind tab (typee, typbind)

      | DecDatatype {datatypee, datbind, withtypee} =>
          showDatbind tab (datatypee, datbind)
          ++
          showOption
            (fn {withtypee, typbind} =>
               at tab (showTypbind tab (withtypee, typbind))) withtypee

      | DecException {exceptionn, elems, delims} =>
          let
            fun showExbind exbind =
              case exbind of
                ExnNew {opp, id, arg} =>
                  showMaybeOpToken opp id
                  ++
                  showOption
                    (fn {off, ty} => token off ++ withNewChild showTy tab ty)
                    arg
              | ExnReplicate {opp, left_id, eq, right_id} =>
                  showOption token opp ++ token left_id ++ token eq
                  ++ token (MaybeLongToken.getToken right_id)

            fun showOne first (starter, elem) =
              at tab (token starter ++ showExbind elem)
          in
            Seq.iterate op++ (showOne true (exceptionn, Seq.nth elems 0))
              (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
          end

      | DecReplicateDatatype
          {left_datatypee, left_id, eq, right_datatypee, right_id} =>
          Seq.iterate op++ empty (Seq.map token (Seq.fromList
            [ left_datatypee
            , left_id
            , eq
            , right_datatypee
            , MaybeLongToken.getToken right_id
            ]))

      | DecLocal {locall, left_dec, inn, right_dec, endd} =>
          showThingSimilarToLetInEnd tab
            { lett = locall
            , isEmpty1 = decIsEmpty left_dec
            , doc1 = withNewChildWithStyle indented showDec tab left_dec
            , inn = inn
            , doc2 = withNewChildWithStyle indented showDec tab right_dec
            , endd = endd
            }

      | DecAbstype {abstypee, datbind, withtypee, withh, dec, endd} =>
          let
            val bottom =
              at tab
                (token withh ++ withNewChildWithStyle indented showDec tab dec)
              ++ at tab (token endd)
          in
            showDatbind tab (abstypee, datbind)
            ++
            showOption
              (fn {withtypee, typbind} =>
                 at tab (showTypbind tab (withtypee, typbind))) withtypee
            ++ bottom
          end
    end


  and showDecFunAt tab {funn, tyvars, fvalbind = {elems, delims}} =
    let
      open Ast.Exp

      fun showArgs tab clauseChildStyle args =
        Seq.iterate op++ empty
          (Seq.map (withNewChildWithStyle clauseChildStyle showPat tab) args)

      fun showInfixed tab clauseChildStyle (larg, id, rarg) =
        withNewChildWithStyle clauseChildStyle showPat tab larg ++ token id
        ++ withNewChildWithStyle clauseChildStyle showPat tab rarg

      fun showFNameArgs tab clauseChildStyle xx =
        case xx of
          PrefixedFun {opp, id, args} =>
            showMaybeOpToken opp id ++ showArgs tab clauseChildStyle args
        | InfixedFun {larg, id, rarg} =>
            showInfixed tab clauseChildStyle (larg, id, rarg)
        | CurriedInfixedFun {lparen, larg, id, rarg, rparen, args} =>
            token lparen ++ (if patStartsWithStar larg then empty else nospace)
            ++ showInfixed tab clauseChildStyle (larg, id, rarg) ++ nospace
            ++ token rparen ++ showArgs tab clauseChildStyle args

      fun showColonTy tab {ty: Ast.Ty.t, colon: Token.t} =
        token colon ++ withNewChild showTy tab ty

      fun showClause mainTab clauseTab clauseChildStyleFirst
        clauseChildStyleRest isFirst (front, {fname_args, ty, eq, exp}) =
        let
          fun afterFront tab clauseChildStyle =
            let
              val expChildStyle =
                if isBiggishExp exp then
                  Tab.Style.combine
                    ( Tab.Style.combine (Tab.Style.indented, Tab.Style.rigid)
                    , clauseChildStyle
                    )
                else
                  clauseChildStyle
            in
              showFNameArgs tab clauseChildStyle fname_args
              ++ showOption (showColonTy tab) ty ++ token eq
              ++ withNewChildWithStyle expChildStyle showExp tab exp
            end
        in
          if isFirst then
            at mainTab (front ++ afterFront mainTab clauseChildStyleFirst)
          else
            at clauseTab (front ++ afterFront clauseTab clauseChildStyleRest)
        end

      fun mkFunction (starter, {elems = innerElems, delims, optbar}) =
        let
          val clauseChildStyleFirst =
            if Seq.length innerElems <= 1 andalso not (Option.isSome optbar) then
              Tab.Style.inplace
            else
              indentedAtLeastBy 6

          val clauseChildStyleRest = indentedAtLeastBy 4

          val mainStyle =
            Tab.Style.combine (rigidInplace, Tab.Style.allowComments)

          val clauseStyle = Tab.Style.combine
            ( Tab.Style.allowComments
            , Tab.Style.combine (Tab.Style.rigid, Tab.Style.indentedExactlyBy 2)
            )
        in
          at tab (newTabWithStyle tab (mainStyle, fn mainTab =>
            newTabWithStyle mainTab (clauseStyle, fn clauseTab =>
              let
                val showClause' =
                  showClause mainTab clauseTab clauseChildStyleFirst
                    clauseChildStyleRest
              in
                case optbar of
                  NONE =>
                    Seq.iterate op++
                      (showClause' true (starter, Seq.nth innerElems 0))
                      (Seq.zipWith (showClause' false)
                         (Seq.map token delims, Seq.drop innerElems 1))
                | SOME bar =>
                    at mainTab starter
                    ++
                    Seq.iterate op++ empty (Seq.zipWith (showClause' false)
                      ( Seq.map token (Seq.append (Seq.singleton bar, delims))
                      , innerElems
                      ))
              end)))
        end

      val front = token funn ++ showTokenSyntaxSeq tab tyvars
    in
      Seq.iterate op++ (mkFunction (front, Seq.nth elems 0))
        (Seq.zipWith mkFunction (Seq.map token delims, Seq.drop elems 1))
    end

end
