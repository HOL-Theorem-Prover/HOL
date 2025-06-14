(** Copyright (c) 2022-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure TabbedTokenDoc :>
sig
  type doc
  type t = doc

  val empty: doc
  val space: doc
  val nospace: doc
  val token: Token.t -> doc
  val text: string -> doc
  val concat: doc * doc -> doc
  val letdoc: doc -> (DocVar.t -> doc) -> doc
  val var: DocVar.t -> doc

  type style = Tab.Style.t

  type tab
  val root: tab
  val newTabWithStyle: tab -> style * (tab -> doc) -> doc
  val newTab: tab -> (tab -> doc) -> doc
  val cond: tab -> {inactive: doc, active: doc} -> doc
  val at: tab -> doc -> doc

  val toStringDoc: {tabWidth: int, debug: bool} -> doc -> TabbedStringDoc.t

  val justCommentsToStringDoc: {tabWidth: int}
                               -> Token.t Seq.t
                               -> TabbedStringDoc.t
end =
struct

  structure D = TabbedStringDoc

  type tab = Tab.t
  type style = Tab.Style.t

  val root = Tab.root

  structure TabDict = Dict(Tab)
  structure TabSet = Set(Tab)
  structure VarDict = Dict(DocVar)

  datatype doc =
    Empty
  | Space
  | NoSpace
  | Concat of doc * doc
  | Token of Token.t
  | Text of string
  | At of tab * doc
  | NewTab of {tab: tab, doc: doc}
  | Cond of {tab: tab, inactive: doc, active: doc}
  | LetDoc of {var: DocVar.t, doc: doc, inn: doc}
  | Var of DocVar.t

  type t = doc

  val empty = Empty
  val nospace = NoSpace
  val space = Space
  val token = Token
  val text = Text
  val var = Var
  fun at t d = At (t, d)

  fun concat (d1, d2) =
    case (d1, d2) of
      (Empty, _) => d2
    | (_, Empty) => d1
    | _ => Concat (d1, d2)

  fun cond tab {inactive, active} =
    Cond {tab = tab, inactive = inactive, active = active}

  fun toString doc =
    case doc of
      Empty => ""
    | Space => "_"
    | NoSpace => "NoSpace"
    | Concat (d1, d2) => toString d1 ^ " ++ " ^ toString d2
    | Token t => "Token('" ^ Token.toString t ^ "')"
    | Text t => "Text('" ^ t ^ "')"
    | At (t, d) => "At(" ^ Tab.toString t ^ "," ^ toString d ^ ")"
    | NewTab {tab = t, doc = d, ...} =>
        "NewTab(" ^ Tab.toString t ^ ", " ^ toString d ^ ")"
    | Cond {tab = t, inactive = df, active = dnf} =>
        "Cond(" ^ Tab.toString t ^ ", " ^ toString df ^ ", " ^ toString dnf
        ^ ")"
    | LetDoc {var, doc = d, inn} =>
        "LetDoc(" ^ DocVar.toString var ^ ", " ^ toString d ^ ", "
        ^ toString inn ^ ")"
    | Var v => "Var(" ^ DocVar.toString v ^ ")"

  fun letdoc d f =
    let
      val v = DocVar.new ()
      val k = f v
    in
      LetDoc {var = v, doc = d, inn = k}
    end

  fun newTabWithStyle parent (style, genDocUsingTab: tab -> doc) =
    let
      val t = Tab.new {parent = parent, style = style}
      val d = genDocUsingTab t
    in
      NewTab {tab = t, doc = d}
    end

  fun newTab parent f = newTabWithStyle parent (Tab.Style.inplace, f)

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  datatype anndoc =
    AnnEmpty
  | AnnNewline
  | AnnNoSpace
  | AnnSpace
  | AnnToken of {at: TabSet.t option, tok: Token.t}
  | AnnText of {at: TabSet.t option, txt: string}
  | AnnConcat of anndoc * anndoc
  | AnnAt of {tab: tab, doc: anndoc}
  | AnnNewTab of {tab: tab, doc: anndoc}
  | AnnCond of {tab: tab, inactive: anndoc, active: anndoc}
  | AnnLetDoc of {var: DocVar.t, doc: anndoc, inn: anndoc}
  | AnnVar of DocVar.t


  fun annToString doc =
    case doc of
      AnnEmpty => ""
    | AnnNewline => "Newline"
    | AnnSpace => "_"
    | AnnNoSpace => "NoSpace"
    | AnnConcat (d1, d2) => annToString d1 ^ " ++ " ^ annToString d2
    | AnnToken {tok = t, ...} => "Token('" ^ Token.toString t ^ "')"
    | AnnText {txt = t, ...} => "Text('" ^ t ^ "')"
    | AnnAt {tab, doc} =>
        "At(" ^ Tab.toString tab ^ ", " ^ annToString doc ^ ")"
    | AnnNewTab {tab = t, doc = d, ...} =>
        "NewTab(" ^ Tab.toString t ^ ", " ^ annToString d ^ ")"
    | AnnCond {tab = t, inactive = df, active = dnf} =>
        "Cond(" ^ Tab.toString t ^ ", " ^ annToString df ^ ", "
        ^ annToString dnf ^ ")"
    | AnnLetDoc {var, doc = d, inn} =>
        "LetDoc(" ^ DocVar.toString var ^ ", " ^ annToString d ^ ", "
        ^ annToString inn ^ ")"
    | AnnVar v => "Var(" ^ DocVar.toString v ^ ")"


  fun annConcat (d1, d2) =
    case (d1, d2) of
      (AnnEmpty, _) => d2
    | (_, AnnEmpty) => d1
    | _ => AnnConcat (d1, d2)


  fun annotate doc =
    let
      (* if tab in broken, then tab has definitely had at least one break *)
      fun loop doc =
        case doc of
          Empty => AnnEmpty
        | Space => AnnSpace
        | NoSpace => AnnNoSpace
        | Token t => AnnToken {at = NONE, tok = t}
        | Text t => AnnText {at = NONE, txt = t}
        | Var v => AnnVar v
        | LetDoc {var, doc, inn} =>
            AnnLetDoc {var = var, doc = loop doc, inn = loop inn}
        | At (tab, doc) => AnnAt {tab = tab, doc = loop doc}
        | Concat (d1, d2) => AnnConcat (loop d1, loop d2)
        | NewTab {tab, doc} => AnnNewTab {tab = tab, doc = loop doc}
        | Cond {tab, inactive, active} =>
            AnnCond {tab = tab, inactive = loop inactive, active = loop active}

      val doc = loop doc
    in
      doc
    end

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  fun ensureSpaces debug (doc: anndoc) =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")

      datatype edge = Spacey | MaybeNotSpacey

      fun edgeOptUnion (e1, e2) =
        case (e1, e2) of
          (SOME MaybeNotSpacey, _) => SOME MaybeNotSpacey
        | (_, SOME MaybeNotSpacey) => SOME MaybeNotSpacey
        | (SOME Spacey, SOME Spacey) => SOME Spacey
        | (NONE, _) => NONE
        | (_, NONE) => NONE

      fun edgeOptToString e =
        case e of
          NONE => "NONE"
        | SOME Spacey => "Spacey"
        | SOME MaybeNotSpacey => "MaybeNotSpacey"

      fun loop vars doc =
        case doc of
          AnnEmpty => (NONE, doc, NONE)
        | AnnNewline => (SOME Spacey, doc, SOME Spacey)
        | AnnNoSpace => (SOME Spacey, doc, SOME Spacey)
        | AnnSpace => (SOME Spacey, doc, SOME Spacey)
        | AnnToken t => (SOME MaybeNotSpacey, doc, SOME MaybeNotSpacey)
        | AnnText t => (SOME MaybeNotSpacey, doc, SOME MaybeNotSpacey)
        | AnnConcat (d1, d2) =>
            let
              val (left, d1, leftright) = loop vars d1
              val (rightleft, d2, right) = loop vars d2
              val doc =
                case (leftright, rightleft) of
                  (SOME MaybeNotSpacey, SOME MaybeNotSpacey) =>
                    AnnConcat (AnnConcat (d1, AnnSpace), d2)
                | _ => AnnConcat (d1, d2)
              val left = if Option.isSome left then left else rightleft
              val right = if Option.isSome right then right else leftright
            in
              (left, doc, right)
            end
        | AnnAt {tab, doc} =>
            let val (left, doc, right) = loop vars doc
            in (left, AnnAt {tab = tab, doc = doc}, right)
            end
        | AnnNewTab {tab, doc} =>
            let val (left, doc, right) = loop vars doc
            in (left, AnnNewTab {tab = tab, doc = doc}, right)
            end
        | AnnCond {tab, active, inactive} =>
            let
              val (left1, active, right1) = loop vars active
              val (left2, inactive, right2) = loop vars inactive
            in
              ( edgeOptUnion (left1, left2)
              , AnnCond {tab = tab, active = active, inactive = inactive}
              , edgeOptUnion (right1, right2)
              )
            end
        | AnnLetDoc {var, doc, inn} =>
            let
              val (left, doc, right) = loop vars doc
              val vars = VarDict.insert vars (var, (left, right))
              val (left, inn, right) = loop vars inn
            in
              (left, AnnLetDoc {var = var, doc = doc, inn = inn}, right)
            end
        | AnnVar v =>
            let val (left, right) = VarDict.lookup vars v
            in (left, doc, right)
            end

      val (_, doc, _) = loop VarDict.empty doc
    in
      doc
    end

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  structure TokenKey =
  struct
    type t = Token.t
    fun compare (t1, t2) =
      let
        val s1 = Token.getSource t1
        val s2 = Token.getSource t2
      in
        case
          Int.compare
            (Source.absoluteStartOffset s1, Source.absoluteStartOffset s2)
        of
          EQUAL =>
            Int.compare
              (Source.absoluteEndOffset s1, Source.absoluteEndOffset s2)
        | other => other
      end
  end

  structure TokenDict = Dict(TokenKey)
  structure TokenSet = Set(TokenKey)

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  fun flowAts debug (doc: anndoc) =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")

      datatype tab_constraint = Active | Inactive
      type context = tab_constraint TabDict.t

      fun markInactive ctx tab = TabDict.insert ctx (tab, Inactive)

      fun markActive ctx tab =
        case Tab.parent tab of
          NONE => ctx
        | SOME p => markActive (TabDict.insert ctx (tab, Active)) p

      fun flowunion (flow1, flow2) =
        case (flow1, flow2) of
          (SOME ts1, SOME ts2) => SOME (TabSet.union (ts1, ts2))
        | (NONE, _) => flow2
        | (_, NONE) => flow1

      fun loop ctx (flowval, vars, doc) =
        case doc of
          AnnEmpty => (flowval, vars, doc)
        | AnnNewline => (flowval, vars, doc)
        | AnnSpace => (flowval, vars, doc)
        | AnnNoSpace => (flowval, vars, doc)
        | AnnToken {tok, ...} =>
            let
              (* val _ =
                Option.app
                  (fn ts =>
                     dbgprintln
                       ("token '" ^ Token.toString tok ^ "' at: "
                        ^
                        String.concatWith " "
                          (List.map Tab.toString (TabSet.listKeys ts)))) flowval *)
            in (NONE, vars, AnnToken {tok = tok, at = flowval})
            end
        | AnnText {txt, ...} =>
            let
              (* val _ =
                Option.app
                  (fn ts =>
                     dbgprintln
                       ("text '" ^ txt ^ "' at: "
                        ^
                        String.concatWith " "
                          (List.map Tab.toString (TabSet.listKeys ts)))) flowval *)
            in (NONE, vars, AnnText {txt = txt, at = flowval})
            end
        | AnnAt {tab, doc} =>
            let
              (* val flowval = SOME (TabSet.singleton tab) *)
              val flowval = flowunion (flowval, SOME (TabSet.singleton tab))
              val (_, vars, doc) = loop ctx (flowval, vars, doc)
            in
              (NONE, vars, AnnAt {tab = tab, doc = doc})
            end
        | AnnConcat (d1, d2) =>
            let
              val (flowval, vars, d1) = loop ctx (flowval, vars, d1)
              val (flowval, vars, d2) = loop ctx (flowval, vars, d2)
            in
              (flowval, vars, AnnConcat (d1, d2))
            end
        | AnnNewTab {tab, doc} =>
            let val (flowval, vars, doc) = loop ctx (flowval, vars, doc)
            in (flowval, vars, AnnNewTab {tab = tab, doc = doc})
            end
        | AnnCond {tab, active, inactive} =>
            (case TabDict.find ctx tab of
               SOME Active => loop ctx (flowval, vars, active)
             | SOME Inactive => loop ctx (flowval, vars, inactive)
             | _ =>
                 let
                   val (flow1, vars, inactive) =
                     loop (markInactive ctx tab) (flowval, vars, inactive)
                   val (flow2, vars, active) =
                     loop (markActive ctx tab) (flowval, vars, active)
                   val flowval = (* TODO: is union necessary here? *)
                     flowunion (flow1, flow2)
                 in
                   ( flowval
                   , vars
                   , AnnCond {tab = tab, active = active, inactive = inactive}
                   )
                 end)
        | AnnLetDoc {var, doc, inn} =>
            let
              val vars = VarDict.insert vars (var, NONE)
              val (flowval, vars, inn) = loop ctx (flowval, vars, inn)
            in
              (flowval, vars, AnnLetDoc {var = var, doc = doc, inn = inn})
            end
        | AnnVar v =>
            let
              val vars = VarDict.insert vars (v, flowunion
                (VarDict.lookup vars v, flowval))
            in
              (NONE, vars, AnnVar v)
            end

      val (_, varinfo, doc) = loop TabDict.empty
        (SOME (TabSet.singleton root), VarDict.empty, doc)

      fun updateVars doc =
        case doc of
          AnnLetDoc {var, doc = d, inn} =>
            let
              val flowval = VarDict.lookup varinfo var
              val (_, _, d) = loop TabDict.empty (flowval, varinfo, d)
            in
              AnnLetDoc {var = var, doc = d, inn = updateVars inn}
            end
        | AnnConcat (d1, d2) => AnnConcat (updateVars d1, updateVars d2)
        | AnnAt {tab, doc} => AnnAt {tab = tab, doc = updateVars doc}
        | AnnCond {tab, inactive, active} =>
            AnnCond
              { tab = tab
              , inactive = updateVars inactive
              , active = updateVars active
              }
        | AnnNewTab {tab, doc} => AnnNewTab {tab = tab, doc = updateVars doc}
        | _ => doc
    in
      updateVars doc
    end

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  fun insertComments debug (doc: anndoc) =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")

      fun isLast tok =
        not (Option.isSome (Token.nextTokenNotCommentOrWhitespace tok))

      fun commentsToDocs cs =
        Seq.map (fn c => AnnToken {at = NONE, tok = c}) cs

      val noComments = Seq.empty ()

      fun concatDocs ds =
        Seq.iterate annConcat AnnEmpty ds

      (* Find index i where the first i comments belong to tok1, and the
       * rest belong to tok2.
       * (tok1, comments, tok2) must be adjacent.
       *)
      fun findSplit (tok1, comments, tok2) =
        let
          val n = Seq.length comments
          fun loop i =
            if i >= n then n
            else if Token.lineDifference (tok1, Seq.nth comments i) > 0 then i
            else loop (i + 1)
        in
          loop 0
        end

      fun commentsBefore tok =
        case Token.prevTokenNotCommentOrWhitespace tok of
          NONE => commentsToDocs (Token.commentsBefore tok)
        | SOME ptok =>
            let
              val cs = Token.commentsBefore tok
              val cs = Seq.drop cs (findSplit (ptok, cs, tok))
            in
              commentsToDocs cs
            end

      fun commentsAfter tok =
        case Token.nextTokenNotCommentOrWhitespace tok of
          NONE => commentsToDocs (Token.commentsAfter tok)
        | SOME ntok =>
            let
              val cs = Token.commentsAfter tok
              val cs = Seq.take cs (findSplit (tok, cs, ntok))
            in
              commentsToDocs cs
            end

      (* returns (hasTokens?, commentsBefore, doc', commentsAfter)
       * ensures:
       *   if not ctxAllowsComments
       *   then (commentsBefore and commentsAfter are both empty)
       *)
      fun loop ctxAllowsComments vars doc :
        (bool * anndoc Seq.t * anndoc * anndoc Seq.t) =
        case doc of
          AnnEmpty => (false, noComments, doc, noComments)
        | AnnNewline => (false, noComments, doc, noComments)
        | AnnNoSpace => (false, noComments, doc, noComments)
        | AnnSpace => (false, noComments, doc, noComments)
        | AnnText _ => (false, noComments, doc, noComments)

        | AnnAt {tab, doc} =>
            let
              val (ht, cb, doc, ca) = (* loop false vars doc *)
                loop (ctxAllowsComments orelse Tab.allowsComments tab) vars doc
              val numComments = Seq.length cb + Seq.length ca
              val (ht, cb, doc, ca) =
                if numComments = 0 orelse not (Tab.allowsComments tab) then
                  (ht, cb, AnnAt {tab = tab, doc = doc}, ca)
                else
                  let
                    val all = Seq.map (fn d => AnnAt {tab = tab, doc = d})
                      (Seq.append3 (cb, Seq.singleton doc, ca))
                  in
                    (true, noComments, concatDocs all, noComments)
                  end
            in
              (ht, cb, doc, ca)
            end

        | AnnConcat (d1, d2) =>
            if not ctxAllowsComments then
              let
                val (ht1, _, d1, _) = loop false vars d1
                val (ht2, _, d2, _) = loop false vars d2
              in
                (ht1 orelse ht2, noComments, AnnConcat (d1, d2), noComments)
              end
            else
              let
                val (ht1, cb1, d1, ca1) = loop ctxAllowsComments vars d1
                val (ht2, cb2, d2, ca2) = loop ctxAllowsComments vars d2
              in
                if ht1 andalso ht2 then
                  ( true
                  , cb1
                  , annConcat (d1, annConcat
                      (concatDocs (Seq.append (ca1, cb2)), d2))
                  , ca2
                  )
                else if ht1 andalso not ht2 then
                  (true, cb1, AnnConcat (d1, d2), Seq.append3 (ca1, cb2, ca2))
                else if (not ht1) andalso ht2 then
                  (true, Seq.append3 (cb1, ca1, cb2), AnnConcat (d1, d2), ca2)
                else
                  ( false
                  , Seq.flatten (Seq.fromList [cb1, ca1, cb2, ca2])
                  , AnnConcat (d1, d2)
                  , noComments
                  )
              end

        | AnnNewTab {tab, doc} =>
            let val (ht, cb, doc, ca) = loop ctxAllowsComments vars doc
            in (ht, cb, AnnNewTab {tab = tab, doc = doc}, ca)
            end

        | AnnCond {tab, inactive, active} =>
            let
              val (ht1, _, inactive, _) = loop false vars inactive
              val (ht2, _, active, _) = loop false vars active
            in
              ( ht1 orelse ht2
              , noComments
              , AnnCond {tab = tab, inactive = inactive, active = active}
              , noComments
              )
            end

        | AnnLetDoc {var, doc, inn} =>
            let
              val (ht, _, doc, _) = loop false vars doc
              val vars = VarDict.insert vars (var, ht)
              val (ht, cb, inn, ca) = loop ctxAllowsComments vars inn
            in
              (ht, cb, AnnLetDoc {var = var, doc = doc, inn = inn}, ca)
            end

        | AnnVar v => (VarDict.lookup vars v, noComments, doc, noComments)

        | AnnToken {at = flow, tok} =>
            let
              val cb = commentsBefore tok
              val ca = commentsAfter tok
              val numComments = Seq.length cb (* + Seq.length ca *)

              val doc = annConcat (doc, concatDocs ca)
            in
              if ctxAllowsComments then
                (* (true, cb, doc, ca) *)
                (true, cb, doc, noComments)
              else if numComments = 0 then
                (true, noComments, doc, noComments)
              else

                case flow of
                  NONE =>
                    ( true
                    , noComments
                    (* , concatDocs (Seq.append3 (cb, Seq.singleton doc, ca)) *)
                    , concatDocs (Seq.append (cb, Seq.singleton doc))
                    , noComments
                    )

                | SOME tabs =>
                    let
                      val tab =
                        (* TODO: what to do when there are multiple possible tabs
                         * this token could be at? Here we just pick the first
                         * of these in the set, and usually it seems each token
                         * is only ever 'at' one possible tab...
                         *)
                        List.hd (TabSet.listKeys tabs)

                      fun withBreak d = AnnAt {tab = tab, doc = d}

                      (* val all = Seq.append3 (cb, Seq.singleton doc, ca) *)
                      val all = Seq.append (cb, Seq.singleton doc)
                    in
                      ( true
                      , noComments
                      , Seq.iterate annConcat (Seq.nth all 0) (Seq.map withBreak
                          (Seq.drop all 1))
                      , noComments
                      )
                    end
            end

      val (_, _, doc, _) = loop false VarDict.empty doc
    in
      flowAts debug doc
    end

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  (* TODO: bug: this doesn't insert a blank line where it should in this case:
   *
   *   <token1>
   *   ++
   *   newTab root (fn inner =>
   *     at(root) ++
   *     at(inner) ++ <token2>
   *   )
   *
   * The flow analysis will observe that <token2> is at 'inner'. But it's
   * possible that 'inner' is inactive and 'root' is active. Visually, this
   * will look like <token2> is below <token1>, and therefore blank lines
   * should be inserted between if necessary.
   *
   * However, our technique for inserting blank lines (currently) is to
   * insert a conditional newline which is active only if the flowval tab
   * is active.
   *
   * In this particular example, the fix would be to conditionally newline
   * if either 'root' is active OR 'inner' is active. But how to compute
   * that?
   *)
  fun insertBlankLines debug (doc: anndoc) =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")

      fun breaksBefore doc tab n =
        if n = 0 then
          doc
        else
          let
            val doc = AnnConcat
              ( AnnCond {tab = tab, inactive = AnnEmpty, active = AnnNewline}
              , doc
              )
          in
            breaksBefore doc tab (n - 1)
          end

      fun prevTokenNotWhitespace t =
        case Token.prevToken t of
          NONE => NONE
        | SOME p =>
            if Token.isWhitespace p then prevTokenNotWhitespace p else SOME p

      fun loop doc =
        case doc of
          AnnEmpty => doc
        | AnnNewline => doc
        | AnnNoSpace => doc
        | AnnSpace => doc
        | AnnText _ => doc
        | AnnAt {tab, doc} => AnnAt {tab = tab, doc = loop doc}
        | AnnToken {at = NONE, tok} => doc
        | AnnToken {at = SOME tabs, tok} =>
            (case prevTokenNotWhitespace tok of
               NONE => doc
             | SOME prevTok =>
                 let
                   val diff = Token.lineDifference (prevTok, tok) - 1
                   val diff = Int.max (0, Int.min (2, diff))
                 (* val _ = dbgprintln
                   ("line diff ('" ^ Token.toString prevTok ^ "','"
                    ^ Token.toString tok ^ "'): " ^ Int.toString diff) *)
                 in
                   if diff = 0 then
                     doc
                   else
                     (* TODO: what to do when there are multiple possible tabs
                      * this token could be at? Here we just pick the first
                      * of these in the set, and usually it seems each token
                      * is only ever 'at' one possible tab...
                      *)
                     breaksBefore doc (List.hd (TabSet.listKeys tabs)) diff
                 end)
        | AnnConcat (d1, d2) => AnnConcat (loop d1, loop d2)
        | AnnNewTab {tab, doc} => AnnNewTab {tab = tab, doc = loop doc}
        | AnnCond {tab, inactive, active} =>
            AnnCond {tab = tab, inactive = loop inactive, active = loop active}
        | AnnLetDoc {var, doc, inn} =>
            AnnLetDoc {var = var, doc = loop doc, inn = loop inn}
        | AnnVar v => AnnVar v
    in
      loop doc
    end

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  structure TCS = TerminalColorString

  fun tokenToStringDoc currentTab tabWidth tok =
    if not (Token.isComment tok orelse Token.isStringConstant tok) then
      D.text (SyntaxHighlighter.highlightToken tok)
    else
      let
        val src = Token.getSource tok

        (** effective offset of the beginning of this token within its line,
          * counting tab-widths appropriately.
          *)
        val effectiveOffset =
          let
            val {col, line = lineNum} = Source.absoluteStart src
            val len = col - 1
            val charsBeforeOnSameLine =
              Source.take (Source.wholeLine src lineNum) len
            fun loop effOff i =
              if i >= len then
                effOff
              else if #"\t" = Source.nth charsBeforeOnSameLine i then
                (* advance up to next tabstop *)
                loop (effOff + tabWidth - effOff mod tabWidth) (i + 1)
              else
                loop (effOff + 1) (i + 1)
          in
            loop 0 0
          end

        fun strip line =
          let
            val (_, ln) =
              TCS.stripEffectiveWhitespace
                {tabWidth = tabWidth, removeAtMost = effectiveOffset} line
          in
            ln
          end

        val t = SyntaxHighlighter.highlightToken tok

        val pieces =
          Seq.map (fn (i, j) => D.text (strip (TCS.substring (t, i, j - i))))
            (Source.lineRanges src)

        val numPieces = Seq.length pieces
      in
        if numPieces = 1 then
          D.text t
        else
          let
            val tab = Tab.new
              { parent = currentTab
              , style = Tab.Style.combine (Tab.Style.inplace, Tab.Style.rigid)
              }
            val doc =
              (* a bit of a hack here: we concatenate a space on the end of
               * each piece (except last), which guarantees that blank lines
               * within the comment are preserved.
               *)
              Seq.iterate D.concat D.empty
                (Seq.map (fn x => D.at tab (D.concat (x, D.space)))
                   (Seq.take pieces (numPieces - 1)))
            val doc = D.concat (doc, D.at tab (Seq.nth pieces (numPieces - 1)))
            val doc = D.newTab (tab, doc)
          in
            doc
          end
      end

  (* ====================================================================== *)

  fun justCommentsToStringDoc {tabWidth} cs =
    Seq.iterate D.concat D.empty
      (Seq.map (fn c => D.at Tab.root (tokenToStringDoc Tab.root tabWidth c)) cs)

  (* ====================================================================== *)


  fun toStringDoc (args as {tabWidth, debug}) doc =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")

      val (doc, tm) = Util.getTime (fn _ => annotate doc)
      val _ = dbgprintln ("annotate: " ^ Time.fmt 3 tm ^ "s")
      (* val (doc, tm) = Util.getTime (fn _ => flowAts debug doc)
      val _ = dbgprintln ("flowAts: " ^ Time.fmt 3 tm ^ "s")
      val (doc, tm) = Util.getTime (fn _ => insertComments debug doc)
      val _ = dbgprintln ("insertComments: " ^ Time.fmt 3 tm ^ "s") *)
      (* val (doc, tm) = Util.getTime (fn _ => ensureSpaces debug doc)
      val _ = dbgprintln ("ensureSpaces: " ^ Time.fmt 3 tm ^ "s") *)
      (* val (doc, tm) = Util.getTime (fn _ => insertBlankLines debug doc)
      val _ = dbgprintln ("insertBlankLines: " ^ Time.fmt 3 tm ^ "s") *)

      fun loop currentTab vars doc =
        case doc of
          AnnEmpty => D.empty
        | AnnNoSpace => D.nospace
        | AnnNewline => D.newline
        | AnnSpace => D.space
        | AnnConcat (d1, d2) =>
            D.concat (loop currentTab vars d1, loop currentTab vars d2)
        | AnnText {txt, ...} => D.text (TerminalColorString.fromString txt)
        | AnnToken {at, tok} => D.token tok
        (* let
          val tab =
            case
              at
            of
              NONE => currentTab
            | SOME tabs =>
                (* TODO: what to do when there are multiple possible
                 * tabs here? *) List.hd (TabSet.listKeys tabs)

          val doc = tokenToStringDoc tab tabWidth tok
        in
          doc
        end *)
        | AnnAt {tab, doc, ...} => D.at tab (loop currentTab vars doc)
        | AnnCond {tab, inactive, active} =>
            D.cond tab
              { inactive = loop currentTab vars inactive
              , active = loop currentTab vars active
              }
        | AnnNewTab {tab, doc} => D.newTab (tab, loop tab vars doc)
        | AnnLetDoc {var, doc, inn} =>
            D.letdoc
              { var = var
              , doc = loop currentTab vars doc
              , inn = loop currentTab vars inn
              }
        (* let
          val doc' = loop currentTab vars doc
          val vars = VarDict.insert vars (var, doc')
        in
          loop currentTab vars inn
        end *)
        | AnnVar v => D.var v

      val (result, tm) = Util.getTime (fn _ => loop Tab.root VarDict.empty doc)

      val _ = dbgprintln ("convert: " ^ Time.fmt 3 tm ^ "s")
    in
      result
    end

end
