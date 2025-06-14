(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** This is essentially an intermediate representation for pretty-printing.
  * It's similar to a pretty doc, but the elements are tokens. The primary
  * transformation on this IR is to add comments.
  *)
structure TokenDoc :>
sig
  type t
  type doc = t

  val empty: doc
  val token: Token.t -> doc

  val indent: doc -> doc

  val beside: doc * doc -> doc

  (** Align a doc so that it wraps back to the same indentation as the
    * first doc:
    *
    *      d1       d2           besideAndAbove (d1, d2)
    *    .......   ****             .......
    *    .......   ***    ====>     .......
    *    .....                      .....****
    *                               ***
    *
    * The first version gets replaced by a space when undone by group. The
    * second is put exactly beside.
    *)
  val besideAndAboveOrSpace: doc * doc -> doc
  val besideAndAbove: doc * doc -> doc

  (** When an "above" is flattened by a group, it can either be replaced by a
    * a space, or it can be put exactly beside (with no extra space).
    *)
  val aboveOrSpace: doc * doc -> doc
  val aboveOrBeside: doc * doc -> doc

  val space: doc
  val softspace: doc
  val group: doc -> doc
  val rigid: doc -> doc

  val insertBlankLines: doc -> doc
  val insertComments: doc -> doc

  val toStringDoc: {tabWidth: int} -> doc -> StringDoc.t
end =
struct

  structure TCS = TerminalColorString

  (** for Space and Above, the boolean indicates whether or not to
    * keep space when undone by group.
    *)
  datatype doc =
    Empty
  | Space of bool
  | Indent of doc
  | Token of Token.t
  | Beside of doc * doc
  | BesideAndAbove of bool * doc * doc
  | Above of bool * doc * doc
  | Group of doc
  | Rigid of doc

  type t = doc

  val empty = Empty
  val token = Token
  val group = Group
  val rigid = Rigid
  fun indent d = Indent d

  fun beside (doc1, doc2) =
    case (doc1, doc2) of
      (Empty, _) => doc2
    | (_, Empty) => doc1
    | _ => Beside (doc1, doc2)

  fun above' withSpace (doc1, doc2) =
    case (doc1, doc2) of
      (Empty, _) => doc2
    | (_, Empty) => doc1
    | _ => Above (withSpace, doc1, doc2)

  fun besideAndAbove' withSpace (doc1, doc2) =
    case (doc1, doc2) of
      (Empty, _) => doc2
    | (_, Empty) => doc1
    | _ => BesideAndAbove (withSpace, doc1, doc2)

  val besideAndAboveOrSpace = besideAndAbove' true
  val besideAndAbove = besideAndAbove' false

  val aboveOrSpace = above' true
  val aboveOrBeside = above' false

  val empty = Empty
  val space = Space true
  val softspace = Space false

  fun insertBlankLines doc =
    let
      fun blankLinesAbove d n =
        if n <= 0 then d else blankLinesAbove (Above (false, space, d)) (n - 1)

      fun preferRight (a, b) =
        if Option.isSome b then b else a
      fun preferLeft (a, b) =
        if Option.isSome a then a else b

      fun doDoc doc =
        case doc of
          Token tok => (SOME tok, doc, SOME tok)

        | Indent d =>
            let val (first, d', last) = doDoc d
            in (first, Indent d', last)
            end

        | Group d =>
            let val (first, d', last) = doDoc d
            in (first, Group d', last)
            end

        | Beside (d1, d2) =>
            let
              val (first1, d1', last1) = doDoc d1
              val (first2, d2', last2) = doDoc d2

              val first = preferLeft (first1, first2)
              val last = preferRight (last1, last2)
            in
              (first, Beside (d1', d2'), last)
            end

        | BesideAndAbove (b, d1, d2) =>
            let
              val (first1, d1', last1) = doDoc d1
              val (first2, d2', last2) = doDoc d2

              val first = preferLeft (first1, first2)
              val last = preferRight (last1, last2)
            in
              (first, BesideAndAbove (b, d1', d2'), last)
            end

        | Above (b, d1, d2) =>
            let
              val (first1, d1', last1) = doDoc d1
              val (first2, d2', last2) = doDoc d2
              val first = preferLeft (first1, first2)
              val last = preferRight (last1, last2)

              val result =
                case (last1, first2) of
                  (SOME t1, SOME t2) =>
                    let
                      val diff = Token.lineDifference (t1, t2) - 1
                      val diff = Int.max (0, Int.min (2, diff))
                    in
                      (* print ("handling " ^ Token.toString t1 ^ " above " ^ Token.toString t2 ^ ": difference " ^ Int.toString diff ^ "\n"); *)

                      Above (b, d1', blankLinesAbove d2' diff)
                    end

                | _ => Above (b, d1', d2')
            in
              (first, result, last)
            end

        | Rigid d =>
            let val (first, d', last) = doDoc d
            in (first, Rigid d', last)
            end

        | _ => (NONE, doc, NONE)

      val (_, doc, _) = doDoc doc
    in
      doc
    end


  fun raiseComments doc =
    let
      fun finalize (doc, commBefore, commAfter) =
        aboveOrSpace (commBefore, aboveOrSpace (doc, commAfter))

      fun modifyDoc g (ht, doc, cb, ca) = (ht, g doc, cb, ca)

      fun combine bin (hasToks1, d1, cb1, ca1) (hasToks2, d2, cb2, ca2) =
        let
          val (resultDoc, cb, ca) =
            if hasToks1 andalso hasToks2 then
              (bin (d1, bin (ca1, bin (cb2, d2))), cb1, ca2)
            else if hasToks1 andalso not hasToks2 then
              (bin (d1, d2), cb1, bin (ca1, bin (cb2, ca2)))
            else if not hasToks1 andalso hasToks2 then
              (bin (d1, d2), bin (cb1, bin (ca1, cb2)), ca2)
            else
              (bin (d1, d2), bin (cb1, bin (ca1, bin (cb2, ca2))), Empty)
        in
          (hasToks1 orelse hasToks2, resultDoc, cb, ca)
        end

      (* returns (containsTokens?, doc', commentsBefore, commentsAfter) *)
      fun loop doc =
        case doc of
          Empty => (false, Empty, Empty, Empty)
        | Space b => (false, Space b, Empty, Empty)
        | Indent doc =>
            let
              val (hasToks, doc', cb, ca) = loop doc
            in
              if hasToks then
                (true, Indent (finalize (doc', cb, ca)), Empty, Empty)
              else
                (false, Indent doc', cb, ca)
            end
        | Token t =>
            if Token.isComment t then (false, Empty, Token t, Empty)
            else (true, Token t, Empty, Empty)
        | Beside (d1, d2) => combine beside (loop d1) (loop d2)
        | BesideAndAbove (withSpace, d1, d2) =>
            combine (besideAndAbove' withSpace) (loop d1) (loop d2)
        | Above (withSpace, d1, d2) =>
            combine (above' withSpace) (loop d1) (loop d2)
        | Group doc => modifyDoc Group (loop doc)
        | Rigid doc => modifyDoc Rigid (loop doc)

      val (_, doc, commBefore, commAfter) = loop doc
    in
      finalize (doc, commBefore, commAfter)
    end


  fun insertComments doc =
    let
      (** Does this doc most recently appear beside something,
        * or below something?
        *)
      datatype mode = BesideMode | AboveMode

      fun tokens mode toks =
        let
          fun combine (doc, tok) =
            case mode of
              BesideMode => beside (doc, beside (space, Token tok))
            | AboveMode => aboveOrSpace (doc, Token tok)
        in
          Seq.iterate combine (Token (Seq.nth toks 0)) (Seq.drop toks 1)
        end

      fun insertCommentsBeforeTok mode tok =
        tokens mode (Seq.append (Token.commentsBefore tok, Seq.$ tok))

      fun insertCommentsAfterTok mode tok =
        tokens mode (Seq.append (Seq.$ tok, Token.commentsAfter tok))

      fun insertAllBefore mode d =
        case d of
          Empty => Empty
        | Space b => Space b
        | Indent d => Indent (insertAllBefore mode d)
        | Token tok => insertCommentsBeforeTok mode tok
        | Beside (d1, d2) =>
            Beside (insertAllBefore mode d1, insertAllBefore BesideMode d2)
        | BesideAndAbove (b, d1, d2) =>
            BesideAndAbove
              (b, insertAllBefore mode d1, insertAllBefore BesideMode d2)
        | Above (b, d1, d2) =>
            Above (b, insertAllBefore mode d1, insertAllBefore AboveMode d2)
        | Group d => Group (insertAllBefore mode d)
        | Rigid d => Rigid (insertAllBefore mode d)

      fun insertOnlyAfterLast mode d =
        case d of
          Empty => (false, Empty)
        | Space b => (false, Space b)
        | Indent d =>
            let val (foundIt, d') = insertOnlyAfterLast mode d
            in (foundIt, Indent d')
            end
        | Token tok => (true, insertCommentsAfterTok mode tok)
        | Beside (d1, d2) =>
            let
              val (foundIt, d2') = insertOnlyAfterLast BesideMode d2
            in
              if foundIt then
                (true, Beside (d1, d2'))
              else
                let val (foundIt, d1') = insertOnlyAfterLast mode d1
                in (foundIt, Beside (d1', d2'))
                end
            end
        | BesideAndAbove (b, d1, d2) =>
            let
              val (foundIt, d2') = insertOnlyAfterLast BesideMode d2
            in
              if foundIt then
                (true, BesideAndAbove (b, d1, d2'))
              else
                let val (foundIt, d1') = insertOnlyAfterLast mode d1
                in (foundIt, BesideAndAbove (b, d1', d2'))
                end
            end
        | Above (b, d1, d2) =>
            let
              val (foundIt, d2') = insertOnlyAfterLast AboveMode d2
            in
              if foundIt then
                (true, Above (b, d1, d2'))
              else
                let val (foundIt, d1') = insertOnlyAfterLast mode d1
                in (foundIt, Above (b, d1', d2'))
                end
            end
        | Group d =>
            let val (foundIt, d') = insertOnlyAfterLast mode d
            in (foundIt, Group d')
            end
        | Rigid d =>
            let val (foundIt, d') = insertOnlyAfterLast mode d
            in (foundIt, Rigid d')
            end

      val doc = insertAllBefore AboveMode doc
      val (_, doc) = insertOnlyAfterLast AboveMode doc
      val doc = raiseComments doc
    in
      doc
    end


  (** returns whether or not allowed to be grouped *)
  fun tokenToStringDoc tabWidth tok =
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
        Seq.map
          (fn (i, j) => StringDoc.text (strip (TCS.substring (t, i, j - i))))
          (Source.lineRanges src)
    (* val _ =
      let
        val ss = Token.toString tok
        val ranges = Source.lineRanges src
        val lines = Seq.map (fn (i, j) => TCS.substring (t, i, j-i)) ranges
        val stripped = Seq.map strip lines
        fun p s = Util.for (0, Seq.length s) (fn i =>
          print (String.toString (TCS.toString {colors=false} (Seq.nth s i)) ^ "\n"))
      in
        print ("------- token -------\n");
        print (String.toString ss ^ "\n");
        print ("------- lines -------\n");
        p lines;
        print ("------- strip -------\n");
        p stripped;
        print ("---------------------\n")
      end *)
    in
      if Seq.length pieces = 1 then (true, StringDoc.text t)
      else (false, Seq.iterate StringDoc.aboveOrSpace StringDoc.empty pieces)
    end


  fun toStringDoc {tabWidth} d =
    let
      (** returns whether or not allowed to be grouped *)
      fun loop d =
        case d of
          Empty => (true, StringDoc.empty)

        | Space true => (true, StringDoc.space)

        | Space false => (true, StringDoc.softspace)

        | Token t => tokenToStringDoc tabWidth t

        | Indent d =>
            let val (groupable, d') = loop d
            in (groupable, StringDoc.indent d')
            end

        | Beside (d1, d2) =>
            let
              val (g1, d1') = loop d1
              val (g2, d2') = loop d2
            in
              (g1 andalso g2, StringDoc.beside (d1', d2'))
            end

        | BesideAndAbove (b, d1, d2) =>
            let
              val (g1, d1') = loop d1
              val (g2, d2') = loop d2
            in
              ( g1 andalso g2
              , if b then StringDoc.besideAndAboveOrSpace (d1', d2')
                else StringDoc.besideAndAbove (d1', d2')
              )
            end

        | Above (b, d1, d2) =>
            let
              val (g1, d1') = loop d1
              val (g2, d2') = loop d2
            in
              ( g1 andalso g2
              , if b then StringDoc.aboveOrSpace (d1', d2')
                else StringDoc.aboveOrBeside (d1', d2')
              )
            end

        | Group d =>
            let val (groupable, d') = loop d
            in if groupable then (true, StringDoc.group d') else (false, d')
            end

        | Rigid d => let val (_, d') = loop d in (false, StringDoc.rigid d') end

      val (_, d') = loop d
    in
      d'
    end

end
