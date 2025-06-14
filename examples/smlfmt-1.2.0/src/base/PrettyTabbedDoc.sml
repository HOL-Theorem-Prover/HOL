(** Copyright (c) 2022-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** Functor argument CustomString could either be a standard string, or could
  * be a TerminalColorString, etc.
  *)
functor PrettyTabbedDoc
  (structure CustomString:
   sig
     type t
     val substring: t * int * int -> t

     (* should be visually distinct, e.g., color the background.
      * the integer argument is a depth; this can be ignored (in which
      * case all depths will be emphasized the same) or can be used
      * to distinguish different tab depths
      *)
     val emphasize: int -> t -> t

     val fromString: string -> t
     val toString: t -> string
     val size: t -> int
     val concat: t list -> t
   end

   structure Token:
   sig
     type t
     val same: t * t -> bool
     val desiredBlankLinesBefore: t -> int
     val splitCommentsBefore: t -> t Seq.t
     val splitCommentsAfter: t -> t Seq.t
     val splitCommentsAfterAndBeforeNext: t -> t Seq.t * t Seq.t
   end

   datatype pieces =
     OnePiece of CustomString.t
   | ManyPieces of CustomString.t Seq.t

   val tokenToPieces: {tabWidth: int} -> Token.t -> pieces) :>
sig
  type doc
  type t = doc

  exception InvalidDoc

  val empty: doc
  val nospace: doc
  val space: doc
  val text: CustomString.t -> doc
  val token: Token.t -> doc
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

  val pretty:
    { ribbonFrac: real
    , maxWidth: int
    , indentWidth: int
    , tabWidth: int
    , debug: bool
    }
    -> doc
    -> CustomString.t

  val prettyJustComments:
    { ribbonFrac: real
    , maxWidth: int
    , indentWidth: int
    , tabWidth: int
    , debug: bool
    }
    -> Token.t Seq.t
    -> CustomString.t
end =
struct

  (* IDEA: lazily activate tabs. If size/ribbon are violated, then
   * promote the outermost tab.
   *
   * Promotion follows this progression, which improves horizontal compaction:
   *       Flattened -> ActivatedInPlace -> ActivatedIndented
   *           -----------------> (horizontal compaction)
   *)


  structure TabDict = Dict(Tab)
  structure TabSet = Set(Tab)
  structure VarDict = Dict(DocVar)

  (* ====================================================================== *)

  exception InvalidDoc

  type tab = Tab.t
  type style = Tab.Style.t

  val root = Tab.root

  (* SAM_NOTE: small time/space tradeoff here. In comparison to SimplePromise,
   * the MemoizedPromise implementation seems to be 5-10% faster using
   * 10-20% more space. IMO the time improvement is a win, since smlfmt
   * needs to be fast. *)
  structure Promise = MemoizedPromise
  (* structure Promise = SimplePromise *)

  datatype doc =
    Empty
  | Space
  | NoSpace
  | Newline
  | Concat of doc * doc
  | Text of CustomString.t
  | Token of Token.t
  | At of tab * doc
  | NewTab of {tab: tab, gen: doc Promise.t}
  | Cond of {tab: tab, inactive: doc, active: doc}
  | LetDoc of {var: DocVar.t, doc: doc, inn: doc}
  | Var of DocVar.t

  type t = doc

  val empty = Empty
  val newline = Newline
  val nospace = NoSpace
  val space = Space
  val text = Text
  val token = Token
  fun at t d = At (t, d)

  val letdoc = LetDoc
  val var = Var

  fun cond tab {inactive, active} =
    Cond {tab = tab, inactive = inactive, active = active}

  fun concat (d1, d2) =
    case (d1, d2) of
      (Empty, _) => d2
    | (_, Empty) => d1
    | _ => Concat (d1, d2)

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
      fun gen () = genDocUsingTab t
    in
      NewTab {tab = t, gen = Promise.new gen}
    end

  fun newTab parent f = newTabWithStyle parent (Tab.Style.inplace, f)

  (* ====================================================================== *)

  fun firstToken doc =
    let
      fun error () =
        raise Fail "PrettyTabbedDoc.firstToken: disagreement"

      fun loop vars doc =
        case doc of
          Concat (d1, d2) =>
            (case loop vars d1 of
               NONE => loop vars d2
             | t => t)
        | Token t => SOME t
        | At (_, d) => loop vars d
        | NewTab {gen, ...} => loop vars (Promise.get gen)
        | Cond {inactive, active, ...} =>
            (case (loop vars inactive, loop vars active) of
               (NONE, NONE) => NONE
             | (SOME t, SOME t') =>
                 if Token.same (t, t') then SOME t else error ()
             | _ => error ())
        | LetDoc {var, doc, inn} =>
            let
              val x = loop vars doc
              val vars = VarDict.insert vars (var, x)
            in
              loop vars inn
            end
        | Var v => VarDict.lookup vars v
        | _ => NONE
    in
      loop VarDict.empty doc
    end

  (* ====================================================================== *)


  fun spaces count =
    CustomString.fromString (CharVector.tabulate (count, fn _ => #" "))


  datatype sentry =
    StartTabHighlight of {tab: tab, col: int}
  | StartMaxWidthHighlight of {col: int}


  datatype eentry =
    EndTabHighlight of {tab: tab, col: int}
  | EndMaxWidthHighlight of {col: int}


  fun sentryCol se =
    case se of
      StartTabHighlight {col, ...} => col
    | StartMaxWidthHighlight {col} => col


  fun eentryCol ee =
    case ee of
      EndTabHighlight {col, ...} => col
    | EndMaxWidthHighlight {col} => col


  fun sentryCmp (se1, se2) =
    case (se1, se2) of
      ( StartTabHighlight {tab = tab1, col = col1}
      , StartTabHighlight {tab = tab2, col = col2}
      ) =>
        (case Int.compare (col1, col2) of
           EQUAL => Tab.compare (tab1, tab2)
         | other => other)

    | (StartTabHighlight {col = col1, ...}, StartMaxWidthHighlight {col = col2}) =>
        (case Int.compare (col1, col2) of
           EQUAL => LESS
         | other => other)

    | (StartMaxWidthHighlight {col = col1}, StartTabHighlight {col = col2, ...}) =>
        (case Int.compare (col1, col2) of
           EQUAL => GREATER
         | other => other)

    | _ => Int.compare (sentryCol se1, sentryCol se2)


  fun eentryCmp (ee1, ee2) =
    case (ee1, ee2) of
      ( EndTabHighlight {tab = tab1, col = col1}
      , EndTabHighlight {tab = tab2, col = col2}
      ) =>
        (case Int.compare (col1, col2) of
           EQUAL => Tab.compare (tab1, tab2)
         | other => other)

    | (EndTabHighlight {col = col1, ...}, EndMaxWidthHighlight {col = col2}) =>
        (case Int.compare (col1, col2) of
           EQUAL => LESS
         | other => other)

    | (EndMaxWidthHighlight {col = col1}, EndTabHighlight {col = col2, ...}) =>
        (case Int.compare (col1, col2) of
           EQUAL => GREATER
         | other => other)

    | _ => Int.compare (eentryCol ee1, eentryCol ee2)


  fun matchingStartEndEntries (se, ee) =
    case (se, ee) of
      ( StartTabHighlight {tab = st, col = sc}
      , EndTabHighlight {tab = et, col = ec, ...}
      ) => Tab.eq (st, et) andalso sc = ec

    | (StartMaxWidthHighlight {col = sc}, EndMaxWidthHighlight {col = ec}) =>
        sc = ec

    | _ => false


  fun sentryEmphasizer se =
    case se of
      StartTabHighlight {tab, ...} => CustomString.emphasize (Tab.depth tab)
    | StartMaxWidthHighlight {...} => CustomString.emphasize 10000000


  fun sentrytos se =
    case se of
      StartTabHighlight {tab = st, col = scol} =>
        "StartTabHighlight {tab = " ^ Tab.name st ^ ", col = "
        ^ Int.toString scol ^ "}"

    | StartMaxWidthHighlight {col} =>
        "StartMaxWidthHighlight {col = " ^ Int.toString col ^ "}"


  fun eentrytos ee =
    case ee of
      EndTabHighlight {tab = et, col = ecol} =>
        "EndTabHighlight {tab = " ^ Tab.name et ^ ", col = " ^ Int.toString ecol
        ^ "}"

    | EndMaxWidthHighlight {col} =>
        "EndMaxWidthHighlight {col = " ^ Int.toString col ^ "}"


  fun sentryInfo se =
    case se of
      StartTabHighlight {tab, ...} =>
        sentryEmphasizer se (CustomString.fromString ("^" ^ Tab.name tab))
    | StartMaxWidthHighlight _ =>
        sentryEmphasizer se (CustomString.fromString "^maxWidth")

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)

  structure Item =
  struct

    datatype item =
      Spaces of int
    | Newline
    | Stuff of CustomString.t
    | StartDebug of sentry
    | EndDebug of eentry

    type t = item


    fun width item =
      case item of
        Spaces n => n
      | Stuff s => CustomString.size s
      | _ => raise Fail "PrettyTabbedDoc.Item.width"


    fun toString item =
      case item of
        Spaces n => "Spaces(" ^ Int.toString n ^ ")"
      | Stuff s =>
          if width item <= 5 then
            "Stuff('" ^ CustomString.toString s ^ "')"
          else
            "Stuff('" ^ String.substring (CustomString.toString s, 0, 5)
            ^ "...')"
      | _ => "???"


    fun split item i =
      if i < 0 orelse i + 1 > width item then
        raise Fail "PrettyTabbedDoc.Item.split: size"
      else
        (* i+1 <= width item *)
        case item of
          Spaces n =>
            (Spaces i, CustomString.fromString " ", Spaces (n - i - 1))
        | Stuff s =>
            let
              val n = CustomString.size s
              val left = CustomString.substring (s, 0, i)
              val mid = CustomString.substring (s, i, 1)
              val right = CustomString.substring (s, i + 1, n - i - 1)
            in
              (Stuff left, mid, Stuff right)
            end
        | _ => raise Fail "PrettyTabbedDoc.Item.split: bad item"

  end

  type item = Item.t

  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)


  fun implementDebugs maxWidth items =
    let
      fun highlightActive accCurrLine acc startDebugs =
        let
          val orderedHighlightCols =
            (* Mergesort.sort sentryCmp (Seq.fromList startDebugs) *)
            Seq.fromList
              (ListMergeSort.sort (Util.gtOfCmp sentryCmp) startDebugs)

          fun processItem (item, (currCol, hi, acc)) =
            let
              val () = ()
              (* val _ = print ("processItem " ^ itos item ^ "\n") *)
              val nextHighlightCol =
                if hi < Seq.length orderedHighlightCols then
                  sentryCol (Seq.nth orderedHighlightCols hi)
                else
                  valOf Int.maxInt

              val n = Item.width item
            in
              if nextHighlightCol < currCol then
                processItem (item, (currCol, hi + 1, acc))
              else if currCol + n <= nextHighlightCol then
                (currCol + n, hi, item :: acc)
              else
                let
                  val emphasizer = sentryEmphasizer
                    (Seq.nth orderedHighlightCols hi)
                  val (left, mid, right) =
                    Item.split item (nextHighlightCol - currCol)
                (*
                val _ =
                  print ("item: " ^ itos item
                     ^ " split into (" ^ itos left ^ ", _, " ^ itos right ^ ")"
                     ^ " nextHightlightCol: " ^ Int.toString nextHighlightCol
                     ^ " currCol: " ^ Int.toString currCol
                     ^ " itemWidth: " ^ Int.toString n
                     ^ " hi: " ^ Int.toString hi
                     ^ "\n")
                *)
                in
                  processItem
                    ( right
                    , ( nextHighlightCol + 1
                      , hi + 1
                      , Item.Stuff (emphasizer mid) :: left :: acc
                      )
                    )
                end
            end

          val (currCol, hi, acc) =
            List.foldr processItem (0, 0, acc) accCurrLine

          (* finish out the columns to highlight, if any remaining *)
          val (_, acc) =
            Util.loop (hi, Seq.length orderedHighlightCols) (currCol, acc)
              (fn ((currCol, acc), hi) =>
                 let
                   val sentry = Seq.nth orderedHighlightCols hi
                   val nextHighlightCol = sentryCol sentry
                   val emphasizer = sentryEmphasizer sentry
                 in
                   if currCol > nextHighlightCol then
                     (currCol, acc)
                   else
                     (* currCol <= nextHighlightCol *)
                     ( nextHighlightCol + 1
                     , Item.Stuff (emphasizer (spaces 1))
                       :: Item.Spaces (nextHighlightCol - currCol) :: acc
                     )
                 end)
        in
          acc
        end


      fun newlineWithEndDebugs endDebugs startDebugs acc =
        if List.null endDebugs then
          (startDebugs, acc)
        else
          let
            val orderedStarts =
              (* Mergesort.sort sentryCmp (Seq.fromList startDebugs) *)
              Seq.fromList
                (ListMergeSort.sort (Util.gtOfCmp sentryCmp) startDebugs)
            val orderedEnds =
              (* Mergesort.sort eentryCmp (Seq.fromList endDebugs) *)
              Seq.fromList
                (ListMergeSort.sort (Util.gtOfCmp eentryCmp) endDebugs)

            val _ = print
              ("newLineWithEndDebugs:\n" ^ "  starts: "
               ^ Seq.toString sentrytos orderedStarts ^ "\n" ^ "  ends: "
               ^ Seq.toString eentrytos orderedEnds ^ "\n")

            (* This is a bit cumbersome, but actually is fairly straightforward:
             * for each `(info, col)` in `EE`, output `info` at column `col`.
             *
             * There's some trickiness though, because multiple `(info, col)`
             * entries might overlap. For this, we check if each entry fits,
             * and if not, we add the entry to `didntFit`, and then process
             * `didntFit` on the next line, repeating until all entries have been
             * output.
             *
             * Update: and now there's more trickiness, because we need to filter
             * starts as we go to get decent output...
             *)
            fun loop (i, SS: sentry Seq.t) (j, EE: eentry Seq.t)
              (didntFitEE: eentry list)
              (removedSSCurrLine: sentry list, remainingSS: sentry list)
              (currCol: int) (accCurrLine: item list) (acc: item list) =
              if j >= Seq.length EE then
                if List.null didntFitEE then
                  let
                    val remainingSS' = Seq.toList (Seq.drop SS i) @ remainingSS
                  in
                    ( remainingSS'
                    , highlightActive accCurrLine acc
                        (removedSSCurrLine @ remainingSS')
                    )
                  end
                else
                  loop
                    (0, Seq.append (Seq.fromRevList remainingSS, Seq.drop SS i))
                    (0, Seq.fromRevList didntFitEE) [] (* didntFitEE *)
                    ([], []) (* (removedSSCurrLine, remainingSS) *)
                    0 (* currCol *) [] (* accCurrLine *)
                    (Item.Newline
                     ::
                     highlightActive accCurrLine acc
                       (Seq.toList (Seq.drop SS i) @ remainingSS
                        @ removedSSCurrLine))
              else
                let
                  val sentry = Seq.nth SS i
                  val eentry = Seq.nth EE j

                  val scol = sentryCol sentry
                  val ecol = eentryCol eentry
                  val info = sentryInfo sentry

                  val _ =
                    (* check invariant *)
                    if scol <= ecol then
                      ()
                    else
                      ( print
                          ("sentry " ^ sentrytos sentry ^ "\n" ^ "eentry "
                           ^ eentrytos eentry ^ "\n" ^ "i " ^ Int.toString i
                           ^ "\n" ^ "j " ^ Int.toString j ^ "\n" ^ "SS "
                           ^ Seq.toString sentrytos SS ^ "\n" ^ "EE "
                           ^ Seq.toString eentrytos EE ^ "\n")
                      ; raise Fail
                          "newlineWithEndDebugs.loop: invariant violated"
                      )
                in
                  if
                    scol < ecol
                    orelse not (matchingStartEndEntries (sentry, eentry))
                  then
                    loop (i + 1, SS) (j, EE) didntFitEE
                      (removedSSCurrLine, sentry :: remainingSS) currCol
                      accCurrLine acc
                  else if
                    ecol < currCol
                  then
                    loop (i + 1, SS) (j + 1, EE) (eentry :: didntFitEE)
                      (removedSSCurrLine, sentry :: remainingSS) currCol
                      accCurrLine acc
                  else
                    let
                      val numSpaces = ecol - currCol
                      val newCol = currCol + numSpaces + CustomString.size info
                    in
                      loop (i + 1, SS) (j + 1, EE) didntFitEE
                        (sentry :: removedSSCurrLine, remainingSS) newCol
                        (Item.Stuff info :: Item.Spaces numSpaces :: accCurrLine)
                        acc
                    end
                end

            val (remainingSS, acc) =
              loop (0, orderedStarts) (0, orderedEnds) [] ([], []) 0 []
                (Item.Newline :: acc)

            val acc = highlightActive [] (Item.Newline :: acc) remainingSS
          in
            (remainingSS, acc)
          end


      fun processItem (item, (accCurrLine, acc, endDebugs, startDebugs)) =
        case item of
          Item.EndDebug entry =>
            (accCurrLine, acc, entry :: endDebugs, startDebugs)
        | Item.StartDebug entry =>
            (accCurrLine, acc, endDebugs, entry :: startDebugs)
        | Item.Newline =>
            let
              val (remainingSS, acc) =
                newlineWithEndDebugs endDebugs startDebugs
                  (highlightActive accCurrLine acc startDebugs)
            in
              ([], Item.Newline :: acc, [], remainingSS)
            end
        | _ => (item :: accCurrLine, acc, endDebugs, startDebugs)


      val init = ([], [], [], [])
      val init = processItem
        (Item.StartDebug (StartMaxWidthHighlight {col = maxWidth}), init)
      val (accCurrLine, acc, endDebugs, startDebugs) =
        List.foldr processItem init
          (Item.EndDebug (EndMaxWidthHighlight {col = maxWidth}) :: items)
    in
      if List.null endDebugs then
        accCurrLine @ acc
      else
        #2 (newlineWithEndDebugs endDebugs startDebugs
          (highlightActive accCurrLine acc startDebugs))
    end


  (* ====================================================================== *)
  (* ====================================================================== *)
  (* ====================================================================== *)


  fun revAndStripTrailingWhitespace (items: item list) =
    let
      fun loopStrip acc items =
        case items of
          [] => acc
        | Item.Spaces _ :: items' => loopStrip acc items'
        | _ => loopKeep acc items

      and loopKeep acc items =
        case items of
          [] => acc
        | Item.Newline :: items' => loopStrip (Item.Newline :: acc) items'
        | x :: items' => loopKeep (x :: acc) items'
    in
      loopStrip [] items
    end


  exception DoPromote of tab


  fun addNewlines n d =
    if n = 0 then d else addNewlines (n - 1) (Concat (Newline, d))


  fun concatDocs ds =
    Seq.iterate concat empty ds


  fun tokenToDoc {tabWidth} currentTab tok =
    case tokenToPieces {tabWidth = tabWidth} tok of
      OnePiece s => Text s
    | ManyPieces pieces =>
        let
          val numPieces = Seq.length pieces
          val tab = Tab.new
            { parent = currentTab
            , style = Tab.Style.combine (Tab.Style.inplace, Tab.Style.rigid)
            }
          val doc =
            (* a bit of a hack here: we concatenate a space on the end of
             * each piece (except last), which guarantees that blank lines
             * within the comment are preserved.
             *)
            Seq.iterate concat empty
              (Seq.map (fn x => at tab (concat (Text x, space)))
                 (Seq.take pieces (numPieces - 1)))
          val doc = concat (doc, at tab (Text (Seq.nth pieces (numPieces - 1))))
          val doc = NewTab {tab = tab, gen = Promise.new (fn () => doc)}
        in
          doc
        end


  fun tokenToDocWithBlankLines {tabWidth} currentTab tok =
    let
      val doc = tokenToDoc {tabWidth = tabWidth} currentTab tok
      val numBlanks = Token.desiredBlankLinesBefore tok
    in
      addNewlines numBlanks doc
    end


  fun pretty {ribbonFrac, maxWidth, indentWidth, tabWidth, debug} doc =
    let
      val t0 = Time.now ()
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")

      val ribbonWidth = Int.max (0, Int.min (maxWidth, Real.round
        (ribbonFrac * Real.fromInt maxWidth)))

      val newline = CustomString.fromString "\n"

      datatype activation_state = Flattened | Activated of int option
      datatype state = Usable of activation_state | Completed

      val tabstate = ref TabDict.empty

      fun getTabState t =
        TabDict.lookup (!tabstate) t

      fun setTabState t x =
        tabstate := TabDict.insert (!tabstate) (t, x)

      val _ = setTabState Tab.root (Usable (Activated (SOME 0)))

      fun isActivated t =
        case getTabState t of
          Usable (Activated _) => true
        | Usable Flattened => false
        | _ => raise Fail "PrettyTabbedDoc.pretty.isActivated: bad tab"

      (* tab -> hit first break? *)
      type debug_state = bool TabDict.t

      (* debug state, current tab, current 'at's, delayed comments, line start, current col, lastItemIsSpacey, accumulator *)
      datatype layout_state =
        LS of
          debug_state
          * tab
          * TabSet.t
          * Token.t Seq.t
          * int
          * int
          * bool
          * (item list)

      fun dbgInsert tab
        (LS (dbgState, ct, cats, coms, s, c, sp, a) : layout_state) :
        layout_state =
        if not debug then
          LS (dbgState, ct, cats, coms, s, c, sp, a)
        else
          LS (TabDict.insert dbgState (tab, false), ct, cats, coms, s, c, sp, a)

      fun dbgBreak tab
        (LS (dbgState, ct, cats, coms, s, c, sp, a) : layout_state) :
        layout_state =
        if not debug then
          LS (dbgState, ct, cats, coms, s, c, sp, a)
        else if TabDict.lookup dbgState tab then
          LS (dbgState, ct, cats, coms, s, c, sp, a)
        else
          LS
            ( TabDict.insert dbgState (tab, true)
            , ct
            , cats
            , coms
            , s
            , c
            , sp
            , Item.StartDebug (StartTabHighlight {tab = tab, col = c}) :: a
            )

      fun isPromotable' t =
        case getTabState t of
          Usable Flattened => true
        | Usable (Activated NONE) => true
        | Usable (Activated (SOME ti)) =>
            (case Tab.parent t of
               NONE => false
             | SOME p =>
                 case getTabState p of
                   Usable (Activated (SOME pi)) =>
                     ti > pi + Int.max (indentWidth, Tab.minIndent t)
                 | _ =>
                     raise Fail
                       "PrettyTabbedDoc.pretty.isPromotable: bad parent tab")
        | _ => raise Fail "PrettyTabbedDoc.pretty.isPromotable: bad tab"


      fun isPromotable t =
        let
          val result = isPromotable' t
        in
          (* if not debug then () else
          print ("PrettyTabbedDoc.debug: isPromotable " ^ Tab.infoString t ^ " = " ^ (if result then "true" else "false") ^ "\n"); *)
          result
        end


      fun oldestPromotableParent t =
        if not (isPromotable t) then
          NONE
        else
          case Tab.parent t of
            SOME p =>
              if not (isPromotable p) then SOME t else oldestPromotableParent p
          | NONE => SOME t


      fun oldestInactiveParent t =
        if isActivated t then
          NONE
        else
          case Tab.parent t of
            SOME p => if isActivated p then SOME t else oldestInactiveParent p
          | NONE => SOME t


      (* Below, the `check` function is used to check for layout violations.
       * If any layout constraints are violated, it tries to promote a tab.
       *
       * The promotion strategy implemented here is simple: we always promote
       * the outermost promotable tab. This strategy prefers full promotion of
       * a tab before activating any of its children, which generally looks
       * pretty good.
       *
       * However, there is room for improvement.
       *
       * Consider this document with tabs labeled 0..3:
       *
       *   Functor (struct val x = 5 val y = 42 end)
       *   |       ||      |         |          |
       *   0       1|      3         3          2
       *            2
       *
       * Then under the current strategy, we could have the output
       * on the left, but not on the right:
       *
       *     possible layout   |  impossible layout
       *   --------------------+-------------------------
       *     Functor           |  Functor (struct
       *       (struct         |             val x = 5
       *          val x = 5    |             val y = 42
       *          val y = 42   |           end)
       *        end)           |
       *
       * The left layout is generated by the promotions [0,0,1,1,2,2,3,3].
       * (Notice in this sequence, each tab is repeated twice: the first
       * promotion activates the tab, and the second promotion relocates
       * the tab by placing it on a new line and indenting)
       *
       * If we instead had an alternative promotion strategy which allowed
       * for fully promoting a child before its parent, then it would be
       * possible to see the layout on the right. The promotion sequence
       * would need to be [0,0,1,2,3,3].
       *
       * UPDATE: tab styles (newly added) allow for some control over this.
       *)
      fun check (state as LS (_, ct, _, _, lnStart, col, _, _)) =
        let
          val widthOkay = col <= maxWidth
          val ribbonOkay = (col - lnStart) <= ribbonWidth
          val okay = widthOkay andalso ribbonOkay
        (* val _ =
          if not debug orelse okay then ()
          else if not widthOkay then
            print ("PrettyTabbedDoc.debug: width violated: ct=" ^ Tab.infoString ct ^ " lnStart=" ^ Int.toString lnStart ^ " col=" ^ Int.toString col ^ "\n")
          else if not ribbonOkay then
            print ("PrettyTabbedDoc.debug: ribbon violated: ct=" ^ Tab.infoString ct ^ " lnStart=" ^ Int.toString lnStart ^ " col=" ^ Int.toString col ^ "\n")
          else
            print ("PrettyTabbedDoc.debug: unknown violation?? ct=" ^ Tab.infoString ct ^ " lnStart=" ^ Int.toString lnStart ^ " col=" ^ Int.toString col ^ "\n") *)
        in
          if okay then
            state
          else
            case oldestPromotableParent ct of
            (* TODO: FIXME: there's a bug here. Even if the current tab (ct)
             * doesn't have a promotable parent, there might be another
             * promotable tab on the same line.
             *
             * For example: tabs s and t occupy the same line; tab s is
             * fully promoted; tab t is inactive because it fits within the
             * max width. After completing tab t, we return to tab s, and then
             * get a width violation. However, tab s (the current tab) has
             * no promotable parent.
             *
             *   sssssssssstttttttttsss|s
             *   ^         ^           ^
             *   tab s:    tab t:      max width
             *   fully     inactive
             *   promoted
             *
             * The fix in the above example is to promote tab t. So, perhaps
             * we need to keep track of a set of promotable tabs on the
             * current line and then choose one to promote (?)
             *)
              SOME p => raise DoPromote p
            | NONE => state
        end


      fun parentTabCol tab =
        case Tab.parent tab of
          NONE => raise Fail "PrettyTabbedDoc.pretty.parentTabCol: no parent"
        | SOME p =>
            case getTabState p of
              Usable (Activated (SOME i)) => i
            | _ => raise Fail "PrettyTabbedDoc.pretty.parentTabCol: bad tab"


      fun ensureAt tab state =
        let
          val LS (dbgState, _, cats, coms, lnStart, col, sp, acc) = state
          val alreadyAtTab = TabSet.contains cats tab

          fun goto i =
            if alreadyAtTab then
              dbgBreak tab (LS (dbgState, tab, cats, coms, lnStart, i, sp, acc))
            else if Tab.isInplace tab andalso col <= i then
              dbgBreak tab (check (LS
                ( dbgState
                , tab
                , if i = col then TabSet.insert cats tab
                  else TabSet.singleton tab
                , coms
                , lnStart
                , i
                , i <> col orelse sp
                , if i = col then acc else Item.Spaces (i - col) :: acc
                )))
            (* else if i = col andalso Tab.isInplace tab then
              dbgBreak tab (LS
                (dbgState, tab, TabSet.insert cats tab, lnStart, i, sp, acc)) *)
            else if i < col then
              dbgBreak tab (check (LS
                ( dbgState
                , tab
                , TabSet.singleton tab
                , coms
                , i
                , i
                , true
                , Item.Spaces i :: Item.Newline :: acc
                )))
            else if isPromotable tab then
              (* force this tab to promote if possible, which should move
               * it onto a new line and indent. *)
              raise DoPromote tab
            else if lnStart < i then

              (* SAM_NOTE: TODO: This case might be unnecessary... we can use
               * tab styles (inplace vs indented) to resolve this issue. Inplace
               * can be allowed to advance, and indented require a fresh line.
               * This would simplify the logic above, too; the case where
               *   i = col andalso Tab.isInplace tab
               * would just be a special case of advancing on the current line.
               *)

              (* This avoids advancing the current line to meet the tab,
               * if possible, which IMO results in strange layouts. *)
              dbgBreak tab (check (LS
                ( dbgState
                , tab
                , if i = col then TabSet.insert cats tab
                  else TabSet.singleton tab
                , coms
                , i
                , i
                , true
                , Item.Spaces i :: Item.Newline :: acc
                )))
            else
              (* Fall back on advancing the current line to meet the tab,
               * which is a little strange, but better than nothing. *)
              dbgBreak tab (check (LS
                ( dbgState
                , tab
                , if i = col then TabSet.insert cats tab
                  else TabSet.singleton tab
                , coms
                , lnStart
                , i
                , i <> col orelse sp
                , Item.Spaces (i - col) :: acc
                )))

          val state' =
            case getTabState tab of
              Usable Flattened =>
                if Tab.isRigid tab then
                  raise DoPromote (valOf (oldestPromotableParent tab))
                else
                  LS (dbgState, tab, cats, coms, lnStart, col, sp, acc)

            | Usable (Activated (SOME i)) => goto i

            | Usable (Activated NONE) =>
                if Tab.isInplace tab then
                  if col < parentTabCol tab then
                    ( setTabState tab (Usable (Activated
                        (SOME (parentTabCol tab))))
                    ; goto (parentTabCol tab)
                    )
                  else
                    let
                      (* never let a tab begin at a place that needs a space *)
                      val desired = if sp then col else col + 1
                    in
                      ( setTabState tab (Usable (Activated (SOME desired)))
                      ; goto desired
                      )
                    end
                else
                  let
                    val i =
                      parentTabCol tab
                      +
                      Int.min
                        ( Int.max (indentWidth, Tab.minIndent tab)
                        , Tab.maxIndent tab
                        )
                  in
                    setTabState tab (Usable (Activated (SOME i)));
                    goto i
                  end

            | _ => raise Fail "PrettyTabbedDoc.pretty.Goto: bad tab"
        in
          state'
        end

      val tokenToDoc = tokenToDoc {tabWidth = tabWidth}

      val tokenToDocWithBlankLines =
        tokenToDocWithBlankLines {tabWidth = tabWidth}


      (* This is a little tricky, but the idea is: try to lay out the doc,
       * and keep track of whether or not there exists an ancestor tab that
       * could be promoted (ap). If we ever violate either the width or
       * ribbon condition, then promote the oldest ancestor tab and try again.
       *
       * Promotion is implemented by throwing an exception (DoPromote), which
       * is caught by the oldest ancestor.
       *)
      fun layout vars (state: layout_state) doc : layout_state =
        case doc of
          Empty => state

        | NoSpace =>
            let val LS (dbgState, ct, cats, coms, lnStart, col, _, acc) = state
            in LS (dbgState, ct, cats, coms, lnStart, col, true, acc)
            end

        | Space =>
            let
              val LS (dbgState, ct, _, coms, lnStart, col, _, acc) = state
              val item = Item.Spaces 1
            in
              check (LS
                ( dbgState
                , ct
                (* an item has been placed, so now we are no longer at a tab *)
                , TabSet.empty
                , coms
                , lnStart
                , col + Item.width item
                , true
                , item :: acc
                ))
            end

        | Text s =>
            let
              val LS (dbgState, ct, _, coms, lnStart, col, sp, acc) = state
              val item = Item.Stuff s
              (* TODO: bug here? this can insert a space immediately inside
               * 'at', causing a token to become displaced. I'm not sure yet if
               * this should be considered a bug. It seems to be fixable in the
               * document structure by inserting tabs in the right place... *)
              val (col, acc) =
                if sp then (col + Item.width item, item :: acc)
                else (col + Item.width item + 1, item :: Item.Spaces 1 :: acc)
            in
              check (LS
                ( dbgState
                , ct
                (* an item has been placed, so now we are no longer at a tab *)
                , TabSet.empty
                , coms
                , lnStart
                , col
                , false
                , acc
                ))
            end

        | Token t => layoutToken vars state t

        | Newline =>
            let
              val LS (dbgState, ct, cats, coms, _, col, _, acc) = state
            in
              check (LS
                ( dbgState
                , ct
                , cats
                , coms
                , col
                , col
                , true
                , Item.Spaces col :: Item.Newline :: acc
                ))
            end

        | Concat (doc1, doc2) => layout vars (layout vars state doc1) doc2

        | LetDoc {var, doc, inn} =>
            let
              fun delayedLayout state =
                layout vars state doc
              val vars = VarDict.insert vars (var, delayedLayout)
            in
              layout vars state inn
            end

        | Var v =>
            let val delayedLayout = VarDict.lookup vars v
            in delayedLayout state
            end

        | At (tab, doc') =>
            let
              val origDoc = doc
              val doc = doc'
              val LS (_, origCurrentTab, _, _, _, _, _, _) = state

              val state = ensureAt tab state
              val LS (dbgState, ct, cats, coms, lnStart, col, sp, acc) = state

              val (state, doc) =
                if
                  not
                    (Tab.allowsComments tab andalso Seq.length coms > 0
                     andalso TabSet.contains cats tab)
                then
                  (state, doc)
                else
                  let
                    val comsDoc = concatDocs
                      (Seq.map (at tab o tokenToDocWithBlankLines tab) coms)
                    val doc = concat (comsDoc, origDoc)

                    val state = LS
                      (dbgState, ct, cats, Seq.empty (), lnStart, col, sp, acc)
                  in
                    (state, doc)
                  end

              val LS (dbgState, _, cats, coms, lnStart, col, sp, acc) =
                layout vars state doc
            in
              LS (dbgState, origCurrentTab, cats, coms, lnStart, col, sp, acc)
            end

        | Cond {tab, inactive, active} =>
            let in
              case getTabState tab of
                Usable (Activated _) => layout vars state active
              | Usable Flattened => layout vars state inactive
              | _ => raise Fail "PrettyTabbedDoc.pretty.layout.Cond: bad tab"
            end

        | NewTab {tab, gen} =>
            let
              val doc = Promise.get gen

              fun tryPromote () =
                (* try to activate first *)
                if not (isActivated tab) then
                  setTabState tab (Usable (Activated NONE))
                else (* if activated, try to relocate *)
                  case getTabState tab of
                    Usable (Activated NONE) =>
                      let
                        val desired =
                          parentTabCol tab
                          +
                          Int.min
                            ( Int.max (indentWidth, Tab.minIndent tab)
                            , Tab.maxIndent tab
                            )
                      in
                        setTabState tab (Usable (Activated (SOME desired)))
                      end
                  | Usable (Activated (SOME i)) =>
                      let
                        val desired = Int.min
                          ( i
                          , parentTabCol tab
                            +
                            Int.min
                              ( Int.max (indentWidth, Tab.minIndent tab)
                              , Tab.maxIndent tab
                              )
                          )
                      in
                        setTabState tab (Usable (Activated (SOME desired)))
                      end
                  | _ =>
                      raise Fail
                        "PrettyTabbedDoc.pretty.layout.NewTab.tryPromote: bad tab"

              fun doit () =
                let in
                  ( ()
                  ; (layout vars (dbgInsert tab state) doc
                     handle DoPromote p =>
                       if not (Tab.eq (p, tab)) then
                         raise DoPromote p
                       else
                         let
                         (* val _ =
                           if not debug then () else
                           print ("PrettyTabbedDoc.debug: promoting " ^ Tab.infoString tab ^ "\n") *)
                         in tryPromote (); doit ()
                         end)
                  )
                end

              val _ = setTabState tab (Usable Flattened)

              val
                LS (dbgState, _, cats, coms, lnStart, col, sp, acc) :
                  layout_state = doit ()

              val acc =
                if not debug then
                  acc
                else
                  case getTabState tab of
                    Usable Flattened => acc
                  | Usable (Activated NONE) => acc
                  | Usable (Activated (SOME i)) =>
                      if TabDict.lookup dbgState tab then
                        Item.EndDebug (EndTabHighlight {tab = tab, col = i})
                        :: acc
                      else
                        acc
                  | _ => raise Fail "PrettyTabbedDoc.debug: error..."
            in
              (* if not debug then () else
              print ("PrettyTabbedDoc.debug: finishing " ^ Tab.infoString tab ^ "\n"); *)

              setTabState tab Completed;

              LS
                ( dbgState
                , valOf (Tab.parent tab)
                , TabSet.remove cats tab
                , coms
                , lnStart
                , col
                , sp
                , acc
                )
            end

      and layoutToken vars state t =
        let
          val LS (dbgState, ct, cats, coms, lnStart, col, sp, acc) = state

          (* NOTE: Token.splitComments{Before,After} defined by the module
           * argument Token, which is an extension of src/lex/Token.
           * See e.g. src/prettier-print/TabbedStringDoc for an instantiation
           * of PrettyTabbedDoc. It is important that splitComments{Before,After}
           * together cover all comments between a pair of normal tokens. *)
          val csBefore = coms
          val (csAfter, nextComs) = Token.splitCommentsAfterAndBeforeNext t

          val state = LS (dbgState, ct, cats, nextComs, lnStart, col, sp, acc)
        in
          if Seq.length csBefore + Seq.length csAfter = 0 then
            if TabSet.size cats = 0 then layout vars state (tokenToDoc ct t)
            else layout vars state (tokenToDocWithBlankLines ct t)
          else if TabSet.size cats = 0 then
            layout vars state (concatDocs (Seq.append3
              ( Seq.map (tokenToDoc ct) csBefore
              , Seq.singleton (tokenToDoc ct t)
              , Seq.map (tokenToDoc ct) csAfter
              )))
          else
            let
              val tab = Tab.new
                { parent = ct
                , style = Tab.Style.combine (Tab.Style.inplace, Tab.Style.rigid)
                }

              val doc =
                concat
                  ( concatDocs
                      (Seq.map (at tab)
                         (Seq.append
                            ( Seq.map (tokenToDocWithBlankLines tab) csBefore
                            , Seq.singleton (tokenToDocWithBlankLines tab t)
                            )))
                  , concatDocs (Seq.map (tokenToDoc tab) csAfter)
                  )

              val doc = NewTab {tab = tab, gen = Promise.new (fn () => doc)}
            in
              layout vars state doc
            end
        end


      val initComments =
        case firstToken doc of
          NONE => Seq.empty ()
        | SOME t => Token.splitCommentsBefore t


      val t1 = Time.now ()
      val _ = dbgprintln ("pre-layout: " ^ Time.fmt 3 (Time.- (t1, t0)) ^ "s")

      val init = LS
        ( TabDict.empty
        , root
        , TabSet.singleton root
        , initComments
        , 0
        , 0
        , true
        , []
        )
      val init = dbgBreak Tab.root (dbgInsert Tab.root init)
      val LS (_, _, _, _, _, _, _, items) = layout VarDict.empty init doc
      val items =
        if not debug then items
        else Item.EndDebug (EndTabHighlight {tab = Tab.root, col = 0}) :: items

      val t2 = Time.now ()
      val _ = dbgprintln ("layout: " ^ Time.fmt 3 (Time.- (t2, t1)) ^ "s")

      val items = if not debug then items else implementDebugs maxWidth items

      val items = revAndStripTrailingWhitespace items

      fun itemToString x =
        case x of
          Item.Newline => newline
        | Item.Spaces n => spaces n
        | Item.Stuff s => s
        | _ => raise Fail "impossible"

      val result = CustomString.concat (List.map itemToString items)

      val t3 = Time.now ()
      val _ = dbgprintln ("post-layout: " ^ Time.fmt 3 (Time.- (t3, t2)) ^ "s")
    in
      result
    end


  fun prettyJustComments (params as {tabWidth, ...}) cs =
    let
      val doc = concatDocs
        (Seq.map (at root o tokenToDocWithBlankLines {tabWidth = tabWidth} root)
           cs)
    in
      pretty params doc
    end

end
