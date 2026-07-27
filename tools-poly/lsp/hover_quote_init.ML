(* tools-poly/lsp/hover_quote_init.ML

   Installs the LSP-side HOL-quotation hover callback.  Loaded by
   tools-poly/hol.ML's LSP branch AFTER HOL is initialized, via
   QUse.use, so all HOL parser modules (TermParse, Preterm, Pretype,
   locn) are in scope.

   The callback parses a captured quotation using HOL's normal
   Parse/Preterm pipeline (through typecheck_phase1 and
   overloading_resolution), keeping the resolved Preterm rather than
   lifting to Term so per-leaf Locn is preserved.  It walks the tree
   to find the innermost Var/Const leaf whose Locn covers the hover
   offset and renders it as markdown.  Bound-var scope is tracked so
   free vs bound is distinguished.

   Location tracking: the callback prepends `(*#loc row col*)` to the
   quotation body (with row/col in file coordinates) so all Locn
   values emerging from the parser are file-absolute LocAs; converting
   them back to byte offsets uses LSPExtension.fromLineCol. *)

local
  open errormonad Preterm

  fun parse_quote body = let
    val g = Parse.term_grammar ()
    val tyg = Parse.type_grammar ()
    val a = TermParse.absyn g tyg [QUOTE body]
    val M =
      TermParse.absyn_to_preterm g a >- (fn pt =>
      typecheck_phase1 NONE pt >>
      overloading_resolution pt >- (fn (pt', _) => return pt'))
    in
      case M Pretype.Env.empty of
        Some (env, pt) => SOME (env, pt)
      | Error _ => NONE
    end handle _ => NONE

  fun locn_covers lines target locn =
    case locn of
      locn.Loc (locn.LocA (l1, c1), locn.LocA (l2, c2)) =>
        let val s = LSPExtension.fromLineCol lines (l1, c1)
            val e = LSPExtension.fromLineCol lines (l2, c2)
        in s <= target andalso target <= e end
    | _ => false

  fun locn_range (locn.Loc (locn.LocA (l1, c1), locn.LocA (l2, c2))) =
      SOME ((l1, c1), (l2, c2 + 1))
    | locn_range _ = NONE

  datatype hover_leaf =
      HLConst of {Name: string, Thy: string,
                  Ty: Pretype.pretype, Locn: locn.locn}
    | HLBound of {Name: string, Ty: Pretype.pretype, Locn: locn.locn}
    | HLFree  of {Name: string, Ty: Pretype.pretype, Locn: locn.locn}

  fun leaf_locn (HLConst {Locn, ...}) = Locn
    | leaf_locn (HLBound {Locn, ...}) = Locn
    | leaf_locn (HLFree  {Locn, ...}) = Locn

  (* Byte-length of a Locn's file range (LocA start ↔ LocA end).
     Non-LocA Locns are treated as huge so they're never preferred. *)
  fun locn_size lines (locn.Loc (locn.LocA (l1, c1), locn.LocA (l2, c2))) =
        LSPExtension.fromLineCol lines (l2, c2) -
        LSPExtension.fromLineCol lines (l1, c1)
    | locn_size _ _ = 100000000

  (* Prefer the leaf with the smaller Locn — i.e., the more specific
     identifier under the cursor.  With Absyn-level Locns pointing at
     the operator token (parse_term.sml giving each operator VAR its
     own token's Locn instead of the LHS's start), operator and
     operand Locns are disjoint in the common case, so `<` on size
     usually decides.  On a size tie, prefer the Rand branch (the
     inner sub-application). *)
  fun better lines a NONE = a
    | better lines NONE b = b
    | better lines (SOME la) (SOME lb) =
        let val sa = locn_size lines (leaf_locn la)
            val sb = locn_size lines (leaf_locn lb)
        in
          if sa <= sb then
            if sa = sb then SOME lb else SOME la
          else SOME lb
        end

  fun find_leaf pt target lines = let
    fun cov l = locn_covers lines target l
    fun bound name bvs = List.exists (fn n => n = name) bvs
    fun go bvs pt = case pt of
        Var {Name, Ty, Locn} =>
          if cov Locn then
            SOME (if bound Name bvs
                  then HLBound {Name = Name, Ty = Ty, Locn = Locn}
                  else HLFree  {Name = Name, Ty = Ty, Locn = Locn})
          else NONE
      | Const {Name, Thy, Ty, Locn} =>
          if cov Locn
          then SOME (HLConst {Name = Name, Thy = Thy, Ty = Ty, Locn = Locn})
          else NONE
      | Comb {Rator, Rand, Locn = combLocn} => let
          (* Descend into both children first.  If neither leaf covers
             the cursor, the cursor may be on an infix-operator symbol
             whose Const has a Locn borrowed from its operands rather
             than the operator's own source position.  Fall back to
             checking whether the Comb's own Locn covers the cursor
             and, if so, surface the operator Const. *)
          val descend = better lines (go bvs Rator) (go bvs Rand)
        in
          case descend of
            SOME _ => descend
          | NONE =>
              if cov combLocn then
                case Rator of
                  Const {Name, Thy, Ty, Locn = _} =>
                    SOME (HLConst {Name = Name, Thy = Thy,
                                   Ty = Ty, Locn = combLocn})
                | Comb {Rator = Const {Name, Thy, Ty, Locn = _}, ...} =>
                    SOME (HLConst {Name = Name, Thy = Thy,
                                   Ty = Ty, Locn = combLocn})
                | _ => NONE
              else NONE
        end
      | Abs {Bvar, Body, ...} => let
          (* Bvar may be wrapped in Constrained (e.g. `!n:num. …`
             gives Abs{Bvar = Constrained{Ptm = Var …, Ty = num},
             …}).  Peel through to find the underlying Var so we
             add its name to the scope and, if the cursor is on the
             binder itself, report HLBound. *)
          fun peel (Constrained {Ptm, ...}) = peel Ptm
            | peel p = p
        in case peel Bvar of
            Var {Name, Ty, Locn} =>
              if cov Locn then
                SOME (HLBound {Name = Name, Ty = Ty, Locn = Locn})
              else go (Name :: bvs) Body
          | _ => go bvs Body
        end
      | Constrained {Ptm, ...} => go bvs Ptm
      | Pattern {Ptm, ...} => go bvs Ptm
      | Antiq _ => NONE
      | Overloaded _ => NONE
    in go [] pt end

  fun render_type env pty =
    let val cleaned = Pretype.apply_subst env pty
    in Parse.type_to_string (Pretype.toType cleaned) end
    handle _ => "?"

  fun format_leaf env leaf =
    let
      val (name, tystr, tail) = case leaf of
          HLConst {Name, Thy, Ty, ...} =>
            (Name, render_type env Ty, "Theory `" ^ Thy ^ "`")
        | HLBound {Name, Ty, ...} =>
            (Name, render_type env Ty, "*bound variable*")
        | HLFree  {Name, Ty, ...} =>
            (Name, render_type env Ty, "*free variable*")
    in
      (* Parse.type_to_string already prefixes ``:`` (HOL type-
         annotation convention), so we don't add another one. *)
      "```\n" ^ name ^ " " ^ tystr ^ "\n```\n\n" ^ tail
    end
in

(* Strip leading/trailing HOL quotation delimiters (``‘`` = E2 80 98
   and ``’`` = E2 80 99) plus surrounding whitespace.  Returns
   (leadingBytes, strippedBody).  We must match the FULL 3-byte
   sequence — checking only the leading 0xE2 would eat characters
   like ``∀`` (E2 88 80), ``∧`` (E2 88 A7), ``⇒`` (E2 87 92). *)
fun stripDelims s = let
  val n = String.size s
  fun byteAt i = Char.ord (String.sub (s, i))
  fun isQuoteAt i =
    i + 2 < n andalso byteAt i = 226 andalso byteAt (i + 1) = 128 andalso
    let val b = byteAt (i + 2) in b = 152 orelse b = 153 end
  fun isQuoteEnd i =  (* three-byte sequence ending exactly at index i *)
    i >= 3 andalso byteAt (i - 3) = 226 andalso byteAt (i - 2) = 128 andalso
    let val b = byteAt (i - 1) in b = 152 orelse b = 153 end
  fun startOfBody i =
    if i >= n then i
    else if isQuoteAt i then startOfBody (i + 3)
    else if Char.isSpace (String.sub (s, i)) then startOfBody (i + 1)
    else i
  fun endOfBody i =
    if i <= 0 then 0
    else if isQuoteEnd i then endOfBody (i - 3)
    else if Char.isSpace (String.sub (s, i - 1)) then endOfBody (i - 1)
    else i
  val a = startOfBody 0
  val b = endOfBody n
  in (a, String.substring (s, a, Int.max (0, b - a))) end

(* Find byte ranges `[…:]` in a body — HOL's DefinitionLabel syntax.
   Returns (label_start, label_end_exclusive) pairs.  Labels are
   only produced by Inductive/CoInductive expansions; other quote
   bodies have none and this returns []. *)
fun labelRanges body = let
  val n = String.size body
  fun scan i acc =
    if i >= n then rev acc
    else if String.sub (body, i) = #"[" then
      (case matchLabel (i + 1) of
         NONE => scan (i + 1) acc
       | SOME e => scan e ((i, e) :: acc))
    else scan (i + 1) acc
  and matchLabel j =  (* find `:]` at or after j, returning j' AFTER `:]` *)
    if j + 1 >= n then NONE
    else let val c = String.sub (body, j)
    in if c = #":" andalso String.sub (body, j + 1) = #"]" then SOME (j + 2)
       else if c = #"[" then
         (* Allow one nested `[…]` (e.g. `[nm[attrs]:]`) *)
         (case findClose (j + 1) of
            NONE => NONE
          | SOME k => matchLabel (k + 1))
       else if c = #"]" orelse c = #"\n" then NONE
       else matchLabel (j + 1)
    end
  and findClose j =
    if j >= n then NONE
    else let val c = String.sub (body, j)
    in if c = #"]" then SOME j
       else if c = #"\n" then NONE
       else findClose (j + 1)
    end
  in scan 0 [] end

(* For a body possibly containing DefinitionLabels, find the region
   (label-free substring) that contains `t` — a body-relative byte
   offset.  Returns (region_start_in_body, region_string).  If the
   cursor lands ON a label itself, returns an empty region. *)
fun findRegion body t = let
  val n = String.size body
  fun step prevEnd [] = (prevEnd, n)
    | step prevEnd ((ls, le) :: rest) =
      if ls > t then (prevEnd, ls)
      else if le > t then (le, le)  (* cursor inside a label *)
      else step le rest
  val (a, b) = step 0 (labelRanges body)
  in (a, String.substring (body, a, Int.max (0, b - a))) end

val () = LSPExtension.hoverQuotation :=
  (fn ({lines, ...} : LSPExtension.hover_context,
       {quote, quoteStart, target}) =>
    let
      val (leadBytes, body) = stripDelims quote
      val bodyStart = quoteStart + leadBytes
      (* Split on `[…:]` labels (Inductive rules) so we parse just the
         label-free region containing the cursor; other bodies have no
         labels and get parsed whole. *)
      val (regionOffset, region) = findRegion body (target - bodyStart)
      val regionStart = bodyStart + regionOffset
      val (startLine, startCol) = LSPExtension.getLineCol lines regionStart
      val pragma =
        "(*#loc " ^ Int.toString (startLine + 1) ^ " " ^
        Int.toString (startCol + 1) ^ "*)"
      val src = pragma ^ region
    in
      case parse_quote src of
        NONE => []
      | SOME (env, pt) =>
        case find_leaf pt target lines of
          NONE => []
        | SOME leaf =>
            [{markdown = format_leaf env leaf,
              range = locn_range (leaf_locn leaf)}]
    end handle _ => [])

end;
