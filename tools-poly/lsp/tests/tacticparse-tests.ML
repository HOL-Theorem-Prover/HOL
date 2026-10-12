(* TacticParse and ProofStepPlan, driven by `bin/hol'.
 *
 * `poly-init2' compiles these structures into the executable rather than
 * into sigobj, so a selftest.exe built by HOLMOSMLC cannot link them and
 * these tests cannot live in `src/parse/selftest.sml' where they started.
 * Running them here costs nothing extra: this directory already starts a
 * `bin/hol' for `load-init-files.ML'.
 *
 * TacticParse's interactive consumers are the LSP's `tactic_steps',
 * `tactic_walker' and `goal_state_init'; ProofStepPlan is the adjacent
 * source-oriented lowering layer.  Their tests therefore run together.
 *)
val () = Meta.load "testutils"
open testutils
(* Remember failures rather than exiting on the first, so one run
   reports them all -- the same arrangement `src/parse/selftest.sml'
   uses. *)
val failcount = ref 0
val () = diemode := Remember failcount

(* ----------------------------------------------------------------------
    TacticParse

    Its only consumers are the LSP's `tactic_steps`, `tactic_walker` and
    `goal_state_init`, none of which a build compiles, so a change to the
    shapes below is invisible until a language server next starts.  These
    are the properties those three rely on.
   ---------------------------------------------------------------------- *)

local
  open TacticParse
  (* The same route the LSP takes: wrap the tactic in a theorem so the
     SML parser will accept it, then shift the spans back. *)
  val wrapPrefix = "Theorem selftest_wrap: T\nProof\n"
  fun fragsOf tacText = let
    val src = wrapPrefix ^ tacText ^ "\nQED\n"
    val consumed = ref false
    fun read _ = if !consumed then "" else (consumed := true; src)
    fun err _ _ _ = ()
    val {parseDec, ...} =
      HOLSourceParser.parseSML "tacticparse_selftest" read err
                               HOLSourceParser.initialScope
    val d = String.size wrapPrefix
  in
    case parseDec () of
      SOME (HOLSourceAST.HOLTheoremDecl {tac, ...}) =>
        SOME (linearize (fn _ => false)
                (mapTacExpr {start = fn _ => fn (s, e) => (s - d, e - d),
                             stop = fn _ => fn x => x,
                             repair = fn _ => fn _ => ()}
                   (parseTacticBlock tac)))
    | _ => NONE
  end
  fun textAt tacText (s, e) = String.substring (tacText, s, e - s)
in

val _ = tprint "TacticParse: `>-' linearizes to a Then1 bracket"
val _ =
    let val txt = "rw [] >- metis_tac [] >> simp []"
    in
      case fragsOf txt of
        NONE => die "did not parse"
      | SOME frags =>
        let
          fun then1s [] = []
            | then1s (FBracket (FOpenThen1 _, inner, FClose, te) :: r) =
                (inner, te) :: then1s r
            | then1s (FGroup (_, inner) :: r) = then1s inner @ then1s r
            | then1s (_ :: r) = then1s r
        in
          case then1s frags of
            [(inner, te)] =>
              (* The walker takes a `>-'s extent from its body because
                 the wrapper carries no span of its own.  If that ever
                 changes, `bracketEndByte' silently starts measuring
                 something else. *)
              if isSome (topSpan te) then
                die "LThen1 grew a span of its own"
              else (case inner of
                      [FAtom a] =>
                        if textAt txt (valOf (topSpan a)) = "metis_tac []"
                        then OK()
                        else die ("branch body is " ^
                                  textAt txt (valOf (topSpan a)))
                    | _ => die "branch body is not one atom")
          | l => die (Int.toString (length l) ^ " Then1 brackets, want 1")
        end
    end

val _ = tprint "TacticParse: atom spans point at their own text"
val _ =
    let val txt = "strip_tac >> conj_tac >> simp []"
    in
      case fragsOf txt of
        NONE => die "did not parse"
      | SOME frags =>
        let
          fun atoms [] = []
            | atoms (FAtom a :: r) = (case topSpan a of
                                        SOME sp => textAt txt sp :: atoms r
                                      | NONE => atoms r)
            | atoms (FGroup (_, inner) :: r) = atoms inner @ atoms r
            | atoms (FBracket (_, inner, _, _) :: r) = atoms inner @ atoms r
            | atoms (_ :: r) = atoms r
          val got = atoms frags
        in
          if got = ["strip_tac", "conj_tac", "simp []"] then OK()
          else die (String.concatWith " | " got)
        end
    end

val _ = tprint "TacticParse: a `>-' never carries its own span"
val _ =
    let
      (* True of both forms, which is why the walker takes a branch's
         extent from its body: for `>- (t)' the parens' extent is the
         body group's, not the wrapper's.  A wrapper that grew a span
         would silently change what `bracketEndByte' measures. *)
      fun then1Body txt =
          case fragsOf txt of
            NONE => NONE
          | SOME frags =>
            let
              fun go [] = NONE
                | go (FBracket (FOpenThen1 _, inner, _, te) :: _) =
                    SOME (te, inner)
                | go (FGroup (_, inner) :: r) =
                    (case go inner of NONE => go r | x => x)
                | go (_ :: r) = go r
            in go frags end
      val bare = then1Body "rw [] >- metis_tac []"
      val parens = then1Body "rw [] >- (simp [] >> rw [])"
      val parenText = "(simp [] >> rw [])"
    in
      case (bare, parens) of
        (SOME (bte, [FAtom _]), SOME (pte, [FGroup ((s, e), _)])) =>
          if isSome (topSpan bte) then die "bare `>-' grew a span"
          else if isSome (topSpan pte) then die "`>- (...)' grew a span"
          else if e - s <> String.size parenText then
            die "the parenthesised body's span is not the parens"
          else OK()
      | _ => die "branch bodies are not (atom, group)"
    end

val _ = tprint "TacticParse: a combinator bracket records its own token"
val _ =
    let
      (* The span the LSP squiggles when a branch proves nothing.  It
         is separate from the wrapper's extent, which stays absent --
         see above -- so nothing the walk measures moves with it. *)
      fun opens txt =
          case fragsOf txt of
            NONE => []
          | SOME frags =>
            let
              fun go [] = []
                | go (FBracket (ok, inner, _, _) :: r) =
                    ok :: go inner @ go r
                | go (FFOpen ok :: r) = ok :: go r
                | go (FGroup (_, inner) :: r) = go inner @ go r
                | go (_ :: r) = go r
            in go frags end
      fun tokenOf txt =
          case List.mapPartial
                 (fn FOpenThen1 sp => SOME sp
                   | FOpenBy (_, sp) => SOME sp
                   | FOpenSufficesBy (_, sp) => SOME sp
                   | _ => NONE)
                 (opens txt) of
            [sp] => SOME (textAt txt sp)
          | _ => NONE
      val cases = [("rw [] >- metis_tac []", ">-"),
                   ("rw [] >- (simp [] >> rw [])", ">-"),
                   ("rw [] THEN1 metis_tac []", "THEN1"),
                   ("`p` by simp []", "by"),
                   ("`p` suffices_by simp []", "suffices_by")]
      val bad = List.filter (fn (txt, want) => tokenOf txt <> SOME want) cases
    in
      case bad of
        [] => OK()
      | (txt, want) :: _ =>
          die ("`" ^ txt ^ "` records " ^
               (case tokenOf txt of NONE => "no token" | SOME t => "`"^t^"`") ^
               ", want `" ^ want ^ "`")
    end

end (* TacticParse local *)

(* ProofStepPlan tests.  These construct TacticParse trees directly: parser
   surface-syntax tests belong to TacticParse, while these check the shared
   lowering and path/signature layer independently. *)
val _ = let
  open TacticParse ProofStepPlan
  fun assert msg true = OK ()
    | assert msg false = die msg
  val a = Opaque (10, "a")
  val b = Opaque (10, "b")
  val c = Opaque (10, "c")
  val plan = fromTactic (Then [a, First [b, c]])
  val _ = tprint "ProofStepPlan lowers structured THEN suffix under Each"
  val _ = assert "unexpected structured THEN plan"
    (case plan of
       [Leaf {kind = TacticLeaf, ...},
        Each [Choice {source = NONE,
                      alternatives = [[Leaf {kind = TacticLeaf, ...}],
                                      [Leaf {kind = TacticLeaf, ...}]]}]] => true
     | _ => false)
  val _ = assert "choice lost its source annotation"
    (case fromTactic (Group (true, "first", First [b, c])) of
       [Choice {source = SOME "first", ...}] => true
     | _ => false)
  val _ = tprint "ProofStepPlan expands mapped tactic applications"
  val mappedArguments = [OOpaque (10, "x"), OOpaque (10, "y")]
  val _ = assert "MAP_EVERY was not lowered as a tactic sequence"
    (case fromTactic (MapEvery ("f", mappedArguments)) of
       [Leaf {tactic = MapEvery ("f", [_]), ...},
        Leaf {tactic = MapEvery ("f", [_]), ...}] => true
     | _ => false)
  val _ = assert "MAP_FIRST was not lowered as a choice"
    (case fromTactic
       (Group (true, "map-first", MapFirst ("f", mappedArguments))) of
       [Choice {source = SOME "map-first",
                alternatives = [[Leaf _], [Leaf _]]}] => true
     | _ => false)
  val _ = tprint "ProofStepPlan keeps tactic-level reverse atomic"
  val reverse = Group (true, "reverse", ThenLT (a, [LReverse]))
  val _ = assert "reverse exposed a spanless list-tactic leaf"
    (case fromTactic reverse of
       [Leaf {kind = TacticLeaf,
              tactic = Group (true, "reverse", _)}] => true
     | _ => false)
  val _ = assert "reverse suffix introduced an Each step"
    (case fromTactic (Then [b, reverse]) of
       [Leaf _, Leaf {tactic = Group (true, "reverse", _), ...}] => true
     | _ => false)
  val _ = tprint "ProofStepPlan omits the >>~- failure sentinel"
  val _ = assert ">>~- exposed its internal First [] sentinel"
    (case fromTactic
       (ThenLT (a,
          [LSelectThen (Rename "pattern", Then [b, First []])])) of
       [Leaf _, Select {selector = SelectMatchingAll "pattern",
                        mode = SelectSolve, body = [Leaf _]}] => true
     | _ => false)
  val _ = tprint "ProofStepPlan keeps list-tactic alternatives atomic"
  val _ = assert "list-tactic alternative was exposed as Choice"
    (case fromTactic (ThenLT (a, [LFirst [LOpaque (10, "x"),
                                         LOpaque (10, "y")]])) of
       [Leaf {kind = TacticLeaf, ...},
        Leaf {kind = ListTacticLeaf, ...}] => true
     | _ => false)
  val _ = tprint "ProofStepPlan lowers THENL representation to Cases"
  val cases = fromTactic
    (ThenLT (a, [LNullOk (LTacsToLT (List ("list", [b, c])))]))
  val _ = assert "unexpected THENL plan"
    (case cases of
       [Leaf _, Cases [[Leaf _], [Leaf _]]] => true
     | _ => false)
  val _ = tprint "ProofStepPlan path lookup follows dynamic structural paths"
  val _ = assert "path did not locate alternative leaf"
    (case stepAtPath plan
       [PathStep 1, PathEach 0, PathStep 0, PathAlternative 2, PathStep 0] of
       SOME (Leaf _) => true
     | _ => false)
  fun leafText _ _ = "opaque"
  fun annotationText _ = "selector"
  val projections = {leaf = leafText, annotation = annotationText}
  val plan2 = fromTactic
    (Then [Opaque (10, "moved-a"),
           First [Opaque (10, "moved-b"), Opaque (10, "moved-c")]])
  val _ = tprint "ProofStepPlan canonical form is controlled by projections"
  val _ = assert "canonical plan unexpectedly depends on annotations"
    (canonicalPlan projections plan = canonicalPlan projections plan2)
  val _ = tprint "ProofStepPlan canonical prefix includes preceding structure"
  val path =
    [PathStep 1, PathEach 0, PathStep 0, PathAlternative 2, PathStep 0]
  val _ = assert "canonical prefix unavailable"
    (Option.isSome (canonicalPrefix projections plan path))
  fun parseTactic source = let
    val fed = ref false
    fun read _ = if !fed then "" else (fed := true; source)
    fun ignoreParseError _ _ _ = ()
    val result = HOLSourceParser.parseSML
      "<ProofStepPlan selftest>" read ignoreParseError
      HOLSourceParser.initialScope
    in
      case #parseDec result () of
        SOME (HOLSourceAST.DecExp expression) => parseTacticBlock expression
      | _ => raise Fail "expected tactic expression"
    end
  val _ = assert "lowercase map_every was not recognized"
    (case parseTactic "map_every f [x]" of
       MapEvery (_, [_]) => true
     | _ => false)
  val groupedSequence = parseTactic
    "CONJ_TAC >> (CONJ_TAC >- ACCEPT_TAC TRUTH >> ACCEPT_TAC TRUTH)"
  val _ = tprint "TacticParse retains parenthesized tactic sequence boundaries"
  val _ = assert "parenthesized tactic sequence was flattened"
    (case groupedSequence of
       Then [Opaque _, Group (_, _, Then [_, Opaque _])] => true
     | _ => false)
  val _ = assert "grouped tactic sequence escaped its Each step"
    (case fromTactic groupedSequence of
       [Leaf _, Each [Leaf _, Select _, Leaf _]] => true
     | _ => false)
  val groupedListSequence = parseTactic "a >>> (b >> c)"
  val _ = tprint "ProofStepPlan keeps grouped list-tactic composition atomic"
  val _ = assert "grouped list-tactic composition was split"
    (case fromTactic groupedListSequence of
       [Leaf {kind = TacticLeaf, ...},
        Leaf {kind = ListTacticLeaf, tactic = Group (_, _, LThen _)}] => true
     | _ => false)
  val _ = assert "FIRST lost its enclosing source annotation"
    (case fromTactic (parseTactic "FIRST [a, b]") of
       [Choice {source = SOME _, alternatives = [[Leaf _], [Leaf _]]}] => true
     | _ => false)
  val _ = assert "MAP_FIRST lost its enclosing source annotation"
    (case fromTactic (parseTactic "MAP_FIRST f [x]") of
       [Choice {source = SOME _, alternatives = [[Leaf _]]}] => true
     | _ => false)
  val _ = tprint "TacticParse preserves FIRST_PROVE"
  val parsedFirstProve = parseTactic "FIRST_PROVE [a, b]"
  val _ = assert "FIRST_PROVE parsed as an opaque tactic"
    (case parsedFirstProve of
       Group (_, _, FirstProve [Opaque _, Opaque _]) => true
     | _ => false)
  val _ = assert "FIRST_PROVE did not print as FIRST_PROVE"
    (case printTacAsSML "FIRST_PROVE [a, b]" parsedFirstProve of
       SOME text => String.isSubstring "FIRST_PROVE" text
     | NONE => false)
  val _ = assert "FIRST_PROVE was not lowered as a choice"
    (case fromTactic parsedFirstProve of
       [Choice {source = SOME _, alternatives = [[Leaf _], [Leaf _]]}] => true
     | _ => false)
  val _ = tprint "TacticParse preserves by rather than elaborating it as sg"
  val parsedBy = parseTactic "q by tac"
  val _ = assert "by parsed as ordinary subgoal/THEN1 structure"
    (case parsedBy of By ((0, 1), (2, 4), _) => true | _ => false)
  val _ = tprint "TacticParse preserves suffices_by as a primitive"
  val parsedSuffices = parseTactic "q suffices_by tac"
  val _ = assert "suffices_by parsed as ordinary subgoal structure"
    (case parsedSuffices of
         SufficesBy ((0, 1), (2, 13), _) => true | _ => false)
  val _ = tprint "TacticParse prints preserved by syntax"
  val _ = assert "by did not print as by"
    (case printTacAsSML "q by tac" parsedBy of
       SOME text => String.isSubstring "by" text
     | NONE => false)
  val _ = tprint "ProofStepPlan preserves by semantics structurally"
  val byPlan = fromTactic (By ("assertion", "by", b))
  val _ = assert "by was lowered through ordinary Subgoal"
    (case byPlan of
       [Leaf {kind = TacticLeaf,
              tactic = By ("assertion", "by", Then [] )},
        Select {selector = SelectFirst, mode = SelectSolve,
                body = [Leaf {kind = TacticLeaf, ...}]}] => true
     | _ => false)
  val _ = tprint "ProofStepPlan preserves suffices_by semantics structurally"
  val sufficesPlan = fromTactic (SufficesBy ("assertion", "suffices_by", b))
  val _ = assert "suffices_by was lowered through ordinary Subgoal"
    (case sufficesPlan of
       [Leaf {kind = TacticLeaf,
              tactic = SufficesBy ("assertion", "suffices_by", Then [])},
        Select {selector = SelectFirst, mode = SelectSolve,
                body = [Leaf {kind = TacticLeaf, ...}]}] => true
     | _ => false)
in
  ()
end

(* ----------------------------------------------------------------------
    TacticLeafSource

    Shared leaf-source lowering and leaf-kind classification.  Synthesised
    source is compiled in the ordinary session namespace rather than only
    compared as text.
   ---------------------------------------------------------------------- *)

structure LeafSrcTest = struct
  (* PolyML.compiler assigns compiled values through these qualified names. *)
  val tac: Abbrev.tactic option ref = ref NONE
  val ltac: Abbrev.list_tactic option ref = ref NONE
end

local
  open TacticParse ProofStepPlan TacticLeafSource
  fun assert msg true = OK ()
    | assert msg false = die msg
  fun parseTactic source = let
    val fed = ref false
    fun read _ = if !fed then "" else (fed := true; source)
    fun ignoreParseError _ _ _ = ()
    val result = HOLSourceParser.parseSML
      "<TacticLeafSource selftest>" read ignoreParseError
      HOLSourceParser.initialScope
    in
      case #parseDec result () of
        SOME (HOLSourceAST.DecExp expression) => parseTacticBlock expression
      | _ => raise Fail "expected tactic expression"
    end

  (* Compile through the same quotation filter as the walker. *)
  fun compilesAs holder src = let
    val wrapped = holder ^ " := SOME (" ^ src ^ ");"
    val filtered =
        HOLSource.fromString {quietOpen = true, print = fn _ => ()} wrapped
    val i = ref 0
    val n = String.size filtered
    fun read () = if !i >= n then NONE
                  else SOME (String.sub (filtered, !i)) before i := !i + 1
    fun swallow _ = ()
    val () = (LeafSrcTest.tac := NONE; LeafSrcTest.ltac := NONE)
    val _ = Portable.total (fn () => PolyML.compiler
              (read, [PolyML.Compiler.CPErrorMessageProc swallow,
                      PolyML.Compiler.CPPrintStream swallow,
                      PolyML.Compiler.CPOutStream swallow]) ()) ()
    in
      Option.isSome (!LeafSrcTest.tac) orelse
      Option.isSome (!LeafSrcTest.ltac)
    end
  fun compiles TacticLeaf src = compilesAs "LeafSrcTest.tac" src
    | compiles ListTacticLeaf src = compilesAs "LeafSrcTest.ltac" src

  fun firstLeaf source =
      case fromTactic (parseTactic source) of
        Leaf {kind, tactic} :: _ => (kind, tactic)
      | Select {body = Leaf {kind, tactic} :: _, ...} :: _ => (kind, tactic)
      | _ => raise Fail ("no leading leaf in: " ^ source)

  fun synthesised source =
      case leafSource source (#2 (firstLeaf source)) of
        SOME (Synthesised text) => SOME text
      | _ => NONE

  val byText = "`a = b` by ACCEPT_TAC TRUTH"
  val _ = tprint "TacticLeafSource lowers a by-assertion applicatively"
  val _ = assert "by leaf did not lower through BasicProvers.byA"
    (case synthesised byText of
       SOME text => String.isPrefix "BasicProvers.byA (" text andalso
                    String.isSubstring "Tactical.ALL_TAC" text
     | NONE => false)

  (* `q by ALL_TAC' fails because `by' must discharge q. *)
  val _ = tprint "TacticLeafSource avoids by's failing surface form"
  val _ = assert "the surface rendering was already applicative"
    (case printTacAsSML byText (#2 (firstLeaf byText)) of
       SOME text => not (String.isSubstring "byA" text)
     | NONE => false)

  val sufficesText = "`a = b` suffices_by ACCEPT_TAC TRUTH"
  val _ = tprint "TacticLeafSource lowers suffices_by applicatively"
  val _ = assert "suffices_by leaf did not lower through suffices_byA"
    (case synthesised sufficesText of
       SOME text => String.isPrefix "BasicProvers.suffices_byA (" text
     | NONE => false)

  val subgoalText = "sg `a = b`"
  val _ = tprint "TacticLeafSource qualifies sg through its own structure"
  val _ = assert "sg was left as surface syntax"
    (case synthesised subgoalText of
       SOME text => String.isPrefix "BasicProvers.subgoal" text
     | NONE => false)

  (* ProofStepPlan keeps Group wrappers; linearize removes them. *)
  val _ = tprint "TacticLeafSource agrees on a grouped and a bare leaf"
  val _ = assert "grouping changed the answer"
    (let val grouped = parseTactic subgoalText
         fun strip (Group (_, _, e)) = e
           | strip e = e
     in
       Option.map sourceText (leafSource subgoalText grouped) =
       Option.map sourceText (leafSource subgoalText (strip grouped))
     end)

  val _ = tprint "TacticLeafSource answers NONE for a spanless no-op"
  val _ = assert "a no-op leaf offered source"
    (not (Option.isSome (leafSource "" (Then []))))

  val _ = tprint "TacticLeafSource routes a tactic in a list as a tactic"
  val _ = assert "OOpaque was misrouted as a list_tactic"
    (fragmentLeafKind (OOpaque (0, (0, 0))) = TacticLeaf)
  val _ = tprint "TacticLeafSource routes goal reordering as a list_tactic"
  val _ = assert "LReverse was misrouted as a tactic"
    (fragmentLeafKind LReverse = ListTacticLeaf)

  (* Synthesised source must not depend on script-local opens. *)
  val corpus =
    [byText, sufficesText, subgoalText,
     "RENAME_TAC [`x`]",
     "MAP_EVERY ACCEPT_TAC [TRUTH]",
     "CONJ_TAC"]
  fun checkCompiles source = let
    val (kind, tactic) = firstLeaf source
    in
      case leafSource source tactic of
        NONE => ()
      | SOME (Verbatim _) => ()   (* User source may depend on local opens. *)
      | SOME (Synthesised text) =>
        (tprint ("TacticLeafSource compiles: " ^ text);
         assert ("synthesised source did not compile: " ^ text)
                (compiles kind text))
    end
  val _ = List.app checkCompiles corpus
in
  ()
end

val () = OS.Process.exit
           (if !failcount = 0 then OS.Process.success
            else OS.Process.failure)
