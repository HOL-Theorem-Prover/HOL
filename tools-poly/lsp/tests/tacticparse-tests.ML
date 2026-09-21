(* TacticParse, driven by `bin/hol'.
 *
 * `poly-init2' compiles TacticParse into the executable rather than into
 * sigobj, so a selftest.exe built by HOLMOSMLC cannot link it and these
 * cannot live in `src/parse/selftest.sml' where they started.  Running
 * them here costs nothing extra: this directory already starts a
 * `bin/hol' for `load-init-files.ML'.
 *
 * Its only consumers are the LSP's `tactic_steps', `tactic_walker' and
 * `goal_state_init', which is why the tests sit beside them.
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
            | then1s (FBracket (FOpenThen1, inner, FClose, te) :: r) =
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
                | go (FBracket (FOpenThen1, inner, _, te) :: _) =
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

end (* TacticParse local *)

val () = OS.Process.exit
           (if !failcount = 0 then OS.Process.success
            else OS.Process.failure)
