signature TacticParse =
sig

datatype 'a tac_expr
  = Then of 'a tac_expr list
  | ThenLT of 'a tac_expr * 'a tac_expr list
  | Subgoal of 'a
  | First of 'a tac_expr list
  | Try of 'a tac_expr
  | Repeat of 'a tac_expr
  | MapEvery of 'a * 'a tac_expr list
  | MapFirst of 'a * 'a tac_expr list
  | Rename of 'a
  | Opaque of int * 'a

  | LThen of 'a tac_expr * 'a tac_expr list
  | LThenLT of 'a tac_expr list
  | LThen1 of 'a tac_expr
  | LTacsToLT of 'a tac_expr
  | LNullOk of 'a tac_expr
  | LFirst of 'a tac_expr list
  | LFirstLT of 'a tac_expr
  | LSelectGoal of 'a
  | LSelectGoals of 'a
  | LAllGoals of 'a tac_expr
  | LNthGoal of 'a tac_expr * 'a
  | LLastGoal of 'a tac_expr
  | LHeadGoal of 'a tac_expr
  | LSplit of 'a * 'a tac_expr * 'a tac_expr
  | LReverse
  | LTry of 'a tac_expr
  | LRepeat of 'a tac_expr
  | LSelectThen of 'a tac_expr * 'a tac_expr
  | LOpaque of int * 'a

  | List of 'a * 'a tac_expr list
  | Group of bool * 'a * 'a tac_expr
  | RepairEmpty of bool * 'a * string
  | RepairGroup of 'a * string * 'a tac_expr * string
  | OOpaque of int * 'a

val isTac: 'a tac_expr -> bool
val topSpan: 'a tac_expr -> 'a option

val parseTacticBlock: HOLSourceAST.exp -> (int * int) tac_expr

val mapTacExpr:
  { start: bool -> 'a -> 'b, stop: bool -> 'b -> 'c,
    repair: 'a -> string -> unit } ->
  'a tac_expr -> 'c tac_expr

val printTacsAsE: string -> (int * int) tac_expr list -> string

datatype tac_frag_open
  = FOpen
  | FOpenThen1
  | FOpenFirst
  | FOpenRepeat
  | FOpenTacsToLT
  | FOpenNullOk
  | FOpenNthGoal of int * int
  | FOpenLastGoal
  | FOpenHeadGoal
  | FOpenSplit of int * int
  | FOpenSelect
  | FOpenFirstLT

datatype tac_frag_mid
  = FNextFirst
  | FNextTacsToLT
  | FNextSplit
  | FNextSelect

datatype tac_frag_close
  = FClose
  | FCloseFirst
  | FCloseRepeat
  | FCloseFirstLT

datatype tac_frag
  = FFOpen of tac_frag_open
  | FFMid of tac_frag_mid
  | FFClose of tac_frag_close
  | FAtom of (int * int) tac_expr
  | FGroup of (int * int) * tac_frag list
  | FBracket of
    tac_frag_open * tac_frag list * tac_frag_close * (int * int) tac_expr
  | FMBracket of
    tac_frag_open * tac_frag_mid * tac_frag_close *
    tac_frag list list * (int * int) tac_expr

val linearize: ((int * int) tac_expr -> bool) ->
  (int * int) tac_expr -> tac_frag list

val unlinearize: tac_frag list -> (int * int) tac_expr

val printFragsAsE: string -> tac_frag list list -> string

val sliceTacticBlock:
  int -> int -> bool -> int * int -> (int * int) tac_expr -> tac_frag list list

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    TacticParse converts HOL4 tactic source code (already parsed into a
    HOLSourceAST.exp) into a structured tac_expr tree, provides inverse
    pretty-printing back to source text, and offers a flat tac_frag
    representation suited to interactive editing through goalFrag.

    The central datatype is 'a tac_expr.  The 'a annotation is normally
    a source span (int * int), threaded uniformly and re-decorated via
    mapTacExpr.  Its constructors fall into three groups:

      - Tactic forms: Then, ThenLT, Subgoal, First, Try, Repeat,
        MapEvery, MapFirst, Rename, Opaque.  These denote ordinary
        tactics (functions on a single goal).  Then is an n-ary
        flattening of THEN; ThenLT bridges into a list_tactic
        continuation.  Opaque carries a precedence and a span when no
        surface pattern matched.
      - List_tactic forms (L-prefixed): LThen, LThenLT, LThen1,
        LTacsToLT, LNullOk, LFirst, LFirstLT, LSelectGoal,
        LSelectGoals, LAllGoals, LNthGoal, LLastGoal, LHeadGoal,
        LSplit, LReverse, LTry, LRepeat, LSelectThen, LOpaque.  These
        denote operations on the goal list, mirroring the *_LT
        combinator family.
      - Meta forms: List (a literal subgoal-tactic list), Group (a
        tagged wrapper preserving the source extent of a sub-expression
        with a tactic-vs-list_tactic flag), RepairEmpty / RepairGroup
        (synthetic nodes inserted where the source was empty or had an
        unclosed bracket), and OOpaque (an opaque list element).

    isTac classifies a tac_expr as a tactic (true) or a list_tactic
    (false).  topSpan pulls the source span out of the meta nodes that
    carry one (Group, List, RepairEmpty/Group, the *Opaque triple, and
    LSelectGoal/LSelectGoals).

    parseTacticBlock : exp -> (int * int) tac_expr is the parser
    proper.  It is built from a small set of mutually-recursive
    simplify_* helpers, one per surface form being recognised:

      - simplify        : the tactic-position entry point.
      - simplifys       : flattens THEN-chains (THEN, >>, ++, \\\\,
                          EVERY [...]).
      - simplifyFirst   : flattens ORELSE / FIRST chains.
      - simplifyThenLT  : flattens THEN_LT / >>> chains, accumulating
                          list_tactic continuations to the right.
      - simplifyThenL   : handles t >| [...] / t THENL [...].
      - simplifyTacList : a literal tactic list element.
      - simplifyLThen   : THEN within a list_tactic context.
      - simplifyLFirst  : ORELSE_LT / FIRST_LT chains.
      - simplifysLT     : list_tactic-position form recognition --
                          TACS_TO_LT, NULL_OK_LT, ALLGOALS, TRYALL,
                          NTH_GOAL, LASTGOAL, HEADGOAL, SPLIT_LT,
                          TRY_LT, REPEAT_LT, FIRST_LT, EVERY_LT,
                          SELECT_LT_THEN, SELECT_LT, REVERSE_LT,
                          ALL_LT.
      - simplifyLT      : list_tactic entry point.

    Surface sugars are recognised at parse time and elaborated to the
    underlying combinator tree: e.g. `t1 by t2` becomes
    ThenLT (Subgoal _, [LThen1 t2]); `suffices_by` additionally inserts
    an LReverse; `>~ pat` becomes LSelectGoal; `>>~- (pat, t)` becomes
    LSelectThen (Rename _, ...).  Unclosed parens turn into RepairGroup
    nodes carrying the missing terminator; empty tactic positions turn
    into RepairEmpty "ALL_TAC" (or "ALL_LT" in list_tactic position).

    mapTacExpr {start, stop, repair} walks a tac_expr applying the
    user-supplied callbacks to every annotation, with the boolean flag
    distinguishing tactic from list_tactic positions and notifying
    repair on the synthesised nodes.  Used to re-decorate the tree
    (e.g. with type info or diagnostic markers) without rewriting its
    structure.

    printTacsAsE renders a list of (int*int) tac_expr back to source
    text, formatted as a sequence of `e(...)` calls suitable for
    interactive replay.  It builds an intermediate tree (TAtom /
    TOpaque / TInfix / TApp / TList / TTuple), then runs a peephole
    pass (optTree) that folds canonical >>>-shaped patterns back into
    surface sugar (>|, >-, >~, >>~, >>~-, by, suffices_by, reverse,
    TRYALL) and drops trivial identity combinators (NO_TAC ORELSE _,
    ALL_TAC >> _, ALL_LT >>> _).  Layout is precedence-driven, with a
    running indent and parens added only when required.

    The linearised form (tac_frag) is the bridge to goalFrag.  An
    expression is decomposed into:

      - FFOpen / FFMid / FFClose markers naming the combinator they
        open, advance, or close (FOpen / FOpenThen1 / FOpenFirst /
        FOpenRepeat / FOpenTacsToLT / FOpenNullOk / FOpenNthGoal /
        FOpenLastGoal / FOpenHeadGoal / FOpenSplit / FOpenSelect /
        FOpenFirstLT, with FNext_* and FClose_* counterparts).
      - FAtom : an entire tac_expr held as an indivisible unit.
      - FGroup : a nested fragment list with its own source span,
        preserving grouping structure across slicing.
      - FBracket / FMBracket : a fully-balanced single- or
        multi-section combinator block, retained as one unit when not
        sliced through.

    linearize takes an isAtom predicate (deciding which subexpressions
    stay whole) and walks the tree, opening brackets at the points
    where isAtom returns false.  unlinearize is its left inverse on
    fully-balanced fragment lists; it is intentionally lossy on the
    open-kind tags (each FOpen_* is mapped to a plausible default
    combinator) because the round trip need only preserve meaning, not
    surface syntax.

    sliceTacticBlock start stop sliceClose sp e extracts the portion
    of e overlapping the source range [start, stop).  Brackets that
    straddle the cut are either expanded into FFOpen / FFMid / FFClose
    fragments (sliceClose = true, the goalFrag editing mode) or
    descended into so only the relevant sub-segments survive
    (sliceClose = false).  The result is a list of fragment lists, one
    per logical section the slice cuts the expression into.
    printFragsAsE composes unlinearize with printTacsAsE for round-trip
    rendering.

    Together these pieces let goalFrag treat a string of tactic source
    as a navigable, sliceable, re-printable structure: parse with
    parseTacticBlock, slice with sliceTacticBlock at cursor positions,
    rewrite, then unlinearize and printFragsAsE back to text.
   ---------------------------------------------------------------------- *)
