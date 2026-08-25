# Context-parameterised tactics: migration strategy

Written against the `new-tactics` line of development (head
`698e4b445` at time of writing).  Inside the sandboxed VM the repo is
mounted at `/repo`; see `developers/claude/LOCKED-VM.md`.

## Context

HOL4 tactics have always been `goal -> goal list * validation`, reading
whatever prover state the process happened to be in.  That makes a
proof's behaviour a function of load order rather than of its own
source.  The worked example, documented in
`developers/discussion/prove-without-current-theory.md`, is
`src/metis/folTools.sml`: it pinned `Parse.Term` to the `normalForms`
grammar, but `GEN_TAC` chooses bound-variable names apart from the
constants of the *ambient* grammar, so a theory defining a constant `g`
loaded first made the proof fail — surfacing 30 directories away, on
Moscow ML only, as an unprovable goal.

`c49daab01` changed the tactic type to

    type tactic = goal -> Context.t -> goal list * validation

so a proof is a function of an explicitly supplied, immutable
`Context.t` (`src/prekernel/Context.sig`) instead of the live global.
The intended payoff is that the LSP server can run tactic proofs on
independent Poly/ML threads, each against a captured snapshot, rather
than serialising on shared mutable state.

Worth knowing up front: **the LSP already captures per-declaration
snapshots and replays from them** (`server.ML:560`, `:821`, `:1064`),
and `goalStateAtPos` (`:1378`) already runs a proof against the context
captured at its position — by bracketing a *global* `Context.restore`.
So this migration is not building that machinery; it is removing the
global mutation at its centre so the same thing can happen on several
threads at once.

Two things follow, and they are the substance of this plan:

1. The parameter is only a channel.  Everything reachable from a proof
   that still reads ambient state — most importantly conversions —
   defeats it.  Closing that is the bulk of the work.
2. Somebody has to decide *which* context each proof gets.  That
   decision belongs to whoever is driving the file, not to
   `boolLib.store_thm_at`.

Intended outcome: no code on the proof path reads process-global state;
proofs are pure functions of `(goal, Context.t)`; and the LSP can
elaborate a file once with cheated placeholders, capturing a snapshot
at each proof site, then replay the real proofs in parallel.

## Starting state

Head is `698e4b445`, merging the `ctnone-proves` branch — the
load-time-proof cleanup documented in
`developers/discussion/prove-without-current-theory.md` — into the
tactic work of `c49daab01` and `8cac98eef`.  The working tree is
clean, so the two projects are no longer tangled and the migration's
history is legible.

The tactic work is early: the type change and the `src/1` combinators
are done, `Parse` has its first two ctxt-taking accessors, and
`Prim_rec` is started.  Everything from Phase 0 onwards is ahead.

That was the state this plan was written against.  Phase 0 and most of
Phase 1 have since landed and the core build is green; see **Status**
below for what that took and where the tree disagreed with the plan.

## Status: Phases 0, 1, 2 and 3a have landed

The full build passes with selftests, so the baseline the phases assume is
real and then some.  Getting there took all of Phase 0 and all of Phase 1,
and the findings below correct this document where the tree disagreed with
it.

**The compat layer is not optional groundwork for later — it is what
makes a green baseline possible at all.**  `Tactical.prove` was
ctxt-first, so every one of the raw call sites was broken; the first
casualty was `src/1/coreboolSupportScript.sml`, two directories in.
Decision 4's `prove_in` / ambient-`prove` split therefore landed
alongside Phase 0 rather than at the head of Phase 1.  `TAC_PROOF` and
`default_prover` needed the same treatment, since raw ambient uses of
both are spread through `src`; the explicit entry point is spelled
`TAC_PROOF_in`, so Phase 4's `TAC_PROOF ctxt (goal, tac)` means
`TAC_PROOF_in`.

### The bug class this migration actually has

Very little of the work was arity.  The substance is that **`tac g` no
longer runs a tactic — it builds a closure awaiting the context** — so
every construct that treats a tactic application's failure or effects as
control flow silently stopped working, while still typechecking:

- `handle` around `tac g`: `IMP_RES_TAC`, `RES_TAC` and their
  `res_quan` counterparts turned from no-ops-on-failure into failing
  tactics; `UNABBREV_TAC` lost the clear error of issue #1483, which its
  own regression test caught; `MATCH_ASSUM_ABBREV_TAC` stopped
  backtracking to the next matching assumption; `HolSmt`'s `NLA_TAC`
  stopped falling back through its decision procedures; `DISCH_TAC`,
  `STRIP_TAC`, `SYM_TAC`, `INDUCT_TAC`, `P_PGEN_TAC` and
  `suffices_by` lost their error wrapping.
- `Lib.total` / `tryfind`: `APPLY_MONOTAC` stopped trying the next
  monotonicity rule.
- Continuation-passing search: `bvk_find_term` skips a candidate
  sub-term whose continuation raises, so `DEEP_INTROk_TAC` accepted the
  first candidate and failed later — this is what broke
  `While`'s `OWHILE_THM`.  `match_goal`'s lazy search abandons a
  candidate match the same way.
- Effect windows: `Portable.with_flag` / `trace` / `add_time` /
  `timeout` / a cache clear placed before the application all close
  before the tactic runs.  `TC_OFF` in `smlExecute`, `tttSearch` and
  `hhReconstruct` suppressed nothing; TacticToe timed closure
  construction; `clear_arith_caches` left the "uncached" leg of the
  arith cache tests running warm.

**The Phase 2 census will not find any of this**, because no ambient read
is involved.  It surfaces only as a failing proof, a lost error message
or a silently weaker tactic.  The rule to grep for is: an application of
a tactic to fewer than two arguments, inside anything that catches, times,
flag-wraps or searches.

### Corrections to this document

- **Script files are not edit-free.**  The scale table's "none" is right
  about plumbing — the expansion supplies the context — but a proof body
  that defines its own tactic helper and falls back on failure needs
  threading like any library.  Five such sites exist in `src` and
  `examples`; `arithmeticScript`'s `LESS_SUB_ADD_LESS` and
  `pred_setScript`'s `CARD_PSUBSET` are the ones that fail visibly.
- **`Proof[exclude_simps=…]` cannot be fixed from the expander.**  The
  eta-expansion suggested for `wrapTac` does not help: the window in
  `with_simpset_updates f g x` closes when `g x` returns, and under the
  new type that is the context-awaiting closure.  The fix landed in the
  wrapper instead — `with_simpset_updates_tac` spans both applications —
  and `wrapTac` is unchanged.  Phase 3a's context transform should
  supersede it and delete the window; `exclSimpsScript.sml` is the guard.
- **`hurdUtils` defined its own `type tactic`**, so its annotations were
  checked against the pre-context shape.  It now takes the type from
  `Abbrev`.  No other file in the tree defines the type independently.
- **`goalFrag.expand` and friends take the context as a parameter**
  (`tactic -> Context.t -> frag_tactic`), which is what Phase 4 wanted;
  `goalStack`, `goalTree` and `Manager` snapshot the session's context,
  which is correct for interactive use and declaration-level as far as
  the tripwire is concerned.
- **`testutils.runtac`** applies a tactic to a goal and the ambient
  context.  Every directory's selftest needs it, so it lives in
  `testutils` rather than being redeclared.

### Where Phase 1 got to

All five items have landed and **the full build is green** — `bin/build -t
-F`, which is the core sequence, `src/parallel_builds/core`, the example
set built at selftest level, and the 1589-entry help-documentation pass.
The LSP suite is 66/66.  Two notes on running it: the `integer_*` cases
need `jrhUtils` in `sigobj`, which only the full build puts there, and the
suite takes `HOL_LSP_TEST_REPO` to point at a worktree.

Item 3 replaced the changed-flag machinery outright: the parsers and
printers derived from the two grammars are a `Susp.susp` in a slot of
their own, rederived by the four grammar mutators, so the 26 flag-setting
sites, both flags, `update_type_fns`, `update_term_fns` and
`invalidate_caches` are gone.  `type_parser1` went with them — it was
rebuilt on every invalidation and never read.

Item 2 and item 4 landed together, as decision 6 requires.  `Parse` gained
`Term_in`, `Absyn_in` and `typedTerm_in` so `Q.store_thm_at` can parse a
statement against the context it proves it in; constants still resolve
against the kernel signature read from the *ambient* context, which is the
kernel readers' own remaining work.  `located_qDefine` takes the context
and ignores it: the quote and the termination proof belong to `Defn`,
which decision 10 reaches in Phase 4.  `CoIndDefLib.xHol_coreln` needs the
parameter as much as `xHol_reln` does — the expander picks between them.

**The expander has two emission modes and both need the argument.**
Without a file and line — Docfile examples, interactive input —
`mkLocString` named the *ambient* `qDefine` / `store_thm`, which take no
context by design, so a context got applied to a theorem.  Both forms now
go through the located entry point with `DB_dtype.Unknown`.  Only the
help-docs stage of a full build catches this; the core build skips it.

### More of the same bug class

Phase 1's work turned up further instances of the deferred-execution
class, all of them silent:

- **`mp_then` and `resolve_then`** — the engines under `drule`,
  `drule_at`, `dxrule` and friends.  Both try candidate positions in turn
  and move on when the continuation raises; with the continuation only
  built, the search commits to the first position.  This is what stopped
  `drule_at_then Any irule` matching in `companionScript`.
- **`Q`'s `wholeterm_rename_helper` and `subterm_helper`** — the search
  behind `rename`, `MATCH_RENAME_TAC` and the abbreviation tactics.  The
  comment above them already said the failure has to be raised late enough
  for `FIRST_ASSUM` to catch it; that is now the context application.
  `symmetryScript` and `unary_recfnsScript` were failing on this.
- **`by0`** — `by`'s line-number error reporting, the sibling of
  `suffices_by`.  `bylocnScript` asserts on exactly that message.
- Effect windows in more guises: `smlTimeout.timeout`, `add_time`,
  `total_time`, `trace`, and a cache clear sequenced before the tactic
  rather than before it runs.

Two lessons for the grep.  Anchoring on `_TAC` misses the lowercase
combinators (`mp_then`, `resolve_then`), and requiring the control-flow
keyword to follow the application immediately misses `... ttac th g\n end
handle ...`.  Both patterns are worth keeping in the sweep.

Finally, a naming hazard: several files use `ctxt` for a list of the
goal's free variables (`markerLib`, `wlogLib`, `Q`).  Sitting next to a
`Context.t` also called `ctxt`, that reads as a bug; they are `fvl` now.

### Editing the expander

`bin/hol.state0` and `bin/unquote` are built from `tools/parsing`, and
Holmake does not know it.  After changing `HOLSourceExpand.sml`, re-run
`poly < tools/smart-configure.sml`, delete `bin/hol.state0` and
`bin/hol.state.min`, and rebuild — otherwise the build keeps expanding
`Theorem … QED` with the old expander and the change is never
exercised.  `tools/Holmake/tests/quote-filter` holds the golden
expansion for both compilers.

## Phase 2: the tripwire and the census

`Context.in_proof` marks the dynamic extent of a parameterised proof and
`Context.snapshot` reports when called inside one, under the trace
`"ambient context inside proof"`.  `TAC_PROOF_in` is the only sanctioned
caller and brackets both the tactic and its validation.  The extent is a
per-thread depth (`ThreadLocal`, restored on exception), so a worker
proving on its own thread cannot see another's.

**The extent has to cover the goal application, not just the context
one.**  `Context.in_proof (tac g) ctxt` evaluates `tac g` before
`in_proof` sees it, and for anything shaped like
`fn g => ... boss_ss() ...` that is exactly where the ambient read
happens; written that way the tripwire reports nothing for `simp`.  It is
`Context.in_proof (fn () => tac g ctxt) ()`.

**Levels, and why the default is not "warn on every read".**  0 silent,
1 one report per theory (default), 2 every read, 3 error.  Reporting every
read means 611k lines across a core build and about a tenth of the
build time of its heaviest theory; one marker per theory log still says
which theories offend, which is what a ratchet needs.  Level 2 gives the
full count when you want to measure.

### Core-build census

| measure                                             |   count |
|-----------------------------------------------------|---------|
| ambient reads inside a proof (trace at 2)            | 611 424 |
| theory logs carrying at least one                    |     100 |
| theory logs carrying at least one (trace at 1)       |      96 |

Heaviest logs, all of them proof-heavy set/list/arithmetic theories:
`cardinal` (100 436), `pred_set` (83 274), `wellorder` (70 883),
`set_relation` (67 415), `rich_list` (39 644), `ordinalBasic` (39 586),
`list` (35 992), `iterate` (23 652), `logroot` (23 084), `gcd` (16 962).

### What is doing the reading

Setting the trace to 3 makes the first read raise, so a tactic either
completes or is named.  Probing the common ones (only *clean* and
*ambient* are conclusive --- a tactic that does not close the goal is
inconclusive):

| tactic                        | reads ambient state |
|-------------------------------|---------------------|
| `ACCEPT_TAC`, `REFL_TAC`, `STRIP_TAC` | no          |
| `REWRITE_TAC []`              | no                  |
| `SIMP_TAC bool_ss []`         | no                  |
| `DECIDE_TAC`                  | no                  |
| `ASM_REWRITE_TAC []`          | yes                 |
| `simp []`, `rw []`, `fs []`   | yes                 |
| `EVAL_TAC`                    | yes                 |
| `GEN_TAC`                     | yes                 |
| `Induct_on`, `Cases_on`       | yes                 |
| `Q.EXISTS_TAC`                | yes                 |

Two of these are worth calling out.  `SIMP_TAC bool_ss []` is clean while
`simp []` is not, which is the thesis of this document in one line: the
simpset passed explicitly is fine, the stateful wrapper around it is the
problem.  And **`GEN_TAC` reads ambient state** --- it chooses its variant
with `gen_variant Parse.is_constname`, which consults the ambient term
grammar.  That is the bug this whole change exists to fix, still live, and
now named by the tripwire; it is the obvious first target for Phase 3.

The rest of the table maps onto the phases as written: `simp`/`rw`/`fs`
are 3a, `EVAL_TAC` and `ASM_REWRITE_TAC` are 3b, `Induct_on`/`Cases_on`
(TypeBase) and `Q.EXISTS_TAC` (parsing in a tactic body) are 3c.


## Hand-off notes (guest VM)

This plan is written to be executed by a fresh session with no
conversation context, in the OrbStack VM described by
`developers/claude/LOCKED-VM.md`.  Consequences that shape the work:

- The repo is mounted at **`/repo`**; worktrees live at
  `/repo/.claude/worktrees/<name>/`.  Create them as the default user,
  then run Claude as the `claude` user.
- **Each worktree needs its own `poly < tools/smart-configure.sml`
  inside the VM** — the macOS-side `bin/Holmake` is Mach-O and will not
  run there.  The tree as handed over has a macOS `bin/Holmake` and no
  `bin/hol.state0`, so configuring is unconditionally the first step.
- **`git commit` works; `git push` and `gh` do not** — GitHub is
  firewalled.  The deliverable is commits on a branch in the mounted
  tree; pushing and PR creation happen from macOS afterwards.  Do not
  plan any step that needs network access.
- **Do not pass `isolation: "worktree"` to the Agent tool** inside the
  VM: git's per-worktree state sits on the read-only side of the bind
  mount and any lockfile write fails with EROFS.  Plain subagents are
  fine.
- Commit this plan into the repo as
  `developers/discussion/context-passing-tactics.md`, alongside the
  existing `prove-without-current-theory.md`, so the VM session can read
  it without depending on anything outside the tree.

## Decisions taken

These were settled in design discussion and are not open.  Where a
decision reverses an earlier instinct, the reasoning is kept, because
the reasoning is what makes it re-derivable.

**Shape of the change**

1. **Conversions keep `conv = term -> thm`.**  A conversion must not
   read ambient state; state it needs is passed explicitly.  Corollary
   adopted in preference to a mechanism: **registered/captured
   conversions must be state-free**, full stop.  No `state -> conv`
   registry redesign — `add_conv` and `convdata` keep their signatures,
   and the few conversions that do read ambient state
   (`patternMatchesLib.sml:985` via `rc_ss`, `realSimps.sml:991`) are
   treated as defects and fixed individually.  The tripwire enforces
   this for free: a violation *is* an ambient read inside a proof.
2. **Pass the specific state, not the whole context**, to anything
   below the tactic.  So `TypeBase`'s consumers take a `typeBase`
   (threaded from the tactic that holds the context), not a
   `Context.t`; `TypeBasePure.*` already takes one.
3. **Argument order is `goal -> Context.t -> ...`,** ctxt last, so
   existing `fun FOO (asl,w) = ...` definitions gain a parameter rather
   than being rewritten.
4. **`prove` stays ambient; `prove_in` is explicit.**
   `prove_in : Context.t -> term * tactic -> thm`, with
   `fun prove (t,tac) = prove_in (Context.snapshot()) (t,tac)`.  This
   keeps the historical spelling and means **none of the 5488 raw call
   sites need editing**.  Same shape for `prove_goal`/`store_thm`.
5. **The expander emits `Context.snapshot ()`** — no named read seam.
   Capture happens at the prover hook (below), so the expander's only
   job is to supply a context.  `Context.install` still exists, for
   workers.
6. **Every tactic-bearing surface form changes at once.**  Half-
   parameterised is worse than either end.

**Concurrency**

7. **The live context cell becomes thread-local, with
   install-and-never-restore.**  A worker installs its snapshot and
   runs; nothing needs undoing afterwards, because a tactic's type
   gives it no way to return a modified context.  This is *not* the
   dangerous use `Context.sig` warns about (issue #2025): that warning
   is about `restore` used to rewind to an earlier epoch, whereas a
   fresh worker thread is merely initialising.
   Two qualifications: the "tactics don't mutate" premise is
   established *by* this migration and is convention rather than a type
   guarantee, so this is safe only from the end of Phase 3; and
   `ThreadLocal.get` yields `NONE` on a fresh thread, so the install
   point must raise a clear error rather than let a worker run against
   a minimal grammar.
8. **Parallel replay is therefore ungated by the census.**  Residual
   ambient reads on a worker are correct once the cell is thread-local,
   so replay switches on at the end of Phase 3 and the census continues
   as a style ratchet rather than a gate.
   *Why the explicit parameter is still worth having, given the above:*
   thread-locality only *isolates* a mutable global — each thread still
   has a drifting cell, so it does not fix the original load-order bug.
   The parameter freezes a proof's inputs, keeps `restore` off the
   proof path entirely, and preserves a forcing function.
9. **Two prover modes, selected by whatever the driver installs via
   `set_prover` — not by `TAC_PROOF`.**  `TAC_PROOF` stays "actually
   prove this".  The modes are *defer* (LSP Phase A: enqueue
   `{site, ctxt, goal, tac}`, return an oracle placeholder) and *run*
   (batch, and Phase B workers).  Phase B is not a third mode; a worker
   is just running the proof.  **Workers must call the unhooked entry
   (`TAC_PROOF`) directly**, or they re-enter the deferring hook and
   enqueue themselves forever.
10. **Termination proofs use the same machinery**, not a special case.
    They only look separate because `Defn.tprove2` goes through
    `proofManagerLib.expand` and `TotalDefn.proveTotal` through
    `default_prover`, neither of which is hookable.  Route both through
    `prove_goal` and the deferring prover handles them like anything
    else.  Definition principles themselves still *run* — they must, to
    determine the output statements, and they are quick; it is only the
    termination proof that is deferred.

**Enforcement and scope**

11. **Enforcement is staged like the `getCT()` check**: a thread-local
    "inside a parameterised proof" flag makes `Context.snapshot()`
    warn, then raise.  Same playbook as
    `prove-without-current-theory.md`, which took that class from 3422
    warnings to 0.
12. **Behaviour-affecting flags move into the context immediately;
     printing flags follow later, as one bundle.**  A flag that can
    change a proof's outcome while living outside the context
    falsifies the whole thesis.  Printing/display flags — which is most
    of `Feedback`'s traces — migrate as a follow-up task, landing as a
    single bundled record in one slot rather than twenty slots.
13. **`suspend`/`Resume` divergence is accepted**, reusing the existing
    `Holmake --fast` tolerance.  The placeholder context is strictly
    more permissive, so the worst case is the IDE accepting a citation
    a real build would reject — a false positive in an optimistic tool.
14. **Simplifier caches stay process-global.**  Cross-context reuse is
    sound (theorems are context-independent) and false hits are
    impossible (`Term.compare` compares kernelids, so same-named
    constants from different contexts are different keys), and they are
    already `Sref`-locked.  The only artefact is a cached *failure*
    being reused where another context would have succeeded.
15. **Delete `Context.Data.register`** (`Context.sig:96`): zero callers,
    and it exists to make the ambient idiom convenient.  If something
    wants it later, add it in ctxt-taking form.

## Scale (measured in this tree, `src` + `examples`)

| proof sites                                  | count  | manual edits |
|----------------------------------------------|--------|--------------|
| `Theorem … QED` blocks                        | 56228  | none\*       |
| `Definition … End` blocks                     | 12738  | none         |
| `Termination` clauses                         | 205    | none         |
| raw `prove`/`store_thm`/`TAC_PROOF` in `*Script.sml` | 4951 | none (see below) |
| ditto in library `*.sml`                      | 537    | none (see below) |
| files defining tactics (`src` only)           | 56     | yes          |
| files defining conversions (`src` only)       | 48     | yes          |

The first three rows are why the expander is the right lever: **69k proof
sites acquire a context with no source edit at all.**

\* Bar one narrow exception, found while landing Phase 0: a proof body
that defines its own tactic helper and catches its failure needs the
context threaded like any library code.  Five such sites exist across
`src` and `examples`.

### The compatibility layer that keeps the other 5.5k untouched

Because the live cell is thread-local (decision 7), an ambient-reading
entry point is still correct:

    (* explicit *)  val prove_in : Context.t -> term * tactic -> thm
    (* ambient   *)  fun prove (t, tac) = prove_in (Context.snapshot ()) (t, tac)

A raw `prove (t, tac)` at the top level of a Script file then reads the
context installed for *this thread* — right answer under Holmake, and
right answer under an LSP worker elaborating that file.  So none of the
5488 raw call sites need editing, and `prove`'s historical spelling
survives.

The tripwire's discriminator (Phase 2) is what keeps this honest: an
ambient read at declaration level is the wrapper doing its job, while
one reached *inside a running proof* is flagged, because that code had
a context in scope and dropped it.

## The mechanical pattern (established in `c49daab01`; follow it)

Tactic that ignores the context — append an ignored parameter:

    val CONJ_TAC : tactic = fn (asl, w) => fn (_ : Context.t) => ...
    fun DISJ1_TAC (asl, w) (_ : Context.t) = ...

Combinator — append and pass down, never re-snapshot:

    fun (tac1 ORELSE tac2) g ctxt = tac1 g ctxt handle HOL_ERR _ => tac2 g ctxt

Tactic that *needs* state — extract from ctxt, hand explicitly to the
conversion, which stays a plain `conv`:

    fun simp_tac_from ctxt = SIMP_CONV (simpset_of ctxt) ...

**Gotcha, and the reason for the annotation above.** Writing the ignored
parameter as bare `fn _ =>` leaves its type free, so the function
generalises and value aliases stop typechecking.  That is why
`c49daab01` had to add `val disj1_tac : tactic = DISJ1_TAC`
(`src/1/Tactic.sml`) and `val NULL_OK_LT : list_tactic -> list_tactic =
NULL_OK_LT` (`src/1/Tactical.sml`).  Annotating the ignored parameter
`(_ : Context.t)` at the definition avoids the whole class; chasing it
via downstream annotations does not scale to 56 files.  Prefer the
annotation at the binding site.

## Phases

Each phase ends with a green core build.  Do not start the next phase
with the tree red.

### Phase 0 — baseline, then the ctxt-taking accessor layer

1. Configure the worktree and drive `src/1` back to compiling (see
   **Starting state**).  Confirm a green core build before going
   further — every later phase assumes it.
2. For every ambient accessor, add a `Context.t`-taking sibling and
   redefine the ambient one in terms of it.  `src/parse/Parse.sml`
   already shows the shape:

       fun get_term_grammar ctxt = Context.Data.get term_grammar_slot ctxt
       fun term_grammar () = get_term_grammar (Context.snapshot())

   Purely additive: new `.sig` entries, no call-site churn, no
   behaviour change.  This phase is mechanical and is what makes every
   later phase possible.

**32 ambient-read sites across 20 files; 2 done (both in `Parse.sml`),
30 to go.**  Do them in this order, because the leverage is very
unevenly distributed:

1. **`src/parse/AncestryData.sml`** (`:151`, `:256`, `:266`) — by far
   the highest leverage.  `get_global_value` is one line of source but
   *N* logical ambient accessors, one per `make`/`fullmake` client, and
   the clients are most of the rest of the list: `TypeBase`
   (`:117`, i.e. `theTypeBase`), `ThmSetData` (`:277`, the engine
   behind every `export_simple_dictionary`/`export_alist` client),
   `computeLib` (`:451`), `transferLib` (`:831`), `markerLib`
   (`:1016`, `:1093`), `DefnBaseCore` (`:255`), `bnfBase` (`:89`),
   `combinpp` (`:85`), `ConstMapML` (`:151`), `EmitML` (`:271`), and
   `Parse` (`:1099`).  Give the returned records ctxt-taking variants
   and a dozen client families follow.
2. **The four kernel signature readers** — `src/0/Term.sml:32`,
   `src/0/Type.sml:29`, `src/experimental-kernel/Term.sml:37`,
   `src/experimental-kernel/Type.sml:14`.  Highest fan-out of all
   (every `mk_const`/`decls`/`uptodate_*`), and each file has a long
   tail of internal ambient consumers to thread through
   (`term_epoch`, `display_name_of_id`, `inST`, `all_consts`, …).
   Note both kernels must move together.
3. **`Thm.getCT`** — `src/thm/std-thm.ML:1275` and
   `src/thm/otknl-thm.ML:1362`.  Edit those, **not** `src/thm/Thm.sml`,
   which is generated by `src/thm/Holmakefile` and gitignored.
4. The rest: `Theory.sml` (6 sites), `DB.sml:114`, `Ho_Rewrite.sml:71`,
   `PmatchHeuristics.sml:326`, `ThmAttribute.sml` (3),
   `ThmSetData.sml:110`, `TypeBase.sml:103`, `simpLib.sml:137`,
   `BasicProvers.sml` (3), `computeLib.sml:325`,
   `transferLib.sml:721`, `proofManagerLib.sml:26`.

Two clean-ups belong here.  **Delete `Context.Data.register`**
(`Context.sig:96`, decision 15): it is documented as the convenience
wrapper for *exactly* the ambient idiom and has zero callers, so
deleting it stops anything adopting it later and baking the ambient
read back in.  If something wants it, add it in ctxt-taking form.
And `src/1/Rewrite.sml:82`'s
`implicit = ref empty_rewrites` is still a plain `ref`, unlike its
`Ho_Rewrite` counterpart — migrate it to a `Context.Data` slot so the
two are symmetric.

_Check_: core build green; the diff adds signature entries and touches
no call sites.

### Phase 1 — entry points, `Parse`'s caches, and every expander site

1. `Tactical`: split explicit from ambient — `prove_in : Context.t -> …`
   with `prove` retained as the ambient wrapper (decision 4; this is
   what saves the 5488 raw call sites).  Likewise `prove_goal`/
   `store_thm`.
2. `boolLib.store_thm_at` takes a `Context.t` instead of reading
   ambient state, and `Q.store_thm_at` uses it for the **quote parse**
   as well as the proof.  Parsing the statement against one context and
   proving it against another is the exact defect this whole change
   exists to close.
3. Move `Parse`'s memoised parser/printer closures into the context.
   `src/parse/Parse.sml:138-150,281` keeps them in plain `ref`s
   (`type_parser1`, `type_parser2`, `the_absyn_parser`,
   `grammar_term_printer`, …), rebuilt only when the
   `*_grammar_changed` flags flip (`:307-318`); the comment at
   `:296-306` already admits they can hold a stale grammar.  Left
   alone, a context-explicit parse routed through `Parse.Term` would
   silently read the cached closure and ignore the context handed in.

   Store them as `Susp.susp` in a `Context.Data` slot — the same
   pattern as the derived values in Phase 3a.  The cache then cannot be
   stale relative to its context, `Parse.Term` becomes
   correct-by-construction for a given context (so nothing needs to
   bypass to `TermParse`), and **`Parse.invalidate_caches` disappears
   entirely** — including the call in `tools-poly/hol.ML:614-628`'s
   `compileSnap` restore thunk.
4. `tools/parsing/HOLSourceExpand.sml`: add the context argument at
   every tactic-bearing surface form, together.  The runtime targets and
   their current signatures:

   - `Theorem … Proof … QED` → `Q.store_thm_at` (`Q.sig:50`)
         `DB.thm_src_location -> string * tmquote * tactic -> thm`
   - `Definition … Termination t End` → `TotalDefn.located_qDefine`
     (`TotalDefn.sig:47`)
         `… -> string -> term quotation -> tactic option -> thm`
   - `[Co]Inductive` → `IndDefLib.xHol_reln` (`IndDefLib.sig:12`)
         `string -> term quotation -> thm * thm * thm`
   - `Resume … QED` → `markerLib.resume` (`markerLib.sig:112`)
         `{suspension_name, label_name} -> tactic -> thm`

   All four are already curried, so appending a final `Context.t`
   argument is natural and matches the anchoring advice above.
   `xHol_reln` needs one because it both parses a quote and proves
   internally.

   **Two forms need no change**, and saying so keeps "everything at
   once" from over-scoping: `Theorem foo = e` (`HOLSimpleThm` →
   `boolLib.save_thm_at`) and `Finalise` (→
   `markerLib.finalise_suspended_thm`) neither parse a quote nor run a
   tactic.

   **`wrapTac` type-checks but is now semantically wrong — fix it here.**
   `wrapTac` (`HOLSourceExpand.sml:74`) emits `fn g => tac g`, which
   still has tactic type, so nothing complains.  But:

   - Its purpose is to defer evaluation until the goal arrives, so HOL
     exceptions surface inside `Q.store_thm`'s error wrapping.  Under
     the new type `tac g` is a *closure awaiting the context*, so the
     deferral no longer covers the tactic's own execution.
   - Worse, **`Proof[exclude_simps=…]` silently stops working.**
     `doProofKvals` wraps the result in `BasicProvers.with_simpset_updates
     f g x` (`BasicProvers.sml:1257`), which holds a temporary simpset
     via `AncestryData.with_temp_value` around the call `g x`.  With
     `g = fn g => tac g` and `x` the goal, `tac goal` merely *builds the
     closure* — the closure's body then runs **outside** the
     `with_temp_value` window, so the excluded simps are back in scope
     by the time the tactic executes.

   **The `exclude_simps` half is fixed properly, in Phase 3a**, by
   making `with_simpset_updates` a *context transform* rather than a
   global clobber — adjust the simpset inside the `Context.t` and every
   simpset-user within the tactic picks it up, with no scoping window
   to get wrong.  Do not paper over it with an arity patch here.

   **The exception-surfacing half remains and is separate.**  Even with
   the attribute fixed, `fn g => tac g` now returns a closure, so HOL
   exceptions raised while the tactic consumes its context surface at a
   different point than before.  If that matters, eta-expand on both
   arguments (`App (App (tac, gDummy), cDummy)`); each new synthetic
   identifier needs its own span per the discipline below, since
   `wrapTac`'s existing dummies are deliberately one byte wide and sit
   at `expStop tac`.  Either way, add a regression test for
   `Proof[exclude_simps=…]` — nothing currently catches it.

5. Fix the call sites still using the old arities, which the type
   change has already invalidated: `boolLib.sml:257`
   (`Tactical.prove(t,tac)`), `Q.sml:66`, `TotalDefn.sml:536,638`,
   `bossLib.sml:140` (`cheat`), `holmakebuild.sml:9-10`,
   `fastbuild.sml:18-24` (old-arity provers handed to `set_prover`),
   `IndDefLib.sml:473-485` (`genify_tac`, old style), and
   `goalFrag.sig:15-18`/`goalFrag.sml:58-61` (`expand : tactic ->
   frag_tactic`, which composes `o tac` at the old type).  `goalFrag`
   matters out of proportion to its size — see Phase 4.

   Span discipline, and it matters: that file documents hover
   navigation breaking when synthetic argument spans overlap — see the
   `tacAnchor` comment and the `mkTuple` stop comment.  Add the context
   as a **curried argument anchored at the tuple's stop**, not as an
   extra tuple element anchored at `theorem_`, or `findChild` will
   resolve cursor hovers inside `Proof … QED` to the wrong node.

_Check_: core build green; expansion-printing and the LSP tests under
`tools-poly/lsp/tests`; hover navigation inside a `Proof … QED` block
still resolves to tactic identifiers.

### Phase 2 — the enforcement tripwire (warning-only)

`TAC_PROOF` sets a thread-local "inside a parameterised proof" flag
(`ThreadLocal`, per Phase 4's reasoning); `Context.snapshot ()`
consulted while it is set reports.  Trace-controlled, defaulting to
warn, exactly as `prove-without-current-theory.md` staged its `getCT`
check.

The discriminator is what makes this work, given that `prove` remains
ambient (decision 4):

- `Context.snapshot ()` at *declaration* level → fine, that is the
  ambient wrapper doing its job.
- `Context.snapshot ()` reached **while a proof is running** → flagged:
  that code had a context in scope and dropped it.

A nested `prove` inside a tactic or conversion hits the second case,
which is precisely the bug class being closed.  Ambient reads are not
banned outright — they are banned *inside a proof*, which is checkable.
This is also what enforces the state-free-conversion invariant
(decision 1) for free.

Then take a census over a core build and record it in that memo's
style — a table of counts plus the most-repeated offenders.  Markers
land in each directory's `.hol/logs/*`, not on the build's stdout;
collect with `grep -ra`.

Per decision 8 this is a **style ratchet, not a gate**: Phase 4 does
not wait on it.  Flip warn → error when the count reaches zero.

_Check_: build green with warnings only; census table committed.

### Phase 3 — plumb tactics and conversions

Work the census down.  Conversions keep `conv = term -> thm`; a
conversion needing state becomes `state -> conv` applied at tactic
level.  Four groups, in this order.

#### 3a. The simpset — one line, then two obstacles

The whole chain is: `bossLib.simp` = `stateful asm_simp_tac []`
(`bossLib.sml:391`) → `boss_ss()` → `make_simpset_derived_value`'s
`get` (`BasicProvers.sml:1391`) → `srw_ss()` (`:1253`) →
`AncestryData.get_global_value` (`AncestryData.sml:249`) →
`Context.Data.get global_slot (Context.snapshot())`.  Below the
tactic, `ASM_SIMP_TAC ss` (`simpLib.sml:902`) → `SIMP_CONV ss`
(`:868`) already takes the simpset explicitly.

**The minimal seam is a single line — `bossLib.sml:389`:**

    fun stateful f ssfl thms : tactic = fn g => fraglistify f (boss_ss()) ssfl thms g

`stateful` is bossLib-local and is the sole funnel for `simp`, `dsimp`,
`csimp`, `rw`, `fs`, `rfs`, `lrw`/`lfs`/`lrfs`, and
`gs`/`gvs`/`gns`/`gnvs`/`rgs` (`bossLib.sml:391-412`).  Threading a
context through that one line converts all of them.  It needs three
context-explicit twins: `srw_ss_of : Context.t -> simpset`
(`BasicProvers.sml:1253`), `make_simpset_derived_value` returning
`get : Context.t -> 'a` (`:1376`), and an `AncestryData`
`get_global_value_of : Context.t -> 'value` (`AncestryData.sml:249`).
Then `SRW_TAC` (`BasicProvers.sml:1320`) separately.

**The two real obstacles are caching, not signatures:**

- `srw_ss ()` *mutates before reading* — `update_global_value
  init_state` (`:1254`) lazily initialises.
- `make_simpset_derived_value`'s `get` (`:1391-1396`) does a
  read-modify-write on the *live* context (`Context.Data.modify vslot`,
  `Context.Data.write staleslot`), so it is not a function of a
  `Context.t` at all.  Its `empty` is also eagerly evaluated as
  `deriver (srw_ss()) init` at slot-creation time (`:1382`), baking in
  the boot-time simpset.

**Resolution: hold a suspension in the slot.**  A context cannot change
under a tactic, so a derived value *is* a pure function of it and no
staleness tracking is needed inside a proof.  Use `Susp`
(`src/portableML/poly/Susp.sig`: `delay`/`force`, evaluate-at-most-once
— a backfill of the Moscow ML basis unit, which is why there is no
`mosml/` copy, so it is portable):

- `get : Context.t -> 'a` is `Susp.force (Data.get vslot ctxt)` — a
  pure read, memoised per context.
- Whatever adjusts the simpset installs a *fresh unforced* suspension
  in the returned context, so the `stale_flags` registry
  (`BasicProvers.sml:1171`) becomes a list of `Context.t -> Context.t`
  instead of closures writing the live context.  **The stale-flag
  mechanism disappears rather than being ported** — which is what
  unblocks the context transform below.
- `empty = Susp.delay (fn () => …)` is unforced, so the eager
  boot-time-simpset problem at `:1382` also goes away.
- Caveat to record: `Susp.force` is an unlocked `ref` update, so two
  threads forcing the same suspension both compute and one assignment
  wins.  Benign — the derivation is deterministic and the write is a
  single ref assignment — but state it rather than let it be
  discovered.

**Then `Proof[exclude_simps=…]` becomes a context transform.**  It
currently works by save/clobber/restore of the global slot plus two
`notify()` calls (`with_simpset_updates`, `:1257`; `mk_tacmod`,
`:1404`).  Because a `Manager.tacmodifier` is `tactic -> tactic` and
`tactic` now carries a context:

    fun with_simpset_updates f tac = fn g => fn ctxt => tac g (map_simpset f ctxt)

Every simpset-user within the tactic picks up the adjusted value, there
is no scoping window to get wrong, and the attribute stops being a
global clobber entirely.  This is also the proper fix for the
`wrapTac` breakage noted in Phase 1.

**One case does need churn below the tactic: `SF`.**  `SIMP_CONV`
(`simpLib.sml:868`) → `process_tags` (`:843`) → `extract_frags`
(`:818-828`) → `lookup_named_frag` (`:150`) → `ssfragDB()`, i.e.
`SF "ARITH"` markers in the theorem list are resolved *inside the
conversion*, on every call.  Verified directly:
`fun SIMP_CONV ss l tm = let val (ss', l') = process_tags ss l in …`.

**`Excl`/`ExclSF` are not affected** — `extract_excls` (`:808-816`)
works purely on names via `destExcl`/`destExclSF` and feeds name-based
simpset operations (`remove_ssfrags`, `-*`), touching no DB.  `SF` is
the odd one out because it is the only marker taking an ssfrag *value*
rather than a string, and a value cannot travel through a `thm list` —
hence the name round-trip through the DB.

The fix is **hoisting, not threading**.  `process_tags` consumes the
theorem list, a tactic-level argument (`ASM_SIMP_TAC ss ths`, `:902`),
so lift it to the tactic — where a context is in scope — and give the
conversion a pre-resolved simpset and theorem list:

    fun SIMP_CONV' (ss, l) tm = TRY_CONV (SIMP_QCONV ss l) tm
    fun SIMP_CONV ss l tm = SIMP_CONV' (process_tags ss l) tm   (* compat *)

`process_tags` returns its arguments unchanged when no markers are
present, so the fast path is untouched.

**`SF` loses its auto-registration.**  Today, given an unregistered
fragment, `SF` (`:830`) registers it and warns that the registration
will not survive theory export.  That becomes an error instead:
lookup-only, fail if unregistered.  This is a deliberate, accepted loss
— and arguably an improvement, since the current behaviour is already a
footgun that warns about itself.

### Starting notes for 3a

Groundwork done: `AncestryData` has `get_global_value_of`, so the bottom
of the chain is reachable from a context, and `GEN_TAC` is off the census.
Four things worth knowing before the simpset itself:

**The derived value does not consult its previous value.**
`make_simpset_derived_value`'s `deriver` has type `simpset -> 'a -> 'a`,
but its only client is `bossLib`'s `boss_augment ss old = addfrags
let_arith_frags ss`, which ignores `old`.  So the derived value *is* a
function of the simpset, the `'a -> 'a` shape is vestigial, and the
suspension can be `Susp.delay (fn () => deriver (srw_ss_of c) init)`
without having to force the previous one to build the next.

**`srw_ss_of` need not mutate.**  `srw_ss ()` is
`update_global_value init_state; #1 (get_global_value())`, but
`init_state : srw_state -> srw_state` is already pure --- it folds the
pending updates into the simpset and marks it initialised.  So
`fun srw_ss_of ctxt = #1 (init_state (get_global_value_of ctxt))` reads a
context without writing one.  On an already-initialised context it returns
immediately; on an uninitialised one it redoes the fold per call, which is
what the suspension in the slot is for.  Note `init_state` also reads
`tyinfol()`, so it stays on the census until 3c.

**Installation has to happen inside the transform that adjusts the
simpset, not as a nested update.**  `RWLock.acquire_read` waits while a
writer is queued, so a `Context.update` reached from inside a
`Data.modify` callback can deadlock against a concurrent `restore`.
`(update_global_value f; notify())` must therefore become one transform
--- `Context.update (install_derived o Data.update global_slot f)` ---
rather than an adjust followed by a nested install.  Today's `notify()`
already writes a slot from inside `AncestryData`'s `apply_to_global`
callback, so this nesting exists already and has not bitten a
single-threaded build; the point is not to build more of it.

**Keep the ambient `boss_ss()` cached.**  `simp` resolves its simpset per
invocation, so dropping the memoisation to get a context-explicit read
would pay `addfrags` on every call.  The suspension-in-a-slot is what
keeps both properties: pure read, computed at most once per context.

### What 3a landed, and what it left

The seam went in as written.  `AncestryData` gained
`update_global_value_of : ('value -> 'value) -> Context.t -> Context.t`,
so ancestry-backed state can be adjusted *in* a context rather than
around a call; `srw_ss_of` reads a context without writing one; and
`bossLib`'s `stateful` --- still the single line behind `simp`, `dsimp`,
`csimp`, `rw`, `fs`, `rfs`, the `l`-prefixed aliases and the `g`-family
--- resolves its simpset from the context the tactic is run in, as do
`SRW_TAC` and `fsrw_tac`.

The `stale_flags` registry became a registry of *installers* and the
derived value became an unforced `Susp` in its slot, as planned, with
two adjustments worth recording:

**The slot holds an option, and `NONE` is not a stale value.**  A slot's
`empty` is what a context that predates the slot reads, and there is no
way to ask whether a slot was ever written.  With a suspension as
`empty`, that context would derive from whatever state the suspension
was built over --- `state0`, say --- rather than from its own simpset,
which is wrong for any context snapshotted before the derived value
existed.  `'a Susp.susp option` with `empty = NONE` makes the question
askable: `NONE` means *no memo for this context*, and the answer is
derived from the context's own simpset, unmemoised.  Correct everywhere;
the unmemoised path is reachable only during the boot that creates the
slot.

**Installers are correctness-critical, exactly as `notify()` was.**  A
missed installation site does not merely lose memoisation --- it leaves a
suspension over a superseded state.  The installer set is therefore the
old `notify()` set, one for one, and comes in two forms because the
simpset is adjusted from two kinds of place: `put`, a pure transform for
top-level adjustments, and `write`, for the paths reached from inside
AncestryData's own callbacks (`apply_to_global`, `finaliser`), which
already hold the global slot's lock and must not open a nested
`Context.update`.  Both are handed the new state rather than reading it
back, so neither depends on when it runs relative to the adjustment.

**`srw_ss ()` now installs when it initialises.**  It used to call
`update_global_value init_state` bare.  Under suspensions that is a
trap: the global state becomes initialised while every derived value
stays suspended over the uninitialised one, so each repeats the fold ---
and reaches `tyinfol()` --- every time it is forced.  It now
initialises through `updnote_global_value`, and only when the state is
not already initialised.

#### `exclude_simps` keeps its window, for now

The plan had `Proof[exclude_simps=…]` stop being a global clobber
outright.  It does not, yet.  `with_simpset_updates_tac` now transforms
the context *and* keeps the ambient window, because a tactic that names
`srw_ss()` itself --- `SIMP_TAC (srw_ss()) ths`, of which the tree has
many --- still reads the ambient simpset, and dropping the window would
silently stop honouring the attribute for all of them.  A silent change
of that shape is worse than a retained clobber.  `exclSimpsScript` now
tests both paths (`foo` ambient, `foo_ctxt` context-carried) rather than
only the one that happened to be there.  The window goes when the census
has retired the ambient readers.

#### Measured: the stateful family is down to `tyinfol()`

Probing at trace level 3, in a fresh process, with `srw_ss()` forced
before the tripwire is armed so that what it reports is the tactic and
not the one-off initialisation:

| tactic                        | before 3a | after 3a  |
|-------------------------------|-----------|-----------|
| `simp []`                     | ambient   | **clean** |
| `fs []`, `gvs []`             | ambient   | **clean** |
| `asm_simp_tac (srw_ss()) []`  | ---       | clean     |
| `ASM_REWRITE_TAC []`          | ambient   | clean     |
| `rw []`                       | ambient   | ambient   |
| `srw_tac [] []`, `SRW_TAC [] []` | ambient | ambient   |
| `EVAL_TAC`                    | ambient   | ambient   |

Every read left in this family is `tyinfol()`, from two sites and no
others: `init_state`, reached lazily when a derived value's suspension is
first forced, and `PRIM_STP_TAC`'s `mkCSET ()` (`:1006`), which is why
the `PRIM_SRW_TAC` family (`rw`, `srw_tac`, `SRW_TAC`) is still on the
list while `simp` is not.  `STP_TAC` (`:1096`) calls `tyinfol()` outright
as well.  So the simpset is done and **TypeBase is the whole of what
remains here** --- which argues for taking 3c before 3b.  `EVAL_TAC` is
unrelated: that is `the_compset()`, and it is 3b as written.

Two traps in measuring this, both of which produced wrong readings first:

- **Probes in one process contaminate each other.**  An earlier tactic
  initialises the state a later one would have read, so the later one
  reads clean.  `fs []` measured clean purely because `simp []` ran
  before it.
- **At level 3 the report is an exception, so it aborts the force.**  A
  suspension whose forcing trips the tripwire is never memoised, so the
  *same* read reports again on every subsequent proof.  Repeated reports
  are not evidence of repeated read sites.

The core-build census is not comparable across this phase as it stands:
`.hol/logs` accumulates logs from earlier builds, and an incremental
build rewrites only what it rebuilt, so a walk of the tree mixes
generations.  Filter by mtime against the build, or clear the logs
first.


### The kernel signature is a separate population

`mk_type` and `mk_const` resolve a *name*, and they resolve it against
`Type.typesig()` / `Term.termsig()` --- which were
`Context.typesig (Context.snapshot())`.  So every name-based term or
type construction inside a proof was an ambient read, and no amount of
tactic-level plumbing removes it: it is the `uptodate_term` threading
item, recorded separately as not urgent.  Left in the census it would
peg the count permanently above zero and bury the reads Phase 3 exists
to find.

`Context.live : unit -> t` now reads the live context without reporting,
and the two kernels' `typesig`/`termsig` use it.  It reports under its
own trace, `"ambient signature inside proof"`, same levels, silent by
default.  **This is a scoping decision, not a fix.**  A tactic that
parses still takes its grammars from the supplied context and its
constants from the live signature, and if those diverge --- a restored
older context --- that is a real inconsistency.  The signatures say so.

#### Where the calls are

1019 calls to `mk_type` / `mk_thy_type` / `mk_const` / `mk_thy_const` /
`prim_mk_const` across `src`, `examples` and `tools`:

| | sites |
|---|---|
| load-time `val` binding | 615 |
| deferred, name is a string literal | 188 |
| deferred, name is dynamic | 216 |

The 615 are the `*Syntax.sml` tables --- `val cons_tm = prim_mk_const
{Name = "CONS", ...}` --- resolved once when the module loads.  They
never run inside a proof and do not matter.

The **literal-name** 188 do run inside proofs, and measurably so:
probing at signature-trace level 3, `PairRules.NOT_PFORALL_CONV`,
`PFORALL_AND_CONV`, `CURRY_CONV`, `ListConv1.LENGTH_CONV`,
`APPEND_CONV` and `numLib.REDUCE_CONV` all report.  But they are looking
up a *fixed, well-known* constant on every call ---
`mk_const("!", ...)` in `PairRules`, `mk_const{Name = "NIL", ...}` in
`ListConv1`, the numeral constructors in `Literal`.  **These do not want
a context; they want hoisting to a load-time constant**, exactly as the
syntax libraries already do.  A local cleanup, no plumbing, and it
removes them from the census outright.

The **dynamic-name** 216 are the ones where which signature you ask
genuinely matters.  Only 121 are in `src` at all, and they sort as:

- kernel internals (`0/Term`, `0/Type`, `experimental-kernel`) --- the
  constructors themselves and their internal plumbing, not callers;
- `src/parse` (`Overload`, `Parse`, `GrammarDeltas`, `term_pp`,
  `parse_bnf`) --- **parsing**, the systematic case;
- definition machinery (`ind_types`, `Datatype`, `RecordType`,
  `quotient`, `DefnBaseCore`) --- runs at definition time, at the top
  level, not inside a proof;
- prooftrace replay and the holyhammer/pfl exporters --- neither runs
  inside a proof.

So the dynamic reads that actually fire inside a proof are parsing, and
the probes agree: of the tactics measured, the ones reaching the
signature are exactly the quotation-parsing ones --- `Cases_on`,
`Q.EXISTS_TAC`, `Q.ABBREV_TAC` --- while `simp`, `rw`, `gvs`,
`DECIDE_TAC`, `ARITH_TAC`, `EVAL_TAC`, `Induct`, `Induct_on`,
`STRIP_TAC` and `REWRITE_TAC` are clean.

**Consequence for the plan.**  Threading a context into the parsing
functions, so they resolve names against the signature of the context
they are parsing in, covers the whole dynamic population; the
literal-name conversions are a separate hoisting pass.  Neither is
needed for Phase 3 to finish, and both are measurable independently now
that the trace is split.

#### 3b. Pure plumbing (state already an explicit parameter below)

Each is an ambient read whose state is already an explicit parameter of
something lower down:

- `EVAL_TAC`/`EVAL_CONV` — reads `the_compset()`
  (`computeLib.sml:325`); `CBV_CONV : compset -> conv` already takes it
  (`computeLib.sig:29`).
- `Ho_Rewrite.REWRITE_*` — reads `implicit()` (`Ho_Rewrite.sml:71`);
  `GEN_REWRITE_CONV'` (`:122`) already takes it.
- `transferLib.xfer_tac` — reads `global_ruledb()` (`:721`);
  `transfer_tm` (`:700`) already takes it.
- The five `DatatypeSimps.*_stateful_ss` — read `TypeBase.elts()`
  (`:334,375,387,404,414`); the `_typeinfos_ss` variants already take
  the tyinfos.

Prerequisite, cheap, do it first: **`src/1/Rewrite.sml:82`
`val implicit = ref empty_rewrites` is still a bare `ref`** — the only
core rewriter state not yet on a `Context.Data` slot, unlike its
`Ho_Rewrite` twin.  Migrate it, then `REWRITE_TAC` (`:187`),
`ASM_REWRITE_TAC` (`:200`) and the `FILTER_*` family follow as plumbing
over the already-explicit `GEN_REWRITE_TAC` (`:181`).

#### 3c. Where the churn budget goes

- **The `TypeBase` accessor layer.**  `TypeBasePure.*` already takes a
  `typeBase` as its first argument, so the pure layer is fine; it is the
  stateful `TypeBase` wrapper's ~40 callers that need a new parameter.
  Includes `primCases_on` (`BasicProvers.sml:295`, i.e. `Cases_on`),
  `induct_on_type` (`:404`, i.e. `Induct_on`), the `PURE_*CASE_TAC`
  family (`:672-696`), `splittable` (`:1059`), and — note — `tyinfol()`
  at `:977`, which means **`PRIM_STP_TAC`, the core of
  `RW_TAC`/`SRW_TAC`, makes an ambient TypeBase read even though its
  simpset is explicit.**
- **Parsing inside tactic bodies.**  Biggest cluster is `src/q/Q.sml`
  (`:207`, `:217`, `:433`, `:441`, `:463`, `:469`).  These need a
  *structural* rewrite, not just a parameter: they are written
  `fun ABBREV_TAC q (gl as (asl,w)) = let … end gl;` — the goal is
  consumed but the context arrives *after* it, so the body cannot see
  the context the new type provides.  Rewrite to
  `fn q => fn gl => fn ctxt => …`.  Others:
  `BasicProvers.sml:147,291,639`, `resolve_then.sml:165`,
  `match_goal.sml:65`, `markerLib.sml:696`, plus scattered sites in
  `quantHeuristics`, `wordsLib`, `IndDefLib`, `Defn`.

#### 3d. Captured conversions — an invariant, not a mechanism

Conversions stored now and invoked later by machinery with no
caller-supplied context.  Per decision 1 these must be **state-free**;
no registry redesign, so `add_conv` and `convdata` keep their
signatures.  The work is fixing the individual offenders:

- `patternMatchesLib.sml:985` — registers a compset conv that goes
  through `rc_ss` (`:193`) and so reads `srw_ss()` *at EVAL time*.  The
  sharpest instance.
- `realSimps.sml:991` — calls `SIMP_CONV (srw_ss() ++ ARITH_ss)` from
  inside decision-procedure code.
- Whatever else the census turns up.

**Not defects, but worth knowing about.**  These hold conversions that
are themselves state-free (structural literal-equality deciders, case
rewrites); their only flaw is being append-only globals that
`Context.restore` does not rewind, so a restored context sees extra
entries that harmlessly fail to apply:

- `DefnBase.const_eq_ref` (`DefnBase.sml:227`, `sig:44`), appended by
  `ORELSEC` at load time from `reduceLib.sml:92`, `wordsLib.sml:2590`,
  `stringLib.sml:88` — and `Defn.sml:17` *copies* the ref, so there are
  two cells.
- `flookupLib.sml:174-186` (`completed_fmap_convs`, `rwt_cnv`).
- `BasicProvers.sml:707`'s case-rewrite cache, mirroring TypeBase via
  `register_update_fn`.

**Explicitly not being changed** (decision 14): the simplifier caches
(`Cache.sml:44`; instances at `numSimps.sml:462`, `realSimps.sml:588`,
`intSimps.sml:251`, `bagSimps.sml:120`, `ConseqConv.sml:1913`).  Cross-
context reuse is sound and false hits are impossible, since
`Term.compare` compares kernelids, so same-named constants from
different contexts are different terms and hence different keys.  They
are already `Sref`-locked.  Only a cached *failure* being reused where
another context would have succeeded is observable.

`BasicProvers.stale_flags` (`:1171`) is handled in 3a, by the
suspension change that removes the mechanism entirely.

_Check_: census monotonically decreasing; core build green after each
directory.  Per decision 8 the tripwire is a style ratchet, not a gate
on Phase 4 — flip it to an error when the count reaches zero, but do
not block replay on it.

### Phase 4 — LSP: convert the existing replay to value-passing

**The mechanism already exists.**  This phase converts it from
global-mutation to value-passing; it does not build it.  What is there:

- `declSnapshot = {endByte, builtTrees, diags, plugins, compileSnap}`
  (`server.ML:560`), captured per *outer declaration* and keyed by
  source byte offset.  `compileSnap : unit -> unit` is a restore thunk
  built in `tools-poly/hol.ML:614-628` as `Context.snapshot()` +
  `Meta.snapshotLoaded()` + `LSPNameSpace.snapshotLayer()`, whose
  restore forces `Parse.invalidate_caches()`.
- Capture at `captureSnap` (`server.ML:1064`), passed to
  `HOL_IDE.initialize` as `onDecCompleted`; deliberately skipped when
  diagnostics are pending, so a mid-edit parse error cannot freeze a
  stale diagnostic into downstream snapshots.
- Resume at `startCompile` (`server.ML:821-880`): finds the largest
  `endByte <= minEditOffset` and recompiles only from there.  Files are
  **not** re-elaborated from scratch on each edit.
- **`goalStateAtPos` (`server.ML:1378-1412`) already runs a proof
  against the context captured at its position** — but by bracketing a
  *global* `Context.restore` with a capture/restore pair.  Since each
  `Theorem … QED` is its own outer dec, the existing per-dec
  granularity already coincides with per-proof-site.

**The choreography.**  SML is strict, so a proof cannot be deferred
*during* elaboration: `val foo = Q.store_thm(…)` must yield a thm
before the next declaration runs.  Hence two phases, with the tactic
value carried between them.

*Phase A — sequential, one thread.*  Elaborate the file with a
**deferring prover** installed through the existing
`Tactical.set_prover`:

    fun deferring_prover ctxt (g, tac) =
      (enqueue {site = …, ctxt = ctxt, goal = g, tac = tac};
       Thm.mk_oracle_thm "lsp_deferred" g)

This is the crux: `set_prover`'s hook already receives
`Context.t -> goal * tactic -> thm`, so the context, goal **and tactic
closure** are all in hand at the proof site.  Instead of discarding the
tactic as today's oracle prover does, enqueue a self-contained work
item and return the placeholder.  Elaboration stays fast.

*Phase B — a bounded worker pool* (not one thread per theorem; a file
can have hundreds) drains the queue.  Each worker does
`Context.install ctxt`, then `TAC_PROOF ctxt (goal, tac)`, and reports
success or failure against `site`.  Items are independent because the
context is an immutable value.

Consequences to hold on to:

- **Capture happens at the prover hook, not at the expander's
  argument** — and that is strictly better than the per-declaration
  `declSnapshot` boundary, being the context at the proof itself.  The
  `declSnapshot` machinery stays, for incremental re-elaboration, which
  is a different job.
- **Workers must call the unhooked entry** (`TAC_PROOF`, not `prove`)
  or they re-enter the deferring hook and enqueue themselves forever.
  This also bypasses `provide_feedback`, which is what you want: the
  worker wants the raw exception to become a diagnostic.
- **`Context.install` is the safety net, not the mechanism** — once the
  proof path is plumbed the worker's ambient reads never happen.
- **`boolLib.current_thm_name`** is read during Phase A on one thread,
  so it is safe *there*; it must not be relied on in Phase B.  The
  location should travel in the work item, which `store_thm_at` already
  has as `loc`.

The other conversion:

1. Replace `goalStateAtPos`'s global restore bracket
   (`server.ML:1378-1412`) with passing the `declSnapshot`'s
   `Context.t` as a value.  That requires
   `goalFrag.expand : tactic -> frag_tactic` (`goalFrag.sml:58-61`) to
   carry a context — either in `goalstate` or as a parameter.  Once it
   does, the walker needs no global restore at all and can run on its
   own thread; `TacticWalker.holder` and its `compileCache`
   (`tactic_walker.ML:29-36`) are fine as they stand.
   Note the live oracle prover is installed at
   `tools-poly/hol.ML:630-632` (tag `lsp_compile_skip`);
   `holide.ML`'s `prelude()` is exported but never called.
2. Move the proof-path mutable state off process globals.  Beyond the
   three obvious cells:

   - `Tactical.unsolved_list` (`Tactical.sml:51`) — written on *every*
     `TAC_PROOF`; two concurrent proofs cross-report unsolved subgoals.
     `DefnBase.sml:687`'s `ThreadLocal` `checkLog` is the model.
   - `boolLib.current_thm_name` (`boolLib.sml:102`) — set immediately
     before `prove`, cleared after: a guaranteed cross-thread clobber.
   - `boolLib.dump_setup_hook` (`:94`) — written at init, *called* at
     proof time.
   - **`Cond_rewr.used_rewrites`** (`src/simp/src/Cond_rewr.sml:14`) —
     a `thm list ref` appended to *during* rewriting, driven by
     `simpLib.sml:1010-1012` which does `used_rewrites := []` then
     `with_flag (track_rewrites, true)`.  A textbook two-proof race.
   - **`BOUNDED (ref n)` counters** (`Rewrite.sml:59-61`, decremented
     in `appconv` at `:89`) — mutable state living *inside* a
     `rewrites` value, so it is shared whenever two proofs use the same
     `rewrites`.  This one is not fixed by moving a global; the value
     itself is stateful.
   - **`Portable.with_flag`** (`Portable.sml:711`) is not thread-safe:
     two threads bracketing the same ref interleave and lose one
     another's restores.  It is used pervasively on the proof path.
     `Context.Data.with_slot_value` (`Context.sig:99`) is the migrated
     equivalent.
   - `Globals` (nearly every exported name is a `ref`, read whenever a
     proof formats a term for an error or trace) and `Feedback`'s
     `trace_map` (`Feedback.sml:262`, with each trace's payload a bare
     ref).  Per decision 12 these split: the ones that can change a
     proof's *outcome* — `Cond_rewr.stack_limit`, `track_rewrites`,
     `PmatchHeuristics.classic`, `Tactical.notheory_action` — move into
     the context in Phase 3, because a flag that changes an outcome
     while living outside the context falsifies the thesis.  The
     printing and tracing majority migrates as a **follow-up task**,
     landing as one bundled record in a single slot rather than twenty
     slots.
3. Make the live context cell thread-local, with
   **install-and-never-restore** (decision 7).  Safe only at this
   point, because it depends on tactics no longer mutating the live
   context — which Phase 3 establishes and which is convention, not a
   type guarantee.  Use `ThreadLocal`, not `Thread_Data`:
   `ThreadLocal` has poly *and* mosml implementations with identical
   signatures (`src/portableML/{poly,mosml}/concurrent/ThreadLocal.sig`),
   the mosml one degrading to a single shared cell — exactly what mosml
   has today.  `Thread_Data` is poly-only, has no `.sig`, and is wired
   into the poly Holmakefile alone.  `src/coretypes/DefnBase.sml:687`
   already uses `ThreadLocal` for `checkLog`, the closest structural
   precedent in the tree.
   `ThreadLocal.get` yields `NONE` on a fresh thread, so **the install
   point must raise a clear error** rather than let a worker run
   against a minimal grammar and produce baffling parse failures.
4. Replay real proofs on the worker pool against the captured
   contexts.
5. Placeholder/real equivalence.  **Tags are fine; hypotheses are
   not.**  A census of every `Thm.tag`/`Tag.`/`mk_oracle_thm` use found
   *no* tag-dependent branching in the elaboration path:
   `ThmAttribute.sml` never mentions tags at all, `ThmSetData` compares
   conclusions only, and `Theory.sml`'s `oracle_string_of` (`:609`)
   feeds a console message.  `export_theory` is moreover a no-op under
   the LSP (`Globals.interactive := true`, `hol.ML:575`), so its hooks
   and the serialisation-time tag readers never run.

   The divergence is that `mk_oracle_thm "…" g` has the goal's
   hypotheses, while a real proof may return extra ones.  Three
   consequences, worst first:

   - **`suspend`/`Resume`/`Finalise` diverge structurally.**
     `save_thm_attrs` (`boolLib.sml:174-224`) branches on suspendlabel
     hypotheses: with them the theorem goes to `markerLib`'s suspension
     store and **not** to the DB; without them (the placeholder) it
     takes the ordinary DB path.  So the same file populates different
     stores depending on whether the proof ran, and every snapshot
     *after* such a theorem is a wrong input for later real proofs.
     This is already known and worked around for `Holmake --fast`
     (`markerLib.sml:1175-1184`, `fast_shortcut` at `:1246`), and there
     is a dedicated regression:
     `src/basicProof/theory_tests/suspFastScript.sml` (issue #1909).
     **Decision 13: accept this, reusing that tolerance.**  The
     placeholder context is strictly *more permissive* — the DB holds
     an entry it shouldn't and the suspension store lacks one — so the
     worst case is the IDE accepting a citation of a still-suspended
     theorem that a real build rejects.  A false positive in an
     optimistic tool, not unsoundness, since Holmake still does the
     real thing.  Keep `suspFastScript.sml` as the guard.

     One correction to that test's own header comment, which would
     otherwise send you looking for code that does not exist: it says
     Resume "detects this situation (fast_proof oracle tag on the
     parent)".  It does not — `markerLib.sml` never inspects a tag
     (its only tag reference is *producing* one at `:1247`).  The
     branch is on the **absence of a suspendlabel hypothesis**.  The
     distinction matters, because hypothesis-absence is what a
     placeholder pass reproduces, whereas a tag check would give you a
     cheap way to detect the placeholder case and there isn't one.
   - **Conditional rewrites.** `Theorem foo[simp]` whose real proof
     leaves hypotheses yields a *conditional* simp rule; the placeholder
     yields an unconditional one.  Same for `[compute]`.
   - `Theory.check_null_hyp` (`:1338`) and
     `boolLib.slab_owner_lookup` (`:116`) are both more permissive
     under placeholders.

6. **Route termination proofs through the same machinery**
   (decision 10).  `set_prover` only hooks `Tactical.prove` and
   `prove_goal` (`Tactical.sml:102-103`), so today `Theorem … QED` and
   `Resume` are cheated while `Definition … Termination tac End` runs
   for real — not by design, but because `Defn.tprove2` goes through
   `proofManagerLib.expand` (`Defn.sml:1906`) and
   `TotalDefn.proveTotal` (`:638`) through `default_prover`, neither of
   which is hookable.

   Replace the goal-manager round-trip in `tprove2` with a direct
   `prove_goal ctxt (goal, tactic)` on the non-interactive path — the
   round-trip exists for interactive `tgoal`/`tprove`, so this is a
   small refactor.  Both entry points must funnel there: the explicit
   `Termination tac` and the automatic `proveTotal`.  The deferring
   prover then handles termination like anything else: Phase A runs the
   definition machinery, hits the termination goal, enqueues it, takes
   an oracle discharge and completes with the right statements; Phase B
   proves it and reports a diagnostic on failure.

   **Definition principles themselves still run.**  They must, to
   determine the statements of the output theorems, and they are quick.
   Only the termination *proof* is deferred.  This preserves the
   equivalence that matters: TFL picks the termination relation before
   the proof, so an oracle discharge leaves the definition's and
   induction theorem's statements unchanged.  `Inductive`/`CoInductive`
   (`IndDefRules.sml:54`, `InductiveDefinition.sml:535`) likewise keep
   running for real.

7. **`Context.restore` does not rewind the kernelid clock**
   (`Context.sig`, explicitly).  A replayed pass that re-executes any
   definition mints constants that are *not* `Term.same_const` with the
   first pass's.  Any replay must therefore avoid re-running
   definitions, not merely restore around them.

_Check_: a Script with several `Theorem … QED` blocks re-checks
correctly under parallel replay and yields the same theorems as a
sequential Holmake build of the same file.  Then run
`src/basicProof/theory_tests/suspFastScript.sml` and a file exercising
`Proof[exclude_simps=…]` — those are the two cases known to diverge
between the cheated and real passes.

### Phase 5 — documentation

Bounded, because `tactic` is a type *abbreviation*: the ~88 Docfiles
that say `FOO_TAC : tactic` stay correct as written.  Only these need
editing:

- `Manual/Description/tactics.smd` — explains the tactic type itself.
- The handful of Docfiles that spell out `goal -> goal list *
  validation` (e.g. `help/Docfiles/Tactic.drule.smd`,
  `Thm_cont.PROVEHYP_THEN.smd`).
- `developers/discussion/context-passing-tactics.md` — this document,
  kept current as the phases land, in the style of its sibling memo.

Leave `Manual/Translations/IT/` alone.

Style, enforced by `tools/h4pedant` in the regression suite: no tabs,
no trailing whitespace, strongly prefer < 80 columns.

## Verification

Baseline and per-phase regression, from the worktree root:

    poly < tools/smart-configure.sml
    bin/build -t --seq=tools/sequences/upto-parallel

That is this repo's "kernel + libraries still healthy?" pass (the *core
build*, per `CLAUDE.md`).  Use `-F` explicitly for a full build — bare
`bin/build` reuses the previous invocation's `--seq=…` and can silently
skip whole swaths of the tree.

While iterating inside a single directory:

- `src/portableML` … `src/1` need `bin/Holmake --poly_not_hol`;
  the next band needs `--holstate=<root>/bin/hol.state0`; plain
  `Holmake` suffices from `src/boss` onwards.  Never combine
  `--poly_not_hol` with `--holstate` — they are alternatives.
- Always pass `--no-cache` for ad-hoc invocations.
- **`Holmake Foo.uo` does not typecheck `Foo`** — it only emits
  dependencies.  Real type errors require the actual build.  Since
  Phase 0–3 are largely a long tail of type errors, budget for real
  builds rather than targeted `.uo` requests.

Tests go in each directory's `selftest.sml` using `testutils`
(`tprint` + `OK`/`die`); run one directly with
`Holmake selftest.exe && ./selftest.exe`.  Do not validate by piping
`.sml` into `bin/hol`.

Those are the standing regressions.  Each phase above additionally
carries its own `_Check_` line, stating what specifically must hold
before moving on; treat those as the gates and this section as the
baseline underneath them.
