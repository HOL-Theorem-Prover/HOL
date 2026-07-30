# Guarding `prove` against a missing current theory

## Proposal

Make `Tactical.TAC_PROOF` complain when it is entered with
`Thm.getCT () = NONE`, so that library code proving theorems as it loads
is caught at the point of the mistake instead of much later, in a form
that is hard to recognise.

The check should start as a warning, so that the existing offenders can
be worked through, and become an error once the list below is empty.

## Why

Library code that proves theorems at load time runs in whatever ambient
state the link order happens to produce.  That makes its behaviour a
function of load order rather than of its own source, which is a bad
property for something that is supposed to be a fixed axiom of a
decision procedure.

The worked example is `src/metis/folTools.sml`, fixed in `5b576aa83`.
Its equality axioms are proved as the structure loads.  It pinned
`Parse.Term` to the `normalForms` grammar, which covers parsing --- but
`GEN_TAC` chooses bound-variable names apart from the constants of the
*ambient* grammar.  `cv_compute_unsoundTheory` defines a constant `g`;
when that theory loads first, `GEN_TAC` renames the goal's `g` to `g'`
while the separately parsed `ASM_CASES_TAC` term still says `g`, the
case split stops matching the goal, and the proof fails.  Reproduce on
any kernel and either ML, from a directory where the theory is on the
load path:

    load "cv_compute_unsoundTheory"; load "folTools";

This surfaced as a Moscow ML CI failure in
`src/num/theories/cv_compute/soundness_check`, roughly 30 directories
and one whole library away from the actual defect, and presenting as an
unprovable goal rather than as anything to do with loading.  Under
Poly/ML the same build was green, purely because metis was already
resident before the offending constant was defined.

A `getCT ()` check would have stopped `folTools` at its first `prove`
with an accurate message.

## Why the current-theory test is the right trigger

Two properties make it a good proxy:

  - A script that has reached `new_theory` has a current theory, so the
    check cannot fire on ordinary script proofs.
  - A standalone executable --- a selftest, or anything run through
    `bin/hol run` --- starts with `getCT () = NONE`, which is exactly
    the situation where link order is fixed and the failure mode above
    is reachable.

It follows that no script should be dynamically loading libraries once
its `new_theory` call has hit; and once the libraries are fixed not to
prove at load time, an interactive session loading a library into a
state that does have a current theory is unaffected.

The check is deliberately partial: a library proving at load time in a
session that happens to have a segment open still slips through.  That
is acceptable, because the standalone case is the one that bites.

## Measured cost

Census taken on 2026-07-27 at `5b576aa83`, by instrumenting
`TAC_PROOF` to log rather than raise, and running

    bin/build --stdknl --no-cache -t --seq=tools/sequences/upto-parallel

The instrumentation, at the head of `TAC_PROOF` in `src/1/Tactical.sml`:

    fun TAC_PROOF (g, tac) =
      (case Thm.getCT() of
           NONE =>
             TextIO.output
               (TextIO.stdErr,
                "NOCT-PROVE|" ^
                (Parse.term_to_string (snd g) handle _ => "<unprintable>") ^
                "\n")
         | SOME _ => ();
       case tac g of ...)

Note that the markers land in each directory's `.hol/logs/*` files, not
on the build's own stdout; collect them with `grep -ra NOCT-PROVE src`.

Results over 89 directories (the build itself stayed green):

| measure                                            | count |
|----------------------------------------------------|-------|
| `TAC_PROOF` calls with no current theory            | 2386  |
| distinct goals among them                           | 176   |
| ... appearing in theory-build logs                  | 1421  |
| ... appearing in selftest logs                      | 965   |
| library files with a top-level `val _ = prove ...`  | 77    |

173 of the 176 distinct goals appear in both theory-build and selftest
logs, which says these are library lemmas reproved on each load rather
than tests proving without a segment.  The most repeated:

    72  |- !f x. f x = I f x
    38  |- z = $@ P ==> ($? P <=> P z)
    38  |- !P. P (if a then b else c) <=> a /\ P b \/ ~a /\ P c
    38  |- !P. (?!x. P x) <=> ?x. P x /\ !y. P y ==> y = x
    36  |- LET f (I x) = f x

The static list of files was produced with

    pat="^ *val [A-Za-z_0-9'.]+ *= *(prove|store_thm|TAC_PROOF"
    pat="$pat|Q\.prove|Q\.store_thm)"
    find src -name "*.sml" -not -path "*/.hol/*" \
         -not -name "*Script.sml" -not -name "selftest.sml" \
      | xargs grep -lnE "$pat"

### Caveats on the numbers

  - `upto-parallel` only.  A full `-F` build will find more, from
    `src/parallel_builds` onwards.
  - The static list requires `val`, so it excludes `fun`-wrapped
    provers that only fire when called --- correctly, since those are
    not load-time --- but it over-counts where such a `val` sits inside
    a function body, and under-counts anything reaching `TAC_PROOF`
    indirectly through a conversion or tactic.  Treat 77 as the right
    order of magnitude, needing a per-file check.

## Suggested staging

  1. Add the check to `TAC_PROOF` as a warning, ideally behind a trace
     so it can be silenced.
  2. Work down the file list.  For each, either move the proof into a
     companion `fooContextScript.sml` background theory that `foo.sml`
     imports (preferred, especially when the theorem is non-trivial),
     or replace the tactic proof with a forward proof using only
     primitive rules (fine for one-liners).  Several files already
     carry a hand-rolled grammar guard (`Canon.sml`, `Extract.sml`,
     `folTools.sml`) --- that guard is a symptom of this problem and
     can go once the proof no longer happens at load time.
  3. Flip the warning to an error.

Files baked into `hol.state0` (in particular the src/1 residents:
`boolLib.sml`, `Drule.sml`, `newtypeTools.sml`, `Prim_rec.sml`,
`Tactic.sml`, `TypeBasePure.sml`) are exempt from the cleanup: their
load-time proofs run once during heap construction and are never
re-executed under a varying ambient state, so they cannot exhibit the
bug the check exists to catch.

## Progress

Step 1 landed: `TAC_PROOF` warns when `Thm.getCT () = NONE`, controlled
by the trace `"TAC_PROOF requires current theory"` (default 1, max 1).
Trace `0` silences it.

Step 2 in progress.  Companion `fooContextScript.sml` files exist for:

  - `src/metis/folTools.sml`      → `folToolsContextScript.sml`
  - `src/metis/folMapping.sml`    → `folMappingContextScript.sml`
  - `src/metis/normalForms.sml`   → `normalFormsContextScript.sml`
  - `src/refute/Canon.sml`        → `canonContextScript.sml`
  - `src/meson/src/Canon_Port.sml`→ `Canon_Port_ContextScript.sml`
  - `src/meson/src/mesonLib.sml`  → `mesonLibContextScript.sml`
  - `src/IndDef/InductiveDefinition.sml` → `InductiveDefinitionContextScript.sml`
  - `src/simp/src/boolSimps.sml`  → `boolSimpsContextScript.sml`
  - `src/coretypes/pairTools.sml` → `pairToolsContextScript.sml`
  - `src/num/reduce/src/Boolconv.sml` → `BoolconvContextScript.sml`
  - `src/num/arith/src/Sub_and_cond.sml` → `SubAndCondContextScript.sml`
  - `src/num/theories/Num_conv.sml` → `NumConvContextScript.sml`
  - `src/datatype/EnumType.sml`   → `EnumTypeContextScript.sml`
  - `src/real/RealField.sml`      → `RealFieldContextScript.sml`

For libraries that already carried a companion script, the theorems
went into that script rather than a new one:

  - `src/quantHeuristics/quantHeuristicsLibParameters.sml` and
    `quantHeuristicsTools.sml` → `quantHeuristicsScript.sml` and
    `ConseqConvScript.sml`.
  - `src/pattern_matches/patternMatchesLib.sml` and
    `constrFamiliesLib.sml` → `patternMatchesScript.sml`.
  - `src/datatype/ind_types.sml` → `ind_typeScript.sml`.
  - `src/n-bit/wordsLib.sml` and `blastLib.sml` → `wordsScript.sml`
    and `blastScript.sml` (34 + 12 lemmas).
  - `src/integer/CooperCore.sml` → `cooperScript.sml`
    (5 polymorphic MEM helpers, INST_TYPE'd at consumer side).

Two `TypeBase.write` → `TypeBase.export` conversions also went in:

  - `src/n-bit/fcpScript.sml`: `gen_datatype_info` result was only
    kept in the current process's TypeBase.  Switching to `export`
    persists it in the theory data, matching what
    `pair`/`sum`/`option`/`list` do; the `fcpLib` re-registration goes
    away with its 80-warning-per-downstream case-lifting prove.

Two build-order flips also went in:

  - `src/pred_set/src/hurdUtils.sml` used to hand-prove `SET_EQ` because
    it sat below `pred_setTheory` in the build order.  Removed
    `hurdUtils` from `pred_setScript`'s `Libs` (inlining the tiny
    `K_TAC` / `KILL_TAC` / `Rewr'` / `art` helpers it drew from there,
    and expanding `Know`/`Suff` to `Q_TAC KNOW_TAC` / `Q_TAC SUFF_TAC`),
    then aliased `SET_EQ` to `pred_setTheory.EXTENSION`.

Grammar guards in the fixed files whose sole purpose was to insulate
the load-time proofs went with the proofs.  One exception: Boolconv
keeps its `Parse.temp_set_grammars` bracket because it also calls
`ParseExtras.temp_loose_equality`, whose ambient effect the bracket is
still scoping.

Core-build census after these changes:

| measure                                             | count |
|-----------------------------------------------------|-------|
| `TAC_PROOF` calls with no current theory             | 144   |
| distinct goals among them                            | 64    |
| log files still carrying at least one                |   6   |

Down from 2386 / 176 / 57 in the baseline.  The library-load-time
class of offender is essentially clean; the remainder splits into:

  - `soundness_check-selftest.log` (38): the selftest itself proves
    without a segment.
  - `src/1/selftest.log` (17): ditto.
  - `bin/hol.state0` log (14): warnings from the state-building phase,
    hitting boolLib and friends — exempt as they run once during heap
    construction.
  - `simp-selftest.log` (3), datatype `theory_tests` (1 each): more
    selftest-in-place prove sites.

The selftest cases are a different class from the library-load-time
one this file started with: each is a test file directly calling `prove`
without opening a segment.  Fixing them means either wrapping the test
in a scratch theory or promoting the tactic proof to a proper Script.
Left for a follow-up.

## Longer term

The deeper fix, which would close the class rather than police it, is to
pass a grammar context into `prove` so that tactics like `GEN_TAC` are
insulated from globals altogether.  Bracketing a file with
`Parse.temp_set_grammars` --- what `folTools` now does --- works, but
every such file re-implements the same guard by hand, and each one can
be defeated the same way by any tactic that reads a global the bracket
does not cover.

## The 77 files

    src/1/boolLib.sml
    src/1/Drule.sml
    src/1/newtypeTools.sml
    src/1/Prim_rec.sml
    src/1/Tactic.sml
    src/1/TypeBasePure.sml
    src/bag/bagSimpleLib.sml
    src/coretypes/pairLib.sml
    src/coretypes/pairTools.sml
    src/datatype/DataSize.sml
    src/datatype/EnumType.sml
    src/datatype/ind_types.sml
    src/datatype/record/RecordType.sml
    src/datatype/theory_tests/recordEnumSimpsLib.sml
    src/finite_maps/alist_treeLib.sml
    src/finite_maps/enumTacs.sml
    src/finite_maps/flookupLib.sml
    src/finite_maps/patriciaLib.sml
    src/finite_maps/tcTacs.sml
    src/HolQbf/QbfConv.sml
    src/HolSmt/Alethe_ProofReplay.sml
    src/HolSmt/Z3_ProformaThms.sml
    src/HolSmt/Z3_ProofReplay.sml
    src/holyhammer/examples/proof.sml
    src/IndDef/CoIndDefLib.sml
    src/IndDef/IndDefRules.sml
    src/IndDef/InductiveDefinition.sml
    src/integer/CooperCore.sml
    src/integer/jrhCore.sml
    src/integer/OmegaMath.sml
    src/integer/OmegaSimple.sml
    src/integer/OmegaSymbolic.sml
    src/marker/markerLib.sml
    src/metis/folMapping.sml
    src/metis/folTools.sml
    src/metis/metisTools.sml
    src/metis/normalForms.sml
    src/n-bit/bitstringLib.sml
    src/n-bit/blastLib.sml
    src/n-bit/wordsLib.sml
    src/num/theories/cv_compute/automation/cv_miscLib.sml
    src/num/theories/cv_compute/automation/cv_repLib.sml
    src/num/theories/cv_compute/automation/cv_transLib.sml
    src/num/theories/cv_compute/automation/cv_typeLib.sml
    src/num/theories/cv_compute/tailrecLib.sml
    src/opentheory/reader/OpenTheoryReader.sml
    src/pattern_matches/constrFamiliesLib.sml
    src/pattern_matches/patternMatchesLib.sml
    src/pattern_matches/patternMatchesSyntax.sml
    src/pfl/examples/tree.sml
    src/pfl/examples/zero.sml
    src/pfl/index.sml
    src/pfl/pflLib.sml
    src/pred_set/src/hurdUtils.sml
    src/pred_set/src/more_theories/countable_typesLib.sml
    src/quantHeuristics/ConseqConv.sml
    src/quantHeuristics/quantHeuristicsLibAbbrev.sml
    src/quantHeuristics/quantHeuristicsLibFunRemove.sml
    src/quantHeuristics/quantHeuristicsLibParameters.sml
    src/quantHeuristics/quantHeuristicsTools.sml
    src/quotient/examples/ind_rel.sml
    src/quotient/examples/lambda/barendregt.sml
    src/quotient/examples/sigma/barendregt.sml
    src/quotient/src/quotient.sml
    src/rational/ratLib.sml
    src/rational/schneiderUtils.sml
    src/real/RealField.sml
    src/real/realSimps.sml
    src/real/SOSLib.sml
    src/refute/Canon.sml
    src/res_quan/src/res_quanLib.sml
    src/simp/src/boolSimps.sml
    src/simp/src/congLib.sml
    src/tactictoe/examples/proof.sml
    src/taut/tautLib.sml
    src/tfl/src/Extract.sml
    src/transfer/transferLib.sml
