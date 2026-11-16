# Note on the Simplifier Code

## Important Types

**simpset**

:   (From `simpLib`.)
    Typically built by bundling *fragments* together, but is actually a collection of four important components:

    -   `mk_rewrs` function.
        This processes “arbitrary” user-provided theorems to turn them into proper rewrites.

    -   `net` a higher-order term-net containing simplifier-conversions

    -   `dprocs` a list of “decision procedures” (lower priority routines), which are *reducer*s.

    -   `travrules`, a *travrules* value

**ssfrag** (a ‘simpset fragment’)

:   (From `simpLib`.)
    A collection of user-provided data that gets pushed into *simpset*s.
    Includes rewrites, conversions, congruences, AC rewrites, decision procedures, relation-simplification data and an optional `filter`, which is used to adjust the simpset `mk_rewrs` function.

**reducer**

:   (From `Traverse`.)
    A bundled piece of code/data that is capable of producing theorems relating input terms to fresh “outputs”.
    Each reducer has its own notion of “context”, values to which clients can add theorems.
    (These contexts are implemented with exceptions to give existential types.)
    Such added theorems may be goal assumptions, or provided by congruence rules.

    Each reducer has an `apply` function, which is passed a context, a `solver` for handling side conditions, a `stack` of already attempted side conditions, a continuation `conv`, a `relation` field and an input term.
    The `apply` function is expected to return a theorem of the form

        |- input  R   output

    where `R` might be as given in the `relation` field.

    Arithmetic decision procedures are `reducer`s.
    Their context is the list of theorems that they believe to be relevant (*i.e.*, Presburger terms), and they ignore all of the information provided by `apply` except the context.

    Reducers don’t depend on anything else in the simplification code base (though their `conv` and `solver`  continuations will call back into simplifier code).

**preorder**

:   (From `Travrules`.)
    A preorder encodes information enough to identify a relation (type `'a -> 'a -> bool`) as something that is reflexive and transitive.
    The preorder stores the constant of the particular relation, and two functions to implement transitivity and reflexivity.
    The former takes two theorems as input, while the latter takes both the argument to the relation and a relation term itself, which, if polymorphic, must have been instantiated so that it can be applied to the argument.
    For the equality case, this data is thus (`min$=`, `TRANS` and (essentially) `REFL`).

**travrules**

:   (From `Travrules`.)
    Embodies a list of *preorders* and two lists of *congprocs*: the “standard congprocs” (`congprocs`), and the “weakening congprocs” (`weakenprocs`).
    The “default” travrules value is `EQ_tr`, and contains the equality preorder, and the equality congproc as a standard congproc.
    (I.e., it has no weakening congprocs.)

    The travrules is a static piece of information for guiding simplification.
    The dynamic data that is maintained during simplification (containing context values, the relation currently being used and the context’s free variables) is a `trav_state`, which is private to module `Traverse`.

    Each simpset contains a list of `travrules` values.

**congproc**

:   (From `Opening`.)
    A congproc is a function that will set up recursive simplification of an input term.
    With the exception of the core equality congruences (`MK_COMB` and `ABS`) these are all built with the function `CONGPROC`.
    In addition to the term, the congproc is passed a record of important data containing

    -   `depther`: a function which will be applied to subterms to produce simplified sub-terms
    -   `solver`: used to handle side-conditions in congruence rules
    -   `relation`: identifies the relation we’re using
    -   `freevars`: the free variables of the context, which may be relevant if descending under a binder

    `congproc` values are stored in `travrules`.

## Important Functions

`SIMP_QCONV`

:   (From `simpLib`.)
    Calls `TRAVERSE` after building initial context values for all of the embedded reducers (giving a trav_state)

`TRAVERSE`

:   (From `Traverse`.)
    Implements the logic of the simplifier’s traversal of terms.
    In particular, this is where the preorder/top-down nature of the simplifier wrt its equality rewrites is decided, because of the way it begins with

        repeat high_priority then descend ...

    The `high_priority` stuff here is to do fire the equality reducer.
    Descent is then the recursive simplification of sub-terms.
    The `...` portion is where decision procedures get to fire, and where weakenprocs get a chance to fire.
    These effectively see the term in bottom-up fashion as a result.

`CONGPROC`

:   (From `Opening`.)
    This builds a *congproc* given a `congrule` theorem and a general notion of reflexivity in the function `refl`.
    It’s important that `refl` be able to generate reflexivity theorems for multiple relations at once: this allows different relations to appear in the assumptions of `congrule`; the conclusion might want to draw conclusions about equality even as one of the assumptions is about another relation again (as happens in weakening congruences).

    One problem here is that reprocessing of assumptions can unnecessarily descend into terms that have already been processed once.
    For example, in the rule for conditional expressions, we have

        p = p’ ==> (p’ ==> t = t’) ==> (~p’ ==> e = e’) ==>
        (COND p t e = COND p’ t’ e’)

    and the reprocess flag will be set to true for the `~p’` assumption (it’s not just a variable).
    Sure, if negation descends over a disjunction or similar, this is an important thing to do (though the `mk_cond_rewr` could presumably do it too), but if nothing simplifies at the top level, it’s painful to have to descend into `p’` again.

# The extension engine

`simpLib`, `congLib`, `Traverse`, `Cond_rewr`, `Opening`, `Travrules`,
`pureSimps`, `boolSimps` and `combinSimps` make up the ordinary simplifier
described above. A second, opt-in engine lives alongside it, in `simpExtLib`,
`TraverseExt`, `Cond_rewrExt`, `congExtLib`, `splitLib` and `simpMarkerLib`.
Importing `simpLib` or `congLib` does not import the extension engine,
its markers, the splitter, persistent split registration or tracking.

Ordinary simpsets contain **no** strategy records, source handles, paired
runners or tracking inventories, and `simpLib.traversedata_for_ss` always
returns ordinary traversal data. Ordinary `Excl`/`-*` names are literal: the
prefixes `rule:`, `solver:`, `looper:`, `split:` and `case:` have no
meaning there.

## Where things live

| Feature | Module/type |
| --- | --- |
| `CONTEXT_REDUCER`, `CONFIG_REDUCER`, configuration/solver/policy types, `XTRAVERSE`, root/observed/child-first traversal | `TraverseExt`, with its own `TraverseExt.reducer` type. |
| Paired/context/configured conditional rewriting | `Cond_rewrExt`. Both engines build their conversions with `Cond_rewr.COND_REWR_CONVS`; `Cond_rewr.COND_REWR_CONV` is its legacy runner. |
| Threaded congruences | `Opening.THREADED_CONGPROC`, `Travrules.mk_threaded_travrules`, `simpExtLib.threaded_cong_ss`. `Opening.CONGPROC` and `Travrules.mk_travrules` do not thread. |
| Extension fragments, simpsets, `dproc_ss`, `SSFRAG`, weakener data | `simpExtLib.ssfrag`/`simpset`, with `TraverseExt.reducer`. |
| Configured preorder simplification | `congExtLib`, with its own congset type and an extension simpset. |
| Loopers, safe/unsafe solvers, subgoaler, condition depth, term order | `simpExtLib`, with the `TraverseExt.ssolver`/`subgoaler` types. |
| `Split`, `ExclX` | `simpExtLib`; marker inspection and recursive processing are in `simpMarkerLib`, not generic `markerLib`. |
| Source handles/views/bundles, control-preserving replay, child-first preparation | `simpExtLib`; build tracked ingredients before installing source-sensitive rules, makers or reducers. |
| Configured `GEN_*`, global/child-first/BOUND tactics | `simpExtLib`, taking its simpset and a `TraverseExt` policy. BOUND requires the bundle already installed. |
| Configured traversal data for a simpset | `simpExtLib.xtraversedata_for_ss`, for `TraverseExt.XTRAVERSE`. |
| Ordinary fragments/simpsets (`PURE_ss`, `BOOL_ss`, `srw_ss()`, ...) in the extension engine | `simpExtLib.lift_ssfrag`, `simpExtLib.lift_simpset`. |

The adapters are one-way. `TraverseExt.lift` wraps an ordinary reducer while
retaining its context/callbacks; `simpExtLib.lift_ssfrag` lifts an ordinary
fragment (its reducers by `TraverseExt.lift`), and lifting the same named
fragment again returns the same extension fragment, with the same rewrite
sources; `simpExtLib.lift_simpset` replays an ordinary simpset's history
(fragments, deletions, weakeners), limit and exclusions through these lifts;
`congExtLib.lift_fragment` lifts public ordinary congruence fragment data.
`simpExtLib.lookup_named_frag` (and so `SF`) also finds fragments registered
with `simpLib`, lifted, unless a fragment of the same name is registered
with `simpExtLib`. A lift does not recover an opaque reducer's source
inventory, and there is no reverse adapter into ordinary traversal.

## Executable tracked construction and projections

Load extension modules explicitly (or list them in a Script's `Libs`).
For example:

```sml
val tracked : simpExtLib.simpset =
  simpExtLib.++ (simpExtLib.lift_simpset pureSimps.pure_ss,
                 simpExtLib.lift_ssfrag boolSimps.BOOL_ss);
val default_data : TraverseExt.traverse_data =
  simpExtLib.traversedata_for_ss tracked;
val configured_data : TraverseExt.xtraverse_data =
  simpExtLib.xtraversedata_for_ss tracked;
```

Both projections belong to `TraverseExt`, **not** ordinary `Traverse`.
The default projection omits simpset strategy settings and uses
construction-once private contexts with `TraverseExt.TRAVERSE`; configured
`TraverseExt.XTRAVERSE` refreshes contexts per application. Extracting either
projection does not recompile, invoke collectors or reset actual counters.
Both retain the tracked object's installed bounded controls, including zero.

Threaded CONG and ETA remain explicit choices. A lifted simpset is a
snapshot: later ordinary local/logged/window updates are not mirrored.

Typed construction, reducer/public-fragment lifts, paired projections and
actual bundle/view sharing are executable in
[`Documentation.sml`](../tests/api-audit/Documentation.sml).
Configured/global/child-first tactic witnesses are in
[`APIExamples.sml`](../tests/simp-ext/APIExamples.sml). Run them through:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/api-audit check
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/simp-ext check
```

### Sources, views, replay and private derivation

- `rewrite_sources`/`rewrite_source_handles` inspect installed native rules;
  they neither compile supplied rules nor discover inside opaque reducers.
  Directives must first pass through `prepare_rewrite_arguments`.
- `prepare_rewrite_bundle` compiles supplied originals once, before binding
  views. `install_rewrite_bundle` and attached `rewrite_views` reuse their
  actual controls/matchers. `combine_rewrite_bundles` retains existing events
  and rejects duplicate bindings; it does not refresh quotas.
- Origin order (`rewrite_source_compare`) alone is not compatibility;
  `same_rewrite_source` also checks compiled statement compatibility. Removal,
  suspension or changed source statements invalidate dependent views while
  surviving conjuncts retain their own identities/sharing.
- Ordinary extension history removal/filtering resets declared allowances;
  `remove_ssfrags_preserving_controls` and
  `filter_rewrites_preserving_controls` explicitly keep surviving live refs,
  including exhaustion. Neither accepts an ordinary simpset.
- `prepare_child_first`/`prepare_child_first_observed` create reusable private
  derivations. Every application uses declared private allowances and restores
  the caller's exact prior counters on success, HOL errors, arbitrary
  exceptions and interrupts. This includes native bounded entries without
  handles, but cannot inspect/reset a lifted opaque reducer's internals.

## Context, solving, congruences and controls

Reducers carry exception-valued private contexts. Ordinary `Traverse.TRAVERSE`
initializes contexts at conversion construction and eagerly constructs its
congruence/weakener factories at that stage. Extended `TRAVERSE` retains
the default schedule; configured/context/observed entry points explicitly
refresh.
`TRAVERSE_WITH_CONTEXT` separates reducer facts from solver-only facts;
solver facts also protect binders but do not install rewrites a second time.

`TraverseExt.simp_prover_ctxt` contains `{stack, context_thms, recurse}`.
Unsafe solvers handle conditions; safe solvers are final solvers selected by
safe tactics, not replacements for the unsafe condition list. Root rewriting
omits descent only at entry; its side conditions still use full traversal.
Child-first policies charge before work and can preserve abstractions.
Observer/policy callback aborts retain original exception identity, including
through nested solver/congruence continuations.

There is one `Cond_rewr.stack_limit` ref. `NONE` in configured native depth
reads it at each candidate check; `SOME n` is local and never changes it.
A `CONTEXT_REDUCER` samples an integer immediately before its callback;
`CONFIG_REDUCER` retains the option. Term order is passed explicitly and
otherwise defaults to `Cond_rewr.ac_term_ord`. No temporary global setting
implements configured invocation.

`Opening.THREADED_CONGPROC`/`Travrules.mk_threaded_travrules` share the
ordinary factories' code while threading earlier results into later premises
and beta-reducing rebuilt RHS terms. The ordinary factories do no such extra
work. Both traversal engines are `TraverseCore`, parameterised by how a
reducer is applied; `congLib` and `congExtLib` are both `congLibFn`; code
common to `simpLib` and `simpExtLib` is in `simpCommon`.
Both engines use the same original `Trace` action/hook/ref and registered
`simplifier` knob; rewrite tracking is one extent, owned by `Cond_rewr`.
`Cond_rewrExt` reports through `Cond_rewr.note_rewrite`, and
`simpExtLib.track` is `Cond_rewr.with_tracking`. `simpLib.track` and
`simpExtLib.track` are therefore the same extent: either sees the rewrites
of both engines in the order they fired. A nested extent of either kind
reports only its own rewrites and the enclosing extent does not see them;
exceptions restore the enclosing extent.
Existing `BoundedRewrites.control`, `Conv.UNCHANGED`, `Feedback.HOL_ERR` and
`Portable.Interrupt` identities are not copied. Named-fragment registries are
intentionally **different typed Context slots**, `simpLib.ssfragDB` and
`simpExtLib.ssfragDB`. SF syntax is shared and lookup is late. `simpLib`
never consults the extension registry; `simpExtLib` falls back to
`simpLib`'s, lifting what it finds.

## Extended arguments and exclusions

Only explicit extension entry points interpret strategies, Split and ExclX.
There is no goal-time promotion/strategy dispatch in ordinary tactics.
Supplied extension rules bind once per invocation after abbreviation
pretactics succeed; label/FRAG lookup keeps its documented late stage.
GEN global passes share one invocation's rules and looper budget across
fixpoint reentry/siblings; saved tactic reuse starts a new invocation.
BOUND consumes its already-installed bundle without reinstalling/recompiling.
NoAsms/IgnAsm apply to both bound and unbound paths.

`ExclX` supports `rule:`, `looper:`, `solver:`, `split:` and `case:`.
`rule:` accepts relaxed dotted/kernel `$` names. Bare names use the strict
parser, preferring rules/dprocs before strategy fallback. Missing/ambiguous
targets fail at processing, not construction. Resolved history retains keys
rather than resolving again. Split/case suppression blocks later split
additions and ambient persistent/TypeBase split rules, not user loopers with
colliding display names. Other deletions are point-in-history operations:
later additions can reinstall a target. Bounds on directives qualify their
payload, not a bounded deletion; genuine bounded rewrite controls remain.

## Persistent split rules: separate explicit opt-in

Loading ordinary libraries, `splitLib`, or extension libraries and querying
split rules claims no `split` namespace. Local `Split`/`add_split` and
TypeBase `split_ss` work without persistent registration. A split-bearing
Script includes `splitPersistLib` in `Libs` **before** declarations and calls
`Theory.add_ML_dependency "splitPersistLib"` for fresh exported imports.
Put this dependency on the earliest split-bearing parent; a child's ML
initialization cannot repair an already-loading parent. An explicit prelude
calling `splitLib.enable_split_attribute ()` before loading the entire graph
is also supported.

`splitLib.exclude_split "Thy.Name"` persistently retracts a named ancestor
rule (not its DB theorem). Unqualified names resolve in the writing theory;
exported REMOVE keys cannot remove a descendant's same-named rule. This is
not local `del_split`/`ExclX`. An existing `split` attribute or set makes
initialization fail rather than replace it; removal requires an enabled
registration. Registration follows `Context.restore`, but the
ML loader is global: after rewind before opt-in, explicitly initialize again;
loading an already-loaded module need not rerun it. Initialization is serial,
not an operation during concurrent proofs or arbitrary late-segment replay.

Persistence uses one private ordered event stream,
`splitLib.persistent.rules.v1`, one direct attribute and one private listener;
there is no generic ThmSetData split set/exporter, and generic markerLib,
ThmSetData and postkernel code are not involved. Query
`splitLib.split_thms`/`named_split_thms`. Fresh-process export, rewind,
ownership repair and heap-reload fixtures are normal selftests:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/src split-persistence split-lifecycle
```

## Tests

`MANIFEST` gives module ownership. Fresh ordinary load paths,
initialization callbacks, shared controls and executable examples are checked
in `../tests/api-audit`; the complete extension integration suite is
`../tests/native-extension`, separate from the ordinary `selftest.sml`.

