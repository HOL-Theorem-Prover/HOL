# Focused simpExtLib contracts

Run from the repository root, once `simpExtLib` is available:

```
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/simp-ext -j1 check
```

`check` builds **and executes** `selftest.exe`, `tracked.exe`,
`exclusions.exe`, `strategies.exe`, `tactics.exe`, `sources.exe`,
`derivation.exe` and `lifetimes.exe`. Building
`.uo` files alone is not validation. The production `simp-ext` target runs it
at `HOLSELFTESTLEVEL=1`. Deliberately ill-typed clients of the two
engines are in `../type-boundaries` (Poly/ML only).

## Construction and compiled clients

The ordinary PURE/BOOL catalog reaches extension simpsets through
`simpExtLib.lift_ssfrag` and `simpExtLib.lift_simpset`; a lifted `bool_ss`
retains the ordered recipe `PURE -> BOOL -> NOT -> CONG -> UNWIND`.

`APIExamples.sml` elaborates clients against the actual production
modules. It checks the complete recipe catalog, explicit ordinary-reducer
lifting, configured reducers, both **extension-typed** projections, argument
preparation, bundle installation, and immutable AC/TypeBase/relational/threaded
factory inputs, plus explicit public congruence-fragment lifting and typed
congruence construction. No fake implementation or legacy projection adapter
is used.

## Semantic checks

- BOOL beta/boolean rewrites and contextual COND congruences; opt-in ETA and
  logical-binder exclusions.
- Saved live conditional depth observes changes to the shared
  `Cond_rewr.stack_limit` in both directions; explicit zero/40 overrides it
  without mutating it. Recursive conditional proofs compare conclusions and
  complete hypothesis sets; recursive side-condition rewrites are not tracked.
- Explicit opaque lifting preserves collector/application payload identity and
  relation/reflexivity callbacks, creates no source inventory, and distinguishes
  construction-once default collection from per-application configured refresh.
- Late projection extraction after exhaustion, in both orders; original/view
  quota sharing, source identity/order, partial/exhausted preserving replay,
  explicit reset replay, preserving filtering and source suspension. No getter
  compilation, maker callback or compilation trace is allowed.
- Prepared bundle combination retains bindings and partially spent actual
  controls; duplicate bindings fail rather than refreshing allowances.
- Parent/child-first overlapping rewrites, charging, argument-only root
  preservation, reusable private normalization with exhausted native quotas,
  and restoration on success and observer exceptions with exact payloads.
- Same-name ordinary/extension typed registries remain independent. Saved SF
  tactics resolve late, follow replacement/Context rewind, and fail when absent.
  SF's shared string-marker syntax does not permit cross-registry fallback.
- One Trace listener and one tracking extent observe both engines. Two distinct
  rules per engine fired alternately are reported in firing order. Nesting in
  both directions isolates inner reports and restores outer tracking, including
  a foreign exception leaving the nested extent.

Closed rewrite fixtures check both sides of each conversion theorem and empty
hypotheses, not just the resulting term. Open conditional fixtures compare the
complete expected theorem/hypothesis set. Saved-tactic checks run through
`VALID`. Context snapshots, listeners and the global depth control are restored.

## Tracked compiler gate

`tracked.sml` adds focused installation, identity and actual-control tests:
projection extraction before use, after partial use and after exhaustion in
both directions; duplicate slots/events, AC components and shared conjuncts;
persistent filtering and preserving replay; cached matcher rebinding versus
explicit reset; compilation/collector order and failure staging; inert getters
and explicit directive preparation; incompatible changed-maker statements;
private alias allowances and exceptional/nested restoration. Proof checks
compare complete expected conclusions and hypothesis sets.

The inventory getter `rewrite_sources` now rejects directives. First call
`prepare_rewrite_arguments` explicitly and inspect its returned set/rules.
This is bounded tracked-compiler acceptance, not exhaustive view/bundle
validation or performance acceptance.

## Exclusion and replay gate

`exclusions.sml` adds 159 checks on explicitly tracked objects. Both default
and configured projections are extracted/used in both orders. Complete
conclusions and hypothesis sets, not just endpoints, are compared.

| New block | Preserved original coverage / additional intersection |
| --- | --- |
| `A deleted conjunct` | native source/view deletion and partial-quota replay; literal/resolved deletion plus preserving removal/filtering of mixed native/prepared sources; surviving identity/order and actual sharing |
| `Failed extended resolution` | native namespace resolution and unmatched literal history; pending duplicate failures must leave old inventory/control state intact |
| `Strict and resolved histories` | native strict-history theory rewind; preserving reconstruction fails/succeeds under the same contract without refreshing live/exhausted controls |
| `Prohibition is distinct` | native named-fragment removal/strategy replay; force-add, duplicates, no-op identity, exact maker/opaque-collector ordering, limits and retained prohibition |
| `Namespace separation` | native strategy namespace/split suppression; ordinary loopers colliding with split/case displays survive suppression, later additions and preserving replay |

No original assertion is moved or relaxed. `../native-extension` still runs
its native checks, including parser/warning/ambiguity contracts, strategy
targets, local/ambient split suppression, mixed views and failures.
Dependent-view invalidation is covered under
"Sources, views and prepared bundles" below.

Only extension-owned `looper_tac` changes: split/case suppression applies to
split loopers, not unrelated ordinary names. Resolution, private history order,
strict reparsing versus resolved replay, and ordinary-reset versus explicit
preserving-control replay stay unchanged. There is no legacy-history identity
inference, new ordinary import, or ordinary representation change.

## Configured tactics and strategies

`strategies.sml` adds **186 checks / 63 executed validations**;
`tactics.sml` adds **88 checks / 18 executed validations**. All proofs are
kernel-derived; residual goals are actually proved, returned validations
called, and complete hypotheses and ordered goals compared.

| New coverage | Original provenance / added intersection |
| --- | --- |
| Final/condition solvers | Native safe/unsafe pipeline; list replacement/removal/order, invalid conclusions/hypotheses, alpha-equivalent contexts, recursion and exact exception payloads |
| Configured controls | Native live depth, custom order and root rewrite tests; saved conversions/tactics, shared default versus explicit depth |
| Loopers | Native replacement/round-limit tests; zero/one/multiple/unlimited rounds, UNCHANGED/failure/exception behavior, changed subgoal restart and saved reuse |
| Counted globals | Native mutual-assumption/fixpoint/root/implication groups; ordered branching and real reconstruction, counted unchanged rotations, conclusion fixpoint reentry and one invocation-wide looper budget |
| Child-first passes | Native child-first overlap; explicit traversal order and configured global reconstruction; private derivation restoration is covered under "Child-first derivation and solver lifetimes" below |
| Supplied invocation binding | Once rules across looper siblings, both traversal policies and saved reuse; final solvers receive untagged facts even when a maker drops their rewrites; Abbr failure precedes FRAG/binding on repeated explicit and configured-alias invocations, while label lookup remains earlier |
| Nested directives | Requirement/multiply-bound-qualified SF and Split execute; genuine multiply-bounded rewrites retain the original theorem, selected bound, full hypotheses and live exhaustion; ReqD failures retain provenance; wrapped assumption policy, label and abbreviation options, including non-global ReqD failure retention |
| Bound local replay | Native `bound_global_fixture`; independent spent ambient quota plus partially spent/exhausted installed bundle and attached view, exact maker/collector schedule, zero bundle/view recompilation traces, same adjusted object observed by loopers and old saved conversions |
| Generic isolation | Generic classifier/tactic forwards extension markers inertly, no new split set/attribute registrations |

No fallback promotion or ordinary API is involved.
Local replay preserves all installed controls directly, rather than resetting
then repairing only the bundle via a second history replay. Installed view
matchers (including rejected shapes) are cached immutably in extension history;
replay checks source compatibility and rebinds only actual counters. Explicit
ordinary-reset replay still refreshes declared allowances. A public excluded
addition returns its exact input before entering compilation.

`APIExamples.sml` compiles explicit strategy, global, child-first and bound
clients. Help examples use `simpExtLib`/`TraverseExt` and tracked recipes.

## Sources, views and prepared bundles

`sources.sml` adds **404 checks**. Conversion checks compare complete conclusions and hypothesis
sets of kernel-derived expected proofs, not just rewritten endpoints.

| New block | Original provenance / added intersection |
| --- | --- |
| Inventory order | Native views/AC/duplicate fixtures; exact fragment/conjunct/component order and native versus installed-view visibility |
| Invalidation matrix | Native view/suspension/filter/removal fixtures; both projections and native/prepared installation after partial use or exhaustion; dependent views disappear while siblings keep actual sharing through replay |
| Statement compatibility | Native stale/support views and changed-maker case; changed conclusion/hypotheses/declared bound invalidate installed aliases and old handles, whereas a different proof of the same statement shares exhaustion |
| Nested composition | Native prepared/composed fixtures; partially spent conjuncts plus exhausted and live independent bindings, complete grouping/install order, duplicate rejection before callbacks, preserving versus reset replay |
| Rejected/foreign views | Cached rejected matcher shapes never recompile; foreign handles cannot invent identities or borrow another binding's control |
| Source reinstallation | A compatible bundle reinstalled after its surviving old view event does not retroactively install that alias; explicit new attachment shares original controls and invalidation works in both directions |
| Alternative installations | The same prepared event/source/index may carry different aliases in separate sets; changed conclusions/hypotheses demand rebuild while equal compiled statements with different proofs/generalization do not; all still share actual controls |
| Opaque context | Native suspension context fixture; exact surviving conjunct facts and exception payload identity through replay in both projection orders |
| Context/key changes | Native strategy invalidation fixture; keyed replacement reports both keys, keyless/opaque changes rebuild, lost view dependencies rebuild even with surviving history events, compatible replay/consumption does not |

Trace listeners count successful and rejected compilation attempts. Getter and
composition checks additionally make makers/collectors throw if invoked.
Prepared originals and both attached views replay without compilation;
ordinary-reset replay refreshes only declared groups, not old saved controls.

`rewrite_context_changes` now compares active compatible view dependencies
and compiled statements in installation order, not only history-event identity
or final membership. All work remains extension-owned; no legacy
allocation, cache, representation, registration or callback path changes.

## Child-first derivation and solver lifetimes

`derivation.sml` adds **1,392 checks**, including 270 prior review-regression
checks and 276 checks for post-abort dispatch and nested continuations.
The pre-existing assertions are retained. `lifetimes.sml` adds **315 checks**,
including 252 selected-child congruence invocation/rejection assertions.
Both launchers run under the normal `check`/selftest-level-1 targets.

| New coverage | Original provenance / added intersection |
| --- | --- |
| Private scopes | Native `prepared_normalization_fixture` and observed preparation: native, bundle, aliases and conjunct groups, partial/exhausted counters, exactly declared uses, saved normalize/arguments reuse and root preservation |
| Failure/restoration | Observer, charge and head-policy callbacks after a bounded rewrite; exact HOL_ERR, foreign payload and Interrupt propagation; same-object nested success and all three failures, restoration of partially spent outer and caller counters |
| Failed candidates | Unchanged child and failed condition observations, unchanged charges and proofs; rejected conditional candidate leaves a shared sibling allowance inside the private scope |
| Opaque clients | Lifted reducer, unsafe solver and congruence collector errors after consumption; ordinary HOL_ERR rejection remains rejection, foreign exceptions/interrupts abort, and exhausted caller controls survive |
| Preparation/reuse | Inert prepare/save/pretest, per-application versus per-child context collection, exact maker/collector counts, no installed-rule recompilation or allowance refresh |
| Pretest abort lifetime | Nonopaque plain/observed pretests recover immediately and after normalization, for HOL_ERR/foreign/Interrupt; no charge, observation or quota reset; caught nested pretest failures preserve partially spent outer quotas |
| Direct native ETA abort | Descent-created ETA candidates propagate exact HOL_ERR/foreign/Interrupt, no repeated callback after abort; saved direct conversions recover without refilling spent caller allowances |
| Post-abort dispatch | Direct, prepared normalize, observed normalize and arguments; repeated HOL_ERR/foreign/Interrupt aborts stop failing and successful fallback conversions; ordinary conversion errors still try both fallbacks, with full proof/hypothesis validation |
| Nested aborts | Recursive native conversions, conditional rewrites and opaque reducer recursion cannot run enclosing fallback candidates, later reducers, solver continuations or observers after abort; standalone argument normalization cannot call a child after policy failure |
| Root entries | Native root contracts plus exact priority/fallback and collector counts, no root fixpoint or descent, retained solver-only context separation |
| Solver closures | Native generic context/stack contracts plus same-data nested use, retained recurse closures, old-context generation identity after later application/failure, exact opaque callback traces |
| Eta/congruence | Native head/eta policy plus saved live predicate and selected descent/unchanged congruence blocking; direct, observed and argument-only policy aborts retain identity and recover on reuse |
| Selected child abort | Generic, observed and abort-hook child-first entries; repeated HOL_ERR/foreign/Interrupt from selected descent cannot invoke failing or successful fallback congruences or other callbacks; exact factory schedule and saved proof recovery; ordinary HOL_ERR rejection, UNCHANGED, foreign/Interrupt and success keep their callback order |

Existing `../traverse-ext/selftest.sml` keeps live default depth, explicit
integer depth, custom order, root-condition full traversal, context ordering,
capture avoidance, default/configured factory schedules, limit rollback and
unchanged observer/reducer/solver/charge counts. `strategies.sml` retains
safe/unsafe solver validation, counted global passes, looper limits and real
proof reconstruction.
