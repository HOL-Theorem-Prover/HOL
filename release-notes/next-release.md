% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: xxxxxx)

We are pleased to announce the ????? release of HOL4.

Contents
--------

-   [New features](#new-features)
-   [Bugs fixed](#bugs-fixed)
-   [New theories](#new-theories)
-   [New tools](#new-tools)
-   [New examples](#new-examples)
-   [Incompatibilities](#incompatibilities)
-   [Deprecations](#deprecations)

New features
------------
-   `PFTWriter` writes binary proof traces using the version 1 format.
    `PFTReader` checks the magic, version, ruleset and four-namespace footer;
    the HOL replayer rejects Candle traces before executing commands.


-   A new theorem attribute, `datatype_simp`, says how a datatype's induction principle should be phrased.

    A type that recurses under an operator gets induction hypotheses stated through that operator's set function, which is correct but is not how a development states its own lemmas, so proofs normalise them by hand at every induction.
    Theorems tagged `datatype_simp` are now used to normalise the principle of every type declared after them.
    With nothing tagged the hypotheses are rephrased only, by pulling out the existentials the operators leave and unwinding the resulting equalities; tagging the set functions' own laws takes `(∀e0. (∃p. e0 ∈ setSND p ∧ MEM p l) ⇒ P e0)` to `(∀x e0. MEM (x,e0) l ⇒ P e0)`.
    What a principle says is therefore a development's decision rather than the package's.

    The principle as the construction stated it is kept alongside, and `TypeBase.set_induction_of` returns it.
    Code that reads a principle should use that: `TypeBase.induction_of` now gives whatever the ambient `datatype_simp` theorems have made of it.

-   HOL4’s algebraic datatype definition machinery now implements the *Bounded Natural Functors* idea due to Traytel *et al.*, which has underpinned Isabelle type definitions for a decade or more.
    This allows easy definition of types that recurse under type oprerators such as finite sets, finite maps, and on the right of function arrows.
    The package now automatically defines map, set and relator constants for those types that are themselves functors (*e.g.*, lists), and the user can specify what names they want for those new constants.

-   `Theory` syntax now supports disabling the generation of documentation in `<thyname>Theory.sig` by following the theory name with the `[no_sig_docs]` annotation.
    Files that use this feature do not need to mention `Feedback.set_trace "TheoryPP.include_docs" 0` anymore.
    (Indeed, see below, that trace doesn’t exist with that name anymore.)

-   Lists and finite-map updates (previously achieved with `LUPDATE v i l` and `fm |+ (k,v)` syntax) can now be written with a syntax using the “maps to” arrow and special bracket delimiters.
    For `LUPDATE v i l`, one can write `l❲i ↦ v❳`, and for `fm |+ (k,v)`, one can write `fm⟨k ↦ v⟩`.
    Moreover, such updates can be chained into lists of updates between the brackets.
    For example, `fm⟨k1 ↦ v1; k2 ↦ v2⟩` represents `fm |+ (k2,v2) |+ (k1,v1)`.

    Finally, the corresponding application/selection terms can be written with the brackets around the key values: `fm⟨k⟩` for `fm ’ k`, and `l❲i❳` for `EL i l`.
    The old syntax continues to work in both cases, but the new forms are preferred when terms are printed.

-   The emacs-mode has moved its “remove Unicode” functionality to the key-binding `M-h u -`, and has added an “add Unicode” function under `M-h u +` which is roughly the inverse.
    (These functions affect either the entirety of the source buffer, or the selected region.)

    The old `M-h C-u` binding which toggles Unicode pretty-printing in the output `*HOL*` buffer has now moved to `M-h u p`.

-   There is now an LSP client (invoked under the hood by `hol lsp`, though this is unlikely to be something that users will invoke directly).
    The Visual Studio extension (available on the [Microsoft](https://marketplace.visualstudio.com/items?itemName=HOL4Developers.hol4-vscode) and [open source](https://open-vsx.org/extension/HOL4Developers/hol4-vscode/) marketplaces) will start the server appropriately.
    For `emacs`, the following is required in users’ `.emacs` or `init.el` files:

           (hol-lsp-enable)                       ; does everything
           (setq hol-lsp-goals-follow-cursor t)   ; *HOL Goals* follows point

    The emacs LSP client shares keys with the older `*HOL*`-process mode so commands like `M-h M-r`, `M-h s`, `M-h m`, `M-h M`, `M-h p`, `M-h g` and `M-h i` do LSP-analogues of what happens in the emacs REPL-mode.

-   `bin/build` has two new flags that control how per-entry HTML pages for `help/Docfiles/*.smd` are produced.
    By default, if `mdbook` is on the user's PATH, `build_help` now invokes the Manual/Reference mdbook target so that the generated `help/src-sml/htmlsigs/<struct>.html` pages link straight into the rendered reference book.
    When `mdbook` is absent, the fallback runs a single-shot `pandoc` pass to emit `help/Docfiles/HTML/<entry>.html` (one pandoc invocation total, not one per entry).
    `bin/build --no-mdbook` forces the fallback even when mdbook is present, and `bin/build --no-helpdocs` skips the entire help-documentation build (no docfile processing, no mdbook, no help DB) -- useful for partial build sequences that don't compile every HOL library and so can't successfully evaluate every polyscripter `>>` directive.

-   `Holmake` recognises a project-root marker file `holproject.toml`: dropping one at the top of a multi-directory development tells `Holmake` that every directory below is part of the same project, and the usual sub-directory `INCLUDES = ../sibling` lines tying them together can be dropped.
    Cross-directory rule and source resolution (`open Foo` from one dir reaching a `Foo.sml` in a sibling, `Ancestors X` in a theory script reaching a sibling's theory products) then works automatically across the project.
    The file is a small TOML document declaring at minimum the project name; optionally also an `[exclude]` list, an `external_includes` list (for dirs outside the project tree that act as implicit `INCLUDES` of every project dir), and `[projects.<id>]` tables for dependencies on other projects.
    A sibling `holproject.local.toml` is gitignored and lets individual developers override `[projects.<id>].path` values.
    Project mode activates only when `Holmake` is invoked from inside a project (or at its root); a `--no-project` flag suppresses it altogether.
    Duplicate source names across project directories (which would make `open Foo` ambiguous) abort the build with a pointer at `[exclude]` as the remedy.
    The `name` key also registers the project's directory in `holpathdb`, replacing the old `.holpath` marker file (whose only content was a single line naming the directory); any in-tree or downstream `.holpath` files must be migrated to a `holproject.toml` containing `name = "<the-old-content>"`.
    An optional top-level `holmake = false` key turns project mode off for that file while keeping `holpathdb` registration and `external_includes` inheritance live (used in the HOL repository itself).
    An optional `[h4pedant]` section configures the style-check tool with a global line-length limit, a `unicode_ok` toggle, an `exclude` list of skipped subdirectories, and a `[[h4pedant.dir]]` array of per-subdirectory overrides; `h4pedant` with no positional arguments walks up to find the project root and scans the whole tree.

    Projects nest: a sub-directory carrying its own `holproject.toml` heads a separate project, governed by its own file rather than the enclosing one's, and `Holmake -r` and `--dirs` account for that.
    Two diagnostics guard the nesting: a project that points into an enclosing project it has not declared with `[projects.<id>]` is warned about, and any key `holproject.toml` does not recognise is reported rather than quietly discarded — a `[project.<id>]` typo for `[projects.<id>]` otherwise reads as correct and behaves as absent.

    See the *Project files* sub-section of *Maintaining HOL Formalizations with Holmake* in the DESCRIPTION manual.

-   Holmake now uses recorded build times to do its parallel scheduling of build tasks.
    This can make a big difference to wall clock times when building big projects.
    Further, a project can now commit a *seed* of build times for this purpose, so that a fresh checkout schedules well before it has measured anything itself.
    A seed should appear in a `build-times` file beside `holproject.toml` (or wherever a new `build_times` key in that file points).
    The seed file is read-only and any locally measured value overrides it, so it matters only until a target has been built once locally.
    Generate one with `developers/gen-build-times`.

-   `Holmake` has a new flag `--dirs` that re-interprets the positional command-line arguments as *root directories* to operate on, rather than build targets.
    `Holmake --dirs d1 d2 …` is semantically similar to running `Holmake` in each of `d1`, `d2`, … in turn, but fuses the work into a single dependency graph dispatched under one parallel scheduler.
    Each root contributes its own “must build” targets (the first target of its `Holmakefile`, with the same plausible-targets fallback as a bare `Holmake`).

-   `Holmake` (under Poly/ML) understands a new per-directory `Holmakefile` variable, `LOCAL_PARALLELISM_LIMIT = n`, which caps the total number of concurrent jobs the parallel scheduler will allow whenever a target from that directory is dispatched.
    `n = 1` gives a directory's targets exclusive access — useful for memory-heavy theory builds that would otherwise OOM when run alongside other jobs under `-j N`.
    `n = 2` allows at most two concurrent jobs total while any of this directory's targets is running, and so on.

-   `Holmake` (under Poly/ML) takes a new option `--retry-oos=n`, which allows each target up to `n` further attempts when its build fails with the Poly/ML runtime reporting that it has run out of store.

-   `bossLib` provides three new short names for common tactics:
    * `have ‘t’` states an intermediate result, leaving it as the first subgoal and adding it (stripped) to the assumptions of the other; it is the tactic already available as `sg`.
    * `suff ‘t’` replaces the goal with a sufficient condition, leaving `t ==> goal` as the first subgoal; it is already available as `qsuff_tac`;
    * `contr` starts a proof by contradiction, and is an abbreviation for `SPOSE_NOT_THEN STRIP_ASSUME_TAC`.

-   `Holmake --strict-outputs` fails a rule whose command exits successfully without creating the target it was supposed to create.
    Without the flag such a rule draws a warning instead, which is the default for now.
    Exempt are phony targets, which name no file; commands whose errors the Holmakefile has already said to ignore with a leading `-`; and the earlier commands of a multi-command rule, only the last of which is expected to have produced the target.

Bugs fixed
----------

-   A definition that recursed through a higher-order function was saved with the recursive call eta-expanded.
    Writing `g n (Nd ts) = Nd (MAP (g n) ts)` stored `MAP (\a. g n a) ts`, which matches neither a goal nor a lemma stated the way it was written, so proofs unfolding such a definition carried an `SF ETA_ss` step to compensate.
    Recursions through `MAP` and `EVERY` with a substitution-like extra parameter have exactly this shape.

    TFL eta-expands such a call on the way in, because a partial application has no other form while the function's arguments are being tupled.
    The expansion is now undone before the equations and the induction principle are saved, so both say what was written.
    A definition whose value genuinely is an abstraction, and a lambda written over a tuple, are left alone.

-   `bin/hol` reading a script on its standard input, *e.g.*, something like `$(HOLDIR)/bin/hol < build.ML`, reported success however badly the script went.
    A failing run now properly exits with failure.

    An uncaught exception is deliberately not treated the same way: the declarations after it still run and the run still succeeds, because the script did reach its end.

-   `Holmake -r` now overrides `--no_prereqs`, as the documentation has always said it does.

-   Three kernel bugs (github issues [#1838](https://github.com/HOL-Theorem-Prover/HOL/issues/1838), [#1839](https://github.com/HOL-Theorem-Prover/HOL/issues/1839), and [#1840](https://github.com/HOL-Theorem-Prover/HOL/issues/1840)) in CV-compute were fixed.
    Thanks to Ramana Kumar for finding these!

-   We also fixed another [kernel soundness bug](https://github.com/HOL-Theorem-Prover/HOL/issues/1870) found by Ramana Kumar in the technology used to push constants from `bool` back into the kernel.

-   The contextual decision-procedure cache used by the arithmetic simpset fragments (`numSimps.ARITH_ss`, `realSimps.REAL_ARITH_ss`, `intSimps.OMEGA_ss`/`COOPER_ss`, and `bagSimps.SBAG_SOLVE_ss`) was unbounded.
    In long-running sessions the cache accumulated entries — both in number of cached goals and in the per-key list of `(context, result)` pairs under each goal — and `simp` invocations slowed down approximately linearly with session length, dominated by linear scans of the per-key list under `boolSyntax.F`.
    The cache now uses LRU eviction on the keyspace and a per-key list cap, with both bounds set at cache-creation time.
    See the `Cache.sig` header for the new `{capacity, per_key_cap}` constructor argument.

-   metis's finite-model heuristic, which weights clauses by how often they hold in a model of the axioms, sampled its valuations from a single random generator created when `mlibModel` was loaded and never reset, and numbered its models from a counter with the same lifetime — a number that is hashed into the model's interpretation.
    Every metis call therefore started from whatever state the previous one left behind, so what a goal cost depended on what had been proved before it in the same session: repeats of one identical relevant-logic proof in a single process ranged from 0.5s to 40s, and the theory containing it built in either 5.6s or 32s depending only on how far the generator had advanced.
    Each model now carries its own generator, and both that and the model's identity are seeded from the structure of the problem being refuted, so which models a call gets no longer depends on its predecessors.
    The two models behind `mlibSupport`'s probable-tautology filter are likewise built per call rather than once per process, which also stops their memoisation caches growing for the lifetime of the session.
    Repeats of one goal still search slightly differently, because HOL's CNF names skolem constants from a genvar counter and model interpretations are md5-derived from those names; that residual is in the naming rather than in metis.
    `developers/bench-metis-order.sml` measures what is left.

New theories
------------

-  `lebesgue_measure`: The equivalence of Lebesgue and Gauge integration.
   A (measurable) function is Lebesgue integrable iff it is Gauge absolutely integrable.
   Theorems in this theory (*e.g.*, `lebesgue_eq_gauge_integral`, `lebesgue_eq_gauge_integral_alt`, *etc.*) can be used to calculate concrete Lebesgue integrals found in Probability applications, etc. (in form of `integral lborel (Normal o f)` where `f IN borel_measurable borel`) by Fundamental Theorem of Calculus (FTC) from `integration` theory, if the anti-derivative of `f` is known (or computable by external CAS software).

New tools
---------

New examples
------------

-   The LaTeX munging technology has a tutorial document in the `examples/latex-generation` directory.

-  `examples/lambda/barendregt`: new theories (`solvable`, `boehm`, `lameta_complete`, `separability`, etc.) containing a formalisation of Böhm trees, Böhm's separation theorem for untyped λ-calculus, completeness of λη-equational theory, Wadsworth's theorem (solvable iff has hnf), Takahashi's modern proofs about η-reduction, etc.

Incompatibilities
-----------------

-   The return types of `parse_term.mk_prec_matrix`, `type_grammar.parse_map`, `type_grammar.privileged_abbrevs`
    have been changed to return maps of type HOLdict instead of Binarymap.

-   `Preterm.eq` has been replaced with `Preterm.veq` which returns `true` if and only if the two arguments are variables with the same names and types.

-   We have implemented a new policy forbidding theory names from being SML or HOL keywords (*e.g.,* `case`, `while`, `of`, …, `Theorem`, `Theory`, `Definition`, …).
    The theories `while` and `functor` have been renamed to `While` and `category_functor`, respectively, in accordance with this.

-   The `examples/fun-op-sem` directory has been renamed `examples/pl-semantics`.

-   The `examples/balanced_bst` directory has been renamed `examples/data-structures/balanced_bst`;
    the script file `examples/zipper/zipperScript.sml` has been moved to `examples/data-structures`;
    the script file `examples/balanced_bst/AVL_treeScript.sml` has been moved to a directory of its own at `examples/data-structures/AVL_tree`.

-   The left-hand side of `LIST_REL_MAP2` has been changed from `LIST_REL (\a b. R a b) l1 (MAP f l2)` to
    `LIST_REL R l1 (MAP f l2)`. We do not expect this to break proof scripts, but document this change here just in case.

-   A few theorems (ended with `'`) in `real_sigmaTheory` are renamed to avoid naming conflicts
    with `realaxTheory`, or to better reflect their nature (see the table below for details.)
    In particular, users are recommended to *not* directly open `realaxTheory` (an intermediate
    theory for constructing real numbers), in which all useful theorems should be also covered by
   `realTheory` (under same or different theorem names).

    |  Old name       | New name           | Statements                                    |
    | --------------- | ------------------ | --------------------------------------------- |
    | `REAL_LE_SUP'`  | `REAL_LE_SUP2`     | `!s a b y. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s` |
    | `REAL_LE_MUL'`  | `REAL_LE_MUL_NEG`  | `!x y. x <= 0 /\ y <= 0 ==> 0 <= x * y`       |
    | `REAL_LT_MUL'`  | `REAL_LT_MUL_NEG`  | `!x y. x < 0 /\ y < 0 ==> 0 < x * y`          |
    | `REAL_LT_LMUL'` | `REAL_LT_LMUL_NEG` | `!x y z. x < 0 ==> (x * y < x * z <=> z < y)` |
    | `REAL_LT_RMUL'` | `REAL_LT_RMUL_NEG` | `!x y z. z < 0 ==> (x * z < y * z <=> y < x)` |

-   For better compatibility with HOL Light (making code-porting easier), arithmetic theory’s `GREATER_EQ` theorem (stating *m ≥ n ⇔ n ≤ m*) is now also available in that theory under the name `GE`.

-   As above, `Cache.CACHE` and `Cache.RCACHE` (used to build cached versions of contextual decision procedures) now take a `{capacity:int, per_key_cap:int}` record argument as their first parameter.
    `capacity` bounds the number of distinct goal terms held in the cache (LRU-evicted when exceeded); `per_key_cap` bounds the list of `(context, result)` pairs stored under each goal (oldest pair dropped when exceeded).
    Direct callers must update their constructor invocations; in-tree callers (`numSimps`, `realSimps`, `intSimps`, `bagSimps`) have been updated to pass `{capacity=2000, per_key_cap=32}`.

-   The function `Parse.remove_user_printer` now returns `unit`.

-   The precedence of the `MOD`-infix’s syntax has been changed to bring it line with convention elsewhere: instead of being tighter then multiplication but looser than exponentiation, it now lives at the same precedence level as multiplication.
    To restore it to its old level/behaviour, use the following declaration at the head of relevant `*Script.sml` files:

           val _ = temp_set_fixity "MOD" (Infixl 650)

    (If one over-arching change is desired, dropping the `temp_` prefix and putting the declaration in a root script-file will install the change for all of one’s theories.)

-   The order of the list of type variables given by `Type.type_vars` and `Term.type_vars_in_term` have changed. User code should be written to not depend on this anyway.

-   The trace `TheoryPP.include_docs` has been renamed to `TheoryPP.include_html_docs`.
    Note that the now-preferred way to have documentation omitted is to add the `[no_sig_docs]` annotation to the `Theory` declaration at the head of a `..Script.sml` file.

-   The `ind_type` theory and the `ind_types` structure have been removed.
    They implemented the original (Harrison) datatype construction, which carved every declared type out of a universal `:α recspace`.
    The BNF package now builds everything `Datatype`/`Hol_datatype` accepts, and builds it faster, so nothing was left for the older construction to do. `recspace` and its constants (`CONSTR`, `FCONS`, `FNIL`, `BOTTOM`) are gone, as is the `ind-type` OpenTheory package.

-   A datatype declaration that recurses through an operator holding none of its argument — `t = C of 'a => t itself` — is now rejected rather than built.
    Such a declaration never said anything: `τ itself` has exactly one inhabitant whatever `τ` is, so the argument carries no information and the type it would pin is already fixed by the constructor's result; `t = C of 'a => t itself` is isomorphic to `t = C of 'a`.
    An `itself` argument over a *parameter* rather than over the type being declared — a field of type `'a itself` pinning a type variable that occurs nowhere else — does not recurse and is unaffected.

-   `ind_types.munge_ind_thm` is now `legacyInduction.munge_ind_thm`.

Deprecations
------------

-   `Triviality` has been deprecated and may be removed in the future.
    Please update theorems of the form `Triviality foo` and `Triviality foo[..]` to
    `Theorem foo[local]` and `Theorem foo[local,..]` respectively to avoid future breakage.

* * * * *

<div class="footer">
*[HOL4, ?????](http://hol-theorem-prover.org)*

[Release notes for the previous version](trindemossen-2.release.html)

</div>
