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

-   `bin/build` has two new flags that control how per-entry HTML
    pages for `help/Docfiles/*.smd` are produced.  By default, if
    `mdbook` is on the user's PATH, `build_help` now invokes the
    Manual/Reference mdbook target so that the generated
    `help/src-sml/htmlsigs/<struct>.html` pages link straight into
    the rendered reference book.  When `mdbook` is absent, the
    fallback runs a single-shot `pandoc` pass to emit
    `help/Docfiles/HTML/<entry>.html` (one pandoc invocation total,
    not one per entry).  `bin/build --no-mdbook` forces the fallback
    even when mdbook is present, and `bin/build --no-helpdocs` skips
    the entire help-documentation build (no docfile processing, no
    mdbook, no help DB) -- useful for partial build sequences that
    don't compile every HOL library and so can't successfully
    evaluate every polyscripter `>>` directive.

-   `Holmake` has a new flag `--dirs` that re-interprets the
    positional command-line arguments as *root directories* to
    operate on, rather than build targets.
    `Holmake --dirs d1 d2 …` is semantically similar to running
    `Holmake` in each of `d1`, `d2`, … in turn, but fuses the
    work into a single dependency graph dispatched under one
    parallel scheduler.
    Each root contributes its own “must build” targets (the
    first target of its `Holmakefile`, with the same
    plausible-targets fallback as a bare `Holmake`).
    Each root's `INCLUDES` traversal starts from its own
    ancestor chain, so mutual references between sibling roots
    no longer trip the `INCLUDES`-loop detector — a workaround
    users previously approximated with multiple `-I` flags but
    that could fail.
    Genuine cycles within a single root's `INCLUDES` chain are
    still reported.

-   `Holmake` (under Poly/ML) understands a new per-directory
    `Holmakefile` variable, `LOCAL_PARALLELISM_LIMIT = n`, which
    caps the total number of concurrent jobs the parallel
    scheduler will allow whenever a target from that directory
    is dispatched.  `n = 1` gives a directory's targets
    exclusive access — useful for memory-heavy theory builds
    that would otherwise OOM when run alongside other jobs
    under `-j N`.  `n = 2` allows at most two concurrent jobs
    total while any of this directory's targets is running,
    and so on.  An invalid right-hand side (non-integer, zero,
    negative, multiple tokens) is reported with a warning and
    the declaration is then ignored.  The variable has no
    effect under Moscow ML (whose `Holmake` is always
    sequential) or under Poly/ML `Holmake -j 1`.

-   `Holmake` recognises a project-root marker file
    `holproject.toml`: dropping one at the top of a multi-directory
    development tells `Holmake` that every `Holmakefile`-bearing
    directory below is part of the same project, and the usual
    sub-directory `INCLUDES = ../sibling` lines tying them together
    can be dropped.  Cross-directory rule and source resolution
    (`open Foo` from one dir reaching a `Foo.sml` in a sibling,
    `Ancestors X` in a theory script reaching a sibling's theory
    products) then works automatically across the project.  The
    file is a small TOML document declaring at minimum the project
    name; optionally also an `[exclude]` list, an
    `external_includes` list (for dirs outside the project tree
    that act as implicit `INCLUDES` of every project dir), and
    `[projects.<id>]` tables for dependencies on other projects.
    A sibling `holproject.local.toml` is gitignored and lets
    individual developers override `[projects.<id>].path` values.
    Project mode activates only when `Holmake` is invoked from
    inside a project (or at its root); a `--no-project` flag
    suppresses it altogether.  Duplicate source names across
    project directories (which would make `open Foo` ambiguous,
    HOL having no per-project namespaces) abort the build with a
    pointer at `[exclude]` as the remedy.  The `name` key also
    registers the project's directory in `holpathdb`, replacing
    the old `.holpath` marker file (whose only content was a
    single line naming the directory); any in-tree or downstream
    `.holpath` files must be migrated to a `holproject.toml`
    containing `name = "<the-old-content>"`.  See the *Project
    files* sub-section of *Maintaining HOL Formalizations with
    Holmake* in the Description manual.

Bugs fixed
----------

-   Three kernel bugs (github issues [#1838](https://github.com/HOL-Theorem-Prover/HOL/issues/1838), [#1839](https://github.com/HOL-Theorem-Prover/HOL/issues/1839), and [#1840](https://github.com/HOL-Theorem-Prover/HOL/issues/1840)) in CV-compute were fixed.
    Thanks to Ramana Kumar for finding these!

-   We also fixed another [kernel soundness bug](https://github.com/HOL-Theorem-Prover/HOL/issues/1870) found by Ramana Kumar in the technology used to push constants from `bool` back into the kernel.

-   `help/Docfiles/*.smd` entries had embedded polyscripter `>>` ML transcript directives (`>>`, `>>__`, `##eval`, etc.) but the pipeline that derived `help/Docfiles/*.txt` for the in-HOL `help` command, and the one that produced `entries.tex` for `Manual/Reference/reference.pdf`, both fed the raw markdown through pandoc without evaluating the directives.
    The plain-text and PDF reference manuals therefore showed literal `>>` blockquote-mangled source instead of evaluated examples.
    Both pipelines now consume a polyscripter-evaluated mirror of the Docfiles directory (produced at `Manual/build/Docfiles-processed/` during `build_help`); the mdbook Reference manual is also routed through the same mirror to share the single polyscripter pass.
    The new pipeline invokes `pandoc` once per output format (rather than once per file) by concatenating the processed entries with sentinels and splitting the result, dropping the per-`help/Docfiles` build-step wall time from tens of seconds to a couple.
    See `help/src-sml/process_docfiles.sml`; closes [#1834](https://github.com/HOL-Theorem-Prover/HOL/issues/1834).

-   The contextual decision-procedure cache used by the arithmetic simpset fragments (`numSimps.ARITH_ss`, `realSimps.REAL_ARITH_ss`, `intSimps.OMEGA_ss`/`COOPER_ss`, and `bagSimps.SBAG_SOLVE_ss`) was unbounded.
    In long-running sessions the cache accumulated entries — both in number of cached goals and in the per-key list of `(context, result)` pairs under each goal — and `simp` invocations slowed down approximately linearly with session length, dominated by linear scans of the per-key list under `boolSyntax.F`.
    The cache now uses LRU eviction on the keyspace and a per-key list cap, with both bounds set at cache-creation time.
    See the `Cache.sig` header for the new `{capacity, per_key_cap}` constructor argument.

New theories
------------

-  `lebesgue_measure`: The equivalence of Lebesgue and Gauge integration.
   A (measurable) function is Lebesgue integrable iff it is Gauge absolutely
   integrable. Theorems in this theory (e.g., lebesgue_eq_gauge_integral,
   lebesgue_eq_gauge_integral_alt, etc.) can be used to calculate concrete
   Lebesgue integrals found in Probability applications, etc. (in form of
  `integral lborel (Normal o f)` where `f IN borel_measurable borel`) by
   Fundamental Theorem of Calculus (FTC) from `integration` theory, if the
   anti-derivative of `f` is known (or computable by external CAS software).

New tools
---------

New examples
------------

-   The LaTeX munging technology has a tutorial document in the `examples/latex-generation` directory.

-  `examples/lambda/barendregt`: new theories (`solvable`, `boehm`,
   `lameta_complete`, `separability`, etc.) containing a formalisation
   of Böhm trees, Böhm's separation theorem for untyped λ-calculus,
   completeness of λη-equational theory, Wadsworth's theorem (solvable
   iff has hnf), Takahashi's modern proofs about η-reduction, etc.

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

-   `Cache.CACHE` and `Cache.RCACHE` (used to build cached versions of contextual decision procedures) now take a `{capacity:int, per_key_cap:int}` record argument as their first parameter.
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
