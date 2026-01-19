% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: xxxxxx)

We are pleased to announce the Trindemossen 1 release of HOL4.
We have changed the name (from Kananaskis) because of the kernel change reflected by the new efficient compute tool (see [below](#verified-comp)).

Contents
--------

-   [New features](#new-features)
-   [Bugs fixed](#bugs-fixed)
-   [New theories](#new-theories)
-   [New tools](#new-tools)
-   [New Examples](#new-examples)
-   [Incompatibilities](#incompatibilities)

New features:
-------------

- The `HOL_CONFIG` environment variable is now consulted when HOL sessions begin, allowing for a custom `hol-config` configuration at a non-standard location, or potentially ignoring any present hol-config.
  If the variable is set, any other hol-config file will be ignored.
  If the value of `HOL_CONFIG` is a readable file, it will be used.

- There is a new theorem attribute, `unlisted`, which causes theorems to be saved/stored in the usual fashion but kept somewhat hidden from user-view.
  Such theorems can be accessed with `DB.fetch`, and may be passed to other tools though the action of other attributes, but will not appear in the results of `DB.find` and `DB.match`, and will not occur as SML bindings in theory files.

- `Holmake` will now look for `.hol_preexec` files in the hierarchy surrounding its invocation.
  The contents of such files will be executed by the shell before `Holmake` begins its work.
  See the DESCRIPTION manual for more.

- `Holmake` (at least under Poly/ML) now stores most of the products of theory-building in a “dot”-directory `.holobjs`.
  For example, if `fooScript.sml` is compiled, the result in the current directory is the addition of `fooTheory.sig` only.
  The files `fooTheory.sml`, `fooTheory.dat`, `fooTheory.uo` and `fooTheory.ui` are all deposited in the `.holobjs` directory.
  This reduces clutter.

- Paralleling the existing `Excl` form for removing specific theorems from a simplifier invocation, there is now a `ExclSF` form (also taking a string argument) that removes a simpset fragment from the simplifier.
  For example

           > simp[ExclSF "BOOL"] ([], “(λx. x + 1) (6 + 1)”);
           val it = ([([], “(λx. x + 1) 7”)], fn)

  where the `BOOL` fragment includes the treatment of β-reduction.

Bugs fixed:
-----------

- Fix [a failure to define a polymorphic datatype with name `a`](https://github.com/HOL-Theorem-Prover/HOL/issues/1140).

New theories:
-------------

- A theory of "contiguity types", as discussed in the paper _Specifying Message Formats with Contiguity Types_, ITP 2021. (DOI: [10.4230/LIPIcs.ITP.2021.30](https://doi.org/10.4230/LIPIcs.ITP.2021.30))

  Contiguity types express formal languages where later parts of a
  string may depend on information held earlier in the string. Thus
  contig types capture a class of context-sensitive languages. They
  are helpful for expressing serialized data containing, for example,
  variable length arrays. The soundness of a parameterized matcher is
  proved.

- `permutes`: The theory of permutations for general and finite sets, originally
  ported from HOL-Light's `Library/permutations.ml`.

- `keccak`: Defines the SHA-3 standard family of hash functions, based on the
  Keccak permutation and sponge construction. Keccak256, which is widely used
  in Ethereum, is included and was the basis for this work. A rudimentary
  computable version based on sptrees is included; faster evaluation using
  cvcompute is left for future work.

New tools:
----------

-   The linear decision procedure for the reals (`REAL_ARITH`, `REAL_ARITH_TAC`
    and `REAL_ASM_ARITH_TAC`) have been updated by porting the latest code from
    HOL-Light. There are two versions: those in the existing `RealArith` package
    only support integral-valued coefficients, while those in the new package
   `RealField` support rational-valued coefficients (this includes division of
    reals, e.g. `|- x / 2 + x /2 = x` can be proved by `RealField.REAL_ARITH`).
    Users can explicitly choose between different versions by explicitly opening
   `RealArith` or `RealField` in their proof scripts. If `realLib` were opened,
    the maximal backward compatibilities are provided by first trying the old
    solver (now available as `RealArith.OLD_REAL_ARITH`, etc.) and (if failed)
    then the new solver. Some existing proofs from HOL-Light can be ported to
    HOL4 more easily.

-   New decision procedure for the reals ported from HOL-Light: `REAL_FIELD`,
   `REAL_FIELD_TAC` and `REAL_ASM_FIELD_TAC` (in the package `RealField`). These
    new tools first try `RealField.REAL_ARITH` and then turn to new solvers
    based on calculations of Grobner's Basis (from the new package `Grobner`).

-   **Multiplying large numbers more efficiently**:

    In `src/real` there is a new library `bitArithLib.sml` which improves the
    performance of large multiplications for the types `:num` and `:real`.
    The library uses arithmetic of bitstrings in combination with the Karatsuba
    multiplication algorithm.
    To use the library, it has to be loaded before the functions that should be
    evaluated are **defined**.

- <a name="verified-comp">**Fast in-logic computation primitive**:</a>
  A port of the Candle theorem prover's primitive rule for computation,
  described in the paper *"Fast, Verified Computation for Candle"* (ITP 2023),
  has been added to the kernel.  The new compute primitive works on certain
  operations on a lisp-like datatype of pairs of numbers:

           Datatype: cv = Pair cv cv
                        | Num num
           End

  This datatype and its operations are defined in `cvScript.sml`, and the
  compute primitive `cv_compute` is accessible via the library
  `cv_computeLib.sml` (both in `src/cv_compute`).

  There is also new automation that enables the use of `cv_compute` on
  functional HOL definitions which do not use the `:cv` type.  In particular,
  `cv_trans` translates such definitions into equivalent functions operating
  over the `:cv` type.  These can then be evaluated using `cv_eval`, which uses
  `cv_compute` internally.  Both `cv_trans` and `cv_eval` can be found in the
  new `cv_transLib`.

  Some usage examples are located in `examples/cv_compute`.  See the
  DESCRIPTION manual for a full description of the functionality offered by
  `cv_compute`.

  NB. To support `cv_compute`, the definitions of `DIV` and `MOD` over natural
  numbers `num` have been given specifications for the case when the second
  operand is zero. We follow HOL Light and Candle in defining `n DIV 0 = 0` and
  `n MOD 0 = n`. These changes make `DIV` and `MOD` match the way Candle's
  compute primitive handles `DIV` and `MOD`.

-   **Polarity-aware theorem-search**. Extending what is available through `DB.find` and `DB.match`, the `DB.polarity_search` allows the user to search for explicitly negative or positive occurrences of the specified pattern.
    Thanks to Eric Hall for this contribution.

New examples:
-------------

-  **Dependability Analysis**:
   Dependability is an umbrella term encompassing Reliability, Availability and Maintainability.
   Two widely used dependability modeling techniques have been formalized namely, Reliability Block Diagrams (RBD) and Fault Trees (FT).
   Both these techniques graphically analyze the causes and factors contributing the functioning and failure of the system under study.
   Moreover, these dependability techniques have been highly recommended by several safety standards, such as IEC61508, ISO26262 and EN50128,
for developing safe hardware and software systems.

   The new recursive datatypes are defined to model RBD and FT providing compositional features in order to analyze complex systems with arbitrary
number of components.

           Datatype: rbd = series (rbd list)
                         | parallel (rbd list)
                         | atomic (α event)
           End

           Datatype: gate = AND (gate list)
                          | OR (gate list)
                          | NOT gate
                          | atomic (α event)
           End

   Some case studies are also formalized and placed with dependability theories, for illustration purposes, including smart grids, WSN data transport protocols, satellite solar arrays, virtual data centers, oil and gas pipeline systems and an air traffic management system.

-   __large_numberTheory__ (in `examples/probability`): various versions of The Law of Large Numbers (LLN) of Probability Theory.

    Some LLN theorems (`WLLN_uncorrelated` and `SLLN_uncorrelated`) previously in `probabilityTheory`
    are now moved to `large_numberTheory` with unified statements.

-   __Vector and Matrix theories__ (in `examples/vector`) translated from HOL-Light's `Multivariate/vectors.ml`.

-   __Relevant Logic__ (in `examples/logic/relevant-logic`): material contributed by James Taylor, mechanising a number of foundational results for propositional relevant logic.
    Three proof systems (two Hilbert, one natural deduction) are shown equivalent, and two model theories (the Routley-Meyer ternary-relation Kripke semantics, and Goldblatt’s “cover” semantics) are shown sound and complete with respect to the proof systems.

-   __armv8-memory-model__ (in `examples/arm`): a port by Anthony Fox of Viktor Vafeiadis’s [Coq formalization of the Armv8 Memory Model](https://github.com/vafeiadis/arm-model), which is based on the official [mixed-size Armv8 memory model](https://github.com/herd/herdtools7/blob/95785c747750be4a3b64adfab9d5f5ee0ead8240/herd/libdir/aarch64.cat) and associated [paper](https://doi.org/10.1145/3458926).

-   __*p*-adic numbers__ (in `examples/padics`): a construction of the *p*-adic numbers by Noah Gorrell.
    The approach taken defines the prime valuation function *ν* on first the natural numbers and then the rationals.
    It then defines the absolute value on ℚ so as to establish a $p$-metric.
    Cauchy sequences over these can be constructed and quotiented to construct a new numeric type.
    The new type `adic` is polymorphic such that the cardinality of the universe of the argument defines the prime number *p* of the construction.
    For types that have infinite or non-prime universes, *p* is taken to be 2.
    Thus, `:2 adic`, `:4 adic` and `:num adic` are isomorphic types, but `:3 adic` is distinct.
    Addition, multiplication and injection from the rationals are defined.

Incompatibilities:
------------------

*   Some new automatic rewrites to do with natural number arithmetic (particularly exponentiation) have been added.
    The most potentially disruptive of these is probably `LT1_EQ0`, which states

           ⊢ n < 1 ⇔ n = 0

    The other new rewrites will simplify terms such as `10 < 2 ** x` (where both the base of the exponentiation and the other argument to the relation are numerals).
    By taking a natural number logarithm, it is possible to turn the above into `3 < x` and `5 ** n < 10654` into `n ≤ 5`.
    The theorems to exclude (using `Excl`, or `temp_delsimps`, or ...) if these new rules break proofs are: `EXP_LE_LOG_SIMP`, `EXP_LT_LOG_SIMP`, `LE_EXP_LOG_SIMP`, `LT_EXP_LOG_SIMP`, `LOG_NUMERAL`, `EXP_LT_1`, `ONE_LE_EXP`, and `TWO_LE_EXP`.

*   The small `productTheory` (products of natural numbers and real numbers, ported from HOL-Light) has been merged into `iterateTheory` (on which `extrealTheory` now depends).

*   Changes in the `formal-languages/context-free` example:

    -   The location type (defined in `locationTheory`) has been simplified
    -   The PEG machinery now has a simple error-reporting facility that attempts to report the end of the longest prefix of the input that might still be in the PEG’s language.
        This means that instead of returning either `SOME result` or `NONE`, PEGs now return a custom `Success`/`Failure` data type with values attached to both constructors.

*   The `MEMBER_NOT_EMPTY` theorem in `bagTheory` has been renamed to `BAG_MEMBER_NOT_EMPTY` to avoid a name-clash with a theorem of the same name in `pred_setTheory`.

*   The “global” simplification tactics (`gs`, `gvs` *et al*) have been adjusted to simplify older assumptions before later ones.
    This will keep assumption *A* in the list if it is newer (more recently added) than, and equivalent to, older assumption *B*.
    The new `rgs` is like the old `gs`.

*   The infix operator `..` from `iterateTheory` is now called `numseg` and is parsed/printed as `{m .. n}` (a “close-fix” operator).
    This brings the syntax into line with `listRangeTheory`’s `[m..n]` syntax.
    In many contexts, expressions with this had to use parentheses as delimiters, and so fixing the incompatibility will require turning something like `(t1..t2)` into `{t1..t2}`.
    However, the old style did allow `e ∈ m..n`, which no longer works without the braces.

*   Due to internal dependency changes, `Diff.DIFF_CONV` (a conversion for proving
    differentiate expressions) is not included in `realLib` any more. Users of `DIFF_CONV`
    should explicitly open `Diff` in proof scripts.

*   The internally-stored names (`string` values) for various simpset fragments have been changed to lose `_ss` suffixes.
    For example, though the `BETA_ss` fragment still appears under that name in the SML namespace, the name it has stored internally is now just `"BETA"`.
    This change makes the naming consistent across all of HOL’s fragments.
    These names are used when referring to fragments in calls to `diminish_srw_ss`, when using `ExclSF` (see above), and in printing the values in the REPL.

*   In `sigma_algebraTheory`, the definition of `measurable` has been generalized without requiring that the involved systems of sets must be σ-algebras.
    This change allows the user to express measurable mappings over generators of σ-algebras (cf. `MEASURABLE_LIFT` for a related important lemma).
    Existing proofs may break in two ways (both are easy to fix):
        1. The need for extra antecedents (usually easily available) when applying some existing measure and probability theorems.
        2. When proving `f IN measurable a b`, some proof branches regarding σ-algebras no longer exists (thus the related proof scripts must be eliminated).

*   Both the `Definition` syntax when a `Termination` argument has been provided, and the underlying `TotalDefn.tDefine` function, won’t now make schematic definitions unless they have been explicitly allowed.
    (With the `Definition` syntax, this is done by using the `schematic` attribute.)
    This brings this flavour of definition into line with the others, where the presence of extra free variables on the RHS of a definition’s equation is usually flagged as an error.

*   In `real_topologyTheory`, some definitions (only the theorem names but not the
    underlying logical constants) have been renamed to avoid conflicts with
    similar definitions in `seqTheory`: from `sums` to `sums_def`, from
    `summable` to `summable_def`. Besides, `infsum` has been renamed to
    `suminf_def` to reflect its overloading to `suminf`. (All these definitions
    are generalized versions of those in `seqTheory`.)

*   The constant `lg` (logarithm with base 2) has moved from the `util_prob` theory to `transc`.

*   The theories under `src/ring/src` have all been prefixed with the string `EVAL_` reflecting the way they are exclusively used within the system, to provide polynomial normalisation using reflection and `computeLib`.
    This frees up the name `ring` to be used only by the material under `examples/algebra`.
    (In the absence of this change, theories that depended on what was in `src/ring/src` could not be used in a development alongside what is in `examples/algebra`.)

*   It is now an error to bind the same name twice in a theory.
    Binding names is what happens when theorems are saved or stored, or when definitions are made.
    These names appear in the exported *thy*`Theory.sig` files.
    Previously, rebound values would replace old ones with only a warning interactively.
    Now an exception is raised.
    In some circumstances when rebinding is appropriate, the `allow_rebind` annotation can be used to permit the behaviour.
    For example:

           Theorem foo: p /\ q <=> q /\ p
           Proof DECIDE_TAC
           QED

           Theorem foo[allow_rebind]: p \/ q <=> q \/ p
           Proof DECIDE_TAC
           QED

    The content of the theorem is irrelevant; any attempt to rebind will cause an error.
    Programmatically, the trace variable `Theory.allow_rebinds` can be set to `1` to allow the old behaviour.
    Thus, the following could be done at the head of a script file to completely turn off checking for the whole file

           val _ = set_trace "Theory.allow_rebinds" 1

    Rebinding is permitted dynamically when the `Globals.interactive` flag is true so that interactive development of theories is not hindered.

*   One error detected by the above change was in `examples/miller/`’s `extra_bool` theory.
    This defines an `xor` operator and included two successive theorems:

           [xor_F] : !p. p xor F = p
           [xor_F] : !p. F xor p = p

    The failure to flag the second as an error meant that the theorem called `xor_F` completely masked the rewrite in the opposite direction.
    The fix was to rename the second `xor_F` to now be `F_xor`, which is an incompatibility if your theory depends on `extra_boolTheory`.

*   The labels for clauses/rules in the “modern” `Inductive` syntax are now syntactically equivalent to conjunctions, so what used to be written as something like

           Inductive reln:
           [~name1:] (!x y. x < y ==> reln (x + 1) y) /\
           [~sym:]
              (!x y. reln x y ==> reln y x) /\
           [~zero:]
              (!x. reln x 0)
           End

    should now be written

           Inductive reln:
           [~name1:] (!x y. x < y ==> reln (x + 1) y)
           [~sym:]
              (!x y. reln x y ==> reln y x)
           [~zero:]
              (!x. reln x 0)
           End

     where all of the trailing/separating conjunctions have been removed.
     The parentheses around each clause above can also be removed, if desired.

     Attempting to mix labels and top-level conjunctions will lead to very confusing results: it’s best to only use one or the other.
     If you do not wish to name rules, you can use any of the following as “nullary” labels: `[]`, `[/\]`, or `[∧]`.
     As with normal labels, these need to occur in column zero.

     The first rule need not have a label at all, so that

           Inductive reln:
              !x y. x < y ==> reln (x + 1) y
           [/\]
              !x y. reln x y ==> reln y x
           [~zero:]
              !x. reln x 0
           End

     will work.
     It will also work to switch to conjunctions for trailing rules:

           Inductive reln:
           [~name1:] !x y. x < y ==> reln (x + 1) y
           [~sym:]
              (!x y. reln x y ==> reln y x) /\
              (!x. reln x 0) /\
              (!y. reln 100 y)
           End

*   A number of theories embodying the “old” approach to measure theory and probability (using a real number as a set’s measure rather than an extended real) have moved from `src/probability` to `examples/probability/legacy`.
    These theories are still used by the dependability analysis example mentioned above, and by the verification of the probabilistic Miller-Rabin primality test (`examples/miller`).
    The effect of this is that the default build of the system will not build these theories; `Holmake` will build them when used in their new directory.

*   The mechanisation of temporal logic that used to live in `src/temporal` has been moved to `examples/logic/temporal`.

* * * * *

<div class="footer">
*[HOL4, Trindemossen 1](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-14.release.html)

</div>
