% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: xxxxxx)

We are pleased to announce the ?????? release of HOL4.

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

New theories:
-------------

- A theory of "contiguity types", as discussed in the paper _Specifying Message Formats with Contiguity Types_, ITP 2021. (DOI: [10.4230/LIPIcs.ITP.2021.30](https://doi.org/10.4230/LIPIcs.ITP.2021.30))

  Contiguity types express formal languages where later parts of a
  string may depend on information held earlier in the string. Thus
  contig types capture a class of context-sensitive languages. They
  are helpful for expressing serialized data containing, for example,
  variable length arrays. The soundness of a parameterized matcher is
  proved.

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

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-14.release.html)

</div>
