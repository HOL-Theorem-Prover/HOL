% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: )

We are pleased to announce the ?????? release of HOL 4.

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

*   The special `Type` syntax for making type abbreviations can now map to `temp_type_abbrev` (or `temp_type_abbrev_pp`) by adding the `local` attribute to the name of the abbreviation.

    For example

           Type foo[local] = “:num -> bool # num”

    or

           Type foo[local,pp] = “:num -> bool # num”

    Thanks to Magnus Myreen for the feature suggestion.

*   We have added a special syntactic form `Overload` to replace various flavours of `overload_on` calls.
    The core syntax is exemplified by

           Overload foo = “myterm”

    Attributes can be added after the name.
    Possible attributes are `local` (for overloads that won’t be exported) and `inferior` to cause a call `inferior_overload_on` (which makes the overload the pretty-printer’s last choice).

    Thanks to Magnus Myreen for the feature suggestion.

*   It is now possible to write `let`-expressions more smoothly inside monadic `do`-`od` blocks.
    Rather than have to write something like

           do
             x <- M1;
             let y = E
             in
               do
                 z <- M2 x y;
                 return (f z);
               od
           od

    one can replace the `let`-bindings with uses of the `<<-` arrow:

           do
             x <- M1;
             y <<- E;
             z <- M2 x y;
             return (f z)
           od

    (The `<<-` line above is semantically identical to writing `y <- return E`, but is nonetheless syntactic sugar for a `let`-expression.)

    The pretty-printer reverses this transformation.

    Thanks to Hrutvik Kanabar for the implementation of this feature.

* A weaker version of TacticToe relying on a few selected tactics
  that does not require any recording is available under the names
  `tactictoe_mini` and `ttt_mini`.

Bugs fixed:
-----------

*  `extrealTheory`: the old definition of `extreal_add` wrongly allows
   `PosInf + NegInf = PosInf`, while the definition of `extreal_sub` wrongly
    allows `PosInf - PosInf = PosInf` and `NegInf - NegInf = PosInf`. Now
    these cases are unspecified, so is division-by-zero (which is indeed
    allowed for reals in `realTheory`). As a consequence, now all
   `EXTREAL_SUM_IAMGE`-related theorems require that there must be no
    mixing of `PosInf` and `NegInf` in the sum elements.
    A bug in `ext_suminf` with non-positive functions is also fixed.

    There is a minor backwards-incompatibility: the above changes may
    lead to more complicated proofs when using extreals, while better
    alignments with textbook proofs are achieved, on the other hand.

*   Fix soundess bug in the HolyHammer translations to first-order.
    Lambda-lifting definitions were stated as local hypothesis but
    were printed in the TPTP format as a global definition.
    In a few cases, the global definition captures some type variables
    causing a soundess issue. Now, local hypothesis are printed
    locally under the quantification of type variables in the translated
    formula.

New theories:
-------------

*  `derivativeTheory` and `integrationTheory`: univariate
    differential and integral calculus (based on Henstock-Kurzweil
    Integral, or gauge integral), ported by Muhammad Qasim and Osman
    Hasan from HOL Light (up to 2015).

*   HOL now provides measure and probability theories based on extended real
    numbers, i.e. the type of measure (probability) is `('a set) -> extreal`.
    The following new (or updated) theories are provided:

        sigma_algebraTheory      * Sigma-algebra and other system of sets
        measureTheory            * Measure Theory defined on extended reals
        real_borelTheory         * Borel-measurable sets generated from reals
        borelTheory              * Borel sets (extreal) and Borel measurable functions
        lebesgueTheory           * Lebesgue integration theory
        martingaleTheory         * Martingales based on sigma-finite filtered measure space
        probabilityTheory        * Probability Theory based on extended reals

    Notable theorems include: Caratheory's Extension Theorem (for semiring),
    the construction of 1-dimensional Borel and Lebesgue measure spaces,
    Radon-Nikodym theorem, Tonelli and Fubini's theorems (product measures),
    Bayes' Rule (Conditional Probability),
    Kolmogorov 0-1 Law, Borel-Cantelli Lemma, Markov/Chebyshev's inequalities,
    convergence concepts of random sequences, and simple versions of
    the Law(s) of Large Numbers.

    There is a major backwards-incompatibility: old proof scripts based on
    real-valued measure and probability theories should now open the following
    legacy theories instead: `sigma_algebraTheory`, `real_measureTheory`,
   `real_borelTheory`, `real_lebesgueTheory` and `real_probabilityTheory`.
    These legacy theories are stil maintained to support __examples/miller__ and
    __examples/diningcryptos__, etc.

    Thanks to Muhammad Qasim, Osman Hasan, Liya Liu and Waqar Ahmad et al. for
    the original work, and Chun Tian for the integration and further extension.

New tools:
----------

*  `holwrap.py`: a simple python script that 'wraps' hol in a similar fashion
    to rlwrap. Features include multiline input, history and basic StandardML
    syntax highlighting.
    See the comments at the head of the script for usage instructions.

New examples:
-------------

*  __algebra__: an abstract algebra library for HOL4. The algebraic types
    are generic, so the library is useful in general.
    The algebraic structures consist of
    `monoidTheory` for monoids with identity, `groupTheory` for groups,
    `ringTheory` for commutative rings, `fieldTheory` for fields,
    `polynomialTheory` for polynomials with coefficients from rings or fields,
    `linearTheory` for vector spaces, including linear independence, and
    `finitefieldTheory` for finite fields, including existence and uniqueness.

*  __simple_complexity__: a simple theory of recurrence loops to assist the
    computational complexity analysis of algorithms. The ingredients are
    `bitsizeTheory` for the complexity measure using binary bits,
    `complexityTheory` for the big-O complexity class,
    and `loopTheory` for various recurrence loop patterns of iteration steps.

*  __AKS__: the mechanisation of the AKS algorithm, contributed by Hing Lun Chan
    from his PhD work.

    The theory behind the AKS algorithm is delivered in __AKS/theories__,
    starting with `AKSintroTheory`, the introspective relation,
    culminating in `AKSimprovedTheory`, proving that the AKS algorithm is a primality test.
    The underlying theories are based on finite fields, hence making use of
    `finitefieldTheory` in __algebra__.

    An implementation of the AKS algorithm is shown to execute in polynomial-time:
    the pseudo-codes of subroutines are given in __AKS/compute__, and the corresponding
    implementations in monadic style are given in __AKS/machine__, which includes a
    simple machine model outlined in `countMonadTheory` and `countMacroTheory`.
    Run-time analysis of subroutines is based on `loopTheory` in __simple_complexity__.

    The AKS main theorems and proofs have been cleaned up in `AKScleanTheory`.
    For details, please refer to his [PhD thesis](http://hdl.handle.net/1885/177195).

* The code for training tree neural networks using `mlTreeNeuralNetwork` on
  datasets of arithmetical and propositional formulas is
  located in __AI_TNN__.

* A demonstration of the reinforcement learning algorithm `mlReinforce`
  on the tasks of synthesizing combinators and Diophantine equations
  can be found in __AI_tasks__.

Incompatibilities:
------------------

*   The treatment of abbreviations (introduced with `qabbrev_tac` for example), has changed slightly.
    The system tries harder to prevent abbreviation assumptions from changing in form; they should stay as `Abbrev(v = e)`, with `v` a variable, for longer.
    Further, the tactic `VAR_EQ_TAC` which eliminates equalities in assumptions and does some other forms of cleanup, and which is called as part of the action of `rw`, `SRW_TAC` and others, now eliminates “malformed” abbreviations.
    To restore the old behaviours, two steps are required:

           val _ = diminish_srw_ss ["ABBREV"]
           val _ = set_trace "BasicProvers.var_eq_old" 1

    which invocation can be made at the head of script files.

*   The theorem `rich_listTheory.REVERSE` (alias of `listTheory.REVERSE_SNOC_DEF`)
    has been removed because `REVERSE` is also a tactical (`Tactical.REVERSE`).

*  `listTheory` and `rich_listTheory`: Some theorems have been generalized.

    For example, `EVERY_{TAKE, DROP, BUTLASTN, LASTN}` had unnecessary preconditions.
    As a result of some theorems being generalized, some `_IMP` versions of the same
    theorems have been dropped, as they are now special cases of the non-`_IMP` versions.

    Also, `DROP_NIL` has been renamed to `DROP_EQ_NIL`, to avoid having both `DROP_nil`
    and `DROP_NIL` around. Furthermore, `>=` in the theorem statement has been replaced with `<=`.

*   Renamed theorems in `pred_setTheory`: `SUBSET_SUBSET_EQ` -> `SUBSET_ANTISYM_EQ`
    (compatible with HOL Light).

* The theorem `SORTED_APPEND_trans_IFF` has been moved from `alist_treeTheory` into `sortingTheory`.
  The moved theorem is now available as `SORTED_APPEND`, and the old `SORTED_APPEND` is now available as `SORTED_APPEND_IMP`.
  To avoid confusion, as `SORTED_APPEND` is now an (conditional) equality, `SORTED_APPEND_IFF` has been renamed to `SORTED_APPEND_GEN`.

*   The definition `SORTED_DEF` is now an automatic rewrite, meaning that terms of the form `SORTED R (h1::h2::t)` will now rewrite to `R h1 h2 /\ SORTED (h2::t)` (in addition to the existing automatic rewrites for `SORTED R []` and `SORTED R [x]`).
    To restore the old behaviour it is necessary to exclude `SORTED_DEF` (use `temp_delsimps`), and reinstate `SORTED_NIL` and `SORTED_SING` (use `augment_srw_ss [rewrites [thmnames]]`).

* The syntax for *greater than* in `intSyntax` and `realSyntax` is consistently
  named as in `numSyntax`: The functions `great_tm`,`dest_great` and `mk_great`
  become `greater_tm`, `dest_greater` and `mk_greater`, respectively.
  Additionally, `int_arithTheory.add_to_great` is renamed to
  `int_arithTheory.add_to_greater`.

*   Two theorems about `list$nub` (removes duplicates in a list), have been made automatic: `listTheory.nub_NIL` (`⊢ nub [] = []`) and `listTheory.all_distinct_nub` (`⊢ ∀l. ALL_DISTINCT (nub l)`).
    Calls to `temp_delsimps` can be used to remove these as necessary.

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-13.release.html)

</div>
