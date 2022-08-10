% Release notes for HOL4, Kananaskis-14

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: 3 February 2021)

We are pleased to announce the Kananaskis-14 release of HOL4.

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

*   The special `Type` syntax for making type abbreviations can now
    map to `temp_type_abbrev` (or `temp_type_abbrev_pp`) by adding the
    `local` attribute to the name of the abbreviation.

    For example

           Type foo[local] = “:num -> bool # num”

    or

           Type foo[local,pp] = “:num -> bool # num”

    Thanks to Magnus Myreen for the feature suggestion.

*   We have added a special syntactic form `Overload` to replace
    various flavours of `overload_on` calls. The core syntax is
    exemplified by

           Overload foo = “myterm”

    Attributes can be added after the name. Possible attributes are
    `local` (for overloads that won’t be exported) and `inferior` to
    cause a call `inferior_overload_on` (which makes the overload the
    pretty-printer’s last choice).

    Thanks to Magnus Myreen for the feature suggestion.

*   The `Holmake` tool will now build multiple targets across multiple
    directories in parallel. Previously, directories were attacked one
    at a time, and parallelisation only happened within those
    directories. Now everything is done at once. The existing `-r`
    option takes on a new meaning as part of this change: it now
    causes `Holmake` to build all targets in all directories
    accessible through `INCLUDES` directives. Without `-r`, `Holmake`
    will build just those dependencies necessary for the current set
    of targets (likely files/theories in the current directory).

*   It is now possible to write `let`-expressions more smoothly inside
    monadic `do`-`od` blocks. Rather than have to write something like

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

    (The `<<-` line above is semantically identical to writing
    `y <- return E`, but is nonetheless syntactic sugar for a
    `let`-expression.)

    The pretty-printer reverses this transformation.

    Thanks to Hrutvik Kanabar for the implementation of this feature.

*   There is (yet) another high-level simplification entry-point: `gs` (standing for “global simplification”).
    Like the others in this family this has type

           thm list -> tactic

    and interprets theorems as rewrites as with the others.
    This tactic simplifies all of a goal by repeatedly simplifying goal assumptions in turn (assuming all other assumptions as it goes) until no change happens, and then finishes by simplifying the goal conclusion, assuming all of the (transformed) assumptions as it does so.

    There are three variants on this base (with the same type): `gns`, `gvs` and `gnvs`.
    The presence of the `v` indicates a tactic that eliminates variables (as is done by `rw` and some others), and the presence of the `n` causes assumptions to _not_ be stripped as they are added back into the goal.
    Stripping (turned on by default) is the effect behind `strip_assume_tac` (and `strip_tac`) when these tactics add to the assumptions.
    It causes, for example, case-splits when disjunctions are added.

    We believe that `gs` will often be a better choice than the existing `fs` and `rfs` tactics.

-   Automatic simplification of multiplicative terms over the real numbers is more aggressive and capable.
    Multiplicative terms are normalised, with coefficients being gathered, and variables sorted and grouped (*e.g.*, `z * 2 * x * 3` turns into `6 * (x * z)`).
    In addition, common factors are eliminated on either side of relation symbols (`<`, `≤`, and `=`), and occurrences of `inv` (`⁻¹`) and division are rearranged as much as possible (*e.g.*, `z * x pow 2 * 4 = x⁻¹ * 6` turns into  `x = 0 ∨ 2 * (x pow 3 * z) = 3`).
    To turn off normalisation over relations within a file, use

           val _ = diminish_srw_ss [“RMULRELNORM_ss”]

    To additionally stop normalisation, use

           val _ = diminish_srw_ss [“RMULCANON_ss”]

    These behaviours can also be turned off in a more fine-grained way by using `Excl` invocations.

-   The `Induct_on` tactic is now more generous in the goals it will work on when inducting on an inductively defined relation.
    For example, if one’s goal was

           ∀s t. FINITE (s ∪ t) ∧ s ⊆ t ⇒ some-concl

    and the aim was to do an induction using the principle associated with finite-ness’s inductive characterisation, one had to manually turn the goal into something like

           ∀s0. FINITE s0 ==> ∀s t. s0 = s ∪ t ∧ s ⊆ t ⇒ some-concl

    before applying `Induct_on ‘FINITE’`.

    Now, `Induct_on` does the necessary transformations first itself.

-   The `Inductive` and `CoInductive` syntaxes now support labelling of specific rules.
    The supported syntax involves names in square brackets in column 0, as per the following:

           Inductive dbeta:
           [~redex:]
             (∀s t. dbeta (dAPP (dABS s) t) (nsub t 0 s)) ∧
           [~appL:]
             (∀s t u. dbeta s t ⇒ dbeta (dAPP s u) (dAPP t u)) ∧
           [~appR:]
             (∀s t u. dbeta s t ⇒ dbeta (dAPP u s) (dAPP u t)) ∧
           [~abs:]
             (∀s t. dbeta s t ⇒ dbeta (dABS s) (dABS t))
           End

    The use of the leading tilde (`~`) character causes the substitution of the “stem” name (here `dbeta`) and an underscore into the name.
    Thus in this case, there will be four theorems saved, the first of which will be called `dbeta_redex`, corresponding to the first conjunct.
    If there is no tilde, the name is taken exactly as given.
    Theorem attributes such as `simp`, `compute` *etc.* can be given in square brackets after the name and before the colon.
    For example, `[~redex[simp]:]`.

    The given names are both saved into the theory (available for future users of the theory) and into the Poly/ML REPL.

-   There is a new `using` infix available in the tactic language.
    It is an SML function of type `tactic * thm -> tactic`, and allows user-specification of theorems to use instead of the defaults.
    Currently, it works with the `Induct_on`, `Induct`, `Cases_on` and `Cases` tactics.
    All of these tactics consult global information in order to apply specific induction and cases theorems.
    If the `using` infix is used, they will attempt to use the provided theorem instead.

    Thus one can do a “backwards” list induction by writing

           Induct_on ‘mylist’ using listTheory.SNOC_INDUCT

    The `using` infix has tighter precedence than the various `THEN` operators so no extra parentheses are required.

Bugs fixed:
-----------

*   In `extrealTheory`: the old definition of `extreal_add` wrongly
    allowed `PosInf + NegInf = PosInf`, while the definition of
    `extreal_sub` wrongly allowed `PosInf - PosInf = PosInf` and
    `NegInf - NegInf = PosInf`. Now these cases are unspecified, as is
    division-by-zero (which is indeed allowed for reals in
    `realTheory`). As a consequence, now all `EXTREAL_SUM_IAMGE`-
    related theorems require that there must be no mixing of `PosInf`
    and `NegInf` in the sum elements. A bug in `ext_suminf` with
    non-positive functions is also fixed.

    There is a minor backwards-incompatibility: the above changes may
    lead to more complicated proofs when using extreals, while better
    alignment with textbook proofs is achieved, on the other hand.

*   Fix soundness bug in the HolyHammer translations to first-order.
    Lambda-lifting definitions were stated as local hypothesis but
    were printed in the TPTP format as global definitions. In a few
    cases, the global definition captured some type variables causing
    a soundness issue. Now, local hypothesis are printed locally under
    the quantification of type variables in the translated formula.

New theories:
-------------

*   Univariate differential and integral calculus (based on
    Henstock-Kurzweil Integral, or gauge integral) in
    `derivativeTheory` and `integrationTheory`. Ported by Muhammad
    Qasim and Osman Hasan from HOL Light (up to 2015).

*   Measure and probability theories based on extended real numbers,
    *i.e.*, the type of measure (probability) is `α set -> extreal`.
    The following new (or updated) theories are provided:

    `sigma_algebraTheory`
      ~ Sigma-algebra and other system of sets

    `measureTheory`
      ~ Measure Theory defined on extended reals

    `real_borelTheory`
      ~ Borel-measurable sets generated from reals

    `borelTheory`
      ~ Borel sets (on extended reals) and Borel-measurable functions

    `lebesgueTheory`
      ~ Lebesgue integration theory

    `martingaleTheory`
      ~ Martingales based on sigma-finite filtered measure space

    `probabilityTheory`
      ~ Probability theory based on extended reals

    Notable theorems include: Carathéodory's Extension Theorem (for
    semirings), the construction of 1-dimensional Borel and Lebesgue
    measure spaces, Radon-Nikodym theorem, Tonelli and Fubini's
    theorems (product measures), Bayes' Rule (Conditional
    Probability), Kolmogorov 0-1 Law, Borel-Cantelli Lemma,
    Markov/Chebyshev's inequalities, convergence concepts of random
    sequences, and simple versions of the Law(s) of Large Numbers.

    There is a major backwards-incompatibility: old proof scripts
    based on real-valued measure and probability theories should now
    open the following legacy theories instead: `sigma_algebraTheory`,
    `real_measureTheory`, `real_borelTheory`, `real_lebesgueTheory`
    and `real_probabilityTheory`. These legacy theories are stil
    maintained to support `examples/miller` and
    `examples/diningcryptos`, etc.

    Thanks to Muhammad Qasim, Osman Hasan, Liya Liu and Waqar Ahmad *et
    al.* for the original work, and Chun Tian for the integration and
    further extension.

New tools:
----------

*   `holwrap.py`: a simple python script that ‘wraps’ hol in a similar
    fashion to `rlwrap`. Features include multiline input, history and
    basic StandardML syntax highlighting. See the comments at the head
    of the script for usage instructions.

New examples:
-------------

*   __algebra__: an abstract algebra library for HOL4. The algebraic
    types are generic, so the library is useful in general. The
    algebraic structures consist of `monoidTheory` for monoids with
    identity, `groupTheory` for groups, `ringTheory` for commutative
    rings, `fieldTheory` for fields, `polynomialTheory` for
    polynomials with coefficients from rings or fields, `linearTheory`
    for vector spaces, including linear independence, and
    `finitefieldTheory` for finite fields, including existence and
    uniqueness.

*   __simple_complexity__: a simple theory of recurrence loops to
    assist the computational complexity analysis of algorithms. The
    ingredients are `bitsizeTheory` for the complexity measure using
    binary bits, `complexityTheory` for the big-O complexity class,
    and `loopTheory` for various recurrence loop patterns of iteration
    steps.

*   __AKS__: a mechanisation of the AKS algorithm, contributed by
    Hing Lun Chan from his PhD work.

    The theory behind the AKS algorithm is delivered in
    __AKS/theories__, starting with `AKSintroTheory`, the
    introspective relation, culminating in `AKSimprovedTheory`,
    proving that the AKS algorithm is a primality test. The underlying
    theories are based on finite fields, hence making use of
    `finitefieldTheory` in __algebra__.

    An implementation of the AKS algorithm is shown to execute in
    polynomial-time: the pseudo-code of subroutines is given in
    __AKS/compute__, and the corresponding implementations in monadic
    style are given in __AKS/machine__, which includes a simple
    machine model outlined in `countMonadTheory` and
    `countMacroTheory`. Run-time analysis of subroutines is based on
    `loopTheory` in __simple_complexity__.

    The AKS main theorems and proofs have been cleaned up in
    `AKScleanTheory`. For details, please refer to his [PhD
    thesis](http://hdl.handle.net/1885/177195).

*   The code for training tree neural networks using
    `mlTreeNeuralNetwork` on datasets of arithmetical and
    propositional formulas is located in __AI_TNN__.

*   A demonstration of the reinforcement learning algorithm
    `mlReinforce` on the tasks of synthesizing combinators and
    Diophantine equations can be found in __AI_tasks__.

*   __bootstrap__: a minimalistic verified bootstrapped compiler.
    By bootstrapped, we mean that the compiler is applied to itself
    inside the logic. We evaluate (using EVAL) this self-application
    to arrive at an x86-64 assembly implementation of the compiler
    function.

*   __Hoare-for-divergence__: a Hoare logic for proving properties
    of (the output behaviour of) diverging programs. This Hoare
    logic has been proved sound and complete. The same directory also
    includes soundness and completeness proofs for a standard
    total-correctness Hoare logic.

*   __Lassie__: a tool for developing tactic languages by example.
    A tutorial using Lassie is included in the manual, and more details about
    the technique can be found in the corresponding [paper](https://arxiv.org/abs/2101.00930).

Incompatibilities:
------------------

*   Two new rewrites to do with disjunctions have been introduced into the automatic simplifier (and also other simpsets that derive from the fundamental `bool_ss` value).
    The rewrites are

           [lift_disj_eq]
             ⊢ (x ≠ y ∨ P ⇔ x = y ⇒ P) ∧
               (P ∨ x ≠ y ⇔ x = y ⇒ P)

           [lift_imp_disj]
             ⊢ ((P ⇒ Q) ∨ R ⇔ P ⇒ Q ∨ R) ∧
               (R ∨ (P ⇒ Q) ⇔ P ⇒ R ∨ Q)

    These can be removed with `Excl` directives, the `-*` operator or `{temp_,}delsimps`.

*   The treatment of abbreviations (introduced with `qabbrev_tac` for
    example), has changed slightly. The system tries harder to prevent
    abbreviation assumptions from changing in form; they should stay
    as `Abbrev(v = e)`, with `v` a variable, for longer. Further, the
    tactic `VAR_EQ_TAC` which eliminates equalities in assumptions and
    does some other forms of cleanup, and which is called as part of
    the action of `rw`, `SRW_TAC` and others, now eliminates
    “malformed” abbreviations. To restore the old behaviours, two
    steps are required:

           val _ = diminish_srw_ss ["ABBREV"]
           val _ = set_trace "BasicProvers.var_eq_old" 1

    which invocation can be made at the head of script files.

*   The theorem `rich_listTheory.REVERSE` (alias of
    `listTheory.REVERSE_SNOC_DEF`) has been removed because `REVERSE`
    is also a tactical (`Tactical.REVERSE`).

*   `listTheory` and `rich_listTheory`: Some theorems have been
    generalized.

    For example, `EVERY_{TAKE, DROP, BUTLASTN, LASTN}` had unnecessary
    preconditions. As a result of some theorems being generalized,
    some `_IMP` versions of the same theorems have been dropped, as
    they are now special cases of the non-`_IMP` versions.

    Also, `DROP_NIL` has been renamed to `DROP_EQ_NIL`, to avoid
    having both `DROP_nil` and `DROP_NIL` around. Furthermore, `>=` in
    the theorem statement has been replaced with `<=`.

*   Renamed theorems in `pred_setTheory`: `SUBSET_SUBSET_EQ` became
    `SUBSET_ANTISYM_EQ` (compatible with HOL Light).

*   The theorem `SORTED_APPEND_trans_IFF` has been moved from
    `alist_treeTheory` into `sortingTheory`. The moved theorem is now
    available as `SORTED_APPEND`, and the old `SORTED_APPEND` is now
    available as `SORTED_APPEND_IMP`. To avoid confusion, as
    `SORTED_APPEND` is now an (conditional) equality,
    `SORTED_APPEND_IFF` has been renamed to `SORTED_APPEND_GEN`.

*   The definition `SORTED_DEF` is now an automatic rewrite, meaning
    that terms of the form `SORTED R (h1::h2::t)` will now rewrite to
    `R h1 h2 /\ SORTED (h2::t)` (in addition to the existing automatic
    rewrites for `SORTED R []` and `SORTED R [x]`). To restore the old
    behaviour it is necessary to exclude `SORTED_DEF` (use
    `temp_delsimps`), and reinstate `SORTED_NIL` and `SORTED_SING`
    (use `augment_srw_ss [rewrites [thmnames]]`).

*   The syntax for *greater than* in `intSyntax` and `realSyntax` is
    consistently named as in `numSyntax`: The functions
    `great_tm`,`dest_great` and `mk_great` become `greater_tm`,
    `dest_greater` and `mk_greater`, respectively. Additionally,
    `int_arithTheory.add_to_great` is renamed to
    `int_arithTheory.add_to_greater`.

*   Two theorems about `list$nub` (the constant that removes
    duplicates in a list), have been made automatic:
    `listTheory.nub_NIL` (`⊢ nub [] = []`) and
    `listTheory.all_distinct_nub` (`⊢ ∀l. ALL_DISTINCT (nub l)`).
    Calls to `temp_delsimps` can be used to remove automatic rewrites
    as necessary.

*   The SML API for `ThmSetData` has changed; user-provided call-backs that apply set-changes (additions and removals of theorems) are only ever called with single changes at once rather than lists, so the required types for these call-backs has changed to reflect this.

*   Parsing of `~x` has been changed so that this is always preferentially interpreted as being a boolean operation.
    This may break proofs over types with a numeric negation that use expressions such as

           SPEC “~x” some_theorem

    It is much better style to use `Q.SPEC ‘~x’ some_theorem`; and indeed one can also use `-` as a unary operator, so that `Q.SPEC ‘-x’ some_theorem` will also work.

    If a big script is broken by this, one can reinstate the old behaviour by changing the grammar locally with

           Overload "~"[local] = “numeric_negation_operator”

    where the appropriate negation operator might be, *e.g.*, `“$real_neg”`.

*   Two theorems about `TAKE` and `DROP` have been added to the stateful simplifier:

           TAKE_LENGTH_ID_rwt2
           ⊢ ∀l m. TAKE m l = l ⇔ LENGTH l ≤ m

           DROP_EQ_NIL
           ⊢ ∀l m. DROP m l = [] ⇔ LENGTH l ≤ m

    The former is a new theorem; the latter is an existing theorem that has been promoted to “automatic” status.
    Use `Excl` or `{temp_,}delsimps` to remove these theorems from the simplifier as necessary.

*   The `BIGINTER_SUBSET` theorem in `pred_setTheory` has changed from

           ⊢ ∀sp s. (∀t. t ∈ s ⇒ t ⊆ sp) ∧ s ≠ ∅ ⇒ BIGINTER s ⊆ sp

    to

           ⊢ ∀sp s t. t ∈ s ∧ t ⊆ sp ⇒ BIGINTER s ⊆ sp

* * * * *

<div class="footer">
*[HOL4, Kananaskis-14](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-13.release.html)

</div>
