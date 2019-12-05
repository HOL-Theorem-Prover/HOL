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

    There is a major backwards-incompatibility: the above changes may
    lead to more complicated proofs when using extreals, while better 
    alignments with textbook proofs are achieved, on the other hand.

New theories:
-------------

*  `derivativeTheory` and `integrationTheory`: univariate
    differential and integral calculus (based on Henstock-Kurzweil
    integral, or generalized Riemann integral, or gauge integral),
    ported by Muhammad Qasim, Osman Hasan et al. from HOL Light (up to 2015).

*  `measureTheory`, `lebesgueTheory`, `martingaleTheory` and `probabilityTheory`:
    the type of measure/probability has been upgraded
    from `('a set) -> real` to `('a set) -> extreal`, better aligned with
    modern textbooks. Many new theorems were added.

    There is a major backwards-incompatibility: old proof scripts
    using real-valued measure and probability theory should now
    instead open `sigma_algebraTheory`, `real_measureTheory`,
    `real_borelTheory`, `real_lebesgueTheory` and `real_probabilityTheory`.

*  `sigma_algebraTheory`: the pure set-theoretic theory of sigma-algebra
    has been moved from `measureTheory` into a dedicated `sigma_algebraTheory`,
    adding also some other system of sets (ring, semiring, and dynkin system).
    This theory is now shared by both `measureTheory` and `real_measureTheory`.

*  `borelTheory`: the extreal-based Borel space and Borel-measurable
    sets is now moved from `measureTheory` into `borelTheory` with
    many new theorems added.

    There is a minor backwards-incompatibility: some old proof scripts using
   `measureTheory` should now also open `sigma_algebraTheory` and `borelTheory`.

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


Incompatibilities:
------------------

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-13.release.html)

</div>
