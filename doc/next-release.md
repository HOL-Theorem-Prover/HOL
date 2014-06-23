<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

Notes on HOL 4, ?????? release
==============================

(Released: ??? date)

We are pleased to announce the ?????? release of HOL 4.

Contents
--------

-   [New features](#new-features)
-   [Bugs fixed](#bugs-fixed)
-   [New theories](#new-theories)
-   [New tools](#new-tools)
-   [New examples](#new-examples)
-   [Incompatibilities](#incompatibilities)

New features:
-------------

* Our *TUTORIAL* and *LOGIC* manuals are now available in Italian translations.  Many thanks to Domenico Masini for doing this work.

* The abbreviation tactics (`Q.ABBREV_TAC` and others) now handle abstractions as abbreviations better.  In particular, if one sets up an abstraction as an abbreviation (*e.g.*, ``Q.ABBREV_TAC `f = (λn. 2 * n + 10)` ``), then the simplifier will find and replace instances not just of the abstraction itself (the old behaviour), but also instances of applications of the abstraction to arguments.  For example, given the abbreviation for `f` above, the simplifier would turn a goal such as `2 * (z + 1) + 10 < 100` into `f (z + 1) < 100`.

* The `MAX_SET` function in `pred_setTheory` is now defined (to have value `0`) on the empty set.

* There is an alternative syntax for specifying datatypes.  Instead of the `Hol_datatype` entry-point, one can also use `Datatype`, which takes a slightly different syntax, inspired by Haskell.  This does away with the use of the (somewhat confusing) `of` and `=>` tokens.

    For example, one would define a simple type of binary tree with

           Datatype`tree = Lf num | Node tree tree`

    If the arguments to a constructor are not just simple types (expressible as single tokens), then they need to be enclosed in parentheses.  For example:

           Datatype`mytype = Constr mytype ('a -> bool) | BaseCase`

    The `Hol_datatype` entry-point can continue to be used.  However, the LaTeX output of `EmitTeX` uses the new format, and the various `DATATYPE` constructors used in the `EmitML` module take quotations in the new format, rather than the old.

* The arithmetic decision procedure for natural numbers will now prove slightly more goals by doing case-splits on boolean sub-terms that are not in the Presburger subset.  This means that goals such as

           0 < y ⇒ x < x + (if P then y else y + 1)

    are now provable.


Bugs fixed:
-----------

* `Holmake` was unnecessarily quiet when it compiled certain SML files.

* The “munging” code for turning HOL into LaTeX now does a better job of rendering data type definition theorems.  (This change is independent of the new underlying syntax described earlier.)

* On Windows, the Unicode trace is now off by default.

* Pretty-printers added to the system with `add_user_printer` weren’t having terms-to-be-printed tested against the supplied patterns (except by the gross approximation provided by the built-in term-net structure).  Thanks to Ramana Kumar for the [bug report](https://github.com/mn200/HOL/issues/172).

New theories:
-------------

* A theory of “list ranges” (`listRangeTheory`).  A range is a term written `[ lo ..< hi ]`, meaning the list consisting of the (natural) numbers from `lo` up to, but not including, `hi`.  The theory comes with some basic and obvious theorems, such as

           MEM i [lo ..< hi] ⇔ lo ≤ i ∧ i < hi

    and

           LENGTH [lo ..< hi] = hi - lo

* A new development in `src/floating-point`, which is a reworking of the theories in  `src/float`. Key differences are listed below.

    1. The data representation:

        - The old `ieeeTheory` uses a pair ` ``:num # num`` ` to represent the exponent and fraction widths and a triple ` ``:num # num # num`` ` to represent sign, exponent and fraction values.

        - The new `binary_ieeeTheory` makes use of HOL records and bit-vectors. The floating-point type ` ``:(α, β) float`` ` has values of the form

                  <| Sign : word1; Exponent : β word; Significand : α word |>

            The fraction and exponent widths are now constrained by the type, which facilitates type-checking and avoids having to pass size arguments to operations.

    2. The new development now supports standard bit-vector encoding schemes. The theory `machine_ieeeTheory` defines floating-point operations over 16-bit, 32-bit and 64-bit values. For example, the 16-bit floating point operations are defined by mapping to and from the type ``:(10, 5) float``, which is given the type abbreviation ``:half``. Theories for other sizes can be built using `machine_ieeeLib.mk_fp_encoding`.

    3. There is now syntax support via the structures `binary_ieeeSyntax` and `machine_ieeeSyntax`.

    4. Ground term evaluation is now supported for most operations. This can be enabled by loading `binary_ieeeLib`.

    5. The full development does not build under Moscow&nbsp;ML&nbsp;2.01, as it makes use of the `IEEEReal` and `PackRealBig` basis structures.


New tools:
----------

- New libraries `enumLib` and `fmapalLib` provide representations in `pred_set` and finite map types of enumerated constant sets and maps as minimum-depth binary search trees. A suitable total order on the set elements (map arguments) must be supplied, with a conversion for evaluating it; assistance with this is provided. The primary objective has been an `IN_CONV`, and a similar `FAPPLY_CONV`, operating with a logarithmic number of comparisons, but additional operations such as `UNION_CONV`, `INTER_CONV`, and `FUPDATE_CONV` are included and have reasonable asymptotic running times. A conversion `TC_CONV` implements Warshall’s algorithm for transitive closure of a binary relation (treated as a set-valued finite map).


New examples:
-------------

Incompatibilities:
------------------

- In `relationTheory`, the theorems `TC_CASES1` and `TC_CASES2` have been renamed to `TC_CASES1_E` and `TC_CASES2_E` respectively, where the `_E` suffix indicates that these are elimination rules.  In other words, these theorems are of the form `TC R x y ⇒ ...`.  This has been done so that new equivalences can be introduced under the old names.  For example, `TC_CASES1` now states

           TC R x z ⇔ R x z ∨ ∃y. R x y ∧ TC R y z

    This change makes the naming consistent with similar theorems `RTC_CASES1` and `RTC_CASES2` about the reflexive and transitive closure.

- A theorem stating

           ⊢ ¬(0 < n) ⇔ (n = 0)

    (for `n` a natural number) has been added to the automatic rewrites used by `SRW_TAC` and `srw_ss()`.

- Some new automatic rewrites from `pred_setTheory`:

    * `⊢ DISJOINT (x INSERT s) t ⇔ DISJOINT s t ∧ x ∉ t`  (and the version of this with `DISJOINT s (x INSERT t)` as the l.h.s.)
    * `⊢ ∀f s. INJ f ∅ s`
    * `⊢ ∀f s. INJ f s ∅ ⇔ (s = ∅)`

* * * * *

<div class="footer">
*[HOL4, ?????](http://hol.sourceforge.net)*

[Release notes for the previous version](kananaskis-9.release.html)

</div>
