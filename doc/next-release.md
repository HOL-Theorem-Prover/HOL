<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->
Notes on HOL 4, ?????? release
====================================

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

* Our TUTORIAL and LOGIC manuals are now available in Italian translations.  Many thanks to Domenico Masini for doing this work.

* The abbreviation tactics (`Q.ABBREV_TAC` and others) now handle abstractions as abbreviations better.  In particular, if one sets up an abstraction as an abbreviation (*e.g.*, ``Q.ABBREV_TAC `f = (λn. 2 * n + 10)` ``), then the simplifier will find and replace instances not just of the abstraction itself (the old behaviour), but also instances of applications of the abstraction to arguments.  For example, given the abbreviation for `f` above, the simplifier would turn a goal such as `2 * (z + 1) + 10 < 100` into `f (z + 1) < 100`.

* The `MAX_SET` function in `pred_setTheory` is now defined (to have value `0`) on the empty set.

* There is an alternative syntax for specifying datatypes.  Instead of the `Hol_datatype` entry-point, one can also use `Datatype`, which takes a slightly different syntax, inspired by Haskell.  This does away with the use of the (somewhat confusing) `of` and `=>` tokens.

  For example, one would define a simple type of binary tree with

           Datatype`tree = Lf num | Node tree tree`

  If the arguments to a constructor are not just simple types (expressible as single tokens), then they need to be enclosed in parentheses.  For example:

           Datatype`mytype = Constr mytype ('a -> bool) | BaseCase`

  The `Hol_datatype` entry-point can continue to be used.  However, the LaTeX output of `EmitTeX` uses the new format, and the various `DATATYPE` constructors used in the `EmitML` module take quotations in the new format, rather than the old.


Bugs fixed:
-----------

* `Holmake` was unnecessarily quiet when it compiled certain SML files.

* The “munging” code for turning HOL into LaTeX now does a better job of rendering data type definition theorems.

* On Windows, the Unicode trace is now off by default.

New theories:
-------------

* A theory of “list ranges” (`listRangeTheory`).  A range is a term written `[ lo ..< hi ]`, meaning the list consisting of the (natural) numbers from `lo` up to, but not including, `hi`.  The theory comes with some basic and obvious theorems, such as

           MEM i [lo ..< hi] ⇔ lo ≤ i ∧ i < hi

   and

           LENGTH [lo ..< hi] = hi - lo

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

* * * * *

*[HOL4, ?????](http://hol.sourceforge.net)*
