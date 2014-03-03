<!-- search and replace ?????? strings corresponding to release name -->
Notes on HOL 4, ?????? release
====================================

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

Bugs fixed:
-----------

* `Holmake` was unnecessarily quiet when it compiled certain SML files.

* The “munging” code for turning HOL into LaTeX now does a better job of rendering data type definition theorems.

* On Windows, the Unicode trace is now off by default.

New theories:
-------------

New tools:
----------

- New libraries `enumLib` and `fmapalLib` provide representations in `pred_set` and finite map types of enumerated constant sets and maps as minimum-depth binary search trees. A suitable total order on the set elements (map arguments) must be supplied, with a conversion for evaluating it; assistance with this is provided. The primary objective has been an `IN_CONV`, and a similar `FAPPLY_CONV`, operating with a logarithmic number of comparisons, but additional operations such as `UNION_CONV`, `INTER_CONV`, and `FUPDATE_CONV` are included and have reasonable asymptotic running times. A conversion `TC_CONV` implements Warshall’s algorithm for transitive closure of a binary relation (treated as a set-valued finite map).


New examples:
-------------

Incompatibilities:
------------------

* * * * *

*[HOL4, ?????](http://hol.sourceforge.net)*
