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

Bugs fixed:
-----------

New theories:
-------------

New tools:
----------

- New libraries `enumLib` and `fmapalLib` provide representations in `pred_set` and finite map types of enumerated constant sets and maps as minimum-depth binary search trees. A suitable total order on the set elements (map arguments) must be supplied, with a conversion for evalulating it; assistance with this is provided. The primary objective has been an `IN_CONV`, and a similar `FAPPLY_CONV`, operating with a logarithmic number of comparisons, but additional operations such as `UNION_CONV`, `INTER_CONV`, and `FUPDATE_CONV` are included and have reasonable asymptotic running times. A conversion `TC_CONV` implements Warshall’s algorithm for transitive closure of a binary relation (treated as a set-valued finite map).


New examples:
-------------


Incompatibilities:
------------------

* * * * *

*[HOL4, ?????](http://hol.sourceforge.net)*
