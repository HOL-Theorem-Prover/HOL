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
-   [New Examples](#new-examples)
-   [Incompatibilities](#incompatibilities)

New features:
-------------

Bugs fixed:
-----------

New theories:
-------------

- `number`, `combinatorics` and `prime`: These theories combine material
   from `examples/algebra/lib`, etc.
   They contain some more advanced results from number theory (in particular properties of prime numbers) and combinatorics.

- `monoid`, `group`, `ring` and `real_algebra`: These theories combine
   material previously held in `examples/algebra`.
   A monoid is an algebraic structure: with a carrier set, a binary operation and an identity element.
   A group is an algebraic structure: a monoid with all its elements invertible.
   A ring takes into account the interplay between its additive group and multiplicative monoid.

New tools:
----------

- `Tactic.TRANS_TAC` (ported from HOL-Light) applies transitivity theorem to goal
  with chosen intermediate term. See its DOC for more details.

- `intLib.INTEGER_TAC` and `intLib.INTEGER_RULE` (ported from HOL-Light): simple
  decision procedures for equations of multivariate polynomials of integers, and
  simple equations about divisibility of integers.

New examples:
-------------

Incompatibilities:
------------------

-   `numLib.prefer_num` has been renamed to `numLib.temp_prefer_num`, which name better describes its semantics.
    The `prefer_num` entry-point is now used to make a change “permanent” (again following the naming convention used by many parsing-related entry-points), which is to say that the overloads made by this function will be exported to child theories.

* * * * *

<div class="footer">
*[HOL4, ?????](http://hol-theorem-prover.org)*

[Release notes for the previous version](trindemossen-1.release.html)

</div>
