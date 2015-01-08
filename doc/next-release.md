% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: ??????)

We are pleased to announce the ?????? release of HOL 4.

Contents
--------

-   [New features](#new-features)
-   [Bugs fixed](#bugs-fixed)
-   [New theories](#new-theories)
-   [New tools](#new-tools)
-   [Examples](#examples)
-   [Incompatibilities](#incompatibilities)

New features:
-------------

Bugs fixed:
-----------

- An embarrassing infinite loop bug in the integration of the integer decision procedures (the Omega test, Cooper’s algorithm) into the simplifier was fixed.

New theories:
-------------

New tools:
----------

New examples:
---------

- A theory of balanced binary trees (`examples/balanced_bst`), based on Haskell code by Leijen and Palamarchuk, and mechanised by Scott Owens.  The type supports operations such as `insert`, `union`, `delete`, filters and folds.  Operations are parameterised by comparison operators for comparing keys.  Balanced trees can themselves be compared.

Incompatibilities:
------------------

- The function `optionSyntax.dest_none` will now unwrap the type of its result, *e.g.*, returning `:α` rather than `:α option` when applied to `NONE : α option`.  This brings it into line with the behaviour of `listSyntax.dest_nil`.  See [this github issue](https://github.com/HOL-Theorem-Prover/HOL/issues/215).

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol.sourceforge.net)*

[Release notes for the previous version](kananaskis-10.release.html)

</div>
