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

- Theorems can now have names that are the same as SML constructor names (*e.g.*, `Empty`).  ([Github issue](http://github.com/HOL-Theorem-Prover/HOL/issues/225))

- `Holmake` will now follow `INCLUDES` specifications from `Holmakefiles` when given “phony” targets to build on the command-line.  (A typical phony target is `all`.) As in the past, it will still act only locally if given just a clean target (`clean`, `cleanDeps` or `cleanAll`).  To clean recursively, you must also pass the `-r` flag to `Holmake`.  ([Github issue](http://github.com/HOL-Theorem-Prover/HOL/issues/145))

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

- The functions `Q.MATCH_RENAME_TAC` and `Q.MATCH_ASSUM_RENAME_TAC` have been adjusted to lose their second arguments (the list of variable names that are not to be bound).  For example, applying ``Q.MATCH_RENAME_TAC `(f x = Pair c1 c2) ⇒ X` ["X"]`` to the goal

           ?- (f x = Pair C'' C0') ⇒ (f C'' = f C0')

    used to result in the renamed goal

           ?- (f x = Pair c1 c2) ⇒ (f c1 = f c2)

    where the `X` in the pattern was ignored.  The interface now achieves the same end by simply allowing the user to write underscores in the pattern.  Thus, the tactic would become ``Q.MATCH_RENAME_TAC `(f x = Pair c1 c2) ⇒ _` ``.  Multiple underscores can be used to ignore multiple sub-terms.

    Of course, the `qmatch_rename_tac` and `qmatch_assum_rename_tac` names for these tactics in `lcsymtacs` have changed types as well.  The new `Q.MATCH_GOALSUB_RENAME_TAC` and `Q.MATCH_ASMSUB_RENAME_TAC` (and their lower-case versions) have similar types, without explicit lists of variable names to ignore.

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol.sourceforge.net)*

[Release notes for the previous version](kananaskis-10.release.html)

</div>
