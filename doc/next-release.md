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

- We have ported HOL Light’s `PAT_CONV` and `PATH_CONV` “conversionals”, providing nice machinery for applying conversions to specific sub-terms.

- The tactic `PAT_ABBREV_TAC` (also available in the `Q` module) can now use patterns that are more polymorphic than the sub-term in the goal that is ultimately matched. ([Github issue](http://github.com/HOL-Theorem-Prover/HOL/issues/252))

Bugs fixed:
-----------

- An embarrassing infinite loop bug in the integration of the integer decision procedures (the Omega test, Cooper’s algorithm) into the simplifier was fixed.

- Theorems can now have names that are the same as SML constructor names (*e.g.*, `Empty`).  ([Github issue](http://github.com/HOL-Theorem-Prover/HOL/issues/225))

- `Holmake` will now follow `INCLUDES` specifications from `Holmakefiles` when given “phony” targets to build on the command-line.  (A typical phony target is `all`.) As in the past, it will still act only locally if given just a clean target (`clean`, `cleanDeps` or `cleanAll`).  To clean recursively, you must also pass the `-r` flag to `Holmake`.  ([Github issue](http://github.com/HOL-Theorem-Prover/HOL/issues/145))

-   We fixed three problems with `Datatype`. Thanks to Ramana Kumar for the reports.
    [First](http://github.com/HOL-Theorem-Prover/HOL/issues/257), `Datatype` will no longer create a recursive type if the recursive instance  is qualified with a theory name other than the current one.
    In other words,

            Datatype`num = C1 num$num | C2`

    won’t create a recursive type (assuming this is not called in theory `num`).
    (`Hol_datatype` had the same problem.)

    [Second](http://github.com/HOL-Theorem-Prover/HOL/issues/257), `Datatype` will handle antiquotations in its input properly (`Hol_datatype` already did).

    [Third](http://github.com/HOL-Theorem-Prover/HOL/issues/260), `Datatype` (and `Hol_datatype`) allows the definition of identical record types in different theories.

-   Attempts to define constants or types with invalid names are now caught much earlier.
    An invalid name is one that contains “non-graphical” characters (as *per* SML’s `Char.isGraph`) or parentheses.
    This means that Unicode cannot be used in the kernel’s name for a constant, but certainly doesn’t prevent Unicode being used in overloaded notation.
    Functions such as `overload_on`, `add_rule` and `set_mapped_fixity` can still be used to create pretty notation with as many Unicode characters included as desired.

-   Loading theories under Poly/ML would fail unnecessarily if the current directory was unwritable.
    Working in such directories will likely cause problems when and if an `export_theory` call is made, so there is a warning emitted in this situation, but the `load` now succeeds.
    Thanks to Narges Khakpour for the bug report.

New theories:
-------------

New tools:
----------

New examples:
---------

- A theory of balanced binary trees (`examples/balanced_bst`), based on Haskell code by Leijen and Palamarchuk, and mechanised by Scott Owens.  The type supports operations such as `insert`, `union`, `delete`, filters and folds.  Operations are parameterised by comparison operators for comparing keys.  Balanced trees can themselves be compared.

-  A formalisation of pattern matches (`examples/pattern_matches`).
   Pattern matching is not directly supported by higher-order logic.
   HOL4’s parser therefore compiles case-expressions (`case x of ...`) to decision trees based on case constants.
   For non-trivial case expressions, there is a big discrepancy between the user’s view and this internal representation.
   The `pattern_matches` example defines a new general-purpose representation for case expressions that mirrors the input syntax in the internal representation closely.
   Because of this close connection, the new representation is more intuitive and often much more compact.
   Complicated parsers and pretty-printers are no longer required.
   Proofs can more closely follow the user’s intentions, and code generators (like CakeML) can produce better code.
   Moreover, the new representation is strictly more general than the currently used representation.
   The new representation allows for guards, patterns with multiple occurrences of the same bound variable, unbound variables, arithmetic expressions in patterns, and more.
   The example provides the definitions as well as tools to work with the new case-expressions.
   These tools include support for evaluating and simplifying them, a highly configurable pattern compilation algorithm inside the logic, and optimisations like detecting redundant rows and eliminating them.


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
