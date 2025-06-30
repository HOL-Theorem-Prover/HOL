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

-   The simplifier now supports `NoAsms` and `IgnAsm` special forms that allow all assumptions (or those matching the provided pattern, in the case of `IgnAsm`) to be excluded.
    See the DESCRIPTION and REFERENCE manuals for details.
    ([GitHub issue](https://github.com/HOL-Theorem-Prover/HOL/issues/1220))

- The automatic termination-finding technology behind `Definition`
    (and lower-level APIs) is now rather stronger, especially when
    dealing with higher order recursions using list operators.  This
    should reduce the number of times you need to introduce explicit
    `Termination`-argument blocks to accompany your
    definitions. Termination condition extraction and termination
    relation guessing now have traces ("Definition.TC extraction" and
    "Definition.termination candidates") that can be examined for illumination.
    See `src/tfl/examples/termination_proverScript.sml` for examples.


Bugs fixed:
-----------

- EVERY_CASE_TAC would loop if the "split-upon" subterm was already an assumption, but no longer.


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

- Dijkstra's algorithm for computing shortest paths: `examples/algorithms/dijkstraScript.sml`

Incompatibilities:
------------------

-   `numLib.prefer_num` has been renamed to `numLib.temp_prefer_num`, which name better describes its semantics.
    The `prefer_num` entry-point is now used to make a change “permanent” (again following the naming convention used by many parsing-related entry-points), which is to say that the overloads made by this function will be exported to child theories.

-   Editor mode implementations have moved in the HOL sources to `tools/editor-modes/{editor-name}`.
    This may affect editor initialisations/configurations, particularly if they hard-code a reference to a particular path.
    For example, in the recommended setup for `emacs`, users will need to change

           (load "<path>/HOL/tools/hol-mode")
           (load "<path>/HOL/tools/hol-unicode")

    to

           (load "<path>/HOL/tools/editor-modes/emacs/hol-mode")
           (load "<path>/HOL/tools/editor-modes/emacs/hol-unicode")

-   The types of `DB.find` and `DB.match` have changed so that instead of returning

           (string * string) * (thm * class)

    they now return

           (string * string) * (thm * class * thm_src_location)

    Using the `#1 o #2` selector should be future-proof here.

-   `util_probTheory` has been merged into `sigma_algebraTheory`.

-   In `set_relationTheory`, the constant `tc` has been renamed to `transitive_closure`.

-   Various `adjoin_to…` entry-points in `Theory` have been removed.
    The biggest incompatibility this causes is the removal of the `<thy>_grammars` binding from all `<thy>Theory` structures.
    To access the grammars specific to a particular theory (`foo`, say), one must now write

           valOf $ Parse.grammarDB {thyname="foo"}

    where the call may fail if the theory is not present in the hierarchy.

* * * * *

<div class="footer">
*[HOL4, ?????](http://hol-theorem-prover.org)*

[Release notes for the previous version](trindemossen-1.release.html)

</div>
