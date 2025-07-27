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
-   [New examples](#new-examples)
-   [Incompatibilities](#incompatibilities)

New features:
-------------

-   The simplifier now supports `NoAsms` and `IgnAsm` special forms that allow all assumptions (or those matching the provided pattern, in the case of `IgnAsm`) to be excluded.
    See the DESCRIPTION and REFERENCE manuals for details.
    ([GitHub issue](https://github.com/HOL-Theorem-Prover/HOL/issues/1220))

-   The automatic termination-finding technology behind `Definition`
    (and lower-level APIs) is now rather stronger, especially when
    dealing with higher order recursions using list operators.  This
    should reduce the number of times you need to introduce explicit
    `Termination`-argument blocks to accompany your
    definitions. Termination condition extraction and termination
    relation guessing now have traces ("Definition.TC extraction" and
    "Definition.termination candidates") that can be examined for illumination.
    See `src/tfl/examples/termination_proverScript.sml` for examples.

-   All of HOL’s internal files are now stored in/under one sub-directory of the source directory where user `*Script.sml` files are found.
    Previously, HOL used `.HOLMK`, `.holobjs`, and `.hollogs`.
    Now everything is stored in/under the sub-directory `.hol`.

    To get rid of old directories, which are now just going to be useless clutter, shell command-lines such as

           find . -path '*/.hollogs/*' -delete
           find . -name '.hollogs' -delete

    might be used from the root of your HOL development.
    Alternatively, use `Holmake -r cleanAll` with your old HOL version, and then switch.

-   Under Poly/ML, the `hol` and `hol.bare` executables can be passed the `–-noconfig` command-line flag to stop them consulting user config files in the user’s home directory (these have names like `hol-config.sml`).
    Under both Moscow ML and Poly/ML, configuration files are also ignored if there is a  `HOL_NOCONFIG` environment variable set.

-   `oneline` from `bossLib` now supports one-line-ification of mutually recrusive functions.
    Each function becomes an equation of its own in the theorem returned by `oneline`.

Bugs fixed:
-----------

- `EVERY_CASE_TAC` would loop if the "split-upon" subterm was already an assumption, but no longer.


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

- `last_assume_tac` has been added. It is the same as `assume_tac` except it adds
  the new assumption to the top of the list of assumptions instead of the bottom.

New examples:
-------------

- Dijkstra's algorithm for computing shortest paths: `examples/algorithms/dijkstraScript.sml`

Incompatibilities:
------------------

-   `numLib.prefer_num` has been renamed to `numLib.temp_prefer_num`, which name better describes its semantics.
    The `prefer_num` entry-point is now used to make a change “permanent” (again following the naming convention used by many parsing-related entry-points), which is to say that the overloads made by this function will be exported to child theories.

-   The cv translator's entry points with `_pre` now take a new string argument, e.g., what used to be `cv_trans_pre foo_def` is now `cv_trans_pre "foo_pre" foo_def`.
    Mutually recursive functions require a name for each functions. In the string argument, multiple names are given either with
    spaces separating them, e.g., `"foo_pre foo_list_pre"`, or commas separating them, e.g., `"foo_pre,foo_list_pre"` or `"foo_pre, foo_list_pre"`.
    The old behaviour (inventing names) is supported by passing the empty string `""` as the name, i.e., `cv_trans_pre "" foo_def`.

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

-   `ASSUME_NAMED_TAC` now puts the new named assumption at the top of the assumption list, but below the other named assumptions.
    Previously, named assumptions were added to the bottom of the assumption list (where they might get in the way).

* * * * *

<div class="footer">
*[HOL4, ?????](http://hol-theorem-prover.org)*

[Release notes for the previous version](trindemossen-1.release.html)

</div>
