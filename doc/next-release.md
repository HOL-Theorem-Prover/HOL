% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: ???)

We are pleased to announce the ?????? release of HOL 4.

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

*   We have implemented new syntaxes for `store_thm` and `save_thm`, which better satisfy the recommendation that `name1` and `name2` below should be the same:

           val name1 = store_thm("name2", tm, tac);

    Now we can remove the “code smell” by writing either

           Theorem name tm-quotation tac

    which will typically look like

           Theorem name
             ‘∀x. P x ⇒ Q x’
             (rpt strip_tac >> ...);

    or by writing with the general pattern

           Theorem name: term-syntax
           Proof tac
           QED

    which might look like

           Theorem name:
             ∀x. P x ⇒ Q x
           Proof
             rpt strip_tac >> ...
           QED

    This latter form must have the `Proof` and `QED` keywords in column 0 in order for the lexing machinery to detect the end of the term and tactic respectively.
    Both forms map to applications of `Q.store_thm` underneath, with an ML binding also made to the appropriate name.
    Both forms allow for theorem attributes to be associated with the name, so that one can write

           Theorem ADD0[simp]: ∀x. x + 0 = x
           Proof tactic
           QED

    Finally, to replace

           val nm = save_thm(“nm”, thm_expr);

    one can now write

           Theorem nm = thm_expr

    These names can also be given attributes in the same way.


Bugs fixed:
-----------

New theories:
-------------

*   `real_topologyTheory`: a rather complete theory of Elementary
    Topology in Euclidean Space, ported by Muhammad Qasim and Osman
    Hasan from HOL-light (up to 2015). The part of General Topology
    (independent of `realTheory`) is now available at
    `topologyTheory`; the old `topologyTheory` is renamed to
    `metricTheory`.

    There is a minor backwards-incompatibility: old proof scripts using
    the metric-related results in previous `topologyTheory` should now
    open `metricTheory` instead. (Thanks to Chun Tian for this work.)

*   Holmakefiles can now refer to the new variable `DEFAULT_TARGETS` in order to generate a list of the targets in the current directory that Holmake would attempt to build by default.
    This provides an easier way to adjust makefiles than that suggested in the [release notes for Kananaskis-10](http://hol-theorem-prover.org/kananaskis-10.release.html).

New tools:
----------

New examples:
---------

Incompatibilities:
------------------

*   The `Holmake` tool now behaves with the `--qof` behaviour enabled by default.
    This means that script files which have a tactic failure occur will cause the building of the corresponding theory to fail, rather than having the build continue with the theorem “cheated”.
    We think this will be less confusing for new users.
    Experts who *do* want to have script files continue past such errors can use the `--noqof` option to enable the old behaviour.

*   When running with Poly/ML, we now require at least version 5.7.0.

*   The `type_abbrev` function now affects only the type parser.
    The pretty-printer will not use the new abbreviation when printing types.
    If the old behaviour of printing the abbreviations as well as parsing them is desired, the new entrypoint `type_abbrev_pp` should be used.

*   The `Globals.priming` reference variable has been removed.
    All priming done by the kernel is now by appending extra prime (apostrophe) characters to the names of variables.
    This also means that this is the only form of variation introduced by the `variant` function.
    However, there is also a new `numvariant` function, which makes the varying function behave as if the old `Globals.priming` was set to `SOME ""` (introduces and increments a numeric suffix).

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-12.release.html)

</div>
