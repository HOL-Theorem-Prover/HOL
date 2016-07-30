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

New theories:
-------------

New tools:
----------

New examples:
---------

Incompatibilities:
------------------

*   The type of the “system printer” used by user-defined pretty-printers to pass control back to the default printer has changed.
    This function now gets passed an additional parameter corresponding to whether or not the default printer should treat the term to be printed as if it were in a binding position or not.
    (This `binderp` parameter is in addition to the parameters indicating the “depth” of the printing, and the precedence gravities.)
    See the *Reference* manual for more details.

*   The `PAT_ASSUM` tactics (`Tactical.PAT_ASSUM`, `Q.PAT_ASSUM` and `bossLib.qpat_assum`) have all been renamed to pick up an internal `_X_` (or `_x_`).
    Thus, the first becomes `PAT_X_ASSUM`, and the last becomes `qpat_x_assum`).
    This makes the names consistent with other theorem-tactics (*e.g.*, `first_x_assum`): the `X` (or `x`) indicates that the matching assumption is removed from the assumption list.
    Using the old names, we also now have versions that *don’t* remove the theorems from the assumption list.

    The behaviour of the quoting versions of the tactics is also slightly different: they will always respect names that occur both in the pattern and in the goal.
    Again, this is for consistency with similar functions such as `qspec_then`.
    This means, for example, that ``qpat_assum `a < b` `` will fail if the actual theorem being matched is something `c < f a`.
    (This is because the pattern and the goal share the name `a`, so that the pattern is implicitly requiring the first argument to `<` to be exactly `a`, which is not the case.)
    This example would have previously worked if there was exactly one assumption with `<`.
    The fix in cases like this is to use more underscores in one’s patterns.

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-11.release.html)

</div>
