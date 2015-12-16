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

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-11.release.html)

</div>
