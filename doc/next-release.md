% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: )

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

*   The special `Type` syntax for making type abbreviations can now map to `temp_type_abbrev` (or `temp_type_abbrev_pp`) by adding the `local` attribute to the name of the abbreviation.

    For example

           Type foo[local] = “:num -> bool # num”

    or

           Type foo[local,pp] = “:num -> bool # num”

    Thanks to Magnus Myreen for the feature suggestion.

*   We have added a special syntactic form `Overload` to replace various flavours of `overload_on` calls.
    The core syntax is exemplified by

           Overload foo = “myterm”

    Attributes can be added after the name.
    Possible attributes are `local` (for overloads that won’t be exported) and `inferior` to cause a call `inferior_overload_on` (which makes the overload the pretty-printer’s last choice).

    Thanks to Magnus Myreen for the feature suggestion.

Bugs fixed:
-----------

New theories:
-------------

New tools:
----------

New examples:
-------------

Incompatibilities:
------------------

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-13.release.html)

</div>
