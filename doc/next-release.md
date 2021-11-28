% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: xxxxxx)

We are pleased to announce the ?????? release of HOL4.

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

- A `HOL_CONFIG` environment variable is considered to allow for a custom `hol-config` configuration at a non-standard location or potentially ignoring any present hol-config.
  If the variable is set, any other hol-config file will be ignored. If the value of `HOL_CONFIG` is a readable file, it will be used.


Bugs fixed:
-----------

New theories:
-------------

New tools:
----------

New examples:
-------------

-  **Dependability Analysis**:
   Dependability is an umbrella term encompassing Reliability, Availability and Maintainabiity.
   Two widely used dependability modeling techniques have been formalized namely, Reliability Block Diagrams (RBD) and Fault Trees (FT).
   Both these techniques graphically analyze the causes and factors contributing the functioning and failure of the system under study.
   Moreover, these dependability techniques have been highly recommended by several safety standards, such as IEC 61508, ISO 26262 and EN50128,
for developing safe hardware and software systems.

   The new recursive datatypes are defined to model RBD and FT providing compositional features in order to analyze complex systems with arbitrary
number of components.

           Datatype: rbd = series (rbd list)
                         | parallel (rbd list)
                         | atomic (α event)
           End

           Datatype: gate = AND (gate list)
                          | OR (gate list)
                          | NOT gate
                          | atomic (α event)
           End

   Some case studies are also formalized and placed with dependability theories, for illustration purposes, including smart grids, WSN data transport protocols, satellite solar arrays, virtual data centers, oil and gas pipeline systems and an air traffic management system.

-   __large_numberTheory__ (in `examples/probability`): various versions of The Law of Large Numbers (LLN) of Probability Theory.

    Some LLN theorems (`WLLN_uncorrelated` and `SLLN_uncorrelated`) previously in `probabilityTheory`
    are now moved to `large_numberTheory` with unified statements.

Incompatibilities:
------------------

*   The small `productTheory` (Products of natural numbers and real numbers, ported from HOL-Light)
    has been merged into `iterateTheory` (on which `extrealTheory` now depends).

*   Changes in the `formal-languages/context-free` example:

    -   The location type (defined in `locationTheory`) has been simplified
    -   The PEG machinery now has a simple error-reporting facility that attempts to report the end of the longest prefix of the input that might still be in the PEG’s language.
        This means that instead of returning either `SOME result` or `NONE`, PEG’s now return a custom `Success`/`Failure` data type with values attached to both constructors.

*   The `MEMBER_NOT_EMPTY` theorem in `bagTheory` has been renamed to `BAG_MEMBER_NOT_EMPTY` to avoid a name-clash with a theorem of the same name in `pred_setTheory`.

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-14.release.html)

</div>
