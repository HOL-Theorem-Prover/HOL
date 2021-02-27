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

Bugs fixed:
-----------

New theories:
-------------

New tools:
----------

New examples:
-------------
<h3>Dependability Analysis:</h3>
Dependability is an umberalla term encompassing Reliability, Availability and Maintainabiity.
Two widely used dependability modeling techniques have been formalized namely, Reliability Block Diagrams (RBD) and Faul Tree (FT).
Both these techniques graphically analyze the causes and factors contributing the functioning and failure of the system under study.
Moreover, these dependability techniques have been highly recommended by several safety standards, such as IEC 61508, ISO 26262 and EN50128,
for developing safe hardware and software systems.

The new recursive datatypes are defined to model RBD and FT providing compositional features in order to analyze complex systems with arbitrary
number of components.


```
val _ = Hol_datatype` rbd = series of rbd list
							| parallel of rbd list
							| atomic of 'a  event `;
```


```
val _ = Hol_datatype` gate = AND of gate list
                            | OR of gate list
                            | NOT of gate
                            | atomic of 'a  event `;
```

Some case studies are also formalized and placed with dependability theories, for illustration purposes, including smart grids, WSN data transport protocols,
satellite solar arrays, virtual data centers, oil and gas pipeline systems and an air traffic management system.


Incompatibilities:
------------------

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-14.release.html)

</div>
