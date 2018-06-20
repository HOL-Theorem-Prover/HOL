name: machine-code-hoare-logic
version: 1.1
description: A Hoare logic for machine code
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "machine-code-hoare-logic-unint.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
