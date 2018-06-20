name: machine-code-hoare-logic-state
version: 1.1
description: Machine code Hoare logic state
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: machine-code-hoare-logic
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Data.Option"
show: "Number.Natural"
show: "Function"
show: "Relation"
main {
  article: "machine-code-hoare-logic-state-unint.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
