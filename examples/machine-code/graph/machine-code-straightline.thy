name: machine-code-straightline
version: 1.0
description: Hoare logic triple support for straightline code
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-string
requires: hol-sort
requires: hol-words
requires: hol-integer
requires: machine-code-hoare-logic
requires: machine-code-hoare-triple
requires: arm-model
requires: arm-step
requires: arm-prog
requires: arm-decomp
requires: m0-model
requires: m0-prog
requires: m0-decomp
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Data.Option"
show: "Number.Natural"
show: "Function"
show: "Relation"
main {
  article: "machine-code-straightline-unint.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
