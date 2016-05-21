name: hol-real-unsat
version: 1.0
description: HOL real theories (with unsatisfied assumptions)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-integer
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Number.Real"
show: "Relation"
main {
  article: "hol4-real-unint.art"
  interpretation: "../opentheory/hol4.int"
}
