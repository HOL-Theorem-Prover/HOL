name: hol-probability
version: 1.0
description: HOL probability theory
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-real
requires: hol-analysis
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-probability-unint.art"
  interpretation: "../opentheory/hol4.int"
}
