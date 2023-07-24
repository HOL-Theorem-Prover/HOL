name: hol-probability
version: 1.2
description: HOL probability theory
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-set
requires: hol-real
requires: hol-extreal
requires: hol-words
requires: hol-analysis
show: "HOL4"
show: "Data.Bool"
show: "Data.Sum"
show: "Data.Pair"
show: "Data.List"
show: "Function"
show: "Relation"
show: "Number.Natural"
show: "Number.Real"
main {
  article: "hol4-probability-unint.art"
  interpretation: "../opentheory/hol4.int"
}
