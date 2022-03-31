name: hol-finite-map
version: 1.0
description: HOL finite maps
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-sort
requires: hol-words
requires: hol-bag
requires: hol-res-quan
requires: hol-string
requires: hol-set
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-finite-map-unint.art"
  interpretation: "../opentheory/hol4.int"
}
