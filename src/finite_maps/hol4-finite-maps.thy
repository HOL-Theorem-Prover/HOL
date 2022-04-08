name: hol-finite-maps
version: 1.0
description: HOL finite maps
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-sort
requires: hol-words
requires: hol-bag
show: "HOL4"
show: "Data.Bool"
show: "Data.Option"
show: "Data.Unit"
show: "Data.Sum"
show: "Data.Pair"
show: "Data.List"
show: "Function"
show: "Relation"
show: "Number.Natural"
main {
  article: "hol4-finite-maps-unint.art"
  interpretation: "../opentheory/hol4.int"
}
