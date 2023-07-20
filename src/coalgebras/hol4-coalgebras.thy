name: hol-coalgebras
version: 1.1
description: HOL coalgebras theories
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-set
requires: hol-finite-maps
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Data.Option"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-coalgebras-unint.art"
  interpretation: "../opentheory/hol4.int"
}
