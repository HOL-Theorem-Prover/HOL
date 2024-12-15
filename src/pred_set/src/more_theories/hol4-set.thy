name: hol-set
version: 1.1
description: HOL set (and topology) theories
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-quotient
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
  article: "hol4-set-unint.art"
  interpretation: "../../../opentheory/hol4.int"
}
