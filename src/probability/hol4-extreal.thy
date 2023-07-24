name: hol-extreal
version: 1.1
description: HOL4 extended reals
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-set
requires: hol-real
requires: hol-analysis
show: "HOL4"
show: "Data.Bool"
show: "Data.Pair"
show: "Data.List"
show: "Function"
show: "Relation"
show: "Number.Natural"
show: "Number.Real"
main {
  article: "hol4-extreal-unint.art"
  interpretation: "../opentheory/hol4.int"
}
