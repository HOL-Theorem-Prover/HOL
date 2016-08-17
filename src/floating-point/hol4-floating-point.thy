name: hol-floating-point
version: 1.2
description: HOL floating point theories
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-integer
requires: hol-real
show: "HOL4"
show: "Data.Bool"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-floating-point-unint.art"
  interpretation: "../opentheory/hol4.int"
}
