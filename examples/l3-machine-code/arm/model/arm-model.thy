name: arm-model
version: 1.1
description: ARM model
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-string
requires: hol-integer
requires: hol-monad
requires: hol-floating-point
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "arm.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
