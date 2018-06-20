name: arm-step
version: 1.1
description: ARM step evaluator
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-string
requires: hol-integer
requires: hol-monad
requires: hol-floating-point
requires: arm-model
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
main {
  article: "arm_step.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
