name: m0-step
version: 1.0
description: M0 step evaluator
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-string
requires: hol-integer
requires: hol-monad
requires: m0-model
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
main {
  article: "m0_step.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
