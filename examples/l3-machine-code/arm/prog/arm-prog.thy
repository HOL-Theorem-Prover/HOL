name: arm-prog
version: 1.1
description: ARM evaluator
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: machine-code-hoare-logic
requires: machine-code-hoare-logic-state
requires: arm-model
requires: arm-step
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
main {
  article: "arm_prog.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
