name: m0-prog
version: 1.0
description: M0 evaluator
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: machine-code-hoare-logic
requires: machine-code-hoare-logic-state
requires: m0-model
requires: m0-step
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
main {
  article: "m0_prog.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
