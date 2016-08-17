name: arm-decomp
version: 1.0
description: ARM decompilation support
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: arm-model
requires: arm-prog
show: "HOL4"
show: "Data.Bool"
show: "Data.Pair"
main {
  article: "arm_decomp.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
