name: m0-decomp
version: 1.0
description: M0 decompilation support
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: m0-prog
show: "HOL4"
show: "Data.Bool"
show: "Data.Pair"
main {
  article: "m0_decomp.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
