name: machine-code-hoare-triple
version: 1.0
description: Total correctness machine-code Hoare triple
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: machine-code-hoare-logic
show: "Data.Bool"
main {
  article: "triple.ot.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
