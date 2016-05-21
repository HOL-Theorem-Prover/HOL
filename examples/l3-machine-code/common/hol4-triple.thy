name: hol-triple
version: 1.0
description: triple
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-machine-code-hoare-triple
show: "Data.Bool"
main {
  article: "triple-unint.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
