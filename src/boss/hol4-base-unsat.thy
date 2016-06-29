name: hol-base-unsat
version: 1.0
description: HOL basic theories (with unsatisfied assumptions)
author: HOL4 people
license: BSD
requires: base
main {
  article: "hol4-base-unint.art"
  interpretation: "../opentheory/hol4.int"
}
