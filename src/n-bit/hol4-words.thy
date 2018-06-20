name: hol-words
version: 1.2
description: n-bit words
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-string
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Data.Option"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-words-unint.art"
  interpretation: "../opentheory/hol4.int"
}
