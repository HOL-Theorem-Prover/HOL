name: hol-machine-code-hoare-triple
version: 1.0
description: Machine code Hoare logic from HOL4 examples
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
requires: base
requires: hol-base
requires: hol-words
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-machine-code-hoare-triple-unint.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
