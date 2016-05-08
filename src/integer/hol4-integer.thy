name: hol-integer
version: 1.0
description: HOL integer theories
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-string
requires: hol-ring
requires: hol-quotient
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-integer-unint.art"
  interpretation: "../opentheory/hol4.int"
}
