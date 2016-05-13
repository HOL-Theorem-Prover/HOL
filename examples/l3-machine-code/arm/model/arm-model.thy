name: arm-model
version: 1.0
description: ARM model
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-string
requires: hol-integer
requires: hol-monad
requires: hol-floating-point
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "arm.ot.art"
  interpretation: "../../../../src/opentheory/hol4.int"
}
