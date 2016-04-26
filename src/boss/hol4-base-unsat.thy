name: hol-base-unsat
version: 1.0
description: HOL basic theories (with unsatisfied assumptions)
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
show: "HOL4"
show: "Data.Bool"
show: "Data.Option"
show: "Data.Unit"
show: "Data.Sum"
show: "Data.Pair"
show: "Data.List"
show: "Function"
show: "Relation"
show: "Number.Natural"
requires: base
main {
  article: "hol4-base-unsat.art"
  interpretation: "../opentheory/hol4.int"
}
