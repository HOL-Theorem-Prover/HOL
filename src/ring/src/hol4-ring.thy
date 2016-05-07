name: hol-ring
version: 1.0
description: HOL ring theories
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
requires: base
requires: hol-base
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-ring-unint.art"
  interpretation: "../../opentheory/hol4.int"
}
