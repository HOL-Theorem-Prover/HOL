name: HOL4 Base
version: 1.0
description: HOL4 Basic theories
author: HOL4 people
license: BSD
main {
  import: bool
  import: marker
  import: combin
  import: relation
  import: one
  import: pair
  import: poset
  import: option
  import: sum
  import: num
  import: prim-rec
  import: arithmetic
  import: numeral
  import: basic-size
  import: while
  import: numpair
  import: pred-set
  import: ind-type
  import: operator
  import: list
  import: rich-list
  import: indexed-lists
}
bool {
  article: "bool_defs.ot.art"
  interpret: const "HOL4.bool_defs.LET" as "HOL4.bool.LET"
  interpret: const "HOL4.bool_defs.literal_case" as "HOL4.bool.literal_case"
  interpret: const "HOL4.bool_defs.IN" as "HOL4.bool.IN"
  interpret: const "HOL4.bool_defs.TYPE_DEFINITION" as "HOL4.bool.TYPE_DEFINITION"
}
marker {
  article: "../marker/marker.ot.art"
}
combin {
  import: bool
  import: marker
  article: "../combin/combin.ot.art"
}
relation {
  import: bool
  import: combin
  article: "../relation/relation.ot.art"
}
one {
  article: "../one/one.ot.art"
}
pair {
  import: bool
  import: relation
  article: "../pair/src/pair.ot.art"
}
poset {
  import: pair
  article: "../pair/src/poset.ot.art"
}
sum {
  import: combin
  article: "../sum/sum.ot.art"
}
option {
  article: "../option/option.ot.art"
}
num {
  article: "../num/theories/num.ot.art"
}
prim-rec {
  import: relation
  import: num
  article: "../num/theories/prim_rec.ot.art"
}
arithmetic {
  import: marker
  import: pair
  import: prim-rec
  import: relation
  article: "../num/theories/arithmetic.ot.art"
}
numeral {
  import: arithmetic
  import: marker
  import: relation
  article: "../num/theories/numeral.ot.art"
}
basic-size {
  import: pair
  article: "../num/theories/basicSize.ot.art"
}
while {
  import: arithmetic
  article: "../num/theories/while.ot.art"
}
numpair {
  import: pair
  import: numeral
  import: relation
  import: marker
  import: prim-rec
  article: "../num/extra_theories/numpair.ot.art"
}
pred-set {
  import: bool
  import: pair
  import: relation
  import: option
  import: arithmetic
  import: while
  import: prim-rec
  import: numeral
  import: numpair
  import: marker
  article: "../pred_set/src/pred_set.ot.art"
}
ind-type {
  import: bool
  import: arithmetic
  article: "../datatype/ind_type.ot.art"
}
operator {
  article: "../list/src/operator.ot.art"
}
list {
  import: bool
  import: arithmetic
  import: numeral
  import: option
  import: pair
  import: relation
  import: while
  import: marker
  import: pred-set
  import: operator
  article: "../list/src/list.ot.art"
}
rich-list {
  import: list
  import: arithmetic
  import: combin
  import: operator
  article: "../list/src/rich_list.ot.art"
}
indexed-lists {
  import: list
  import: relation
  article: "../list/src/indexedLists.ot.art"
}
