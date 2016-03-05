name: HOL4 Base
version: 1.0
description: HOL4 Basic theories
author: HOL4 people
license: BSD
main {
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
  import: list
  import: rich-list
  import: indexed-lists
}
marker {
  article: "../marker/marker.ot.art"
}
combin {
  import: marker
  article: "../combin/combin.ot.art"
}
relation {
  import: combin
  article: "../relation/relation.ot.art"
}
one {
  article: "../one/one.ot.art"
}
pair {
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
list {
  import: arithmetic
  import: numeral
  import: option
  import: pair
  import: relation
  import: while
  import: marker
  article: "../list/src/list.ot.art"
}
rich-list {
  import: list
  import: arithmetic
  import: combin
  article: "../list/src/rich_list.ot.art"
}
indexed-lists {
  import: list
  import: relation
  article: "../list/src/indexedLists.ot.art"
}
