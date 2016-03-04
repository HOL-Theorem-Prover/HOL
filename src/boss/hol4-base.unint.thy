name: HOL4 Base
version: 1.0
description: HOL4 Basic theories
author: HOL4 people
license: BSD
show: "HOL4"
show: "Data.Bool"
show: "Data.Option"
show: "Data.Unit"
show: "Data.Sum"
show: "Data.Pair"
show: "Function"
show: "Relation"
show: "Number.Natural"
requires: base
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
  import: one
  import: sum
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
