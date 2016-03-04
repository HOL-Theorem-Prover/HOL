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
}
marker {
  article: "../marker/marker.ot.art"
!interpretation
}
combin {
  import: marker
  article: "../combin/combin.ot.art"
!interpretation
}
relation {
  import: combin
  article: "../relation/relation.ot.art"
!interpretation
}
one {
  article: "../one/one.ot.art"
!interpretation
}
pair {
  import: relation
  article: "../pair/src/pair.ot.art"
!interpretation
}
poset {
  import: pair
  article: "../pair/src/poset.ot.art"
!interpretation
}
sum {
  import: combin
  article: "../sum/sum.ot.art"
!interpretation
}
option {
  import: one
  import: sum
  article: "../option/option.ot.art"
!interpretation
}
