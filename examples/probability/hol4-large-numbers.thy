name: hol-large-numbers
version: 1.1
description: HOL theories up to the Law of Large Numbers (including OpenTheory base)
author: Chun Tian <binghe.lisp@gmail.com>
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
show: "Number.Real"
main {
  import: base
  import: hol-base
  import: hol-set
  import: hol-real
  import: hol-extreal
  import: hol-analysis
  import: hol-probability
  import: large-number
}
base {
  package: base-1.221
}
hol-base {
  import: base
  package: hol-base-1.3
}
hol-sort {
  import: base
  import: hol-base
  package: hol-sort-1.1
}
hol-string {
  import: base
  import: hol-base
  import: hol-sort
  package: hol-string-1.2
}
hol-words {
  import: base
  import: hol-base
  import: hol-string
  package: hol-words-1.3
}
hol-ring {
  import: base
  import: hol-base
  import: hol-sort
  package: hol-ring-1.2
}
hol-res-quan {
  import: base
  import: hol-base
  package: hol-res-quan-1.2
}
hol-quotient {
  import: base
  import: hol-base
  import: hol-res-quan
  package: hol-quotient-1.2
}
hol-set {
  import: base
  import: hol-base
  import: hol-quotient  
  package: hol-set-1.0
}
hol-integer {
  import: base
  import: hol-base
  import: hol-words
  import: hol-string
  import: hol-ring
  import: hol-quotient
  package: hol-integer-1.2
}
hol-real {
  import: base
  import: hol-base
  import: hol-set
  import: hol-integer
  package: hol-real-1.2
}
hol-analysis {
  import: base
  import: hol-base
  import: hol-set
  import: hol-real
  package: hol-analysis-1.1
}
hol-extreal {
  import: base
  import: hol-base
  import: hol-set
  import: hol-real
  import: hol-analysis
  package: hol-extreal-1.0
}
hol-probability {
  import: base
  import: hol-base
  import: hol-set
  import: hol-real
  import: hol-analysis
  import: hol-extreal
  import: hol-words
  package: hol-probability-1.1
}
large-number {
  import: base
  import: hol-base
  import: hol-set
  import: hol-real
  import: hol-extreal
  import: hol-analysis
  import: hol-probability
  article: "large_number.ot.art"
  interpretation: "../../src/opentheory/hol4.int"
}
