name: hol-real-assums
version: 1.1
description: Assumptions of the HOL real theories
author: HOL4 people
license: BSD
base {
  package: base-1.221
}
hol-base {
  import: base
  package: hol-base-1.4
}
hol-set {
  import: base
  import: hol-base
  import: hol-quotient
  package: hol-set-1.0
}
hol-string {
  import: base
  import: hol-base
  package: hol-string-1.2
}
hol-words {
  import: base
  import: hol-base
  import: hol-string
  package: hol-words-1.2
}
hol-ring {
  import: base
  import: hol-base
  package: hol-ring-1.2
}
hol-res-quan {
  import: base
  import: hol-base
  package: hol-res-quan-1.1
}
hol-quotient {
  import: base
  import: hol-base
  import: hol-res-quan
  package: hol-quotient-1.1
}
hol-sort {
  import: base
  import: hol-base
  package: hol-sort-1.1
}
hol-bag {
  import: base
  import: hol-base
  package: hol-bag-1.0
}
hol-finite-map {
  import: base
  import: hol-base
  import: hol-sort
  package: hol-finite-map-1.0
}
hol-integer {
  import: base
  import: hol-base
  import: hol-words
  import: hol-string
  import: hol-ring
  import: hol-quotient
  package: hol-integer-1.1
}
main {
  import: base
  import: hol-base
  import: hol-integer
  import: hol-set
  article: "hol4-real-unsat.art"
}
