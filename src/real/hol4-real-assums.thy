name: hol-real-assums
version: 1.0
description: Assumptions of the HOL real theories
author: HOL4 people
license: BSD
base {
  package: base-1.200
}
hol-base {
  import: base
  package: hol-base-1.0
}
hol-string {
  import: base
  import: hol-base
  package: hol-string-1.0
}
hol-words {
  import: base
  import: hol-base
  import: hol-string
  package: hol-words-1.0
}
hol-ring {
  import: base
  import: hol-base
  package: hol-ring-1.0
}
hol-res-quan {
  import: base
  import: hol-base
  package: hol-res-quan-1.0
}
hol-quotient {
  import: base
  import: hol-base
  import: hol-res-quan
  package: hol-quotient-1.0
}
hol-integer {
  import: base
  import: hol-base
  import: hol-words
  import: hol-string
  import: hol-ring
  import: hol-quotient
  package: hol-integer-1.0
}
main {
  import: base
  import: hol-base
  import: hol-integer
  article: "hol4-real-unsat.art"
}
