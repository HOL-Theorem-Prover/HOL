name: hol-real-assums
version: 1.0
description: Assumptions of the HOL real theories
author: HOL4 people
license: BSD
main {
  import: base
  import: hol-base
  import: hol-set
  import: hol-integer
  article: "hol4-real-unsat.art"
}
base {
  package: base-1.221
}
hol-base {
  import: base
  article: "../boss/hol4-base.art"
}
hol-set {
  import: base
  import: hol-base
  import: hol-quotient
  article: "../pred_set/src/more_theories/hol4-set.art"
}
hol-string {
  import: base
  import: hol-base
  article: "../string/hol4-string.art"
}
hol-words {
  import: base
  import: hol-base
  import: hol-string
  article: "../n-bit/hol4-words.art"
}
hol-ring {
  import: base
  import: hol-base
  article: "../ring/src/hol4-ring.art"
}
hol-res-quan {
  import: base
  import: hol-base
  article: "../res_quan/src/hol4-res-quan.art"
}
hol-quotient {
  import: base
  import: hol-base
  import: hol-res-quan
  article: "../quotient/src/hol4-quotient.art"
}
hol-integer {
  import: base
  import: hol-base
  import: hol-words
  import: hol-string
  import: hol-ring
  import: hol-quotient
  article: "../integer/hol4-integer.art"
}
