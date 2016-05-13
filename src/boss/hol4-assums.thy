name: hol-base-assums
version: 1.0
description: Assumptions of the HOL basic theories
author: HOL4 people
license: BSD
main {
  import: base
  import: hol
}
base {
  package: base-1.202
}
hol {
  import: base
  article: "hol4-base-unsat.art"
  interpretation: "../opentheory/hol4.int"
}
