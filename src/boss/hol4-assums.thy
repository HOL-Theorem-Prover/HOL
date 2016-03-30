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
  package: base-1.200
}
hol {
  import: base
  package: hol-base-unsat-1.0
}
