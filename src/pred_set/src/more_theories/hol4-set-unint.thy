name: hol-set-unint
version: 1.0
description: HOL set theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: cardinal
  import: ordinal
  import: topology
  import: wellorder
  import: permutes
}
cardinal {
  import: wellorder
  article: "cardinal.ot.art"
}
ordinal {
  import: wellorder
  import: cardinal
  import: topology
  article: "ordinal.ot.art"
}
topology {
  import: cardinal
  article: "topology.ot.art"
}
wellorder {
  article: "wellorder.ot.art"
}
permutes {
  import: cardinal
  article: "permutes.ot.art"
}
