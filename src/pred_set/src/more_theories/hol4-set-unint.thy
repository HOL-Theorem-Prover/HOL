name: hol-set-unint
version: 1.0
description: HOL set theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: cardinal
  import: ordinal-basic
  import: ordinal
  import: topology
  import: wellorder
  import: permutes
}
cardinal {
  import: wellorder
  import: permutes
  article: "../cardinal.ot.art"
}
ordinal-basic {
  import: wellorder
  import: cardinal
  article: "../ordinalBasic.ot.art"
}
ordinal {
  import: wellorder
  import: cardinal
  import: topology
  import: ordinal-basic
  article: "ordinal.ot.art"
}
topology {
  import: cardinal
  article: "topology.ot.art"
}
wellorder {
  article: "../wellorder.ot.art"
}
permutes {
  article: "../permutes.ot.art"
}
