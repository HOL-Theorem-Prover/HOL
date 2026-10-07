name: hol-set-unint
version: 1.0
description: HOL set theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: ordinal
  import: topology
}
ordinal {
  import: topology
  article: "ordinal.ot.art"
}
topology {
  article: "topology.ot.art"
}
