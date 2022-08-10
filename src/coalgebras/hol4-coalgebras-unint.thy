name: hol-coalgebras
version: 1.0
description: HOL coalgebras theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: llist
  import: lbtree
  import: path
  import: bisimulation
}
bisimulation {
  article: "../relation/bisimulation.ot.art"
}
llist {
  article: "llist.ot.art"
}
lbtree {
  import: llist
  article: "lbtree.ot.art"
}
path {
  import: llist
  article: "path.ot.art"
}
