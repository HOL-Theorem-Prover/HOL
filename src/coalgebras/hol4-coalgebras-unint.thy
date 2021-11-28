name: hol-coalgebras
version: 1.0
description: HOL coalgebras theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: GPL
main {
  import: llist
  import: lbtree
  import: path
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
