name: hol-finite-maps-unint
version: 1.0
description: HOL finite maps (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: finite-map
  import: alist
}
finite-map {
  article: "finite_map.ot.art"
}
alist {
  import: finite-map
  article: "alist.ot.art"
}
