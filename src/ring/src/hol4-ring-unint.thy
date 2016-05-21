name: hol-ring-unint
version: 1.0
description: HOL ring theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: ring
  import: canonical
  import: num-ring
  import: prelim
  import: quote
  import: ring-norm
  import: semi-ring
}
ring {
  import: semi-ring
  article: "ring.ot.art"
}
ring-norm {
  import: canonical
  import: ring
  import: semi-ring
  article: "ringNorm.ot.art"
}
canonical {
  import: prelim
  import: quote
  import: semi-ring
  article: "canonical.ot.art"
}
prelim {
  article: "prelim.ot.art"
}
quote {
  import: prelim
  article: "quote.ot.art"
}
semi-ring {
  article: "semi_ring.ot.art"
}
num-ring {
  import: canonical
  import: quote
  import: semi-ring
  article: "numRing.ot.art"
}
