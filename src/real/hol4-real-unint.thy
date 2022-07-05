name: hol-real-unint
version: 1.0
description: HOL real theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: realax
  import: real
  import: intreal
  import: iterate
  import: real-sigma
  import: metric
  import: nets
}
realax {
  article: "realax.ot.art"
}
real {
  import: realax
  article: "real.ot.art"
}
intreal {
  import: realax
  import: real
  article: "intreal.ot.art"
}
iterate {
  import: realax
  import: real
  article: "iterate.ot.art"
}
real-sigma {
  import: realax
  import: real
  import: iterate
  article: "real_sigma.ot.art"
}
metric {
  import: realax
  import: real
  article: "metric.ot.art"
}
nets {
  import: realax
  import: real
  import: metric
  article: "nets.ot.art"
}
