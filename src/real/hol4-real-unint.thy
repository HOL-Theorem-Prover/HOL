name: hol-real-unint
version: 1.0
description: HOL real theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: real
  import: intreal
  import: iterate
  import: real-sigma
  import: metric
  import: nets
}
real {
  article: "real.ot.art"
}
intreal {
  import: real
  article: "intreal.ot.art"
}
iterate {
  import: real
  article: "iterate.ot.art"
}
real-sigma {
  import: real
  import: iterate
  article: "real_sigma.ot.art"
}
metric {
  import: real
  article: "metric.ot.art"
}
nets {
  import: real
  import: metric
  article: "nets.ot.art"
}
