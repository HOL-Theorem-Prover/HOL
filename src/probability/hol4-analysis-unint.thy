name: hol-analysis-unint
version: 1.0
description: HOL real analysis (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: iterate
  import: product
  import: real-topology
  import: derivative
  import: integration
}
iterate {
  article: "iterate.ot.art"
}
product {
  import: iterate
  article: "iterate.ot.art"
}
real-topology {
  import: iterate
  import: product
  article: "real_topology.ot.art"
}
derivative {
  import: iterate
  import: product
  import: real-topology
  article: "derivative.ot.art"
}
integration {
  import: iterate
  import: product
  import: real-topology
  import: derivative
  article: "integration.ot.art"
}
