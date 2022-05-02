name: hol-analysis-unint
version: 1.0
description: HOL real analysis (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: real-topology
  import: derivative
  import: integration
  import: transc
  import: powser
  import: poly
  import: lim
  import: seq
  import: integral
}
real-topology {
  article: "real_topology.ot.art"
}
derivative {
  import: real-topology
  import: seq
  article: "derivative.ot.art"
}
integration {
  import: real-topology
  import: seq
  import: lim
  import: transc
  import: derivative
  article: "integration.ot.art"
}
transc {
  import: real-topology
  import: derivative
  import: seq
  import: lim
  import: powser
  article: "transc.ot.art"
}
powser {
  import: real-topology
  import: lim
  import: seq
  article: "powser.ot.art"
}
poly {
  import: real-topology
  import: lim
  article: "poly.ot.art"
}
seq {
  import: real-topology
  article: "seq.ot.art"
}
lim {
  import: real-topology
  import: derivative
  import: seq
  article: "lim.ot.art"
}
integral {
  import: real-topology
  import: seq
  import: lim
  import: integration
  article: "integral.ot.art"
}
