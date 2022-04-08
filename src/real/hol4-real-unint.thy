name: hol-real-unint
version: 1.0
description: HOL real theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: real
  import: intreal
  import: transc
  import: powser
  import: integral
  import: poly
  import: real-sigma
  import: seq
  import: metric
  import: lim
  import: nets
  import: iterate
}
real {
  article: "real.ot.art"
}
intreal {
  import: real
  article: "intreal.ot.art"
}
transc {
  import: real
  import: seq
  import: lim
  import: powser
  article: "transc.ot.art"
}
powser {
  import: real
  import: lim
  import: seq
  article: "powser.ot.art"
}
integral {
  import: real
  import: transc
  import: seq
  import: lim
  article: "integral.ot.art"
}
poly {
  import: real
  import: lim
  article: "poly.ot.art"
}
iterate {
  import: real
  article: "iterate.ot.art"
}
real-sigma {
  import: real
  import: seq
  import: iterate
  import: transc
  article: "real_sigma.ot.art"
}
seq {
  import: real
  import: metric
  import: nets
  article: "seq.ot.art"
}
metric {
  import: real
  article: "metric.ot.art"
}
lim {
  import: real
  import: metric
  import: nets
  import: seq
  article: "lim.ot.art"
}
nets {
  import: real
  import: metric
  article: "nets.ot.art"
}
