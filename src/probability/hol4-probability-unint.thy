name: hol-probability-unint
version: 1.0
description: HOL probability theory (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: util-prob
  import: sigma-algebra
  import: real-borel
  import: measure
  import: borel
  import: lebesgue
  import: martingale
  import: probability
}
util-prob {
  article: "util_prob.ot.art"
}
sigma-algebra {
  import: util-prob
  article: "sigma_algebra.ot.art"
}
real-borel {
  import: util-prob
  import: sigma-algebra
  article: "real_borel.ot.art"
}
measure {
  import: util-prob
  import: sigma-algebra
  article: "measure.ot.art"
}
borel {
  import: util-prob
  import: sigma-algebra
  import: real-borel
  import: measure
  article: "borel.ot.art"
}
lebesgue {
  import: util-prob
  import: sigma-algebra
  import: measure
  import: borel
  article: "lebesgue.ot.art"
}
martingale {
  import: util-prob
  import: sigma-algebra
  import: real-borel
  import: measure
  import: borel
  import: lebesgue
  article: "martingale.ot.art"
}
probability {
  import: util-prob
  import: sigma-algebra
  import: measure
  import: borel
  import: lebesgue
  import: martingale
  article: "probability.ot.art"
}
