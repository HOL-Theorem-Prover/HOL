name: hol-extreal-unint
version: 1.0
description: HOL4 extended reals (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: util-prob
  import: extreal
}
util-prob {
  article: "util_prob.ot.art"
}
extreal {
  import: util-prob
  article: "extreal.ot.art"
}
