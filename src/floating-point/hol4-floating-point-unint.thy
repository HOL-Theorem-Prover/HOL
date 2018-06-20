name: hol-floating-point-unint
version: 1.0
description: HOL floating point theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: machine-ieee
  import: binary-ieee
}
machine-ieee {
  import: binary-ieee
  article: "machine_ieee.ot.art"
}
binary-ieee {
  article: "binary_ieee.ot.art"
}
