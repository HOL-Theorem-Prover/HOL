name: machine-code-hoare-logic-unint
version: 1.0
description: Machine code Hoare logic state (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: state
  import: temporal-state
}
state {
  article: "state.ot.art"
}
temporal-state {
  import: state
  article: "temporal_state.ot.art"
}
