name: machine-code-hoare-logic-unint
version: 1.0
description: A Hoare logic for machine code (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: address
  import: prog
  import: set-sep
  import: tailrec
  import: temporal
}
address {
  article: "address.ot.art"
}
prog {
  import: set-sep
  import: tailrec
  article: "prog.ot.art"
}
set-sep {
  article: "set_sep.ot.art"
}
tailrec {
  article: "tailrec.ot.art"
}
temporal {
  import: set-sep
  import: prog
  article: "temporal.ot.art"
}
