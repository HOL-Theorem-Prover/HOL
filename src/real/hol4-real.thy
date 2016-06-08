name: hol-real
version: 1.1
description: HOL real theories
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-integer
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Number.Real"
show: "Relation"
main {
  import: unsat
  import: proofs
}
unsat {
  import: proofs
  article: "hol4-real-unsat.art"
}
proofs {
  article: "prove_real_assums.ot.art"
  interpretation: "../opentheory/hol4.int"
  interpret: const "HOL4.prove_real_assums.real_0" as "HOL4.realax.real_0"
  interpret: const "HOL4.prove_real_assums.real_1" as "HOL4.realax.real_1"
  interpret: const "HOL4.prove_real_assums.inv" as "Number.Real.inv"
  interpret: const "HOL4.prove_real_assums.inv0" as "HOL4.realax.inv"
  interpret: const "HOL4.prove_real_assums./" as "Number.Real./"
  interpret: const "HOL4.prove_real_assums.real_div" as "HOL4.real./"
}
