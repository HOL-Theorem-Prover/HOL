name: hol-real-sat
version: 1.0
description: HOL real theories plus proofs of assumptions
author: HOL developers <hol-developers@lists.sourceforge.net>
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
}
