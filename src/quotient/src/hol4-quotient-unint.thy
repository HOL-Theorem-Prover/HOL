name: hol-quotient-unint
version: 1.0
description: HOL quotient theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: quotient
  import: quotient-option
  import: quotient-list
  import: quotient-pair
  import: quotient-pred-set
  import: quotient-sum
}
quotient {
  article: "quotient.ot.art"
}
quotient-option {
  import: quotient
  article: "quotient_option.ot.art"
}
quotient-list {
  import: quotient
  article: "quotient_list.ot.art"
}
quotient-pair {
  import: quotient
  article: "quotient_pair.ot.art"
}
quotient-pred-set {
  import: quotient
  import: quotient-pair
  article: "quotient_pred_set.ot.art"
}
quotient-sum {
  import: quotient
  article: "quotient_sum.ot.art"
}
