name: hol-sort-unint
version: 1.1
description: HOL sorting theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: sorting
  import: mergesort
  import: ternary-comparisons
}
sorting {
  article: "sorting.ot.art"
}
mergesort {
  import: sorting
  article: "mergesort.ot.art"
}
ternary-comparisons {
  article: "ternaryComparisons.ot.art"
}
