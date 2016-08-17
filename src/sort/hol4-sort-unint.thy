name: hol-sort-unint
version: 1.0
description: HOL sorting theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: sorting
  import: mergesort
}
sorting {
  article: "sorting.ot.art"
}
mergesort {
  import: sorting
  article: "mergesort.ot.art"
}
