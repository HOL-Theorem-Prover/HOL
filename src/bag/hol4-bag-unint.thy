name: hol-bag-unint
version: 1.0
description: HOL bag theory (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: bag
  import: prime-factor
}
bag {
  article: "bag.ot.art"
}
prime-factor {
  import: bag
  article: "primeFactor.ot.art"
}
