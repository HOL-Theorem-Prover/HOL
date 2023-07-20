name: hol-extreal-unint
version: 1.0
description: HOL4 extended reals (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: extreal-base
  import: extreal
}
extreal-base {
  article: "../real/extreal_base.ot.art"
}
extreal {
  import: extreal-base
  article: "extreal.ot.art"
}
