name: hol-integer-unint
version: 1.0
description: HOL integer theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: integer
  import: integer-word
  import: omega
  import: integer-ring
  import: int-bitwise
  import: int-arith
  import: deep-syntax
}
integer {
  article: "integer.ot.art"
}
integer-word {
  import: integer
  import: int-arith
  article: "integer_word.ot.art"
}
omega {
  import: integer
  article: "Omega.ot.art"
}
integer-ring {
  import: integer
  article: "integerRing.ot.art"
}
int-bitwise {
  import: integer
  import: int-arith
  article: "int_bitwise.ot.art"
}
int-arith {
  import: integer
  article: "int_arith.ot.art"
}
deep-syntax {
  import: integer
  import: int-arith
  article: "DeepSyntax.ot.art"
}
