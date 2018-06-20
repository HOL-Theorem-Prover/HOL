name: hol-words-unint
version: 1.0
description: n-bit words (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: alignment
  import: bitstring
  import: blast
  import: fcp
  import: sum-num
  import: words
}
alignment {
  import: fcp
  import: words
  article: "alignment.ot.art"
}
bitstring {
  import: fcp
  import: words
  article: "bitstring.ot.art"
}
blast {
  import: fcp
  import: words
  article: "blast.ot.art"
}
fcp {
  article: "fcp.ot.art"
}
sum-num {
  article: "sum_num.ot.art"
}
words {
  import: fcp
  import: sum-num
  article: "words.ot.art"
}
