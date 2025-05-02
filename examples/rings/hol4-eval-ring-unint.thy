name: hol-eval-ring-unint
version: 1.1
description: HOL ring theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: EVAL_ring
  import: EVAL_canonical
  import: EVAL_numring
  import: EVAL_quote
  import: EVAL_ring-norm
  import: EVAL_semiring
}
EVAL_ring {
  import: EVAL_semiring
  article: "EVAL_ring.ot.art"
}
EVAL_ring-norm {
  import: EVAL_canonical
  import: EVAL_ring
  import: EVAL_semiring
  article: "EVAL_ringNorm.ot.art"
}
EVAL_canonical {
  import: EVAL_quote
  import: EVAL_semiring
  article: "EVAL_canonical.ot.art"
}
EVAL_quote {
  article: "EVAL_quote.ot.art"
}
EVAL_semiring {
  article: "EVAL_semiring.ot.art"
}
EVAL_numring {
  import: EVAL_canonical
  import: EVAL_quote
  import: EVAL_semiring
  article: "EVAL_numRing.ot.art"
}
