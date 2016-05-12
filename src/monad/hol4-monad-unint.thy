name: hol-monad-unint
version: 1.0
description: HOL monad theories (before re-interpretation)
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
main {
  import: state-transformer
  import: error-state-monad
}
state-transformer {
  article: "state_transformer.ot.art"
}
error-state-monad {
  article: "errorStateMonad.ot.art"
}
