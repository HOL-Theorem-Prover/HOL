Theory gh168d[bare]
Ancestors
  gh294a gh294b
Libs
  HolKernel Parse boolLib testutils

val b2b = bool --> bool
val b2b2b = bool --> b2b
val ty1 = ``:gh294a$foo``
val ty2 = ``:gh294b$foo``

val _ = assert (equal b2b) ty1
val _ = assert (equal b2b2b) ty2

