Theory github115a[bare]
Libs
  HolKernel Parse boolLib

val v1 = mk_var("v", bool --> bool)
val v2 = mk_var("v", bool)

val t = mk_forall(v1, v2)

val atoms = all_atoms t

val _ = assert
          (fn _ => length (HOLset.listItems atoms) = 3 andalso
                   HOLset.member(atoms, v1) andalso
                   HOLset.member(atoms, v2))
          t

Theorem th = DISCH_ALL (ASSUME t)

