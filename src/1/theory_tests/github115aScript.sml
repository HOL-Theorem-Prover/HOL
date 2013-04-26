open HolKernel Parse boolLib

val _ = new_theory "github115a"

val v1 = mk_var("v", bool --> bool)
val v2 = mk_var("v", bool)

val t = mk_forall(v1, v2)

val atoms = all_atoms t

val _ = assert
          (fn _ => length (HOLset.listItems atoms) = 3 andalso
                   HOLset.member(atoms, v1) andalso
                   HOLset.member(atoms, v2))
          t

val th = save_thm("th", DISCH_ALL (ASSUME t))

val _ = export_theory()
