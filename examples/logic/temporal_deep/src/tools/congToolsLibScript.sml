Theory congToolsLib
Libs
  Sanity

Definition LIST_AS_SET_CONGRUENCE_RELATION_def:
   LIST_AS_SET_CONGRUENCE_RELATION R l1 l2 =
          ((!x1. MEM x1 l1 ==> (?x2. MEM x2 l2 /\ R x1 x2)) /\
           (!x2. MEM x2 l2 ==> (?x1. MEM x1 l1 /\ R x1 x2)))
End


Theorem LIST_AS_SET_CONGRUENCE_RELATION_REFL:
      !R. (!x. R x x) ==> (!l. LIST_AS_SET_CONGRUENCE_RELATION R l l)
Proof

      SIMP_TAC std_ss [LIST_AS_SET_CONGRUENCE_RELATION_def] THEN
      PROVE_TAC[]
QED


Theorem LIST_AS_SET_CONGRUENCE_RELATION_TRANS:
      !R. (!x1 x2 x3. (R x1 x2 /\ R x2 x3) ==> R x1 x3) ==> (!l1 l2 l3. LIST_AS_SET_CONGRUENCE_RELATION R l1 l2 /\ LIST_AS_SET_CONGRUENCE_RELATION R l2 l3 ==> LIST_AS_SET_CONGRUENCE_RELATION R l1 l3)
Proof

      SIMP_TAC std_ss [LIST_AS_SET_CONGRUENCE_RELATION_def] THEN
      METIS_TAC[]
QED


Theorem LIST_AS_SET_CONGRUENCE_RELATION_CONG:
      !R e e' l l'.
        R e e' ==>
        LIST_AS_SET_CONGRUENCE_RELATION R l l' ==>
        LIST_AS_SET_CONGRUENCE_RELATION R (e::l) (e'::l')
Proof

      SIMP_TAC list_ss [LIST_AS_SET_CONGRUENCE_RELATION_def] THEN
      METIS_TAC[]
QED


Theorem LIST_AS_SET_CONGRUENCE_RELATION_REWRITES:
      !R. (
      (!e l. LIST_AS_SET_CONGRUENCE_RELATION R (e::l) [] = F) /\
      (!e l. LIST_AS_SET_CONGRUENCE_RELATION R [] (e::l) = F) /\
      (!e l l'. LIST_AS_SET_CONGRUENCE_RELATION R (e::e::l) l' =
                  LIST_AS_SET_CONGRUENCE_RELATION R (e::l) l') /\
      (!e l l'. LIST_AS_SET_CONGRUENCE_RELATION R l' (e::e::l) =
                  LIST_AS_SET_CONGRUENCE_RELATION R l' (e::l)))
Proof

      SIMP_TAC list_ss [LIST_AS_SET_CONGRUENCE_RELATION_def] THEN
      METIS_TAC[]
QED


