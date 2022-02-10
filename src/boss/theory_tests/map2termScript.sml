open HolKernel Parse boolLib bossLib;

val _ = new_theory "map2term";

Datatype:
  tree = Lf num | Nd num (tree list)
End

Definition plus_def:
  (plus (Lf n1) (Lf n2) = Lf (n1 + n2)) /\
  (plus (Nd n1 bs1) (Nd n2 bs2) =
     if n1 = n2 then
       Nd n1 (MAP2 plus bs1 bs2)
     else Lf 0)
Termination
  WF_REL_TAC ‘measure (tree_size o FST)’
End


val _ = export_theory();
