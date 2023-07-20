open HolKernel Parse boolLib bossLib;

val _ = new_theory "dbdef";

Definition variant_def:
  variant x xs = if MEM x xs then variant (x + 1) xs else x
Termination
  WF_REL_TAC ‘measure (λ(n,ns). LENGTH (FILTER (λm. n <= m) ns))’ >>
  Induct_on ‘xs’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  irule (DECIDE “x <= y ==> x < SUC y”) >>
  irule listTheory.LENGTH_FILTER_LEQ_MONO >> simp[]
End

val foo_def = Definition.new_definition("foo_def", “foo x = x + 1”);
val bar_def = new_definition("bar_def", “bar x = x + 2”);

Definition just_listpr:
  just_listpr [] = SOME [] /\
  just_listpr (h::t) =
  case (h,just_listpr t) of
    (NONE, _) => NONE
  | (_, NONE) => NONE
  | (SOME h, SOME t) => SOME(h::t)
End

Definition just_listcase:
  just_listcase l =
  case l of
    [] => SOME []
  | h::t => case (h,just_listcase t) of
              (NONE, _) => NONE
            | (_, NONE) => NONE
            | (SOME h, SOME t) => SOME (h::t)
End




val _ = export_theory();
