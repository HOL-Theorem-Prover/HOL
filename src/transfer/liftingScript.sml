open HolKernel Parse boolLib bossLib

open transferTheory

val _ = new_theory "lifting"

Definition Qt_def:
  Qt R Abs Rep Tf <=>
    R = inv Tf O Tf /\
    (!a b. Tf a b ==> Abs a = b) /\
    !a. Tf (Rep a) a
End

Theorem Qt_alt:
  Qt R Abs Rep Tf <=>
      (!a. Abs (Rep a) = a) /\
      (!a. R (Rep a) (Rep a)) /\
      (!c1 c2. R c1 c2 <=> R c1 c1 /\ R c2 c2 /\ Abs c1 = Abs c2) /\
      (Tf = \c a. R c c /\ Abs c = a)
Proof
  simp[Qt_def, FUN_EQ_THM, relationTheory.inv_DEF, relationTheory.O_DEF] >>
  metis_tac[]
QED

Theorem Qt_alt_def2:(* isabelle name *)
  Qt R Abs Rep Tf <=>
    (!c a. Tf c a ==> Abs c = a) /\
    (!a. Tf (Rep a) a) /\
    !c1 c2. R c1 c2 <=> Tf c1 (Abs c2) /\ Tf c2 (Abs c1)
Proof
  simp[Qt_def, FUN_EQ_THM, relationTheory.O_DEF, relationTheory.inv_DEF] >>
  metis_tac[]
QED


Theorem idQ[simp]:
  Qt $= I I $=
Proof
  simp[Qt_def, FUN_EQ_THM, relationTheory.inv_DEF] >> metis_tac[]
QED

Theorem pairQ:
  Qt R1 Abs1 Rep1 Tf1 /\ Qt R2 Abs2 Rep2 Tf2 ==>
  Qt (R1 ### R2) (Abs1 ## Abs2) (Rep1 ## Rep2) (Tf1 ### Tf2)
Proof
  simp[Qt_def, pairTheory.FORALL_PROD, FUN_EQ_THM, PAIR_REL_def,
       relationTheory.inv_DEF, relationTheory.O_DEF, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem listQ:
  Qt R Abs Rep Tf ==> Qt (LIST_REL R) (MAP Abs) (MAP Rep) (LIST_REL Tf)
Proof
  simp[Qt_def, FUN_EQ_THM, relationTheory.inv_DEF, relationTheory.O_DEF] >>
  rw[]
  >- (rename [‘LIST_REL R al bl <=> ?y. _ y /\ _ y’] >>
      map_every qid_spec_tac [‘bl’, ‘al’] >> Induct_on ‘al’ >>
      simp[PULL_EXISTS] >> metis_tac[])
  >- (rename [‘MAP Abs al = bl’] >>
      pop_assum mp_tac >> map_every qid_spec_tac [‘bl’, ‘al’] >>
      Induct_on ‘al’ >>
      simp[PULL_EXISTS] >> metis_tac[])
  >- (rename [‘LIST_REL Tf (MAP Rep al) al’] >>
      Induct_on ‘al’ >> simp[PULL_EXISTS])
QED

Definition map_fun_def:
  map_fun f g h = g o h o f
End
val _ = set_mapped_fixity{fixity = Infixr 501, term_name = "map_fun",
                          tok = "--->"}

Theorem map_fun_thm[simp]:
  (f ---> g) h x = g (h (f x))
Proof
  simp[map_fun_def]
QED

(* no idea which orientation of this makes most sense *)
Theorem map_fun_o:
  (f1 o f2) ---> (g1 o g2) = (f2 ---> g1) o (f1 ---> g2)
Proof
  simp[FUN_EQ_THM]
QED


Theorem map_fun_id[simp]:
  (I ---> I) = I
Proof
  simp[FUN_EQ_THM, map_fun_def]
QED

Theorem funQ:
  Qt (D : 'a -> 'a -> bool) AbsD (RepD : 'c -> 'a) (TfD : 'a -> 'c -> bool) /\
  Qt (R : 'b -> 'b -> bool) (AbsR : 'b -> 'd) (RepR : 'd -> 'b)
     (TfR : 'b -> 'd -> bool) ==>
  Qt ((D |==> R) : ('a -> 'b) -> ('a -> 'b) -> bool)
     (RepD ---> AbsR)
     (AbsD ---> RepR)
     (TfD |==> TfR)
Proof
  simp[Qt_alt_def2, relationTheory.O_DEF, relationTheory.inv_DEF, FUN_EQ_THM,
       FUN_REL_def, PULL_EXISTS] >> metis_tac[]
QED

Theorem HK_thm2:
  Qt R Abs Rep Tf /\ f = Abs t /\ R t t ==> Tf t f
Proof
  simp[Qt_alt_def2] >> metis_tac[]
QED

Theorem Qt_EQ:
  Qt R Abs Rep Tf ==> (Tf |==> Tf |==> (=)) R $=
Proof
  simp[Qt_def, FUN_REL_def, relationTheory.inv_DEF,
       relationTheory.O_DEF] >> metis_tac[]
QED

Theorem Qt_right_unique:
  Qt R Abs Rep Tf ==> right_unique Tf
Proof
  simp[Qt_def, right_unique_def, relationTheory.O_DEF, relationTheory.inv_DEF]>>
  metis_tac[]
QED

Theorem Qt_surj:
  Qt R Abs Rep Tf ==> surj Tf
Proof
  simp[Qt_def, surj_def, relationTheory.inv_DEF, relationTheory.O_DEF] >>
  metis_tac[]
QED

val _ = export_theory()
