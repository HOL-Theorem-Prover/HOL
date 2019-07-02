open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open recfunsTheory;
open recsetsTheory;
open prnlistTheory;
open recursivefnsTheory;
open primrecfnsTheory;
open prtermTheory;


val _ = new_theory "recdegrees"

Datatype`form = BASE num num | EXISTS num form | ALL num form`

Definition MKEA[simp]:
 (MKEA 0 R = BASE R 1) ∧
 (MKEA (SUC n) R = EXISTS (SUC n) (MKAE n R)) ∧
 (MKAE 0 R = BASE R 1) ∧
 (MKAE (SUC n) R = ALL (SUC n) (MKEA n R))
End

Definition interpret[simp]:
  (interpret σ (BASE Ri n) <=> (Phi Ri (nlist_of (MAP σ (GENLIST I (n)))) = SOME 1)) ∧
  (interpret σ (EXISTS v f) <=> ∃n. interpret σ⦇v↦n⦈ f) ∧
  (interpret σ (ALL v f) <=> ∀n. interpret σ⦇v↦n⦈ f)
End

Definition rec_sigma:
  (rec_sigma A n <=> 
  ∃Ri. (∀m. (Phi Ri m = SOME 0) ∨ (Phi Ri m = SOME 1)) ∧ 
       ∀x. x∈A <=> interpret I⦇0↦x⦈ (MKEA n Ri))					
End

Theorem recfn_nhd:
  recfn (SOME o pr1 nhd) 1
Proof
  fs[primrec_nhd,primrec_recfn]
QED

Theorem nhd_nlist_of:
  nhd (nlist_of (h::t)) = h
Proof
  fs[nhd_thm]
QED

Theorem nhd_phi_exists:
  ∃i. ∀x. Phi i (nlist_of x) = SOME (pr1 nhd x)
Proof
  assume_tac recfn_nhd >> drule recfns_in_Phi >> rw[] >> qexists_tac`i` >> rw[] >> 
  `∃l. nlist_of l = x` by fs[nlist_of_onto] >> rw[] >> Cases_on`l` >> rw[]
QED


Theorem recfn_ncons:
  recfn (SOME o pr2 ncons) 2
Proof
  assume_tac primrec_ncons >> fs[primrec_recfn]
QED

Theorem recfn_ncons1:
  recfn (SOME o pr1 (λx. ncons x 0)) 1
Proof
  assume_tac primrec_ncons >> 
  `Cn (pr2 ncons) [(proj 0); zerof] = pr1 (λx. ncons x 0)` by 
    (fs[FUN_EQ_THM,Cn_def,pr1_def] >> rw[] >> Cases_on`x` >> rw[] ) >> 
  `recfn (SOME o  (Cn (pr2 ncons) [proj 0; zerof])) 1` suffices_by rw[] >> 
  `primrec (Cn (pr2 ncons) [proj 0; zerof]) 1` suffices_by fs[primrec_recfn] >>
  fs[primrec_rules]
QED

Theorem ncons_phi_exists:
  ∃i. ∀x. Phi i x = SOME (ncons x 0)
Proof
  assume_tac recfn_ncons1 >> drule recfns_in_Phi >> rw[] >>
  qexists_tac`i` >> rw[] >> 
  `∃l. nlist_of l = x` by fs[nlist_of_onto] >> rw[] >> Cases_on`l` >> rw[] >> 
QED

Theorem recfn_nlist_of:
  ∃Ri. ∀n. Phi Ri n = SOME (nlist_of [n])
Proof
  fs[nlist_of_def] >> 
QED

Theorem recfns_in_Phi2:
  ∀f n. recfn f 1 ⇒ ∃i. ∀x. Phi i x = f [x]
Proof
  rw[] >> drule recfns_in_Phi >> rw[] >> 
  `∃Ri. ∀n. Phi Ri n = SOME (nlist_of [n])` by fs[recfn_nlist_of] >>
  `∃Rii. ∀n. Phi Rii n = monad_bind (Phi Ri n) (λx. Phi i x)` by fs[composition_computable] >>
  qexists_tac`Rii` >> rw[] >> ` Phi i (nlist_of [x]) = f [x]` by fs[] >> fs[]
QED

Theorem rec_sigma0_corr:
  rec_sigma A 0 <=> recursive A
Proof
  simp[rec_sigma,recursive_def] >> eq_tac >> rw[]
  >- (fs[combinTheory.APPLY_UPDATE_THM] >>
      `∃i. ∀x. Phi i x = SOME (ncons x 0)` by cheat fs[ncons_phi_exists] >> 
      `∃Rii. ∀n. Phi Rii n = monad_bind (Phi i n) (λx. Phi Ri x)` by fs[composition_computable]>>      qexists_tac`Rii` >> rw[] >> metis_tac[] )
  >- ()
QED

Definition rec_pi:
  (rec_pi A 0 <=> recursive A) ∧
  (rec_pi A (SUC n) <=> ∃R m. rec_relation R m ∧ (∀x. x∈A <=> all_exists m (R x)  ) )					
End

Definition rec_delta:
  (rec_delta A n <=> (rec_sigma A n ∧ rec_pi A n ))				
End

Theorem 1_3_i:
  rec_sigma A n <=> rec_pi (COMPL A) n
Proof

QED

Theorem 1_3_ii1:
  rec_sigma A n ==> (∀m. m>n ==> (rec_sigma A m ∨ rec_pi A m) )
Proof

QED

Theorem 1_3_ii2:
  rec_pi A n ==> (∀m. m>n ==> (rec_sigma A m ∨ rec_pi A m) )
Proof

QED


Theorem 1_3_iii1:
  rec_sigma A n ∧ rec_sigma B n ==> (rec_sigma (A ∪ B) n ∧ rec_sigma (A ∩ B) n)
Proof

QED

Theorem 1_3_iii2:
  rec_pi A n ∧ rec_pi B n ==> (rec_pi (A ∪ B) n ∧ rec_pi (A ∩ B) n)
Proof

QED

Theorem 1_3_iv:
  rec_sigma R n ∧ n>0 ∧ A = {x | ∃y. R (x,y)} ==> rec_sigma A n
Proof

QED

val _ = export_theory()
