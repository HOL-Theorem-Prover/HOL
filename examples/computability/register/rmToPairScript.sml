open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;
open primrecfnsTheory;
open listTheory;
open mp_then;
open boolTheory;
open numpairTheory;
open pred_setTheory;
open rmModelTheory;
open rmToolsTheory;
open rmSampleMachinesTheory;

val _ = new_theory "rmToPair";

fun generate_machine_rwts thm = 
  let val (mname,tm)= dest_eq (concl thm)
      val qthm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_Q”, mname))
      val states_t = rhs (concl qthm)
      val states = pred_setSyntax.strip_set states_t
      fun mktf k = SIMP_CONV (srw_ss()) [thm] (list_mk_comb(“rm_tf”, [mname,k]))
      val tf_thms = map mktf states
      val inthm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_In”, mname))
      val outthm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_Out”, mname))
      val q0thm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_q0”, mname))
  in LIST_CONJ (inthm :: outthm :: q0thm :: qthm :: tf_thms)
  end
  
(* Proof *) 
(* 
---------------------------------------------------
----     Proving RM -> Pair, First, Second     ----
---------------------------------------------------
*)

Definition lst_def:
  lst = <|
        Q := {1;2;3;4};
        tf := (λs. case s of 
                | 1 => Dec 1 (SOME 2) NONE
                | 2 => Dec 2 (SOME 1) (SOME 3)
                | 3 => Inc 3 (SOME 4)
                | 4 => Dec 1 (SOME 4) (SOME 1));
        q0 := 1;
        In := [1;2];
        Out := 3;
        |>
End


Theorem lst_thms[simp]:
  lst.Q = {1;2;3;4} ∧
  lst.tf 1 = Dec 1 (SOME 2) NONE ∧
  lst.tf 2 = Dec 2 (SOME 1) (SOME 3) ∧
  lst.tf 3 = Inc 3 (SOME 4) ∧
  lst.tf 4 = Dec 1 (SOME 4) (SOME 1)
Proof 
  rw[lst_def]
QED 

Theorem lst_correct:
  rmcorr lst 1 (λrs. rs = RS ∧ rs 3 = 0) NONE (λrs. rs 3 = if RS 2 < RS 1 then 1 else 0)
Proof 
  irule loop_correct >>
  simp[] >>
  qexists_tac `λrs. (rs 3 = 0 ⇒ (RS 2 < RS 1 ⇔ rs 2 < rs 1)) 
               ∧ (rs 3 = 1 ⇒ (RS 2 < RS 1) ∧ rs 1 = 0 ∧ rs 2 = 0) ∧ rs 3 < 2 ` >>
  simp[] >>
  rpt strip_tac >>
  rw[APPLY_UPDATE_THM] >>
  irule rmcorr_dec >> 
  simp[] >>
  rw[] 
  >- (irule rmcorr_inc >> simp[] >> 
      irule loop_correct >> simp[APPLY_UPDATE_THM] >>
      map_every qexists_tac [`λrs. rs 3 = 1 ∧ (RS 2 < RS 1) ∧ rs 2 = 0`] >> 
      simp[] >>
      rw[APPLY_UPDATE_THM] >> 
      rw[rmcorr_stay])
  >> rw[APPLY_UPDATE_THM] 
  >> `∀rs0. (λrs.((rs 3 = 0 ⇒ (RS 2 < RS 1 ⇔ rs 2 < rs 1)) ∧ rs 3 ≠ 1 ∧ rs 3 < 2) ∧
          rs 1 = N) rs0
   ==>  
    (λrs'.((rs' 3 = 0 ⇒ (RS 2 < RS 1 ⇔ rs' 2 < rs' 1)) ∧
           (rs' 3 = 1 ⇒ RS 2 < RS 1 ∧ rs' 1 = 0 ∧ rs' 2 = 0) ∧ rs' 3 < 2) ∧
          rs' 1 ≤ N) rs0` by rw[APPLY_UPDATE_THM]
  >> rw[rmcorr_stay] 
QED

(* tri 0 = 0 ∧ ∀n. tri (SUC n) = SUC n + tri n *)
Definition Tri_def:
  Tri = <|
          Q :={1;2;3;4;5;6;7};
          tf :=(λs. 
                  case s of 
                  | 1 => Dec 1 (SOME 2) NONE
                  | 2 => Inc 2 (SOME 3) 
                  | 3 => Dec 1 (SOME 4) (SOME 6)
                  | 4 => Inc 2 (SOME 5)
                  | 5 => Inc 3 (SOME 3)
                  | 6 => Dec 3 (SOME 7) (SOME 1)
                  | 7 => Inc 1 (SOME 6)
                );
          q0 := 1;
          In := [1];
          Out := 2;
|>
End

val tri = EVAL ``RUN Tri [10]``;


Theorem Tri_facts[simp] = generate_machine_rwts Tri_def

Theorem Tri_correct:
 rmcorr Tri 1 (λrs. rs = RS ∧ ∀k. k ∈ {2;3} ⇒ rs k = 0) NONE (λrs. rs 2 = tri (RS 1))
Proof 
  irule loop_correct >> simp[] >>
  qexists_tac `(λrs. rs 2 + tri (rs 1) = tri (RS 1) ∧ rs 3 = 0)` >>
  rw[] 
  >- fs[]
  >> irule rmcorr_inc >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_seq 
  >> map_every qexists_tac [`(λrs. rs 1 = 0 ∧ rs 2 + tri (rs 3) = tri (RS 1) ∧ rs 3 = N)`, `6`]
  >> rw[APPLY_UPDATE_THM]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac `(λrs. rs 1 + rs 2 + tri (rs 1 + rs 3) = tri (RS 1) ∧ rs 1 + rs 3 = N)` >> rw[APPLY_UPDATE_THM]
      >- fs[GSYM ADD1]
      >- fs[]
      >> irule rmcorr_inc >> simp[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> simp[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[]
      >> fs[]
      )
  >> irule loop_correct >> simp[] 
  >> qexists_tac `λrs. rs 2 + tri (rs 1 + rs 3) = tri (RS 1) ∧ rs 1 + rs 3 = N`
  >> rw[APPLY_UPDATE_THM]
  >- fs[]
  >- fs[]
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[APPLY_UPDATE_THM]
  >> rw[]
  >> fs[]
QED 

(*  ∀n. tri⁻¹ n = SND (invtri0 n 0) *)
Definition invTri_def:
  invTri = <|
      Q := {1;2;3;4;5;6;7;8};
      tf := (λs. case s of 
                     1 => Dec 1 (SOME 2) (SOME 7)
                  |  2 => Dec 2 (SOME 3) (SOME 4)
                  |  3 => Inc 3 (SOME 1)
                  |  4 => Dec 3 (SOME 5) (SOME 6)
                  |  5 => Inc 2 (SOME 4)
                  |  6 => Inc 2 (SOME 1)
                  |  7 => Dec 3 (SOME 8) NONE
                  |  8 => Inc 2 (SOME 7) 
                   );
      q0 := 1;
      In := [1];
      Out := 2;
    |>
End


Theorem invTri_facts[simp] = generate_machine_rwts invTri_def

Theorem invTri_correct:
  rmcorr invTri 1 (λrs. rs = RS ∧ ∀k. k ∈ {2;3} ⇒ rs k = 0) NONE (λrs. rs 2 = invtri (RS 1))
Proof 
  irule rmcorr_seq >> simp[] >>
  map_every qexists_tac [`λrs. (rs 3 + rs 2) = invtri (RS 1)`,`7`] >>
  rw[]
  (* LOOP *)
  >- (irule loop_correct >> simp[] >> 
      qexists_tac `λrs. SND (invtri0 (rs 1 + rs 3) (rs 2 + rs 3)) = invtri (RS 1)` >>
      rw[]
      >- rw[invtri_def]
      >- fs[Once invtri0_def]
      >> rw[APPLY_UPDATE_THM]
      (*     -> 4 (-> 5) -> 6
         2                    -> 1
                   -> 3              *)
      >> irule rmcorr_dec >> simp[]
      >> rw[APPLY_UPDATE_THM]
        (* 2    -> 4 (-> 5) -> 6 ->   1*)
      >- (irule rmcorr_seq >> simp[] >>
          map_every qexists_tac [`λrs. rs 3 = 0 ∧ rs 1 = N ∧
                 SND (invtri0 (rs 1 + rs 2 + 1) (rs 2)) = invtri (RS 1)` ,`6`] >>
          rw[]
            (* 4 -> 6 *)
          >- (irule loop_correct >> simp[] >>
               qexists_tac `λrs. rs 1 = N ∧ 
                  SND (invtri0 (rs 1 + rs 2 + rs 3 + 1) (rs 2 + rs 3)) = invtri (RS 1)` >> rw[]
               >- fs[Once invtri0_def]
               >- fs[Once invtri0_def]
               >> irule rmcorr_inc >> simp[]
               >> irule rmcorr_stay >> simp[] 
               >> rw[APPLY_UPDATE_THM]
               >> fs[])
            (* 6 -> 1 *)
          >> irule rmcorr_inc >> simp[]
          >> rw[APPLY_UPDATE_THM]
          >> irule rmcorr_stay >> simp[] 
          >> rw[]
          >> fs[]
          >> `invtri0 (rs 1 + rs 2) (rs 2 − 1) = invtri0 (rs 1) (rs 2)` by simp[Once invtri0_def]
          >> metis_tac[]
          )
        (* 2 -> 3 -> 1*)
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> simp[] 
      >> rw[]
      >> fs[]
      )
  (* RETURN r2+r3 *)
  >> irule loop_correct >> simp[]
  >> qexists_tac `λrs. rs 3 + rs 2 = tri⁻¹ (RS 1)`
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[] 
  >> rw[APPLY_UPDATE_THM]
QED 


(* 
Pair f g n = npair (f n) (g n) 

npair 0 0 = 0 (input register) 
npair 0 2 = 5 (input register) 
npair 0 1 = 2 (scratch register) 
*)
Definition Pair_def:
  Pair f g = 
        let 
            add1 = mrInst 1 simp_add;
            tri' = mrInst 2 Tri;
            add2 = mrInst 3 simp_add;
            f' = mrInst 4 f;
            g' = mrInst 5 g;

            dupn_f = dup 0 (HD f'.In) 2; 
            dupn_g = dup 0 (HD g'.In) 2;

            dup00_1 = dup f'.Out (HD add1.In) 2;
            dup01_1 = dup g'.Out (EL 1 add1.In) 2;
            dup01_3 = dup g'.Out (HD add2.In) 2;
            
            dup1_2 = dup add1.Out (HD tri'.In) 2;
            
            dup2_3 = dup tri'.Out (EL 1 add2.In) 2;

            mix = [dupn_f; dupn_g; f'; g'; dup00_1; dup01_1; dup01_3; add1; dup1_2; tri'; dup2_3; add2];
            mix' = MAPi msInst mix;
        in 
          link_all mix' with In := [0]
End



(* FST n = nfst n 
    FST.In = 0; 
    FST.Out = 16 (sub.Out) 

npair 0 0 = 0 (input register) 
npair 0 1 = 2 (scratch register) 
npair 4 1 = 16 (output register )
*)
Definition FST_def:
  FST = 
        let 
            tri' = mrInst 1 Tri;
            invtri' = mrInst 2 invTri;
            add = mrInst 3 simp_add;
            sub = mrInst 4 simp_sub;

            dup0_2 = dup 0 (HD invtri'.In) 2;
            dup0_4 = dup 0 (EL 1 sub.In) 2;
            
            dup2_3 = dup invtri'.Out (HD add.In) 2;
            dup2_1 = dup invtri'.Out (HD tri'.In) 2;
            
            dup1_3 = dup tri'.Out (EL 1 add.In) 2;

            dup3_4 = dup add.Out (HD sub.In) 2;

            mix = [dup0_2; dup0_4; invtri'; dup2_3; dup2_1; tri'; dup1_3; add; dup3_4; sub];
            mix' = MAPi msInst mix;
        in 
          link_all mix' with In := [0]
End


(* SND n = nsnd n *)
Definition SND_def:
  SND = 
        let 
            invtri' = mrInst 1 invTri;
            tri' = mrInst 2 Tri;
            sub = mrInst 3 simp_sub;

            dup0_1 = dup 0 (HD invtri'.In) 2;
            dup0_3 = dup 0 (HD sub.In) 2;
            
            dup1_2 = dup invtri'.Out (HD tri'.In) 2;
            
            dup2_3 = dup tri'.Out (EL 1 sub.In) 2;

            mix = [dup0_1; dup0_3; invtri'; dup1_2; tri'; dup2_3; sub];
            mix' = MAPi msInst mix;
        in 
          link_all mix' with In := [0]
End

(* TODO: Prove Pair, FST and SND *)

(*
Theorem SND_rmcorr:
∀N.
  rmcorr SND SND.q0 (λrs. rs 0 = N ∧ ∀k. k ≠ 0 ⇒ rs k = 0) NONE (λrs. rs SND.Out = nsnd N)
Proof 
  rw[SND_def, link_all_def, wfrm_def] >> rw[] >>
  irule link_correct_V >> rw[] >> rw[]
  >- (irule link_wfrm >> rw[] >> irule link_wfrm >> rw[] 
      >- (irule link_wfrm >> rw[] >> irule link_wfrm >> rw[] >> rw[wfrm_def, invTri_def, action_states_def])
      >>


     >> irule link_wfrm >> rw[]
      >> irule link_wfrm >> rw[])
  >- rw[link_wfrm, mrInst_wfrm, msInst_wfrm]
  >- rw[wfrm_def, simp_sub_def]

QED 
*)

val _ = export_theory ()

