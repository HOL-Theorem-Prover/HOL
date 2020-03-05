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

val _ = new_theory "rmTools";

val identity_def = Define `
  identity = <|
  Q := {0;1};
  tf := (λs. case s of 
                | 0 => Inc 1 (SOME 1)
                | 1 => Dec 1 NONE NONE
        );
  q0 := 0;
  In := [0];
  Out := 0;
  |>
`;

(* 
   ---------------------------------- 
   -----    Helper Functions    -----
   ----------------------------------
*)

val dup0_def = Define `
  dup0 r1 r2 r3= <| 
    Q := {1;2;3;4;5};
    tf := (λs. case s of 
            | 1 => Dec r1 (SOME 2) (SOME 4)
            | 2 => Inc r2 (SOME 3)
            | 3 => Inc r3 (SOME 1) 
            | 4 => Dec r3 (SOME 5) NONE
            | 5 => Inc r1 (SOME 4)
            );
    q0 := 1;
    In := [r1];
    Out := r2;
  |>
`;

Definition dup_def:
  dup r1 r2 r3= <| 
    Q := {0;1;2;3;4;5};
    tf := (λs. case s of 
            | 0 => Dec r2 (SOME 0) (SOME 1)
            | 1 => Dec r1 (SOME 2) (SOME 4)
            | 2 => Inc r2 (SOME 3)
            | 3 => Inc r3 (SOME 1) 
            | 4 => Dec r3 (SOME 5) NONE
            | 5 => Inc r1 (SOME 4)
            );
    q0 := 0;
    In := [r1];
    Out := r2;
  |>
End


val rInst_def = Define `
  (rInst mnum (Inc r sopt) = Inc (npair mnum r) sopt)
    ∧
  (rInst mnum (Dec r sopt1 sopt2) = Dec (npair mnum r) sopt1 sopt2)
`;

Definition mrInst_def:
  mrInst mnum m = <|
    Q := m.Q;
    tf := rInst mnum o m.tf ;
    q0 := m.q0;
    In := MAP (λr. npair mnum r) m.In;
    Out := npair mnum m.Out;
  |>
End


val sInst_def = Define `
  (sInst mnum (Inc r sopt) = Inc r (OPTION_MAP (npair mnum) sopt))
    ∧
  (sInst mnum (Dec r sopt1 sopt2) = 
      Dec r (OPTION_MAP (npair mnum) sopt1) (OPTION_MAP (npair mnum) sopt2))
`;

Definition msInst_def:
  msInst mnum m = <|
    Q := IMAGE (npair mnum) m.Q;
    tf := sInst mnum o m.tf o nsnd;
    q0 := npair mnum m.q0;
    In := m.In;
    Out := m.Out;
  |>
End

Definition upd_def[simp]:
  (upd NONE d = SOME d) 
    ∧
  (upd (SOME d0) d = SOME d0)
End

Definition end_link_def[simp]:
  (end_link (Inc q d0) d = Inc q (upd d0 d))
    ∧
  (end_link (Dec q d1 d2) d = Dec q (upd d1 d) (upd d2 d))
End


val linktf_def = Define`
  linktf m1Q tf1 tf2 m2init s = 
     if s ∈ m1Q then end_link (tf1 s) m2init
     else tf2 s
`;

Definition link_def:
  link m1 m2 = <|
    Q := m1.Q ∪ m2.Q;
    tf := linktf m1.Q m1.tf m2.tf m2.q0;
    q0 := m1.q0;
    In := m1.In;
    Out := m2.Out;
  |>
End

val _ = set_mapped_fixity {
  term_name = "link",
  tok = "⇨",
  fixity = Infixl 500
}


val link_all_def = Define`
  (link_all [] = identity) ∧     
  (link_all (m::ms) = FOLDL (λa mm. a ⇨ mm) m ms)
`;

(* 
   -----------------------------------------
   -----    Verification Techniques    -----
   -----------------------------------------
*)


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
  

Definition correct_def:
  correct m f a ⇔ ∀l. LENGTH l = a ⇒ RUN m l = f l
End

Definition run_step_def:
  run_step m rsq 0 = rsq ∧
  run_step m rsq (SUC n) = run_step m (run_machine_1 m rsq) n 
End

Theorem run_one_step:
  ∀m rsq n. run_machine_1 m (run_step m rsq n) = run_step m rsq (SUC n)
Proof 
  Induct_on `n` >> simp[run_step_def]
QED

Theorem combo_steps:
 ∀m rs q1 n1 n2.  run_step m (run_step m (rs, SOME q1) n1) n2
  = run_step m (rs, SOME q1) (n1+n2)
Proof 
  Induct_on `n2` 
  >- simp[run_step_def]
  >> rw[run_step_def, run_machine_def]
  >> `n1 + SUC n2 = SUC n1 + n2` by fs[]
  >> simp[]
  >> `run_step m (run_step m (rs,SOME q1) (SUC n1)) n2 =
       run_step m (rs,SOME q1) (SUC n1 + n2)` suffices_by rw[run_one_step]
  >> metis_tac[]
QED

Definition rmcorr_def:
  rmcorr M q P qf Q = 
    ∀rs. P rs ⇒ ∃n rs'. (run_step M (rs, SOME q) n = (rs', qf)) ∧ Q rs' 
End

Definition rm_ends_def:
  rm_ends m rs q = ∃n rs'. run_step m (rs, SOME q) n = (rs', NONE) 
End 

(*
Definition rm_ends_V_def:
  rm_ends_V M 
End
*) 

Definition correct1_def:
  correct1 f m ⇔ ∀a. RUN m [a] = f a 
End


Definition correct1_rmcorr_def:
  correct1_rmcorr f M ⇔  ∃min. M.In = [min] ∧ wfrm M ∧ 
      ∀inp. rmcorr M M.q0 (λrs. rs min = inp ∧ ∀k. k ≠ min ⇒ rs k = 0) NONE (λrs. rs M.Out = f inp)
End 

Definition correct2_def:
  correct2 f m ⇔ ∀a b. RUN m [a;b] = f a b
End


Theorem rmcorr_seq:
  rmcorr m q1 P (SOME q2) Q ∧ rmcorr m q2 Q q3 R ⇒ rmcorr m q1 P q3 R
Proof 
  rw[rmcorr_def] >> 
  last_x_assum (qspec_then `rs` assume_tac) >> rfs[] >>
  last_x_assum (qspec_then `rs'` assume_tac) >> rfs[] >>
  qexists_tac`n+n'` >>
  qexists_tac`rs''` >>
  `run_step m (rs,SOME q1) (n + n') =  run_step m (run_step m (rs,SOME q1) n) n' ` 
    by simp[combo_steps] >>
  `run_step m (run_step m (rs,SOME q1) n) n' = run_step m (rs', SOME q2) n' ` 
    by simp[] >>
  rw[]
QED


Theorem rmcorr_seq_V:
  (∀rs. Q rs ⇒ Q' rs) ∧ 
  rmcorr m q1 P (SOME q2) Q ∧ rmcorr m q2 Q' q3 R
⇒ rmcorr m q1 P q3 R
Proof 
  rw[rmcorr_def] >> 
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  map_every qexists_tac [`n+n'`,`rs''`] >>
  `run_step m (rs,SOME q1) (n + n') =  run_step m (run_step m (rs,SOME q1) n) n' ` 
    by simp[combo_steps] >> rw[]
QED

Theorem rmcorr_inc:
  m.tf q0 = Inc r (SOME d)
∧
  q0 ∈ m.Q
∧
  rmcorr m d (λrs. P (rs (| r |-> rs r - 1 |)) ∧ 0 < rs r) q Q
==> 
  rmcorr m q0 P q Q
Proof 
  rw[rmcorr_def] >>
  qabbrev_tac `rs' = rs⦇r ↦ rs r + 1⦈` >> 
  `rs'⦇r ↦ rs' r - 1⦈ = rs` by rw[APPLY_UPDATE_THM, Abbr`rs'`, FUN_EQ_THM] >>
  `P rs'⦇r ↦ rs' r - 1⦈` by fs[] >>
  `0 < rs' r ` by rw[APPLY_UPDATE_THM, Abbr`rs'`] >>
  first_x_assum drule_all >>
  strip_tac >> 
  map_every qexists_tac [`SUC n`, `rs''`] >>
  rw[run_step_def, run_machine_1_def]
QED 


Theorem rmcorr_stay:
(∀rs. P rs ⇒ Q rs) ⇒ rmcorr m q P (SOME q) Q
Proof 
  rw[rmcorr_def] >>
  map_every qexists_tac [`0`, `rs`] >>
  first_x_assum drule >>
  strip_tac >>
  rw[run_step_def]
QED

Theorem rmcorr_dec:
  m.tf q0 = Dec r (SOME t) (SOME e)
∧ 
  q0 ∈ m.Q
∧
  rmcorr m t (λrs. P (rs (|r |-> rs r + 1|))) q Q
∧
  rmcorr m e (λrs. P rs ∧ rs r = 0) q Q
==>
  rmcorr m q0 P q Q
Proof 
  rw[rmcorr_def] >> 
  Cases_on `0 < rs r` 
  >- (qabbrev_tac`rs' = rs (| r |-> rs r - 1|)` >> 
      `P rs' ⦇r ↦ rs' r + 1⦈ ` 
          by simp[Abbr`rs'`, APPLY_UPDATE_THM, UPDATE_EQ, APPLY_UPDATE_ID]
       >> last_x_assum drule >> strip_tac >> map_every qexists_tac [`SUC n`, `rs''`]
       >> rw[run_step_def, run_machine_1_def])
  >> `rs r = 0` by simp[] 
  >> first_x_assum drule_all
  >> strip_tac >> map_every qexists_tac [`SUC n`, `rs'`]
  >> rw[run_step_def, run_machine_1_def]
QED


Theorem rmcorr_weakening:
  (∀s. P s ⇒ P' s) ∧ (∀s. Q' s ⇒ Q s) ∧ (rmcorr m q0 P' q Q') 
==> rmcorr m q0 P q Q 
Proof 
  rw[rmcorr_def] >>
  `P' rs` by fs[] >>
  `∃n rs'. run_step m (rs,SOME q0) n = (rs',q) ∧ Q' rs'` by fs[] >>
  `Q rs'` by fs[] >>
  qexists_tac `n` >> 
  qexists_tac `rs'` >>
  rw[]
QED


Theorem loop_correct_0:
∀ m q INV gd body exit.
  (∀N. rmcorr m body (λrs. INV (rs(| gd |-> rs gd + 1|)) ∧ rs gd = N) (SOME q) (λrs'. INV rs' ∧ rs' gd <= N))
∧ (m.tf(q) = Dec gd (SOME body) exit) ∧ q ∈ m.Q

==> rmcorr m q INV exit (λrs. INV rs ∧ rs gd = 0)
Proof   
  rw[rmcorr_def] >>
  completeInduct_on `rs gd` >>
  rw[] >>
  fs[PULL_FORALL] >>
  Cases_on`0<rs gd` 
  >- (qabbrev_tac `rsx = rs⦇gd ↦ rs gd - 1⦈` >> 
     `run_machine_1 m (rs, SOME q) = (rsx, SOME body)` by simp[run_machine_1_def] >>
      first_x_assum (qspec_then `rsx` mp_tac) >>
      impl_tac 
      >- rw[Abbr `rsx`, APPLY_UPDATE_THM, APPLY_UPDATE_ID, UPDATE_EQ] 
      >> strip_tac >>
      `rs' gd < rs gd` by fs[Abbr`rsx`, APPLY_UPDATE_THM] >>
      first_x_assum drule_all >> rw[] >>
      map_every qexists_tac [`SUC (n + n')`, `rs''`] >>
      simp[run_step_def, GSYM combo_steps]
    )
  >> map_every qexists_tac [`SUC 0`, `rs`]
  >> rw[run_step_def]
  >> rw[run_machine_1_def]
QED


Theorem loop_correct:
∀ m q INV P Q gd body exit.
  (∀N. rmcorr m body (λrs. INV (rs(| gd |-> rs gd + 1|)) 
    ∧ rs gd = N) (SOME q) (λrs'. INV rs' ∧ rs' gd <= N))
∧ (∀rs. P rs ⇒ INV rs) 
∧ (∀rs. INV rs ∧ rs gd = 0 ⇒ Q rs)
∧ (m.tf(q) = Dec gd (SOME body) exit)
∧ q ∈ m.Q

==> rmcorr m q P exit Q
Proof   
  rw[] >>
  `rmcorr m q INV exit (λrs. INV rs ∧ rs gd = 0)` by rw[loop_correct_0] >>
  fs[rmcorr_def] >>
  rw[rmcorr_def] >>
  `INV rs` by fs[] >>
  `∃n rs'. run_step m (rs,SOME q) n = (rs',exit) ∧ INV rs' ∧ rs' gd = 0` by fs[] >>
  qexists_tac`n` >>
  qexists_tac`rs'` >>
  `Q rs'` by fs[] >>
  rw[]
QED


(*
------------------------------------------
----  Proofs for Helper/Glue Machines ----
------------------------------------------
*)


(* Proofs for smaller Machine (including helper machines *)
(* Helper machines (glue machines): dup, link, mrInst, msInst *)
Definition id_def:
  id a = a
End

Theorem identity_correct:
  correct1 id identity 
Proof
  rw[correct1_def, id_def, identity_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  rw[Once WHILE, run_machine_1_def] >> 
  rw[Once WHILE, run_machine_1_def] 
  >> rw[Once WHILE, run_machine_1_def] >> rw[APPLY_UPDATE_THM] 
QED


Theorem dup_facts[simp]:
  (dup r1 r2 r3).tf 0 = Dec r2 (SOME 0) (SOME 1) ∧
  (dup r1 r2 r3).tf 1 = Dec r1 (SOME 2) (SOME 4) ∧
  (dup r1 r2 r3).tf 2 = Inc r2 (SOME 3) ∧
  (dup r1 r2 r3).tf 3 = Inc r3 (SOME 1) ∧
  (dup r1 r2 r3).tf 4 = Dec r3 (SOME 5) NONE ∧
  (dup r1 r2 r3).tf 5 = Inc r1 (SOME 4) ∧
  (dup r1 r2 r3).Q = {0;1;2;3;4;5} ∧
  (dup r1 r2 r3).q0 = 0 ∧
  (dup r1 r2 r3).In = [r1] ∧
  (dup r1 r2 r3).Out = r2 
Proof
  rw[dup_def]
QED

(* TODO: use rmcorr_inc and dec instead of expanding run_step and rmcorr_def *)
Theorem dup_correct:
  ∀r1 r2 r3 RS. 
  r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧ RS r3 = 0
  ∧ P = (λrs. rs = RS) ∧ Q = (λrs'. rs' = RS (| r2 |-> RS r1 |) ) 
==>
  rmcorr (dup r1 r2 r3) 0 P NONE Q
Proof 
  rw[] >>
  irule rmcorr_seq >>
(* loop1 : clear r2 *)
  map_every qexists_tac [`λrs'. rs'= RS (| r2 |-> 0 |)`, `1`] >> rw[] 
  >- (irule loop_correct >> simp[] >> qexists_tac`(λrs. ∀k. k ≠ r2 ⇒ rs k = RS k)` 
      >> rw[] 
      >- (rw[APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[] >> rw[]) 
      >> rw[rmcorr_def] >> map_every qexists_tac [`0`, `rs`] 
      >> rw[] 
      >- rw[run_step_def]
      >> first_x_assum drule
      >> rw[APPLY_UPDATE_THM]
      )
  >> irule rmcorr_seq >>
(* loop2: transfer r1 into r2 and r3 *)
  map_every qexists_tac [`λrs'. rs'= RS (| r1 |-> 0 ; r2 |-> RS r1 ; r3 |-> RS r1|)`, `4`] >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac`(λrs. rs r1 + rs r2 = RS r1 ∧ rs r2 = rs r3 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k)` 
      >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >- (`rs r2 = RS r1` by simp[] >> rw[APPLY_UPDATE_THM, FUN_EQ_THM]
          >> rw[] >> rw[])
      >> rw[rmcorr_def]
      >> map_every qexists_tac [`SUC (SUC 0)`,`rs (| r2 |-> rs r2 + 1 ; r3 |-> rs r3 + 1 |)`]
      >> rw[run_step_def, run_machine_1_def, FUN_EQ_THM, APPLY_UPDATE_THM]
      )
(* loop3: transfer r3 back into r1 *)
  >> irule loop_correct >> simp[] >> 
  qexists_tac`(λrs. rs r1 + rs r3 = RS r1 ∧ rs r2 = RS r1 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k)` >> 
  rw[APPLY_UPDATE_THM] >>
  fs[] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] 
  >- (Cases_on `x = r1` 
      >- fs[]
      >> Cases_on `x = r2`
      >- fs[]
      >> Cases_on `x = r3`
      >- fs[] 
      >> rw[APPLY_UPDATE_ID, FUN_EQ_THM])
  >> rw[rmcorr_def] 
  >> map_every qexists_tac [`SUC 0`,`rs (| r1 |-> rs r1 + 1|)`]
  >> rw[run_step_def, run_machine_1_def, APPLY_UPDATE_THM, FUN_EQ_THM]
QED



Theorem dup_correct_2:
  ∀r1 r2 r3 RS. 
  r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧ P = (λrs. rs r3 = 0 ∧ rs r1 = N) ∧ Q = (λrs. rs r3 = 0 ∧ rs r1 = N ∧ rs r2 = N) 
==>
  rmcorr (dup r1 r2 r3) 0 P NONE Q
Proof 
  rw[] >>
  irule rmcorr_seq >>
(* loop1 : clear r2 *)
  map_every qexists_tac [`λrs. rs r2 = 0 ∧ rs r3 = 0 ∧ rs r1 = N`, `1`] >> rw[] 
  >- (irule loop_correct >> simp[] >> qexists_tac`(λrs. rs r3 = 0 ∧ rs r1 = N)` 
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[]
      )
  >> irule rmcorr_seq >>
(* loop2: transfer r1 into r2 and r3 *)
  map_every qexists_tac [`λrs. rs r1 = 0 ∧ rs r2 = N ∧ rs r3 = N`, `4`] >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac`(λrs. rs r1 + rs r2 = N ∧ rs r2 = rs r3)` 
      >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> rw[]
      >> irule rmcorr_inc >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[]
      )
(* loop3: transfer r3 back into r1 *)
  >> irule loop_correct >> simp[] >> 
  qexists_tac`λrs. rs r1 + rs r3 = N ∧ rs r2 = N` >> 
  rw[APPLY_UPDATE_THM] >>
  fs[] >>
  irule rmcorr_inc >> rw[] >>
  rw[APPLY_UPDATE_THM] >>
  irule rmcorr_stay >> rw[]
QED



Theorem dup_correct_V:
  ∀r1 r2 r3 RS. 
  RS r3 = 0 ∧ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧
  P = (λrs. rs = RS) ∧ Q = (λrs. ∀k. k ≠ r2 ⇒ rs k = RS k ∧ rs r2 = RS r1) 
==>
  rmcorr (dup r1 r2 r3) 0 P NONE Q
Proof 
  rw[] >>
  irule rmcorr_seq >>
(* loop1 : clear r2 *)
  map_every qexists_tac [`λrs. rs r2 = 0 ∧ ∀k. k ≠ r2 ⇒ rs k = RS k`, `1`] >> rw[] 
  >- (irule loop_correct >> simp[] >> qexists_tac`(λrs. ∀k. k ≠ r2 ⇒ rs k = RS k)` 
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[])
  >> irule rmcorr_seq >>
(* loop2: transfer r1 into r2 and r3 *)
  map_every qexists_tac [`λrs. rs r1 = 0 ∧ rs r2 = RS r1 ∧ rs r3 = RS r1 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k`, `4`] >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac`(λrs. rs r1 + rs r2 = RS r1 ∧ rs r2 = rs r3 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k)` 
      >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> rw[]
      >> irule rmcorr_inc >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[])
(* loop3: transfer r3 back into r1 *)
  >> irule loop_correct >> simp[] >> 
  qexists_tac`λrs. rs r1 + rs r3 = RS r1 ∧ rs r2 = RS r1 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k` >> 
  rw[APPLY_UPDATE_THM] >> fs[] 
  >- (Cases_on `k = r1` >> fs[] >> Cases_on `k = r3` >> fs[])
  >> irule rmcorr_inc >> rw[]
  >> rw[APPLY_UPDATE_THM] 
  >> irule rmcorr_stay >> rw[]
QED



Theorem dup_correct_INV:
  ∀r1 r2 r3 INV. 
    r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧
    P = (λrs. rs r3 = 0 ∧ rs r1 = N ∧ 
              INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r)) ∧ 
    Q = (λrs. rs r2 = N ∧ rs r1 = N ∧ rs r3 = 0 ∧ INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r)) 
  ==>
    rmcorr (dup r1 r2 r3) 0 P NONE Q
Proof 
  rw[] >>
  (*qabbrev_tac`RS = (λrs r. if r = r1 ∨ r = r2 ∨ r = r3 then 0 else rs r)` >>*)
  irule rmcorr_seq >>
(* loop1 : clear r2 *)
  map_every qexists_tac [`λrs. rs r2 = 0 ∧ rs r1 = N ∧ rs r3 = 0 ∧  INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r)`, `1`] >> rw[] 
  >- (irule loop_correct >> simp[] >> qexists_tac`(λrs. rs r1 = N ∧ rs r3 = 0 ∧  INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r))` 
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[])
  >> irule rmcorr_seq >>
(* loop2: transfer r1 into r2 and r3 *)
  map_every qexists_tac [`λrs. rs r1 = 0 ∧ rs r2 = N ∧ rs r3 = N ∧  INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r)`, `4`] >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac`(λrs. rs r1 + rs r2 = N ∧ rs r2 = rs r3 ∧  INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r))` 
      >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> rw[]
      >> irule rmcorr_inc >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[])
(* loop3: transfer r3 back into r1 *)
  >> irule loop_correct >> simp[] >> 
  qexists_tac`λrs. rs r1 + rs r3 = N ∧ rs r2 = N ∧ INV (λr. if r ∈ {r1; r2; r3} then 0 else rs r)` >> 
  rw[APPLY_UPDATE_THM] >> fs[] 
  >> irule rmcorr_inc >> rw[]
  >> rw[APPLY_UPDATE_THM] 
  >> irule rmcorr_stay >> rw[]
QED 


Theorem link_Q[simp]:
  (link m1 m2).Q = m1.Q ∪ m2.Q
Proof 
  rw[link_def]
QED 

Theorem link_tf:
  (link m1 m2).tf s = if s ∈ m1.Q then end_link (m1.tf s) m2.q0 else m2.tf s
Proof 
  rw[link_def, linktf_def]
QED 

Theorem run_machine_1_NONE[simp]:
  run_machine_1 m (rs, NONE) = (rs, NONE)
Proof 
  rw[run_machine_1_def]
QED 

Theorem run_step_NONE[simp]:
  run_step m (rs, NONE) n = (rs, NONE)
Proof 
  Induct_on `n` >> 
  rw[run_step_def] 
QED

Theorem regOf_end_link[simp]:
  regOf (end_link ins s) = regOf ins
Proof 
  Cases_on`ins` >> simp[end_link_def]
QED


Theorem  inst_Val_end_link[simp]:
  inst_Val (end_link ins s) v = inst_Val ins v
Proof 
  Cases_on`ins` >> simp[end_link_def]
QED

Theorem inst_Dest_end_link[simp]:
  inst_Dest (end_link ins d) v = 
    case inst_Dest ins v of 
        SOME d' => SOME d'
      | NONE => SOME d
Proof 
  Cases_on`ins` >> rw[end_link_def] >> rename [`upd opt d`] >> 
  Cases_on`opt` >> simp[upd_def]
QED 

Theorem inst_Dest_wf:
  wfrm m ∧ q ∈ m.Q ∧ inst_Dest (m.tf q) v = SOME q' ⇒ q' ∈ m.Q
Proof 
  Cases_on`m.tf q` >> rw[wfrm_def] >> first_x_assum drule 
  >> simp[action_states_def, opt_to_set_def]
QED



Theorem link_run_step_m1ToSOME:
  ∀q m m' rs rs'. 
  wfrm m ∧ wfrm m' ∧ DISJOINT m.Q m'.Q ∧ q ∈ m.Q ⇒
  (run_step m (rs, SOME q) n = (rs', SOME p) ⇒ run_step (link m m') (rs, SOME q) n = (rs', SOME p))
Proof 
  Induct_on `n` 
  (* 0 step *)
  >> rw[run_step_def] 
  (* k, suc k *)
  (* SOME to SOME *)
  >> fs[run_machine_1_alt] >> rw[link_tf] >> rfs[] >> 
  Cases_on `inst_Dest (m.tf q) (rs (regOf (m.tf q)))` >> fs[]
  >> first_x_assum irule >> simp[] 
  >> metis_tac[inst_Dest_wf]
QED


Theorem link_run_step_m1_ToNONE:
 ∀q m m' rs rs'. 
  wfrm m ∧ wfrm m' ∧ DISJOINT m.Q m'.Q ∧ q ∈ m.Q ⇒
  (run_step m (rs, SOME q) n = (rs', NONE) ⇒ ∃n'. n' ≤ n ∧ run_step (link m m') (rs, SOME q) n' = (rs', SOME m'.q0))
Proof 
  Induct_on `n` 
  (* 0 step *)
  >> rw[run_step_def] 
  (* SOME to NONE*)
  >> fs[run_machine_1_alt] >> rw[link_tf] >> rfs[]
  >> Cases_on `inst_Dest (m.tf q) (rs (regOf (m.tf q)))` >> fs[] 
  (* To NONE *)
  >- (qexists_tac`SUC 0` >> rw[run_step_def] >> rw[run_machine_1_alt] >>
      rw[APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[link_tf])
  (* To SOME *)
  >> `∃n'. n' ≤ n ∧ run_step (m ⇨ m') (rs,SOME q) (SUC n') = (rs',SOME m'.q0)`
         suffices_by (rw[] >> qexists_tac`SUC n'` >> rw[])
  >> rw[run_step_def] 
  >> rw[run_machine_1_alt, link_tf]
  >> rename [`SOME q`, `q' ∈ m.Q`]
  >> qabbrev_tac `rs0 = rs⦇regOf (m.tf q') ↦ inst_Val (m.tf q') (rs (regOf (m.tf q')))⦈`
  >> first_x_assum irule >> simp[] 
  >> metis_tac[inst_Dest_wf]
QED 



Theorem link_run_step_m2:
  ∀q m m' rs rs'. 
  wfrm m ∧ wfrm m' ∧ DISJOINT m.Q m'.Q ∧ q ∈ m'.Q ⇒
  (run_step m' (rs, SOME q) n = (rs', opt) ⇒ run_step (link m m') (rs, SOME q) n = (rs', opt))
Proof 
  Induct_on `n` 
  (* 0 step *)
  >> rw[run_step_def] 
  (* k, suc k *)
  >> fs[run_machine_1_alt] >> rw[link_tf] >> fs[] 
  (* q in m.Q and q in m'.Q *)
  >- (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[])
  (* q not in m.Q and q in m'.Q *)
  >> rfs[]
  >> qabbrev_tac `rs0 = rs⦇regOf (m'.tf q) ↦ inst_Val (m'.tf q) (rs (regOf (m'.tf q)))⦈`
  >> Cases_on `inst_Dest (m'.tf q) (rs (regOf (m'.tf q)))` >> fs[]   (* q0 = NONE *)
  (* q0 = SOME _ *)
  >> first_x_assum irule >> simp[]
  >> metis_tac[inst_Dest_wf]
QED


Theorem link_m1end:
  q0 ∈ m.Q ∧ wfrm m' ∧ wfrm m ∧ DISJOINT m.Q m'.Q ∧ rmcorr m q0 P NONE Q ⇒ rmcorr (link m m') q0 P (SOME m'.q0) Q
Proof 
  rw[rmcorr_def] >> metis_tac[link_run_step_m1_ToNONE]
QED 

Theorem link_m2end:
  q0 ∈ m'.Q ∧ wfrm m' ∧ wfrm m ∧ DISJOINT m.Q m'.Q ∧ rmcorr m' q0 P opt Q ⇒ rmcorr (link m m') q0 P opt Q
Proof 
  rw[rmcorr_def] >> metis_tac[link_run_step_m2]
QED 


Theorem link_correct:
  wfrm m1 ∧ wfrm m2 ∧ DISJOINT m1.Q m2.Q ∧ rmcorr m1 m1.q0 P NONE Q ∧ rmcorr m2 m2.q0 Q opt R ∧ q = m1.q0
⇒ rmcorr (link m1 m2) q P opt R
Proof
  rw[] >>
  irule rmcorr_seq >>
  map_every qexists_tac [`Q`,`m2.q0`] >>
  rw[] 
  >- metis_tac[link_m1end, wfrm_def]
  >> metis_tac[link_m2end, wfrm_def]
QED

Theorem link_correct_V:
  wfrm m1 ∧ wfrm m2 ∧ DISJOINT m1.Q m2.Q ∧ q = m1.q0 ∧
  rmcorr m1 m1.q0 P NONE Q ∧ rmcorr m2 m2.q0 Q' opt R ∧ (∀rs. Q rs ⇒ Q' rs)
⇒ rmcorr (link m1 m2) q P opt R
Proof
  rw[] >>
  irule rmcorr_seq_V >>
  map_every qexists_tac [`Q`,`Q'`, `m2.q0`] >>
  rw[] 
  >- metis_tac[link_m1end, wfrm_def]
  >> metis_tac[link_m2end, wfrm_def]
QED

Theorem mrInst_prop[simp]:
 (s ∈ M.Q ⇒ (mrInst n M).tf s = (rInst n (M.tf s))) ∧
   (mrInst n M).Q = M.Q
Proof 
  rw[mrInst_def]
QED

Definition rs_mrInst_B4_def:
  rs_mrInst_B4 rsm rs mnum = (∀q. (rsm (mnum *, q) = rs q))
End 

Definition rs_mrInst_Aft_def:
  rs_mrInst_Aft rsm' rsm rs' mnum = 
  ((∀q. rsm' (mnum*, q)= rs' q) ∧ (∀r. nfst r ≠ mnum ⇒ (rsm' r = rsm r)))
End 


Theorem inst_Dest_rInst[simp]:
  inst_Dest (rInst mnum opt) v = inst_Dest opt v
Proof 
  Cases_on `opt` 
  >> metis_tac[inst_Dest_def, rInst_def]
QED 

Theorem regOf_rInst[simp]:
  regOf (rInst mnum opt) = npair mnum (regOf opt)
Proof 
  Cases_on `opt` >> 
  rw[regOf_def, rInst_def]
QED 

Theorem inst_Val_rInst[simp]:
  inst_Val (rInst mnum opt) v = inst_Val opt v
Proof 
  Cases_on `opt` >> metis_tac[inst_Val_def, rInst_def]
QED 

Theorem mrInst_run_step:
  ∀q n rs rs' M mnum rsm rsm'. 
  wfrm M ∧ q ∈ M.Q ∧ rs_mrInst_B4 rsm rs mnum ∧ rs_mrInst_Aft rsm' rsm rs' mnum ⇒
  (run_step M (rs, SOME q) n = (rs', opt) ⇒ 
  run_step (mrInst mnum M) (rsm, SOME q) n = (rsm', opt))
Proof 
  Induct_on`n` >>
  (* 0 Case *)
  rw[run_step_def] >>
  (* Inductive Case *)
  fs[run_machine_1_alt, rs_mrInst_B4_def, rs_mrInst_Aft_def] 
  >- (rw[FUN_EQ_THM] >> metis_tac[numpairTheory.npair_cases, numpairTheory.nfst_npair]) 
  >> rfs[]
  >> Cases_on `inst_Dest (M.tf q) (rs (regOf (M.tf q)))` 
  (* NONE *)
  >- (fs[] >> rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] 
        >- rw[APPLY_UPDATE_THM] (*>> *)
        >> Cases_on `nfst x ≠ mnum` 
        >- simp[]
        >> rw[] 
        >> metis_tac[APPLY_UPDATE_THM, npair])
  (* SOME *)
  >> first_x_assum irule 
  >> rw[]
  >- (rw[APPLY_UPDATE_THM] >> metis_tac[nfst_npair])
  >- (map_every qexists_tac [`rs⦇regOf (M.tf q) ↦ inst_Val (M.tf q) (rs (regOf (M.tf q)))⦈`, `rs'`] >>
      rw[APPLY_UPDATE_THM])
  >> metis_tac[inst_Dest_wf]
QED

Definition liftP_def:
  liftP n P = (λrs. P (λr. rs (npair n r)))
End 

(* rmcorr M q P opt Q ==> rmcorr (mrInst n M) q (λrs. (P (λr. rs (nsnd r))) ∧ (λr. nfst r = mnum)) opt (λrs. Q (λr. rs (nsnd r)))*)
Theorem mrInst_correct:
 (wfrm M ∧ q ∈ M.Q ∧ P' = liftP n P ∧ Q' = liftP n Q) ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst n M) q P' opt Q')
Proof
  rw[liftP_def, rmcorr_def] >>
  rename [`P (λr. rsm (mnum ⊗ r))`] >>
  `∃n rs'. run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt) ∧ Q rs'` by rfs[] >>
  `rs_mrInst_B4 rsm (λr. rsm (mnum ⊗ r)) mnum` by rw[rs_mrInst_B4_def] >>
  rename [`run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt)`] >>
  qexists_tac `n` >> 
  drule mrInst_run_step >>
  rw[] >>
  qexists_tac `(λr. if nfst r = mnum then rs' (nsnd r) else rsm r)` >>
  `rs_mrInst_Aft (λr. if nfst r = mnum then rs' (nsnd r) else rsm r) rsm rs' mnum` 
    by rw[rs_mrInst_Aft_def] >>
  rw[] 
  >- metis_tac[]
  >> `rs' = (λr. rs' r)` by metis_tac[FUN_EQ_THM]
  >> metis_tac[]
QED

Definition liftP_V_def:
  liftP_V n P X = (λrs. P (λr. rs (n ⊗ r)) ∧ X rs)
End


Theorem mrInst_correct_kV:
 ∀RS M q P Q opt mnum P' Q'. (wfrm M ∧ q ∈ M.Q ∧ P' = liftP_V mnum P (λrs. ∀k. nfst k ≠ mnum ⇒ rs k = RS k) 
       ∧ Q' = liftP_V mnum Q (λrs. ∀k. nfst k ≠ mnum ⇒ rs k = RS k))
  ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst mnum M) q P' opt Q')
Proof
  rw[liftP_V_def, rmcorr_def] >>
  first_x_assum drule >> rw[] >>
  map_every qexists_tac[`n`,`λr. if nfst r = mnum then rs' (nsnd r) else RS r`] >>
  rw[]
  >- (drule mrInst_run_step >> rw[]
      >> first_x_assum irule >> rw[]
      >> qexists_tac `λr. rs (mnum ⊗ r)`
      >> qexists_tac `rs'` >> rw[]
      >- rw[rs_mrInst_B4_def]
      >> rw[rs_mrInst_Aft_def])
  >> metis_tac[]
QED

(* rmcorr M q P opt Q ==> rmcorr (mrInst n M) q (λrs. (P (λr. rs (nsnd r))) ∧ (λr. nfst r = mnum)) opt (λrs. Q (λr. rs (nsnd r)))*)
Theorem mrInst_correct_V:
 ∀RS. (wfrm M ∧ q ∈ M.Q ∧ P' = liftP_V n P (λrs. rs = RS) 
       ∧ Q' = liftP_V n Q (λrs. ∀k. nfst k ≠ n ⇒ rs k = RS k))
  ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst n M) q P' opt Q')
Proof
  rw[liftP_V_def, rmcorr_def] >>
  rename [`P (λr. rsm (mnum ⊗ r))`] >>
  `∃n rs'. run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt) ∧ Q rs'` by rfs[] >>
  `rs_mrInst_B4 rsm (λr. rsm (mnum ⊗ r)) mnum` by rw[rs_mrInst_B4_def] >>
  rename [`run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt)`] >>
  qexists_tac `n` >> 
  drule mrInst_run_step >>
  rw[] >>
  qexists_tac `(λr. if nfst r = mnum then rs' (nsnd r) else rsm r)` >>
  `rs_mrInst_Aft (λr. if nfst r = mnum then rs' (nsnd r) else rsm r) rsm rs' mnum` 
    by rw[rs_mrInst_Aft_def] >>
  rw[] 
  >- metis_tac[]
  >> `rs' = (λr. rs' r)` by metis_tac[FUN_EQ_THM]
  >> metis_tac[]
QED

Theorem mrInst_correct_kN:
  nfst k ≠ n ∧
  (wfrm M ∧ q ∈ M.Q ∧ P' = liftP_V n P (λrs. rs k = N) ∧ Q' = liftP_V n Q (λrs. rs k = N))
  ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst n M) q P' opt Q')
Proof
  rw[liftP_V_def, rmcorr_def] >>
  rename [`P (λr. rsm (mnum ⊗ r))`] >>
  `∃n rs'. run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt) ∧ Q rs'` by rfs[] >>
  `rs_mrInst_B4 rsm (λr. rsm (mnum ⊗ r)) mnum` by rw[rs_mrInst_B4_def] >>
  rename [`run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt)`] >>
  qexists_tac `n` >> 
  drule mrInst_run_step >>
  rw[] >>
  qexists_tac `(λr. if nfst r = mnum then rs' (nsnd r) else rsm r)` >>
  `rs_mrInst_Aft (λr. if nfst r = mnum then rs' (nsnd r) else rsm r) rsm rs' mnum` 
    by rw[rs_mrInst_Aft_def] >>
  rw[] 
  >- metis_tac[]
  >> `rs' = (λr. rs' r)` by metis_tac[FUN_EQ_THM]
  >> metis_tac[]
QED

Definition npair_opt_def:
  npair_opt mnum NONE = NONE ∧
  npair_opt mnum (SOME q) = SOME (npair mnum q)
End 

Theorem regOf_msInst[simp]:
  regOf ((msInst mnum M).tf (mnum ⊗ q)) = regOf (M.tf q)
Proof
  rw[msInst_def] >>
  Cases_on `M.tf q` >>
  metis_tac[regOf_def, sInst_def]
QED 

Theorem inst_Val_msInst[simp]:
  inst_Val ((msInst mnum M).tf (mnum ⊗ q)) v = inst_Val (M.tf q) v
Proof 
  rw[msInst_def] >>
  Cases_on `M.tf q` >>
  metis_tac[inst_Val_def, sInst_def]
QED 

Theorem inst_Dest_msInst[simp]:
  inst_Dest ((msInst mnum M).tf (mnum ⊗ q)) v = npair_opt mnum (inst_Dest (M.tf q) v)
Proof 
  rw[msInst_def] >> 
  Cases_on `M.tf q` >> rw[inst_Dest_def, sInst_def, npair_opt_def] >> fs[]
  >> rename [`npair_opt mnum opt`]
  >> Cases_on `opt` >>  fs[] >>  metis_tac[npair_opt_def]
QED

Theorem msInst_run_step:
  ∀q n rs rs' M mnum. 
  wfrm M ∧ q ∈ M.Q  ⇒
  (run_step M (rs, SOME q) n = (rs', opt) ⇒ 
  run_step (msInst mnum M) (rs, SOME (npair mnum q)) n = (rs', npair_opt mnum opt))
Proof 
  Induct_on `n` >> rw[npair_opt_def, run_step_def, run_machine_1_alt]
  (* 0 Case *)
  >- metis_tac[npair_opt_def]
  (* Inductive Case *)
  >- fs[msInst_def]  (* (mnum, q) not in new machine's Q (False) *)
  >- fs[msInst_def] 
  >> Cases_on `inst_Dest (M.tf q) (rs (regOf (M.tf q)))`
  (* From NONE *)
  >- (fs[run_step_def] >> rw[msInst_def, npair_opt_def])
  (* From SOME *)
  >> rw[npair_opt_def] 
  >> first_x_assum irule 
  >> rw[]
  >> metis_tac[inst_Dest_wf]
QED 


Theorem msInst_correct: 
∀mnum M q P opt Q.
  (wfrm M ∧ q ∈ M.Q) ⇒ 
  (rmcorr M q P opt Q ⇒ rmcorr (msInst mnum M) (npair mnum q) P (npair_opt mnum opt) Q) 
Proof 
  metis_tac[rmcorr_def, msInst_run_step]
QED 

Theorem msInst_correct_2: 
  wfrm M ∧ q ∈ M.Q ∧ 
  rmcorr M q P opt Q ∧
    q' = npair mnum q ∧
    opt' = npair_opt mnum opt
    ⇒ rmcorr (msInst mnum M) q' P opt' Q
Proof 
  metis_tac[msInst_correct]
QED 


Theorem rInst_states[simp]:
  action_states (rInst mnum act) = action_states act
Proof 
  Cases_on `act` >>
  rw[rInst_def, action_states_def]
QED 

Theorem mrInst_wfrm[simp]:
∀mnum f.  wfrm (mrInst mnum f) ⇔  wfrm f
Proof 
  rw[wfrm_def, mrInst_def]
QED

Theorem opt_to_set_OPTION_MAP[simp]:
   opt_to_set (OPTION_MAP f stop) = {f x| x ∈ opt_to_set stop}
Proof 
  Cases_on `stop` >> 
  rw[EXTENSION, optionTheory.OPTION_MAP_DEF, opt_to_set_def] 
QED 

Theorem sInst_states[simp]:
  action_states (sInst mnum act) = {npair mnum x | x ∈ action_states act}
Proof 
  Cases_on `act` >> 
  rw[sInst_def, action_states_def, EXTENSION] >>
  metis_tac[]
QED 

Theorem msInst_wfrm[simp]:
∀mnum f.  wfrm (msInst mnum f) ⇔  wfrm f
Proof 
  rw[wfrm_def, msInst_def, PULL_EXISTS] >>
  rw[pred_setTheory.SUBSET_DEF] >>
  rw[PULL_EXISTS] 
QED

Theorem mrInst_Q[simp]:
  (mrInst mnum f).Q = f.Q ∧ (mrInst mnum f).q0 = f.q0
Proof 
  rw[mrInst_def]
QED 

Theorem msInst_Q[simp]:
  (msInst mnum f).Q = {npair mnum x | x ∈ f.Q} ∧ (msInst mnum f).q0 = npair mnum f.q0
Proof 
  rw[msInst_def, EXTENSION]
QED

Theorem msInst_In[simp]:
  (msInst mnum f).In = f.In 
Proof 
  rw[msInst_def]
QED 

Theorem mrInst_In[simp]:
  (mrInst mnum f).In = MAP (λr. npair mnum r) f.In
Proof 
  rw[mrInst_def]
QED

Theorem msInst_mrInst_In[simp]:
 (msInst mnum' (mrInst mnum f)).In = MAP (λr. npair mnum r) f.In
Proof 
  rw[]
QED

Theorem msInst_Out[simp]:
  (msInst mnum f).Out = f.Out
Proof 
  rw[msInst_def]
QED 

Theorem mrInst_Out[simp]:
  (mrInst mnum f).Out = npair mnum f.Out
Proof 
  rw[mrInst_def]
QED

Theorem msInst_with_In[simp]:
  msInst mnum m with In := x = msInst mnum (m with In := x)
Proof 
  rw[msInst_def]
QED 


Theorem link_facts[simp]:
  (link m1 m2).q0 = m1.q0 ∧
  (link m1 m2).Out = m2.Out
Proof 
  rw[link_def]
QED 


Theorem dup_wfrm[simp]:
 ∀r1 r2 r3. wfrm (dup r1 r2 r3)
Proof 
  rw[dup_def, wfrm_def, action_states_def, opt_to_set_def] >>
  rw[dup_def, wfrm_def, action_states_def, opt_to_set_def]
QED


Theorem link_with_In[simp]:
∀a b lst. link a b with In := lst = link (a with In := lst) b 
Proof  
  rw[link_def] 
QED 

Theorem link_In[simp]:
∀a b. (link a b).In = a.In
Proof 
  rw[link_def]
QED

Theorem link_wfrm[simp]:
  wfrm m1 ∧ wfrm m2 ⇒ wfrm (link m1 m2) 
Proof 
  rw[wfrm_def, link_def, linktf_def] >> simp[]
  >- (Cases_on`m1.tf s` >> rw[end_link_def] 
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[])
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[]) 
        >> Cases_on`o0` >> rw[] >> last_x_assum drule >> rw[])
  >> Cases_on`s ∈ m1.Q` >> rw[]
  >- (Cases_on`m1.tf s` >> rw[end_link_def] 
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[])
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[]) 
        >> Cases_on`o0` >> rw[] >> last_x_assum drule >> rw[])
  >> metis_tac[SUBSET_DEF, IN_UNION]
QED 

Theorem wfrm_In[simp]:
∀x m.  wfrm (m with In := x) = wfrm m 
Proof 
  rw[wfrm_def]
QED 

Theorem with_In[simp]:
∀m.  (m with In := m.In) = m 
Proof 
 simp[rm_component_equality]
QED 

val _ = export_theory ()