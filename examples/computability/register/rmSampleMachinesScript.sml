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

val _ = new_theory "rmSampleMachines";

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

(*
   ----------------------------------
   -------- Simple Machines ---------
   ----------------------------------
*)

(* Returns the given constant by putting it in register 0 *)
Definition const_def:
  const n =
    if n = 0 then  <|
       Q := {1} ;
       tf := (λs. Inc 0 NONE);
       q0 := 1 ;
       In := [0] ;
       Out := 1 ;
    |>
    else
      if n = 1 then <|
         Q := {1} ;
         tf := (λn. case n of
                | 1 => Inc 1 NONE
              );
         q0 := 1 ;
         In := [0] ;
         Out := 1 ;
        |>
    else let m = const (n-1)
     in
      <|
         Q  := {n} ∪ m.Q ;
         tf := m.tf (| n |-> Inc 1 (SOME (n-1)) |) ;
         q0 := n ;
         In := [0] ;
         Out := 1 ;
      |>
End

(* Defined in rmToolsTheory *)
(*
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
*)

val identity'_def = Define `
  identity' = <|
  Q := {0;1};
  tf := (λs. case s of
                | 0 => Inc 0 (SOME 1)
                | 1 => Dec 0 NONE NONE
        );
  q0 := 0;
  In := [1;0;2];
  Out := 0;
  |>
`;

val identity2_def = Define `
  identity2 = <|
  Q := {10;11};
  tf := (λs. case s of
                | 10 => Inc 10 (SOME 11)
                | 11 => Dec 10 NONE NONE
        );
  q0 := 10;
  In := [10];
  Out := 10;
  |>
`;

val empty_def = Define `
  empty = <|
      Q := {1} ;
      tf := (λn. Dec 0 (SOME 1) NONE) ;
      q0 := 1 ;
      In := [0] ;
      Out := 0 ;
  |>
`;

val empty'_def = Define `
  empty' m = <|
      Q := {0} ;
      tf := (λn. Dec m (SOME 0) NONE) ;
      q0 := 0;
      In := [m] ;
      Out := m ;
  |>
`;

val transfer_def = Define `
  transfer = <|
      Q := {1;2} ;
      tf := (λn. case n of
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Inc 1 (SOME 1)
          ) ;
      q0 := 1 ;
      In := [0] ;
      Out := 1 ;
  |>
`;

val double_def = Define `
  double = <|
    Q := {1;2;3};
    tf := (λs. case s of
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Inc 1 (SOME 3)
            | 3 => Inc 1 (SOME 1)
            );
    q0 := 1;
    In := [0];
    Out := 1;
    |>
  `;



(*
   -------------------------------------------------------------
   -------- More Complicated machines and their proofs ---------
   -------------------------------------------------------------
*)


Definition simp_add_def:
  simp_add = <|
    Q := {1;2};
    tf := (λs. case s of
            | 1 => Dec 2 (SOME 2) NONE
            | 2 => Inc 1 (SOME 1)
            | otherwise => ARB
          );
    q0 := 1;
    In := [2; 1];
    Out := 1;
  |>
End


(* Substract 2 from 1 (stops at 0)*)
Definition simp_sub_def:
  simp_sub = <|
    Q := {1;2};
    tf := (λs. case s of
            | 1 => Dec 2 (SOME 2) NONE
            | 2 => Dec 1 (SOME 1) (SOME 1)
          );
    q0 := 1;
    In := [1;2];
    Out := 1;
  |>
End


Theorem simp_sub_facts[simp] = generate_machine_rwts simp_sub_def

(* To help assist proof for Pair et al *)
(*
Theorem simp_sub_correct_rmcorr:
∀RS.
  rmcorr simp_sub 1 (λrs. )
Proof
QED
*)

Theorem simp_add_facts[simp] = generate_machine_rwts simp_add_def

Theorem simp_add_correct_rmcorr:
∀RS.
  rmcorr simp_add 1 (λrs. rs = RS) NONE (λrs. ∀k. k ∉ {1;2} ⇒ rs k = RS k ∧ rs 2 = 0 ∧ rs 1 = RS 1 + RS 2)
Proof
  rw[] >>
  irule loop_correct >> simp[] >>
  qexists_tac `λrs.  ∀k. k ∉ {1;2} ⇒ rs k = RS k ∧ rs 2 + rs 1 = RS 1 + RS 2` >>
  rw[]
  >- (first_x_assum drule_all >> rw[])
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_inc >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_stay >> simp[]
  >> rw[]
  >> first_x_assum drule_all
  >> rw[]
QED

Theorem simp_add_correct:
  correct2 (+) simp_add
Proof
  rw[simp_add_def, correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = a + b` >>
  `∀rs0. FST (WHILE gd (r m) (rs0, SOME 1)) 1 = rs0 1 + rs0 2`
    suffices_by rw[Abbr`init`, findi_def] >>
  gen_tac >>
  rw[Abbr`r`, Abbr`m`, Abbr`gd`] >>
  Induct_on `rs0 2` >>
  rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM]
QED


val addition_def = Define `
  addition = <|
      Q := {1;2;3;4;5} ;
      tf := (λn. case n of
            | 1 => Dec 2 (SOME 2) (SOME 4)
            | 2 => Inc 1 (SOME 3)
            | 3 => Inc 3 (SOME 1)
            | 4 => Dec 3 (SOME 5) NONE
            | 5 => Inc 2 (SOME 4)
          ) ;
      q0 := 1 ;
      In := [1;2] ;
      Out := 1 ;
  |>
`;

Theorem addition_facts[simp] = generate_machine_rwts addition_def

Theorem addition_correct_rmcorr:
∀RS. RS 3 = 0 ⇒
  rmcorr addition 1 (λrs. rs = RS) NONE (λrs. rs 1 = RS 1 + RS 2 ∧ ∀k. k ≠ 1 ⇒ rs k = RS k)
Proof
  rw[] >>
  irule rmcorr_seq >> simp[] >>
  map_every qexists_tac [`λrs. ∀k. k ∉ {1;2;3} ⇒ rs k = RS k ∧ rs 1 = RS 1 + RS 2 ∧ rs 3 = RS 2 ∧ rs 2 = 0`,`4`] >>
  rw[]
  >- (irule loop_correct >> simp[] >>
      qexists_tac `λrs. ∀k. k ∉ {1;2;3} ⇒ rs k = RS k ∧ rs 1 + rs 2 = RS 1 + RS 2 ∧ rs 3 + rs 2 = RS 2` >>
      rw[]
      >- (first_x_assum drule_all >> rw[])
      >- (first_x_assum drule_all >> rw[])
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> first_x_assum drule_all >> rw[]
    )
  >> irule loop_correct >> simp[]
  >> qexists_tac `λrs. rs 1 = RS 1 + RS 2 ∧ rs 3 + rs 2 = RS 2 ∧ ∀k. k ∉ {1;2;3} ⇒ rs k = RS k`
  >> rw[APPLY_UPDATE_THM]
  >- (fs[] >> Cases_on `k = 2`
      >- rw[]
      >> Cases_on `k = 3`
      >> rw[])
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[]
  >> rw[APPLY_UPDATE_THM]
QED


Theorem addition_correct:
  correct2 (+) addition
Proof
  rw[addition_def, correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = a + b` >>
  `∀rs0. FST (WHILE gd (r m) (rs0, SOME 1)) 1 = rs0 1 + rs0 2`
    suffices_by rw[Abbr`init`, findi_def] >>
  gen_tac >>
  Induct_on `rs0 2`
    >- (`∀rs0. FST (WHILE gd (r m) (rs0, SOME 4)) 1 = rs0 1`
          suffices_by (rw[] >> rw[Once WHILE, Abbr`r`, Abbr`m`, run_machine_1_def])
        >> gen_tac
        >> Induct_on `rs0 3`
        >> rw[Abbr`gd`, Abbr`r`, Abbr`m`]
        >> rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM])
    >> rw[Abbr`r`, Abbr`m`, Abbr`gd`]
    >> rw[Ntimes WHILE 3, run_machine_1_def, APPLY_UPDATE_THM]
QED


val multiplication_def = Define `
   multiplication = <|
      Q := {1;2;3;4;5;6} ;
      tf := (λn. case n of
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Dec 1 (SOME 3) (SOME 5)
            | 3 => Inc 2 (SOME 4)
            | 4 => Inc 3 (SOME 2)
            | 5 => Dec 3 (SOME 6) (SOME 1)
            | 6 => Inc 1 (SOME 5)
           );
      q0 := 1 ;
      In := [0;1] ;
      Out := 2 ;
  |>
`;


Theorem multi_facts[simp] = generate_machine_rwts multiplication_def

Theorem multiplication_correct_rmcorr:
∀RS. (RS 2 = 0 ∧ RS 3 = 0) ⇒
  rmcorr multiplication 1 (λrs. rs = RS) NONE (λrs. rs 2 = RS 0 * RS 1 ∧ rs 0 = 0 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k)
Proof
  rw[] >>
  irule loop_correct >> simp[] >>
  qexists_tac `λrs. rs 0 * rs 1 + rs 2 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k` >>
  rw[]
  >- fs[]
  >> irule rmcorr_seq >> simp[APPLY_UPDATE_THM]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 0 * rs 3 + rs 2 = RS 0 * RS 1 ∧ rs 1 = 0 ∧ rs 3 = RS 1 ∧ ∀k. k ∉ {0;1;2;3} ⇒ rs k = RS k`,`5`]
  >> rw[]
  >- (irule loop_correct >> simp[] >>
      qexists_tac `λrs. rs 0 = N ∧ rs 1 + rs 3 = RS 1 ∧ rs 0 * RS 1 + rs 2 + rs 1 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;1;2;3} ⇒ rs k = RS k `
      >> rw[] >> fs[]
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> fs[])
  >> irule rmcorr_seq >> simp[]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 0 * RS 1 + rs 2 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k`, `1`]
  >> rw[]
  >- (irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 0 = N ∧ rs 1 + rs 3 = RS 1 ∧ rs 0 * RS 1 + rs 2 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;1;2;3} ⇒ rs k = RS k`
      >> rw[]
      >- fs[]
      >- (Cases_on `k = 1`
          >> fs[]
          >> Cases_on `k = 3`
          >> fs[])
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM]
      )
  >> irule rmcorr_stay >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> fs[]
QED


(* Old Multiplication Proof, up to the end of mult_correct *)
Theorem mult_loop1:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) (rs, SOME 2)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication)
    (rs (| 1 |-> 0;
           2 |-> rs 2 + rs 1;
           3 |-> rs 3 + rs 1 |)
     , SOME 5)
Proof
  Induct_on `rs 1` >> rw[]
    >- (rw[Once WHILE, run_machine_1_def, multiplication_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes WHILE 3, run_machine_1_def, multiplication_def] >>
      rw[APPLY_UPDATE_THM] >>
      `rs 1 = SUC v` by simp[] >> fs[] >>
      fs[multiplication_def, APPLY_UPDATE_THM] >>
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM]
QED

Theorem mult_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) (rs, SOME 5)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication)
    (rs (| 1 |-> rs 1 + rs 3;
           3 |-> 0 |)
     , SOME 1)
Proof
  Induct_on `rs 3` >> rw[]
    >- (rw[Once WHILE, run_machine_1_def, multiplication_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes WHILE 2, run_machine_1_def, multiplication_def] >>
      rw[APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >>
      fs[multiplication_def, APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, APPLY_UPDATE_THM]
QED



Theorem multi_correct:
  correct2 $* multiplication
Proof
  rw[correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a * b` >>
  `∀rs0. (rs0 3 = 0) ⇒ (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = rs0 0 * rs0 1 + rs0 2)`
    suffices_by rw[Abbr`init`, findi_def] >> rw[] >>
  Induct_on `rs0 0` >> rw[]
    >- (rw[multiplication_def, Ntimes WHILE 2, Abbr`gd`, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[])
    >> rw[Once WHILE, run_machine_1_def, Abbr`gd`, Abbr`r`, Abbr`m`, mult_loop1]
    >> rw[mult_loop2]
    >> rw[APPLY_UPDATE_THM] >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> fs[arithmeticTheory.ADD1]
QED


(* swapping r1 and r2 for multiplication part can make the machine faster *)
(* r1 ** r0 *)
Definition exponential_def:
  exponential  = <|
    Q := {1;2;3;4;5;6;7;8;9;10;11;12;13;14};
    tf := (λs. case s of
            | 14 => Inc 2 (SOME 1)
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Dec 1 (SOME 3) (SOME 9)
            | 3 => Inc 5 (SOME 4)
            | 4 => Dec 2 (SOME 5) (SOME 7)
            | 5 => Inc 3 (SOME 6)
            | 6 => Inc 4 (SOME 4)
            | 7 => Dec 4 (SOME 8) (SOME 2)
            | 8 => Inc 2 (SOME 7)
            | 9 => Dec 5 (SOME 10) (SOME 11)
            | 10 => Inc 1 (SOME 9)
            | 11 => Dec 2 (SOME 11) (SOME 12)
            | 12 => Dec 3 (SOME 13) (SOME 1)
            | 13 => Inc 2 (SOME 12)
            );
    q0 := 14;
    In := [1;0];
    Out := 2;
  |>
End

Theorem exp_facts[simp] = generate_machine_rwts exponential_def

Theorem exponential_correct_rmcorr:
∀RS. (RS 2 = 0 ∧ RS 3 = 0 ∧ RS 4 = 0 ∧ RS 5 = 0) ⇒
  rmcorr exponential 14 (λrs. rs = RS) NONE
      (λrs. rs 2 = RS 1 ** RS 0 ∧ rs 0 = 0 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k)
Proof
  rw[] >>
  irule rmcorr_inc >> simp[] >>
  irule loop_correct >> simp[] >>
  qexists_tac `λrs. rs 2 * (rs 1 ** rs 0) = RS 1 ** RS 0 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k` >>
  rw[APPLY_UPDATE_THM]
  >- (`rs 2 = 1` by fs[UPDATE_APPLY] >> rw[APPLY_UPDATE_THM])
  >- rw[APPLY_UPDATE_THM]
  >- fs[]
  >> irule rmcorr_seq >> simp[]
  >> map_every qexists_tac
   [`λrs. rs 0 = N ∧ rs 1 = 0 ∧ rs 5 = RS 1 ∧ rs 2 * (rs 5 ** (rs 0 + 1)) = RS 1 ** RS 0 ∧
        rs 3 = rs 2 * rs 5 ∧ ∀k. k ∉ {0;1;2;3;5} ⇒ rs k = RS k`,`9`]
  >> rw[]
  >- (irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 1 + rs 5 = RS 1 ∧ rs 0 = N ∧ rs 2 * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0
         ∧ rs 4 = 0 ∧ rs 3 + rs 1 * rs 2 = RS 1 * rs 2 ∧ ∀k. k ∉ {0;1;2;3;5} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_seq >> simp[]
      >> map_every qexists_tac [`λrs. rs 1 = N' ∧ rs 0 = N ∧
         rs 1 + rs 5 = RS 1 ∧ rs 4 * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0
         ∧ rs 2 = 0 ∧ rs 3 + rs 1 * rs 4 = RS 1 * rs 4 ∧ ∀k. k ∉ {0;1;2;3;4;5} ⇒ rs k = RS k`,`7`]
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- (irule loop_correct >> simp[]
          >> qexists_tac `λrs. rs 1 = N' ∧ rs 0 = N ∧
         rs 1 + rs 5 = RS 1 ∧ (rs 2 + rs 4) * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0
         ∧ (rs 2 + rs 3) + rs 1 * (rs 2 + rs 4) = RS 1 * (rs 2 + rs 4) ∧ ∀k. k ∉ {0;1;2;3;4;5} ⇒ rs k = RS k`
          >> rw[APPLY_UPDATE_THM] >> fs[]
          >> irule rmcorr_inc >> simp[]
          >> irule rmcorr_inc >> simp[]
          >> rw[APPLY_UPDATE_THM]
          >> irule rmcorr_stay >> simp[]
          >> rw[APPLY_UPDATE_THM] >> fs[])
      >> irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 1 = N' ∧ rs 0 = N ∧
         rs 1 + rs 5 = RS 1 ∧ (rs 2 + rs 4) * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0
         ∧ rs 3 + rs 1 * (rs 2 + rs 4) = RS 1 * (rs 2 + rs 4) ∧ ∀k. k ∉ {0;1;2;3;4;5} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- (Cases_on `k=4` >> fs[])
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM] >> fs[]
      )
  >> irule rmcorr_seq >> simp[]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 2 * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0 ∧
        rs 3 = rs 2 * RS 1 ∧ ∀k. k ∉ {0;2;3} ⇒ rs k = RS k`,`11`]
  >> rw[]
  >- (irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 0 = N ∧ (rs 5 + rs 1) = RS 1 ∧ rs 2 * ((rs 5 + rs 1) ** (rs 0 + 1)) = RS 1 ** RS 0 ∧
        rs 3 = rs 2 * (rs 5 + rs 1) ∧ ∀k. k ∉ {0;1;2;3;5} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- metis_tac[]
      >- metis_tac[]
      >- (Cases_on `k=1` >> fs[] >> Cases_on `k=5` >> fs[])
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >> metis_tac[])
  >> irule rmcorr_seq >> simp[]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 3 * (RS 1 ** rs 0) = RS 1 ** RS 0 ∧
        ∀k. k ∉ {0;3} ⇒ rs k = RS k`,`12`]
  >> rw[]
  >- (irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 0 = N ∧ rs 3 * (RS 1 ** rs 0) = RS 1 ** RS 0 ∧
        ∀k. k ∉ {0;2;3} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- (`rs 0 + 1 = SUC (rs 0)` by fs[]
          >> `rs 2 * (RS 1 ** (rs 0 + 1) )= rs 2 * (RS 1 ** (SUC (rs 0)))` by metis_tac[]
          >> `rs 2 * RS 1 ** SUC (rs 0) = rs 2 * RS 1 * RS 1 ** rs 0` by fs[EXP]
          >> `RS 1 * rs 2 * RS 1 ** rs 0 = rs 2 * RS 1 * RS 1 ** rs 0` by rw[MULT_COMM]
          >> metis_tac[])
      >- (Cases_on `k=2` >> fs[])
      >> irule rmcorr_stay >> simp[]
      )
  >> irule loop_correct >> simp[]
  >> qexists_tac `λrs. rs 0 = N ∧ (rs 3 + rs 2) * (RS 1 ** rs 0) = RS 1 ** RS 0 ∧
        ∀k. k ∉ {0;2;3} ⇒ rs k = RS k`
  >> rw[APPLY_UPDATE_THM] >> fs[]
  >- (Cases_on`k = 3` >> fs[])
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> fs[]
QED


(* Old Exponential Correct Proof, up to the end of exp_correct *)
Theorem exp_loop1_1:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 4)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential)
    (rs (| 2 |-> 0;
           3 |-> rs 3 + rs 2;
           4 |-> rs 4 + rs 2 |)
     , SOME 7)
Proof
  Induct_on `rs 2` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 2 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes whileTheory.WHILE 3, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 2 = SUC v` by simp[] >> fs[] >>
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >>
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop1_2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 7)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential)
    (rs (| 2 |-> rs 2 + rs 4;
           4 |-> 0 |)
     , SOME 2)
Proof
  Induct_on `rs 4` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 4 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 4 = SUC v` by simp[] >> fs[] >>
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop1:
  (rs 4 = 0) ⇒ (WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 2)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential)
    (rs (| 1 |-> 0;
           2 |-> rs 4 + rs 2;
           3 |-> rs 3 + rs 1 * rs 2;
           5 |-> rs 5 + rs 1 |)
     , SOME 9))
Proof
  Induct_on `rs 1` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def]
    >> rw[exp_loop1_1, combinTheory.APPLY_UPDATE_THM]
    >> rw[exp_loop1_2, combinTheory.APPLY_UPDATE_THM]
    >> `rs 1 = SUC v` by simp[] >> fs[]
    >> fs[exponential_def, combinTheory.APPLY_UPDATE_THM]
    >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)`
    >> `rs1 = rs2` suffices_by simp[] >> simp[Abbr `rs1`, Abbr`rs2`]
    >> fs[ADD1]
    >> `(rs 2 + v * rs 2) = rs 2 * (v + 1)` by simp[]
    >> simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    >> rw[]
    >> `0 = rs 4` by simp[]
QED


Theorem exp_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 9)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential)
    (rs (| 1 |-> rs 1 + rs 5;
           5 |-> 0 |)
     , SOME 11)
Proof
  Induct_on `rs 5` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 5 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 5 = SUC v` by simp[] >> fs[] >>
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop3:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 11)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential)
    (rs (| 2 |-> 0 |)
     , SOME 12)
Proof
  Induct_on `rs 2` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 2 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 2 = SUC v` by simp[] >> fs[] >>
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop4:
WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 12)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential)
    (rs (| 2 |-> rs 2 + rs 3;
           3 |-> 0 |)
     , SOME 1)
Proof
  Induct_on `rs 3` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >>
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_correct:
  ∀a b. RUN exponential [a;b] = a ** b
Proof
  rw[init_machine_def, run_machine_def, RUN_def, findi_def] >>
  rw[Once WHILE, run_machine_1_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a ** b` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 5 = 0)) ⇒
     (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = (rs0 1 ** rs0 0) * rs0 2)`
     suffices_by rw[Abbr`init`, APPLY_UPDATE_THM, findi_def] >> rw[] >>
  Induct_on `rs0 0`
    >- (rw[exponential_def, Ntimes whileTheory.WHILE 2, Abbr`gd`, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[])
    >> rw[]
    >> rw[Once whileTheory.WHILE, run_machine_1_def, Abbr`gd`, Abbr`r`, Abbr`m`]
    >> rw[APPLY_UPDATE_THM, exp_loop1]
    >> rw[APPLY_UPDATE_THM, exp_loop2]
    >> rw[APPLY_UPDATE_THM, exp_loop3]
    >> rw[APPLY_UPDATE_THM, exp_loop4]
    >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> rw[EXP]
QED


(* 0: input *)
Definition factorial_def:
  factorial = <|
    Q := {0;1;2;3;4;5;6;7;8;9;10};
    tf := (λn. case n of
            | 0 => Inc 1 (SOME 1)
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Inc 2 (SOME 3)
            | 3 => Dec 1 (SOME 4) (SOME 9)
            | 4 => Dec 2 (SOME 5) (SOME 7)
            | 5 => Inc 3 (SOME 6)
            | 6 => Inc 4 (SOME 4)
            | 7 => Dec 4 (SOME 8) (SOME 3)
            | 8 => Inc 2 (SOME 7)
            | 9 => Dec 3 (SOME 10) (SOME 1)
            | 10 => Inc 1 (SOME 9)
           );
      q0 := 0 ;
      In := [0] ;
      Out := 1 ;
      |>
End

Theorem fac_facts[simp]:
  (factorial.In = [0]) ∧
  (factorial.Out = 1) ∧
  (factorial.q0 = 0) ∧
  (factorial.Q = {0;1;2;3;4;5;6;7;8;9;10}) ∧
  (factorial.tf 0 = Inc 1 (SOME 1)) ∧
  (factorial.tf 1 = Dec 0 (SOME 2) NONE) ∧
  (factorial.tf 2 = Inc 2 (SOME 3)) ∧
  (factorial.tf 3 = Dec 1 (SOME 4) (SOME 9))
Proof
  simp[factorial_def]
QED

(* Old Factorial Proof, up to the end of fac_correct *)
Theorem fac_loop1_1:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 4)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial)
    (rs (| 2 |-> 0;
           3 |-> rs 3 + rs 2;
           4 |-> rs 4 + rs 2 |)
     , SOME 7)
Proof
  Induct_on `rs 2` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 2 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes whileTheory.WHILE 3, run_machine_1_def, factorial_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 2 = SUC v` by simp[] >> fs[] >>
      fs[factorial_def, combinTheory.APPLY_UPDATE_THM] >>
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem fac_loop1_2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 7)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial)
    (rs (| 2 |-> rs 2 + rs 4;
           4 |-> 0 |)
     , SOME 3)
Proof
  Induct_on `rs 4` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 4 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, factorial_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 4 = SUC v` by simp[] >> fs[] >>
      fs[factorial_def, combinTheory.APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED


Theorem fac_loop1:
  (rs 4 = 0) ⇒ (WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 3)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial)
    (rs (| 1 |-> 0;
           2 |-> rs 4 + rs 2;
           3 |-> rs 3 + rs 1 * rs 2|)
     , SOME 9))
Proof
  Induct_on `rs 1` >> rw[]
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[fac_loop1_1, combinTheory.APPLY_UPDATE_THM]
    >> rw[fac_loop1_2, combinTheory.APPLY_UPDATE_THM]
    >> `rs 1 = SUC v` by simp[] >> fs[]
    >> rw[factorial_def]
    >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)`
    >> `rs1 = rs2` suffices_by simp[] >> simp[Abbr `rs1`, Abbr`rs2`]
    >> fs[arithmeticTheory.ADD1]
    >> `(rs 2 + v * rs 2) = rs 2 * (v + 1)` by simp[]
    >> simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    >> rw[]
    >> `0 = rs 4` by simp[]
QED

Theorem fac_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 9)
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial)
    (rs (| 1 |-> rs 1 + rs 3;
           3 |-> 0 |)
     , SOME 1)
Proof
  Induct_on `rs 3` >> rw[]
    >- (rw[Once WHILE, run_machine_1_def, factorial_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >>
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes WHILE 2, run_machine_1_def, factorial_def] >>
      rw[APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >>
      fs[factorial_def, APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED


Theorem fac_correct:
  ∀a. RUN factorial [a] = FACT a
Proof
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  rw[Once WHILE, run_machine_1_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) (init, SOME 1)) 1 = _` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 1 = FACT (rs0 2))) ⇒
     (FST (WHILE gd (r m) (rs0 , SOME 1)) 1 = FACT (rs0 0 + rs0 2))`
     suffices_by rw[Abbr`init`, APPLY_UPDATE_THM, FACT] >>
  rw[] >>
  Induct_on `rs0 0` >> rw[Abbr`r`, Abbr`m`, Abbr`gd`]
    >- (rw[APPLY_UPDATE_THM, factorial_def, Ntimes whileTheory.WHILE 2, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[] >> rw[numeralTheory.numeral_fact]
        >>rw[Once WHILE, run_machine_1_def] >> rw[APPLY_UPDATE_THM])
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[APPLY_UPDATE_THM, fac_loop1]
    >> rw[APPLY_UPDATE_THM, fac_loop2]
    >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> qmatch_abbrev_tac `FST (WHILE _ _ (ss, SOME 1)) 1 = _`
    >> first_x_assum (qspec_then `ss` mp_tac)
    >> simp[Abbr`ss`, APPLY_UPDATE_THM]
    >> simp[GSYM ADD1, FACT]
    >> rw[APPLY_UPDATE_THM]
    >> rw[ADD1]
QED

val _ = export_theory ()
