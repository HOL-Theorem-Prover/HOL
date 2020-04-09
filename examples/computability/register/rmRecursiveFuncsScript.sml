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
open rmToPairTheory;

val _ = new_theory "rmRecursiveFuncs";
(*
   ----------------------------------
   ------      Projection      ------
   ----------------------------------
   *)

(* Returns the n-th element of the list ns, indexing from 0 *)
(* Not useful for unary recursive functions *)

Definition Pi_def:
  Pi n ns = <|
      Q := {0;1};
      tf := (λs. case s of
                | 0 => Inc 0 (SOME 1)
                | 1 => Dec 0 NONE NONE
        );
      q0 := 0;
      In := GENLIST I ns;
      Out := n;
    |>
End

 (*
   --------------------------------------
   ------------ Composition  ------------
   --------------------------------------
   *)


(* Cn f g = f o g *)

Definition Cn_def:
  Cn f g =
      let f' = mrInst 1 f;
          g' = mrInst 2 g;
          d1 = dup g'.Out (HD f'.In) (npair 0 1);
          mix = [g'; d1; f'];
          mix' = MAPi msInst mix;
      in
        link_all mix' with In := g'.In
End


val Old_Cn_def = Define `
  Old_Cn m ms =
    let isz = LENGTH (HD ms).In;
        mms = MAPi (λi mm. mrInst (i+2) mm) (m::ms);
        m'  = HD mms;
        ms' = TL mms;
        ics = FLAT (MAP (λmm. MAPi (λi r. dup (npair 0 i) r (npair 1 0)) mm.In) ms');
        ocs = MAPi (λi mm. dup mm.Out (EL i m'.In) (npair 1 0)) ms';
        mix = ics++ms'++ocs++[m'];
        mix' = MAPi msInst mix;
    in
      link_all mix' with In := MAP (npair 0) (GENLIST I isz)
`;



(*
   --------------------------------------------
   ------ N-ary Primitive Recursion  ----------
   --------------------------------------------
*)


Definition loopguard_def:
  loopguard guard step = <|
    Q:= {npair 0 2} ∪ step.Q;
    tf := (λs. if s=(npair 0 2) then (Dec guard (SOME step.q0) NONE)
                else end_link (step.tf s) (npair 0 2));
    q0 := (npair 0 2);
    In := [guard] ++ step.In;
    Out := step.Out;
  |>
End


Definition count_def:
  count = <|
    Q:= {(npair 0 0)};
    tf := (λs. Inc (npair 0 0) NONE);
    q0 := (npair 0 0);
    In := [(npair 0 0)];
    Out := (npair 0 0);
  |>
End


(*
(0,0) counter
(0,1) acc
(0,2) guard

Pr guard [i1...in]
base [i1...in]
step counter acc [i1...in]
*)

Definition Pr_def:
  Pr base step =
      let base' = mrInst 2 base;
          step' = mrInst 3 step;
          ptb   = MAPi (λi r. dup (npair 0 (i+3)) r (npair 1 0)) base'.In;
          btp   = dup base'.Out (npair 0 1) (npair 1 0) ;
          pts0  = dup (npair 0 0) (HD step'.In) (npair 1 0);
          pts1  = dup (npair 0 1) (EL 1 step'.In) (npair 1 0);
          pts   = MAPi (λi r. dup (npair 0 (i+3)) r (npair 1 0)) (DROP 2 step'.In);
          stp   = dup step'.Out (npair 0 1) (npair 1 0);
          mix1   = ptb ++ [base'] ++ [btp];
          mix2   = pts0::pts1::pts ++ [step'] ++ [count] ++ [stp];
          mix1'  = MAPi (λi m. msInst (i+1) m) mix1;
          mix1'' = MAP (msInst 2) mix1';
          mix2'  = MAPi (λi m. msInst (i+1) m) mix2;
          mix2'' = MAP (msInst 3) mix2';
          m2     = link_all mix2'';
          m2'  = loopguard (npair 0 2) m2;
          mix  = mix1''++[m2'];
    in
      link_all mix with In := MAP (λr. npair 0 (r+2)) (GENLIST I $ LENGTH base.In + 1)
End


Definition add1_def:
  add1 = <|
    Q:={0};
    tf:=(λs. Inc 0 NONE);
    q0:=0;
    In:=[0];
    Out:=0;
  |>
End



(*
   --------------------------------------------
   ------ Unary Primitive Recursion  ----------
   --------------------------------------------
*)

(*
Definition guard_def:
  guard s = <|
      Q := {1};
      tf := (λs. Dec 0 (SOME s) NONE);
      q0 := 1;
      In := [0];
      Out := 0;
      |>
End
*)

(* Assumption: ((guard, count), (accumulator, inputs))*)
(*
Definition loopguard_unary:
  loopguard_unary =
      let

      in
End


Definition count_unary:
  count = <|
    Q:= {(npair 0 0)};
    tf := (λs. Inc (npair 0 0) NONE);
    q0 := (npair 0 0);
    In := [(npair 0 0)];
    Out := (npair 0 0);
  |>
End
*)


Definition swap_NONE_state:
  swap_NONE_state M S = <|
        Q := {s | s ∈ M.Q ∨ s = S};
        tf := (λs. end_link (M.tf s) S);
        q0 := M.q0;
        In := M.In;
        Out := M.Out;
    |>
End

(* TODO: new guard and count functions *)
(* Assumption: ((guard, count), (accumulator, inputs))*)

Definition Pr_unary_def:
  Pr_unary base step guard countt =
      let base' = mrInst 1 base;
          guard'= mrInst 2 guard;
          step' = mrInst 3 step;
          countt' = mrInst 4 countt;

          d0_1  = dup 0 (HD base'.In) 2;
          d1_2  = dup base'.Out (HD guard'.In) 2;
          d2_3  = dup guard'.Out (HD step'.In) 2;
          d3_4  = dup step'.Out (HD countt'.In) 2;
          d4_2  = dup countt'.Out (HD guard'.In) 2;
          d4_2' = swap_NONE_state d4_2 guard'.q0;

          mix   = [d0_1; base'; d1_2; guard'; d2_3; step'; d3_4; countt'; d4_2'];
          mix'  = MAPi msInst mix
      in
        link_all mix with In := [0]
End


(*
   ----------------------------------
   ----  Minimisation Function   ----
   ----------------------------------
*)

(*
Definition Mu_def:
   Mu f =
      let
        f' = mrInst 1 f;
        count' = count ++ f' ;
        mtf = dup Mu.In f'.In (npair 0 1);
        ftg = dup f'.Out guard.In (npair 0 1);
        guard' = plink (msInst 0 guard) (msInst 1 count);
        mix = mtf ++ f' ++ ftg;
        mix' = MAPi (λi m. msInst (i+2) m) mix;
      in
        link with In := [(npair 0 0)]
End
*)



(* Proof *)
(*
---------------------------------------------------
----  Proving RM -> Unary Recursive Functions  ----
---------------------------------------------------
- 0
- Successor
- Pair
- First
- Second
- Composition
- Primitive Recursion
- Minimisation
*)


(* 0 *)
Theorem const0rm[simp] = EVAL``const 0``;

Theorem const0_correct:
  correct (const 0) zerof 1
Proof
  rw[correct_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  simp[] >>
  rw[Ntimes WHILE 2, run_machine_1_def] >>
  rw[APPLY_UPDATE_THM]
QED

Theorem const0_correct1_rmcorr:
  correct1_rmcorr (λi. 0) (const 0)
Proof
  rw[correct1_rmcorr_def, wfrm_def] >>
  rw[rmcorr_def] >>
  map_every qexists_tac [`SUC 0`, `λr. if r = 0 then rs r + 1 else 0`] >>
  rw[run_step_def, run_machine_1_def] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >>
  Cases_on`r = 0` >> fs[]
QED

(* SUC *)
Theorem add1_correct:
  correct add1 succ 1
Proof
  rw[correct_def, add1_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  Cases_on `l` >> fs[] >>
  rw[Ntimes WHILE 2, run_machine_1_def] >>
  rw[APPLY_UPDATE_THM]
QED


Theorem add1_correct1_rmcorr:
  correct1_rmcorr SUC add1
Proof
  rw[correct1_rmcorr_def, wfrm_def, add1_def] >>
  rw[rmcorr_def] >>
  map_every qexists_tac [`SUC 0`, `λr. if r = 0 then rs r + 1 else 0`] >>
  rw[run_step_def, run_machine_1_def] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >>
  Cases_on`r = 0` >> fs[]
QED

(* Projection *)
(*
Theorem findi_snoc:
  findi i (SNOC k l) =
            if MEM i l then findi i l
            else if i = k then LENGTH l
            else LENGTH l + 1
Proof
  Induct_on `l` >> simp[findi_def]
  >> rw[]
  >> fs[]
QED

Theorem findi_genlist[simp]:
  findi i (GENLIST I j) =
              if i < j then i
                else j
Proof
  Induct_on `j` >> simp[findi_def, GENLIST, findi_snoc, MEM_GENLIST]
QED


Theorem pi_correct:
  correct (Pi i j) (proj i) j
Proof
  rw[Pi_def, correct_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  rw[AllCaseEqs()] >>
  rw[Once WHILE, run_machine_1_def]
  >> rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM]
  >> simp[proj_def]
QED
*)


(* Composition*)

(*
  g := mrInst 2 g
  f := mrInst 1 f
  *)

Theorem Cn_In[simp]:
  LENGTH M2.In = 1 ⇒
   (Cn M1 M2).In = [npair 2 (HD M2.In)]
Proof
  rw[Cn_def]
QED


Theorem Cn_rmcorr:
∀M N Op f g fin gin RS.
  wfrm g ∧ wfrm f ∧ g.In = [gin] ∧ f.In = [fin]
∧
  rmcorr g g.q0 (λrs. rs gin = M ∧ ∀k. k ≠ gin ⇒ rs k = 0) NONE (λrs. rs g.Out = N)
∧
  rmcorr f f.q0 (λrs. rs fin = N ∧ ∀k. k ≠ fin ⇒ rs k = 0) NONE (λrs. rs f.Out = Op)

⇒ rmcorr (Cn f g) (Cn f g).q0 (λrs. rs (2 ⊗ gin) = M ∧ ∀k. k ≠ (2 ⊗ gin) ⇒ rs k = 0) NONE (λrs. rs (Cn f g).Out = Op)
Proof
  rw[Cn_def, link_all_def] >>
  irule link_correct_V >> simp[] >> rw[]
  >- (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[npair_11, DECIDE``2 ≠ 0``])
  >- (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[npair_11, DECIDE``2 ≠ 1``])
  >> qexists_tac `λrs. rs (HD (msInst 2 (mrInst 1 f)).In) = N ∧
                       rs (msInst 0 (mrInst 2 g)).Out = N ∧
                       ∀k. k ≠ (HD (msInst 2 (mrInst 1 f)).In) ∧ nfst k ≠ 2 ⇒ rs k = 0`
  >> qexists_tac `λrs. rs (HD (msInst 2 (mrInst 1 f)).In) = N ∧ ∀k. k ≠ (HD (msInst 2 (mrInst 1 f)).In) ∧ nfst k = 1 ⇒ rs k = 0`
  >> reverse (rw[])
  (* f *)
  >- (irule msInst_correct_2 >> rw[] >> qexists_tac`NONE` >> rw[]
      >- rw[npair_opt_def]
      >- metis_tac[wfrm_def]
      >> irule mrInst_correct >> rw[]
      >- metis_tac[wfrm_def]
      >> map_every qexists_tac [`(λrs. rs fin = N ∧ ∀k. k ≠ fin ⇒ rs k = 0)`,`(λrs. rs f.Out = Op)`]
      >> rw[liftP_def]
      >> rw[FUN_EQ_THM]
      >> `(∀k. k ≠ 1 ⊗ fin ∧ nfst k = 1 ⇒ rs k = 0) = (∀k. k ≠ fin ⇒ rs (1 ⊗ k) = 0)`
            by (rw[EQ_IMP_THM] >> `∃p q. k = npair p q` by metis_tac[npair_cases] >> fs[])
      >> rw[])
  >> irule link_correct_V >> simp[] >> rw[]
  >- (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[npair_11, DECIDE``1 ≠ 0``])
  >> qexists_tac `λrs.rs (msInst 0 (mrInst 2 g)).Out = N ∧ ∀k. nfst k ≠ 2 ⇒ rs k = 0`
  >> qexists_tac `λrs.rs (msInst 0 (mrInst 2 g)).Out = N ∧ ∀k. nfst k ≠ 2 ∧ k ≠ (HD (msInst 2 (mrInst 1 f)).In) ⇒ rs k = 0`
  >> reverse (rw[])
  (* dup *)
  >- (irule msInst_correct_2 >> rw[] >> qexists_tac`NONE` >> rw[]
      >- rw[npair_opt_def]
      >> irule dup_correct_INV >> simp[]
      >> qexists_tac `λrs. ∀k. nfst k ≠ 2 ∧ k ≠ (HD (msInst 2 (mrInst 1 f)).In) ⇒ rs k = 0`
      >> qexists_tac `N` >> rw[]
      >> rw[FUN_EQ_THM, EQ_IMP_THM]
      >> first_x_assum drule_all
      >> rw[] >> fs[])
  (* g *)
  >> irule msInst_correct_2 >> rw[]
  >> qexists_tac `NONE` >> rw[]
  >- rw[npair_opt_def]
  >- metis_tac[wfrm_def]
  >> `(mrInst 2 g).In = [2 ⊗ gin]` by simp[]
  >> `(mrInst 2 g with In := [2 ⊗ gin]) = (mrInst 2 g with In := (mrInst 2 g).In)` by metis_tac[]
  >> simp[]
  >> irule mrInst_correct_kV >> rw[]
  >- fs[wfrm_def]
  >> qexists_tac `λrs. rs gin = M ∧ ∀k. k ≠ gin ⇒ rs k = 0`
  >> qexists_tac `λrs. rs g.Out = N`
  >> qexists_tac `λr. 0`
  >> rw[liftP_V_def]
  >> rw[FUN_EQ_THM, EQ_IMP_THM]
  >- (`∃p q. k = npair p q` by simp[npair_cases] >> fs[])
  >> `∃p q. k = npair p q` by simp[npair_cases] >> fs[]
  >> Cases_on `nfst k = 2` >> fs[]
  >- (last_x_assum drule >> rw[] >> fs[])
  >> metis_tac[]
QED

Theorem Cn_wfrm[simp]:
  wfrm m1 ∧ wfrm m2  ⇒ wfrm (Cn m1 m2)
Proof
  rw[Cn_def, link_all_def]
QED

Theorem Cn_correct1_rmcorr:
∀M1 M2 f g. correct1_rmcorr f M1 ∧ correct1_rmcorr g M2
⇒ correct1_rmcorr (f o g) (Cn M1 M2)
Proof
  rw[correct1_rmcorr_def] >> simp[] >>
  gen_tac >>
  irule Cn_rmcorr >> simp[] >>
  metis_tac[]
QED

val _ = export_theory ()
