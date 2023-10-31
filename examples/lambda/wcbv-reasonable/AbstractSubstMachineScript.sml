(* See:
     Forster, Kunze and Roth,
     "The Weak Call-by-Value 𝜆-Calculus Is Reasonable for Both Time and Space", POPL 2020
   for inspiration
*)

(* Added assumptions for closed terms for some theorems (commented)
    due to the difference between
      how substitutions are defined
        in HOL library and in Forster etc.'s Coq proof *)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory relationTheory combinTheory;

open PrelimsTheory;
open weak_CBVTheory;
open ProgramsTheory;

val _ = new_theory "AbstractSubstMachine";

Theorem jumpTarget_correct_conc:
  ∀s c. jumpTarget 0 [] (compile s ++ [retT] ++ c) = SOME (compile s, c)
Proof
  rw[] >>
  `jumpTarget 0 [] (compile s ++ retT::c) = SOME (compile s, c)`
    by rw[jumpTarget_correct] >>
  `compile s ⧺ [retT] ⧺ c = compile s ⧺ retT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED

Type state = ``:Pro list # Pro list``;

(* tc (c:Pro) C: list Pro *)
Definition tc:
  tc c C =
    case c of
      [] => C
    | _  => c::C
End

Inductive step:
[~pushVal:]
  ∀P P' Q T V.
    jumpTarget 0 [] P = SOME (Q,P') ⇒ step ((lamT::P)::T,V) (tc P' T,Q::V)
[~beta:]
  ∀P Q R T V.
    step ((appT::P)::T,Q::R::V) (substP R 0 (lamT::Q++[retT])::tc P T,V)
End

Definition init:
  init s = ([compile s], [])
End

Theorem jumpTarget_simps:
  (jumpTarget l res [] = NONE) ∧
  (jumpTarget l res (varT v3::P') = jumpTarget l (res ⧺ [varT v3]) P') ∧
  (jumpTarget l res (appT::P') = jumpTarget l (res ⧺ [appT]) P') ∧
  (jumpTarget l res (lamT::P') = jumpTarget (SUC l) (res ⧺ [lamT]) P') ∧
  (jumpTarget 0 res (retT::P') = SOME (res,P')) ∧
  (jumpTarget (SUC l') res (retT::P') = jumpTarget l' (res ⧺ [retT]) P')
Proof
  rw[] >> rw[Once jumpTarget]
QED

Theorem tc_compile:
  ∀s c C. tc (compile s++c) C = (compile s++c)::C
Proof
  Induct_on `s` >> rw[tc, Once compile] >>
  Cases_on `compile s ⧺ compile s' ⧺ [appT] ⧺ c` >> rw[] >> gs[]
QED

(* --------------------------
         Time Cost Model
   -------------------------- *)

(* Added assumption `` closed s `` here *)
Theorem correctTime':
  ∀s t k c0 C V.
    closed s ⇒
    timeBS k s t ⇒
    ∃p l.
      reprP p t ∧
      NRC step l ((compile s++c0)::C,V) (tc c0 C,p::V) ∧
      l = 3*k+1
Proof
  Induct_on `timeBS` >> rw[]
  >- (qexists_tac `compile s` >> rw[reprP_cases] >>
      `step ((compile (dABS s) ⧺ c0)::C',V) (tc c0 C',compile s::V)`
        suffices_by metis_tac[] >>
      rw[Once step_cases] >> rw[Once compile] >>
      qexists_tac `c0`  >>
      rw[jumpTarget_correct_conc])
  >> rw[Once compile] >>
  rename [`3 * (i + (j + (k + 1))) + 1`,
          `timeBS i s (dABS s')`,
          `timeBS j t (dABS t')`,
          `timeBS k (subst s' 0 (dABS t')) u`] >>
  drule closed_app >> rw[] >>
  last_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  `closed (dABS s')` by metis_tac[closed_timeBS] >>
  `closed (dABS t')` by metis_tac[closed_timeBS] >>
  `closed (subst s' 0 (dABS t'))` by metis_tac[closed_subst2] >>
  first_x_assum drule >> rw[] >>
  last_x_assum (qspecl_then [`compile t ++ appT :: c0`, `C'`, `V`] ASSUME_TAC) >>
  last_x_assum (qspecl_then [`appT :: c0`, `C'`, `compile s'::V`] ASSUME_TAC) >>
  last_x_assum (qspecl_then [`[]`, `tc c0 C'`, `V`] ASSUME_TAC) >>
  rw[reprP_cases] >>
  `NRC step (((3 * j + 1) + ((3 * k + 1) + 1)) + (3 * i + 1))
          ((compile s ⧺ compile t ⧺ [appT] ⧺ c0)::C',V)
          (tc c0 C',compile s''::V)`
      suffices_by (`3 * (i + (j + (k + 1))) + 1 =
                   (3 * i + 1 + ((3 * j + 1) + ((3 * k + 1) + 1)))`
                      by rw[] >> rw[]) >>
  irule (iffRL NRC_add) >> rw[O_DEF] >>
  qexists_tac `(tc (compile t ⧺ appT::c0) C',compile s'::V)` >> rw[]
  >- (`compile s ⧺ compile t ++ [appT] ⧺ c0 =
       compile s ⧺ compile t ++ appT::c0`
         suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND]) >>
  `NRC step ((3 * k + 2) + (3 * j + 1 ))
          (tc (compile t ⧺ appT::c0) C',compile s'::V)
          (tc c0 C',compile s''::V)`
      suffices_by rw[] >>
  irule (iffRL NRC_add) >> rw[O_DEF] >>
  qexists_tac `(tc (appT::c0) C',compile t'::compile s'::V)` >> rw[]
  >- rw[tc_compile]
  >> `NRC step ((3 * k + 1) + 1)
          (tc (appT::c0) C',compile t'::compile s'::V)
          (tc c0 C',compile s''::V)`
        suffices_by rw[] >>
  irule (iffRL NRC_add) >> rw[O_DEF] >>
  qexists_tac `(compile (subst s' 0 (dABS t'))::tc c0 C',V)` >> rw[]
  >- (rw[Once tc] >>
      rw[Once step_cases] >>
      `compile (subst s' 0 (dABS t')) =
       substP (compile s') 0 (compile (dABS t'))`
        by metis_tac[substP_correct] >> rw[] >>
      `compile (dABS t') = lamT::(compile t' ⧺ [retT])`
        suffices_by rw[] >>
       rw[Once compile])
  >> fs[tc]
QED

(* Added assumption `` closed s `` here *)
Theorem correctTime:
  ∀s t k.
    closed s ⇒
    timeBS k s t ⇒
    ∃p.
      reprP p t ∧
      NRC step (3*k+1) (init s) ([],[p])
Proof
  rw[init] >>
  `∃p l.
      reprP p t ∧
      NRC step l ((compile s ⧺ [])::[],[]) (tc [] [],p::[]) ∧
      l = 3 * k + 1`
    by metis_tac[correctTime'] >>
  qexists_tac `p` >> rw[] >>
  fs[tc]
QED

(* --------------------------
        Space Cost Model
   -------------------------- *)

Theorem helperF:
  ∀P T.
    SUM (MAP sizeT P) + SUM (MAP sizeP T) ≤ SUM (MAP sizeP (tc P T))
Proof
  rw[tc] >> Cases_on `P` >> rw[] >>
  rw[sizeP]
QED

Theorem helper2:
  ∀s m. size s ≤ m ⇒ 1 + SUM (MAP sizeT (compile s)) ≤ 2*m
Proof
  rw[] >>
  `SUM (MAP sizeT (compile s)) + 1 ≤ 2 * size s`
    by metis_tac[sizeP_size] >>
  gs[integerTheory.INT_LE_TRANS]
QED

Theorem helperF':
  ∀P T.
    SUM (MAP sizeP (tc P T)) ≤ SUM (MAP sizeT P) + SUM (MAP sizeP T) + 1
Proof
  rw[tc] >> Cases_on `P` >> rw[sizeP]
QED

Theorem size_le_sizeT:
  ∀s.
    size s ≤ SUM (MAP sizeT (compile s))
Proof
  Induct_on `s` >> rw[]
  >- (rw[size, compile, sizeT])
  >- (rw[Once size, Once compile] >>
      `sizeT appT = 1` by rw[sizeT] >> rw[] >>
      rw[SUM_APPEND])
  >> rw[Once size, Once compile] >>
  `sizeT lamT = 1` by rw[sizeT] >> rw[] >>
  rw[SUM_APPEND]
QED

Definition redWithMaxSizeS:
  redWithMaxSizeS =
    redWithMaxSize (λ(T',V'). (SUM (MAP sizeP T') + SUM (MAP sizeP V'))) step
End

(* Added assumption `` closed s `` here *)
Theorem correctSpace':
  ∀s t k P T V.
    closed s ⇒
    spaceBS k s t ⇒
    ∃m Q.
      reprP Q t ∧
      redWithMaxSizeS m ((compile s++P)::T,V) (tc P T,Q::V) ∧
      k + SUM (MAP sizeP (tc P T)) + SUM (MAP sizeP V) ≤ m ∧
      m ≤ 2*k + SUM (MAP sizeP (tc P T)) + SUM (MAP sizeP V)
Proof
  simp[redWithMaxSizeS] >>
  Induct_on `spaceBS` >> rw[]
  >- (rw[Once compile] >>
      qexistsl_tac
      [`MAX (SUM (MAP sizeP ((lamT::compile s ++ [retT] ++ P)::T')) + SUM (MAP sizeP V))
            (SUM (MAP sizeP (tc P T')) + SUM (MAP sizeP (compile s::V)))`,
       `compile s`] >> rw[reprP_cases]
      >- (`redWithMaxSize (λ(T',V'). SUM (MAP sizeP T') + SUM (MAP sizeP V'))
                          step
                          ((λ(T',V'). SUM (MAP sizeP T') + SUM (MAP sizeP V')) (tc P T',compile s::V))
                          (tc P T',compile s::V)
                          (tc P T',compile s::V)`
            by metis_tac[redWithMaxSize_R] >> gs[] >>
          rw[Once redWithMaxSize_cases] >>
          qexistsl_tac [`(tc P T',compile s::V)`,
                        `(SUM (MAP sizeP V) +
                         (SUM (MAP sizeP (tc P T')) + sizeP (compile s)))`] >>
          rw[] >> rw[Once step_cases] >>
          qexists_tac `P` >> rw[] >>
          metis_tac[jumpTarget_correct_conc])
      >- (`size (dABS s) ≤ sizeP (compile s)` suffices_by metis_tac[] >>
          rw[Once size, sizeP] >> metis_tac[sizeP_size'])
      >- (rw[tc] >> Cases_on `P` >> rw[]
          >- (rw[sizeP, Once size] >>
              `sizeT lamT = 1` by rw[Once sizeT] >>
              `sizeT retT = 1` by rw[Once sizeT] >>
              rw[] >>
              `size s ≤ size s ⇒
               1 + SUM (MAP sizeT (compile s)) ≤ 2*(size s)`
                by metis_tac[helper2] >>
              `size s ≤ size s` by rw[] >>
              first_x_assum drule >> rw[] >>
              rw[SUM_APPEND])
          >> rw[sizeP] >>
          `sizeT lamT = 1` by rw[Once sizeT] >>
          `sizeT retT = 1` by rw[Once sizeT] >> rw[] >>
          rw[SUM_APPEND] >> rw[Once size] >>
          `SUM (MAP sizeT (compile s)) ≤ 2 * size s`
            suffices_by rw[] >>
          `size s ≤ size s` by rw[] >>
          drule helper2 >> rw[])
      >> rw[sizeP, Once size] >>
      `sizeT lamT = 1` by rw[Once sizeT] >>
      `sizeT retT = 1` by rw[Once sizeT] >>
      rw[] >>
      `size s ≤ size s ⇒
       1 + SUM (MAP sizeT (compile s)) ≤ 2*(size s)`
        by metis_tac[helper2] >>
      `size s ≤ size s` by rw[] >>
      first_x_assum drule >> rw[] >>
      rw[SUM_APPEND])
  >> rw[Once compile] >>
  drule closed_app >> rw[] >>
  last_x_assum drule >> rw[] >>
  last_x_assum drule >> rw[] >>
  drule_all closed_spaceBS >> rw[] >>
  `closed (dABS s')` by metis_tac[closed_spaceBS] >>
  `closed (subst s' 0 (dABS t'))` by metis_tac[closed_subst2] >>
  first_x_assum drule >> rw[] >>
  last_x_assum (qspecl_then [`compile s'' ⧺ [appT] ⧺ P`,
                             `T'`, `V`] ASSUME_TAC) >>
  fs[] >>
  last_x_assum (qspecl_then [`[appT] ⧺ P`,
                             `T'`, `Q::V`] ASSUME_TAC) >>
  last_x_assum (qspecl_then [`[]`,
                             `(tc P T')`, `V`] ASSUME_TAC) >>
  fs[] >>
  `redWithMaxSize
      (λ(T',V'). SUM (MAP sizeP T') + SUM (MAP sizeP V'))
      step
      (MAX m m') ((compile s ⧺ compile s'' ⧺ [appT] ⧺ P)::T',V)
      (tc (appT::P) T',Q'::Q::V)`
    by (irule redWithMaxSize_trans >>
        qexistsl_tac [`m`, `m'`, `tc (compile s'' ⧺ [appT] ⧺ P) T',Q::V`] >>
        rw[] >> rw[Once tc] >>
        Cases_on `compile s'' ⧺ [appT] ⧺ P` >> rw[] >> gs[]) >>
  `step (tc (appT::P) T',Q'::Q::V) (compile (subst s' 0 (dABS t'))::tc P T',V)`
    by (rw[Once step_cases, tc] >> fs[reprP_cases] >> rw[] >>
        `compile (dABS t') = lamT::(compile t' ⧺ [retT])`
          suffices_by metis_tac[substP_correct] >>
        rw[Once compile]) >>
  drule redWithMaxSize_C >> rw[] >>
  first_x_assum drule >> rw[] >>
  qexistsl_tac [`MAX (MAX m m')
                     (MAX (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + (sizeP Q + sizeP Q')))
                           m'')`,
                `Q''`] >> rw[]
  (* 6 *)
  (* 1/6 *)
  >- (irule redWithMaxSize_trans >>
      qexistsl_tac [`(MAX m m')`,
                    `(MAX
                         (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + (sizeP Q + sizeP Q')))
                          m'')`,
                    `(tc (appT::P) T',Q'::Q::V)`] >>
      rw[] >>
      `(tc [] (tc P T'),Q''::V) = (tc P T',Q''::V)`
        suffices_by metis_tac[] >> rw[tc])
  (* 2/6 *)
  >- (rpt (qpat_x_assum `redWithMaxSize _ _ _ _ _` (K all_tac)) >>
      rw[MAX_DEF]
      >- fs[tc]
      >- fs[tc]
      >- (fs[reprP_cases] >> rw[] >>
          DISJ1_TAC >> DISJ2_TAC >>
          `k' + (SUM (MAP sizeP V)
              + (SUM (MAP sizeP (tc P T')) + (size (dABS s') + 1)))
           ≤
           k' + (SUM (MAP sizeP V)
              + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP (compile s')))`
            suffices_by rw[] >> rw[tc] >>
          Cases_on `P` >> rw[]
          >- (rw[sizeP] >> `sizeT appT = 1` by rw[Once sizeT] >> rw[] >>
              rw[Once size] >>
              `size s' ≤ SUM (MAP sizeT (compile s'))`
                suffices_by rw[] >>
              metis_tac[size_le_sizeT])
          >> rw[sizeP] >> `sizeT appT = 1` by rw[Once sizeT]  >> rw[] >>
          rw[Once size] >>
          `size s' ≤ SUM (MAP sizeT (compile s'))`
                suffices_by rw[] >>
          metis_tac[size_le_sizeT])
      >- (fs[reprP_cases] >> rw[] >>
          DISJ1_TAC >> DISJ2_TAC >>
          `k' + (SUM (MAP sizeP V)
              + (SUM (MAP sizeP (tc P T')) + (size (dABS s') + 1)))
           ≤
           k' + (SUM (MAP sizeP V)
              + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP (compile s')))`
            suffices_by rw[] >> rw[tc] >>
          Cases_on `P` >> rw[]
          >- (rw[sizeP] >> `sizeT appT = 1` by rw[Once sizeT] >> rw[] >>
              rw[Once size] >>
              `size s' ≤ SUM (MAP sizeT (compile s'))`
                suffices_by rw[] >>
              metis_tac[size_le_sizeT])
          >> rw[sizeP] >> `sizeT appT = 1` by rw[Once sizeT]  >> rw[] >>
          rw[Once size] >>
          `size s' ≤ SUM (MAP sizeT (compile s'))`
                suffices_by rw[] >>
          metis_tac[size_le_sizeT])
      >> fs[reprP_cases] >> rw[] >>
      DISJ1_TAC >> DISJ1_TAC >>
      `k + (SUM (MAP sizeP V)
         + (SUM (MAP sizeP (tc P T')) + (size s'' + 1)))
       ≤
       k + (SUM (MAP sizeP V)
         + (SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))))`
        suffices_by rw[integerTheory.INT_LE_TRANS] >> rw[Once tc] >>
      Cases_on `P` >> rw[]
      >- (rw[sizeP] >> `sizeT appT = 1` by rw[Once sizeT] >> rw[] >>
          rw[tc_compile] >> rw[sizeP] >>
          `size s'' ≤ SUM (MAP sizeT (compile s''))`
            suffices_by rw[SUM_APPEND] >>
          metis_tac[size_le_sizeT])
      >> `tc (compile s'' ⧺ [appT] ⧺ h::t) T' =
          (compile s'' ⧺ [appT] ⧺ h::t)::T'`
            by metis_tac[tc_compile, APPEND_ASSOC] >>
      rw[] >> rw[sizeP] >> rw[SUM_APPEND] >>
      `sizeT appT = 1` by rw[sizeT] >>
      `size s'' ≤ SUM (MAP sizeT (compile s''))`
        suffices_by rw[] >>
      metis_tac[size_le_sizeT])
  (* 3/6 *)
  >- (rpt (qpat_x_assum `redWithMaxSize _ _ _ _ _` (K all_tac)) >>
      `2 * k +
        (SUM (MAP sizeP V) +
         SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))) ≤
         SUM (MAP sizeP V) +
        (SUM (MAP sizeP (tc P T')) +
         2 * MAX (k + (size s'' + 1)) (MAX (k' + (size (dABS s') + 1)) k''))`
        suffices_by rw[] >> rw[MAX_DEF]
      (* 5 *)
      >- (`2 * k +
          (SUM (MAP sizeP V) +
           SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))) ≤
           2 * (k + (size s'' + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          `SUM (MAP sizeP (tc (compile s'' ++ [appT] ⧺ P) T'))
            ≤ SUM (MAP sizeP (tc P T')) + 2 * (size s'' + 1)`
            suffices_by rw[integerTheory.INT_LDISTRIB] >>
          Cases_on `P` >> rw[]
          >- (`tc [] T' = T'` by rw[tc] >> rw[] >>
              rw[tc_compile] >> rw[sizeP] >>
              `sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              `size s'' ≤ size s''` by rw[] >>
              drule helper2 >> rw[])
          >> `tc (h::t'') T' = (h::t'')::T'` by rw[tc] >>
          rw[] >>
          `tc (compile s'' ⧺ [appT] ⧺ h::t'') T' =
           (compile s'' ⧺ [appT] ⧺ h::t'')::T'`
             by metis_tac[tc_compile, APPEND_ASSOC] >>
          rw[] >> rw[sizeP] >> rw[SUM_APPEND] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[] >>
          `size s'' ≤ size s''` by rw[] >>
          drule helper2 >> rw[])
      >- (`2 * k +
          (SUM (MAP sizeP V) +
           SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))) ≤
           2 * (k + (size s'' + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          `SUM (MAP sizeP (tc (compile s'' ++ [appT] ⧺ P) T'))
            ≤ SUM (MAP sizeP (tc P T')) + 2 * (size s'' + 1)`
            suffices_by rw[integerTheory.INT_LDISTRIB] >>
          Cases_on `P` >> rw[]
          >- (`tc [] T' = T'` by rw[tc] >> rw[] >>
              rw[tc_compile] >> rw[sizeP] >>
              `sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              `size s'' ≤ size s''` by rw[] >>
              drule helper2 >> rw[])
          >> `tc (h::t'') T' = (h::t'')::T'` by rw[tc] >>
          rw[] >>
          `tc (compile s'' ⧺ [appT] ⧺ h::t'') T' =
           (compile s'' ⧺ [appT] ⧺ h::t'')::T'`
             by metis_tac[tc_compile, APPEND_ASSOC] >>
          rw[] >> rw[sizeP] >> rw[SUM_APPEND] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[] >>
          `size s'' ≤ size s''` by rw[] >>
          drule helper2 >> rw[])
      >- (`2 * k +
          (SUM (MAP sizeP V) +
           SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))) ≤
           2 * (k + (size s'' + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          `SUM (MAP sizeP (tc (compile s'' ++ [appT] ⧺ P) T'))
            ≤ SUM (MAP sizeP (tc P T')) + 2 * (size s'' + 1)`
            suffices_by rw[integerTheory.INT_LDISTRIB] >>
          Cases_on `P` >> rw[]
          >- (`tc [] T' = T'` by rw[tc] >> rw[] >>
              rw[tc_compile] >> rw[sizeP] >>
              `sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              `size s'' ≤ size s''` by rw[] >>
              drule helper2 >> rw[])
          >> `tc (h::t'') T' = (h::t'')::T'` by rw[tc] >>
          rw[] >>
          `tc (compile s'' ⧺ [appT] ⧺ h::t'') T' =
           (compile s'' ⧺ [appT] ⧺ h::t'')::T'`
             by metis_tac[tc_compile, APPEND_ASSOC] >>
          rw[] >> rw[sizeP] >> rw[SUM_APPEND] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[] >>
          `size s'' ≤ size s''` by rw[] >>
          drule helper2 >> rw[])
      >-(`2 * k +
          (SUM (MAP sizeP V) +
           SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))) ≤
           2 * (k + (size s'' + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          `SUM (MAP sizeP (tc (compile s'' ++ [appT] ⧺ P) T'))
            ≤ SUM (MAP sizeP (tc P T')) + 2 * (size s'' + 1)`
            suffices_by rw[integerTheory.INT_LDISTRIB] >>
          Cases_on `P` >> rw[]
          >- (`tc [] T' = T'` by rw[tc] >> rw[] >>
              rw[tc_compile] >> rw[sizeP] >>
              `sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              `size s'' ≤ size s''` by rw[] >>
              drule helper2 >> rw[])
          >> `tc (h::t'') T' = (h::t'')::T'` by rw[tc] >>
          rw[] >>
          `tc (compile s'' ⧺ [appT] ⧺ h::t'') T' =
           (compile s'' ⧺ [appT] ⧺ h::t'')::T'`
             by metis_tac[tc_compile, APPEND_ASSOC] >>
          rw[] >> rw[sizeP] >> rw[SUM_APPEND] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[] >>
          `size s'' ≤ size s''` by rw[] >>
          drule helper2 >> rw[])
      >> `2 * k +
          (SUM (MAP sizeP V) +
           SUM (MAP sizeP (tc (compile s'' ⧺ [appT] ⧺ P) T'))) ≤
           2 * (k + (size s'' + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          `SUM (MAP sizeP (tc (compile s'' ++ [appT] ⧺ P) T'))
            ≤ SUM (MAP sizeP (tc P T')) + 2 * (size s'' + 1)`
            suffices_by rw[integerTheory.INT_LDISTRIB] >>
          Cases_on `P` >> rw[]
          >- (`tc [] T' = T'` by rw[tc] >> rw[] >>
              rw[tc_compile] >> rw[sizeP] >>
              `sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              `size s'' ≤ size s''` by rw[] >>
              drule helper2 >> rw[])
          >> `tc (h::t'') T' = (h::t'')::T'` by rw[tc] >>
          rw[] >>
          `tc (compile s'' ⧺ [appT] ⧺ h::t'') T' =
           (compile s'' ⧺ [appT] ⧺ h::t'')::T'`
             by metis_tac[tc_compile, APPEND_ASSOC] >>
          rw[] >> rw[sizeP] >> rw[SUM_APPEND] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[] >>
          `size s'' ≤ size s''` by rw[] >>
          drule helper2 >> rw[])
  (* 4/6 *)
  >- (rpt (qpat_x_assum `redWithMaxSize _ _ _ _ _` (K all_tac)) >>
      `2 * k' + (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP Q))
       ≤
        SUM (MAP sizeP V) + (SUM (MAP sizeP (tc P T')) +
         2 * MAX (k + (size s'' + 1)) (MAX (k' + (size (dABS s') + 1)) k''))`
        suffices_by rw[] >> rw[MAX_DEF] >> fs[reprP_cases]
      >- (`2 * k' +
          (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP Q))
          ≤
           2 * (k' + (size (dABS s') + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          rw[tc, sizeP] >>
          Cases_on `P` >> rw[]
          >- (`sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              rw[Once size] >>
              `SUM (MAP sizeT (compile s')) + 1 ≤
                2 * (size s')`
                suffices_by rw[] >>
              metis_tac[sizeP_size])
          >> rw[sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >>
          rw[SUM_APPEND] >>
          `SUM (MAP sizeT (compile s')) ≤
           2*(size (dABS s'))`
            suffices_by rw[] >>
          `size s' ≤ size s'` by rw[] >>
          drule helper2 >> rw[] >> rw[Once size])
      >- (`2 * k' +
          (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP Q))
          ≤
           2 * (k' + (size (dABS s') + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          rw[tc, sizeP] >>
          Cases_on `P` >> rw[]
          >- (`sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              rw[Once size] >>
              `SUM (MAP sizeT (compile s')) + 1 ≤
                2 * (size s')`
                suffices_by rw[] >>
              metis_tac[sizeP_size])
          >> rw[sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >>
          rw[SUM_APPEND] >>
          `SUM (MAP sizeT (compile s')) ≤
           2*(size (dABS s'))`
            suffices_by rw[] >>
          `size s' ≤ size s'` by rw[] >>
          drule helper2 >> rw[] >> rw[Once size])
      >- (`2 * k' +
          (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP Q))
          ≤
           2 * (k' + (size (dABS s') + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          rw[tc, sizeP] >>
          Cases_on `P` >> rw[]
          >- (`sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              rw[Once size] >>
              `SUM (MAP sizeT (compile s')) + 1 ≤
                2 * (size s')`
                suffices_by rw[] >>
              metis_tac[sizeP_size])
          >> rw[sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >>
          rw[SUM_APPEND] >>
          `SUM (MAP sizeT (compile s')) ≤
           2*(size (dABS s'))`
            suffices_by rw[] >>
          `size s' ≤ size s'` by rw[] >>
          drule helper2 >> rw[] >> rw[Once size])
      >- (`2 * k' +
          (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP Q))
          ≤
           2 * (k' + (size (dABS s') + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          rw[tc, sizeP] >>
          Cases_on `P` >> rw[]
          >- (`sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              rw[Once size] >>
              `SUM (MAP sizeT (compile s')) + 1 ≤
                2 * (size s')`
                suffices_by rw[] >>
              metis_tac[sizeP_size])
          >> rw[sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >>
          rw[SUM_APPEND] >>
          `SUM (MAP sizeT (compile s')) ≤
           2*(size (dABS s'))`
            suffices_by rw[] >>
          `size s' ≤ size s'` by rw[] >>
          drule helper2 >> rw[] >> rw[Once size])
      >- (`2 * k' +
          (SUM (MAP sizeP V) + (SUM (MAP sizeP (tc (appT::P) T')) + sizeP Q))
          ≤
           2 * (k' + (size (dABS s') + 1)) + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc P T')))`
            suffices_by rw[] >>
          rw[tc, sizeP] >>
          Cases_on `P` >> rw[]
          >- (`sizeT appT = 1` by rw[sizeT] >>
              rw[SUM_APPEND] >>
              rw[Once size] >>
              `SUM (MAP sizeT (compile s')) + 1 ≤
                2 * (size s')`
                suffices_by rw[] >>
              metis_tac[sizeP_size])
          >> rw[sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >>
          rw[SUM_APPEND] >>
          `SUM (MAP sizeT (compile s')) ≤
           2*(size (dABS s'))`
            suffices_by rw[] >>
          `size s' ≤ size s'` by rw[] >>
          drule helper2 >> rw[] >> rw[Once size]))
  (* 5/6 *)
  >- (ntac 2 (qpat_x_assum `spaceBS _ _ _` mp_tac) >>
      drule spaceBS_ge >>
      qpat_x_assum `spaceBS _ _ _` (K all_tac) >>
      ntac 2 strip_tac >> drule spaceBS_ge >>
      qpat_x_assum `spaceBS _ _ _` (K all_tac) >>
      ntac 2 strip_tac >> drule spaceBS_ge >>
      qpat_x_assum `spaceBS _ _ _` (K all_tac) >>
      strip_tac >>
      qpat_x_assum `redWithMaxSize _ _ _ (compile (subst _ _ _)::_, _) _` mp_tac >>
      drule redWithMaxSize_ge >> rw[]
      >- (fs[reprP_cases] >> rw[] >> rw[Once tc, sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[MAX_DEF]
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                 ≤ 2 * k''` suffices_by rw[integerTheory.INT_LE_ADD2] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * (k' + (size (dABS s') + 1))` suffices_by rw[] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                 ≤ 2 * k''` suffices_by rw[integerTheory.INT_LE_ADD2] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * (k' + (size (dABS s') + 1))` suffices_by rw[] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >> `k' + (size (dABS s') + 1) ≤ k + (size s'' + 1)`
                by fs[integerTheory.int_le] >>
              `SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
      >- (fs[reprP_cases] >> rw[] >> rw[Once tc, sizeP] >>
          `sizeT appT = 1` by rw[sizeT] >> rw[MAX_DEF]
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >- (`SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[])
          >> `k' + (size (dABS s') + 1) ≤ k + (size s'' + 1)`
                by fs[integerTheory.int_le] >>
              `SUM (MAP sizeT P) + SUM (MAP sizeP T') ≤ SUM (MAP sizeP (tc P T'))`
                by metis_tac[helperF] >>
              `SUM (MAP sizeT (compile s')) + SUM (MAP sizeT (compile t')) + 4
                ≤ 2 * size (dABS t') + 2 * size (dABS s') + 2` suffices_by rw[] >>
              rw[Once size] >> rw[Once size] >>
              `size s' ≤ size s'` by rw[] >>
              drule helper2 >> rw[] >>
              `size t' ≤ size t'` by rw[] >>
              drule helper2 >> rw[]))
  (* 6/6 *)
  >> rpt (qpat_x_assum `redWithMaxSize _ _ _ _ _` (K all_tac)) >>
  `2 * k'' + (SUM (MAP sizeP V) + SUM (MAP sizeP (tc [] (tc P T'))))
    ≤
      SUM (MAP sizeP V) +
      (SUM (MAP sizeP (tc P T')) +
      2 * MAX (k + (size s'' + 1)) (MAX (k' + (size (dABS s') + 1)) k''))`
    suffices_by rw[] >>
  rw[MAX_DEF] >> fs[reprP_cases] >>
  rw[Once tc]
QED

(* Added assumption `` closed s `` here *)
Theorem correctSpace:
  ∀s t m.
    closed s ⇒
    spaceBS m s t ⇒
    ∃m' P.
      reprP P t ∧
      redWithMaxSizeS m' (init s) ([],[P]) ∧
      m ≤ m' ∧
      m' ≤ 2 * m
Proof
  rw[] >> drule correctSpace' >>
  rw[init] >> first_x_assum drule >> rw[] >>
  first_x_assum (qspecl_then [`[]`, `[]`, `[]`] ASSUME_TAC) >>
  fs[tc] >> metis_tac[]
QED

val _ = export_theory ()
