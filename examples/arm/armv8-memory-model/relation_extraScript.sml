open HolKernel Parse boolLib bossLib
open set_relationTheory relationTheory

val () = new_theory "relation_extra"

(* -------------------------------------------------------------------------
   Definitions
   ------------------------------------------------------------------------- *)

Definition seq:
  seq = flip relation$O
End

Definition RMINUS:
  RMINUS R1 R2 x y <=> R1 x y /\ ~R2 x y
End

Definition RCROSS:
  RCROSS R1 R2 x y <=> R1 x /\ R2 y
End

Definition funeq:
  funeq f r = !x y. (r x y ==> f x = f y)
End

Definition functional:
  functional r = !x y z. r x y ==> r x z ==> y = z
End

Definition immediate:
  immediate r a b = (r a b /\ (!c. r a c ==> ~r c b))
End

Definition restr_rel:
  restr_rel cond r a b <=> r a b /\ cond a /\ cond b
End

Definition restr_eq_rel:
  restr_eq_rel f r a b <=> r a b /\ f a = f b
End

Definition acyclic:
  acyclic R = irreflexive (TC R)
End

Definition is_total:
  is_total A r = !a b. a IN A /\ b IN A /\ a <> b ==> r a b \/ r b a
End

Definition strict_total_order:
  strict_total_order A r <=> StrongOrder r /\ is_total A r
End

Definition classes:
  classes (eqv : 'a -> 'a -> bool) X = ?x. X = eqv x
End

Definition lift:
  lift (eqv : 'a -> 'a -> bool) (r : 'a -> 'a -> bool) X Y =
  ?x y. r x y /\ X = eqv x /\ Y = eqv y
End

Definition delift:
  delift (eqv : 'a -> 'a -> bool) r x y <=>
  r (eqv x) (eqv y) /\ eqv x x /\ eqv y y
End

Definition refl:
  refl eqv r = !x y. r x y \/ r y x ==> eqv x x
End

val () = List.app Parse.add_infix
  [("seq",    550, HOLgrammars.RIGHT),
   ("RMINUS", 600, HOLgrammars.LEFT),
   ("RCROSS", 602, HOLgrammars.LEFT)]

val () = List.app Unicode.unicode_version
  [{u = UTF8.chr 0x2A3E,                    tmnm = "seq"},
   {u = "-" ^ UnicodeChars.sub_r,           tmnm = "RMINUS"},
   {u = UTF8.chr 0xD7 ^ UnicodeChars.sub_r, tmnm = "RCROSS"}]

(* -------------------------------------------------------------------------
   Lemmas
   ------------------------------------------------------------------------- *)

(* (R1 ⨾ R2) x y <=> ?z. R1 x z /\ R2 z y *)
Theorem semi =
  seq
  |> SIMP_RULE (srw_ss()) [FUN_EQ_THM, relationTheory.O_DEF]
  |> Q.SPECL [`R1`, `R2`, `x`, `y`]
  |> GEN_ALL

val rel_rwts =
  simpLib.rewrites
    [relationTheory.RSUBSET, relationTheory.RUNION, relationTheory.RINTER,
     relationTheory.RRANGE, relationTheory.transitive_def,
     relationTheory.reflexive_def, relationTheory.irreflexive_def,
     relationTheory.diag_def, pred_setTheory.SUBSET_applied,
     RMINUS, RCROSS, semi, FUN_EQ_THM, pred_setTheory.SPECIFICATION]

fun rel_ss() = srw_ss()++rel_rwts

fun xrw thms = rw_tac (rel_ss()) thms
fun xsimp thms = asm_simp_tac (rel_ss()) thms
fun xfs thms = full_simp_tac (rel_ss()) thms

(* - diag ------------------------------------------------------------------ *)

Theorem diag_trans:
  transitive (diag p)
Proof
  xsimp []
QED

Theorem seq_diag_trans_l:
  transitive r ==> transitive (diag p ⨾ r)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_diag_trans_r:
  transitive r ==> transitive (r ⨾ diag p)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem diag_runion:
  diag (r1 UNION r2) = diag r1 RUNION diag r2
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rc_runion:
  RC r = (diag (K T) RUNION r)
Proof
  xsimp [relationTheory.RC_DEF]
QED

Theorem diag_T_seq_l:
  diag (K T) ⨾ r = r
Proof
  xsimp []
QED

Theorem diag_T_seq_r:
  r ⨾ diag (K T) = r
Proof
  xsimp []
QED

Theorem diag_rsubset:
  p1 SUBSET p2 ==> diag p1 RSUBSET diag p2
Proof
  xsimp []
QED

(* - seq ------------------------------------------------------------------- *)

Theorem seq_assoc:
  (r1 ⨾ r2) ⨾ r3 = r1 ⨾ r2 ⨾ r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem transp_seq:
  inv (r1 ⨾ r2) = inv r2 ⨾ inv r1
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_empty_l:
  REMPTY ⨾ r = REMPTY
Proof
  xsimp []
QED

Theorem seq_empty_r:
  r ⨾ REMPTY = REMPTY
Proof
  xsimp []
QED

Theorem irreflexive_seq:
  irreflexive (r1 ⨾ r2) = irreflexive (r2 ⨾ r1)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem reflexive_seq:
  reflexive r1 /\ reflexive r2 ==> reflexive (r1 ⨾ r2)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem functional_seq:
  functional r1 /\ functional r2 ==> functional (r1 ⨾ r2)
Proof
  xsimp [functional]
  \\ metis_tac []
QED

Theorem functional_alt:
  functional r <=> (inv r ⨾ r RSUBSET diag (K T))
Proof
  xsimp [functional]
  \\ metis_tac []
QED

Theorem inclusion_seq_mon:
   r1 RSUBSET r2 /\ r3 RSUBSET r4 ==> (r1 ⨾ r3) RSUBSET (r2 ⨾ r4)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_rsubset_l:
  !r. r1 RSUBSET r /\ (r ⨾ r2) RSUBSET r3 ==> (r1 ⨾ r2) RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_rsubset_r:
  !r. r2 RSUBSET r /\ (r1 ⨾ r) RSUBSET r3 ==> (r1 ⨾ r2) RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem inclusion_seq_refl:
   r1 RSUBSET r3 /\ r2 RSUBSET r3 /\ transitive r3 ==> (r1 ⨾ RC r2) RSUBSET r3
Proof
  xsimp [rc_runion]
  \\ metis_tac []
QED

Theorem inclusion_seq_eqv_l:
   diag dom ⨾ r RSUBSET r
Proof
  xsimp []
QED

Theorem inclusion_seq_eqv_r:
   r  ⨾ diag dom RSUBSET r
Proof
  xsimp []
QED

Theorem inclusion_seq_eqv:
  r1 RSUBSET r2 ==> diag dom1 ⨾ r1 ⨾ diag dom2 RSUBSET r2
Proof
  xrw []
QED

Theorem inclusion_seq_trans:
   r1 RSUBSET r3 /\ r2 RSUBSET r3 /\ transitive r3 ==> (r1 ⨾ r2) RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rsubset_seq_l:
  !r. r RSUBSET r3 /\ r1 RSUBSET (r2 ⨾ r) ==> r1 RSUBSET (r2 ⨾ r3)
Proof
  xrw []
  \\ metis_tac []
QED

Theorem rsubset_seq_r:
  !r. r RSUBSET r2 /\ r1 RSUBSET (r ⨾ r3) ==> r1 RSUBSET (r2 ⨾ r3)
Proof
  xrw []
  \\ metis_tac []
QED

Theorem inclusion_seq_l:
   r1 RSUBSET r2 /\ reflexive r3 ==> r1 RSUBSET r2 ⨾ r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem inclusion_seq_r:
   r1 RSUBSET r3 /\ reflexive r2 ==> r1 RSUBSET r2 ⨾ r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_minus_transitive:
  transitive r ==>
  (r1 ⨾ r2) RMINUS r RSUBSET
  ((r1 RMINUS r) ⨾ r2) RUNION ((r1 RINTER r) ⨾ (r2 RMINUS r))
Proof
  xsimp []
  \\ metis_tac []
QED

(* - rsubset --------------------------------------------------------------- *)

Theorem rsubset_refl[simp]:
  r RSUBSET r
Proof
  xsimp []
QED

Theorem rsubset_trans:
  !r2. r1 RSUBSET r2 /\ r2 RSUBSET r3 ==> r1 RSUBSET r3
Proof
  xsimp []
QED

Theorem rc_rsubset:
  r1 RSUBSET r2 /\ reflexive r2 ==> RC r1 RSUBSET r2
Proof
  xrw [rc_runion]
  \\ simp []
QED

Theorem tc_rsubset:
  r1 RSUBSET r2 /\ transitive r2 ==> TC r1 RSUBSET r2
Proof
  xsimp []
  \\ strip_tac
  \\ ho_match_mp_tac relationTheory.TC_INDUCT
  \\ metis_tac []
QED

Theorem rtc_rsubset:
  r1 RSUBSET r2 /\ transitive r2 /\ reflexive r2 ==> RTC r1 RSUBSET r2
Proof
  xsimp []
  \\ strip_tac
  \\ ho_match_mp_tac relationTheory.RTC_INDUCT
  \\ metis_tac []
QED

Theorem rsubset_rc:
  r1 RSUBSET r2 ==> r1 RSUBSET RC r2
Proof
  xsimp [rc_runion]
QED

Theorem rsubset_tc:
  r1 RSUBSET r2 ==> r1 RSUBSET TC r2
Proof
  xsimp [Once relationTheory.TC_CASES1]
QED

Theorem rsubset_rtc:
  r1 RSUBSET r2 ==> r1 RSUBSET RTC r2
Proof
  xrw []
QED

Theorem rsubset_rrange:
  r1 RSUBSET r2 ==> RRANGE r1 SUBSET RRANGE r2
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem inclusion_ct_seq_eqv_l:
  TC (diag dom ⨾ r) RSUBSET diag dom ⨾ TC r
Proof
  xsimp []
  \\ ho_match_mp_tac relationTheory.TC_INDUCT
  \\ strip_tac
  >- xrw [Once relationTheory.TC_CASES1]
  \\ metis_tac [relationTheory.transitive_def, relationTheory.TC_TRANSITIVE]
QED

Theorem inclusion_ct_seq_eqv_r:
  TC (r ⨾ diag dom) RSUBSET TC r ⨾ diag dom
Proof
  xsimp []
  \\ ho_match_mp_tac relationTheory.TC_INDUCT
  \\ strip_tac
  >- xrw [Once relationTheory.TC_CASES2]
  \\ metis_tac [relationTheory.transitive_def, relationTheory.TC_TRANSITIVE]
QED

Theorem inclusion_minus_rel:
  r1 RMINUS r2 RSUBSET r1
Proof
  xsimp []
QED

(* - runion and rinter ----------------------------------------------------- *)

Theorem runion_empty_l:
  REMPTY RUNION r = r
Proof
  xsimp []
QED

Theorem runion_empty_r:
  r RUNION REMPTY = r
Proof
  xsimp []
QED

Theorem runion_rsubset:
  (r1 RUNION r2) RSUBSET r3 <=> r1 RSUBSET r3 /\ r2 RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem runion_rsubset_l:
  !r. r1 RSUBSET r /\ (r RUNION r2) RSUBSET r3  ==> (r1 RUNION r2) RSUBSET r3
Proof
  xrw []
  \\ simp []
QED

Theorem runion_rsubset_r:
  !r. r2 RSUBSET r /\ (r1 RUNION r) RSUBSET r3  ==> (r1 RUNION r2) RSUBSET r3
Proof
  xrw []
  \\ simp []
QED

Theorem rsubset_rinter:
  r1 RSUBSET (r2 RINTER r3) <=> r1 RSUBSET r2 /\ r1 RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_runion_l:
  (r1 RUNION r2) ⨾ r3 = r1 ⨾ r3 RUNION r2 ⨾ r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem seq_runion_r:
  r1 ⨾ (r2 RUNION r3) = r1 ⨾ r2 RUNION r1 ⨾ r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem runion_rinter_l:
  (r1 RUNION r2) RINTER r3 = (r1 RINTER r3) RUNION (r2 RINTER r3)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem runion_rinter_r:
  r1 RINTER (r2 RUNION r3) = (r1 RINTER r2) RUNION (r1 RINTER r3)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rsubset_runion:
  r1 RSUBSET r2 \/ r1 RSUBSET r3 ==> r1 RSUBSET (r2 RUNION r3)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rinter_rsubset:
  r1 RSUBSET r3 \/ r2 RSUBSET r3 ==> (r1 RINTER r2) RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rinter_rsubset_l:
  !r. r1 RSUBSET r /\ (r RINTER r2) RSUBSET r3 ==> (r1 RINTER r2) RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rinter_rsubset_r:
  !r. r2 RSUBSET r /\ (r1 RINTER r) RSUBSET r3 ==> (r1 RINTER r2) RSUBSET r3
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem cr_union_r:
  RC (r1 RUNION r2) = r1 RUNION RC r2
Proof
  xsimp [rc_runion]
  \\ metis_tac []
QED

Theorem runion_idem:
  r RUNION r = r
Proof
  xsimp []
QED

Theorem rminus_runion_l:
  (r1 RUNION r2) RMINUS r = (r1 RMINUS r) RUNION (r2 RMINUS r)
Proof
  xsimp []
  \\ metis_tac []
QED

(* - doms ------------------------------------------------------------------ *)

Theorem dom_dom:
  r = diag r1 ⨾ r ⨾ diag r2 ==> !x y. r x y ==> r1 x /\ r2 y
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem dom_l:
  r = diag r1 ⨾ r ⨾ diag r2 ==> r = diag r1 ⨾ r
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem dom_r:
  r = diag r1 ⨾ r ⨾ diag r2 ==> r = r ⨾ diag r2
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem doms_helper:
  (r RSUBSET s1 RCROSS s2) ==> (r = diag s1 ⨾ r ⨾ diag s2)
Proof
  xsimp []
  \\ metis_tac []
QED

(* - tc -------------------------------------------------------------------- *)

Theorem inclusion_t_t:
  r1 RSUBSET r2 ==> TC r1 RSUBSET TC r2
Proof
  xsimp []
  \\ metis_tac [relationTheory.TC_MONOTONE]
QED

Theorem inclusion_t_t2:
  r1 RSUBSET TC r2 ==> TC r1 RSUBSET TC r2
Proof
  xrw []
  \\ pop_assum mp_tac
  \\ qmatch_rename_tac `TC r1 x y ==> TC r2 x y`
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ match_mp_tac relationTheory.TC_INDUCT
  \\ rw []
  \\ metis_tac [relationTheory.TC_RULES]
QED

Theorem inclusion_rt_rt:
  r1 RSUBSET r2 ==> RTC r1 RSUBSET RTC r2
Proof
  xsimp []
  \\ metis_tac [relationTheory.RTC_MONOTONE]
QED

Theorem inclusion_rt_rt2:
  r1 RSUBSET RTC r2 ==> RTC r1 RSUBSET RTC r2
Proof
  xrw []
  \\ pop_assum mp_tac
  \\ qmatch_rename_tac `RTC r1 x y ==> RTC r2 x y`
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ match_mp_tac relationTheory.RTC_INDUCT
  \\ rw []
  \\ metis_tac [relationTheory.RTC_CASES_RTC_TWICE]
QED

Theorem seq_tc:
  r ⨾ TC r RSUBSET TC r
Proof
  xrw []
  \\ simp [Once relationTheory.TC_CASES1]
  \\ metis_tac []
QED

Theorem tc_seq:
  TC r ⨾ r RSUBSET TC r
Proof
  xrw []
  \\ simp [Once relationTheory.TC_CASES2]
  \\ metis_tac []
QED

Theorem seq_rtc:
  r ⨾ RTC r RSUBSET RTC r
Proof
  xrw []
  \\ simp [Once relationTheory.RTC_CASES1]
  \\ metis_tac []
QED

Theorem rtc_seq:
  RTC r ⨾ r RSUBSET RTC r
Proof
  xrw []
  \\ simp [Once relationTheory.RTC_CASES2]
  \\ metis_tac []
QED

Theorem tc_rtc:
  TC r RSUBSET RTC r
Proof
  xrw [relationTheory.TC_RTC]
QED

Theorem ct_begin:
  TC r = r ⨾ RTC r
Proof
  xrw [relationTheory.EXTEND_RTC_TC_EQN]
QED

Theorem ct_end:
  TC r = RTC r ⨾ r
Proof
  xrw [relationTheory.EXTEND_RTC_TC_RIGHT1_EQN]
QED

Theorem ct_step =
  rsubset_tc
  |> Q.INST [`r2` |-> `r1`]
  |> Q.INST [`r1` |-> `r`]
  |> SIMP_RULE std_ss [rsubset_refl]

Theorem rt_ct:
  RTC r ⨾ TC r = TC r
Proof
  xrw [relationTheory.EXTEND_RTC_TC_RIGHT1_EQN]
  \\ metis_tac [relationTheory.RTC_TRANSITIVE, relationTheory.RTC_REFLEXIVE,
                relationTheory.transitive_def, relationTheory.reflexive_def]
QED

Theorem RTC_TC_RTC:
  RTC (TC r) = RTC r
Proof
  simp [GSYM relationTheory.TC_RC_EQNS, relationTheory.TC_IDEM]
QED

Theorem tc_mon:
  !r2 r1. TC r1 a b /\ r1 RSUBSET r2 ==> TC r2 a b
Proof
  ntac 3 strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`b`, `b`)
  \\ Q.SPEC_TAC (`a`, `a`)
  \\ ho_match_mp_tac relationTheory.TC_INDUCT
  \\ rw [relationTheory.RSUBSET]
  \\ metis_tac [relationTheory.TC_RULES]
QED

Theorem acyclic_mon:
  !r2 r1. acyclic r2 /\ r1 RSUBSET r2 ==> acyclic r1
Proof
  rw [acyclic, relationTheory.irreflexive_def]
  \\ metis_tac [tc_mon]
QED

(* - relate strict_total_order to StrongLinearOrder ------------------------ *)

Theorem strict_total_order_UNIV:
  strict_total_order UNIV = StrongLinearOrder
Proof
  simp [FUN_EQ_THM, strict_total_order, is_total,
        relationTheory.StrongLinearOrder, relationTheory.trichotomous]
  \\ metis_tac []
QED

(* - restr_rel ------------------------------------------------------------- *)

Theorem restr_relEE:
  restr_rel d r = r RINTER d RCROSS d
Proof
  xsimp [restr_rel]
QED

Theorem lift_mori:
  r2 RSUBSET r3 ==> (lift r1 r2 RSUBSET lift r1 r3)
Proof
  xrw [lift]
  \\ metis_tac []
QED

Theorem irreflexive_restr:
  irreflexive r ==> irreflexive (restr_rel dom r)
Proof
  xsimp [restr_rel]
QED

Theorem transitive_restr:
  transitive r ==> transitive (restr_rel dom r)
Proof
  xsimp [restr_rel]
  \\ metis_tac []
QED

Theorem is_total_restr:
  is_total dom r ==> is_total dom (restr_rel dom r)
Proof
  simp [is_total, restr_rel, pred_setTheory.SPECIFICATION]
QED

(* - paths ----------------------------------------------------------------- *)

Theorem irreflexive_union:
  irreflexive (r1 RUNION r2) = (irreflexive r1 /\ irreflexive r2)
Proof
  xrw []
  \\ metis_tac []
QED

Theorem inclusion_t_ind_left:
  r1 RSUBSET r2 /\ r1 ⨾ r2 RSUBSET r2 ==> TC r1 RSUBSET r2
Proof
  xrw []
  \\ pop_assum mp_tac
  \\ qmatch_rename_tac `TC r1 x y ==> r2 x y`
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
  \\ metis_tac []
QED

Theorem inclusion_t_ind_right:
  r1 RSUBSET r2 /\ r2 ⨾ r1 RSUBSET r2 ==> TC r1 RSUBSET r2
Proof
  xrw []
  \\ pop_assum mp_tac
  \\ qmatch_rename_tac `TC r1 x y ==> r2 x y`
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ ho_match_mp_tac relationTheory.TC_INDUCT_RIGHT1
  \\ metis_tac []
QED

Theorem path_absorb1:
  r2 ⨾ r1 RSUBSET r2 ==>
  TC (r1 RUNION r2) = TC r1 RUNION TC r2 RUNION TC r1 ⨾ TC r2
Proof
  rw [relationTheory.EqIsBothRSUBSET]
  >- (
    match_mp_tac inclusion_t_ind_right
    \\ rw [runion_rsubset, rsubset_runion, rsubset_tc, seq_runion_l,
           seq_runion_r, tc_seq, inclusion_seq_mon]
    >- (
      match_mp_tac rsubset_runion
      \\ disj1_tac
      \\ match_mp_tac rsubset_runion
      \\ disj2_tac
      \\ xfs [ct_end, seq_assoc]
      \\ metis_tac []
    )
    \\ metis_tac [rsubset_runion, ct_end, seq_assoc, inclusion_seq_mon, tc_rtc,
                  rsubset_refl]
  )
  \\ rw [runion_rsubset]
  \\ TRY (match_mp_tac inclusion_seq_trans \\ simp [] \\ strip_tac)
  \\ match_mp_tac inclusion_t_t
  \\ xsimp []
QED

Theorem path_absorb2:
  r2 ⨾ r1 RSUBSET r1 ==>
  TC (r1 RUNION r2) = TC r1 RUNION TC r2 RUNION TC r1 ⨾ TC r2
Proof
  rw [relationTheory.EqIsBothRSUBSET]
  >- (
    match_mp_tac inclusion_t_ind_left
    \\ rw [runion_rsubset, rsubset_runion, rsubset_tc, seq_runion_l,
           seq_runion_r, tc_seq, inclusion_seq_mon, seq_tc, GSYM seq_assoc]
    >- (
      ntac 2 (match_mp_tac rsubset_runion \\ disj1_tac)
      \\ qspec_then `r2 ⨾ r1 ⨾ RTC r1` match_mp_tac
           (Q.GENL [`r2`, `r1`, `r3`] (SPEC_ALL rsubset_trans))
      \\ strip_tac
      >- (
        match_mp_tac inclusion_seq_mon
        \\ simp [GSYM ct_begin]
      )
      \\ simp [GSYM seq_assoc, ct_begin]
      \\ metis_tac [inclusion_seq_mon, rsubset_refl]
    )
    \\ match_mp_tac rsubset_runion
    \\ disj2_tac
    \\ simp [GSYM seq_assoc]
    \\ match_mp_tac inclusion_seq_mon
    \\ simp []
    \\ CONV_TAC (LAND_CONV (REWRITE_CONV [ct_begin]))
    \\ simp [GSYM seq_assoc, ct_begin]
    \\ metis_tac [inclusion_seq_mon, rsubset_refl]
  )
  \\ rw [runion_rsubset]
  \\ TRY (match_mp_tac inclusion_seq_trans \\ simp [] \\ strip_tac)
  \\ match_mp_tac inclusion_t_t
  \\ xsimp []
QED

Theorem path_absorb:
  (r2 ⨾ r1 RSUBSET r2 \/ r2 ⨾ r1 RSUBSET r1) ==>
  TC (r1 RUNION r2) = TC r1 RUNION TC r2 RUNION TC r1 ⨾ TC r2
Proof
  metis_tac [path_absorb1, path_absorb2]
QED

Theorem irreflexive_seqC:
  irreflexive (r1 ⨾ r2) = irreflexive (r2 ⨾ r1)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem clos_trans_rotl:
  TC (r1 ⨾ r2) = r1 ⨾ RTC (r2 ⨾ r1) ⨾ r2
Proof
  xrw []
  \\ eq_tac
  \\ rw []
  >- (
    pop_assum mp_tac
    \\ rename1 `TC (r1 ⨾ r2) x y`
    \\ Q.SPEC_TAC (`y`, `y`)
    \\ Q.SPEC_TAC (`x`, `x`)
    \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
    \\ rw []
    \\ xfs []
    \\ qmatch_assum_rename_tac `r1 x z`
    >- ntac 2 (qexists_tac `z` \\ simp [])
    \\ qexists_tac `z`
    \\ simp []
    \\ qmatch_assum_rename_tac `r2 w y`
    \\ qexists_tac `w`
    \\ simp []
    \\ simp [Once relationTheory.RTC_CASES1]
    \\ disj2_tac
    \\ xsimp []
    \\ metis_tac []
  )
  \\ qmatch_assum_rename_tac `r1 x y`
  \\ qmatch_assum_rename_tac `r2 v w`
  \\ qpat_x_assum `r1 x y` mp_tac
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ Q.SPEC_TAC (`w`, `w`)
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`v`, `v`)
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ ho_match_mp_tac relationTheory.RTC_INDUCT
  \\ rw []
  >- (
    xsimp [Once relationTheory.TC_CASES1]
    \\ metis_tac []
  )
  \\ xfs []
  \\ xsimp [Once relationTheory.TC_CASES1]
  \\ metis_tac []
QED

Theorem transitiveI:
  transitive r <=> ((r ⨾ r) RSUBSET r)
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem rtE:
  RTC r = (diag (K T) RUNION TC r)
Proof
  xsimp [relationTheory.RTC_CASES_TC]
QED

Theorem rt_idem:
  RTC r ⨾ RTC r = RTC r
Proof
  xsimp [GSYM relationTheory.RTC_CASES_RTC_TWICE]
QED

Theorem t_rt:
  TC r ⨾ RTC r = TC r
Proof
  xsimp [relationTheory.RTC_CASES_TC]
  \\ metis_tac [relationTheory.TC_RULES]
QED

Theorem inclusion_seq_rt:
  r1 RSUBSET RTC r3 /\ r2 RSUBSET RTC r3 ==> r1 ⨾ r2 RSUBSET RTC r3
Proof
  strip_tac
  \\ match_mp_tac inclusion_seq_trans
  \\ simp []
QED

Theorem path_ut:
  transitive r2 ==> RTC (r1 RUNION r2) = RTC r1 ⨾ RTC (r2 ⨾ TC r1) ⨾ RC r2
Proof
  rw [relationTheory.EqIsBothRSUBSET]
  >- (
    match_mp_tac (ONCE_REWRITE_RULE [CONJ_COMM] rtc_rsubset)
    \\ simp [GSYM CONJ_ASSOC]
    \\ strip_tac
    >- (
      rw [transitiveI]
      \\ rw [Once rc_runion, runion_rsubset, seq_runion_r,
             seq_runion_l, diag_T_seq_r]
      >- (
        simp [GSYM seq_assoc]
        \\ match_mp_tac inclusion_seq_mon
        \\ simp [Once (Q.INST [`r` |-> `r2 ⨾ TC r1`] rtE)]
        \\ simp [seq_runion_r, diag_T_seq_r, seq_runion_l, rt_idem]
        \\ rw [runion_rsubset, seq_assoc]
        \\ match_mp_tac inclusion_seq_mon
        \\ simp [Once ct_end, seq_assoc]
        \\ match_mp_tac rsubset_trans
        \\ qexists_tac `RTC (r2 ⨾ TC r1) ⨾ r2 ⨾ TC r1 ⨾ RTC (r2 ⨾ TC r1)`
        \\ strip_tac
        >- metis_tac [seq_assoc, t_rt, rsubset_refl]
        \\ match_mp_tac inclusion_seq_rt
        \\ simp [GSYM ct_begin, GSYM seq_assoc, tc_rtc]
      )
      \\ simp [seq_assoc]
      \\ match_mp_tac inclusion_seq_mon
      \\ simp []
      \\ CONV_TAC (PATH_CONV "lrrrl" (ONCE_REWRITE_CONV [rtE]))
      \\ simp [seq_runion_l, diag_T_seq_l]
      \\ rw [runion_rsubset, seq_runion_l, seq_runion_r]
      >- (
        CONV_TAC (PATH_CONV "lrrrl"
                    (ONCE_REWRITE_CONV [Q.INST [`r` |-> `r2 ⨾ TC r1`] rtE]))
        \\ simp [seq_runion_l, seq_runion_r, diag_T_seq_r, diag_T_seq_l]
        \\ rw [runion_rsubset]
        >- (
          simp [seq_assoc]
          \\ match_mp_tac inclusion_seq_mon
          \\ xrw [rc_runion]
          \\ xfs []
          \\ metis_tac []
        )
        \\ simp [GSYM seq_assoc]
        \\ match_mp_tac inclusion_seq_mon
        \\ simp [Q.INST [`r` |-> `r2 ⨾ TC r1`] ct_begin]
        \\ simp [seq_assoc]
        \\ match_mp_tac rsubset_trans
        \\ qexists_tac `RTC (r2 ⨾ TC r1) ⨾ r2 ⨾ TC r1 ⨾ RTC (r2 ⨾ TC r1)`
        \\ strip_tac
        >- (
          imp_res_tac transitiveI
          \\ xfs []
          \\ metis_tac []
        )
        \\ match_mp_tac inclusion_seq_rt
        \\ simp [GSYM seq_assoc, GSYM ct_begin, tc_rtc]
      )
      \\ simp [GSYM seq_assoc]
      \\ match_mp_tac inclusion_seq_mon
      \\ simp [seq_assoc]
      \\ match_mp_tac inclusion_seq_rt
      \\ simp [GSYM seq_assoc, GSYM ct_begin, tc_rtc]
    )
    \\ xrw []
    \\ metis_tac [relationTheory.RTC_RULES, relationTheory.RC_REFL,
                  relationTheory.RC_SUBSET]
  )
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac `RTC r1 ⨾ RTC (r2 ⨾ RTC r1) ⨾ RC r2`
  \\ strip_tac
  >- (
    rpt (match_mp_tac inclusion_seq_mon \\ simp [])
    \\ match_mp_tac inclusion_rt_rt
    \\ match_mp_tac inclusion_seq_mon
    \\ simp [tc_rtc]
  )
  \\ simp [GSYM seq_assoc]
  \\ match_mp_tac inclusion_seq_trans
  \\ rw []
  >- metis_tac [inclusion_seq_trans, inclusion_rt_rt, rsubset_runion,
                rsubset_refl, inclusion_rt_rt2, rsubset_rtc,
                relationTheory.RTC_TRANSITIVE]
  \\ xrw [rc_runion]
  \\ xsimp [relationTheory.RTC_RULES]
QED

Theorem rewrite_trans_seq_cr_l:
  transitive r ==> RC r ⨾ r RSUBSET r
Proof
  xrw [rc_runion]
  \\ metis_tac []
QED

Theorem rt_begin:
  RTC r = diag (K T) RUNION r ⨾ RTC r
Proof
  xrw []
  \\ metis_tac [relationTheory.RTC_CASES1]
QED

Theorem rt_end:
  RTC r = diag (K T) RUNION RTC r ⨾ r
Proof
  xrw []
  \\ metis_tac [relationTheory.RTC_CASES2]
QED

Theorem path_ut2:
  transitive r2 ==>
  TC (r1 RUNION r2) = TC r1 RUNION RTC r1 ⨾ RTC (r2 ⨾ TC r1) ⨾ r2 ⨾ RTC r1
Proof
  rw [relationTheory.EqIsBothRSUBSET]
  >- (
    simp [Once ct_end, path_ut, seq_runion_r]
    \\ reverse (rw [seq_assoc, runion_rsubset])
    >- (
      match_mp_tac rsubset_trans
      \\ qexists_tac `RTC r1 ⨾ RTC (r2 ⨾ TC r1) ⨾ r2`
      \\ strip_tac
      >- metis_tac [seq_assoc, rewrite_trans_seq_cr_l, inclusion_seq_mon,
                    rsubset_refl]
      \\ xrw [rc_runion]
      \\ metis_tac [relationTheory.RTC_REFL]
    )
    \\ rw [rc_runion, runion_rsubset, seq_runion_l, seq_runion_r, diag_T_seq_l]
    >- (
      simp [Once (Q.INST [`r` |-> `r2 ⨾ TC r1`] rt_end)]
      \\ rw [runion_rsubset, seq_runion_l, seq_runion_r, diag_T_seq_l,
             seq_assoc]
      >- metis_tac [ct_end, rsubset_runion, rsubset_refl]
      \\ match_mp_tac rsubset_trans
      \\ qexists_tac `RTC r1 ⨾ RTC (r2 ⨾ TC r1) ⨾ r2 ⨾ RTC r1 ⨾ r1`
      \\ strip_tac
      >- metis_tac [inclusion_seq_mon, rsubset_refl, tc_rtc]
      \\ simp [Once (GSYM ct_end)]
      \\ metis_tac [rsubset_runion, inclusion_seq_mon, tc_rtc, rsubset_refl]
    )
    \\ metis_tac [rsubset_runion, inclusion_seq_mon, tc_rtc, rsubset_refl,
                  rsubset_rtc]
  )
  \\ rw [runion_rsubset]
  >- metis_tac [inclusion_t_t, rsubset_runion, rsubset_refl]
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac `RTC r1 ⨾ RTC (r2 ⨾ RTC r1) ⨾ r2 ⨾ RTC r1`
  \\ strip_tac
  >- metis_tac [inclusion_rt_rt, inclusion_seq_mon, rsubset_refl, tc_rtc]
  \\ simp [Once (GSYM rt_ct)]
  \\ simp [GSYM ct_end]
  \\ match_mp_tac inclusion_seq_mon
  \\ strip_tac
  >- simp [inclusion_rt_rt, rsubset_runion]
  \\ match_mp_tac inclusion_t_t2
  \\ simp [ct_begin]
  \\ metis_tac [inclusion_seq_mon, inclusion_rt_rt, rsubset_runion,
                rsubset_refl]
QED

(* - acyclic --------------------------------------------------------------- *)

Theorem acyclic_seqC:
  acyclic (r1 ⨾ r2) = acyclic (r2 ⨾ r1)
Proof
  simp [acyclic, Once clos_trans_rotl, relationTheory.irreflexive_def]
  \\ xsimp [relationTheory.EXTEND_RTC_TC_RIGHT1_EQN]
  \\ metis_tac []
QED

Theorem irreflexive_inclusion:
  !r1 r2. r1 RSUBSET r2 /\ irreflexive r2 ==> irreflexive r1
Proof
  xsimp []
  \\ metis_tac []
QED

Theorem acyclic_absorb:
  (r2 ⨾ r1 RSUBSET r1 \/ r2 ⨾ r1 RSUBSET r2) ==>
  (acyclic (r1 RUNION r2) <=> acyclic r1 /\ acyclic r2)
Proof
  strip_tac
  \\ eq_tac
  \\ rpt strip_tac
  \\ TRY (
     qspec_then `r1 RUNION r2` match_mp_tac acyclic_mon
     \\ xfs []
     \\ FAIL_TAC ""
  )
  \\ fs [acyclic, path_absorb, irreflexive_union, Once irreflexive_seqC]
  >- (
    match_mp_tac irreflexive_inclusion
    \\ qexists_tac `TC r1`
    \\ simp []
    \\ CONV_TAC (RAND_CONV (REWRITE_CONV [ct_begin]))
    \\ CONV_TAC (LAND_CONV (RAND_CONV (REWRITE_CONV [ct_begin])))
    \\ simp [GSYM seq_assoc]
    \\ match_mp_tac inclusion_seq_mon
    \\ xfs []
    \\ rw []
    \\ pop_assum mp_tac
    \\ qmatch_rename_tac `r1 z y ==> r1 x y`
    \\ Q.SPEC_TAC (`y`, `y`)
    \\ pop_assum mp_tac
    \\ Q.SPEC_TAC (`z`, `z`)
    \\ Q.SPEC_TAC (`x`, `x`)
    \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
    \\ rw []
    \\ metis_tac []
  )
  >- (
    match_mp_tac irreflexive_inclusion
    \\ qexists_tac `TC r2`
    \\ simp []
    \\ CONV_TAC (RAND_CONV (REWRITE_CONV [ct_end]))
    \\ simp [Once ct_end]
    \\ simp [seq_assoc]
    \\ match_mp_tac inclusion_seq_mon
    \\ xfs []
    \\ rw []
    \\ qmatch_rename_tac `r2 x y`
    \\ qmatch_assum_rename_tac `r2 x z`
    \\ qpat_x_assum `r2 x z` mp_tac
    \\ Q.SPEC_TAC (`x`, `x`)
    \\ pop_assum mp_tac
    \\ Q.SPEC_TAC (`y`, `y`)
    \\ Q.SPEC_TAC (`z`, `z`)
    \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
    \\ rw []
    \\ metis_tac []
  )
QED

Theorem acyclic_disj:
  r ⨾ r = REMPTY ==> acyclic r
Proof
  xrw [acyclic, Once relationTheory.TC_CASES1, Once relationTheory.TC_CASES2]
  \\ metis_tac []
QED

Theorem ct_of_union_ct_l:
  TC (TC r1 RUNION r2) = TC (r1 RUNION r2)
Proof
  simp [relationTheory.EqIsBothRSUBSET]
  \\ strip_tac
  >- (
    match_mp_tac tc_rsubset
    \\ rw [runion_rsubset]
    \\ metis_tac [inclusion_t_t, rsubset_tc, rsubset_runion, rsubset_refl]
  )
  \\ match_mp_tac inclusion_t_t
  \\ rw [runion_rsubset]
  \\ metis_tac [inclusion_t_t, rsubset_tc, rsubset_runion, rsubset_refl]
QED

Theorem ct_of_union_ct_r:
  TC (r1 RUNION TC r2) = TC (r1 RUNION r2)
Proof
  simp [relationTheory.EqIsBothRSUBSET]
  \\ strip_tac
  >- (
    match_mp_tac tc_rsubset
    \\ rw [runion_rsubset]
    \\ metis_tac [inclusion_t_t, rsubset_tc, rsubset_runion, rsubset_refl]
  )
  \\ match_mp_tac inclusion_t_t
  \\ rw [runion_rsubset]
  \\ metis_tac [inclusion_t_t, rsubset_tc, rsubset_runion, rsubset_refl]
QED

Theorem acyclic_ut:
  transitive r2 ==>
  acyclic (r1 RUNION r2) =
  (acyclic r1 /\ irreflexive r2 /\ acyclic (r2 ⨾ TC r1))
Proof
  rw [acyclic, path_ut2, irreflexive_union, Once irreflexive_seqC, seq_assoc,
      rt_idem]
  \\ CONV_TAC (PATH_CONV "lrrrr" (REWRITE_CONV [rtE]))
  \\ simp [seq_runion_r, irreflexive_union, diag_T_seq_r, GSYM ct_end]
  \\ simp [Once irreflexive_seqC, Once rtE, seq_runion_r, irreflexive_union,
           diag_T_seq_r]
  \\ eq_tac
  \\ rw []
  \\ simp [Once ct_begin, seq_assoc]
  \\ qsuff_tac `irreflexive (r2 ⨾ TC r1 ⨾ RTC (r2 ⨾ TC r1))`
  >- (
    rw [relationTheory.irreflexive_def]
    \\ imp_res_tac transitiveI
    \\ xfs []
    \\ metis_tac []
  )
  \\ metis_tac [ct_begin, seq_assoc]
QED

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
