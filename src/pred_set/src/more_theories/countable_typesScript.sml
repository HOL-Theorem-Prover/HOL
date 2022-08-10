open HolKernel bossLib boolTheory pred_setTheory;

open Tactic Tactical;

val _ = new_theory "countable_types";

Theorem unit_countable:
  countable (UNIV : unit set)
Proof
  simp [countable_def, INJ_DEF]
QED

Theorem list_countable:
  countable Lset <=> countable (BIGUNION (IMAGE set Lset))
Proof
  EQ_TAC \\ rw []
  >- (
    irule bigunion_countable
    \\ simp [PULL_EXISTS, image_countable, finite_countable]
  )
  \\ qspec_then `IMAGE (\n. {xs | LENGTH xs = n /\
        EVERY (\x. x IN BIGUNION (IMAGE set Lset)) xs}) UNIV`
    mp_tac bigunion_countable
  \\ simp []
  \\ reverse impl_tac
  >- (
    rw [] \\ drule_then irule subset_countable
    \\ simp [SUBSET_DEF, PULL_EXISTS, listTheory.EVERY_MEM]
    \\ metis_tac []
  )
  \\ simp [PULL_EXISTS]
  \\ Induct
  \\ simp []
  \\ csimp []
  \\ dxrule_then dxrule cross_countable
  \\ rw []
  \\ qspec_then `\xs. (TL xs, HD xs)` irule inj_countable
  \\ first_assum (irule_at Any)
  \\ simp [INJ_IFF, listTheory.LENGTH_CONS, PULL_EXISTS]
  \\ metis_tac []
QED

Theorem countable_split:
  ! (X : 'a set) (f : 'a -> (num list # 'a list)) (m : 'a -> num).
  INJ f X UNIV /\
  (!x y. x IN X /\ MEM y (SND (f x)) ==> y IN X /\ m y < m x)
  ==>
  countable X
Proof
  rw []
  \\ qspec_then `IMAGE (\n. {x | m x < n /\ x IN X}) UNIV`
    mp_tac bigunion_countable
  \\ simp []
  \\ impl_tac
  >- (
    simp [PULL_EXISTS]
    \\ Induct
    \\ simp []
    \\ qspec_then `f` irule inj_countable
    \\ qexists_tac `f`
    \\ qexists_tac `UNIV CROSS {xs | EVERY (\x. m x < n /\ x IN X) xs}`
    \\ irule_at Any cross_countable
    \\ simp [list_countable]
    \\ drule_then (irule_at Any) subset_countable
    \\ fs [SUBSET_DEF, PULL_EXISTS, INJ_DEF, listTheory.EVERY_MEM]
    \\ rw []
    \\ res_tac
    \\ simp []
  )
  >- (
    rw []
    \\ drule_then irule subset_countable
    \\ simp [SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac [prim_recTheory.LESS_SUC_REFL]
  )
QED

val _ = export_theory ();

