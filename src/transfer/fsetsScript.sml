open HolKernel Parse boolLib bossLib;

open transferTheory finite_mapTheory pred_setTheory

val _ = new_theory "fsets";

Type fset[pp] = “:'a |-> unit”

Overload fIN = “\e (fs:'a fset). e IN FDOM fs”

Overload fUNION = “FUNION : 'a fset -> 'a fset -> 'a fset”

Overload fINSERT = “\e fs. fs |+ (e,())”

Definition FSET_def:
  FSET AB fs s <=> !a b. AB a b ==> (fIN a fs <=> b IN s)
End

Theorem fIN_IN:
  (AB ===> FSET AB ===> (=)) fIN (IN)
Proof
  simp[FUN_REL_def, FSET_def]
QED

Theorem fEMPTY_EMPTY:
  FSET AB FEMPTY EMPTY
Proof
  simp[FSET_def]
QED

Theorem fUNION_UNION:
  (FSET AB ===> FSET AB ===> FSET AB) fUNION (UNION)
Proof
  simp[FUN_REL_def, FSET_def] >> metis_tac[]
QED

Theorem fINSERT_INSERT:
  bi_unique AB ==>
  (AB ===> FSET AB ===> FSET AB) fINSERT (INSERT)
Proof
  simp[FUN_REL_def, FSET_def, bi_unique_def, left_unique_def,
       right_unique_def] >> metis_tac[]
QED

Theorem fupdate_correct:
  bi_unique AB ==>
  (FSET AB ===> PAIRU AB ===> FSET AB) $|+ (combin$C $INSERT)
Proof
  simp[FUN_REL_def, PAIRU_def, pairTheory.FORALL_PROD, FSET_def, bi_unique_def,
       left_unique_def, right_unique_def] >> metis_tac[]
QED

Overload fDELETE = “fdomsub : 'a fset -> 'a -> 'a fset”
Theorem fDELETE_DELETE:
  bi_unique AB ==>
  (FSET AB ===> AB ===> FSET AB) fDELETE (DELETE)
Proof
  simp[FUN_REL_def, FSET_def, bi_unique_def, left_unique_def,
       right_unique_def] >> metis_tac[]
QED

Overload toSet = “FDOM : 'a fset -> 'a set”
Theorem toSet_correct:
  (FSET AB ===> AB ===> (=)) toSet I
Proof
  simp[FUN_REL_def, FSET_def] >> simp[IN_DEF]
QED

Theorem bi_unique_FSET[simp]:
  bi_unique AB /\ bitotal AB ==> bi_unique (FSET AB)
Proof
  simp[bi_unique_def, FSET_def, left_unique_def, right_unique_def,
       bitotal_def, total_def, surj_def, pred_setTheory.EXTENSION, fmap_EXT] >>
  metis_tac[]
QED

Theorem KT_FINITE:
  surj AB /\ right_unique AB ==> (FSET AB ===> (=)) (K T) FINITE
Proof
  rw[FUN_REL_def, FSET_def, right_unique_def, total_def, surj_def] >>
  fs[SKOLEM_THM] >>
  ‘b = { e | fIN (f e) a }’
    by simp[pred_setTheory.EXTENSION] >>
  qabbrev_tac ‘a0 = { f e | e | fIN (f e) a /\ e IN b }’ >>
  ‘a0 SUBSET FDOM a’ by simp[SUBSET_DEF, Abbr‘a0’, PULL_EXISTS] >>
  ‘FINITE a0’ by metis_tac[SUBSET_FINITE, FDOM_FINITE] >>
  ‘a0 = IMAGE f b’ by simp[Abbr‘a0’, EXTENSION] >>
  ‘!e1 e2. f e1 = f e2 <=> e1 = e2’ by metis_tac[] >>
  metis_tac[INJECTIVE_IMAGE_FINITE]
QED

Theorem RRANGE_FSET:
  RRANGE (FSET AB) = { bset | FINITE { a | ?b. AB a b /\ b IN bset} /\
                              !a b b'. b IN bset /\ AB a b /\ AB a b' ==>
                                       b' IN bset }
Proof
  simp[FSET_def, relationTheory.RRANGE, Once FUN_EQ_THM] >>
  qx_gen_tac ‘bset’ >> eq_tac
  >- (disch_then (qx_choose_then ‘afm’ strip_assume_tac) >>
      ‘{ a | ?b. AB a b /\ b IN bset } = { a | (?b. AB a b) /\ fIN a afm }’
         by (simp[EXTENSION] >> metis_tac[]) >> pop_assum SUBST1_TAC >>
      conj_tac
      >- (irule SUBSET_FINITE >> qexists_tac ‘FDOM afm’ >> simp[SUBSET_DEF]) >>
      metis_tac[]) >>
  strip_tac >> qexists_tac ‘FUN_FMAP (K ()) {a | ?b. AB a b /\ b IN bset}’ >>
  simp[FUN_FMAP_DEF] >> metis_tac[]
QED

Theorem RRANGE_FSET_EQ[simp]:
  RRANGE (FSET (=)) = FINITE
Proof
  simp[RRANGE_FSET, Once FUN_EQ_THM]
QED

(* if not left-unique there could be an infinite number of alphas all
   mapping to the one beta, and then {alpha_1} on the left couldn't
   relate to {beta} because of all the other alphas that would have to
   also be in the set on the left
*)
Theorem total_FSET:
  left_unique AB ==> total (FSET AB)
Proof
  simp[total_def, left_unique_def] >> strip_tac >> qx_gen_tac ‘fs’ >>
  qexists_tac ‘{ b | ?a. AB a b /\ fIN a fs }’ >>
  simp[FSET_def, EXTENSION] >> metis_tac[]
QED

Theorem fset_ext:
  (fm1 : 'a fset = fm2) <=> FDOM fm1 = FDOM fm2
Proof
  simp[fmap_EXT]
QED

(* if there is no b for a1 and a2, then the finite-maps with a1 and a2 in their
   domains both relate to the empty set but are not equal *)
Theorem left_unique_FSET:
  total AB ==> left_unique (FSET AB)
Proof
  simp[left_unique_def, total_def] >> strip_tac >>
  qx_genl_tac [‘fm1’, ‘fm2’, ‘s’] >>
  rw[FSET_def, EXTENSION, fset_ext] >> metis_tac[]
QED

Theorem right_unique_FSET:
  surj AB ==> right_unique (FSET AB)
Proof
  simp[right_unique_def, surj_def] >> strip_tac >>
  qx_genl_tac [‘fm’, ‘s1’, ‘s2’] >>
  rw[FSET_def, EXTENSION] >> metis_tac[]
QED

val _ = export_theory();
