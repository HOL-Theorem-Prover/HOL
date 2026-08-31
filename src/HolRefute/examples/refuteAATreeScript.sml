(* HolRefute by case study: AA trees, adapted from Isabelle's
   Manual_Nits.thy section 3.2. *)

Theory refuteAATree
Ancestors
  list
Libs
  Refute

Datatype:
  aatree = ATip | ANode num num aatree aatree
End

Definition alevel_def:
  alevel ATip = 0 /\
  alevel (ANode x k l r) = k
End

Definition aleft_def:
  aleft ATip = ATip /\
  aleft (ANode x k l r) = l
End

Definition aright_def:
  aright ATip = ATip /\
  aright (ANode x k l r) = r
End

Definition aelems_def:
  aelems ATip = [] /\
  aelems (ANode x k l r) = aelems l ++ [x] ++ aelems r
End

Definition awf_def:
  awf ATip = T /\
  awf (ANode x k l r) =
    if l = ATip then
      k = 1 /\
      (r = ATip \/
       (alevel r = 1 /\ aleft r = ATip /\ aright r = ATip))
    else
      awf l /\ awf r /\ r <> ATip /\ alevel l < k /\
      alevel r <= k /\ alevel (aright r) < k
End

Definition askew_def:
  askew ATip = ATip /\
  askew (ANode x k l r) =
    case l of
      ATip => ANode x k l r
    | ANode y j ll lr =>
        if j = k then ANode y j ll (ANode x k lr r)
        else ANode x k l r
End

Definition asplit_def:
  asplit ATip = ATip /\
  asplit (ANode x k l r) =
    case r of
      ATip => ANode x k l r
    | ANode y j rl rr =>
        if alevel rr = k then ANode y (k + 1) (ANode x k l rl) rr
        else ANode x k l r
End

Definition ains0_def:
  ains0 x ATip = ANode x 1 ATip ATip /\
  ains0 x (ANode y k l r) =
    ANode y k (if x < y then ains0 x l else l)
              (if y < x then ains0 x r else r)
End

Definition ains_def:
  ains x ATip = ANode x 1 ATip ATip /\
  ains x (ANode y k l r) =
    asplit (askew (ANode y k (if x < y then ains x l else l)
                             (if y < x then ains x r else r)))
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem inserting_without_rebalancing_preserves_wellformedness:
  awf t ==> awf (ains0 x t)
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem askew_elems[local]:
  aelems (askew t) = aelems t
Proof
  Cases_on `t`
  >- rw [askew_def, aelems_def]
  >> Cases_on `a` >> rw [askew_def, aelems_def, APPEND_ASSOC]
QED

Theorem asplit_elems[local]:
  aelems (asplit t) = aelems t
Proof
  Cases_on `t`
  >- rw [asplit_def, aelems_def]
  >> Cases_on `a0` >> rw [asplit_def, aelems_def, APPEND_ASSOC]
QED

Theorem wellformed_trees_need_no_skew:
  awf t ==> askew t = t
Proof
  QUICKCHECK_TAC >>
  Cases_on `t`
  >- rw [awf_def, askew_def]
  >> Cases_on `a`
  >- rw [awf_def, askew_def]
  >> rw [awf_def, askew_def, alevel_def] >> gvs []
QED

Theorem wellformed_trees_need_no_split:
  awf t ==> asplit t = t
Proof
  QUICKCHECK_TAC >>
  Cases_on `t`
  >- rw [awf_def, asplit_def]
  >> Cases_on `a0`
  >- rw [asplit_def]
  >> Cases_on `a`
  >- (rw [awf_def, asplit_def, alevel_def, aleft_def,
          aright_def] >> gvs [])
  >> rw [awf_def, asplit_def, alevel_def, aright_def] >> gvs []
QED

Theorem the_fixed_insert_inserts:
  MEM y (aelems (ains x t)) <=> y = x \/ MEM y (aelems t)
Proof
  QUICKCHECK_TAC >>
  Induct_on `t`
  >- rw [ains_def, askew_elems, asplit_elems, aelems_def]
  >> rw [ains_def, askew_elems, asplit_elems, aelems_def,
         MEM_APPEND]
  >- simp [DISJ_ASSOC]
  >- tautLib.TAUT_TAC
  >> `x = n0` by
       (irule arithmeticTheory.LESS_EQUAL_ANTISYM >>
        gvs [arithmeticTheory.NOT_LESS])
  >> gvs [] >> tautLib.TAUT_TAC
QED

Theorem the_fixed_insert_preserves_the_level:
  alevel (ains x t) = alevel t
Proof
  REFUTE_TAC >> cheat
QED

(* QUICKCHECK_TAC finds no counterexample to the claim that ains preserves
   awf.  This diagnostic is not a proof: a full proof needs strengthened
   level and shape invariants for the intermediate skew and split steps,
   which would dominate this counterexample-focused example. *)
