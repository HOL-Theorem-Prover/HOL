(* HolRefute by case study: de Bruijn substitution, adapted from Isabelle's
   Manual_Nits.thy section 2.10. *)

Theory refuteSubst
Libs
  Refute

Datatype:
  tm = V num | Lam tm | App tm tm
End

Definition lift_def:
  lift (V j) k = V (if j < k then j else j + 1) /\
  lift (Lam t) k = Lam (lift t (k + 1)) /\
  lift (App t u) k = App (lift t k) (lift u k)
End

Definition loose_def:
  (loose (V j) k <=> k <= j) /\
  (loose (Lam t) k <=> loose t (SUC k)) /\
  (loose (App t u) k <=> loose t k \/ loose u k)
End

Definition subst0_def:
  subst0 s (V j) = s j /\
  subst0 s (Lam t) =
    Lam (subst0 (\n. case n of
                       0 => V 0
                     | SUC m => lift (s m) 1) t) /\
  subst0 s (App t u) = App (subst0 s t) (subst0 s u)
End

Definition subst_def:
  subst s (V j) = s j /\
  subst s (Lam t) =
    Lam (subst (\n. case n of
                      0 => V 0
                    | SUC m => lift (s m) 0) t) /\
  subst s (App t u) = App (subst s t) (subst s u)
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem closed_terms_are_fixed_by_substitution:
  ~loose t 0 ==> subst0 s t = t
Proof
  NARROWING_TAC >> cheat
QED

Theorem lifted_substitution_is_identity_below[local]:
  (!j. j < k ==> s j = V j) ==>
  !j. j < SUC k ==>
      (case j of
         0 => V 0
       | SUC m => lift (s m) 0) = V j
Proof
  strip_tac >>
  gen_tac >>
  Cases_on `j` >>
  simp [lift_def]
QED

Theorem subst_below[local]:
  !t k s. (!j. j < k ==> s j = V j) /\ ~loose t k ==>
          subst s t = t
Proof
  Induct
  >- simp [loose_def, subst_def]
  >- (simp [loose_def, subst_def] >>
      rpt strip_tac >>
      first_x_assum irule >>
      qexists `SUC k` >>
      conj_tac
      >- metis_tac [lifted_substitution_is_identity_below]
      >> gvs [])
  >> simp [loose_def, subst_def] >>
  metis_tac []
QED

Theorem substitution_fixes_closed_terms:
  ~loose t 0 ==> subst s t = t
Proof
  REFUTE_TAC >>
  strip_tac >>
  irule subst_below >>
  qexists `0` >>
  simp []
QED
