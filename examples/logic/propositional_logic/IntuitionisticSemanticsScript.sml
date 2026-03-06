Theory IntuitionisticSemantics
Ancestors
  ipropSyntax

Datatype:
  model = <| worlds : num set ;
             rel : num -> num -> bool ;
             valn : num -> string -> bool
          |>
End

Definition isModel_def:
  isModel M ⇔
    (∀w1 w2. w1 ∈ M.worlds ∧ M.rel w1 w2 ⇒ w2 ∈ M.worlds) ∧
    (* partial order *)
    (∀w. w ∈ M.worlds ⇒ M.rel w w) ∧
    (∀w1 w2 w3. w1 ∈ M.worlds ∧ w2 ∈ M.worlds ∧ w3 ∈ M.worlds ⇒
                M.rel w1 w2 ∧ M.rel w2 w3 ⇒ M.rel w1 w3) ∧
    (∀w1 w2. w1 ∈ M.worlds ∧ w2 ∈ M.worlds ∧ M.rel w1 w2 ∧ M.rel w2 w1 ⇒
             w1 = w2) ∧
    (* valn monotone *)
    ∀u v p. u ∈ M.worlds ∧ v ∈ M.worlds ∧ M.rel u v ∧ M.valn u p ⇒ M.valn v p
End

Definition models_def:
  (models M w (a ∧ⁱ b) ⇔
     w ∈ M.worlds ∧ models M w a ∧ models M w b) ∧
  (models M w (a ⇒ⁱ b) ⇔
     w ∈ M.worlds ∧ ∀w'. M.rel w w' ∧ models M w' a ⇒ models M w' b) ∧
  (models M w (a ∨ⁱ b) ⇔
     w ∈ M.worlds ∧ (models M w a ∨ models M w b)) ∧
  (models M w ⊥ⁱ ⇔ F) ∧
  (models M w (IVar s) ⇔ M.valn w s)
End

Theorem models_monotone:
  isModel M ∧ w ∈ M.worlds ∧ M.rel w w' ∧ models M w ϕ ⇒
  models M w' ϕ
Proof
  Cases_on ‘isModel M’ >> simp[] >>
  Induct_on ‘ϕ’ >> simp[models_def] >> rw[] >> gvs[] >>
  metis_tac[isModel_def]
QED

Definition valid_def:
  valid ϕ ⇔ ∀M w. isModel M ∧ w ∈ M.worlds ⇒ models M w ϕ
End
