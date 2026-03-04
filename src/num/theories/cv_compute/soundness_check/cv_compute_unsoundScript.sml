Theory cv_compute_unsound[bare]
Ancestors
  cv num arithmetic
Libs
  HolKernel Parse boolLib Q[qualified]

val bad_cv_fst_def = Prim_rec.new_recursive_definition {
  name = "bad_cv_fst_def",
  rec_axiom = cv_Axiom,
  def = “bad_cv_fst (cv$Num _) = cv$Num 0 /\
         bad_cv_fst (cv$Pair p q) = if p = q then p else q”
}

Theorem bad_cv_fst2:
  bad_cv_fst (cv$Num m) = cv$Num 0
Proof
  rewrite_tac[bad_cv_fst_def]
QED

Theorem bad_cv_fst1_lemma:
  p = q ==>
  bad_cv_fst (cv$Pair p q) = p
Proof
  strip_tac >> asm_rewrite_tac[bad_cv_fst_def]
QED

(* Define g so that g x y distinguishes equal from unequal args *)
val g_def = new_definition("g_def",
  “g (x:cv) (y:cv) = cv_if (cv_eq x y) (cv$Num 1) (cv$Num 0)”);

(* Prove the restricted equation: g2 x x = Num 1 *)
(* Since cv_eq x x = Num 1 and cv_if (Num 1) (Num 1) (Num 0) = Num 1 *)
Theorem g_xx:
  g x x = cv$Num 1
Proof
  REWRITE_TAC[g_def, cv_eq_def, cv_if_def]
QED
