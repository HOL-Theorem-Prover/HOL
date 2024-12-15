open HolKernel boolLib cvTheory numTheory arithmeticTheory

val _ = new_theory "cv_compute_unsound";

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

val _ = export_theory();
