open HolKernel Parse boolLib bossLib;

val _ = new_theory "transfer";

(* uniqueness, which might also be termed injectivity *)
val right_unique_def = Define‘
  right_unique (R : 'a -> 'b -> bool) <=>
    !a b1 b2. R a b1 /\ R a b2 ==> (b1 = b2)’;

val left_unique_def = Define‘
  left_unique (R: 'a -> 'b -> bool) <=>
    !a1 a2 b. R a1 b /\ R a2 b ==> (a1 = a2)’;

val bi_unique_def = Define‘bi_unique R <=> left_unique R /\ right_unique R’;

(* totality or surjectivity *)
val total_def = Define‘total (R : 'a -> 'b -> bool) <=> !x:'a. ?y. R x y’;
val surj_def = Define‘surj (R : 'a -> 'b -> bool) <=> !y:'b. ?x. R x y’;
val bitotal_def = Define‘bitotal (R : 'a -> 'b -> bool) <=> total R /\ surj R’;

val _ =
    set_mapped_fixity {fixity = Infixr 490, term_name = "FUN_REL", tok = "===>"}

val FUN_REL_def = Define‘
  (AB ===> CD) (f : 'a -> 'c) (g : 'b -> 'd) <=>
    !a:'a b:'b. AB a b ==> CD (f a) (g b)
’;

val FUN_REL_COMB = Q.store_thm(
  "FUN_REL_COMB",
  ‘(AB ===> CD) f g /\ AB a b ==> CD (f a) (g b)’,
  simp[FUN_REL_def]);

val FUN_REL_ABS = Q.store_thm(
  "FUN_REL_ABS",
  ‘(!a b. AB a b ==> CD (f a) (g b)) ==>
   (AB ===> CD) (\a. f a) (\b. g b)’,
  simp[FUN_REL_def]);

val FUN_REL_EQ2 = Q.store_thm(
  "FUN_REL_EQ2[simp]",
  ‘((=) ===> (=)) = (=)’,
  simp[FUN_REL_def, FUN_EQ_THM]);

val PAIR_REL_def = Define‘PAIR_REL AB CD (a,c) (b,d) <=> AB a b /\ CD c d’;
val _ =
    set_mapped_fixity {fixity = Infixr 601, term_name = "PAIR_REL", tok = "###"}

val _ = export_theory();
