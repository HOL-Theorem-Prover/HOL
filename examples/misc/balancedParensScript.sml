Theory balancedParens
Ancestors
  list rich_list arithmetic

Datatype: alpha = a | b  (* a = "(", b = ")"  *)
End

fun met h = metis_tac([APPEND,APPEND_ASSOC]@h)

val (S_rules,S_ind,S_cases) = Hol_reln`
  S [] ∧
  (S w ⇒ S ([a] ++ w ++ [b])) ∧
  (S w1 ∧ S w2 ⇒ S (w1++w2))`

Theorem Snil[simp]:
   S []
Proof rw[Once S_cases]
QED

val (T_rules,T_ind,T_cases) = Hol_reln`
  T [] ∧
  (T w1 ∧ T w2 ⇒ T (w1 ++ [a] ++ w2 ++ [b]))`

Theorem TS:
   ∀w. T w ⇒ S w
Proof
  Induct_on`T` >> met[S_rules]
QED

Theorem Tnil[simp]:
   T []
Proof rw[Once T_cases]
QED

Theorem Tapp:
   ∀w2. T w2 ⇒ ∀w1. T w1 ⇒ T (w1 ++ w2)
Proof
  Induct_on`T` >> simp[T_rules]
QED

Theorem ST:
   ∀w. S w ⇒ T w
Proof
  Induct_on`S` >> met[T_rules,Tapp]
QED

Theorem T_iff_S:
   T w ⇔ S w
Proof metis_tac[TS,ST]
QED

Definition balanced_def:
  (balanced [] 0 ⇔ T) ∧
  (balanced (a::xs) n ⇔ balanced xs (SUC n)) ∧
  (balanced (b::xs) (SUC n) ⇔ balanced xs n) ∧
  (balanced _ _ ⇔ F)
End
val _ = export_rewrites["balanced_def"]
val balanced_ind = theorem"balanced_ind"

Theorem balanced_append:
   ∀w1 n1. balanced w1 n1 ⇒ ∀w2 n2. balanced w2 n2 ⇒ balanced (w1++w2) (n1+n2)
Proof
  ho_match_mp_tac balanced_ind >>
  rw[] >> fs[] >- (
    res_tac >> fsrw_tac[ARITH_ss][ADD1] ) >>
  REWRITE_TAC[ADD_CLAUSES] >>
  simp[]
QED

Theorem S_balanced:
   ∀w. S w ⇒ balanced w 0
Proof
  Induct_on`S` >>
  simp[] >> conj_tac >- (
    SUBST1_TAC(DECIDE``1 = 0+1``) >>
    rpt strip_tac >> irule balanced_append >>
    REWRITE_TAC[ONE] >> simp[] ) >>
  metis_tac[balanced_append,DECIDE``0+0=0``]
QED

Theorem Sins:
   ∀w. S w ⇒ ∀w1 w2. (w = w1 ++ w2) ⇒ S(w1++[a;b]++w2)
Proof
  Induct_on`S`>>
  rw[APPEND_EQ_APPEND,APPEND_EQ_CONS] >> fs[] >>
  met[S_rules]
QED

Theorem balanced_S:
   ∀w n. balanced w n ⇒ S (REPLICATE n a ++ w)
Proof
  ho_match_mp_tac balanced_ind >>
  asm_simp_tac std_ss [REPLICATE_GENLIST] >> rw[] >> fs[]
  >- (fs[GENLIST,SNOC_APPEND] >> met[]) >>
  imp_res_tac Sins >>
  first_x_assum(qspec_then`w`mp_tac) >> simp[] >>
  simp[GENLIST,SNOC_APPEND] >> met[]
QED

Theorem balanced_iff_S:
   balanced w 0 ⇔ S w
Proof
  metis_tac[balanced_S,S_balanced,REPLICATE,APPEND]
QED
