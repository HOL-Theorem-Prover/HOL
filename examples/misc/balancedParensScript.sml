open HolKernel boolLib bossLib lcsymtacs
     listTheory rich_listTheory arithmeticTheory

val _ = new_theory"balancedParens"

val _ = Datatype`alpha = a | b`; (* a = "(", b = ")"  *)

fun met h = metis_tac([APPEND,APPEND_ASSOC]@h)

val (S_rules,S_ind,S_cases) = Hol_reln`
  S [] ∧
  (S w ⇒ S ([a] ++ w ++ [b])) ∧
  (S w1 ∧ S w2 ⇒ S (w1++w2))`

val Snil = Q.store_thm("Snil[simp]",
  `S []`, rw[Once S_cases]);

val (T_rules,T_ind,T_cases) = Hol_reln`
  T [] ∧
  (T w1 ∧ T w2 ⇒ T (w1 ++ [a] ++ w2 ++ [b]))`

val TS = Q.store_thm("TS",
  `∀w. T w ⇒ S w`,
  Induct_on`T` >> met[S_rules])

val Tnil = Q.store_thm("Tnil[simp]",
  `T []`, rw[Once T_cases])

val Tapp = Q.store_thm("Tapp",
  `∀w2. T w2 ⇒ ∀w1. T w1 ⇒ T (w1 ++ w2)`,
  Induct_on`T` >> simp[T_rules])

val ST = Q.store_thm("ST",
  `∀w. S w ⇒ T w`,
  Induct_on`S` >> met[T_rules,Tapp])

val T_iff_S = Q.store_thm("T_iff_S",
  `T w ⇔ S w`, metis_tac[TS,ST]);

val balanced_def = Define`
  (balanced [] 0 ⇔ T) ∧
  (balanced (a::xs) n ⇔ balanced xs (SUC n)) ∧
  (balanced (b::xs) (SUC n) ⇔ balanced xs n) ∧
  (balanced _ _ ⇔ F)`
val _ = export_rewrites["balanced_def"]
val balanced_ind = theorem"balanced_ind"

val balanced_append = Q.store_thm("balanced_append",
  `∀w1 n1. balanced w1 n1 ⇒ ∀w2 n2. balanced w2 n2 ⇒ balanced (w1++w2) (n1+n2)`,
  ho_match_mp_tac balanced_ind >>
  rw[] >> fs[] >- (
    res_tac >> fsrw_tac[ARITH_ss][ADD1] ) >>
  REWRITE_TAC[ADD_CLAUSES] >>
  simp[])

val S_balanced = Q.store_thm("S_balanced",
  `∀w. S w ⇒ balanced w 0`,
  Induct_on`S` >>
  simp[] >> conj_tac >- (
    SUBST1_TAC(DECIDE``1 = 0+1``) >>
    rpt strip_tac >> irule balanced_append >>
    REWRITE_TAC[ONE] >> simp[] ) >>
  metis_tac[balanced_append,DECIDE``0+0=0``])

val Sins = Q.store_thm("Sins",
  `∀w. S w ⇒ ∀w1 w2. (w = w1 ++ w2) ⇒ S(w1++[a;b]++w2)`,
  Induct_on`S`>>
  rw[APPEND_EQ_APPEND,APPEND_EQ_CONS] >> fs[] >>
  met[S_rules])

val balanced_S = Q.store_thm("balanced_S",
  `∀w n. balanced w n ⇒ S (REPLICATE n a ++ w)`,
  ho_match_mp_tac balanced_ind >>
  simp[REPLICATE_GENLIST] >> rw[] >> fs[] >- (
    fs[GENLIST,SNOC_APPEND] >> met[] ) >>
  imp_res_tac Sins >>
  first_x_assum(qspec_then`w`mp_tac) >> simp[] >>
  simp[GENLIST,SNOC_APPEND] >> met[])

val balanced_iff_S = Q.store_thm("balanced_iff_S",
  `balanced w 0 ⇔ S w`,
  metis_tac[balanced_S,S_balanced,REPLICATE,APPEND])

val _ = export_theory()
