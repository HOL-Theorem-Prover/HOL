open HolKernel boolLib bossLib Parse dep_rewrite
     pairTheory pred_setTheory listTheory helperListTheory bagTheory ringTheory
     gbagTheory polynomialTheory polyWeakTheory polyRingTheory polyEvalTheory

val _ = new_theory"multipoly"

(* stuff that should be moved *)

open monoidTheory groupTheory helperSetTheory

Theorem ring_mult_lsum:
  Ring r /\ c IN r.carrier ==>
  !b. FINITE_BAG b ==> SET_OF_BAG b SUBSET r.carrier ==>
      r.prod.op (GBAG r.sum b) c =
      GBAG r.sum (BAG_IMAGE (\x. r.prod.op x c) b)
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ rpt strip_tac
  \\ fs[SET_OF_BAG_INSERT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def] )
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ring_mult_ladd]
  \\ simp[]
  \\ conj_tac
  >- (
    `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ irule EQ_SYM
  \\ irule GITBAG_GBAG
  \\ simp[]
QED

Theorem ring_mult_rsum:
  Ring r /\ c IN r.carrier ==>
  !b. FINITE_BAG b ==> SET_OF_BAG b SUBSET r.carrier ==>
      r.prod.op c (GBAG r.sum b) =
      GBAG r.sum (BAG_IMAGE (\x. r.prod.op c x) b)
Proof
  rpt strip_tac
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum b * c`
  \\ `AbelianMonoid r.sum`
  by metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ `GBAG r.sum b IN r.carrier`
  by (
    `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ conj_tac >- metis_tac[ring_mult_comm]
  \\ DEP_REWRITE_TAC[MP_CANON ring_mult_lsum]
  \\ simp[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[]
  \\ fs[SUBSET_DEF]
  \\ metis_tac[ring_mult_comm]
QED

Theorem ring_mult_sum_image:
  Ring r /\ FINITE s1 /\ FINITE s2 /\ IMAGE f1 s1 SUBSET r.carrier /\ IMAGE f2 s2 SUBSET r.carrier ==>
  r.prod.op (GBAG r.sum (BAG_IMAGE f1 (BAG_OF_SET s1)))
            (GBAG r.sum (BAG_IMAGE f2 (BAG_OF_SET s2))) =
  GBAG r.sum (BAG_IMAGE (\(x1,x2). r.prod.op (f1 x1) (f2 x2)) (BAG_OF_SET (s1 CROSS s2)))
Proof
  strip_tac
  \\ ntac 3 (pop_assum mp_tac)
  \\ qid_spec_tac`s2`
  \\ pop_assum mp_tac
  \\ qid_spec_tac`s1`
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ `AbelianMonoid r.sum`
  by metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ rw[]
  >- (
    irule ring_mult_lzero
    \\ simp[]
    \\ `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ simp[Once CROSS_INSERT_LEFT]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
  \\ conj_tac >- simp[IN_DISJOINT]
  \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
  \\ simp[]
  \\ DEP_REWRITE_TAC[GBAG_UNION]
  \\ simp[]
  \\ conj_asm1_tac
  >- fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ring_mult_ladd]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    conj_tac
    \\ `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[MP_CANON ring_mult_rsum]
  \\ simp[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule EQ_TRANS
  \\ qexists_tac`BAG_IMAGE ((λ(x1,x2). f1 x1 * f2 x2) o (λx2. (e,x2))) (BAG_OF_SET s2)`
  \\ conj_tac
  >- (
    irule BAG_IMAGE_CONG
    \\ simp[FORALL_PROD] )
  \\ simp[BAG_IMAGE_COMPOSE]
  \\ irule BAG_IMAGE_CONG
  \\ simp[]
  \\ DEP_REWRITE_TAC[GSYM BAG_OF_SET_IMAGE_INJ]
  \\ simp[]
  \\ simp[Once EXTENSION, FORALL_PROD]
QED

Theorem poly_eval_GBAG:
  Ring r ==>
  !p. weak p /\ x IN r.carrier ==>
     poly_eval r p x = GBAG r.sum (BAG_IMAGE (\n. r.prod.op (EL n p) (r.prod.exp x n))
                                              (BAG_OF_SET (count (LENGTH p))))
Proof
  strip_tac
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[] \\ fs[weak_snoc]
  \\ simp[weak_eval_snoc]
  \\ rw[COUNT_SUC]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ simp[]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[EL_LENGTH_SNOC]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ conj_asm1_tac
  >- fs[SUBSET_DEF, PULL_EXISTS, EL_SNOC, weak_every_mem, MEM_EL]
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`a + b = b' + a`
  \\ irule EQ_TRANS
  \\ qexists_tac`a + b'`
  \\ reverse conj_tac >- (
    imp_res_tac AbelianMonoid_def
    \\ first_x_assum irule
    \\ conj_tac >- simp[Abbr`a`]
    \\ qunabbrev_tac`b'`
    \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ fs[weak_every_mem, MEM_EL, PULL_EXISTS] )
  \\ AP_TERM_TAC
  \\ unabbrev_all_tac
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[EL_SNOC]
QED

(* end of moving stuff *)

(* A multivariate polynomial is represented as a function assigning each
monomial to a coefficient. A monomial is a bag of indeterminates, representing
a product of the indeterminates each exponentiated by their multiplicity. *)

Type mpoly = ``:'v bag -> 'c``;

Definition rrestrict_def:
  rrestrict r v = if v IN r.carrier then v else r.sum.id
End

Theorem rrestrict_in_carrier[simp]:
  Ring r ==> rrestrict r (p m) ∈ r.carrier
Proof
  rw[rrestrict_def]
QED

Theorem rrestrict_rrestrict[simp]:
  rrestrict r (rrestrict r v) = rrestrict r v
Proof
  rw[rrestrict_def] \\ fs[]
QED

Theorem rrestrict_zero[simp]:
  Ring r ==> rrestrict r r.sum.id = r.sum.id
Proof
  rw[rrestrict_def]
QED

(* The monomials of a polynomial (with coefficients in a ring r) are those
whose coefficients are not zero. *)

Definition monomials_def:
  monomials r p = { t | rrestrict r (p t) <> r.sum.id }
End

(* We only consider polynomials with finitely many terms, and where each term
has finitely many indeterminates. *)

Definition finite_mpoly_def:
  finite_mpoly r p <=>
    FINITE (monomials r p) ∧ (∀m. m ∈ monomials r p ⇒ FINITE_BAG m)
End

(* The support is the set of indeterminates that appear in the polynomial. *)

Definition support_def:
  support r p = BIGUNION (IMAGE SET_OF_BAG (monomials r p))
End

(* The function associated with the polynomial, assuming a mapping from
   indeterminates to the ring of coefficients. *)

Definition mpoly_eval_def:
  mpoly_eval r f p = GBAG r.sum
    (BAG_IMAGE (λt. r.prod.op (rrestrict r (p t)) (GBAG r.prod (BAG_IMAGE f t)))
      (BAG_OF_SET (monomials r p)))
End

(* A multivariate polynomial with a single variable corresponds to a univariate
polynomial. *)

Theorem empty_monomials:
  monomials r p = {} <=> (!x. p x IN r.carrier ==> p x = r.sum.id)
Proof
  rw[monomials_def, Once EXTENSION, rrestrict_def]
  \\ rw[EQ_IMP_THM] \\ metis_tac[]
QED

Theorem empty_support:
  support r p = {} <=> monomials r p SUBSET {{||}}
Proof
  rw[support_def, SUBSET_DEF, IMAGE_EQ_SING]
  \\ metis_tac[NOT_IN_EMPTY]
QED

Definition poly_of_mpoly_def:
  poly_of_mpoly r p =
    if support r p = {} then
    if rrestrict r (p {||}) = r.sum.id then [] else [rrestrict r (p {||})] else
    let v = @v. v IN support r p in
    GENLIST (\n. rrestrict r (p (\w. if w = v then n else 0)))
    (SUC (MAX_SET (IMAGE (\m. m v) (monomials r p))))
End

Theorem support_SING_monomial_form:
  support r p = {v} /\ m IN monomials r p ==>
  m = \x. if x = v then m v else 0
Proof
  rw[support_def]
  \\ fs[Once EXTENSION, PULL_EXISTS]
  \\ simp[Once FUN_EQ_THM] \\ rw[]
  \\ Cases_on`BAG_IN x m`
  \\ fs[BAG_IN, BAG_INN] \\ metis_tac[]
QED

Theorem weak_poly_of_mpoly:
  Ring r ==> weak (poly_of_mpoly r p)
Proof
  rw[weak_every_element, poly_of_mpoly_def, EVERY_GENLIST]
QED

Theorem poly_poly_of_mpoly:
  Ring r /\ FINITE (monomials r p) /\ support r p SUBSET {v} ==>
  poly (poly_of_mpoly r p)
Proof
  rw[poly_def_alt, weak_poly_of_mpoly]
  \\ fs[poly_of_mpoly_def] \\ rw[] \\ fs[]
  \\ fs[GENLIST_LAST]
  \\ `support r p = {v}`
  by ( simp[SET_EQ_SUBSET] \\ Cases_on`support r p` \\ fs[] )
  \\ gs[]
  \\ qmatch_asmsub_abbrev_tac`MAX_SET s`
  \\ Cases_on`s = {}` >- ( fs[Abbr`s`] \\ fs[support_def] )
  \\ `FINITE s` by simp[Abbr`s`]
  \\ `MAX_SET s ∈ s` by metis_tac[MAX_SET_DEF]
  \\ qmatch_asmsub_abbrev_tac`ms ∈ s`
  \\ fs[Abbr`s`]
  \\ qmatch_asmsub_abbrev_tac`rrestrict r (p m') = _`
  \\ `m = m'`
  by (
    imp_res_tac support_SING_monomial_form
    \\ simp[Abbr`m'`] )
  \\ fs[monomials_def]
QED

Definition mpoly_of_poly_def:
  mpoly_of_poly r v p m =
  if SET_OF_BAG m = {v} ∧ m v < LENGTH p
  then rrestrict r (EL (m v) p)
  else if m = {||} /\ 0 < LENGTH p then rrestrict r (EL 0 p)
  else r.sum.id
End

Theorem monomials_mpoly_of_poly:
  Ring r /\ poly p ==>
  monomials r (mpoly_of_poly r v p) =
  IMAGE (λn x. if x = v then n else 0)
  (count (LENGTH p) INTER { n | EL n p <> r.sum.id })
Proof
  rw[monomials_def, Once EXTENSION]
  \\ rw[rrestrict_def] \\ fs[mpoly_of_poly_def]
  \\ pop_assum mp_tac \\ rw[]
  \\ fs[poly_def_alt, SET_OF_BAG_SING]
  \\ rw[] \\ gs[]
  \\ fs[FUN_EQ_THM,EMPTY_BAG] \\ fs[PULL_EXISTS, weak_every_mem]
  \\ rw[rrestrict_def]
  >- metis_tac[]
  >- metis_tac[MEM_EL]
  >- metis_tac[MEM_EL, EL]
  >- metis_tac[MEM_EL, EL]
  >- (
    Cases_on`n < LENGTH p` \\ fs[]
    \\ reverse(Cases_on`n=0`) >- metis_tac[] \\ fs[]
    \\ rw[] \\ fs[])
QED

Theorem support_mpoly_of_poly:
  Ring r /\ poly p ==>
  support r (mpoly_of_poly r v p) = if LENGTH p <= 1 then {} else {v}
Proof
  rw[support_def, monomials_mpoly_of_poly]
  >- (
    Cases_on`p` \\ fs[]
    \\ Cases_on`t` \\ fs[]
    \\ simp[IMAGE_EQ_SING]
    \\ rw[EXTENSION, PULL_EXISTS]
    \\ disj2_tac
    \\ qexists_tac`0` \\ simp[]
    \\ rw[FUN_EQ_THM, EMPTY_BAG] \\ rw[] )
  \\ rw[Once EXTENSION, PULL_EXISTS]
  \\ rw[BAG_IN, BAG_INN]
  \\ Cases_on`x=v`\\ simp[]
  \\ fs[poly_def_alt] \\ rfs[]
  \\ Cases_on`p = []` \\ gs[]
  \\ Cases_on`p` \\ gs[]
  \\ Cases_on`t = []` \\ gs[]
  \\ imp_res_tac LAST_EL_CONS
  \\ qexists_tac`LENGTH t`
  \\ simp[]
  \\ Cases_on`t` \\ fs[]
QED

Theorem poly_of_mpoly_of_poly:
  Ring r ⇒
  ∀p. poly p ⇒ poly_of_mpoly r (mpoly_of_poly r v p) = p
Proof
  rw[]
  \\ simp[poly_of_mpoly_def]
  \\ simp[support_mpoly_of_poly]
  \\ Cases_on`LENGTH p ≤ 1` \\ simp[]
  >- (
    simp[mpoly_of_poly_def]
    \\ Cases_on`p` \\ gs[]
    \\ gs[rrestrict_def]
    \\ Cases_on`t` \\ gs[] )
  \\ simp[monomials_mpoly_of_poly]
  \\ simp[GSYM IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ qmatch_goalsub_abbrev_tac`MAX_SET s`
  \\ `LENGTH p - 1 ∈ s`
  by (
    simp[Abbr`s`]
    \\ fs[poly_def_alt]
    \\ Cases_on`p = []` \\ gs[]
    \\ imp_res_tac LAST_EL
    \\ gs[arithmeticTheory.PRE_SUB1] )
  \\ `FINITE s` by simp[Abbr`s`]
  \\ `LENGTH p - 1 ≤ MAX_SET s` by metis_tac[X_LE_MAX_SET]
  \\ `s <> {}` by (strip_tac \\ fs[])
  \\ `MAX_SET s ∈ s` by metis_tac[MAX_SET_DEF]
  \\ `MAX_SET s < LENGTH p` by fs[Abbr`s`]
  \\ `MAX_SET s = LENGTH p - 1` by gs[]
  \\ `0 < LENGTH p` by gs[]
  \\ simp[arithmeticTheory.ADD1]
  \\ simp[LIST_EQ_REWRITE]
  \\ qx_gen_tac`n` \\ strip_tac
  \\ simp[mpoly_of_poly_def]
  \\ simp[SET_OF_BAG_SING, Once FUN_EQ_THM]
  \\ Cases_on`n = 0`
  >- (
    simp[Once FUN_EQ_THM, EMPTY_BAG]
    \\ simp[rrestrict_def] \\ rw[]
    \\ gs[poly_def_alt, weak_every_mem]
    \\ Cases_on`p` \\ gs[] )
  \\ reverse IF_CASES_TAC
  >- ( fs[] \\ metis_tac[] )
  \\ simp[]
  \\ simp[rrestrict_def]
  \\ gs[poly_def_alt, weak_every_mem]
  \\ metis_tac[MEM_EL]
QED

Definition mpoly_def:
  mpoly r p <=> IMAGE p UNIV ⊆ r.carrier ∧ FINITE (monomials r p)
End

Theorem mpoly_of_poly_of_mpoly:
  Ring r ∧ mpoly r p ∧ support r p ⊆ {v} ⇒
  mpoly_of_poly r v (poly_of_mpoly r p) = p
Proof
  rw[mpoly_def]
  \\ simp[poly_of_mpoly_def]
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC
    >- (
      rw[mpoly_of_poly_def, Once FUN_EQ_THM]
      \\ fs[rrestrict_def, empty_support, SUBSET_DEF, PULL_EXISTS] \\ gs[]
      \\ gs[monomials_def, rrestrict_def]
      \\ metis_tac[] )
    \\ rw[mpoly_of_poly_def, Once FUN_EQ_THM]
    \\ fs[empty_support, SUBSET_DEF, PULL_EXISTS]
    \\ simp[SET_OF_BAG_SING]
    \\ rw[] \\ gs[EMPTY_BAG]
    \\ gs[FUN_EQ_THM, monomials_def, rrestrict_def]
    \\ metis_tac[] )
  \\ SELECT_ELIM_TAC
  \\ conj_tac >- metis_tac[pred_setTheory.MEMBER_NOT_EMPTY]
  \\ rpt strip_tac
  \\ `support r p = {v}`
  by (
    simp[SET_EQ_SUBSET]
    \\ fs[SUBSET_DEF]
    \\ metis_tac[] )
  \\ imp_res_tac support_SING_monomial_form
  \\ gs[SUBSET_DEF, PULL_EXISTS]
  \\ BasicProvers.VAR_EQ_TAC \\ gs[rrestrict_def]
  \\ rw[mpoly_of_poly_def, Once FUN_EQ_THM]
  \\ gs[rrestrict_def]
  \\ qmatch_goalsub_rename_tac`_ = p m`
  \\ Cases_on`m = {||}` \\ gs[]
  >- ( AP_TERM_TAC \\ simp[FUN_EQ_THM, EMPTY_BAG] )
  \\ reverse(Cases_on`m ∈ monomials r p`)
  >- (
    fs[monomials_def]
    \\ gs[rrestrict_def]
    \\ rw[]
    \\ fs[SET_OF_BAG_SING]
    \\ rw[] )
  \\ simp[SET_OF_BAG_SING]
  \\ qmatch_goalsub_abbrev_tac`MAX_SET s`
  \\ `m v ∈ s` by ( simp[Abbr`s`] \\ metis_tac[] )
  \\ `FINITE s` by simp[Abbr`s`]
  \\ `m v ≤ MAX_SET s` by metis_tac[X_LE_MAX_SET]
  \\ simp[]
  \\ res_tac
  \\ first_assum SUBST1_TAC
  \\ simp[FUN_EQ_THM]
  \\ rw[] \\ fs[]
  \\ first_x_assum(qspec_then`m v`mp_tac)
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ fs[FUN_EQ_THM, EMPTY_BAG]
QED

Theorem BIJ_poly_of_mpoly:
  Ring r ==>
  BIJ (poly_of_mpoly r)
    { p | mpoly r p ∧ support r p ⊆ {v} }
    { p | poly p }
Proof
  rw[BIJ_IFF_INV, mpoly_def]
  >- (irule poly_poly_of_mpoly \\ metis_tac[])
  \\ qexists_tac`mpoly_of_poly r v`
  \\ simp[support_mpoly_of_poly, monomials_mpoly_of_poly]
  \\ conj_tac >- (
    simp[SUBSET_DEF, PULL_EXISTS]
    \\ rw[mpoly_of_poly_def] \\ rw[] )
  \\ metis_tac[mpoly_of_poly_of_mpoly, poly_of_mpoly_of_poly, mpoly_def]
QED

Theorem eval_mpoly_of_poly:
  Ring r /\ poly p /\ f v IN r.carrier ==>
  mpoly_eval r f (mpoly_of_poly r v p) = poly_eval r p (f v)
Proof
  rw[mpoly_eval_def, monomials_mpoly_of_poly]
  \\ DEP_REWRITE_TAC[poly_eval_GBAG]
  \\ conj_tac >- fs[poly_def_alt]
  \\ irule GITBAG_CONG
  \\ simp[PULL_EXISTS, SUBSET_DEF]
  \\ `weak p` by imp_res_tac poly_def_alt
  \\ fs[weak_every_mem, MEM_EL, PULL_EXISTS]
  \\ `AbelianMonoid r.sum` by
  metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ simp[]
  \\ `∀n. BAG_IMAGE f (λx. if x = v then n else 0) = (λx. if x = f v then n else 0)`
  by (
    rw[BAG_IMAGE_DEF, BAG_FILTER_DEF]
    \\ simp[FUN_EQ_THM]
    \\ gen_tac
    \\ rewrite_tac[GSYM FINITE_SET_OF_BAG]
    \\ qmatch_goalsub_abbrev_tac`SET_OF_BAG b`
    \\ `SET_OF_BAG b ⊆ {v}`
    by (
      rw[SET_OF_BAG, Abbr`b`, SUBSET_DEF, BAG_IN, BAG_INN]
      \\ pop_assum mp_tac \\ rw[] )
    \\ `FINITE {v}` by simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[SUBSET_FINITE]
    \\ Cases_on`b = {||}` \\ gs[]
    >- ( fs[Abbr`b`, EMPTY_BAG, FUN_EQ_THM] \\ metis_tac[] )
    \\ `SET_OF_BAG b = {v}`
    by (
      simp[SET_EQ_SUBSET]
      \\ Cases_on`b` \\ fs[]
      \\ fs[SET_OF_BAG_INSERT] )
    \\ imp_res_tac SET_OF_BAG_SING_CARD
    \\ simp[Abbr`b`]
    \\ rw[] )
  \\ simp[]
  \\ `∀n. GBAG r.prod (λx. if x = f v then n else 0) = f v ** n`
  by (
    Induct \\ rw[]
    >- (
      qmatch_goalsub_abbrev_tac`GITBAG _ eb _ = _`
      \\ `eb = {||}` by simp[Abbr`eb`, FUN_EQ_THM, EMPTY_BAG]
      \\ rw[] )
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`GBAG _ bi`
    \\ qmatch_asmsub_abbrev_tac`GBAG _ b = _`
    \\ `bi = BAG_INSERT (f v) b`
    by (
      simp[BAG_INSERT, Abbr`bi`, FUN_EQ_THM]
      \\ rw[Abbr`b`] )
    \\ rw[]
    \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
    \\ simp[]
    \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
    \\ simp[]
    \\ `SET_OF_BAG b ⊆ {f v}`
    by (
      simp[SET_OF_BAG, Abbr`b`, SUBSET_DEF, BAG_IN, BAG_INN]
      \\ rw[] )
    \\ `FINITE {f v}` by simp[]
    \\ `FINITE_BAG b` by metis_tac[FINITE_SET_OF_BAG, SUBSET_FINITE]
    \\ fs[SUBSET_DEF]
    \\ metis_tac[Ring_def])
  \\ simp[]
  \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE f1 b1 _ = BAG_IMAGE f2 b2 _`
  \\ `∀n. BAG_IN n b2 ==> f2 n = f1 (λx. if x = v then n else 0)`
  by (
    simp[Abbr`b2`]
    \\ simp[Abbr`f1`, Abbr`f2`]
    \\ simp[mpoly_of_poly_def]
    \\ rpt strip_tac
    \\ simp[SET_OF_BAG_SING]
    \\ Cases_on`n = 0` \\ simp[]
    >- (
      rw[FUN_EQ_THM, EMPTY_BAG]
      \\ rw[rrestrict_def]
      \\ metis_tac[EL] )
    \\ rw[FUN_EQ_THM, EMPTY_BAG]
    \\ reverse(rw[rrestrict_def])
    >- (Cases_on`p` \\ fs[])
    \\ fs[]
    \\ first_x_assum(qspec_then`n`mp_tac)
    \\ simp[] )
  \\ simp[mpoly_of_poly_def, SET_OF_BAG_SING]
  \\ Cases_on`p = []` \\ simp[]
  \\ `0 < LENGTH p` by (Cases_on`p` \\ fs[])
  \\ simp[]
  \\ Cases_on`x = r.sum.id` \\ simp[]
  \\ reverse(Cases_on`∃n. f2 n = x ∧ n < LENGTH p`) \\ simp[]
  >- (
    strip_tac \\ fs[]
    \\ first_x_assum(qspec_then`n`mp_tac)
    \\ simp[Abbr`f2`]
    \\ BasicProvers.VAR_EQ_TAC
    \\ qmatch_goalsub_abbrev_tac`a * b <> a' * b`
    \\ `a = a'`
    by (
      simp[Abbr`a`, Abbr`a'`]
      \\ Cases_on`n = 0` \\ fs[]
      >- (
        simp[FUN_EQ_THM, EMPTY_BAG]
        \\ simp[rrestrict_def]
        \\ metis_tac[EL] )
      \\ simp[FUN_EQ_THM]
      \\ `0 < n` by simp[]
      \\ `rrestrict r (EL n p) = EL n p` by simp[rrestrict_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[] )
    \\ simp[] )
  \\ fs[]
  \\ BasicProvers.VAR_EQ_TAC
  \\ irule EQ_TRANS
  \\ qexists_tac`BAG_IMAGE (f1 o (λn x. if x = v then n else 0)) b2 (f2 n)`
  \\ reverse conj_tac
  >- ( AP_THM_TAC \\ irule BAG_IMAGE_CONG \\ simp[] )
  \\ `FINITE_BAG b1 ∧ FINITE_BAG b2` by simp[Abbr`b1`, Abbr`b2`]
  \\ simp[BAG_IMAGE_COMPOSE]
  \\ simp[Once BAG_IMAGE_DEF]
  \\ simp[Once BAG_IMAGE_DEF, SimpRHS]
  \\ AP_TERM_TAC
  \\ simp[BAG_FILTER_DEF]
  \\ simp[FUN_EQ_THM]
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE g`
  \\ simp[Abbr`b1`, BAG_OF_SET]
  \\ reverse(rw[])
  >- (
    rw[BAG_IMAGE_DEF, BCARD_0]
    \\ simp[BAG_FILTER_EQ_EMPTY]
    \\ simp[BAG_EVERY]
    \\ simp[Abbr`b2`] \\ fs[]
    \\ rw[]
    \\ strip_tac \\ rw[]
    \\ first_x_assum(qspec_then`e`mp_tac)
    \\ simp[]
    \\ fs[Abbr`f1`, mpoly_of_poly_def, Abbr`g`]
    \\ strip_tac \\ fs[]
    \\ qpat_x_assum`_ = f2 n`mp_tac
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ simp[rrestrict_def]
    \\ rw[]
    \\ fs[FUN_EQ_THM, EMPTY_BAG]
    \\ `e = 0` by metis_tac[]
    \\ fs[] )
  \\ simp[Abbr`b2`]
  \\ simp[BAG_IMAGE_DEF]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ DEP_REWRITE_TAC[BAG_CARD_BAG_OF_SET]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`_ INTER s`
  \\ qmatch_asmsub_rename_tac`EL m p <> _`
  \\ `s = {m}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET]
    \\ simp[SUBSET_DEF]
    \\ simp[Abbr`g`]
    \\ simp[FUN_EQ_THM]
    \\ rw[]
    \\ first_x_assum(qspec_then`v`mp_tac)
    \\ rw[] )
  \\ `count (LENGTH p) INTER s = {m}`
  by simp[Once EXTENSION]
  \\ simp[]
QED

Theorem eval_poly_of_mpoly:
  Ring r /\ mpoly r p ∧ f v ∈ r.carrier ∧ support r p SUBSET {v} ==>
  poly_eval r (poly_of_mpoly r p) (f v) = mpoly_eval r f p
Proof
  rpt strip_tac
  \\ drule mpoly_of_poly_of_mpoly
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ irule EQ_TRANS
  \\ qmatch_asmsub_abbrev_tac`q = p`
  \\ qexists_tac`mpoly_eval r f q`
  \\ reverse conj_tac >- simp[]
  \\ qunabbrev_tac`q`
  \\ DEP_REWRITE_TAC[eval_mpoly_of_poly]
  \\ simp[]
  \\ irule poly_poly_of_mpoly
  \\ metis_tac[mpoly_def ]
QED

(* Addition of polynomials *)

Definition mpoly_add_def:
  mpoly_add r p1 p2 t = r.sum.op (rrestrict r (p1 t)) (rrestrict r (p2 t))
End

Theorem rrestrict_mpoly_add[simp]:
  Ring r ⇒
  rrestrict r (mpoly_add r p1 p2 t) = r.sum.op (rrestrict r (p1 t)) (rrestrict r (p2 t))
Proof
  rewrite_tac[rrestrict_def]
  \\ strip_tac
  \\ rpt IF_CASES_TAC
  \\ gs[mpoly_add_def]
  \\ rw[rrestrict_def]
QED

Theorem monomials_mpoly_add:
  Ring r ==>
  monomials r (mpoly_add r p1 p2) =
    (monomials r p1 ∪ monomials r p2) DIFF
      { m | r.sum.op (rrestrict r (p1 m)) (rrestrict r (p2 m)) = r.sum.id }
Proof
  rw[monomials_def, rrestrict_def, mpoly_add_def]
  \\ rw[Once SET_EQ_SUBSET, SUBSET_DEF]
  \\ fs[] \\ rw[] \\ gs[]
QED

Theorem support_mpoly_add_SUBSET:
  Ring r ==> support r (mpoly_add r p q) SUBSET support r p UNION support r q
Proof
  rw[support_def, SUBSET_DEF, PULL_EXISTS, monomials_mpoly_add]
  \\ metis_tac[]
QED

Theorem mpoly_mpoly_add:
  Ring r /\ FINITE (monomials r p) /\ FINITE (monomials r q) ==>
  mpoly r (mpoly_add r p q)
Proof
  rw[mpoly_def, monomials_mpoly_add]
  \\ rw[SUBSET_DEF, mpoly_add_def]
  \\ irule ring_add_element
  \\ simp[]
QED

Theorem mpoly_eval_mpoly_add:
  Ring r ∧ finite_mpoly r p1 ∧ finite_mpoly r p2 ∧
  (∀x::(support r p1 ∪ support r p2). f x ∈ R) ⇒
  mpoly_eval r f (mpoly_add r p1 p2) = mpoly_eval r f p1 + mpoly_eval r f p2
Proof
  rw[mpoly_eval_def, monomials_mpoly_add, RES_FORALL_THM]
  \\ rw[mpoly_add_def]
  \\ qmatch_goalsub_abbrev_tac`GBAG r.sum (BAG_IMAGE f1 _) + GBAG r.sum (BAG_IMAGE f2 _)`
  \\ qmatch_goalsub_abbrev_tac`_ DIFF tz`
  \\ simp[BAG_OF_SET_DIFF]
  \\ qmatch_goalsub_abbrev_tac`BAG_FILTER (COMPL tz) t12`
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE f12`
  \\ `FINITE_BAG t12` by gs[Abbr`t12`, finite_mpoly_def]
  \\ `AbelianMonoid r.sum ∧ AbelianMonoid r.prod` by
  metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ `∀t. FINITE_BAG t ∧ IMAGE f (SET_OF_BAG t) ⊆ R ⇒ GBAG r.prod (BAG_IMAGE f t) ∈ R`
  by (
    rpt strip_tac
    \\ `r.prod.carrier = r.carrier` by metis_tac[ring_carriers]
    \\ first_assum (SUBST1_TAC o SYM)
    \\ irule GBAG_in_carrier
    \\ fs[SUBSET_DEF, PULL_EXISTS] )
  \\ `∀t. BAG_IN t t12 ⇒ GBAG r.prod (BAG_IMAGE f t) ∈ R`
  by (
    rpt strip_tac
    \\ first_x_assum irule
    \\ gs[finite_mpoly_def, Abbr`t12`, SUBSET_DEF, PULL_EXISTS, support_def]
    \\ metis_tac[] )
  \\ `GBAG r.sum (BAG_IMAGE f12 (BAG_FILTER tz t12)) ∈ R`
  by (
    `r.sum.carrier = r.carrier` by metis_tac[ring_carriers]
    \\ first_assum (SUBST1_TAC o SYM)
    \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[Abbr`f12`] \\ simp[Abbr`f1`, Abbr`f2`])
  \\ `GBAG r.sum (BAG_IMAGE f12 (BAG_FILTER tz t12)) = #0`
  by (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS, Abbr`tz`, Abbr`f12`]
    \\ rw[Abbr`f1`, Abbr`f2`]
    \\ DEP_REWRITE_TAC[GSYM ring_mult_ladd]
    \\ asm_rewrite_tac[] \\ simp[] )
  \\ qmatch_goalsub_abbrev_tac`s = _`
  \\ `s ∈ R`
  by (
    simp[Abbr`s`]
    \\ `r.sum.carrier = r.carrier` by metis_tac[ring_carriers]
    \\ first_assum (SUBST1_TAC o SYM)
    \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[Abbr`f12`, Abbr`f1`, Abbr`f2`] )
  \\ `s = s + #0` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`s`
  \\ qpat_x_assum`_ = #0` (SUBST1_TAC o SYM)
  \\ DEP_ONCE_REWRITE_TAC[GSYM GITBAG_UNION]
  \\ conj_asm1_tac
  >- (
    simp[]
    \\ gs[SUBSET_DEF, PULL_EXISTS]
    \\ simp[Abbr`f12`, Abbr`f1`, Abbr`f2`] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_FINITE_UNION]
  \\ conj_asm1_tac >- simp[]
  \\ REWRITE_TAC[BAG_FILTER_SPLIT]
  \\ qmatch_goalsub_abbrev_tac`_ = (GITBAG _ _ zz) + _`
  \\ `zz = r.sum.id`
  by (
    qunabbrev_tac`zz`
    \\ irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ simp[Abbr`tz`, Abbr`f12`]
    \\ simp[Abbr`f1`, Abbr`f2`]
    \\ rpt strip_tac
    \\ DEP_REWRITE_TAC[GSYM ring_mult_ladd]
    \\ asm_rewrite_tac[] \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[ring_add_rzero]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    `r.sum.carrier = r.carrier` by metis_tac[ring_carriers]
    \\ first_assum (SUBST1_TAC o SYM)
    \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[Abbr`f12`] \\ simp[Abbr`f1`, Abbr`f2`])
  \\ `∀t. BAG_IN t t12 ==> f12 t = (λx. f1 x + f2 x) t`
  by simp[Abbr`f12`, Abbr`f1`, Abbr`f2`]
  \\ `BAG_IMAGE f12 t12 = BAG_IMAGE (λx. f1 x + f2 x) t12`
  by ( irule BAG_IMAGE_CONG \\ simp[] )
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[GITBAG_BAG_IMAGE_op]
  \\ conj_asm1_tac >- fs[SUBSET_DEF, PULL_EXISTS, Abbr`f1`, Abbr`f2`]
  \\ qmatch_goalsub_abbrev_tac`_ = GBAG _ (BAG_IMAGE _ t1) + GBAG _ (BAG_IMAGE _ t2)`
  \\ `∃b1. BAG_IMAGE f1 t12 = BAG_UNION (BAG_IMAGE f1 t1) b1 ∧ BAG_EVERY ((=) #0) b1
           ∧ FINITE_BAG b1`
  by (
    `t12 = BAG_OF_SET (monomials r p1 ∪ (monomials r p2 DIFF monomials r p1))`
    by simp[Abbr`t12`]
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
    \\ conj_tac >- metis_tac[IN_DISJOINT, IN_DIFF]
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
    \\ simp[] \\ fs[finite_mpoly_def]
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ simp[Abbr`f1`]
    \\ fs[monomials_def, Abbr`t12`])
  \\ `∃b2. BAG_IMAGE f2 t12 = BAG_UNION (BAG_IMAGE f2 t2) b2 ∧ BAG_EVERY ((=) #0) b2
           ∧ FINITE_BAG b2`
  by (
    `t12 = BAG_OF_SET (monomials r p2 ∪ (monomials r p1 DIFF monomials r p2))`
    by simp[Abbr`t12`, UNION_COMM]
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
    \\ conj_tac >- metis_tac[IN_DISJOINT, IN_DIFF]
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
    \\ simp[] \\ fs[finite_mpoly_def]
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ simp[Abbr`f2`]
    \\ fs[monomials_def, Abbr`t12`])
  \\ simp[Abbr`t12`]
  \\ DEP_REWRITE_TAC[GBAG_UNION]
  \\ conj_asm1_tac
  >- (
    gs[Abbr`t1`,Abbr`t2`]
    \\ gs[SUBSET_DEF,BAG_EVERY]
    \\ metis_tac[ring_zero_element] )
  \\ `GBAG r.sum b1 = #0 ∧ GBAG r.sum b2 = #0`
  by ( conj_tac \\ irule IMP_GBAG_EQ_ID \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[ring_add_rzero]
  \\ gs[]
  \\ `r.sum.carrier = r.carrier` by metis_tac[ring_carriers]
  \\ first_assum (SUBST1_TAC o SYM)
  \\ conj_tac \\ irule GBAG_in_carrier
  \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`t1`, Abbr`t2`, Abbr`f1`, Abbr`f2`]
QED

Theorem mpoly_add_assoc:
  Ring r ==>
  mpoly_add r (mpoly_add r x y) z =
  mpoly_add r x (mpoly_add r y z)
Proof
  rw[mpoly_add_def, FUN_EQ_THM]
  \\ irule ring_add_assoc
  \\ rw[]
QED

Theorem monomials_zero[simp]:
  monomials r (K r.sum.id) = {}
Proof
  rw[monomials_def, EXTENSION]
  \\ rw[rrestrict_def]
QED

Theorem support_zero[simp]:
  support r (K r.sum.id) = {}
Proof
  rw[empty_support]
QED

Theorem mpoly_zero[simp]:
  Ring r ==> mpoly r (K r.sum.id)
Proof
  rw[mpoly_def] \\ rw[SUBSET_DEF]
QED

Theorem mpoly_add_zero:
  Ring r /\ mpoly r p ==>
  mpoly_add r (K r.sum.id) p = p
Proof
  rw[FUN_EQ_THM, mpoly_add_def]
  \\ rw[rrestrict_def]
  \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Definition mpoly_neg_def:
  mpoly_neg r p m = r.sum.inv (rrestrict r (p m))
End

Theorem monomials_mpoly_neg[simp]:
  Ring r ==> monomials r (mpoly_neg r p) = monomials r p
Proof
  rw[monomials_def, EXTENSION]
  \\ rw[mpoly_neg_def]
  \\ rw[rrestrict_def]
QED

Theorem support_mpoly_neg[simp]:
  Ring r ==> support r (mpoly_neg r p) = support r p
Proof
  rw[support_def]
QED

Theorem mpoly_mpoly_neg[simp]:
  Ring r /\ mpoly r p ==> mpoly r (mpoly_neg r p)
Proof
  rw[mpoly_def, mpoly_neg_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem mpoly_add_neg:
  Ring r ==>
  mpoly_add r (mpoly_neg r p) p = K r.sum.id
Proof
  rw[FUN_EQ_THM, mpoly_add_def, mpoly_neg_def]
  \\ rw[rrestrict_def]
QED

Theorem mpoly_add_comm:
  Ring r ==> mpoly_add r p q = mpoly_add r q p
Proof
  rw[FUN_EQ_THM, mpoly_add_def]
  \\ irule ring_add_comm
  \\ rw[]
QED

Theorem mpoly_of_poly_add:
  Ring r /\ poly p /\ poly q ==>
  mpoly_of_poly r v (p + q) =
  mpoly_add r (mpoly_of_poly r v p) (mpoly_of_poly r v q)
Proof
  rw[mpoly_of_poly_def, Once FUN_EQ_THM, mpoly_add_def]
  \\ Cases_on`x = {||}` \\ simp[]
  >- (
    Cases_on`p + q = []` \\ simp[]
    >- (
      `p + q = |0|` by simp[]
      \\ Cases_on`p=[]` \\ gs[]
      \\ Cases_on`q=[]` \\ gs[]
      \\ rw[] \\ gs[]
      \\ `p = -q` by
      metis_tac[polyRingTheory.poly_add_eq_zero, polynomialTheory.poly_zero]
      \\ Cases_on`p` \\ Cases_on`q` \\ gs[]
      \\ rw[rrestrict_def] )
    \\ Cases_on`p=[]` \\ gs[] >- rw[]
    \\ Cases_on`q=[]` \\ gs[] >- rw[]
    \\ rw[] \\ gs[]
    \\ Cases_on`p` \\ Cases_on`q` \\ gs[]
    \\ qpat_x_assum`_ <> _`mp_tac
    \\ rewrite_tac[polynomialTheory.poly_add_def]
    \\ rewrite_tac[polynomialTheory.weak_add_def]
    \\ rewrite_tac[polynomialTheory.poly_chop_def]
    \\ rewrite_tac[polyWeakTheory.zero_poly_cons]
    \\ IF_CASES_TAC \\ gs[]
    \\ rw[rrestrict_def] )
  \\ Cases_on`SET_OF_BAG x = {v}` \\ gs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ qspec_tac(`x v`,`n`)
  \\ ntac 2 (pop_assum mp_tac)
  \\ map_every qid_spec_tac[`q`,`p`]
  \\ Induct \\ simp[]
  >- ( rw[] \\ rw[] )
  \\ rw[] \\ fs[]
  \\ Cases_on`q=[]` \\ gs[] >- rw[]
  \\ Cases_on`q` \\ gs[]
  \\ qmatch_goalsub_abbrev_tac`LENGTH ls`
  \\ `ls <> [] ==> ls = (h+h')::(p+t)`
  by (
    rw[Abbr`ls`]
    \\ pop_assum mp_tac
    \\ rewrite_tac[polynomialTheory.poly_add_def]
    \\ rewrite_tac[polynomialTheory.weak_add_def]
    \\ rewrite_tac[polynomialTheory.poly_chop_def]
    \\ IF_CASES_TAC >- rw[] \\ rw[] )
  \\ reverse(Cases_on`ls = []` \\ gs[])
  >- ( Cases_on`n` \\ gs[] \\ rw[rrestrict_def] )
  \\ `(h'::t) = -(h::p)`
  by (
    DEP_REWRITE_TAC[GSYM polyRingTheory.poly_add_eq_zero]
    \\ conj_tac >- simp[]
    \\ DEP_ONCE_REWRITE_TAC[polyRingTheory.poly_add_comm]
    \\ simp[] )
  \\ simp[]
  \\ Cases_on`n` >- simp[rrestrict_def]
  \\ simp[]
  \\ first_x_assum(qspec_then`-p`mp_tac)
  \\ simp[]
  \\ rfs[]
QED

(* Multiplication of polynomials *)

Definition mpoly_mul_def:
  mpoly_mul r p1 p2 m =
    GBAG r.sum (BAG_IMAGE (λ(m1,m2). r.prod.op (rrestrict r (p1 m1)) (rrestrict r (p2 m2)))
                   (BAG_OF_SET { (m1,m2) | BAG_UNION m1 m2 = m ∧
                                           m1 ∈ monomials r p1 ∧
                                           m2 ∈ monomials r p2 }))
End

Theorem monomials_mpoly_mul_SUBSET:
  Ring r ==>
  monomials r (mpoly_mul r p1 p2) ⊆
  IMAGE (UNCURRY BAG_UNION) (monomials r p1 × monomials r p2)
Proof
  rw[monomials_def, SUBSET_DEF, EXISTS_PROD]
  \\ pop_assum mp_tac
  \\ simp[mpoly_mul_def, Once rrestrict_def]
  \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`GBAG _ b <> _`
  \\ `AbelianMonoid r.sum`
  by metis_tac[Ring_def, AbelianGroup_def, Group_def, AbelianMonoid_def]
  \\ `¬BAG_EVERY ($= #0) b`
  by (
    drule IMP_GBAG_EQ_ID
    \\ disch_then(qspec_then`b`(irule o CONTRAPOS))
    \\ simp[] )
  \\ fs[BAG_EVERY,Abbr`b`]
  \\ imp_res_tac BAG_IN_BAG_IMAGE_IMP
  \\ fs[] \\ rw[] \\ fs[]
  \\ qexistsl_tac[`m1`,`m2`]
  \\ simp[]
  \\ CCONTR_TAC \\ gs[]
QED

Theorem support_mpoly_mul_SUBSET:
  Ring r ==>
  support r (mpoly_mul r p q) SUBSET support r p UNION support r q
Proof
  rw[support_def]
  \\ imp_res_tac monomials_mpoly_mul_SUBSET
  \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ metis_tac[BAG_IN_BAG_UNION]
QED

Theorem mpoly_mul_in_carrier:
  Ring r /\ FINITE (monomials r p1) /\ FINITE (monomials r p2)
  ==> mpoly_mul r p1 p2 m ∈ r.carrier
Proof
  strip_tac
  \\ rw[mpoly_mul_def]
  \\ `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ simp[SUBSET_DEF]
  \\ conj_asm1_tac >- metis_tac[Ring_def, AbelianGroup_def, Group_def, AbelianMonoid_def]
  \\ reverse conj_tac
  >- (
    rw[]
    \\ imp_res_tac BAG_IN_BAG_IMAGE_IMP
    \\ fs[] \\ rw[] )
  \\ irule BAG_IMAGE_FINITE
  \\ simp[]
  \\ irule SUBSET_FINITE
  \\ qexists_tac`monomials r p1 × monomials r p2`
  \\ simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem mpoly_mul_BAG_FILTER_cross:
  mpoly_mul r p1 p2 m =
  GBAG r.sum (BAG_IMAGE (λ(m1,m2). r.prod.op (rrestrict r (p1 m1)) (rrestrict r (p2 m2)))
                (BAG_FILTER (((=) m) o UNCURRY BAG_UNION)
                  (BAG_OF_SET (monomials r p1 × monomials r p2))))
Proof
  rw[mpoly_mul_def]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ simp[Once EXTENSION, FORALL_PROD]
  \\ metis_tac[]
QED

Theorem mpoly_eval_mpoly_mul:
  Ring r /\ finite_mpoly r p1 /\ finite_mpoly r p2 /\
  (!x::support r p1 ∪ support r p2. f x IN r.carrier) ==>
  mpoly_eval r f (mpoly_mul r p1 p2) =
  r.prod.op (mpoly_eval r f p1) (mpoly_eval r f p2)
Proof
  rw[mpoly_eval_def]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE g (BAG_OF_SET mp)`
  \\ mp_tac monomials_mpoly_mul_SUBSET
  \\ simp[] \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`mp ⊆ mu`
  \\ `mu = mp UNION (mu DIFF mp)` by metis_tac[UNION_DIFF_EQ, SUBSET_UNION_ABSORPTION]
  \\ `AbelianMonoid r.sum` by PROVE_TAC[Ring_def, AbelianGroup_def,
                                        AbelianMonoid_def, Group_def]
  \\ `AbelianMonoid r.prod` by PROVE_TAC[Ring_def]
  \\ `FINITE mu` by fs[finite_mpoly_def, Abbr`mu`]
  \\ `FINITE mp` by metis_tac[SUBSET_FINITE]
  \\ `∀t. FINITE_BAG t /\ SET_OF_BAG (BAG_IMAGE f t) ⊆ r.carrier
          ⇒ GBAG r.prod (BAG_IMAGE f t) ∈ r.carrier`
  by (
    rpt strip_tac
    \\ `r.carrier = r.prod.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ `∀t. t ∈ mu ⇒ FINITE_BAG t ∧ SET_OF_BAG (BAG_IMAGE f t) ⊆ r.carrier`
  by (
    simp[Abbr`mu`, PULL_EXISTS, FORALL_PROD]
    \\ fs[finite_mpoly_def]
    \\ fs[SUBSET_DEF, RES_FORALL_THM, PULL_EXISTS, support_def]
    \\ metis_tac[] )
  \\ `∀s. s ⊆ mu ⇒ IMAGE g s ⊆ r.carrier`
  by (
    rpt strip_tac
    \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`g`]
    \\ rfs[] \\ rw[]
    \\ `GBAG r.prod (BAG_IMAGE f t) ∈ r.carrier` suffices_by rw[]
    \\ first_x_assum irule
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `∀s. s ⊆ mu ⇒ GBAG r.sum (BAG_IMAGE g (BAG_OF_SET s)) ∈ r.carrier`
  by (
    rpt strip_tac
    \\ `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule GBAG_in_carrier
    \\ `FINITE s` by metis_tac[SUBSET_FINITE]
    \\ rfs[] )
  \\ `GBAG r.sum (BAG_IMAGE g (BAG_OF_SET (mu DIFF mp))) = r.sum.id`
  by (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS, Abbr`g`]
    \\ simp[Abbr`mp`, monomials_def] )
  \\ `GBAG r.sum (BAG_IMAGE g (BAG_OF_SET mp)) = GBAG r.sum (BAG_IMAGE g (BAG_OF_SET mu))`
  by (
    qmatch_goalsub_abbrev_tac`x = _`
    \\ qmatch_asmsub_abbrev_tac`z = #0`
    \\ irule EQ_TRANS
    \\ qexists_tac`x + z`
    \\ conj_tac >- simp[Abbr`x`]
    \\ qunabbrev_tac`x` \\ qunabbrev_tac`z`
    \\ DEP_REWRITE_TAC[GSYM GBAG_UNION]
    \\ conj_tac >- fs[]
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_FINITE_UNION]
    \\ conj_tac >- fs[]
    \\ rewrite_tac[BAG_OF_SET_DIFF]
    \\ `BAG_OF_SET mp = BAG_FILTER mp (BAG_OF_SET mu)`
    by (
      simp[BAG_FILTER_BAG_OF_SET]
      \\ simp[Once EXTENSION]
      \\ fs[SUBSET_DEF] \\ fs[IN_DEF]
      \\ metis_tac[] )
    \\ pop_assum SUBST1_TAC
    \\ rewrite_tac[BAG_FILTER_SPLIT])
  \\ simp[]
  \\ qpat_x_assum`mu = _`kall_tac
  \\ qunabbrev_tac`mu`
  \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE g b`
  \\ `BAG_IMAGE g b = BAG_IMAGE (λm. mpoly_mul r p1 p2 m * GBAG r.prod (BAG_IMAGE f m)) b`
  by (
    irule BAG_IMAGE_CONG
    \\ simp[Abbr`g`]
    \\ simp[rrestrict_def]
    \\ rpt strip_tac
    \\ DEP_REWRITE_TAC[mpoly_mul_in_carrier]
    \\ fs[finite_mpoly_def] )
  \\ pop_assum SUBST_ALL_TAC
  \\ qunabbrev_tac`g`
  \\ simp[mpoly_mul_BAG_FILTER_cross]
  \\ qmatch_goalsub_abbrev_tac`BAG_FILTER _ (BAG_OF_SET p12)`
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE ff b`
  \\ `BAG_IMAGE ff b =
      BAG_IMAGE
        (λm. GBAG r.sum
          (BAG_IMAGE (λ(m1,m2). rrestrict r (p1 m1) * rrestrict r (p2 m2) * GBAG r.prod (BAG_IMAGE f (BAG_UNION m1 m2)))
            (BAG_FILTER (((=) m) o UNCURRY BAG_UNION) (BAG_OF_SET p12)))) b`
  by (
    irule BAG_IMAGE_CONG
    \\ simp[Abbr`ff`]
    \\ gen_tac
    \\ simp[Abbr`b`, EXISTS_PROD]
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`r.prod.op (GBAG r.sum bb) c`
    \\ DEP_REWRITE_TAC[MP_CANON ring_mult_lsum]
    \\ fs[Abbr`bb`, Abbr`p12`, finite_mpoly_def, GSYM BAG_IMAGE_COMPOSE]
    \\ conj_asm1_tac
    >- (
      simp[Abbr`c`]
      \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
      \\ `r.carrier = r.prod.carrier` by metis_tac[ring_carriers]
      \\ pop_assum SUBST1_TAC
      \\ irule GBAG_in_carrier
      \\ simp[]
      \\ fs[SUBSET_DEF, PULL_EXISTS, RES_FORALL_THM]
      \\ dsimp[]
      \\ fs[support_def, PULL_EXISTS]
      \\ metis_tac[] )
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[FORALL_PROD]
    \\ simp[Abbr`c`])
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE ff (BAG_FILTER _ _)`
  \\ qmatch_goalsub_abbrev_tac`_ = GBAG r.sum (BAG_IMAGE f1 _) * GBAG r.sum (BAG_IMAGE f2 _)`
  \\ `!P. BAG_IMAGE ff (BAG_FILTER P (BAG_OF_SET p12)) =
          BAG_IMAGE (λ(m1,m2). r.prod.op (f1 m1) (f2 m2)) (BAG_FILTER P (BAG_OF_SET p12))`
  by (
    gen_tac
    \\ irule BAG_IMAGE_CONG
    \\ simp[Abbr`p12`, FORALL_PROD]
    \\ simp[Abbr`ff`, Abbr`f1`, Abbr`f2`]
    \\ rpt strip_tac
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
    \\ fs[finite_mpoly_def]
    \\ DEP_REWRITE_TAC[GBAG_UNION] \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`pp * qq * (rr * ss) = _`
    \\ conj_asm1_tac
    >- (
      fs[SUBSET_DEF, PULL_EXISTS, RES_FORALL_THM]
      \\ fs[support_def, PULL_EXISTS]
      \\ metis_tac[] )
    \\ `rr ∈ r.carrier ∧ ss ∈ r.carrier`
    by ( unabbrev_all_tac \\ simp[]  )
    \\ `pp ∈ r.carrier ∧ qq ∈ r.carrier` by simp[Abbr`pp`,Abbr`qq`]
    \\ fs[AbelianMonoid_def]
    \\ DEP_REWRITE_TAC[monoid_assoc]
    \\ simp[]
    \\ AP_TERM_TAC
    \\ metis_tac[monoid_assoc, ring_carriers]  )
  \\ simp[]
  \\ DEP_REWRITE_TAC[ring_mult_sum_image]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[Abbr`f1`, Abbr`f2`]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ fs[finite_mpoly_def]
    \\ `∀t. t ∈ monomials r p1 ∨ t ∈ monomials r p2 ⇒
            IMAGE f (SET_OF_BAG t) SUBSET r.carrier`
    by (
      fs[RES_FORALL_THM, support_def, SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[] )
    \\ simp[] )
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE ft (BAG_OF_SET _)`
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE fg b`
  \\ `BAG_IMAGE fg b =
      BAG_IMAGE (λP. GBAG r.sum (BAG_IMAGE ft (BAG_FILTER P (BAG_OF_SET p12))))
                (BAG_IMAGE (λm p. m = UNCURRY BAG_UNION p) b)`
  by (
    DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[Abbr`b`]
    \\ irule BAG_IMAGE_CONG
    \\ simp[Abbr`fg`, PULL_EXISTS, combinTheory.o_DEF])
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`fg`
  \\ simp[Abbr`b`]
  \\ DEP_ONCE_REWRITE_TAC[GSYM BAG_OF_SET_IMAGE_INJ]
  \\ simp[PULL_EXISTS]
  \\ simp[Once FUN_EQ_THM]
  \\ irule GBAG_IMAGE_PARTITION
  \\ simp[PULL_EXISTS]
  \\ simp[Abbr`p12`, FORALL_PROD, EXISTS_PROD]
  \\ conj_tac >- metis_tac[]
  \\ fs[SUBSET_DEF, PULL_EXISTS, Abbr`ft`, FORALL_PROD]
QED

Theorem mpoly_mpoly_mul:
  Ring r /\ FINITE (monomials r p) /\ FINITE (monomials r q) ==>
  mpoly r (mpoly_mul r p q)
Proof
  rw[mpoly_def, SUBSET_DEF]
  >- (
    irule mpoly_mul_in_carrier
    \\ simp[] )
  \\ irule SUBSET_FINITE
  \\ imp_res_tac monomials_mpoly_mul_SUBSET
  \\ metis_tac[IMAGE_FINITE, FINITE_CROSS]
QED

Theorem rrestrict_mpoly_mul:
  Ring r /\ FINITE (monomials r p) /\ FINITE (monomials r q) ==>
  rrestrict r ((mpoly_mul r p q) m) = mpoly_mul r p q m
Proof
  rw[rrestrict_def]
  \\ imp_res_tac mpoly_mpoly_mul
  \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem mpoly_mul_comm:
  Ring r /\ FINITE (monomials r p) /\ FINITE (monomials r q) ==>
  mpoly_mul r p q = mpoly_mul r q p
Proof
  rw[FUN_EQ_THM]
  \\ rw[mpoly_mul_def]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s1`
  \\ qmatch_goalsub_abbrev_tac`_ = _ _ (_ _ (BAG_OF_SET s2)) _`
  \\ `s2 = IMAGE (λ(x,y). (y,x)) s1`
  by (
    simp[Abbr`s1`, Abbr`s2`]
    \\ simp[Once EXTENSION, PULL_EXISTS, FORALL_PROD]
    \\ metis_tac[COMM_BAG_UNION] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ simp[FORALL_PROD]
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
  \\ conj_tac
  >- (
    irule SUBSET_FINITE
    \\ qexists_tac`monomials r p CROSS monomials r q`
    \\ simp[SUBSET_DEF, Abbr`s1`, PULL_EXISTS] )
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM]
  \\ irule ring_mult_comm
  \\ simp[]
QED

Theorem mpoly_mul_assoc:
  Ring r /\ FINITE (monomials r x) /\ FINITE (monomials r y) /\ FINITE (monomials r z) ==>
  mpoly_mul r (mpoly_mul r x y) z =
  mpoly_mul r x (mpoly_mul r y z)
Proof
  strip_tac \\ simp[FUN_EQ_THM]
  \\ qx_gen_tac`m`
  \\ rw[mpoly_mul_def]
  \\ qho_match_abbrev_tac`GBAG r.sum (BAG_IMAGE (λ(m1,m2). f12 m1 * f3 m2) _) = _`
  \\ qho_match_abbrev_tac`_ = GBAG r.sum (BAG_IMAGE (λ(m1,m2). f1 m1 * f23 m2) _)`
  \\ gs[]
  \\ qmatch_goalsub_abbrev_tac`_ _ (_ _ (BAG_OF_SET sxy)) _ = _ _ (_ _ (BAG_OF_SET syz)) _`
  \\ qabbrev_tac`xyz = monomials r x × (monomials r y × monomials r z)`
  \\ qabbrev_tac`mm = xyz INTER {(m1,m2,m3) | BAG_UNION m1 (BAG_UNION m2 m3) = m}`
  \\ `sxy ⊆ IMAGE (λ(m1,m2,m3). (BAG_UNION m1 m2, m3)) mm`
  by (
    simp[Abbr`sxy`, SUBSET_DEF, Abbr`mm`, PULL_EXISTS, Abbr`xyz`]
    \\ rpt strip_tac
    \\ drule monomials_mpoly_mul_SUBSET
    \\ simp[SUBSET_DEF, EXISTS_PROD]
    \\ disch_then drule
    \\ strip_tac \\ rw[]
    \\ metis_tac[ASSOC_BAG_UNION] )
  \\ `syz ⊆ IMAGE (λ(m1,m2,m3). (m1, BAG_UNION m2 m3)) mm`
  by (
    simp[Abbr`syz`, SUBSET_DEF, Abbr`mm`, PULL_EXISTS, Abbr`xyz`]
    \\ rpt strip_tac
    \\ drule monomials_mpoly_mul_SUBSET
    \\ simp[SUBSET_DEF, EXISTS_PROD]
    \\ disch_then drule
    \\ strip_tac \\ rw[]
    \\ metis_tac[ASSOC_BAG_UNION] )
  \\ qmatch_asmsub_abbrev_tac`sxy SUBSET s12`
  \\ qmatch_asmsub_abbrev_tac`syz SUBSET s23`
  \\ `AbelianMonoid r.sum`
  by metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ `FINITE xyz` by simp[Abbr`xyz`]
  \\ `FINITE mm` by simp[Abbr`mm`]
  \\ `FINITE s12 /\ FINITE s23` by simp[Abbr`s12`, Abbr`s23`]
  \\ `FINITE sxy /\ FINITE syz` by metis_tac[SUBSET_FINITE]
  \\ qmatch_goalsub_abbrev_tac`GBAG r.sum (BAG_IMAGE f12_3 _) =
                               GBAG r.sum (BAG_IMAGE f1_23 _)`
  \\ `GBAG r.sum (BAG_IMAGE f12_3 (BAG_OF_SET (s12 DIFF sxy))) = #0`
  by (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ simp[Abbr`s12`,Abbr`sxy`, PULL_EXISTS, FORALL_PROD]
    \\ simp[Abbr`f12_3`, Abbr`f3`]
    \\ simp[Abbr`mm`, ASSOC_BAG_UNION]
    \\ simp[monomials_def]
    \\ rpt strip_tac
    \\ simp[Abbr`f12`]
    \\ gs[Abbr`f1`]
    \\ gs[mpoly_mul_def] )
  \\ `GBAG r.sum (BAG_IMAGE f1_23 (BAG_OF_SET (s23 DIFF syz))) = #0`
  by (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ simp[Abbr`s23`,Abbr`syz`, PULL_EXISTS, FORALL_PROD]
    \\ simp[Abbr`f1_23`, Abbr`f1`]
    \\ simp[Abbr`mm`, ASSOC_BAG_UNION]
    \\ simp[monomials_def]
    \\ rpt strip_tac
    \\ simp[Abbr`f23`]
    \\ gs[Abbr`f3`]
    \\ gs[mpoly_mul_def] )
  \\ `s12 = sxy UNION (s12 DIFF sxy) /\
      s23 = syz UNION (s23 DIFF syz)` by (gs[EXTENSION, SUBSET_DEF] \\ metis_tac[])
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum (BAG_IMAGE f12_3 (BAG_OF_SET s12))`
  \\ conj_tac
  >- (
    qpat_x_assum`s12 = _`SUBST1_TAC
    \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
    \\ simp[IN_DISJOINT]
    \\ conj_tac >- metis_tac[]
    \\ DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ conj_asm1_tac
    >- simp[SUBSET_DEF, PULL_EXISTS, Abbr`f12_3`, Abbr`f12`, Abbr`f3`, FORALL_PROD]
    \\ irule EQ_SYM
    \\ irule ring_add_rzero
    \\ simp[]
    \\ `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum (BAG_IMAGE f1_23 (BAG_OF_SET s23))`
  \\ reverse conj_tac
  >- (
    qpat_x_assum`s23 = _`SUBST1_TAC
    \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
    \\ simp[IN_DISJOINT]
    \\ conj_tac >- metis_tac[]
    \\ DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ conj_asm1_tac
    >- simp[SUBSET_DEF, PULL_EXISTS, Abbr`f1_23`, Abbr`f1`, Abbr`f23`, FORALL_PROD]
    \\ irule ring_add_rzero
    \\ simp[]
    \\ `r.carrier = r.sum.carrier` by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 2 (pop_assum kall_tac)
  \\ qpat_x_assum`sxy SUBSET _`kall_tac
  \\ qpat_x_assum`syz SUBSET _`kall_tac
  \\ qpat_x_assum`FINITE sxy`kall_tac
  \\ qpat_x_assum`FINITE syz`kall_tac
  \\ map_every qunabbrev_tac[`syz`,`sxy`]
  \\ gs[GSYM mpoly_mul_def, Abbr`f1`,Abbr`f3`]
  \\ gs[rrestrict_mpoly_mul]
  \\ `f1_23 = λ(m1,m2).
        GBAG r.sum (BAG_IMAGE (λ(m3,m4). rrestrict r (x m1) * rrestrict r (y m3) * rrestrict r (z m4))
                              (BAG_OF_SET {(m5,m6) | BAG_UNION m5 m6 = m2 ∧
                                                     m5 ∈ monomials r y ∧
                                                     m6 ∈ monomials r z}))`
  by (
    simp[Abbr`f1_23`, Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Abbr`f23`, mpoly_mul_def]
    \\ rpt strip_tac
    \\ DEP_REWRITE_TAC[MP_CANON ring_mult_rsum]
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac`FINITE s`
    \\ `s ⊆ monomials r y × monomials r z`
    by simp[SUBSET_DEF, PULL_EXISTS, Abbr`s`]
    \\ `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_CROSS]
    \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM]
    \\ rpt gen_tac
    \\ irule (GSYM ring_mult_assoc)
    \\ simp[] )
  \\ pop_assum SUBST1_TAC
  \\ `f12_3 = λ(m1,m2).
        GBAG r.sum (BAG_IMAGE (λ(m3,m4). rrestrict r (x m3) * rrestrict r (y m4) * rrestrict r (z m2))
                              (BAG_OF_SET {(m5,m6) | BAG_UNION m5 m6 = m1 ∧
                                                     m5 ∈ monomials r x ∧
                                                     m6 ∈ monomials r y}))`
  by (
    simp[Abbr`f12_3`, Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Abbr`f12`, mpoly_mul_def]
    \\ rpt strip_tac
    \\ DEP_REWRITE_TAC[MP_CANON ring_mult_lsum]
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac`FINITE s`
    \\ `s ⊆ monomials r x × monomials r y`
    by simp[SUBSET_DEF, PULL_EXISTS, Abbr`s`]
    \\ `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_CROSS]
    \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD] )
  \\ pop_assum SUBST1_TAC
  \\ ntac 2 (pop_assum kall_tac)
  \\ map_every qunabbrev_tac[`f12`,`f23`]
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum (BAG_IMAGE (λP.
       GBAG r.sum (BAG_IMAGE
         (λ(m1,m2,m3). rrestrict r (x m1) * rrestrict r (y m2) * rrestrict r (z m3))
         (BAG_FILTER P (BAG_OF_SET mm))))
           (BAG_OF_SET (IMAGE (λ(m1,m2,m3) (n1,n2,n3). m3 = n3 /\ BAG_UNION m1 m2 = BAG_UNION n1 n2) mm)))`
  \\ conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`_ = GBAG _ (_ _ (BAG_OF_SET ss))`
    \\ `ss = IMAGE (λ(m12,m3) (n1,n2,n3). m3 = n3 ∧ m12 = BAG_UNION n1 n2) s12`
    by (
      simp[Abbr`ss`, Abbr`s12`, GSYM IMAGE_COMPOSE]
      \\ simp[combinTheory.o_DEF, LAMBDA_PROD] )
    \\ simp[Abbr`ss`]
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
    \\ simp[FORALL_PROD]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ conj_tac
    >- (
      simp[Abbr`s12`, PULL_EXISTS, FORALL_PROD]
      \\ metis_tac[] )
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[FORALL_PROD]
    \\ simp[Abbr`s12`, PULL_EXISTS, FORALL_PROD]
    \\ simp[Abbr`mm`, Abbr`xyz`]
    \\ rpt gen_tac \\ strip_tac
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[BAG_FILTER_BAG_OF_SET, LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac`_ _ (BAG_OF_SET s) = BAG_IMAGE fg _`
    \\ irule EQ_TRANS
    \\ qmatch_goalsub_rename_tac`z m3`
    \\ qexists_tac`BAG_IMAGE fg (BAG_OF_SET (IMAGE (λ(m1,m2). (m1,m2,m3)) s))`
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
      \\ simp[FORALL_PROD]
      \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
      \\ `s ⊆ monomials r x × monomials r y`
      by simp[Abbr`s`,SUBSET_DEF,PULL_EXISTS]
      \\ simp[]
      \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_CROSS]
      \\ irule BAG_IMAGE_CONG
      \\ simp[FORALL_PROD, Abbr`fg`] )
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ simp[Once EXTENSION, FORALL_PROD, PULL_EXISTS]
    \\ simp[Abbr`s`, PULL_EXISTS]
    \\ metis_tac[ASSOC_BAG_UNION] )
  \\ DEP_REWRITE_TAC[MP_CANON GBAG_IMAGE_PARTITION]
  \\ simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ conj_tac >- metis_tac[]
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum (BAG_IMAGE (λP.
       GBAG r.sum (BAG_IMAGE
         (λ(m1,m2,m3). rrestrict r (x m1) * rrestrict r (y m2) * rrestrict r (z m3))
         (BAG_FILTER P (BAG_OF_SET mm))))
           (BAG_OF_SET (IMAGE (λ(m1,m2,m3) (n1,n2,n3). m1 = n1 /\ BAG_UNION m2 m3 = BAG_UNION n2 n3) mm)))`
  \\ reverse conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`GBAG _ (_ _ (BAG_OF_SET ss)) = _`
    \\ `ss = IMAGE (λ(m1,m23) (n1,n2,n3). m1 = n1 ∧ m23 = BAG_UNION n2 n3) s23`
    by (
      simp[Abbr`ss`, Abbr`s23`, GSYM IMAGE_COMPOSE]
      \\ simp[combinTheory.o_DEF, LAMBDA_PROD] )
    \\ simp[Abbr`ss`]
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
    \\ simp[FORALL_PROD]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ conj_tac
    >- (
      simp[Abbr`s23`, PULL_EXISTS, FORALL_PROD]
      \\ metis_tac[] )
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[FORALL_PROD]
    \\ simp[Abbr`s23`, PULL_EXISTS, FORALL_PROD]
    \\ simp[Abbr`mm`, Abbr`xyz`]
    \\ rpt gen_tac \\ strip_tac
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[BAG_FILTER_BAG_OF_SET, LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE fg _ = _ _ (BAG_OF_SET s)`
    \\ irule EQ_TRANS
    \\ qmatch_goalsub_rename_tac`x m1`
    \\ qexists_tac`BAG_IMAGE fg (BAG_OF_SET (IMAGE (λ(m2,m3). (m1,m2,m3)) s))`
    \\ reverse conj_tac
    >- (
      DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
      \\ simp[FORALL_PROD]
      \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
      \\ `s ⊆ monomials r y × monomials r z`
      by simp[Abbr`s`,SUBSET_DEF,PULL_EXISTS]
      \\ simp[]
      \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_CROSS]
      \\ irule BAG_IMAGE_CONG
      \\ simp[FORALL_PROD, Abbr`fg`] )
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ simp[Once EXTENSION, FORALL_PROD, PULL_EXISTS]
    \\ simp[Abbr`s`, PULL_EXISTS]
    \\ metis_tac[ASSOC_BAG_UNION] )
  \\ DEP_REWRITE_TAC[MP_CANON GBAG_IMAGE_PARTITION]
  \\ simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ metis_tac[]
QED

Theorem imp_mpoly_mul_zero:
  monomials r p = {} \/ monomials r q = {} ==> mpoly_mul r p q = K #0
Proof
  strip_tac \\ rw[mpoly_mul_def, Once FUN_EQ_THM]
QED

Definition mpoly_one_def:
  mpoly_one r m = if m = {||} then r.prod.id else r.sum.id
End

Theorem monomials_mpoly_one:
  Ring r ==> monomials r (mpoly_one r) = if r.sum.id = r.prod.id then {} else {{||}}
Proof
  strip_tac
  \\ qmatch_goalsub_abbrev_tac`COND b`
  \\ rewrite_tac[SET_EQ_SUBSET, SUBSET_DEF]
  \\ Cases_on`b=T` \\ fs[]
  \\ rw[monomials_def, mpoly_one_def]
  \\ rw[rrestrict_def]
QED

Theorem support_mpoly_one[simp]:
  Ring r ==> support r (mpoly_one r) = {}
Proof
  rw[empty_support, monomials_mpoly_one]
QED

Theorem mpoly_mpoly_one[simp]:
  Ring r ==> mpoly r (mpoly_one r)
Proof
  rw[mpoly_def, SUBSET_DEF]
  >- rw[mpoly_one_def]
  \\ rw[monomials_mpoly_one]
QED

Theorem mpoly_mul_one:
  Ring r /\ mpoly r p ==>
  mpoly_mul r (mpoly_one r) p = p /\
  mpoly_mul r p (mpoly_one r) = p
Proof
  strip_tac
  \\ conj_asm1_tac
  >- (
    rw[FUN_EQ_THM]
    \\ rw[mpoly_mul_def, monomials_mpoly_one]
    \\ imp_res_tac ring_one_eq_zero
    \\ gs[SUBSET_DEF, PULL_EXISTS, mpoly_def]
    \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s = if x IN monomials r p then {({||},x)} else {}`
    by ( rw[Abbr`s`, Once EXTENSION] )
    \\ reverse(rw[])
    >- gs[monomials_def, rrestrict_def]
    \\ DEP_REWRITE_TAC[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ simp[mpoly_one_def]
    \\ simp[rrestrict_def] )
  \\ DEP_ONCE_REWRITE_TAC[mpoly_mul_comm]
  \\ gs[mpoly_def, monomials_mpoly_one]
  \\ rw[]
QED

Theorem mpoly_of_poly_mul:
  Ring r /\ poly p /\ poly q ==>
  mpoly_of_poly r v (p * q) =
  mpoly_mul r (mpoly_of_poly r v p) (mpoly_of_poly r v q)
Proof
  rw[mpoly_of_poly_def, Once FUN_EQ_THM, mpoly_mul_BAG_FILTER_cross]
  \\ simp[monomials_mpoly_of_poly]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ Cases_on`x = {||}` \\ gs[]
  >- (
    qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s ⊆ {({||},{||})}`
    by simp[Abbr`s`, SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ Cases_on`s = {}` \\ gs[]
    >- (
      rw[]
      \\ DEP_REWRITE_TAC[polyRingTheory.HD_poly_mult]
      \\ simp[]
      \\ conj_asm1_tac >- (strip_tac \\ fs[])
      \\ qpat_x_assum`_ = {}`mp_tac
      \\ simp[Once EXTENSION, FORALL_PROD]
      \\ simp[Once FUN_EQ_THM, EMPTY_BAG]
      \\ simp[Once FUN_EQ_THM, EMPTY_BAG]
      \\ Cases_on`p = |0|`
      >- (
        pop_assum SUBST_ALL_TAC
        \\ rewrite_tac[polyRingTheory.poly_mult_zero]
        \\ gs[] )
      \\ Cases_on`q = |0|`
      >- (
        pop_assum SUBST_ALL_TAC
        \\ rewrite_tac[polyRingTheory.poly_mult_zero]
        \\ gs[] )
      \\ Cases_on`p` >- fs[]
      \\ Cases_on`q` >- fs[]
      \\ fs[]
      \\ simp[rrestrict_def]
      \\ Cases_on`h = #0` \\ simp[]
      \\ Cases_on`h' = #0` \\ simp[]
      \\ dsimp[]
      \\ conj_tac \\ disch_then(qspec_then`0`mp_tac)
      \\ (impl_tac >- rw[]) \\ simp[] )
    \\ `s = {({||},{||})}`
    by (
      simp[SET_EQ_SUBSET]
      \\ fs[GSYM pred_setTheory.MEMBER_NOT_EMPTY, SUBSET_DEF]
      \\ metis_tac[] )
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ Cases_on`p = |0|`
    >- ( `p * q = |0|` by metis_tac[polyRingTheory.poly_mult_zero] \\ gs[] )
    \\ Cases_on`q = |0|`
    >- ( `p * q = |0|` by metis_tac[polyRingTheory.poly_mult_zero] \\ gs[] )
    \\ `0 < LENGTH p /\ 0 < LENGTH q` by (Cases_on`p` \\ Cases_on`q` \\ fs[])
    \\ simp[]
    \\ fs[Abbr`s`]
    \\ Cases_on`p` \\ Cases_on`q` \\ fs[]
    \\ rw[]
    >- (
      DEP_REWRITE_TAC[polyRingTheory.HD_poly_mult]
      \\ simp[]
      \\ conj_tac >- (strip_tac \\ fs[])
      \\ simp[rrestrict_def] )
    \\ simp[rrestrict_def]
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[polyRingTheory.poly_mult_cross]
    \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[GSYM polyRingTheory.poly_add_shift]
    \\ conj_tac >- simp[]
    \\ qmatch_goalsub_abbrev_tac`LENGTH l`
    \\ strip_tac
    \\ `l = []` by (Cases_on`l` \\ fs[])
    \\ qunabbrev_tac`l`
    \\ pop_assum mp_tac
    \\ rewrite_tac[polynomialTheory.poly_add_def]
    \\ rewrite_tac[GSYM polyWeakTheory.zero_poly_chop]
    \\ DEP_REWRITE_TAC[GSYM polyWeakTheory.weak_cons_eq_add_shift]
    \\ conj_tac
    >- (
      conj_tac >- simp[]
      \\ rewrite_tac[polynomialTheory.Weak_def]
      \\ conj_tac >- simp[]
      \\ irule polyWeakTheory.poly_chop_weak
      \\ irule polyWeakTheory.weak_add_weak
      \\ conj_tac >- simp[]
      \\ conj_tac
      >- (
        irule polyWeakTheory.poly_chop_weak
        \\ irule polyWeakTheory.weak_add_weak
        \\ simp[] )
      \\ simp[] )
    \\ rewrite_tac[polynomialTheory.zero_poly_def]
    \\ strip_tac
    \\ simp[] )
  \\ reverse(Cases_on`SET_OF_BAG x = {v}`) \\ gs[]
  >- (
    qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ Cases_on`s = {}` \\ gs[]
    \\ fs[Abbr`s`, GSYM pred_setTheory.MEMBER_NOT_EMPTY, EXISTS_PROD]
    \\ rw[]
    \\ fs[SET_OF_BAG_UNION]
    \\ fs[SET_OF_BAG, BAG_IN, BAG_INN, EMPTY_BAG, FUN_EQ_THM]
    \\ Cases_on`x=v`\\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`n'` \\ fs[] )
  \\ rewrite_tac[polynomialTheory.poly_mult_def]
  \\ qmatch_goalsub_abbrev_tac`lhs = _`
  \\ `lhs = if x v < LENGTH (weak_mult r p q) then
               EL (x v) (weak_mult r p q) else #0`
  by (
    unabbrev_all_tac
    \\ IF_CASES_TAC
    >- (
      qspec_then`weak_mult r p q`assume_tac polyWeakTheory.poly_chop_length
      \\ reverse IF_CASES_TAC >- fs[]
      \\ simp[EL_chop]
      \\ rw[rrestrict_def]
      \\ imp_res_tac polyRingTheory.poly_is_weak
      \\ `weak (weak_mult r p q)` by simp[]
      \\ fs[polyWeakTheory.weak_every_mem]
      \\ fs[listTheory.MEM_EL, PULL_EXISTS]
      \\ metis_tac[] )
    \\ rw[]
    \\ irule EQ_SYM
    \\ irule EL_chop_0
    \\ simp[] )
  \\ simp[Abbr`lhs`]
  \\ pop_assum kall_tac
  \\ simp[polyWeakTheory.weak_mult_length]
  \\ Cases_on`p= []` \\ simp[]
  \\ Cases_on`q= []` \\ simp[]
  \\ reverse IF_CASES_TAC \\ simp[]
  >- (
    qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s = {}` suffices_by simp[]
    \\ simp[Abbr`s`]
    \\ simp[Once EXTENSION, FORALL_PROD]
    \\ rpt strip_tac
    \\ fs[BAG_UNION]
    \\ simp[DISJ_EQ_IMP]
    \\ strip_tac \\ fs[] \\ rw[]
    \\ fs[] )
  \\ DEP_REWRITE_TAC[polyWeakTheory.EL_weak_mult]
  \\ simp[polyWeakTheory.weak_mult_length]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ qabbrev_tac`z = {n | EL n p <> #0 } × {n | EL n q <> #0}`
  \\ `s = s INTER z UNION s INTER (COMPL z)`
  by ( simp[Once EXTENSION] \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
  \\ conj_tac >- (simp[IN_DISJOINT] \\ metis_tac[])
  \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
  \\ conj_tac >- simp[Abbr`s`]
  \\ DEP_REWRITE_TAC[GBAG_UNION]
  \\ imp_res_tac polyRingTheory.poly_is_weak
  \\ fs[polyWeakTheory.weak_every_mem, listTheory.MEM_EL, PULL_EXISTS]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- simp[groupTheory.abelian_group_is_abelian_monoid]
  \\ simp[CONJ_ASSOC]
  \\ conj_tac
  >- ( simp[Abbr`s`] \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD] )
  \\ qmatch_goalsub_abbrev_tac`_ + zz`
  \\ `zz = #0`
  by (
    qunabbrev_tac`zz`
    \\ irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, Abbr`s`, PULL_EXISTS, FORALL_PROD]
    \\ simp[Abbr`z`]
    \\ rw[] \\ rw[] )
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`g + _`
  \\ `g ∈ r.sum.carrier`
  by (
    qunabbrev_tac`g`
    \\ irule GBAG_in_carrier
    \\ simp[Abbr`s`]
    \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD] )
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET t`
  \\ `t = IMAGE (λ(n,m). ((λx. if x = v then n else 0),
                          (λx. if x = v then m else 0))) (s INTER z)`
  by (
    simp[Abbr`t`]
    \\ simp[Abbr`s`, Once EXTENSION, PULL_EXISTS]
    \\ simp[FORALL_PROD, EXISTS_PROD, Abbr`z`]
    \\ rw[EQ_IMP_THM]
    >- (
      simp[BAG_UNION]
      \\ simp[FUN_EQ_THM]
      \\ qmatch_asmsub_rename_tac`n < LENGTH p`
      \\ qmatch_asmsub_rename_tac`m < LENGTH q`
      \\ qexistsl_tac[`n`,`m`]
      \\ simp[] )
    \\ simp[Once FUN_EQ_THM]
    \\ simp[Once FUN_EQ_THM]
    \\ qmatch_asmsub_rename_tac`n + m = x v`
    \\ qexistsl_tac[`n`,`m`]
    \\ simp[]
    \\ simp[Once FUN_EQ_THM]
    \\ simp[BAG_UNION]
    \\ fs[SET_OF_BAG, BAG_IN, BAG_INN, Once EXTENSION]
    \\ rw[]
    \\ qmatch_goalsub_rename_tac`x k`
    \\ `~(x k >= 1)` by metis_tac[]
    \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ simp[FORALL_PROD]
  \\ conj_tac
  >- ( rw[FUN_EQ_THM] \\ metis_tac[] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[Abbr`s`]
  \\ simp[Abbr`g`]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[FORALL_PROD]
  \\ simp[Abbr`z`]
  \\ rpt strip_tac
  \\ `!n. SET_OF_BAG (\x. if x = v then n else 0) = if n = 0 then {} else {v}`
  by ( rw[SET_OF_BAG, BAG_IN, BAG_INN, EXTENSION] \\ rw[] )
  \\ simp[]
  \\ `!n. (\x. if x = v then n else 0) = {||} <=> n = 0`
  by (
    rw[FUN_EQ_THM, EMPTY_BAG]
    \\ rw[EQ_IMP_THM]
    \\ metis_tac[] )
  \\ simp[]
  \\ qmatch_asmsub_rename_tac`EL n p`
  \\ qmatch_asmsub_rename_tac`EL m q`
  \\ Cases_on`n=0` \\ Cases_on`m=0` \\ fs[]
  \\ simp[rrestrict_def]
  \\ rpt(first_x_assum(qspec_then`0`mp_tac)) \\ rw[]
QED

(* Distributivity *)

Theorem mpoly_mul_add:
  Ring r /\ FINITE (monomials r x) /\ FINITE (monomials r y) /\ FINITE (monomials r z) ==>
  mpoly_mul r x (mpoly_add r y z) =
  mpoly_add r (mpoly_mul r x y) (mpoly_mul r x z)
Proof
  rw[FUN_EQ_THM, mpoly_add_def]
  \\ DEP_REWRITE_TAC[rrestrict_mpoly_mul]
  \\ rw[mpoly_mul_def, monomials_mpoly_add]
  \\ qmatch_goalsub_abbrev_tac`GBAG r.sum (BAG_IMAGE f3 (BAG_OF_SET s3)) =
                               GBAG r.sum (BAG_IMAGE f1 (BAG_OF_SET s1)) +
                               GBAG r.sum (BAG_IMAGE f2 (BAG_OF_SET s2))`
  \\ `FINITE s1 ∧ FINITE s2 ∧ FINITE s3`
  by (
    conj_tac
    >- (
      irule SUBSET_FINITE
      \\ qexists_tac`monomials r x × monomials r y`
      \\ simp[SUBSET_DEF, Abbr`s1`, PULL_EXISTS] )
    \\ conj_tac
    >- (
      irule SUBSET_FINITE
      \\ qexists_tac`monomials r x × monomials r z`
      \\ simp[SUBSET_DEF, Abbr`s2`, PULL_EXISTS] )
    \\ irule SUBSET_FINITE
    \\ qexists_tac`monomials r x × (monomials r y ∪ monomials r z)`
    \\ simp[SUBSET_DEF, Abbr`s3`, PULL_EXISTS] )
  \\ `AbelianMonoid r.sum`
  by metis_tac[Ring_def, AbelianMonoid_def, AbelianGroup_def, Group_def]
  \\ `GBAG r.sum (BAG_IMAGE f1 (BAG_OF_SET s1)) =
      GBAG r.sum (BAG_IMAGE f3 (BAG_OF_SET (s1 DIFF s2))) +
      GBAG r.sum (BAG_IMAGE f1 (BAG_OF_SET (s1 INTER s2)))`
  by (
    `s1 = (s1 DIFF s2) UNION (s1 INTER s2)`
    by ( simp[Once EXTENSION] \\ metis_tac[] )
    \\ pop_assum(fn th => simp[Once th])
    \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
    \\ conj_tac >- (simp[IN_DISJOINT] \\ metis_tac[])
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
    \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ conj_asm1_tac >- simp[PULL_EXISTS,SUBSET_DEF, Abbr`f1`, FORALL_PROD]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[]
    \\ simp[Abbr`s1`, Abbr`s2`, Abbr`f1`, Abbr`f3`, PULL_EXISTS]
    \\ rpt strip_tac \\ gs[]
    \\ fs[monomials_def] )
  \\ `GBAG r.sum (BAG_IMAGE f2 (BAG_OF_SET s2)) =
      GBAG r.sum (BAG_IMAGE f3 (BAG_OF_SET (s2 DIFF s1))) +
      GBAG r.sum (BAG_IMAGE f2 (BAG_OF_SET (s1 INTER s2)))`
  by (
    `s2 = (s2 DIFF s1) UNION (s1 INTER s2)`
    by ( simp[Once EXTENSION] \\ metis_tac[] )
    \\ pop_assum(fn th => simp[Once th])
    \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
    \\ conj_tac >- (simp[IN_DISJOINT] \\ metis_tac[])
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
    \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ conj_asm1_tac >- simp[PULL_EXISTS,SUBSET_DEF, Abbr`f2`, FORALL_PROD]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[]
    \\ simp[Abbr`s1`, Abbr`s2`, Abbr`f2`, Abbr`f3`, PULL_EXISTS]
    \\ rpt strip_tac \\ gs[]
    \\ fs[monomials_def] )
  \\ pop_assum SUBST1_TAC
  \\ pop_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`(a + b) + (c + d)`
  \\ `!s. FINITE_BAG s ==> GBAG r.sum (BAG_IMAGE f1 s) ∈ r.carrier ∧
          GBAG r.sum (BAG_IMAGE f2 s) ∈ r.carrier ∧
          GBAG r.sum (BAG_IMAGE f3 s) ∈ r.carrier`
  by (
    gen_tac \\ strip_tac
    \\ `r.carrier =r.sum.carrier `by metis_tac[ring_carriers]
    \\ pop_assum SUBST1_TAC
    \\ rpt conj_tac \\ irule GBAG_in_carrier
    \\ simp[]
    \\ simp[PULL_EXISTS,SUBSET_DEF,Abbr`f1`,Abbr`f2`,Abbr`f3`, FORALL_PROD])
  \\ `a ∈ r.carrier /\ b ∈ r.carrier /\ c ∈ r.carrier /\ d ∈ r.carrier`
  by simp[Abbr`a`,Abbr`b`,Abbr`c`,Abbr`d`]
  \\ `(a + b) + (c + d) = (a + c) + (b + d)`
  by (
    simp[ring_add_assoc, ring_add_comm]
    \\ AP_TERM_TAC
    \\ metis_tac[ring_add_assoc, ring_add_comm] )
  \\ pop_assum SUBST1_TAC
  \\ `b + d = GBAG r.sum (BAG_IMAGE f3 (BAG_OF_SET (s1 INTER s2)))`
  by (
    qunabbrev_tac`f3`
    \\ qunabbrev_tac`b` \\ qunabbrev_tac`d`
    \\ qunabbrev_tac`f1` \\ qunabbrev_tac`f2`
    \\ DEP_REWRITE_TAC[GSYM (MP_CANON GITBAG_BAG_IMAGE_op)]
    \\ simp[]
    \\ simp[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
    \\ simp[LAMBDA_PROD] )
  \\ pop_assum SUBST1_TAC
  \\ map_every qunabbrev_tac[`b`,`d`]
  \\ map_every qunabbrev_tac[`a`,`c`]
  \\ DEP_REWRITE_TAC[GSYM GBAG_UNION]
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ conj_tac
  >- (
    simp[Abbr`f3`, PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
    \\ dsimp[] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_FINITE_UNION]
  \\ conj_tac >- simp[]
  \\ DEP_REWRITE_TAC[GSYM BAG_OF_SET_DISJOINT_UNION]
  \\ conj_tac >- ( simp[IN_DISJOINT] \\ metis_tac[] )
  \\ `s3 = s1 UNION s2 DIFF {(m1,m2) | (m1,m2) | rrestrict r (y m2) + rrestrict r (z m2) = #0}`
  by (
    simp[Abbr`s3`, Abbr`s1`, Abbr`s2`, Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ simp[FORALL_PROD]
    \\ metis_tac[] )
  \\ simp[Abbr`s3`]
  \\ pop_assum kall_tac
  \\ simp[BAG_OF_SET_DIFF]
  \\ qmatch_goalsub_abbrev_tac`_ = _ _ (BAG_IMAGE _ (BAG_OF_SET s12)) _`
  \\ `s12 = s1 ∪ s2`
  by ( simp[SET_EQ_SUBSET, Abbr`s12`, SUBSET_DEF] )
  \\ pop_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`BAG_FILTER s b`
  \\ `BAG_IMAGE f3 b = BAG_IMAGE f3 (BAG_UNION (BAG_FILTER s b) (BAG_FILTER (COMPL s) b))`
  by metis_tac[BAG_FILTER_SPLIT]
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_UNION]
  \\ conj_tac >- simp[Abbr`b`]
  \\ DEP_REWRITE_TAC[GBAG_UNION]
  \\ conj_tac
  >- (
    simp[Abbr`b`]
    \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`f3`, FORALL_PROD] )
  \\ qmatch_goalsub_abbrev_tac`a = a + c`
  \\ `a IN R /\ c IN R`
  by ( simp[Abbr`a`,Abbr`c`] \\ simp[Abbr`b`] )
  \\ `c = #0` suffices_by simp[]
  \\ qunabbrev_tac`c`
  \\ irule IMP_GBAG_EQ_ID
  \\ simp[BAG_EVERY]
  \\ simp[Abbr`b`, PULL_EXISTS]
  \\ simp[Abbr`f3`, Abbr`s`, PULL_EXISTS]
  \\ rpt gen_tac
  \\ DEP_REWRITE_TAC[GSYM ring_mult_radd]
  \\ conj_tac >- simp[]
  \\ rewrite_tac[GSYM AND_IMP_INTRO]
  \\ disch_then SUBST1_TAC
  \\ simp[]
QED

(* Ring of multivariate polynomials over a given support *)

Definition mpoly_ring_def:
  mpoly_ring (r:'a ring) (s:'v set) :('a,'v) mpoly ring =
  let m = { p | mpoly r p /\ support r p ⊆ s } in
    <| carrier := m;
         sum := <| carrier := m; op := mpoly_add r; id := K r.sum.id |>;
         prod := <| carrier := m; op := mpoly_mul r; id := mpoly_one r |> |>
End

Theorem mpoly_add_group:
  Ring r ==> Group (mpoly_ring r s).sum
Proof
  strip_tac
  \\ simp[group_def_alt, mpoly_ring_def]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ imp_res_tac mpoly_def
    \\ simp[mpoly_mpoly_add]
    \\ imp_res_tac support_mpoly_add_SUBSET
    \\ fs[SUBSET_DEF]
    \\ metis_tac[])
  \\ conj_tac >- simp[mpoly_add_assoc]
  \\ conj_tac >- simp[mpoly_add_zero]
  \\ rpt strip_tac
  \\ qexists_tac`mpoly_neg r x`
  \\ simp[mpoly_add_neg]
QED

Theorem mpoly_add_abelian_group:
  Ring r ==> AbelianGroup (mpoly_ring r s).sum
Proof
  rw[AbelianGroup_def, mpoly_add_group]
  \\ fs[mpoly_ring_def]
  \\ simp[mpoly_add_comm]
QED

Theorem mpoly_mul_monoid:
  Ring r ==> Monoid (mpoly_ring r s).prod
Proof
  strip_tac
  \\ rewrite_tac[Monoid_def]
  \\ simp[mpoly_ring_def]
  \\ conj_tac
  >- (
    rpt strip_tac
    >- ( irule mpoly_mpoly_mul \\ fs[mpoly_def] )
    \\ imp_res_tac support_mpoly_mul_SUBSET
    \\ fs[SUBSET_DEF]
    \\ metis_tac[])
  \\ conj_tac >- (
    rpt strip_tac
    \\ irule mpoly_mul_assoc
    \\ fs[mpoly_def])
  \\ rw[mpoly_mul_one]
QED

Theorem mpoly_mul_abelian_monoid:
  Ring r ==> AbelianMonoid (mpoly_ring r s).prod
Proof
  rw[AbelianMonoid_def]
  >- rw[mpoly_mul_monoid]
  \\ fs[mpoly_ring_def]
  \\ irule mpoly_mul_comm
  \\ fs[mpoly_def]
QED

Theorem mpoly_ring[simp]:
  Ring r ==> Ring (mpoly_ring r s)
Proof
  strip_tac
  \\ rewrite_tac[Ring_def]
  \\ conj_tac >- simp[mpoly_add_abelian_group]
  \\ conj_tac >- simp[mpoly_mul_abelian_monoid]
  \\ conj_tac >- simp[mpoly_ring_def]
  \\ conj_tac >- simp[mpoly_ring_def]
  \\ rw[mpoly_ring_def]
  \\ irule mpoly_mul_add
  \\ fs[mpoly_def]
QED

(* Some facts in the ring of polynomials *)

Theorem mpoly_ring_sum_applied:
  !b. FINITE_BAG b ==> Ring r /\ SET_OF_BAG b SUBSET (mpoly_ring r s).carrier
  ==> !x.
  GBAG (mpoly_ring r s).sum b x =
  GBAG r.sum (BAG_IMAGE (\f. f x) b)
Proof
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT \\ rw[]
  >- rw[mpoly_ring_def]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ fs[SET_OF_BAG_INSERT]
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS, abelian_group_is_abelian_monoid]
    \\ fs[mpoly_ring_def]
    \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS] )
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ simp[Once mpoly_ring_def]
  \\ simp[mpoly_add_def]
  \\ simp[rrestrict_def]
  \\ rw[]
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`_ NOTIN _`mp_tac
  \\ simp[]
  \\ `r.carrier = r.sum.carrier`by metis_tac[ringTheory.ring_carriers]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ simp[]
QED

Theorem mpoly_sum_monomials:
  Ring r /\ mpoly r p /\ support r p SUBSET s ==>
  GBAG (mpoly_ring r s).sum
    (BAG_IMAGE (\m t. if t = m then p m else r.sum.id)
      (BAG_OF_SET (monomials r p))) = p
Proof
  strip_tac
  \\ simp[Once FUN_EQ_THM]
  \\ strip_tac
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ `FINITE (monomials r p)` by fs[mpoly_def]
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[mpoly_ring_def]
  \\ conj_asm1_tac
  >- (
    ntac 2 strip_tac
    \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[support_def, monomials_def, PULL_EXISTS]
    \\ rw[] \\ fs[support_def, PULL_EXISTS]
    >- (
      qmatch_goalsub_abbrev_tac`FINITE z`
      \\ `z = {m}` suffices_by rw[]
      \\ rw[Abbr`z`, EXTENSION]
      \\ rw[] \\ fs[monomials_def] )
    \\ metis_tac[] )
  \\ simp[GSYM BAG_IMAGE_COMPOSE, combinTheory.o_DEF]
  \\ reverse(Cases_on`x IN monomials r p`)
  >- (
    `p x = #0` by
    gs[monomials_def, mpoly_def, SUBSET_DEF, PULL_EXISTS, rrestrict_def]
    \\ simp[]
    \\ irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS, abelian_group_is_abelian_monoid]
    \\ rw[] \\ fs[] )
  \\ drule INSERT_DELETE
  \\ disch_then(SUBST1_TAC o GSYM)
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- simp[abelian_group_is_abelian_monoid]
  \\ `∀x. p x IN r.carrier` by fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`_ + g`
  \\ `g = #0` suffices_by rw[]
  \\ qunabbrev_tac`g`
  \\ irule IMP_GBAG_EQ_ID
  \\ simp[BAG_EVERY, PULL_EXISTS]
QED

(* Degree of a variable in a polynomial *)

Definition degree_of_def:
  degree_of r (p:('c,'v) mpoly) v =
    MAX_SET (IMAGE (λt. t v) (monomials r p))
End

Theorem degree_of_mpoly_add_le:
  Ring r /\ FINITE (monomials r p) ∧ FINITE (monomials r q) ⇒
  degree_of r (mpoly_add r p q) v ≤ MAX (degree_of r p v) (degree_of r q v)
Proof
  rw[degree_of_def]
  \\ simp[monomials_mpoly_add]
  \\ Cases_on`monomials r p = {}` \\ gs[]
  >- ( disj2_tac \\ irule SUBSET_MAX_SET \\ simp[SUBSET_DEF] )
  \\ Cases_on`monomials r q = {}` \\ gs[]
  >- ( disj1_tac \\ irule SUBSET_MAX_SET \\ simp[SUBSET_DEF] )
  \\ qmatch_goalsub_abbrev_tac`MAX_SET a ≤ MAX_SET tp ∨ _ ≤ _ tq`
  \\ Cases_on`a = {}` \\ simp[]
  \\ `FINITE a` by simp[Abbr`a`]
  \\ `MAX_SET a ∈ a` by metis_tac[MAX_SET_DEF]
  \\ `FINITE tp ∧ FINITE tq` by simp[Abbr`tp`, Abbr`tq`]
  \\ `tp <> {} /\ tq <> {}` by simp[Abbr`tp`, Abbr`tq`]
  \\ `MAX_SET tp ∈ tp` by metis_tac[MAX_SET_DEF]
  \\ `MAX_SET tq ∈ tq` by metis_tac[MAX_SET_DEF]
  \\ Cases_on`MAX_SET a ≤ MAX_SET tp` \\ simp[]
  \\ `MAX_SET a ∉ tp` by metis_tac[X_LE_MAX_SET]
  \\ `MAX_SET a ∈ tq`
  by (
    qmatch_goalsub_abbrev_tac`ma ∈ tq`
    \\ fs[Abbr`a`, Abbr`tp`, Abbr`tq`]
    \\ metis_tac[] )
  \\ irule X_LE_MAX_SET
  \\ simp[]
QED

Theorem degree_of_mpoly_add_less:
  Ring r /\ FINITE (monomials r p) /\ FINITE (monomials r q) /\
  degree_of r p v < degree_of r q v
  ==>
  degree_of r (mpoly_add r p q) v = degree_of r q v
Proof
  strip_tac
  \\ pop_assum mp_tac
  \\ simp[degree_of_def]
  \\ simp[monomials_mpoly_add]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`MAX_SET mp < MAX_SET mq`
  \\ Cases_on`mq = {}` \\ fs[]
  \\ `FINITE mq` by simp[Abbr`mq`]
  \\ `MAX_SET mq ∈ mq` by metis_tac[MAX_SET_DEF]
  \\ irule arithmeticTheory.LESS_EQUAL_ANTISYM
  \\ conj_tac
  >- (
    irule X_LE_MAX_SET
    \\ fs[Abbr`mq`]
    \\ qexists_tac`t`
    \\ simp[]
    \\ pop_assum mp_tac
    \\ simp[monomials_def]
    \\ strip_tac
    \\ `rrestrict r (p t) = #0` suffices_by simp[]
    \\ rw[rrestrict_def]
    \\ CCONTR_TAC
    \\ `t v ∈ mp`
    by (
      simp[Abbr`mp`]
      \\ simp[monomials_def, rrestrict_def]
      \\ metis_tac[] )
    \\ `t v <= MAX_SET mp`
    by ( irule X_LE_MAX_SET \\ simp[Abbr`mp`] )
    \\ fs[] )
  \\ simp[GSYM monomials_mpoly_add]
  \\ qunabbrev_tac`mq`
  \\ simp[GSYM degree_of_def]
  \\ drule degree_of_mpoly_add_le
  \\ disch_then (qspecl_then[`v`,`q`,`p`]mp_tac)
  \\ simp[]
  \\ strip_tac \\ simp[]
  \\ fs[Abbr`mp`, GSYM degree_of_def]
QED

Theorem degree_of_mpoly_add_less_sym:
  Ring r /\ FINITE (monomials r p) /\ FINITE (monomials r q) /\
  degree_of r q v < degree_of r p v
  ==>
  degree_of r (mpoly_add r p q) v = degree_of r p v
Proof
  strip_tac
  \\ simp[Once mpoly_add_comm]
  \\ irule degree_of_mpoly_add_less
  \\ simp[]
QED

Theorem degree_of_zero[simp]:
  degree_of r (K #0) v = 0
Proof
  rw[degree_of_def]
QED

Theorem support_degree_of:
  FINITE (monomials r p) ==>
  (v IN support r p <=> 1 <= degree_of r p v)
Proof
  rw[support_def, degree_of_def, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`1 <= MAX_SET ls`
  \\ `1 <= MAX_SET ls <=> MAX_SET ls <> 0` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ `FINITE ls` by simp[Abbr`ls`]
  \\ simp[helperSetTheory.MAX_SET_EQ_0, Abbr`ls`]
  \\ simp[IMAGE_EQ_SING]
  \\ Cases_on`monomials r p = {}` \\ simp[]
  \\ rw[BAG_IN, BAG_INN]
  \\ rw[EQ_IMP_THM]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

val _ = export_theory();
