open HolKernel boolLib bossLib Parse;

open dep_rewrite pairTheory pred_setTheory listTheory rich_listTheory bagTheory
     gcdsetTheory numberTheory combinatoricsTheory;

open ringTheory polynomialTheory polyWeakTheory polyRingTheory polyEvalTheory
     polyFieldTheory;

open monoidTheory groupTheory;

val _ = new_theory "multipoly";

Theorem GBAG_IMAGE_GBAG_BAG_OF_SET:
  AbelianMonoid g ==>
  !s. FINITE s ==>
  (!x. x IN s ==> FINITE (b x) /\ !y. y IN b x ==> f x y IN g.carrier) ==>
  GBAG g
    (BAG_IMAGE
      (\x. GBAG g (BAG_IMAGE (f x) (BAG_OF_SET (b x))))
    (BAG_OF_SET s)) =
  GBAG g
    (BAG_IMAGE (UNCURRY f)
      (BAG_OF_SET (BIGUNION (IMAGE (\x. IMAGE (\y. (x, y)) (b x)) s))))
Proof
  strip_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ conj_asm1_tac
  >- (
    rw[] \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, PULL_EXISTS] )
  \\ DEP_REWRITE_TAC[GSYM GBAG_UNION]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
  \\ simp[IN_DISJOINT, PULL_EXISTS, PULL_FORALL, FORALL_PROD]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ simp[]
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ srw_tac[ETA_ss][]
QED

Theorem SET_OF_BAG_UPDATE:
  SET_OF_BAG ((x =+ n) b) =
  if 0 < n then
    if BAG_IN x b then SET_OF_BAG b
    else x INSERT SET_OF_BAG b
  else
    if BAG_IN x b then SET_OF_BAG b DELETE x
    else SET_OF_BAG b
Proof
  rw[SET_OF_BAG, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, BAG_IN, BAG_INN]
  \\ rw[] \\ fs[]
QED

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
  \\ conj_asm1_tac
  >- fs[SUBSET_DEF, PULL_EXISTS, EL_SNOC, weak_every_mem, MEM_EL]
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`a + b = b' + a`
  \\ irule EQ_TRANS
  \\ qexists_tac`a + b'`
  \\ reverse conj_tac >- (
    `AbelianMonoid r.sum` by simp[]
    \\ imp_res_tac AbelianMonoid_def
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
  mpoly_eval r p f = GBAG r.sum
    (BAG_IMAGE (λt. r.prod.op (rrestrict r (p t)) (GBAG r.prod (BAG_IMAGE f t)))
      (BAG_OF_SET (monomials r p)))
End

Theorem mpoly_eval_support:
  (!x. x IN support r p ==> f1 x = f2 x) ==>
  mpoly_eval r p f1 = mpoly_eval r p f2
Proof
  strip_tac
  \\ simp[mpoly_eval_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[]
  \\ fs[support_def, PULL_EXISTS]
  \\ rw[]
  \\ AP_TERM_TAC \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ metis_tac[]
QED

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

Theorem mpoly_of_poly_empty:
  mpoly_of_poly r v [] = K r.sum.id
Proof
  rw[FUN_EQ_THM, mpoly_of_poly_def]
QED

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

Theorem FINITE_support_finite_mpoly:
  mpoly r p ==> (FINITE (support r p) <=> finite_mpoly r p)
Proof
  rw[support_def, PULL_EXISTS, mpoly_def]
  \\ simp[finite_mpoly_def]
QED

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

Theorem BIJ_mpoly_of_poly:
  Ring r ==>
  BIJ (mpoly_of_poly r v) {p | poly p} {p | mpoly r p /\ support r p SUBSET {v}}
Proof
  strip_tac
  \\ drule BIJ_poly_of_mpoly
  \\ disch_then(qspec_then`v`strip_assume_tac)
  \\ drule BIJ_LINV_BIJ
  \\ qmatch_goalsub_abbrev_tac`BIJ f s` \\ strip_tac
  \\ `∀x. x IN s ==> f x = mpoly_of_poly r v x`
  suffices_by metis_tac[BIJ_CONG]
  \\ simp[Abbr`f`]
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac`LINV f t x`
  \\ `mpoly_of_poly r v x = mpoly_of_poly r v (f (LINV f t x))`
  by metis_tac[BIJ_LINV_THM]
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`f`
  \\ DEP_REWRITE_TAC[mpoly_of_poly_of_mpoly]
  \\ qmatch_goalsub_abbrev_tac`f x`
  \\ `f x IN t` by metis_tac[BIJ_DEF, INJ_DEF]
  \\ fs[Abbr`t`]
QED

Theorem eval_mpoly_of_poly:
  Ring r /\ poly p /\ f v IN r.carrier ==>
  mpoly_eval r (mpoly_of_poly r v p) f = poly_eval r p (f v)
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
  poly_eval r (poly_of_mpoly r p) (f v) = mpoly_eval r p f
Proof
  rpt strip_tac
  \\ drule mpoly_of_poly_of_mpoly
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ irule EQ_TRANS
  \\ qmatch_asmsub_abbrev_tac`q = p`
  \\ qexists_tac`mpoly_eval r q f`
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
  mpoly_eval r (mpoly_add r p1 p2) f = mpoly_eval r p1 f + mpoly_eval r p2 f
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

Theorem mpoly_eval_zero:
  Ring r ==>
  mpoly_eval r (K r.sum.id) = K r.sum.id
Proof
  rw[mpoly_eval_def, FUN_EQ_THM]
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
      metis_tac[poly_add_eq_zero, polynomialTheory.poly_zero]
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
    DEP_REWRITE_TAC[GSYM poly_add_eq_zero]
    \\ conj_tac >- simp[]
    \\ DEP_ONCE_REWRITE_TAC[poly_add_comm]
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
  mpoly_eval r (mpoly_mul r p1 p2) f =
  r.prod.op (mpoly_eval r p1 f) (mpoly_eval r p2 f)
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

Theorem mpoly_of_poly_const:
  Ring r /\ c IN r.carrier ==>
  mpoly_of_poly r v [c] = r.prod.op c o (mpoly_one r)
Proof
  rw[Once FUN_EQ_THM, mpoly_of_poly_def]
  \\ Cases_on`x` \\ simp[mpoly_one_def]
  >- simp[rrestrict_def]
  \\ simp[SET_OF_BAG_INSERT] \\ rw[]
  \\ Cases_on`BAG_INSERT e b0 v` \\ fs[]
  \\ fs[BAG_INSERT]
  \\ pop_assum mp_tac \\ rw[]
  \\ fs[INSERT_EQ_SING]
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
    \\ rgs[SUBSET_DEF, PULL_EXISTS, mpoly_def]
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
    >- ( `p * q = |0|` by metis_tac[polyRingTheory.poly_mult_zero] \\ rgs[] )
    \\ Cases_on`q = |0|`
    >- ( `p * q = |0|` by metis_tac[polyRingTheory.poly_mult_zero] \\ rgs[] )
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

(* multiplication by a constant *)

Theorem monomials_cmul:
  IntegralDomain r /\ mpoly r p /\ c IN r.carrier /\ c <> r.sum.id ==>
  monomials r (r.prod.op c o p) = monomials r p
Proof
  rw[monomials_def, EXTENSION, IntegralDomain_def]
  \\ rw[rrestrict_def]
  \\ gs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem support_cmul:
  IntegralDomain r /\ mpoly r p /\ c IN r.carrier /\ c <> r.sum.id ==>
  support r (r.prod.op c o p) = support r p
Proof
  rw[support_def, monomials_cmul]
QED

Theorem mpoly_cmul:
  Ring r /\ mpoly r p /\ c IN r.carrier ==>
  mpoly r (r.prod.op c o p)
Proof
  rw[mpoly_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ fs[monomials_def]
  \\ irule SUBSET_FINITE
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[SUBSET_DEF]
  \\ rw[rrestrict_def]
  \\ strip_tac \\ gs[]
QED

Theorem mpoly_mul_cmul:
  Ring r /\ mpoly r p /\ mpoly r q /\ c IN r.carrier ==>
  mpoly_mul r (r.prod.op c o p) q =
  r.prod.op c o mpoly_mul r p q
Proof
  strip_tac
  \\ imp_res_tac mpoly_cmul
  \\ ntac 4 (pop_assum kall_tac)
  \\ rw[mpoly_mul_BAG_FILTER_cross, FUN_EQ_THM]
  \\ DEP_REWRITE_TAC[MP_CANON ring_mult_rsum]
  \\ imp_res_tac mpoly_def
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ simp[UNCURRY, LAMBDA_PROD]
  \\ simp[rrestrict_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ irule GITBAG_CONG
  \\ simp[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ fs[combinTheory.o_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ qx_gen_tac`z`
  \\ simp[BAG_IMAGE_DEF]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ simp[UNCURRY, LAMBDA_PROD]
  \\ disch_then assume_tac
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[Once EXTENSION, FORALL_PROD]
  \\ qx_genl_tac[`m1`,`m2`]
  \\ DEP_REWRITE_TAC[ring_mult_assoc]
  \\ simp[]
  \\ Cases_on`c * (p m1 * q m2) = z` \\ simp[]
  \\ Cases_on`x = BAG_UNION m1 m2` \\ simp[]
  \\ Cases_on`m2 IN monomials r q` \\ simp[]
  \\ simp[monomials_def]
  \\ simp[rrestrict_def]
  \\ Cases_on`p m1 = r.sum.id` >- gs[]
  \\ simp[]
  \\ `z = (c * p m1) * q m2` by metis_tac[ring_mult_assoc]
  \\ strip_tac \\ gs[]
QED

Theorem cmul_zero:
  Ring r /\ mpoly r p ==> r.prod.op r.sum.id o p = K r.sum.id
Proof
  rw[mpoly_def]
  \\ rw[FUN_EQ_THM]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
QED

Theorem cmul_one:
  Ring r /\ mpoly r p ==> r.prod.op r.prod.id o p = p
Proof
  rw[mpoly_def, FUN_EQ_THM]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
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

Theorem mpoly_ring_carrier:
  (mpoly_ring r s).carrier = { p | mpoly r p /\ support r p SUBSET s }
Proof
  rw[mpoly_ring_def]
QED

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

Theorem mpoly_eval_in_carrier:
  Ring r /\ mpoly r p /\ finite_mpoly r p /\
  IMAGE f (support r p) SUBSET r.carrier
  ==>
  mpoly_eval r p f IN r.carrier
Proof
  strip_tac
  \\ rw[mpoly_eval_def]
  \\ `r.carrier = r.sum.carrier` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ imp_res_tac mpoly_def
  \\ simp[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ rw[rrestrict_def]
  \\ irule ring_mult_element
  \\ simp[]
  \\ `r.carrier = r.prod.carrier` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ imp_res_tac finite_mpoly_def
  \\ simp[]
  \\ fs[SUBSET_DEF, PULL_EXISTS, support_def]
  \\ metis_tac[Ring_def]
QED

Theorem monomials_mpoly_ring_more_support:
  s SUBSET s' /\ mpoly (mpoly_ring r s) p ==>
  monomials (mpoly_ring r s) p =
  monomials (mpoly_ring r s') p
Proof
  rw[monomials_def, mpoly_def]
  \\ rw[EXTENSION]
  \\ rw[rrestrict_def]
  \\ fs[mpoly_ring_def, SUBSET_DEF, PULL_EXISTS]
  \\ fs[]
  \\ metis_tac[]
QED

Theorem support_mpoly_ring_more_support:
  s SUBSET s' /\ mpoly (mpoly_ring r s) p ==>
  support (mpoly_ring r s) p = support (mpoly_ring r s') p
Proof
  rw[support_def]
  \\ imp_res_tac monomials_mpoly_ring_more_support
  \\ simp[]
QED

Theorem mpoly_mpoly_ring_more_support:
  mpoly (mpoly_ring r s) p /\ s SUBSET s' ==>
  mpoly (mpoly_ring r s') p
Proof
  strip_tac
  \\ rw[mpoly_def]
  >- (
    fs[mpoly_def, mpoly_ring_def, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ imp_res_tac(GSYM monomials_mpoly_ring_more_support)
  \\ simp[]
  \\ fs[mpoly_def]
QED

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

Theorem mpoly_ring_neg:
  Ring r /\ mpoly r p /\ support r p SUBSET s ==>
  (mpoly_ring r s).sum.inv p = mpoly_neg r p
Proof
  strip_tac
  \\ `Ring (mpoly_ring r s)` by simp[]
  \\ `p IN (mpoly_ring r s).carrier` by simp[mpoly_ring_def]
  \\ drule_then drule ringTheory.ring_add_eq_zero
  \\ `mpoly_neg r p IN (mpoly_ring r s).carrier`
  by ( simp[mpoly_ring_def, mpoly_neg_def])
  \\ disch_then drule
  \\ disch_then(irule o GSYM o #1 o EQ_IMP_RULE)
  \\ simp[mpoly_ring_def]
  \\ metis_tac[mpoly_add_neg, mpoly_add_comm]
QED

Theorem mpoly_eval_neg:
  Ring r /\ mpoly r p /\ support r p SUBSET s /\
  FINITE (support r p) /\ IMAGE f (support r p) SUBSET r.carrier ==>
  mpoly_eval r ((mpoly_ring r s).sum.inv p) f =
  r.sum.inv (mpoly_eval r p f)
Proof
  rw[mpoly_ring_neg]
  \\ rw[mpoly_eval_def]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp[support_def]
  \\ `FINITE (monomials r p)` by fs[mpoly_def]
  \\ pop_assum mp_tac
  \\ qspec_tac(`monomials r p`,`ms`)
  \\ Induct \\ rw[]
  \\ rw[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[] \\ fs[]
  \\ `∀t. t IN ms \/ t = e ==> GBAG r.prod (BAG_IMAGE f t) IN r.prod.carrier`
  by (
    rpt strip_tac
    \\ irule GBAG_in_carrier
    \\ fs[PULL_EXISTS, SUBSET_DEF]
    \\ metis_tac[Ring_def] )
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw[rrestrict_def, mpoly_neg_def]
    \\ irule ring_mult_element \\ rw[] \\ rfs[] )
  \\ rfs[]
  \\ DEP_REWRITE_TAC[ring_neg_add]
  \\ conj_tac
  >- (
    rw[]
    \\ `r.carrier = r.sum.carrier` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ drule ring_neg_mult
  \\ qmatch_goalsub_abbrev_tac`-(a * b)`
  \\ disch_then(qspecl_then[`a`,`b`]mp_tac)
  \\ impl_tac >- rw[Abbr`a`,Abbr`b`]
  \\ disch_then(SUBST1_TAC o CONJUNCT1)
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[rrestrict_def, Abbr`a`, mpoly_neg_def]
  \\ gs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem mpoly_eval_sub:
  Ring r /\ mpoly r p /\ mpoly r q /\ support r p ⊆ s /\ support r q ⊆ s ∧
  FINITE (support r p) /\ FINITE (support r q) ∧
  IMAGE f s SUBSET r.carrier ==>
  mpoly_eval r (ring_sub (mpoly_ring r s) p q) f =
  ring_sub r (mpoly_eval r p f) (mpoly_eval r q f)
Proof
  strip_tac
  \\ simp[]
  \\ `(mpoly_ring r s).sum.op = mpoly_add r` by simp[mpoly_ring_def]
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_add]
  \\ DEP_REWRITE_TAC[mpoly_eval_neg]
  \\ simp[]
  \\ simp[ring_sub_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ fs[support_def, PULL_EXISTS, RES_FORALL_THM]
  \\ DEP_REWRITE_TAC[mpoly_ring_neg]
  \\ fs[PULL_EXISTS, SUBSET_DEF, support_def]
  \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
  \\ simp[]
  \\ simp[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ fs[mpoly_def, support_def, PULL_EXISTS]
  \\ rw[]
  \\ metis_tac[]
QED

Theorem monomials_sum_SUBSET:
  Ring r ==>
  !b. FINITE_BAG b ==>
  SET_OF_BAG b SUBSET (mpoly_ring r s).carrier ==>
  monomials r (GBAG (mpoly_ring r s).sum b) SUBSET
  BIGUNION (IMAGE (monomials r) (SET_OF_BAG b))
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  >- rw[mpoly_ring_def]
  \\ rw[SET_OF_BAG_INSERT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ gen_tac
  \\ `(mpoly_ring r s).sum.op = mpoly_add r` by simp[mpoly_ring_def]
  \\ pop_assum(fn th => simp[Once th])
  \\ DEP_REWRITE_TAC[monomials_mpoly_add]
  \\ simp[]
  \\ rw[] \\ fs[]
QED

Theorem support_sum_SUBSET:
  !b. FINITE_BAG b ==>
  Ring r /\ SET_OF_BAG b SUBSET (mpoly_ring r s).carrier ==>
  support r (GBAG (mpoly_ring r s).sum b) ⊆
  BIGUNION (IMAGE (support r) (SET_OF_BAG b))
Proof
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ conj_tac >- rw[mpoly_ring_def]
  \\ rw[]
  \\ DEP_REWRITE_TAC[SET_OF_BAG_INSERT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ conj_asm1_tac
  >- fs[SUBSET_DEF, PULL_EXISTS]
  \\ `(mpoly_ring r s).sum.op = mpoly_add r` by simp[mpoly_ring_def]
  \\ pop_assum (fn th => simp[Once th])
  \\ qpat_x_assum`_ ==> _`mp_tac
  \\ impl_tac >- fs[SUBSET_DEF, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`a SUBSET z`
  \\ strip_tac
  \\ irule SUBSET_TRANS
  \\ qexists_tac`support r e UNION a`
  \\ reverse conj_tac >- fs[SUBSET_DEF]
  \\ qunabbrev_tac`a`
  \\ irule support_mpoly_add_SUBSET
  \\ simp[]
QED

Theorem mpoly_eval_sum:
  !b. FINITE_BAG b ==>
  Ring r /\ SET_OF_BAG b SUBSET (mpoly_ring r s).carrier /\
  IMAGE f (BIGUNION (IMAGE (support r) (SET_OF_BAG b))) SUBSET r.carrier /\
  BAG_EVERY (finite_mpoly r) b
  ==>
  mpoly_eval r (GBAG (mpoly_ring r s).sum b) f =
  GBAG r.sum (BAG_IMAGE (flip (mpoly_eval r) f) b)
Proof
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ conj_tac
  >- simp[mpoly_ring_def, mpoly_eval_zero]
  \\ rw[]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ conj_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ irule mpoly_eval_in_carrier
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[mpoly_ring_def]
    \\ conj_tac >- metis_tac[]
    \\ rfs[BAG_EVERY] )
  \\ `(mpoly_ring r s).sum.op = mpoly_add r` by simp[mpoly_ring_def]
  \\ pop_assum (fn th => simp[Once th])
  \\ qmatch_goalsub_abbrev_tac`mpoly_add r e g`
  \\ `g IN (mpoly_ring r s).carrier`
  by (
    qunabbrev_tac`g`
    \\ `(mpoly_ring r s).carrier = (mpoly_ring r s).sum.carrier`by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[]
    \\ fs[PULL_EXISTS, SUBSET_DEF] )
  \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_add]
  \\ conj_tac
  >- (
    fs[] \\ rfs[BAG_EVERY]
    \\ simp[RES_FORALL_THM]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ `support r g SUBSET BIGUNION (IMAGE (support r) (SET_OF_BAG b))`
    by (
      qunabbrev_tac`g`
      \\ irule support_sum_SUBSET
      \\ simp[SUBSET_DEF, PULL_EXISTS] )
    \\ `FINITE (support r g)`
    by (
      irule SUBSET_FINITE
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[PULL_EXISTS]
      \\ fs[mpoly_ring_def]
      \\ metis_tac[FINITE_support_finite_mpoly] )
    \\ fs[mpoly_ring_def]
    \\ conj_tac >- metis_tac[FINITE_support_finite_mpoly]
    \\ fs[SUBSET_DEF ,PULL_EXISTS]
    \\ metis_tac[] )
  \\ AP_TERM_TAC
  \\ first_x_assum irule
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem support_mul_SUBSET:
  !b. FINITE_BAG b ==>
  Ring r /\ SET_OF_BAG b SUBSET (mpoly_ring r s).carrier ==>
  support r (GBAG (mpoly_ring r s).prod b) ⊆
  BIGUNION (IMAGE (support r) (SET_OF_BAG b))
Proof
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ conj_tac >- rw[mpoly_ring_def]
  \\ rw[]
  \\ DEP_REWRITE_TAC[SET_OF_BAG_INSERT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ conj_asm1_tac
  >- (fs[SUBSET_DEF, PULL_EXISTS] \\ metis_tac[mpoly_ring, Ring_def])
  \\ `(mpoly_ring r s).prod.op = mpoly_mul r` by simp[mpoly_ring_def]
  \\ pop_assum (fn th => simp[Once th])
  \\ qpat_x_assum`_ ==> _`mp_tac
  \\ impl_tac >- fs[SUBSET_DEF, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`a SUBSET z`
  \\ strip_tac
  \\ irule SUBSET_TRANS
  \\ qexists_tac`support r e UNION a`
  \\ reverse conj_tac >- fs[SUBSET_DEF]
  \\ qunabbrev_tac`a`
  \\ irule support_mpoly_mul_SUBSET
  \\ simp[]
QED

Theorem mpoly_eval_one[simp]:
  Ring r ==>
  mpoly_eval r (mpoly_one r) = K r.prod.id
Proof
  rw[mpoly_eval_def, monomials_mpoly_one,
     BAG_OF_SET_INSERT_NON_ELEMENT, FUN_EQ_THM]
  \\ rw[rrestrict_def, mpoly_one_def]
QED

Theorem mpoly_eval_prod:
  !b. FINITE_BAG b ==>
  Ring r /\ SET_OF_BAG b SUBSET (mpoly_ring r s).carrier /\
  IMAGE f (BIGUNION (IMAGE (support r) (SET_OF_BAG b))) SUBSET r.carrier /\
  BAG_EVERY (finite_mpoly r) b
  ==>
  mpoly_eval r (GBAG (mpoly_ring r s).prod b) f =
  GBAG r.prod (BAG_IMAGE (flip (mpoly_eval r) f) b)
Proof
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ conj_tac
  >- simp[mpoly_ring_def, mpoly_eval_one]
  \\ rw[]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ conj_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ conj_tac >- metis_tac[mpoly_ring, Ring_def]
    \\ conj_tac >- metis_tac[mpoly_ring, Ring_def]
    \\ rw[] \\ irule mpoly_eval_in_carrier
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[mpoly_ring_def]
    \\ conj_tac >- metis_tac[]
    \\ rfs[BAG_EVERY] )
  \\ `(mpoly_ring r s).prod.op = mpoly_mul r` by simp[mpoly_ring_def]
  \\ pop_assum (fn th => simp[Once th])
  \\ qmatch_goalsub_abbrev_tac`mpoly_mul r e g`
  \\ `g IN (mpoly_ring r s).carrier`
  by (
    qunabbrev_tac`g`
    \\ `(mpoly_ring r s).carrier = (mpoly_ring r s).prod.carrier`by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[]
    \\ fs[PULL_EXISTS, SUBSET_DEF]
    \\ metis_tac[mpoly_ring, Ring_def])
  \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_mul]
  \\ conj_tac
  >- (
    fs[] \\ rfs[BAG_EVERY]
    \\ simp[RES_FORALL_THM]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ `support r g SUBSET BIGUNION (IMAGE (support r) (SET_OF_BAG b))`
    by (
      qunabbrev_tac`g`
      \\ irule support_mul_SUBSET
      \\ simp[SUBSET_DEF, PULL_EXISTS] )
    \\ `FINITE (support r g)`
    by (
      irule SUBSET_FINITE
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[PULL_EXISTS]
      \\ fs[mpoly_ring_def]
      \\ metis_tac[FINITE_support_finite_mpoly] )
    \\ fs[mpoly_ring_def]
    \\ conj_tac >- metis_tac[FINITE_support_finite_mpoly]
    \\ fs[SUBSET_DEF ,PULL_EXISTS]
    \\ metis_tac[] )
  \\ AP_TERM_TAC
  \\ first_x_assum irule
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem mpoly_eval_cmul:
  IntegralDomain r /\ mpoly r p /\ c IN r.carrier /\ c <> r.sum.id /\
  IMAGE f (support r p) SUBSET r.carrier /\
  (!m. m IN monomials r p ==> FINITE_BAG m)
  ==>
  mpoly_eval r (r.prod.op c o p) f = r.prod.op c (mpoly_eval r p f)
Proof
  rw[mpoly_eval_def]
  \\ DEP_REWRITE_TAC[monomials_cmul]
  \\ simp[]
  \\ DEP_REWRITE_TAC[MP_CANON ring_mult_rsum]
  \\ imp_res_tac mpoly_def
  \\ simp[]
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[rrestrict_def]
  \\ simp[GSYM BAG_IMAGE_COMPOSE, combinTheory.o_DEF]
  \\ `∀t. t IN monomials r p ==> GBAG r.prod (BAG_IMAGE f t) IN r.prod.carrier`
  by (
    rpt strip_tac
    \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ fs[support_def, PULL_EXISTS]
    \\ metis_tac[Ring_def] )
  \\ conj_asm1_tac
  >- (
    rw[]
    \\ irule ring_mult_element
    \\ rfs[] )
  >- (
    AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ rfs[]
    \\ metis_tac[ring_mult_assoc] )
QED

Theorem DISJOINT_support_mpoly_mul:
  IntegralDomain r /\ mpoly r p /\ mpoly r q /\
  DISJOINT (support r p) (support r q) ==>
  monomials r (mpoly_mul r p q) =
  IMAGE (UNCURRY BAG_UNION) (monomials r p × monomials r q) /\
  !m1 m2. m1 IN monomials r p /\ m2 IN monomials r q ==>
    mpoly_mul r p q (BAG_UNION m1 m2) = r.prod.op(p m1)(q m2)
Proof
  strip_tac
  \\ `Ring r` by simp[integral_domain_is_ring]
  \\ conj_asm1_tac
  >- (
    rw[Once monomials_def]
    \\ simp[mpoly_mul_BAG_FILTER_cross]
    \\ rw[Once EXTENSION, PULL_EXISTS, EXISTS_PROD]
    \\ rewrite_tac[rrestrict_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ `r.carrier = r.sum.carrier` by simp[]
      \\ pop_assum SUBST1_TAC
      \\ irule GBAG_in_carrier
      \\ imp_res_tac mpoly_def
      \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD] )
    \\ pop_assum kall_tac
    \\ eq_tac
    >- (
      simp[BAG_FILTER_BAG_OF_SET]
      \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE _ (BAG_OF_SET s)`
      \\ Cases_on`s = {}` \\ simp[]
      \\ pop_assum mp_tac \\ simp[Abbr`s`]
      \\ simp[Once EXTENSION, EXISTS_PROD] )
    \\ disch_then(qx_choosel_then[`m1`,`m2`]strip_assume_tac)
    \\ simp[BAG_FILTER_BAG_OF_SET]
    \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s = {(m1,m2)}` suffices_by (
      simp[BAG_OF_SET_INSERT_NON_ELEMENT]
      \\ imp_res_tac mpoly_def
      \\ fs[SUBSET_DEF, PULL_EXISTS]
      \\ fs[monomials_def, rrestrict_def]
      \\ fs[IntegralDomain_def] )
    \\ simp[Abbr`s`, Once EXTENSION, FORALL_PROD]
    \\ qx_genl_tac[`t1`,`t2`]
    \\ reverse eq_tac >- metis_tac[]
    \\ strip_tac
    \\ fs[IN_DISJOINT, support_def, PULL_EXISTS]
    \\ pop_assum mp_tac
    \\ simp[FUN_EQ_THM, BAG_UNION]
    \\ strip_tac
    \\ simp[GSYM FORALL_AND_THM]
    \\ qx_gen_tac`z`
    \\ first_x_assum(qspec_then`z`mp_tac)
    \\ Cases_on`BAG_IN z m1`
    >- (
      `¬BAG_IN z m2` by metis_tac[]
      \\ `¬BAG_IN z m2` by metis_tac[]
      \\ `¬BAG_IN z t2` by metis_tac[]
      \\ `m2 z = 0 /\ t2 z = 0` by fs[BAG_IN, BAG_INN]
      \\ simp[] )
    \\ Cases_on`BAG_IN z m2`
    >- (
      `¬BAG_IN z t1` by metis_tac[]
      \\ `m1 z = 0 /\ t1 z = 0` by fs[BAG_IN, BAG_INN]
      \\ simp[] )
    \\ `m1 z = 0 ∧ m2 z = 0` by fs[BAG_IN, BAG_INN]
    \\ simp[])
  \\ rw[]
  \\ simp[mpoly_mul_BAG_FILTER_cross]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ `s = {(m1,m2)}` suffices_by (
    simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ imp_res_tac mpoly_def
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[monomials_def, rrestrict_def]
    \\ fs[IntegralDomain_def] )
  \\ simp[Abbr`s`, Once EXTENSION, FORALL_PROD]
  \\ qx_genl_tac[`t1`,`t2`]
  \\ reverse eq_tac >- metis_tac[]
  \\ strip_tac
  \\ fs[IN_DISJOINT, support_def, PULL_EXISTS]
  \\ pop_assum mp_tac
  \\ simp[FUN_EQ_THM, BAG_UNION]
  \\ strip_tac
  \\ simp[GSYM FORALL_AND_THM]
  \\ qx_gen_tac`z`
  \\ first_x_assum(qspec_then`z`mp_tac)
  \\ Cases_on`BAG_IN z m1`
  >- (
    `¬BAG_IN z m2` by metis_tac[]
    \\ `¬BAG_IN z m2` by metis_tac[]
    \\ `¬BAG_IN z t2` by metis_tac[]
    \\ `m2 z = 0 /\ t2 z = 0` by fs[BAG_IN, BAG_INN]
    \\ simp[] )
  \\ Cases_on`BAG_IN z m2`
  >- (
    `¬BAG_IN z t1` by metis_tac[]
    \\ `m1 z = 0 /\ t1 z = 0` by fs[BAG_IN, BAG_INN]
    \\ simp[] )
  \\ `m1 z = 0 ∧ m2 z = 0` by fs[BAG_IN, BAG_INN]
  \\ simp[]
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
  \\ simp[MAX_SET_EQ_0, Abbr`ls`]
  \\ simp[IMAGE_EQ_SING]
  \\ Cases_on`monomials r p = {}` \\ simp[]
  \\ rw[BAG_IN, BAG_INN]
  \\ rw[EQ_IMP_THM]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem degree_of_mpoly_of_poly:
  Ring r /\ poly p ==>
  degree_of r (mpoly_of_poly r v p) v = deg p
Proof
  rw[degree_of_def, monomials_mpoly_of_poly]
  \\ rw[GSYM IMAGE_COMPOSE, combinTheory.o_DEF]
  \\ rw[polynomialTheory.poly_deg_def]
  \\ DEP_REWRITE_TAC[MAX_SET_TEST_IFF]
  \\ simp[]
  \\ fs[polyRingTheory.poly_def_alt]
  \\ simp[Once EXTENSION]
  \\ conj_asm2_tac >- metis_tac[]
  \\ simp[rich_listTheory.EL_PRE_LENGTH]
  \\ simp[arithmeticTheory.PRE_SUB1]
  \\ CCONTR_TAC \\ fs[]
QED

Theorem degree_of_sum_le:
  !b. FINITE_BAG b ==>
  Ring r /\ SET_OF_BAG b SUBSET (mpoly_ring r s).carrier ==>
  degree_of r (GBAG (mpoly_ring r s).sum b) v <=
  MAX_SET (IMAGE (flip (degree_of r) v) (SET_OF_BAG b))
Proof
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  >- rw[mpoly_ring_def]
  \\ fs[]
  \\ simp[SET_OF_BAG_INSERT]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ conj_tac >- fs[SUBSET_DEF, PULL_EXISTS]
  \\ `(mpoly_ring r s).sum.op = mpoly_add r` by simp[mpoly_ring_def]
  \\ pop_assum (fn th => simp[Once th])
  \\ qmatch_goalsub_abbrev_tac`mpoly_add r e f`
  \\ `f IN (mpoly_ring r s).carrier`
  by (
    qunabbrev_tac`f`
    \\ `(mpoly_ring r s).carrier = (mpoly_ring r s).sum.carrier`by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[]
    \\ fs[PULL_EXISTS, SUBSET_DEF] )
  \\ irule arithmeticTheory.LESS_EQ_TRANS
  \\ qexists_tac`MAX (degree_of r e v) (degree_of r f v)`
  \\ conj_tac
  >- (
    irule degree_of_mpoly_add_le
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[mpoly_ring_def, mpoly_def] )
  \\ DEP_REWRITE_TAC[MAX_SET_THM]
  \\ simp[]
  \\ disj2_tac
  \\ first_x_assum irule
  \\ fs[SUBSET_DEF, PULL_EXISTS]
QED

(* mpoly_of_poly is a ring isomorphism *)

Theorem RingIso_mpoly_of_poly:
  Ring r ==>
  RingIso (mpoly_of_poly r v) (poly_ring r) (mpoly_ring r {v})
Proof
  strip_tac
  \\ rewrite_tac[RingIso_def]
  \\ reverse conj_asm2_tac
  >- (
    simp[mpoly_ring_def, polynomialTheory.poly_ring_def]
    \\ irule BIJ_mpoly_of_poly \\ simp[] )
  \\ simp[RingHomo_def]
  \\ conj_asm1_tac >- fs[BIJ_DEF, INJ_DEF]
  \\ simp[GroupHomo_def, poly_ring_ring]
  \\ conj_tac
  >- (
    simp[mpoly_ring_def]
    \\ rpt strip_tac
    \\ irule mpoly_of_poly_add
    \\ fs[polynomialTheory.poly_ring_def] )
  \\ simp[MonoidHomo_def, poly_ring_ring]
  \\ reverse conj_tac
  >- (
    simp[mpoly_ring_def]
    \\ simp[mpoly_of_poly_def, FUN_EQ_THM]
    \\ simp[polynomialTheory.poly_ring_def]
    \\ rw[mpoly_one_def] \\ gs[] \\ rw[rrestrict_def]
    \\ gs[EMPTY_BAG] \\ pop_assum mp_tac \\ rw[]
    >- (
      Cases_on`x v` \\ gs[]
      \\ fs[FUN_EQ_THM, SET_OF_BAG, BAG_IN, BAG_INN]
      \\ metis_tac[DECIDE``~(0 >= 1n)``] )
    \\ fs[FUN_EQ_THM]
    \\ metis_tac[] )
  \\ simp[mpoly_ring_def]
  \\ rpt strip_tac
  \\ irule mpoly_of_poly_mul
  \\ fs[polynomialTheory.poly_ring_def]
QED

Theorem RingIso_poly_of_mpoly:
  Ring r ==>
  RingIso (poly_of_mpoly r) (mpoly_ring r {v}) (poly_ring r)
Proof
  strip_tac
  \\ drule RingIso_mpoly_of_poly
  \\ disch_then(qspec_then`v`strip_assume_tac)
  \\ irule ring_iso_sym_any
  \\ simp[poly_ring_ring]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[polynomialTheory.poly_ring_def, mpoly_ring_def]
  \\ metis_tac[poly_of_mpoly_of_poly, mpoly_of_poly_of_mpoly,
               poly_poly_of_mpoly, mpoly_def]
QED

Theorem poly_of_mpoly_add:
  Ring r /\ mpoly r p /\ mpoly r q /\ support r p SUBSET {v} /\ support r q SUBSET {v} ==>
  poly_of_mpoly r (mpoly_add r p q) =
  poly_of_mpoly r p + poly_of_mpoly r q
Proof
  strip_tac
  \\ drule RingIso_poly_of_mpoly
  \\ disch_then(qspec_then`v`strip_assume_tac)
  \\ imp_res_tac RingIso_def
  \\ imp_res_tac RingHomo_def
  \\ imp_res_tac GroupHomo_def
  \\ fs[mpoly_ring_def]
QED

Theorem mpoly_ring_empty_support_iso:
  Ring r ==>
  RingIso (\p. p {||}) (mpoly_ring r {}) r
Proof
  simp[RingIso_def]
  \\ strip_tac
  \\ reverse conj_asm2_tac
  >- (
    simp[mpoly_ring_def, empty_support]
    \\ simp[BIJ_IFF_INV]
    \\ simp[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ qexists_tac`\x m. if m = {||} then x else r.sum.id`
    \\ reverse(rw[] \\ rw[])
    >- (
      simp[FUN_EQ_THM]
      \\ rw[EMPTY_BAG]
      \\ gs[monomials_def, rrestrict_def, EMPTY_BAG]
      >- ( AP_TERM_TAC \\ simp[FUN_EQ_THM] )
      \\ irule EQ_SYM  \\ CCONTR_TAC
      \\ res_tac \\ fs[] )
    \\ pop_assum mp_tac
    \\ qmatch_goalsub_abbrev_tac`monomials r p`
    \\ `monomials r p SUBSET {{||}}`
    by (
      rw[monomials_def, SUBSET_DEF, Abbr`p`]
      \\ CCONTR_TAC \\ gs[rrestrict_def] )
    >- fs[SUBSET_DEF]
    \\ rw[]
    \\ irule SUBSET_FINITE
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ simp[RingHomo_def]
  \\ conj_asm1_tac >- fs[BIJ_DEF, INJ_DEF]
  \\ simp[GroupHomo_def]
  \\ conj_tac
  >- (
    gs[mpoly_ring_def]
    \\ gs[mpoly_add_def]
    \\ simp[rrestrict_def] )
  \\ simp[MonoidHomo_def]
  \\ gs[mpoly_ring_def]
  \\ simp[mpoly_one_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ simp[mpoly_mul_BAG_FILTER_cross]
  \\ Cases_on`monomials r p = {}` \\ gs[]
  >- (
    `p {||} = #0` suffices_by rw[]
    \\ fs[monomials_def, mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ pop_assum mp_tac \\ simp[Once EXTENSION]
    \\ simp[rrestrict_def] )
  \\ Cases_on`monomials r p' = {}` \\ gs[]
  >- (
    `p' {||} = #0` suffices_by rw[]
    \\ fs[monomials_def, mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ pop_assum mp_tac \\ simp[Once EXTENSION]
    \\ simp[rrestrict_def] )
  \\ gs[empty_support]
  \\ `monomials r p = {{||}} /\ monomials r p' = {{||}}`
  by (
    simp[SET_EQ_SUBSET]
    \\ Cases_on`monomials r p` \\ gs[]
    \\ Cases_on`monomials r p'` \\ gs[] )
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ `s = {({||},{||})}` by (simp[Abbr`s`, Once EXTENSION, FORALL_PROD] \\ metis_tac[])
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ gs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[rrestrict_def]
QED

(* Isolating a variable: the other variable polynomials become coefficients *)

Definition remove_var_mono_def:
  remove_var_mono r x p m t =
    if t = (x =+ 0n) m then rrestrict r (p m) else r.sum.id
End

Theorem monomials_remove_var_mono_SUBSET:
  !r p x m. monomials r (remove_var_mono r x p m) ⊆  IMAGE (x =+ 0) (monomials r p)
Proof
  rw[SUBSET_DEF, monomials_def]
  \\ gs[rrestrict_def, remove_var_mono_def]
  \\ pop_assum mp_tac \\ rw[] \\ rfs[]
  \\ qexists_tac`m` \\ simp[]
QED

Theorem mpoly_remove_var_mono:
  Ring r /\ mpoly r p /\ m IN monomials r p ==>
  mpoly r (remove_var_mono r x p m)
Proof
  simp[mpoly_def]
  \\ strip_tac
  \\ qspecl_then[`r`,`p`,`x`,`m`]assume_tac monomials_remove_var_mono_SUBSET
  \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, IMAGE_FINITE]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ rw[remove_var_mono_def]
QED

Theorem support_remove_var_mono:
  m IN monomials (r:'a ring) p ==>
  support r (remove_var_mono r x p m) SUBSET support r p DELETE x
Proof
  rw[support_def, PULL_EXISTS]
  \\ qspecl_then[`r`,`p`,`x`,`m`]assume_tac monomials_remove_var_mono_SUBSET
  \\ fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
  \\ first_x_assum drule
  \\ strip_tac
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ fs[BAG_IN, BAG_INN]
  \\ qpat_x_assum`_ >= 1`mp_tac
  \\ rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem remove_var_mono_nonzero[simp]:
  Ring r /\ m IN monomials r p ==>
  remove_var_mono r x p m <> K #0
Proof
  rw[Once FUN_EQ_THM, remove_var_mono_def]
  \\ qexists_tac`(x =+ 0) m`
  \\ fs[monomials_def]
QED

Theorem remove_var_mono_inj:
  Ring r /\ mpoly r p /\ mpoly r q /\
  remove_var_mono r x p =
  remove_var_mono r x q
  ==>
  p = q
Proof
  simp[FUN_EQ_THM, remove_var_mono_def]
  \\ strip_tac
  \\ qx_gen_tac`m`
  \\ first_x_assum(qspecl_then[`m`,`(x =+ 0) m`]mp_tac)
  \\ simp[]
  \\ simp[rrestrict_def]
  \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem degree_of_remove_var_mono_le:
  FINITE (monomials r p) /\ x <> y ==>
  degree_of r (remove_var_mono r x p m) y <= degree_of r p y
Proof
  simp[degree_of_def]
  \\ qmatch_goalsub_abbrev_tac`IMAGE _ s`
  \\ `s SUBSET IMAGE (x =+ 0) (monomials r p)`
  by metis_tac[monomials_remove_var_mono_SUBSET]
  \\ strip_tac
  \\ `FINITE s` by metis_tac[SUBSET_FINITE, IMAGE_FINITE]
  \\ irule SUBSET_MAX_SET
  \\ simp[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ rw[]
  \\ res_tac
  \\ rw[]
  \\ rw[combinTheory.APPLY_UPDATE_THM]
  \\ metis_tac[]
QED

Definition isolate_var_mono_def:
  isolate_var_mono r x p m t =
    if t = (λy. if y = x then m x else 0n)
    then remove_var_mono r x p m
    else K r.sum.id
End

Theorem monomials_isolate_var_mono:
  Ring r /\ mpoly r p /\ m IN monomials r p ==>
  monomials (mpoly_ring r (support r p DELETE x)) (isolate_var_mono r x p m) =
  {λy. if y = x then m x else 0}
Proof
  strip_tac
  \\ rw[Once monomials_def]
  \\ rw[SET_EQ_SUBSET, SUBSET_DEF]
  >- (
    fs[rrestrict_def]
    \\ pop_assum mp_tac
    \\ rw[]
    \\ fs[isolate_var_mono_def]
    \\ fs[Once mpoly_ring_def]
    \\ pop_assum mp_tac \\ rw[] )
  \\ simp[isolate_var_mono_def]
  \\ imp_res_tac mpoly_remove_var_mono
  \\ simp[rrestrict_def]
  \\ once_rewrite_tac[mpoly_ring_def]
  \\ simp[]
  \\ simp[support_remove_var_mono]
  \\ simp[remove_var_mono_def, FUN_EQ_THM]
  \\ qexists_tac`(x =+ 0) m`
  \\ rw[]
  \\ fs[monomials_def]
QED

Theorem mpoly_isolate_var_mono:
  Ring r /\ mpoly r p /\ m IN monomials r p ==>
  mpoly (mpoly_ring r (support r p DELETE x))
    (isolate_var_mono r x p m)
Proof
  strip_tac
  \\ simp[Once mpoly_def]
  \\ simp[monomials_isolate_var_mono]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[isolate_var_mono_def]
  \\ rw[]
  >- (
    imp_res_tac mpoly_remove_var_mono
    \\ simp[mpoly_ring_def]
    \\ simp[support_remove_var_mono] )
  \\ simp[mpoly_ring_def]
QED

Theorem support_isolate_var_mono:
  Ring r /\ mpoly r p /\ m IN monomials r p ==>
  support (mpoly_ring r (support r p DELETE x))
    (isolate_var_mono r x p m) = if BAG_IN x m then {x} else {}
Proof
  strip_tac
  \\ simp[Once support_def]
  \\ simp[monomials_isolate_var_mono]
  \\ simp[SET_OF_BAG]
  \\ simp[Once EXTENSION]
  \\ rw[BAG_IN, BAG_INN]
  \\ fs[]
QED

Theorem isolate_var_mono_inj:
  Ring r /\ mpoly r p /\ mpoly r q ==>
  isolate_var_mono r x p = isolate_var_mono r x q
  ==> p = q
Proof
  rw[isolate_var_mono_def, Ntimes FUN_EQ_THM 2]
  \\ irule remove_var_mono_inj
  \\ qexists_tac`r` \\ simp[]
  \\ qexists_tac`x`
  \\ simp[Once FUN_EQ_THM]
  \\ qx_gen_tac`m`
  \\ first_x_assum(qspec_then`m`mp_tac)
  \\ qmatch_goalsub_abbrev_tac`COND (_ = f)`
  \\ disch_then(qspec_then`f`mp_tac) \\ simp[]
QED

Definition isolate_var_ring_def:
  isolate_var_ring r x p =
    mpoly_ring (mpoly_ring r (support r p DELETE x)) {x}
End

Theorem isolate_var_ring_ring[simp]:
  Ring r ==> Ring (isolate_var_ring r x p)
Proof
  rw[isolate_var_ring_def]
QED

Theorem isolate_var_mono_in_carrier:
  Ring r /\ mpoly r p /\ m IN monomials r p ==>
  isolate_var_mono r x p m IN (isolate_var_ring r x p).carrier
Proof
  rw[isolate_var_ring_def]
  \\ qmatch_goalsub_abbrev_tac`mpoly_ring mr`
  \\ simp[mpoly_ring_def]
  \\ simp[mpoly_isolate_var_mono, Abbr`mr`]
  \\ simp[support_isolate_var_mono]
  \\ rw[]
QED

Definition isolate_var_def:
  isolate_var r x p =
    GBAG (isolate_var_ring r x p).sum
      (BAG_IMAGE (isolate_var_mono r x p)
        (BAG_OF_SET (monomials r p)))
End

Theorem isolate_var_in_carrier:
  Ring r /\ mpoly r p ==>
  isolate_var r x p ∈ (isolate_var_ring r x p).carrier
Proof
  rw[isolate_var_def]
  \\ `(isolate_var_ring r x p).carrier = (isolate_var_ring r x p).sum.carrier`
  by metis_tac[isolate_var_ring_ring, ringTheory.ring_carriers]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ imp_res_tac mpoly_def
  \\ simp[abelian_group_is_abelian_monoid]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[isolate_var_mono_in_carrier]
QED

Theorem isolate_var_coeff:
  Ring r /\ mpoly r p ==>
  isolate_var r x p (λy. if y = x then n else 0) =
  GBAG (mpoly_ring r (support r p DELETE x)).sum
    (BAG_OF_SET (IMAGE (remove_var_mono r x p)
                       (monomials r p INTER { m | m x = n })))
Proof
  strip_tac
  \\ imp_res_tac mpoly_def
  \\ simp[isolate_var_def]
  \\ simp[isolate_var_ring_def]
  \\ DEP_ONCE_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ simp[abelian_group_is_abelian_monoid]
  \\ simp[GSYM isolate_var_ring_def]
  \\ simp[SUBSET_DEF, PULL_EXISTS, isolate_var_mono_in_carrier]
  \\ simp[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ simp[isolate_var_mono_def]
  \\ irule GITBAG_CONG
  \\ simp[PULL_EXISTS]
  \\ simp[SUBSET_DEF, PULL_EXISTS, abelian_group_is_abelian_monoid]
  \\ reverse conj_tac
  >- (
    rw[] \\ simp[mpoly_ring_def]
    \\ simp[mpoly_remove_var_mono, support_remove_var_mono] )
  \\ simp[mpoly_ring_def]
  \\ gen_tac
  \\ disch_then assume_tac
  \\ simp[BAG_IMAGE_DEF]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ simp[BAG_CARD_BAG_OF_SET]
  \\ simp[BAG_OF_SET]
  \\ IF_CASES_TAC
  >- (
    qmatch_goalsub_abbrev_tac`_ INTER s`
    \\ first_x_assum(qx_choose_then`m`strip_assume_tac)
    \\ `s = {m}`
    by (
      simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF]
      \\ `∀f. (λy. if y = x then n else 0) = (λy. if x = y then f y else 0)
      ⇔ f x = n`
      by (
        rw[FUN_EQ_THM, EQ_IMP_THM]
        \\ metis_tac[] )
      \\ simp[]
      \\ qx_gen_tac`z`
      \\ rw[]
      \\ fs[remove_var_mono_def, FUN_EQ_THM]
      \\ pop_assum mp_tac
      \\ rw[]
      \\ first_x_assum(qspec_then`(x =+ 0) m`mp_tac)
      \\ first_x_assum(qspec_then`(x =+ 0) m`mp_tac)
      \\ simp[]
      \\ IF_CASES_TAC \\ simp[]
      \\ fs[combinTheory.APPLY_UPDATE_THM]
      \\ TRY(IF_CASES_TAC \\ fs[] \\
             ntac 2 (pop_assum mp_tac) \\ rw[]
             \\ fs[monomials_def] \\ NO_TAC)
      \\ metis_tac[] )
    \\ simp[]
    \\ simp[INTER_SING] )
  \\ qmatch_goalsub_abbrev_tac`CARD s`
  \\ `s = {}` suffices_by rw[]
  \\ simp[Abbr`s`, Once EXTENSION]
  \\ pop_assum mp_tac
  \\ simp[] \\ strip_tac
  \\ rw[]
  \\ fs[FUN_EQ_THM]
  \\ metis_tac[]
QED

Theorem isolate_var_coeff_zero:
  Ring r /\ mpoly r p /\
  ((?y. x <> y /\ BAG_IN y b) ∨ !m. m IN monomials r p ==> m x <> b x) ==>
  isolate_var r x p b = K #0
Proof
  rw[isolate_var_def, isolate_var_ring_def]
  \\ imp_res_tac mpoly_def
  \\ DEP_ONCE_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ simp[abelian_group_is_abelian_monoid]
  \\ simp[PULL_EXISTS, SUBSET_DEF]
  \\ simp[GSYM isolate_var_ring_def]
  \\ simp[isolate_var_mono_in_carrier]
  \\ qmatch_goalsub_abbrev_tac`GBAG rr _`
  \\ `rr.id = K #0`
  by ( simp[Abbr`rr`, mpoly_ring_def] )
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ irule IMP_GBAG_EQ_ID
  \\ simp[Abbr`rr`, abelian_group_is_abelian_monoid]
  \\ simp[BAG_EVERY, PULL_EXISTS]
  \\ simp[isolate_var_mono_def]
  \\ rw[mpoly_ring_def]
  \\ fs[BAG_IN, BAG_INN] \\ rfs[]
  \\ rw[remove_var_mono_def, FUN_EQ_THM]
  \\ metis_tac[]
QED

Theorem degree_of_isolate_var_le:
  Ring r /\ mpoly r p ==>
  degree_of r (isolate_var r v p m) x <= degree_of r p x
Proof
  rw[isolate_var_def]
  \\ rewrite_tac[isolate_var_ring_def]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ imp_res_tac mpoly_def
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[GSYM isolate_var_ring_def]
  \\ simp[isolate_var_mono_in_carrier]
  \\ qmatch_goalsub_abbrev_tac`degree_of r (GBAG (mpoly_ring r s).sum b)`
  \\ irule arithmeticTheory.LESS_EQ_TRANS
  \\ qexists_tac`MAX_SET (IMAGE (flip (degree_of r) x) (SET_OF_BAG b))`
  \\ conj_tac
  >- (
    irule degree_of_sum_le
    \\ simp[Abbr`b`]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ rpt strip_tac
    \\ drule_then (drule_then drule) isolate_var_mono_in_carrier
    \\ simp[isolate_var_ring_def]
    \\ disch_then(qspec_then`v`mp_tac)
    \\ qmatch_goalsub_abbrev_tac`mpoly_ring rr`
    \\ simp[mpoly_ring_def]
    \\ simp[Once mpoly_def]
    \\ simp[Once SUBSET_DEF, PULL_EXISTS]
    \\ simp[Abbr`rr`, mpoly_ring_def] )
  \\ qmatch_goalsub_abbrev_tac`MAX_SET ss`
  \\ Cases_on`ss = {}` \\ simp[]
  \\ `FINITE ss` by simp[Abbr`ss`, Abbr`b`]
  \\ `∀a. a IN ss ==> a <= degree_of r p x`
  suffices_by metis_tac[MAX_SET_DEF]
  \\ simp[Abbr`ss`, PULL_EXISTS]
  \\ simp[Abbr`b`, PULL_EXISTS]
  \\ rw[isolate_var_mono_def]
  \\ reverse(Cases_on`x = v`)
  >- ( irule degree_of_remove_var_mono_le \\ simp[] )
  \\ `degree_of r (remove_var_mono r v p y) x = 0`
  suffices_by simp[]
  \\ `~(1 <= degree_of r (remove_var_mono r v p y) x)`
  suffices_by simp[]
  \\ DEP_REWRITE_TAC[GSYM support_degree_of]
  \\ conj_tac >-
  metis_tac[monomials_remove_var_mono_SUBSET, SUBSET_FINITE, IMAGE_FINITE]
  \\ metis_tac[support_remove_var_mono, SUBSET_DEF, IN_DELETE]
QED

Definition one_mono_def:
  one_mono r x n y = if y = x then n else r.sum.id
End

Theorem monomials_one_mono:
  Ring r ==>
  monomials r (one_mono r x n) =
  if n = r.sum.id \/ n NOTIN r.carrier then {} else {x}
Proof
  rw[monomials_def, one_mono_def, EXTENSION] \\ rw[] \\ fs[]
  \\ rw[rrestrict_def]
QED

Theorem mpoly_one_mono[simp]:
  Ring r /\ n IN r.carrier ==>
  mpoly r (one_mono r v n)
Proof
  rw[mpoly_def, one_mono_def, SUBSET_DEF] \\ rw[]
  \\ rw[monomials_one_mono]
QED

Theorem support_one_mono:
  Ring r ==>
  support r (one_mono r x n) =
  if n = r.sum.id \/ n NOTIN r.carrier then {} else SET_OF_BAG x
Proof
  rw[support_def, monomials_one_mono]
QED

Theorem sum_distinct_one_monomials_nonzero:
  Ring r /\ (∀m. m IN ms /\ m <> K r.sum.id ==>
                 ?v n. SET_OF_BAG v SUBSET s /\
                       n IN r.carrier /\
                       m = one_mono r v n /\
                       (!m'. m' IN ms /\ m' v <> #0 ==> m' = m))
  /\ FINITE ms
  ==>
  (GBAG (mpoly_ring r s).sum (BAG_OF_SET ms) = K #0 <=> ms SUBSET {K #0})
Proof
  strip_tac
  \\ reverse EQ_TAC
  >- (
    Cases_on`ms` \\ simp[]
    >- rw[mpoly_ring_def]
    \\ rw[]
    \\ Cases_on`t` \\ fs[]
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ simp[mpoly_ring_def] )
  \\ qpat_x_assum`∀m. _`mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac`ms`
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ strip_tac
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac
  >- (
    pop_assum mp_tac
    \\ dsimp[]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[]
    \\ strip_tac
    \\ qexists_tac`v`
    \\ metis_tac[] )
  \\ strip_tac
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[mpoly_ring_def, SUBSET_DEF, abelian_group_is_abelian_monoid]
    \\ reverse conj_tac
    >- (
      Cases_on`e = K #0` \\ simp[]
      \\ first_x_assum(qspec_then`e`mp_tac)
      \\ simp[] \\ strip_tac
      \\ simp[]
      \\ simp[support_one_mono]
      \\ fs[SUBSET_DEF]
      \\ rw[] )
    \\ gen_tac \\ strip_tac
    \\ Cases_on`x = K #0` \\ simp[]
    \\ first_x_assum(qspec_then`x`mp_tac)
    \\ simp[] \\ strip_tac
    \\ simp[]
    \\ simp[support_one_mono]
    \\ fs[SUBSET_DEF]
    \\ rw[] )
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`_ e g`
  \\ simp[mpoly_ring_def]
  \\ `g IN (mpoly_ring r s).sum.carrier`
  by (
    qunabbrev_tac`g`
    \\ irule GBAG_in_carrier
    \\ simp[] )
  \\ `mpoly r g` by fs[mpoly_ring_def]
  \\ Cases_on`e = K #0` \\ simp[mpoly_add_zero]
  \\ simp[Once mpoly_add_comm]
  \\ `mpoly r e` by fs[mpoly_ring_def]
  \\ Cases_on`g = K #0` \\ simp[mpoly_add_zero]
  \\ first_assum(qspec_then`e`mp_tac)
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ simp[FUN_EQ_THM]
  \\ simp[mpoly_add_def]
  \\ qexists_tac`v`
  \\ simp[one_mono_def]
  \\ simp[rrestrict_def]
  \\ Cases_on`n = #0`
  >- fs[one_mono_def, FUN_EQ_THM]
  \\ rw[]
  \\ `g v = #0` suffices_by rw[]
  \\ simp[Abbr`g`]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ simp[]
  \\ irule IMP_GBAG_EQ_ID
  \\ simp[BAG_EVERY, PULL_EXISTS, abelian_group_is_abelian_monoid]
  \\ qx_gen_tac`m` \\ strip_tac
  \\ Cases_on`m = K #0` \\ simp[]
  \\ first_x_assum(qspec_then`m`mp_tac)
  \\ simp[]
  \\ metis_tac[]
QED

Theorem monomials_isolate_var:
  Ring r /\ mpoly r p ==>
  monomials (mpoly_ring r (support r p DELETE x))
    (isolate_var r x p) =
    IMAGE (λm y. if y = x then m x else 0) (monomials r p)
Proof
  simp[Once monomials_def]
  \\ strip_tac
  \\ imp_res_tac isolate_var_in_carrier
  \\ pop_assum mp_tac
  \\ simp[isolate_var_ring_def]
  \\ disch_then(qspec_then`x`mp_tac)
  \\ qmatch_goalsub_abbrev_tac`mpoly_ring mr _`
  \\ simp[mpoly_ring_def]
  \\ strip_tac
  \\ simp[rrestrict_def]
  \\ imp_res_tac mpoly_def
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
  \\ conj_tac
  >- (
    gen_tac
    \\ `mr.sum.id = K #0` by simp[Abbr`mr`, mpoly_ring_def]
    \\ pop_assum SUBST1_TAC
    \\ strip_tac
    \\ drule(CONTRAPOS isolate_var_coeff_zero)
    \\ simp[DISJ_EQ_IMP] \\ strip_tac
    \\ qexists_tac`m` \\ simp[]
    \\ simp[FUN_EQ_THM]
    \\ rw[] \\ rw[]
    \\ res_tac \\ fs[BAG_IN]
    \\ fs[BAG_INN]
    \\ first_x_assum(qspec_then`y`mp_tac) \\ simp[])
  \\ ntac 2 strip_tac
  \\ qmatch_goalsub_abbrev_tac`isolate_var r x p f`
  \\ `f = λy. if y = x then m x else 0` by (
    rw[Abbr`f`, FUN_EQ_THM]
    \\ IF_CASES_TAC \\ simp[] )
  \\ simp[Abbr`f`]
  \\ pop_assum SUBST1_TAC
  \\ simp[isolate_var_coeff]
  \\ qmatch_goalsub_abbrev_tac`g <> _`
  \\ `mr.sum.id = K #0` by simp[Abbr`mr`, mpoly_ring_def]
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`g`
  \\ qunabbrev_tac`mr`
  \\ DEP_REWRITE_TAC[sum_distinct_one_monomials_nonzero]
  \\ simp[PULL_EXISTS, SUBSET_DEF]
  \\ qexists_tac`m` \\ simp[]
  \\ qx_gen_tac`m2` \\ strip_tac
  \\ qexists_tac`(x =+ 0) m2`
  \\ qexists_tac`p m2`
  \\ simp[support_def, PULL_EXISTS]
  \\ simp[Once FUN_EQ_THM]
  \\ simp[remove_var_mono_def, one_mono_def]
  \\ `p m2 IN r.carrier` by fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ simp[Once rrestrict_def]
  \\ conj_tac
  >- (
    qx_gen_tac`y`
    \\ strip_tac
    \\ qexists_tac`m2`
    \\ simp[]
    \\ fs[BAG_IN, BAG_INN, combinTheory.APPLY_UPDATE_THM]
    \\ pop_assum mp_tac \\ rw[] )
  \\ qx_gen_tac`m3`
  \\ IF_CASES_TAC \\ simp[]
  \\ `p m3 IN r.carrier` by fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ simp[rrestrict_def]
  \\ strip_tac
  \\ `m3 = m2` suffices_by simp[]
  \\ simp[Once FUN_EQ_THM]
  \\ fs[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ metis_tac[]
QED

Theorem mpoly_isolate_var[simp]:
  Ring r /\ mpoly r p ==>
  mpoly (mpoly_ring r (support r p DELETE x)) (isolate_var r x p)
Proof
  strip_tac
  \\ simp[mpoly_def]
  \\ simp[monomials_isolate_var]
  \\ imp_res_tac mpoly_def
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[isolate_var_def]
  \\ rw[isolate_var_ring_def]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ simp[]
  \\ simp[GSYM isolate_var_ring_def]
  \\ simp[SUBSET_DEF, PULL_EXISTS, isolate_var_mono_in_carrier]
  \\ qmatch_goalsub_abbrev_tac`rr.sum`
  \\ `rr.carrier = rr.sum.carrier` by simp[Abbr`rr`]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ simp[Abbr`rr`, abelian_group_is_abelian_monoid]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qx_gen_tac`m`
  \\ strip_tac
  \\ imp_res_tac isolate_var_mono_in_carrier
  \\ fs[isolate_var_ring_def]
  \\ first_x_assum(qspec_then`x`mp_tac)
  \\ qmatch_goalsub_abbrev_tac`mpoly_ring rr`
  \\ simp[mpoly_ring_def]
  \\ simp[mpoly_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem support_isolate_var:
  Ring r /\ mpoly r p ==>
  support (mpoly_ring r (support r p DELETE x)) (isolate_var r x p) =
  {x} INTER support r p
Proof
  rw[Once support_def]
  \\ simp[monomials_isolate_var]
  \\ simp[support_def]
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ simp[BAG_IN, BAG_INN]
  \\ rw[EQ_IMP_THM]
  \\ rpt (pop_assum mp_tac) \\ rw[]
  \\ metis_tac[]
QED

Theorem degree_of_isolate_var:
  Ring r /\ mpoly r p /\ support r p SUBSET s ==>
  degree_of (mpoly_ring r (s DELETE v)) (isolate_var r v p) v =
  degree_of r p v
Proof
  strip_tac
  \\ rw[degree_of_def]
  \\ `monomials (mpoly_ring r (s DELETE v)) (isolate_var r v p) =
      monomials (mpoly_ring r (support r p DELETE v)) (isolate_var r v p)`
  by (
    irule EQ_SYM
    \\ irule monomials_mpoly_ring_more_support
    \\ simp[mpoly_isolate_var]
    \\ fs[SUBSET_DEF] )
  \\ pop_assum SUBST1_TAC
  \\ simp[monomials_isolate_var]
  \\ simp[GSYM IMAGE_COMPOSE, combinTheory.o_DEF]
QED

(* Restoring the isolated variable *)

Definition restore_var_def:
  restore_var r x p m =
    p (λt. if t = x then m x else 0n) ((x =+ 0) m)
End

Theorem restore_isolate_var:
  Ring r /\ mpoly r p ==>
  restore_var r x (isolate_var r x p) = p
Proof
  rw[FUN_EQ_THM]
  \\ rw[restore_var_def]
  \\ rw[isolate_var_coeff]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ `FINITE (monomials r p)` by fs[mpoly_def]
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[mpoly_ring_def]
  \\ simp[mpoly_remove_var_mono]
  \\ simp[support_remove_var_mono]
  \\ drule mpoly_sum_monomials
  \\ disch_then drule
  \\ disch_then(qspec_then`support r p`mp_tac)
  \\ impl_tac >- simp[]
  \\ qmatch_goalsub_abbrev_tac`hide = p _`
  \\ disch_then (SUBST1_TAC o SYM)
  \\ simp[Abbr`hide`]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[mpoly_ring_def]
  \\ simp[GSYM one_mono_def]
  \\ simp_tac(srw_ss()++ETA_ss)[]
  \\ `!x. p x IN r.carrier` by fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ simp[mpoly_one_mono]
  \\ simp[support_one_mono]
  \\ conj_tac >- (
    rw[support_def]
    \\ rw[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ simp[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ simp[]
  \\ conj_tac
  >- (
    rw[Once FUN_EQ_THM, remove_var_mono_def]
    \\ fs[monomials_def]
    \\ first_x_assum(qspec_then`(x =+ 0)y`mp_tac)
    \\ simp[] \\ rw[]
    \\ simp[Once FUN_EQ_THM]
    \\ fs[combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
    \\ metis_tac[] )
  \\ simp[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ simp[remove_var_mono_def]
  \\ simp[one_mono_def]
  \\ simp[rrestrict_def]
  \\ DEP_REWRITE_TAC[GSYM (MP_CANON GBAG_IMAGE_FILTER)]
  \\ simp[SUBSET_DEF, PULL_EXISTS, abelian_group_is_abelian_monoid]
  \\ simp[GSYM BAG_FILTER_BAG_OF_SET]
  \\ simp[BAG_FILTER_FILTER]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ rw[combinTheory.APPLY_UPDATE_THM]
  \\ metis_tac[]
QED

Theorem monomials_restore_var:
  Ring r /\ mpoly (mpoly_ring r s) p /\ support (mpoly_ring r s) p SUBSET {x} /\
  x NOTIN s ==>
  monomials r (restore_var r x p) =
  BIGUNION (IMAGE (\m. IMAGE (x =+ m x) (monomials r (p m)))
                  (monomials (mpoly_ring r s) p))
Proof
  rw[monomials_def, restore_var_def, support_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ rw[Once EXTENSION, PULL_EXISTS]
  \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ gs[rrestrict_def]
  \\ gs[mpoly_ring_def]
  \\ qpat_x_assum`FINITE _`kall_tac
  \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  >- (
    qmatch_asmsub_abbrev_tac`p m t`
    \\ qexistsl_tac[`m`,`t`]
    \\ simp[FUN_EQ_THM]
    \\ simp[Abbr`t`, combinTheory.APPLY_UPDATE_THM]
    \\ rw[Abbr`m`]
    \\ metis_tac[])
  \\ simp[combinTheory.UPDATE_EQ]
  \\ simp[combinTheory.APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`p m'`
  \\ `m' = m` by (
    simp[FUN_EQ_THM, Abbr`m'`]
    \\ rw[]
    \\ qmatch_goalsub_rename_tac`m z = 0`
    \\ `~(BAG_IN z m)` by metis_tac[]
    \\ fs[BAG_IN, BAG_INN] )
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`p m t'`
  \\ qmatch_asmsub_rename_tac`p m t`
  \\ `t' = t` suffices_by rw[]
  \\ rw[Abbr`t'`, combinTheory.APPLY_UPDATE_THM]
  \\ last_x_assum(qspec_then`m`mp_tac)
  \\ rw[support_def, PULL_EXISTS, monomials_def, rrestrict_def]
  \\ gs[]
  \\ `~BAG_IN x t` by metis_tac[]
  \\ fs[BAG_IN, BAG_INN]
QED

Theorem mpoly_restore_var:
  Ring r /\ mpoly (mpoly_ring r s) p /\ support (mpoly_ring r s) p SUBSET {x} /\
  x NOTIN s ==>
  mpoly r (restore_var r x p)
Proof
  strip_tac
  \\ imp_res_tac mpoly_def
  \\ simp[mpoly_def]
  \\ DEP_REWRITE_TAC[monomials_restore_var]
  \\ simp[PULL_EXISTS]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[restore_var_def]
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`p m`
    \\ first_x_assum(qspec_then`m`mp_tac)
    \\ simp[mpoly_ring_def, mpoly_def]
    \\ strip_tac
    \\ fs[SUBSET_DEF]
    \\ fs[PULL_EXISTS] )
  \\ rpt strip_tac
  \\ irule IMAGE_FINITE
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ first_x_assum (qspec_then`m`mp_tac)
  \\ first_x_assum (qspec_then`m`mp_tac)
  \\ simp[mpoly_ring_def, mpoly_def]
QED

Theorem support_restore_var:
  Ring r /\ mpoly (mpoly_ring r s) p /\ support (mpoly_ring r s) p SUBSET {x} /\
  x NOTIN s ==>
  support r (restore_var r x p) =
  BIGUNION (IMAGE (BIGUNION o IMAGE SET_OF_BAG o monomials r o p)
                  (monomials (mpoly_ring r s) p))
  ∪ if monomials (mpoly_ring r s) p ⊆ {{||}} then {} else {x}
Proof
  strip_tac
  \\ simp[support_def]
  \\ DEP_REWRITE_TAC[monomials_restore_var]
  \\ simp[]
  \\ simp[IMAGE_BIGUNION]
  \\ simp[GSYM IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ simp[GSYM IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ simp[SET_OF_BAG_UPDATE]
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ rw[EQ_IMP_THM, PULL_EXISTS]
  >- (
    qpat_x_assum`_ ∈ COND _ _ _` mp_tac
    \\ rw[]
    >- metis_tac[]
    >- (
      fs[support_def, SUBSET_DEF, PULL_EXISTS]
      \\ res_tac \\ fs[EMPTY_BAG] )
    \\ metis_tac[] )
  >- (
    fs[SUBSET_DEF]
    \\ res_tac \\ rw[]
    \\ qexists_tac`{||}`
    \\ fs[EMPTY_BAG]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[]
    \\ fs[support_def, PULL_EXISTS]
    \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ strip_tac \\ rw[]
    \\ last_x_assum(qspec_then`K 0`mp_tac)
    \\ simp[mpoly_ring_def]
    \\ simp[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  >- (
    qpat_x_assum`_ ∈ COND _ _ _` mp_tac
    \\ rw[] \\ metis_tac[] )
  >- (
    goal_assum(first_assum o mp_then Any mp_tac)
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[]
    \\ strip_tac \\ rw[] \\ fs[]
    \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ qmatch_asmsub_rename_tac`p m`
    \\ last_x_assum(qspec_then`m`mp_tac)
    \\ simp[mpoly_ring_def]
    \\ simp[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  >- (
    fs[SUBSET_DEF]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ qpat_x_assum`_ ∈ monomials _ _`mp_tac
    \\ simp[Once monomials_def]
    \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw[rrestrict_def]
    \\ simp[monomials_def]
    \\ pop_assum mp_tac
    \\ simp[Once FUN_EQ_THM]
    \\ simp[mpoly_ring_def] \\ strip_tac
    \\ simp[rrestrict_def]
    \\ qmatch_asmsub_rename_tac`p b c <> _`
    \\ qexists_tac`c`
    \\ last_x_assum(qspec_then`b`mp_tac)
    \\ simp[mpoly_ring_def]
    \\ simp[mpoly_def, SUBSET_DEF, PULL_EXISTS]
    \\ strip_tac
    \\ fs[support_def, PULL_EXISTS]
    \\ pop_assum mp_tac
    \\ simp[monomials_def, rrestrict_def]
    \\ strip_tac
    \\ `~BAG_IN x c` by metis_tac[]
    \\ simp[] \\ rw[] \\ fs[]
    \\ qpat_x_assum`b <> _`mp_tac
    \\ simp[EMPTY_BAG]
    \\ simp[FUN_EQ_THM]
    \\ qx_gen_tac`z`
    \\ CCONTR_TAC
    \\ last_x_assum(qspecl_then[`z`,`b`]mp_tac)
    \\ simp[BAG_IN, BAG_INN]
    \\ simp[monomials_def, FUN_EQ_THM]
    \\ simp[rrestrict_def]
    \\ simp[mpoly_ring_def]
    \\ reverse conj_tac
    >- ( strip_tac \\ fs[] )
    \\ qexists_tac`c`
    \\ rw[] \\ pop_assum mp_tac
    \\ simp[mpoly_def, support_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw[monomials_def, rrestrict_def]
    \\ metis_tac[])
QED

Theorem isolate_restore_var:
  Ring r /\ mpoly (mpoly_ring r s) p /\ support (mpoly_ring r s) p SUBSET {x} /\
  x NOTIN s ==>
  isolate_var r x (restore_var r x p) = p
Proof
  rw[Once FUN_EQ_THM]
  \\ qmatch_goalsub_rename_tac`p m`
  \\ rw[isolate_var_def]
  \\ DEP_REWRITE_TAC[monomials_restore_var]
  \\ simp[]
  \\ simp[isolate_var_ring_def]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ `FINITE (monomials (mpoly_ring r s) p)` by fs[mpoly_def]
  \\ `∀m. mpoly r (p m) ∧ support r (p m) SUBSET s`
  by (
    qhdtm_x_assum`mpoly`mp_tac
    \\ simp[Once mpoly_def]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[mpoly_ring_def, SUBSET_DEF]
    \\ metis_tac[])
  \\ `∀m. FINITE (monomials r (p m))` by fs[mpoly_def]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE _ ss`
  \\ `FINITE_BAG ss` by simp[Abbr`ss`, PULL_EXISTS]
  \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`ss`]
  \\ conj_tac
  >- (
    rpt strip_tac
    \\ simp[GSYM isolate_var_ring_def]
    \\ irule isolate_var_mono_in_carrier
    \\ DEP_REWRITE_TAC[monomials_restore_var]
    \\ DEP_REWRITE_TAC[mpoly_restore_var]
    \\ simp[PULL_EXISTS]
    \\ metis_tac[] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ reverse(Cases_on`m ∈ monomials (mpoly_ring r s) p`)
  >- (
    pop_assum mp_tac
    \\ simp[Once monomials_def]
    \\ simp[rrestrict_def]
    \\ reverse IF_CASES_TAC
    >- (
      fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[] )
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`GBAG g _ = g'.id`
    \\ `g'.id = g.id` by rw[Abbr`g`, Abbr`g'`, mpoly_ring_def]
    \\ pop_assum SUBST1_TAC
    \\ irule IMP_GBAG_EQ_ID
    \\ simp[Abbr`g`, abelian_group_is_abelian_monoid]
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ qx_genl_tac[`m'`,`t`] \\ strip_tac
    \\ simp[isolate_var_mono_def]
    \\ simp[mpoly_ring_def]
    \\ rw[]
    \\ simp[remove_var_mono_def, Once FUN_EQ_THM]
    \\ qx_gen_tac`t'`
    \\ rw[]
    \\ rw[rrestrict_def]
    \\ simp[restore_var_def]
    \\ rw[Abbr`g'`]
    \\ rw[mpoly_ring_def] )
  \\ `!y. BAG_IN y m ==> y = x`
  by (
    fs[SUBSET_DEF, support_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `m = λy. if y = x then m x else 0`
  by (
    rw[FUN_EQ_THM] \\ rw[]
    \\ fs[BAG_IN, BAG_INN]
    \\ first_x_assum(qspec_then`y`mp_tac)
    \\ simp[] )
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE f`
  \\ qmatch_goalsub_abbrev_tac`GBAG g _ = _`
  \\ `f = λb. if b x = m x then
                 remove_var_mono r x (restore_var r x p) b
                 else g.id`
  by (
    simp[Abbr`f`, Once FUN_EQ_THM]
    \\ simp[isolate_var_mono_def]
    \\ simp[Abbr`g`, mpoly_ring_def]
    \\ gen_tac
    \\ Cases_on`m x = b x` \\ fs[]
    >- (
      rw[]
      \\ pop_assum mp_tac
      \\ simp[FUN_EQ_THM]
      \\ metis_tac[] )
    \\ rw[]
    \\ pop_assum mp_tac
    \\ simp[] )
  \\ simp[Abbr`f`]
  \\ pop_assum kall_tac
  \\ DEP_REWRITE_TAC[GSYM (MP_CANON GBAG_IMAGE_FILTER)]
  \\ simp[Abbr`g`, abelian_group_is_abelian_monoid]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ conj_tac
  >- (
    rw[]
    \\ simp[mpoly_ring_def]
    \\ DEP_REWRITE_TAC[mpoly_remove_var_mono]
    \\ DEP_REWRITE_TAC[support_remove_var_mono]
    \\ DEP_REWRITE_TAC[monomials_restore_var]
    \\ simp[PULL_EXISTS]
    \\ DEP_REWRITE_TAC[mpoly_restore_var] \\ simp[]
    \\ metis_tac[] )
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET ms`
  \\ `ms = IMAGE (x =+ m x) (monomials r (p m))`
  by (
    simp[Abbr`ms`, Once EXTENSION, PULL_EXISTS]
    \\ rw[EQ_IMP_THM]
    >- (
      fs[combinTheory.APPLY_UPDATE_THM]
      \\ fs[support_def, SUBSET_DEF, PULL_EXISTS]
      \\ `m = m'` suffices_by metis_tac[]
      \\ simp[FUN_EQ_THM]
      \\ qx_gen_tac`z`
      \\ Cases_on`z = x` \\ simp[]
      \\ qpat_x_assum`m = _`SUBST1_TAC \\ simp[]
      \\ first_x_assum(qspecl_then[`z`,`m'`]mp_tac)
      \\ simp[] \\ simp[BAG_IN, BAG_INN] )
    \\ simp[combinTheory.APPLY_UPDATE_THM]
    \\ metis_tac[] )
  \\ simp[Abbr`ms`]
  \\ pop_assum kall_tac
  \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ conj_tac
  >- (
    rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    \\ qmatch_goalsub_rename_tac`b z = _`
    \\ first_x_assum(qspec_then`z`mp_tac)
    \\ rw[]
    \\ fs[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ `~(BAG_IN x b) /\ ~(BAG_IN x y)` by metis_tac[]
    \\ fs[BAG_IN, BAG_INN] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF]
  \\ drule mpoly_sum_monomials
  \\ `mpoly r (p m)` by metis_tac[]
  \\ disch_then drule
  \\ disch_then(qspec_then`s`mp_tac)
  \\ impl_tac >- metis_tac[]
  \\ qmatch_goalsub_abbrev_tac`_⇒ gg = _`
  \\ disch_then(SUBST1_TAC o SYM)
  \\ simp[Abbr`gg`]
  \\ qmatch_goalsub_abbrev_tac`GBAG rr.sum br = GBAG rs.sum _`
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG rs.sum br`
  \\ conj_tac
  >- (
    `rs.sum.id = rr.sum.id` by simp[Abbr`rr`, Abbr`rs`, mpoly_ring_def]
    \\ pop_assum SUBST1_TAC
    \\ irule GITBAG_same_op
    \\ simp[Abbr`br`]
    \\ simp[Abbr`rr`, Abbr`rs`, mpoly_ring_def] )
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ simp[Abbr`br`]
  \\ irule BAG_IMAGE_CONG
  \\ simp[]
  \\ simp[Once FUN_EQ_THM]
  \\ simp[remove_var_mono_def]
  \\ qx_gen_tac`b`
  \\ strip_tac
  \\ qx_gen_tac`t`
  \\ `b x = 0`
  by (
    fs[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ Cases_on`BAG_IN x b` \\ fs[BAG_IN, BAG_INN]
    \\ metis_tac[] )
  \\ `(x =+ 0) b = b`
  by simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ simp[]
  \\ rw[]
  \\ simp[rrestrict_def, restore_var_def]
  \\ fs[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ simp[combinTheory.APPLY_UPDATE_THM]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ qpat_x_assum`m = _`(mp_tac o SYM)
  \\ simp[FUN_EQ_THM]
QED

Theorem isolate_var_inj:
  Ring r /\ mpoly r p /\ mpoly r q /\
  isolate_var r x p = isolate_var r x q ==>
  p = q
Proof
  strip_tac
  \\ irule EQ_TRANS
  \\ qexists_tac`restore_var r x (isolate_var r x p)`
  \\ conj_tac >- simp[restore_isolate_var]
  \\ simp[]
  \\ simp[restore_isolate_var]
QED

(* These form a ring isomorphism, which composes back to PolyRing *)

Theorem RingIso_restore_var:
  Ring r /\ x IN s ==>
  RingIso (restore_var r x)
    (mpoly_ring (mpoly_ring r (s DELETE x)) {x})
    (mpoly_ring r s)
Proof
  strip_tac
  \\ rewrite_tac[RingIso_def]
  \\ reverse conj_asm2_tac
  >- (
    simp[BIJ_DEF]
    \\ simp[INJ_DEF, GSYM CONJ_ASSOC]
    \\ conj_asm1_tac
    >- (
      qmatch_goalsub_abbrev_tac`mpoly_ring rr {x}`
      \\ simp[mpoly_ring_def]
      \\ qx_gen_tac`p` \\ strip_tac
      \\ DEP_REWRITE_TAC[Q.GEN`s`mpoly_restore_var]
      \\ simp[Abbr`rr`, PULL_EXISTS]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[]
      \\ DEP_REWRITE_TAC[Q.SPEC`s DELETE x`(Q.GEN`s`support_restore_var)]
      \\ simp[]
      \\ simp[SUBSET_DEF, PULL_EXISTS]
      \\ rw[]
      \\ fs[support_def, SUBSET_DEF, PULL_EXISTS, mpoly_def]
      \\ qmatch_asmsub_rename_tac`p m`
      \\ first_x_assum(qspec_then`m`mp_tac)
      \\ simp[mpoly_ring_def]
      \\ simp[mpoly_def]
      \\ simp[support_def, SUBSET_DEF, PULL_EXISTS]
      \\ rw[] \\ metis_tac[] )
    \\ conj_tac
    >- (
      qmatch_goalsub_abbrev_tac`mpoly_ring rr {x}`
      \\ simp[mpoly_ring_def]
      \\ rpt strip_tac
      \\ `x NOTIN s DELETE x` by simp[]
      \\ metis_tac[isolate_restore_var])
    \\ simp[SURJ_DEF]
    \\ qx_gen_tac`p` \\ strip_tac
    \\ qexists_tac`isolate_var r x p`
    \\ DEP_REWRITE_TAC[restore_isolate_var]
    \\ simp[]
    \\ conj_asm1_tac >- fs[mpoly_ring_def]
    \\ qmatch_goalsub_abbrev_tac`mpoly_ring rr {_}`
    \\ simp[mpoly_ring_def]
    \\ conj_asm1_tac
    >- (
      qunabbrev_tac`rr`
      \\ irule mpoly_mpoly_ring_more_support
      \\ qexists_tac`support r p DELETE x`
      \\ simp[mpoly_isolate_var]
      \\ qpat_x_assum`p IN _`mp_tac
      \\ simp[mpoly_ring_def, SUBSET_DEF] )
    \\ irule SUBSET_TRANS
    \\ qexists_tac`support (mpoly_ring r (support r p DELETE x)) (isolate_var r x p)`
    \\ qunabbrev_tac`rr`
    \\ reverse conj_tac
    >- simp[support_isolate_var]
    \\ qmatch_goalsub_abbrev_tac`a SUBSET b`
    \\ `b = a` suffices_by rw[]
    \\ unabbrev_all_tac
    \\ irule support_mpoly_ring_more_support
    \\ qpat_x_assum`p IN _`mp_tac
    \\ simp[]
    \\ simp[mpoly_ring_def, SUBSET_DEF] )
  \\ simp[RingHomo_def]
  \\ conj_asm1_tac >- fs[BIJ_DEF, INJ_DEF]
  \\ simp[GroupHomo_def, GSYM CONJ_ASSOC]
  \\ conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`mpoly_ring rr {_}`
    \\ simp[mpoly_ring_def]
    \\ qx_genl_tac[`p`,`q`]
    \\ strip_tac
    \\ simp[FUN_EQ_THM, mpoly_add_def]
    \\ simp[rrestrict_def]
    \\ first_assum(qspec_then`p`mp_tac)
    \\ first_x_assum(qspec_then`q`mp_tac)
    \\ simp[mpoly_ring_def]
    \\ strip_tac \\ strip_tac
    \\ imp_res_tac mpoly_def
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ simp[restore_var_def, mpoly_add_def]
    \\ simp[rrestrict_def]
    \\ simp[Abbr`rr`, mpoly_ring_def]
    \\ simp[mpoly_add_def]
    \\ simp[rrestrict_def]
    \\ qpat_x_assum`∀x. q x IN _`mp_tac
    \\ qpat_x_assum`∀x. p x IN _`mp_tac
    \\ simp[mpoly_ring_def]
    \\ simp[mpoly_def, SUBSET_DEF, PULL_EXISTS] )
  \\ simp[MonoidHomo_def]
  \\ reverse conj_asm2_tac
  >- (
    simp[mpoly_ring_def, mpoly_one_def, FUN_EQ_THM, restore_var_def]
    \\ rw[mpoly_one_def] \\ fs[EMPTY_BAG, FUN_EQ_THM]
    \\ rw[combinTheory.APPLY_UPDATE_THM]
    \\ metis_tac[] )
  \\ qmatch_goalsub_abbrev_tac`mpoly_ring rr {_}`
  \\ simp[mpoly_ring_def]
  \\ qx_genl_tac[`p`,`q`]
  \\ strip_tac
  \\ simp[FUN_EQ_THM, mpoly_mul_BAG_FILTER_cross]
  \\ simp[rrestrict_def]
  \\ first_assum(qspec_then`p`mp_tac)
  \\ first_x_assum(qspec_then`q`mp_tac)
  \\ simp[mpoly_ring_def]
  \\ strip_tac \\ strip_tac
  \\ imp_res_tac mpoly_def
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[restore_var_def, mpoly_mul_BAG_FILTER_cross]
  \\ simp[rrestrict_def]
  \\ DEP_REWRITE_TAC[Q.SPEC`s DELETE x`(Q.GEN`s`monomials_restore_var)]
  \\ simp[SUBSET_DEF]
  \\ qx_gen_tac`b`
  \\ simp[Abbr`rr`]
  \\ DEP_REWRITE_TAC[mpoly_ring_sum_applied]
  \\ simp[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
  \\ qmatch_goalsub_abbrev_tac`mp × mq`
  \\ simp[mpoly_ring_def]
  \\ simp[mpoly_mul_BAG_FILTER_cross]
  \\ qpat_x_assum`∀x. q x IN _`mp_tac
  \\ qpat_x_assum`∀x. p x IN _`mp_tac
  \\ simp[mpoly_ring_def]
  \\ simp[mpoly_def, SUBSET_DEF, PULL_EXISTS]
  \\ ntac 2 strip_tac
  \\ simp[rrestrict_def]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ qho_match_abbrev_tac`GBAG g
      (BAG_IMAGE (λ(x1,x2). GBAG g (BAG_IMAGE (f x1 x2) (BAG_OF_SET (bb x1 x2))))
        (BAG_OF_SET ss)) = _`
  \\ qspecl_then[`g`,`UNCURRY f`,`UNCURRY bb`]mp_tac
       (Q.GENL[`g`,`f`,`b`]GBAG_IMAGE_GBAG_BAG_OF_SET)
  \\ impl_tac >- simp[Abbr`g`, abelian_group_is_abelian_monoid]
  \\ disch_then(qspec_then`ss`mp_tac)
  \\ impl_tac >- simp[Abbr`ss`]
  \\ impl_tac >- ( simp[Abbr`bb`, Abbr`f`, Abbr`ss`, FORALL_PROD, Abbr`g`] )
  \\ simp[LAMBDA_PROD]
  \\ disch_then kall_tac
  \\ simp[Abbr`f`, Abbr`bb`, Abbr`ss`]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s1`
  \\ `FINITE s1` by ( simp[Abbr`s1`, PULL_EXISTS, FORALL_PROD] )
  \\ qmatch_goalsub_abbrev_tac`_ = GBAG _ (BAG_IMAGE _ (BAG_OF_SET s2))`
  \\ `FINITE s2` by ( simp[Abbr`s2`, PULL_EXISTS, FORALL_PROD] )
  \\ irule (MP_CANON GITBAG_CONG)
  \\ simp[Abbr`g`, SUBSET_DEF, PULL_EXISTS, abelian_group_is_abelian_monoid]
  \\ simp[Abbr`s1`, Abbr`s2`, PULL_EXISTS, EXISTS_PROD]
  \\ qx_gen_tac`z`
  \\ disch_then assume_tac
  \\ simp[BAG_IMAGE_DEF]
  \\ simp[BAG_FILTER_BAG_OF_SET, UNCURRY, LAMBDA_PROD]
  \\ DEP_REWRITE_TAC[BAG_CARD_BAG_OF_SET]
  \\ simp[]
  \\ conj_asm1_tac >- ( irule FINITE_INTER \\ simp[PULL_EXISTS] )
  \\ irule FINITE_BIJ_CARD \\ simp[]
  \\ qexists_tac`λ((p1,p2),p3,p4). (BAG_UNION p1 p3, BAG_UNION p2 p4)`
  \\ simp[BIJ_IFF_INV, PULL_EXISTS, EXISTS_PROD]
  \\ qexists_tac`λ(p1,p2). (((λt. if t = x then p1 x else 0),
                             (λt. if t = x then p2 x else 0)),
                            (x =+ 0) p1, (x =+ 0) p2)`
  \\ simp[combinTheory.APPLY_UPDATE_THM]
  \\ `∀m. m IN mp ==> m = λt. if t = x then m x else 0`
  by (
    qpat_x_assum`∀x. x IN support _ p ⇒ _`mp_tac
    \\ simp[support_def, PULL_EXISTS]
    \\ simp[BAG_IN, BAG_INN]
    \\ rpt strip_tac
    \\ simp[Once FUN_EQ_THM]
    \\ gen_tac \\ IF_CASES_TAC \\ simp[]
    \\ `¬(m t >= 1)` by metis_tac[]
    \\ fs[] )
  \\ `∀m. m IN mq ==> m = λt. if t = x then m x else 0`
  by (
    qpat_x_assum`∀x. x IN support _ q ⇒ _`mp_tac
    \\ simp[support_def, PULL_EXISTS]
    \\ simp[BAG_IN, BAG_INN]
    \\ rpt strip_tac
    \\ simp[Once FUN_EQ_THM]
    \\ gen_tac \\ IF_CASES_TAC \\ simp[]
    \\ `¬(m t >= 1)` by metis_tac[]
    \\ fs[] )
  \\ `∀t m. m IN monomials r (p t) ==> m x = 0`
  by (
    rpt gen_tac \\ strip_tac
    \\ ntac 4(first_x_assum(qspec_then`t`mp_tac))
    \\ simp[support_def, PULL_EXISTS]
    \\ simp[BAG_IN, BAG_INN]
    \\ rpt strip_tac
    \\ `¬(m x >= 1)` by metis_tac[]
    \\ fs[] )
  \\ `∀t m. m IN monomials r (q t) ==> m x = 0`
  by (
    rpt gen_tac \\ strip_tac
    \\ ntac 4(first_x_assum(qspec_then`t`mp_tac))
    \\ simp[support_def, PULL_EXISTS]
    \\ simp[BAG_IN, BAG_INN]
    \\ rpt strip_tac
    \\ `¬(m x >= 1)` by metis_tac[]
    \\ fs[] )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ strip_tac
    \\ rpt(goal_assum(first_assum o mp_then Any mp_tac))
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[IN_DEF, PULL_EXISTS, EXISTS_PROD]
    \\ strip_tac
    \\ BasicProvers.VAR_EQ_TAC
    \\ res_tac
    \\ qmatch_asmsub_abbrev_tac`p_2 = λt. if t = _ then x2 else _`
    \\ qmatch_asmsub_abbrev_tac`p_1 = λt. if t = _ then x1 else _`
    \\ simp_tac(srw_ss())[BAG_UNION]
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    \\ conj_tac >- (
      gen_tac
      \\ IF_CASES_TAC >- (
        BasicProvers.VAR_EQ_TAC \\ simp[] )
      \\ simp[] )
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    \\ conj_tac >- (
      gen_tac
      \\ IF_CASES_TAC >- (
        BasicProvers.VAR_EQ_TAC \\ simp[] )
      \\ simp[] )
    \\ qpat_x_assum`_ = BAG_UNION _ _`mp_tac
    \\ qpat_x_assum`_ = BAG_UNION _ _`mp_tac
    \\ simp_tac(srw_ss())[BAG_UNION]
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    \\ strip_tac
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    \\ strip_tac
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM]
    \\ conj_tac
    >- (
      qx_gen_tac`y`
      \\ ntac 2 (first_x_assum(qspec_then`y`mp_tac))
      \\ IF_CASES_TAC
      >- ( BasicProvers.VAR_EQ_TAC \\ simp_tac(srw_ss())[] )
      \\ pop_assum mp_tac \\ simp_tac(srw_ss())[] )
    \\ qmatch_goalsub_abbrev_tac`p aa bb * q cc dd = p e f * q g h`
    \\ `aa = e ∧ bb = f ∧ cc = g ∧ dd = h` suffices_by rw[]
    \\ simp_tac(srw_ss())[Abbr`aa`,Abbr`bb`,Abbr`cc`,Abbr`dd`,Abbr`g`,Abbr`h`,Abbr`f`,Abbr`e`]
    \\ simp_tac(srw_ss())[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac \\ gen_tac \\ IF_CASES_TAC
    \\ asm_simp_tac bool_ss []
    \\ TRY BasicProvers.VAR_EQ_TAC
    \\ simp[] )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ strip_tac
    \\ BasicProvers.VAR_EQ_TAC
    \\ res_tac
    \\ qmatch_asmsub_abbrev_tac`m = λt. if t = _ then xx else _`
    \\ qmatch_asmsub_abbrev_tac`m' = λt. if t = _ then xy else _`
    \\ BasicProvers.VAR_EQ_TAC
    \\ BasicProvers.VAR_EQ_TAC
    \\ qmatch_asmsub_rename_tac`(_ =+ _)m1`
    \\ `(x =+ 0) m1 = m1`
    by ( simp[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] )
    \\ pop_assum SUBST1_TAC
    \\ conj_tac >- simp[]
    \\ qmatch_goalsub_rename_tac`(_ =+ _)m2`
    \\ `(x =+ 0) m2 = m2`
    by ( simp[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] )
    \\ pop_assum SUBST1_TAC
    \\ conj_tac >- simp[]
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, BAG_UNION]
    \\ conj_tac >- (rw[] \\ rw[])
    \\ conj_tac >- simp[]
    \\ conj_tac >- simp[]
    \\ simp_tac(srw_ss())[Once FUN_EQ_THM]
    \\ conj_tac >- (rw[] \\ rw[])
    \\ simp_tac(srw_ss())[IN_DEF, EXISTS_PROD] )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ strip_tac
    \\ res_tac
    \\ qmatch_goalsub_rename_tac`BAG_UNION m _`
    \\ qmatch_goalsub_rename_tac`_ ∧ _ = m'`
    \\ qmatch_asmsub_abbrev_tac`m = λt. if t = _ then xx else _`
    \\ qmatch_asmsub_abbrev_tac`m' = λt. if t = _ then xy else _`
    \\ BasicProvers.VAR_EQ_TAC
    \\ BasicProvers.VAR_EQ_TAC
    \\ simp_tac(srw_ss())[BAG_UNION]
    \\ simp_tac(srw_ss())[FUN_EQ_THM]
    \\ simp_tac(srw_ss())[combinTheory.APPLY_UPDATE_THM]
    \\ rw[] \\ rw[] )
  \\ rpt gen_tac
  \\ strip_tac
  \\ simp_tac(srw_ss())[BAG_UNION]
  \\ simp_tac(srw_ss())[FUN_EQ_THM]
  \\ simp_tac(srw_ss())[combinTheory.APPLY_UPDATE_THM]
  \\ res_tac
  \\ qmatch_asmsub_abbrev_tac`m = λt. if t = _ then xx else _`
  \\ qmatch_asmsub_abbrev_tac`m' = λt. if t = _ then xy else _`
  \\ BasicProvers.VAR_EQ_TAC
  \\ BasicProvers.VAR_EQ_TAC
  \\ rw[]
QED

Theorem RingIso_isolate_var:
  Ring r /\ x IN s ==>
    RingIso (isolate_var r x)
      (mpoly_ring r s)
      (mpoly_ring (mpoly_ring r (s DELETE x)) {x})
Proof
  strip_tac
  \\ irule ring_iso_sym_any
  \\ simp[]
  \\ qexists_tac`restore_var r x`
  \\ simp[RingIso_restore_var]
  \\ conj_tac
  >- (
    qx_gen_tac`p` \\ strip_tac
    \\ irule isolate_restore_var
    \\ simp[]
    \\ qexists_tac`s DELETE x` \\ simp[]
    \\ fs[mpoly_ring_def] )
  \\ qx_gen_tac`p` \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`mpoly_ring rr {x}`
  \\ qpat_x_assum`p ∈ _`mp_tac
  \\ simp[mpoly_ring_def]
  \\ strip_tac
  \\ drule mpoly_isolate_var
  \\ disch_then drule
  \\ disch_then(qspec_then`x`strip_assume_tac)
  \\ drule mpoly_mpoly_ring_more_support
  \\ disch_then(qspec_then`s DELETE x`mp_tac)
  \\ impl_keep_tac >- fs[SUBSET_DEF]
  \\ strip_tac
  \\ last_assum(mp_then (Pat`mpoly`) mp_tac
                   support_mpoly_ring_more_support)
  \\ disch_then drule
  \\ simp[support_isolate_var]
  \\ disch_then(SUBST1_TAC o SYM)
  \\ simp[SUBSET_DEF] \\ rfs[]
  \\ irule restore_isolate_var
  \\ simp[]
QED

Theorem RingIso_mpoly_ring_poly_ring:
  Ring r /\ x IN s ==>
  RingIso (poly_of_mpoly (mpoly_ring r (s DELETE x)) o isolate_var r x)
    (mpoly_ring r s) (PolyRing (mpoly_ring r (s DELETE x)))
Proof
  strip_tac
  \\ irule ring_iso_trans
  \\ qexists_tac`mpoly_ring (mpoly_ring r (s DELETE x)) {x}`
  \\ conj_tac >- simp[RingIso_isolate_var]
  \\ irule RingIso_poly_of_mpoly
  \\ simp[]
QED

Theorem degree_of_mpoly_mul_deg:
  Ring r /\ mpoly r p /\ mpoly r q /\
  support r p ⊆ s /\ support r q ⊆ s /\ v IN s ==>
  degree_of r (mpoly_mul r p q) v =
  Deg (mpoly_ring r (s DELETE v))
    (poly_mult (mpoly_ring r (s DELETE v))
         (poly_of_mpoly (mpoly_ring r (s DELETE v)) (isolate_var r v p))
         (poly_of_mpoly (mpoly_ring r (s DELETE v)) (isolate_var r v q)))
Proof
  strip_tac
  \\ `p IN (mpoly_ring r s).carrier`
  by ( simp[mpoly_ring_def] \\ simp[SUBSET_DEF] )
  \\ `q IN (mpoly_ring r s).carrier`
  by ( simp[mpoly_ring_def] \\ simp[SUBSET_DEF] )
  \\ drule RingIso_mpoly_ring_poly_ring
  \\ disch_then drule
  \\ simp[RingIso_def]
  \\ strip_tac
  \\ fs[RingHomo_def]
  \\ fs[MonoidHomo_def]
  \\ first_x_assum(qspecl_then[`p`,`q`]mp_tac)
  \\ simp[]
  \\ disch_then(SUBST1_TAC o SYM)
  \\ qmatch_goalsub_abbrev_tac`poly_of_mpoly rr`
  \\ simp[mpoly_ring_def]
  \\ qmatch_goalsub_abbrev_tac`degree_of r pq`
  \\ `mpoly r pq` by (
    simp[Abbr`pq`]
    \\ irule mpoly_mpoly_mul
    \\ fs[mpoly_def] )
  \\ `support r pq DELETE v SUBSET s DELETE v`
  by (
    irule SUBSET_TRANS
    \\ qexists_tac `(support r p ∪ support r q) DELETE v`
    \\ reverse conj_tac >- (fs[SUBSET_DEF] \\ metis_tac[])
    \\ drule support_mpoly_mul_SUBSET
    \\ fs[SUBSET_DEF] )
  \\ `mpoly rr (isolate_var r v pq)`
  by (
    qunabbrev_tac`rr`
    \\ irule mpoly_mpoly_ring_more_support
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ `support rr (isolate_var r v pq) SUBSET {v}`
  by (
    qunabbrev_tac`rr`
    \\ irule SUBSET_TRANS
    \\ qexists_tac`support (mpoly_ring r (support r pq DELETE v)) (isolate_var r v pq)`
    \\ reverse conj_tac >- simp[support_isolate_var]
    \\ qmatch_goalsub_abbrev_tac`a ⊆ b`
    \\ `b = a` suffices_by rw[]
    \\ unabbrev_all_tac
    \\ irule support_mpoly_ring_more_support
    \\ simp[] )
  \\ DEP_REWRITE_TAC[GSYM degree_of_mpoly_of_poly]
  \\ conj_asm1_tac
  >- (
    simp[Abbr`rr`]
    \\ irule poly_poly_of_mpoly
    \\ simp[]
    \\ reverse conj_tac >- metis_tac[]
    \\ qmatch_goalsub_abbrev_tac`monomials _ ipq`
    \\ `monomials (mpoly_ring r (s DELETE v)) ipq =
        monomials (mpoly_ring r (support r pq DELETE v)) ipq`
    by (
      irule EQ_SYM
      \\ irule monomials_mpoly_ring_more_support
      \\ simp[Abbr`ipq`])
    \\ simp[monomials_isolate_var, Abbr`ipq`]
    \\ irule IMAGE_FINITE
    \\ fs[mpoly_def] )
  \\ DEP_REWRITE_TAC[mpoly_of_poly_of_mpoly]
  \\ simp[]
  \\ qunabbrev_tac`rr`
  \\ DEP_REWRITE_TAC[degree_of_isolate_var]
  \\ simp[Abbr`pq`]
  \\ fs[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem mpoly_integral_domain:
  !s. FINITE s ==>
      !r. IntegralDomain r ==> IntegralDomain (mpoly_ring r s)
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  >- (
    `Ring r` by simp[integral_domain_is_ring]
    \\ `Ring (mpoly_ring r {})` by simp[]
    \\ `∃f. RingIso f r (mpoly_ring r {})`
    suffices_by metis_tac[integral_domain_ring_iso]
    \\ metis_tac[mpoly_ring_empty_support_iso, ring_iso_sym] )
  \\ `Ring r` by simp[integral_domain_is_ring]
  \\ qmatch_goalsub_abbrev_tac`IntegralDomain d`
  \\ `e IN (e INSERT s) /\ (e INSERT s) DELETE e = s`
  by ( simp[Once EXTENSION] \\ metis_tac[] )
  \\ `Ring (mpoly_ring r (e INSERT s))` by simp[]
  \\ `Ring (PolyRing (mpoly_ring r s))` by simp[poly_ring_ring]
  \\ `∃f. RingIso f (PolyRing (mpoly_ring r s)) (mpoly_ring r (e INSERT s))`
  by metis_tac[RingIso_mpoly_ring_poly_ring, ring_iso_sym]
  \\ metis_tac[integral_domain_ring_iso, poly_integral_domain]
QED

Theorem degree_of_mpoly_mul:
  IntegralDomain r /\ mpoly r p /\ mpoly r q /\
  support r p SUBSET s /\ support r q SUBSET s /\ v IN s /\ FINITE s /\
  p <> K r.sum.id /\ q <> K r.sum.id
  ==>
  degree_of r (mpoly_mul r p q) v = degree_of r p v + degree_of r q v
Proof
  strip_tac
  \\ `Ring r` by simp[integral_domain_is_ring]
  \\ DEP_REWRITE_TAC[degree_of_mpoly_mul_deg]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`Deg rr (poly_mult rr pp qq)`
  \\ `mpoly rr (isolate_var r v p)`
  by (
    qunabbrev_tac`rr`
    \\ irule mpoly_mpoly_ring_more_support
    \\ qexists_tac`support r p DELETE v`
    \\ fs[SUBSET_DEF] )
  \\ `mpoly rr (isolate_var r v q)`
  by (
    qunabbrev_tac`rr`
    \\ irule mpoly_mpoly_ring_more_support
    \\ qexists_tac`support r q DELETE v`
    \\ fs[SUBSET_DEF] )
  \\ `support rr (isolate_var r v p) = {v} INTER support r p`
  by (
    irule EQ_TRANS
    \\ qexists_tac`support (mpoly_ring r (support r p DELETE v)) (isolate_var r v p)`
    \\ reverse conj_tac >- simp[support_isolate_var]
    \\ qunabbrev_tac`rr`
    \\ irule EQ_SYM
    \\ irule support_mpoly_ring_more_support
    \\ fs[SUBSET_DEF] )
  \\ `support rr (isolate_var r v q) = {v} INTER support r q`
  by (
    irule EQ_TRANS
    \\ qexists_tac`support (mpoly_ring r (support r q DELETE v)) (isolate_var r v q)`
    \\ reverse conj_tac >- simp[support_isolate_var]
    \\ qunabbrev_tac`rr`
    \\ irule EQ_SYM
    \\ irule support_mpoly_ring_more_support
    \\ fs[SUBSET_DEF] )
  \\ `Poly rr pp`
  by (
    simp[Abbr`rr`, Abbr`pp`]
    \\ irule poly_poly_of_mpoly
    \\ fs[mpoly_def]
    \\ qexists_tac`v` \\ simp[SUBSET_DEF] )
  \\ `Poly rr qq`
  by (
    simp[Abbr`rr`, Abbr`qq`]
    \\ irule poly_poly_of_mpoly
    \\ fs[mpoly_def]
    \\ qexists_tac`v` \\ simp[SUBSET_DEF] )
  \\ DEP_REWRITE_TAC[polyRingTheory.weak_deg_mult_nonzero]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- simp[Abbr`rr`]
  \\ `FINITE (s DELETE v)` by simp[]
  \\ `IntegralDomain rr` by metis_tac[mpoly_integral_domain]
  \\ conj_asm1_tac
  >- (
    `Lead rr pp <> rr.sum.id /\ Lead rr qq <> rr.sum.id`
    suffices_by metis_tac[poly_lead_element, IntegralDomain_def]
    \\ simp[poly_lead_eq_zero]
    \\ qspecl_then[`r`,`v`,`s`]mp_tac
         (Q.GENL[`r`,`x`,`s`]RingIso_mpoly_ring_poly_ring)
    \\ impl_tac >- simp[]
    \\ qmatch_goalsub_abbrev_tac`RingIso f r1 r2`
    \\ strip_tac
    \\ `Ring r1 /\ Ring r2` by simp[Abbr`r1`, Abbr`r2`, poly_ring_ring]
    \\ `∀x. x IN r1.carrier ==> (f x = r2.sum.id <=> x = r1.sum.id)`
    by metis_tac[ring_iso_eq_zero]
    \\ `pp = f p /\ qq = f q` by simp[Abbr`f`]
    \\ `r2.sum.id = []` by simp[Abbr`r2`]
    \\ `p IN r1.carrier /\ q IN r1.carrier`
    by ( simp[Abbr`r1`, mpoly_ring_def] )
    \\ fs[]
    \\ simp[Abbr`r1`, mpoly_ring_def] )
  \\ DEP_REWRITE_TAC[GSYM degree_of_mpoly_of_poly]
  \\ simp[]
  \\ map_every qunabbrev_tac[`pp`,`qq`]
  \\ DEP_REWRITE_TAC[mpoly_of_poly_of_mpoly]
  \\ simp[]
  \\ qunabbrev_tac`rr`
  \\ DEP_REWRITE_TAC[degree_of_isolate_var]
  \\ simp[]
QED

(* this gives us a strong version of support_mpoly_mul_SUBSET for IDs *)
Theorem support_mpoly_mul:
  IntegralDomain r /\
  mpoly r p /\ mpoly r q /\ p <> K r.sum.id /\ q <> K r.sum.id /\
  FINITE (support r p) /\ FINITE (support r q)
  ==>
  support r (mpoly_mul r p q) = support r p ∪ support r q
Proof
  strip_tac
  \\ `Ring r` by simp[integral_domain_is_ring]
  \\ rewrite_tac[SET_EQ_SUBSET]
  \\ conj_tac >- simp[support_mpoly_mul_SUBSET]
  \\ simp[SUBSET_DEF]
  \\ `mpoly r (mpoly_mul r p q)` by metis_tac[mpoly_mpoly_mul, mpoly_def]
  \\ simp[GSYM FORALL_AND_THM]
  \\ gen_tac
  \\ DEP_REWRITE_TAC[support_degree_of]
  \\ conj_tac >- metis_tac[mpoly_def]
  \\ DEP_REWRITE_TAC[Q.GEN`s`degree_of_mpoly_mul]
  \\ simp[]
  \\ qexists_tac`support r p UNION support r q UNION {x}`
  \\ simp[SUBSET_DEF]
QED

(* roots of a polynomial *)

Definition mpoly_root_def:
  mpoly_root r p f = (mpoly_eval r p f = r.sum.id)
End

Definition mpoly_roots_def:
  mpoly_roots r p =
    { f | IMAGE f (support r p) SUBSET r.carrier /\ mpoly_root r p f }
End

Theorem mpoly_roots_of_poly:
  IntegralDomain r /\ poly p ==>
  mpoly_roots r (mpoly_of_poly r v p) =
  BIGUNION (IMAGE (λx. {f | 0 < Deg r p ==> f v = x})
                  (poly_roots r p))
Proof
  rw[mpoly_roots_def]
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ simp[support_mpoly_of_poly]
  \\ Cases_on`p = []` \\ simp[]
  >- (
    simp[mpoly_of_poly_empty, mpoly_root_def]
    \\ rewrite_tac[GSYM polynomialTheory.poly_zero]
    \\ rewrite_tac[polyRootTheory.poly_roots_zero]
    \\ simp[mpoly_eval_def]
    \\ rw[Once EXTENSION, PULL_EXISTS]
    \\ metis_tac[ring_zero_element])
  \\ Cases_on`LENGTH p = 1` \\ simp[]
  >- (
    Cases_on`p` \\ fs[]
    \\ simp[mpoly_of_poly_const]
    \\ rw[mpoly_root_def]
    \\ simp[Once EXTENSION, PULL_EXISTS]
    \\ gen_tac
    \\ DEP_REWRITE_TAC[mpoly_eval_cmul]
    \\ simp[monomials_mpoly_one]
    \\ simp[polyRootTheory.poly_roots_const] )
  \\ IF_CASES_TAC
  >- (Cases_on`LENGTH p` \\ fs[])
  \\ simp[SUBSET_DEF]
  \\ rw[mpoly_root_def]
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ qx_gen_tac`f`
  \\ simp[polynomialTheory.poly_roots_def]
  \\ `0 < deg p`
  by ( EVAL_TAC \\ rw[arithmeticTheory.PRE_SUB1] )
  \\ simp[]
  \\ Cases_on`f v IN r.carrier` \\ simp[]
  \\ DEP_REWRITE_TAC[eval_mpoly_of_poly]
  \\ simp[]
  \\ rw[polynomialTheory.poly_root_def]
QED

Theorem poly_roots_of_mpoly:
  IntegralDomain r /\ mpoly r p /\ support r p SUBSET {v} ==>
  poly_roots r (poly_of_mpoly r p) =
  IMAGE (\f. f v) (mpoly_roots r p) INTER r.carrier
Proof
  strip_tac
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ drule_then (drule_then drule) mpoly_of_poly_of_mpoly
  \\ qmatch_goalsub_abbrev_tac`mpoly_of_poly _ _ pp`
  \\ disch_then (SUBST1_TAC o SYM)
  \\ DEP_REWRITE_TAC[mpoly_roots_of_poly]
  \\ conj_asm1_tac >- metis_tac[poly_poly_of_mpoly, mpoly_def]
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  >- ( qexistsl_tac[`K x`,`x`] \\ simp[] \\ fs[poly_roots_def])
  \\ fs[poly_roots_def]
  \\ Cases_on`pp = |0|`
  >- metis_tac[polyWeakTheory.poly_root_zero]
  \\ imp_res_tac poly_nonzero_with_root_deg_pos
  \\ fs[]
QED

(* a polynomial that evaluates to zero at sufficiently
   many points (determined by its degrees) is identically zero *)

Theorem monomials_mpoly_eval_o_isolate_var:
  Ring r /\ mpoly r p
  ==>
  monomials r (flip (mpoly_eval r) f o isolate_var r e p) SUBSET
    IMAGE (λm v. if v = e then m e else 0) (monomials r p)
Proof
  simp[monomials_def]
  \\ simp[SUBSET_DEF]
  \\ strip_tac
  \\ qx_gen_tac`t`
  \\ simp[rrestrict_def]
  \\ IF_CASES_TAC \\ simp[]
  \\ Cases_on`∃y. e <> y /\ BAG_IN y t`
  >- (
    `isolate_var r e p t = K r.sum.id` by (
      irule isolate_var_coeff_zero \\ metis_tac[] )
    \\ simp[mpoly_eval_zero] )
  \\ Cases_on`∀m. m IN monomials r p ==> m e <> t e`
  >- (
    `isolate_var r e p t = K r.sum.id` by (
      irule isolate_var_coeff_zero \\ metis_tac[] )
    \\ simp[mpoly_eval_zero] )
  \\ ntac 2 (pop_assum mp_tac) \\ simp[]
  \\ strip_tac \\ strip_tac
  \\ `t = λy. if y = e then m e else 0`
  by (
    simp[FUN_EQ_THM]
    \\ rw[]
    \\ fs[BAG_IN, BAG_INN]
    \\ first_x_assum(qspec_then`y`mp_tac)
    \\ simp[] )
  \\ pop_assum SUBST_ALL_TAC
  \\ strip_tac
  \\ qexists_tac`m`
  \\ simp[] \\ rw[]
  \\ fs[mpoly_def, monomials_def, SUBSET_DEF, PULL_EXISTS]
  \\ rfs[rrestrict_def]
QED

Theorem update_zero_BAG_DIFF:
  (x =+ 0)b = b - (\y. if x = y then b x else 0)
Proof
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ rw[BAG_DIFF]
QED

Theorem mpoly_eval_mpoly_eval_o_isolate_var:
  Ring r /\ mpoly r p /\ IMAGE f (support r p DELETE x) SUBSET r.carrier /\
  g x IN r.carrier /\ FINITE (support r p) ==>
  mpoly_eval r (flip (mpoly_eval r) f o isolate_var r x p) g =
  mpoly_eval r p ((x =+ g x) f)
Proof
  strip_tac
  \\ simp[Once mpoly_eval_def]
  \\ simp[Once mpoly_eval_def, SimpRHS]
  \\ drule monomials_mpoly_eval_o_isolate_var
  \\ disch_then drule
  \\ disch_then(qspecl_then[`f`,`x`]strip_assume_tac)
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ qmatch_asmsub_abbrev_tac`s ⊆ ss`
  \\ qmatch_goalsub_abbrev_tac`GBAG r.sum (BAG_IMAGE h _)`
  \\ `FINITE ss` by metis_tac[mpoly_def, SUBSET_FINITE, IMAGE_FINITE]
  \\ `FINITE s` by metis_tac[SUBSET_FINITE]
  \\ `∀t. t IN ss ==>
        GBAG r.prod (BAG_IMAGE g t) = r.prod.exp (g x) (t x)`
  by (
    gen_tac
    \\ simp_tac (srw_ss())[Abbr`ss`]
    \\ strip_tac
    \\ `BAG_IMAGE g t = (λv. if v = g x then m x else 0)`
    by (
      simp[BAG_EXTENSION]
      \\ simp[BAG_INN, BAG_IMAGE_DEF, BAG_FILTER_DEF]
      \\ rpt gen_tac
      \\ Cases_on`e = g x` \\ simp[]
      >- (
        qmatch_goalsub_abbrev_tac`FINITE_BAG b`
        \\ `b = λv. if v = x then m x else 0`
        by ( simp[Abbr`b`, FUN_EQ_THM] \\ rw[] )
        \\ `SET_OF_BAG b SUBSET {x}`
        by (
          simp[SET_OF_BAG, BAG_IN, BAG_INN, Abbr`b`, SUBSET_DEF]
          \\ rw[] )
        \\ rewrite_tac[GSYM FINITE_SET_OF_BAG]
        \\ reverse IF_CASES_TAC
        >- ( `INFINITE {x}` by metis_tac[SUBSET_FINITE] \\ fs[] )
        \\ `BAG_CARD b = m x` suffices_by simp[]
        \\ Cases_on`SET_OF_BAG b = {}` \\ fs[]
        >- ( fs[EMPTY_BAG, FUN_EQ_THM] \\ metis_tac[] )
        \\ `SET_OF_BAG b = {x}` by (
          Cases_on`SET_OF_BAG b` \\ fs[]
          \\ fs[SUBSET_DEF] \\ rw[]
          \\ Cases_on`t'` \\ fs[] \\ metis_tac[] )
        \\ drule SET_OF_BAG_SING_CARD
        \\ simp[] )
      \\ qmatch_goalsub_abbrev_tac`FINITE_BAG b`
      \\ `b = {||}`
      by (
        simp[EMPTY_BAG, Abbr`b`, FUN_EQ_THM]
        \\ rw[] )
      \\ simp[] )
    \\ `t x = (BAG_IMAGE g t) (g x)` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule IMP_GBAG_EQ_EXP
    \\ conj_tac >- metis_tac[Ring_def]
    \\ conj_tac >- simp[]
    \\ rw[SUBSET_DEF, BAG_IN, BAG_INN]
    \\ CCONTR_TAC \\ fs[] )
  \\ `GBAG r.sum (BAG_IMAGE h (BAG_OF_SET (ss DIFF s))) = r.sum.id`
  by (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ simp[Abbr`s`]
    \\ simp[Abbr`h`]
    \\ rw[monomials_def]
    \\ DEP_REWRITE_TAC[ring_mult_lzero]
    \\ simp[]
    \\ `r.carrier = r.prod.carrier` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ metis_tac[] )
  \\ `!s. s SUBSET ss ==>
          GBAG r.sum (BAG_IMAGE h (BAG_OF_SET s)) IN r.sum.carrier`
  by (
    rpt strip_tac
    \\ irule GBAG_in_carrier
    \\ qmatch_assum_rename_tac`xx SUBSET ss`
    \\ `FINITE xx` by metis_tac[SUBSET_FINITE]
    \\ simp[Abbr`h`, SUBSET_DEF, PULL_EXISTS]
    \\ rpt strip_tac
    \\ irule ring_mult_element
    \\ simp[]
    \\ metis_tac[SUBSET_DEF, ring_carriers, ring_exp_element] )
  \\ irule EQ_TRANS
  \\ qexists_tac`r.sum.op (GBAG r.sum (BAG_IMAGE h (BAG_OF_SET s)))
                          (GBAG r.sum (BAG_IMAGE h (BAG_OF_SET (ss DIFF s))))`
  \\ conj_tac >- simp[]
  \\ DEP_REWRITE_TAC[GSYM GBAG_UNION]
  \\ conj_tac
  >- (
    simp[]
    \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`h`]
    \\ rw[]
    \\ irule ring_mult_element
    \\ simp[]
    \\ metis_tac[SUBSET_DEF, ring_carriers, ring_exp_element] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_FINITE_UNION]
  \\ conj_tac >- simp[]
  \\ DEP_REWRITE_TAC[GSYM BAG_OF_SET_DISJOINT_UNION]
  \\ conj_tac >- (simp[IN_DISJOINT] \\ metis_tac[])
  \\ `s UNION (ss DIFF s) = ss`
  by ( simp[EXTENSION] \\ metis_tac[SUBSET_DEF] )
  \\ pop_assum SUBST1_TAC
  \\ `∀t. t IN ss ==> mpoly_eval r (isolate_var r x p t) f IN r.carrier`
  by (
    rpt strip_tac
    \\ irule mpoly_eval_in_carrier
    \\ drule mpoly_isolate_var
    \\ disch_then drule
    \\ drule support_isolate_var
    \\ disch_then drule
    \\ disch_then(qspec_then`x`strip_assume_tac)
    \\ disch_then(qspec_then`x`strip_assume_tac)
    \\ imp_res_tac mpoly_def
    \\ fs[mpoly_ring_carrier]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- metis_tac[]
    \\ metis_tac[SUBSET_FINITE, SUBSET_DEF] )
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum (BAG_IMAGE
         (λt. mpoly_eval r (isolate_var r x p t) f * g x ** t x)
         (BAG_OF_SET ss))`
  \\ conj_tac
  >- (
    AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[]
    \\ simp[Abbr`h`]
    \\ simp[rrestrict_def] )
  \\ qunabbrev_tac`h`
  \\ pop_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE h _`
  \\ `∀t. t IN ss ==> h t =
        GBAG r.sum (BAG_IMAGE (flip (mpoly_eval r) f)
          (BAG_OF_SET (IMAGE (remove_var_mono r x p)
                             (monomials r p INTER {m | m x = t x})))) * g x ** t x`
  by (
    gen_tac
    \\ simp[Abbr`ss`]
    \\ strip_tac
    \\ simp[Abbr`h`]
    \\ DEP_REWRITE_TAC[isolate_var_coeff]
    \\ simp[]
    \\ DEP_REWRITE_TAC[MP_CANON mpoly_eval_sum]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[mpoly_ring_carrier]
    \\ simp[mpoly_remove_var_mono]
    \\ imp_res_tac mpoly_def
    \\ simp[]
    \\ simp[BAG_EVERY, PULL_EXISTS]
    \\ conj_asm1_tac >- simp[support_remove_var_mono]
    \\ reverse conj_tac
    >- metis_tac[FINITE_support_finite_mpoly, mpoly_remove_var_mono,
                 SUBSET_FINITE, FINITE_DELETE]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ pop_assum mp_tac
  \\ qho_match_abbrev_tac`(∀t. t IN ss ==> h t = h2 t) ==> _`
  \\ strip_tac
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG r.sum (BAG_IMAGE h2 (BAG_OF_SET ss))`
  \\ conj_tac
  >- (
    AP_THM_TAC \\ AP_TERM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[] )
  \\ pop_assum kall_tac
  \\ qunabbrev_tac`h`
  \\ `BAG_IMAGE h2 (BAG_OF_SET ss) =
      BAG_IMAGE (λt. GBAG r.sum
        (BAG_IMAGE (λm. mpoly_eval r (remove_var_mono r x p m) f * g x ** m x)
                   (BAG_OF_SET (monomials r p INTER {m | m x = t x}))))
        (BAG_OF_SET ss)`
  by (
    irule BAG_IMAGE_CONG
    \\ simp[Abbr`h2`]
    \\ qx_gen_tac`t` \\ strip_tac
    \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
    \\ conj_tac
    >- (
      rw[remove_var_mono_def, Once FUN_EQ_THM]
      \\ first_x_assum(qspec_then`(x =+ 0) y`mp_tac)
      \\ simp[Once FUN_EQ_THM]
      \\ reverse(rw[]) >- fs[monomials_def]
      \\ fs[combinTheory.APPLY_UPDATE_THM]
      \\ simp[FUN_EQ_THM]
      \\ metis_tac[] )
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ imp_res_tac mpoly_def
    \\ simp[]
    \\ simp[combinTheory.o_DEF]
    \\ DEP_REWRITE_TAC[MP_CANON ring_mult_lsum]
    \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ reverse conj_tac
    >- (
      AP_THM_TAC \\ AP_TERM_TAC
      \\ irule BAG_IMAGE_CONG
      \\ simp[] )
    \\ rw[]
    \\ irule mpoly_eval_in_carrier
    \\ simp[mpoly_remove_var_mono]
    \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
    \\ simp[mpoly_remove_var_mono]
    \\ drule support_remove_var_mono
    \\ disch_then(qspec_then`x`mp_tac)
    \\ strip_tac
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, FINITE_DELETE]
    \\ fs[SUBSET_DEF, PULL_EXISTS] )
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`h2`
  \\ simp[GSYM BAG_FILTER_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE ff (BAG_FILTER _ b)`
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE h (BAG_OF_SET ss)`
  \\ `BAG_IMAGE h (BAG_OF_SET ss) =
      BAG_IMAGE (λP. GBAG r.sum (BAG_IMAGE ff (BAG_FILTER P b)))
        (BAG_IMAGE (λt m. m x = t x) (BAG_OF_SET ss))`
  by (
    DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF] )
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`h`
  \\ DEP_ONCE_REWRITE_TAC[GSYM BAG_OF_SET_IMAGE_INJ]
  \\ conj_tac
  >- (
    simp[Abbr`ss`, PULL_EXISTS]
    \\ rw[FUN_EQ_THM] \\ rw[]
    \\ metis_tac[] )
  \\ DEP_REWRITE_TAC[MP_CANON GBAG_IMAGE_PARTITION]
  \\ simp[]
  \\ simp[Abbr`b`]
  \\ imp_res_tac mpoly_def
  \\ simp[PULL_EXISTS]
  \\ simp[Once FUN_EQ_THM]
  \\ conj_tac
  >- (
    simp[Abbr`ss`, PULL_EXISTS]
    \\ reverse conj_tac >- metis_tac[]
    \\ simp[Abbr`ff`, SUBSET_DEF, PULL_EXISTS]
    \\ rw[]
    \\ irule ring_mult_element
    \\ simp[]
    \\ irule mpoly_eval_in_carrier
    \\ simp[mpoly_remove_var_mono]
    \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
    \\ simp[mpoly_remove_var_mono]
    \\ drule support_remove_var_mono
    \\ disch_then(qspec_then`x`mp_tac)
    \\ strip_tac
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, FINITE_DELETE]
    \\ fs[SUBSET_DEF, PULL_EXISTS] )
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[Abbr`ff`]
  \\ qx_gen_tac`m` \\ strip_tac
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[rrestrict_def]
  \\ simp[mpoly_eval_def]
  \\ `monomials r (remove_var_mono r x p m) SUBSET {(x =+ 0) m}`
  by (
    rw[SUBSET_DEF, monomials_def, remove_var_mono_def]
    \\ CCONTR_TAC \\ fs[] \\ rfs[] )
  \\ Cases_on`monomials r (remove_var_mono r x p m) = {}`
  >- (
    simp[]
    \\ fs[empty_monomials]
    \\ pop_assum mp_tac
    \\ simp[remove_var_mono_def]
    \\ disch_then(qspec_then`(x =+ 0) m`mp_tac)
    \\ simp[rrestrict_def] \\ strip_tac
    \\ DEP_REWRITE_TAC[ring_mult_lzero]
    \\ simp[]
    \\ `r.carrier = r.prod.carrier` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ imp_res_tac FINITE_support_finite_mpoly
    \\ fs[finite_mpoly_def]
    \\ conj_tac >- metis_tac[Ring_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ simp[combinTheory.APPLY_UPDATE_THM]
    \\ fs[support_def, PULL_EXISTS]
    \\ metis_tac[])
  \\ `monomials r (remove_var_mono r x p m) = {(x =+ 0) m}`
  by (
    simp[SET_EQ_SUBSET]
    \\ Cases_on`monomials r (remove_var_mono r x p m)` \\ fs[] )
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ simp[remove_var_mono_def]
  \\ simp[rrestrict_def]
  \\ qmatch_goalsub_abbrev_tac`GBAG r.prod b1`
  \\ qmatch_goalsub_abbrev_tac`_ = _ * GBAG r.prod b2`
  \\ `GBAG r.prod b1 IN r.prod.carrier /\ GBAG r.prod b2 IN r.prod.carrier`
  by (
    conj_tac \\ irule GBAG_in_carrier
    \\ (conj_tac >- metis_tac[Ring_def])
    \\ imp_res_tac FINITE_support_finite_mpoly
    \\ fs[finite_mpoly_def]
    \\ simp[Abbr`b1`, Abbr`b2`]
    \\ fs[SUBSET_DEF, PULL_EXISTS, support_def, combinTheory.APPLY_UPDATE_THM]
    >- (
      fs[BAG_IN, BAG_INN, combinTheory.APPLY_UPDATE_THM]
      \\ reverse conj_tac
      >- ( rw[] \\ metis_tac[] )
      \\ irule BAG_IMAGE_FINITE
      \\ simp[update_zero_BAG_DIFF]
      \\ irule FINITE_BAG_DIFF
      \\ simp[] )
    \\ rw[] \\ metis_tac[] )
  \\ rfs[]
  \\ DEP_REWRITE_TAC[ring_mult_assoc]
  \\ conj_tac >- simp[]
  \\ AP_TERM_TAC
  \\ `m = BAG_UNION ((x =+ 0) m) (λy. if y = x then m x else 0)`
  by (
    simp[FUN_EQ_THM, BAG_UNION, combinTheory.APPLY_UPDATE_THM]
    \\ gen_tac \\ IF_CASES_TAC \\ simp[] )
  \\ `FINITE_BAG m` by metis_tac[FINITE_support_finite_mpoly, finite_mpoly_def]
  \\ qmatch_asmsub_abbrev_tac`m = BAG_UNION m1 m2`
  \\ `FINITE_BAG m1 /\ FINITE_BAG m2` by metis_tac[FINITE_BAG_UNION]
  \\ qpat_x_assum`m = _`(assume_tac o SYM)
  \\ simp[Abbr`b2`]
  \\ qmatch_goalsub_abbrev_tac`_ * gmx`
  \\ first_assum(fn th => CHANGED_TAC(rewrite_tac[(SYM th)]))
  \\ simp[]
  \\ DEP_REWRITE_TAC[GBAG_UNION]
  \\ conj_tac
  >- (
    simp[]
    \\ conj_tac >- metis_tac[Ring_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, support_def, Abbr`m1`, Abbr`m2`]
    \\ fs[combinTheory.APPLY_UPDATE_THM, BAG_IN, BAG_INN]
    \\ rpt strip_tac \\ IF_CASES_TAC \\ fs[]
    \\ metis_tac[] )
  \\ `BAG_IMAGE ((x =+ g x) f) m1 = b1`
  by (
    qunabbrev_tac`b1`
    \\ irule BAG_IMAGE_CONG
    \\ simp[combinTheory.APPLY_UPDATE_THM]
    \\ simp[Abbr`m1`, update_zero_BAG_DIFF]
    \\ simp[BAG_IN, BAG_INN, BAG_DIFF]
    \\ strip_tac \\ IF_CASES_TAC \\ simp[] )
  \\ simp[]
  \\ AP_TERM_TAC
  \\ irule EQ_SYM
  \\ qunabbrev_tac`gmx`
  \\ qmatch_goalsub_abbrev_tac`GBAG r.prod b2`
  \\ `m x = b2 (g x)`
  by (
    simp[Abbr`b2`]
    \\ `BAG_IMAGE ((x =+ g x) f) m2 = (λv. if v = g x then m x else 0)`
    by (
      simp[BAG_EXTENSION]
      \\ simp[BAG_INN, BAG_IMAGE_DEF, BAG_FILTER_DEF]
      \\ rpt gen_tac
      \\ simp[combinTheory.APPLY_UPDATE_THM]
      \\ Cases_on`e = g x` \\ simp[]
      >- (
        qmatch_goalsub_abbrev_tac`FINITE_BAG b`
        \\ `b = λv. if v = x then m x else 0`
        by ( simp[Abbr`b`, FUN_EQ_THM, Abbr`m2`] \\ rw[] )
        \\ `SET_OF_BAG b SUBSET {x}`
        by (
          simp[SET_OF_BAG, BAG_IN, BAG_INN, Abbr`b`, SUBSET_DEF, Abbr`m2`]
          \\ rw[] )
        \\ rewrite_tac[GSYM FINITE_SET_OF_BAG]
        \\ reverse IF_CASES_TAC
        >- ( `INFINITE {x}` by metis_tac[SUBSET_FINITE] \\ fs[] )
        \\ `BAG_CARD b = m x` suffices_by simp[]
        \\ Cases_on`SET_OF_BAG b = {}` \\ fs[Abbr`m2`]
        >- ( fs[EMPTY_BAG, FUN_EQ_THM] \\ metis_tac[] )
        \\ `SET_OF_BAG b = {x}` by (
          Cases_on`SET_OF_BAG b` \\ fs[]
          \\ fs[SUBSET_DEF] \\ rw[]
          \\ Cases_on`t` >- simp[]
          \\ metis_tac[IN_INSERT])
        \\ drule SET_OF_BAG_SING_CARD
        \\ simp[] )
      \\ qmatch_goalsub_abbrev_tac`FINITE_BAG b`
      \\ `b = {||}`
      by (
        simp[EMPTY_BAG, Abbr`b`, FUN_EQ_THM, Abbr`m2`]
        \\ rw[] )
      \\ simp[] )
    \\ simp[] )
  \\ pop_assum SUBST1_TAC
  \\ irule IMP_GBAG_EQ_EXP
  \\ simp[]
  \\ conj_tac >- metis_tac[Ring_def]
  \\ rw[SUBSET_DEF, BAG_IN, BAG_INN, Abbr`b2`, Abbr`m2`]
  \\ rw[combinTheory.APPLY_UPDATE_THM] \\ fs[]
QED

Theorem zero_degree_of_is_zero:
  IntegralDomain r /\ mpoly r p /\ FINITE (support r p) /\
  BIGUNION (IMAGE s (support r p)) SUBSET r.carrier /\
  (!x. x IN support r p /\ FINITE (s x) ==> degree_of r p x < CARD (s x)) ∧
  (∀f. (∀x. x IN support r p ==> f x IN s x)
       ==> mpoly_eval r p f = r.sum.id)
  ==>
  p = K r.sum.id
Proof
  strip_tac
  \\ ntac 4 (pop_assum mp_tac)
  \\ qmatch_goalsub_abbrev_tac`FINITE supp`
  \\ `support r p ⊆ supp` by simp[Abbr`supp`]
  \\ strip_tac
  \\ qpat_x_assum`_ SUBSET _`mp_tac
  \\ qpat_x_assum`mpoly _ _`mp_tac
  \\ qid_spec_tac`s`
  \\ qid_spec_tac`p`
  \\ pop_assum mp_tac
  \\ qid_spec_tac`supp`
  \\ pop_assum kall_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ simp[]
  \\ conj_tac
  >- (
    rw[empty_support]
    \\ gs[mpoly_eval_def]
    \\ Cases_on`monomials r p` \\ gs[empty_monomials]
    >- gs[mpoly_def, PULL_EXISTS, SUBSET_DEF, FUN_EQ_THM]
    \\ fs[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ simp[FUN_EQ_THM]
    \\ fs[monomials_def, Once EXTENSION]
    \\ `Ring r` by fs[IntegralDomain_def]
    \\ fs[]
    \\ rfs[mpoly_def, SUBSET_DEF, PULL_EXISTS, rrestrict_def]
    \\ metis_tac[] )
  \\ rpt strip_tac
  \\ reverse(Cases_on`e IN support r p`)
  >- (
    first_x_assum irule
    \\ reverse conj_tac >- fs[SUBSET_DEF]
    \\ qexists_tac`s` \\ rw[]
    \\ first_x_assum(qspec_then`λx. if x = e then CHOICE (s e) else f x`mp_tac)
    \\ impl_tac
    >- (
      reverse(rw[])
      \\ irule CHOICE_DEF
      \\ `degree_of r p e = 0`
      by (
        imp_res_tac mpoly_def
        \\ imp_res_tac support_degree_of
        \\ `¬(1 <= degree_of r p e)` by metis_tac[]
        \\ fs[] )
      \\ reverse(Cases_on`FINITE (s e)`)
      >- metis_tac[cardinalTheory.INFINITE_NONEMPTY]
      \\ `0 < CARD (s e)` by metis_tac[]
      \\ Cases_on`s e` \\ fs[] )
    \\ disch_then(SUBST1_TAC o SYM)
    \\ irule mpoly_eval_support
    \\ rw[] )
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ `∀f. (∀x. x IN supp ==> f x IN s x) ==>
          mpoly r (flip (mpoly_eval r) f o (isolate_var r e p)) /\
          support r (flip (mpoly_eval r) f o (isolate_var r e p)) SUBSET {e}`
  by (
    gen_tac \\ strip_tac
    \\ first_x_assum(qspecl_then[`p`,`s`]kall_tac)
    \\ drule monomials_mpoly_eval_o_isolate_var
    \\ disch_then drule
    \\ disch_then(qspecl_then[`f`,`e`]mp_tac)
    \\ strip_tac
    \\ reverse conj_tac
    >- (
      pop_assum mp_tac
      \\ simp[support_def, SUBSET_DEF, PULL_EXISTS]
      \\ rw[]
      \\ first_x_assum drule \\ strip_tac
      \\ fs[BAG_IN, BAG_INN]
      \\ CCONTR_TAC \\ fs[] )
    \\ simp[mpoly_def]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ conj_tac
    >- (
      qx_gen_tac`t`
      \\ irule mpoly_eval_in_carrier
      \\ `mpoly (mpoly_ring r (support r p DELETE e)) (isolate_var r e p)`
      by ( irule mpoly_isolate_var \\ simp[] )
      \\ imp_res_tac mpoly_def
      \\ fs[SUBSET_DEF, PULL_EXISTS]
      \\ fs[mpoly_ring_carrier]
      \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
      \\ `support r p SUBSET e INSERT supp` by simp[SUBSET_DEF]
      \\ `FINITE (support r p)` by
      metis_tac[SUBSET_DEF, SUBSET_FINITE, FINITE_INSERT]
      \\ conj_tac >- metis_tac[]
      \\ conj_tac >- metis_tac[IN_DELETE, SUBSET_DEF]
      \\ metis_tac[SUBSET_FINITE, FINITE_DELETE])
    \\ metis_tac[SUBSET_FINITE, IMAGE_FINITE, mpoly_def])
  \\ `∀f g. (∀x. x IN supp ==> f x IN s x) /\ g e IN s e ==>
            mpoly_eval r
              (flip (mpoly_eval r) f o (isolate_var r e p)) g = r.sum.id`
  by (
    rpt strip_tac
    \\ irule EQ_TRANS
    \\ qexists_tac`mpoly_eval r p ((e =+ g e) f)`
    \\ reverse conj_tac
    >- (
      first_x_assum irule
      \\ simp[combinTheory.APPLY_UPDATE_THM]
      \\ rw[] \\ rw[] )
    \\ irule mpoly_eval_mpoly_eval_o_isolate_var
    \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_INSERT]
    \\ conj_tac >- simp[]
    \\ conj_tac >- metis_tac[SUBSET_DEF]
    \\ simp_tac(srw_ss())[SUBSET_DEF, PULL_EXISTS]
    \\ qpat_x_assum`BIGUNION _ SUBSET _`mp_tac
    \\ simp_tac(srw_ss())[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[SUBSET_DEF, IN_INSERT])
  \\ `∀f. (∀x. x IN supp ==> f x IN s x) ==>
          (flip (mpoly_eval r) f o (isolate_var r e p)) = K r.sum.id`
  by (
    rpt strip_tac
    \\ qmatch_goalsub_abbrev_tac`q = _`
    \\ CCONTR_TAC
    \\ `q IN (mpoly_ring r {e}).carrier`
    by ( simp[mpoly_ring_carrier] \\ metis_tac[] )
    \\ `poly_of_mpoly r q <> (PolyRing r).sum.id`
    by (
      disch_then(mp_tac o Q.AP_TERM`mpoly_of_poly r e`)
      \\ DEP_REWRITE_TAC[mpoly_of_poly_of_mpoly]
      \\ conj_tac >- metis_tac[]
      \\ `mpoly_of_poly r e (PolyRing r).sum.id = K r.sum.id`
      suffices_by simp[]
      \\ simp[FUN_EQ_THM]
      \\ simp[mpoly_of_poly_def] )
    \\ `poly (poly_of_mpoly r q)` by (
      irule poly_poly_of_mpoly
      \\ metis_tac[mpoly_def] )
    \\ `FINITE (roots (poly_of_mpoly r q))`
    by metis_tac[polyRootTheory.poly_roots_finite_id]
    \\ `CARD (roots (poly_of_mpoly r q)) <= Deg r (poly_of_mpoly r q)`
    by metis_tac[polyRootTheory.poly_roots_count_id]
    \\ `Deg r (poly_of_mpoly r q) = degree_of r q e`
    by (
      DEP_REWRITE_TAC[GSYM (Q.SPEC`e`(Q.GEN`v`degree_of_mpoly_of_poly))]
      \\ DEP_REWRITE_TAC[mpoly_of_poly_of_mpoly]
      \\ metis_tac[] )
    \\ drule poly_roots_of_mpoly
    \\ disch_then (qspecl_then[`e`,`q`]mp_tac)
    \\ impl_tac >- metis_tac[]
    \\ qmatch_goalsub_abbrev_tac`_ = ss`
    \\ `s e SUBSET ss`
    by (
      simp[Abbr`ss`, SUBSET_DEF]
      \\ qx_gen_tac`v` \\ strip_tac
      \\ qexists_tac`K v`
      \\ simp[]
      \\ simp[mpoly_roots_def]
      \\ simp[SUBSET_DEF, PULL_EXISTS]
      \\ conj_tac >- metis_tac[SUBSET_DEF]
      \\ simp[mpoly_root_def]
      \\ first_x_assum(qspecl_then[`f`,`K v`]mp_tac)
      \\ simp[] )
    \\ `FINITE ss ==> CARD (s e) <= CARD ss`
    by (
      strip_tac
      \\ irule CARD_SUBSET
      \\ simp[] )
    \\ strip_tac
    \\ `degree_of r q e <= degree_of r p e`
    by (
      simp[degree_of_def]
      \\ drule monomials_mpoly_eval_o_isolate_var
      \\ disch_then drule
      \\ disch_then(qspecl_then[`f`,`e`]mp_tac)
      \\ simp[] \\ strip_tac
      \\ Cases_on`monomials r q = {}` \\ simp[]
      \\ irule X_LE_MAX_SET
      \\ simp[]
      \\ imp_res_tac mpoly_def \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`MAX_SET ms`
      \\ `FINITE ms` by metis_tac[mpoly_def, IMAGE_FINITE]
      \\ `ms <> {}` by (strip_tac \\ fs[Abbr`ms`])
      \\ `MAX_SET ms IN ms` by metis_tac[MAX_SET_DEF]
      \\ qmatch_goalsub_abbrev_tac`mms = _`
      \\ fs[Abbr`ms`]
      \\ fs[SUBSET_DEF]
      \\ res_tac
      \\ qexists_tac`m`
      \\ rw[] )
    \\ `FINITE ss` by metis_tac[]
    \\ `FINITE (s e)` by metis_tac[SUBSET_FINITE]
    \\ `degree_of r p e < CARD (s e)` by metis_tac[]
    \\ `degree_of r q e < CARD (s e)` by simp[]
    \\ `CARD ss <= degree_of r q e` by metis_tac[]
    \\ fs[] )
  \\ `p IN (mpoly_ring r (support r p)).carrier`
  by simp[mpoly_ring_carrier]
  \\ qmatch_asmsub_abbrev_tac`p IN rr.carrier`
  \\ `p = rr.sum.id` suffices_by simp[Abbr`rr`, mpoly_ring_def]
  \\ drule RingIso_isolate_var
  \\ disch_then drule \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`RingIso _ _ re`
  \\ strip_tac
  \\ `Ring rr /\ Ring re` by simp[Abbr`rr`, Abbr`re`]
  \\ `rr.sum.id IN rr.carrier` by metis_tac[ring_zero_element]
  \\ `isolate_var r e p = re.sum.id` suffices_by metis_tac[ring_iso_eq_zero]
  \\ qmatch_asmsub_abbrev_tac`re = mpoly_ring rd _`
  \\ simp[Once FUN_EQ_THM]
  \\ qx_gen_tac`t`
  \\ `re.sum.id = K (K r.sum.id)` by
  simp_tac(srw_ss()++boolSimps.LET_ss)[Abbr`rd`, Abbr`re`, mpoly_ring_def]
  \\ pop_assum SUBST1_TAC \\ simp[]
  \\ first_x_assum irule
  \\ drule_then drule mpoly_isolate_var
  \\ disch_then(qspec_then`e`mp_tac)
  \\ asm_simp_tac pure_ss []
  \\ strip_tac
  \\ drule (mpoly_def |> SPEC_ALL |> EQ_IMP_RULE |> #1)
  \\ strip_tac
  \\ `isolate_var r e p t IN rd.carrier` by fs[SUBSET_DEF, PULL_EXISTS]
  \\ reverse conj_asm2_tac
  >- (
    fs[Abbr`rd`, mpoly_ring_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ qexists_tac`s`
  \\ conj_asm1_tac
  >- (
    rpt strip_tac
    \\ irule arithmeticTheory.LESS_EQ_LESS_TRANS
    \\ qexists_tac`degree_of r p x`
    \\ conj_tac >- metis_tac[]
    \\ irule degree_of_isolate_var_le
    \\ simp[] )
  \\ reverse conj_tac >- simp[]
  \\ rpt strip_tac
  \\ reverse(Cases_on`t IN monomials rd (isolate_var r e p)`)
  >- (
    pop_assum mp_tac
    \\ simp[monomials_def]
    \\ simp[rrestrict_def]
    \\ `rd.sum.id = K r.sum.id` by simp[Abbr`rd`, mpoly_ring_def]
    \\ simp[mpoly_eval_zero] )
  \\ pop_assum mp_tac
  \\ qunabbrev_tac`rd`
  \\ DEP_REWRITE_TAC[monomials_isolate_var]
  \\ conj_tac >- simp[]
  \\ strip_tac
  \\ first_x_assum drule
  \\ simp[FUN_EQ_THM]
QED

val _ = export_theory();
