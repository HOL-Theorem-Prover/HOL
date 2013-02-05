open HolKernel Parse boolLib bossLib

open ordinalTheory
open lcsymtacs

open pred_setTheory cardinalTheory
val _ = new_theory "veblen"

val closed_def = Define`
  closed A ⇔ ∀g. (∀n:num. g n ∈ A) ⇒ sup { g n | n | T} ∈ A
`;

val unbounded_def = Define`
  unbounded (A:α ordinal set) = ∀a. ∃b. b ∈ A ∧ a < b
`;

val club_def = Define`club A ⇔ closed A ∧ unbounded A`

val continuous_def = Define`
  continuous f ⇔
    ∀A:'a ordinal set.
          A ≼ univ(:'a inf) ⇒ f (sup A) = sup (IMAGE f A)
`;

val strict_mono_def = Define`
  strict_mono f ⇔ ∀x y:'a ordinal. x < y ⇒ f x < f y
`;

val dsimp = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss)

val nrange_IN_Uinf = store_thm(
  "nrange_IN_Uinf",
  ``{ f n | n:num | T} ≼ 𝕌(:'a inf)``,
  qsuff_tac `countable { f n | n | T }`
  >- metis_tac[Unum_cle_Uinf, cardleq_TRANS, countable_thm] >>
  simp[countable_surj] >> disj2_tac >> qexists_tac `f` >>
  simp[SURJ_DEF] >> metis_tac[]);
val _ = export_rewrites ["nrange_IN_Uinf"]

(*
val increasing = store_thm(
  "increasing",
  ``strict_mono f ∧ continuous f ⇒ x ≤ f x``,
  strip_tac >> qid_spec_tac `x` >>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `x` >> strip_tac >> simp[ordlt_SUC_DISCRETE] >>
      qsuff_tac `x < f x⁺`
      >- (simp[ordle_lteq] >> rpt strip_tac >> fs[]) >>
      match_mp_tac ordlet_TRANS >> qexists_tac `f x` >>
      fs[strict_mono_def]) >>
  qx_gen_tac `a` >> strip_tac >>


val clubs_exist = store_thm(
  "clubs_exist",
  ``strict_mono (f:'a ordinal -> 'a ordinal) ∧ continuous f ⇒
      club (IMAGE f 𝕌(:'a ordinal))``,
  simp[club_def, closed_def, unbounded_def] >> rpt strip_tac >| [
    qabbrev_tac `ss = { oleast x. g n = f x | n | T }` >>
    qexists_tac `sup ss` >> `ss ≼ 𝕌(:'a inf)` by simp[Abbr`ss`] >>
    `f (sup ss) = sup (IMAGE f ss)` by fs[continuous_def] >>
    simp[] >> match_mp_tac sup_eq_sup >>
    dsimp[IMAGE_cardleq_rwt] >> simp[] >> conj_tac
    >- (dsimp[Abbr`ss`] >> qx_gen_tac `n` >> qexists_tac `n` >>
        DEEP_INTRO_TAC oleast_intro >> simp[]) >>
    dsimp[Abbr`ss`] >> qx_gen_tac `n` >> qexists_tac `n` >>
    DEEP_INTRO_TAC oleast_intro >> simp[],
    dsimp[] >> qexists_tac `a⁺` >> match_mp_tac ordlet_TRANS >>
    qexists_tac `f a` >> fs[strict_mono_def]
  ]);

val sup_mem_INTER = store_thm(
  "sup_mem_INTER",
  ``(∀n. club (A n)) ∧ (∀n. A (SUC n) ⊆ A n) ∧
    (∀n. f n ∈ A n) ∧ (∀m n. m ≤ n ⇒ f m ≤ f n) ⇒
    sup {f n | n | T} ∈ BIGINTER {A n | n | T}``,
  dsimp[] >> qx_gen_tac `k` >> strip_tac >>
  `sup { f n | n | T} = sup { f (n + k) | n | T }`
    by (match_mp_tac sup_eq_sup >> dsimp[] >> simp[] >> conj_tac
        >- (qx_gen_tac `n` >> qexists_tac `n` >>
            first_x_assum match_mp_tac >> decide_tac) >>
        qx_gen_tac `n` >> qexists_tac `k + n` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qsuff_tac `∀n. f (n + k) ∈ A k` >- fs[club_def, closed_def] >>
  qx_gen_tac `n` >>
  qsuff_tac `A (n + k) ⊆ A k` >- metis_tac [SUBSET_DEF] >>
  Induct_on `n` >> simp[arithmeticTheory.ADD_CLAUSES] >>
  metis_tac [SUBSET_TRANS, DECIDE ``x + y:num = y + x``]);

val club_INTER = store_thm(
  "club_INTER",
  ``(∀n. club (A n)) ∧ (∀n. A (SUC n) ⊆ A n) ⇒
    club (BIGINTER {A n | n | T})``,
  strip_tac >> simp[club_def] >> conj_tac
  >- (fs[closed_def, club_def] >> dsimp[]) >>
  dsimp[club_def, closed_def, unbounded_def] >>
  qx_gen_tac `a` >> rpt strip_tac >>
  qexists_tac `sup {oleast b. b ∈ A n ∧ a < b | n | T}` >>
  conj_tac
  >- (qx_gen_tac `n` >> first_assum ho_match_mp_tac >>
      qx_gen_tac `m` >> DEEP_INTRO_TAC oleast_intro >> conj_tac
      >- metis_tac[] >>
      rw[]


  simp[sup_thm] >> dsimp[] >> qexists_tac `n` >>
  DEEP_INTRO_TAC oleast_intro >> simp[]
*)

val _ = export_theory()
