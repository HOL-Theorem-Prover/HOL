Theory veblen
Ancestors
  ordinal pred_set cardinal

(* Material from Brian Huffman's AFP entry on Ordinal arithmetic *)

Theorem better_induction:
    !P. P 0 /\ (!a. P a ==> P a^+) /\
        (!a. 0 < a /\ (!b. b < a ==> P b) ==> P (sup (preds a))) ==>
        !a. P a
Proof
  gen_tac >> strip_tac >> match_mp_tac simple_ord_induction >> simp[] >>
  qx_gen_tac `a` >> strip_tac >> fs[sup_preds_omax_NONE] >> metis_tac[]
QED

Definition closed_def:
  closed A <=> !g. (!n:num. g n IN A) ==> sup { g n | n | T} IN A
End

Definition unbounded_def:
  unbounded (A:'a ordinal set) = !a. ?b. b IN A /\ a < b
End

Definition club_def:  club A <=> closed A /\ unbounded A
End

Definition continuous_def:
  continuous f <=>
    !A:'a ordinal set.
          A <<= univ(:'a inf) ==> f (sup A) = sup (IMAGE f A)
End

Definition strict_mono_def:
  strict_mono f <=> !x y:'a ordinal. x < y ==> f x < f y
End

val dsimp = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss)

Theorem nrange_IN_Uinf[simp]:
    { f n | n:num | T} <<= univ(:'a inf)
Proof
  qsuff_tac `countable { f n | n | T }`
  >- metis_tac[Unum_cle_Uinf, cardleq_TRANS, countable_thm] >>
  simp[countable_surj] >> disj2_tac >> qexists_tac `f` >>
  simp[SURJ_DEF] >> metis_tac[]
QED

Theorem increasing:
    !f x. strict_mono f /\ continuous f ==> x <= f x
Proof
  ntac 3 strip_tac >> qid_spec_tac `x` >>
  ho_match_mp_tac better_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `x` >> strip_tac >> simp[ordlt_SUC_DISCRETE] >>
      qsuff_tac `x < f x^+`
      >- (simp[ordle_lteq] >> rpt strip_tac >> fs[]) >>
      match_mp_tac ordlet_TRANS >> qexists_tac `f x` >>
      fs[strict_mono_def]) >>
  qx_gen_tac `a` >> strip_tac >> fs[continuous_def, preds_inj_univ] >>
  simp[sup_thm,preds_inj_univ] >> qx_gen_tac `b` >> Cases_on `a <= b` >>
  simp[] >> fs[] >> match_mp_tac ordle_TRANS >> qexists_tac `f b` >>
  simp[] >> match_mp_tac suple_thm >> simp[IMAGE_cardleq_rwt, preds_inj_univ]
QED

Theorem clubs_exist:
    strict_mono (f:'a ordinal -> 'a ordinal) /\ continuous f ==>
      club (IMAGE f univ(:'a ordinal))
Proof
  simp[club_def, closed_def, unbounded_def] >> rpt strip_tac >| [
    qabbrev_tac `ss = { oleast x. g n = f x | n | T }` >>
    qexists_tac `sup ss` >> `ss <<= univ(:'a inf)` by simp[Abbr`ss`] >>
    `f (sup ss) = sup (IMAGE f ss)` by fs[continuous_def] >>
    simp[] >> match_mp_tac sup_eq_sup >>
    dsimp[IMAGE_cardleq_rwt] >> simp[] >> conj_tac
    >- (dsimp[Abbr`ss`] >> qx_gen_tac `n` >> qexists_tac `n` >>
        DEEP_INTRO_TAC oleast_intro >> simp[]) >>
    dsimp[Abbr`ss`] >> qx_gen_tac `n` >> qexists_tac `n` >>
    DEEP_INTRO_TAC oleast_intro >> simp[],
    dsimp[] >> qexists_tac `a^+` >> match_mp_tac ordlet_TRANS >>
    qexists_tac `f a` >> fs[strict_mono_def, increasing]
  ]
QED

Theorem mono_natI:
    (!n. f n : 'a ordinal <= f (SUC n)) ==> !m n. m <= n ==> f m <= f n
Proof
  strip_tac >> Induct_on `n` >> simp[] >> qx_gen_tac `m` >> strip_tac >>
  Cases_on `m = SUC n` >- simp[] >>
  `m <= n` by decide_tac >>
  metis_tac[ordle_TRANS]
QED

Theorem sup_mem_INTER:
    (!n. club (A n)) /\ (!n. A (SUC n) SUBSET A n) /\
    (!n. f n IN A n) /\ (!m n. m <= n ==> f m <= f n) ==>
    sup {f n | n | T} IN BIGINTER {A n | n | T}
Proof
  dsimp[] >> qx_gen_tac `k` >> strip_tac >>
  `sup { f n | n | T} = sup { f (n + k) | n | T }`
    by (match_mp_tac sup_eq_sup >> dsimp[] >> simp[] >> conj_tac
        >- (qx_gen_tac `n` >> qexists_tac `n` >>
            first_x_assum match_mp_tac >> decide_tac) >>
        qx_gen_tac `n` >> qexists_tac `k + n` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qsuff_tac `!n. f (n + k) IN A k` >- fs[club_def, closed_def] >>
  qx_gen_tac `n` >>
  qsuff_tac `A (n + k) SUBSET A k` >- metis_tac [SUBSET_DEF] >>
  Induct_on `n` >> simp[arithmeticTheory.ADD_CLAUSES] >>
  metis_tac [SUBSET_TRANS, DECIDE ``x + y:num = y + x``]
QED

val smem' = sup_mem_INTER |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) []
                          |> GEN_ALL

Theorem oleast_leq:
    !P a. P a ==> (oleast) P <= a
Proof
  ntac 3 strip_tac >> DEEP_INTRO_TAC oleast_intro >> metis_tac[]
QED

Theorem club_INTER:
    (!n. club (A n)) /\ (!n. A (SUC n) SUBSET A n) ==>
    club (BIGINTER {A n | n | T})
Proof
  strip_tac >> simp[club_def] >> conj_tac
  >- (fs[closed_def, club_def] >> dsimp[]) >>
  dsimp[club_def, closed_def, unbounded_def] >>
  qx_gen_tac `a` >> rpt strip_tac >>
  qexists_tac `sup {oleast b. b IN A n /\ a < b | n | T}` >>
  conj_tac
  >- (qx_gen_tac `n` >> ho_match_mp_tac smem' >> simp[] >>
      conj_tac
      >- (qx_gen_tac `n` >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
          fs[club_def, unbounded_def]) >>
      ho_match_mp_tac mono_natI >> qx_gen_tac `n` >>
      ho_match_mp_tac oleast_leq >>
      conj_tac
      >- (DEEP_INTRO_TAC oleast_intro >> conj_tac
          >- fs[club_def, unbounded_def] >>
          metis_tac[SUBSET_DEF]) >>
      DEEP_INTRO_TAC oleast_intro >> conj_tac
      >- fs[club_def, unbounded_def] >> simp[]) >>
  simp[sup_thm] >> dsimp[] >> qexists_tac `n` >>
  DEEP_INTRO_TAC oleast_intro >> simp[] >> fs[club_def, unbounded_def]
QED

