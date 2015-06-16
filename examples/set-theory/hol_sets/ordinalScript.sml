open HolKernel Parse boolLib bossLib
open lcsymtacs
open boolSimps

open set_relationTheory pred_setTheory cardinalTheory
open wellorderTheory

val _ = new_theory "ordinal"

val _ = ParseExtras.tight_equality()

fun dsimp thl = asm_simp_tac (srw_ss() ++ DNF_ss) thl

(* perform quotient, creating a type of "ordinals". *)
fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = NONE, fname = s, func = t};

val orderiso_equiv = prove(
  ``!s1 s2. orderiso (s1:'a wellorder) (s2:'a wellorder) <=>
            (orderiso s1 : 'a wellorder set = orderiso s2)``,
  rw[FUN_EQ_THM, EQ_IMP_THM] >>
  metis_tac [orderiso_SYM, orderiso_TRANS, orderiso_REFL])

val alphaise =
    INST_TYPE  [beta |-> ``:'a inf``, delta |-> ``:'a inf``,
                gamma |-> ``:'a inf``, alpha |-> ``:'a inf``]

val [ordlt_REFL, ordlt_TRANS, ordlt_WF0, ordlt_trichotomy] =
    quotient.define_quotient_types_full
    {
     types = [{name = "ordinal", equiv = alphaise orderiso_equiv}],
     defs = map mk_def
       [("ordlt", ``orderlt : 'a inf wellorder -> 'a inf wellorder -> bool``)],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     respects = [alphaise orderlt_orderiso, alphaise finite_iso],
     poly_preserves = [],
     poly_respects = [],
     old_thms = [alphaise orderlt_REFL, alphaise orderlt_TRANS,
                 alphaise (REWRITE_RULE [relationTheory.WF_DEF] orderlt_WF),
                 alphaise orderlt_trichotomy]}

val _ = save_thm ("ordlt_REFL", ordlt_REFL)
val _ = export_rewrites ["ordlt_REFL"]
val _ = save_thm ("ordlt_TRANS", ordlt_TRANS)
val ordlt_WF = save_thm (
  "ordlt_WF",
  REWRITE_RULE [GSYM relationTheory.WF_DEF] ordlt_WF0)

val _ = overload_on ("<", ``ordlt``)
val _ = overload_on ("<=", ``\a b. ~(b < a)``)

val _ = save_thm ("ordlt_trichotomy", ordlt_trichotomy)

val _ = overload_on ("mkOrdinal", ``ordinal_ABS``)

val allOrds_def = Define`
  allOrds = wellorder_ABS { (x,y) | (x = y) \/ ordlt x y }
`;
val EXISTS_PROD = pairTheory.EXISTS_PROD
val EXISTS_SUM = sumTheory.EXISTS_SUM
val FORALL_SUM = sumTheory.FORALL_SUM

val wellorder_allOrds = store_thm(
  "wellorder_allOrds",
  ``wellorder { (x,y) | x = y \/ ordlt x y }``,
  simp[wellorder_def, strict_def, wellfounded_WF, relationTheory.WF_DEF] >>
  rpt conj_tac >| [
    simp_tac (srw_ss() ++ CONJ_ss)
             [REWRITE_RULE[SPECIFICATION] GSPECIFICATION, EXISTS_PROD] >>
    metis_tac[ordlt_REFL, ordlt_WF0],
    simp[linear_order_def, in_domain, in_range] >> rw[]
      >- (simp[transitive_def]>> metis_tac [ordlt_TRANS])
      >- (simp[antisym_def] >> metis_tac [ordlt_TRANS, ordlt_REFL]) >>
    metis_tac [ordlt_trichotomy],
    simp[reflexive_def]
  ])

val WIN_allOrds = store_thm(
  "WIN_allOrds",
  ``(x,y) WIN allOrds <=> ordlt x y``,
  simp[allOrds_def, destWO_mkWO, wellorder_allOrds, strict_def] >>
  metis_tac [ordlt_REFL]);

val elsOf_allOrds = store_thm(
  "elsOf_allOrds",
  ``elsOf allOrds = univ(:'a ordinal)``,
  rw[elsOf_def, EXTENSION, in_domain, in_range, allOrds_def,
     destWO_mkWO, wellorder_allOrds] >>
  metis_tac [ordlt_trichotomy]);

val (mkOrdinal_REP, orderiso_mkOrdinal) =
  theorem "ordinal_QUOTIENT"
          |> SIMP_RULE (srw_ss()) [quotientTheory.QUOTIENT_def, orderiso_REFL]
          |> CONJ_PAIR


val ordlt_mkOrdinal = store_thm(
  "ordlt_mkOrdinal",
  ``ordlt o1 o2 <=>
    !w1 w2. (mkOrdinal w1 = o1) /\ (mkOrdinal w2 = o2) ==> orderlt w1 w2``,
  rw[definition "ordlt_def"] >> eq_tac >> rpt strip_tac >| [
    `orderiso w1 (ordinal_REP o1) /\ orderiso w2 (ordinal_REP o2)`
      by metis_tac [orderiso_mkOrdinal, mkOrdinal_REP] >>
    metis_tac [orderlt_orderiso],
    simp[mkOrdinal_REP]
  ]);

val orderlt_iso_REFL = store_thm(
  "orderlt_iso_REFL",
  ``orderiso w1 w2 ==> ~orderlt w1 w2``,
  metis_tac [orderlt_orderiso, orderlt_REFL, orderiso_REFL]);

val orderiso_wobound2 = store_thm(
  "orderiso_wobound2",
  ``orderiso (wobound x w) (wobound y w) ==> ~((x,y) WIN w)``,
  rpt strip_tac >>
  qsuff_tac `orderlt (wobound x w) (wobound y w)`
     >- metis_tac [orderlt_iso_REFL] >>
  simp[orderlt_def] >> qexists_tac `x` >>
  simp[elsOf_wobound, wobound2,orderiso_REFL]);

val wellorder_ordinal_isomorphism = store_thm(
  "wellorder_ordinal_isomorphism",
  ``!w. orderiso w (wobound (mkOrdinal w) allOrds)``,
  spose_not_then assume_tac >>
  pop_assum (strip_assume_tac o REWRITE_RULE [] o
             HO_MATCH_MP (REWRITE_RULE [relationTheory.WF_DEF] orderlt_WF)) >>
  `orderlt w (wobound (mkOrdinal w) allOrds) \/
     orderlt (wobound (mkOrdinal w) allOrds) w`
    by metis_tac [orderlt_trichotomy]
  >| [
    pop_assum mp_tac >> simp[orderlt_def] >> qx_gen_tac `b` >>
    Cases_on `b ∈ elsOf (wobound (mkOrdinal w) allOrds)` >> simp[] >>
    pop_assum mp_tac >> simp[elsOf_wobound, wobound2] >>
    simp[WIN_allOrds] >> rpt strip_tac >>
    fs[ordlt_mkOrdinal] >>
    first_x_assum (qspecl_then [`ordinal_REP b`, `w`] mp_tac) >>
    simp[mkOrdinal_REP] >> strip_tac >> res_tac >> fs[mkOrdinal_REP] >>
    metis_tac [orderiso_TRANS, orderiso_SYM, orderlt_iso_REFL],
    pop_assum mp_tac >> simp[orderlt_def] >> qx_gen_tac `e` >>
    Cases_on `e ∈ elsOf w` >> simp[] >> strip_tac >>
    `orderlt (wobound e w) w`
      by (simp[orderlt_def] >> metis_tac [orderiso_REFL]) >>
    qabbrev_tac `E = wobound e w` >>
    `orderiso E (wobound (mkOrdinal E) allOrds)` by metis_tac[] >>
    `orderiso (wobound (mkOrdinal w) allOrds) (wobound (mkOrdinal E) allOrds)`
      by metis_tac [orderiso_TRANS] >>
    `ordlt (mkOrdinal E) (mkOrdinal w)`
       by (simp[ordlt_mkOrdinal] >>
           map_every qx_gen_tac [`w1`, `w2`] >>
           simp[GSYM orderiso_mkOrdinal] >>
           metis_tac[orderlt_orderiso, orderiso_SYM]) >>
    `~((mkOrdinal E, mkOrdinal w) WIN allOrds)`
       by metis_tac[orderiso_wobound2,orderiso_SYM]>>
    fs[WIN_allOrds]
  ]);

val preds_def = Define`
  preds (w : 'a ordinal) = { w0 | ordlt w0 w }
`;

val IN_preds = store_thm(
  "IN_preds",
  ``x IN preds w <=> ordlt x w``,
  rw[preds_def]);
val _ = export_rewrites ["IN_preds"]

val preds_11 = store_thm(
  "preds_11",
  ``(preds w1 = preds w2) = (w1 = w2)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `ordlt w1 w2 \/ ordlt w2 w1` by metis_tac [ordlt_trichotomy] >>
  qpat_assum `x = y` mp_tac >> rw[EXTENSION, preds_def] >>
  metis_tac [ordlt_REFL]);
val _ = export_rewrites ["preds_11"]

val downward_closed_def = Define`
  downward_closed s <=>
    !a b. a IN s /\ ordlt b a ==> b IN s
`;

val preds_downward_closed = store_thm(
  "preds_downward_closed",
  ``downward_closed (preds w)``,
  rw[downward_closed_def, preds_def] >> metis_tac [ordlt_TRANS]);

val preds_bij = store_thm(
  "preds_bij",
  ``BIJ preds UNIV (downward_closed DELETE UNIV)``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, preds_11] >>
  fs[SPECIFICATION, preds_downward_closed] >>
  rw[EXTENSION] >| [
    metis_tac [IN_preds, ordlt_REFL],
    metis_tac [IN_preds, ordlt_REFL],
    qspec_then `\w. w NOTIN x` mp_tac ordlt_WF0 >> simp[] >>
    qsuff_tac `?w. w NOTIN x`
       >- metis_tac [downward_closed_def, ordlt_trichotomy] >>
    fs[EXTENSION] >> metis_tac[]
  ]);

val preds_lt_PSUBSET = store_thm(
  "preds_lt_PSUBSET",
  ``ordlt w1 w2 <=> preds w1 PSUBSET preds w2``,
  simp[PSUBSET_DEF, SUBSET_DEF, preds_def, EQ_IMP_THM, EXTENSION] >> conj_tac
    >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
  simp_tac (srw_ss() ++ CONJ_ss) [] >>
  metis_tac [ordlt_REFL, ordlt_TRANS, ordlt_trichotomy])

val preds_wobound = store_thm(
  "preds_wobound",
  ``preds ord = elsOf (wobound ord allOrds)``,
  simp[EXTENSION, elsOf_wobound, preds_def, WIN_allOrds]);

val preds_inj_univ = store_thm(
  "preds_inj_univ",
  ``preds (ord:'a ordinal) ≼ univ(:'a inf)``,
  simp[preds_wobound] >>
  qspec_then `ordinal_REP ord` mp_tac wellorder_ordinal_isomorphism >>
  simp[mkOrdinal_REP] >> strip_tac >> imp_res_tac orderiso_SYM >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss())[orderiso_thm]) >>
  simp[cardleq_def] >> qexists_tac `f` >>
  fs[BIJ_DEF, INJ_DEF]);

val _ = type_abbrev("cord", ``:unit ordinal``)

val unitinf_univnum = store_thm(
  "unitinf_univnum",
  ``univ(:unit inf) ≈ univ(:num)``,
  simp[cardeq_def] >>
  qexists_tac `λs. case s of INL n => n + 1 | INR () => 0` >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, EXISTS_SUM, FORALL_SUM] >>
  Cases >> simp[arithmeticTheory.ADD1] >>
  qexists_tac `()` >> simp[])

val cord_countable_preds = store_thm(
  "cord_countable_preds",
  ``countable (preds (ord:cord))``,
  simp[countable_thm] >>
  qsuff_tac `preds ord ≼ univ(:unit inf)`
     >- metis_tac [unitinf_univnum, CARDEQ_CARDLEQ, cardeq_REFL] >>
  simp[preds_inj_univ]);

val univ_ord_greater_cardinal = store_thm(
  "univ_ord_greater_cardinal",
  ``~(univ(:'a ordinal) ≼ univ(:'a inf))``,
  strip_tac >>
  `elsOf allOrds = univ(:'a ordinal)` by simp[elsOf_allOrds] >>
  `elsOf (allOrds:'a ordinal wellorder) ≼ univ(:'a inf)`
      by simp[] >>
  `∃w:'a inf wellorder. orderiso (allOrds:'a ordinal wellorder) w`
    by metis_tac [elsOf_cardeq_iso, cardleq_def] >>
  `orderiso w (wobound (mkOrdinal w) allOrds)`
    by simp[wellorder_ordinal_isomorphism] >>
  `mkOrdinal w ∈ elsOf allOrds` by simp[elsOf_allOrds] >>
  `orderlt (allOrds:'a ordinal wellorder) (allOrds:'a ordinal wellorder)`
     by metis_tac [orderlt_def, orderiso_TRANS] >>
  fs[orderlt_REFL]);

val univ_cord_uncountable = store_thm(
  "univ_cord_uncountable",
  ``~countable (univ(:cord))``,
  simp[countable_thm] >> strip_tac >>
  `univ(:cord) ≼ univ(:unit inf)`
     by metis_tac [CARDEQ_CARDLEQ, cardeq_REFL, unitinf_univnum] >>
  fs[univ_ord_greater_cardinal]);

val ordle_lteq = store_thm(
  "ordle_lteq",
  ``(α:α ordinal) ≤ β <=> α < β ∨ (α = β)``,
  metis_tac [ordlt_trichotomy, ordlt_REFL, ordlt_TRANS])

val ordle_ANTISYM = store_thm(
  "ordle_ANTISYM",
  ``α ≤ β ∧ β ≤ α ⇒ (α = β)``,
  metis_tac [ordlt_trichotomy]);

val ordle_TRANS = store_thm(
  "ordle_TRANS",
  ``∀x y z. (x:'a ordinal) ≤ y ∧ y ≤ z ⇒ x ≤ z``,
  metis_tac [ordlt_TRANS, ordle_lteq]);

val ordlet_TRANS = store_thm(
  "ordlet_TRANS",
  ``∀x y z. (x:'a ordinal) ≤ y ∧ y < z ⇒ x < z``,
  metis_tac [ordle_lteq, ordlt_TRANS]);
val ordlte_TRANS = store_thm(
  "ordlte_TRANS",
  ``∀x y z. (x:'a ordinal) < y ∧ y ≤ z ⇒ x < z``,
  metis_tac [ordle_lteq, ordlt_TRANS]);

val oleast_def = Define`
  $oleast (P:'a ordinal -> bool) = @x. P x ∧ ∀y. y < x ==> ¬P y
`;

val _ = set_fixity "oleast" Binder

val oleast_intro = store_thm(
  "oleast_intro",
  ``∀Q P. (∃α. P α) ∧ (∀α. (∀β. β < α ==> ¬ P β) ∧ P α ==> Q α) ==>
          Q ($oleast P)``,
  rw[oleast_def] >> SELECT_ELIM_TAC >> conj_tac >-
    (match_mp_tac ordlt_WF0 >> metis_tac[]) >>
  rw[]);

val ordSUC_def = Define`
  ordSUC α = oleast β. α < β
`
val _ = overload_on ("TC", ``ordSUC``)

val fromNat_def = Define`
  (fromNat 0 = oleast α. T) ∧
  (fromNat (SUC n) = ordSUC (fromNat n))
`;
val fromNat_SUC = save_thm("fromNat_SUC", fromNat_def |> CONJUNCT2)
val _ = export_rewrites ["fromNat_SUC"]

val _ = add_numeral_form (#"o", SOME "fromNat")

(* prints as 0 ≤ α *)
val ordlt_ZERO = store_thm(
  "ordlt_ZERO",
  ``¬(α < 0)``,
 simp[fromNat_def] >> DEEP_INTRO_TAC oleast_intro >> simp[])
val _ = export_rewrites ["ordlt_ZERO"]

val preds_surj = save_thm(
  "preds_surj",
  preds_bij |> SIMP_RULE (srw_ss()) [BIJ_DEF] |> CONJUNCT2
            |> SIMP_RULE (srw_ss()) [SURJ_DEF] |> CONJUNCT2
            |> REWRITE_RULE [SPECIFICATION]);

val no_maximal_ordinal = store_thm(
  "no_maximal_ordinal",
  ``∀α. ∃β. α < β``,
  simp[preds_lt_PSUBSET] >> gen_tac >>
  qabbrev_tac `P = preds α ∪ {α}` >>
  `α ∉ preds α` by simp[ordlt_REFL] >>
  `P ≠ univ(:'a ordinal)`
     by (strip_tac >>
         qsuff_tac `P ≼ univ(:'a inf)` >-
           metis_tac [univ_ord_greater_cardinal] >>
         pop_assum (K ALL_TAC) >>
         Cases_on `FINITE P` >- simp[FINITE_CLE_INFINITE] >>
         `P = α INSERT preds α` by metis_tac [INSERT_SING_UNION,UNION_COMM] >>
         `INFINITE (preds α)` by fs[] >>
         `P ≈ preds α` by metis_tac [cardeq_INSERT] >>
         metis_tac [CARDEQ_CARDLEQ, cardeq_REFL, preds_inj_univ]) >>
  `downward_closed P` by (simp[Abbr`P`, downward_closed_def] >>
                          metis_tac [ordlt_TRANS]) >>
  `∃β. preds β = P` by metis_tac [preds_surj] >>
  qexists_tac `β` >> simp[Abbr`P`] >>
  simp[PSUBSET_DEF, EXTENSION] >> metis_tac [ordlt_REFL]);

val ordlt_SUC = store_thm(
  "ordlt_SUC",
  ``α < ordSUC α``,
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- metis_tac[no_maximal_ordinal] >> simp[]);
val _ = export_rewrites ["ordlt_SUC"]

val ordSUC_ZERO = store_thm(
  "ordSUC_ZERO",
  ``ordSUC α ≠ 0``,
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- metis_tac [ordlt_SUC] >>
  rpt strip_tac >> fs[]);
val _ = export_rewrites ["ordSUC_ZERO"]

val ordlt_DISCRETE1 = store_thm(
  "ordlt_DISCRETE1",
  ``¬(α < β ∧ β < ordSUC α)``,
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac >-
  metis_tac [ordlt_SUC] >> metis_tac [ordle_lteq]);

val ordlt_SUC_DISCRETE = store_thm(
  "ordlt_SUC_DISCRETE",
  ``α < β⁺ <=> α < β ∨ (α = β)``,
  Tactical.REVERSE eq_tac >- metis_tac [ordlt_TRANS, ordlt_SUC] >>
  metis_tac [ordlt_trichotomy, ordlt_DISCRETE1]);

val ordSUC_MONO = store_thm(
  "ordSUC_MONO",
  ``α⁺ < β⁺ <=> α < β``,
  eq_tac >> spose_not_then strip_assume_tac
  >- (fs[ordlt_SUC_DISCRETE]
      >- (`(α = β) ∨ β < α` by metis_tac [ordlt_trichotomy] >>
          metis_tac [ordlt_TRANS, ordlt_REFL, ordlt_SUC]) >>
      rw[] >> fs[ordlt_SUC]) >>
  fs[ordlt_SUC_DISCRETE] >>
  `β < α⁺` by metis_tac [ordlt_trichotomy] >>
  fs[ordlt_SUC_DISCRETE] >> metis_tac [ordlt_TRANS, ordlt_REFL])
val _ = export_rewrites ["ordSUC_MONO"]

val ordSUC_11 = store_thm(
  "ordSUC_11",
  ``(α⁺ = β⁺) <=> (α = β)``,
  simp[EQ_IMP_THM] >> strip_tac >> spose_not_then assume_tac >>
  `α < β ∨ β < α` by metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_REFL, ordSUC_MONO]);
val _ = export_rewrites ["ordSUC_11"]

val sup_def = Define`
  sup ordset = oleast α. α ∉ BIGUNION (IMAGE preds ordset)
`;

val ord_induction = save_thm(
  "ord_induction",
  ordlt_WF0 |> Q.SPEC `P` |> CONV_RULE CONTRAPOS_CONV
            |> CONV_RULE (BINOP_CONV NOT_EXISTS_CONV)
            |> CONV_RULE (LAND_CONV (REWRITE_CONV [DE_MORGAN_THM] THENC
                                     ONCE_REWRITE_CONV [DISJ_SYM] THENC
                                     REWRITE_CONV [GSYM IMP_DISJ_THM]))
            |> Q.INST [`P` |-> `\x. ~ P x`] |> BETA_RULE
            |> REWRITE_RULE []
            |> CONV_RULE (RAND_CONV (RENAME_VARS_CONV ["α"])))

val sup_thm = store_thm(
  "sup_thm",
  ``(s: 'a ordinal set) ≼ univ(:'a inf) ==> ∀α. α < sup s ⇔ ∃β. β ∈ s ∧ α < β``,
  strip_tac >>
  qabbrev_tac `apreds = BIGUNION (IMAGE preds s)` >>
  `apreds ≼ univ(:'a inf)`
    by (qunabbrev_tac `apreds` >> match_mp_tac CARD_BIGUNION >>
        dsimp[preds_inj_univ] >> metis_tac [cardleq_TRANS, IMAGE_cardleq]) >>
  `apreds ≠ univ(:'a ordinal)` by metis_tac [univ_ord_greater_cardinal] >>
  `downward_closed apreds`
    by (dsimp[Abbr`apreds`, downward_closed_def] >>
        metis_tac[ordlt_TRANS]) >>
  `∃α. preds α = apreds`
    by (mp_tac preds_bij >> simp[BIJ_DEF, SURJ_DEF, SPECIFICATION]) >>
  `sup s = α`
    by (asm_simp_tac bool_ss [sup_def] >>
        DEEP_INTRO_TAC oleast_intro >> conj_tac
        >- (fs[EXTENSION] >> metis_tac[]) >>
        simp[] >> qx_gen_tac `α'` >> strip_tac >>
        qsuff_tac `α' ≤ α ∧ α ≤ α'` >- metis_tac [ordlt_trichotomy] >>
        rpt strip_tac >| [
          `α ∈ apreds` by res_tac >> metis_tac [IN_preds, ordlt_REFL],
          rw[] >> fs[]
        ]) >>
  simp[] >>
  qx_gen_tac `β` >> rpt strip_tac >>
  `β < α ⇔ β ∈ apreds` by metis_tac [IN_preds] >>
  simp[Abbr`apreds`] >> metis_tac [IN_preds]);

val suple_thm = store_thm(
  "suple_thm",
  ``∀β s:'a ordinal set. s ≼ univ(:'a inf) ∧ β ∈ s ⇒ β ≤ sup s``,
  metis_tac [sup_thm, ordlt_REFL]);

val sup_eq_sup = store_thm(
  "sup_eq_sup",
  ``(s1:α ordinal set) ≼ univ(:α inf) ∧
    (s2:α ordinal set) ≼ univ(:α inf) ∧
    (∀a. a ∈ s1 ⇒ ∃b. b ∈ s2 ∧ a ≤ b) ∧
    (∀b. b ∈ s2 ⇒ ∃a. a ∈ s1 ∧ b ≤ a) ⇒ (sup s1 = sup s2)``,
  strip_tac >> match_mp_tac ordle_ANTISYM >> simp[sup_thm] >>
  metis_tac [suple_thm, ordle_TRANS]);

val Unum_cle_Uinf = store_thm(
  "Unum_cle_Uinf",
  ``𝕌(:num) ≼ 𝕌(:'a inf)``,
  simp[cardleq_def] >> qexists_tac `INL` >> simp[INJ_INL]);

val csup_thm = store_thm(
  "csup_thm",
  ``countable (s : 'a ordinal set) ⇒ ∀β. β < sup s ⇔ ∃δ. δ ∈ s ∧ β < δ``,
  simp[countable_thm] >>
  metis_tac [sup_thm, cardleq_def, Unum_cle_Uinf, cardleq_TRANS])

val predimage_sup_thm = store_thm(
  "predimage_sup_thm",
  ``∀β:'a ordinal.
          β < sup (IMAGE f (preds (α:'a ordinal))) <=> ∃δ. δ < α ∧ β < f δ``,
  match_mp_tac (sup_thm |> Q.INST [`s` |-> `IMAGE f (preds (α:'b ordinal))`]
                        |> SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  metis_tac [cardleq_TRANS, IMAGE_cardleq, preds_inj_univ]);

val impI = DECIDE ``¬p ∨ q <=> (p ==> q)``

val predimage_suplt_ELIM = save_thm(
  "predimage_suplt_ELIM",
  predimage_sup_thm |> SPEC_ALL |> Q.AP_TERM `$~`
                    |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [impI]))
                    |> EQ_IMP_RULE |> #1
                    |> SIMP_RULE bool_ss [SimpL ``$==>``, ordle_lteq]
                    |> SIMP_RULE bool_ss [DISJ_IMP_THM]
                    |> CONJUNCT1)
val suppred_suplt_ELIM = save_thm(
  "suppred_suplt_ELIM",
  predimage_suplt_ELIM |> Q.INST [`f` |-> `λx.x`]
                       |> SIMP_RULE (srw_ss()) []);

val sup_EMPTY = store_thm(
  "sup_EMPTY",
  ``sup {} = 0``,
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  qx_gen_tac `α` >> disch_then (qspec_then `0` mp_tac) >>
  simp[ordle_lteq]);
val _ = export_rewrites ["sup_EMPTY"]

val sup_SING = store_thm(
  "sup_SING",
  ``sup {α} = α``,
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac >-
    (qexists_tac `α` >> simp[]) >>
  simp[] >> qx_gen_tac `β` >> rw[ordle_lteq] >>
  metis_tac [ordlt_REFL]);
val _ = export_rewrites ["sup_SING"]

val sup_preds_SUC = store_thm(
  "sup_preds_SUC",
  ``sup (preds α⁺) = α``,
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac >-
    (qsuff_tac `∃β. ∀x. β ∈ preds x ==> α⁺ ≤ x ` >- metis_tac[] >>
     simp[] >> qexists_tac `α⁺` >> simp[ordle_lteq]) >>
  qx_gen_tac `β` >> simp_tac (srw_ss() ++ DNF_ss) [] >>
  strip_tac >>
  `∀δ. β < δ ==> α⁺ ≤ δ` by metis_tac [IN_preds] >>
  qsuff_tac `β ≤ α ∧ α ≤ β` >- metis_tac [ordlt_trichotomy] >>
  rpt strip_tac
  >- (`∃x. α < x ∧ x < α⁺` by metis_tac [] >>
      fs[ordlt_SUC_DISCRETE] >> metis_tac [ordlt_REFL, ordlt_TRANS]) >>
  res_tac >> fs[ordlt_SUC]);

val _ = overload_on ("countableOrd", ``\a. countable(preds a)``)

val preds_ordSUC = store_thm(
  "preds_ordSUC",
  ``preds a⁺ = a INSERT preds a``,
  simp[EXTENSION, ordlt_SUC_DISCRETE] >> metis_tac[]);

val countableOrds_dclosed = store_thm(
  "countableOrds_dclosed",
  ``α < β ∧ countableOrd β ⇒ countableOrd α``,
  strip_tac >>
  `preds α ⊆ preds β` by metis_tac [preds_lt_PSUBSET, PSUBSET_DEF] >>
  metis_tac[subset_countable]);

val omax_def = Define`
  omax (s : 'a ordinal set) =
    some α. maximal_elements s { (x,y) | x <= y } = {α}
`;

val omax_SOME = store_thm(
  "omax_SOME",
  ``(omax s = SOME α) <=> α ∈ s ∧ !β. β ∈ s ⇒ β ≤ α``,
  simp[omax_def] >> DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
  conj_tac
  >- (qx_gen_tac `β` >> simp[maximal_elements_def, EXTENSION] >>
      strip_tac >> eq_tac
      >- (strip_tac >> simp[] >> conj_tac >- metis_tac[] >>
          qx_gen_tac `γ` >> rpt strip_tac >>
          metis_tac [ordlt_REFL, ordle_lteq]) >>
      metis_tac[]) >>
  simp[EXTENSION, maximal_elements_def] >> strip_tac >> Cases_on `α ∈ s` >>
  simp[] >> first_assum (qspec_then `α` mp_tac) >>
  disch_then (Q.X_CHOOSE_THEN `β` strip_assume_tac) >>
  Cases_on `β = α`
  >- (qpat_assum `P ∧ Q <=/=> R` mp_tac >> simp[] >> metis_tac [ordle_lteq]) >>
  fs[] >> metis_tac []);

val omax_NONE = store_thm(
  "omax_NONE",
  ``(omax s = NONE) <=> ∀α. α ∈ s ⇒ ∃β. β ∈ s ∧ α < β``,
  simp[omax_def] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  simp[maximal_elements_def, EXTENSION] >>
  metis_tac [ordle_lteq]);

val omax_EMPTY = store_thm(
  "omax_EMPTY",
  ``omax {} = NONE``,
  simp[omax_NONE]);
val _ = export_rewrites ["omax_EMPTY"]

val preds_0 = store_thm(
  "preds_0",
  ``preds 0 = {}``,
  simp[preds_def]);
val _ = export_rewrites ["preds_0"]

val ordleq0 = store_thm(
  "ordleq0",
  ``(x:'a ordinal) ≤ 0 ⇔ (x = 0)``,
  eq_tac >> simp[ordle_lteq]);
val _ = export_rewrites ["ordleq0"]

val preds_EQ_EMPTY = store_thm(
  "preds_EQ_EMPTY",
  ``preds x = ∅ ⇔ x = 0``,
  simp[EQ_IMP_THM] >> simp[EXTENSION] >>
  disch_then (qspec_then `0` mp_tac) >> simp[]);
val _ = export_rewrites ["preds_EQ_EMPTY"]

val omax_sup = store_thm(
  "omax_sup",
  ``(omax s = SOME α) ==> (sup s = α)``,
  simp[omax_SOME, sup_def] >> strip_tac >>
  DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac
  >- (qsuff_tac `∃β. ∀γ. β ∈ preds γ ==> γ ∉ s` >- metis_tac[] >>
      simp[] >> metis_tac[]) >>
  dsimp [] >> qx_gen_tac `β` >> strip_tac >>
  `∀γ. β ∈ preds γ ⇒ γ ∉ s` by metis_tac[] >>
  fs [] >> qsuff_tac `α ≤ β ∧ β ≤ α` >- metis_tac [ordlt_trichotomy] >>
  metis_tac[]);

val preds_omax_SOME_SUC = store_thm(
  "preds_omax_SOME_SUC",
  ``(omax (preds α) = SOME β) <=> (α = β⁺)``,
  simp[omax_SOME] >> eq_tac >> strip_tac
  >- (qsuff_tac `α ≤ β⁺ ∧ β⁺ ≤ α` >- metis_tac [ordlt_trichotomy] >>
      rpt strip_tac >- metis_tac [ordlt_SUC] >>
      metis_tac [ordlt_SUC_DISCRETE, ordlt_TRANS, ordlt_REFL]) >>
  simp[ordlt_SUC_DISCRETE, ordle_lteq]);

val omax_preds_SUC = store_thm(
  "omax_preds_SUC",
  ``omax (preds α⁺) = SOME α``,
  metis_tac [preds_omax_SOME_SUC]);
val _ = export_rewrites ["omax_preds_SUC"]

val simple_ord_induction = store_thm(
  "simple_ord_induction",
  ``∀P. P 0 ∧ (∀α. P α ⇒ P α⁺) ∧
        (∀α. (omax (preds α) = NONE) ∧ 0 < α ∧ (∀β. β < α ⇒ P β) ⇒ P α) ⇒
        ∀α. P α``,
  gen_tac >> strip_tac >>
  ho_match_mp_tac ord_induction >> qx_gen_tac `a` >>
  Cases_on `a = 0` >> simp[] >>
  `(omax (preds a) = NONE) ∨ ∃a0. omax (preds a) = SOME a0`
    by metis_tac [optionTheory.option_CASES]
  >- (`0 < a` by metis_tac [ordlt_ZERO, ordle_lteq] >> metis_tac[]) >>
  fs[preds_omax_SOME_SUC]);

val _ = overload_on ("islimit", ``λa:α ordinal. omax (preds a) = NONE``)

val sup_preds_omax_NONE = store_thm(
  "sup_preds_omax_NONE",
  ``(omax (preds α) = NONE) ⇔ (sup (preds α) = α)``,
  simp[omax_NONE, sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  simp_tac(srw_ss() ++ DNF_ss) [impI] >>
  qexists_tac `α` >> conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `γ` >> strip_tac >> Tactical.REVERSE eq_tac
  >- (rw[] >> metis_tac[]) >>
  strip_tac >> qsuff_tac `γ ≤ α ∧ α ≤ γ` >- metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_TRANS, ordlt_REFL]);

val dclose_def = Define`dclose s = { x:'a ordinal | ∃y. y ∈ s ∧ x < y }`;

val preds_sup = store_thm(
  "preds_sup",
  ``s ≼ univ(:'a inf) ⇒ (preds (sup s:'a ordinal) = dclose s)``,
  simp[EXTENSION, sup_thm, dclose_def]);

fun mklesup th =
    th |> UNDISCH_ALL |> Q.SPEC `sup s`
       |> SIMP_RULE (srw_ss()) [] |> REWRITE_RULE [impI] |> DISCH_ALL
(* |- countable s ⇒ ∀δ. δ ∈ s ⇒ δ ≤ sup s *)
val csup_lesup = save_thm("csup_lesup", mklesup csup_thm)

fun mksuple th =
    th |> UNDISCH_ALL |> Q.SPEC `β` |> AP_TERM ``$~``
       |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
       |> REWRITE_RULE [impI]
       |> DISCH_ALL

val csup_suple = save_thm("csup_suple", mksuple csup_thm)

val preds_sup_thm = store_thm(
  "preds_sup_thm",
  ``downward_closed s ∧ s ≠ univ(:α ordinal) ⇒
    ∀β. β < sup s <=> ∃δ. δ ∈ s ∧ β < δ``,
  strip_tac >>
  qspec_then `s` mp_tac preds_surj >> simp[] >>
  disch_then (Q.X_CHOOSE_THEN `α` ASSUME_TAC) >>
  `(omax s = NONE) ∨ ∃β. omax s = SOME β` by (Cases_on `omax s` >> simp[])
  >- (`sup s = α`
        by (simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >>
            dsimp[impI] >> qexists_tac `α` >> conj_tac >- rw[ordle_lteq] >>
            qx_gen_tac `β` >> rw[] >>
            qsuff_tac `β ≤ α ∧ α ≤ β` >- metis_tac [ordlt_trichotomy] >>
            rpt strip_tac >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
            fs[omax_NONE] >> metis_tac[]) >>
      pop_assum SUBST1_TAC >> rw[] >> fs[omax_NONE] >>
      metis_tac[ordlt_TRANS]) >>
  `α = β⁺` by (rw[] >> fs[preds_omax_SOME_SUC]) >> qx_gen_tac `δ` >> rw[] >>
  simp[sup_preds_SUC] >> eq_tac >- (strip_tac >> qexists_tac `β` >> simp[]) >>
  simp[ordlt_SUC_DISCRETE] >>
  disch_then (Q.X_CHOOSE_THEN `γ` strip_assume_tac) >- metis_tac[ordlt_TRANS] >>
  rw[]);

val preds_lesup = save_thm("preds_lesup", mklesup preds_sup_thm)
val preds_suple = save_thm("preds_suple", mksuple preds_sup_thm)

val fromNat_11 = store_thm(
  "fromNat_11",
  ``∀x y. (&x:α ordinal = &y) = (x = y)``,
  Induct >- (Cases >> simp[]) >> Cases >> simp[])
val _ = export_rewrites ["fromNat_11"]

val ordlt_fromNat = store_thm(
  "ordlt_fromNat",
  ``∀n (x:α ordinal). x < &n <=> ∃m. (x = &m) ∧ m < n``,
  Induct >>
  dsimp [ordlt_SUC_DISCRETE, DECIDE ``m < SUC n <=> m < n ∨ (m = n)``]);

val fromNat_ordlt = store_thm(
  "fromNat_ordlt",
  ``(&n:'a ordinal < &m) ⇔ (n < m)``,
  simp[ordlt_fromNat]);
val _ = export_rewrites ["fromNat_ordlt"]

val allNats_dwardclosedetc = prove(
  ``downward_closed { fromNat i : α ordinal | T } ∧
    { fromNat i | T } ≠ univ(:α ordinal)``,
  simp[downward_closed_def] >> conj_tac
  >- (map_every qx_gen_tac [`a`, `b`] >>
      disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `i` assume_tac)
                                  assume_tac) >>
      rw[] >> fs[ordlt_fromNat]) >>
  qsuff_tac `{&i : 'a ordinal | T} ≼ univ(:α inf)`
  >- metis_tac [univ_ord_greater_cardinal] >>
  simp[cardleq_def] >> qexists_tac `λα. INL (@n. &n = α)` >>
  simp[INJ_DEF] >> rw[] >> fs[]);

val omega_def = Define`
  omega = sup { fromNat i | T }
`;
val _ = overload_on ("ω", ``omega``)

val lt_omega0 =
  MATCH_MP preds_sup_thm allNats_dwardclosedetc
           |> SIMP_RULE (srw_ss() ++ DNF_ss) [SYM omega_def, ordlt_fromNat]

val lt_omega = store_thm(
  "lt_omega",
  ``∀α. α < ω <=> ∃m. α = &m``,
  simp_tac (srw_ss() ++ DNF_ss) [lt_omega0, EQ_IMP_THM] >> qx_gen_tac `n` >>
  qexists_tac `SUC n` >> simp[]);

val fromNat_lt_omega = store_thm(
  "fromNat_lt_omega",
  ``∀n. &n < ω``,
  simp[lt_omega]);
val _ = export_rewrites ["fromNat_lt_omega"]

val fromNat_eq_omega = store_thm(
  "fromNat_eq_omega",
  ``∀n. &n ≠ ω``,
  metis_tac [ordlt_REFL, fromNat_lt_omega]);
val _ = export_rewrites ["fromNat_eq_omega"]

(* recursion principles *)
val restrict_away = prove(
  ``IMAGE (RESTRICT f $< (α:α ordinal)) (preds α) = IMAGE f (preds α)``,
  rw[EXTENSION, relationTheory.RESTRICT_DEF] >> srw_tac[CONJ_ss][]);

val ord_RECURSION = store_thm(
  "ord_RECURSION",
  ``!(z:'b) (sf:'a ordinal -> 'b -> 'b) (lf:'a ordinal -> 'b set -> 'b).
       ?h : 'a ordinal -> 'b.
         (h 0 = z) ∧
         (∀α. h α⁺ = sf α (h α)) ∧
         !α. 0 < α ∧ islimit α ==>
             (h α = lf α (IMAGE h (preds α)))``,
  rpt gen_tac >>
  qexists_tac `WFREC $< (λg x. if x = 0 then z
                               else
                                 case omax (preds x) of
                                   NONE => lf x (IMAGE g (preds x))
                                 | SOME x0 => sf x0 (g x0)) ` >>
  rpt conj_tac
  >- simp[relationTheory.WFREC_THM, ordlt_WF]
  >- simp[Once relationTheory.WFREC_THM, relationTheory.RESTRICT_DEF, SimpLHS,
          ordlt_WF] >>
  simp[relationTheory.WFREC_THM, ordlt_WF, restrict_away] >> qx_gen_tac `a` >>
  strip_tac >> `a ≠ 0` by metis_tac [ordlt_REFL] >> simp[])

val ordADD_def = new_specification(
  "ordADD_def", ["ordADD"],
  ord_RECURSION |> Q.ISPEC `β:'a ordinal` |> Q.SPEC `λ(x:'a ordinal) r. r⁺`
                |> Q.SPEC `λx rs. sup rs`
                |> SIMP_RULE (srw_ss()) []
                |> Q.GEN `β`
                |> CONV_RULE SKOLEM_CONV)
val _ = export_rewrites ["ordADD_def"]
val _ = overload_on ("+", ``ordADD``)

val ordADD_0L = store_thm(
  "ordADD_0L",
  ``∀α:α ordinal. 0 + α = α``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >>
  `IMAGE ($+ 0) (preds a) = preds a`
    by (rpt (asm_simp_tac (srw_ss() ++ CONJ_ss)[EXTENSION])) >>
  fs[sup_preds_omax_NONE]);
val _ = export_rewrites ["ordADD_0L"]

val ubsup_thm = store_thm(
  "ubsup_thm",
  ``(∀α. α ∈ s ⇒ α < β) ==> ∀γ. γ < sup s ⇔ ∃δ. δ ∈ s ∧ γ < δ``,
  strip_tac >> simp[sup_def] >> gen_tac >> DEEP_INTRO_TAC oleast_intro >>
  dsimp[impI] >>
  qexists_tac `β` >> conj_tac >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
  qx_gen_tac `α` >> strip_tac >> eq_tac >- metis_tac[] >>
  disch_then (Q.X_CHOOSE_THEN `δ` strip_assume_tac) >>
  `δ ≤ α`by metis_tac[] >> fs[ordle_lteq] >> rw[] >> metis_tac [ordlt_TRANS]);

val ordADD_fromNat = store_thm(
  "ordADD_fromNat",
  ``ordADD (&n) (&m) = &(n + m)``,
  Induct_on `m` >> simp[arithmeticTheory.ADD_CLAUSES]);
val _ = export_rewrites ["ordADD_fromNat"]

val omax_preds_omega = store_thm(
  "omax_preds_omega",
  ``omax (preds ω) = NONE``,
  simp_tac (srw_ss() ++ DNF_ss) [omax_NONE, lt_omega] >> qx_gen_tac `m` >>
  qexists_tac `SUC m` >> simp[]);
val omega_islimit = save_thm("omega_islimit", omax_preds_omega)

val ordADD_fromNat_omega = store_thm(
  "ordADD_fromNat_omega",
  ``&n + ω = ω``,
  simp[ordADD_def,omax_preds_omega] >>
  `∀α. α ∈ IMAGE ($+ (&n)) (preds ω) ==> α < ω` by dsimp[lt_omega] >>
  pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
  match_mp_tac ordle_ANTISYM >> simp[] >> conj_tac
  >- (qx_gen_tac `δ` >> Cases_on `δ ≤ ω` >> simp[] >> fs[] >>
      simp[lt_omega] >> qx_gen_tac `x` >>
      Cases_on `∃m. x = &m` >> fs[] >> strip_tac >>
      metis_tac [fromNat_lt_omega, ordlt_TRANS, ordlt_REFL]) >>
  simp[lt_omega] >> qx_gen_tac `m` >> strip_tac >>
  full_simp_tac (srw_ss() ++ DNF_ss) [lt_omega, impI] >>
  first_x_assum (qspec_then `&m` mp_tac) >> simp[] >>
  qexists_tac `m+1` >> decide_tac);

val lt_suppreds = save_thm(
  "lt_suppreds",
  predimage_sup_thm |> Q.INST [`f` |-> `λx. x`] |> SIMP_RULE (srw_ss()) [])

val omax_preds_SUC = store_thm(
  "omax_preds_SUC",
  ``omax (preds x⁺) = SOME x``,
  simp[preds_omax_SOME_SUC]);

val ORD_ONE = store_thm(
  "ORD_ONE",
  ``0⁺ = 1``,
  simp_tac bool_ss [GSYM fromNat_SUC] >> simp[]);
val _ = export_rewrites ["ORD_ONE"]

val ordSUC_NUMERAL = store_thm(
  "ordSUC_NUMERAL",
  ``(&NUMERAL n)⁺ = &(NUMERAL n + 1)``,
  simp[GSYM arithmeticTheory.ADD1]);
val _ = export_rewrites ["ordSUC_NUMERAL"]

val ordZERO_ltSUC = store_thm(
  "ordZERO_ltSUC",
  ``0 < x⁺``,
  metis_tac [ordSUC_ZERO, ordlt_ZERO, ordlt_trichotomy]);
val _ = export_rewrites ["ordZERO_ltSUC"]

val ordlt_CANCEL_ADDR = store_thm(
  "ordlt_CANCEL_ADDR",
  ``∀(b:'a ordinal) a. a < a + b <=> 0 < b``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `b` >> strip_tac >> qx_gen_tac `a` >>
      Cases_on `b = 0` >- simp[] >>
      match_mp_tac ordlt_TRANS >> qexists_tac `a⁺` >> simp[] >>
      spose_not_then strip_assume_tac >> fs[ordle_lteq]) >>
  simp_tac (srw_ss() ++ CONJ_ss)[predimage_sup_thm] >> rpt strip_tac >>
  simp[GSYM lt_suppreds] >> fs[sup_preds_omax_NONE]);
val _ = export_rewrites ["ordlt_CANCEL_ADDR"]

val ordlt_CANCEL_ADDL = store_thm(
  "ordlt_CANCEL_ADDL",
  ``a + b < a <=> F``,
  simp[ordle_lteq] >> Cases_on `0 < b` >> simp[] >>
  fs[ordleq0]);
val _ = export_rewrites ["ordlt_CANCEL_ADDL"]

val ordADD_CANCEL_LEMMA0 = prove(
  ``α = α + γ ⇔ γ = 0``,
  Cases_on `γ = 0` >> simp[] >>
  qsuff_tac `α < α + γ` >- metis_tac[ordlt_REFL] >> simp[] >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq])
val ordADD_CANCEL1 = save_thm(
  "ordADD_CANCEL1",
  CONJ (GEN_ALL ordADD_CANCEL_LEMMA0)
       (ordADD_CANCEL_LEMMA0 |> CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))
                             |> GEN_ALL))
val _ = export_rewrites ["ordADD_CANCEL1"]

val ordADD_MONO = store_thm(
  "ordADD_MONO",
  ``∀b:'a ordinal a c. a < b ⇒ c + a < c + b``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (ntac 2 strip_tac >> simp[ordlt_SUC_DISCRETE] >> rw[] >> rw[]) >>
  qx_gen_tac `b` >> strip_tac >> simp[predimage_sup_thm] >>
  map_every qx_gen_tac [`a`, `c`] >> strip_tac >>
  `∃d. d < b ∧ a < d`
    by (simp[GSYM lt_suppreds] >> fs[sup_preds_omax_NONE]) >>
  metis_tac[]);

val ordlt_CANCEL = store_thm(
  "ordlt_CANCEL",
  ``∀b a (c:'a ordinal). c + a < c + b <=> a < b``,
  simp[EQ_IMP_THM, ordADD_MONO] >> rpt strip_tac >>
  metis_tac[ordlt_trichotomy, ordlt_REFL, ordlt_TRANS, ordADD_MONO]);
val _ = export_rewrites ["ordlt_CANCEL"]

val ordADD_RIGHT_CANCEL = store_thm(
  "ordADD_RIGHT_CANCEL",
  ``∀β α γ. ((α:α ordinal) + β = α + γ) ⇔ (β = γ)``,
  metis_tac[ordlt_trichotomy, ordADD_MONO, ordlt_REFL]);
val _ = export_rewrites ["ordADD_RIGHT_CANCEL"]

val leqLEFT_CANCEL = store_thm(
  "leqLEFT_CANCEL",
  ``∀x a. x ≤ a + x``,
  ho_match_mp_tac simple_ord_induction >> rpt conj_tac >- simp[] >- simp[] >>
  qx_gen_tac `x` >> strip_tac >>
  qx_gen_tac `a` >> strip_tac >>
  `∃b. a + x < b ∧ b < x` by metis_tac[omax_NONE, IN_preds] >>
  `b ≤ a + b` by metis_tac[] >>
  `a + x < a + b` by metis_tac [ordle_lteq, ordlt_TRANS] >>
  fs[] >> metis_tac[ordlt_TRANS, ordlt_REFL]);
val _ = export_rewrites ["leqLEFT_CANCEL"]

val lemma = prove(
  ``∀c a b:'a ordinal. a < b ∧ b < a + c ⇒ ∃d. a + d = b``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> rpt conj_tac
  >- metis_tac [ordlt_TRANS, ordlt_REFL]
  >- (simp[ordlt_SUC_DISCRETE] >> metis_tac[]) >>
  simp[predimage_sup_thm]);

val ordlt_EXISTS_ADD = store_thm(
  "ordlt_EXISTS_ADD",
  ``∀a b:'a ordinal. a < b ⇔ ∃c. c ≠ 0 ∧ b = a + c``,
  simp_tac (srw_ss() ++ DNF_ss) [EQ_IMP_THM] >> Tactical.REVERSE conj_tac
  >- metis_tac[ordlt_trichotomy, ordlt_ZERO] >>
  map_every qx_gen_tac [`a`, `b`] >> strip_tac >>
  `b ≤ a + b` by simp[] >> fs[ordle_lteq]
  >- (`∃c. a + c = b` by metis_tac[lemma] >> rw[] >> strip_tac >> fs[]) >>
  qexists_tac `b` >> simp[] >> strip_tac >> fs[]);

val ordle_EXISTS_ADD = store_thm(
  "ordle_EXISTS_ADD",
  ``∀a b:'a ordinal. a ≤ b ⇔ ∃c. b = a + c``,
  simp[ordle_lteq] >> metis_tac [ordlt_EXISTS_ADD, ordADD_def]);

val ordle_CANCEL_ADDR = store_thm(
  "ordle_CANCEL_ADDR",
  ``x ≤ x + a``,
  simp[ordle_lteq] >> metis_tac[ordlt_trichotomy, ordlt_ZERO]);
val _ = export_rewrites ["ordle_CANCEL_ADDR"]

val dclose_BIGUNION = store_thm(
  "dclose_BIGUNION",
  ``dclose s = BIGUNION (IMAGE preds s)``,
  dsimp[Once EXTENSION, dclose_def] >> metis_tac[]);

val countableOrds_uncountable = store_thm(
  "countableOrds_uncountable",
  ``¬countable { a:'a ordinal | countableOrd a }``,
  strip_tac >> qabbrev_tac `CO = { a | countableOrd a }` >>
  `CO ≼ 𝕌(:'a inf)`
     by metis_tac[countable_thm, cardleq_TRANS, Unum_cle_Uinf] >>
  `∀β. β < sup CO ⇔ ∃δ. δ ∈ CO ∧ β < δ` by metis_tac [sup_thm] >>
  `countableOrd (sup CO)`
    by (`preds (sup CO) = dclose CO` by simp[preds_sup] >>
        simp[countable_thm, dclose_BIGUNION] >>
        match_mp_tac CARD_BIGUNION >>
        asm_simp_tac (srw_ss() ++ DNF_ss) [] >> conj_tac
        >- (match_mp_tac IMAGE_cardleq_rwt >> fs[countable_thm]) >>
        simp[Abbr`CO`, countable_thm]) >>
  `countable (preds (sup CO)⁺)` by simp[preds_ordSUC] >>
  `(sup CO)⁺ ∈ CO` by simp[Abbr`CO`] >>
  `sup CO < (sup CO)⁺` by simp[] >>
  metis_tac [ordlt_REFL]);

val dclose_cardleq_univinf = store_thm(
  "dclose_cardleq_univinf",
  ``(s:'a ordinal set) ≼ univ(:'a inf) ==> dclose s ≼ univ(:'a inf)``,
  strip_tac >> simp[dclose_BIGUNION] >>
  match_mp_tac CARD_BIGUNION >>
  dsimp[preds_inj_univ] >> metis_tac [cardleq_TRANS, IMAGE_cardleq]);

val sup_lt_implies = store_thm(
  "sup_lt_implies",
  ``(s:'a ordinal set) ≼ univ(:'a inf) ∧ sup s < a ∧ b ∈ s ⇒ b < a``,
  strip_tac >>
  `sup s ≤ a` by simp[ordle_lteq] >>
  pop_assum mp_tac >> simp[sup_thm, impI] >> strip_tac >>
  `b ≤ a` by simp[] >> fs[ordle_lteq] >> fs[] >>
  `a ≤ sup s` by metis_tac [mklesup sup_thm]);

val sup_eq_max = store_thm(
  "sup_eq_max",
  ``(∀b. b ∈ s ⇒ b ≤ a) ∧ a ∈ s ⇒ sup s = a``,
  strip_tac >>
  `∀b. b ∈ s ⇒ b < a⁺` by fs[ordlt_SUC_DISCRETE, ordle_lteq] >>
  pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
  `a ≤ sup s` by metis_tac [ordlt_REFL] >>
  `sup s ≤ a` by simp[impI] >>
  metis_tac [ordle_ANTISYM]);

val sup_eq_SUC = store_thm(
  "sup_eq_SUC",
  ``s:'a ordinal set ≼ univ(:'a inf) ∧ sup s = a⁺ ⇒ a⁺ ∈ s``,
  rpt strip_tac >> `a < sup s` by simp[] >>
  pop_assum mp_tac >> pop_assum (mp_tac o SYM) >> simp[sup_thm] >> strip_tac >>
  disch_then (Q.X_CHOOSE_THEN `b` strip_assume_tac) >>
  qsuff_tac `b = a⁺` >- metis_tac[] >>
  match_mp_tac ordle_ANTISYM >> conj_tac
  >- metis_tac [sup_lt_implies, ordlt_REFL] >>
  simp[ordlt_SUC_DISCRETE] >> metis_tac[ordle_lteq, ordlt_REFL]);


val generic_continuity = store_thm(
  "generic_continuity",
  ``(∀a. 0 < a ∧ islimit a ⇒ f a :'a ordinal = sup (IMAGE f (preds a))) ∧
    (∀x y. x ≤ y ⇒ f x ≤ f y) ⇒
    ∀s:'a ordinal set.
          s ≼ univ(:'a inf) ∧ s ≠ ∅ ⇒ f (sup s) = sup (IMAGE f s)``,
  rpt strip_tac >>
  `islimit (sup s) ∨ ∃a. omax (preds (sup s)) = SOME a`
    by metis_tac [optionTheory.option_CASES]
  >| [
    Cases_on `sup s = 0` >> simp[]
    >- (pop_assum (mp_tac o Q.AP_TERM `preds`) >>
        asm_simp_tac bool_ss [preds_sup] >> simp[dclose_def, EXTENSION] >>
        fs[omax_NONE] >>
        disch_then (qspec_then `0` mp_tac) >>
        disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
        `s = {0}` by (fs[EXTENSION] >> metis_tac[]) >> simp[]) >>
    match_mp_tac ordle_ANTISYM >> Tactical.REVERSE conj_tac
    >- (dsimp[sup_thm, IMAGE_cardleq_rwt, impI, dclose_cardleq_univinf] >>
        ntac 2 strip_tac >> first_x_assum match_mp_tac >>
        simp[mklesup sup_thm]) >>
    `0 < sup s` by metis_tac [ordlt_trichotomy, ordlt_ZERO] >>
    simp[preds_sup] >>
    qpat_assum `islimit (sup s)` mp_tac >> simp[preds_sup] >> strip_tac >>
    dsimp[sup_thm, IMAGE_cardleq_rwt, impI, dclose_cardleq_univinf,
          dclose_def] >>
    ntac 4 strip_tac >>
    match_mp_tac ordle_TRANS >> qexists_tac `f y` >> conj_tac
    >- metis_tac [ordle_lteq] >>
    match_mp_tac
      (SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] (mklesup sup_thm)) >>
    simp[IMAGE_cardleq_rwt] >> metis_tac[],

    `sup (preds (sup s)) = a` by metis_tac[omax_sup] >>
    fs[preds_omax_SOME_SUC] >>
    `a⁺ ∈ s` by metis_tac [sup_eq_SUC] >>
    ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
    match_mp_tac sup_eq_max >> dsimp[] >>
    ntac 2 strip_tac >> first_x_assum match_mp_tac >>
    metis_tac [mklesup sup_thm]
  ])

val ord_CASES = store_thm(
  "ord_CASES",
  ``∀a. (a = 0) ∨ (∃a0. a = a0⁺) ∨ (0 < a ∧ islimit a)``,
  gen_tac >> Cases_on `a = 0` >- simp[] >>
  `0 < a` by metis_tac [ordlt_trichotomy, ordlt_ZERO] >>
  Cases_on `omax (preds a)` >> simp[] >>
  fs[preds_omax_SOME_SUC]);

val islimit_0 = store_thm("islimit_0", ``islimit 0``, simp[])

(* An intermediate value theorem of sorts.

   Thanks to Martin Ward for the theorem and some related discussion.
   For the moment, we don't have a proof without the weakly increasing
   side condition, which is annoying.
*)

val ordinal_IVT = store_thm(
  "ordinal_IVT",
  ``(∀a:α ordinal.
       0 < a ∧ islimit a ⇒ f a : α ordinal = sup (IMAGE f (preds a))) ∧
    (∀x y. x ≤ y ⇒ f x ≤ f y) ∧ α₁ < α₂ ∧ f α₁ ≤ γ ∧ γ < f α₂ ⇒
    ∃β. α₁ ≤ β ∧ β < α₂ ∧ f β ≤ γ ∧ γ < f β⁺``,
  strip_tac >>
  qabbrev_tac `μ = oleast a. γ < f a ∧ α₁ < a` >>
  `γ < f μ ∧ α₁ < μ ∧ (∀α. α < μ ⇒ f α ≤ γ ∨ α ≤ α₁)`
    by (simp[Abbr`μ`] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
        >- (qexists_tac `α₂` >> simp[ordle_lteq]) >> simp[]) >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  `¬islimit μ`
    by (strip_tac >> `sup (preds μ)= μ` by fs[sup_preds_omax_NONE] >>
        `0 < μ` by (spose_not_then assume_tac >> fs[]) >>
        `f μ = sup (IMAGE f (preds μ))` by metis_tac[] >>
        `∃δ. δ < μ ∧ γ < f δ` by metis_tac[predimage_sup_thm] >>
        `δ ≤ α₁` by metis_tac[] >>
        `f δ ≤ f α₁` by metis_tac[] >>
        metis_tac [ordlte_TRANS, ordle_TRANS]) >>
  `∃δ. μ = δ⁺` by metis_tac[ord_CASES, islimit_0] >>
  `δ < μ` by simp[] >>
  qexists_tac `δ` >>
  `α₁ ≤ δ` by metis_tac[ordlt_SUC_DISCRETE, ordle_lteq] >>
  `f δ ≤ γ` by metis_tac[ordle_ANTISYM] >>
  `δ < α₂` suffices_by metis_tac[] >>
  metis_tac[ordle_TRANS, ordle_TRANS]);

val ordADD_continuous = save_thm(
  "ordADD_continuous",
  generic_continuity |> Q.INST [`f` |-> `$+ a`] |> SIMP_RULE (srw_ss()) [])

val ordADD_ASSOC = store_thm(
  "ordADD_ASSOC",
  ``∀a b c:'a ordinal. a + (b + c) = (a + b) + c``,
  qsuff_tac `∀c a b:'a ordinal. a + (b + c) = (a + b) + c` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[predimage_sup_thm] >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  `IMAGE ($+ (a + b)) (preds c) = IMAGE ($+ a) (IMAGE ($+ b) (preds c))`
    by (dsimp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) []) >>
  simp[] >>
  match_mp_tac ordADD_continuous >>
  simp[IMAGE_cardleq_rwt, preds_inj_univ] >>
  metis_tac [preds_0, preds_11, ordlt_REFL]);

val exists_C = prove(
  ``(∃h:'a -> 'a -> 'a. P h) <=> (∃h. P (combin$C h))``,
  eq_tac >> strip_tac
  >- (qexists_tac `combin$C h` >>
      qsuff_tac `combin$C (combin$C h) = h` >- simp[] >>
      simp[FUN_EQ_THM]) >> metis_tac[]);

val ADD1R = store_thm(
  "ADD1R",
  ``a + 1 = a⁺``,
  REWRITE_TAC [GSYM ORD_ONE] >> simp[]);

val ordADD_weak_MONO = store_thm(
  "ordADD_weak_MONO",
  ``∀c a b:'a ordinal. a < b ⇒ a + c ≤ b + c``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- simp[ordle_lteq] >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  strip_tac >> simp[predimage_sup_thm, impI] >> qx_gen_tac `d` >> strip_tac >>
  strip_tac >>
  `a + d ≤ b + d` by metis_tac[] >>
  `b + d ∈ IMAGE ($+ b) (preds c)` by simp[] >>
  metis_tac[sup_lt_implies, IMAGE_cardleq_rwt, preds_inj_univ]);

(* Multiplication *)

val ordMULT_def = new_specification(
  "ordMULT_def", ["ordMULT"],
  ord_RECURSION |> INST_TYPE [beta |-> ``:'a ordinal``]
                |> Q.SPEC `0`
                |> Q.SPEC `λap r. r + β`
                |> Q.SPEC `λa preds. sup preds`
                |> Q.GEN `β`
                |> CONV_RULE SKOLEM_CONV
                |> BETA_RULE)
val _ = export_rewrites ["ordMULT_def"]
val _ = overload_on ("*", ``ordMULT``)

val ordMULT_0L = store_thm(
  "ordMULT_0L",
  ``∀a:'a ordinal. 0 * a = 0``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE ($* 0) (preds a) = {0}` >> simp[] >>
  simp[EXTENSION] >> metis_tac[]);
val _ = export_rewrites ["ordMULT_0L"]

val ordMULT_0R = store_thm("ordMULT_0R", ``∀a:'a ordinal. a * 0 = 0``, simp[]);

val ordMULT_1L = store_thm(
  "ordMULT_1L",
  ``∀a. 1 * (a:'a ordinal) = a``,
  ho_match_mp_tac simple_ord_induction >> simp[ADD1R] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE ($* 1) (preds a) = preds a`
  >- fs [sup_preds_omax_NONE] >>
  dsimp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) []);
val _ = export_rewrites ["ordMULT_1L"]

val ordMULT_1R = store_thm(
  "ordMULT_1R",
  ``∀a:'a ordinal. a * 1 = a``,
  simp_tac bool_ss [GSYM ORD_ONE, ordMULT_def, ordADD_0L]);
val _ = export_rewrites ["ordMULT_1R"]

val ordMULT_2R = store_thm(
  "ordMULT_2R",
  ``(a:'a ordinal) * 2 = a + a``,
  `2 = 1⁺` by simp[] >> pop_assum SUBST1_TAC >> simp[]);

val islimit_SUC_lt = store_thm(
  "islimit_SUC_lt",
  ``islimit b ∧ a < b ⇒ a⁺ < b``,
  fs[omax_NONE] >> metis_tac [ordlt_SUC_DISCRETE, ordlt_trichotomy, ordle_lteq])

val ordMULT_lt_MONO_R = store_thm(
  "ordMULT_lt_MONO_R",
  ``∀a b c:'a ordinal. a < b ∧ 0 < c ⇒ c * a < c * b``,
  qsuff_tac `∀b a c:'a ordinal. a < b ∧ 0 < c ⇒ c * a < c * b` >- metis_tac[]>>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (simp[ordlt_SUC_DISCRETE] >> qx_gen_tac `b` >> strip_tac >>
      map_every qx_gen_tac [`a`, `c`] >>
      Cases_on `a = b` >> simp[] >> strip_tac >>
      `c * a < c * b` by metis_tac[] >>
      `c * b < c * b + c` by simp[] >> metis_tac [ordlt_TRANS]) >>
  qx_gen_tac `b` >> strip_tac >> map_every qx_gen_tac [`a`, `c`] >>
  strip_tac >> simp[predimage_sup_thm] >>
  `∃d. a < d ∧ d < b`
    by metis_tac[sup_preds_omax_NONE, IN_preds, preds_inj_univ, sup_thm] >>
  metis_tac[]);

val ordMULT_le_MONO_R = store_thm(
  "ordMULT_le_MONO_R",
  ``∀a b c:'a ordinal. a ≤ b ⇒ c * a ≤ c * b``,
  simp[ordle_lteq] >> rpt strip_tac >> simp[] >>
  Cases_on `c = 0` >> simp[] >>
  `0 < c` by metis_tac [ordlt_ZERO, ordlt_trichotomy] >>
  metis_tac [ordMULT_lt_MONO_R])

val ordMULT_lt_MONO_R_EQN = store_thm(
  "ordMULT_lt_MONO_R_EQN",
  ``c * a < c * b <=> a < b ∧ 0 < c``,
  simp[EQ_IMP_THM, ordMULT_lt_MONO_R] >>
  Cases_on `0 < c` >- metis_tac [ordMULT_le_MONO_R] >> fs[]);
val _ = export_rewrites ["ordMULT_lt_MONO_R_EQN"]

val ordADD_le_MONO_L = store_thm(
  "ordADD_le_MONO_L",
  ``x ≤ y ⇒ x + z ≤ y + z``,
  simp[ordle_lteq, SimpL ``$==>``] >> simp[DISJ_IMP_THM, ordADD_weak_MONO]);

val ordMULT_le_MONO_L = store_thm(
  "ordMULT_le_MONO_L",
  ``∀a b c:'a ordinal. a ≤ b ⇒ a * c ≤ b * c``,
  qsuff_tac `∀c a b:'a ordinal. a ≤ b ⇒ a * c ≤ b * c` >- metis_tac[] >>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
      strip_tac >>
      `a * c + a ≤ a * c + b` by simp[] >>
      match_mp_tac ordle_TRANS >> qexists_tac `a * c + b` >> simp[] >>
      simp[ordADD_le_MONO_L]) >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >> strip_tac>>
  simp[predimage_sup_thm, impI] >> qx_gen_tac `d` >> strip_tac >>
  match_mp_tac ordle_TRANS >> qexists_tac `b * d` >> simp[] >>
  qsuff_tac `b * d ∈ IMAGE ($* b) (preds c)`
  >- metis_tac [mklesup sup_thm, IMAGE_cardleq_rwt, preds_inj_univ] >>
  simp[] >> metis_tac[]);

val ordMULT_CANCEL_R = store_thm(
  "ordMULT_CANCEL_R",
  ``(z * x = z * y:'a ordinal) <=> (z = 0) ∨ (x = y)``,
  simp[EQ_IMP_THM, DISJ_IMP_THM] >> strip_tac >>
  Tactical.REVERSE (Cases_on `0 < z`) >- fs[] >>
  `x < y ∨ (x = y) ∨ y < x` by metis_tac [ordlt_trichotomy] >>
  metis_tac [ordMULT_lt_MONO_R_EQN, ordlt_REFL]);
val _ = export_rewrites ["ordMULT_CANCEL_R"]

val ordMULT_continuous0 =
  generic_continuity |> Q.INST [`f` |-> `$* a`]
                     |> SIMP_RULE (srw_ss()) []

val ordMULT_continuous = store_thm(
  "ordMULT_continuous",
  ``∀s:'a ordinal set. s ≼ univ(:'a inf) ⇒ a * sup s = sup (IMAGE ($* a) s)``,
  rpt strip_tac >> Cases_on `s = {}` >> simp[ordMULT_continuous0]);

val ordMULT_fromNat = store_thm(
  "ordMULT_fromNat",
  ``(&n : 'a ordinal) * &m = &(n * m)``,
  Induct_on `m` >> simp[arithmeticTheory.MULT_CLAUSES]);
val _ = export_rewrites ["ordMULT_fromNat"]

val omega_MUL_fromNat = store_thm(
  "omega_MUL_fromNat",
  ``0 < n ⇒ &n * ω = ω``,
  simp[omax_preds_omega] >> strip_tac >>
  match_mp_tac ordle_ANTISYM >> dsimp[predimage_sup_thm, lt_omega, impI] >>
  conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `m` >>
  qsuff_tac `&m < sup (IMAGE ($* &n) (preds ω))` >- metis_tac[ordlt_REFL]>>
  dsimp[predimage_sup_thm, lt_omega] >>
  qexists_tac `m + 1` >> simp[arithmeticTheory.LEFT_ADD_DISTRIB] >>
  qsuff_tac `m ≤ m * n ∧ m * n < n + m * n` >- DECIDE_TAC >>
  simp[]);

val ordMULT_LDISTRIB = store_thm(
  "ordMULT_LDISTRIB",
  ``∀a b c:'a ordinal. c * (a + b) = c * a + c * b``,
  qsuff_tac `∀b a c. c * (a + b) = c * a + c * b` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordADD_ASSOC] >>
  qx_gen_tac `b` >> strip_tac >>
  `preds b ≠ {}` by (strip_tac >> fs[]) >>
  simp[ordADD_continuous, ordMULT_continuous, IMAGE_cardleq_rwt,
       preds_inj_univ] >>
  rpt strip_tac >> AP_TERM_TAC >> dsimp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [])

val ordMULT_ASSOC = store_thm(
  "ordMULT_ASSOC",
  ``∀a b c:'a ordinal. a * (b * c) = (a * b) * c``,
  qsuff_tac `∀c a b:'a ordinal. a * (b * c) = (a * b) * c` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordMULT_LDISTRIB] >>
  simp[ordMULT_continuous, IMAGE_cardleq_rwt, preds_inj_univ] >>
  rpt strip_tac >> AP_TERM_TAC >> dsimp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [])

val ordDIVISION0 = prove(
  ``∀a b:'a ordinal. 0 < b ⇒ ∃q r. a = b * q + r ∧ r < b``,
  rpt strip_tac >>
  qabbrev_tac `d = sup { c | b * c ≤ a }` >>
  `∀c. b * c ≤ a ⇒ c ≤ a`
     by (ntac 2 strip_tac >> match_mp_tac ordle_TRANS >>
         qexists_tac `b * c` >> simp[] >>
         match_mp_tac ordle_TRANS >> qexists_tac `1 * c` >> conj_tac >- simp[]>>
         match_mp_tac ordMULT_le_MONO_L >>
         simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
         simp[] >> strip_tac >> fs[]) >>
  `∀α. α ∈ { c | b * c ≤ a } ⇒ α < a⁺`
    by (simp[ordlt_SUC_DISCRETE] >> metis_tac [ordle_lteq]) >>
  `∀α. α < d ⇔ ∃c. b * c ≤ a ∧ α < c`
    by (simp[Abbr`d`] >> pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
        simp[]) >>
  `b * d ≤ a`
    by (simp[Abbr`d`] >>
        `{ c | b * c ≤ a } ≼ univ(:'a inf)`
          by (`{ c | b * c ≤ a } ≼ preds a⁺`
                by simp[SUBSET_DEF, SUBSET_CARDLEQ] >>
              `preds a⁺ ≼ univ(:'a inf)` by simp[preds_inj_univ] >>
              metis_tac [cardleq_TRANS]) >>
        dsimp[ordMULT_continuous, sup_thm, IMAGE_cardleq_rwt, impI]) >>
  `∃r. b * d + r = a` by metis_tac [ordle_EXISTS_ADD] >>
  qsuff_tac `r < b` >- metis_tac[] >>
  spose_not_then strip_assume_tac >>
  `∃bb. b + bb = r` by metis_tac [ordle_EXISTS_ADD] >>
  `b * d⁺ + bb = a` by simp[GSYM ordADD_ASSOC] >>
  `∀c. b * c ≤ a ⇒ c ≤ d` by metis_tac [ordlt_REFL] >>
  metis_tac [ordlt_SUC, ordle_EXISTS_ADD]);

val ordDIVISION = new_specification(
  "ordDIVISION", ["ordDIV", "ordMOD"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ordDIVISION0)

val _ = set_fixity "/" (Infixl 600)
val _ = overload_on ("/", ``ordDIV``)

val _ = set_fixity "%" (Infixl 650)
val _ = overload_on ("%", ``ordMOD``)

val ordDIV_UNIQUE = store_thm(
  "ordDIV_UNIQUE",
  ``∀a b q r. 0 < (b:'a ordinal) ∧ a = b*q + r ∧ r < b ⇒ a / b = q``,
  rpt strip_tac >>
  `a = b * (a / b) + a % b ∧ a % b < b` by metis_tac [ordDIVISION] >>
  `a / b < q ∨ a / b = q ∨ q < a / b` by metis_tac [ordlt_trichotomy] >| [
    `∃bb. (q = a/b + bb) ∧ 0 < bb`
      by metis_tac [ordlt_EXISTS_ADD, ordlt_trichotomy, ordlt_ZERO] >>
    `a = b * (a/b + bb) + r` by metis_tac[] >>
    `_ = b * (a/b) + b * bb + r` by metis_tac[ordMULT_LDISTRIB] >>
    `a % b = b * bb + r` by metis_tac [ordADD_ASSOC, ordADD_RIGHT_CANCEL] >>
    `b * bb + r < b` by metis_tac[] >>
    `b ≤ b * bb`
      by (simp_tac bool_ss [Once (GSYM ordMULT_1R), SimpR ``ordlt``] >>
          match_mp_tac ordMULT_le_MONO_R >>
          simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
          simp[] >> strip_tac >> fs[]) >>
    `b ≤ b * bb + r` by metis_tac [ordle_CANCEL_ADDR, ordADD_le_MONO_L,
                                   ordle_TRANS],

    `∃bb. q + bb = a/b ∧ 0 < bb`
      by metis_tac [ordlt_EXISTS_ADD, ordlt_trichotomy, ordlt_ZERO] >>
    `a = b * (q + bb) + a % b` by metis_tac[] >>
    `_ = b * q + b * bb + a % b` by simp[ordMULT_LDISTRIB] >>
    `r = b * bb + a % b` by metis_tac [ordADD_ASSOC, ordADD_RIGHT_CANCEL] >>
    `b * bb + a % b < b` by metis_tac[] >>
    `b ≤ b * bb`
      by (simp_tac bool_ss [Once (GSYM ordMULT_1R), SimpR ``ordlt``] >>
          match_mp_tac ordMULT_le_MONO_R >>
          simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
          simp[] >> strip_tac >> fs[]) >>
    `b ≤ b * bb + a % b`
      by metis_tac [ordle_CANCEL_ADDR, ordADD_le_MONO_L, ordle_TRANS]
  ]);

val ordMOD_UNIQUE = store_thm(
  "ordMOD_UNIQUE",
  ``∀a b q r. 0 < b ∧ a = b * q + r ∧ r < b ⇒ a % b = r``,
  rpt strip_tac >>
  `(a = b * (a / b) + a % b) ∧ a % b < b` by metis_tac [ordDIVISION] >>
  `a / b = q` by metis_tac [ordDIV_UNIQUE] >> pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `r' = a % b` >> fs[])

(* Exponentiation *)
val ordEXP_def = new_specification(
  "ordEXP_def", ["ordEXP"],
  ord_RECURSION |> INST_TYPE [beta |-> ``:'a ordinal``]
                |> Q.SPEC `1`
                |> Q.SPEC `λap r. r * a`
                |> Q.SPEC `λa preds. sup preds`
                |> Q.GEN `a`
                |> CONV_RULE SKOLEM_CONV
                |> BETA_RULE
                |> SIMP_RULE (srw_ss()) [FORALL_AND_THM])
val _ = export_rewrites ["ordEXP_def"]
val _ = overload_on ("**", ``ordEXP``)

val ordEXP_1R = store_thm(
  "ordEXP_1R",
  ``(a:'a ordinal) ** 1 = a``,
  simp_tac bool_ss [GSYM ORD_ONE, ordEXP_def] >> simp[]);
val _ = export_rewrites ["ordEXP_1R"]

val ordEXP_1L = store_thm(
  "ordEXP_1L",
  ``∀a:'a ordinal. 1 ** a = 1``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE ($** 1) (preds a) = {1}` >> simp[] >>
  simp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) [] >> metis_tac[]);
val _ = export_rewrites ["ordEXP_1L"]

val ordEXP_2R = store_thm(
  "ordEXP_2R",
  ``(a:'a ordinal) ** 2 = a * a``,
  `2 = 1⁺` by simp[] >> pop_assum SUBST1_TAC >> simp[]);

val ordEXP_fromNat = store_thm(
  "ordEXP_fromNat",
  ``(&x:'a ordinal) ** &n = &(x ** n)``,
  Induct_on `n` >> simp[arithmeticTheory.EXP]);
val _ = export_rewrites ["ordEXP_fromNat"]

val ordEXP_le_MONO_L = store_thm(
  "ordEXP_le_MONO_L",
  ``∀x a b. a ≤ b ⇒ a ** x ≤ b ** x``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `x` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
      strip_tac >> match_mp_tac ordle_TRANS >>
      qexists_tac `a ** x * b` >> simp[ordMULT_le_MONO_L, ordMULT_le_MONO_R]) >>
  qx_gen_tac `x` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  strip_tac >> simp[predimage_sup_thm, impI] >>
  qx_gen_tac `d` >> strip_tac >>
  `a ** d ≤ b ** d` by simp[] >>
  `b ** d ∈ IMAGE ($** b) (preds x)` by (simp[] >> metis_tac[]) >>
  metis_tac [mklesup sup_thm, ordle_TRANS, IMAGE_cardleq_rwt, preds_inj_univ]);

val IFF_ZERO_lt = store_thm(
  "IFF_ZERO_lt",
  ``(x:'a ordinal ≠ 0 ⇔ 0 < x) ∧ (1 ≤ x ⇔ 0 < x)``,
  REWRITE_TAC [GSYM ORD_ONE] >> simp[ordlt_SUC_DISCRETE] >>
  metis_tac [ordlt_trichotomy, ordlt_ZERO]);

val islimit_SUC = store_thm(
  "islimit_SUC",
  ``islimit x⁺ ⇔ F``,
  simp[omax_NONE, impI, ordlt_SUC_DISCRETE] >>
  metis_tac[ordle_lteq]);
val _ = export_rewrites ["islimit_SUC"]

val islimit_fromNat = store_thm(
  "islimit_fromNat",
  ``islimit &x ⇔ x = 0``,
  Cases_on `x` >> simp[]);
val _ = export_rewrites ["islimit_fromNat"]

val ordEXP_ZERO_limit = store_thm(
  "ordEXP_ZERO_limit",
  ``∀x. islimit x ⇒ 0 ** x = 1``,
  ho_match_mp_tac simple_ord_induction >> simp[] >>
  qx_gen_tac `x` >> strip_tac >>
  qsuff_tac `IMAGE ($** 0) (preds x) = {0; 1}`
  >- (simp[] >> dsimp[sup_def, impI] >> strip_tac >>
      DEEP_INTRO_TAC oleast_intro >> simp[] >>
      conj_tac >- metis_tac [ordlt_REFL] >>
      qx_gen_tac `a` >> strip_tac >>
      qsuff_tac `a ≤ 1` >- metis_tac[ordle_ANTISYM] >>
      metis_tac[ordlt_REFL]) >>
  simp[EXTENSION] >> qx_gen_tac `y` >> dsimp[EQ_IMP_THM] >>
  Tactical.REVERSE (rpt conj_tac)
  >- (strip_tac >> qexists_tac `0` >> simp[])
  >- (strip_tac >> qexists_tac `0⁺` >> simp[] >>
      spose_not_then strip_assume_tac >> fs[ordle_lteq]
      >- metis_tac [ordlt_DISCRETE1, ORD_ONE] >>
      fs[]) >>
  qx_gen_tac `z` >> strip_tac >> Cases_on `islimit z` >- metis_tac[] >>
  `∃z0. z = z0⁺`
    by metis_tac [preds_omax_SOME_SUC, optionTheory.option_CASES] >>
  simp[])

val ordEXP_ZERO_nonlimit = store_thm(
  "ordEXP_ZERO_nonlimit",
  ``¬islimit x ⇒ 0 ** x = 0``,
  metis_tac [preds_omax_SOME_SUC, optionTheory.option_CASES, ordEXP_def,
             ordMULT_0R]);

val sup_EQ_0 = store_thm(
  "sup_EQ_0",
  ``s:'a ordinal set ≼ univ(:'a inf) ⇒ (sup s = 0 ⇔ s = {} ∨ s = {0})``,
  strip_tac >>
  qspec_then `0` (mp_tac o Q.AP_TERM `$~`) (sup_thm |> UNDISCH_ALL) >>
  simp_tac pure_ss [NOT_EXISTS_THM] >> simp[impI] >>
  disch_then (K ALL_TAC) >> simp[EXTENSION] >> metis_tac[])

val ordADD_EQ_0 = store_thm(
  "ordADD_EQ_0",
  ``∀y x. (x:'a ordinal) + y = 0 ⇔ x = 0 ∧ y = 0``,
  ho_match_mp_tac simple_ord_induction >> simp[] >>
  simp[sup_EQ_0, IMAGE_cardleq_rwt, preds_inj_univ] >>
  qx_gen_tac `y` >> strip_tac >> qx_gen_tac `x` >>
  `preds y <> {}` by (strip_tac >> fs[]) >>
  simp[EXTENSION] >>
  `y ≠ 0` by metis_tac [ordlt_REFL] >> simp[] >>
  qexists_tac `x⁺` >> simp[] >> qexists_tac `1` >>
  metis_tac [ADD1R, islimit_SUC_lt, ORD_ONE])
val _ = export_rewrites ["ordADD_EQ_0"]

val IMAGE_EQ_SING = store_thm(
  "IMAGE_EQ_SING",
  ``IMAGE f s = {x} ⇔ (∃y. y ∈ s) ∧ ∀y. y ∈ s ⇒ f y = x``,
  simp[EXTENSION] >> metis_tac []);

val ordMULT_EQ_0 = store_thm(
  "ordMULT_EQ_0",
  ``∀x y. x * y = 0 ⇔ x = 0 ∨ y = 0``,
  CONV_TAC SWAP_FORALL_CONV >>
  ho_match_mp_tac simple_ord_induction >> simp[] >>
  simp_tac (srw_ss() ++ CONJ_ss) [] >> qx_gen_tac `x` >> strip_tac >>
  simp[sup_EQ_0, IMAGE_cardleq_rwt, preds_inj_univ] >>
  `preds x <> {} ∧ x ≠ 0` by (rpt strip_tac >> fs[]) >>
  qx_gen_tac `y` >> eq_tac
  >- (simp[IMAGE_EQ_SING] >> strip_tac >>
      pop_assum (qspec_then `1` mp_tac) >> simp[] >>
      disch_then match_mp_tac >> metis_tac [islimit_SUC_lt, ORD_ONE]) >>
  simp[IMAGE_EQ_SING] >> metis_tac[]);
val _ = export_rewrites ["ordMULT_EQ_0"]

val ordEXP_EQ_0 = store_thm(
  "ordEXP_EQ_0",
  ``∀y x. x ** y = 0 ⇔ x = 0 ∧ ¬islimit y``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- metis_tac[] >>
  qx_gen_tac `y` >> strip_tac >>
  simp[sup_EQ_0, IMAGE_cardleq_rwt, preds_inj_univ] >>
  simp[IFF_ZERO_lt] >>
  `preds y ≠ ∅` by (strip_tac >> fs[]) >> simp[] >>
  simp[IMAGE_EQ_SING] >> qx_gen_tac `x` >> DISJ2_TAC >>
  qexists_tac `0` >> simp[]);

val ZERO_lt_ordEXP_I = store_thm(
  "ZERO_lt_ordEXP_I",
  ``∀a x:'a ordinal. 0 < a ⇒ 0 < a ** x``,
  metis_tac [IFF_ZERO_lt, ordEXP_EQ_0]);

val ZERO_lt_ordEXP = store_thm(
  "ZERO_lt_ordEXP",
  ``0 < a ** x ⇔ 0 < a ∨ islimit x``,
  metis_tac [ordEXP_EQ_0, IFF_ZERO_lt])

val ordEXP_lt_MONO_R = store_thm(
  "ordEXP_lt_MONO_R",
  ``∀y x a:'a ordinal. 1 < a ∧ x < y ⇒ a ** x < a ** y``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> rpt conj_tac >>
  qx_gen_tac `y` >> strip_tac >> map_every qx_gen_tac [`x`, `a`]
  >- (simp[ordlt_SUC_DISCRETE] >> rw[] >| [
        match_mp_tac ordlt_TRANS >> qexists_tac `a ** y` >> simp[],
        ALL_TAC
      ] >> simp_tac bool_ss [SimpL ``ordlt``, Once (GSYM ordMULT_1R)] >>
      simp[ZERO_lt_ordEXP] >> DISJ1_TAC >>
      match_mp_tac ordlt_TRANS >> qexists_tac `1` >> simp[]) >>
  simp[predimage_sup_thm] >> fs[omax_NONE] >>
  metis_tac[]);

val ordEXP_lt_IFF = store_thm(
  "ordEXP_lt_IFF",
  ``∀x y a:'a ordinal. 1 < a ⇒ (a ** x < a ** y ⇔ x < y)``,
  simp[EQ_IMP_THM, ordEXP_lt_MONO_R] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq]
  >- metis_tac[ordlt_TRANS, ordlt_REFL, ordEXP_lt_MONO_R] >> fs[]);
val _ = export_rewrites ["ordEXP_lt_IFF"]

val ordEXP_le_MONO_R = store_thm(
  "ordEXP_le_MONO_R",
  ``∀x y a. 0 < a ∧ x ≤ y ⇒ a ** x ≤ a ** y``,
  rpt gen_tac >> simp[ordle_lteq] >> rw[] >> Cases_on `a = 1` >- simp[] >>
  qsuff_tac `1 < a` >- metis_tac [ordEXP_lt_MONO_R] >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq] >> fs[] >>
  metis_tac [ORD_ONE, ordlt_DISCRETE1]);

val ordEXP_continuous = store_thm(
  "ordEXP_continuous",
  ``∀a s:'a ordinal set.
       0 < a ∧ s ≼ univ(:'a inf) ∧ s ≠ ∅ ⇒
       a ** sup s = sup (IMAGE ($** a) s)``,
  simp[generic_continuity, ordEXP_le_MONO_R]);

val ordEXP_ADD = store_thm(
  "ordEXP_ADD",
  ``0 < x ⇒ x ** (y + z) = x ** y * x ** z``,
  map_every qid_spec_tac [`x`,`y`,`z`] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordMULT_ASSOC] >>
  qx_gen_tac `z` >> strip_tac >> map_every qx_gen_tac [`y`, `x`] >>
  `preds z ≠ ∅` by (strip_tac >> fs[]) >>
  simp[ordEXP_continuous, IMAGE_cardleq_rwt, preds_inj_univ,
       ordMULT_continuous, GSYM IMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF] >> strip_tac >> AP_TERM_TAC >>
  simp[EXTENSION] >> metis_tac[]);

val ordEXP_MUL = store_thm(
  "ordEXP_MUL",
  ``0 < x ⇒ x ** (y * z) = (x ** y) ** z``,
  strip_tac >> map_every qid_spec_tac [`y`, `z`] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordEXP_ADD] >>
  qx_gen_tac `z` >> strip_tac >> qx_gen_tac `y` >>
  `preds z ≠ ∅` by (strip_tac >> fs[]) >>
  simp[ordEXP_continuous, IMAGE_cardleq_rwt, preds_inj_univ,
       GSYM IMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF] >> AP_TERM_TAC >>
  simp[EXTENSION] >> metis_tac []);

val fixpoints_exist = store_thm(
  "fixpoints_exist",
  ``(!s:'a ordinal set. s ≠ ∅ ∧ s ≼ univ(:'a inf) ⇒
                        f (sup s) = sup (IMAGE f s)) ∧
    (∀x. x ≤ f x) ⇒
    ∀a. ∃b. a ≤ b ∧ f b = b``,
  rpt strip_tac >> qexists_tac `sup { FUNPOW f n a | n | T }` >>
  `{FUNPOW f n a | n | T} ≼ univ(:'a inf)`
    by (simp[cardleq_def] >>
        qsuff_tac `∃g. SURJ g univ(:'a inf) {FUNPOW f n a | n | T}`
        >- metis_tac[SURJ_INJ_INV] >>
        qexists_tac `λx. case x of INL n => FUNPOW f n a
                                 | INR n => a` >>
        dsimp[SURJ_DEF] >> conj_tac
        >- (simp[sumTheory.FORALL_SUM] >>
            metis_tac [arithmeticTheory.FUNPOW]) >>
        qx_gen_tac `n` >> qexists_tac `INL n` >> simp[]) >>
  conj_tac
  >- (match_mp_tac suple_thm >> simp[] >> qexists_tac `0` >> simp[]) >>
  `{ FUNPOW f n a | n | T } ≠ ∅` by simp[EXTENSION] >>
  simp[] >> match_mp_tac sup_eq_sup >>
  dsimp[IMAGE_cardleq_rwt] >>
  `∀n. ∃m. f (FUNPOW f n a) ≤ FUNPOW f m a`
    by (strip_tac >> qexists_tac `SUC n` >>
        simp[arithmeticTheory.FUNPOW_SUC]) >>
  `∀n. ∃m. FUNPOW f n a ≤ f (FUNPOW f m a)`
    by (strip_tac >> qexists_tac `n` >> simp[]) >> simp[]);

val x_le_ordEXP_x = store_thm(
  "x_le_ordEXP_x",
  ``∀a x. 1 < a ⇒ x ≤ a ** x``,
  gen_tac >> Cases_on `1 < a` >> simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac >>
  qx_gen_tac `x` >> strip_tac
  >- (qsuff_tac `x < a ** x * a`
      >- (simp[ordlt_SUC_DISCRETE] >> simp[ordle_lteq] >>
          metis_tac[ordlt_REFL]) >>
      qsuff_tac `a ** x < a ** x * a`
      >- metis_tac[ordle_lteq, ordlt_TRANS] >>
      SIMP_TAC bool_ss [SimpL ``ordlt``, Once (GSYM ordMULT_1R)] >>
      simp[ZERO_lt_ordEXP] >> DISJ1_TAC >> match_mp_tac ordlt_TRANS >>
      qexists_tac `1` >> simp[]) >>
  `∀b. b < x ⇒ b⁺ < x` by metis_tac [islimit_SUC_lt] >>
  fs[omax_NONE] >> strip_tac >>
  `∃b. b < x ∧ sup (IMAGE ($** a) (preds x)) < b` by metis_tac[] >>
  `∀d. d < x ⇒ a ** d ≤ b` by metis_tac[predimage_suplt_ELIM] >>
  `a ** b < a ** b⁺` by simp[] >>
  `a ** b⁺ ≤ b` by metis_tac[] >>
  `b ≤ a ** b` by metis_tac[] >>
  metis_tac[ordlt_TRANS, ordle_lteq, ordlt_REFL])

val epsilon0_def = Define`
  epsilon0 = oleast x. ω ** x = x
`

val _ = overload_on("ε₀", ``epsilon0``)

val epsilon0_fixpoint = store_thm(
  "epsilon0_fixpoint",
  ``ω ** ε₀ = ε₀``,
  simp[epsilon0_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  metis_tac [fromNat_lt_omega, ordEXP_continuous, x_le_ordEXP_x,
             fixpoints_exist]);

val epsilon0_least_fixpoint = store_thm(
  "epsilon0_least_fixpoint",
  ``∀a. a < ε₀ ⇒ a < ω ** a ∧ ω ** a < ε₀``,
  gen_tac >> simp[epsilon0_def] >> DEEP_INTRO_TAC oleast_intro >>
  metis_tac [epsilon0_fixpoint, x_le_ordEXP_x, ordle_lteq, ordEXP_lt_MONO_R,
             fromNat_lt_omega]);

val zero_lt_epsilon0 =
  epsilon0_fixpoint |> SIMP_RULE (srw_ss()) [ASSUME ``ε₀ = 0``]
                    |> DISCH_ALL
                    |> SIMP_RULE (srw_ss()) [IFF_ZERO_lt]

val one_lt_epsilon0 =
    MATCH_MP epsilon0_least_fixpoint zero_lt_epsilon0
             |> SIMP_RULE (srw_ss()) []

(* |- ω < ε₀ *)
val omega_lt_epsilon0 = save_thm(
  "omega_lt_epsilon0",
  MATCH_MP epsilon0_least_fixpoint one_lt_epsilon0
           |> SIMP_RULE (srw_ss()) [])
val _ = export_rewrites ["omega_lt_epsilon0"]

val fromNat_lt_epsilon0 = store_thm(
  "fromNat_lt_epsilon0",
  ``&n < ε₀``,
  metis_tac [ordlt_TRANS, fromNat_lt_omega, omega_lt_epsilon0]);
val _ = export_rewrites ["fromNat_lt_epsilon0"]

val add_nat_islimit = store_thm(
  "add_nat_islimit",
  ``0 < n ⇒ islimit (α + &n) = F``,
  Induct_on `n` >> simp[]);
val _ = export_rewrites ["add_nat_islimit"]

val strict_continuity_preserves_islimit = store_thm(
  "strict_continuity_preserves_islimit",
  ``(∀s. s ≼ univ(:α inf) ∧ s ≠ ∅ ⇒
         f (sup s) = sup (IMAGE f s) : 'a ordinal) ∧
    (∀x y. x < y ⇒ f x < f y) ∧
    islimit (α:α ordinal) ∧ α ≠ 0 ⇒ islimit (f α)``,
  strip_tac >> fs[sup_preds_omax_NONE] >>
  first_assum (fn th => simp_tac (srw_ss()) [SimpRHS, Once (SYM th)]) >>
  `preds α ≠ ∅`
    by (strip_tac >> `0 < a` by fs[IFF_ZERO_lt] >> rw[] >> fs[]) >>
  simp[preds_inj_univ] >>
  match_mp_tac ordle_ANTISYM >>
  simp[sup_thm, IMAGE_cardleq_rwt, preds_inj_univ, impI] >> conj_tac
  >- (qx_gen_tac `b` >> strip_tac >> match_mp_tac ordle_TRANS >>
      qexists_tac `f α` >> conj_tac >- simp[ordle_lteq] >>
      Q.UNDISCH_THEN `sup (preds α) = α`
        (fn th => simp_tac (srw_ss()) [SimpR ``ordlt``, Once (SYM th)]) >>
      simp[preds_inj_univ]) >>
  asm_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `x` >> strip_tac >>
  match_mp_tac suple_thm >> simp[preds_inj_univ])

val add_omega_islimit = store_thm(
  "add_omega_islimit",
  ``islimit (α + ω)``,
  ho_match_mp_tac strict_continuity_preserves_islimit >>
  simp[omax_preds_omega, ordADD_continuous])
val _ = export_rewrites ["add_omega_islimit"]

val islimit_mul_R = store_thm(
  "islimit_mul_R",
  ``∀α. islimit α ⇒ islimit (β * α)``,
  Cases_on `β = 0` >- simp[] >> fs[IFF_ZERO_lt] >> gen_tac >>
  Cases_on `α = 0` >- simp[] >> fs[IFF_ZERO_lt] >> strip_tac >>
  qspec_then `$* β` mp_tac
    (Q.GEN `f` strict_continuity_preserves_islimit) >> simp[] >>
  simp[ordMULT_continuous, IFF_ZERO_lt])

val mul_omega_islimit = store_thm(
  "mul_omega_islimit",
  ``islimit (ω * α)``,
  qspec_then `α` strip_assume_tac ord_CASES >> simp[islimit_mul_R]);

val omega_exp_islimit = store_thm(
  "omega_exp_islimit",
  ``0 < α ⇒ islimit (ω ** α)``,
  qspec_then `α` strip_assume_tac ord_CASES
  >- simp[]
  >- (simp[] >> simp[islimit_mul_R, omax_preds_omega]) >>
  strip_tac >> ho_match_mp_tac strict_continuity_preserves_islimit >>
  simp[IFF_ZERO_lt, ordEXP_continuous]);

val expbound_add = store_thm(
  "expbound_add",
  ``∀α x y. x < ω ** α ∧ y < ω ** α ⇒ x + y < ω ** α``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> rpt conj_tac
  >- metis_tac [IFF_ZERO_lt, ordADD_def]
  >- (qx_gen_tac `a` >> strip_tac >>
      simp_tac bool_ss [ordMULT_def,omega_islimit,fromNat_lt_omega] >>
      simp[predimage_sup_thm] >>
      map_every qx_gen_tac [`x`, `y`] >>
      CONV_TAC (LAND_CONV (BINOP_CONV
                               (SIMP_CONV(srw_ss() ++ DNF_ss)[lt_omega]))) >>
      disch_then (CONJUNCTS_THEN2
                  (Q.X_CHOOSE_THEN `b` strip_assume_tac)
                  (Q.X_CHOOSE_THEN `c` strip_assume_tac)) >>
      `x + y < ω ** a * &(b + c)`
        by (simp_tac bool_ss [ordMULT_LDISTRIB, GSYM ordADD_fromNat] >>
            match_mp_tac ordlte_TRANS >>
            qexists_tac `x + ω ** a * &c` >> simp[] >>
            simp[ordADD_weak_MONO]) >>
      asm_simp_tac(srw_ss() ++ DNF_ss)[] >> qexists_tac `&(b + c)` >>
      simp[]) >>
  qx_gen_tac `a` >> strip_tac >>
  map_every qx_gen_tac [`x`, `y`] >>
  simp[predimage_sup_thm] >>
  disch_then (CONJUNCTS_THEN2
              (Q.X_CHOOSE_THEN `b` strip_assume_tac)
              (Q.X_CHOOSE_THEN `c` strip_assume_tac)) >>
  Cases_on `b < c`
  >- (`ω ** b < ω ** c` by simp[] >>
      `x < ω ** c` by metis_tac [ordlt_TRANS] >>
      metis_tac[]) >>
  `ω ** c ≤ ω ** b` by simp[] >>
  `y < ω ** b` by metis_tac [ordlte_TRANS] >>
  metis_tac[])

val downduct = prove(
  ``(∀n. n ≤ m ∧ P (SUC n) ⇒ P n) ∧ P m ⇒
    (∀n. n ≤ m ⇒ P n)``,
  strip_tac >> fs[arithmeticTheory.LESS_EQ_EXISTS] >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> CONV_TAC SWAP_FORALL_CONV >>
  Induct >> rw[] >> simp[]);

val addL_fixpoint_iff = store_thm(
  "addL_fixpoint_iff",
  ``α + β = β ⇔ α * ω ≤ β``,
  eq_tac
  >- (simp[omega_islimit, ordMULT_def, EQ_IMP_THM, sup_thm, IMAGE_cardleq_rwt,
           preds_inj_univ, lt_omega] >> strip_tac >>
      qx_gen_tac `γ` >> Cases_on `β < γ` >> simp[] >>
      qx_gen_tac `δ` >> Cases_on `γ = α * δ` >> simp[] >> qx_gen_tac `m` >>
      strip_tac >> rw[] >>
      `∀n. n ≤ m ⇒ β < α * &n` suffices_by
         (disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      ho_match_mp_tac downduct >> simp[] >>
      qx_gen_tac `n`>>
      `α * &n + α = α + α * &n` suffices_by metis_tac[ordlt_CANCEL] >>
      Induct_on `n` >> simp[] >> metis_tac[ordADD_ASSOC])
  >- (simp[ordle_EXISTS_ADD] >>
      disch_then (qx_choose_then `c` SUBST_ALL_TAC) >>
      simp[ordADD_ASSOC] >>
      `α + α * ω = α * (1 + ω)` by simp[ordMULT_LDISTRIB] >>
      simp[ordADD_fromNat_omega, omega_islimit]))

(* And so, arithmetic (addition, multiplication and exponentiation) is
   closed under ε₀ *)
val ordADD_under_epsilon0 = store_thm(
  "ordADD_under_epsilon0",
  ``x < ε₀ ∧ y < ε₀ ⇒ x + y < ε₀``,
  ONCE_REWRITE_TAC [GSYM epsilon0_fixpoint] >>
  simp[expbound_add])

val ordMUL_under_epsilon0 = store_thm(
  "ordMUL_under_epsilon0",
  ``x < ε₀ ∧ y < ε₀ ⇒ x * y < ε₀``,
  strip_tac >> imp_res_tac epsilon0_least_fixpoint >>
  `x * y < ω ** x * ω ** y`
    by (match_mp_tac ordlet_TRANS >>
        qexists_tac `ω ** x * y` >> simp[ZERO_lt_ordEXP] >>
        match_mp_tac ordMULT_le_MONO_L >> simp[ordle_lteq]) >>
  `ω ** x * ω ** y = ω ** (x + y)` by simp[ordEXP_ADD] >>
  pop_assum SUBST_ALL_TAC >>
  qsuff_tac `ω ** (x + y) < ε₀` >- metis_tac[ordlt_TRANS] >>
  metis_tac [epsilon0_fixpoint, ordADD_under_epsilon0, fromNat_lt_omega,
             ordEXP_lt_IFF]);

val ordEXP_under_epsilon0 = store_thm(
  "ordEXP_under_epsilon0",
  ``a < ε₀ ∧ b < ε₀ ⇒ a ** b < ε₀``,
  strip_tac >>
  `a < ω ** a` by imp_res_tac epsilon0_least_fixpoint >>
  `a ** b <= (ω ** a) ** b` by metis_tac [ordEXP_le_MONO_L, ordle_lteq] >>
  `(ω ** a) ** b = ω ** (a * b)` by simp [GSYM ordEXP_MUL] >>
  pop_assum SUBST_ALL_TAC >>
  `ω ** (a * b) < ε₀`
    by simp[ordEXP_lt_IFF, ordMUL_under_epsilon0,
            Once (GSYM epsilon0_fixpoint)] >>
  metis_tac [ordlet_TRANS]);

val eval_poly_def = Define`
  eval_poly (a:'a ordinal) [] = 0 ∧
  eval_poly a ((c,e)::t) = a ** e * c + eval_poly a t
`;
val _ = export_rewrites ["eval_poly_def"]

val is_polyform_def = Define`
  (is_polyform (a:'a ordinal) [] ⇔ T) ∧
  (is_polyform a [(c,e)] ⇔ 0 < c ∧ c < a) ∧
  (is_polyform a ((c1,e1) :: (c2,e2) :: t) ⇔
     0 < c1 ∧ c1 < a ∧ e2 < e1 ∧ is_polyform a ((c2,e2) :: t))
`;

val is_polyform_ELthm = store_thm(
  "is_polyform_ELthm",
  ``is_polyform a ces ⇔
      (∀i j. i < j ∧ j < LENGTH ces ⇒ SND (EL j ces) < SND (EL i ces)) ∧
      (∀c e. MEM (c,e) ces ⇒ 0 < c ∧ c < a)``,
  map_every qid_spec_tac [`ces`, `a`] >>
  ho_match_mp_tac (theorem "is_polyform_ind") >> simp[is_polyform_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  eq_tac >> simp[] >| [
    strip_tac >> ASM_REWRITE_TAC [] >>
    map_every qx_gen_tac [`i`, `j`] >>
    `i = 0 ∨ ∃i0. i = SUC i0` by (Cases_on `i` >> simp[])
    >- (simp[] >> strip_tac >>
        `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >>
        fs[] >>
        `j0 = 0 ∨ ∃j00. j0 = SUC j00` by (Cases_on `j0` >> simp[]) >> simp[] >>
        first_x_assum (qspecl_then [`0`, `j0`] mp_tac) >> simp[] >>
        metis_tac [ordlt_TRANS]) >>
    strip_tac >>
    `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
    asm_simp_tac (srw_ss() ++ ARITH_ss) [],
    rpt strip_tac
    >- (first_x_assum (qspecl_then [`0`, `SUC 0`] mp_tac) >> simp[])
    >- (first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
    >- res_tac >> res_tac
  ]);

val polyform_exists = store_thm(
  "polyform_exists",
  ``∀a:'a ordinal b.
      1 < a ⇒ ∃ces. is_polyform a ces ∧ b = eval_poly a ces``,
  gen_tac >> Cases_on `1 < a` >> simp[is_polyform_ELthm] >>
  `0 < a` by (match_mp_tac ordlt_TRANS >> qexists_tac `1` >> simp[]) >>
  ho_match_mp_tac ord_induction >>
  qx_gen_tac `b` >> strip_tac >> Cases_on `b = 0`
  >- (qexists_tac `[]` >> simp[]) >>
  `0 < b ∧ 1 ≤ b` by fs[IFF_ZERO_lt] >>
  qabbrev_tac `s = { e | a ** e ≤ b }` >>
  `∀e. e ∈ s ⇔ a ** e ≤ b` by simp[Abbr`s`] >>
  `s ≠ ∅` by (simp[EXTENSION] >> qexists_tac `0` >> simp[]) >>
  `∀c. c ∈ s ⇒ c < b⁺`
    by (simp[ordlt_SUC_DISCRETE, GSYM ordle_lteq] >>
        metis_tac [x_le_ordEXP_x, ordle_TRANS]) >>
  `s ≼ univ(:'a inf)`
    by (`s ≼ preds b⁺` by simp[SUBSET_CARDLEQ, SUBSET_DEF] >>
        metis_tac [cardleq_TRANS, preds_inj_univ]) >>
  qabbrev_tac `E = sup s` >>
  `∀g. g < E ⇔ ∃d. d ∈ s ∧ g < d` by simp[sup_thm, Abbr`E`] >>
  `a ** E ≤ b`
    by dsimp[Abbr`E`, ordEXP_continuous, sup_thm, IMAGE_cardleq_rwt, impI] >>
  `b < a ** E⁺`
    by (spose_not_then strip_assume_tac >>
        `E⁺ ∈ s` by simp[] >> `E⁺ ≤ E` by metis_tac [suple_thm] >>
        fs[]) >>
  qabbrev_tac `c1 = b / a ** E` >>
  qabbrev_tac `r = b % a ** E` >>
  `0 < a ** E` by simp[ZERO_lt_ordEXP] >>
  `b = a ** E * c1 + r ∧ r < a ** E` by metis_tac [ordDIVISION] >>
  `r < b` by metis_tac [ordlt_TRANS, ordle_lteq] >>
  `0 < c1` by (spose_not_then strip_assume_tac >> fs[]) >>
  `c1 < a`
    by (spose_not_then strip_assume_tac >>
        `a ** E * a ≤ a ** E * c1` by simp[] >>
        `a ** E * a + r ≤ b` by simp[ordADD_le_MONO_L] >>
        metis_tac [ordEXP_def, ordle_CANCEL_ADDR, ordle_TRANS]) >>
  `∃ces. (∀i j. i < j ∧ j < LENGTH ces ⇒ SND (EL j ces) < SND (EL i ces)) ∧
         (∀c e. MEM (c,e) ces ⇒ 0 < c ∧ c < a) ∧
         r = eval_poly a ces` by metis_tac[] >>
  qexists_tac `(c1,E) :: ces` >> dsimp[] >> Tactical.REVERSE (rpt conj_tac)
  >- metis_tac[] >- metis_tac[] >>
  gen_tac >>
  `(∃i0. i = SUC i0) ∨ i = 0` by (Cases_on `i` >> simp[])
  >- (gen_tac >> Cases_on `j` >> simp[]) >>
  qpat_assum `∀g. g < E ⇔ P` (K ALL_TAC) >> simp[] >>
  qsuff_tac `0 < LENGTH ces ⇒ SND (EL 0 ces) < E`
  >- (strip_tac >> qx_gen_tac `j` >> strip_tac >>
      `j = 0 ∨ ∃j0. j = SUC j0` by (Cases_on `j` >> simp[]) >> simp[] >>
      `j0 < LENGTH ces` by fs[] >>
      `0 < LENGTH ces` by decide_tac >>
      Cases_on `j0 = 0` >- asm_simp_tac bool_ss [] >>
      `0 < j0` by decide_tac >>
      metis_tac [ordlt_TRANS]) >>
  `ces = [] ∨ ∃c0 e0 t. ces = (c0,e0)::t`
    by metis_tac [pairTheory.pair_CASES, listTheory.list_CASES] >- simp[] >>
  simp[] >> (* rts: e0 < E *) spose_not_then strip_assume_tac >>
  `r = a ** e0 * c0 + eval_poly a t` by simp[] >>
  `a ** E ≤ a ** e0` by simp[ordEXP_le_MONO_R] >>
  `a ** e0 ≤ a ** e0 * c0`
    by (simp_tac bool_ss [SimpR ``ordlt``, Once (GSYM ordMULT_1R)] >>
        match_mp_tac ordMULT_le_MONO_R >> simp[IFF_ZERO_lt] >> fs[]) >>
  `a ** e0 * c0 ≤ a ** e0 * c0 + eval_poly a t` by simp[] >>
  metis_tac [ordle_TRANS, ordle_lteq, ordlt_REFL, ordlt_TRANS])

val polyform_def = new_specification(
  "polyform_def",
  ["polyform"],
  SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
            polyform_exists);

(* Cantor Normal Form - polynomials where the base is ω *)
val _ = overload_on ("CNF", ``polyform ω``)

val CNF_thm = save_thm(
  "CNF_thm",
  polyform_def |> SPEC ``ω`` |> SIMP_RULE (srw_ss()) [])

val polyform_0 = store_thm(
  "polyform_0",
  ``1 < a ⇒ polyform a 0 = []``,
  strip_tac >>
  qspecl_then [`a`, `0`] mp_tac polyform_def >> simp[] >>
  `polyform a 0 = [] ∨ ∃c e t. polyform a 0 = (c,e)::t`
    by metis_tac[pairTheory.pair_CASES, listTheory.list_CASES]
    >- simp[] >>
  simp[SimpL ``$==>``] >> strip_tac >> fs[]
  >- fs[ordEXP_EQ_0] >>
  `0 < c` by metis_tac[is_polyform_ELthm,listTheory.MEM] >>
  metis_tac[IFF_ZERO_lt]);

val polyform_EQ_NIL = store_thm(
  "polyform_EQ_NIL",
  ``1 < a ⇒ (polyform a x = [] ⇔ x = 0)``,
  simp[EQ_IMP_THM, polyform_0] >>
  rpt strip_tac >>
  qspecl_then [`a`, `x`] mp_tac polyform_def >> simp[]);

val is_polyform_CONS_E = store_thm(
  "is_polyform_CONS_E",
  ``is_polyform a ((c,e)::t) ⇒ 0 < c ∧ c < a ∧ is_polyform a t``,
  Cases_on `t` >> simp[is_polyform_def] >> Cases_on `h` >>
  simp[is_polyform_def]);

val expbounds = prove(
  ``1 < (a:'a ordinal) ∧ y < a ** e ∧ c < a ∧ e < e' ⇒
    a ** e * c + y < a ** e'``,
  strip_tac >>
  `a ** e * c + y < a ** e * c + a ** e` by simp[] >>
  `a ** e * c + a ** e = a ** e * ordSUC c` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  `c⁺ ≤ a` by metis_tac [ordlt_DISCRETE1] >>
  `a ** e * c⁺ ≤ a ** e * a` by simp[ordMULT_le_MONO_R] >>
  `a ** e * a = a ** e⁺` by simp[] >> pop_assum SUBST_ALL_TAC >>
  `a ** e⁺ ≤ a ** e'`
     by (match_mp_tac ordEXP_le_MONO_R >> conj_tac
         >- (spose_not_then strip_assume_tac >> fs[]) >>
         metis_tac [ordlt_DISCRETE1]) >>
  metis_tac [ordlte_TRANS, ordle_TRANS])

val is_polyform_head_dominates_tail = store_thm(
  "is_polyform_head_dominates_tail",
  ``1 < a ∧ is_polyform a ((c,e)::t) ⇒ eval_poly a t < a ** e``,
  qsuff_tac
     `∀a ces. 1 < a ∧ is_polyform a ces ∧ ces ≠ [] ⇒
              eval_poly a (TL ces) < a ** SND (HD ces)`
  >- (disch_then (qspecl_then [`a`, `(c,e)::t`] strip_assume_tac) >>
      strip_tac >> fs[]) >>
  ho_match_mp_tac (theorem "is_polyform_ind") >> simp[is_polyform_def] >>
  rpt strip_tac
  >- (spose_not_then strip_assume_tac >> fs[] >> fs[ordEXP_EQ_0]) >>
  fs[] >> metis_tac[is_polyform_CONS_E, expbounds])

val cx_lt_x = store_thm(
  "cx_lt_x",
  ``x * c < (x:'a ordinal) ⇔ 0 < x ∧ c = 0``,
  simp_tac bool_ss [SimpLHS, SimpR ``ordlt``, Once (GSYM ordMULT_1R)] >>
  simp[] >> metis_tac [IFF_ZERO_lt]);
val _ = export_rewrites ["cx_lt_x"]

val explemma = prove(
  ``1 < a ∧ a ** e1 * c1 + eval_poly a t1 = a ** e2 * c2 + eval_poly a t2 ∧
    is_polyform a ((c1,e1)::t1) ∧ is_polyform a ((c2,e2)::t2) ⇒
    e1 ≤ e2``,
  rpt strip_tac (* e2 < e1 *) >>
  `eval_poly a t2 < a ** e2` by metis_tac [is_polyform_head_dominates_tail] >>
  imp_res_tac is_polyform_CONS_E >>
  `a ** e2 * c2 + eval_poly a t2 < a ** e1` by simp[expbounds] >>
  `a ** e1 ≤ a ** e1 * c1` by simp[IFF_ZERO_lt] >>
  `a ** e1 * c1 ≤ a ** e1 * c1 + eval_poly a t1` by simp[] >>
  metis_tac[ordlte_TRANS, ordle_TRANS, ordlt_REFL]);

val coefflemma = prove(
  ``1 < a ∧ a ** e * c1 + eval_poly a t1 = a ** e * c2 + eval_poly a t2 ∧
    is_polyform a ((c1,e)::t1) ∧ is_polyform a ((c2,e)::t2) ⇒
    c1 ≤ c2``,
  rpt strip_tac (* c2 < c1 *) >>
  `eval_poly a t2 < a ** e` by metis_tac [is_polyform_head_dominates_tail] >>
  imp_res_tac is_polyform_CONS_E >>
  `a ** e * c2 + eval_poly a t2 < a ** e * c2 + a ** e` by simp[] >>
  `a ** e * c2 + a ** e = a ** e * c2⁺` by simp[] >> pop_assum SUBST_ALL_TAC >>
  `a ** e * c2⁺ ≤ a ** e * c1` by (simp[] >> metis_tac [ordlt_DISCRETE1]) >>
  `a ** e * c1 ≤ a ** e * c1 + eval_poly a t1` by simp[] >>
  metis_tac [ordlte_TRANS, ordle_TRANS, ordlt_REFL]);

val polyform_UNIQUE = store_thm(
  "polyform_UNIQUE",
  ``∀a b ces.
      1 < a ∧ is_polyform a ces ∧ b = eval_poly a ces ⇒
      polyform a b = ces``,
  gen_tac >> ho_match_mp_tac ord_induction >> qx_gen_tac `b` >>
  strip_tac >> qx_gen_tac `ces1` >> strip_tac >>
  `0 < a` by (`0 < 1o` by simp[] >> metis_tac [ordlt_TRANS]) >>
  qspecl_then [`a`, `b`] mp_tac polyform_def >>
  disch_then (strip_assume_tac o REWRITE_RULE [ASSUME``1<a:'a ordinal``]) >>
  `ces1 = [] ∨ ∃c e t. ces1 = (c,e)::t`
    by metis_tac[pairTheory.pair_CASES, listTheory.list_CASES]
  >- (pop_assum SUBST_ALL_TAC >> `b = 0` by fs[] >> simp[polyform_0]) >>
  pop_assum SUBST_ALL_TAC >>
  `0 < c ∧ c < a` by metis_tac[listTheory.MEM, is_polyform_ELthm] >>
  `b = a ** e * c + eval_poly a t` by fs[] >>
  `polyform a b ≠ []` by simp[polyform_EQ_NIL, IFF_ZERO_lt, ZERO_lt_ordEXP] >>
  `∃c' e' t'. polyform a b = (c',e')::t'`
    by metis_tac [listTheory.list_CASES, pairTheory.pair_CASES] >>
  `0 < c' ∧ c' < a` by metis_tac [is_polyform_CONS_E] >>
  `b = a ** e' * c' + eval_poly a t'` by fs[] >>
  `e' = e` by metis_tac [explemma, ordle_ANTISYM] >> pop_assum SUBST_ALL_TAC >>
  `c' = c` by metis_tac [coefflemma, ordle_ANTISYM] >> pop_assum SUBST_ALL_TAC>>
  `eval_poly a t = eval_poly a t'` by metis_tac [ordADD_RIGHT_CANCEL] >>
  qsuff_tac `t = t'` >- simp[] >>
  `eval_poly a t < b`
    by (`eval_poly a t < a ** e`
          by metis_tac [is_polyform_head_dominates_tail] >>
        `a ** e ≤ a ** e * c` by simp[IFF_ZERO_lt] >>
        `a ** e * c ≤ a ** e * c + eval_poly a t` by simp[] >>
        metis_tac [ordlte_TRANS, ordle_TRANS]) >>
  metis_tac [is_polyform_CONS_E]);

val polyform_eval_poly = store_thm(
  "polyform_eval_poly",
  ``1 < α ∧ is_polyform α β ⇒ (polyform α (eval_poly α β) = β)``,
  strip_tac >> match_mp_tac polyform_UNIQUE >> simp[]);

val CNF_nat = store_thm(
  "CNF_nat",
  ``CNF &n = if n = 0 then [] else [(&n,0)]``,
  rw[] >> match_mp_tac polyform_UNIQUE >> rw[is_polyform_def] >> decide_tac);

val _ = overload_on ("ordLOG", ``λb x. SND (HD (polyform b x))``)
val _ = overload_on ("olog", ``λx. ordLOG ω x``)
val ordLOG_correct = store_thm(
  "ordLOG_correct",
  ``1 < b ∧ 0 < x ⇒ ordEXP b (ordLOG b x) ≤ x ∧
    ∀a. ordLOG b x < a ⇒ x < ordEXP b a``,
  strip_tac >>
  `(polyform b x = []) ∨ ∃c e t. polyform b x = (c,e) :: t`
    by metis_tac [pairTheory.pair_CASES, listTheory.list_CASES]
  >- (pop_assum mp_tac >> fs[polyform_EQ_NIL] >> strip_tac >> fs[]) >>
  simp[] >>
  `is_polyform b (polyform b x) ∧ (x = eval_poly b (polyform b x))`
    by metis_tac [polyform_def] >>
  first_assum SUBST1_TAC >> simp[] >>
  `0 < c ∧ c < b ∧ is_polyform b t` by metis_tac[is_polyform_CONS_E] >>
  `c ≠ 0` by (strip_tac >> fs[]) >>
  conj_tac
  >- (match_mp_tac ordle_TRANS >> qexists_tac `b ** e * c` >> simp[]) >>
  rpt strip_tac >>
  (is_polyform_head_dominates_tail
     |> Q.INST [`a` |-> `b`, `c` |-> `1`, `e` |-> `a`, `t` |-> `polyform b x`]
     |> MP_TAC) >> simp[] >> disch_then match_mp_tac >>
  simp[is_polyform_def] >> metis_tac[]);

(* |- 0 < x ⇒ ω ** olog x ≤ x ∧ ∀a. olog x < a ⇒ x < ω ** a *)
val olog_correct = save_thm(
  "olog_correct",
  ordLOG_correct |> Q.INST [`b` |-> `ω`] |> SIMP_RULE (srw_ss()) []);



val _ = export_theory()
