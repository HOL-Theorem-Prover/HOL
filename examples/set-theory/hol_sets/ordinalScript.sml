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

val [ordlt_REFL, ordlt_TRANS, ordlt_WF0, ordlt_trichotomy,
     ordlt_ZERO0, ord_finite_ZERO0] =
    quotient.define_quotient_types_full
    {
     types = [{name = "ordinal", equiv = alphaise orderiso_equiv}],
     defs = map mk_def
       [("ordlt", ``orderlt : 'a inf wellorder -> 'a inf wellorder -> bool``),
        ("ord_ZERO", ``wZERO : 'a inf wellorder``),
        ("ord_finite", ``finite : 'a inf wellorder -> bool``)],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     respects = [alphaise orderlt_orderiso, alphaise finite_iso],
     poly_preserves = [],
     poly_respects = [],
     old_thms = [alphaise orderlt_REFL, alphaise orderlt_TRANS,
                 alphaise (REWRITE_RULE [relationTheory.WF_DEF] orderlt_WF),
                 alphaise orderlt_trichotomy, alphaise LT_wZERO,
                 alphaise finite_wZERO
                 ]}

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

val countable_thm = store_thm(
  "countable_thm",
  ``countable s <=> s ≼ univ(:num)``,
  simp[countable_def, cardleq_def]);

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

val csup_thm = store_thm(
  "csup_thm",
  ``countable (s : cord set) ==> ∀β. β < sup s ⇔ ∃δ. δ ∈ s ∧ β < δ``,
  simp[countable_def] >>
  metis_tac [sup_thm, cardleq_def, unitinf_univnum, cardeq_REFL,
             CARDEQ_CARDLEQ])

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

val ordle_ANTISYM = store_thm(
  "ordle_ANTISYM",
  ``α ≤ β ∧ β ≤ α ⇒ (α = β)``,
  metis_tac [ordlt_trichotomy]);

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

val ordleq0 = store_thm(
  "ordleq0",
  ``(x:'a ordinal) ≤ 0 ⇔ (x = 0)``,
  eq_tac >> simp[ordle_lteq]);
val _ = export_rewrites ["ordleq0"]

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

val IMAGE_cardleq_rwt = store_thm(
  "IMAGE_cardleq_rwt",
  ``s ≼ t ⇒ IMAGE f s ≼ t``,
  metis_tac [cardleq_TRANS, IMAGE_cardleq]);

val dclose_BIGUNION = store_thm(
  "dclose_BIGUNION",
  ``dclose s = BIGUNION (IMAGE preds s)``,
  dsimp[Once EXTENSION, dclose_def] >> metis_tac[]);

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

val ordle_TRANS = store_thm(
  "ordle_TRANS",
  ``∀x y z. (x:'a ordinal) ≤ y ∧ y ≤ z ⇒ x ≤ z``,
  metis_tac [ordlt_TRANS, ordle_lteq]);

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
    match_mp_tac sup_eq_max >> dsimp[] >> qexists_tac `a⁺` >> simp[] >>
    ntac 2 strip_tac >> first_x_assum match_mp_tac >>
    metis_tac [mklesup sup_thm]
  ])

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
                |> Q.SPEC `λap r. r + b`
                |> Q.SPEC `λa preds. sup preds`
                |> Q.GEN `b`
                |> CONV_RULE SKOLEM_CONV
                |> BETA_RULE
                |> SIMP_RULE (srw_ss()) [Once exists_C]
                |> SIMP_RULE (srw_ss()) [combinTheory.C_DEF])
val _ = export_rewrites ["ordMULT_def"]
val _ = overload_on ("*", ``ordMULT``)

val ordMULT_0R = store_thm(
  "ordMULT_0R",
  ``∀a:'a ordinal. a * 0 = 0``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE (λy. y * 0) (preds a) = {0}` >> simp[] >>
  simp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ DNF_ss ++ CONJ_ss) [] >> metis_tac[]);
val _ = export_rewrites ["ordMULT_0R"]

val ordMULT_1L = store_thm(
  "ordMULT_1L",
  ``1 * (a:'a ordinal) = a``,
  REWRITE_TAC [GSYM ORD_ONE] >> simp[]);
val _ = export_rewrites ["ordMULT_1L"]

val ordMULT_2L = store_thm(
  "ordMULT_2L",
  ``2 * (a:'a ordinal) = a + a``,
  `2 = 1⁺` by simp[] >> pop_assum SUBST1_TAC >> simp[]);

val ordMULT_1R = store_thm(
  "ordMULT_1R",
  ``∀a:'a ordinal. a * 1 = a``,
  ho_match_mp_tac simple_ord_induction >> simp[ADD1R] >>
  qx_gen_tac `a` >> strip_tac >>
  qsuff_tac `IMAGE (λy. y * 1) (preds a) = preds a`
  >- fs[sup_preds_omax_NONE] >>
  dsimp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) []);

val ord_CASES = store_thm(
  "ord_CASES",
  ``∀a. (a = 0) ∨ (∃a0. a = a0⁺) ∨ (0 < a ∧ islimit a)``,
  gen_tac >> Cases_on `a = 0` >- simp[] >>
  `0 < a` by metis_tac [ordlt_trichotomy, ordlt_ZERO] >>
  Cases_on `omax (preds a)` >> simp[] >>
  fs[preds_omax_SOME_SUC]);

val islimit_SUC = store_thm(
  "islimit_SUC",
  ``islimit b ∧ a < b ⇒ a⁺ < b``,
  fs[omax_NONE] >> metis_tac [ordlt_SUC_DISCRETE, ordlt_trichotomy, ordle_lteq])

val ordMULT_lt_MONO_L = store_thm(
  "ordMULT_lt_MONO_L",
  ``∀a b c:'a ordinal. a < b ∧ 0 < c ⇒ a * c < b * c``,
  qsuff_tac `∀b a c:'a ordinal. a < b ∧ 0 < c ⇒ a * c < b * c` >- metis_tac[]>>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (simp[ordlt_SUC_DISCRETE] >> qx_gen_tac `b` >> strip_tac >>
      map_every qx_gen_tac [`a`, `c`] >>
      Cases_on `a = b` >> simp[] >> strip_tac >>
      `a * c < b * c` by metis_tac[] >>
      `b * c < b * c + c` by simp[] >> metis_tac [ordlt_TRANS]) >>
  qx_gen_tac `b` >> strip_tac >> map_every qx_gen_tac [`a`, `c`] >>
  strip_tac >> simp[predimage_sup_thm] >>
  `∃d. a < d ∧ d < b`
    by metis_tac[sup_preds_omax_NONE, IN_preds, preds_inj_univ, sup_thm] >>
  metis_tac[]);

val ordMULT_le_MONO_L = store_thm(
  "ordMULT_le_MONO_L",
  ``∀a b c:'a ordinal. a ≤ b ⇒ a * c ≤ b * c``,
  simp[ordle_lteq] >> rpt strip_tac >> simp[] >>
  Cases_on `c = 0` >> simp[] >>
  `0 < c` by metis_tac [ordlt_ZERO, ordlt_trichotomy] >>
  metis_tac [ordMULT_lt_MONO_L])

val ordMULT_lt_MONO_L_EQN = store_thm(
  "ordMULT_lt_MONO_L_EQN",
  ``a * c < b * c <=> a < b ∧ 0 < c``,
  simp[EQ_IMP_THM, ordMULT_lt_MONO_L] >>
  Cases_on `0 < c` >- metis_tac [ordMULT_le_MONO_L] >> fs[]);
val _ = export_rewrites ["ordMULT_lt_MONO_L_EQN"]

val ordADD_le_MONO_L = store_thm(
  "ordADD_le_MONO_L",
  ``x ≤ y ⇒ x + z ≤ y + z``,
  simp[ordle_lteq, SimpL ``$==>``] >> simp[DISJ_IMP_THM, ordADD_weak_MONO]);

val ordMULT_le_MONO_R = store_thm(
  "ordMULT_le_MONO_R",
  ``∀a b c:'a ordinal. a ≤ b ⇒ c * a ≤ c * b``,
  qsuff_tac `∀c a b:'a ordinal. a ≤ b ⇒ c * a ≤ c * b` >- metis_tac[] >>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
      strip_tac >>
      `c * a + a ≤ c * a + b` by simp[] >>
      match_mp_tac ordle_TRANS >> qexists_tac `c * a + b` >> simp[] >>
      simp[ordADD_le_MONO_L]) >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >> strip_tac>>
  simp[predimage_sup_thm, impI] >> qx_gen_tac `d` >> strip_tac >>
  match_mp_tac ordle_TRANS >> qexists_tac `d * b` >> simp[] >>
  qsuff_tac `d * b ∈ IMAGE (λy. y * b) (preds c)`
  >- metis_tac [mklesup sup_thm, IMAGE_cardleq_rwt, preds_inj_univ] >>
  simp[] >> metis_tac[]);

val ordMULT_CANCEL_L = store_thm(
  "ordMULT_CANCEL_L",
  ``(x * z = y * z:'a ordinal) <=> (z = 0) ∨ (x = y)``,
  simp[EQ_IMP_THM, DISJ_IMP_THM] >> strip_tac >>
  Tactical.REVERSE (Cases_on `0 < z`) >- fs[] >>
  `x < y ∨ (x = y) ∨ y < x` by metis_tac [ordlt_trichotomy] >>
  metis_tac [ordMULT_lt_MONO_L_EQN, ordlt_REFL]);

val ordMULT_continuous0 =
  generic_continuity |> Q.INST [`f` |-> `λx. x * y`]
                     |> SIMP_RULE (srw_ss()) []

val ordMULT_continuous = store_thm(
  "ordMULT_continuous",
  ``∀s:'a ordinal set. s ≼ univ(:'a inf) ⇒
           (sup s * a = sup (IMAGE (λx. x * a) s))``,
  rpt strip_tac >> Cases_on `s = {}` >> simp[ordMULT_continuous0]);

val ordMULT_fromNat = store_thm(
  "ordMULT_fromNat",
  ``(&n : 'a ordinal) * &m = &(n * m)``,
  Induct_on `n` >> simp[arithmeticTheory.MULT_CLAUSES]);
val _ = export_rewrites ["ordMULT_fromNat"]

val omega_MUL_fromNat = store_thm(
  "omega_MUL_fromNat",
  ``0 < n ⇒ ω * &n = ω``,
  simp[omax_preds_omega] >> strip_tac >>
  match_mp_tac ordle_ANTISYM >> dsimp[predimage_sup_thm, lt_omega, impI] >>
  conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `m` >>
  qsuff_tac `&m < sup (IMAGE (λy. y * &n) (preds ω))` >- metis_tac[ordlt_REFL]>>
  dsimp[predimage_sup_thm, lt_omega] >>
  qexists_tac `m + 1` >> simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >>
  qsuff_tac `m ≤ m * n ∧ m * n < n + m * n` >- DECIDE_TAC >>
  simp[]);

val ordMULT_RDISTRIB = store_thm(
  "ordMULT_RDISTRIB",
  ``∀a b c:'a ordinal. (a + b) * c = a * c + b * c``,
  qsuff_tac `∀b a c. (a + b) * c = a * c + b * c` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordADD_ASSOC] >>
  qx_gen_tac `b` >> strip_tac >>
  `preds b ≠ {}` by (simp[EXTENSION] >> metis_tac[]) >>
  simp[ordADD_continuous, ordMULT_continuous, IMAGE_cardleq_rwt,
       preds_inj_univ] >>
  rpt strip_tac >> AP_TERM_TAC >> dsimp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [])

val ordMULT_ASSOC = store_thm(
  "ordMULT_ASSOC",
  ``∀a b c:'a ordinal. a * (b * c) = (a * b) * c``,
  ho_match_mp_tac simple_ord_induction >> simp[ordMULT_RDISTRIB] >>
  simp[ordMULT_continuous, IMAGE_cardleq_rwt, preds_inj_univ] >>
  rpt strip_tac >> AP_TERM_TAC >> dsimp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [])

val ordDIVISION0 = prove(
  ``∀a b:'a ordinal. 0 < b ⇒ ∃q r. a = q * b + r ∧ r < b``,
  rpt strip_tac >>
  qabbrev_tac `d = sup { c | c * b ≤ a }` >>
  `∀c. c * b ≤ a ⇒ c ≤ a`
     by (ntac 2 strip_tac >> match_mp_tac ordle_TRANS >>
         qexists_tac `c * b` >> simp[] >>
         simp[Once (GSYM ordMULT_1R), SimpR ``ordlt``] >>
         match_mp_tac ordMULT_le_MONO_R >>
         simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
         simp[] >> strip_tac >> fs[]) >>
  `∀α. α ∈ { c | c * b ≤ a } ⇒ α < a⁺`
    by (simp[ordlt_SUC_DISCRETE] >> metis_tac [ordle_lteq]) >>
  `∀α. α < d ⇔ ∃c. c * b ≤ a ∧ α < c`
    by (simp[Abbr`d`] >> pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
        simp[]) >>
  `d * b ≤ a`
    by (simp[Abbr`d`] >>
        `{ c | c * b ≤ a } ≼ univ(:'a inf)`
          by (`{ c | c * b ≤ a } ≼ preds a⁺`
                by simp[SUBSET_DEF, SUBSET_CARDLEQ] >>
              `preds a⁺ ≼ univ(:'a inf)` by simp[preds_inj_univ] >>
              metis_tac [cardleq_TRANS]) >>
        dsimp[ordMULT_continuous, sup_thm, IMAGE_cardleq_rwt, impI]) >>
  `∃r. d * b + r = a` by metis_tac [ordle_EXISTS_ADD] >>
  qsuff_tac `r < b` >- metis_tac[] >>
  spose_not_then strip_assume_tac >>
  `∃bb. b + bb = r` by metis_tac [ordle_EXISTS_ADD] >>
  `d⁺ * b + bb = a` by simp[GSYM ordADD_ASSOC] >>
  `∀c. c * b ≤ a ⇒ c ≤ d` by metis_tac [ordlt_REFL] >>
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
  ``∀a b q r. 0 < (b:'a ordinal) ∧ a = q*b + r ∧ r < b ⇒ a / b = q``,
  rpt strip_tac >>
  `a = a / b * b + a % b ∧ a % b < b` by metis_tac [ordDIVISION] >>
  `a / b < q ∨ a / b = q ∨ q < a / b` by metis_tac [ordlt_trichotomy] >| [
    `∃bb. (q = a/b + bb) ∧ 0 < bb`
      by metis_tac [ordlt_EXISTS_ADD, ordlt_trichotomy, ordlt_ZERO] >>
    `a = (a/b + bb) * b + r` by metis_tac[] >>
    `_ = a/b * b + bb * b + r` by metis_tac[ordMULT_RDISTRIB] >>
    `a % b = bb * b + r` by metis_tac [ordADD_ASSOC, ordADD_RIGHT_CANCEL] >>
    `bb * b + r < b` by metis_tac[] >>
    `b ≤ bb * b`
      by (simp_tac bool_ss [Once (GSYM ordMULT_1L), SimpR ``ordlt``] >>
          match_mp_tac ordMULT_le_MONO_L >>
          simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
          simp[] >> strip_tac >> fs[]) >>
    `b ≤ bb * b + r` by metis_tac [ordle_CANCEL_ADDR, ordADD_le_MONO_L,
                                   ordle_TRANS],

    `∃bb. q + bb = a/b ∧ 0 < bb`
      by metis_tac [ordlt_EXISTS_ADD, ordlt_trichotomy, ordlt_ZERO] >>
    `a = (q + bb) * b + a % b` by metis_tac[] >>
    `_ = q * b + bb * b + a % b` by simp[ordMULT_RDISTRIB] >>
    `r = bb * b + a % b` by metis_tac [ordADD_ASSOC, ordADD_RIGHT_CANCEL] >>
    `bb * b + a % b < b` by metis_tac[] >>
    `b ≤ bb * b`
      by (simp_tac bool_ss [Once (GSYM ordMULT_1L), SimpR ``ordlt``] >>
          match_mp_tac ordMULT_le_MONO_L >>
          simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
          simp[] >> strip_tac >> fs[]) >>
    `b ≤ bb * b + a % b`
      by metis_tac [ordle_CANCEL_ADDR, ordADD_le_MONO_L, ordle_TRANS]
  ]);

val ordMOD_UNIQUE = store_thm(
  "ordMOD_UNIQUE",
  ``∀a b q r. 0 < b ∧ a = q * b + r ∧ r < b ⇒ a % b = r``,
  rpt strip_tac >>
  `(a = a / b * b + a % b) ∧ a % b < b` by metis_tac [ordDIVISION] >>
  `a / b = q` by metis_tac [ordDIV_UNIQUE] >> pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `r' = a % b` >> fs[])

(* Exponentiation *)
val ordEXP_def = new_specification(
  "ordEXP_def", ["ordEXP"],
  ord_RECURSION |> INST_TYPE [beta |-> ``:'a ordinal``]
                |> Q.SPEC `1`
                |> Q.SPEC `λap r. a * r`
                |> Q.SPEC `λa preds. sup preds`
                |> Q.GEN `a`
                |> CONV_RULE SKOLEM_CONV
                |> BETA_RULE
                |> SIMP_RULE (srw_ss()) [FORALL_AND_THM])
val _ = export_rewrites ["ordEXP_def"]
val _ = overload_on ("**", ``ordEXP``)

val _ = export_rewrites ["ordMULT_1R"]
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
      qexists_tac `b * a ** x` >> simp[ordMULT_le_MONO_L, ordMULT_le_MONO_R]) >>
  qx_gen_tac `x` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  strip_tac >> simp[predimage_sup_thm, impI] >>
  qx_gen_tac `d` >> strip_tac >>
  `a ** d ≤ b ** d` by simp[] >>
  `b ** d ∈ IMAGE ($** b) (preds x)` by (simp[] >> metis_tac[]) >>
  metis_tac [mklesup sup_thm, ordle_TRANS, IMAGE_cardleq_rwt, preds_inj_univ]);


val _ = export_theory()
