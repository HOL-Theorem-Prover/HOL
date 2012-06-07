open HolKernel Parse boolLib bossLib
open lcsymtacs
open boolSimps

open set_relationTheory pred_setTheory cardinalTheory
open wellorderTheory

val _ = new_theory "ordinal"



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
  ``wellorder { (x,y) | (x = y) \/ ordlt x y }``,
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
    by metis_tac [elsOf_cardeq_iso] >>
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
val _ = add_numeral_form (#"o", SOME "fromNat")

(* prints as 0 ≤ α *)
val ordlt_ZERO = store_thm(
  "ordlt_ZERO",
  ``¬(α < 0)``,
 simp[fromNat_def] >> DEEP_INTRO_TAC oleast_intro >> simp[])
val _ = export_rewrites ["ordlt_ZERO"]

val EMPTY_CARDLEQ = store_thm(
  "EMPTY_CARDLEQ",
  ``{} ≼ t``,
  simp[cardleq_def, INJ_EMPTY]);  (* export_rewrites for pred_set *)
val _ = export_rewrites ["EMPTY_CARDLEQ"]

val FINITE_CLE_INFINITE = store_thm(
  "FINITE_CLE_INFINITE",
  ``FINITE s ∧ INFINITE t ==> s ≼ t``,
  qsuff_tac `INFINITE t ⇒ ∀s. FINITE s ⇒ s ≼ t` >- metis_tac[] >>
  strip_tac >> Induct_on `FINITE` >> conj_tac >- simp[] >>
  simp[cardleq_def] >> gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
                              (Q.X_CHOOSE_THEN `f` assume_tac)) >>
  qx_gen_tac `e` >> strip_tac >>
  `FINITE (IMAGE f s)` by simp[] >>
  `∃y. y ∈ t ∧ y ∉ IMAGE f s` by metis_tac [IN_INFINITE_NOT_FINITE] >>
  qexists_tac `λx. if x = e then y else f x` >>
  fs[INJ_DEF] >> asm_simp_tac (srw_ss() ++ DNF_ss) [] >> rw[] >> metis_tac[])

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

val csup_thm = store_thm(
  "csup_thm",
  ``countable (s : cord set) ==>
      (∀β. β < sup s ⇔ ∃δ. δ ∈ s ∧ β < δ)``,
  strip_tac >>
  qabbrev_tac `bpreds = BIGUNION (IMAGE preds s)` >>
  `countable bpreds`
       by (qunabbrev_tac `bpreds` >> match_mp_tac bigunion_countable >>
           asm_simp_tac (srw_ss() ++ DNF_ss) [image_countable,
                                              cord_countable_preds]) >>
  `bpreds <> univ(:cord)` by metis_tac [univ_cord_uncountable] >>
  `downward_closed bpreds`
     by (asm_simp_tac (srw_ss() ++ DNF_ss)
                      [Abbr`bpreds`, downward_closed_def] >>
         metis_tac [ordlt_TRANS]) >>
  `∃α. preds α = bpreds`
     by (mp_tac (INST_TYPE [alpha |-> ``:unit``] preds_bij) >>
         simp[BIJ_DEF, SURJ_DEF, SPECIFICATION]) >>
  `sup s = α`
     by (asm_simp_tac bool_ss [sup_def] >>
         DEEP_INTRO_TAC oleast_intro >> conj_tac
           >- (fs[EXTENSION] >> metis_tac[]) >>
         simp[] >> qx_gen_tac `α'` >> strip_tac >>
         qsuff_tac `α' ≤ α ∧ α ≤ α'` >- metis_tac [ordlt_trichotomy] >>
         rpt strip_tac >| [
           `α ∈ bpreds` by res_tac >> metis_tac [IN_preds, ordlt_REFL],
           rw[] >> fs[]
         ]) >>
  simp[] >>
  qx_gen_tac `β` >> rpt strip_tac >>
  `β < α ⇔ β ∈ bpreds` by metis_tac [IN_preds] >>
  simp[Abbr`bpreds`] >> metis_tac [IN_preds]);

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
  asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
  qx_gen_tac `β` >> strip_tac >>
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

val islimit_def = Define`
  islimit α <=> (omax (preds α) = NONE)
`;

val sup_preds_omax_NONE = store_thm(
  "sup_preds_omax_NONE",
  ``(omax (preds α) = NONE) ⇔ (sup (preds α) = α)``,
  simp[omax_NONE, sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  simp_tac(srw_ss() ++ DNF_ss) [DECIDE ``¬p ∨ q <=> (p ==> q)``] >>
  qexists_tac `α` >> conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `γ` >> strip_tac >> Tactical.REVERSE eq_tac
  >- (rw[] >> metis_tac[]) >>
  strip_tac >> qsuff_tac `γ ≤ α ∧ α ≤ γ` >- metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_TRANS, ordlt_REFL]);

val islimit_0 = store_thm(
  "islimit_0",
  ``islimit 0``,
  simp[islimit_def]);
val _ = export_rewrites ["islimit_0"]

fun mklesup th =
    th |> UNDISCH_ALL |> Q.SPEC `sup s`
       |> SIMP_RULE (srw_ss()) []
       |> REWRITE_RULE [DECIDE ``¬p ∨ q <=> (p ==> q)``]
       |> DISCH_ALL
(* |- countable s ⇒ ∀δ. δ ∈ s ⇒ δ ≤ sup s *)
val csup_lesup = save_thm("csup_lesup", mklesup csup_thm)

fun mksuple th =
    th |> UNDISCH_ALL |> Q.SPEC `β` |> AP_TERM ``$~``
       |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
       |> REWRITE_RULE [DECIDE ``¬p ∨ q <=> (p ==> q)``]
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
            asm_simp_tac (srw_ss() ++ DNF_ss)
                         [DECIDE ``¬p ∨ q <=> (p ⇒ q)``] >>
            qexists_tac `α` >> conj_tac >- rw[ordle_lteq] >>
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
  Induct >- (Cases >> simp[SimpRHS, fromNat_def]) >>
  Cases >- simp[SimpLHS, fromNat_def] >> simp[fromNat_def]);
val _ = export_rewrites ["fromNat_11"]

val ordlt_fromNat = store_thm(
  "ordlt_fromNat",
  ``∀n (x:α ordinal). x < &n <=> ∃m. (x = &m) ∧ m < n``,
  Induct >>
  asm_simp_tac (srw_ss() ++ DNF_ss)
               [fromNat_def, ordlt_SUC_DISCRETE,
                DECIDE ``m < SUC n <=> m < n ∨ (m = n)``]);

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
val _ = export_rewrites ["fromNat_lt_omega"]

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
         !α. α ≠ 0 ∧ (omax (preds α) = NONE) ==>
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
  simp[relationTheory.WFREC_THM, ordlt_WF, restrict_away])

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
  ``∀α. 0o + α = α``,
  ho_match_mp_tac ord_induction >> gen_tac >>
  Cases_on `α = 0` >- simp[] >>
  Cases_on `omax (preds α)`
  >- (simp[ordADD_def] >> strip_tac >>
      `IMAGE ($+ 0) (preds α) = preds α`
         by (rpt (asm_simp_tac (srw_ss() ++ CONJ_ss)[EXTENSION])) >>
      fs[sup_preds_omax_NONE]) >>
  fs[preds_omax_SOME_SUC]);
val _ = export_rewrites ["ordADD_0L"]

val _ = export_theory()
