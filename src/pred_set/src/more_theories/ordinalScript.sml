open HolKernel Parse boolLib bossLib

open boolSimps optionTheory set_relationTheory pred_setTheory;

open wellorderTheory cardinalTheory topologyTheory;

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
  allOrds = mkWO { (x,y) | (x = y) \/ ordlt x y }
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
    Cases_on `b IN elsOf (wobound (mkOrdinal w) allOrds)` >> simp[] >>
    pop_assum mp_tac >> simp[elsOf_wobound, wobound2] >>
    simp[WIN_allOrds] >> rpt strip_tac >>
    fs[ordlt_mkOrdinal] >>
    first_x_assum (qspecl_then [`ordinal_REP b`, `w`] mp_tac) >>
    simp[mkOrdinal_REP] >> strip_tac >> res_tac >> fs[mkOrdinal_REP] >>
    metis_tac [orderiso_TRANS, orderiso_SYM, orderlt_iso_REFL],
    pop_assum mp_tac >> simp[orderlt_def] >> qx_gen_tac `e` >>
    Cases_on `e IN elsOf w` >> simp[] >> strip_tac >>
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
  qpat_x_assum `x = y` mp_tac >> rw[EXTENSION, preds_def] >>
  metis_tac [ordlt_REFL]);
val _ = export_rewrites ["preds_11"]

Theorem ordlt_preds_mono:
  a < b ==> preds a <<= preds b
Proof
  strip_tac >> irule CARD_LE_SUBSET >> simp[SUBSET_DEF] >>
  metis_tac[ordlt_TRANS]
QED

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

Theorem cardeq_ordinals_exist:
  (s:'b set) <<= univ(:num + 'a) ==>
  ?a:'a ordinal. preds a =~ s
Proof
  strip_tac >>
  qspec_then ‘s’ (qx_choose_then ‘w1’ assume_tac) allsets_wellorderable >>
  gvs[cardleq_def] >>
  drule_then (qx_choose_then ‘w2’ assume_tac) elsOf_cardeq_iso>>
  qspec_then ‘w2’ assume_tac wellorder_ordinal_isomorphism >>
  qexists_tac ‘mkOrdinal w2’ >>
  simp[preds_wobound] >> gs[orderiso_thm, cardeq_def] >>
  metis_tac[BIJ_SYM, BIJ_COMPOSE]
QED

val preds_inj_univ = store_thm(
  "preds_inj_univ",
  ``preds (ord:'a ordinal) <<= univ(:'a inf)``,
  simp[preds_wobound] >>
  qspec_then `ordinal_REP ord` mp_tac wellorder_ordinal_isomorphism >>
  simp[mkOrdinal_REP] >> strip_tac >> imp_res_tac orderiso_SYM >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss())[orderiso_thm]) >>
  simp[cardleq_def] >> qexists_tac `f` >>
  fs[BIJ_DEF, INJ_DEF]);

val _ = type_abbrev("cord", ``:unit ordinal``)

val unitinf_univnum = store_thm(
  "unitinf_univnum",
  ``univ(:unit inf) =~ univ(:num)``,
  simp[cardeq_def] >>
  qexists_tac `\s. case s of INL n => n + 1 | INR () => 0` >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, EXISTS_SUM, FORALL_SUM] >>
  Cases >> simp[arithmeticTheory.ADD1] >>
  qexists_tac `()` >> simp[])

val cord_countable_preds = store_thm(
  "cord_countable_preds",
  ``countable (preds (ord:cord))``,
  simp[countable_thm] >>
  qsuff_tac `preds ord <<= univ(:unit inf)`
     >- metis_tac [unitinf_univnum, CARDEQ_CARDLEQ, cardeq_REFL] >>
  simp[preds_inj_univ]);

val univ_ord_greater_cardinal = store_thm(
  "univ_ord_greater_cardinal",
  ``~(univ(:'a ordinal) <<= univ(:'a inf))``,
  strip_tac >>
  `elsOf allOrds = univ(:'a ordinal)` by simp[elsOf_allOrds] >>
  `elsOf (allOrds:'a ordinal wellorder) <<= univ(:'a inf)`
      by simp[] >>
  `?w:'a inf wellorder. orderiso (allOrds:'a ordinal wellorder) w`
    by metis_tac [elsOf_cardeq_iso, cardleq_def] >>
  `orderiso w (wobound (mkOrdinal w) allOrds)`
    by simp[wellorder_ordinal_isomorphism] >>
  `mkOrdinal w IN elsOf allOrds` by simp[elsOf_allOrds] >>
  `orderlt (allOrds:'a ordinal wellorder) (allOrds:'a ordinal wellorder)`
     by metis_tac [orderlt_def, orderiso_TRANS] >>
  fs[orderlt_REFL]);

val univ_cord_uncountable = store_thm(
  "univ_cord_uncountable",
  ``~countable (univ(:cord))``,
  simp[countable_thm] >> strip_tac >>
  `univ(:cord) <<= univ(:unit inf)`
     by metis_tac [CARDEQ_CARDLEQ, cardeq_REFL, unitinf_univnum] >>
  fs[univ_ord_greater_cardinal]);

val ordle_lteq = store_thm(
  "ordle_lteq",
  ``(a:'a ordinal) <= b <=> a < b \/ (a = b)``,
  metis_tac [ordlt_trichotomy, ordlt_REFL, ordlt_TRANS])

val ordle_ANTISYM = store_thm(
  "ordle_ANTISYM",
  ``a <= b /\ b <= a ==> (a = b)``,
  metis_tac [ordlt_trichotomy]);

val ordle_TRANS = store_thm(
  "ordle_TRANS",
  ``!x y z. (x:'a ordinal) <= y /\ y <= z ==> x <= z``,
  metis_tac [ordlt_TRANS, ordle_lteq]);

val ordlet_TRANS = store_thm(
  "ordlet_TRANS",
  ``!x y z. (x:'a ordinal) <= y /\ y < z ==> x < z``,
  metis_tac [ordle_lteq, ordlt_TRANS]);
val ordlte_TRANS = store_thm(
  "ordlte_TRANS",
  ``!x y z. (x:'a ordinal) < y /\ y <= z ==> x < z``,
  metis_tac [ordle_lteq, ordlt_TRANS]);

val oleast_def = Define`
  $oleast (P:'a ordinal -> bool) = @x. P x /\ !y. y < x ==> ~P y
`;

val _ = set_fixity "oleast" Binder

val oleast_intro = store_thm(
  "oleast_intro",
  ``!Q P. (?a. P a) /\ (!a. (!b. b < a ==> ~ P b) /\ P a ==> Q a) ==>
          Q ($oleast P)``,
  rw[oleast_def] >> SELECT_ELIM_TAC >> conj_tac >-
    (match_mp_tac ordlt_WF0 >> metis_tac[]) >>
  rw[]);

val ordSUC_def = Define`
  ordSUC a = oleast b. a < b
`
val _ = overload_on ("TC", ``ordSUC``)

val fromNat_def = Define`
  (fromNat 0 = oleast a. T) /\
  (fromNat (SUC n) = ordSUC (fromNat n))
`;
val fromNat_SUC = save_thm("fromNat_SUC", fromNat_def |> CONJUNCT2)
val _ = export_rewrites ["fromNat_SUC"]

val _ = add_numeral_form (#"o", SOME "fromNat")

(* prints as 0 <= a *)
val ordlt_ZERO = store_thm(
  "ordlt_ZERO",
  ``~(a < 0)``,
 simp[fromNat_def] >> DEEP_INTRO_TAC oleast_intro >> simp[])
val _ = export_rewrites ["ordlt_ZERO"]

val preds_surj = save_thm(
  "preds_surj",
  preds_bij |> SIMP_RULE (srw_ss()) [BIJ_DEF] |> CONJUNCT2
            |> SIMP_RULE (srw_ss()) [SURJ_DEF] |> CONJUNCT2
            |> REWRITE_RULE [SPECIFICATION]);

val no_maximal_ordinal = store_thm(
  "no_maximal_ordinal",
  ``!a. ?b. a < b``,
  simp[preds_lt_PSUBSET] >> gen_tac >>
  qabbrev_tac `P = preds a UNION {a}` >>
  `a NOTIN preds a` by simp[ordlt_REFL] >>
  `P <> univ(:'a ordinal)`
     by (strip_tac >>
         qsuff_tac `P <<= univ(:'a inf)` >-
           metis_tac [univ_ord_greater_cardinal] >>
         pop_assum (K ALL_TAC) >>
         Cases_on `FINITE P` >- simp[FINITE_CLE_INFINITE] >>
         `P = a INSERT preds a` by metis_tac [INSERT_SING_UNION,UNION_COMM] >>
         `INFINITE (preds a)` by fs[] >>
         `P =~ preds a` by metis_tac [cardeq_INSERT] >>
         metis_tac [CARDEQ_CARDLEQ, cardeq_REFL, preds_inj_univ]) >>
  `downward_closed P` by (simp[Abbr`P`, downward_closed_def] >>
                          metis_tac [ordlt_TRANS]) >>
  `?b. preds b = P` by metis_tac [preds_surj] >>
  qexists_tac `b` >> simp[Abbr`P`] >>
  simp[PSUBSET_DEF, EXTENSION] >> metis_tac [ordlt_REFL]);

val ordlt_SUC = store_thm(
  "ordlt_SUC",
  ``a < ordSUC a``,
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- metis_tac[no_maximal_ordinal] >> simp[]);
val _ = export_rewrites ["ordlt_SUC"]

val ordSUC_ZERO = store_thm(
  "ordSUC_ZERO",
  ``ordSUC a <> 0``,
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- metis_tac [ordlt_SUC] >>
  rpt strip_tac >> fs[]);
val _ = export_rewrites ["ordSUC_ZERO"]

val ordlt_DISCRETE1 = store_thm(
  "ordlt_DISCRETE1",
  ``~(a < b /\ b < ordSUC a)``,
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac >-
  metis_tac [ordlt_SUC] >> metis_tac [ordle_lteq]);

val ordlt_SUC_DISCRETE = store_thm(
  "ordlt_SUC_DISCRETE",
  ``a < ordSUC b <=> a < b \/ (a = b)``,
  Tactical.REVERSE eq_tac >- metis_tac [ordlt_TRANS, ordlt_SUC] >>
  metis_tac [ordlt_trichotomy, ordlt_DISCRETE1]);

val ordSUC_MONO = store_thm(
  "ordSUC_MONO",
  ``a^+ < b^+ <=> a < b``,
  eq_tac >> spose_not_then strip_assume_tac
  >- (fs[ordlt_SUC_DISCRETE]
      >- (`(a = b) \/ b < a` by metis_tac [ordlt_trichotomy] >>
          metis_tac [ordlt_TRANS, ordlt_REFL, ordlt_SUC]) >>
      rw[] >> fs[ordlt_SUC]) >>
  fs[ordlt_SUC_DISCRETE] >>
  `b < a^+` by metis_tac [ordlt_trichotomy] >>
  fs[ordlt_SUC_DISCRETE] >> metis_tac [ordlt_TRANS, ordlt_REFL])
val _ = export_rewrites ["ordSUC_MONO"]

val ordSUC_11 = store_thm(
  "ordSUC_11",
  ``(a^+ = b^+) <=> (a = b)``,
  simp[EQ_IMP_THM] >> strip_tac >> spose_not_then assume_tac >>
  `a < b \/ b < a` by metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_REFL, ordSUC_MONO]);
val _ = export_rewrites ["ordSUC_11"]

val sup_def = Define`
  sup ordset = oleast a. a NOTIN BIGUNION (IMAGE preds ordset)
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
            |> CONV_RULE (RAND_CONV (RENAME_VARS_CONV ["a"])))

Theorem sup_thm:
  (s: 'a ordinal set) <<= univ(:'a inf) ==>
  !a. a < sup s <=> ?b. b IN s /\ a < b
Proof
  strip_tac >>
  qabbrev_tac `apreds = BIGUNION (IMAGE preds s)` >>
  `apreds <<= univ(:'a inf)`
    by (qunabbrev_tac `apreds` >> match_mp_tac CARD_BIGUNION >>
        dsimp[preds_inj_univ] >> metis_tac [cardleq_TRANS, IMAGE_cardleq]) >>
  `apreds <> univ(:'a ordinal)` by metis_tac [univ_ord_greater_cardinal] >>
  `downward_closed apreds`
    by (dsimp[Abbr`apreds`, downward_closed_def] >>
        metis_tac[ordlt_TRANS]) >>
  `?a. preds a = apreds`
    by (mp_tac preds_bij >> simp[BIJ_DEF, SURJ_DEF, SPECIFICATION]) >>
  `sup s = a`
    by (asm_simp_tac bool_ss [sup_def] >>
        DEEP_INTRO_TAC oleast_intro >> conj_tac
        >- (fs[EXTENSION] >> metis_tac[]) >>
        Q.RM_ABBREV_TAC ‘apreds’ >>
        simp[] >> qx_gen_tac `a'` >> strip_tac >>
        qsuff_tac `a' <= a /\ a <= a'` >- metis_tac [ordlt_trichotomy] >>
        rpt strip_tac >| [
          `a IN apreds` by res_tac >> metis_tac [IN_preds, ordlt_REFL],
          rw[] >> fs[]
        ]) >>
  simp[] >>
  qx_gen_tac `b` >> rpt strip_tac >>
  `b < a <=> b IN apreds` by metis_tac [IN_preds] >>
  simp[Abbr`apreds`] >> metis_tac [IN_preds]
QED

val suple_thm = store_thm(
  "suple_thm",
  ``!b s:'a ordinal set. s <<= univ(:'a inf) /\ b IN s ==> b <= sup s``,
  metis_tac [sup_thm, ordlt_REFL]);

val sup_eq_sup = store_thm(
  "sup_eq_sup",
  ``(s1:'a ordinal set) <<= univ(:'a inf) /\
    (s2:'a ordinal set) <<= univ(:'a inf) /\
    (!a. a IN s1 ==> ?b. b IN s2 /\ a <= b) /\
    (!b. b IN s2 ==> ?a. a IN s1 /\ b <= a) ==> (sup s1 = sup s2)``,
  strip_tac >> match_mp_tac ordle_ANTISYM >> simp[sup_thm] >>
  metis_tac [suple_thm, ordle_TRANS]);

val Unum_cle_Uinf = store_thm(
  "Unum_cle_Uinf",
  ``univ(:num) <<= univ(:'a inf)``,
  simp[cardleq_def] >> qexists_tac `INL` >> simp[INJ_INL]);

val csup_thm = store_thm(
  "csup_thm",
  ``countable (s : 'a ordinal set) ==> !b. b < sup s <=> ?d. d IN s /\ b < d``,
  simp[countable_thm] >>
  metis_tac [sup_thm, cardleq_def, Unum_cle_Uinf, cardleq_TRANS])

val predimage_sup_thm = store_thm(
  "predimage_sup_thm",
  ``!b:'a ordinal.
          b < sup (IMAGE f (preds (a:'a ordinal))) <=> ?d. d < a /\ b < f d``,
  match_mp_tac (sup_thm |> Q.INST [`s` |-> `IMAGE f (preds (a:'b ordinal))`]
                        |> SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  metis_tac [cardleq_TRANS, IMAGE_cardleq, preds_inj_univ]);

val impI = DECIDE ``~p \/ q <=> (p ==> q)``

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
  predimage_suplt_ELIM |> Q.INST [`f` |-> `\x.x`]
                       |> SIMP_RULE (srw_ss()) []);

val sup_EMPTY = store_thm(
  "sup_EMPTY",
  ``sup {} = 0``,
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  qx_gen_tac `a` >> disch_then (qspec_then `0` mp_tac) >>
  simp[ordle_lteq]);
val _ = export_rewrites ["sup_EMPTY"]

val sup_SING = store_thm(
  "sup_SING",
  ``sup {a} = a``,
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac >-
    (qexists_tac `a` >> simp[]) >>
  simp[] >> qx_gen_tac `b` >> rw[ordle_lteq] >>
  metis_tac [ordlt_REFL]);
val _ = export_rewrites ["sup_SING"]

val sup_preds_SUC = store_thm(
  "sup_preds_SUC",
  ``sup (preds a^+) = a``,
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac >-
    (qsuff_tac `?b. !x. b IN preds x ==> a^+ <= x ` >- metis_tac[] >>
     simp[] >> qexists_tac `a^+` >> simp[ordle_lteq]) >>
  qx_gen_tac `b` >> simp_tac (srw_ss() ++ DNF_ss) [] >>
  strip_tac >>
  `!d. b < d ==> a^+ <= d` by metis_tac [IN_preds] >>
  qsuff_tac `b <= a /\ a <= b` >- metis_tac [ordlt_trichotomy] >>
  rpt strip_tac
  >- (`?x. a < x /\ x < a^+` by metis_tac [] >>
      fs[ordlt_SUC_DISCRETE] >> metis_tac [ordlt_REFL, ordlt_TRANS]) >>
  res_tac >> fs[ordlt_SUC]);

val _ = overload_on ("countableOrd", ``\a. countable(preds a)``)

val preds_ordSUC = store_thm(
  "preds_ordSUC",
  ``preds a^+ = a INSERT preds a``,
  simp[EXTENSION, ordlt_SUC_DISCRETE] >> metis_tac[]);

val countableOrds_dclosed = store_thm(
  "countableOrds_dclosed",
  ``a < b /\ countableOrd b ==> countableOrd a``,
  strip_tac >>
  `preds a SUBSET preds b` by metis_tac [preds_lt_PSUBSET, PSUBSET_DEF] >>
  metis_tac[subset_countable]);

val omax_def = Define`
  omax (s : 'a ordinal set) =
    some a. maximal_elements s { (x,y) | x <= y } = {a}
`;

val omax_SOME = store_thm(
  "omax_SOME",
  ``(omax s = SOME a) <=> a IN s /\ !b. b IN s ==> b <= a``,
  simp[omax_def] >> DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  >- (qx_gen_tac `b` >> simp[maximal_elements_def, EXTENSION] >>
      strip_tac >> eq_tac
      >- (strip_tac >> simp[] >> conj_tac >- metis_tac[] >>
          qx_gen_tac `c` >> rpt strip_tac >>
          metis_tac [ordlt_REFL, ordle_lteq]) >>
      metis_tac[]) >>
  simp[EXTENSION, maximal_elements_def] >> strip_tac >> Cases_on `a IN s` >>
  simp[] >> first_assum (qspec_then `a` mp_tac) >>
  disch_then (Q.X_CHOOSE_THEN `b` strip_assume_tac) >>
  Cases_on `b = a`
  >- (qpat_x_assum `P /\ Q <=/=> R` mp_tac >> simp[] >> metis_tac [ordle_lteq]) >>
  fs[] >> metis_tac []);

val omax_NONE = store_thm(
  "omax_NONE",
  ``(omax s = NONE) <=> !a. a IN s ==> ?b. b IN s /\ a < b``,
  simp[omax_def] >> DEEP_INTRO_TAC some_intro >>
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
  ``(x:'a ordinal) <= 0 <=> (x = 0)``,
  eq_tac >> simp[ordle_lteq]);
val _ = export_rewrites ["ordleq0"]

val preds_EQ_EMPTY = store_thm(
  "preds_EQ_EMPTY",
  ``preds x = {} <=> x = 0``,
  simp[EQ_IMP_THM] >> simp[EXTENSION] >>
  disch_then (qspec_then `0` mp_tac) >> simp[]);
val _ = export_rewrites ["preds_EQ_EMPTY"]

val omax_sup = store_thm(
  "omax_sup",
  ``(omax s = SOME a) ==> (sup s = a)``,
  simp[omax_SOME, sup_def] >> strip_tac >>
  DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac
  >- (qsuff_tac `?b. !c. b IN preds c ==> c NOTIN s` >- metis_tac[] >>
      simp[] >> metis_tac[]) >>
  dsimp [] >> qx_gen_tac `b` >> strip_tac >>
  `!c. b IN preds c ==> c NOTIN s` by metis_tac[] >>
  fs [] >> qsuff_tac `a <= b /\ b <= a` >- metis_tac [ordlt_trichotomy] >>
  metis_tac[]);

val preds_omax_SOME_SUC = store_thm(
  "preds_omax_SOME_SUC",
  ``(omax (preds a) = SOME b) <=> (a = b^+)``,
  simp[omax_SOME] >> eq_tac >> strip_tac
  >- (qsuff_tac `a <= b^+ /\ b^+ <= a` >- metis_tac [ordlt_trichotomy] >>
      rpt strip_tac >- metis_tac [ordlt_SUC] >>
      metis_tac [ordlt_SUC_DISCRETE, ordlt_TRANS, ordlt_REFL]) >>
  simp[ordlt_SUC_DISCRETE, ordle_lteq]);

Theorem omax_preds_SUC[simp]: omax (preds a^+) = SOME a
Proof metis_tac [preds_omax_SOME_SUC]
QED

val simple_ord_induction = store_thm(
  "simple_ord_induction",
  ``!P. P 0 /\ (!a. P a ==> P a^+) /\
        (!a. (omax (preds a) = NONE) /\ 0 < a /\ (!b. b < a ==> P b) ==> P a) ==>
        !a. P a``,
  gen_tac >> strip_tac >>
  ho_match_mp_tac ord_induction >> qx_gen_tac `a` >>
  Cases_on `a = 0` >> simp[] >>
  `(omax (preds a) = NONE) \/ ?a0. omax (preds a) = SOME a0`
    by metis_tac [option_CASES]
  >- (`0 < a` by metis_tac [ordlt_ZERO, ordle_lteq] >> metis_tac[]) >>
  fs[preds_omax_SOME_SUC]);

val _ = overload_on ("islimit", ``\a:'a ordinal. omax (preds a) = NONE``)

val sup_preds_omax_NONE = store_thm(
  "sup_preds_omax_NONE",
  ``(omax (preds a) = NONE) <=> (sup (preds a) = a)``,
  simp[omax_NONE, sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  simp_tac(srw_ss() ++ DNF_ss) [impI] >>
  qexists_tac `a` >> conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `c` >> strip_tac >> Tactical.REVERSE eq_tac
  >- (rw[] >> metis_tac[]) >>
  strip_tac >> qsuff_tac `c <= a /\ a <= c` >- metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_TRANS, ordlt_REFL]);

Theorem preds_nat:
  preds (&n) = IMAGE fromNat (count n)
Proof
  Induct_on ‘n’ >> simp[preds_ordSUC, COUNT_SUC]
QED

Theorem omax_INSERT:
  omax (x INSERT y) = if (!e. e IN y ==> e <= x) then SOME x
                      else omax y
Proof
  Cases_on‘omax y’ >>
  gs[omax_SOME, omax_NONE, AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM,
     RIGHT_AND_OVER_OR, EXISTS_OR_THM]
  >- metis_tac[] >>
  rename [‘_ \/ _ /\ a <= b’] >> Cases_on ‘b <= a’
  >- metis_tac[ordle_TRANS] >> gs[] >> metis_tac[ordle_lteq]
QED

Theorem FINITE_omax_IS_SOME:
  s <> {} /\ FINITE s ==> ?a. omax s = SOME a
Proof
  Induct_on ‘FINITE’ >> simp[omax_INSERT, AllCaseEqs(), EXISTS_OR_THM] >>
  rw[] >> simp[PULL_EXISTS] >> Cases_on ‘s = {}’ >> simp[] >>
  gs[omax_SOME] >>
  Cases_on ‘e < a’ >- metis_tac[] >>
  metis_tac[ordle_TRANS]
QED

Theorem fromNat_11[simp]:
  !x y. (&x:'a ordinal = &y) = (x = y)
Proof
  Induct >- (Cases >> simp[]) >> Cases >> simp[]
QED

Theorem FINITE_preds:
  FINITE (preds a) <=> ?n. a = &n
Proof
  simp[EQ_IMP_THM, PULL_EXISTS, preds_nat] >>
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  simp[preds_ordSUC] >> rw[] >> gs[]
  >- simp[GSYM fromNat_SUC, Excl "fromNat_SUC"] >>
  ‘preds a <> {}’ by (strip_tac >> gs[]) >>
  drule_all FINITE_omax_IS_SOME >> simp[]
QED

val dclose_def = Define`dclose s = { x:'a ordinal | ?y. y IN s /\ x < y }`;

val preds_sup = store_thm(
  "preds_sup",
  ``s <<= univ(:'a inf) ==> (preds (sup s:'a ordinal) = dclose s)``,
  simp[EXTENSION, sup_thm, dclose_def]);

fun mklesup th =
    th |> UNDISCH_ALL |> Q.SPEC `sup s`
       |> SIMP_RULE (srw_ss()) [] |> REWRITE_RULE [impI] |> DISCH_ALL
(* |- countable s ==> !d. d IN s ==> d <= sup s *)
val csup_lesup = save_thm("csup_lesup", mklesup csup_thm)

fun mksuple th =
    th |> UNDISCH_ALL |> Q.SPEC `b` |> AP_TERM ``$~``
       |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
       |> REWRITE_RULE [impI]
       |> DISCH_ALL

val csup_suple = save_thm("csup_suple", mksuple csup_thm)

val preds_sup_thm = store_thm(
  "preds_sup_thm",
  ``downward_closed s /\ s <> univ(:'a ordinal) ==>
    !b. b < sup s <=> ?d. d IN s /\ b < d``,
  strip_tac >>
  qspec_then `s` mp_tac preds_surj >> simp[] >>
  disch_then (Q.X_CHOOSE_THEN `a` ASSUME_TAC) >>
  `(omax s = NONE) \/ ?b. omax s = SOME b` by (Cases_on `omax s` >> simp[])
  >- (`sup s = a`
        by (simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >>
            dsimp[impI] >> qexists_tac `a` >> conj_tac >- rw[ordle_lteq] >>
            qx_gen_tac `b` >> rw[] >>
            qsuff_tac `b <= a /\ a <= b` >- metis_tac [ordlt_trichotomy] >>
            rpt strip_tac >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
            fs[omax_NONE] >> metis_tac[]) >>
      pop_assum SUBST1_TAC >> rw[] >> fs[omax_NONE] >>
      metis_tac[ordlt_TRANS]) >>
  `a = b^+` by (rw[] >> fs[preds_omax_SOME_SUC]) >> qx_gen_tac `d` >> rw[] >>
  simp[sup_preds_SUC] >> eq_tac >- (strip_tac >> qexists_tac `b` >> simp[]) >>
  simp[ordlt_SUC_DISCRETE] >>
  disch_then (Q.X_CHOOSE_THEN `c` strip_assume_tac) >- metis_tac[ordlt_TRANS] >>
  rw[]);

val preds_lesup = save_thm("preds_lesup", mklesup preds_sup_thm)
val preds_suple = save_thm("preds_suple", mksuple preds_sup_thm)

val ordlt_fromNat = store_thm(
  "ordlt_fromNat",
  ``!n (x:'a ordinal). x < &n <=> ?m. (x = &m) /\ m < n``,
  Induct >>
  dsimp [ordlt_SUC_DISCRETE, DECIDE ``m < SUC n <=> m < n \/ (m = n)``]);

val fromNat_ordlt = store_thm(
  "fromNat_ordlt",
  ``(&n:'a ordinal < &m) <=> (n < m)``,
  simp[ordlt_fromNat]);
val _ = export_rewrites ["fromNat_ordlt"]

val allNats_dwardclosedetc = prove(
  ``downward_closed { fromNat i : 'a ordinal | T } /\
    { fromNat i | T } <> univ(:'a ordinal)``,
  simp[downward_closed_def] >> conj_tac
  >- (map_every qx_gen_tac [`a`, `b`] >>
      disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `i` assume_tac)
                                  assume_tac) >>
      rw[] >> fs[ordlt_fromNat]) >>
  qsuff_tac `{&i : 'a ordinal | T} <<= univ(:'a inf)`
  >- metis_tac [univ_ord_greater_cardinal] >>
  simp[cardleq_def] >> qexists_tac `\a. INL (@n. &n = a)` >>
  simp[INJ_DEF] >> rw[] >> fs[]);

val omega_def = Define`
  omega = sup { fromNat i | T }
`;
val _ = overload_on ("ω", ``omega``)   (* UOK *)

val lt_omega0 =
  MATCH_MP preds_sup_thm allNats_dwardclosedetc
           |> SIMP_RULE (srw_ss() ++ DNF_ss) [SYM omega_def, ordlt_fromNat]

val lt_omega = store_thm(
  "lt_omega",
  ``!a. a < omega <=> ?m. a = &m``,
  simp_tac (srw_ss() ++ DNF_ss) [lt_omega0, EQ_IMP_THM] >> qx_gen_tac `n` >>
  qexists_tac `SUC n` >> simp[]);

val fromNat_lt_omega = store_thm(
  "fromNat_lt_omega",
  ``!n. &n < omega``,
  simp[lt_omega]);
val _ = export_rewrites ["fromNat_lt_omega"]

val fromNat_eq_omega = store_thm(
  "fromNat_eq_omega",
  ``!n. &n <> omega``,
  metis_tac [ordlt_REFL, fromNat_lt_omega]);
val _ = export_rewrites ["fromNat_eq_omega"]

(* recursion principles *)
val restrict_away = prove(
  ``IMAGE (RESTRICT f $< (a:'a ordinal)) (preds a) = IMAGE f (preds a)``,
  rw[EXTENSION, relationTheory.RESTRICT_DEF] >> srw_tac[CONJ_ss][]);

val ord_RECURSION = store_thm(
  "ord_RECURSION",
  ``!(z:'b) (sf:'a ordinal -> 'b -> 'b) (lf:'a ordinal -> 'b set -> 'b).
       ?h : 'a ordinal -> 'b.
         (h 0 = z) /\
         (!a. h a^+ = sf a (h a)) /\
         !a. 0 < a /\ islimit a ==>
             (h a = lf a (IMAGE h (preds a)))``,
  rpt gen_tac >>
  qexists_tac `WFREC $< (\g x. if x = 0 then z
                               else
                                 case omax (preds x) of
                                   NONE => lf x (IMAGE g (preds x))
                                 | SOME x0 => sf x0 (g x0)) ` >>
  rpt conj_tac
  >- simp[relationTheory.WFREC_THM, ordlt_WF]
  >- simp[Once relationTheory.WFREC_THM, relationTheory.RESTRICT_DEF, SimpLHS,
          ordlt_WF] >>
  simp[relationTheory.WFREC_THM, ordlt_WF, restrict_away] >> qx_gen_tac `a` >>
  strip_tac >> `a <> 0` by metis_tac [ordlt_REFL] >> simp[])

val ordADD_def = new_specification(
  "ordADD_def", ["ordADD"],
  ord_RECURSION |> Q.ISPEC `b:'a ordinal` |> Q.SPEC `\(x:'a ordinal) r. r^+`
                |> Q.SPEC `\x rs. sup rs`
                |> SIMP_RULE (srw_ss()) []
                |> Q.GEN `b`
                |> CONV_RULE SKOLEM_CONV)
val _ = export_rewrites ["ordADD_def"]
val _ = overload_on ("+", ``ordADD``)

val ordADD_0L = store_thm(
  "ordADD_0L",
  ``!a:'a ordinal. 0 + a = a``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >>
  `IMAGE ($+ 0) (preds a) = preds a`
    by (rpt (asm_simp_tac (srw_ss() ++ CONJ_ss)[EXTENSION])) >>
  fs[sup_preds_omax_NONE]);
val _ = export_rewrites ["ordADD_0L"]

val ubsup_thm = store_thm(
  "ubsup_thm",
  ``(!a. a IN s ==> a < b) ==> !c. c < sup s <=> ?d. d IN s /\ c < d``,
  strip_tac >> simp[sup_def] >> gen_tac >> DEEP_INTRO_TAC oleast_intro >>
  dsimp[impI] >>
  qexists_tac `b` >> conj_tac >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
  qx_gen_tac `a` >> strip_tac >> eq_tac >- metis_tac[] >>
  disch_then (Q.X_CHOOSE_THEN `d` strip_assume_tac) >>
  `d <= a`by metis_tac[] >> fs[ordle_lteq] >> rw[] >> metis_tac [ordlt_TRANS]);

val ordADD_fromNat = store_thm(
  "ordADD_fromNat",
  ``ordADD (&n) (&m) = &(n + m)``,
  Induct_on `m` >> simp[arithmeticTheory.ADD_CLAUSES]);
val _ = export_rewrites ["ordADD_fromNat"]

val omax_preds_omega = store_thm(
  "omax_preds_omega",
  ``omax (preds omega) = NONE``,
  simp_tac (srw_ss() ++ DNF_ss) [omax_NONE, lt_omega] >> qx_gen_tac `m` >>
  qexists_tac `SUC m` >> simp[]);
val omega_islimit = save_thm("omega_islimit", omax_preds_omega)

val ordADD_fromNat_omega = store_thm(
  "ordADD_fromNat_omega",
  ``&n + omega = omega``,
  simp[ordADD_def,omax_preds_omega] >>
  `!a. a IN IMAGE ($+ (&n)) (preds omega) ==> a < omega` by dsimp[lt_omega] >>
  pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
  match_mp_tac ordle_ANTISYM >> simp[] >> conj_tac
  >- (qx_gen_tac `d` >> Cases_on `d <= omega` >> simp[] >> fs[] >>
      simp[lt_omega] >> qx_gen_tac `x` >>
      Cases_on `?m. x = &m` >> fs[] >> strip_tac >>
      metis_tac [fromNat_lt_omega, ordlt_TRANS, ordlt_REFL]) >>
  simp[lt_omega] >> qx_gen_tac `m` >> strip_tac >>
  full_simp_tac (srw_ss() ++ DNF_ss) [lt_omega, impI] >>
  first_x_assum (qspec_then `&m` mp_tac) >> simp[] >>
  qexists_tac `m+1` >> decide_tac);

val lt_suppreds = save_thm(
  "lt_suppreds",
  predimage_sup_thm |> Q.INST [`f` |-> `\x. x`] |> SIMP_RULE (srw_ss()) [])

val ORD_ONE = store_thm(
  "ORD_ONE",
  ``0^+ = 1``,
  simp_tac bool_ss [GSYM fromNat_SUC] >> simp[]);
val _ = export_rewrites ["ORD_ONE"]

val ordSUC_NUMERAL = store_thm(
  "ordSUC_NUMERAL",
  ``(&NUMERAL n)^+ = &(NUMERAL n + 1)``,
  simp[GSYM arithmeticTheory.ADD1]);
val _ = export_rewrites ["ordSUC_NUMERAL"]

val ordZERO_ltSUC = store_thm(
  "ordZERO_ltSUC",
  ``0 < x^+``,
  metis_tac [ordSUC_ZERO, ordlt_ZERO, ordlt_trichotomy]);
val _ = export_rewrites ["ordZERO_ltSUC"]

val ordlt_CANCEL_ADDR = store_thm(
  "ordlt_CANCEL_ADDR",
  ``!(b:'a ordinal) a. a < a + b <=> 0 < b``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `b` >> strip_tac >> qx_gen_tac `a` >>
      Cases_on `b = 0` >- simp[] >>
      match_mp_tac ordlt_TRANS >> qexists_tac `a^+` >> simp[] >>
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
  ``a = a + c <=> c = 0``,
  Cases_on `c = 0` >> simp[] >>
  qsuff_tac `a < a + c` >- metis_tac[ordlt_REFL] >> simp[] >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq])
val ordADD_CANCEL1 = save_thm(
  "ordADD_CANCEL1",
  CONJ (GEN_ALL ordADD_CANCEL_LEMMA0)
       (ordADD_CANCEL_LEMMA0 |> CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))
                             |> GEN_ALL))
val _ = export_rewrites ["ordADD_CANCEL1"]

val ordADD_MONO = store_thm(
  "ordADD_MONO",
  ``!b:'a ordinal a c. a < b ==> c + a < c + b``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (ntac 2 strip_tac >> simp[ordlt_SUC_DISCRETE] >> rw[] >> rw[]) >>
  qx_gen_tac `b` >> strip_tac >> simp[predimage_sup_thm] >>
  map_every qx_gen_tac [`a`, `c`] >> strip_tac >>
  `?d. d < b /\ a < d`
    by (simp[GSYM lt_suppreds] >> fs[sup_preds_omax_NONE]) >>
  metis_tac[]);

val ordlt_CANCEL = store_thm(
  "ordlt_CANCEL",
  ``!b a (c:'a ordinal). c + a < c + b <=> a < b``,
  simp[EQ_IMP_THM, ordADD_MONO] >> rpt strip_tac >>
  metis_tac[ordlt_trichotomy, ordlt_REFL, ordlt_TRANS, ordADD_MONO]);
val _ = export_rewrites ["ordlt_CANCEL"]

val ordADD_RIGHT_CANCEL = store_thm(
  "ordADD_RIGHT_CANCEL",
  ``!b a c. ((a:'a ordinal) + b = a + c) <=> (b = c)``,
  metis_tac[ordlt_trichotomy, ordADD_MONO, ordlt_REFL]);
val _ = export_rewrites ["ordADD_RIGHT_CANCEL"]

val leqLEFT_CANCEL = store_thm(
  "leqLEFT_CANCEL",
  ``!x a. x <= a + x``,
  ho_match_mp_tac simple_ord_induction >> rpt conj_tac >- simp[] >- simp[] >>
  qx_gen_tac `x` >> strip_tac >>
  qx_gen_tac `a` >> strip_tac >>
  `?b. a + x < b /\ b < x` by metis_tac[omax_NONE, IN_preds] >>
  `b <= a + b` by metis_tac[] >>
  `a + x < a + b` by metis_tac [ordle_lteq, ordlt_TRANS] >>
  fs[] >> metis_tac[ordlt_TRANS, ordlt_REFL]);
val _ = export_rewrites ["leqLEFT_CANCEL"]

val lemma = prove(
  ``!c a b:'a ordinal. a < b /\ b < a + c ==> ?d. a + d = b``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> rpt conj_tac
  >- metis_tac [ordlt_TRANS, ordlt_REFL]
  >- (simp[ordlt_SUC_DISCRETE] >> metis_tac[]) >>
  simp[predimage_sup_thm]);

val ordlt_EXISTS_ADD = store_thm(
  "ordlt_EXISTS_ADD",
  ``!a b:'a ordinal. a < b <=> ?c. c <> 0 /\ b = a + c``,
  simp_tac (srw_ss() ++ DNF_ss) [EQ_IMP_THM] >> Tactical.REVERSE conj_tac
  >- metis_tac[ordlt_trichotomy, ordlt_ZERO] >>
  map_every qx_gen_tac [`a`, `b`] >> strip_tac >>
  `b <= a + b` by simp[] >> fs[ordle_lteq]
  >- (`?c. a + c = b` by metis_tac[lemma] >> rw[] >> strip_tac >> fs[]) >>
  qexists_tac `b` >> simp[] >> strip_tac >> fs[]);

val ordle_EXISTS_ADD = store_thm(
  "ordle_EXISTS_ADD",
  ``!a b:'a ordinal. a <= b <=> ?c. b = a + c``,
  simp[ordle_lteq] >> metis_tac [ordlt_EXISTS_ADD, ordADD_def]);

val ordle_CANCEL_ADDR = store_thm(
  "ordle_CANCEL_ADDR",
  ``x <= x + a``,
  simp[ordle_lteq] >> metis_tac[ordlt_trichotomy, ordlt_ZERO]);
val _ = export_rewrites ["ordle_CANCEL_ADDR"]

val dclose_BIGUNION = store_thm(
  "dclose_BIGUNION",
  ``dclose s = BIGUNION (IMAGE preds s)``,
  dsimp[Once EXTENSION, dclose_def] >> metis_tac[]);

val countableOrds_uncountable = store_thm(
  "countableOrds_uncountable",
  ``~countable { a:'a ordinal | countableOrd a }``,
  strip_tac >> qabbrev_tac `CO = { a | countableOrd a }` >>
  `CO <<= univ(:'a inf)`
     by metis_tac[countable_thm, cardleq_TRANS, Unum_cle_Uinf] >>
  `!b. b < sup CO <=> ?d. d IN CO /\ b < d` by metis_tac [sup_thm] >>
  `countableOrd (sup CO)`
    by (`preds (sup CO) = dclose CO` by simp[preds_sup] >>
        simp[countable_thm, dclose_BIGUNION] >>
        match_mp_tac CARD_BIGUNION >>
        asm_simp_tac (srw_ss() ++ DNF_ss) [] >> conj_tac
        >- (match_mp_tac IMAGE_cardleq_rwt >> fs[countable_thm]) >>
        simp[Abbr`CO`, countable_thm]) >>
  `countable (preds (sup CO)^+)` by simp[preds_ordSUC] >>
  `(sup CO)^+ IN CO` by simp[Abbr`CO`] >>
  `sup CO < (sup CO)^+` by simp[] >>
  metis_tac [ordlt_REFL]);

val dclose_cardleq_univinf = store_thm(
  "dclose_cardleq_univinf",
  ``(s:'a ordinal set) <<= univ(:'a inf) ==> dclose s <<= univ(:'a inf)``,
  strip_tac >> simp[dclose_BIGUNION] >>
  match_mp_tac CARD_BIGUNION >>
  dsimp[preds_inj_univ] >> metis_tac [cardleq_TRANS, IMAGE_cardleq]);

val sup_lt_implies = store_thm(
  "sup_lt_implies",
  ``(s:'a ordinal set) <<= univ(:'a inf) /\ sup s < a /\ b IN s ==> b < a``,
  strip_tac >>
  `sup s <= a` by simp[ordle_lteq] >>
  pop_assum mp_tac >> simp[sup_thm, impI] >> strip_tac >>
  `b <= a` by simp[] >> fs[ordle_lteq] >> fs[] >>
  `a <= sup s` by metis_tac [mklesup sup_thm]);

val sup_eq_max = store_thm(
  "sup_eq_max",
  ``(!b. b IN s ==> b <= a) /\ a IN s ==> sup s = a``,
  strip_tac >>
  `!b. b IN s ==> b < a^+` by fs[ordlt_SUC_DISCRETE, ordle_lteq] >>
  pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
  `a <= sup s` by metis_tac [ordlt_REFL] >>
  `sup s <= a` by simp[impI] >>
  metis_tac [ordle_ANTISYM]);

val sup_eq_SUC = store_thm(
  "sup_eq_SUC",
  ``s:'a ordinal set <<= univ(:'a inf) /\ sup s = a^+ ==> a^+ IN s``,
  rpt strip_tac >> `a < sup s` by simp[] >>
  pop_assum mp_tac >> pop_assum (mp_tac o SYM) >> simp[sup_thm] >> strip_tac >>
  disch_then (Q.X_CHOOSE_THEN `b` strip_assume_tac) >>
  qsuff_tac `b = a^+` >- metis_tac[] >>
  match_mp_tac ordle_ANTISYM >> conj_tac
  >- metis_tac [sup_lt_implies, ordlt_REFL] >>
  simp[ordlt_SUC_DISCRETE] >> metis_tac[ordle_lteq, ordlt_REFL]);


val generic_continuity = store_thm(
  "generic_continuity",
  ``(!a. 0 < a /\ islimit a ==> f a :'a ordinal = sup (IMAGE f (preds a))) /\
    (!x y. x <= y ==> f x <= f y) ==>
    !s:'a ordinal set.
          s <<= univ(:'a inf) /\ s <> {} ==> f (sup s) = sup (IMAGE f s)``,
  rpt strip_tac >>
  `islimit (sup s) \/ ?a. omax (preds (sup s)) = SOME a`
    by metis_tac [option_CASES]
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
    qpat_x_assum `islimit (sup s)` mp_tac >> simp[preds_sup] >> strip_tac >>
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
    `a^+ IN s` by metis_tac [sup_eq_SUC] >>
    ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
    match_mp_tac sup_eq_max >> dsimp[] >>
    ntac 2 strip_tac >> first_x_assum match_mp_tac >>
    metis_tac [mklesup sup_thm]
  ])

val ord_CASES = store_thm(
  "ord_CASES",
  ``!a. (a = 0) \/ (?a0. a = a0^+) \/ (0 < a /\ islimit a)``,
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
  ``(!a:'a ordinal.
       0 < a /\ islimit a ==> f a : 'a ordinal = sup (IMAGE f (preds a))) /\
    (!x y. x <= y ==> f x <= f y) /\ a1 < a2 /\ f a1 <= c /\ c < f a2 ==>
    ?b. a1 <= b /\ b < a2 /\ f b <= c /\ c < f b^+``,
  strip_tac >>
  qabbrev_tac `mu = oleast a. c < f a /\ a1 < a` >>
  `c < f mu /\ a1 < mu /\ (!a. a < mu ==> f a <= c \/ a <= a1)`
    by (simp[Abbr`mu`] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
        >- (qexists_tac `a2` >> simp[ordle_lteq]) >> simp[]) >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  `~islimit mu`
    by (strip_tac >> `sup (preds mu)= mu` by fs[sup_preds_omax_NONE] >>
        `0 < mu` by (spose_not_then assume_tac >> fs[]) >>
        `f mu = sup (IMAGE f (preds mu))` by metis_tac[] >>
        `?d. d < mu /\ c < f d` by metis_tac[predimage_sup_thm] >>
        `d <= a1` by metis_tac[] >>
        `f d <= f a1` by metis_tac[] >>
        metis_tac [ordlte_TRANS, ordle_TRANS]) >>
  `?d. mu = d^+` by metis_tac[ord_CASES, islimit_0] >>
  `d < mu` by simp[] >>
  qexists_tac `d` >>
  `a1 <= d` by metis_tac[ordlt_SUC_DISCRETE, ordle_lteq] >>
  `f d <= c` by metis_tac[ordle_ANTISYM] >>
  `d < a2` suffices_by metis_tac[] >>
  metis_tac[ordle_TRANS, ordle_TRANS]);

val ordADD_continuous = save_thm(
  "ordADD_continuous",
  generic_continuity |> Q.INST [`f` |-> `$+ a`] |> SIMP_RULE (srw_ss()) [])

val ordADD_ASSOC = store_thm(
  "ordADD_ASSOC",
  ``!a b c:'a ordinal. a + (b + c) = (a + b) + c``,
  qsuff_tac `!c a b:'a ordinal. a + (b + c) = (a + b) + c` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[predimage_sup_thm] >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  `IMAGE ($+ (a + b)) (preds c) = IMAGE ($+ a) (IMAGE ($+ b) (preds c))`
    by (dsimp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) []) >>
  simp[] >>
  match_mp_tac ordADD_continuous >>
  simp[IMAGE_cardleq_rwt, preds_inj_univ] >>
  metis_tac [preds_0, preds_11, ordlt_REFL]);

val exists_C = prove(
  ``(?h:'a -> 'a -> 'a. P h) <=> (?h. P (combin$C h))``,
  eq_tac >> strip_tac
  >- (qexists_tac `combin$C h` >>
      qsuff_tac `combin$C (combin$C h) = h` >- simp[] >>
      simp[FUN_EQ_THM]) >> metis_tac[]);

val ADD1R = store_thm(
  "ADD1R",
  ``a + 1 = a^+``,
  REWRITE_TAC [GSYM ORD_ONE] >> simp[]);

val ordADD_weak_MONO = store_thm(
  "ordADD_weak_MONO",
  ``!c a b:'a ordinal. a < b ==> a + c <= b + c``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- simp[ordle_lteq] >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  strip_tac >> simp[predimage_sup_thm, impI] >> qx_gen_tac `d` >> strip_tac >>
  strip_tac >>
  `a + d <= b + d` by metis_tac[] >>
  `b + d IN IMAGE ($+ b) (preds c)` by simp[] >>
  metis_tac[sup_lt_implies, IMAGE_cardleq_rwt, preds_inj_univ]);

(* Multiplication *)

val ordMULT_def = new_specification(
  "ordMULT_def", ["ordMULT"],
  ord_RECURSION |> INST_TYPE [beta |-> ``:'a ordinal``]
                |> Q.SPEC `0`
                |> Q.SPEC `\ap r. r + b`
                |> Q.SPEC `\a preds. sup preds`
                |> Q.GEN `b`
                |> CONV_RULE SKOLEM_CONV
                |> BETA_RULE)
val _ = export_rewrites ["ordMULT_def"]
val _ = overload_on ("*", ``ordMULT``)

val ordMULT_0L = store_thm(
  "ordMULT_0L",
  ``!a:'a ordinal. 0 * a = 0``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE ($* 0) (preds a) = {0}` >> simp[] >>
  simp[EXTENSION] >> metis_tac[]);
val _ = export_rewrites ["ordMULT_0L"]

val ordMULT_0R = store_thm("ordMULT_0R", ``!a:'a ordinal. a * 0 = 0``, simp[]);

val ordMULT_1L = store_thm(
  "ordMULT_1L",
  ``!a. 1 * (a:'a ordinal) = a``,
  ho_match_mp_tac simple_ord_induction >> simp[ADD1R] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE ($* 1) (preds a) = preds a`
  >- fs [sup_preds_omax_NONE] >>
  dsimp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) []);
val _ = export_rewrites ["ordMULT_1L"]

val ordMULT_1R = store_thm(
  "ordMULT_1R",
  ``!a:'a ordinal. a * 1 = a``,
  simp_tac bool_ss [GSYM ORD_ONE, ordMULT_def, ordADD_0L]);
val _ = export_rewrites ["ordMULT_1R"]

val ordMULT_2R = store_thm(
  "ordMULT_2R",
  ``(a:'a ordinal) * 2 = a + a``,
  `2 = 1^+` by simp[] >> pop_assum SUBST1_TAC >> simp[]);

val islimit_SUC_lt = store_thm(
  "islimit_SUC_lt",
  ``islimit b /\ a < b ==> a^+ < b``,
  fs[omax_NONE] >> metis_tac [ordlt_SUC_DISCRETE, ordlt_trichotomy, ordle_lteq])

val ordMULT_lt_MONO_R = store_thm(
  "ordMULT_lt_MONO_R",
  ``!a b c:'a ordinal. a < b /\ 0 < c ==> c * a < c * b``,
  qsuff_tac `!b a c:'a ordinal. a < b /\ 0 < c ==> c * a < c * b` >- metis_tac[]>>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (simp[ordlt_SUC_DISCRETE] >> qx_gen_tac `b` >> strip_tac >>
      map_every qx_gen_tac [`a`, `c`] >>
      Cases_on `a = b` >> simp[] >> strip_tac >>
      `c * a < c * b` by metis_tac[] >>
      `c * b < c * b + c` by simp[] >> metis_tac [ordlt_TRANS]) >>
  qx_gen_tac `b` >> strip_tac >> map_every qx_gen_tac [`a`, `c`] >>
  strip_tac >> simp[predimage_sup_thm] >>
  `?d. a < d /\ d < b`
    by metis_tac[sup_preds_omax_NONE, IN_preds, preds_inj_univ, sup_thm] >>
  metis_tac[]);

val ordMULT_le_MONO_R = store_thm(
  "ordMULT_le_MONO_R",
  ``!a b c:'a ordinal. a <= b ==> c * a <= c * b``,
  simp[ordle_lteq] >> rpt strip_tac >> simp[] >>
  Cases_on `c = 0` >> simp[] >>
  `0 < c` by metis_tac [ordlt_ZERO, ordlt_trichotomy] >>
  metis_tac [ordMULT_lt_MONO_R])

val ordMULT_lt_MONO_R_EQN = store_thm(
  "ordMULT_lt_MONO_R_EQN",
  ``c * a < c * b <=> a < b /\ 0 < c``,
  simp[EQ_IMP_THM, ordMULT_lt_MONO_R] >>
  Cases_on `0 < c` >- metis_tac [ordMULT_le_MONO_R] >> fs[]);
val _ = export_rewrites ["ordMULT_lt_MONO_R_EQN"]

val ordADD_le_MONO_L = store_thm(
  "ordADD_le_MONO_L",
  ``x <= y ==> x + z <= y + z``,
  simp[ordle_lteq, SimpL ``$==>``] >> simp[DISJ_IMP_THM, ordADD_weak_MONO]);

val ordMULT_le_MONO_L = store_thm(
  "ordMULT_le_MONO_L",
  ``!a b c:'a ordinal. a <= b ==> a * c <= b * c``,
  qsuff_tac `!c a b:'a ordinal. a <= b ==> a * c <= b * c` >- metis_tac[] >>
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
      strip_tac >>
      `a * c + a <= a * c + b` by simp[] >>
      match_mp_tac ordle_TRANS >> qexists_tac `a * c + b` >> simp[] >>
      simp[ordADD_le_MONO_L]) >>
  qx_gen_tac `c` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >> strip_tac>>
  simp[predimage_sup_thm, impI] >> qx_gen_tac `d` >> strip_tac >>
  match_mp_tac ordle_TRANS >> qexists_tac `b * d` >> simp[] >>
  qsuff_tac `b * d IN IMAGE ($* b) (preds c)`
  >- metis_tac [mklesup sup_thm, IMAGE_cardleq_rwt, preds_inj_univ] >>
  simp[] >> metis_tac[]);

val ordMULT_CANCEL_R = store_thm(
  "ordMULT_CANCEL_R",
  ``(z * x = z * y:'a ordinal) <=> (z = 0) \/ (x = y)``,
  simp[EQ_IMP_THM, DISJ_IMP_THM] >> strip_tac >>
  Tactical.REVERSE (Cases_on `0 < z`) >- fs[] >>
  `x < y \/ (x = y) \/ y < x` by metis_tac [ordlt_trichotomy] >>
  metis_tac [ordMULT_lt_MONO_R_EQN, ordlt_REFL]);
val _ = export_rewrites ["ordMULT_CANCEL_R"]

val ordMULT_continuous0 =
  generic_continuity |> Q.INST [`f` |-> `$* a`]
                     |> SIMP_RULE (srw_ss()) []

val ordMULT_continuous = store_thm(
  "ordMULT_continuous",
  ``!s:'a ordinal set. s <<= univ(:'a inf) ==> a * sup s = sup (IMAGE ($* a) s)``,
  rpt strip_tac >> Cases_on `s = {}` >> simp[ordMULT_continuous0]);

val ordMULT_fromNat = store_thm(
  "ordMULT_fromNat",
  ``(&n : 'a ordinal) * &m = &(n * m)``,
  Induct_on `m` >> simp[arithmeticTheory.MULT_CLAUSES]);
val _ = export_rewrites ["ordMULT_fromNat"]

val omega_MUL_fromNat = store_thm(
  "omega_MUL_fromNat",
  ``0 < n ==> &n * omega = omega``,
  simp[omax_preds_omega] >> strip_tac >>
  match_mp_tac ordle_ANTISYM >> dsimp[predimage_sup_thm, lt_omega, impI] >>
  conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `m` >>
  qsuff_tac `&m < sup (IMAGE ($* &n) (preds omega))` >- metis_tac[ordlt_REFL]>>
  dsimp[predimage_sup_thm, lt_omega] >>
  qexists_tac `m + 1` >> simp[arithmeticTheory.LEFT_ADD_DISTRIB] >>
  qsuff_tac `m <= m * n /\ m * n < n + m * n` >- DECIDE_TAC >>
  simp[]);

val ordMULT_LDISTRIB = store_thm(
  "ordMULT_LDISTRIB",
  ``!a b c:'a ordinal. c * (a + b) = c * a + c * b``,
  qsuff_tac `!b a c. c * (a + b) = c * a + c * b` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordADD_ASSOC] >>
  qx_gen_tac `b` >> strip_tac >>
  `preds b <> {}` by (strip_tac >> fs[]) >>
  simp[ordADD_continuous, ordMULT_continuous, IMAGE_cardleq_rwt,
       preds_inj_univ] >>
  rpt strip_tac >> AP_TERM_TAC >> dsimp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [])

val ordMULT_ASSOC = store_thm(
  "ordMULT_ASSOC",
  ``!a b c:'a ordinal. a * (b * c) = (a * b) * c``,
  qsuff_tac `!c a b:'a ordinal. a * (b * c) = (a * b) * c` >- simp[] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordMULT_LDISTRIB] >>
  simp[ordMULT_continuous, IMAGE_cardleq_rwt, preds_inj_univ] >>
  rpt strip_tac >> AP_TERM_TAC >> dsimp[EXTENSION] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [])

val ordDIVISION0 = prove(
  ``!a b:'a ordinal. 0 < b ==> ?q r. a = b * q + r /\ r < b``,
  rpt strip_tac >>
  qabbrev_tac `d = sup { c | b * c <= a }` >>
  `!c. b * c <= a ==> c <= a`
     by (ntac 2 strip_tac >> match_mp_tac ordle_TRANS >>
         qexists_tac `b * c` >> simp[] >>
         match_mp_tac ordle_TRANS >> qexists_tac `1 * c` >> conj_tac >- simp[]>>
         match_mp_tac ordMULT_le_MONO_L >>
         simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
         simp[] >> strip_tac >> fs[]) >>
  `!aa. aa IN { c | b * c <= a } ==> aa < a^+`
    by (simp[ordlt_SUC_DISCRETE] >> metis_tac [ordle_lteq]) >>
  `!aa. aa < d <=> ?c. b * c <= a /\ aa < c`
    by (simp[Abbr`d`] >> pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
        simp[]) >>
  `b * d <= a`
    by (simp[Abbr`d`] >>
        `{ c | b * c <= a } <<= univ(:'a inf)`
          by (`{ c | b * c <= a } <<= preds a^+`
                by simp[SUBSET_DEF, SUBSET_CARDLEQ] >>
              `preds a^+ <<= univ(:'a inf)` by simp[preds_inj_univ] >>
              metis_tac [cardleq_TRANS]) >>
        dsimp[ordMULT_continuous, sup_thm, IMAGE_cardleq_rwt, impI]) >>
  `?r. b * d + r = a` by metis_tac [ordle_EXISTS_ADD] >>
  qsuff_tac `r < b` >- metis_tac[] >>
  spose_not_then strip_assume_tac >>
  `?bb. b + bb = r` by metis_tac [ordle_EXISTS_ADD] >>
  `b * d^+ + bb = a` by simp[GSYM ordADD_ASSOC] >>
  `!c. b * c <= a ==> c <= d` by metis_tac [ordlt_REFL] >>
  metis_tac [ordlt_SUC, ordle_EXISTS_ADD]);

(* old definition:
val ordDIVISION = new_specification(
  "ordDIVISION", ["ordDIV", "ordMOD"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ordDIVISION0)
 *)

(* new definition (by Chun Tian as OpenTheory workarounds) *)
Theorem ordDIVISION1[local] :
    !a b:'a ordinal. 0 < b ==> ?c. a = b * FST c + SND c /\ SND c < b
Proof
    rpt STRIP_TAC
 >> STRIP_ASSUME_TAC
      (SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ordDIVISION0)
 >> POP_ASSUM (MP_TAC o (Q.SPECL [‘a’, ‘b’]))
 >> RW_TAC std_ss []
 >> rename1 ‘g a b < b’
 >> Q.EXISTS_TAC ‘(f a b,g a b)’ >> rw []
QED

(* The next 3 theorems are skipped in ordinal.otd *)
val ordDIVMOD = new_specification(
   "ordDIVMOD", ["ordDIVMOD"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ordDIVISION1);

Definition ordDIV :
    ordDIV a b = FST (ordDIVMOD a b)
End

Definition ordMOD :
    ordMOD a b = SND (ordDIVMOD a b)
End

(* |- !a b. 0 < b ==> a = b * ordDIV a b + ordMOD a b /\ ordMOD a b < b *)
Theorem ordDIVISION =
    REWRITE_RULE [GSYM ordDIV, GSYM ordMOD] ordDIVMOD

(* end of new definition of ordDIV and ordMOD *)

val _ = set_fixity "/" (Infixl 600)
val _ = overload_on ("/", ``ordDIV``)

val _ = set_fixity "%" (Infixl 650)
val _ = overload_on ("%", ``ordMOD``)

val ordDIV_UNIQUE = store_thm(
  "ordDIV_UNIQUE",
  ``!a b q r. 0 < (b:'a ordinal) /\ a = b*q + r /\ r < b ==> a / b = q``,
  rpt strip_tac >>
  `a = b * (a / b) + a % b /\ a % b < b` by metis_tac [ordDIVISION] >>
  `a / b < q \/ a / b = q \/ q < a / b` by metis_tac [ordlt_trichotomy] >| [
    `?bb. (q = a/b + bb) /\ 0 < bb`
      by metis_tac [ordlt_EXISTS_ADD, ordlt_trichotomy, ordlt_ZERO] >>
    `a = b * (a/b + bb) + r` by metis_tac[] >>
    `_ = b * (a/b) + b * bb + r` by metis_tac[ordMULT_LDISTRIB] >>
    `a % b = b * bb + r` by metis_tac [ordADD_ASSOC, ordADD_RIGHT_CANCEL] >>
    `b * bb + r < b` by metis_tac[] >>
    `b <= b * bb`
      by (simp_tac bool_ss [Once (GSYM ordMULT_1R), SimpR ``ordlt``] >>
          match_mp_tac ordMULT_le_MONO_R >>
          simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
          simp[] >> strip_tac >> fs[]) >>
    `b <= b * bb + r` by metis_tac [ordle_CANCEL_ADDR, ordADD_le_MONO_L,
                                   ordle_TRANS],

    `?bb. q + bb = a/b /\ 0 < bb`
      by metis_tac [ordlt_EXISTS_ADD, ordlt_trichotomy, ordlt_ZERO] >>
    `a = b * (q + bb) + a % b` by metis_tac[] >>
    `_ = b * q + b * bb + a % b` by simp[ordMULT_LDISTRIB] >>
    `r = b * bb + a % b` by metis_tac [ordADD_ASSOC, ordADD_RIGHT_CANCEL] >>
    `b * bb + a % b < b` by metis_tac[] >>
    `b <= b * bb`
      by (simp_tac bool_ss [Once (GSYM ordMULT_1R), SimpR ``ordlt``] >>
          match_mp_tac ordMULT_le_MONO_R >>
          simp_tac bool_ss [GSYM ORD_ONE, ordlt_SUC_DISCRETE] >>
          simp[] >> strip_tac >> fs[]) >>
    `b <= b * bb + a % b`
      by metis_tac [ordle_CANCEL_ADDR, ordADD_le_MONO_L, ordle_TRANS]
  ]);

val ordMOD_UNIQUE = store_thm(
  "ordMOD_UNIQUE",
  ``!a b q r. 0 < b /\ a = b * q + r /\ r < b ==> a % b = r``,
  rpt strip_tac >>
  `(a = b * (a / b) + a % b) /\ a % b < b` by metis_tac [ordDIVISION] >>
  `a / b = q` by metis_tac [ordDIV_UNIQUE] >> pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `r' = a % b` >> fs[])

(* Exponentiation *)
val ordEXP_def = new_specification(
  "ordEXP_def", ["ordEXP"],
  ord_RECURSION |> INST_TYPE [beta |-> ``:'a ordinal``]
                |> Q.SPEC `1`
                |> Q.SPEC `\ap r. r * a`
                |> Q.SPEC `\a preds. sup preds`
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
  ``!a:'a ordinal. 1 ** a = 1``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >> qsuff_tac `IMAGE ($** 1) (preds a) = {1}` >> simp[] >>
  simp[EXTENSION] >> asm_simp_tac (srw_ss() ++ CONJ_ss) [] >> metis_tac[]);
val _ = export_rewrites ["ordEXP_1L"]

val ordEXP_2R = store_thm(
  "ordEXP_2R",
  ``(a:'a ordinal) ** 2 = a * a``,
  `2 = 1^+` by simp[] >> pop_assum SUBST1_TAC >> simp[]);

val ordEXP_fromNat = store_thm(
  "ordEXP_fromNat",
  ``(&x:'a ordinal) ** &n = &(x ** n)``,
  Induct_on `n` >> simp[arithmeticTheory.EXP]);
val _ = export_rewrites ["ordEXP_fromNat"]

val ordEXP_le_MONO_L = store_thm(
  "ordEXP_le_MONO_L",
  ``!x a b. a <= b ==> a ** x <= b ** x``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `x` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
      strip_tac >> match_mp_tac ordle_TRANS >>
      qexists_tac `a ** x * b` >> simp[ordMULT_le_MONO_L, ordMULT_le_MONO_R]) >>
  qx_gen_tac `x` >> strip_tac >> map_every qx_gen_tac [`a`, `b`] >>
  strip_tac >> simp[predimage_sup_thm, impI] >>
  qx_gen_tac `d` >> strip_tac >>
  `a ** d <= b ** d` by simp[] >>
  `b ** d IN IMAGE ($** b) (preds x)` by (simp[] >> metis_tac[]) >>
  metis_tac [mklesup sup_thm, ordle_TRANS, IMAGE_cardleq_rwt, preds_inj_univ]);

val IFF_ZERO_lt = store_thm(
  "IFF_ZERO_lt",
  ``(x:'a ordinal <> 0 <=> 0 < x) /\ (1 <= x <=> 0 < x)``,
  REWRITE_TAC [GSYM ORD_ONE] >> simp[ordlt_SUC_DISCRETE] >>
  metis_tac [ordlt_trichotomy, ordlt_ZERO]);

val islimit_SUC = store_thm(
  "islimit_SUC",
  ``islimit x^+ <=> F``,
  simp[omax_NONE, impI, ordlt_SUC_DISCRETE] >>
  metis_tac[ordle_lteq]);
val _ = export_rewrites ["islimit_SUC"]

val islimit_fromNat = store_thm(
  "islimit_fromNat",
  ``islimit &x <=> x = 0``,
  Cases_on `x` >> simp[]);
val _ = export_rewrites ["islimit_fromNat"]

val ordEXP_ZERO_limit = store_thm(
  "ordEXP_ZERO_limit",
  ``!x. islimit x ==> 0 ** x = 1``,
  ho_match_mp_tac simple_ord_induction >> simp[] >>
  qx_gen_tac `x` >> strip_tac >>
  qsuff_tac `IMAGE ($** 0) (preds x) = {0; 1}`
  >- (simp[] >> dsimp[sup_def, impI] >> strip_tac >>
      DEEP_INTRO_TAC oleast_intro >> simp[] >>
      conj_tac >- metis_tac [ordlt_REFL] >>
      qx_gen_tac `a` >> strip_tac >>
      qsuff_tac `a <= 1` >- metis_tac[ordle_ANTISYM] >>
      metis_tac[ordlt_REFL]) >>
  simp[EXTENSION] >> qx_gen_tac `y` >> dsimp[EQ_IMP_THM] >>
  Tactical.REVERSE (rpt conj_tac)
  >- (strip_tac >> qexists_tac `0` >> simp[])
  >- (strip_tac >> qexists_tac `0^+` >> simp[] >>
      spose_not_then strip_assume_tac >> fs[ordle_lteq]
      >- metis_tac [ordlt_DISCRETE1, ORD_ONE] >>
      fs[]) >>
  qx_gen_tac `z` >> strip_tac >> Cases_on `islimit z` >- metis_tac[] >>
  `?z0. z = z0^+`
    by metis_tac [preds_omax_SOME_SUC, option_CASES] >>
  simp[])

val ordEXP_ZERO_nonlimit = store_thm(
  "ordEXP_ZERO_nonlimit",
  ``~islimit x ==> 0 ** x = 0``,
  metis_tac [preds_omax_SOME_SUC, option_CASES, ordEXP_def,
             ordMULT_0R]);

val sup_EQ_0 = store_thm(
  "sup_EQ_0",
  ``s:'a ordinal set <<= univ(:'a inf) ==> (sup s = 0 <=> s = {} \/ s = {0})``,
  strip_tac >>
  qspec_then `0` (mp_tac o Q.AP_TERM `$~`) (sup_thm |> UNDISCH_ALL) >>
  simp_tac pure_ss [NOT_EXISTS_THM] >> simp[impI] >>
  disch_then (K ALL_TAC) >> simp[EXTENSION] >> metis_tac[])

val ordADD_EQ_0 = store_thm(
  "ordADD_EQ_0",
  ``!y x. (x:'a ordinal) + y = 0 <=> x = 0 /\ y = 0``,
  ho_match_mp_tac simple_ord_induction >> simp[] >>
  simp[sup_EQ_0, IMAGE_cardleq_rwt, preds_inj_univ] >>
  qx_gen_tac `y` >> strip_tac >> qx_gen_tac `x` >>
  `preds y <> {}` by (strip_tac >> fs[]) >>
  simp[EXTENSION] >>
  `y <> 0` by metis_tac [ordlt_REFL] >> simp[] >>
  qexists_tac `x^+` >> simp[] >> qexists_tac `1` >>
  metis_tac [ADD1R, islimit_SUC_lt, ORD_ONE])
val _ = export_rewrites ["ordADD_EQ_0"]

val IMAGE_EQ_SING = store_thm(
  "IMAGE_EQ_SING",
  ``IMAGE f s = {x} <=> (?y. y IN s) /\ !y. y IN s ==> f y = x``,
  simp[EXTENSION] >> metis_tac []);

val ordMULT_EQ_0 = store_thm(
  "ordMULT_EQ_0",
  ``!x y. x * y = 0 <=> x = 0 \/ y = 0``,
  CONV_TAC SWAP_FORALL_CONV >>
  ho_match_mp_tac simple_ord_induction >> simp[] >>
  simp_tac (srw_ss() ++ CONJ_ss) [] >> qx_gen_tac `x` >> strip_tac >>
  simp[sup_EQ_0, IMAGE_cardleq_rwt, preds_inj_univ] >>
  `preds x <> {} /\ x <> 0` by (rpt strip_tac >> fs[]) >>
  qx_gen_tac `y` >> eq_tac
  >- (simp[IMAGE_EQ_SING] >> strip_tac >>
      pop_assum (qspec_then `1` mp_tac) >> simp[] >>
      disch_then match_mp_tac >> metis_tac [islimit_SUC_lt, ORD_ONE]) >>
  simp[IMAGE_EQ_SING] >> metis_tac[]);
val _ = export_rewrites ["ordMULT_EQ_0"]

val ordEXP_EQ_0 = store_thm(
  "ordEXP_EQ_0",
  ``!y x. x ** y = 0 <=> x = 0 /\ ~islimit y``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- metis_tac[] >>
  qx_gen_tac `y` >> strip_tac >>
  simp[sup_EQ_0, IMAGE_cardleq_rwt, preds_inj_univ] >>
  simp[IFF_ZERO_lt] >>
  `preds y <> {}` by (strip_tac >> fs[]) >> simp[] >>
  simp[IMAGE_EQ_SING] >> qx_gen_tac `x` >> DISJ2_TAC >>
  qexists_tac `0` >> simp[]);

val ZERO_lt_ordEXP_I = store_thm(
  "ZERO_lt_ordEXP_I",
  ``!a x:'a ordinal. 0 < a ==> 0 < a ** x``,
  metis_tac [IFF_ZERO_lt, ordEXP_EQ_0]);

val ZERO_lt_ordEXP = store_thm(
  "ZERO_lt_ordEXP",
  ``0 < a ** x <=> 0 < a \/ islimit x``,
  metis_tac [ordEXP_EQ_0, IFF_ZERO_lt])

val ordEXP_lt_MONO_R = store_thm(
  "ordEXP_lt_MONO_R",
  ``!y x a:'a ordinal. 1 < a /\ x < y ==> a ** x < a ** y``,
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
  ``!x y a:'a ordinal. 1 < a ==> (a ** x < a ** y <=> x < y)``,
  simp[EQ_IMP_THM, ordEXP_lt_MONO_R] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq]
  >- metis_tac[ordlt_TRANS, ordlt_REFL, ordEXP_lt_MONO_R] >> fs[]);
val _ = export_rewrites ["ordEXP_lt_IFF"]

val ordEXP_le_MONO_R = store_thm(
  "ordEXP_le_MONO_R",
  ``!x y a. 0 < a /\ x <= y ==> a ** x <= a ** y``,
  rpt gen_tac >> simp[ordle_lteq] >> rw[] >> Cases_on `a = 1` >- simp[] >>
  qsuff_tac `1 < a` >- metis_tac [ordEXP_lt_MONO_R] >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq] >> fs[] >>
  metis_tac [ORD_ONE, ordlt_DISCRETE1]);

val ordEXP_continuous = store_thm(
  "ordEXP_continuous",
  ``!a s:'a ordinal set.
       0 < a /\ s <<= univ(:'a inf) /\ s <> {} ==>
       a ** sup s = sup (IMAGE ($** a) s)``,
  simp[generic_continuity, ordEXP_le_MONO_R]);

val ordEXP_ADD = store_thm(
  "ordEXP_ADD",
  ``0 < x ==> x ** (y + z) = x ** y * x ** z``,
  map_every qid_spec_tac [`x`,`y`,`z`] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordMULT_ASSOC] >>
  qx_gen_tac `z` >> strip_tac >> map_every qx_gen_tac [`y`, `x`] >>
  `preds z <> {}` by (strip_tac >> fs[]) >>
  simp[ordEXP_continuous, IMAGE_cardleq_rwt, preds_inj_univ,
       ordMULT_continuous, GSYM IMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF] >> strip_tac >> AP_TERM_TAC >>
  simp[EXTENSION] >> metis_tac[]);

val ordEXP_MUL = store_thm(
  "ordEXP_MUL",
  ``0 < x ==> x ** (y * z) = (x ** y) ** z``,
  strip_tac >> map_every qid_spec_tac [`y`, `z`] >>
  ho_match_mp_tac simple_ord_induction >> simp[ordEXP_ADD] >>
  qx_gen_tac `z` >> strip_tac >> qx_gen_tac `y` >>
  `preds z <> {}` by (strip_tac >> fs[]) >>
  simp[ordEXP_continuous, IMAGE_cardleq_rwt, preds_inj_univ,
       GSYM IMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF] >> AP_TERM_TAC >>
  simp[EXTENSION] >> metis_tac []);

val fixpoints_exist = store_thm(
  "fixpoints_exist",
  ``(!s:'a ordinal set. s <> {} /\ s <<= univ(:'a inf) ==>
                        f (sup s) = sup (IMAGE f s)) /\
    (!x. x <= f x) ==>
    !a. ?b. a <= b /\ f b = b``,
  rpt strip_tac >> qexists_tac `sup { FUNPOW f n a | n | T }` >>
  `{FUNPOW f n a | n | T} <<= univ(:'a inf)`
    by (simp[cardleq_def] >>
        qsuff_tac `?g. SURJ g univ(:'a inf) {FUNPOW f n a | n | T}`
        >- metis_tac[SURJ_INJ_INV] >>
        qexists_tac `\x. case x of INL n => FUNPOW f n a
                                 | INR n => a` >>
        dsimp[SURJ_DEF] >> conj_tac
        >- (simp[sumTheory.FORALL_SUM] >>
            metis_tac [arithmeticTheory.FUNPOW]) >>
        qx_gen_tac `n` >> qexists_tac `INL n` >> simp[]) >>
  conj_tac
  >- (match_mp_tac suple_thm >> simp[] >> qexists_tac `0` >> simp[]) >>
  `{ FUNPOW f n a | n | T } <> {}` by simp[EXTENSION] >>
  simp[] >> match_mp_tac sup_eq_sup >>
  dsimp[IMAGE_cardleq_rwt] >>
  `!n. ?m. f (FUNPOW f n a) <= FUNPOW f m a`
    by (strip_tac >> qexists_tac `SUC n` >>
        simp[arithmeticTheory.FUNPOW_SUC]) >>
  `!n. ?m. FUNPOW f n a <= f (FUNPOW f m a)`
    by (strip_tac >> qexists_tac `n` >> simp[]) >> simp[]);

val x_le_ordEXP_x = store_thm(
  "x_le_ordEXP_x",
  ``!a x. 1 < a ==> x <= a ** x``,
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
  `!b. b < x ==> b^+ < x` by metis_tac [islimit_SUC_lt] >>
  fs[omax_NONE] >> strip_tac >>
  `?b. b < x /\ sup (IMAGE ($** a) (preds x)) < b` by metis_tac[] >>
  `!d. d < x ==> a ** d <= b` by metis_tac[predimage_suplt_ELIM] >>
  `a ** b < a ** b^+` by simp[] >>
  `a ** b^+ <= b` by metis_tac[] >>
  `b <= a ** b` by metis_tac[] >>
  metis_tac[ordlt_TRANS, ordle_lteq, ordlt_REFL])

val epsilon0_def = Define`
  epsilon0 = oleast x. omega ** x = x
`

val _ = overload_on("ε₀", ``epsilon0``)  (* UOK *)

val epsilon0_fixpoint = store_thm(
  "epsilon0_fixpoint",
  ``omega ** epsilon0 = epsilon0``,
  simp[epsilon0_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  metis_tac [fromNat_lt_omega, ordEXP_continuous, x_le_ordEXP_x,
             fixpoints_exist]);

val epsilon0_least_fixpoint = store_thm(
  "epsilon0_least_fixpoint",
  ``!a. a < epsilon0 ==> a < omega ** a /\ omega ** a < epsilon0``,
  gen_tac >> simp[epsilon0_def] >> DEEP_INTRO_TAC oleast_intro >>
  metis_tac [epsilon0_fixpoint, x_le_ordEXP_x, ordle_lteq, ordEXP_lt_MONO_R,
             fromNat_lt_omega]);

val zero_lt_epsilon0 =
  epsilon0_fixpoint |> SIMP_RULE (srw_ss()) [ASSUME ``epsilon0 = 0``]
                    |> DISCH_ALL
                    |> SIMP_RULE (srw_ss()) [IFF_ZERO_lt]

val one_lt_epsilon0 =
    MATCH_MP epsilon0_least_fixpoint zero_lt_epsilon0
             |> SIMP_RULE (srw_ss()) []

(* |- omega < epsilon0 *)
val omega_lt_epsilon0 = save_thm(
  "omega_lt_epsilon0",
  MATCH_MP epsilon0_least_fixpoint one_lt_epsilon0
           |> SIMP_RULE (srw_ss()) [])
val _ = export_rewrites ["omega_lt_epsilon0"]

val fromNat_lt_epsilon0 = store_thm(
  "fromNat_lt_epsilon0",
  ``&n < epsilon0``,
  metis_tac [ordlt_TRANS, fromNat_lt_omega, omega_lt_epsilon0]);
val _ = export_rewrites ["fromNat_lt_epsilon0"]

val add_nat_islimit = store_thm(
  "add_nat_islimit",
  ``0 < n ==> islimit (a + &n) = F``,
  Induct_on `n` >> simp[]);
val _ = export_rewrites ["add_nat_islimit"]

val strict_continuity_preserves_islimit = store_thm(
  "strict_continuity_preserves_islimit",
  ``(!s. s <<= univ(:'a inf) /\ s <> {} ==>
         f (sup s) = sup (IMAGE f s) : 'a ordinal) /\
    (!x y. x < y ==> f x < f y) /\
    islimit (a:'a ordinal) /\ a <> 0 ==> islimit (f a)``,
  strip_tac >> fs[sup_preds_omax_NONE] >>
  first_assum (fn th => simp_tac (srw_ss()) [SimpRHS, Once (SYM th)]) >>
  `preds a <> {}`
    by (strip_tac >> `0 < a` by fs[IFF_ZERO_lt] >> rw[] >> fs[]) >>
  simp[preds_inj_univ] >>
  match_mp_tac ordle_ANTISYM >>
  simp[sup_thm, IMAGE_cardleq_rwt, preds_inj_univ, impI] >> conj_tac
  >- (qx_gen_tac `b` >> strip_tac >> match_mp_tac ordle_TRANS >>
      qexists_tac `f a` >> conj_tac >- simp[ordle_lteq] >>
      Q.UNDISCH_THEN `sup (preds a) = a`
        (fn th => simp_tac (srw_ss()) [SimpR ``ordlt``, Once (SYM th)]) >>
      simp[preds_inj_univ]) >>
  asm_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `x` >> strip_tac >>
  match_mp_tac suple_thm >> simp[preds_inj_univ])

val add_omega_islimit = store_thm(
  "add_omega_islimit",
  ``islimit (a + omega)``,
  ho_match_mp_tac strict_continuity_preserves_islimit >>
  simp[omax_preds_omega, ordADD_continuous])
val _ = export_rewrites ["add_omega_islimit"]

val islimit_mul_R = store_thm(
  "islimit_mul_R",
  ``!a. islimit a ==> islimit (b * a)``,
  Cases_on `b = 0` >- simp[] >> fs[IFF_ZERO_lt] >> gen_tac >>
  Cases_on `a = 0` >- simp[] >> fs[IFF_ZERO_lt] >> strip_tac >>
  qspec_then `$* b` mp_tac
    (Q.GEN `f` strict_continuity_preserves_islimit) >> simp[] >>
  simp[ordMULT_continuous, IFF_ZERO_lt])

val mul_omega_islimit = store_thm(
  "mul_omega_islimit",
  ``islimit (omega * a)``,
  qspec_then `a` strip_assume_tac ord_CASES >> simp[islimit_mul_R]);

val omega_exp_islimit = store_thm(
  "omega_exp_islimit",
  ``0 < a ==> islimit (omega ** a)``,
  qspec_then `a` strip_assume_tac ord_CASES
  >- simp[]
  >- (simp[] >> simp[islimit_mul_R, omax_preds_omega]) >>
  strip_tac >> ho_match_mp_tac strict_continuity_preserves_islimit >>
  simp[IFF_ZERO_lt, ordEXP_continuous]);

val expbound_add = store_thm(
  "expbound_add",
  ``!a x y. x < omega ** a /\ y < omega ** a ==> x + y < omega ** a``,
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
      `x + y < omega ** a * &(b + c)`
        by (simp_tac bool_ss [ordMULT_LDISTRIB, GSYM ordADD_fromNat] >>
            match_mp_tac ordlte_TRANS >>
            qexists_tac `x + omega ** a * &c` >> simp[] >>
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
  >- (`omega ** b < omega ** c` by simp[] >>
      `x < omega ** c` by metis_tac [ordlt_TRANS] >>
      metis_tac[]) >>
  `omega ** c <= omega ** b` by simp[] >>
  `y < omega ** b` by metis_tac [ordlte_TRANS] >>
  metis_tac[])

Theorem downduct[local]:
  (!n. n <= m /\ P (SUC n) ==> P n) /\ P m ==>
  (!n. n <= m ==> P n)
Proof
  strip_tac >> fs[arithmeticTheory.LESS_EQ_EXISTS, PULL_EXISTS] >>
  CONV_TAC SWAP_FORALL_CONV >>
  Induct >> rw[] >> simp[] >>
  gvs[DECIDE “n + SUC d = d + m <=> m = SUC n”] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

val addL_fixpoint_iff = store_thm(
  "addL_fixpoint_iff",
  ``a + b = b <=> a * omega <= b``,
  eq_tac
  >- (simp[omega_islimit, ordMULT_def, EQ_IMP_THM, sup_thm, IMAGE_cardleq_rwt,
           preds_inj_univ, lt_omega] >> strip_tac >>
      qx_gen_tac `c` >> Cases_on `b < c` >> simp[] >>
      qx_gen_tac `d` >> Cases_on `c = a * d` >> simp[] >> qx_gen_tac `m` >>
      strip_tac >> rw[] >>
      `!n. n <= m ==> b < a * &n` suffices_by
         (disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      ho_match_mp_tac downduct >> simp[] >>
      qx_gen_tac `n`>>
      `a * &n + a = a + a * &n` suffices_by metis_tac[ordlt_CANCEL] >>
      Induct_on `n` >> simp[] >> metis_tac[ordADD_ASSOC])
  >- (simp[ordle_EXISTS_ADD] >>
      disch_then (qx_choose_then `c` SUBST_ALL_TAC) >>
      simp[ordADD_ASSOC] >>
      `a + a * omega = a * (1 + omega)` by simp[ordMULT_LDISTRIB] >>
      simp[ordADD_fromNat_omega, omega_islimit]))

(* And so, arithmetic (addition, multiplication and exponentiation) is
   closed under epsilon0 *)
val ordADD_under_epsilon0 = store_thm(
  "ordADD_under_epsilon0",
  ``x < epsilon0 /\ y < epsilon0 ==> x + y < epsilon0``,
  ONCE_REWRITE_TAC [GSYM epsilon0_fixpoint] >>
  simp[expbound_add])

val ordMUL_under_epsilon0 = store_thm(
  "ordMUL_under_epsilon0",
  ``x < epsilon0 /\ y < epsilon0 ==> x * y < epsilon0``,
  strip_tac >> imp_res_tac epsilon0_least_fixpoint >>
  `x * y < omega ** x * omega ** y`
    by (match_mp_tac ordlet_TRANS >>
        qexists_tac `omega ** x * y` >> simp[ZERO_lt_ordEXP] >>
        match_mp_tac ordMULT_le_MONO_L >> simp[ordle_lteq]) >>
  `omega ** x * omega ** y = omega ** (x + y)` by simp[ordEXP_ADD] >>
  pop_assum SUBST_ALL_TAC >>
  qsuff_tac `omega ** (x + y) < epsilon0` >- metis_tac[ordlt_TRANS] >>
  metis_tac [epsilon0_fixpoint, ordADD_under_epsilon0, fromNat_lt_omega,
             ordEXP_lt_IFF]);

val ordEXP_under_epsilon0 = store_thm(
  "ordEXP_under_epsilon0",
  ``a < epsilon0 /\ b < epsilon0 ==> a ** b < epsilon0``,
  strip_tac >>
  `a < omega ** a` by imp_res_tac epsilon0_least_fixpoint >>
  `a ** b <= (omega ** a) ** b` by metis_tac [ordEXP_le_MONO_L, ordle_lteq] >>
  `(omega ** a) ** b = omega ** (a * b)` by simp [GSYM ordEXP_MUL] >>
  pop_assum SUBST_ALL_TAC >>
  `omega ** (a * b) < epsilon0`
    by simp[ordEXP_lt_IFF, ordMUL_under_epsilon0,
            Once (GSYM epsilon0_fixpoint)] >>
  metis_tac [ordlet_TRANS]);

val eval_poly_def = Define`
  eval_poly (a:'a ordinal) [] = 0 /\
  eval_poly a ((c,e)::t) = a ** e * c + eval_poly a t
`;
val _ = export_rewrites ["eval_poly_def"]

val is_polyform_def = Define`
  (is_polyform (a:'a ordinal) [] <=> T) /\
  (is_polyform a [(c,e)] <=> 0 < c /\ c < a) /\
  (is_polyform a ((c1,e1) :: (c2,e2) :: t) <=>
     0 < c1 /\ c1 < a /\ e2 < e1 /\ is_polyform a ((c2,e2) :: t))
`;

val is_polyform_ELthm = store_thm(
  "is_polyform_ELthm",
  ``is_polyform a ces <=>
      (!i j. i < j /\ j < LENGTH ces ==> SND (EL j ces) < SND (EL i ces)) /\
      (!c e. MEM (c,e) ces ==> 0 < c /\ c < a)``,
  map_every qid_spec_tac [`ces`, `a`] >>
  ho_match_mp_tac (theorem "is_polyform_ind") >> simp[is_polyform_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  eq_tac >> simp[] >| [
    strip_tac >> ASM_REWRITE_TAC [] >>
    map_every qx_gen_tac [`i`, `j`] >>
    `i = 0 \/ ?i0. i = SUC i0` by (Cases_on `i` >> simp[])
    >- (simp[] >> strip_tac >>
        `?j0. j = SUC j0` by (Cases_on `j` >> fs[]) >>
        fs[] >>
        `j0 = 0 \/ ?j00. j0 = SUC j00` by (Cases_on `j0` >> simp[]) >> simp[] >>
        first_x_assum (qspecl_then [`0`, `j0`] mp_tac) >> simp[] >>
        metis_tac [ordlt_TRANS]) >>
    strip_tac >>
    `?j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
    asm_simp_tac (srw_ss() ++ ARITH_ss) [],
    rpt strip_tac
    >- (first_x_assum (qspecl_then [`0`, `SUC 0`] mp_tac) >> simp[])
    >- (first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
    >- res_tac >> res_tac
  ]);

val polyform_exists = store_thm(
  "polyform_exists",
  ``!a:'a ordinal b.
      1 < a ==> ?ces. is_polyform a ces /\ b = eval_poly a ces``,
  gen_tac >> Cases_on `1 < a` >> simp[is_polyform_ELthm] >>
  `0 < a` by (match_mp_tac ordlt_TRANS >> qexists_tac `1` >> simp[]) >>
  ho_match_mp_tac ord_induction >>
  qx_gen_tac `b` >> strip_tac >> Cases_on `b = 0`
  >- (qexists_tac `[]` >> simp[]) >>
  `0 < b /\ 1 <= b` by fs[IFF_ZERO_lt] >>
  qabbrev_tac `s = { e | a ** e <= b }` >>
  `!e. e IN s <=> a ** e <= b` by simp[Abbr`s`] >>
  `s <> {}` by (simp[EXTENSION] >> qexists_tac `0` >> simp[]) >>
  `!c. c IN s ==> c < b^+`
    by (simp[ordlt_SUC_DISCRETE, GSYM ordle_lteq] >>
        metis_tac [x_le_ordEXP_x, ordle_TRANS]) >>
  `s <<= univ(:'a inf)`
    by (`s <<= preds b^+` by simp[SUBSET_CARDLEQ, SUBSET_DEF] >>
        metis_tac [cardleq_TRANS, preds_inj_univ]) >>
  qabbrev_tac `E = sup s` >>
  `!g. g < E <=> ?d. d IN s /\ g < d` by simp[sup_thm, Abbr`E`] >>
  `a ** E <= b`
    by dsimp[Abbr`E`, ordEXP_continuous, sup_thm, IMAGE_cardleq_rwt, impI] >>
  `b < a ** E^+`
    by (spose_not_then strip_assume_tac >>
        `E^+ IN s` by simp[] >> `E^+ <= E` by metis_tac [suple_thm] >>
        fs[]) >>
  qabbrev_tac `c1 = b / a ** E` >>
  qabbrev_tac `r = b % a ** E` >>
  `0 < a ** E` by simp[ZERO_lt_ordEXP] >>
  `b = a ** E * c1 + r /\ r < a ** E` by metis_tac [ordDIVISION] >>
  `r < b` by metis_tac [ordlt_TRANS, ordle_lteq] >>
  `0 < c1` by (spose_not_then strip_assume_tac >> fs[]) >>
  `c1 < a`
    by (spose_not_then strip_assume_tac >>
        `a ** E * a <= a ** E * c1` by simp[] >>
        `a ** E * a + r <= b` by simp[ordADD_le_MONO_L] >>
        metis_tac [ordEXP_def, ordle_CANCEL_ADDR, ordle_TRANS]) >>
  `?ces. (!i j. i < j /\ j < LENGTH ces ==> SND (EL j ces) < SND (EL i ces)) /\
         (!c e. MEM (c,e) ces ==> 0 < c /\ c < a) /\
         r = eval_poly a ces` by metis_tac[] >>
  qexists_tac `(c1,E) :: ces` >> dsimp[] >> Tactical.REVERSE (rpt conj_tac)
  >- metis_tac[] >- metis_tac[] >>
  gen_tac >>
  `(?i0. i = SUC i0) \/ i = 0` by (Cases_on `i` >> simp[])
  >- (gen_tac >> Cases_on `j` >> simp[]) >>
  qpat_x_assum `!g. g < E <=> P` (K ALL_TAC) >> simp[] >>
  qsuff_tac `0 < LENGTH ces ==> SND (EL 0 ces) < E`
  >- (strip_tac >> qx_gen_tac `j` >> strip_tac >>
      `j = 0 \/ ?j0. j = SUC j0` by (Cases_on `j` >> simp[]) >> simp[] >>
      `j0 < LENGTH ces` by fs[] >>
      `0 < LENGTH ces` by decide_tac >>
      Cases_on `j0 = 0` >- asm_simp_tac bool_ss [] >>
      `0 < j0` by decide_tac >>
      metis_tac [ordlt_TRANS]) >>
  `ces = [] \/ ?c0 e0 t. ces = (c0,e0)::t`
    by metis_tac [pairTheory.pair_CASES, listTheory.list_CASES] >- simp[] >>
  simp[] >> (* rts: e0 < E *) spose_not_then strip_assume_tac >>
  `r = a ** e0 * c0 + eval_poly a t` by simp[] >>
  `a ** E <= a ** e0` by simp[ordEXP_le_MONO_R] >>
  `a ** e0 <= a ** e0 * c0`
    by (simp_tac bool_ss [SimpR ``ordlt``, Once (GSYM ordMULT_1R)] >>
        match_mp_tac ordMULT_le_MONO_R >> simp[IFF_ZERO_lt] >> fs[]) >>
  `a ** e0 * c0 <= a ** e0 * c0 + eval_poly a t` by simp[] >>
  metis_tac [ordle_TRANS, ordle_lteq, ordlt_REFL, ordlt_TRANS])

val polyform_def = new_specification(
  "polyform_def",
  ["polyform"],
  SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
            polyform_exists);

(* Cantor Normal Form - polynomials where the base is omega *)
val _ = overload_on ("CNF", ``polyform omega``)

val CNF_thm = save_thm(
  "CNF_thm",
  polyform_def |> SPEC ``omega`` |> SIMP_RULE (srw_ss()) [])

val polyform_0 = store_thm(
  "polyform_0",
  ``1 < a ==> polyform a 0 = []``,
  strip_tac >>
  qspecl_then [`a`, `0`] mp_tac polyform_def >> simp[] >>
  `polyform a 0 = [] \/ ?c e t. polyform a 0 = (c,e)::t`
    by metis_tac[pairTheory.pair_CASES, listTheory.list_CASES]
    >- simp[] >>
  simp[SimpL ``$==>``] >> strip_tac >> fs[]
  >- fs[ordEXP_EQ_0] >>
  `0 < c` by metis_tac[is_polyform_ELthm,listTheory.MEM] >>
  metis_tac[IFF_ZERO_lt]);

val polyform_EQ_NIL = store_thm(
  "polyform_EQ_NIL",
  ``1 < a ==> (polyform a x = [] <=> x = 0)``,
  simp[EQ_IMP_THM, polyform_0] >>
  rpt strip_tac >>
  qspecl_then [`a`, `x`] mp_tac polyform_def >> simp[]);

val is_polyform_CONS_E = store_thm(
  "is_polyform_CONS_E",
  ``is_polyform a ((c,e)::t) ==> 0 < c /\ c < a /\ is_polyform a t``,
  Cases_on `t` >> simp[is_polyform_def] >> Cases_on `h` >>
  simp[is_polyform_def]);

val expbounds = prove(
  ``1 < (a:'a ordinal) /\ y < a ** e /\ c < a /\ e < e' ==>
    a ** e * c + y < a ** e'``,
  strip_tac >>
  `a ** e * c + y < a ** e * c + a ** e` by simp[] >>
  `a ** e * c + a ** e = a ** e * ordSUC c` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  `c^+ <= a` by metis_tac [ordlt_DISCRETE1] >>
  `a ** e * c^+ <= a ** e * a` by simp[ordMULT_le_MONO_R] >>
  `a ** e * a = a ** e^+` by simp[] >> pop_assum SUBST_ALL_TAC >>
  `a ** e^+ <= a ** e'`
     by (match_mp_tac ordEXP_le_MONO_R >> conj_tac
         >- (spose_not_then strip_assume_tac >> fs[]) >>
         metis_tac [ordlt_DISCRETE1]) >>
  metis_tac [ordlte_TRANS, ordle_TRANS])

val is_polyform_head_dominates_tail = store_thm(
  "is_polyform_head_dominates_tail",
  ``1 < a /\ is_polyform a ((c,e)::t) ==> eval_poly a t < a ** e``,
  qsuff_tac
     `!a ces. 1 < a /\ is_polyform a ces /\ ces <> [] ==>
              eval_poly a (TL ces) < a ** SND (HD ces)`
  >- (disch_then (qspecl_then [`a`, `(c,e)::t`] strip_assume_tac) >>
      strip_tac >> fs[]) >>
  ho_match_mp_tac (theorem "is_polyform_ind") >> simp[is_polyform_def] >>
  rpt strip_tac
  >- (spose_not_then strip_assume_tac >> fs[] >> fs[ordEXP_EQ_0]) >>
  fs[] >> metis_tac[is_polyform_CONS_E, expbounds])

val cx_lt_x = store_thm(
  "cx_lt_x",
  ``x * c < (x:'a ordinal) <=> 0 < x /\ c = 0``,
  simp_tac bool_ss [SimpLHS, SimpR ``ordlt``, Once (GSYM ordMULT_1R)] >>
  simp[] >> metis_tac [IFF_ZERO_lt]);
val _ = export_rewrites ["cx_lt_x"]

val explemma = prove(
  ``1 < a /\ a ** e1 * c1 + eval_poly a t1 = a ** e2 * c2 + eval_poly a t2 /\
    is_polyform a ((c1,e1)::t1) /\ is_polyform a ((c2,e2)::t2) ==>
    e1 <= e2``,
  rpt strip_tac (* e2 < e1 *) >>
  `eval_poly a t2 < a ** e2` by metis_tac [is_polyform_head_dominates_tail] >>
  imp_res_tac is_polyform_CONS_E >>
  `a ** e2 * c2 + eval_poly a t2 < a ** e1` by simp[expbounds] >>
  `a ** e1 <= a ** e1 * c1` by (simp[IFF_ZERO_lt] >> rw[] >> fs[]) >>
  `a ** e1 * c1 <= a ** e1 * c1 + eval_poly a t1` by simp[] >>
  metis_tac[ordlte_TRANS, ordle_TRANS, ordlt_REFL]);

val coefflemma = prove(
  ``1 < a /\ a ** e * c1 + eval_poly a t1 = a ** e * c2 + eval_poly a t2 /\
    is_polyform a ((c1,e)::t1) /\ is_polyform a ((c2,e)::t2) ==>
    c1 <= c2``,
  rpt strip_tac (* c2 < c1 *) >>
  `eval_poly a t2 < a ** e` by metis_tac [is_polyform_head_dominates_tail] >>
  imp_res_tac is_polyform_CONS_E >>
  `a ** e * c2 + eval_poly a t2 < a ** e * c2 + a ** e` by simp[] >>
  `a ** e * c2 + a ** e = a ** e * c2^+` by simp[] >> pop_assum SUBST_ALL_TAC >>
  `a ** e * c2^+ <= a ** e * c1` by (simp[] >> metis_tac [ordlt_DISCRETE1]) >>
  `a ** e * c1 <= a ** e * c1 + eval_poly a t1` by simp[] >>
  metis_tac [ordlte_TRANS, ordle_TRANS, ordlt_REFL]);

Theorem polyform_UNIQUE:
    !a b ces.
      1 < a /\ is_polyform a ces /\ b = eval_poly a ces ==>
      polyform a b = ces
Proof
  gen_tac >> ho_match_mp_tac ord_induction >> qx_gen_tac `b` >>
  strip_tac >> qx_gen_tac `ces1` >> strip_tac >>
  `0 < a` by (`0 < 1o` by simp[] >> metis_tac [ordlt_TRANS]) >>
  qspecl_then [`a`, `b`] mp_tac polyform_def >>
  disch_then (strip_assume_tac o REWRITE_RULE [ASSUME``1<a:'a ordinal``]) >>
  `ces1 = [] \/ ?c e t. ces1 = (c,e)::t`
    by metis_tac[pairTheory.pair_CASES, listTheory.list_CASES]
  >- (pop_assum SUBST_ALL_TAC >> `b = 0` by fs[] >> simp[polyform_0]) >>
  pop_assum SUBST_ALL_TAC >>
  `0 < c /\ c < a` by metis_tac[listTheory.MEM, is_polyform_ELthm] >>
  `b = a ** e * c + eval_poly a t` by fs[] >>
  `polyform a b <> []` by simp[polyform_EQ_NIL, IFF_ZERO_lt, ZERO_lt_ordEXP] >>
  `?c' e' t'. polyform a b = (c',e')::t'`
    by metis_tac [listTheory.list_CASES, pairTheory.pair_CASES] >>
  `0 < c' /\ c' < a` by metis_tac [is_polyform_CONS_E] >>
  `b = a ** e' * c' + eval_poly a t'` by fs[] >>
  `e' = e` by metis_tac [explemma, ordle_ANTISYM] >> pop_assum SUBST_ALL_TAC >>
  `c' = c` by metis_tac [coefflemma, ordle_ANTISYM] >> pop_assum SUBST_ALL_TAC>>
  `eval_poly a t = eval_poly a t'` by metis_tac [ordADD_RIGHT_CANCEL] >>
  qsuff_tac `t = t'` >- simp[] >>
  `eval_poly a t < b`
    by (`eval_poly a t < a ** e`
          by metis_tac [is_polyform_head_dominates_tail] >>
        `a ** e <= a ** e * c` by simp[IFF_ZERO_lt, Excl "lift_disj_eq"] >>
        `a ** e * c <= a ** e * c + eval_poly a t` by simp[] >>
        metis_tac [ordlte_TRANS, ordle_TRANS]) >>
  metis_tac [is_polyform_CONS_E]
QED

val polyform_eval_poly = store_thm(
  "polyform_eval_poly",
  ``1 < a /\ is_polyform a b ==> (polyform a (eval_poly a b) = b)``,
  strip_tac >> match_mp_tac polyform_UNIQUE >> simp[]);

val CNF_nat = store_thm(
  "CNF_nat",
  ``CNF &n = if n = 0 then [] else [(&n,0)]``,
  rw[] >> match_mp_tac polyform_UNIQUE >> rw[is_polyform_def] >> decide_tac);

val _ = overload_on ("ordLOG", ``\b x. SND (HD (polyform b x))``)
val _ = overload_on ("olog", ``\x. ordLOG omega x``)
val ordLOG_correct = store_thm(
  "ordLOG_correct",
  ``1 < b /\ 0 < x ==> ordEXP b (ordLOG b x) <= x /\
    !a. ordLOG b x < a ==> x < ordEXP b a``,
  strip_tac >>
  `(polyform b x = []) \/ ?c e t. polyform b x = (c,e) :: t`
    by metis_tac [pairTheory.pair_CASES, listTheory.list_CASES]
  >- (pop_assum mp_tac >> fs[polyform_EQ_NIL] >> strip_tac >> fs[]) >>
  simp[] >>
  `is_polyform b (polyform b x) /\ (x = eval_poly b (polyform b x))`
    by metis_tac [polyform_def] >>
  first_assum SUBST1_TAC >> simp[] >>
  `0 < c /\ c < b /\ is_polyform b t` by metis_tac[is_polyform_CONS_E] >>
  `c <> 0` by (strip_tac >> fs[]) >>
  conj_tac
  >- (match_mp_tac ordle_TRANS >> qexists_tac `b ** e * c` >> simp[]) >>
  rpt strip_tac >>
  (is_polyform_head_dominates_tail
     |> Q.INST [`a` |-> `b`, `c` |-> `1`, `e` |-> `a`, `t` |-> `polyform b x`]
     |> MP_TAC) >> simp[] >> disch_then match_mp_tac >>
  simp[is_polyform_def] >> metis_tac[]);

(* |- 0 < x ==> omega ** olog x <= x /\ !a. olog x < a ==> x < omega ** a *)
val olog_correct = save_thm(
  "olog_correct",
  ordLOG_correct |> Q.INST [`b` |-> `omega`] |> SIMP_RULE (srw_ss()) []);

(* ----------------------------------------------------------------------
    Results about cardinalities of ordinal predecessor sets
   ---------------------------------------------------------------------- *)

Definition csuc_def:
  csuc (a : 'a ordinal) =
  oleast (b: ('a + num -> bool) ordinal). preds a <</= preds b
End

Definition cardSUC_def:
  cardSUC (s : 'a set) = preds $ csuc (oleast a:'a ordinal. preds a =~ s)
End

Theorem bumpUNIV_cardlt:
  univ(:num + 'a) <</= univ(:num + ('a + num -> bool))
Proof
  simp[disjUNION_UNIV] >> Cases_on ‘INFINITE univ(:'a)’
  >- (‘univ(:num) +_c univ(:'a) =~ univ(:'a)’
        by (irule cardleq_ANTISYM >>
            gs[INFINITE_Unum,CARD_ADD_ABSORB_LE, CARD_LE_ADDL]) >>
      ‘univ(:'a) <</= univ(:num) +_c univ(:'a + num -> bool)’
        suffices_by metis_tac[CARD_LT_CONG, cardeq_REFL]>>
      resolve_then (Pos hd) irule
                   CANTOR_THM_UNIV cardlt_leq_trans >>
      qspec_then ‘univ(:num)’
                 (fn th =>
                    resolve_then (Pos hd) irule th
                                 cardleq_TRANS)
                 CARD_LE_ADDL >>
      irule CARD_LE_ADD >> simp[] >>
      simp[cardleq_def, INJ_IFF] >>
      qexists_tac ‘IMAGE INL’ >> simp[IMAGE_11]) >>
  irule CARD_ADD2_ABSORB_LT >> simp[CARD_ADD_FINITE_EQ] >>
  conj_tac
  >- (resolve_then (Pos hd) irule
      CANTOR_THM_UNIV cardlt_leq_trans >>
      simp[cardleq_def, INJ_IFF] >>
      qexists_tac ‘λs. INR (IMAGE INR s)’ >>
      simp[IMAGE_11]) >>
  gs[FINITE_CARD_LT] >>
  pop_assum (C (resolve_then (Pos hd) irule)
             cardlt_leq_trans) >>
  simp[CARD_LE_ADDR]
QED

Theorem cardinality_bump_exists:
  !x : 'a ordinal. ?y: ('a + num -> bool) ordinal. cardlt (preds x) (preds y)
Proof
  gen_tac >>
  irule_at (Pos hd)
           (CARD_LET_TRANS |> Q.ISPEC ‘preds x’
                           |> Q.ISPEC ‘univ(:num + 'a)’) >>
  simp[preds_inj_univ] >>
  qexists_tac ‘sup { a | preds a =~ univ(:num + 'a)}’>>
  qmatch_abbrev_tac ‘UNIV <</= preds (sup ords)’ >>
  strip_tac >>
  qabbrev_tac ‘bigU = univ(:num + ('a + num -> bool))’ >>
  ‘INFINITE bigU /\ !x. x IN bigU’ by simp[Abbr‘bigU’] >>
  ‘univ(:num + 'a) <</= bigU’ by simp[Abbr‘bigU’, bumpUNIV_cardlt] >>
  ‘omax ords = NONE’
    by (simp[omax_NONE] >> CCONTR_TAC >> gs[] >>
        rename [‘mx IN ords’] >> ‘mx < ordSUC mx’ by simp[] >>
        ‘ordSUC mx NOTIN ords’ by metis_tac[] >> pop_assum mp_tac >>
        gs[Abbr‘ords’, preds_ordSUC] >>
        ‘INFINITE univ(:num+'a)’ by simp[] >>
        ‘INFINITE (preds mx)’ by metis_tac[CARD_INFINITE_CONG] >>
        metis_tac[cardeq_INSERT, cardeq_SYM, cardeq_TRANS]) >>
  ‘ords <<= bigU’ (* can't prove much about sup ords without this *)
    by (CCONTR_TAC >> gs[cardlt_lenoteq] >>
        ‘?f. INJ f bigU ords’ by metis_tac[cardleq_def] >>
        ‘(!u. preds (f u) =~ univ(:num + 'a)) /\
         (!u v. f u = f v <=> u = v)’
          by fs[INJ_IFF, Abbr‘ords’] >>
        qabbrev_tac ‘fU = IMAGE f bigU’ >>
        ‘fU =~ bigU’
          by (simp[Abbr‘fU’] >> gs[INJ_DEF, CARD_EQ_IMAGE]) >>
        ‘fU <<= univ(:num+('a+num->bool))’
          by metis_tac[cardleq_REFL, CARD_LE_CONG, cardeq_REFL] >>
        drule_then assume_tac sup_thm >>
        reverse (Cases_on ‘omax fU’)
        >- (gs[omax_SOME] >> rename [‘mx IN fU’] >>
            ‘?u. f u = mx’ by gs[Abbr‘fU’] >>
            ‘ordSUC mx IN ords’
              by (gs[Abbr‘ords’, preds_ordSUC] >>
                  ‘preds mx =~ univ(:num + 'a)’ by metis_tac[] >>
                  ‘INFINITE univ(:num + 'a)’ by simp[] >>
                  ‘INFINITE (preds mx)’ by metis_tac[CARD_INFINITE_CONG] >>
                  metis_tac[cardeq_INSERT, cardeq_SYM, cardeq_TRANS]) >>
            pop_assum mp_tac >> simp[Abbr‘ords’] >> strip_tac >>
            ‘fU <<= preds $ ordSUC mx’
              by (simp[preds_sup, cardleq_def, INJ_IFF] >>
                  qexists_tac ‘I’>> simp[] >> rpt strip_tac >>
                  irule ordlet_TRANS >> qexists_tac ‘mx’ >> simp[]) >>
            ‘bigU <<= univ(:num + 'a)’ by metis_tac[CARD_LE_CONG] >>
            metis_tac[cardleq_ANTISYM]) >>
        Cases_on ‘sup fU IN ords’
        >- (‘fU <<= preds (sup fU)’
              by (simp[preds_sup,cardleq_def,INJ_IFF] >>
                  qexists_tac ‘I’ >> simp[dclose_def] >> gs[omax_NONE]) >>
            ‘preds (sup fU) =~ univ(:num + 'a)’ by gs[Abbr‘ords’] >>
            ‘bigU <<= univ(:num + 'a)’ by metis_tac[CARD_LE_CONG] >>
            metis_tac[cardleq_ANTISYM]) >>
        ‘!a. a IN ords ==> a < sup fU’
          by (simp[] >> CCONTR_TAC >> gs[] >>
              ‘sup fU < a’ by metis_tac[sup_thm, ordle_lteq] >>
              ‘preds (sup fU) SUBSET preds a’
                by metis_tac[PSUBSET_DEF, preds_lt_PSUBSET] >>
              ‘fU <<= preds (sup fU)’
                by (simp[preds_sup,cardleq_def,INJ_IFF] >>
                    qexists_tac ‘I’ >> simp[dclose_def] >> gs[omax_NONE])>>
              ‘preds a =~ univ(:num + 'a)’ by gs[Abbr‘ords’] >>
              ‘fU <<= univ(:num + 'a)’
                by metis_tac[cardleq_TRANS, CARD_LE_CONG, cardeq_REFL,
                             SUBSET_CARDLEQ] >>
              ‘bigU <<= univ(:num + 'a)’
                by metis_tac[CARD_LE_CONG, cardeq_REFL]>>
              metis_tac[cardleq_ANTISYM]) >>
        ‘sup fU = sup ords’
          by (irule ordle_ANTISYM >> drule_then assume_tac ubsup_thm >>
              simp[]>> rw[] >- metis_tac[ordle_lteq] >>
              simp[ordle_lteq] >> rename [‘a NOTIN fU \/ _’] >>
              Cases_on ‘a IN fU’ >> simp[] >> gs[omax_NONE] >>
              ‘a IN ords’ suffices_by metis_tac[] >> gs[INJ_IFF, Abbr‘fU’])>>
        ‘fU <<= preds (sup ords)’
          by (simp[preds_sup,cardleq_def,INJ_IFF] >>
              qexists_tac ‘I’ >> simp[dclose_def] >> gs[omax_NONE])>>
        ‘bigU <<= univ(:num + 'a)’
          by metis_tac[CARD_LE_CONG, cardeq_REFL, cardleq_TRANS,
                       cardeq_SYM] >>
        metis_tac[cardleq_ANTISYM]) >>
  qpat_x_assum ‘preds (sup _) <<= _’ mp_tac >> simp[] >>
  ‘sup ords NOTIN ords’
    by (gs[omax_NONE] >> strip_tac >> first_x_assum drule >>
        metis_tac[suple_thm]) >>
  ‘~(univ(:num + 'a) =~ preds (sup ords))’
    by (gs[Abbr‘ords’] >> metis_tac[cardeq_SYM]) >>
  simp[CARD_LT_LE] >>
  ‘?a. a IN ords’ suffices_by
    (strip_tac >>
     ‘a < sup ords’ by (simp[sup_thm] >> gs[omax_NONE]) >>
     ‘preds a SUBSET preds (sup ords)’
       by metis_tac[preds_lt_PSUBSET, PSUBSET_DEF] >>
     ‘preds a =~ univ(:num + 'a)’ by gs[Abbr‘ords’] >>
     metis_tac[CARD_LE_SUBSET, CARD_LE_CONG, cardeq_SYM, cardeq_REFL]) >>
  simp[Abbr‘ords’] >> irule cardeq_ordinals_exist >>
  simp[cardleq_lteq, Abbr‘bigU’]
QED

Theorem ZERO_LT_csuc[simp]:
  0 < csuc a /\ csuc a <> 0
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> rpt strip_tac >>
  CCONTR_TAC >> gvs[]
QED

Theorem cardSUC_EQ0[simp]:
  cardSUC A <> {}
Proof
  simp[cardSUC_def]
QED

Theorem csuc_is_nonzero_limit:
  omega <= a ==> islimit (csuc a) /\ 0 < csuc a
Proof
  strip_tac >> simp[] >>
  qspec_then ‘a’ (qx_choose_then ‘b’ assume_tac) cardinality_bump_exists >>
  CCONTR_TAC >>
  ‘csuc a <> 0’ by (strip_tac >> gs[]) >>
  ‘?a0. csuc a = ordSUC a0’ by metis_tac[ord_CASES] >>
  gs[csuc_def] >> pop_assum mp_tac >>
  DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- goal_assum drule >>
  simp[preds_ordSUC] >>
  ‘INFINITE (preds a)’
    by (simp[FINITE_preds] >> rpt strip_tac >> gs[]) >>
  simp[INFINITE_cardleq_INSERT] >> Cases_on ‘preds a0 <<= preds a’ >>
  simp[] >> qexists_tac ‘a0’ >> simp[]
QED

Theorem CARD_FINITE_preds:
  CARD (preds (&n : 'a ordinal)) = CARD (preds (&n : unit ordinal))
Proof
  simp[preds_nat, CARD_INJ_IMAGE]
QED

Theorem csuc_nat:
  csuc (fromNat n) = ordSUC (fromNat n)
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  rpt strip_tac >- metis_tac[cardinality_bump_exists] >>
  gs[] >> irule ordle_ANTISYM >> rpt strip_tac
  >- (gs[preds_lt_PSUBSET] >> qpat_x_assum ‘preds _ <</= preds _’ mp_tac >>
      simp[] >>
      drule_at (Pos last) CARD_PSUBSET >>
      simp[FINITE_preds, GSYM fromNat_SUC, Excl "fromNat_SUC"] >>
      simp[] >>
      ‘FINITE (preds a)’
        by metis_tac[SUBSET_FINITE, FINITE_preds, fromNat_SUC, PSUBSET_DEF] >>
      simp[CARD_LE_CARD, FINITE_preds, preds_ordSUC, CARD_FINITE_preds]) >>
  first_x_assum drule >>
  simp[preds_nat, preds_ordSUC, CARD_LT_CARD, CARD_INJ_IMAGE]
QED

Theorem lt_csuc:
  x < csuc y <=> preds x <<= preds y
Proof
  simp[csuc_def] >>
  DEEP_INTRO_TAC oleast_intro >> rpt strip_tac
  >- metis_tac[cardinality_bump_exists] >> gs[] >> simp[EQ_IMP_THM] >>
  strip_tac >> CCONTR_TAC >> qpat_x_assum ‘a <= x’ mp_tac >>
  PURE_REWRITE_TAC[ordle_lteq] >> rpt strip_tac >> gvs[] >>
  gs[preds_lt_PSUBSET] >>
  ‘preds a <<= preds x’ by metis_tac[CARD_LE_SUBSET, PSUBSET_DEF] >>
  metis_tac[cardlt_REFL, CARD_LTE_TRANS, CARD_LE_TRANS]
QED

Theorem orderiso_cardeq_elsOf:
  orderiso w1 w2 ==> elsOf w1 =~ elsOf w2
Proof
  simp[orderiso_thm, cardeq_def] >> metis_tac[]
QED

Theorem transfer_ordinals:
  !a:'a ordinal.
    preds a <<= univ(:num + 'b) ==>
    ?b:'b ordinal. orderiso (wobound a allOrds) (wobound b allOrds) /\
                   preds a =~ preds b
Proof
  rw[cardleq_def,preds_wobound] >>
  drule_then (qx_choose_then ‘w1’ assume_tac) elsOf_cardeq_iso>>
  qexists_tac ‘mkOrdinal w1’ >>
  qspec_then ‘w1’ assume_tac wellorder_ordinal_isomorphism >>
  conj_asm1_tac >- metis_tac[orderiso_TRANS] >>
  metis_tac[orderiso_cardeq_elsOf]
QED

Theorem cardlt_preds:
  cardlt (preds x) (preds y) ==> x < y
Proof
  CONV_TAC CONTRAPOS_CONV >> simp[ordle_lteq, DISJ_IMP_THM] >>
  metis_tac[PSUBSET_DEF, CARD_LE_SUBSET, preds_lt_PSUBSET]
QED

Theorem INFINITE_eqpreds:
  omega <= (x:'a ordinal) ==> INFINITE { y : 'a ordinal | preds y =~ preds x }
Proof
  rpt strip_tac >>
  ‘{ y : 'a ordinal | preds y =~ preds x} <> {}’
    by (simp[EXTENSION] >> metis_tac[cardeq_REFL]) >>
  drule_all_then strip_assume_tac FINITE_omax_IS_SOME >>
  gs[omax_SOME] >> rename [‘preds a =~ preds x’] >>
  ‘INFINITE (preds a)’
    by (strip_tac >> gvs[FINITE_preds] >> rename [‘preds (&n) =~ preds x’] >>
        ‘x <= &n’ by metis_tac[cardeq_REFL] >>
        ‘omega <= &n’ by metis_tac[ordle_TRANS] >> gs[]) >>
  ‘preds (ordSUC a) =~ preds x’
    by (simp[preds_ordSUC] >> metis_tac[CARDEQ_INSERT_RWT, cardeq_TRANS]) >>
  first_x_assum drule >> simp[]
QED

Theorem cardlt_lepreds:
  cardlt (preds (x : 'a ordinal)) { (y : 'a ordinal) | preds y <<= preds x }
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = { y : 'a ordinal | preds y <<= preds x }’ >>
  ‘s <<= univ(:num + 'a)’ by metis_tac[cardleq_TRANS, preds_inj_univ] >>
  Cases_on ‘x < omega’
  >- (gvs[lt_omega, preds_nat] >>
      rev_drule_at (Pos last) CARD_LE_CARD_IMP >> simp[Abbr‘s’] >>
      simp[CARD_INJ_IMAGE] >> qmatch_abbrev_tac ‘~(CARD s <= m)’ >>
      ‘s = IMAGE $& (count (m + 1))’ suffices_by simp[CARD_INJ_IMAGE] >>
      simp[Abbr‘s’, EXTENSION] >> qx_gen_tac ‘n’ >> eq_tac
      >- (strip_tac >> drule_at (Pos last) CARD_LE_CARD_IMP >>
          simp[CARD_INJ_IMAGE] >>
          ‘n < omega’
            by (CCONTR_TAC >> qpat_x_assum ‘_ <<= _’ mp_tac >> simp[] >>
                irule CARD_LT_FINITE_INFINITE >> simp[FINITE_preds] >>
                rpt strip_tac >> gs[]) >> gvs[lt_omega] >>
          rename [‘preds (&n)’] >> simp[preds_nat, CARD_INJ_IMAGE]) >>
      rw[] >> simp[preds_nat] >> irule CARD_LE_SUBSET >> simp[SUBSET_DEF]) >>
  ‘INFINITE s’
    by (‘s = { y | preds y =~ preds x} UNION { y | cardlt (preds y) (preds x)}’
          by (simp[Abbr‘s’, EXTENSION] >> metis_tac[cardleq_lteq]) >>
        simp[INFINITE_eqpreds]) >>
  ‘dclose s = s’
    by (simp[dclose_def, EXTENSION] >> qx_gen_tac ‘a’ >> eq_tac >>
        rpt strip_tac
        >- (gs[Abbr‘s’, preds_lt_PSUBSET] >>
            metis_tac[cardleq_TRANS, CARD_LE_SUBSET, PSUBSET_DEF]) >>
        qexists_tac ‘ordSUC a’ >> simp[] >> gs[Abbr‘s’, preds_ordSUC] >>
        irule (iffRL INFINITE_cardleq_INSERT) >> simp[FINITE_preds] >>
        rpt strip_tac >> gs[]) >>
  ‘preds (sup s) = s’ by simp[preds_sup] >>
  Cases_on ‘preds (sup s) =~ preds x’
  >- (‘preds (ordSUC (sup s)) =~ preds x’
        by (gs[preds_ordSUC] >> metis_tac[cardeq_TRANS, CARDEQ_INSERT_RWT]) >>
      ‘!x. x IN s ==> x <= sup s’ by simp[suple_thm] >>
      ‘ordSUC (sup s) IN s’ suffices_by (strip_tac >> first_x_assum drule >>
                                         simp[]) >>
      qabbrev_tac ‘mx = sup s’ >> simp[Abbr‘s’] >>
      metis_tac[cardleq_REFL, CARD_LE_CONG, cardeq_REFL]) >>
  Cases_on ‘preds (sup s) <</= preds x’
  >- (drule cardlt_preds >> simp[] >> irule suple_thm >> simp[] >>
      simp[Abbr‘s’]) >>
  ‘preds x <</= preds(sup s)’ by metis_tac[CARD_LT_TOTAL] >> gs[preds_sup]
QED

Theorem cardle_preds_EQ_cardeq_preds:
  omega <= (x:'a ordinal) ==>
  { (y:'a ordinal) | preds y <<= preds x } =~
  { (y:'a ordinal) | preds y =~ preds x }
Proof
  strip_tac >> irule cardleq_ANTISYM >> reverse conj_tac
  >- (irule CARD_LE_SUBSET >> simp[SUBSET_DEF] >>
      metis_tac[CARD_LE_CONG, cardeq_REFL, cardeq_SYM, cardleq_REFL]) >>
  ‘{ (y:'a ordinal) | preds y <<= preds x} =
   { y | preds y =~ preds x } UNION { y | cardlt (preds y) (preds x) }’
    by (simp[EXTENSION, Once cardleq_lteq] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  resolve_then (Pos hd) irule UNION_LE_ADD_C cardleq_TRANS >>
  irule CARD_ADD2_ABSORB_LE >> simp[INFINITE_eqpreds] >>
  simp[Once cardleq_def, INJ_IFF, PULL_EXISTS] >>
  qexists_tac ‘λy. x + y’ >> simp[] >> qx_gen_tac ‘y’ >>
  strip_tac >> drule_then assume_tac cardlt_preds >>
  ‘preds (x + y) = preds x UNION IMAGE (λy. x + y) (preds y)’
    by (simp[EXTENSION, EQ_IMP_THM] >> rw[] >> simp[]
        >- (rename [‘x0 < x + y’] >> Cases_on ‘x0 < x’ >> simp[] >>
            gs[ordle_EXISTS_ADD]) >>
        irule ordlte_TRANS >> first_assum $ irule_at Any >> simp[]) >>
  simp[] >>
  ‘preds x INTER IMAGE (λy. x + y) (preds y) = {}’
    by (simp[EXTENSION] >> qx_gen_tac ‘a’ >> Cases_on ‘x <= a’ >> simp[] >>
        qx_gen_tac ‘b’ >> rpt strip_tac >> gvs[]) >>
  dxrule_then assume_tac CARDEQ_DISJOINT_UNION >>
  drule_then irule cardeq_TRANS >>
  resolve_then (Pos hd) irule CARD_ADD_SYM cardeq_TRANS >>
  irule CARD_ADD_ABSORB >> conj_tac
  >- (strip_tac >> gvs[FINITE_preds]) >>
  irule IMAGE_cardleq_rwt >> metis_tac[cardleq_lteq]
QED

Theorem cardlt_eqpreds:
  omega <= (x:'a ordinal) ==>
  cardlt (preds x) { y:'a ordinal | preds y =~ preds x }
Proof
  strip_tac >>
  resolve_then (Pos hd)
               (resolve_then Any irule
                (ONCE_REWRITE_RULE [cardeq_SYM] cardle_preds_EQ_cardeq_preds))
               cardeq_REFL
               (iffRL CARD_LT_CONG) >>
  simp[cardlt_lepreds]
QED

Theorem lt_cardSUC:
  A <</= cardSUC A
Proof
  simp[cardSUC_def] >> qabbrev_tac ‘Aord = oleast a:'a ordinal. preds a =~ A’ >>
  ‘preds Aord =~ A’
    by (simp[Abbr‘Aord’] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
        irule cardeq_ordinals_exist >>
        simp[disjUNION_UNIV] >>
        resolve_then (Pos hd) irule CARD_LE_UNIV CARD_LE_TRANS >>
        simp[CARD_LE_ADDL]) >>
  ‘preds Aord <</= preds (csuc Aord)’
    suffices_by metis_tac[CARD_LT_CONG, cardeq_REFL] >>
  ‘preds Aord <<= univ(:num + ('a + num -> bool))’
    by (resolve_then (Pos hd) irule preds_inj_univ CARD_LE_TRANS >>
        simp[Once cardleq_lteq, bumpUNIV_cardlt]) >>
  drule_then (qx_choose_then ‘Aord'’ strip_assume_tac) transfer_ordinals >>
  ‘Aord' < csuc Aord’
    by (simp[lt_csuc] >> metis_tac[CARD_LE_CONG, CARD_LE_REFL, cardeq_REFL]) >>
  ‘preds Aord' <</= preds (csuc Aord)’ suffices_by
    metis_tac[CARD_LE_CONG, cardeq_REFL, cardeq_SYM] >>
  simp[csuc_def] >>
  DEEP_INTRO_TAC oleast_intro >> rw[]
  >- metis_tac[cardinality_bump_exists] >>
  ‘preds a = { y | preds y <<= preds Aord' }’
    by (simp[EXTENSION] >> rw[EQ_IMP_THM]
        >- metis_tac[CARD_LE_CONG, cardeq_REFL, cardeq_SYM] >>
        irule cardlt_preds >>
        first_assum $ C (resolve_then (Pos hd) irule) CARD_LET_TRANS >>
        metis_tac[CARD_LT_CONG, cardeq_REFL]) >>
  simp[cardlt_lepreds]
QED

Theorem le_cardSUC[simp]:
  A <<= cardSUC A
Proof
  metis_tac[lt_cardSUC, cardleq_lteq]
QED

Theorem omega_LEQ_INFINITE_preds:
  INFINITE (preds a) ==> omega <= a
Proof
  CONV_TAC CONTRAPOS_CONV >> simp[FINITE_preds, lt_omega]
QED

Theorem csuc_EQ_N[simp]:
  csuc a = &n <=> ?m. n = SUC m /\ a = &m
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> qx_gen_tac ‘b’ >> rpt strip_tac >>
  simp[EQ_IMP_THM, PULL_EXISTS] >> rw[]
  >- (Cases_on ‘n’ >> gvs[] >>
      rename [‘a = &m’, ‘preds a <</= preds (ordSUC (&m))’] >>
      ‘FINITE (preds (ordSUC (&m) : ('a + num -> bool) ordinal))’
        by simp[FINITE_preds, GSYM fromNat_SUC, Excl "fromNat_SUC"] >>
      ‘FINITE (preds a)’ by metis_tac[CARD_LE_FINITE, cardleq_lteq] >>
      gvs[FINITE_preds, preds_nat,GSYM fromNat_SUC, Excl "fromNat_SUC"] >>
      rename [‘cardlt (IMAGE $& (count n)) (IMAGE $& (count (SUC m)))’] >>
      gvs[CARD_LE_CARD, CARD_INJ_IMAGE] >> ‘m <= n’ suffices_by simp[] >>
      first_x_assum $ qspec_then ‘&m’ mp_tac >>
      simp[preds_nat, CARD_LE_CARD, CARD_INJ_IMAGE]) >>
  rename [‘preds (&m) <</= preds b’] >>
  ‘FINITE (preds b)’
    by (CCONTR_TAC >> drule_then assume_tac omega_LEQ_INFINITE_preds >>
        ‘&(SUC m) < b’ by (irule ordlte_TRANS >> goal_assum drule >> simp[]) >>
        first_x_assum drule >> simp[preds_nat, CARD_LE_CARD, CARD_INJ_IMAGE]) >>
  gvs[FINITE_preds] >>
  gvs[CARD_LE_CARD, CARD_INJ_IMAGE, preds_nat, GSYM fromNat_SUC,
      Excl "fromNat_SUC", arithmeticTheory.NOT_LESS_EQUAL] >>
  ‘n - 1 <= m’ suffices_by simp[] >>
  first_x_assum $ qspec_then ‘&(n - 1)’ mp_tac >>
  simp[preds_nat, CARD_LE_CARD, CARD_INJ_IMAGE]
QED

Theorem FINITE_cardSUC[simp]:
  FINITE (cardSUC A) <=> FINITE A
Proof
  simp[cardSUC_def, FINITE_preds] >> DEEP_INTRO_TAC oleast_intro >>
  rpt strip_tac
  >- (irule cardeq_ordinals_exist >>
      resolve_then (Pos hd) irule CARD_LE_UNIV cardleq_TRANS >>
      simp[disjUNION_UNIV, CARD_LE_ADDL]) >>
  eq_tac
  >- (strip_tac >> gvs[] >> drule_then irule (iffLR CARDEQ_FINITE) >>
      simp[preds_nat]) >>
  strip_tac >> drule_then drule (iffRL CARDEQ_FINITE) >>
  simp[FINITE_preds]
QED

Theorem cardleq_preds_csuc:
  preds a <<= preds b ==> preds (csuc a) <<= preds (csuc b)
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> rw[] >>
  DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> rw[] >>
  rename [‘preds a <<= preds b’, ‘preds b <</= preds c’,
          ‘preds a <</= preds d’] >>
  CCONTR_TAC >>
  ‘?c' : ('a + num -> bool) ordinal.
     orderiso (wobound c allOrds) (wobound c' allOrds) /\
     preds c =~ preds c'’
    by (irule transfer_ordinals >>
        resolve_then (Pos last) irule preds_inj_univ cardleq_TRANS >>
        metis_tac[cardleq_lteq]) >>
  ‘preds c' <</= preds d’ by metis_tac[CARD_LT_CONG, cardeq_REFL] >>
  drule_then assume_tac cardlt_preds >> first_x_assum drule >>
  metis_tac[CARD_LE_TRANS, CARD_LET_TRANS, CARD_LT_REFL, CARD_LT_CONG,
            cardeq_REFL]
QED

(* uncountable ordinals *)
Type ucinf = “:('a + num -> bool) inf”
Type ucord = “:('a + num -> bool) ordinal”


Theorem ucinf_uncountable: ~countable univ(:'a ucinf)
Proof
  simp[SUM_UNIV, UNIV_FUN_TO_BOOL, infinite_pow_uncountable]
QED

Theorem Unum_cardlt_ucinf: univ(:num) <</= univ(:'a ucinf)
Proof
  simp[cardlt_lenoteq] >> conj_tac
  >- (simp[cardleq_def] >> qexists_tac `INL` >> simp[INJ_INL]) >>
  strip_tac >> drule countable_cardeq >>
  simp[ucinf_uncountable, num_countable] >> strip_tac >>
  resolve_then Any drule UNIV_fun_exp (iffLR countable_cardeq) >>
  simp[countable_setexp, SUM_UNIV]
QED

Theorem Unum_cardle_ucinf: univ(:num) <<= univ(:'a ucinf)
Proof
  simp[cardleq_lteq, Unum_cardlt_ucinf]
QED

Theorem ucord_sup_exists_lemma:
  { a:'a ucord | countableOrd a } <<= univ(:'a ucinf)
Proof
  spose_not_then assume_tac >> fs[cardlt_lenoteq] >>
  `?f. INJ f univ(:'a ucinf) {a:'a ucord | countableOrd a}`
     by metis_tac[cardleq_def] >>
  `(!u. countableOrd (f u)) /\ (!u v. f u = f v <=> u = v)`
      by fs[INJ_IFF] >>
  qabbrev_tac `fU = IMAGE f univ(:'a ucinf)` >>
  `fU <<= univ(:'a ucinf)` by simp[Abbr`fU`, IMAGE_cardleq] >>
  drule_then assume_tac sup_thm >>
  Cases_on `countableOrd (sup fU)`
  >- (`!u. f u <= sup fU`
        by (gen_tac >> match_mp_tac suple_thm >> simp[Abbr`fU`]) >>
      qsuff_tac `univ(:'a ucinf) <<= preds (sup fU)`
      >- (strip_tac >>
          `preds (sup fU) <<= univ(:num)` by fs[countable_thm] >>
          drule_all cardleq_TRANS >>
          REWRITE_TAC [GSYM countable_thm, ucinf_uncountable]) >>
      Cases_on `?u. f u = sup fU`
      >- (pop_assum strip_assume_tac >>
          `!v. v <> u ==> f v < sup fU` by metis_tac[ordle_lteq] >>
          qabbrev_tac `U0 = univ(:'a ucinf) DELETE u` >>
          `univ(:'a ucinf) = u INSERT U0`
             by metis_tac[INSERT_DELETE, IN_UNIV] >>
          `U0 =~ univ(:'a ucinf)`
             by metis_tac[finite_countable, FINITE_DELETE, ucinf_uncountable,
                          cardeq_SYM, CARDEQ_INSERT_RWT] >>
          qsuff_tac `U0 <<= preds (sup fU)`
          >- metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
          simp[cardleq_def] >> qexists_tac `f` >>
          simp[INJ_DEF, Abbr`U0`]) >>
      pop_assum (fn th => `!u. f u < sup fU` by metis_tac[ordle_lteq, th]) >>
      simp[cardleq_def] >> qexists_tac `f` >> simp[INJ_DEF]) >>
  `{ a:'a ucord | countableOrd a } <<= preds (sup fU)`
    by (match_mp_tac SUBSET_CARDLEQ >> simp[SUBSET_DEF] >>
        qx_gen_tac `c` >> strip_tac >>
        spose_not_then assume_tac >>
        `sup fU <= c` by metis_tac[] >>
        `preds (sup fU) SUBSET preds c`
          by (simp[SUBSET_DEF] >> metis_tac [ordlte_TRANS]) >>
        metis_tac [subset_countable]) >>
  qsuff_tac `preds (sup fU) <<= univ(:'a ucinf)`
  >- metis_tac [cardleq_ANTISYM, cardleq_TRANS] >>
  simp[preds_sup, dclose_BIGUNION] >>
  match_mp_tac CARD_BIGUNION >>
  dsimp[IMAGE_cardleq_rwt] >>
  dsimp[Abbr`fU`] >>
  metis_tac[countable_thm, cardleq_TRANS, Unum_cardle_ucinf]
QED

Definition omega1_def:
  omega1 : 'a ucord = sup { a | countableOrd a }
End
Overload "ω₁" = “omega1”  (* UOK *)

Theorem x_lt_omega1_countable: x < omega1 <=> countableOrd x
Proof
  simp[omega1_def, sup_thm, ucord_sup_exists_lemma, EQ_IMP_THM] >>
  rpt strip_tac >- metis_tac[countableOrds_dclosed] >>
  qexists_tac `x^+` >> simp[preds_ordSUC]
QED

(* |- ~countableOrd omega1 *)
Theorem omega1_not_countable =
  x_lt_omega1_countable |> Q.INST[`x` |-> `omega1`] |> SIMP_RULE (srw_ss()) []

Theorem preds_omega_UNIV:
  preds omega =~ univ(:num)
Proof
  simp[cardeq_def] >>
  ONCE_REWRITE_TAC [BIJ_SYM] >>
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF, lt_omega, PULL_EXISTS] >>
  qexists_tac ‘fromNat’ >> simp[]
QED

Theorem preds_omega_lt_preds_omega1:
  preds omega <</= preds (omega1 : ('a + num -> bool) ordinal)
Proof
  assume_tac omega1_not_countable >>
  gs[countable_thm] >>
  resolve_then (Pos hd) (resolve_then (Pos hd) irule cardeq_REFL)
               preds_omega_UNIV (iffRL CARD_LT_CONG) >> simp[]
QED

Theorem csuc_omega:
  csuc omega = omega1
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- irule_at Any preds_omega_lt_preds_omega1 >>
  rpt strip_tac >> irule ordle_ANTISYM >> CCONTR_TAC >> gs[]
  >- (rename [‘a < omega1’, ‘preds omega <</= preds a’] >>
      gs[x_lt_omega1_countable, countable_thm] >>
      metis_tac[CARD_LE_CONG, cardeq_REFL, preds_omega_UNIV]) >>
  first_x_assum drule >> simp[preds_omega_lt_preds_omega1]
QED

(* ----------------------------------------------------------------------
    Connection to topological notions
   ---------------------------------------------------------------------- *)

Definition ival_def:
  ival (a:'a ordinal) b = { e | a < e /\ e < b }
End

(* including rays (2nd disj'n) lets the space cover all ordinals (incl. 0). *)
Theorem order_topology_exists:
  istopology { s | !e. e IN s ==>
                       (?a:'a ordinal b. e IN ival a b /\ ival a b SUBSET s) \/
                       ?b. e < b /\ !d. d < b ==> d IN s }
Proof
  simp[istopology, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
  >- (rpt $ first_x_assum dxrule >> rpt strip_tac >~
      [‘ival _ _ SUBSET s /\ ival _ _ SUBSET t’, ‘ival a b SUBSET s’,
       ‘ival x y SUBSET t’]
      >- (disj1_tac >>
          wlog_tac ‘a <= x’ [‘a’, ‘b’, ‘x’, ‘y’, ‘s’, ‘t’]
          >- (gvs[] >> metis_tac[ordle_lteq]) >>
          qexistsl_tac [‘x’, ‘if y <= b then y else b’] >>
          rw[] >> gvs[ival_def, SUBSET_DEF] >>
          metis_tac[ordlet_TRANS, ordlte_TRANS, ordlt_TRANS]) >~
      [‘ival _ _ SUBSET A /\ ival _ _ SUBSET B’, ‘_ < a ==> _ IN A’,
       ‘_ < b ==> _ IN B’]
      >- (disj2_tac >> qexists_tac ‘if a < b then a else b’ >> rw[] >>
          metis_tac[ordlt_TRANS, ordlte_TRANS]) >>
      rename [‘ival a b SUBSET A’, ‘e < c’] >>
      disj1_tac >> qexistsl_tac [‘a’, ‘if b < c then b else c’] >> rw[] >>
      gvs[ival_def, SUBSET_DEF] >> metis_tac[ordlte_TRANS, ordlt_TRANS]) >>
  qpat_x_assum ‘_ SUBSET _’ mp_tac >>
  simp[SUBSET_DEF, SimpL “$==>”] >> disch_then drule >> simp[] >>
  disch_then drule >> strip_tac >> metis_tac[SUBSET_BIGUNION_SUBSET_I]
QED

Definition ordlt_top_def:
  ordlt_top =
  topology { s | !e. e IN s ==>
                     (?a:'a ordinal b. e IN ival a b /\ ival a b SUBSET s) \/
                     ?b. e < b /\ !d. d < b ==> d IN s }
End

Theorem open_in_ordlt:
  open_in ordlt_top s <=>
  !e. e IN s ==> (?a:'a ordinal b. e IN ival a b /\ ival a b SUBSET s) \/
                 ?b. e < b /\ !d. d < b ==> d IN s
Proof
  simp[topology_tybij |> cj 2 |> iffLR, order_topology_exists, ordlt_top_def]
QED

Theorem topspace_ordlt_top[simp]:
  topspace ordlt_top = UNIV
Proof
  simp[topspace, EXTENSION, open_in_ordlt] >> qx_gen_tac ‘a’ >>
  qexists_tac ‘{ e | e < ordSUC a }’ >> simp[] >> metis_tac[]
QED

Theorem limpt_islimit:
  limpt ordlt_top a (preds a) <=> islimit a /\ a <> 0
Proof
  simp[limpt_thm, EQ_IMP_THM] >> rpt strip_tac >> gvs[]
  >- (Cases_on ‘a’ using ord_CASES >> simp[] >>
      rename [‘ordSUC a IN _’] >>
      pop_assum $ qspec_then ‘ival a (ordSUC (ordSUC a))’ mp_tac >> simp[] >>
      rpt strip_tac >~
      [‘open_in’]
      >- (simp[open_in_ordlt] >> metis_tac[SUBSET_REFL]) >>
      simp[ival_def] >>
      rename [‘b = ordSUC a’] >> Cases_on ‘b = ordSUC a’ >> simp[] >>
      ‘b < ordSUC a \/ ordSUC a < b’ by metis_tac[ordlt_trichotomy] >>
      simp[] >> gs[ordlt_SUC_DISCRETE, ordle_lteq])
  >- (pop_assum mp_tac >> simp[] >> qexists_tac ‘{ a | a < 1 }’ >>
      simp[open_in_ordlt] >> metis_tac[]) >>
  gs[open_in_ordlt] >> first_x_assum $ drule_then strip_assume_tac >~
  [‘a IN ival x y’, ‘ival x y SUBSET A’]
  >- (gs[SUBSET_DEF, ival_def] >>
      ‘ordSUC x < a’ by metis_tac[islimit_SUC_lt] >>
      ‘ordSUC x IN A’ by metis_tac[ordlt_SUC, ordlt_TRANS] >>
      metis_tac[ordlt_REFL]) >>
  qexists_tac ‘0’ >> simp[] >>
  metis_tac[ordleq0, ordlt_TRANS]
QED

Theorem open_sing_nonlimit:
  open_in ordlt_top {x} <=> ~islimit x \/ x = 0
Proof
  qspec_then ‘x’ strip_assume_tac ord_CASES >> simp[] >~
  [‘open_in _ {0}’]
  >- (simp[open_in_ordlt] >> disj2_tac >> qexists_tac ‘1’ >>
      simp[ordlt_fromNat, PULL_EXISTS]) >~
  [‘open_in _ {ordSUC a}’]
  >- (simp[open_in_ordlt] >> disj1_tac >>
      qexistsl_tac [‘a’, ‘ordSUC (ordSUC a)’] >>
      simp[ival_def, SUBSET_DEF] >>
      qx_gen_tac ‘b’ >> Cases_on ‘b = ordSUC a’ >> simp[] >>
      ‘b < ordSUC a \/ ordSUC a < b’ by metis_tac[ordlt_trichotomy] >>
      simp[] >> CCONTR_TAC >> gs[ordlt_SUC_DISCRETE, ordle_lteq] >>
      metis_tac[ordlt_TRANS, ordlt_REFL]) >>
  ‘x <> 0’ by (strip_tac >> gvs[]) >> simp[open_in_ordlt] >>
  rw[] >> simp[ival_def, SUBSET_DEF] >~
  [‘x <= a’, ‘b <= x’]
  >- (Cases_on ‘x <= a’ >> gs[] >>
      Cases_on ‘b <= x’ >> gs[] >>
      ‘ordSUC a < x’ by simp[islimit_SUC_lt] >> qexists_tac ‘ordSUC a’ >>
      simp[] >> metis_tac[ordlt_TRANS, ordlt_REFL]) >>
  rename [‘a <= x’, ‘_ <> x’] >>
  Cases_on ‘x < a’ >> simp[] >> qexists_tac ‘0’  >>
  metis_tac[ordleq0, ordlt_TRANS]
QED

Theorem rays_open:
  open_in ordlt_top { x | x < a } /\
  open_in ordlt_top { x | a < x }
Proof
  conj_tac >- (simp[open_in_ordlt] >> metis_tac[]) >>
  qabbrev_tac ‘k = { ival a b | b | T}’ >>
  ‘!s. s IN k ==> open_in ordlt_top s’
    by (simp[Abbr‘k’, open_in_ordlt, PULL_EXISTS] >>
        metis_tac[SUBSET_REFL]) >>
  ‘{ x | a < x } = BIGUNION k’ suffices_by metis_tac[OPEN_IN_BIGUNION] >>
  simp[Once EXTENSION, Abbr‘k’, PULL_EXISTS, ival_def] >>
  metis_tac[ordlt_SUC]
QED


Theorem closed_sing:
  closed_in ordlt_top {x}
Proof
  simp[closed_in] >>
  ‘UNIV DIFF {x} = {y | y < x} UNION {y | x < y}’
    by (simp[EXTENSION] >> metis_tac[ordlt_trichotomy, ordlt_REFL]) >>
  simp[OPEN_IN_UNION, rays_open]
QED


val _ = export_theory()
