Theory ordinalBasic[bare]

Ancestors
  wellorder pred_set set_relation pair
Libs
  HolKernel Parse boolLib boolSimps simpLib BasicProvers QLib metisLib
  TotalDefn pred_setLib

fun bossify stac ths = stac (srw_ss() ++ numSimps.ARITH_ss) ths
val simp = bossify asm_simp_tac
val fs = bossify full_simp_tac
val gvs = bossify (global_simp_tac {droptrues = true, elimvars = true,
                                    oldestfirst = true, strip = true})
val gs = bossify (global_simp_tac {droptrues = true, elimvars = false,
                                   oldestfirst = true, strip = true})
val rw = srw_tac[numSimps.ARITH_ss]
val metis_tac = METIS_TAC

(* perform quotient, creating a type of "ordinals". *)
fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = NONE, fname = s, func = t};

Theorem orderiso_equiv[local]:
    !s1 s2. orderiso (s1:'a wellorder) (s2:'a wellorder) <=>
            (orderiso s1 : 'a wellorder set = orderiso s2)
Proof
  rw[FUN_EQ_THM, EQ_IMP_THM] >>
  metis_tac [orderiso_SYM, orderiso_TRANS, orderiso_REFL]
QED

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

Theorem ordlt_REFL[simp] = ordlt_REFL
Theorem ordlt_TRANS = ordlt_TRANS
Theorem ordlt_WF0 = ordlt_WF0
Theorem ordlt_WF =
  REWRITE_RULE [GSYM relationTheory.WF_DEF] ordlt_WF0

Overload "<" = ``ordlt``
Overload "<=" = ``\a b. ~(b < a)``

Theorem ordlt_trichotomy = ordlt_trichotomy

Overload mkOrdinal = ``ordinal_ABS``

Definition allOrds_def:
  allOrds = mkWO { (x,y) | (x = y) \/ ordlt x y }
End

Theorem wellorder_allOrds:
    wellorder { (x,y) | x = y \/ ordlt x y }
Proof
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
  ]
QED

Theorem WIN_allOrds:
    (x,y) WIN allOrds <=> ordlt x y
Proof
  simp[allOrds_def, destWO_mkWO, wellorder_allOrds, strict_def] >>
  metis_tac [ordlt_REFL]
QED

Theorem elsOf_allOrds:
    elsOf allOrds = univ(:'a ordinal)
Proof
  rw[elsOf_def, EXTENSION, in_domain, in_range, allOrds_def,
     destWO_mkWO, wellorder_allOrds] >>
  metis_tac [ordlt_trichotomy]
QED

val (mkOrdinal_REP, orderiso_mkOrdinal) =
  theorem "ordinal_QUOTIENT"
          |> SIMP_RULE (srw_ss()) [quotientTheory.QUOTIENT_def, orderiso_REFL]
          |> CONJ_PAIR
Theorem mkOrdinal_REP = mkOrdinal_REP
Theorem orderiso_mkOrdinal = orderiso_mkOrdinal

Theorem ordlt_mkOrdinal:
    ordlt o1 o2 <=>
    !w1 w2. (mkOrdinal w1 = o1) /\ (mkOrdinal w2 = o2) ==> orderlt w1 w2
Proof
  rw[definition "ordlt_def"] >> eq_tac >> rpt strip_tac >| [
    `orderiso w1 (ordinal_REP o1) /\ orderiso w2 (ordinal_REP o2)`
      by metis_tac [orderiso_mkOrdinal, mkOrdinal_REP] >>
    metis_tac [orderlt_orderiso],
    simp[mkOrdinal_REP]
  ]
QED

Theorem orderlt_iso_REFL:
    orderiso w1 w2 ==> ~orderlt w1 w2
Proof
  metis_tac [orderlt_orderiso, orderlt_REFL, orderiso_REFL]
QED

Theorem orderiso_wobound2:
    orderiso (wobound x w) (wobound y w) ==> ~((x,y) WIN w)
Proof
  rpt strip_tac >>
  qsuff_tac `orderlt (wobound x w) (wobound y w)`
     >- metis_tac [orderlt_iso_REFL] >>
  simp[orderlt_def] >> qexists_tac `x` >>
  simp[elsOf_wobound, wobound2,orderiso_REFL]
QED

Theorem wellorder_ordinal_isomorphism:
    !w. orderiso w (wobound (mkOrdinal w) allOrds)
Proof
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
  ]
QED

Definition preds_def:
  preds (w : 'a ordinal) = { w0 | ordlt w0 w }
End

Theorem IN_preds[simp]:
    x IN preds w <=> ordlt x w
Proof
  rw[preds_def]
QED

Theorem preds_11[simp]:
    (preds w1 = preds w2) = (w1 = w2)
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `ordlt w1 w2 \/ ordlt w2 w1` by metis_tac [ordlt_trichotomy] >>
  qpat_x_assum `x = y` mp_tac >> rw[EXTENSION, preds_def] >>
  metis_tac [ordlt_REFL]
QED

Definition downward_closed_def:
  downward_closed s <=>
    !a b. a IN s /\ ordlt b a ==> b IN s
End

Theorem preds_downward_closed:
    downward_closed (preds w)
Proof
  rw[downward_closed_def, preds_def] >> metis_tac [ordlt_TRANS]
QED

Theorem preds_bij:
    BIJ preds UNIV (downward_closed DELETE UNIV)
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, preds_11] >>
  fs[SPECIFICATION, preds_downward_closed] >>
  rw[EXTENSION] >| [
    metis_tac [IN_preds, ordlt_REFL],
    metis_tac [IN_preds, ordlt_REFL],
    qspec_then `\w. w NOTIN x` mp_tac ordlt_WF0 >> simp[] >>
    qsuff_tac `?w. w NOTIN x`
       >- metis_tac [downward_closed_def, ordlt_trichotomy] >>
    fs[EXTENSION] >> metis_tac[]
  ]
QED

Theorem preds_lt_PSUBSET:
    ordlt w1 w2 <=> preds w1 PSUBSET preds w2
Proof
  simp[PSUBSET_DEF, SUBSET_DEF, preds_def, EQ_IMP_THM, EXTENSION] >> conj_tac
    >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
  simp_tac (srw_ss() ++ CONJ_ss) [] >>
  metis_tac [ordlt_REFL, ordlt_TRANS, ordlt_trichotomy]
QED

Theorem preds_wobound:
    preds ord = elsOf (wobound ord allOrds)
Proof
  simp[EXTENSION, elsOf_wobound, preds_def, WIN_allOrds]
QED
