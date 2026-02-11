Theory ordinalBasic[bare]

Ancestors
  wellorder pred_set set_relation pair option cardinal
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

Definition oleast_def:
  $oleast (P:'a ordinal -> bool) = @x. P x /\ !y. y < x ==> ~P y
End

val _ = set_fixity "oleast" Binder

Theorem oleast_intro:
    !Q P. (?a. P a) /\ (!a. (!b. b < a ==> ~ P b) /\ P a ==> Q a) ==>
          Q ($oleast P)
Proof
  rw[oleast_def] >> SELECT_ELIM_TAC >> conj_tac >-
    (match_mp_tac ordlt_WF0 >> metis_tac[]) >>
  rw[]
QED

Definition ordSUC_def:
  ordSUC a = oleast b. a < b
End
Overload TC = ``ordSUC``

Definition fromNat_def:
  (fromNat 0 = oleast a. T) /\
  (fromNat (SUC n) = ordSUC (fromNat n))
End
Theorem fromNat_SUC[simp] = fromNat_def |> CONJUNCT2

val _ = add_numeral_form (#"o", SOME "fromNat")

(* recursion principles *)
Theorem restrict_away[local]:
    IMAGE (RESTRICT f $< (a:'a ordinal)) (preds a) = IMAGE f (preds a)
Proof
  rw[EXTENSION, relationTheory.RESTRICT_DEF] >> srw_tac[CONJ_ss][]
QED

Theorem preds_inj_univ:
    preds (ord:'a ordinal) <<= univ(:'a inf)
Proof
  simp[preds_wobound] >>
  qspec_then `ordinal_REP ord` mp_tac wellorder_ordinal_isomorphism >>
  simp[mkOrdinal_REP] >> strip_tac >> imp_res_tac orderiso_SYM >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss())[orderiso_thm]) >>
  simp[cardleq_def] >> qexists_tac `f` >>
  fs[BIJ_DEF, INJ_DEF]
QED

Theorem univ_ord_greater_cardinal:
    ~(univ(:'a ordinal) <<= univ(:'a inf))
Proof
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
  fs[orderlt_REFL]
QED

(* prints as 0 <= a *)
Theorem ordlt_ZERO[simp]:
    ~(a < 0)
Proof
 simp[fromNat_def] >> DEEP_INTRO_TAC oleast_intro >> simp[]
QED

Theorem preds_surj =
  preds_bij |> SIMP_RULE (srw_ss()) [BIJ_DEF] |> CONJUNCT2
            |> SIMP_RULE (srw_ss()) [SURJ_DEF] |> CONJUNCT2
            |> REWRITE_RULE [SPECIFICATION];

Theorem no_maximal_ordinal:
    !a. ?b. a < b
Proof
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
  simp[PSUBSET_DEF, EXTENSION] >> metis_tac [ordlt_REFL]
QED

Theorem ordlt_SUC[simp]:
    a < ordSUC a
Proof
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- metis_tac[no_maximal_ordinal] >> simp[]
QED

Theorem ordSUC_ZERO[simp]:
    ordSUC a <> 0
Proof
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- metis_tac [ordlt_SUC] >>
  rpt strip_tac >> fs[]
QED

Definition omax_def:
  omax (s : 'a ordinal set) =
    some a. maximal_elements s { (x,y) | x <= y } = {a}
End

Theorem ordle_lteq:
    (a:'a ordinal) <= b <=> a < b \/ (a = b)
Proof
  metis_tac [ordlt_trichotomy, ordlt_REFL, ordlt_TRANS]
QED

Theorem omax_SOME:
    (omax s = SOME a) <=> a IN s /\ !b. b IN s ==> b <= a
Proof
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
  fs[] >> metis_tac []
QED

Theorem omax_NONE:
    (omax s = NONE) <=> !a. a IN s ==> ?b. b IN s /\ a < b
Proof
  simp[omax_def] >> DEEP_INTRO_TAC some_intro >>
  simp[maximal_elements_def, EXTENSION] >>
  metis_tac [ordle_lteq]
QED

Theorem omax_EMPTY[simp]:
    omax {} = NONE
Proof
  simp[omax_NONE]
QED

Theorem ordlt_DISCRETE1:
    ~(a < b /\ b < ordSUC a)
Proof
  simp[ordSUC_def] >> DEEP_INTRO_TAC oleast_intro >> conj_tac >-
  metis_tac [ordlt_SUC] >> metis_tac [ordle_lteq]
QED

Theorem ordlt_SUC_DISCRETE:
    a < ordSUC b <=> a < b \/ (a = b)
Proof
  Tactical.REVERSE eq_tac >- metis_tac [ordlt_TRANS, ordlt_SUC] >>
  metis_tac [ordlt_trichotomy, ordlt_DISCRETE1]
QED

Theorem preds_omax_SOME_SUC:
    (omax (preds a) = SOME b) <=> (a = b^+)
Proof
  simp[omax_SOME] >> eq_tac >> strip_tac
  >- (qsuff_tac `a <= b^+ /\ b^+ <= a` >- metis_tac [ordlt_trichotomy] >>
      rpt strip_tac >- metis_tac [ordlt_SUC] >>
      metis_tac [ordlt_SUC_DISCRETE, ordlt_TRANS, ordlt_REFL]) >>
  simp[ordlt_SUC_DISCRETE, ordle_lteq]
QED

Theorem omax_preds_SUC[simp]: omax (preds a^+) = SOME a
Proof metis_tac [preds_omax_SOME_SUC]
QED

Overload islimit = ``\a:'a ordinal. omax (preds a) = NONE``

Theorem ord_RECURSION:
  !(z:'b) (sf:'a ordinal -> 'b -> 'b) (lf:'a ordinal -> 'b set -> 'b).
    ?h : 'a ordinal -> 'b.
      (h 0 = z) /\
      (!a. h a^+ = sf a (h a)) /\
      !a. 0 < a /\ islimit a ==>
          (h a = lf a (IMAGE h (preds a)))
Proof
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
  strip_tac >> `a <> 0` by metis_tac [ordlt_REFL] >> simp[]
QED

Theorem ord_induction =
  ordlt_WF0 |> Q.SPEC `P` |> CONV_RULE CONTRAPOS_CONV
            |> CONV_RULE (BINOP_CONV NOT_EXISTS_CONV)
            |> CONV_RULE (LAND_CONV (REWRITE_CONV [DE_MORGAN_THM] THENC
                                     ONCE_REWRITE_CONV [DISJ_SYM] THENC
                                     REWRITE_CONV [GSYM IMP_DISJ_THM]))
            |> Q.INST [`P` |-> `\x. ~ P x`] |> BETA_RULE
            |> REWRITE_RULE []
            |> CONV_RULE (RAND_CONV (RENAME_VARS_CONV ["a"]))

Theorem simple_ord_induction:
    !P. P 0 /\ (!a. P a ==> P a^+) /\
        (!a. (omax (preds a) = NONE) /\ 0 < a /\ (!b. b < a ==> P b) ==> P a) ==>
        !a. P a
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac ord_induction >> qx_gen_tac `a` >>
  Cases_on `a = 0` >> simp[] >>
  `(omax (preds a) = NONE) \/ ?a0. omax (preds a) = SOME a0`
    by metis_tac [option_CASES]
  >- (`0 < a` by metis_tac [ordlt_ZERO, ordle_lteq] >> metis_tac[]) >>
  fs[preds_omax_SOME_SUC]
QED
