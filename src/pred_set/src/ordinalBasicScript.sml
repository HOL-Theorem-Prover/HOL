Theory ordinalBasic[bare]

Ancestors
  wellorder pred_set set_relation pair option cardinal
Libs
  HolKernel Parse boolLib boolSimps simpLib BasicProvers QLib metisLib
  TotalDefn pred_setLib pureSimps TypeBase tautLib[qualified]

fun bossify stac ths = stac (srw_ss() ++ numSimps.ARITH_ss) ths
val simp = bossify asm_simp_tac
fun dsimp ths = simp(SF DNF_ss :: ths)
val fs = bossify full_simp_tac
val gvs = bossify (global_simp_tac {droptrues = true, elimvars = true,
                                    oldestfirst = true, strip = true})
val gs = bossify (global_simp_tac {droptrues = true, elimvars = false,
                                   oldestfirst = true, strip = true})
val rw = srw_tac[numSimps.ARITH_ss]
val metis_tac = METIS_TAC

val impI = tautLib.TAUT_PROVE ``~p \/ q <=> (p ==> q)``

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

Theorem ordSUC_MONO[simp]:
    a^+ < b^+ <=> a < b
Proof
  eq_tac >> spose_not_then strip_assume_tac
  >- (fs[ordlt_SUC_DISCRETE]
      >- (`(a = b) \/ b < a` by metis_tac [ordlt_trichotomy] >>
          metis_tac [ordlt_TRANS, ordlt_REFL, ordlt_SUC]) >>
      rw[] >> fs[ordlt_SUC]) >>
  fs[ordlt_SUC_DISCRETE] >>
  `b < a^+` by metis_tac [ordlt_trichotomy] >>
  fs[ordlt_SUC_DISCRETE] >> metis_tac [ordlt_TRANS, ordlt_REFL]
QED

Theorem ordSUC_11[simp]:
    (a^+ = b^+) <=> (a = b)
Proof
  simp[EQ_IMP_THM] >> strip_tac >> spose_not_then assume_tac >>
  `a < b \/ b < a` by metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_REFL, ordSUC_MONO]
QED

Definition sup_def:
  sup ordset = oleast a. a NOTIN BIGUNION (IMAGE preds ordset)
End

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

val ordADD_def = new_specification(
  "ordADD_def", ["ordADD"],
  ord_RECURSION |> Q.ISPEC `b:'a ordinal` |> Q.SPEC `\(x:'a ordinal) r. r^+`
                |> Q.SPEC `\x rs. sup rs`
                |> SIMP_RULE (srw_ss()) []
                |> Q.GEN `b`
                |> CONV_RULE SKOLEM_CONV)
val _ = export_rewrites ["ordADD_def"]
Overload "+" = ``ordADD``

Theorem sup_preds_omax_NONE:
    (omax (preds a) = NONE) <=> (sup (preds a) = a)
Proof
  simp[omax_NONE, sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  simp_tac(srw_ss() ++ DNF_ss) [impI] >>
  qexists_tac `a` >> conj_tac >- simp[ordle_lteq] >>
  qx_gen_tac `c` >> strip_tac >> Tactical.REVERSE eq_tac
  >- (rw[] >> metis_tac[]) >>
  strip_tac >> qsuff_tac `c <= a /\ a <= c` >- metis_tac [ordlt_trichotomy] >>
  metis_tac [ordlt_TRANS, ordlt_REFL]
QED

Theorem ordADD_0L[simp]:
    !a:'a ordinal. 0 + a = a
Proof
  ho_match_mp_tac simple_ord_induction >> simp[] >> qx_gen_tac `a` >>
  strip_tac >>
  `IMAGE ($+ 0) (preds a) = preds a`
    by (rpt (asm_simp_tac (srw_ss() ++ CONJ_ss)[EXTENSION])) >>
  fs[sup_preds_omax_NONE]
QED

Theorem ordADD_fromNat[simp]:
    ordADD (&n) (&m) = &(n + m)
Proof
  Induct_on `m` >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem ordleq0[simp]:
    (x:'a ordinal) <= 0 <=> (x = 0)
Proof
  eq_tac >> simp[ordle_lteq]
QED

Theorem sup_EQ_0:
  s:'a ordinal set <<= univ(:'a inf) ==> (sup s = 0 <=> s = {} \/ s = {0})
Proof
  strip_tac >>
  qspec_then `0` (mp_tac o Q.AP_TERM `$~`) (sup_thm |> UNDISCH_ALL) >>
  simp_tac pure_ss [NOT_EXISTS_THM] >> simp[impI] >>
  disch_then (K ALL_TAC) >> simp[EXTENSION] >> metis_tac[]
QED

Theorem fromNat_11[simp]:
  !x y. (&x:'a ordinal = &y) = (x = y)
Proof
  Induct >- (Cases >> simp[]) >> Cases >> simp[]
QED

Theorem ORD_ONE[simp]:
    0^+ = 1
Proof
  simp_tac bool_ss [GSYM fromNat_SUC] >> simp[]
QED

Theorem ordSUC_NUMERAL[simp]:
    (&NUMERAL n)^+ = &(NUMERAL n + 1)
Proof
  simp[GSYM arithmeticTheory.ADD1]
QED

Theorem ordZERO_ltSUC[simp]:
    0 < x^+
Proof
  metis_tac [ordSUC_ZERO, ordlt_ZERO, ordlt_trichotomy]
QED

Theorem IFF_ZERO_lt:
    (x:'a ordinal <> 0 <=> 0 < x) /\ (1 <= x <=> 0 < x)
Proof
  REWRITE_TAC [GSYM ORD_ONE] >> simp[ordlt_SUC_DISCRETE] >>
  metis_tac [ordlt_trichotomy, ordlt_ZERO]
QED

Theorem islimit_SUC[simp]:
    islimit x^+ <=> F
Proof
  simp[omax_NONE, impI, ordlt_SUC_DISCRETE] >>
  metis_tac[ordle_lteq]
QED

Theorem preds_0[simp]:
    preds 0 = {}
Proof
  simp[preds_def]
QED

Theorem preds_EQ_EMPTY[simp]:
    preds x = {} <=> x = 0
Proof
  simp[EQ_IMP_THM] >> simp[EXTENSION] >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

Theorem islimit_fromNat[simp]:
  islimit &x <=> x = 0
Proof
  Cases_on `x` >> simp[]
QED

Theorem ordle_ANTISYM:
    a <= b /\ b <= a ==> (a = b)
Proof
  metis_tac [ordlt_trichotomy]
QED

Theorem ordle_TRANS:
    !x y z. (x:'a ordinal) <= y /\ y <= z ==> x <= z
Proof
  metis_tac [ordlt_TRANS, ordle_lteq]
QED

Theorem ordlet_TRANS:
    !x y z. (x:'a ordinal) <= y /\ y < z ==> x < z
Proof
  metis_tac [ordle_lteq, ordlt_TRANS]
QED
Theorem ordlte_TRANS:
    !x y z. (x:'a ordinal) < y /\ y <= z ==> x < z
Proof
  metis_tac [ordle_lteq, ordlt_TRANS]
QED

Theorem ubsup_thm:
    (!a. a IN s ==> a < b) ==> !c. c < sup s <=> ?d. d IN s /\ c < d
Proof
  strip_tac >> simp[sup_def] >> gen_tac >> DEEP_INTRO_TAC oleast_intro >>
  dsimp[impI] >>
  qexists_tac `b` >> conj_tac >- metis_tac [ordlt_TRANS, ordlt_REFL] >>
  qx_gen_tac `a` >> strip_tac >> eq_tac >- metis_tac[] >>
  disch_then (Q.X_CHOOSE_THEN `d` strip_assume_tac) >>
  `d <= a`by metis_tac[] >> fs[ordle_lteq] >> rw[] >> metis_tac [ordlt_TRANS]
QED

Theorem sup_eq_max:
    (!b. b IN s ==> b <= a) /\ a IN s ==> sup s = a
Proof
  strip_tac >>
  `!b. b IN s ==> b < a^+` by fs[ordlt_SUC_DISCRETE, ordle_lteq] >>
  pop_assum (assume_tac o MATCH_MP ubsup_thm) >>
  `a <= sup s` by metis_tac [ordlt_REFL] >>
  `sup s <= a` by simp[impI] >>
  metis_tac [ordle_ANTISYM]
QED

Theorem sup_EMPTY[simp]:
    sup {} = 0
Proof
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >>
  qx_gen_tac `a` >> disch_then (qspec_then `0` mp_tac) >>
  simp[ordle_lteq]
QED

Theorem sup_SING[simp]:
    sup {a} = a
Proof
  simp[sup_def] >> DEEP_INTRO_TAC oleast_intro >> simp[] >> conj_tac >-
    (qexists_tac `a` >> simp[]) >>
  simp[] >> qx_gen_tac `b` >> rw[ordle_lteq] >>
  metis_tac [ordlt_REFL]
QED

Theorem sup_preds_SUC:
    sup (preds a^+) = a
Proof
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
  res_tac >> fs[ordlt_SUC]
QED

Theorem preds_ordSUC:
    preds a^+ = a INSERT preds a
Proof
  simp[EXTENSION, ordlt_SUC_DISCRETE] >> metis_tac[]
QED

Theorem preds_nat:
  preds (&n) = IMAGE fromNat (count n)
Proof
  Induct_on ‘n’ >> simp[preds_ordSUC, COUNT_SUC]
QED

Theorem islimit_SUC_lt:
    islimit b /\ a < b ==> a^+ < b
Proof
  fs[omax_NONE] >> metis_tac [ordlt_SUC_DISCRETE, ordlt_trichotomy, ordle_lteq]
QED

Theorem predimage_sup_thm:
    !b:'a ordinal.
          b < sup (IMAGE f (preds (a:'a ordinal))) <=> ?d. d < a /\ b < f d
Proof
  match_mp_tac (sup_thm |> Q.INST [`s` |-> `IMAGE f (preds (a:'b ordinal))`]
                        |> SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  metis_tac [cardleq_TRANS, IMAGE_cardleq, preds_inj_univ]
QED

Theorem lemma[local]:
    !c a b:'a ordinal. a < b /\ b < a + c ==> ?d. a + d = b
Proof
  ho_match_mp_tac simple_ord_induction >> simp[] >> rpt conj_tac
  >- metis_tac [ordlt_TRANS, ordlt_REFL]
  >- (simp[ordlt_SUC_DISCRETE] >> metis_tac[]) >>
  simp[predimage_sup_thm]
QED

Theorem lt_suppreds =
  predimage_sup_thm |> Q.INST [`f` |-> `\x. x`] |> SIMP_RULE (srw_ss()) []

Theorem ordlt_CANCEL_ADDR[simp]:
    !(b:'a ordinal) a. a < a + b <=> 0 < b
Proof
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (qx_gen_tac `b` >> strip_tac >> qx_gen_tac `a` >>
      Cases_on `b = 0` >- simp[] >>
      match_mp_tac ordlt_TRANS >> qexists_tac `a^+` >> simp[] >>
      spose_not_then strip_assume_tac >> fs[ordle_lteq]) >>
  simp_tac (srw_ss() ++ CONJ_ss)[predimage_sup_thm] >> rpt strip_tac >>
  simp[GSYM lt_suppreds] >> fs[sup_preds_omax_NONE]
QED

Theorem ordlt_CANCEL_ADDL[simp]:
    a + b < a <=> F
Proof
  simp[ordle_lteq] >> Cases_on `0 < b` >> simp[] >>
  fs[ordleq0]
QED

fun mklesup th =
    th |> UNDISCH_ALL |> Q.SPEC `sup s`
       |> SIMP_RULE (srw_ss()) [] |> REWRITE_RULE [impI] |> DISCH_ALL

Theorem Unum_cle_Uinf:
    univ(:num) <<= univ(:'a inf)
Proof
  simp[cardleq_def] >> qexists_tac `INL` >> simp[INJ_INL]
QED

Theorem csup_thm:
    countable (s : 'a ordinal set) ==> !b. b < sup s <=> ?d. d IN s /\ b < d
Proof
  simp[countable_thm] >>
  metis_tac [sup_thm, cardleq_def, Unum_cle_Uinf, cardleq_TRANS]
QED

(* |- countable s ==> !d. d IN s ==> d <= sup s *)
Theorem csup_lesup = mklesup csup_thm

fun mksuple th =
    th |> UNDISCH_ALL |> Q.SPEC `b` |> AP_TERM ``$~``
       |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
       |> REWRITE_RULE [impI]
       |> DISCH_ALL

Theorem csup_suple = mksuple csup_thm


Theorem ordADD_CANCEL_LEMMA0[local]:
    a = a + c <=> c = 0
Proof
  Cases_on `c = 0` >> simp[] >>
  qsuff_tac `a < a + c` >- metis_tac[ordlt_REFL] >> simp[] >>
  spose_not_then strip_assume_tac >> fs[ordle_lteq]
QED
Theorem ordADD_CANCEL1[simp] =
  CONJ (GEN_ALL ordADD_CANCEL_LEMMA0)
       (ordADD_CANCEL_LEMMA0 |> CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))
                             |> GEN_ALL)

Theorem ordADD_MONO:
    !b:'a ordinal a c. a < b ==> c + a < c + b
Proof
  ho_match_mp_tac simple_ord_induction >> simp[] >> conj_tac
  >- (ntac 2 strip_tac >> simp[ordlt_SUC_DISCRETE] >> rw[] >> rw[]) >>
  qx_gen_tac `b` >> strip_tac >> simp[predimage_sup_thm] >>
  map_every qx_gen_tac [`a`, `c`] >> strip_tac >>
  `?d. d < b /\ a < d`
    by (simp[GSYM lt_suppreds] >> fs[sup_preds_omax_NONE]) >>
  metis_tac[]
QED

Theorem ordlt_CANCEL[simp]:
    !b a (c:'a ordinal). c + a < c + b <=> a < b
Proof
  simp[EQ_IMP_THM, ordADD_MONO] >> rpt strip_tac >>
  metis_tac[ordlt_trichotomy, ordlt_REFL, ordlt_TRANS, ordADD_MONO]
QED

Theorem ordADD_RIGHT_CANCEL[simp]:
    !b a c. ((a:'a ordinal) + b = a + c) <=> (b = c)
Proof
  metis_tac[ordlt_trichotomy, ordADD_MONO, ordlt_REFL]
QED

Theorem leqLEFT_CANCEL[simp]:
    !x a. x <= a + x
Proof
  ho_match_mp_tac simple_ord_induction >> rpt conj_tac >- simp[] >- simp[] >>
  qx_gen_tac `x` >> strip_tac >>
  qx_gen_tac `a` >> strip_tac >>
  `?b. a + x < b /\ b < x` by metis_tac[omax_NONE, IN_preds] >>
  `b <= a + b` by metis_tac[] >>
  `a + x < a + b` by metis_tac [ordle_lteq, ordlt_TRANS] >>
  fs[] >> metis_tac[ordlt_TRANS, ordlt_REFL]
QED

Theorem ordlt_EXISTS_ADD:
  !a b:'a ordinal. a < b <=> ?c. c <> 0 /\ b = a + c
Proof
  simp_tac (srw_ss() ++ DNF_ss) [EQ_IMP_THM] >> Tactical.REVERSE conj_tac
  >- metis_tac[ordlt_trichotomy, ordlt_ZERO] >>
  map_every qx_gen_tac [`a`, `b`] >> strip_tac >>
  `b <= a + b` by simp[] >> fs[ordle_lteq]
  >- (`?c. a + c = b` by metis_tac[lemma] >> rw[] >> strip_tac >> fs[]) >>
  qexists_tac `b` >> simp[] >> strip_tac >> fs[]
QED

Theorem ordle_EXISTS_ADD:
    !a b:'a ordinal. a <= b <=> ?c. b = a + c
Proof
  simp[ordle_lteq] >> metis_tac [ordlt_EXISTS_ADD, ordADD_def]
QED


(* ----------------------------------------------------------------------
    Results about cardinalities of ordinal predecessor sets
   ---------------------------------------------------------------------- *)

Definition omega_def:
  omega = sup { fromNat i | T }
End
Overload "ω" = ``omega``

Definition csuc_def:
  csuc (a : 'a ordinal) =
  oleast (b: ('a + num -> bool) ordinal). preds a <</= preds b
End

Definition cardSUC_def:
  cardSUC (s : 'a set) = preds $ csuc (oleast a:'a ordinal. preds a =~ s)
End

Definition dclose_def:  dclose s = { x:'a ordinal | ?y. y IN s /\ x < y }
End

Theorem preds_sup:
    s <<= univ(:'a inf) ==> (preds (sup s:'a ordinal) = dclose s)
Proof
  simp[EXTENSION, sup_thm, dclose_def]
QED

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

Theorem suple_thm:
    !b s:'a ordinal set. s <<= univ(:'a inf) /\ b IN s ==> b <= sup s
Proof
  metis_tac [sup_thm, ordlt_REFL]
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

Theorem ord_CASES:
    !a. (a = 0) \/ (?a0. a = a0^+) \/ (0 < a /\ islimit a)
Proof
  gen_tac >> Cases_on `a = 0` >- simp[] >>
  `0 < a` by metis_tac [ordlt_trichotomy, ordlt_ZERO] >>
  Cases_on `omax (preds a)` >> simp[] >>
  fs[preds_omax_SOME_SUC]
QED

Theorem ordlt_fromNat:
    !n (x:'a ordinal). x < &n <=> ?m. (x = &m) /\ m < n
Proof
  Induct >>
  dsimp [ordlt_SUC_DISCRETE, numLib.DECIDE ``m < SUC n <=> m < n \/ (m = n)``]
QED

Theorem fromNat_ordlt[simp]:
    (&n:'a ordinal < &m) <=> (n < m)
Proof
  simp[ordlt_fromNat]
QED

Theorem allNats_dwardclosedetc[local]:
    downward_closed { fromNat i : 'a ordinal | T } /\
    { fromNat i | T } <> univ(:'a ordinal)
Proof
  simp[downward_closed_def] >> conj_tac
  >- (map_every qx_gen_tac [`a`, `b`] >>
      disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `i` assume_tac)
                                  assume_tac) >>
      rw[] >> fs[ordlt_fromNat]) >>
  qsuff_tac `{&i : 'a ordinal | T} <<= univ(:'a inf)`
  >- metis_tac [univ_ord_greater_cardinal] >>
  simp[cardleq_def] >> qexists_tac `\a. INL (@n. &n = a)` >>
  simp[INJ_DEF] >> rw[] >> fs[]
QED

Theorem preds_sup_thm:
    downward_closed s /\ s <> univ(:'a ordinal) ==>
    !b. b < sup s <=> ?d. d IN s /\ b < d
Proof
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
  rw[]
QED

Theorem preds_lesup = mklesup preds_sup_thm
Theorem preds_suple = mksuple preds_sup_thm

val lt_omega0 =
  MATCH_MP preds_sup_thm allNats_dwardclosedetc
           |> SIMP_RULE (srw_ss() ++ DNF_ss) [SYM omega_def, ordlt_fromNat]

Theorem lt_omega:
    !a. a < omega <=> ?m. a = &m
Proof
  simp_tac (srw_ss() ++ DNF_ss) [lt_omega0, EQ_IMP_THM] >> qx_gen_tac `n` >>
  qexists_tac `SUC n` >> simp[]
QED

Theorem fromNat_lt_omega[simp]:
    !n. &n < omega
Proof
  simp[lt_omega]
QED

Theorem fromNat_eq_omega[simp]:
    !n. &n <> omega
Proof
  metis_tac [ordlt_REFL, fromNat_lt_omega]
QED

Theorem omax_preds_omega:
    omax (preds omega) = NONE
Proof
  simp_tac (srw_ss() ++ DNF_ss) [omax_NONE, lt_omega] >> qx_gen_tac `m` >>
  qexists_tac `SUC m` >> simp[]
QED
Theorem omega_islimit = omax_preds_omega

Theorem ordADD_fromNat_omega:
    &n + omega = omega
Proof
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
  qexists_tac `m+1` >> numLib.DECIDE_TAC
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

Theorem dclose_BIGUNION:
    dclose s = BIGUNION (IMAGE preds s)
Proof
  dsimp[Once EXTENSION, dclose_def] >> metis_tac[]
QED

Theorem cardSUC_EQ0[simp]:
  cardSUC A <> {}
Proof
  simp[cardSUC_def]
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

Theorem preds_csuc_lemma:
  preds a ≼ preds (csuc a)
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> metis_tac[cardleq_lteq]
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
