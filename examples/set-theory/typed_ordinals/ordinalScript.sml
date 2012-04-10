open HolKernel Parse boolLib bossLib
open lcsymtacs
open boolSimps

open set_relationTheory pred_setTheory

val _ = new_theory "ordinal"

val isomorphic_def = Define`
  isomorphic R1 R2 <=>
    ?f. (!x y. R2 (f x) (f y) <=> R1 x y) /\
        (!x y. (f x = f y) = (x = y)) /\
        (!a. ?x. f x = a)
`;

val wellfounded_def = Define`
  wellfounded R <=>
   !s. (?w. w IN s) ==> ?min. min IN s /\ !w. (w,min) IN R ==> w NOTIN s
`;

val wellorder_def = Define`
  wellorder R <=>
    wellfounded R /\ strict_linear_order R (domain R UNION range R)
`;

(* well order examples *)
val wellorder_EMPTY = store_thm(
  "wellorder_EMPTY",
  ``wellorder {}``,
  rw[wellorder_def, wellfounded_def, strict_linear_order_def, transitive_def,
     antisym_def, domain_def, range_def]);

val wellorder_SING = store_thm(
  "wellorder_SING",
  ``wellorder {(x,y)} <=> x <> y``,
  rw[wellorder_def, wellfounded_def] >> eq_tac >| [
    rpt strip_tac >> rw[] >>
    first_x_assum (qspec_then `{x}` mp_tac) >> simp[],

    strip_tac >> conj_tac >| [
      rw[] >> Cases_on `x IN s` >- (qexists_tac `x` >> rw[]) >>
      rw[] >> metis_tac [],
      rw[strict_linear_order_def, domain_def, range_def] >>
      rw[transitive_def]
    ]
  ]);

val rrestrict_SUBSET = store_thm(
  "rrestrict_SUBSET",
  ``rrestrict r s SUBSET r``,
  rw[SUBSET_DEF,rrestrict_def] >> rw[]);



val wellfounded_subset = store_thm(
  "wellfounded_subset",
  ``!r0 r. wellfounded r /\ r0 SUBSET r ==> wellfounded r0``,
  rw[wellfounded_def] >>
  `?min. min IN s /\ !w. (w,min) IN r ==> w NOTIN s` by metis_tac [] >>
  metis_tac [SUBSET_DEF])

val termP_term_REP = #termP_term_REP wellorder_results




val wellorder_TYPDEF = new_type_definition(

val wellorder_results = newtypeTools.rich_new_type(
  "wellorder",
  prove(``?x. wellorder x``, qexists_tac `{}` >> simp[wellorder_EMPTY]))

val iseg_def = Define`iseg w x = { y | (y,x) IN wellorder_REP w }`

val wellorder_rrestrict = store_thm(
  "wellorder_rrestrict",
  ``wellorder (rrestrict (wellorder_REP w) (iseg w x))``,
  rw[wellorder_def, iseg_def]
    >- (match_mp_tac wellfounded_subset >> qexists_tac `wellorder_REP w` >>
        rw[rrestrict_SUBSET] >>
        metis_tac [termP_term_REP, wellorder_def])
    >- (rw[rrestrict_def, domain_def, range_def] >>
        qabbrev_tac `WO = wellorder_REP w` >>
        rw[strict_linear_order_def] >| [
          rw[domain_def],
          rw[range_def],
          rw[transitive_def] >>
          `transitive WO`
             by metis_tac [wellorder_def, strict_linear_order_def,
                           termP_term_REP] >>
          fs [transitive_def] >> metis_tac [],
          metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def],
          simp[] >>
          metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def,
                     in_domain, in_range, IN_UNION],
          simp[] >>
          metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def,
                     in_domain, in_range, IN_UNION],
          simp[] >>
          metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def,
                     in_domain, in_range, IN_UNION],
          simp[] >>
          metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def,
                     in_domain, in_range, IN_UNION]
        ]))

val wobound_def = Define`
  wobound x w = wellorder_ABS (rrestrict (wellorder_REP w) (iseg w x))
`;

val _ = overload_on("WIN", ``λp w. p IN wellorder_REP w``)
val _ = set_fixity "WIN" (Infix(NONASSOC, 425))

val IN_wobound = store_thm(
  "IN_wobound",
  ``(x,y) WIN wobound z w <=> (x,z) WIN w /\ (y,z) WIN w /\ (x,y) WIN w``,
  rw[wobound_def, wellorder_rrestrict, #repabs_pseudo_id wellorder_results] >>
  rw[rrestrict_def, iseg_def] >> metis_tac []);

val _ = overload_on ("wrange", ``\w. range (wellorder_REP w)``)

val localDefine = with_flag (computeLib.auto_import_definitions, false) Define

val orderlt_def = localDefine`
  orderlt = {
    (w1,w2) | ?x. x IN range (wellorder_REP w2) /\ (w1 = wobound x w2)
  }
`

val orderle_def = localDefine`
  orderle = orderlt UNION {(x,x) | T}
`;

val orderle_REFL = store_thm(
  "orderle_REFL",
  ``reflexive orderle s``,
  rw[reflexive_def, orderle_def]);

val orderlt_SUBSET = store_thm(
  "orderlt_SUBSET",
  ``(w1,w2) IN orderlt ==> wellorder_REP w1 SUBSET wellorder_REP w2``,
  simp_tac (srw_ss() ++ DNF_ss)[orderlt_def, SUBSET_DEF, IN_wobound,
                                pairTheory.FORALL_PROD]);

val orderle_ANTISYM = store_thm(
  "orderle_ANTISYM",
  ``antisym orderle``,
  simp[antisym_def, orderle_def] >> map_every qx_gen_tac [`w1`, `w2`] >>
  strip_tac >> simp[] >>
  metis_tac [orderlt_SUBSET, SUBSET_ANTISYM, #absrep_id wellorder_results]);

val WIN_TRANS = store_thm(
  "WIN_TRANS",
  ``(x,y) WIN w /\ (y,z) WIN w ==> (x,z) WIN w``,
  `transitive (wellorder_REP w)`
     by metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def] >>
  metis_tac [transitive_def]);

val wrange_wobound = store_thm(
  "wrange_wobound",
  ``wrange (wobound x w) = iseg w x INTER wrange w``,
  rw[EXTENSION, range_def, iseg_def, IN_wobound, EQ_IMP_THM] >>
  metis_tac[WIN_TRANS]);

val wellorder_cases = store_thm(
  "wellorder_cases",
  ``!w. ?s. wellorder s /\ (w = wellorder_ABS s)``,
  rw[Once (#termP_exists wellorder_results)] >>
  simp_tac (srw_ss() ++ DNF_ss)[#absrep_id wellorder_results]);
val WEXTENSION = store_thm(
  "WEXTENSION",
  ``(w1 = w2) <=> !a b. (a,b) WIN w1 <=> (a,b) WIN w2``,
  qspec_then `w1` (Q.X_CHOOSE_THEN `s1` STRIP_ASSUME_TAC) wellorder_cases >>
  qspec_then `w2` (Q.X_CHOOSE_THEN `s2` STRIP_ASSUME_TAC) wellorder_cases >>
  simp[#repabs_pseudo_id wellorder_results,
       #term_ABS_pseudo11 wellorder_results,
       EXTENSION, pairTheory.FORALL_PROD]);

val wobound2 = store_thm(
  "wobound2",
  ``(a,b) WIN w ==> (wobound a (wobound b w) = wobound a w)``,
  rw[WEXTENSION, IN_wobound, EQ_IMP_THM] >> metis_tac [WIN_TRANS]);

val wellorder_fromNat = store_thm(
  "wellorder_fromNat",
  ``wellorder { (i,j) | i < j /\ j <= n }``,
  rw[wellorder_def, wellfounded_def, strict_linear_order_def] >| [
    qexists_tac `LEAST m. m IN s` >> numLib.LEAST_ELIM_TAC >> rw[] >>
    metis_tac [],
    srw_tac[ARITH_ss][transitive_def],
    full_simp_tac (srw_ss() ++ ARITH_ss) [domain_def, range_def],
    full_simp_tac (srw_ss() ++ ARITH_ss) [domain_def, range_def],
    full_simp_tac (srw_ss() ++ ARITH_ss) [domain_def, range_def],
    full_simp_tac (srw_ss() ++ ARITH_ss) [domain_def, range_def]
  ]);

val fromNat_def = Define`
  fromNat n = wellorder_ABS { (i,j) | i < j /\ j <= n }
`

val fromNat_11 = store_thm(
  "fromNat_11",
  ``(fromNat i = fromNat j) <=> (i = j)``,
  rw[fromNat_def, WEXTENSION, wellorder_fromNat,
     #repabs_pseudo_id wellorder_results] >>
  simp[EQ_IMP_THM] >> strip_tac >>
  spose_not_then assume_tac >>
  `i < j \/ j < i` by DECIDE_TAC >| [
     first_x_assum (qspecl_then [`i`, `j`] mp_tac),
     first_x_assum (qspecl_then [`j`, `i`] mp_tac)
  ] >> srw_tac[ARITH_ss][]);

val wellorder_REP_fromNat = store_thm(
  "wellorder_REP_fromNat",
  ``wellorder_REP (fromNat n) = { (i,j) | i < j /\ j <= n}``,
  rw[fromNat_def, wellorder_fromNat, #repabs_pseudo_id wellorder_results]);

val wrange_fromNat = store_thm(
  "wrange_fromNat",
  ``wrange (fromNat i) = { x | 1 <= x /\ x <= i }``,
  rw[EXTENSION, wellorder_REP_fromNat, range_def, EQ_IMP_THM] >>
  TRY DECIDE_TAC >> qexists_tac `x - 1` >> DECIDE_TAC);

val WIN_fromNat = store_thm(
  "WIN_fromNat",
  ``(i,j) WIN fromNat n <=> i < j /\ j <= n``,
  rw[wellorder_REP_fromNat]);

val wobound_fromNat = store_thm(
  "wobound_fromNat",
  ``i <= j ==> (wobound i (fromNat j) = fromNat (i - 1))``,
  rw[WEXTENSION, WIN_fromNat, IN_wobound] >> eq_tac >>
  srw_tac [ARITH_ss][]);

val fromNat_chain = store_thm(
  "fromNat_chain",
  ``chain { fromNat i | T } orderle``,
  rw[chain_def, orderle_def, orderlt_def] >>
  Cases_on `i = i'` >> rw[fromNat_11, wrange_fromNat] >> Cases_on `i < i'` >| [
    DISJ1_TAC >> qexists_tac `i + 1` >>
    srw_tac[ARITH_ss][wobound_fromNat],
    DISJ2_TAC >> qexists_tac `i' + 1` >>
    srw_tac[ARITH_ss][wobound_fromNat]
  ]);

(*
val fromNats_no_upperbound = store_thm(
  "fromNats_no_upperbound",
  ``upper_bounds { fromNat i | T } orderle = {}``,
  rw[EXTENSION, upper_bounds_def] >> srw_tac[DNF_ss][]
    obvious but tedious
*)

val elsOf_def = Define`
  elsOf w = domain (wellorder_REP w) UNION range (wellorder_REP w)
`;

val elsOf_wobound = store_thm(
  "elsOf_wobound",
  ``elsOf (wobound x w) =
      let s = { y | (y,x) WIN w }
      in
        if FINITE s /\ (CARD s = 1) then {}
        else s``,
  simp[wobound_def, EXTENSION] >> qx_gen_tac `a` >>
  simp[elsOf_def, wellorder_rrestrict, #repabs_pseudo_id wellorder_results] >>
  simp[rrestrict_def, iseg_def, domain_def, range_def] >> eq_tac >|[
    disch_then (DISJ_CASES_THEN (Q.X_CHOOSE_THEN `b` STRIP_ASSUME_TAC)) >>
    rw[] >>
    `a <> b` by (strip_tac >> fs[WIN_REFL]) >>
    `a IN { y | (y,x) WIN w} /\ b IN { y | (y,x) WIN w}` by rw[] >>
    `SING { y | (y,x) WIN w }` by metis_tac [SING_IFF_CARD1] >>
    `?z. { y | (y,x) WIN w } = {z}` by fs[SING_DEF] >>
    pop_assum SUBST_ALL_TAC >> fs[],

    rw [] >>
    qabbrev_tac `s = { y | (y,x) WIN w }` >> Cases_on `FINITE s` >> fs[] >| [
      `CARD s <> 0`
        by (strip_tac >> `s = {}` by metis_tac [CARD_EQ_0] >>
            `a IN s` by rw[Abbr`s`] >> rw[] >> fs[]) >>
      `?b. a <> b /\ (b,x) WIN w`
         by (SPOSE_NOT_THEN strip_assume_tac >>
             qsuff_tac `s = {a}` >- (strip_tac >> fs[]) >>
             rw[EXTENSION, Abbr`s`, EQ_IMP_THM] >> metis_tac []) >>
      metis_tac [WIN_trichotomy, WIN_elsOf],

      `?b. a <> b /\ b IN s`
         by (qspecl_then [`s`, `{a}`] MP_TAC IN_INFINITE_NOT_FINITE >>
             simp[] >> metis_tac []) >>
      fs[Abbr`s`] >> metis_tac [WIN_trichotomy, WIN_elsOf]
    ]
  ]);

val WIN_elsOf = store_thm(
  "WIN_elsOf",
  ``(x,y) WIN w ==> x IN elsOf w /\ y IN elsOf w``,
  rw[elsOf_def, range_def, domain_def] >> metis_tac[]);

val WIN_trichotomy = store_thm(
  "WIN_trichotomy",
  ``!x y. x IN elsOf w /\ y IN elsOf w ==>
          (x,y) WIN w \/ (x = y) \/ (y,x) WIN w``,
  rpt strip_tac >>
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[elsOf_def] >> metis_tac[]);

val WIN_REFL = store_thm(
  "WIN_REFL",
  ``(x,x) WIN w = F``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, strict_linear_order_def]);

val orderiso_def = Define`
  orderiso w1 w2 <=>
    ?f. (!x. x IN elsOf w1 ==> f x IN elsOf w2) /\
        (!x1 x2. x1 IN elsOf w1 /\ x2 IN elsOf w1 ==>
                 ((f x1 = f x2) = (x1 = x2))) /\
        (!y. y IN elsOf w2 ==> ?x. x IN elsOf w1 /\ (f x = y)) /\
        (!x y. (x,y) WIN w1 ==> (f x, f y) WIN w2)
`;

val orderiso_thm = store_thm(
  "orderiso_thm",
  ``orderiso w1 w2 <=>
     ?f. BIJ f (elsOf w1) (elsOf w2) /\
         !x y. (x,y) WIN w1 ==> (f x, f y) WIN w2``,
  rw[orderiso_def, BIJ_DEF, INJ_DEF, SURJ_DEF] >> eq_tac >> rpt strip_tac >>
  qexists_tac `f` >> metis_tac []);

val orderiso_REFL = store_thm(
  "orderiso_REFL",
  ``!w. orderiso w w``,
  rw[orderiso_def] >> qexists_tac `\x.x` >> rw[]);

val orderiso_SYM = store_thm(
  "orderiso_SYM",
  ``!w1 w2. orderiso w1 w2 ==> orderiso w2 w1``,
  rw[orderiso_thm] >>
  qabbrev_tac `g = LINV f (elsOf w1)` >>
  `BIJ g (elsOf w2) (elsOf w1)` by metis_tac [BIJ_LINV_BIJ] >>
  qexists_tac `g` >> simp[] >>
  rpt strip_tac >>
  `x IN elsOf w2 /\ y IN elsOf w2` by metis_tac [WIN_elsOf] >>
  `g x IN elsOf w1 /\ g y IN elsOf w1` by metis_tac [BIJ_DEF, INJ_DEF] >>
  `(g x, g y) WIN w1 \/ (g x = g y) \/ (g y, g x) WIN w1`
    by metis_tac [WIN_trichotomy]
    >- (`x = y` by metis_tac [BIJ_DEF, INJ_DEF] >> fs[WIN_REFL]) >>
  `(f (g y), f (g x)) WIN w2` by metis_tac [WIN_TRANS] >>
  `(y,x) WIN w2` by metis_tac [BIJ_LINV_INV] >>
  metis_tac [WIN_TRANS, WIN_REFL]);

val orderiso_TRANS = store_thm(
  "orderiso_TRANS",
  ``!w1 w2 w3. orderiso w1 w2 /\ orderiso w2 w3 ==> orderiso w1 w3``,
  rw[orderiso_def] >> qexists_tac `f' o f` >>
  rw[] >> metis_tac []);

val orderlt_def = Define`
  orderlt w1 w2 = ?x. x IN elsOf w2 /\ orderiso w1 (wobound x w2)
`;


val orderlt_orderiso = store_thm(
  "orderlt_orderiso",
  ``orderiso x0 y0 /\ orderiso a0 b0 ==> (orderlt x0 a0 <=> orderlt y0 b0)``,
  rw[orderlt_def, EQ_IMP_THM] >| [
    `orderiso y0 (wobound x a0)` by metis_tac [orderiso_SYM, orderiso_TRANS] >>
    `?f. BIJ f (elsOf a0) (elsOf b0) /\
         (!x y. (x,y) WIN a0 ==> (f x, f y) WIN b0)`
       by metis_tac [orderiso_thm] >>
    qexists_tac `f x` >> conj_tac
      >- metis_tac [BIJ_DEF, INJ_DEF] >>
    qsuff_tac `orderiso (wobound x a0) (wobound (f x) b0)`
      >- metis_tac [orderiso_TRANS] >>
    rw[orderiso_thm] >> qexists_tac `f` >> rw[IN_wobound] >>
    ntac 2 (pop_assum mp_tac) >> rpt (pop_assum (K ALL_TAC)) >>
    rw[elsOf_wobound]
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF]
    match_mp_tac orderiso_TRANS >> qexists_tac `wobound x a0`





val ordle_partial_UNIV = store_thm(
  "ordle_partial_UNIV",
  ``partial_order orderle UNIV``,
  rw[partial_order_def, orderle_TRANS, orderle_ANTISYM, orderle_REFL]);

zorns_lemma
val preord = new_type_definition

val iso_REFL = store_thm(
  "iso_REFL",
  ``isomorphic R R``,
  rw[isomorphic_def] >> qexists_tac `\x.x` >> rw[]);

val iso_SYM = store_thm(
  "iso_SYM",
  ``isomorphic R1 R2 ==> isomorphic R2 R1``,
  rw[isomorphic_def] >>
  pop_assum (Q.X_CHOOSE_THEN `g` ASSUME_TAC o CONV_RULE SKOLEM_CONV) >>
  metis_tac []);

val iso_TRANS = store_thm(
  "iso_TRANS",
  ``isomorphic R1 R2 /\ isomorphic R2 R3 ==> isomorphic R1 R3``,
  rw[isomorphic_def] >> qexists_tac `f' o f` >> rw[] >> metis_tac []);




