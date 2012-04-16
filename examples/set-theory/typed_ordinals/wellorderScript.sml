open HolKernel Parse boolLib bossLib
open lcsymtacs
open boolSimps

open set_relationTheory pred_setTheory

val _ = new_theory "wellorder"

val wellfounded_def = Define`
  wellfounded R <=>
   !s. (?w. w IN s) ==> ?min. min IN s /\ !w. (w,min) IN R ==> w NOTIN s
`;

val wellfounded_WF = store_thm(
  "wellfounded_WF",
  ``wellfounded R <=> WF (CURRY R)``,
  rw[wellfounded_def, relationTheory.WF_DEF, SPECIFICATION]);

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

val wellorder_results = newtypeTools.rich_new_type(
  "wellorder",
  prove(``?x. wellorder x``, qexists_tac `{}` >> simp[wellorder_EMPTY]))

val termP_term_REP = #termP_term_REP wellorder_results

val elsOf_def = Define`
  elsOf w = domain (wellorder_REP w) UNION range (wellorder_REP w)
`;

val _ = overload_on("WIN", ``λp w. p IN wellorder_REP w``)
val _ = set_fixity "WIN" (Infix(NONASSOC, 425))
val _ = overload_on ("wrange", ``\w. range (wellorder_REP w)``)


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
  fs[elsOf_def, wellorder_def, strict_linear_order_def] >> metis_tac[]);

val WIN_REFL = store_thm(
  "WIN_REFL",
  ``(x,x) WIN w = F``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, strict_linear_order_def]);
val _ = export_rewrites ["WIN_REFL"]

val WIN_TRANS = store_thm(
  "WIN_TRANS",
  ``(x,y) WIN w /\ (y,z) WIN w ==> (x,z) WIN w``,
  `transitive (wellorder_REP w)`
     by metis_tac [termP_term_REP, wellorder_def, strict_linear_order_def] >>
  metis_tac [transitive_def]);

val WIN_WF = store_thm(
  "WIN_WF",
  ``wellfounded (\p. p WIN w)``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def] >>
  qsuff_tac `(\p. p WIN w) = wellorder_REP w` >- simp[] >>
  simp[FUN_EQ_THM, SPECIFICATION]);

val CURRY_def = pairTheory.CURRY_DEF |> SPEC_ALL |> ABS ``y:'b``
                                     |> ABS ``x:'a``
                                     |> SIMP_RULE (bool_ss ++ ETA_ss) []

val WIN_WF2 = save_thm(
  "WIN_WF2",
  WIN_WF |> SIMP_RULE (srw_ss()) [wellfounded_WF, CURRY_def])

val iseg_def = Define`iseg w x = { y | (y,x) WIN w }`

val wellorder_rrestrict = store_thm(
  "wellorder_rrestrict",
  ``wellorder (rrestrict (wellorder_REP w) (iseg w x))``,
  rw[wellorder_def, iseg_def]
    >- (match_mp_tac wellfounded_subset >> qexists_tac `wellorder_REP w` >>
        rw[rrestrict_SUBSET] >>
        metis_tac [termP_term_REP, wellorder_def])
    >- (qabbrev_tac `WO = wellorder_REP w` >>
        qabbrev_tac `els = {y | (y,x) IN WO}` >>
        simp[strict_linear_order_def] >> rpt conj_tac >| [
          simp[transitive_def, rrestrict_def] >> metis_tac [WIN_TRANS],
          simp[rrestrict_def, Abbr`WO`],
          map_every qx_gen_tac [`a`, `b`] >>
          simp[rrestrict_def, in_domain, in_range] >>
          `!e. e IN els ==> e IN elsOf w`
             by (rw[elsOf_def, Abbr`els`, domain_def, range_def] >>
                 metis_tac[]) >>
          metis_tac [WIN_trichotomy]
        ]))

val wobound_def = Define`
  wobound x w = wellorder_ABS (rrestrict (wellorder_REP w) (iseg w x))
`;

val IN_wobound = store_thm(
  "IN_wobound",
  ``(x,y) WIN wobound z w <=> (x,z) WIN w /\ (y,z) WIN w /\ (x,y) WIN w``,
  rw[wobound_def, wellorder_rrestrict, #repabs_pseudo_id wellorder_results] >>
  rw[rrestrict_def, iseg_def] >> metis_tac []);

val localDefine = with_flag (computeLib.auto_import_definitions, false) Define

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

val elsOf_NEVER_SING = store_thm(
  "elsOf_NEVER_SING",
  ``!e. elsOf w <> {e}``,
  rw[elsOf_def] >> disch_then (assume_tac o SIMP_RULE (srw_ss()) [EXTENSION]) >>
  `e IN domain (wellorder_REP w) \/ e IN wrange w` by metis_tac[] >>
   fs[in_domain, in_range] >> metis_tac [WIN_REFL]);

val orderlt_REFL = store_thm(
  "orderlt_REFL",
  ``orderlt w w = F``,
  simp[orderlt_def] >> qx_gen_tac `x` >> Cases_on `x IN elsOf w` >> simp[] >>
  simp[orderiso_thm] >> qx_gen_tac `f` >>
  Cases_on `BIJ f (elsOf w) (elsOf (wobound x w))` >> simp[] >>
  spose_not_then strip_assume_tac >>
  `f x IN elsOf (wobound x w)` by metis_tac [BIJ_IFF_INV] >>
  `elsOf (wobound x w) = {y | (y,x) WIN w}`
       by (full_simp_tac (srw_ss() ++ COND_elim_ss)
                                 [elsOf_wobound, LET_THM] >>
                   fs[]) >>
  `!n. (FUNPOW f (SUC n) x, FUNPOW f n x) WIN w`
     by (Induct >> simp[] >- fs[] >>
         `(FUNPOW f (SUC (SUC n)) x, FUNPOW f (SUC n) x) WIN wobound x w`
            by metis_tac [arithmeticTheory.FUNPOW_SUC] >>
         fs [IN_wobound]) >>
  mp_tac WIN_WF >> simp[wellfounded_def] >>
  qexists_tac `{ FUNPOW f n x | n | T }` >> simp[] >>
  simp_tac (srw_ss() ++ DNF_ss)[] >> qx_gen_tac `min` >>
  Cases_on `!n. min <> FUNPOW f n x` >- simp[] >>
  fs[] >> DISJ2_TAC >> rw[] >> qexists_tac `SUC n` >>
  rw[Once SPECIFICATION]);

val FINITE_IMAGE_INJfn = prove(
  ``!s. (!x y. x IN s /\ y IN s ==> ((f x = f y) = (x = y))) ==>
        (FINITE (IMAGE f s) = FINITE s)``,
  rpt strip_tac >> simp[EQ_IMP_THM, IMAGE_FINITE] >>
  qsuff_tac `!t. FINITE t ==>
                 !s'. s' SUBSET s /\ (t = IMAGE f s') ==> FINITE s'`
    >- metis_tac[SUBSET_REFL] >>
  Induct_on `FINITE t` >> conj_tac >- metis_tac[IMAGE_EQ_EMPTY, FINITE_EMPTY] >>
  qx_gen_tac `t` >> strip_tac >> qx_gen_tac `e` >> strip_tac >>
  qx_gen_tac `s'` >> strip_tac >>
  `?d. (e = f d) /\ d IN s'`
     by (pop_assum mp_tac >> simp[EXTENSION] >> metis_tac[]) >>
  qsuff_tac `t = IMAGE f (s' DELETE d)`
    >- metis_tac [FINITE_DELETE, DELETE_SUBSET, SUBSET_TRANS] >>
  Q.UNDISCH_THEN `e INSERT t = IMAGE f s'` mp_tac >> simp[EXTENSION] >>
  strip_tac >> qx_gen_tac `x` >>
  `!x. x IN s' ==> x IN s` by fs[SUBSET_DEF] >>
  Cases_on `x = f d` >> asm_simp_tac(srw_ss() ++ CONJ_ss)[] >- rw[] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >> metis_tac []);

val IMAGE_CARD_INJfn = prove(
  ``!s. FINITE s /\ (!x y. x IN s /\ y IN s ==> ((f x = f y) = (x = y))) ==>
        (CARD (IMAGE f s) = CARD s)``,
  rpt strip_tac >>
  qsuff_tac `!t. FINITE t ==> t SUBSET s ==> (CARD (IMAGE f t) = CARD t)`
    >- metis_tac [SUBSET_REFL] >>
  Induct_on `FINITE t` >> simp[] >> rpt strip_tac >>
  `!x. x IN t ==> x IN s` by fs[SUBSET_DEF] >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) []);

val wobounds_preserve_bijections = store_thm(
  "wobounds_preserve_bijections",
  ``BIJ f (elsOf w1) (elsOf w2) /\ x IN elsOf w1 /\
    (!x y. (x,y) WIN w1 ==> (f x, f y) WIN w2) ==>
    BIJ f (elsOf (wobound x w1)) (elsOf (wobound (f x) w2))``,
  simp[BIJ_IFF_INV,elsOf_wobound] >> strip_tac >>
  `{ y | (y, f x) WIN w2 } = IMAGE f {y | (y,x) WIN w1 }`
     by (simp[EXTENSION] >> qx_gen_tac `e` >> eq_tac >| [
           strip_tac >>
           `e IN elsOf w2 /\ f x IN elsOf w2`
              by (rw[elsOf_def, in_domain, in_range] >> metis_tac[]) >>
            `?d. d IN elsOf w1 /\ (e = f d)` by metis_tac[] >>
            rw[] >>
            `d <> x` by metis_tac [WIN_REFL] >>
            `~((x,d) WIN w1)` by metis_tac [WIN_TRANS, WIN_REFL] >>
            metis_tac [WIN_trichotomy],
            disch_then (Q.X_CHOOSE_THEN `d` STRIP_ASSUME_TAC) >> rw[]
         ]) >>
  qabbrev_tac `ltx = {y | (y,x) WIN w1}` >> simp[] >>
  `!x y. x IN ltx /\ y IN ltx ==> ((f x = f y) <=> (x = y))`
     by (simp[Abbr`ltx`] >> metis_tac [IN_UNION, in_domain, elsOf_def]) >>
  asm_simp_tac (srw_ss() ++ CONJ_ss) [FINITE_IMAGE_INJfn, IMAGE_CARD_INJfn] >>
  Cases_on `FINITE ltx /\ (CARD ltx = 1)` >> simp[] >| [
    `!x. x IN ltx ==> x IN elsOf w1`
       by (rw[Abbr`ltx`, elsOf_def, in_domain] >> metis_tac []) >>
    asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
    `!x y. x IN elsOf w1 /\ y IN elsOf w1 ==> ((f x = f y) = (x = y))`
       by metis_tac [] >>
    asm_simp_tac (srw_ss() ++ CONJ_ss)[] >> metis_tac []
  ]);

val orderlt_TRANS = store_thm(
  "orderlt_TRANS",
  ``!w1 w2 w3. orderlt w1 w2 /\ orderlt w2 w3 ==> orderlt w1 w3``,
  simp[orderlt_def] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2
                  (Q.X_CHOOSE_THEN `a` strip_assume_tac)
                  (Q.X_CHOOSE_THEN `b` strip_assume_tac)) >>
  `(?f. BIJ f (elsOf w1) (elsOf (wobound a w2)) /\
        !x y. (x,y) WIN w1 ==> (f x, f y) WIN wobound a w2) /\
   (?g. BIJ g (elsOf w2) (elsOf (wobound b w3)) /\
        !x y. (x,y) WIN w2 ==> (g x, g y) WIN wobound b w3)`
     by metis_tac[orderiso_thm] >>
  `g a IN elsOf (wobound b w3)` by metis_tac [BIJ_IFF_INV] >>
  `(g a, b) WIN w3`
    by (pop_assum mp_tac >> simp[elsOf_wobound, in_domain, in_range] >>
        asm_simp_tac (srw_ss() ++ COND_elim_ss) [LET_THM] >>
        metis_tac[]) >>
  qexists_tac `g a` >> conj_tac >- metis_tac[IN_UNION, elsOf_def, in_domain] >>
  match_mp_tac orderiso_TRANS >> qexists_tac `wobound a w2` >>
  rw[] >> rw[orderiso_thm] >> qexists_tac `g` >> conj_tac >| [
    `wobound (g a) w3 = wobound (g a) (wobound b w3)`
      by rw[wobound2] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac wobounds_preserve_bijections >> rw[],
    fs[IN_wobound]
  ]);

val wleast_def = Define`
  wleast w s =
    some x. x IN elsOf w /\ x NOTIN s /\
            !y. y IN elsOf w /\ y NOTIN s /\ x <> y ==> (x,y) WIN w
`;

val wo2wo_def = Define`
  wo2wo w1 w2 =
    WFREC (\x y. (x,y) WIN w1)
          (\f x. let s0 = IMAGE f (iseg w1 x) in
                 let s1 = IMAGE THE (s0 DELETE NONE)
                 in
                   if s1 = elsOf w2 then NONE
                   else wleast w2 s1)
`;

val restrict_away = prove(
  ``IMAGE (RESTRICT f (\x y. (x,y) WIN w) x) (iseg w x) = IMAGE f (iseg w x)``,
  rw[EXTENSION, relationTheory.RESTRICT_DEF, iseg_def] >> srw_tac[CONJ_ss][]);

val wo2wo_thm = save_thm(
  "wo2wo_thm",
  wo2wo_def |> concl |> strip_forall |> #2 |> rhs |> strip_comb |> #2
            |> C ISPECL relationTheory.WFREC_THM
            |> C MATCH_MP WIN_WF2
            |> SIMP_RULE (srw_ss()) []
            |> REWRITE_RULE [GSYM wo2wo_def, restrict_away])


val WO_INDUCTION =
    relationTheory.WF_INDUCTION_THM |> C MATCH_MP WIN_WF2 |> Q.GEN `w`
                                    |> BETA_RULE

val wleast_IN_wo = store_thm(
  "wleast_IN_wo",
  ``(wleast w s = SOME x) ==>
       x IN elsOf w /\ x NOTIN s /\
       !y. y IN elsOf w /\ y NOTIN s /\ x <> y ==> (x,y) WIN w``,
  simp[wleast_def] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  simp[]);

val wleast_EQ_NONE = store_thm(
  "wleast_EQ_NONE",
  ``(wleast w s = NONE) ==> elsOf w SUBSET s``,
  simp[wleast_def] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[] >>
  simp[SUBSET_DEF] >>
  qspec_then `w` ho_match_mp_tac WO_INDUCTION >>
  qx_gen_tac `x` >> rpt strip_tac >>
  first_x_assum (fn th => qspec_then `x` mp_tac th >> simp[] >>
                          disch_then strip_assume_tac) >>
  `(y,x) WIN w` by metis_tac [WIN_trichotomy] >> metis_tac[]);

val wo2wo_IN_w2 = store_thm(
  "wo2wo_IN_w2",
  ``!x y. (wo2wo w1 w2 x = SOME y) ==> y IN elsOf w2``,
  rw[Once wo2wo_thm, LET_THM] >> metis_tac [wleast_IN_wo]);

val IMAGE_wo2wo_SUBSET = store_thm(
  "IMAGE_wo2wo_SUBSET",
  ``IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 x) DELETE NONE) SUBSET elsOf w2``,
  simp_tac (srw_ss() ++ DNF_ss) [SUBSET_DEF] >> qx_gen_tac `a` >>
  Cases_on `wo2wo w1 w2 a` >> rw[] >> metis_tac [wo2wo_IN_w2]);

val wo2wo_EQ_NONE = store_thm(
  "wo2wo_EQ_NONE",
  ``!x. (wo2wo w1 w2 x = NONE) ==>
        !y. (x,y) WIN w1 ==> (wo2wo w1 w2 y = NONE)``,
  ONCE_REWRITE_TAC [wo2wo_thm] >> rw[LET_THM] >| [
    qsuff_tac
        `IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 y) DELETE NONE) = elsOf w2` >-
        rw[] >>
    match_mp_tac SUBSET_ANTISYM >> rw[IMAGE_wo2wo_SUBSET] >>
    match_mp_tac SUBSET_TRANS >>
    qexists_tac `IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 x) DELETE NONE)` >>
    conj_tac >- rw[] >>
    simp_tac (srw_ss() ++ DNF_ss) [SUBSET_DEF] >>
    qsuff_tac `!a. a IN iseg w1 x ==> a IN iseg w1 y` >- metis_tac[] >>
    rw[iseg_def] >> metis_tac [WIN_TRANS],
    imp_res_tac wleast_EQ_NONE >>
    qsuff_tac `IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 x) DELETE NONE) SUBSET
               elsOf w2` >- metis_tac [SUBSET_ANTISYM] >>
    rw[IMAGE_wo2wo_SUBSET]
  ]);

val wo2wo_EQ_SOME_downwards = store_thm(
  "wo2wo_EQ_SOME_downwards",
  ``!x y. (wo2wo w1 w2 x = SOME y) ==>
          !x0. (x0,x) WIN w1 ==> ?y0. wo2wo w1 w2 x0 = SOME y0``,
  metis_tac [wo2wo_EQ_NONE, optionTheory.option_CASES]);

val _ = overload_on (
  "woseg",
  ``\w1 w2 x. IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 x) DELETE NONE)``)

val mono_woseg = store_thm(
  "mono_woseg",
  ``(x1,x2) WIN w1 ==> woseg w1 w2 x1 SUBSET woseg w1 w2 x2``,
  simp_tac(srw_ss() ++ DNF_ss) [SUBSET_DEF, iseg_def]>> metis_tac [WIN_TRANS]);

val wo2wo_injlemma = prove(
  ``(x,y) WIN w1 /\ (wo2wo w1 w2 y = SOME z) ==> (wo2wo w1 w2 x <> SOME z)``,
  rw[Once wo2wo_thm, LET_THM, SimpL ``$==>``] >> strip_tac >>
  `z IN woseg w1 w2 y`
     by (asm_simp_tac (srw_ss() ++ DNF_ss) [] >> qexists_tac `x` >>
         simp[iseg_def]) >>
  metis_tac [wleast_IN_wo]);

val wo2wo_11 = store_thm(
  "wo2wo_11",
  ``x1 IN elsOf w1 /\ x2 IN elsOf w1 /\ (wo2wo w1 w2 x1 = SOME y) /\
    (wo2wo w1 w2 x2 = SOME y) ==> (x1 = x2)``,
  rpt strip_tac >>
  `(x1 = x2) \/ (x1,x2) WIN w1 \/ (x2,x1) WIN w1`
     by metis_tac [WIN_trichotomy] >>
  metis_tac [wo2wo_injlemma]);

val wleast_SUBSET = store_thm(
  "wleast_SUBSET",
  ``(wleast w s1 = SOME x) /\ (wleast w s2 = SOME y) /\ s1 SUBSET s2 ==>
    (x = y) \/ (x,y) WIN w``,
  simp[wleast_def] >> DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >> metis_tac[SUBSET_DEF]);

val wo2wo_mono = store_thm(
  "wo2wo_mono",
  ``(wo2wo w1 w2 x0 = SOME y0) /\ (wo2wo w1 w2 x = SOME y) /\ (x0,x) WIN w1 ==>
    (y0,y) WIN w2``,
  rpt strip_tac >>
  `x0 IN elsOf w1 /\ x IN elsOf w1`
      by metis_tac [elsOf_def, in_domain, in_range, IN_UNION] >>
  `y0 <> y` by metis_tac [WIN_REFL, wo2wo_11] >>
  rpt (qpat_assum `wo2wo X Y Z = WW` mp_tac) >>
  ONCE_REWRITE_TAC [wo2wo_thm] >> rw[LET_THM] >>
  metis_tac [mono_woseg, wleast_SUBSET]);

val wo2wo_ONTO = store_thm(
  "wo2wo_ONTO",
  ``(wo2wo w1 w2 x = SOME y) /\ (y0,y) WIN w2 ==>
    ?x0. wo2wo w1 w2 x0 = SOME y0``,
  simp[SimpL ``$==>``, Once wo2wo_thm] >> rw[] >>
  spose_not_then strip_assume_tac >>
  `y0 NOTIN woseg w1 w2 x`
     by (asm_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `a` >>
         `(wo2wo w1 w2 a = NONE) \/ ?y'. wo2wo w1 w2 a = SOME y'`
            by metis_tac [optionTheory.option_CASES] >> simp[] >>
         metis_tac[]) >>
  `y0 <> y` by metis_tac [WIN_REFL] >>
  `y0 IN elsOf w2 /\ y IN elsOf w2` by metis_tac [WIN_elsOf] >>
  metis_tac [WIN_TRANS, WIN_REFL, wleast_IN_wo]);

(*val orderlt_WF = store_thm(
  "orderlt_WF",
  ``WF orderlt``,
  rw[prim_recTheory.WF_IFF_WELLFOUNDED, prim_recTheory.wellfounded_def] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `w0 = f 0` >>
  qsuff_tac `?g. !n. (g (SUC n), g n) WIN w0`
    >-


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





*)

val _ = export_theory()
