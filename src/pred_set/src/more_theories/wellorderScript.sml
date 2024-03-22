open HolKernel Parse boolLib bossLib
open boolSimps mesonLib numLib InductiveDefinition tautLib

open relationTheory set_relationTheory pred_setTheory pairTheory
     arithmeticTheory optionTheory;

val _ = new_theory "wellorder"

val _ = temp_delsimps ["NORMEQ_CONV"]

fun K_TAC _ = ALL_TAC;
fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN
    SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF,
      IN_INSERT, IN_DELETE, IN_REST, IN_BIGINTER, IN_BIGUNION, IN_IMAGE,
      GSPECIFICATION, IN_DEF, EXISTS_PROD] THEN METIS_TAC [];

val FORALL_PROD = pairTheory.FORALL_PROD
val EXISTS_PROD = pairTheory.EXISTS_PROD
val EXISTS_SUM = sumTheory.EXISTS_SUM
val FORALL_SUM = sumTheory.FORALL_SUM

(* there's another ``wellfounded`` in prim_recTheory with different type *)
val _ = hide "wellfounded";

val wellfounded_def = Define`
  wellfounded R <=>
   !s. (?w. w IN s) ==> ?min. min IN s /\ !w. (w,min) IN R ==> w NOTIN s
`;
val _ = overload_on ("Wellfounded", ``wellfounded``);

val wellfounded_WF = store_thm(
  "wellfounded_WF",
  ``!R. wellfounded R <=> WF (CURRY R)``,
  rw[wellfounded_def, WF_DEF, SPECIFICATION]);

val wellorder_def = Define`
  wellorder R <=>
    wellfounded (strict R) /\ linear_order R (domain R UNION range R) /\
    reflexive R (domain R UNION range R)
`;

(* well order examples *)
val wellorder_EMPTY = store_thm(
  "wellorder_EMPTY",
  ``wellorder {}``,
  rw[wellorder_def, wellfounded_def, linear_order_def, transitive_def,
     antisym_def, domain_def, range_def, reflexive_def, strict_def]);

val wellorder_SING = store_thm(
  "wellorder_SING",
  ``!x y. wellorder {(x,y)} <=> (x = y)``,
  rw[wellorder_def, wellfounded_def, strict_def, reflexive_def,
     domain_def, range_def] >>
  eq_tac >| [
    metis_tac[],
    simp[linear_order_def, transitive_def, domain_def, range_def, antisym_def]
  ]);

val rrestrict_SUBSET = store_thm(
  "rrestrict_SUBSET",
  ``!r s. rrestrict r s SUBSET r``,
  rw[SUBSET_DEF,rrestrict_def] >> rw[]);

val wellfounded_subset = store_thm(
  "wellfounded_subset",
  ``!r0 r. wellfounded r /\ r0 SUBSET r ==> wellfounded r0``,
  rw[wellfounded_def] >>
  `?min. min IN s /\ !w. (w,min) IN r ==> w NOTIN s` by metis_tac [] >>
  metis_tac [SUBSET_DEF])

val wellorder_results = newtypeTools.rich_new_type
   {tyname = "wellorder",
    exthm  = prove(``?x. wellorder x``, qexists_tac `{}` >> simp[wellorder_EMPTY]),
    ABS    = "mkWO",
    REP    = "destWO"};

Theorem mkWO_destWO[simp] = #absrep_id wellorder_results
Theorem destWO_mkWO = #repabs_pseudo_id wellorder_results

val termP_term_REP = #termP_term_REP wellorder_results

val elsOf_def = Define`
  elsOf w = domain (destWO w) UNION range (destWO w)
`;

val _ = overload_on("WIN", ``\p w. p IN strict (destWO w)``)
val _ = set_fixity "WIN" (Infix(NONASSOC, 425))
val _ = overload_on("WLE", ``\p w. p IN destWO w``)
val _ = set_fixity "WLE" (Infix(NONASSOC, 425))
val _ = overload_on ("wrange", ``\w. range (destWO w)``)

val WIN_elsOf = store_thm(
  "WIN_elsOf",
  ``(x,y) WIN w ==> x IN elsOf w /\ y IN elsOf w``,
  rw[elsOf_def, range_def, domain_def, strict_def] >> metis_tac[]);

val WLE_elsOf = store_thm(
  "WLE_elsOf",
  ``(x,y) WLE w ==> x IN elsOf w /\ y IN elsOf w``,
  rw[elsOf_def, range_def, domain_def] >> metis_tac[]);

val WIN_trichotomy = store_thm(
  "WIN_trichotomy",
  ``!x y. x IN elsOf w /\ y IN elsOf w ==>
          (x,y) WIN w \/ (x = y) \/ (y,x) WIN w``,
  rpt strip_tac >>
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[elsOf_def, wellorder_def, strict_def, linear_order_def] >> metis_tac[]);

val WIN_REFL = store_thm(
  "WIN_REFL",
  ``(x,x) WIN w <=> F``,
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, strict_def]);
val _ = export_rewrites ["WIN_REFL"]

val WLE_TRANS = store_thm(
  "WLE_TRANS",
  ``(x,y) WLE w /\ (y,z) WLE w ==> (x,z) WLE w``,
  strip_tac >>
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, linear_order_def, transitive_def] >> metis_tac[]);

val WLE_ANTISYM = store_thm(
  "WLE_ANTISYM",
  ``(x,y) WLE w /\ (y,x) WLE w ==> (x = y)``,
  strip_tac >>
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, linear_order_def, antisym_def]);

val WIN_WLE = store_thm(
  "WIN_WLE",
  ``(x,y) WIN w ==> (x,y) WLE w``,
  rw[strict_def]);

val elsOf_WLE = store_thm(
  "elsOf_WLE",
  ``x IN elsOf w <=> (x,x) WLE w``,
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, elsOf_def, reflexive_def, in_domain, in_range] >>
  metis_tac[]);

val transitive_strict = store_thm(
  "transitive_strict",
  ``transitive r /\ antisym r ==> transitive (strict r)``,
  simp[transitive_def, strict_def, antisym_def] >> metis_tac[]);

val WIN_TRANS = store_thm(
  "WIN_TRANS",
  ``(x,y) WIN w /\ (y,z) WIN w ==> (x,z) WIN w``,
  `transitive (destWO w) /\ antisym (destWO w)`
     by metis_tac [termP_term_REP, wellorder_def, linear_order_def] >>
  metis_tac [transitive_def, transitive_strict]);

val WIN_WF = store_thm(
  "WIN_WF",
  ``wellfounded (\p. p WIN w)``,
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def] >>
  qsuff_tac `(\p. p WIN w) = strict (destWO w)` >- simp[] >>
  simp[FUN_EQ_THM, SPECIFICATION]);

val CURRY_def = pairTheory.CURRY_DEF |> SPEC_ALL |> ABS ``y:'b``
                                     |> ABS ``x:'a``
                                     |> SIMP_RULE (bool_ss ++ ETA_ss) []

val WIN_WF2 = save_thm(
  "WIN_WF2",
  WIN_WF |> SIMP_RULE (srw_ss()) [wellfounded_WF, CURRY_def])

val iseg_def = Define`iseg w x = { y | (y,x) WIN w }`

val strict_subset = store_thm(
  "strict_subset",
  ``r1 SUBSET r2 ==> strict r1 SUBSET strict r2``,
  simp[strict_def, SUBSET_DEF, FORALL_PROD]);

val transitive_rrestrict = store_thm(
  "transitive_rrestrict",
  ``transitive r ==> transitive (rrestrict r s)``,
  rw[transitive_def, rrestrict_def] >> metis_tac[]);

val antisym_rrestrict = store_thm(
  "antisym_rrestrict",
  ``antisym r ==> antisym (rrestrict r s)``,
  rw[antisym_def, rrestrict_def] >> metis_tac[]);

val linear_order_rrestrict = store_thm(
  "linear_order_rrestrict",
  ``linear_order r (domain r UNION range r) ==>
    linear_order (rrestrict r s)
                 (domain (rrestrict r s) UNION range (rrestrict r s))``,
  rw[linear_order_def, in_domain, in_range, antisym_rrestrict,
     transitive_rrestrict] >>
  fs[rrestrict_def] >> metis_tac[]);

val reflexive_rrestrict = store_thm(
  "reflexive_rrestrict",
  ``reflexive r (domain r UNION range r) ==>
    reflexive (rrestrict r s)
              (domain (rrestrict r s) UNION range (rrestrict r s))``,
  rw[reflexive_def, rrestrict_def, in_domain, in_range] >> metis_tac[]);

val wellorder_rrestrict = store_thm(
  "wellorder_rrestrict",
  ``wellorder (rrestrict (destWO w) s)``,
  `wellorder (destWO w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def] >>
  rw[linear_order_rrestrict, reflexive_rrestrict] >>
  match_mp_tac wellfounded_subset >>
  qexists_tac `strict(destWO w)` >>
  rw[rrestrict_SUBSET, strict_subset]);

val wobound_def = Define`
  wobound x w = mkWO (rrestrict (destWO w) (iseg w x))
`;

val WIN_wobound = store_thm(
  "WIN_wobound",
  ``(x,y) WIN wobound z w <=> (x,z) WIN w /\ (y,z) WIN w /\ (x,y) WIN w``,
  rw[wobound_def, wellorder_rrestrict, destWO_mkWO,
     strict_def] >>
  rw[rrestrict_def, iseg_def, strict_def] >> metis_tac []);

val WLE_wobound = store_thm(
  "WLE_wobound",
  ``(x,y) WLE wobound z w <=> (x,z) WIN w /\ (y,z) WIN w /\ (x,y) WLE w``,
  rw[wobound_def, wellorder_rrestrict, destWO_mkWO] >>
  rw[rrestrict_def, iseg_def] >> metis_tac[]);

val localDefine = with_flag (computeLib.auto_import_definitions, false) Define

val wellorder_cases = store_thm(
  "wellorder_cases",
  ``!w. ?s. wellorder s /\ (w = mkWO s)``,
  rw[Once (#termP_exists wellorder_results)] >>
  simp_tac (srw_ss() ++ DNF_ss)[#absrep_id wellorder_results]);

val WEXTENSION = store_thm(
  "WEXTENSION",
  ``(w1 = w2) <=> !a b. (a,b) WLE w1 <=> (a,b) WLE w2``,
  qspec_then `w1` strip_assume_tac wellorder_cases >>
  qspec_then `w2` strip_assume_tac wellorder_cases >>
  simp[#term_ABS_pseudo11 wellorder_results, EXTENSION, FORALL_PROD,
       destWO_mkWO]);

val wobound2 = store_thm(
  "wobound2",
  ``(a,b) WIN w ==> (wobound a (wobound b w) = wobound a w)``,
  simp[WEXTENSION, WLE_wobound, WIN_wobound] >> metis_tac [WIN_TRANS]);

val wellorder_fromNat = store_thm(
  "wellorder_fromNat",
  ``wellorder { (i,j) | i <= j /\ j < n }``,
  rw[wellorder_def, wellfounded_def, linear_order_def, in_range, in_domain,
     reflexive_def,transitive_def,antisym_def] >>
  qexists_tac `LEAST m. m IN s` >> numLib.LEAST_ELIM_TAC >> rw[strict_def] >>
  metis_tac []);

val INJ_preserves_transitive = store_thm(
  "INJ_preserves_transitive",
  ``transitive r /\ INJ f (domain r UNION range r) t ==>
    transitive (IMAGE (f ## f) r)``,
  simp[transitive_def, EXISTS_PROD] >> strip_tac >>
  map_every qx_gen_tac [`x`, `y`, `z`] >>
  simp[GSYM AND_IMP_INTRO] >>
  disch_then (Q.X_CHOOSE_THEN `a` (Q.X_CHOOSE_THEN `b` strip_assume_tac)) >>
  disch_then (Q.X_CHOOSE_THEN `b'` (Q.X_CHOOSE_THEN `c` strip_assume_tac)) >>
  rw[] >> qabbrev_tac `DR = domain r UNION range r` >>
  `b IN DR /\ b' IN DR` by (rw[Abbr`DR`, in_domain, in_range] >> metis_tac[]) >>
  `b' = b` by metis_tac [INJ_DEF] >> rw[] >> metis_tac[]);

val INJ_preserves_antisym = store_thm(
  "INJ_preserves_antisym",
  ``antisym r /\ INJ f (domain r UNION range r) t ==> antisym (IMAGE (f ## f) r)``,
  simp[antisym_def, EXISTS_PROD] >> strip_tac >>
  map_every qx_gen_tac [`x`, `y`] >> simp[GSYM AND_IMP_INTRO] >>
  disch_then (Q.X_CHOOSE_THEN `a` (Q.X_CHOOSE_THEN `b` strip_assume_tac)) >>
  disch_then (Q.X_CHOOSE_THEN `a'` (Q.X_CHOOSE_THEN `b'` strip_assume_tac)) >>
  rw[] >> qabbrev_tac `DR = domain r UNION range r` >>
  metis_tac [INJ_DEF, IN_UNION, in_domain, in_range]);


val INJ_preserves_linear_order = store_thm(
  "INJ_preserves_linear_order",
  ``linear_order r (domain r UNION range r) /\ INJ f (domain r UNION range r) t ==>
    linear_order (IMAGE (f ## f) r) (IMAGE f (domain r UNION range r))``,
  simp[linear_order_def, EXISTS_PROD] >> rpt strip_tac >| [
    simp[SUBSET_DEF, in_domain, EXISTS_PROD] >> metis_tac[],
    simp[SUBSET_DEF, in_range, EXISTS_PROD] >> metis_tac[],
    metis_tac [INJ_preserves_transitive],
    metis_tac [INJ_preserves_antisym],
    prove_tac [INJ_DEF, IN_UNION, in_domain, in_range],
    prove_tac [INJ_DEF, IN_UNION, in_domain, in_range],
    prove_tac [INJ_DEF, IN_UNION, in_domain, in_range],
    prove_tac [INJ_DEF, IN_UNION, in_domain, in_range]
  ]);

val domain_IMAGE_ff = store_thm(
  "domain_IMAGE_ff",
  ``domain (IMAGE (f ## g) r) = IMAGE f (domain r)``,
  simp[domain_def, EXTENSION, EXISTS_PROD] >> prove_tac[]);
val range_IMAGE_ff = store_thm(
  "range_IMAGE_ff",
  ``range (IMAGE (f ## g) r) = IMAGE g (range r)``,
  simp[range_def, EXTENSION, EXISTS_PROD] >> prove_tac[]);

val INJ_preserves_wellorder = store_thm(
  "INJ_preserves_wellorder",
  ``wellorder r /\ INJ f (domain r UNION range r) t ==> wellorder (IMAGE (f ## f) r)``,
  simp[wellorder_def] >> rpt strip_tac >| [
    fs[wellfounded_def, strict_def] >> qx_gen_tac `s` >>
    disch_then (Q.X_CHOOSE_THEN `e` assume_tac) >>
    asm_simp_tac (srw_ss() ++ DNF_ss) [EXISTS_PROD] >>
    Cases_on `s INTER IMAGE f (domain r UNION range r) = {}` >-
      (qexists_tac `e` >> fs[EXTENSION, in_domain, in_range] >> metis_tac[]) >>
    pop_assum mp_tac >> qabbrev_tac `DR = domain r UNION range r` >>
    asm_simp_tac (srw_ss() ++ DNF_ss)[EXTENSION] >>
    qx_gen_tac `x` >> strip_tac >>
    first_x_assum (qspec_then `{ x | x IN DR /\ f x IN s }` mp_tac) >>
    asm_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss) [] >>
    disch_then (Q.X_CHOOSE_THEN `min` strip_assume_tac) >>
    qexists_tac `f min` >> simp[] >> map_every qx_gen_tac [`a`, `b`] >>
    rpt strip_tac >>
    `a IN DR /\ b IN DR` by (rw[Abbr`DR`, in_domain, in_range] >> metis_tac[]) >>
    `b = min` by metis_tac [INJ_DEF] >> metis_tac[],
    simp[domain_IMAGE_ff, range_IMAGE_ff] >>
    metis_tac [IMAGE_UNION, INJ_preserves_linear_order],
    fs[reflexive_def, EXISTS_PROD, in_domain, in_range] >>
    metis_tac[]
  ]);

val wellorder_fromNat_SUM = store_thm(
  "wellorder_fromNat_SUM",
  ``wellorder { (INL i, INL j) | i <= j /\ j < n }``,
  qmatch_abbrev_tac `wellorder w` >>
  qabbrev_tac `w0 = { (i,j) | i <= j /\ j < n }` >>
  `w = IMAGE (INL ## INL) w0`
     by simp[EXTENSION, Abbr`w`, Abbr`w0`, EXISTS_PROD] >>
  simp[] >> match_mp_tac (GEN_ALL INJ_preserves_wellorder) >>
  `wellorder w0` by simp[Abbr`w0`, wellorder_fromNat] >>
  simp[INJ_DEF] >>
  qexists_tac `IMAGE INL (domain w0 UNION range w0)` >>
  simp[]);

val fromNatWO_def = Define`
  fromNatWO n = mkWO { (INL i, INL j) | i <= j /\ j < n }
`

val fromNatWO_11 = store_thm(
  "fromNatWO_11",
  ``(fromNatWO i = fromNatWO j) <=> (i = j)``,
  rw[fromNatWO_def, WEXTENSION, wellorder_fromNat_SUM,
     destWO_mkWO] >>
  simp[Once EQ_IMP_THM] >> strip_tac >>
  spose_not_then assume_tac >>
  `i < j \/ j < i` by DECIDE_TAC >| [
     first_x_assum (qspecl_then [`INL i`, `INL i`] mp_tac),
     first_x_assum (qspecl_then [`INL j`, `INL j`] mp_tac)
  ] >> srw_tac[ARITH_ss][]);

val elsOf_fromNatWO = store_thm(
  "elsOf_fromNatWO",
  ``elsOf (fromNatWO n) = IMAGE INL (count n)``,
  simp[fromNatWO_def, EXTENSION, elsOf_def, destWO_mkWO,
       wellorder_fromNat_SUM, in_domain, in_range, EQ_IMP_THM] >>
  simp_tac (srw_ss() ++ DNF_ss ++ ARITH_ss) [] >>
  qx_gen_tac `x` >> strip_tac >> disj1_tac >> qexists_tac `x` >> rw[]);



val WLE_WIN = store_thm(
  "WLE_WIN",
  ``(x,y) WLE w ==> (x = y) \/ (x,y) WIN w``,
  rw[strict_def]);

val elsOf_wobound = store_thm(
  "elsOf_wobound",
  ``elsOf (wobound x w) = { y | (y,x) WIN w }``,
  simp[wobound_def, EXTENSION] >> qx_gen_tac `a` >>
  simp[elsOf_def, wellorder_rrestrict, destWO_mkWO] >>
  simp[rrestrict_def, iseg_def, domain_def, range_def] >>
  metis_tac [elsOf_WLE, WIN_elsOf]);

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

val orderlt_REFL = store_thm(
  "orderlt_REFL",
  ``orderlt w w = F``,
  simp[orderlt_def] >> qx_gen_tac `x` >> Cases_on `x IN elsOf w` >> simp[] >>
  simp[orderiso_thm] >> qx_gen_tac `f` >>
  Cases_on `BIJ f (elsOf w) (elsOf (wobound x w))` >> simp[strict_def] >>
  spose_not_then strip_assume_tac >>
  `f x IN elsOf (wobound x w)` by metis_tac [BIJ_IFF_INV] >>
  `elsOf (wobound x w) = {y | (y,x) WIN w}`
       by fs[elsOf_wobound] >>
  `!n. (FUNPOW f (SUC n) x, FUNPOW f n x) WIN w`
     by (Induct >> simp[] >- fs[] >>
         `(FUNPOW f (SUC (SUC n)) x, FUNPOW f (SUC n) x) WIN wobound x w`
            by metis_tac [arithmeticTheory.FUNPOW_SUC, WIN_WLE, WIN_REFL,
                          WLE_WIN] >>
         fs [WIN_wobound]) >>
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
  qexists_tac `g` >> rpt conj_tac >| [
    qx_gen_tac `y` >> strip_tac >>
    `y IN elsOf w2` by metis_tac [WIN_elsOf] >>
    `g y IN elsOf w1` by metis_tac[] >>
    metis_tac [WIN_trichotomy, WIN_REFL, WIN_TRANS],
    metis_tac [WIN_elsOf],
    metis_tac [WIN_elsOf]
  ])

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
  `(g a, b) WIN w3` by fs[elsOf_wobound, in_domain, in_range] >>
  qexists_tac `g a` >> conj_tac >- metis_tac[WIN_elsOf] >>
  match_mp_tac orderiso_TRANS >> qexists_tac `wobound a w2` >>
  rw[] >> rw[orderiso_thm] >> qexists_tac `g` >> conj_tac >| [
    `wobound (g a) w3 = wobound (g a) (wobound b w3)`
      by rw[wobound2] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac wobounds_preserve_bijections >> rw[],
    fs[WIN_wobound]
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
  rw[EXTENSION, RESTRICT_DEF, iseg_def] >> srw_tac[CONJ_ss][]);

val wo2wo_thm = save_thm(
  "wo2wo_thm",
  wo2wo_def |> concl |> strip_forall |> #2 |> rhs |> strip_comb |> #2
            |> C ISPECL WFREC_THM
            |> C MATCH_MP WIN_WF2
            |> SIMP_RULE (srw_ss()) []
            |> REWRITE_RULE [GSYM wo2wo_def, restrict_away])

val WO_INDUCTION =
    WF_INDUCTION_THM |> C MATCH_MP WIN_WF2 |> Q.GEN `w`
                                    |> BETA_RULE

val wleast_IN_wo = store_thm(
  "wleast_IN_wo",
  ``(wleast w s = SOME x) ==>
       x IN elsOf w /\ x NOTIN s /\
       !y. y IN elsOf w /\ y NOTIN s /\ x <> y ==> (x,y) WIN w``,
  simp[wleast_def] >> DEEP_INTRO_TAC some_intro >>
  simp[]);

val wleast_EQ_NONE = store_thm(
  "wleast_EQ_NONE",
  ``(wleast w s = NONE) ==> elsOf w SUBSET s``,
  simp[wleast_def] >> DEEP_INTRO_TAC some_intro >> rw[] >>
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
  ONCE_REWRITE_TAC [wo2wo_thm] >> rw[LET_THM] >>
  match_mp_tac SUBSET_ANTISYM >> rw[IMAGE_wo2wo_SUBSET] >>
  match_mp_tac SUBSET_TRANS >>
  qexists_tac `IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 x) DELETE NONE)` >>
  conj_tac >- (
    Cases_on`wleast w2 (IMAGE THE (IMAGE (wo2wo w1 w2) (iseg w1 x) DELETE NONE))` >>
    imp_res_tac wleast_EQ_NONE >> fs[] ) >>
  simp_tac (srw_ss() ++ DNF_ss) [SUBSET_DEF] >>
  qsuff_tac `!a. a IN iseg w1 x ==> a IN iseg w1 y` >- metis_tac[] >>
  rw[iseg_def] >> metis_tac [WIN_TRANS]);

val wo2wo_EQ_SOME_downwards = store_thm(
  "wo2wo_EQ_SOME_downwards",
  ``!x y. (wo2wo w1 w2 x = SOME y) ==>
          !x0. (x0,x) WIN w1 ==> ?y0. wo2wo w1 w2 x0 = SOME y0``,
  metis_tac [wo2wo_EQ_NONE, option_CASES]);

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
  simp[wleast_def] >> DEEP_INTRO_TAC some_intro >> simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >> metis_tac[SUBSET_DEF]);

val wo2wo_mono = store_thm(
  "wo2wo_mono",
  ``(wo2wo w1 w2 x0 = SOME y0) /\ (wo2wo w1 w2 x = SOME y) /\ (x0,x) WIN w1 ==>
    (y0,y) WIN w2``,
  rpt strip_tac >>
  `x0 IN elsOf w1 /\ x IN elsOf w1` by metis_tac [WIN_elsOf] >>
  `y0 <> y` by metis_tac [WIN_REFL, wo2wo_11] >>
  rpt (qpat_x_assum `wo2wo X Y Z = WW` mp_tac) >>
  ONCE_REWRITE_TAC [wo2wo_thm] >> rw[LET_THM] >>
  metis_tac [mono_woseg, wleast_SUBSET]);

val wo2wo_ONTO = store_thm(
  "wo2wo_ONTO",
  ``x IN elsOf w1 /\ (wo2wo w1 w2 x = SOME y) /\ (y0,y) WIN w2 ==>
    ?x0. x0 IN elsOf w1 /\ (wo2wo w1 w2 x0 = SOME y0)``,
  simp[SimpL ``$==>``, Once wo2wo_thm] >> rw[] >>
  spose_not_then strip_assume_tac >>
  `y0 NOTIN woseg w1 w2 x`
     by (asm_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `a` >>
         `(wo2wo w1 w2 a = NONE) \/ ?y'. wo2wo w1 w2 a = SOME y'`
            by metis_tac [option_CASES] >> simp[iseg_def] >>
         metis_tac[WIN_elsOf]) >>
  `y0 <> y` by metis_tac [WIN_REFL] >>
  `y0 IN elsOf w2 /\ y IN elsOf w2` by metis_tac [WIN_elsOf] >>
  metis_tac [WIN_TRANS, WIN_REFL, wleast_IN_wo]);

val wo2wo_EQ_NONE_woseg = store_thm(
  "wo2wo_EQ_NONE_woseg",
  ``(wo2wo w1 w2 x = NONE) ==> (elsOf w2 = woseg w1 w2 x)``,
  rw[Once wo2wo_thm, LET_THM] >>
  spose_not_then strip_assume_tac >>
  last_x_assum mp_tac >> simp[] >>
  spose_not_then strip_assume_tac >>
  fs[NOT_IS_SOME_EQ_NONE] >>
  imp_res_tac wleast_EQ_NONE >>
  metis_tac[IMAGE_wo2wo_SUBSET,SUBSET_DEF,EXTENSION]);

val orderlt_trichotomy = store_thm(
  "orderlt_trichotomy",
  ``orderlt w1 w2 \/ orderiso w1 w2 \/ orderlt w2 w1``,
  Cases_on `?x. x IN elsOf w1 /\ (wo2wo w1 w2 x = NONE)` >| [
    `?x0. wleast w1 { x | ?y. wo2wo w1 w2 x = SOME y } = SOME x0`
       by (Cases_on `wleast w1 { x | ?y. wo2wo w1 w2 x = SOME y }` >>
           rw[] >> imp_res_tac wleast_EQ_NONE >>
           pop_assum mp_tac >> simp[SUBSET_DEF] >> qexists_tac `x` >>
           rw[]) >>
    pop_assum (mp_tac o MATCH_MP (GEN_ALL wleast_IN_wo)) >>
    rw[] >>
    `!x. (x,x0) WIN w1 ==> ?y. wo2wo w1 w2 x = SOME y`
       by metis_tac [WIN_TRANS, WIN_REFL, WIN_elsOf] >>
    qsuff_tac `orderlt w2 w1` >- rw[] >>
    simp[orderlt_def] >> qexists_tac `x0` >> rw[] >>
    MATCH_MP_TAC orderiso_SYM >>
    rw[orderiso_def] >>
    qexists_tac `THE o wo2wo w1 w2` >>
    `elsOf (wobound x0 w1) = { x | (x,x0) WIN w1 }` by rw[elsOf_wobound] >>
    simp[] >> rpt conj_tac >| [
      metis_tac [wo2wo_IN_w2, THE_DEF],
      metis_tac [wo2wo_11, THE_DEF, WIN_elsOf],
      `elsOf w2 = woseg w1 w2 x0`
        by metis_tac [wo2wo_EQ_NONE_woseg, option_CASES] >>
      asm_simp_tac (srw_ss() ++ DNF_ss) [iseg_def] >>
      metis_tac [option_CASES],
      simp[WIN_wobound] >> metis_tac [THE_DEF, wo2wo_mono]
    ],
    ALL_TAC
  ] >>
  fs[METIS_PROVE []``(!x. ~P x \/ Q x) = (!x. P x ==> Q x)``,
     METIS_PROVE [option_CASES, NOT_SOME_NONE]
                  ``(x <> NONE) <=> ?y. x = SOME y``] >>
  Cases_on `elsOf w2 = { y | ?x. x IN elsOf w1 /\ (wo2wo w1 w2 x = SOME y) }`
  >| [
    qsuff_tac `orderiso w1 w2` >- rw[] >>
    rw[orderiso_def] >> qexists_tac `THE o wo2wo w1 w2` >>
    pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [EXTENSION]) >>
    simp[] >> rpt conj_tac >| [
      metis_tac [THE_DEF, option_CASES],
      metis_tac [wo2wo_11, THE_DEF, option_CASES],
      metis_tac [THE_DEF],
      metis_tac [THE_DEF, wo2wo_mono, WIN_elsOf,
                 option_CASES]
    ],
    ALL_TAC
  ] >>
  `?y. y IN elsOf w2 /\ !x. x IN elsOf w1 ==> (wo2wo w1 w2 x <> SOME y)`
    by (pop_assum mp_tac >> simp[EXTENSION] >> metis_tac [wo2wo_IN_w2]) >>
  qabbrev_tac `
    y0_opt = wleast w2 { y | ?x. x IN elsOf w1 /\ (wo2wo w1 w2 x = SOME y) }
  ` >>
  `y0_opt <> NONE`
     by (qunabbrev_tac `y0_opt` >> strip_tac >>
         imp_res_tac wleast_EQ_NONE >> fs[SUBSET_DEF] >> metis_tac[]) >>
  `?y0. y0_opt = SOME y0` by metis_tac [option_CASES] >>
  qunabbrev_tac `y0_opt` >>
  pop_assum (strip_assume_tac o MATCH_MP wleast_IN_wo) >> fs[] >>
  qsuff_tac `orderlt w1 w2` >- rw[] >> simp[orderlt_def] >>
  qexists_tac `y0` >> simp[orderiso_def] >>
  qexists_tac `THE o wo2wo w1 w2` >>
  `!a b. a IN elsOf w1 /\ (wo2wo w1 w2 a = SOME b) ==> (b,y0) WIN w2`
    by (rpt strip_tac >>
        `b <> y0` by metis_tac [] >>
        `~((y0,b) WIN w2)`
           by metis_tac [wo2wo_ONTO, NOT_SOME_NONE] >>
        metis_tac [WIN_trichotomy, wo2wo_IN_w2]) >>
  simp[elsOf_wobound] >> rpt conj_tac >| [
    metis_tac [THE_DEF, option_CASES],
    metis_tac [THE_DEF, wo2wo_11, option_CASES],
    metis_tac [WIN_REFL, WIN_TRANS, WIN_elsOf, THE_DEF, option_CASES],
    simp[WIN_wobound] >>
    metis_tac [wo2wo_mono, THE_DEF, WIN_elsOf, option_CASES]
  ]);

val wZERO_def = Define`wZERO = mkWO {}`

val elsOf_wZERO = store_thm(
  "elsOf_wZERO",
  ``elsOf wZERO = {}``,
  simp[wZERO_def, elsOf_def, destWO_mkWO,
       wellorder_EMPTY, EXTENSION, in_domain, in_range]);
val _ = export_rewrites ["elsOf_wZERO"]

val WIN_wZERO = store_thm(
  "WIN_wZERO",
  ``(x,y) WIN wZERO <=> F``,
  simp[wZERO_def, destWO_mkWO, wellorder_EMPTY,
       strict_def]);
val _ = export_rewrites ["WIN_wZERO"]

val WLE_wZERO = store_thm(
  "WLE_wZERO",
  ``(x,y) WLE wZERO <=> F``,
  simp[wZERO_def, destWO_mkWO, wellorder_EMPTY]);
val _ = export_rewrites ["WLE_wZERO"]

val orderiso_wZERO = store_thm(
  "orderiso_wZERO",
  ``orderiso wZERO w <=> (w = wZERO)``,
  simp[orderiso_thm, BIJ_EMPTY, EQ_IMP_THM] >>
  Q.ISPEC_THEN `w` strip_assume_tac wellorder_cases >>
  simp[elsOf_def, EXTENSION, in_range, in_domain, wZERO_def,
       #term_ABS_pseudo11 wellorder_results, wellorder_EMPTY,
       destWO_mkWO,
       FORALL_PROD]);

val elsOf_EQ_EMPTY = store_thm(
  "elsOf_EQ_EMPTY",
  ``(elsOf w = {}) <=> (w = wZERO)``,
  simp[EQ_IMP_THM] >> strip_tac >>
  qsuff_tac `orderiso w wZERO` >- metis_tac [orderiso_wZERO, orderiso_SYM] >>
  simp[orderiso_thm, BIJ_EMPTY] >> metis_tac [WIN_elsOf, NOT_IN_EMPTY]);
val _ = export_rewrites ["elsOf_EQ_EMPTY"]

val LT_wZERO = store_thm(
  "LT_wZERO",
  ``orderlt w wZERO = F``,
  simp[orderlt_def]);

val orderlt_WF = store_thm(
  "orderlt_WF",
  ``WF (orderlt : 'a wellorder -> 'a wellorder -> bool)``,
  rw[prim_recTheory.WF_IFF_WELLFOUNDED, prim_recTheory.wellfounded_def] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `w0 = f 0` >>
  qsuff_tac `~ WF (\x y. (x,y) WIN w0)` >- rw[WIN_WF2] >>
  simp[WF_DEF] >>
  `!n. orderlt (f (SUC n)) w0`
     by (Induct >- metis_tac [arithmeticTheory.ONE] >>
         metis_tac [orderlt_TRANS]) >>
  `!n. ?x. x IN elsOf w0 /\ orderiso (wobound x w0) (f (SUC n))`
     by metis_tac [orderlt_def, orderiso_SYM] >>
  qexists_tac `
     \e. ?n. e IN elsOf w0 /\ orderiso (wobound e w0) (f (SUC n))
  ` >> simp[] >> conj_tac >- metis_tac[] >>
  qx_gen_tac `y` >>
  Cases_on `y IN elsOf w0` >> simp[] >>
  Cases_on `!n. ~ orderiso (wobound y w0) (f (SUC n))` >> simp[] >>
  pop_assum (Q.X_CHOOSE_THEN `m` strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `orderlt (f (SUC (SUC m))) (f (SUC m))` by metis_tac[] >>
  pop_assum (Q.X_CHOOSE_THEN `p` strip_assume_tac o
             SIMP_RULE (srw_ss()) [orderlt_def]) >>
  `?h. BIJ h (elsOf (f (SUC m))) (elsOf (wobound y w0)) /\
       !a b. (a,b) WIN f (SUC m) ==> (h a, h b) WIN wobound y w0`
    by metis_tac [orderiso_thm, orderiso_SYM] >>
  qexists_tac `h p` >>
  `h p IN elsOf (wobound y w0)` by metis_tac [BIJ_IFF_INV] >>
  pop_assum mp_tac >> simp[elsOf_wobound] >> rw[] >>
  qexists_tac `SUC m` >> conj_tac >- metis_tac [WIN_elsOf] >>
  match_mp_tac (INST_TYPE [beta |-> alpha] orderiso_TRANS) >>
  qexists_tac `wobound p (f (SUC m))` >>
  Tactical.REVERSE conj_tac >- metis_tac [orderiso_SYM] >>
  match_mp_tac orderiso_SYM >> simp[orderiso_thm] >> qexists_tac `h` >>
  conj_tac
    >- (`wobound (h p) w0 = wobound (h p) (wobound y w0)` by rw [wobound2] >>
        pop_assum SUBST1_TAC >>
        match_mp_tac wobounds_preserve_bijections >> rw[]) >>
  fs[WIN_wobound])

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
    rw[orderiso_thm] >> qexists_tac `f` >> rw[WIN_wobound] >>
    match_mp_tac wobounds_preserve_bijections >>
    fs[orderiso_thm],
    `orderiso x0 (wobound x b0)` by metis_tac [orderiso_TRANS] >>
    `?f. BIJ f (elsOf b0) (elsOf a0) /\
         (!x y. (x,y) WIN b0 ==> (f x, f y) WIN a0)`
       by metis_tac [orderiso_thm, orderiso_SYM] >>
    qexists_tac `f x` >> conj_tac >- metis_tac [BIJ_IFF_INV] >>
    qsuff_tac `orderiso (wobound x b0) (wobound (f x) a0)`
      >- metis_tac [orderiso_TRANS] >>
    rw[orderiso_thm] >> qexists_tac `f` >> rw[WIN_wobound] >>
    match_mp_tac wobounds_preserve_bijections >>
    metis_tac [orderiso_thm, orderiso_SYM]
  ]);

val finite_def = Define`
  finite w = FINITE (elsOf w)
`;

val finite_iso = store_thm(
  "finite_iso",
  ``orderiso w1 w2 ==> (finite w1 <=> finite w2)``,
  rw[orderiso_thm, finite_def] >> metis_tac [BIJ_FINITE, BIJ_LINV_BIJ]);

val finite_wZERO = store_thm(
  "finite_wZERO",
  ``finite wZERO``,
  rw[finite_def]);

val orderiso_unique = store_thm(
  "orderiso_unique",
  ``BIJ f1 (elsOf w1) (elsOf w2) /\ BIJ f2 (elsOf w1) (elsOf w2) /\
    (!x y. (x,y) WIN w1 ==> (f1 x, f1 y) WIN w2) /\
    (!x y. (x,y) WIN w1 ==> (f2 x, f2 y) WIN w2) ==>
    !x. x IN elsOf w1 ==> (f1 x = f2 x)``,
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  `wellorder (destWO w1)` by rw[termP_term_REP] >>
  fs[wellorder_def, wellfounded_def] >>
  first_x_assum (qspec_then `elsOf w1 INTER {x | f1 x <> f2 x}` mp_tac) >>
  asm_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss) [] >>
  qx_gen_tac `min` >> Cases_on `min IN elsOf w1` >> fs[] >>
  Cases_on `f1 min = f2 min` >> simp[] >>
  Cases_on `(f1 min, f2 min) WIN w2` >| [
    `?a. (f2 a = f1 min) /\ a IN elsOf w1` by metis_tac [BIJ_IFF_INV] >>
    `(a,min) WIN w1` by metis_tac [WIN_trichotomy, WIN_TRANS, WIN_REFL] >>
    metis_tac [BIJ_IFF_INV],
    `(f2 min, f1 min) WIN w2` by metis_tac [BIJ_IFF_INV, WIN_trichotomy] >>
    `?a. (f1 a = f2 min) /\ a IN elsOf w1` by metis_tac [BIJ_IFF_INV] >>
    `(a,min) WIN w1` by metis_tac [WIN_trichotomy, WIN_TRANS, WIN_REFL] >>
    metis_tac [BIJ_IFF_INV]
  ]);

val seteq_wlog = store_thm(
  "seteq_wlog",
  ``!f.
      (!a b. P a b ==> P b a) /\ (!x a b. P a b /\ x IN f a ==> x IN f b) ==>
      (!a b. P a b ==> (f a = f b))``,
  rpt strip_tac >> match_mp_tac SUBSET_ANTISYM >> metis_tac[SUBSET_DEF])

val wo_INDUCTION = save_thm(
  "wo_INDUCTION",
  MATCH_MP WF_INDUCTION_THM WIN_WF2
           |> SIMP_RULE (srw_ss()) []
           |> Q.SPEC `\x. x IN elsOf w ==> P x`
           |> SIMP_RULE (srw_ss()) []
           |> Q.GEN `w` |> Q.GEN `P`)

val FORALL_NUM = store_thm(
  "FORALL_NUM",
  ``(!n. P n) <=> P 0 /\ !n. P (SUC n)``,
  metis_tac [arithmeticTheory.num_CASES])

val strict_UNION = store_thm(
  "strict_UNION",
  ``strict (r1 UNION r2) = strict r1 UNION strict r2``,
  simp[EXTENSION, FORALL_PROD, strict_def] >> metis_tac[]);

val WLE_WIN_EQ = store_thm(
  "WLE_WIN_EQ",
  ``(x,y) WLE w <=> (x = y) /\ x IN elsOf w \/ (x,y) WIN w``,
  metis_tac [elsOf_WLE, WLE_WIN, WIN_WLE]);

val remove_def = Define`
  remove e w = mkWO { (x,y) | x <> e /\ y <> e /\ (x,y) WLE w }
`;

val wellorder_remove = store_thm(
  "wellorder_remove",
  ``wellorder { (x,y) | x <> e /\ y <> e /\ (x,y) WLE w }``,
  qspec_then `w` assume_tac (GEN_ALL termP_term_REP) >>
  qmatch_abbrev_tac `wellorder r` >>
  `r = rrestrict (destWO w) (elsOf w DELETE e)`
     by (simp[EXTENSION, Abbr`r`, rrestrict_def, FORALL_PROD] >>
         metis_tac [WLE_elsOf]) >>
  simp[wellorder_rrestrict]);

val elsOf_remove = store_thm(
  "elsOf_remove",
  ``elsOf (remove e w) = elsOf w DELETE e``,
  simp[elsOf_def, remove_def, wellorder_remove,
       destWO_mkWO] >>
  simp[domain_def, range_def, EXTENSION] >>
  metis_tac[WLE_elsOf, WLE_WIN_EQ]);

val WIN_remove = store_thm(
  "WIN_remove",
  ``(x,y) WIN remove e w <=> x <> e /\ y <> e /\ (x,y) WIN w``,
  simp[remove_def, destWO_mkWO, wellorder_remove, strict_def]);

val ADD1_def = Define`
  ADD1 e w =
    if e IN elsOf w then w
    else
      mkWO (destWO w UNION {(x,e) | x IN elsOf w} UNION {(e,e)})
`;

val wellorder_ADD1 = store_thm(
  "wellorder_ADD1",
  ``e NOTIN elsOf w ==>
    wellorder (destWO w UNION {(x,e) | x IN elsOf w} UNION {(e,e)})``,
  `wellorder (destWO w)` by rw [termP_term_REP] >>
  rw[wellorder_def] >| [
    simp[wellfounded_def, strict_def] >> qx_gen_tac `s` >>
    disch_then (Q.X_CHOOSE_THEN `a` assume_tac) >>
    Cases_on `?b. b IN s /\ b IN elsOf w` >> fs[] >| [
      fs[wellorder_def, wellfounded_def] >>
      first_x_assum (qspec_then `elsOf w INTER s` mp_tac) >>
      asm_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss)[] >>
      metis_tac [WLE_elsOf, WLE_WIN],
      qexists_tac `a` >> metis_tac [WLE_elsOf]
    ],
    fs[linear_order_def, wellorder_def] >>
    `domain (destWO w UNION {(x,e) | x IN elsOf w} UNION {(e,e)}) =
     e INSERT elsOf w`
       by (rw[EXTENSION, in_domain, in_range, EQ_IMP_THM] >>
           metis_tac [WLE_elsOf]) >>
    `range (destWO w UNION {(x,e) | x IN elsOf w} UNION {(e,e)}) =
     e INSERT elsOf w`
       by (rw[EXTENSION, in_domain, in_range] >>
           metis_tac [elsOf_WLE, WLE_elsOf]) >>
    simp[] >> rpt conj_tac >| [
      fs[transitive_def] >> metis_tac[WLE_elsOf, elsOf_WLE],
      fs[antisym_def] >> metis_tac[WLE_elsOf, elsOf_WLE],
      fs[in_domain, in_range] >> metis_tac[WLE_elsOf, elsOf_WLE]
    ],
    fs[wellorder_def, reflexive_def, in_domain, in_range] >>
    metis_tac[WLE_elsOf, elsOf_WLE]
  ])

val elsOf_ADD1 = store_thm(
  "elsOf_ADD1",
  ``elsOf (ADD1 e w) = e INSERT elsOf w``,
  simp[EXTENSION, ADD1_def, Once elsOf_def, SimpLHS] >>
  qx_gen_tac `x` >>
  rw[#repabs_pseudo_id wellorder_results, wellorder_ADD1] >| [
    fs[elsOf_def] >> metis_tac[],
    simp[in_domain, in_range] >> metis_tac [WLE_elsOf]
  ]);

val WIN_ADD1 = store_thm(
  "WIN_ADD1",
  ``(x,y) WIN ADD1 e w <=>
      e NOTIN elsOf w /\ x IN elsOf w /\ (y = e) \/
      (x,y) WIN w``,
  rw[#repabs_pseudo_id wellorder_results, wellorder_ADD1, ADD1_def,
     strict_def] >> metis_tac[]);

val elsOf_cardeq_iso = store_thm(
  "elsOf_cardeq_iso",
  ``INJ f (elsOf (wo:'b wellorder)) univ(:'a) ==>
    ?wo':'a wellorder. orderiso wo wo'``,
  simp[elsOf_def] >> strip_tac >>
  `wellorder (destWO wo)` by simp[#termP_term_REP wellorder_results] >>
  qexists_tac `mkWO (IMAGE (f ## f) (destWO wo))` >>
  simp[orderiso_thm] >>
  `wellorder (IMAGE (f ## f) (destWO wo))`
    by imp_res_tac INJ_preserves_wellorder >>
  qexists_tac `f` >>
  simp[destWO_mkWO, elsOf_def, domain_IMAGE_ff, range_IMAGE_ff] >>
  simp_tac bool_ss [GSYM IMAGE_UNION] >>
  qabbrev_tac `
    els = domain (destWO wo) UNION range (destWO wo)` >>
  simp[BIJ_DEF, SURJ_IMAGE] >>
  simp[strict_def, EXISTS_PROD] >>
  fs[INJ_DEF] >>
  map_every qx_gen_tac [`x`, `y`] >> strip_tac >>
  `x IN elsOf wo /\ y IN elsOf wo` by metis_tac [WLE_elsOf] >>
  fs[elsOf_def] >> metis_tac[IN_UNION]);

fun unabbrev_in_goal s = let
  fun check th = let
    val c = concl th
    val _ = match_term ``Abbrev b`` c
    val (v,ty) = c |> rand |> lhand |> dest_var
  in
    if v = s then let
        val th' = PURE_REWRITE_RULE [markerTheory.Abbrev_def] th
      in
        SUBST1_TAC th'
      end
    else NO_TAC
  end
in
  first_assum check
end

val allsets_wellorderable = store_thm(
  "allsets_wellorderable",
  ``!s. ?wo. elsOf wo = s``,
  gen_tac >>
  qabbrev_tac `A = { w | elsOf w SUBSET s }` >>
  qabbrev_tac `
    R = { (w1,w2) | w1 IN A /\ w2 IN A /\
                    ((w1 = w2) \/ ?x. x IN elsOf w2 /\ (w1 = wobound x w2)) }
  ` >>
  `A <> {}` by (simp[EXTENSION, Abbr`A`] >> qexists_tac `wZERO` >> simp[]) >>
  `partial_order R A`
    by (simp[partial_order_def, Abbr`R`, domain_def, range_def] >>
        rpt conj_tac
        >- simp_tac (srw_ss() ++ DNF_ss) [SUBSET_DEF]
        >- simp_tac (srw_ss() ++ DNF_ss) [SUBSET_DEF]
        >- (simp[transitive_def] >> rw[] >> fs[elsOf_wobound] >>
            metis_tac[wobound2, WIN_elsOf])
        >- simp[reflexive_def]
        >> simp[antisym_def] >> rw[] >> fs[elsOf_wobound] >>
           metis_tac[orderlt_def, orderiso_REFL, orderlt_REFL,
                     wobound2, WIN_elsOf]) >>
  `!c. chain c R ==> upper_bounds c R <> {}`
    by (simp[EXTENSION, chain_def, upper_bounds_def] >> gen_tac >> strip_tac >>
        qabbrev_tac `Ls = BIGUNION (IMAGE destWO c)` >>
        `!x y. (x,y) IN Ls <=> ?w. w IN c /\ (x,y) WLE w`
          by (simp_tac (srw_ss() ++ DNF_ss) [Abbr`Ls`] >> metis_tac[]) >>
        `!w1 w2. w1 IN c /\ w2 IN c ==> elsOf w1 SUBSET elsOf w2 \/ elsOf w2 SUBSET elsOf w1`
          by (rpt strip_tac >> `(w1,w2) IN R \/ (w2,w1) IN R` by metis_tac[] >>
              pop_assum mp_tac >> simp[Abbr`R`] >> rw[] >- simp[]
              >- (simp[SUBSET_DEF, elsOf_wobound] >> metis_tac [WIN_elsOf])
              >- simp[] >>
              simp[SUBSET_DEF, elsOf_wobound] >> metis_tac [WIN_elsOf]) >>
        `!e. e IN (domain Ls UNION range Ls) <=> ?w. w IN c /\ e IN elsOf w`
          by (simp[domain_def, range_def] >> gen_tac >>
              eq_tac >- metis_tac [WLE_elsOf] >>
              metis_tac [elsOf_WLE]) >>
        `wellorder Ls`
           by (simp[wellorder_def] >> rpt conj_tac
               >- ((* WF *)simp[wellfounded_def, strict_def] >>
                   simp_tac(srw_ss() ++ DNF_ss)[] >>
                   map_every qx_gen_tac [`ss`, `x`] >> strip_tac >>
                   Cases_on `?w. w IN c /\ ss INTER elsOf w <> {}`
                   >- (fs[] >>
                       `wellorder (destWO w)` by simp [termP_term_REP] >>
                       `wellfounded (strict (destWO w))` by fs[wellorder_def] >>
                       pop_assum (qspec_then `ss INTER elsOf w` mp_tac o
                                  SIMP_RULE (srw_ss()) [wellfounded_def]) >>
                       simp_tac (srw_ss() ++ DNF_ss)[] >>
                       `?y. y IN ss /\ y IN elsOf w`
                         by (fs[EXTENSION] >> metis_tac[]) >>
                       disch_then (qspec_then `y` mp_tac) >> simp[] >>
                       disch_then (Q.X_CHOOSE_THEN `min` strip_assume_tac) >>
                       qexists_tac `min` >> simp[] >>
                       map_every qx_gen_tac [`z`, `w'`] >> strip_tac >>
                       `!u. (u,min) WIN w ==> u NOTIN ss` by metis_tac [WIN_elsOf] >>
                       Cases_on `w = w'` >- metis_tac[WLE_WIN_EQ] >>
                       `(w,w') IN R \/ (w',w) IN R` by metis_tac[] >>
                       pop_assum mp_tac >>
                       asm_simp_tac (srw_ss() ++ DNF_ss) [Abbr`R`] >>
                       qx_gen_tac `b` >> strip_tac >>
                       first_x_assum match_mp_tac
                       >- (simp[WIN_wobound] >> fs[elsOf_wobound] >>
                           metis_tac[WLE_WIN_EQ, WIN_TRANS]) >>
                       metis_tac [WIN_wobound, WLE_WIN_EQ]) >>
                   fs[] >> qexists_tac `x` >> simp[] >>
                   fs[EXTENSION] >> metis_tac[WLE_elsOf])
               >- ((* linear *)
                   simp[linear_order_def] >> rpt conj_tac
                   >- ((* transitive *)
                       simp[transitive_def] >>
                       map_every qx_gen_tac [`x`, `y`, `z`] >>
                       disch_then (CONJUNCTS_THEN2
                                   (Q.X_CHOOSE_THEN `w1` strip_assume_tac)
                                   (Q.X_CHOOSE_THEN `w2` strip_assume_tac)) >>
                       `(w1,w2) IN R \/ (w2,w1) IN R` by simp[] >>
                       pop_assum mp_tac >> simp[Abbr`R`] >>
                       Cases_on `w1 = w2` >- metis_tac [WLE_TRANS] >> simp[]>>
                       rw[] >> fs[WLE_wobound] >> metis_tac[WLE_TRANS])
                   >- ((* antisym *)
                       simp[antisym_def] >>
                       map_every qx_gen_tac [`x`, `y`] >>
                       disch_then (CONJUNCTS_THEN2
                                   (Q.X_CHOOSE_THEN `w1` strip_assume_tac)
                                   (Q.X_CHOOSE_THEN `w2` strip_assume_tac)) >>
                       `(w1,w2) IN R \/ (w2,w1) IN R` by simp[] >>
                       pop_assum mp_tac >> simp[Abbr`R`] >>
                       Cases_on `w1 = w2` >- metis_tac [WLE_ANTISYM] >> simp[]>>
                       rw[] >> fs[WLE_wobound] >> metis_tac [WLE_ANTISYM]) >>
                   (* trichotomous *)
                   map_every qx_gen_tac [`x`, `y`] >>
                   disch_then (CONJUNCTS_THEN2
                               (Q.X_CHOOSE_THEN `w1` strip_assume_tac)
                               (Q.X_CHOOSE_THEN `w2` strip_assume_tac)) >>
                   `(w1,w2) IN R \/ (w2,w1) IN R` by simp[] >>
                   pop_assum mp_tac >> simp[Abbr`R`] >>
                   Cases_on `w1 = w2`
                   >- metis_tac [WIN_trichotomy, WLE_WIN_EQ] >> simp[]>>
                   rw[] >> fs[elsOf_wobound] >>
                   metis_tac [WIN_elsOf, WIN_trichotomy, WLE_WIN_EQ]) >>
               (* reflexive *)
               simp[reflexive_def] >> simp[elsOf_WLE]) >>
        qexists_tac `mkWO Ls` >> conj_tac
        >- ((* mkWO Ls IN range R *)
            simp[range_def] >> qexists_tac `wZERO` >>
            map_every unabbrev_in_goal ["R", "A"] >> simp[] >> conj_tac
            >- (asm_simp_tac bool_ss [elsOf_def, SUBSET_DEF, destWO_mkWO] >>
                simp_tac bool_ss [GSYM elsOf_def] >> qx_gen_tac `x` >>
                disch_then (Q.X_CHOOSE_THEN `w` strip_assume_tac) >>
                qpat_x_assum `w IN c`
                  (fn th =>
                     first_x_assum
                       (fn imp => mp_tac (MATCH_MP imp (CONJ th th)) >>
                                  simp[SUBSET_DEF, Abbr`R`, Abbr`A`] >>
                                  NO_TAC))) >>
            Cases_on `c = {}` >- fs[Abbr`Ls`, wZERO_def] >>
            Cases_on `c = {wZERO}` >- fs[Abbr`Ls`] >>
            `?w. w IN c /\ w <> wZERO` by (fs[EXTENSION] >> metis_tac[]) >>
            DISJ2_TAC >> qexists_tac `THE (wleast w {})` >>
            Cases_on `wleast w {}` >- (imp_res_tac wleast_EQ_NONE >> fs[]) >>
            pop_assum (mp_tac o MATCH_MP wleast_IN_wo) >> simp[] >>
            strip_tac >> asm_simp_tac bool_ss [elsOf_def, destWO_mkWO] >>
            simp_tac bool_ss [GSYM elsOf_def] >> conj_tac >- metis_tac[] >>
            simp[wobound_def,iseg_def, destWO_mkWO, strict_def] >>
            qmatch_abbrev_tac `wZERO = mkWO (rrestrict Ls ss)` >>
            qsuff_tac `ss = {}` >- simp[wZERO_def, rrestrict_def] >>
            qunabbrev_tac `ss` >> simp[EXTENSION] >>
            qx_gen_tac `y` >> Cases_on `x = y` >> simp[] >>
            qx_gen_tac `w'` >> Cases_on `w' IN c` >> simp[] >>
            `(w,w') IN R \/ (w',w) IN R` by simp[] >>
            pop_assum mp_tac >> simp[Abbr`R`] >>
            Cases_on `w = w'` >> simp[]
            >- metis_tac[WLE_WIN_EQ, WIN_elsOf, WIN_TRANS, WIN_REFL]
            >- (rw[] >> fs[elsOf_wobound, WIN_wobound] >>
                metis_tac [WLE_WIN_EQ, WIN_TRANS, WIN_REFL])
            >- metis_tac[WLE_WIN_EQ, WIN_elsOf, WIN_TRANS, WIN_REFL] >>
            rw[] >> rw[WLE_wobound] >>
            metis_tac [WIN_TRANS, WIN_REFL, WLE_WIN_EQ, WIN_elsOf]) >>
        (* mkWO Ls actually is u.b. *)
        qx_gen_tac `y` >> Cases_on `y IN c` >> simp[] >>
        `(y,y) IN R` by metis_tac[] >> pop_assum mp_tac >>
        unabbrev_in_goal "R" >> simp[] >> disch_then (K ALL_TAC) >>
        `mkWO Ls IN A`
          by (simp[Abbr`A`] >>
              asm_simp_tac bool_ss [elsOf_def, destWO_mkWO, SUBSET_DEF] >>
              simp_tac bool_ss [GSYM elsOf_def] >> qx_gen_tac `x` >>
              disch_then (Q.X_CHOOSE_THEN `w` strip_assume_tac) >>
              `(w,w) IN R` by metis_tac [] >> pop_assum mp_tac >>
              simp[Abbr`R`, SUBSET_DEF]) >> simp[] >>
        Cases_on `y = mkWO Ls` >> simp[] >>
        `elsOf y SUBSET elsOf (mkWO Ls)`
          by (asm_simp_tac bool_ss [SUBSET_DEF, elsOf_def, destWO_mkWO] >>
              metis_tac[]) >>
        `elsOf y <> elsOf (mkWO Ls)`
          by (strip_tac >>
              `y = mkWO Ls`
                by (ONCE_REWRITE_TAC [SYM (#term_REP_11 wellorder_results)] >>
                    simp[EXTENSION, destWO_mkWO, FORALL_PROD] >>
                    map_every qx_gen_tac [`a`, `b`] >> eq_tac >- metis_tac[] >>
                    disch_then (Q.X_CHOOSE_THEN `w` strip_assume_tac) >>
                    `(y,w) IN R \/ (w,y) IN R` by simp[] >>
                    pop_assum mp_tac >> simp[Abbr`R`] >> Cases_on `w = y` >>
                    simp[] >> TRY (fs[] >> NO_TAC) >>
                    asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
                    qx_gen_tac `x` >> strip_tac >> rw[]
                    >- (`x NOTIN elsOf (wobound x w)`
                          by simp_tac(srw_ss())[elsOf_wobound] >>
                        `x IN elsOf (mkWO Ls)`
                          by (asm_simp_tac bool_ss [destWO_mkWO, elsOf_def] >>
                              simp_tac bool_ss [GSYM elsOf_def] >>
                              metis_tac[]) >> metis_tac[]) >>
                    fs[WLE_wobound])) >>
        `?a. a IN elsOf (mkWO Ls) /\ a NOTIN elsOf y`
          by (fs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
        qexists_tac `THE (wleast (mkWO Ls) (elsOf y))` >>
        `(wleast (mkWO Ls) (elsOf y) = NONE) \/
         ?b. wleast (mkWO Ls) (elsOf y) = SOME b`
          by (Cases_on `wleast (mkWO Ls) (elsOf y)` >> simp[])
        >- (imp_res_tac wleast_EQ_NONE >> metis_tac [SUBSET_ANTISYM]) >>
        simp[] >>
        pop_assum (mp_tac o MATCH_MP wleast_IN_wo) >> strip_tac >> simp[] >>
        ONCE_REWRITE_TAC [SYM (#term_REP_11 wellorder_results)] >>
        simp[EXTENSION, WLE_wobound, FORALL_PROD, destWO_mkWO, strict_def] >>
        map_every qx_gen_tac [`d`, `e`] >> eq_tac
        >- (`?w. w IN c /\ b IN elsOf w` by metis_tac[elsOf_def, destWO_mkWO] >>
            strip_tac >>
            `d IN elsOf w /\ e IN elsOf w`
               by metis_tac[WLE_elsOf, SUBSET_DEF] >>
            `(w,y) IN R \/ (y,w) IN R` by simp[]
            >- (pop_assum mp_tac >> simp[Abbr`R`] >> `w <> y` by metis_tac[] >>
                simp[GSYM RIGHT_EXISTS_AND_THM] >>
                disch_then (Q.X_CHOOSE_THEN `x` strip_assume_tac) >>
                rw[] >> fs[elsOf_wobound] >> metis_tac [WIN_elsOf]) >>
            pop_assum mp_tac >> simp[Abbr`R`] >> `w <> y` by metis_tac[] >>
            simp[GSYM RIGHT_EXISTS_AND_THM] >>
            disch_then (Q.X_CHOOSE_THEN `x` strip_assume_tac) >>
            fs[WLE_wobound, elsOf_wobound] >> qexists_tac `w` >> simp[] >>
            `b = x`
              by (`x IN elsOf (mkWO Ls)`
                    by (simp[elsOf_def, destWO_mkWO] >>
                        metis_tac [IN_UNION, elsOf_def]) >>
                  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
                  Cases_on `b = x` >> simp[destWO_mkWO] >>
                  simp_tac (srw_ss()) [strict_def] >> DISJ1_TAC >>
                  `(x,b) WIN w` by metis_tac [WIN_trichotomy] >>
                  `(x,b) IN Ls` by metis_tac [WLE_WIN_EQ] >> strip_tac >>
                  metis_tac [WLE_ANTISYM, destWO_mkWO]) >>
            pop_assum SUBST_ALL_TAC >> metis_tac [WIN_REFL, WLE_WIN_EQ]) >>
        simp_tac (srw_ss() ++ CONJ_ss) [WLE_WIN_EQ] >>
        `!i w. w IN c /\ (i,b) WIN w ==> i IN elsOf y`
          by (rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >>
              `b <> i` by metis_tac [WIN_REFL] >>
              `i IN elsOf (mkWO Ls)`
                by metis_tac [WIN_elsOf, elsOf_def, destWO_mkWO] >>
              simp[destWO_mkWO] >> simp_tac (srw_ss()) [strict_def] >>
              `(i,b) IN Ls` by metis_tac[WLE_WIN_EQ] >>
              metis_tac[destWO_mkWO, WLE_ANTISYM]) >>
        Cases_on `d <> b` >> simp[] >> Cases_on `e = b` >> simp[] >>
        Cases_on `d = e` >> simp[] >>
        metis_tac[WIN_trichotomy, WLE_WIN_EQ, WLE_ANTISYM, destWO_mkWO]) >>
  `?M. M IN maximal_elements A R` by metis_tac [zorns_lemma] >>
  pop_assum mp_tac >> simp[maximal_elements_def] >> strip_tac >>
  Cases_on `elsOf M = s` >- metis_tac[] >>
  `elsOf M SUBSET s` by fs[Abbr`A`] >>
  `?a. a IN s /\ a NOTIN elsOf M`
    by (fs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  qabbrev_tac `Ms = destWO M UNION {(x,a) | x IN elsOf M} UNION {(a,a)}` >>
  `ADD1 a M IN A` by simp[Abbr`A`, elsOf_ADD1] >>
  `M <> ADD1 a M`
    by (disch_then (mp_tac o Q.AP_TERM `elsOf`) >>
        simp[EXTENSION, elsOf_ADD1] >> metis_tac[]) >>
  `(M,ADD1 a M) IN R`
    by (unabbrev_in_goal "R" >> simp[] >> qexists_tac `a` >>
        simp[WEXTENSION, WLE_wobound, WIN_ADD1, WLE_WIN_EQ, elsOf_ADD1] >>
        `!x. ~((x,a) WIN M)` by metis_tac [WIN_elsOf] >> simp[] >>
        metis_tac[WIN_elsOf]) >>
  metis_tac[]);

Theorem reln_to_rel[local]:
  reln_to_rel = CURRY
Proof
  simp[FUN_EQ_THM, reln_to_rel_def, IN_DEF]
QED

Theorem StrongWellOrderExists:
  ?R:'a -> 'a -> bool. StrongLinearOrder R /\ WF R
Proof
  qspec_then ‘univ(:'a)’ (qx_choose_then ‘wo’ assume_tac)
             allsets_wellorderable >>
  qspec_then ‘wo’ mp_tac (GEN_ALL termP_term_REP) >>
  simp[wellorder_def] >> gs[elsOf_def] >>
  strip_tac >> qexists_tac ‘CURRY $ strict $ destWO wo’ >>
  gs[wellfounded_WF] >>
  simp[GSYM strict_linear_order_reln_to_rel_conv_UNIV, GSYM reln_to_rel,
       strict_linear_order]
QED


(* ------------------------------------------------------------------------- *)
(*    Wellfoundedness (WF) from hol-light's iterateTheory                    *)
(* ------------------------------------------------------------------------- *)

(* Only used as a variable; don't want to contaminate other uses.
   In particular, this is used at quite a different precedence for left-shift
   in descendents of words
*)
val _ = temp_set_fixity "<<" (Infix(NONASSOC, 450));


val WF = store_thm ("WF",
  ``WF(<<) <=> !P:'a->bool. (?x. P(x)) ==> (?x. P(x) /\ !y. y << x ==> ~P(y))``,
    METIS_TAC [WF_DEF]);

(* ------------------------------------------------------------------------- *)
(* Strengthen it to equality.                                                *)
(* ------------------------------------------------------------------------- *)

val WF_EQ = store_thm ("WF_EQ",
 ``WF(<<) <=> !P:'a->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))``,
  REWRITE_TAC[WF] THEN MESON_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Equivalence of wellfounded induction.                                     *)
(* ------------------------------------------------------------------------- *)

val WF_IND = store_thm ("WF_IND",
 ``WF(<<) <=> !P:'a->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)``,
  REWRITE_TAC[WF] THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  POP_ASSUM(MP_TAC o SPEC ``\x:'a. ~(P:'a->bool)(x)``) THEN REWRITE_TAC[] THEN MESON_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Equivalence of the "infinite descending chains" version.                  *)
(* ------------------------------------------------------------------------- *)

val WF_DCHAIN = store_thm ("WF_DCHAIN",
 ``WF(<<) <=> ~(?s:num->'a. !n. s(SUC n) << s(n))``,
  SIMP_TAC std_ss [WF, TAUT `(a <=> ~b) <=> (~a <=> b)`, NOT_FORALL_THM] THEN
  EQ_TAC THEN DISCH_THEN CHOOSE_TAC THENL
   [POP_ASSUM(MP_TAC o REWRITE_RULE[NOT_IMP]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``a:'a``) ASSUME_TAC) THEN
    SUBGOAL_THEN ``!x:'a. ?y. P(x) ==> P(y) /\ y << x`` MP_TAC THENL
     [ASM_MESON_TAC[], SIMP_TAC std_ss [SKOLEM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN ``f:'a->'a`` STRIP_ASSUME_TAC) THEN
    KNOW_TAC ``?s. (s (0:num) = a) /\ (!n. s (SUC n) = f (s n))`` THENL
    [ASSUME_TAC prim_recTheory.num_Axiom_old THEN
     POP_ASSUM (MP_TAC o Q.SPECL [`a:'a`, `(\m n. f m)`]) THEN
     METIS_TAC [], STRIP_TAC] THEN
    EXISTS_TAC ``s:num->'a`` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN ``!n. P(s n) /\ s(SUC n):'a << s(n)``
      (fn th => ASM_MESON_TAC[th]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[],
    EXISTS_TAC ``\y:'a. ?n:num. y = s(n)`` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *uniqueness* part of recursion.                        *)
(* ------------------------------------------------------------------------- *)

val WF_UREC = store_thm ("WF_UREC",
 ``WF(<<) ==>
       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
            ==> !(f:'a->'b) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                              ==> (f = g)``,
  REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
  UNDISCH_TAC `` !(P :'a -> bool).
            (!(x :'a). (!(y :'a). y << x ==> P y) ==> P x) ==> !(x :'a). P x`` THEN
  DISCH_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `(\x. (f:'a->'b) x = g x)`) THEN
  SIMP_TAC std_ss [] THEN
  DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[]);

val WF_UREC_WF = store_thm ("WF_UREC_WF",
 ``(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
        ==> !(f:'a->bool) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                          ==> (f = g)) ==> WF(<<)``,
  REWRITE_TAC[WF_IND] THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``\f x. P(x:'a) \/ !z:'a. z << x ==> f(z)``) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [MESON_TAC[], DISCH_THEN(MP_TAC o SPECL [``P:'a->bool``, ``\x:'a. T``]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]]);

(* ------------------------------------------------------------------------- *)
(* Stronger form of recursion with "inductive invariant" (Krstic/Matthews).  *)
(* ------------------------------------------------------------------------- *)

val lemma = prove_nonschematic_inductive_relations_exist bool_monoset
   ``!f:'a->'b x. (!z. z << x ==> R z (f z)) ==> R x (H f x)``;

Theorem WF_REC_INVARIANT:
 WF(<<) ==>
 !H S. (!f g x. (!z. z << x ==> f z = g z /\ S z (f z)) ==>
                H f x = H g x /\ S x (H f x)) ==>
       ?f:'a->'b. !x. f x = H f x
Proof
  REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN ``R:'a->'b->bool`` STRIP_ASSUME_TAC lemma THEN
  SUBGOAL_THEN ``!x:'a. ?!y:'b. R x y`` (fn th => ASM_MESON_TAC[th]) THEN
  ONCE_REWRITE_TAC [METIS [] ``(?!y. R x y) = (\x. ?!y. R x y) x``] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  first_x_assum (CONV_TAC o BINDER_CONV o REWR_CONV) >>
  SUBGOAL_THEN ``!x:'a y:'b. R x y ==> S' x y`` MP_TAC THEN METIS_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *existence* part of recursion.                         *)
(* ------------------------------------------------------------------------- *)

val WF_REC = store_thm ("WF_REC",
 ``WF(<<)
   ==> !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
           ==> ?f:'a->'b. !x. f x = H f x``,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC_INVARIANT) THEN
  EXISTS_TAC ``\x:'a y:'b. T`` THEN ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness properties of natural numbers.                            *)
(* ------------------------------------------------------------------------- *)

val WF_num = store_thm ("WF_num",
 ``WF((<):num->num->bool)``,
  REWRITE_TAC[WF_IND, arithmeticTheory.COMPLETE_INDUCTION]);

val WF_REC_num = store_thm ("WF_REC_num",
 ``!H. (!f g n. (!m. m < n ==> (f m = g m)) ==> (H f n = H g n))
        ==> ?f:num->'a. !n. f n = H f n``,
  MATCH_ACCEPT_TAC(MATCH_MP WF_REC WF_num));

Theorem TARSKI_SET:
  !f. (!s t. s SUBSET t ==> f(s) SUBSET f(t)) ==> ?s:'a->bool. f(s) = s
Proof
  REPEAT STRIP_TAC THEN
  MAP_EVERY Q.ABBREV_TAC
            [`Y = {b:'a->bool | f(b) SUBSET b}`, `a:'a->bool = BIGINTER Y`] THEN
  ‘!b:'a->bool. b IN Y <=> f(b) SUBSET b’
    by SIMP_TAC std_ss [GSPECIFICATION, Abbr‘Y’] THEN
  ‘!b:'a->bool. b IN Y ==> f(a:'a->bool) SUBSET b’
    by METIS_TAC[SUBSET_TRANS, IN_BIGINTER, SUBSET_DEF] THEN
  ‘f(a:'a->bool) SUBSET a’ by METIS_TAC[IN_BIGINTER, SUBSET_DEF] THEN
   METIS_TAC[SUBSET_ANTISYM, IN_BIGINTER]
QED

val _ = export_theory()
