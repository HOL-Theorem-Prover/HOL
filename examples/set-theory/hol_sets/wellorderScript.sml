open HolKernel Parse boolLib bossLib
open lcsymtacs
open boolSimps

open set_relationTheory pred_setTheory cardinalTheory

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
  ``wellorder {(x,y)} <=> (x = y)``,
  rw[wellorder_def, wellfounded_def, strict_def, reflexive_def,
     domain_def, range_def] >>
  eq_tac >| [
    metis_tac[],
    simp[linear_order_def, transitive_def, domain_def, range_def, antisym_def]
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

val _ = overload_on("WIN", ``λp w. p IN strict (wellorder_REP w)``)
val _ = set_fixity "WIN" (Infix(NONASSOC, 425))
val _ = overload_on("WLE", ``λp w. p IN wellorder_REP w``)
val _ = set_fixity "WLE" (Infix(NONASSOC, 425))
val _ = overload_on ("wrange", ``\w. range (wellorder_REP w)``)

val WIN_elsOf = store_thm(
  "WIN_elsOf",
  ``(x,y) WIN w ==> x IN elsOf w /\ y IN elsOf w``,
  rw[elsOf_def, range_def, domain_def, strict_def] >> metis_tac[]);

val WLE_elsOf = store_thm(
  "WLE_elsOf",
  ``(x,y) WLE w ==> x ∈ elsOf w ∧ y ∈ elsOf w``,
  rw[elsOf_def, range_def, domain_def] >> metis_tac[]);

val WIN_trichotomy = store_thm(
  "WIN_trichotomy",
  ``!x y. x IN elsOf w /\ y IN elsOf w ==>
          (x,y) WIN w \/ (x = y) \/ (y,x) WIN w``,
  rpt strip_tac >>
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[elsOf_def, wellorder_def, strict_def, linear_order_def] >> metis_tac[]);

val WIN_REFL = store_thm(
  "WIN_REFL",
  ``(x,x) WIN w = F``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, strict_def]);
val _ = export_rewrites ["WIN_REFL"]

val WLE_TRANS = store_thm(
  "WLE_TRANS",
  ``(x,y) WLE w /\ (y,z) WLE w ==> (x,z) WLE w``,
  strip_tac >>
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, linear_order_def, transitive_def] >> metis_tac[]);

val WLE_ANTISYM = store_thm(
  "WLE_ANTISYM",
  ``(x,y) WLE w /\ (y,x) WLE w ==> (x = y)``,
  strip_tac >>
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, linear_order_def, antisym_def]);

val WIN_WLE = store_thm(
  "WIN_WLE",
  ``(x,y) WIN w ==> (x,y) WLE w``,
  rw[strict_def]);

val elsOf_WLE = store_thm(
  "elsOf_WLE",
  ``x ∈ elsOf w <=> (x,x) WLE w``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def, elsOf_def, reflexive_def, in_domain, in_range] >>
  metis_tac[]);

val transitive_strict = store_thm(
  "transitive_strict",
  ``transitive r /\ antisym r ==> transitive (strict r)``,
  simp[transitive_def, strict_def, antisym_def] >> metis_tac[]);

val WIN_TRANS = store_thm(
  "WIN_TRANS",
  ``(x,y) WIN w /\ (y,z) WIN w ==> (x,z) WIN w``,
  `transitive (wellorder_REP w) /\ antisym (wellorder_REP w)`
     by metis_tac [termP_term_REP, wellorder_def, linear_order_def] >>
  metis_tac [transitive_def, transitive_strict]);

val WIN_WF = store_thm(
  "WIN_WF",
  ``wellfounded (\p. p WIN w)``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def] >>
  qsuff_tac `(\p. p WIN w) = strict (wellorder_REP w)` >- simp[] >>
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
  ``r1 ⊆ r2 ⇒ strict r1 ⊆ strict r2``,
  simp[strict_def, SUBSET_DEF, pairTheory.FORALL_PROD]);

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
                 (domain (rrestrict r s) ∪ range (rrestrict r s))``,
  rw[linear_order_def, in_domain, in_range, antisym_rrestrict,
     transitive_rrestrict] >>
  fs[rrestrict_def] >> metis_tac[]);

val reflexive_rrestrict = store_thm(
  "reflexive_rrestrict",
  ``reflexive r (domain r ∪ range r) ==>
    reflexive (rrestrict r s)
              (domain (rrestrict r s) ∪ range (rrestrict r s))``,
  rw[reflexive_def, rrestrict_def, in_domain, in_range] >> metis_tac[]);

val wellorder_rrestrict = store_thm(
  "wellorder_rrestrict",
  ``wellorder (rrestrict (wellorder_REP w) (iseg w x))``,
  `wellorder (wellorder_REP w)` by metis_tac [termP_term_REP] >>
  fs[wellorder_def] >>
  rw[iseg_def, linear_order_rrestrict, reflexive_rrestrict] >>
  match_mp_tac wellfounded_subset >>
  qexists_tac `strict(wellorder_REP w)` >>
  rw[rrestrict_SUBSET, strict_subset]);

val wobound_def = Define`
  wobound x w = wellorder_ABS (rrestrict (wellorder_REP w) (iseg w x))
`;

val WIN_wobound = store_thm(
  "WIN_wobound",
  ``(x,y) WIN wobound z w <=> (x,z) WIN w /\ (y,z) WIN w /\ (x,y) WIN w``,
  rw[wobound_def, wellorder_rrestrict, #repabs_pseudo_id wellorder_results,
     strict_def] >>
  rw[rrestrict_def, iseg_def, strict_def] >> metis_tac []);

val WLE_wobound = store_thm(
  "WLE_wobound",
  ``(x,y) WLE wobound z w <=> (x,z) WIN w /\ (y,z) WIN w /\ (x,y) WLE w``,
  rw[wobound_def, wellorder_rrestrict, #repabs_pseudo_id wellorder_results] >>
  rw[rrestrict_def, iseg_def] >> metis_tac[]);

val localDefine = with_flag (computeLib.auto_import_definitions, false) Define

val wellorder_cases = store_thm(
  "wellorder_cases",
  ``!w. ?s. wellorder s /\ (w = wellorder_ABS s)``,
  rw[Once (#termP_exists wellorder_results)] >>
  simp_tac (srw_ss() ++ DNF_ss)[#absrep_id wellorder_results]);

val WEXTENSION = store_thm(
  "WEXTENSION",
  ``(w1 = w2) <=> !a b. (a,b) WLE w1 <=> (a,b) WLE w2``,
  qspec_then `w1` strip_assume_tac wellorder_cases >>
  qspec_then `w2` strip_assume_tac wellorder_cases >>
  simp[#term_ABS_pseudo11 wellorder_results, EXTENSION, pairTheory.FORALL_PROD,
       #repabs_pseudo_id wellorder_results]);

val wobound2 = store_thm(
  "wobound2",
  ``(a,b) WIN w ==> (wobound a (wobound b w) = wobound a w)``,
  simp[WEXTENSION, WLE_wobound, WIN_wobound] >> metis_tac [WIN_TRANS]);

val wellorder_fromNat = store_thm(
  "wellorder_fromNat",
  ``wellorder { (i,j) | i <= j /\ j < n }``,
  rw[wellorder_def, wellfounded_def, linear_order_def, in_range, in_domain,
     reflexive_def]
  >| [
    qexists_tac `LEAST m. m IN s` >> numLib.LEAST_ELIM_TAC >> rw[strict_def] >>
    metis_tac [DECIDE ``x ≤ y ⇔ (x = y) ∨ x < y``],
    srw_tac[ARITH_ss][transitive_def],
    srw_tac[ARITH_ss][antisym_def],
    decide_tac,
    decide_tac,
    decide_tac,
    decide_tac,
    decide_tac
  ]);

val INJ_preserves_transitive = store_thm(
  "INJ_preserves_transitive",
  ``transitive r ∧ INJ f (domain r ∪ range r) t ⇒
    transitive (IMAGE (f ## f) r)``,
  simp[transitive_def, pairTheory.EXISTS_PROD] >> strip_tac >>
  map_every qx_gen_tac [`x`, `y`, `z`] >>
  simp[GSYM AND_IMP_INTRO] >>
  disch_then (Q.X_CHOOSE_THEN `a` (Q.X_CHOOSE_THEN `b` strip_assume_tac)) >>
  disch_then (Q.X_CHOOSE_THEN `b'` (Q.X_CHOOSE_THEN `c` strip_assume_tac)) >>
  rw[] >> qabbrev_tac `DR = domain r ∪ range r` >>
  `b ∈ DR ∧ b' ∈ DR` by (rw[Abbr`DR`, in_domain, in_range] >> metis_tac[]) >>
  `b' = b` by metis_tac [INJ_DEF] >> rw[] >> metis_tac[]);

val INJ_preserves_antisym = store_thm(
  "INJ_preserves_antisym",
  ``antisym r ∧ INJ f (domain r ∪ range r) t ⇒ antisym (IMAGE (f ## f) r)``,
  simp[antisym_def, pairTheory.EXISTS_PROD] >> strip_tac >>
  map_every qx_gen_tac [`x`, `y`] >> simp[GSYM AND_IMP_INTRO] >>
  disch_then (Q.X_CHOOSE_THEN `a` (Q.X_CHOOSE_THEN `b` strip_assume_tac)) >>
  disch_then (Q.X_CHOOSE_THEN `a'` (Q.X_CHOOSE_THEN `b'` strip_assume_tac)) >>
  rw[] >> qabbrev_tac `DR = domain r ∪ range r` >>
  metis_tac [INJ_DEF, IN_UNION, in_domain, in_range]);


val INJ_preserves_linear_order = store_thm(
  "INJ_preserves_linear_order",
  ``linear_order r (domain r ∪ range r) ∧ INJ f (domain r ∪ range r) t ⇒
    linear_order (IMAGE (f ## f) r) (IMAGE f (domain r ∪ range r))``,
  simp[linear_order_def, pairTheory.EXISTS_PROD] >> rpt strip_tac >| [
    simp[SUBSET_DEF, in_domain, pairTheory.EXISTS_PROD] >> metis_tac[],
    simp[SUBSET_DEF, in_range, pairTheory.EXISTS_PROD] >> metis_tac[],
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
  simp[domain_def, EXTENSION, pairTheory.EXISTS_PROD] >> prove_tac[]);
val range_IMAGE_ff = store_thm(
  "range_IMAGE_ff",
  ``range (IMAGE (f ## g) r) = IMAGE g (range r)``,
  simp[range_def, EXTENSION, pairTheory.EXISTS_PROD] >> prove_tac[]);

val INJ_preserves_wellorder = store_thm(
  "INJ_preserves_wellorder",
  ``wellorder r ∧ INJ f (domain r ∪ range r) t ⇒ wellorder (IMAGE (f ## f) r)``,
  simp[wellorder_def] >> rpt strip_tac >| [
    fs[wellfounded_def, strict_def] >> qx_gen_tac `s` >>
    disch_then (Q.X_CHOOSE_THEN `e` assume_tac) >>
    asm_simp_tac (srw_ss() ++ DNF_ss) [pairTheory.EXISTS_PROD] >>
    Cases_on `s ∩ IMAGE f (domain r ∪ range r) = ∅` >-
      (qexists_tac `e` >> fs[EXTENSION, in_domain, in_range] >> metis_tac[]) >>
    pop_assum mp_tac >> qabbrev_tac `DR = domain r ∪ range r` >>
    asm_simp_tac (srw_ss() ++ DNF_ss)[EXTENSION] >>
    qx_gen_tac `x` >> strip_tac >>
    first_x_assum (qspec_then `{ x | x ∈ DR ∧ f x ∈ s }` mp_tac) >>
    asm_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss) [] >>
    disch_then (Q.X_CHOOSE_THEN `min` strip_assume_tac) >>
    qexists_tac `f min` >> simp[] >> map_every qx_gen_tac [`a`, `b`] >>
    rpt strip_tac >>
    `a ∈ DR ∧ b ∈ DR` by (rw[Abbr`DR`, in_domain, in_range] >> metis_tac[]) >>
    `b = min` by metis_tac [INJ_DEF] >> metis_tac[],
    simp[domain_IMAGE_ff, range_IMAGE_ff] >>
    metis_tac [IMAGE_UNION, INJ_preserves_linear_order],
    fs[reflexive_def, pairTheory.EXISTS_PROD, in_domain, in_range] >>
    metis_tac[]
  ]);

val wellorder_fromNat_SUM = store_thm(
  "wellorder_fromNat_SUM",
  ``wellorder { (INL i, INL j) | i <= j /\ j < n }``,
  qmatch_abbrev_tac `wellorder w` >>
  qabbrev_tac `w0 = { (i,j) | i ≤ j ∧ j < n }` >>
  `w = IMAGE (INL ## INL) w0`
     by simp[EXTENSION, Abbr`w`, Abbr`w0`, pairTheory.EXISTS_PROD] >>
  simp[] >> match_mp_tac (GEN_ALL INJ_preserves_wellorder) >>
  `wellorder w0` by simp[Abbr`w0`, wellorder_fromNat] >>
  simp[INJ_DEF] >>
  qexists_tac `IMAGE INL (domain w0 ∪ range w0)` >>
  simp[]);

val fromNat0_def = Define`
  fromNat0 n = wellorder_ABS { (INL i, INL j) | i <= j /\ j < n }
`

val fromNat0_11 = store_thm(
  "fromNat0_11",
  ``(fromNat0 i = fromNat0 j) <=> (i = j)``,
  rw[fromNat0_def, WEXTENSION, wellorder_fromNat_SUM,
     #repabs_pseudo_id wellorder_results] >>
  simp[Once EQ_IMP_THM] >> strip_tac >>
  spose_not_then assume_tac >>
  `i < j \/ j < i` by DECIDE_TAC >| [
     first_x_assum (qspecl_then [`INL i`, `INL i`] mp_tac),
     first_x_assum (qspecl_then [`INL j`, `INL j`] mp_tac)
  ] >> srw_tac[ARITH_ss][]);

val elsOf_fromNat0 = store_thm(
  "elsOf_fromNat0",
  ``elsOf (fromNat0 n) = IMAGE INL (count n)``,
  simp[fromNat0_def, EXTENSION, elsOf_def, #repabs_pseudo_id wellorder_results,
       wellorder_fromNat_SUM, in_domain, in_range, EQ_IMP_THM] >>
  simp_tac (srw_ss() ++ DNF_ss ++ ARITH_ss) [] >>
  qx_gen_tac `x` >> strip_tac >> disj1_tac >> qexists_tac `x` >> rw[]);

val _ = type_abbrev ("inf", ``:num + 'a``)

val shift1_def = Define`
  shift1 (w : 'a inf wellorder) =
    wellorder_ABS (IMAGE ((SUC ++ I) ## (SUC ++ I)) (wellorder_REP w))
`

val SURJ_IMAGE = store_thm(
  "SURJ_IMAGE",
  ``SURJ f s (IMAGE f s)``,
  rw[SURJ_DEF] >> metis_tac[]);

val EXISTS_SUM = prove(
  ``(?x:'a + 'b. P x) = (?a. P (INL a)) \/ (?b. P (INR b))``,
  metis_tac [sumTheory.sum_CASES]);

val FORALL_SUM =
  EXISTS_SUM |> Q.INST [`P` |-> `\x. ~ Q x`] |> AP_TERM ``(~)``
             |> CONV_RULE (BINOP_CONV (SIMP_CONV bool_ss []))
             |> Q.INST [`Q` |-> `P`]

val wellorder_shift1 = store_thm(
  "wellorder_shift1",
  ``wellorder w ==> wellorder (IMAGE ((SUC ++ I) ## (SUC ++ I)) w)``,
  strip_tac >> match_mp_tac (GEN_ALL INJ_preserves_wellorder) >>
  qabbrev_tac `s0 = domain w ∪ range w` >>
  qexists_tac `IMAGE (SUC ++ I) s0` >>
  simp[INJ_DEF, EXISTS_SUM, FORALL_SUM]);

val ZERO_NOT_SHIFT1 = store_thm(
  "ZERO_NOT_SHIFT1",
  ``INL 0 NOTIN elsOf (shift1 w)``,
  simp[shift1_def, elsOf_def, in_domain, in_range,
       #repabs_pseudo_id wellorder_results, wellorder_shift1,
       #termP_term_REP wellorder_results, FORALL_SUM, pairTheory.FORALL_PROD]);

val ADD1_def = Define`
  ADD1 e w =
    if e IN elsOf w then w
    else
      wellorder_ABS (wellorder_REP w UNION {(x,e) | x IN elsOf w} UNION {(e,e)})
`;

val WLE_WIN = store_thm(
  "WLE_WIN",
  ``(x,y) WLE w ==> (x = y) ∨ (x,y) WIN w``,
  rw[strict_def]);

val wellorder_ADD1 = store_thm(
  "wellorder_ADD1",
  ``e NOTIN elsOf w ==>
    wellorder (wellorder_REP w UNION {(x,e) | x IN elsOf w} UNION {(e,e)})``,
  `wellorder (wellorder_REP w)` by rw [termP_term_REP] >>
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
    `domain (wellorder_REP w UNION {(x,e) | x IN elsOf w} UNION {(e,e)}) =
     e INSERT elsOf w`
       by (rw[EXTENSION, in_domain, in_range, EQ_IMP_THM] >>
           metis_tac [WLE_elsOf]) >>
    `range (wellorder_REP w UNION {(x,e) | x IN elsOf w} UNION {(e,e)}) =
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

val woSUC_def = Define`
  woSUC (w : 'a inf wellorder) = ADD1 (INL 0) (shift1 w)
`;

val elsOf_wobound = store_thm(
  "elsOf_wobound",
  ``elsOf (wobound x w) = { y | (y,x) WIN w }``,
  simp[wobound_def, EXTENSION] >> qx_gen_tac `a` >>
  simp[elsOf_def, wellorder_rrestrict, #repabs_pseudo_id wellorder_results] >>
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
    `y ∈ elsOf w2` by metis_tac [WIN_elsOf] >>
    `g y ∈ elsOf w1` by metis_tac[] >>
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
  `x0 IN elsOf w1 /\ x IN elsOf w1` by metis_tac [WIN_elsOf] >>
  `y0 <> y` by metis_tac [WIN_REFL, wo2wo_11] >>
  rpt (qpat_assum `wo2wo X Y Z = WW` mp_tac) >>
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
            by metis_tac [optionTheory.option_CASES] >> simp[iseg_def] >>
         metis_tac[WIN_elsOf]) >>
  `y0 <> y` by metis_tac [WIN_REFL] >>
  `y0 IN elsOf w2 /\ y IN elsOf w2` by metis_tac [WIN_elsOf] >>
  metis_tac [WIN_TRANS, WIN_REFL, wleast_IN_wo]);

val wo2wo_EQ_NONE_woseg = store_thm(
  "wo2wo_EQ_NONE_woseg",
  ``(wo2wo w1 w2 x = NONE) ==> (elsOf w2 = woseg w1 w2 x)``,
  rw[Once wo2wo_thm, LET_THM] >>
  `?y. y IN elsOf w2 /\ y NOTIN woseg w1 w2 x`
     by metis_tac [IMAGE_wo2wo_SUBSET, SUBSET_DEF, EXTENSION] >>
  strip_tac >> imp_res_tac wleast_EQ_NONE >> metis_tac [SUBSET_DEF]);

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
      metis_tac [wo2wo_IN_w2, optionTheory.THE_DEF],
      metis_tac [wo2wo_11, optionTheory.THE_DEF, WIN_elsOf],
      `elsOf w2 = woseg w1 w2 x0`
        by metis_tac [wo2wo_EQ_NONE_woseg, optionTheory.option_CASES] >>
      asm_simp_tac (srw_ss() ++ DNF_ss) [iseg_def] >>
      metis_tac [optionTheory.option_CASES],
      simp[WIN_wobound] >> metis_tac [optionTheory.THE_DEF, wo2wo_mono]
    ],
    ALL_TAC
  ] >>
  fs[METIS_PROVE []``(!x. ~P x \/ Q x) = (!x. P x ==> Q x)``,
     METIS_PROVE [optionTheory.option_CASES, optionTheory.NOT_SOME_NONE]
                  ``(x <> NONE) <=> ?y. x = SOME y``] >>
  Cases_on `elsOf w2 = { y | ?x. x IN elsOf w1 /\ (wo2wo w1 w2 x = SOME y) }`
  >| [
    qsuff_tac `orderiso w1 w2` >- rw[] >>
    rw[orderiso_def] >> qexists_tac `THE o wo2wo w1 w2` >>
    pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [EXTENSION]) >>
    simp[] >> rpt conj_tac >| [
      metis_tac [optionTheory.THE_DEF],
      metis_tac [wo2wo_11, optionTheory.THE_DEF],
      metis_tac [optionTheory.THE_DEF],
      metis_tac [optionTheory.THE_DEF, wo2wo_mono, WIN_elsOf]
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
  `?y0. y0_opt = SOME y0` by metis_tac [optionTheory.option_CASES] >>
  qunabbrev_tac `y0_opt` >>
  pop_assum (strip_assume_tac o MATCH_MP wleast_IN_wo) >> fs[] >>
  qsuff_tac `orderlt w1 w2` >- rw[] >> simp[orderlt_def] >>
  qexists_tac `y0` >> simp[orderiso_def] >>
  qexists_tac `THE o wo2wo w1 w2` >>
  `!a b. a IN elsOf w1 /\ (wo2wo w1 w2 a = SOME b) ==> (b,y0) WIN w2`
    by (rpt strip_tac >>
        `b <> y0` by metis_tac [] >>
        `~((y0,b) WIN w2)`
           by metis_tac [wo2wo_ONTO, optionTheory.NOT_SOME_NONE] >>
        metis_tac [WIN_trichotomy, wo2wo_IN_w2]) >>
  simp[elsOf_wobound] >> rpt conj_tac >| [
    metis_tac [optionTheory.THE_DEF],
    metis_tac [optionTheory.THE_DEF, wo2wo_11],
    metis_tac [WIN_REFL, WIN_TRANS, WIN_elsOf, optionTheory.THE_DEF],
    simp[WIN_wobound] >> metis_tac [wo2wo_mono, optionTheory.THE_DEF, WIN_elsOf]
  ]);

val wZERO_def = Define`wZERO = wellorder_ABS {}`

val elsOf_wZERO = store_thm(
  "elsOf_wZERO",
  ``elsOf wZERO = {}``,
  simp[wZERO_def, elsOf_def, #repabs_pseudo_id wellorder_results,
       wellorder_EMPTY, EXTENSION, in_domain, in_range]);
val _ = export_rewrites ["elsOf_wZERO"]

val WIN_wZERO = store_thm(
  "WIN_wZERO",
  ``(x,y) WIN wZERO <=> F``,
  simp[wZERO_def, #repabs_pseudo_id wellorder_results, wellorder_EMPTY,
       strict_def]);
val _ = export_rewrites ["WIN_wZERO"]

val WLE_wZERO = store_thm(
  "WLE_wZERO",
  ``(x,y) WLE wZERO <=> F``,
  simp[wZERO_def, #repabs_pseudo_id wellorder_results, wellorder_EMPTY]);
val _ = export_rewrites ["WLE_wZERO"]

val orderiso_wZERO = store_thm(
  "orderiso_wZERO",
  ``orderiso wZERO w <=> (w = wZERO)``,
  simp[orderiso_thm, BIJ_EMPTY, EQ_IMP_THM] >>
  Q.ISPEC_THEN `w` strip_assume_tac wellorder_cases >>
  simp[elsOf_def, EXTENSION, in_range, in_domain, wZERO_def,
       #term_ABS_pseudo11 wellorder_results, wellorder_EMPTY,
       #repabs_pseudo_id wellorder_results,
       pairTheory.FORALL_PROD]);

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
  simp[relationTheory.WF_DEF] >>
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

val islimit_def = Define`
  islimit w = !e. e IN elsOf w ==>
                  ?e'. e' IN elsOf w /\ (e,e') WIN w
`;

val islimit_maximals = store_thm(
  "islimit_maximals",
  ``islimit w <=> (maximal_elements (elsOf w) (wellorder_REP w) = {})``,
  rw[islimit_def, maximal_elements_def, EXTENSION] >>
  rw[METIS_PROVE [] ``(!x. ~P x \/ Q x) = (!x. P x ==> Q x)``] >>
  metis_tac [WIN_REFL, WLE_WIN, WIN_WLE]);

val islimit_wZERO = store_thm(
  "islimit_wZERO",
  ``islimit wZERO``,
  rw[islimit_def, wZERO_def]);

val islimit_iso = store_thm(
  "islimit_iso",
  ``orderiso w1 w2 ==> (islimit w1 <=> islimit w2)``,
  rw[orderiso_thm, islimit_def, EQ_IMP_THM] >| [
    `?a. a IN elsOf w1 /\ (f a = e)` by metis_tac [BIJ_IFF_INV] >>
    `?b. b IN elsOf w1 /\ (a,b) WIN w1` by metis_tac [] >>
    `f b IN elsOf w2` by metis_tac [BIJ_IFF_INV] >>
    metis_tac[],
    `f e IN elsOf w2` by metis_tac [BIJ_IFF_INV] >>
    `?u. u IN elsOf w2 /\ (f e,u) WIN w2` by metis_tac [] >>
    `?e'. e' IN elsOf w1 /\ (u = f e')` by metis_tac [BIJ_IFF_INV] >>
    metis_tac [WIN_trichotomy, WIN_REFL, WIN_TRANS]
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

val canon_wellorder_def = Define`
  canon_wellorder w = !x. x IN elsOf w ==> (x = @y. ~((y,x) WIN w))
`;

val orderiso_unique = store_thm(
  "orderiso_unique",
  ``BIJ f1 (elsOf w1) (elsOf w2) /\ BIJ f2 (elsOf w1) (elsOf w2) /\
    (!x y. (x,y) WIN w1 ==> (f1 x, f1 y) WIN w2) /\
    (!x y. (x,y) WIN w1 ==> (f2 x, f2 y) WIN w2) ==>
    !x. x IN elsOf w1 ==> (f1 x = f2 x)``,
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  `wellorder (wellorder_REP w1)` by rw[termP_term_REP] >>
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
  MATCH_MP relationTheory.WF_INDUCTION_THM WIN_WF2
           |> SIMP_RULE (srw_ss()) []
           |> Q.SPEC `\x. x IN elsOf w ==> P x`
           |> SIMP_RULE (srw_ss()) []
           |> Q.GEN `w` |> Q.GEN `P`)

(*
val canonicals_unique = store_thm(
  "canonicals_unique",
  ``canon_wellorder w1 /\ canon_wellorder w2 /\ orderiso w1 w2 ==> (w1 = w2)``,
  simp[canon_wellorder_def, orderiso_thm] >> rpt strip_tac >>
  qsuff_tac `!x. x IN elsOf w1 ==> (f x = x)`
    >- (strip_tac >>
        qsuff_tac `wellorder_REP w1 = wellorder_REP w2`
           >- rw [#term_REP_11 wellorder_results] >>
        simp[EXTENSION, pairTheory.FORALL_PROD] >>
        `!x y. (x,y) WIN w1 ==> ((f x, f y) WIN w2 = (x,y) WIN w2)`
           by metis_tac [WIN_elsOf] >>
        fs[] >> simp[EQ_IMP_THM] >>
        map_every qx_gen_tac [`a`, `b`] >> strip_tac >>
        `?a0 b0. a0 IN elsOf w1 /\ (f a0 = a) /\ b0 IN elsOf w1 /\ (f b0 = b)`
           by metis_tac [BIJ_IFF_INV, WLE_elsOf] >>
        ntac 2 (qpat_assum `f XX = YY` mp_tac) >> simp[] >> rw[] >>
        metis_tac [WIN_trichotomy, WIN_TRANS, WIN_REFL]) >>
  ho_match_mp_tac wo_INDUCTION >> rpt strip_tac >>
  `f x IN elsOf w2` by metis_tac [BIJ_IFF_INV] >>
  qsuff_tac `(@y. ~((y,x) WIN w1)) = (@y. ~((y, f x) WIN w2))`
    >- (res_tac >> ntac 2 (pop_assum (SUBST1_TAC o SYM)) >> rw[]) >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> EQ_TAC >-
    metis_tac [WIN_elsOf] >>
  strip_tac >>
  `?x0. x0 IN elsOf w1 /\ (f x0 = y)` by metis_tac [BIJ_IFF_INV, WIN_elsOf] >>
  `(x0,x) WIN w1` by metis_tac [WIN_trichotomy, WIN_TRANS, WIN_REFL] >>
  metis_tac[])
*)

val elsOf_shift1 = store_thm(
  "elsOf_shift1",
  ``elsOf (shift1 w) = IMAGE (SUC ++ I) (elsOf w)``,
  simp[shift1_def, elsOf_def, EXTENSION, #repabs_pseudo_id wellorder_results,
       wellorder_shift1, #termP_term_REP wellorder_results, in_domain,
       in_range, EXISTS_SUM, pairTheory.EXISTS_PROD] >>
  simp_tac (srw_ss() ++ DNF_ss)[] >> metis_tac[]);

val FORALL_NUM = store_thm(
  "FORALL_NUM",
  ``(!n. P n) <=> P 0 /\ !n. P (SUC n)``,
  metis_tac [arithmeticTheory.num_CASES])

val WIN_shift1 = store_thm(
  "WIN_shift1",
  ``!x y.
      (x,y) WIN shift1 w <=>
      x <> INL 0 ∧ y <> INL 0 ∧ ((PRE ++ I) x, (PRE ++ I) y) WIN w``,
  simp[shift1_def, #repabs_pseudo_id wellorder_results, wellorder_shift1,
       #termP_term_REP wellorder_results, strict_def, pairTheory.EXISTS_PROD,
       EXISTS_SUM, FORALL_SUM] >>
  simp_tac (srw_ss() ++ DNF_ss) [] >> rpt conj_tac >| [
    simp[Once FORALL_NUM] >> qx_gen_tac `a` >> simp[Once FORALL_NUM],
    simp[Once FORALL_NUM],
    simp[Once FORALL_NUM]
  ]);

val PRE_SUC_PP = prove(
  ``(PRE ++ I) ((SUC ++ I) x) = x``,
  Cases_on `x` >> rw[]);

val SUC_PP11 = prove(
  ``((SUC ++ I) x1 = (SUC ++ I) x2) = (x1 = x2)``,
  Cases_on `x1` >> Cases_on `x2` >> rw[]);

val SUC_PP_NEQ0 = prove(
  ``(SUC ++ I) x <> INL 0``,
  Cases_on `x` >> rw[])

val shift1_orderiso = store_thm(
  "shift1_orderiso",
  ``orderiso w (shift1 w)``,
  rw[orderiso_thm] >> qexists_tac `SUC ++ I` >>
  simp[elsOf_shift1, BIJ_DEF, INJ_DEF, SURJ_DEF, SUC_PP11, WIN_shift1,
       PRE_SUC_PP, SUC_PP_NEQ0] >> metis_tac[])

val elsOf_ADD1 = store_thm(
  "elsOf_ADD1",
  ``elsOf (ADD1 e w) = e INSERT elsOf w``,
  simp[EXTENSION, ADD1_def, Once elsOf_def, SimpLHS] >>
  qx_gen_tac `x` >>
  rw[#repabs_pseudo_id wellorder_results, wellorder_ADD1] >| [
    fs[elsOf_def] >> metis_tac[],
    simp[in_domain, in_range] >> metis_tac [WLE_elsOf]
  ]);

val strict_UNION = store_thm(
  "strict_UNION",
  ``strict (r1 ∪ r2) = strict r1 ∪ strict r2``,
  simp[EXTENSION, pairTheory.FORALL_PROD, strict_def] >> metis_tac[]);

val WIN_ADD1 = store_thm(
  "WIN_ADD1",
  ``(x,y) WIN ADD1 e w <=>
      e NOTIN elsOf w /\ x IN elsOf w /\ (y = e) \/
      (x,y) WIN w``,
  rw[#repabs_pseudo_id wellorder_results, wellorder_ADD1, ADD1_def,
     strict_def] >> metis_tac[]);

val elsOf_woSUC = store_thm(
  "elsOf_woSUC",
  ``elsOf (woSUC w) = INL 0 INSERT IMAGE (SUC ++ I) (elsOf w)``,
  simp[woSUC_def, elsOf_ADD1, elsOf_shift1]);

val WIN_woSUC = save_thm(
  "WIN_woSUC",
  ``(x,y) WIN woSUC w``
     |> SIMP_CONV (srw_ss()) [woSUC_def, WIN_ADD1, ZERO_NOT_SHIFT1]
     |> SIMP_RULE (srw_ss()) [elsOf_shift1, WIN_shift1, EXISTS_SUM]);

val SUC_PP_EQ_INL = prove(
  ``!x. ((SUC ++ I) x = INL y) <=> ?n. (x = INL n) /\ (y = SUC n)``,
  simp[FORALL_SUM]);

val SUC_PP_EQ_INR = prove(
  ``!x. ((SUC ++ I) x = INR y) <=> (x = INR y)``,
  simp[FORALL_SUM]);

val woSUC_orderiso = store_thm(
  "woSUC_orderiso",
  ``orderiso w1 w2 ⇒ orderiso (woSUC w1) (woSUC w2)``,
  simp[orderiso_def, elsOf_woSUC, WIN_woSUC] >>
  disch_then (Q.X_CHOOSE_THEN `f` strip_assume_tac) >>
  qexists_tac `
    λx. if x = INL 0 then INL 0 else (SUC ++ I) (f ((PRE ++ I) x))
  ` >>
  rw[] >> rw[PRE_SUC_PP, SUC_PP_NEQ0, SUC_PP11, SUC_PP_EQ_INL,
             SUC_PP_EQ_INR] >>
  simp[EXISTS_SUM, SUC_PP_NEQ0, RIGHT_AND_OVER_OR, EXISTS_OR_THM, SUC_PP11] >|[
    simp_tac (srw_ss() ++ COND_elim_ss ++ CONJ_ss) [SUC_PP_NEQ0, SUC_PP11] >>
    Cases_on `x` >> asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
    metis_tac [sumTheory.sum_CASES],
    metis_tac [sumTheory.sum_CASES],
    metis_tac [sumTheory.sum_CASES]
  ]);

val fromNat0_11 = store_thm(
  "fromNat0_11",
  ``(fromNat0 n = fromNat0 m) <=> (n = m)``,
  simp[EQ_IMP_THM] >> disch_then (mp_tac o Q.AP_TERM `elsOf`) >>
  simp[elsOf_fromNat0, EXTENSION] >> spose_not_then strip_assume_tac >>
  `n < m ∨ m < n` by decide_tac >| [
     first_x_assum (qspec_then `INL n` mp_tac) >> simp[],
     first_x_assum (qspec_then `INL m` mp_tac) >> simp[]
  ]);

val WIN_fromNat0 = prove(
  ``(x,y) WIN fromNat0 n <=>
     ?m p. m < p /\ p < n /\ (x = INL m) /\ (y = INL p)``,
  rw[fromNat0_def, wellorder_fromNat_SUM, #repabs_pseudo_id wellorder_results,
     strict_def] >>
  map_every Cases_on [`x`, `y`] >> simp[]);

val fromNat0_orderiso11 = store_thm(
  "fromNat0_orderiso11",
  ``orderiso (fromNat0 n) (fromNat0 m) <=> (n = m)``,
  simp[EQ_IMP_THM] >> conj_tac >-
    (simp[orderiso_thm, elsOf_fromNat0] >>
     disch_then (Q.X_CHOOSE_THEN `f` strip_assume_tac) >>
     `(CARD (IMAGE INL (count n)) = n) ∧ (CARD (IMAGE INL (count m)) = m)`
        by rw[CARD_INJ_IMAGE, IMAGE_FINITE] >>
     metis_tac [IMAGE_FINITE, FINITE_COUNT, FINITE_BIJ_CARD_EQ]) >>
  rw[orderiso_thm] >>
  qexists_tac `\x. case x of INL n => INL n | INR a => ARB` >>
  rw[WIN_fromNat0, elsOf_fromNat0] >> rw[] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >> fs[] >>
  asm_simp_tac (srw_ss() ++ DNF_ss) []);

val woSUC_fromNat0 = store_thm(
  "woSUC_fromNat0",
  ``orderiso (woSUC (fromNat0 n)) (fromNat0 (n + 1))``,
  simp[orderiso_def, elsOf_woSUC, elsOf_fromNat0, WIN_woSUC, WIN_fromNat0] >>
  qexists_tac `λx. case x of INL 0 => INL n
                           | INL (SUC m) => INL m` >>
  simp_tac (srw_ss() ++ DNF_ss ++ ARITH_ss)[EXISTS_SUM, FORALL_SUM] >>
  Cases >> simp[] >> Cases >> simp[]);

val fromNat0_wZERO = store_thm(
  "fromNat0_wZERO",
  ``orderiso (fromNat0 0:'a inf wellorder) (wZERO:'b wellorder)``,
  spose_not_then strip_assume_tac >>
  `orderlt (wZERO:'b wellorder) (fromNat0 0:'a inf wellorder)`
    by prove_tac [orderlt_trichotomy, LT_wZERO] >>
  fs[orderlt_def, elsOf_fromNat0])

val woSUC_fromNat00 = store_thm(
  "woSUC_fromNat00",
  ``~orderiso (woSUC w) (fromNat0 0)``,
  rw[orderiso_thm, elsOf_fromNat0, BIJ_EMPTY] >> DISJ1_TAC >>
  disch_then (mp_tac o Q.AP_TERM `elsOf`) >>
  simp[elsOf_woSUC]);

(* perform quotient, creating a type of "pre-ordinals".

   These should all that's necessary, but I can't see how to define the limit
   operation on these.  Instead, the "real" type of ordinals will be the
   downward-closed sets of pre-ordinals.
*)
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
     ordlt_ZERO, ord_islimit_ZERO, ord_finite_ZERO, fromNat_11,
     ord_SUC_fromNat, ord_SUC_ZERO, fromNat_ZERO] =
    quotient.define_quotient_types_full
    {
     types = [{name = "ordinal", equiv = alphaise orderiso_equiv}],
     defs = map mk_def
       [("ordlt", ``orderlt : 'a inf wellorder -> 'a inf wellorder -> bool``),
        ("ord_islimit", ``islimit : 'a inf wellorder -> bool``),
        ("ord_ZERO", ``wZERO : 'a inf wellorder``),
        ("ord_finite", ``finite : 'a inf wellorder -> bool``),
        ("ord_SUC", ``woSUC : 'a inf wellorder -> 'a inf wellorder``),
        ("fromNat", ``fromNat0 : num -> 'a inf wellorder``)],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     respects = [alphaise islimit_iso, alphaise orderlt_orderiso,
                 alphaise finite_iso,
                 INST_TYPE [beta |-> alpha] woSUC_orderiso],
     poly_preserves = [],
     poly_respects = [],
     old_thms = [alphaise orderlt_REFL, alphaise orderlt_TRANS,
                 alphaise (REWRITE_RULE [relationTheory.WF_DEF] orderlt_WF),
                 alphaise orderlt_trichotomy, alphaise LT_wZERO,
                 alphaise islimit_wZERO, alphaise finite_wZERO,
                 INST_TYPE [beta |-> alpha] fromNat0_orderiso11,
                 INST_TYPE [beta |-> alpha] woSUC_fromNat0,
                 INST_TYPE [beta |-> alpha] woSUC_fromNat00,
                 INST_TYPE [beta |-> ``:'a inf``] fromNat0_wZERO
                 ]}

val _ = save_thm ("ordlt_REFL", ordlt_REFL)
val _ = save_thm ("ordlt_TRANS", ordlt_TRANS)
val ordlt_WF = save_thm (
  "ordlt_WF",
  REWRITE_RULE [GSYM relationTheory.WF_DEF] ordlt_WF0)
val _ = save_thm ("ord_ZERO", ordlt_ZERO)
val _ = save_thm ("ord_islimit_ZERO", ord_islimit_ZERO)
val _ = save_thm ("ord_finite_ZERO", ord_finite_ZERO)
val _ = save_thm ("fromNat_11", fromNat_11)
val _ = save_thm ("ord_SUC_fromNat", ord_SUC_fromNat)

val _ = overload_on ("mkOrdinal", ``ordinal_ABS``)

val allOrds_def = Define`
  allOrds = wellorder_ABS { (x,y) | (x = y) \/ ordlt x y }
`;

val wellorder_allOrds = store_thm(
  "wellorder_allOrds",
  ``wellorder { (x,y) | (x = y) \/ ordlt x y }``,
  simp[wellorder_def, strict_def, wellfounded_WF, relationTheory.WF_DEF] >>
  rpt conj_tac >| [
    simp_tac (srw_ss() ++ CONJ_ss)
             [REWRITE_RULE[SPECIFICATION] GSPECIFICATION,
              pairTheory.EXISTS_PROD] >>
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
  simp[allOrds_def, #repabs_pseudo_id wellorder_results, wellorder_allOrds,
       strict_def] >> metis_tac [ordlt_REFL]);

val elsOf_allOrds = store_thm(
  "elsOf_allOrds",
  ``elsOf allOrds = univ(:'a ordinal)``,
  rw[elsOf_def, EXTENSION, in_domain, in_range, allOrds_def,
     #repabs_pseudo_id wellorder_results, wellorder_allOrds] >>
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

val preds_11 = store_thm(
  "preds_11",
  ``(preds w1 = preds w2) = (w1 = w2)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `ordlt w1 w2 \/ ordlt w2 w1` by metis_tac [ordlt_trichotomy] >>
  qpat_assum `x = y` mp_tac >> rw[EXTENSION, preds_def] >>
  metis_tac [ordlt_REFL]);

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
    qspec_then `\w. w NOTIN x` mp_tac ordlt_WF0 >> simp[IN_preds] >>
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

val elsOf_cardeq_iso = store_thm(
  "elsOf_cardeq_iso",
  ``elsOf (wo:'b wellorder) ≼ univ(:'a) ⇒ ∃wo':'a wellorder. orderiso wo wo'``,
  simp[cardleq_def] >> disch_then (Q.X_CHOOSE_THEN `f` mp_tac) >>
  simp[elsOf_def] >> strip_tac >>
  `wellorder (wellorder_REP wo)` by simp[#termP_term_REP wellorder_results] >>
  qexists_tac `wellorder_ABS (IMAGE (f ## f) (wellorder_REP wo))` >>
  simp[orderiso_thm] >>
  `wellorder (IMAGE (f ## f) (wellorder_REP wo))`
    by imp_res_tac INJ_preserves_wellorder >>
  qexists_tac `f` >>
  simp[#repabs_pseudo_id wellorder_results, elsOf_def, domain_IMAGE_ff,
       range_IMAGE_ff] >>
  simp_tac bool_ss [GSYM IMAGE_UNION] >>
  qabbrev_tac `
    els = domain (wellorder_REP wo) UNION range (wellorder_REP wo)` >>
  simp[BIJ_DEF, SURJ_IMAGE] >>
  simp[strict_def, pairTheory.EXISTS_PROD] >>
  fs[INJ_DEF] >> conj_tac >- metis_tac [] >>
  map_every qx_gen_tac [`x`, `y`] >> strip_tac >>
  `x ∈ elsOf wo ∧ y ∈ elsOf wo` by metis_tac [WLE_elsOf] >>
  fs[elsOf_def] >> metis_tac[IN_UNION]);

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


val _ = export_theory()
