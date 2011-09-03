open HolKernel boolLib bossLib Parse stringTheory arithmeticTheory
     finite_mapTheory pred_setTheory bagTheory pairTheory relationTheory
     prim_recTheory apply_piTheory ntermTheory nsubstTheory nwalkTheory
     nwalkstarTheory nomsetTheory listTheory dis_setTheory ramanaLib
     monadsyntax ntermLib

val _ = new_theory "nunifDef"
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 }

val nvR_update = Q.prove(
  `v NOTIN FDOM s /\ x <> v ==> (nvR (s |+ (v,t)) y x <=> nvR s y x)`,
  SRW_TAC [][nvR_def] THEN
  Cases_on `x IN FDOM s` THEN
  SRW_TAC [][FLOOKUP_DEF,FAPPLY_FUPDATE_THM]);

val TC_nvR_update = Q.prove(
`!y x. (nvR (s |+ (v,t)))^+ y x ==> v NOTIN FDOM s ==>
    (nvR s)^+ y x \/ ?u. (nvR s)^* v x /\ u IN nvars t /\ (nvR s)^* y u`,
HO_MATCH_MP_TAC TC_STRONG_INDUCT THEN CONJ_TAC THENL [
  MAP_EVERY Q.X_GEN_TAC [`y`,`x`] THEN SRW_TAC [][] THEN
  Cases_on `x = v` THENL [
    DISJ2_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [nvR_def,FLOOKUP_DEF] THEN
    Q.EXISTS_TAC `y` THEN SRW_TAC [][],
    METIS_TAC [nvR_update,TC_RULES]
  ],
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
    THEN1 METIS_TAC [TC_RULES] THEN
  DISJ2_TAC THEN Q.EXISTS_TAC `u` THEN
  METIS_TAC [TC_RTC,RTC_TRANSITIVE,transitive_def]
]);

val nwfs_extend = Q.store_thm(
  "nwfs_extend",
  `nwfs s /\ v NOTIN FDOM s /\ v NOTIN nvars (nwalkstar s t) ==>
   nwfs (s |+ (v, t))`,
  SRW_TAC [boolSimps.CONJ_ss][noc_eq_nvars_nwalkstar, nwfs_no_cycles] THEN
  STRIP_TAC THEN
  `!u. u IN nvars t ==> ~(nvR s)^+ v u`
     by METIS_TAC [TC_nvR_nvars_nwalkstar, nwfs_no_cycles] THEN
  `?u. (nvR s)^* v v' /\ u IN nvars t /\ (nvR s)^* v' u`
     by METIS_TAC [TC_nvR_update] THEN
  FULL_SIMP_TAC (srw_ss()) [RTC_CASES_TC] THEN
  METIS_TAC [NOT_FDOM_nwalkstar,nwfs_no_cycles,TC_RULES]
);

val _ = type_abbrev("fe",``:(string # num) set``);
val _ = type_abbrev("pkg", ``:('a nsubst # fe)``);

val term_fcs_def = tDefine "term_fcs" `
  term_fcs a t =
  case t
  of Nom b -> if a = b then NONE else SOME {}
  || Sus p v -> SOME {(perm_of (REVERSE p) a, v)}
  || Tie b tt -> if a = b then SOME {} else term_fcs a tt
  || nPair t1 t2 -> OPTION_MAP2 $UNION (term_fcs a t1) (term_fcs a t2)
  || nConst _ -> SOME {}`
(WF_REL_TAC `measure (npair_count o SND)` THEN SRW_TAC [ARITH_ss][]);

val _ = overload_on("monad_bind",``OPTION_BIND``);

val term_fcs_monadic_thm = Q.store_thm("term_fcs_monadic_thm",
` term_fcs a t =
  case t
  of Nom b -> if a = b then NONE else SOME {}
  || Sus p v -> SOME {(perm_of (REVERSE p) a, v)}
  || Tie b tt -> if a = b then SOME {} else term_fcs a tt
  || nPair t1 t2 -> do fe1 <- term_fcs a t1; fe2 <- term_fcs a t2; SOME (fe1 ∪ fe2) od
  || nConst _ -> SOME {}`,
Cases_on `t` THEN SRW_TAC [][Once term_fcs_def] THEN
Q.MATCH_ABBREV_TAC `OPTION_MAP2 $UNION x1 x2 = y` THEN
Cases_on `x1` THEN SRW_TAC [][] THEN
Cases_on `x2` THEN SRW_TAC [][]);

val fcs_acc = Define`
  fcs_acc s (a,v) ac = OPTION_MAP2 $UNION ac (term_fcs a (nwalk* s (Sus [] v)))`;

val unify_eq_vars_def = Define`
  unify_eq_vars ds v (s,fe) =
  do fex <- ITSET (fcs_acc s) (IMAGE (λa. (a,v)) ds) (SOME {});
     SOME (s,fe UNION fex)
  od`;

val add_bdg_def = RWDefine`
  add_bdg pi v t0 (s,fe) =
  let t = (apply_pi (REVERSE pi) t0) in
    if noc s t v then NONE else SOME ((s|+(v,t)),fe)`

val ntunify_defn_q = `
  ntunify (s,fe) t1 t2 =
  if nwfs s then
    case (nwalk s t1, nwalk s t2)
    of (Nom a1, Nom a2) -> if a1 = a2 then SOME (s,fe) else NONE
    || (Sus pi1 v1, Sus pi2 v2) ->
         if v1 = v2
         then unify_eq_vars (dis_set pi1 pi2) v1 (s,fe)
         else add_bdg pi1 v1 (Sus pi2 v2) (s,fe)
    || (Sus pi1 v1, t2) -> add_bdg pi1 v1 t2 (s,fe)
    || (t1, Sus pi2 v2) -> add_bdg pi2 v2 t1 (s,fe)
    || (Tie a1 t1, Tie a2 t2) ->
         if a1 = a2 then ntunify (s,fe) t1 t2
         else do fcs <- term_fcs a1 (nwalk* s t2);
                 ntunify (s, fe UNION fcs) t1 (apply_pi [(a1,a2)] t2)
              od
    || (nPair t1a t1d, nPair t2a t2d) ->
         do (sx,fex) <- ntunify (s,fe) t1a t2a;
            ntunify (sx,fex) t1d t2d
         od
    || (nConst c1, nConst c2) -> if c1 = c2 then SOME (s,fe) else NONE
    || _ -> NONE
  else ARB`

val ntunify_defn = Hol_defn "ntunify" ntunify_defn_q

val _ = store_term_thm("ntunify_defn", TermWithCase ntunify_defn_q)

val SOME ntunify_aux_defn = Defn.aux_defn ntunify_defn

val sysvars_def = Define`
  sysvars s (t1:'a nterm) (t2:'a nterm) =
    nvars t1 UNION nvars t2 UNION
    FDOM s UNION BIGUNION (FRANGE (nvars o_f s))`

val FINITE_sysvars = RWstore_thm(
"FINITE_sysvars",
`FINITE (sysvars s t1 t2)`,
SRW_TAC [][sysvars_def] THEN
FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF] THEN
Cases_on `s ' x'` THEN SRW_TAC [][o_f_DEF])

val sysvars_comm = Q.store_thm(
"sysvars_comm",
`sysvars s t1 t2 = sysvars s t2 t1`,
SRW_TAC [][sysvars_def] THEN
METIS_TAC [UNION_COMM])

val sysvars_apply_pi = Q.store_thm(
"sysvars_apply_pi",
`(sysvars s t1 t2 = sysvars s (apply_pi pi t1) t2)`,
SRW_TAC [][sysvars_def])

val uR_def = Define`
uR = \((sx,fex:fe),c,c2) ((s,fe:fe),t,t2).
   nwfs sx
/\ s SUBMAP sx
/\ sysvars sx c c2 SUBSET sysvars s t t2
/\ measure (npair_count o (nwalkstar sx)) c t`

val WF_uR = Q.store_thm(
"WF_uR",
`WF nunifDef$uR`,
SRW_TAC [][WF_IFF_WELLFOUNDED,wellfounded_def,uR_def,UNCURRY] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
Q.ABBREV_TAC `f1 = \n. FST (FST (f n))` THEN
`!n. FST (FST (f n)) = f1 n` by SRW_TAC [][Abbr`f1`] THEN
Q.ABBREV_TAC `f2 = \n. FST (SND (f n))` THEN
`!n. FST (SND (f n)) = f2 n` by SRW_TAC [][Abbr`f2`] THEN
Q.ABBREV_TAC `f3 = \n. SND (SND (f n))` THEN
`!n. SND (SND (f n)) = f3 n` by SRW_TAC [][Abbr`f3`] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
REPEAT (Q.PAT_ASSUM `Abbrev B` (K ALL_TAC)) THEN
`!m n. m < n ==>
     sysvars (f1 n) (f2 n) (f3 n) ⊆ sysvars (f1 m) (f2 m) (f3 m)`
  by (Induct THENL
      [Induct THEN1 SRW_TAC [][] THEN
       Cases_on `n` THEN METIS_TAC [SUBSET_TRANS,LESS_0],
       Induct THEN1 SRW_TAC [][] THEN STRIP_TAC THEN
       `SUC m < n \/ (SUC m = n)` by (SRW_TAC [ARITH_ss] [LESS_EQ]) THEN
       METIS_TAC [SUBSET_TRANS]
      ]) THEN
`!m n. m < n ==> f1 m SUBMAP f1 n`
  by (Induct THENL
      [Induct THEN1 SRW_TAC [][] THEN
       Cases_on `n` THEN METIS_TAC [SUBMAP_TRANS,LESS_0],
       Induct THEN1 SRW_TAC [][] THEN STRIP_TAC THEN
       `SUC m < n \/ (SUC m = n)` by (SRW_TAC [ARITH_ss] [LESS_EQ]) THEN
       METIS_TAC [SUBMAP_TRANS]
      ]) THEN
`?m.!n. m < n ==>
    (sysvars (f1 n) (f2 n) (f3 n) = sysvars (f1 m) (f2 m) (f3 m))`
  by (SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [SKOLEM_THM] THEN
      `!m. m < f' m /\
           sysvars (f1 (f' m)) (f2 (f' m)) (f3 (f' m))
           PSUBSET
           sysvars (f1 m) (f2 m) (f3 m)`
        by (METIS_TAC [PSUBSET_DEF]) THEN
      `!m.measure CARD
            (sysvars (f1 (f' m)) (f2 (f' m)) (f3 (f' m)))
            (sysvars (f1 m) (f2 m) (f3 m))`
        by (METIS_TAC [measure_thm,FINITE_sysvars,CARD_PSUBSET])
        THEN
      `WF (measure (CARD:((num -> bool) -> num)))` by SRW_TAC [][] THEN
      FULL_SIMP_TAC bool_ss [WF_IFF_WELLFOUNDED,wellfounded_def] THEN
      POP_ASSUM (Q.SPEC_THEN
                   `\n. let t = FUNPOW f' n 0
                        in sysvars (f1 t) (f2 t) (f3 t)`
                 MP_TAC) THEN
      FULL_SIMP_TAC (srw_ss()) [LET_THM,FUNPOW_SUC]) THEN
`?m. !n. m < n ==> (f1 m = f1 n)`
by (Q.ISPECL_THEN
    [`f1`, `\n. sysvars (f1 n) (f2 n) (f3 n) DIFF (FDOM(f1 n))`, `m`]
    (MATCH_MP_TAC o GSYM o SIMP_RULE (srw_ss()) [])
    commonUnifTheory.extension_chain THEN
    SRW_TAC [][DISJOINT_DEF] THENL [
      SRW_TAC [][EXTENSION] THEN METIS_TAC [],
      METIS_TAC [UNION_DIFF,sysvars_def,SUBSET_UNION,SUBSET_TRANS]
    ]) THEN
Q.ABBREV_TAC `z = MAX m m'` THEN
`!n. z < n ==> (f1 n = f1 m')`
  by (METIS_TAC [MAX_LT]) THEN
`!n. z < n ==> npair_count (nwalkstar (f1 m') (f2 (SUC n))) <
               npair_count (nwalkstar (f1 m') (f2 n))`
  by (METIS_TAC [LESS_SUC]) THEN
`WF (measure (npair_count o (nwalkstar (f1 m'))))`
  by SRW_TAC [][] THEN
FULL_SIMP_TAC bool_ss [WF_IFF_WELLFOUNDED,wellfounded_def] THEN
POP_ASSUM (Q.SPEC_THEN `\n. f2(z+n+1)` MP_TAC) THEN
SRW_TAC [][ADD_CLAUSES] THEN
SRW_TAC [ARITH_ss][])

val nwalkstar_subpair = Q.store_thm(
"nwalkstar_subpair",
`nwfs s /\ (nwalk s t1 = nPair t1a t1d) ==>
  npair_count (nwalkstar s t1a) < npair_count (nwalkstar s t1) /\
  npair_count (nwalkstar s t1d) < npair_count (nwalkstar s t1)`,
SRW_TAC [][nwalk_def] THEN
Cases_on `t1` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [])

val nwalkstar_subtie = Q.store_thm(
"nwalkstar_subtie",
`nwfs s /\ (nwalk s t1 = Tie a1 t1a) ==>
  npair_count (nwalkstar s t1a) < npair_count (nwalkstar s t1)`,
SRW_TAC [][nwalk_def] THEN
Cases_on `t1` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [])

val lemp = Q.prove(
`(nwfs s ∧ (nvwalk s p v = nPair ta td) ⇒ v IN FDOM s) ∧
 ∀ta td. nvars ta SUBSET nvars (nPair ta td) ∧
         nvars td SUBSET nvars (nPair ta td)`,
SRW_TAC [][] THEN METIS_TAC [NOT_FDOM_nvwalk,ntermeq_thm])

val sysvars_SUBSET_pairs = Q.store_thm(
"sysvars_SUBSET_pairs",
`nwfs s /\
 (nwalk s t1 = nPair t1a t1d) /\
 (nwalk s t2 = nPair t2a t2d) ==>
 sysvars s t1a t2a SUBSET sysvars s t1 t2 /\
 sysvars s t1d t2d SUBSET sysvars s t1 t2`,
SRW_TAC [][nwalk_def,sysvars_def] THEN
Cases_on `t1` THEN Cases_on `t2` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
METIS_TAC [nvars_nvwalk_SUBSET_FRANGE, lemp, SUBSET_TRANS,SUBSET_UNION])

val lemt = Q.prove(
`(nwfs s ∧ (nvwalk s p v = Tie ta td) ⇒ v IN FDOM s) ∧
 ∀ta td. nvars td SUBSET nvars (Tie ta td)`,
SRW_TAC [][] THEN METIS_TAC [NOT_FDOM_nvwalk,ntermeq_thm])

val sysvars_SUBSET_ties = Q.store_thm(
"sysvars_SUBSET_ties",
`nwfs s ∧
 (nwalk s t1 = Tie a1 t1a) ∧
 (nwalk s t2 = Tie a2 t2a) ⇒
 sysvars s t1a t2a SUBSET sysvars s t1 t2`,
SRW_TAC [][nwalk_def,sysvars_def] THEN
Cases_on `t1` THEN Cases_on `t2` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
METIS_TAC [nvars_nvwalk_SUBSET_FRANGE,lemt,SUBSET_TRANS,SUBSET_UNION]);

val tca_thm = Q.store_thm(
"tca_thm",
`nwfs (FST p) /\
 (nwalk (FST p) t1 = nPair t1a t1d) /\
 (nwalk (FST p) t2 = nPair t2a t2d) ==>
 uR (p,t1a,t2a) (p,t1,t2)`,
Cases_on `p` THEN
SRW_TAC [][uR_def,SUBMAP_REFL] THEN1
METIS_TAC [sysvars_SUBSET_pairs] THEN
METIS_TAC [nwalkstar_subpair]);

val tctie_thm = Q.store_thm(
"tctie_thm",
`nwfs (FST p) ∧
 (nwalk (FST p) t1 = Tie a1 t1a) ∧
 (nwalk (FST p) t2 = Tie a2 t2a) ⇒
  uR ((FST p,fex),t1a,apply_pi pi t2a) (p,t1,t2)`,
Cases_on `p` THEN
SRW_TAC [][uR_def,SUBMAP_REFL] THEN1
METIS_TAC [sysvars_SUBSET_ties,sysvars_apply_pi,sysvars_comm] THEN
METIS_TAC [nwalkstar_subtie]);

val aux_def =
SIMP_RULE std_ss []
(MATCH_MP
 (MATCH_MP WFREC_COROLLARY
  (Q.SPEC`nunifDef$uR`(definition"ntunify_tupled_AUX_def")))
 WF_uR);

val uR_ind = WF_INDUCTION_THM |> Q.ISPEC `nunifDef$uR` |> SIMP_RULE (srw_ss()) [WF_uR]
|> Q.SPEC `\(a,b,c).P (FST a) (SND a) b c`
|> SIMP_RULE std_ss [FORALL_PROD] |> Q.GEN`P`;

val FRANGE_DOMSUB_SUBSET = Q.store_thm(
"FRANGE_DOMSUB_SUBSET",
`BIGUNION (FRANGE (f \\ x)) SUBSET BIGUNION (FRANGE f)`,
SRW_TAC [][BIGUNION,SUBSET_DEF,FRANGE_DEF] THEN
METIS_TAC [DOMSUB_FAPPLY_THM]);

val met1 =
[nvars_nvwalk_SUBSET_FRANGE,lemp,lemt,
SUBSET_TRANS,SUBSET_UNION,FRANGE_DOMSUB_SUBSET,o_f_DOMSUB];

val met2 =
[nvars_apply_pi,FRANGE_FLOOKUP,o_f_FRANGE,
 SUBSET_UNION,SUBSET_BIGUNION_I,SUBSET_TRANS];

val lem1 = Q.prove(
`nwfs s ∧ (nvwalk s pv v = Sus py y) ∧
 ((nvwalk s px x = nPair (Sus pv v) t2) ∨
  (nvwalk s px x = nPair t2 (Sus pv v))) ⇒
 ∃vs. y IN vs ∧ vs IN FRANGE (nvars o_f s)`,
SRW_TAC [][] THENL [
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN
  MP_TAC (Q.SPECL [`x`,`nvwalk s px x`,`s`,`px`] (GEN_ALL nvwalk_FDOM)) THEN
  SRW_TAC [][] THENL [
    `v IN nvars (nPair (Sus pv v) t2)` by SRW_TAC [][] THEN
    METIS_TAC [FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi],
    `y IN nvars (Sus py y)` by SRW_TAC [][] THEN
    METIS_TAC [FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi]
  ],
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN
  MP_TAC (Q.SPECL [`x`,`nvwalk s px x`,`s`,`px`] (GEN_ALL nvwalk_FDOM)) THEN
  SRW_TAC [][] THENL [
    `v IN nvars (nPair t2 (Sus pv v))` by SRW_TAC [][] THEN
    METIS_TAC [FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi],
    `y IN nvars (Sus py y)` by SRW_TAC [][] THEN
    METIS_TAC [FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi]
  ]
]);

val lem2 = Q.prove(
`nwfs s ∧ ((nvwalk s px x = nPair (Sus pv v) t2) ∨
          (nvwalk s px x = nPair t2 (Sus pv v))) ⇒
 nvars (nvwalk s pv v) SUBSET BIGUNION (FRANGE (nvars o_f s))`,
Cases_on `nvwalk s pv v` THEN SRW_TAC [][] THENL [
  METIS_TAC [lem1],
  METIS_TAC [lem1],
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `nvars C SUBSET (nvars (Tie s' C))` by SRW_TAC [][] THEN METIS_TAC met1,
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `nvars C SUBSET (nvars (Tie s' C))` by SRW_TAC [][] THEN METIS_TAC met1,
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `nvars C SUBSET (nvars (nPair C C0))` by SRW_TAC [][] THEN METIS_TAC met1,
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `nvars C SUBSET (nvars (nPair C C0))` by SRW_TAC [][] THEN METIS_TAC met1,
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `nvars C SUBSET (nvars (nPair C C0))` by SRW_TAC [][] THEN METIS_TAC met1,
  MP_TAC (Q.SPECL [`v`,`nvwalk s pv v`,`s`,`pv`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `nvars C0 SUBSET (nvars (nPair C C0))` by SRW_TAC [][] THEN METIS_TAC met1
]);

val lem3 = Q.prove(
`nwfs s ∧ (nvwalk s px x = nPair t1 t2) ∧
 (vs SUBSET (nvars t1) ∨
  vs SUBSET (nvars t2)) ⇒
 vs SUBSET BIGUNION (FRANGE (nvars o_f s))`,
SRW_TAC [][] THENL [
  MP_TAC (Q.SPECL [`x`,`nvwalk s px x`,`s`,`px`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  METIS_TAC met1,
  MP_TAC (Q.SPECL [`x`,`nvwalk s px x`,`s`,`px`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  METIS_TAC met1
]);

fun tac1 t1a t2a =
Cases_on t1a THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
SRW_TAC [][sysvars_def] THENL [
  METIS_TAC met1, METIS_TAC met1, METIS_TAC [lem1], METIS_TAC met1,
  Cases_on t2a THEN FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THENL [
    METIS_TAC (lem2::met1),
    Q.MATCH_ABBREV_TAC  `X SUBSET Y` THEN
    `X SUBSET BIGUNION (FRANGE (nvars o_f s))` by METIS_TAC (lem3::met1) THEN
    METIS_TAC met1,
    Q.MATCH_ABBREV_TAC `X1 SUBSET Y1 ∧ X2 SUBSET Y2` THEN
    `X1 SUBSET BIGUNION (FRANGE (nvars o_f s)) ∧
     X2 SUBSET BIGUNION (FRANGE (nvars o_f s))` by
     METIS_TAC (lem3::met1) THEN
     METIS_TAC met1
  ],
  METIS_TAC met1
];

val lem4 = Q.prove(
`nwfs s ⇒ nvars (nvwalk s px x) SUBSET {x} ∨ nvars (nvwalk s px x) SUBSET BIGUNION (FRANGE (nvars o_f s))`,
MP_TAC (Q.SPECL [`x`,`nvwalk s px x`,`s`,`px`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC ([FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi]@met2));

fun tac2 t =
Cases_on t THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
SRW_TAC [][sysvars_def] THENL [
  METIS_TAC met1, METIS_TAC met1, METIS_TAC [lem1], METIS_TAC met1,
  Cases_on `C` THEN FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THENL [
    METIS_TAC (lem4::met1),
    METIS_TAC met1,
    METIS_TAC met1
  ],
  METIS_TAC met1
];

fun tac3 t =
Cases_on `C` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
SRW_TAC [][sysvars_def] THENL [
  `nvars t1d SUBSET (nvars (nPair t1a t1d))` by SRW_TAC [][] THEN
   METIS_TAC (lem4::met1),
   METIS_TAC met1,
   MP_TAC (Q.SPECL [`n'`,`nvwalk s l' n'`,`s`,`l'`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
   `v IN nvars (Sus p v)` by SRW_TAC [][] THEN
   METIS_TAC [FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi],
   METIS_TAC met1,
   Cases_on t THEN FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THENL [
     METIS_TAC (lem2::met1),
    Q.MATCH_ABBREV_TAC  `X SUBSET Y` THEN
    `X SUBSET BIGUNION (FRANGE (nvars o_f s))` by METIS_TAC (lem3::met1) THEN
    METIS_TAC met1,
    Q.MATCH_ABBREV_TAC `X1 SUBSET Y1 ∧ X2 SUBSET Y2` THEN
    `X1 SUBSET BIGUNION (FRANGE (nvars o_f s)) ∧
     X2 SUBSET BIGUNION (FRANGE (nvars o_f s))` by
     METIS_TAC (lem3::met1) THEN
     METIS_TAC met1
  ],
  METIS_TAC met1
];

fun tac5 t1 t2 =
Cases_on t1 THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
SRW_TAC [][sysvars_def] THENL [
  METIS_TAC met1, METIS_TAC met1,
  MP_TAC (Q.SPECL [`n`,`nvwalk s l n`,`s`,`l`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
  `v IN nvars (Sus p v)` by SRW_TAC [][] THEN
  METIS_TAC [FRANGE_FLOOKUP,o_f_FRANGE,nvars_apply_pi],
  METIS_TAC met1,
  Cases_on t2 THEN FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THENL [
    METIS_TAC (lem4::met1),
    METIS_TAC met1,
    METIS_TAC met1
  ],
  METIS_TAC met1
];

val sysvars_SUBSET_FUPDATE_pairs = Q.store_thm(
"sysvars_SUBSET_FUPDATE_pairs",
`nwfs (s |+ (v,apply_pi pi t)) /\ v NOTIN FDOM s /\
 (nwalk s t1 = nPair t1a t1d) /\
 (nwalk s t2 = nPair t2a t2d) /\
 (((∃p.nwalk s t1a = Sus p v) /\ (nwalk s t2a = t)) \/
  ((∃p.nwalk s t2a = Sus p v) /\ (nwalk s t1a = t))) ==>
 sysvars (s |+ (v,apply_pi pi t)) t1d t2d SUBSET sysvars s t1 t2`,
SIMP_TAC (srw_ss()) [nwalk_def,GSYM AND_IMP_INTRO] THEN
NTAC 2 STRIP_TAC THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
Q.MATCH_ABBREV_TAC `X1 ⇒ X2 ⇒ Y` THEN
MAP_EVERY Q.UNABBREV_TAC [`X1`,`X2`] THEN
Cases_on `t1` THEN Cases_on `t2` THEN
SRW_TAC [][nvwalk_case_thms] THEN
Q.UNABBREV_TAC `Y` THENL [
  STRIP_TAC THENL [ tac1 `t1a` `t2a`, tac1 `t2a` `t1a`],
  Q.MATCH_ABBREV_TAC `X ⇒ Y SUBSET sysvars s Z (nPair C C0)` THEN
  TRY (Q.RM_ABBREV_TAC `C`) THEN UNABBREV_ALL_TAC THEN
  STRIP_TAC THENL [ tac2 `t1a`, tac3 `t1a`],
  Q.MATCH_ABBREV_TAC `X ⇒ Y SUBSET sysvars s (nPair C C0) Z` THEN
  TRY (Q.RM_ABBREV_TAC `C`) THEN UNABBREV_ALL_TAC THEN
  STRIP_TAC THENL [ tac3 `t2a`, tac2 `t2a`],
  Q.MATCH_ABBREV_TAC `X ⇒ Y SUBSET sysvars s (nPair C1 D1) (nPair C2 D2)` THEN
  MAP_EVERY Q.RM_ABBREV_TAC [`C1`,`C2`] THEN UNABBREV_ALL_TAC THEN
  STRIP_TAC THENL [ tac5 `C1` `C2`, tac5 `C2` `C1`]
]);

val nwalkstar_subpair_FUPDATE = Q.store_thm(
"nwalkstar_subpair_FUPDATE",
`nwfs s /\ v NOTIN FDOM s /\ v NOTIN nvars (nwalkstar s t) /\
 (nwalk s t1 = nPair t1a t1d) ==>
 npair_count (nwalkstar (s |+ (v,apply_pi pi t)) t1d) <
 npair_count (nwalkstar (s |+ (v,apply_pi pi t)) t1)`,
SRW_TAC [][] THEN
`nwfs (s |+ (v,apply_pi pi t))` by METIS_TAC [nwfs_extend,nvars_nwalkstar_ignores_pi] THEN
`s SUBMAP (s |+ (v,apply_pi pi t))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
`nwalk (s |+ (v,apply_pi pi t)) t1 = nPair t1a t1d`
  by (Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      (Q.MATCH_ABBREV_TAC `nvwalk sx pn n = nPair t1a t1d` THEN
       Q_TAC SUFF_TAC `nvwalk s pn n = nvwalk sx pn n` THEN1 SRW_TAC [][] THEN
       MATCH_MP_TAC (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (UNDISCH nvwalk_SUBMAP)) THEN
       SRW_TAC [][Abbr`sx`])) THEN
Q.PAT_ASSUM `nwfs (s|+x)` ASSUME_TAC THEN
Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [nwalk_def,nvwalk_case_thms] THEN
SRW_TAC [ARITH_ss][nwalkstar_thm]
)

val uR_subpair_FUPDATE = Q.prove(
`nwfs s /\ v NOTIN FDOM s /\ v NOTIN nvars (nwalkstar s t) /\
 (nwalk s t1 = nPair t1a t1d) /\
 (nwalk s t2 = nPair t2a t2d) /\
 (((∃l. nwalk s t1a = Sus l v) /\ (nwalk s t2a = t)) \/
  ((∃l. nwalk s t2a = Sus l v) /\ (nwalk s t1a = t))) ==>
 uR ((s |+ (v,apply_pi pi t),fe), t1d, t2d) ((s,fe),t1,t2)`,
STRIP_TAC THEN
`nwfs (s |+ (v,apply_pi pi t))` by METIS_TAC [nwfs_extend,nvars_nwalkstar_ignores_pi] THEN
`s SUBMAP (s|+(v,apply_pi pi t))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
(SRW_TAC [][uR_def] THEN1
 METIS_TAC [sysvars_SUBSET_FUPDATE_pairs] THEN
 METIS_TAC [nwalkstar_subpair_FUPDATE])
)

val uR_subpair = Q.prove(
`nwfs s /\
 (nwalk s t1 = nPair t1a t1d) /\
 (nwalk s t2 = nPair t2a t2d) ==>
  uR ((s,fe),t1a,t2a) ((s,fe),t1,t2) /\
  uR ((s,fe),t1d,t2d) ((s,fe),t1,t2)`,
REPEAT STRIP_TAC THEN
SRW_TAC [][uR_def,SUBMAP_REFL] THEN
METIS_TAC [sysvars_SUBSET_pairs,nwalkstar_subpair]
)

val uR_subtie = Q.prove(
`nwfs s ∧
 (nwalk s t1 = Tie a1 t1a) ∧
 (nwalk s t2 = Tie a2 t2a) ⇒
 uR ((s,fe),t1a,t2a) ((s,fe),t1,t2)`,
SRW_TAC [][uR_def,SUBMAP_REFL] THEN
METIS_TAC [sysvars_SUBSET_ties,nwalkstar_subtie])

val uP_def = Define`
uP sx s t1 t2 = nwfs sx /\ s SUBMAP sx /\
  FDOM sx UNION BIGUNION (FRANGE (nvars o_f sx)) SUBSET sysvars s t1 t2`

val lem5 = Q.prove(
`nwfs s ∧ (nvwalk s l n = Sus p v ) ⇒
 (v = n) ∨ (∃vs. v IN vs ∧ vs IN FRANGE (nvars o_f s))`,
MP_TAC (Q.SPECL [`n`,`nvwalk s l n`,`s`,`l`] (GEN_ALL nvwalk_FDOM)) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
DISJ2_TAC THEN Q.EXISTS_TAC `nvars (Sus p v)` THEN
CONJ_TAC THEN1 SRW_TAC [][] THEN
METIS_TAC [o_f_FRANGE,nvars_apply_pi,FRANGE_FLOOKUP])

val uP_subterm_FUPDATE = Q.prove(
`nwfs s /\ v NOTIN FDOM s /\ v NOTIN nvars (nwalkstar s t) /\
 (((∃p. nwalk s t1 = Sus p v) /\ (nwalk s t2 = t)) \/
  ((∃p. nwalk s t2 = Sus p v) /\ (nwalk s t1 = t))) ==>
 uP (s |+ (v,apply_pi pi t)) s t1 t2`,
STRIP_TAC THEN
`nwfs (s |+ (v,apply_pi pi t))` by METIS_TAC [nwfs_extend,nvars_nwalkstar_ignores_pi] THEN
`s SUBMAP (s|+(v,apply_pi pi t))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
Q.MATCH_ASSUM_RENAME_TAC `nwalk s tt = Sus p v` [] THEN
Q.PAT_ASSUM `nwalk s tt = Sus p v`  MP_TAC THEN
Cases_on `tt` THEN SRW_TAC [][nwalk_def] THENL [
  Cases_on `nwalk s t2` THEN Cases_on `t2`,
  Cases_on `nwalk s t1` THEN Cases_on `t1` ] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [nwalk_def,nvwalk_case_thms] THEN
ASM_SIMP_TAC (srw_ss()) [uP_def,sysvars_def] THEN
METIS_TAC (lem5::met1))

val uR_ignores_fe = Q.store_thm(
"uR_ignores_fe",
`uR ((s1,fe1),x1,y1) ((s2,fe2),x2,y2) ⇒
 uR ((s1,fe3),x1,y1) ((s2,fe4),x2,y2)`,
SRW_TAC [][uR_def])

val npair_count_nwalkstar_ignores_pi = Q.store_thm(
"npair_count_nwalkstar_ignores_pi",
`nwfs s ⇒ !t pi. npair_count (nwalk* s t) = npair_count (nwalk* s (apply_pi pi t))`,
STRIP_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
STRIP_TAC THEN REVERSE (Cases_on `t`) THEN FULL_SIMP_TAC (psrw_ss()) [] THEN1
(SRW_TAC [][] THEN REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `pi` MP_TAC)) THEN
 SRW_TAC [ARITH_ss][]) THEN
Cases_on `nvwalk s l n` THEN FULL_SIMP_TAC (psrw_ss()) [Sus_case1] THEN
REPEAT STRIP_TAC THEN
(nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
(nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`pi++l`,`n`] MP_TAC) THEN SRW_TAC [][] THEN
Cases_on `nvwalk s [] n` THEN FULL_SIMP_TAC (srw_ss()) [Sus_case1] THEN
REPEAT( FIRST_X_ASSUM (Q.SPEC_THEN `pi` MP_TAC)) THEN
SRW_TAC [][apply_pi_decompose])

val uR_ignores_pi = Q.store_thm(
"uR_ignores_pi",
`uR ((s1,fe1),x1,y1) ((s2,fe2),x2,y2) ⇒
 uR ((s1,fe1),apply_pi px1 x1,apply_pi py1 y1) ((s2,fe2),apply_pi px2 x2,apply_pi py2 y2)`,
SRW_TAC [][uR_def] THENL [
  METIS_TAC [sysvars_apply_pi,sysvars_comm],
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [npair_count_nwalkstar_ignores_pi]
])

val uP_ignores_pi = Q.store_thm(
"uP_ignores_pi",
`uP s1 s2 x y ⇒
 uP s1 s2 (apply_pi px1 x) (apply_pi py2 y)`,
SRW_TAC [][uP_def] THEN
METIS_TAC [sysvars_apply_pi,sysvars_comm])

val uR_IMP_uP = Q.store_thm(
"uR_IMP_uP",
`uR ((sx,fex),c1,c2) ((s,fe),t1,t2) ==> uP sx s t1 t2`,
SRW_TAC [][uR_def,uP_def,sysvars_def])

val nwalkstar_nwalk_SUBMAP = Q.store_thm(
"nwalkstar_nwalk_SUBMAP",
`s SUBMAP sx /\ nwfs sx ==>
  (nwalk* sx t = nwalk* sx (nwalk s t))`,
METIS_TAC [nwalkstar_SUBMAP,nwalkstar_nwalk,nwfs_SUBMAP])

val uP_IMP_subtie_uR = Q.store_thm(
"uP_IMP_subtie_uR",
`nwfs s ∧
 (nwalk s t1 = Tie a1 t1a) ∧
 (nwalk s t2 = Tie a2 t2a) ∧
 uP sx s t1a t2a ⇒
 uR ((sx,fex),t1a,t2a) ((s,fe),t1,t2)`,
SRW_TAC [][] THEN
`sysvars s t1a t2a SUBSET sysvars s t1 t2`
by METIS_TAC [sysvars_SUBSET_ties] THEN
FULL_SIMP_TAC (srw_ss()) [uR_def,uP_def] THEN
`FDOM sx SUBSET sysvars s t1 t2 ∧
 BIGUNION (FRANGE (nvars o_f sx)) SUBSET sysvars s t1 t2`
by METIS_TAC [SUBSET_TRANS] THEN
SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [sysvars_def] THEN
SRW_TAC [][measure_thm] THEN
IMP_RES_TAC nwalkstar_nwalk_SUBMAP THEN
FIRST_X_ASSUM (Q.SPEC_THEN `t1` MP_TAC) THEN
SRW_TAC [][])

val uP_IMP_subpair_uR = Q.store_thm(
"uP_IMP_subpair_uR",
`nwfs s /\
 (nwalk s t1 = nPair t1a t1d) /\
 (nwalk s t2 = nPair t2a t2d) /\
 (uP sx s t1a t2a \/ uP sx s t1d t2d) ==>
 uR ((sx,fex),t1d,t2d) ((s,fe),t1,t2)`,
SRW_TAC [][] THEN (
`sysvars s t1a t2a SUBSET sysvars s t1 t2 /\
 sysvars s t1d t2d SUBSET sysvars s t1 t2`
  by METIS_TAC [sysvars_SUBSET_pairs] THEN
FULL_SIMP_TAC (srw_ss()) [uR_def,uP_def] THEN
`FDOM sx SUBSET sysvars s t1 t2 /\
 BIGUNION (FRANGE (nvars o_f sx)) SUBSET sysvars s t1 t2`
 by METIS_TAC [SUBSET_TRANS] THEN
SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [sysvars_def] THEN
SRW_TAC [][] THEN
IMP_RES_TAC nwalkstar_nwalk_SUBMAP THEN
FIRST_X_ASSUM (Q.SPEC_THEN `t1` MP_TAC) THEN
SRW_TAC [ARITH_ss][]))

val unify_eq_vars_preserves_s = Q.store_thm(
"unify_eq_vars_preserves_s",
`(unify_eq_vars x y (s,fe) = SOME (s',fe')) ⇒ (s = s')`,
SRW_TAC [][unify_eq_vars_def])

val aux_uP = Q.prove(
`!s fe t1 t2 sx fex.
   nwfs s /\ (ntunify_tupled_aux uR ((s,fe),t1,t2) = SOME (sx,fex)) ==>
     uP sx s t1 t2`,
HO_MATCH_MP_TAC uR_ind THEN
REPEAT (GEN_TAC ORELSE (DISCH_THEN STRIP_ASSUME_TAC)) THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC (srw_ss()) [aux_def,LET_THM] THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2`
THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
  SRW_TAC [][uP_def,SUBMAP_REFL,sysvars_def] THEN
  METIS_TAC [SUBSET_UNION,SUBSET_TRANS],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`Nom s'`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN METIS_TAC [nwalk_to_var],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`Nom s'`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN METIS_TAC [nwalk_to_var],
  SRW_TAC [][] THENL [
    IMP_RES_TAC unify_eq_vars_preserves_s THEN
    SRW_TAC [][uP_def,sysvars_def,SUBMAP_REFL] THEN
    METIS_TAC [SUBSET_UNION,SUBSET_TRANS],
    MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`Sus l' n'`] uP_subterm_FUPDATE)) THEN
    SRW_TAC [][] THENL [
      METIS_TAC [nwalk_to_var],
      Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
      Cases_on `t2` THEN
      FULL_SIMP_TAC (srw_ss()) [nwalk_def] THEN
      IMP_RES_TAC nvwalk_to_var THEN
      SRW_TAC [][NOT_FDOM_nvwalk],
      SELECT_ELIM_TAC THEN SRW_TAC [][permeq_sym]
    ]
  ],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`Tie s' C`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN1 METIS_TAC [nwalk_to_var] THEN
  METIS_TAC [noc_eq_nvars_nwalkstar,IN_DEF,nvars_nwalkstar_ignores_pi],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`nPair C C0`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN1 METIS_TAC [nwalk_to_var] THEN
  METIS_TAC [noc_eq_nvars_nwalkstar,IN_DEF,nvars_nwalkstar_ignores_pi],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`nConst s'`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN METIS_TAC [nwalk_to_var],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`Tie s' C`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN1 METIS_TAC [nwalk_to_var] THEN
  METIS_TAC [noc_eq_nvars_nwalkstar,IN_DEF,nvars_nwalkstar_ignores_pi],
  Q.MATCH_ABBREV_TAC `((if P then RESTRICT f R X ((s,fe),D,D') else Y) = Z) ==>
                      Z2` THEN
  MAP_EVERY Q.RM_ABBREV_TAC [`D`, `D'`] THEN
  UNABBREV_ALL_TAC THEN
  SRW_TAC [][RESTRICT_LEMMA,uR_subtie] THENL [
    METIS_TAC [uR_subtie,uP_IMP_subtie_uR,uR_IMP_uP],
    `∀fex. uR ((s,fex),D,apply_pi [(s',s'')] D') ((s,fe),t1,t2)`
    by METIS_TAC [uR_ignores_fe, uR_ignores_pi, apply_pi_nil, uR_subtie] THEN
    Cases_on `term_fcs s' (nwalk* s D')` THEN
    FULL_SIMP_TAC (srw_ss()) [RESTRICT_LEMMA] THEN
    `uP sx s D (apply_pi [(s',s'')] D')` by METIS_TAC [] THEN
    `uP sx s D D'` by METIS_TAC [uP_ignores_pi,apply_pi_decompose,apply_pi_inverse] THEN
    MATCH_MP_TAC (GEN_ALL uR_IMP_uP) THEN
    METIS_TAC [uP_IMP_subtie_uR]
  ],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`nPair C C0`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN1 METIS_TAC [nwalk_to_var] THEN
  METIS_TAC [noc_eq_nvars_nwalkstar,IN_DEF,nvars_nwalkstar_ignores_pi],
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = nPair D1a D1b` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = nPair D2a D2b` [] THEN
  `uR ((s,fe),D1a,D2a) ((s,fe),t1,t2)` by METIS_TAC [uR_subpair] THEN
  SRW_TAC [][RESTRICT_LEMMA] THEN
  Cases_on `x` THEN
  `uP q s D1a D2a` by METIS_TAC [] THEN
  FULL_SIMP_TAC (srw_ss()) [UNCURRY] THEN
  `uR ((q,r),D1b,D2b) ((s,fe),t1,t2)` by METIS_TAC [uP_IMP_subpair_uR] THEN
  FULL_SIMP_TAC (srw_ss()) [RESTRICT_LEMMA,UNCURRY] THEN
  `uP sx q D1b D2b` by METIS_TAC [uP_def] THEN
  FULL_SIMP_TAC (srw_ss()) [uP_def,uR_def] THEN
  METIS_TAC [SUBSET_TRANS,SUBMAP_TRANS],
  SRW_TAC [][] THEN
  MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.INST[`t`|->`nConst s'`] uP_subterm_FUPDATE)) THEN
  SRW_TAC [][] THEN METIS_TAC [nwalk_to_var],
  SRW_TAC [][uP_def,sysvars_def,SUBMAP_REFL] THEN
  METIS_TAC [SUBSET_TRANS,SUBSET_UNION]
])

val nvars_nwalk = Q.store_thm(
"nvars_nwalk",
`nwfs s ∧ (nwalk s t1 = t2) ⇒
 (nvars t2 SUBSET nvars t1) ∨
 (nvars t2 SUBSET BIGUNION (FRANGE (nvars o_f s)))`,
SRW_TAC [][] THEN
Cases_on `t1` THEN SRW_TAC [][] THEN
METIS_TAC [lem4])

val lem = Q.prove(
`∀s t1 t2 t3. s SUBSET t1 UNION t2 UNION t3 ∧ t1 SUBSET t4 ∧ t2 SUBSET t4 ∧ t3 SUBSET t4 ⇒ s SUBSET t4`,
SRW_TAC [][] THEN METIS_TAC [UNION_SUBSET,SUBSET_TRANS])

val sysvars_pairtie = Q.store_thm(
"sysvars_pairtie",
`nwfs sx ∧ s SUBMAP sx ∧
 (nwalk s t1 = nPair t1a t1d) ∧
 (nwalk s t2 = nPair t2a t2d) ∧
 (nwalk s t1a = Tie a1 c1) ∧
 (nwalk s t2a = Tie a2 c2) ∧
 sysvars sx c1 c2 SUBSET sysvars s t1a t2a ⇒
 sysvars sx t1d t2d SUBSET sysvars s t1 t2`,
STRIP_TAC THEN IMP_RES_TAC nwfs_SUBMAP THEN
SRW_TAC [][sysvars_def] THENL [
  Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC (lem4::met1),
  Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC (lem4::met1),
  `sysvars s t1a t2a SUBSET sysvars s t1 t2`
  by METIS_TAC[ sysvars_SUBSET_pairs] THEN
  FULL_SIMP_TAC (srw_ss()) [sysvars_def] THEN
  MATCH_MP_TAC lem THEN
  MAP_EVERY Q.EXISTS_TAC [`nvars t1a`,`nvars t2a`,`FDOM s UNION BIGUNION (FRANGE (nvars o_f s))`] THEN
  SRW_TAC [][] THEN METIS_TAC [UNION_ASSOC],
  `sysvars s t1a t2a SUBSET sysvars s t1 t2`
  by METIS_TAC[ sysvars_SUBSET_pairs] THEN
  FULL_SIMP_TAC (srw_ss()) [sysvars_def] THEN
  MATCH_MP_TAC lem THEN
  MAP_EVERY Q.EXISTS_TAC [`nvars t1a`,`nvars t2a`,`FDOM s UNION BIGUNION (FRANGE (nvars o_f s))`] THEN
  SRW_TAC [][] THEN METIS_TAC [UNION_ASSOC]
])

val tcd_thm = Q.store_thm(
"tcd_thm",
`nwfs (FST p) /\
 (nwalk (FST p) t1 = nPair t1a t1d) /\
 (nwalk (FST p) t2 = nPair t2a t2d) /\
 (ntunify_tupled_aux uR (p,t1a,t2a) = SOME px) ==>
 uR (px,t1d,t2d) (p,t1,t2)`,
MAP_EVERY Cases_on [`p`,`px`] THEN SRW_TAC [][] THEN
METIS_TAC [aux_uP, uP_IMP_subpair_uR])

val [tctie_thm,tcd_thm,tca_thm] = map ((SIMP_RULE (srw_ss()) [FORALL_PROD]) o GEN_ALL) [tctie_thm,tcd_thm,tca_thm]

val (ntunify_def,ntunify_ind) = Defn.tprove (
ntunify_defn,
WF_REL_TAC `uR` THEN
SRW_TAC [][WF_uR] THENL [
  SRW_TAC [][tctie_thm],
  METIS_TAC [apply_pi_nil,tctie_thm],
  SRW_TAC [][tcd_thm],
  SRW_TAC [][tca_thm]
])

val aux_eqn =
hd(Defn.eqns_of ntunify_aux_defn) |>
Q.INST[`R`|->`uR`] |>
PROVE_HYP WF_uR |>
(fn th => PROVE_HYP (prove(hd(hyp th),SRW_TAC[][tctie_thm])) th) |>
(fn th => PROVE_HYP (prove(hd(hyp th),SRW_TAC[][] THEN METIS_TAC[apply_pi_nil,tctie_thm,PAIR])) th) |>
(fn th => PROVE_HYP (prove(hd(hyp th),SRW_TAC[][tcd_thm])) th) |>
(fn th => PROVE_HYP (prove(hd(hyp th),SRW_TAC[][tca_thm])) th);

val aux_eq_ntunify = Q.store_thm(
"aux_eq_ntunify",
`!s fe t1 t2. ntunify_tupled_aux uR ((s,fe),t1,t2) = ntunify (s,fe) t1 t2`,
HO_MATCH_MP_TAC ntunify_ind THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][Once aux_eqn] THEN
SRW_TAC [][Once ntunify_def,SimpRHS] THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
SRW_TAC [][] THENL [
  Q.MATCH_ASSUM_RENAME_TAC `nwalk q t2 = Tie a2 c2` [] THEN
  Cases_on `term_fcs s' (nwalk* q c2)` THEN SRW_TAC [][],
  Q.MATCH_ASSUM_RENAME_TAC `nwalk q t1 = nPair t1a t1d` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk q t2 = nPair t2a t2d` [] THEN
  Cases_on `ntunify (q,fe) t1a t2a` THEN SRW_TAC [][UNCURRY]
]);

val nunify_exists = prove(
``∃nunify.∀s fe t1 t2. nwfs s ⇒ (nunify (s,fe) t1 t2 =
    case (nwalk s t1, nwalk s t2)
    of (Nom a1, Nom a2) -> if a1 = a2 then SOME (s,fe) else NONE
    || (Sus pi1 v1, Sus pi2 v2) ->
         if v1 = v2
         then unify_eq_vars (dis_set pi1 pi2) v1 (s,fe)
         else add_bdg pi1 v1 (Sus pi2 v2) (s,fe)
    || (Sus pi1 v1, t2) -> add_bdg pi1 v1 t2 (s,fe)
    || (t1, Sus pi2 v2) -> add_bdg pi2 v2 t1 (s,fe)
    || (Tie a1 t1, Tie a2 t2) ->
         if a1 = a2 then nunify (s,fe) t1 t2
         else do fcs <- term_fcs a1 (nwalk* s t2);
                 nunify (s, fe UNION fcs) t1 (apply_pi [(a1,a2)] t2)
              od
    || (nPair t1a t1d, nPair t2a t2d) ->
         do (sx,fex) <- nunify (s,fe) t1a t2a;
            nunify (sx,fex) t1d t2d
         od
    || (nConst c1, nConst c2) -> if c1 = c2 then SOME (s,fe) else NONE
    || _ -> NONE)``,
Q.EXISTS_TAC `ntunify` THEN
SRW_TAC [][Once ntunify_def,SimpLHS] THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
SRW_TAC [][]);

val nunify_def = new_specification("nunify_def",["nunify"],nunify_exists);

val nunify_eq_ntunify = Q.store_thm(
"nunify_eq_ntunify",
`!s fe t1 t2. nwfs (FST (s,fe)) ==> (nunify (s,fe) t1 t2 = ntunify (s,fe) t1 t2)`,
HO_MATCH_MP_TAC ntunify_ind THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][Once ntunify_def,SimpRHS] THEN
SRW_TAC [][Once nunify_def,SimpLHS] THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
SRW_TAC [][] THENL [
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = Tie a2 c2` [] THEN
  Cases_on `term_fcs s' (nwalk* s c2)` THEN SRW_TAC [][],
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = nPair t1a t1d` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = nPair t2a t2d` [] THEN
  Cases_on `ntunify (s,fe) t1a t2a` THEN SRW_TAC [][] THEN
  `nwfs (FST x)` by METIS_TAC [aux_eq_ntunify,uP_def,aux_uP,PAIR] THEN
  SRW_TAC [][UNCURRY]
]);

val _ = Q.store_thm(
"nunify_uP",
`nwfs s /\ (nunify (s,fe) t1 t2 = SOME (sx,fex)) ==>
   uP sx s t1 t2`,
METIS_TAC [FST,nunify_eq_ntunify,aux_eq_ntunify,aux_uP]);

val _ = save_thm ("nunify_ind",
ntunify_ind |>
SIMP_RULE (srw_ss()) [GSYM nunify_eq_ntunify,GSYM AND_IMP_INTRO] |>
Q.SPEC `UNCURRY P` |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO] |> Q.GEN `P`);

val verify_fcs = Define`
  verify_fcs fcs s = ITSET (fcs_acc s) fcs (SOME {})`;

val nomunify_def = Define`
  nomunify (s,fe) t1 t2 =
  do (sx,feu) <- nunify (s,fe) t1 t2;
     fex <- verify_fcs feu sx;
     SOME (sx,fex)
  od`;

val _ = export_theory ();
