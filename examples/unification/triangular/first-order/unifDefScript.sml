open HolKernel boolLib bossLib ramanaLib Parse stringTheory arithmeticTheory finite_mapTheory pred_setTheory bagTheory relationTheory prim_recTheory pairTheory termTheory monadsyntax substTheory walkTheory walkstarTheory

val _ = new_theory "unifDef";
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 };
val _ = overload_on("monad_bind",``OPTION_BIND``);

val vR_update = Q.prove(
  `v NOTIN FDOM s /\ x <> v ==> (vR (s |+ (v,t)) y x <=> vR s y x)`,
  SRW_TAC [][vR_def] THEN
  Cases_on `x IN FDOM s` THEN
  SRW_TAC [][FLOOKUP_DEF,FAPPLY_FUPDATE_THM]);

val TC_vR_update = Q.prove(
`!y x. (vR (s |+ (v,t)))^+ y x ==> v NOTIN FDOM s ==>
    (vR s)^+ y x \/ ?u. (vR s)^* v x /\ u IN vars t /\ (vR s)^* y u`,
HO_MATCH_MP_TAC TC_STRONG_INDUCT THEN
CONJ_TAC
THENL [
  MAP_EVERY Q.X_GEN_TAC [`y`,`x`] THEN SRW_TAC [][] THEN
  Cases_on `x = v` THENL [
    DISJ2_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
    Q.EXISTS_TAC `y` THEN SRW_TAC [] [],
    METIS_TAC [vR_update,TC_RULES]
  ],
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
    THEN1 METIS_TAC [TC_RULES] THEN
  DISJ2_TAC THEN Q.EXISTS_TAC `u` THEN
  METIS_TAC [TC_RTC,RTC_TRANSITIVE,transitive_def]
]);

val wfs_extend = Q.store_thm(
  "wfs_extend",
  `wfs s /\ v NOTIN FDOM s /\ v NOTIN vars (walkstar s t) ==>
   wfs (s |+ (v, t))`,
  SRW_TAC [boolSimps.CONJ_ss][oc_eq_vars_walkstar, wfs_no_cycles] THEN
  STRIP_TAC THEN
  `!u. u IN vars t ==> ~(vR s)^+ v u`
     by METIS_TAC [TC_vR_vars_walkstar, wfs_no_cycles] THEN
  `?u. (vR s)^* v v' /\ u IN vars t /\ (vR s)^* v' u`
     by METIS_TAC [TC_vR_update] THEN
  FULL_SIMP_TAC (srw_ss()) [RTC_CASES_TC] THEN
  METIS_TAC [NOT_FDOM_walkstar,wfs_no_cycles,TC_RULES]
);

val vwalk_FDOM = Q.store_thm(
"vwalk_FDOM",
`wfs s ==> (vwalk s v = t) ==>
  (v NOTIN FDOM s /\ (t = Var v)) \/
  (v IN FDOM s /\ (t <> Var v) /\
   ?u.(vwalk s v = vwalk s u) /\ (FLOOKUP s u = SOME t))`,
REVERSE (Cases_on `v IN FDOM s`)
THEN1 METIS_TAC [NOT_FDOM_vwalk] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `v IN FDOM s` MP_TAC THEN
Q.PAT_ASSUM `vwalk s v = t` MP_TAC THEN
Q.ID_SPEC_TAC `v` THEN
HO_MATCH_MP_TAC vwalk_ind THEN
REPEAT (GEN_TAC ORELSE STRIP_TAC) THEN
ASM_SIMP_TAC (srw_ss()) [] THEN
Cases_on `FLOOKUP s v`
  THEN1 (POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF]) THEN
`x = s ' v` by (POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF]) THEN
Cases_on `s ' v` THENL [
  `vwalk s v = vwalk s n`
     by FULL_SIMP_TAC (srw_ss()) [Once(UNDISCH vwalk_def), FLOOKUP_DEF] THEN
  SRW_TAC [][] THENL [
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    Q_TAC SUFF_TAC `n = v` THEN1 METIS_TAC [] THEN
    REVERSE (Cases_on `n IN FDOM s`)
     THEN1 METIS_TAC [NOT_FDOM_vwalk,term_11] THEN
    `vwalk s n <> Var n` by METIS_TAC [] THEN
    `v IN vars (vwalk s n)` by METIS_TAC [IN_INSERT,vars_def] THEN
    `(vR s)^+ v n` by METIS_TAC [vwalk_vR] THEN
    `vR s n v` by FULL_SIMP_TAC (srw_ss()) [vR_def] THEN
    `(vR s)^+ n n` by METIS_TAC [TC_RULES] THEN
    METIS_TAC [wfs_no_cycles],
    Cases_on `n IN FDOM s` THEN1 METIS_TAC [] THEN
    `vwalk s v = Var n` by METIS_TAC [NOT_FDOM_vwalk] THEN
    METIS_TAC []
  ],
  `vwalk s v = x` by SRW_TAC [][Once vwalk_def,FLOOKUP_DEF] THEN METIS_TAC [],
  `vwalk s v = x` by SRW_TAC [][Once vwalk_def,FLOOKUP_DEF] THEN METIS_TAC []
]);

val allvars_def = Define`
  allvars s (t1:'a term) (t2:'a term) = vars t1 ∪ vars t2 ∪ substvars s`;

val FINITE_allvars = RWstore_thm(
"FINITE_allvars",
`FINITE (allvars s t1 t2)`,
SRW_TAC [][allvars_def]);

val allvars_sym = Q.store_thm(
"allvars_sym",
`allvars s t1 t2 = allvars s t2 t1`,
SRW_TAC [][allvars_def,UNION_COMM]);

val uR_def = Define`
uR (sx,c1,c2) (s,t1,t2) =
wfs sx ∧ s SUBMAP sx
∧ allvars sx c1 c2 SUBSET allvars s t1 t2
∧ measure (pair_count o (walkstar sx)) c1 t1`

val FDOM_allvars = prove(
  ``FDOM s ⊆ allvars s t1 t2``,
  SRW_TAC [][allvars_def, substvars_def, SUBSET_DEF]);
val intro = SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO]

val uR_lambda = let
  val c = concl (SPEC_ALL uR_def)
  val args = #2 (strip_comb (lhs c))
  val rhs' = pairSyntax.list_mk_pabs(args, rhs c)
in
  prove(``uR = ^rhs'``,
        SIMP_TAC (srw_ss()) [FUN_EQ_THM, FORALL_PROD, uR_def])
end

val uR_lex_def = Define`
  uR_lex = inv_image ((λs1 s2. s2 SUBMAP s1 ∧ s2 ≠ s1) LEX (λs1 s2. s1 PSUBSET s2 ∧ FINITE s2) LEX (measure pair_count))
           (λ(s,t1,t2). (s,allvars s t1 t2,walk* s t1))`

open lcsymtacs

val uR_RSUBSET_uR_lex = Q.store_thm(
"uR_RSUBSET_uR_lex",
`uR RSUBSET uR_lex`,
srw_tac [][RSUBSET] >>
PairCases_on`x` >> PairCases_on`y` >>
Q.MATCH_RENAME_TAC `uR_lex (sx,c1,c2) (s,t1,t2)` [] >>
FULL_SIMP_TAC (srw_ss()) [uR_def,uR_lex_def,measure_thm,inv_image_def,LEX_DEF] >>
Cases_on `sx = s` >> srw_tac [][PSUBSET_DEF])

val WF_FINITE_PSUBSET = Q.store_thm(
"WF_FINITE_PSUBSET",
`WF (λs1 s2. s1 PSUBSET s2 ∧ FINITE s2)`,
srw_tac [][WF_EQ_WFP] >>
REVERSE (Cases_on `FINITE x`) >- (
  srw_tac [][WFP_DEF] ) >>
POP_ASSUM mp_tac >>
Q.ID_SPEC_TAC `x` >>
match_mp_tac FINITE_COMPLETE_INDUCTION >>
srw_tac [][] >>
match_mp_tac WFP_RULES >>
srw_tac [][])

(*
val WF_uR = Q.store_thm(
"WF_uR",
`WF uR`,
match_mp_tac WF_SUBSET >>
qexists_tac `uR_lex` >>
conj_tac >- (
  srw_tac [][uR_lex_def] >>
  match_mp_tac WF_inv_image >>
  match_mp_tac WF_LEX >>
  conj_tac >- (
    ??? ) >>
  match_mp_tac WF_LEX >>
  conj_tac >- srw_tac [][WF_FINITE_PSUBSET]
  srw_tac [][WF_measure] ) >>
metis_tac [uR_RSUBSET_uR_lex,RSUBSET])

val uR_lex1_def = Define`
  uR_lex1 (sx,c1,c2) (s,t1,t2) =
  (s SUBMAP sx ∧ s ≠ sx ∨ (
    (s = sx) ∧
    allvars sx c1 c2 PSUBSET allvars s t1 t2 ∨ (
      (allvars sx c1 c2 = allvars s t1 t2) ∧
      pair_count (walk* sx c1) < pair_count (walk* s t1))))`

val uR_imp_uR_lex1 = Q.store_thm(
"uR_imp_uR_lex1",
`uR RSUBSET uR_lex1`,
srw_tac [][RSUBSET] >>
PairCases_on`x` >>
PairCases_on`y` >>
Q.MATCH_RENAME_TAC `uR_lex1 (sx,c1,c2) (s,t1,t2)` [] >>
FULL_SIMP_TAC (srw_ss()) [uR_def,uR_lex1_def,measure_thm] >>
Cases_on `s = sx` >> srw_tac [][] >>
Cases_on `allvars s c1 c2 = allvars s t1 t2` >> srw_tac [][PSUBSET_DEF])

val uR_lex1_imp_uR = Q.store_thm(
"uR_lex1_imp_uR",
`uR_lex1 RSUBSET uR`,
srw_tac [][RSUBSET] >>
PairCases_on`x` >>
PairCases_on`y` >>
Q.MATCH_RENAME_TAC `uR (sx,c1,c2) (s,t1,t2)` [] >>
FULL_SIMP_TAC (srw_ss()) [uR_def,uR_lex1_def,measure_thm] >>

val uR_lex1_uR = Q.store_thm(
"uR_lex1_uR",
`uR_lex1 = uR`,
srw_tac [][FUN_EQ_THM] >>
Q.MATCH_RENAME_TAC `uR_lex1 c p ⇔ uR c p` [] >>
PairCases_on `c` >> PairCases_on `p` >>
Q.MATCH_RENAME_TAC `uR_lex1 (sx,c1,c2) (s,t1,t2) ⇔ X` ["X"] >>
srw_tac [][uR_def,uR_lex1_def,measure_thm] >>
Cases_on `wfs sx` >> srw_tac [][] >>
Cases_on `s SUBMAP sx` >> srw_tac [][] >- (
  Cases_on `s = sx` >> srw_tac [][]
*)

val WF_uR = Q.store_thm(
"WF_uR",
`WF uR`,
SRW_TAC [][WF_IFF_WELLFOUNDED,wellfounded_def,uR_lambda,UNCURRY,EXISTS_OR_THM] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
Q.ISPECL_THEN [`λx y. y:num set SUBSET x`,
               `λn. allvars (FST (f n)) (FST (SND (f n))) (SND (SND (f n)))`]
              MP_TAC
              transitive_monotone THEN
DISCH_THEN
    (fn th => th |> SIMP_RULE (srw_ss()) [transitive_def,GSYM AND_IMP_INTRO]
                 |> UNDISCH
                 |> (fn th => PROVE_HYP (prove(hd(hyp th),
                                               METIS_TAC [SUBSET_TRANS])) th)
                 |> MP_TAC) THEN
`∀m n. m < n ⇒ FST (f m) ⊑ FST (f n)`
   by (CONV_TAC (STRIP_QUANT_CONV
                     (RAND_CONV (RAND_CONV (UNBETA_CONV ``n:num``) THENC
                                 LAND_CONV (UNBETA_CONV ``m:num``)))) THEN
       MATCH_MP_TAC transitive_monotone THEN
       SRW_TAC [][transitive_def] THEN METIS_TAC [SUBMAP_TRANS]) THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`?m.!n. m < n ==> (allvars (FST(f n)) (FST(SND(f n))) (SND(SND(f n))) =
                   allvars (FST(f m)) (FST(SND(f m))) (SND(SND(f m))))`
  by (SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [SKOLEM_THM] THEN
      `!m. m < f' m /\
           allvars (FST(f(f' m))) (FST(SND(f(f' m)))) (SND(SND(f(f' m))))
           PSUBSET
           allvars (FST(f m)) (FST(SND(f m))) (SND(SND(f m)))`
        by (METIS_TAC [PSUBSET_DEF]) THEN
      `!m.measure CARD
            (allvars (FST(f(f' m))) (FST(SND(f(f' m)))) (SND(SND(f(f' m)))))
            (allvars (FST(f m)) (FST(SND(f m))) (SND(SND(f m))))`
        by (METIS_TAC [measure_thm,FINITE_allvars,CARD_PSUBSET])
        THEN
      `WF (measure (CARD:((num -> bool) -> num)))` by SRW_TAC [][] THEN
      FULL_SIMP_TAC bool_ss [WF_IFF_WELLFOUNDED,wellfounded_def] THEN
      POP_ASSUM (Q.SPEC_THEN
                   `\n.LET (\t.allvars (FST t) (FST(SND t)) (SND(SND t)))
                           (f (FUNPOW f' n 0))`
                 MP_TAC) THEN
      FULL_SIMP_TAC (srw_ss()) [LET_THM,FUNPOW_SUC]) THEN
`?m.!n.m < n ==> ((FST(f m)) = (FST(f n)))`
by (Q.ISPECL_THEN
    [`FST o f`,
     `\n.allvars (FST(f n)) (FST(SND(f n))) (SND(SND(f n))) DIFF
         (FDOM(FST(f n)))`,`m`] (MATCH_MP_TAC o GSYM o SIMP_RULE (srw_ss()) [])
    commonUnifTheory.extension_chain THEN
    SRW_TAC [][DISJOINT_DEF] THENL [
      SRW_TAC [][EXTENSION] THEN METIS_TAC [],
      METIS_TAC [UNION_DIFF,allvars_def,substvars_def,SUBSET_UNION,SUBSET_TRANS]
    ]) THEN
Q.ABBREV_TAC `z = MAX m m'` THEN
`!n. z < n ==> (FST(f n) = FST(f m'))` by (METIS_TAC [MAX_LT]) THEN
`!n. z < n ==> measure (pair_count o (walkstar (FST(f m'))))
               (FST(SND(f(SUC n)))) (FST(SND(f n)))`
  by (SRW_TAC [][] THEN METIS_TAC [LESS_SUC]) THEN
`WF (measure (pair_count o (walkstar (FST(f m')))))` by SRW_TAC [][] THEN
FULL_SIMP_TAC bool_ss [WF_IFF_WELLFOUNDED,wellfounded_def] THEN
POP_ASSUM (Q.SPEC_THEN `\n.(FST(SND(f(z+n+1))))` MP_TAC) THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `!n.z < n ==> measure X Y Z` (Q.SPEC_THEN `z+n+1` MP_TAC) THEN
SRW_TAC [ARITH_ss][ADD1]);

val tunify_defn_q =`
  tunify s t1 t2 =
  if wfs s then
    case (walk s t1, walk s t2) of
      (Var v1, Var v2) -> SOME if (v1 = v2) then s else (s |+ (v1,Var v2))
   || (Var v1, t2) -> if oc s t2 v1 then NONE else SOME (s |+ (v1,t2))
   || (t1, Var v2) -> if oc s t1 v2 then NONE else SOME (s |+ (v2,t1))
   || (Pair t1a t1d, Pair t2a t2d) ->
        do sx <- tunify s t1a t2a; tunify sx t1d t2d od
   || (Const c1, Const c2) -> if (c1 = c2) then SOME s else NONE
   || _ -> NONE
else ARB`;

val tunify_defn = Hol_defn "tunify" tunify_defn_q;

val _ = store_term_thm("tunify_defn", TermWithCase tunify_defn_q);

val [tc0,tc1,tc2] = map (SIMP_TERM (srw_ss()) []) (Defn.tcs_of tunify_defn);
val _ = store_term_thm("tunify_tcd", tc0);
val _ = store_term_thm("tunify_tca", tc1);
val _ = store_term_thm("tunify_tc_WF", tc2);

val vwalk_to_Pair_SUBSET_rangevars = Q.store_thm(
"vwalk_to_Pair_SUBSET_rangevars",
`wfs s /\ (vwalk s v = Pair t1 t2)
  ==> (vars t1 SUBSET (rangevars s)) /\
      (vars t2 SUBSET (rangevars s))`,
STRIP_TAC THEN
`v ∈ FDOM s` by METIS_TAC [NOT_FDOM_vwalk,term_distinct] THEN
IMP_RES_TAC vwalk_IN_FRANGE THEN
IMP_RES_TAC IN_FRANGE_rangevars THEN
POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) []);

val allvars_SUBSET = Q.store_thm(
"allvars_SUBSET",
`wfs s /\
 (walk s t1 = Pair t1a t1d) /\
 (walk s t2 = Pair t2a t2d) ==>
 allvars s t1a t2a SUBSET allvars s t1 t2 /\
 allvars s t1d t2d SUBSET allvars s t1 t2`,
SRW_TAC [][walk_def,allvars_def] THEN
Cases_on `t1` THEN Cases_on `t2` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [vwalk_to_Pair_SUBSET_rangevars,substvars_def,SUBSET_TRANS,SUBSET_UNION]);

val walkstar_subterm_smaller = Q.store_thm(
"walkstar_subterm_smaller",
`wfs s /\ (walk s t1 = Pair t1a t1d) ==>
  pair_count (walkstar s t1a) < pair_count (walkstar s t1) /\
  pair_count (walkstar s t1d) < pair_count (walkstar s t1)`,
SRW_TAC [][walk_def] THEN
Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val tca_thm = Q.store_thm(
"tca_thm",
`wfs s /\
 (walk s t1 = Pair t1a t1d) /\
 (walk s t2 = Pair t2a t2d) ==>
 uR (s,t1a,t2a) (s,t1,t2)`,
SRW_TAC [][uR_def,SUBMAP_REFL] THEN
METIS_TAC [allvars_SUBSET,walkstar_subterm_smaller]);

val met = METIS_TAC [SUBSET_UNION,SUBSET_TRANS];

val allvars_SUBSET_FUPDATE = Q.store_thm(
"allvars_SUBSET_FUPDATE",
`(walk s t1 = Pair t1a t1d) /\ (walk s t2 = Pair t2a t2d) /\
 (walk s t1a = Var v) /\ wfs s ==>
 allvars (s |+ (v,walk s t2a)) t1d t2d SUBSET allvars s t1 t2`,
SRW_TAC [][allvars_def] THEN1 (
  Cases_on `walk s t1 = t1` THEN1 (
    FULL_SIMP_TAC (srw_ss()) [] THEN met) THEN
  IMP_RES_TAC walk_IN_FRANGE THEN
  IMP_RES_TAC IN_FRANGE_rangevars THEN
  Q.PAT_ASSUM `walk s t1 = X` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [substvars_def] THEN met )
THEN1 (
  Cases_on `walk s t2 = t2` THEN1 (
    FULL_SIMP_TAC (srw_ss()) [] THEN met) THEN
  IMP_RES_TAC walk_IN_FRANGE THEN
  IMP_RES_TAC IN_FRANGE_rangevars THEN
  Q.PAT_ASSUM `walk s t2 = X` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [substvars_def] THEN met ) THEN
IMP_RES_TAC walk_to_var THEN SRW_TAC [][] THEN
ASM_SIMP_TAC (srw_ss()) [substvars_def,rangevars_FUPDATE] THEN
CONJ_TAC THEN1 (
  REVERSE CONJ_TAC THEN1 met THEN
  Cases_on `u = v` THEN SRW_TAC [][] THEN1 (
    Cases_on `walk s t1 = t1` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC walk_IN_FRANGE THEN
    IMP_RES_TAC IN_FRANGE_rangevars THEN
    Q.PAT_ASSUM `walk s t1 = X` ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] ) THEN
  FULL_SIMP_TAC (srw_ss()) []  THEN
  `u ∈ FDOM s` by METIS_TAC [NOT_FDOM_vwalk,term_11] THEN
  IMP_RES_TAC vwalk_IN_FRANGE THEN
  IMP_RES_TAC IN_FRANGE_rangevars THEN
  Q.PAT_ASSUM `vwalk s u = X` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
CONJ_TAC THEN1 met THEN
Cases_on `walk s t2a = t2a` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  Cases_on `walk s t2 = t2` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN1 met THEN
  IMP_RES_TAC walk_IN_FRANGE THEN
  IMP_RES_TAC IN_FRANGE_rangevars THEN
  Q.PAT_ASSUM `walk s t2 = X` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN met ) THEN
IMP_RES_TAC walk_IN_FRANGE THEN
IMP_RES_TAC IN_FRANGE_rangevars THEN met );

val walkstar_subterm_FUPDATE = Q.store_thm(
"walkstar_subterm_FUPDATE",
`wfs s /\ v NOTIN FDOM s /\ v NOTIN vars (walkstar s t) /\
 (walk s t1 = Pair t1a t1d) ==>
  pair_count (walkstar (s |+ (v,t)) t1d) <
  pair_count (walkstar (s |+ (v,t)) t1)`,
SRW_TAC [][] THEN
`wfs (s |+ (v,t))` by METIS_TAC [wfs_extend] THEN
`s SUBMAP (s |+ (v,t))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
`walk (s |+ (v,t)) t1 = Pair t1a t1d`
  by (Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [walk_def] THEN
      Q.MATCH_ABBREV_TAC `vwalk (s|+(v,t)) s' = Pair t1a t1d` THEN
      MP_TAC(Q.SPECL[`s'`,`s`](Q.INST[`sx`|->`(s |+ (v,t))`](UNDISCH
      vwalk_SUBMAP))) THEN
      SRW_TAC [][]) THEN
Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [walk_def] THEN
SRW_TAC [ARITH_ss][measure_thm,walkstar_thm]
);

val SOME tunify_aux_defn = Defn.aux_defn tunify_defn;

val aux_def =
SIMP_RULE std_ss []
(MATCH_MP
 (MATCH_MP WFREC_COROLLARY
  (Q.SPEC`uR`(definition"tunify_tupled_AUX_def")))
 WF_uR);

val uR_subterm = Q.store_thm(
"uR_subterm",
`wfs s /\
 (walk s t1 = Pair t1a t1d) /\
 (walk s t2 = Pair t2a t2d) ==>
  uR (s,t1a,t2a) (s,t1,t2) /\
  uR (s,t1d,t2d) (s,t1,t2)`,
REPEAT STRIP_TAC THEN
SRW_TAC [][uR_def,SUBMAP_REFL] THEN
METIS_TAC [allvars_SUBSET,walkstar_subterm_smaller]
);

val uR_subterm_FUPDATE = Q.store_thm(
"uR_subterm_FUPDATE",
`(walk s t1 = Pair t1a t1d) /\
 (walk s t2 = Pair t2a t2d) /\
 ((walk s t1a = Var v) /\ (walk s t2a = t) ∨
  (walk s t2a = Var v) ∧ (walk s t1a = t)) ∧
 wfs s /\
 v NOTIN FDOM s /\
 v NOTIN vars (walk* s t) ==>
 uR (s |+ (v,t), t1d, t2d) (s,t1,t2)`,
STRIP_TAC THEN
`wfs (s |+ (v,t))` by METIS_TAC [wfs_extend] THEN
`s SUBMAP (s|+(v,t))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
(SRW_TAC [][uR_def] THEN1 METIS_TAC [allvars_SUBSET_FUPDATE,allvars_sym] THEN
METIS_TAC [walkstar_subterm_FUPDATE])
);

val uR_ind = save_thm("uR_ind",WF_INDUCTION_THM |> Q.ISPEC `uR` |> SIMP_RULE (srw_ss()) [WF_uR]
|> Q.SPEC `\(a,b,c).P a b c` |> SIMP_RULE std_ss [FORALL_PROD] |> Q.GEN`P`);

val uP_def = Define`
uP sx s t1 t2 = wfs sx /\ s SUBMAP sx /\ substvars sx SUBSET allvars s t1 t2`;

val uP_sym = Q.store_thm(
"uP_sym",
`uP sx s t1 t2 ⇔ uP sx s t2 t1`,
SRW_TAC [][uP_def,allvars_sym]);

val uP_FUPDATE = Q.store_thm(
"uP_FUPDATE",
`wfs s /\
 v NOTIN FDOM s /\
 v NOTIN vars (walkstar s t2) /\
 (walk s t1 = Var v) ==>
 uP (s |+ (v,walk s t2)) s t1 t2`,
STRIP_TAC THEN
`wfs (s |+ (v,walk s t2))` by METIS_TAC [wfs_extend,walkstar_walk] THEN
`s SUBMAP (s|+(v,walk s t2))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
SRW_TAC [][uP_def,allvars_def] THEN
Cases_on `walk s t2 = t2` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [substvars_def,rangevars_FUPDATE] THEN
Cases_on `walk s t1 = t1` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 met THEN
IMP_RES_TAC walk_IN_FRANGE THEN
IMP_RES_TAC IN_FRANGE_rangevars THEN
Q.PAT_ASSUM `walk s t1 = X` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN met);

val walk_SUBMAP = Q.store_thm(
"walk_SUBMAP",
`wfs sx /\ s SUBMAP sx ==>
  case walk s t of
     Var u -> walk sx t = walk sx (Var u)
  || u -> walk sx t = u`,
Cases_on `t` THEN SRW_TAC [][walk_def] THEN
MP_TAC (Q.SPECL [`n`,`s`] (UNDISCH vwalk_SUBMAP)) THEN
SRW_TAC [][])

val uR_IMP_uP = Q.store_thm(
"uR_IMP_uP",
`uR (sx,c1,c2) (s,t1,t2) ==> uP sx s t1 t2`,
SRW_TAC [][uR_def,uP_def,allvars_def])

val uP_IMP_subterm_uR = Q.store_thm(
"uP_IMP_subterm_uR",
`wfs s /\
 (walk s t1 = Pair t1a t1d) /\
 (walk s t2 = Pair t2a t2d) /\
 (uP sx s t1a t2a \/ uP sx s t1d t2d) ==>
 uR (sx,t1d,t2d) (s,t1,t2)`,
SRW_TAC [][] THEN (
`allvars s t1a t2a SUBSET allvars s t1 t2 /\
 allvars s t1d t2d SUBSET allvars s t1 t2`
  by METIS_TAC [allvars_SUBSET] THEN
FULL_SIMP_TAC (srw_ss()) [uR_def,uP_def] THEN
`substvars sx SUBSET allvars s t1 t2` by METIS_TAC [SUBSET_TRANS] THEN
SRW_TAC [][] THENL [
  SRW_TAC [][Once allvars_def] THEN
  METIS_TAC [allvars_def,SUBSET_UNION,SUBSET_TRANS],
  `walk sx t1 = walk s t1`
    by (MP_TAC (Q.INST [`t`|->`t1`] walk_SUBMAP) THEN
        SRW_TAC [][]) THEN
  Cases_on `t1` THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [measure_thm,walk_def]
]))

val aux_uP = Q.store_thm(
"aux_uP",
`!s t1 t2 sx.
   wfs s /\ (tunify_tupled_aux uR (s,t1,t2) = SOME sx) ==>
     uP sx s t1 t2`,
HO_MATCH_MP_TAC uR_ind THEN
REPEAT (GEN_TAC ORELSE (DISCH_THEN STRIP_ASSUME_TAC)) THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC (srw_ss()) [aux_def] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2`
THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
  SRW_TAC [][] THEN1
    (SRW_TAC [][uP_def,SUBMAP_REFL,allvars_def] THEN
     METIS_TAC [SUBSET_UNION,SUBSET_TRANS]) THEN
  `n NOTIN FDOM s`
    by (IMP_RES_TAC walk_var_vwalk THEN
        IMP_RES_TAC vwalk_to_var THEN
        IMP_RES_TAC NOT_FDOM_vwalk) THEN
  `n NOTIN vars (walkstar s (Var n'))`
    by (IMP_RES_TAC walk_var_vwalk THEN
        IMP_RES_TAC vwalk_to_var THEN
        IMP_RES_TAC NOT_FDOM_vwalk THEN
        SRW_TAC [][walkstar_thm]) THEN
  METIS_TAC [uP_FUPDATE,walkstar_walk],
  SRW_TAC [][] THEN
  `n NOTIN FDOM s`
    by (IMP_RES_TAC walk_var_vwalk THEN
        IMP_RES_TAC vwalk_to_var THEN
        IMP_RES_TAC NOT_FDOM_vwalk) THEN
  `n NOTIN vars (walkstar s (Pair t t0))`
    by (`~(n IN oc s t \/ n IN oc s t0)` by METIS_TAC [IN_DEF] THEN
        SRW_TAC [][walkstar_thm] THEN
        METIS_TAC [oc_eq_vars_walkstar]) THEN
  METIS_TAC [uP_FUPDATE,walkstar_walk],
  SRW_TAC [][] THEN
  `n NOTIN FDOM s`
    by (IMP_RES_TAC walk_var_vwalk THEN
        IMP_RES_TAC vwalk_to_var THEN
        IMP_RES_TAC NOT_FDOM_vwalk) THEN
  Q.MATCH_ASSUM_RENAME_TAC `walk s X = Const c` ["X"] THEN
  `n NOTIN vars (walkstar s (Const c))`
    by (SRW_TAC [][walkstar_thm]) THEN
  METIS_TAC [uP_FUPDATE,walkstar_walk],
  SRW_TAC [][] THEN
  `n NOTIN FDOM s`
    by (IMP_RES_TAC walk_var_vwalk THEN
        IMP_RES_TAC vwalk_to_var THEN
        IMP_RES_TAC NOT_FDOM_vwalk) THEN
  `n NOTIN vars (walkstar s (Pair t t0))`
    by (`~(n IN oc s t \/ n IN oc s t0)` by METIS_TAC [IN_DEF] THEN
        SRW_TAC [][walkstar_thm] THEN
        METIS_TAC [oc_eq_vars_walkstar]) THEN
  METIS_TAC [uP_FUPDATE,walkstar_walk,uP_sym],
  `uR (s,t,t') (s,t1,t2)` by METIS_TAC [uR_subterm] THEN
  ASM_SIMP_TAC (srw_ss()) [RESTRICT_LEMMA] THEN
  Cases_on `tunify_tupled_aux uR (s,t,t')` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `uP x s t t'`
     by (FIRST_ASSUM (Q.SPECL_THEN [`s`,`t`,`t'`] ASSUME_TAC)
         THEN RES_TAC) THEN
  `uR (x,t0,t0') (s,t1,t2)`
     by METIS_TAC [uP_IMP_subterm_uR] THEN
  ASM_SIMP_TAC (srw_ss()) [RESTRICT_LEMMA] THEN
  STRIP_TAC THEN
  `wfs x` by FULL_SIMP_TAC (srw_ss()) [uP_def] THEN
  `uP sx x t0 t0'` by METIS_TAC [] THEN
  FULL_SIMP_TAC (srw_ss()) [uP_def,uR_def] THEN
  METIS_TAC [SUBMAP_TRANS,SUBSET_TRANS],
  SRW_TAC [][] THEN
  `n NOTIN FDOM s`
    by (IMP_RES_TAC walk_var_vwalk THEN
        IMP_RES_TAC vwalk_to_var THEN
        IMP_RES_TAC NOT_FDOM_vwalk) THEN
  Q.MATCH_ASSUM_RENAME_TAC `walk s X = Const c` ["X"] THEN
  `n NOTIN vars (walkstar s (Const c))`
    by (SRW_TAC [][walkstar_thm]) THEN
  METIS_TAC [uP_FUPDATE,walkstar_walk,uP_sym],
  SRW_TAC [][uP_def,allvars_def,SUBMAP_REFL] THEN
  METIS_TAC [SUBSET_UNION,SUBSET_TRANS]
])

val tcd_thm = Q.store_thm(
"tcd_thm",
`wfs s /\
 (walk s t1 = Pair t1a t1d) /\
 (walk s t2 = Pair t2a t2d) /\
 (tunify_tupled_aux uR (s,t1a,t2a) = SOME sx) ==>
 uR (sx,t1d,t2d) (s,t1,t2)`,
METIS_TAC [aux_uP, uP_IMP_subterm_uR])

val (tunify_def,tunify_ind) = Defn.tprove (
tunify_defn,
WF_REL_TAC `uR` THEN METIS_TAC [WF_uR,tca_thm,tcd_thm]
)

val [aux_eqn0] = Defn.eqns_of tunify_aux_defn
val aux_eqn = aux_eqn0 |> Q.INST[`R`|->`uR`] |>
              PROVE_HYP WF_uR |>
              (fn th => PROVE_HYP
               (prove(hd(hyp th),SRW_TAC[][tcd_thm])) th) |>
              (fn th => PROVE_HYP
               (prove(hd(hyp th),SRW_TAC[][tca_thm])) th)

val aux_eq_tunify = Q.store_thm(
"aux_eq_tunify",
`!s t1 t2. tunify_tupled_aux uR (s,t1,t2) = tunify s t1 t2`,
HO_MATCH_MP_TAC tunify_ind THEN
REPEAT STRIP_TAC THEN
SRW_TAC [][Once aux_eqn] THEN
SRW_TAC [][Once tunify_def,SimpRHS] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN
SRW_TAC [][] THEN
Cases_on `tunify s t t'` THEN SRW_TAC [][]
)

val ext_s_check_def = RWDefine`
ext_s_check s v t = if oc s t v then NONE else SOME (s |+ (v,t))`

val unify_exists = prove(
``?unify.!s t1 t2.wfs s ==> (unify s t1 t2 =
    case (walk s t1, walk s t2) of
      (Var v1, Var v2) -> SOME if (v1 = v2) then s else (s |+ (v1,Var v2))
   || (Var v1, t2) -> ext_s_check s v1 t2
   || (t1, Var v2) -> ext_s_check s v2 t1
   || (Pair t1a t1d, Pair t2a t2d) ->
        do sx <- unify s t1a t2a; unify sx t1d t2d od
   || (Const c1, Const c2) -> if (c1 = c2) then SOME s else NONE
   || _ -> NONE)``,
Q.EXISTS_TAC `tunify` THEN
SRW_TAC [][Once tunify_def,SimpLHS] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN
SRW_TAC [][])

val unify_def = new_specification("unify_def",["unify"],unify_exists)

val _ = store_type_thm("unify_type",type_of``unify``)

val unify_eq_tunify = Q.store_thm(
"unify_eq_tunify",
`!s t1 t2. wfs s ==> (unify s t1 t2 = tunify s t1 t2)`,
HO_MATCH_MP_TAC tunify_ind THEN
REPEAT STRIP_TAC THEN
SRW_TAC [][Once tunify_def,SimpRHS] THEN
SRW_TAC [][Once unify_def,SimpLHS] THEN
Cases_on `walk s t1` THEN Cases_on `walk s t2` THEN
SRW_TAC [][] THEN
Cases_on `tunify s t t'` THEN SRW_TAC [][] THEN
`wfs x` by METIS_TAC [aux_eq_tunify,uP_def,aux_uP] THEN
METIS_TAC [])

val _ = metisTools.limit :=  { time = NONE, infs = NONE }
val unify_ind = Q.store_thm(
"unify_ind",
`!P.
     (!s t1 t2.
        (!t1a t1d t2a t2d sx.
           wfs s /\
           (walk s t1 = Pair t1a t1d) /\
           (walk s t2 = Pair t2a t2d) /\
           (unify s t1a t2a = SOME sx) ==>
           P sx t1d t2d) /\
        (!t1a t1d t2a t2d.
           wfs s /\
           (walk s t1 = Pair t1a t1d) /\
           (walk s t2 = Pair t2a t2d) ==>
           P s t1a t2a) ==>
        P s t1 t2) ==>
     !v v1 v2. P v v1 v2`,
METIS_TAC [unify_eq_tunify,tunify_ind])

val unify_uP = Q.store_thm(
"unify_uP",
`wfs s /\ (unify s t1 t2 = SOME sx) ==>
   uP sx s t1 t2`,
METIS_TAC [unify_eq_tunify,aux_eq_tunify,aux_uP])

val _ = export_theory ()
