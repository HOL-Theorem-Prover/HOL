open HolKernel boolLib bossLib Parse pred_setTheory finite_mapTheory
prim_recTheory relationTheory pairTheory bagTheory apply_piTheory
ntermTheory nsubstTheory nwalkTheory nomsetTheory listTheory
ramanaLib ntermLib

val _ = new_theory "nwalkstar"

val (noc_rules, noc_ind, noc_cases) = Hol_reln`
  (v IN nvars t /\ v NOTIN FDOM s ==> noc s t v) /\
  (u IN nvars t /\ (nvwalk s [] u = t') /\ noc s t' v ==>
                noc s t v)`

val noc2 = CONJUNCT2 (SIMP_RULE bool_ss [FORALL_AND_THM] noc_rules)

val noc_strong_ind =
  save_thm("noc_strong_ind",IndDefLib.derive_strong_induction(noc_rules, noc_ind))

val noc_pair_E0 = Q.prove(
  `!t v. noc s t v ==>
          !t1 t2. (t = nPair t1 t2) ==> noc s t1 v \/ noc s t2 v`,
  HO_MATCH_MP_TAC noc_strong_ind THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [noc_rules] THEN
  METIS_TAC [noc_rules])

val noc_pair_E = SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] noc_pair_E0

val noc_pair_I = Q.prove(
  `(!t1. noc s t1 v ==> noc s (nPair t1 t2) v) /\
   (!t2. noc s t2 v ==> noc s (nPair t1 t2) v)`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [noc_cases]) THEN
  SRW_TAC [][] THEN
  METIS_TAC [nvars_def, IN_UNION, noc_rules])

val noc_pair = Q.prove(
  `noc s (nPair t1 t2) v = noc s t1 v \/ noc s t2 v`,
  METIS_TAC [noc_pair_E, noc_pair_I])

val noc_const = Q.prove(
  `~noc s (nConst c) v`,
  ONCE_REWRITE_TAC [noc_cases] THEN SRW_TAC [][])

val noc_nom = Q.prove(
  `~noc s (Nom a) v`,
  ONCE_REWRITE_TAC [noc_cases] THEN SRW_TAC [][])

val noc_tie = Q.prove(
  `noc s (Tie a t) v = noc s t v`,
  ONCE_REWRITE_TAC [noc_cases] THEN SRW_TAC [][])

val noc_var1 = Q.prove(
  `!t v. noc s t v ==>
        !p u. (t = Sus p u) /\ nwfs s ==>
               case nvwalk s [] u
               of Sus p v1 -> (v1 = v)
               || Tie a t -> noc s t v
               || nPair t1 t2 -> noc s t1 v ∨ noc s t2 v
               || _ -> F`,
  HO_MATCH_MP_TAC noc_strong_ind THEN SRW_TAC [][]
    THEN1 (FULL_SIMP_TAC (srw_ss())[] THEN
           SRW_TAC [][Once nvwalk_def,FLOOKUP_DEF]) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  Cases_on `nvwalk s [] u` THEN
  FULL_SIMP_TAC (srw_ss()) [noc_pair,noc_const,noc_nom,noc_tie]  THEN
  `nvwalk s [] n = Sus [] n` by METIS_TAC [nvwalk_to_var,NOT_FDOM_nvwalk] THEN
  FULL_SIMP_TAC (srw_ss()) [])

val noc_var2 = Q.prove(
  `nwfs s ==> !pn v. (pn = []) ∧
          (case nvwalk s pn v
           of Sus p u -> (x = u)
           || Tie a t -> noc s t x
           || nPair t1 t2 -> noc s t1 x ∨ noc s t2 x
           || _ -> F) ⇒
          noc s (Sus p v) x`,
  DISCH_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN SRW_TAC [][] THEN
  Cases_on `nvwalk s [] v` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    MATCH_MP_TAC noc2 THEN SRW_TAC [][] THEN
    `n NOTIN FDOM s` by METIS_TAC [nvwalk_to_var,NOT_FDOM_nvwalk] THEN
    METIS_TAC [noc_rules, nvars_def, IN_INSERT],
    MATCH_MP_TAC noc2 THEN SRW_TAC [][noc_tie],
    MATCH_MP_TAC noc2 THEN SRW_TAC [][noc_pair],
    MATCH_MP_TAC noc2 THEN SRW_TAC [][noc_pair]])

val noc_var = Q.prove(
  `nwfs s ==> (noc s (Sus p v) x =
          case nvwalk s [] v
          of Sus p u -> (x = u)
          || Tie a t -> noc s t x
          || nPair t1 t2 -> noc s t1 x ∨ noc s t2 x
          || _ -> F)`,
SRW_TAC [][EQ_IMP_THM] THENL [
  (noc_var1 |>
   Q.SPECL [`Sus p v`,`x`] |>
   SIMP_RULE (srw_ss()) [] |>
   UNDISCH |>
   Q.SPEC `p` |>
   SIMP_RULE (srw_ss()) [] |>
   DISCH_ALL |>
   ASSUME_TAC) THEN
  Cases_on `nvwalk s [] v` THEN FULL_SIMP_TAC (srw_ss()) [],
  (noc_var2 |>
   UNDISCH |>
   Q.SPECL [`[]`,`v`] |>
   SIMP_RULE (srw_ss()) [] |>
   MATCH_MP_TAC) THEN
  Cases_on `nvwalk s [] v` THEN FULL_SIMP_TAC (srw_ss()) []
])

val noc_thm = RWsave_thm("noc_thm", LIST_CONJ [noc_nom, noc_var, noc_tie, noc_pair, noc_const])

val pre_nwalkstar_def = TotalDefn.xDefineSchema "pre_nwalkstar"
`nwalkstar t = case nwalk s t
               of Tie a t -> Tie a (nwalkstar t)
               || nPair t1 t2 -> nPair (nwalkstar t1) (nwalkstar t2)
               || t -> t`;

val _ = overload_on("nwalk*",``nwalkstar``)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "n◁", BreakSpace(1,0)],
                  term_name = "nwalk*",
                  fixity = Infixr 700};

val _ = store_term_thm("nwalkstar_def_print", TermWithCase
`nwfs s ⇒
(nwalk* s t = case nwalk s t
               of Tie a t -> Tie a (nwalk* s t)
               || nPair t1 t2 -> nPair (nwalk* s t1) (nwalk* s  t2)
               || t -> t)`);

val _ = overload_on("npair_count", ``nterm_size ARB``)

fun inst_nwalkstar th =
Q.INST [`R` |-> `inv_image ((LEX) (mlt1 (nvR s)^+)^+ (measure npair_count))
                            (λt. (nvarb t, t))`] th

val [h3,h1,h2,h4] = hyp (inst_nwalkstar pre_nwalkstar_def)

val th1 = Q.prove(`nwfs s ⇒ ^(h1)`,
STRIP_TAC THEN REPEAT GEN_TAC THEN
SIMP_TAC (srw_ss()) [inv_image_def,LEX_DEF] THEN
Cases_on `t` THEN SRW_TAC [][] THENL [
  `∀u. u IN nvars (nPair t1 t2) ⇒ (nvR s)^+ u n`
  by METIS_TAC [nvwalk_nvR,ntermeq_thm] THEN
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][mlt1_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`n`,`nvarb t2`,`{||}`] THEN
  SRW_TAC [][],
  Q.MATCH_RENAME_TAC `X ∨ Y ∧ 0 < 1 + npair_count t1` ["X","Y"] THEN
  Cases_on `nvarb t1 = {||}` THEN1
    SRW_TAC [ARITH_ss][] THEN
  DISJ1_TAC THEN Q.MATCH_ABBREV_TAC `(mlt1 R)^+ b2 (b1 + b2)` THEN
  Q_TAC SUFF_TAC `(mlt1 R)^+ b2 (b2 + b1)` THEN1
    METIS_TAC [COMM_BAG_UNION] THEN
  MATCH_MP_TAC TC_mlt1_UNION2_I THEN
  UNABBREV_ALL_TAC THEN
  SRW_TAC [][]
])

val th2 = Q.prove(`nwfs s ⇒ ^(h2)`,
STRIP_TAC THEN REPEAT GEN_TAC THEN
SIMP_TAC (srw_ss()) [inv_image_def,LEX_DEF] THEN
Cases_on `t` THEN SRW_TAC [][] THENL [
  `∀u. u IN nvars (nPair t1 t2) ⇒ (nvR s)^+ u n`
  by METIS_TAC [nvwalk_nvR,ntermeq_thm] THEN
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][mlt1_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`n`,`nvarb t1`,`{||}`] THEN
  SRW_TAC [][],
  Q.MATCH_RENAME_TAC
    `X ∨ Y ∧ npair_count t1 < 1 + npair_count t1 + npair_count t2`
    ["X","Y"] THEN
  Cases_on `nvarb t2 = {||}` THEN1
    SRW_TAC [ARITH_ss][] THEN
  DISJ1_TAC THEN MATCH_MP_TAC TC_mlt1_UNION2_I THEN
  SRW_TAC [][]
])

val th3 = prove(``nwfs s ⇒ ^(h3)``,
STRIP_TAC THEN REPEAT GEN_TAC THEN
SIMP_TAC (srw_ss()) [inv_image_def,LEX_DEF] THEN
Cases_on `t` THEN SRW_TAC [][] THEN
`∀u. u IN nvars (Tie a t') ⇒ (nvR s)^+ u n`
  by METIS_TAC [nvwalk_nvR,ntermeq_thm] THEN
MATCH_MP_TAC TC_SUBSET THEN
SRW_TAC [][mlt1_def] THEN
MAP_EVERY Q.EXISTS_TAC [`n`,`nvarb t'`,`{||}`] THEN
SRW_TAC [][])

val th4 = prove(``nwfs s ⇒ ^(h4)``,
SRW_TAC [][nwfs_def] THEN
MATCH_MP_TAC WF_inv_image THEN
SRW_TAC [][WF_measure,WF_TC,WF_LEX,WF_mlt1])

fun nwalkstar_nwfs_hyp th =
  th |>
  PROVE_HYP (UNDISCH th1) |>
  PROVE_HYP (UNDISCH th2) |>
  PROVE_HYP (UNDISCH th3) |>
  PROVE_HYP (UNDISCH th4)

val nwalkstar_def = save_thm("nwalkstar_def",DISCH_ALL(nwalkstar_nwfs_hyp (inst_nwalkstar pre_nwalkstar_def)))
val nwalkstar_ind = save_thm("nwalkstar_ind",nwalkstar_nwfs_hyp (inst_nwalkstar (theorem "pre_nwalkstar_ind")))

val nwalkstar_nom = nwalkstar_def |> UNDISCH |> Q.SPEC `Nom a` |> DISCH_ALL |> SIMP_RULE (srw_ss()) []
val nwalkstar_var = nwalkstar_def |> UNDISCH |> Q.SPEC `Sus p v` |> DISCH_ALL |> SIMP_RULE (srw_ss()) []
val nwalkstar_tie = nwalkstar_def |> UNDISCH |> Q.SPEC `Tie a t` |> DISCH_ALL |> SIMP_RULE (srw_ss()) []
val nwalkstar_pair = nwalkstar_def |> UNDISCH |> Q.SPEC `nPair t1 t2` |> DISCH_ALL |> SIMP_RULE (srw_ss()) []
val nwalkstar_const = nwalkstar_def |> UNDISCH |> Q.SPEC `nConst c` |> DISCH_ALL |> SIMP_RULE (srw_ss()) []
val nwalkstar_thm = RWsave_thm(
  "nwalkstar_thm",
  LIST_CONJ [nwalkstar_nom,nwalkstar_var,nwalkstar_tie,nwalkstar_pair,nwalkstar_const]
  |> SIMP_RULE bool_ss [GSYM IMP_CONJ_THM])

val noc_ignores_pi = Q.store_thm(
"noc_ignores_pi",
`nwfs s ⇒ ∀t. (noc s (apply_pi pi t) v ⇔ noc s t v)`,
STRIP_TAC THEN Induct THEN SRW_TAC [][])

val noc_if_nvars_nwalkstar = Q.prove(
`nwfs s ==> !t. v IN nvars (nwalk* s t) ==> noc s t v`,
DISCH_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `nvwalk s l n` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
  SRW_TAC [][] THEN Cases_on `nvwalk s [] n` THEN FULL_SIMP_TAC (srw_ss()) [],
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
  Cases_on `nvwalk s [] n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN METIS_TAC [noc_ignores_pi],
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
  SRW_TAC [][] THEN
  Cases_on `nvwalk s [] n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [noc_ignores_pi],
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
  SRW_TAC [][] THEN
  Cases_on `nvwalk s [] n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [noc_ignores_pi]
])

val NOT_FDOM_nwalkstar = Q.store_thm(
"NOT_FDOM_nwalkstar",
`nwfs s ==> !t. v NOTIN FDOM s ==> v IN nvars t ==> v IN nvars (nwalk* s t)`,
DISCH_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN SRW_TAC [][] THEN
Cases_on `t` THEN Cases_on `nvwalk s l n` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `n NOTIN FDOM s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [Once nvwalk_def,FLOOKUP_DEF] THEN
SRW_TAC [][])

val noc_NOTIN_FDOM = Q.store_thm(
  "noc_NOTIN_FDOM",
  `nwfs s ==> !t v. noc s t v ==> v NOTIN FDOM s`,
  STRIP_TAC THEN HO_MATCH_MP_TAC noc_ind THEN SRW_TAC [] [])

val nvars_nwalkstar_ignores_pi = Q.store_thm(
"nvars_nwalkstar_ignores_pi",
`nwfs s ⇒ ∀t pi. nvars (nwalkstar s t) = nvars (nwalkstar s (apply_pi pi t))`,
STRIP_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
SRW_TAC [][] THEN
REVERSE (Cases_on `t`) THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (psrw_ss()) [] THEN1 METIS_TAC [] THEN
(nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
(nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`pi++l`,`n`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `nvwalk s [] n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [apply_pi_decompose] THEN
METIS_TAC [])

val nvars_nwalkstar_if_noc = Q.prove(
`nwfs s ==> !t v. noc s t v ==> v IN nvars (nwalkstar s t)`,
STRIP_TAC THEN HO_MATCH_MP_TAC noc_strong_ind THEN SRW_TAC [] [] THEN1
  METIS_TAC [NOT_FDOM_nwalkstar] THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SPEC_ALL_TAC [] THEN
Induct_on `t` THEN SRW_TAC [][] THEN1 (
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`l`,`n`] MP_TAC) THEN
  STRIP_TAC THEN
  Cases_on `nvwalk s [] n` THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    IMP_RES_TAC nvwalk_to_var THEN
    IMP_RES_TAC NOT_FDOM_nvwalk THEN
    FULL_SIMP_TAC (srw_ss()) []) THEN
  METIS_TAC [nvars_nwalkstar_ignores_pi] ) THEN
METIS_TAC []
)

val noc_eq_nvars_nwalkstar = Q.store_thm(
  "noc_eq_nvars_nwalkstar",
  `nwfs s ==> (noc s t v ⇔ v ∈ nvars (nwalk* s t))`,
  SRW_TAC [][FUN_EQ_THM] THEN
  METIS_TAC [nvars_nwalkstar_if_noc,noc_if_nvars_nwalkstar,IN_DEF])

val nvwalk_EQ_nom_nvR = Q.prove(
`!v u. (nvR s)^+ v u ⇒ v NOTIN FDOM s ∧ nwfs s ⇒
     !p a. nvwalk s p u ≠ Nom a`,
HO_MATCH_MP_TAC TC_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [nvR_def] THENL [
  Cases_on `FLOOKUP s u`,
  Cases_on `FLOOKUP s u'`
] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][Once nvwalk_def] THEN Cases_on `x` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][NOT_FDOM_nvwalk,nvwalk_case_thms])

val nvwalk_EQ_var_nvR = Q.prove(
  `nwfs s ==> !p u p1 v1 v2. (nvwalk s p u = Sus p1 v1) /\ (nvR s)^+ v2 u /\
                        v2 NOTIN FDOM s ==> (v1 = v2)`,
  STRIP_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN SRW_TAC [][] THEN
  IMP_RES_TAC TC_CASES2 THEN
  FULL_SIMP_TAC (srw_ss()) [nvR_def] THEN
  Cases_on `FLOOKUP s u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nvwalk s p u = UU` MP_TAC THEN
  SRW_TAC [][Once nvwalk_def] THEN
  Cases_on `x` THEN
  POP_ASSUM MP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_nvwalk] THEN
  SELECT_ELIM_TAC THEN SRW_TAC [][] THEN
  METIS_TAC [permeq_sym])

val nvwalk_EQ_const_nvR = prove(
  ``!v u. (nvR s)^+ v u ==> v NOTIN FDOM s /\ nwfs s ==>
          !p c. nvwalk s p u <> nConst c``,
  HO_MATCH_MP_TAC TC_INDUCT_RIGHT1 THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [nvR_def] THEN
    Cases_on `FLOOKUP s u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][Once nvwalk_def] THEN Cases_on `x` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][NOT_FDOM_nvwalk,nvwalk_case_thms],
    FULL_SIMP_TAC (srw_ss()) [nvR_def] THEN
    Cases_on `FLOOKUP s u'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][Once nvwalk_def] THEN Cases_on `x` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][NOT_FDOM_nvwalk,nvwalk_case_thms]
  ])

val nvwalk_EQ_tie_nvR = Q.prove(
`!v u. (nvR s)^+ v u ⇒
   !a t p. v NOTIN FDOM s ∧ nwfs s ∧ (nvwalk s p u = Tie a t) ⇒
           ∃u. (u IN nvars t) ∧ (nvR s)^* v u`,
HO_MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [nvR_def] THENL [
  Cases_on `FLOOKUP s u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nvwalk s p u = XXX` MP_TAC THEN
  SRW_TAC [][Once nvwalk_def] THEN
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    POP_ASSUM MP_TAC THEN
    SRW_TAC [][NOT_FDOM_nvwalk,nvwalk_case_thms],
    Q.EXISTS_TAC `v` THEN SRW_TAC [][]
  ],
  Cases_on `FLOOKUP s u'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nvwalk s p u' = XXX` MP_TAC THEN
  SRW_TAC [][Once nvwalk_def] THEN
  POP_ASSUM MP_TAC THEN
  Cases_on `x` THEN SRW_TAC [][nvwalk_case_thms]
  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [TC_RTC]
])

val nvwalk_EQ_pair_nvR = prove(
  ``!v u. (nvR s)^+ v u ==>
          !t1 t2 p. v NOTIN FDOM s /\ nwfs s /\ (nvwalk s p u = nPair t1 t2) ==>
                  ?u. (u IN nvars t1 \/ u IN nvars t2) /\ (nvR s)^* v u``,
  HO_MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [nvR_def] THENL [
    Cases_on `FLOOKUP s u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.PAT_ASSUM `nvwalk s p u = XXX` MP_TAC THEN
    SRW_TAC [][Once nvwalk_def] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      POP_ASSUM MP_TAC THEN
      SRW_TAC [][NOT_FDOM_nvwalk,nvwalk_case_thms],
      Q.EXISTS_TAC `v` THEN SRW_TAC [][],
      Q.EXISTS_TAC `v` THEN SRW_TAC [][]
    ],
    Cases_on `FLOOKUP s u'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.PAT_ASSUM `nvwalk s p u' = XXX` MP_TAC THEN
    SRW_TAC [][Once nvwalk_def] THEN
    POP_ASSUM MP_TAC THEN
    Cases_on `x` THEN SRW_TAC [][nvwalk_case_thms]
    THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [TC_RTC]
  ])

val TC_nvR_nvars_nwalkstar = Q.store_thm(
  "TC_nvR_nvars_nwalkstar",
   `nwfs s ==>
   !t v u. (nvR s)^+ v u /\ v NOTIN FDOM s /\ u IN nvars t ==>
           v IN nvars (nwalkstar s t)`,
  STRIP_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN SRW_TAC [][] THEN
  REVERSE (Cases_on `t`) THEN Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN
  Cases_on `nvwalk s l n` THEN SRW_TAC [][] THENL [
    METIS_TAC [nvwalk_EQ_nom_nvR],
    IMP_RES_TAC nvwalk_EQ_var_nvR THEN
    SRW_TAC [][],
    IMP_RES_TAC nvwalk_EQ_tie_nvR THEN
    `(u = v) ∨ (nvR s)^+ v u`
    by METIS_TAC [EXTEND_RTC_TC_EQN,RTC_CASES1] THEN
    FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_nwalkstar] THEN
    METIS_TAC [],
    Q.MATCH_RENAME_TAC `v IN nvars (nwalkstar s t1) ∨ v IN nvars (nwalkstar s t2)` [] THEN
    `?u. u IN nvars (nPair t1 t2) /\ (nvR s)^* v u`
       by (SRW_TAC [][] THEN METIS_TAC [nvwalk_EQ_pair_nvR]) THEN
    `(u = v) \/ (nvR s)^+ v u`
       by METIS_TAC [EXTEND_RTC_TC_EQN, RTC_CASES1] THEN
    FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_nwalkstar] THEN
    METIS_TAC [],
    METIS_TAC [nvwalk_EQ_const_nvR]
  ])

val noc_TC_nvR = Q.store_thm(
"noc_TC_nvR",
`∀t v. noc s t v ⇒ nwfs s ⇒ ∃u. u ∈ nvars t ∧ (nvR s)^* v u`,
HO_MATCH_MP_TAC noc_ind THEN SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `v` THEN SRW_TAC [][RTC_REFL] ) THEN
RES_TAC THEN
Cases_on `u = u'` THEN1 METIS_TAC [] THEN
Q_TAC SUFF_TAC `(nvR s)^+ u' u` THEN1 (
  SRW_TAC [][] THEN Q.EXISTS_TAC `u` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [RTC_CASES_TC] THEN SRW_TAC [][] THEN
  METIS_TAC [TC_RULES] ) THEN
MATCH_MP_TAC (UNDISCH nvwalk_nvR) THEN
`nvwalk s [] u ≠ Sus [] u` by (
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
METIS_TAC [])

val nwalkstar_SUBMAP = Q.store_thm(
"nwalkstar_SUBMAP",
`s ⊑ sx ∧ nwfs sx ⇒ (nwalk* sx t = nwalk* sx (nwalk* s t))`,
SRW_TAC [][] THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP] THEN
Q.ID_SPEC_TAC `t` THEN
HO_MATCH_MP_TAC nwalkstar_ind THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
Cases_on `nwalk s t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.MATCH_ABBREV_TAC `X = Y (nwalk* s t)` THEN
SRW_TAC [][Once nwalkstar_def] THEN
UNABBREV_ALL_TAC THEN
SRW_TAC [][Once nwalkstar_def,SimpLHS] THEN
MP_TAC nwalk_SUBMAP THEN
SRW_TAC [][] THEN
POP_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
ASM_SIMP_TAC (psrw_ss()) [])

val nwalkstar_idempotent = Q.store_thm(
"nwalkstar_idempotent",
`nwfs s ==> !t.(nwalkstar s t = nwalkstar s (nwalkstar s t))`,
METIS_TAC [nwalkstar_SUBMAP,SUBMAP_REFL])

val nwalkstar_FEMPTY = RWstore_thm(
"nwalkstar_FEMPTY",
`nwalk* (FEMPTY) t = t`,
Induct_on `t` THEN ASM_SIMP_TAC (psrw_ss()) [])

val NOT_FDOM_nwalkstar = Q.store_thm(
"NOT_FDOM_nwalkstar",
`nwfs s ==> !t. v NOTIN FDOM s ==> v IN nvars t ==> v IN nvars (nwalk* s t)`,
DISCH_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
SRW_TAC [][] THEN Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [Once nvwalk_def, nvars_def, FLOOKUP_DEF])

val nwalkstar_nwalk = Q.store_thm(
"nwalkstar_nwalk",
`nwfs s ==> (nwalk* s (nwalk s t) = nwalk* s t)`,
Cases_on `t` THEN SRW_TAC [][] THEN
Cases_on `nvwalk s l n` THEN ASM_SIMP_TAC (psrw_ss()) [] THEN
`nvwalk s l' n' = Sus l' n'` by METIS_TAC [nvwalk_to_var,NOT_FDOM_nvwalk] THEN
ASM_SIMP_TAC (psrw_ss()) [])

val nwalkstar_to_var = Q.store_thm(
"nwalkstar_to_var",
`(nwalk* s t = Sus pi v) ∧ nwfs s ⇒ v NOTIN FDOM s ∧ ∃pu u. t = Sus pu u`,
STRIP_TAC THEN
IMP_RES_TAC (GSYM nwalkstar_nwalk) THEN
POP_ASSUM (Q.SPEC_THEN `t` ASSUME_TAC) THEN
Cases_on `nwalk s t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC nwalk_to_var THEN
IMP_RES_TAC NOT_FDOM_nvwalk THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][])

val nwalkstar_apply_pi = Q.store_thm(
"nwalkstar_apply_pi", (* Lemma 2.14.0*)
`nwfs s ⇒ ∀t.nwalk* s (apply_pi pi t) = apply_pi pi (nwalk* s t)`,
STRIP_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
STRIP_TAC THEN Cases_on `t` THEN
ASM_SIMP_TAC (psrw_ss()) [] THEN
SRW_TAC [][] THEN
(nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> MP_TAC) THEN
(nvwalk_modulo_pi |> Q.SPECL [`s`,`pi++l`,`n`] |> MP_TAC) THEN
SRW_TAC [][] THEN Cases_on `nvwalk s [] n` THEN
FULL_SIMP_TAC (psrw_ss()) [lswapstr_decompose, apply_pi_decompose]);

val _ = export_theory ()
