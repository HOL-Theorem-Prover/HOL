open HolKernel boolLib bossLib Parse relationTheory finite_mapTheory
     listTheory pred_setTheory apply_piTheory ntermTheory nsubstTheory
     nomsetTheory listTheory ramanaLib ntermLib

val _ = new_theory "nwalk"

val pre_nvwalk_def = TotalDefn.xDefineSchema "pre_nvwalk"
 `nvwalk pi v =
    case FLOOKUP s v
    of SOME (Sus p u) -> nvwalk (pi ++ p) u
    || SOME t -> apply_pi pi t
    || NONE -> Sus pi v`

val _ = store_term_thm("nvwalk_def_print",
TermWithCase`
nwfs s ⇒
  (nvwalk s pi v =
   case FLOOKUP s v
   of SOME (Sus p u) -> nvwalk s (pi ++ p) u
   || SOME t -> apply_pi pi t
   || NONE -> Sus pi v)`)

fun nvwalk_nwfs_hyp th =
let val th =
  Q.INST [`R` |-> `inv_image (nvR s) SND`] th
in
  foldl (fn (h,th) => PROVE_HYP h th) th
    (map
      (UNDISCH o
      (fn t => prove (``nwfs s ==> ^t``,
                      SIMP_TAC (srw_ss()) [nwfs_def,WF_inv_image] THEN
                      SRW_TAC [][inv_image_def,nvR_def])))
      (hyp th))
end

val nvwalk_def = save_thm("nvwalk_def",pre_nvwalk_def |> nvwalk_nwfs_hyp |> DISCH_ALL)
val nvwalk_ind = save_thm("nvwalk_ind",nvwalk_nwfs_hyp (theorem "pre_nvwalk_ind"))

val NOT_FDOM_nvwalk = Q.store_thm(
  "NOT_FDOM_nvwalk",
  `nwfs s /\ v NOTIN FDOM s ==> (nvwalk s p v = Sus p v)`,
  SRW_TAC [] [Once nvwalk_def, FLOOKUP_DEF,permeq_refl])

val pmact_permeq' = pmact_permeq |> UNDISCH |> REWRITE_RULE [FUN_EQ_THM]
                                 |> SPEC_ALL |> DISCH_ALL

val nvwalk_Vf = Q.store_thm(
"nvwalk_Vf",
`nwfs s ⇒ ∀p1 u p2. p1 == p2 ⇒ (nvwalk s p1 u = nvwalk s p2 u)`,
STRIP_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP s u` THEN1
  (REPEAT (POP_ASSUM MP_TAC) THEN
   REPEAT (SRW_TAC [] [Once nvwalk_def, FLOOKUP_DEF])) THEN
SRW_TAC [][Once nvwalk_def,SimpLHS] THEN
SRW_TAC [][Once nvwalk_def,SimpRHS] THEN
Cases_on `x` THEN SRW_TAC [][pmact_permeq'] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `@p'.p'==l` MP_TAC) THEN
`l == (@p'.p'==l)` by (SELECT_ELIM_TAC THEN METIS_TAC [permeq_refl,permeq_sym]) THEN
SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
MATCH_MP_TAC app_permeq_monotone THEN SRW_TAC [][])

val nvwalk_case_thms = save_thm("nvwalk_case_thms",LIST_CONJ [Sus_case2,nvwalk_Vf,app_permeq_monotone])

val nvwalk_to_var = Q.store_thm(
  "nvwalk_to_var",
  `nwfs s ==> !pv v p2 u. (nvwalk s pv v = Sus p2 u) ==> u NOTIN FDOM s`,
  DISCH_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN
  SRW_TAC [][] THEN
  Cases_on `FLOOKUP s v` THEN1
    (REPEAT (POP_ASSUM MP_TAC) THEN
     REPEAT (SRW_TAC [] [Once nvwalk_def, FLOOKUP_DEF])) THEN
  `?pw w.x = Sus pw w`
     by (Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [Once (UNDISCH nvwalk_def)]
     THEN METIS_TAC [permeq_refl]) THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`pw`,`w`] MP_TAC) THEN SRW_TAC [][] THEN
  `nvwalk s (pv ++ pw) w = Sus p2 u`
  by (Q.PAT_ASSUM `nvwalk s pv v = X` MP_TAC THEN
      SRW_TAC [] [Once nvwalk_def,nvwalk_case_thms]) THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [])

val nvwalk_nvR = Q.store_thm(
"nvwalk_nvR",
`nwfs s ==> !p v u. u IN nvars (nvwalk s p v) /\ nvwalk s p v ≠ Sus p v ==>
           (nvR s)^+ u v`,
DISCH_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN SRW_TAC [][] THEN
`(FLOOKUP s v = NONE) \/ ?t. FLOOKUP s v = SOME t`
   by (Cases_on `FLOOKUP s v` THEN SRW_TAC [][]) THEN1
(`nvwalk s p v = Sus p v` by (ONCE_REWRITE_TAC [UNDISCH nvwalk_def] THEN
 SRW_TAC [][])) THEN
Cases_on `t` THENL [
  FULL_SIMP_TAC (srw_ss()) [Once(UNDISCH nvwalk_def)],
  `nvwalk s p v = nvwalk s (p++l) n` by
  (SRW_TAC [][Once nvwalk_def,nvwalk_case_thms]) THEN
  `nvR s n v` by SRW_TAC [][nvR_def] THEN
  Cases_on `nvwalk s (p ++ l) n = Sus (p ++ l) n` THENL [
    `u = n` by FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][TC_SUBSET],
    `(nvR s)^+ u n` by METIS_TAC [] THEN
    MATCH_MP_TAC (GEN_ALL (CONJUNCT2 (SPEC_ALL TC_RULES))) THEN
    METIS_TAC [TC_SUBSET]
  ],
  `∃a t. nvwalk s p v = Tie a t` by (SRW_TAC [][Once nvwalk_def]) THEN
  POP_ASSUM MP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [Once(UNDISCH nvwalk_def)] THEN
  STRIP_TAC THEN
  `u IN nvars t` by METIS_TAC [nvars_apply_pi] THEN
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][nvR_def],
  Q.MATCH_ASSUM_RENAME_TAC `FLOOKUP s v = SOME (nPair t1 t2)` [] THEN
  `∃pi. nvwalk s p v = apply_pi pi (nPair t1 t2)` by (SRW_TAC [][Once nvwalk_def] THEN METIS_TAC []) THEN
  `u IN nvars (nPair t1 t2)` by METIS_TAC [nvars_apply_pi] THEN
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][nvR_def] THEN FULL_SIMP_TAC (srw_ss()) [],
  Q.MATCH_ASSUM_RENAME_TAC `FLOOKUP s v = SOME (nConst c)` [] THEN
  `nvwalk s p v = nConst c` by (SRW_TAC [] [Once nvwalk_def]) THEN
  FULL_SIMP_TAC (srw_ss()) []
]);

val nwalk_def_q = `nwalk s t = case t of Sus p v -> nvwalk s p v || _ -> t`

val nwalk_def = Define nwalk_def_q

val _ = store_term_thm ("nwalk_def_print", TermWithCase nwalk_def_q)

val nwalk_thm = RWstore_thm(
"nwalk_thm",
`nwfs s ⇒
 (nwalk s (Nom a) = (Nom a)) ∧
 (nwalk s (Sus p v) = nvwalk s p v) ∧
 (nwalk s (Tie a t) = (Tie a t)) ∧
 (nwalk s (nPair t1 t2) = (nPair t1 t2)) ∧
 (nwalk s (nConst c) = (nConst c))`,
SRW_TAC [][nwalk_def,nvwalk_case_thms]);

val nwalk_to_var = Q.store_thm(
"nwalk_to_var",
`(nwalk s t = Sus p v) ∧ nwfs s ==>
   v NOTIN FDOM s /\ ?pu u.(t = Sus pu u)`,
STRIP_TAC THEN Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [nvwalk_to_var]);

val nwalk_FEMPTY = RWstore_thm(
"nwalk_FEMPTY",
`(nwalk FEMPTY t = t) /\
 (nvwalk FEMPTY p v = Sus p v)`,
Cases_on `t` THEN REPEAT (SRW_TAC [][Once(DISCH_ALL nvwalk_def),permeq_refl]))

val nvwalk_modulo_pi = Q.store_thm(
"nvwalk_modulo_pi",
`∀s pi v. nwfs s ⇒ (nvwalk s pi v = apply_pi pi (nvwalk s [] v))`,
REPEAT STRIP_TAC THEN Q_TAC SUFF_TAC
`∀pi1 v pi2.
∃t. (nvwalk s pi1 v = apply_pi pi1 t) ∧
    (nvwalk s pi2 v = apply_pi pi2 t)`
THEN1 (
  SRW_TAC [][] THEN
  POP_ASSUM (Q.SPECL_THEN [`pi`,`v`,`[]`] MP_TAC) THEN
  SRW_TAC [][]) THEN
HO_MATCH_MP_TAC nvwalk_ind THEN SRW_TAC [][] THEN
Cases_on `FLOOKUP s v` THEN1
  (NTAC 2 (SRW_TAC [] [Once nvwalk_def]) THEN
   Q.EXISTS_TAC `Sus [] v` THEN ASM_SIMP_TAC (psrw_ss()) []) THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [Once nvwalk_def,nvwalk_case_thms] THEN
Q.HO_MATCH_ABBREV_TAC `∃t. X t ∧ Y t` THEN
Q.UNABBREV_TAC `Y` THEN
SRW_TAC [] [Once nvwalk_def,nvwalk_case_thms] THEN
Q.UNABBREV_TAC `X` THEN
POP_ASSUM MP_TAC THEN
Q.MATCH_ABBREV_TAC `(FLOOKUP s v = SOME aterm) ⇒ X` THEN
STRIP_TAC THEN Q.UNABBREV_TAC`X` THEN
TRY (Q.EXISTS_TAC `aterm` THEN SRW_TAC [][Abbr`aterm`] THEN NO_TAC) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `(pi2++l)` MP_TAC) THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `apply_pi l t` THEN SRW_TAC [][apply_pi_decompose]);

val nvars_nvwalk_ignores_pi = Q.store_thm(
"nvars_nvwalk_ignores_pi",
`nwfs s ⇒
 ∀p1 v p2. nvars (nvwalk s p1 v) = nvars (nvwalk s p2 v)`,
STRIP_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  SRW_TAC [][Once nvwalk_def] THEN SRW_TAC [][Once nvwalk_def]) THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
  SRW_TAC [][Once nvwalk_def] THEN SRW_TAC [][Once nvwalk_def],
  SRW_TAC [][Once nvwalk_def,nvwalk_case_thms] THEN
  SRW_TAC [][Once nvwalk_def,nvwalk_case_thms,SimpRHS],
  SRW_TAC [][Once nvwalk_def] THEN SRW_TAC [][Once nvwalk_def],
  SRW_TAC [][Once nvwalk_def] THEN SRW_TAC [][Once nvwalk_def],
  SRW_TAC [][Once nvwalk_def] THEN SRW_TAC [][Once nvwalk_def]
])

val nvwalk_FDOM = Q.store_thm(
"nvwalk_FDOM",
`nwfs s ==> (nvwalk s p v = t) ==>
  (v ∉ FDOM s /\ (t = Sus p v)) \/
  (v IN FDOM s /\ (!pv. t ≠ Sus pv v) /\
   ?u pu tu.(nvwalk s p v = nvwalk s pu u) ∧
            (FLOOKUP s u = SOME tu) ∧ (t = apply_pi pu tu))`,
REVERSE (Cases_on `v IN FDOM s`)
THEN1 METIS_TAC [NOT_FDOM_nvwalk] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `v IN FDOM s` MP_TAC THEN
Q.PAT_ASSUM `nvwalk s p v = t` MP_TAC THEN
MAP_EVERY Q.ID_SPEC_TAC [`v`,`p`] THEN
HO_MATCH_MP_TAC nvwalk_ind THEN
REPEAT (GEN_TAC ORELSE STRIP_TAC) THEN
ASM_SIMP_TAC (srw_ss()) [] THEN
Cases_on `FLOOKUP s v`
  THEN1 (POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF]) THEN
`x = s ' v` by (POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF]) THEN
Cases_on `s ' v` THENL [
  `nvwalk s p v = apply_pi p x` by SRW_TAC [][Once nvwalk_def,FLOOKUP_DEF]
  THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  MAP_EVERY Q.EXISTS_TAC [`v`,`p`] THEN SRW_TAC [][] THEN METIS_TAC [],
  `nvwalk s p v = nvwalk s (p ++ l) n`
     by SRW_TAC [][Once nvwalk_def,SimpLHS,nvwalk_case_thms] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THENL [
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    Q_TAC SUFF_TAC `n = v` THEN1 METIS_TAC [] THEN
    REVERSE (Cases_on `n IN FDOM s`)
     THEN1 METIS_TAC [NOT_FDOM_nvwalk,ntermeq_thm] THEN
    `∀pn. nvwalk s (p ++ l) n <> Sus pn n` by METIS_TAC [] THEN
    `v IN nvars (nvwalk s (p++l) n)` by METIS_TAC [IN_INSERT,nvars_def] THEN
    `(nvR s)^+ v n` by METIS_TAC [nvwalk_nvR] THEN
    `nvR s n v` by FULL_SIMP_TAC (srw_ss()) [nvR_def] THEN
    `(nvR s)^+ n n` by METIS_TAC [TC_RULES] THEN
    METIS_TAC [nwfs_no_cycles],
    Cases_on `n IN FDOM s` THEN1 METIS_TAC [] THEN
    `nvwalk s p v = Sus (p ++ l) n` by METIS_TAC [NOT_FDOM_nvwalk] THEN
    MAP_EVERY Q.EXISTS_TAC [`v`,`p`] THEN
    ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,FLOOKUP_DEF] THEN
    SRW_TAC [][Once nvwalk_def,FLOOKUP_DEF]
  ],
  `nvwalk s p v = apply_pi p x` by SRW_TAC [][Once nvwalk_def,FLOOKUP_DEF]
  THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  MAP_EVERY Q.EXISTS_TAC [`v`,`p`] THEN SRW_TAC [][]
  THEN METIS_TAC [],
  `nvwalk s p v = apply_pi p x` by SRW_TAC [][Once nvwalk_def,FLOOKUP_DEF]
  THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  MAP_EVERY Q.EXISTS_TAC [`v`,`p`] THEN SRW_TAC [][]
  THEN METIS_TAC [],
  `nvwalk s p v = apply_pi p x` by SRW_TAC [][Once nvwalk_def,FLOOKUP_DEF]
  THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  MAP_EVERY Q.EXISTS_TAC [`v`,`p`] THEN SRW_TAC [][]
  THEN METIS_TAC []
])

val nvars_nvwalk_SUBSET_FRANGE = Q.store_thm(
"nvars_nvwalk_SUBSET_FRANGE",
`nwfs s ∧ v IN FDOM s ⇒ nvars (nvwalk s p v) SUBSET BIGUNION (FRANGE (nvars o_f s))`,
STRIP_TAC THEN
Q_TAC SUFF_TAC `∃pi t2. (nvwalk s p v = apply_pi pi t2) ∧ t2 IN FRANGE s`
THEN1 METIS_TAC [o_f_FRANGE,nvars_apply_pi,SUBSET_BIGUNION_I] THEN
METIS_TAC [FRANGE_FLOOKUP,nvwalk_FDOM]);

val nvwalk_eq_perms = Q.store_thm(
"nvwalk_eq_perms",
`nwfs s ⇒ p1 == p2 ⇒ (nvwalk s p1 v = nvwalk s p2 v)`,
Q_TAC SUFF_TAC
`nwfs s ⇒ ∀p1 v p2. p1 == p2 ⇒ (nvwalk s p1 v = nvwalk s p2 v)`
THEN1 METIS_TAC [] THEN
STRIP_TAC THEN HO_MATCH_MP_TAC nvwalk_ind THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  SRW_TAC [][Once nvwalk_def] THEN
  SRW_TAC [][Once nvwalk_def] ) THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
NTAC 2 (SRW_TAC [][Once nvwalk_def,nvwalk_case_thms]))
val _ = export_permweakening "nvwalk_eq_perms"

val nvwalk_SUBMAP = Q.store_thm(
"nvwalk_SUBMAP",
`nwfs sx ==> !p v s.s SUBMAP sx ==>
 ¬ is_Sus (nvwalk s p v) ⇒
 (nvwalk s p v = nvwalk sx p v)`,
STRIP_TAC THEN HO_MATCH_MP_TAC (Q.INST[`s`|->`sx`]nvwalk_ind) THEN
SRW_TAC [][] THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP] THEN
SRW_TAC [][Once nvwalk_def,SimpLHS] THEN
FULL_SIMP_TAC (srw_ss()) [Once nvwalk_def] THEN
Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) []
THEN1 METIS_TAC [permeq_refl] THEN
IMP_RES_TAC FLOOKUP_SUBMAP THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
TRY (SRW_TAC [][Once nvwalk_def] THEN NO_TAC) THEN
SRW_TAC [][Once nvwalk_def,SimpRHS,nvwalk_case_thms]);

val nvwalk_SUBMAP_var = Q.store_thm(
"nvwalk_SUBMAP_var",
`nwfs sx ==> !p v s.s SUBMAP sx ==>
 (nvwalk s p v = Sus pu u) ⇒
 (nvwalk sx p v = nvwalk sx pu u)`,
STRIP_TAC THEN HO_MATCH_MP_TAC (Q.INST[`s`|->`sx`]nvwalk_ind) THEN
SRW_TAC [][] THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP] THEN
SRW_TAC [][Once nvwalk_def,SimpLHS] THEN
Cases_on `FLOOKUP sx v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF] THEN
  IMP_RES_TAC SUBMAP_DEF THEN
  `v NOTIN FDOM s` by METIS_TAC [] THEN
  IMP_RES_TAC NOT_FDOM_nvwalk THEN
  `Sus p v = Sus pu u` by METIS_TAC [] THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
Q.PAT_ASSUM `nvwalk s p v = Sus pu u` MP_TAC THEN
Q.MATCH_ABBREV_TAC `X ⇒ Y` THEN
Q.UNABBREV_TAC `X` THEN
SRW_TAC [][Once nvwalk_def] THEN
Q.UNABBREV_TAC `Y` THEN
Cases_on `FLOOKUP s v` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [nvwalk_case_thms] THEN
  TRY (SRW_TAC [][Once nvwalk_def] THEN NO_TAC) THEN
  SRW_TAC [][Once nvwalk_def,SimpRHS,nvwalk_case_thms, pmact_permeq'] ) THEN
IMP_RES_TAC FLOOKUP_SUBMAP THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `nvwalk s pi n = Sus pu u` MP_TAC THEN
SELECT_ELIM_TAC THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `x` MP_TAC) THEN
SRW_TAC [][] THEN METIS_TAC [permeq_sym]);

val nwalk_SUBMAP = Q.store_thm(
"nwalk_SUBMAP",
`nwfs sx ∧ s SUBMAP sx ⇒
 (¬is_Sus (nwalk s t) ⇒ (nwalk sx t = nwalk s t)) ∧
 (∀p v. (nwalk s t = Sus p v) ⇒ (nwalk sx t = nvwalk sx p v))`,
STRIP_TAC THEN
IMP_RES_TAC nwfs_SUBMAP THEN
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [nvwalk_SUBMAP] THEN
METIS_TAC [nvwalk_SUBMAP_var])

val _ = export_theory ();
