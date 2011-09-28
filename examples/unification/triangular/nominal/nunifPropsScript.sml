open HolKernel boolLib bossLib Parse stringTheory arithmeticTheory finite_mapTheory pred_setTheory bagTheory pairTheory relationTheory prim_recTheory quotientLib nomsetTheory listTheory ramanaLib ntermTheory nsubstTheory apply_piTheory nwalkTheory nwalkstarTheory nunifDefTheory dis_setTheory monadsyntax ntermLib

val _ = new_theory "nunifProps"
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 }

val _ = export_permweakening "dis_set.dis_set_eq_perms"

val fresh_q = `
  (fresh fe a (Nom b) = a ≠ b) ∧
  (fresh fe a (Sus pi v) = (lswapstr (REVERSE pi) a, v) ∈ fe) ∧
  (fresh fe a (Tie b t) = (a = b) ∨ a ≠ b ∧ fresh fe a t) ∧
  (fresh fe a (nPair t1 t2) = fresh fe a t1 ∧ fresh fe a t2) ∧
  (fresh fe a (nConst c) = T)`;
val def_suffix = !Defn.def_suffix;
val _ = Defn.def_suffix := "_def_with_choice";
val fresh_def_with_choice = Define fresh_q;
val _ = Defn.def_suffix := def_suffix;
val fresh_def = Q.store_thm("fresh_def",fresh_q,SIMP_TAC (psrw_ss()) [fresh_def_with_choice]);

val fresh_apply_pi = Q.store_thm(
"fresh_apply_pi",
`fresh fcs a t ⇒ fresh fcs (lswapstr pi a) (apply_pi pi t)`,
Induct_on `t` THEN ASM_SIMP_TAC (psrw_ss()) [fresh_def] THEN1 (
  SRW_TAC [][REVERSE_APPEND,pmact_decompose] ) THEN
SRW_TAC [][] THEN SRW_TAC [][])

val lemma27 = Q.store_thm( (* Lemma 2.7 - just consequences of the above, but good for metis *)
"lemma27",
`(∀t a pi fcs. fresh fcs a (apply_pi pi t) ⇒ fresh fcs (lswapstr (REVERSE pi) a) t) ∧
 (∀t a pi fcs. fresh fcs (lswapstr pi a) t ⇒ fresh fcs a (apply_pi (REVERSE pi) t)) ∧
 (∀t a pi fcs. fresh fcs a t ⇒ fresh fcs (lswapstr pi a) (apply_pi pi t))`,
SRW_TAC [][] THEN1 (
  IMP_RES_TAC fresh_apply_pi THEN
  POP_ASSUM (Q.SPEC_THEN `REVERSE pi` MP_TAC) THEN
  SRW_TAC [][] )
THEN1 (
  IMP_RES_TAC fresh_apply_pi THEN
  POP_ASSUM (Q.SPEC_THEN `REVERSE pi` MP_TAC) THEN
  SRW_TAC [][] )
THEN METIS_TAC [fresh_apply_pi])

val (equiv_rules,equiv_ind,equiv_cases) = Hol_reln`
  (equiv fcs (Nom a) (Nom a)) ∧
  ((∀a. a IN dis_set p1 p2 ⇒ (a,v) IN fcs) ⇒
   (equiv fcs (Sus p1 v) (Sus p2 v))) ∧
  (equiv fcs t1 t2 ⇒
   equiv fcs (Tie a t1) (Tie a t2)) ∧
  (a1 ≠ a2 ∧ fresh fcs a1 t2 ∧
   equiv fcs t1 (apply_pi [(a1,a2)] t2) ⇒
   equiv fcs (Tie a1 t1) (Tie a2 t2)) ∧
  (equiv fcs t1a t2a ∧ equiv fcs t1d t2d ⇒
   equiv fcs (nPair t1a t1d) (nPair t2a t2d)) ∧
  (equiv fcs (nConst c) (nConst c))`

val equiv_refl = RWstore_thm(
"equiv_refl",
`equiv fcs t t`,
Induct_on `t` THEN SRW_TAC [][]
THEN SRW_TAC [][Once equiv_cases] THEN
NTAC 2 (Q.EXISTS_TAC `l`) THEN
SRW_TAC [][dis_set_def])

val equiv_fresh = Q.store_thm( (* Lemma 2.9 *)
"equiv_fresh",
`equiv fe t1 t2 ∧ fresh fe a t1 ⇒ fresh fe a t2`,
MAP_EVERY Q.ID_SPEC_TAC [`t2`,`t1`] THEN
SIMP_TAC bool_ss [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC equiv_ind THEN
SRW_TAC [][] THEN
IMP_RES_TAC fresh_apply_pi THEN
FULL_SIMP_TAC (psrw_ss()) [fresh_def] THEN1 (
  Cases_on `lswapstr (REVERSE p2) a IN dis_set p1 p2`
  THEN FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  `lswapstr (REVERSE p1) (lswapstr p1 (lswapstr (REVERSE p2) a)) = lswapstr (REVERSE p1) a`
  by METIS_TAC [] THEN
  FULL_SIMP_TAC bool_ss [GSYM pmact_decompose] THEN
  FULL_SIMP_TAC (srw_ss()) [pmact_decompose]) THEN
Cases_on `a = a2` THEN
Q.PAT_ASSUM `a ≠ a1` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC fresh_apply_pi THEN
POP_ASSUM (Q.SPEC_THEN `REVERSE [(a1,a2)]` MP_TAC) THEN
ASM_SIMP_TAC (srw_ss()) [])

val equiv_apply_pi = Q.store_thm( (* equation 9, used for Theorem 2.11 *)
"equiv_apply_pi",
`equiv fe t1 t2 ⇒ equiv fe (apply_pi pi t1) (apply_pi pi t2)`,
Q_TAC SUFF_TAC
`∀t1 t2. equiv fe t1 t2 ⇒ ∀pi. equiv fe (apply_pi pi t1) (apply_pi pi t2)`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC equiv_ind THEN
SRW_TAC [][] THEN
ASM_SIMP_TAC (psrw_ss()) [] THEN
SRW_TAC [][Once equiv_cases] THEN1 (
  MAP_EVERY Q.EXISTS_TAC [`pi++p1`,`pi++p2`] THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  (dis_set_app_same_left |> EQ_IMP_RULE |> fst |> MATCH_MP_TAC) THEN
  SRW_TAC [][] )
THEN1 METIS_TAC [fresh_apply_pi] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `pi` MP_TAC) THEN
Q.MATCH_ABBREV_TAC `equiv fe X Y1 ⇒ equiv fe X Y2` THEN
Q_TAC SUFF_TAC `Y1 = Y2` THEN1 METIS_TAC [] THEN
MAP_EVERY Q.UNABBREV_TAC [`Y1`,`Y2`] THEN
SRW_TAC [][pmact_sing_to_back]);

val equiv_sym = Q.store_thm(
"equiv_sym",
`equiv fe t1 t2 ⇒ equiv fe t2 t1`,
MAP_EVERY Q.ID_SPEC_TAC [`t2`,`t1`] THEN
HO_MATCH_MP_TAC equiv_ind THEN
SRW_TAC [][] THEN1 (
  SRW_TAC [][Once equiv_cases]  THEN
  MAP_EVERY Q.EXISTS_TAC [`p2`,`p1`] THEN
  SRW_TAC [][] THEN METIS_TAC [dis_set_comm] )
THEN1 ( SRW_TAC [][Once equiv_cases] )
THEN1 (
  ASM_SIMP_TAC (srw_ss()) [Once equiv_cases] THEN
  `equiv fe (apply_pi [(a2,a1)] (apply_pi [(a1,a2)] t2)) (apply_pi [(a2,a1)] t1)`
  by (MATCH_MP_TAC equiv_apply_pi THEN SRW_TAC [][] ) THEN
  FULL_SIMP_TAC (srw_ss()) [pmact_flip_args] THEN
  MATCH_MP_TAC (GEN_ALL equiv_fresh) THEN
  Q.EXISTS_TAC `[(a1,a2)] · t2` THEN
  IMP_RES_TAC fresh_apply_pi THEN
  POP_ASSUM (Q.SPEC_THEN `[(a1,a2)]` MP_TAC) THEN
  SRW_TAC [][]) THEN
SRW_TAC [][Once equiv_cases])

val fresh_ds_equiv = Q.store_thm( (* Lemma 2.8 *)
"fresh_ds_equiv",
`(∀a. a IN (dis_set pi1 pi2) ⇒ (fresh fcs a t)) ⇒
 equiv fcs (apply_pi pi1 t) (apply_pi pi2 t)`,
MAP_EVERY Q.ID_SPEC_TAC [`pi2`,`pi1`,`t`] THEN
Induct THEN SRW_TAC [][fresh_def] THEN
FULL_SIMP_TAC (psrw_ss()) [dis_set_def] THEN
SRW_TAC [][Once equiv_cases] THEN1 (
  MAP_EVERY Q.EXISTS_TAC [`pi1 ++ l`,`pi2++l`] THEN
  SRW_TAC [][dis_set_def,pmact_decompose] THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []
) THEN
Cases_on `lswapstr pi2 s = lswapstr pi1 s` THEN SRW_TAC [][] THENL [
  FIRST_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][] THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
  (lemma27 |> CONJUNCT2 |> CONJUNCT1 |> Q.SPECL [`t`,`lswapstr pi1 s`,`REVERSE pi2`,`fcs`]
   |> SIMP_RULE (srw_ss()) [] |> MATCH_MP_TAC) THEN
  Q.MATCH_ABBREV_TAC `fresh fcs a t` THEN
  Q_TAC SUFF_TAC `lswapstr pi1 a ≠ lswapstr pi2 a ∧ a ≠ s` THEN1 METIS_TAC [] THEN
  UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN METIS_TAC [pmact_eql],
  SRW_TAC [][GSYM apply_pi_decompose] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
  Cases_on `a = s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  REVERSE (Cases_on `lswapstr pi1 a = lswapstr pi2 a`)
  THEN1 RES_TAC THEN
  Cases_on `lswapstr pi2 a = lswapstr pi1 s` THEN
  Cases_on `lswapstr pi2 a = lswapstr pi2 s` THEN
  FULL_SIMP_TAC (srw_ss()) []
])

val equiv_ds_fresh = Q.store_thm( (* 2.12.3 *)
"equiv_ds_fresh",
`equiv fe (apply_pi pi1 t) (apply_pi pi2 t) ∧ a IN dis_set pi1 pi2 ⇒ fresh fe a t`,
Q_TAC SUFF_TAC
`!t1 t2. equiv fe t1 t2 ⇒
!pi1 pi2 t a. (apply_pi pi1 t = t1) ∧ (apply_pi pi2 t = t2) ∧
a ∈ dis_set pi1 pi2 ⇒ fresh fe a t` THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC equiv_ind THEN
STRIP_TAC THEN1 (
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql,fresh_def,dis_set_def] THEN
  METIS_TAC [pmact_inverse] ) THEN
STRIP_TAC THEN1 (
  ASM_SIMP_TAC (srw_ss()) [apply_pi_eql,fresh_def] THEN
  SRW_TAC [][dis_set_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  `lswapstr (pi1⁻¹ ++ p1)⁻¹ = lswapstr (pi2⁻¹ ++ p2)⁻¹`
     by (MATCH_MP_TAC pmact_permeq THEN
         IMP_RES_TAC permof_REVERSE_monotone) THEN
  POP_ASSUM (fn th => SIMP_TAC bool_ss [SimpRHS, th]) THEN
  SRW_TAC [][pmact_decompose]) THEN
STRIP_TAC THEN1 (
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql,fresh_def,dis_set_def] THEN
  SRW_TAC [][] THEN
  Cases_on `a' = lswapstr (REVERSE pi2) a` THEN SRW_TAC [][]
  THEN METIS_TAC [] ) THEN
STRIP_TAC THEN1 (
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql,fresh_def,dis_set_def] THEN
  SRW_TAC [][] THEN
  Cases_on `a = lswapstr (REVERSE pi2) a2` THEN SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `fresh fe (lswapstr pi2 a) t2` THEN1 METIS_TAC [lemma27] THEN
  Cases_on `a1 = lswapstr pi2 a` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`pi1 ++ (REVERSE pi2)`,`[(a1,a2)]`,`lswapstr pi2 a`] MP_TAC) THEN
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_decompose,pmact_decompose] THEN
  STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
  Cases_on `a2 = lswapstr pi2 a` THEN1 (
    SRW_TAC [][] THEN FULL_SIMP_TAC (psrw_ss()) [] ) THEN
  SRW_TAC [][] ) THEN
STRIP_TAC THEN1 (
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql,fresh_def,dis_set_def] THEN
  METIS_TAC [] ) THEN
ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql,fresh_def,dis_set_def])

val equiv_trans_lemma = Q.store_thm(
"equiv_trans_lemma",
`equiv fe t1 t2 ∧ equiv fe t2 (apply_pi pi t2) ⇒ equiv fe t1 (apply_pi pi t2)`,
Q_TAC SUFF_TAC
`∀t1 t2. equiv fe t1 t2 ⇒ ∀pi. equiv fe t2 (apply_pi pi t2) ⇒ equiv fe t1 (apply_pi pi t2)`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC equiv_ind THEN
STRIP_TAC THEN1 SRW_TAC [][Once equiv_cases] THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC (psrw_ss()) [Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC (psrw_ss()) [Once equiv_cases] THEN
  STRIP_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`p1`,`pi++p2`] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  METIS_TAC [pmact_permeq] ) THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  SRW_TAC [][] THEN
  METIS_TAC [apply_pi_decompose] ) THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  SRW_TAC [][] THEN1 (
    Cases_on `lswapstr pi a1 = a1` THEN1 METIS_TAC [fresh_apply_pi] THEN
    Cases_on `lswapstr (REVERSE pi) a1 = a1` THEN1 (
      FULL_SIMP_TAC (srw_ss()) [pmact_eql] ) THEN
    MATCH_MP_TAC (GEN_ALL equiv_ds_fresh) THEN
    MAP_EVERY Q.EXISTS_TAC [`[]`,`REVERSE pi`] THEN
    SRW_TAC [][dis_set_def])
  THEN1 (
    `equiv fe (apply_pi [(a1,a2)] t2) (apply_pi [(a1,a2)] (apply_pi pi t2))`
    by METIS_TAC [equiv_apply_pi] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `(a1,a2)::pi ++ (REVERSE [(a1,a2)])` MP_TAC) THEN
    SIMP_TAC (srw_ss()) [apply_pi_decompose] THEN
    FULL_SIMP_TAC (srw_ss()) [GSYM apply_pi_decompose] ) THEN
  Cases_on `lswapstr pi a2 = a2` THEN
  Cases_on `lswapstr pi a2 = a1` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    `equiv fe (apply_pi [(a1,a2)] t2) (apply_pi [(a1,a2)] (apply_pi [(a2,a1)] (apply_pi pi t2)))`
    by METIS_TAC [equiv_apply_pi] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `pi ++ (REVERSE [(a1,a2)])` MP_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [apply_pi_decompose] THEN
    FULL_SIMP_TAC (srw_ss()) [pmact_flip_args]) THEN
  `fresh fe a1 (apply_pi [(a2,lswapstr pi a2)] (apply_pi pi t2))`
  by METIS_TAC [equiv_fresh] THEN
  `fresh fe (lswapstr (REVERSE [(a2,lswapstr pi a2)]) a1) (apply_pi pi t2)`
  by METIS_TAC [lemma27] THEN
  Q.PAT_ASSUM `lswapstr pi a2 ≠ a1` ASSUME_TAC THEN
  Q.PAT_ASSUM `a1 ≠ a2` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `(a1,lswapstr pi a2)::pi ++ (REVERSE [(a1,a2)])` MP_TAC) THEN
  SIMP_TAC (srw_ss()) [apply_pi_decompose] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM apply_pi_decompose] THEN
  STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC fresh_ds_equiv THEN
  `∀a. a ∈ dis_set [] ((a2,lswapstr pi a2)::pi) ⇒ fresh fe a t2`
  by (SRW_TAC [][] THEN MATCH_MP_TAC (GEN_ALL equiv_ds_fresh) THEN
      MAP_EVERY Q.EXISTS_TAC [`[]`,`((a2,lswapstr pi a2)::pi)`] THEN
      SRW_TAC [][] THEN METIS_TAC [dis_set_comm,equiv_sym] ) THEN
  FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  SRW_TAC [][] THEN
  Cases_on `a = a1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `a = a2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `a1 = lswapstr pi a` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `a2 = lswapstr pi a` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `lswapstr pi (lswapstr pi a) = a` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `lswapstr (REVERSE pi) a = a` THEN
  FULL_SIMP_TAC (srw_ss()) [pmact_eql] THEN
  `fresh fe (lswapstr (REVERSE pi) (lswapstr pi a)) (apply_pi (REVERSE pi) (apply_pi pi t2))`
  by METIS_TAC [lemma27] THEN
  FULL_SIMP_TAC (srw_ss()) []) THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once equiv_cases] ) THEN
SRW_TAC [][Once equiv_cases])

val equiv_trans = Q.store_thm(
"equiv_trans",
`equiv fe t1 t2 ∧ equiv fe t2 t3 ⇒ equiv fe t1 t3`,
Q_TAC SUFF_TAC
`∀t1 t2. equiv fe t1 t2 ⇒ ∀t3. equiv fe t2 t3 ⇒ equiv fe t1 t3`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC equiv_ind THEN
STRIP_TAC THEN1 (
  SRW_TAC [][Once equiv_cases] ) THEN
STRIP_TAC THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  SRW_TAC [][Once equiv_cases] THEN
  MAP_EVERY Q.EXISTS_TAC  [`p1`,`p2'`] THEN
  SRW_TAC [][] THEN
  `dis_set p1' p2' = dis_set p2 p2'`
  by METIS_TAC [dis_set_eq_perms,permeq_refl,permeq_sym] THEN
  FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  Cases_on `lswapstr p1 a ≠ lswapstr p2 a` THEN SRW_TAC [][] THEN
  Cases_on `lswapstr p2 a ≠ lswapstr p2' a` THEN SRW_TAC [][] THEN
  METIS_TAC [] ) THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once equiv_cases] ) THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN1 (
    IMP_RES_TAC equiv_fresh THEN
    SRW_TAC [][] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC equiv_apply_pi THEN
    SRW_TAC [][] ) THEN
  Cases_on `a2' = a1` THEN ASM_SIMP_TAC (srw_ss()) [] THEN1 (
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    `equiv fe ([(a1,a2)] · t2) ([(a1,a2)] · ([(a2,a1)] · t2'))`
      by ( MATCH_MP_TAC equiv_apply_pi THEN SRW_TAC [][]) THEN
    FULL_SIMP_TAC (srw_ss()) [pmact_flip_args]) THEN
  Q.MATCH_ASSUM_RENAME_TAC `a2 ≠ a3` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `fresh fe a2 t3` [] THEN
  CONJ1_TAC THEN1 (
    `equiv fe (apply_pi (REVERSE [(a2,a3)]) t2) (apply_pi (REVERSE [(a2,a3)]) (apply_pi [(a2,a3)] t3))`
    by METIS_TAC [equiv_apply_pi] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `fresh fe (lswapstr [(a2,a3)] a1) (apply_pi [(a2,a3)] t2)`
    by METIS_TAC [lemma27] THEN
    POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [equiv_fresh] ) THEN
  `equiv fe (apply_pi [(a1,a2)] t2) (apply_pi [(a1,a2)] (apply_pi [(a2,a3)] t3))`
  by (METIS_TAC [equiv_apply_pi]) THEN
  `dis_set [(a1,a3)] [(a1,a2);(a2,a3)] = {a1;a2}`
  by (SRW_TAC [][dis_set_def,EXTENSION] THEN
      Cases_on `x = a1` THEN SRW_TAC [][] THEN
      Cases_on `x = a2` THEN SRW_TAC [][] THEN
      Cases_on `x = a3` THEN SRW_TAC [][] ) THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  `equiv fe (apply_pi [(a1,a2);(a2,a3)] t3) (apply_pi [(a1,a3)] t3)`
  by METIS_TAC [fresh_ds_equiv,dis_set_comm] THEN
  `equiv fe (apply_pi [(a1,a2)] t2)
            (apply_pi ([(a1,a3)] ++ (REVERSE [(a1,a2);(a2,a3)]))
                      (apply_pi [(a1,a2);(a2,a3)] t3))` by
  (MATCH_MP_TAC equiv_trans_lemma THEN
   CONJ_TAC THEN1 FULL_SIMP_TAC (srw_ss()) [GSYM apply_pi_decompose] THEN
   SRW_TAC [][apply_pi_decompose]) THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [apply_pi_decompose]) THEN
STRIP_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once equiv_cases] ) THEN
SRW_TAC [][Once equiv_cases])

val fresh_extra_fcs = Q.store_thm(
"fresh_extra_fcs",
`fresh fe a t ∧ fe SUBSET fex ⇒ fresh fex a t`,
Induct_on `t` THEN SRW_TAC [][fresh_def] THEN METIS_TAC [SUBSET_DEF])

val term_fcs_FINITE = Q.store_thm(
"term_fcs_FINITE",
`(term_fcs a t = SOME fe) ⇒ FINITE fe`,
Q.ID_SPEC_TAC `fe` THEN
Induct_on `t` THEN
ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
SRW_TAC [][] THEN SRW_TAC [][])

val term_fcs_fresh = Q.store_thm(
"term_fcs_fresh",
`(term_fcs a t = SOME fe) ⇒ fresh fe a t`,
Q.ID_SPEC_TAC `fe` THEN Induct_on `t` THEN
ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def, fresh_def] THEN
SRW_TAC [][] THEN METIS_TAC [fresh_extra_fcs,SUBSET_UNION])

val term_fcs_minimal = Q.store_thm(
"term_fcs_minimal",
`(term_fcs a t = SOME fe) ∧ fresh fe' a t ⇒ fe SUBSET fe'`,
Q.ID_SPEC_TAC `fe` THEN Induct_on `t` THEN
ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def, fresh_def] THEN
SRW_TAC [][] THEN SRW_TAC [][])

val term_fcs_SOME = LIST_CONJ [term_fcs_FINITE,term_fcs_fresh,term_fcs_minimal]

val term_fcs_NONE = Q.store_thm(
"term_fcs_NONE",
`∀t fe. (term_fcs a t = NONE) ⇒ ∀fe. ¬fresh fe a t`,
Induct THEN SRW_TAC [][fresh_def] THEN
TRY (POP_ASSUM MP_TAC) THEN
SRW_TAC [][Once term_fcs_def] THEN
METIS_TAC [])

val fcs_acc_RECURSES = Q.store_thm(
"fcs_acc_RECURSES",
`FINITE t ⇒
 (ITSET (fcs_acc s) (e INSERT t) b =
  fcs_acc s e (ITSET (fcs_acc s) (t DELETE e) b))`,
STRIP_TAC THEN MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
SIMP_TAC (srw_ss()) [FORALL_PROD] THEN
SRW_TAC [][fcs_acc_def] THEN
MAP_EVERY Cases_on
[`z`,`term_fcs p_1 (nwalk* s (Sus [] p_2))`,`term_fcs p_1' (nwalk* s (Sus [] p_2'))`] THEN
SRW_TAC [][] THEN
METIS_TAC [UNION_ASSOC,UNION_COMM])

val unify_eq_vars_extends_fe = Q.store_thm(
"unify_eq_vars_extends_fe",
`FINITE ds ∧ (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ⇒ fe SUBSET fex`,
SRW_TAC [][unify_eq_vars_def] THEN
SRW_TAC [][SUBSET_UNION])

val image_lem = Q.prove(
`e NOTIN t ⇒ (IMAGE (λa. (a,v:num)) t DELETE (e,v) = IMAGE (λa. (a,v)) t)`,
SRW_TAC [][EXTENSION,EQ_IMP_THM])

val unify_eq_vars_FINITE = Q.store_thm(
"unify_eq_vars_FINITE",
`FINITE ds ∧ (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ FINITE fe ⇒ FINITE fex`,
Q_TAC SUFF_TAC
`∀ds. FINITE ds ⇒ ∀fe fex. (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ FINITE fe ⇒ FINITE fex`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SIMP_TAC (srw_ss()) [unify_eq_vars_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `X = SOME fex'` MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES,fcs_acc_def,image_lem] THEN
SRW_TAC [][] THEN METIS_TAC [FINITE_UNION,term_fcs_FINITE])

val unify_eq_vars_fresh = Q.store_thm(
"unify_eq_vars_fresh",
`FINITE ds ∧ (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ a ∈ ds ⇒
 fresh fex a (nwalk* s' (Sus [] v))`,
Q_TAC SUFF_TAC
`∀ds. FINITE ds ⇒ ∀fe fex. (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ a ∈ ds ⇒
 fresh fex a (nwalk* s' (Sus [] v))`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SIMP_TAC (srw_ss()) [unify_eq_vars_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `X = SOME fex'` MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES,fcs_acc_def,image_lem] THEN
SRW_TAC [][] THEN IMP_RES_TAC term_fcs_fresh THEN
METIS_TAC [fresh_extra_fcs,SUBSET_UNION,UNION_ASSOC])

val unify_eq_vars_minimal = Q.store_thm(
"unify_eq_vars_minimal",
`FINITE ds ∧ (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ c ∈ fex ⇒
 c ∈ fe ∨ c ∉ fe ∧ ∃a fcs. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧ a ∈ ds ∧ c ∈ fcs`,
Q_TAC SUFF_TAC
`∀ds. FINITE ds ⇒ ∀fe fex. (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ c ∈ fex ⇒
 c ∈ fe ∨ c ∉ fe ∧ ∃a fcs. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧ a ∈ ds ∧ c ∈ fcs`
THEN1 SRW_TAC [][] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SIMP_TAC (srw_ss()) [unify_eq_vars_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN SRW_TAC [][] THEN
Cases_on `c ∈ fe` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.PAT_ASSUM `X = SOME fex'` MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES,fcs_acc_def,image_lem] THEN
SRW_TAC [][] THEN METIS_TAC [UNION_COMM])

val unify_eq_vars_SOME = LIST_CONJ [unify_eq_vars_FINITE,unify_eq_vars_fresh,unify_eq_vars_minimal]

val unify_eq_vars_NONE = Q.store_thm(
"unify_eq_vars_NONE",
`FINITE ds ∧ (unify_eq_vars ds v (s,fe) = NONE) ⇒
 ∃a. a ∈ ds ∧ ∀fe. ¬ fresh fe a (nwalk* s (Sus [] v))`,
Q_TAC SUFF_TAC
`∀t. FINITE t ⇒ ∀fe. (unify_eq_vars t v (s,fe) = NONE) ⇒
  (∃a. a IN t ∧ ∀fex. ¬ fresh fex a (nwalk* s (Sus [] v)))`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][unify_eq_vars_def,ITSET_EMPTY] THEN
IMP_RES_TAC image_lem THEN POP_ASSUM (Q.SPEC_THEN `v` MP_TAC) THEN STRIP_TAC THEN
Q.PAT_ASSUM `FINITE t` ASSUME_TAC THEN
Q.PAT_ASSUM `a NOTIN t` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [fcs_acc_RECURSES,DELETE_NON_ELEMENT,fcs_acc_def] THEN
METIS_TAC [term_fcs_NONE])

val unify_eq_vars_decompose = Q.store_thm(
"unify_eq_vars_decompose",
`(unify_eq_vars (a INSERT ds) v (s,fe) = SOME (sx,fex)) ∧ FINITE ds ⇒
 ∃fe0 fcs.
 (unify_eq_vars ds v (s,fe) = SOME (s, fe0)) ∧
 (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧
 (fex = fe0 ∪ fcs)`,
SRW_TAC [][] THEN
Cases_on `a ∈ ds` THEN1 (
  FULL_SIMP_TAC (srw_ss()) [ABSORPTION] THEN
  IMP_RES_TAC unify_eq_vars_preserves_s THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_SOME THEN
  FULL_SIMP_TAC (srw_ss()) [ABSORPTION] THEN
  RES_TAC THEN
  Cases_on  `term_fcs a (nwalk* s (Sus [] v))` THEN1 (
    IMP_RES_TAC term_fcs_NONE ) THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC term_fcs_minimal THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF,EXTENSION] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [unify_eq_vars_def,fcs_acc_RECURSES,fcs_acc_def] THEN
`(a,v) ∉ IMAGE (λa. (a,v)) ds`
by (SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
METIS_TAC [UNION_ASSOC])

val unify_eq_vars_INSERT = Q.store_thm(
"unify_eq_vars_INSERT",
`(unify_eq_vars ds v (s,fe) = SOME (sx,fex)) ∧
 (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧
 FINITE ds ⇒
 (unify_eq_vars (a INSERT ds) v (s,fe) = SOME (s,fex ∪ fcs))`,
SRW_TAC [][unify_eq_vars_def,fcs_acc_RECURSES,fcs_acc_def] THEN
REVERSE (Cases_on `(a,v) ∈ IMAGE (λa. (a,v)) ds`) THEN1 (
  FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
  METIS_TAC [UNION_ASSOC]) THEN
`(a,v) INSERT (IMAGE (λa. (a,v)) ds DELETE (a,v)) = IMAGE (λa. (a,v)) ds`
by SRW_TAC [][] THEN
(fcs_acc_RECURSES |> Q.INST [`e`|->`(a,v)`,`t`|->`IMAGE (λa. (a,v)) ds DELETE (a,v)`,`b`|->`SOME {}`]
 |> SIMP_RULE (srw_ss()) [fcs_acc_def] |> MP_TAC) THEN
SRW_TAC [][] THEN SRW_TAC [][UNION_IDEMPOT,GSYM UNION_ASSOC])

val equiv_eq_perms = Q.store_thm(
"equiv_eq_perms",
`equiv fcs (Sus p1 v1) (Sus p2 v2) ∧ p1 == q1 ∧ p2 == q2 ⇒ equiv fcs (Sus q1 v1) (Sus q2 v2)`,
SRW_TAC [][Once equiv_cases] THEN
SRW_TAC [][Once equiv_cases] THEN
FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
METIS_TAC [pmact_permeq,permeq_sym])

val fresh_eq_perms = Q.store_thm(
"fresh_eq_perms",
`fresh fcs a (Sus p v) ∧ p == q ⇒ fresh fcs a (Sus q v)`,
ASM_SIMP_TAC (psrw_ss()) [fresh_def] THEN
METIS_TAC [pmact_eql,pmact_permeq])

val unify_eq_vars_equiv = Q.store_thm(
"unify_eq_vars_equiv",
`nwfs s ∧ (unify_eq_vars (dis_set pi1 pi2) v (s,fe) = SOME (s,fcs)) ⇒
 equiv fcs (nwalk* s (Sus pi1 v)) (nwalk* s (Sus pi2 v))`,
STRIP_TAC THEN
MP_TAC (Q.SPECL [`s`,`pi1`,`v`] (nvwalk_modulo_pi)) THEN
MP_TAC (Q.SPECL [`s`,`pi2`,`v`] (nvwalk_modulo_pi)) THEN
SRW_TAC [][] THEN
Cases_on `nvwalk s [] v` THEN FULL_SIMP_TAC (psrw_ss()) [] THENL [
  (fresh_ds_equiv |> Q.GEN `t` |> Q.SPEC `Nom s'` |> SIMP_RULE (srw_ss()) [] |> MATCH_MP_TAC) THEN
  `FINITE (dis_set pi1 pi2)` by SRW_TAC [][] THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_fresh THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][],
  ASM_SIMP_TAC (psrw_ss()) [] THEN
  Q_TAC SUFF_TAC `equiv fcs (Sus (pi1 ++ l) n) (Sus (pi2 ++ l) n)`
  THEN1 (STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL equiv_eq_perms) THEN
         MAP_EVERY Q.EXISTS_TAC [`pi2++l`,`pi1++l`] THEN
         NTAC 2 SELECT_ELIM_TAC THEN SRW_TAC [][] THEN METIS_TAC [permeq_sym]) THEN
  (fresh_ds_equiv |> Q.GEN `t` |> Q.SPEC `Sus l n` |> SIMP_RULE (psrw_ss()) [] |> MATCH_MP_TAC) THEN
  `FINITE (dis_set pi1 pi2)` by SRW_TAC [][] THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_fresh THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (psrw_ss()) [],
  Q.MATCH_ASSUM_RENAME_TAC `nvwalk s [] v = Tie s' C` [] THEN
  (fresh_ds_equiv |> GEN_ALL |> Q.SPECL [`nwalkstar s (Tie s' C)`,`pi2`,`pi1`] |>
   SIMP_RULE (srw_ss()) [] |> MP_TAC) THEN
  SRW_TAC [][nwalkstar_apply_pi] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  `FINITE (dis_set pi1 pi2)` by SRW_TAC [][] THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_fresh THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (psrw_ss()) [],
  Q.MATCH_ASSUM_RENAME_TAC `nvwalk s [] v = nPair C1 C2` [] THEN
  (fresh_ds_equiv |> GEN_ALL |> Q.SPECL [`nwalkstar s (nPair C1 C2)`,`pi2`,`pi1`] |>
   SIMP_RULE (srw_ss()) [] |> MP_TAC) THEN
  SRW_TAC [][nwalkstar_apply_pi] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  `FINITE (dis_set pi1 pi2)` by SRW_TAC [][] THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_fresh THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (psrw_ss()) []])

val nunify_extends_fe = Q.store_thm(
"nunify_extends_fe",
`∀s fe t1 t2 sx fex. nwfs s ∧ (nunify (s,fe) t1 t2 = SOME (sx,fex)) ⇒  fe SUBSET fex`,
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
SRW_TAC [][Once nunify_def,LET_THM] THEN SRW_TAC [][] THENL [
  METIS_TAC [unify_eq_vars_extends_fe,FINITE_dis_set],
  FULL_SIMP_TAC (srw_ss()) [UNCURRY] THEN
  Cases_on `x` THEN
  `nwfs q` by METIS_TAC [nunify_uP,uP_def] THEN
  METIS_TAC [SUBSET_TRANS]
])

val unify_eq_vars_empty = RWstore_thm(
"unify_eq_vars_empty",
`unify_eq_vars {} v (s,fe) = SOME (s,fe)`,
SRW_TAC [][unify_eq_vars_def,ITSET_EMPTY])

val verify_fcs_empty = RWstore_thm(
"verify_fcs_empty",
`verify_fcs {} s = SOME {}`,
SRW_TAC [][verify_fcs_def,ITSET_EMPTY]);

val verify_fcs_FINITE = Q.store_thm(
"verify_fcs_FINITE",
`FINITE fe ∧ (verify_fcs fe s = SOME ve) ⇒ FINITE ve`,
Q_TAC SUFF_TAC
`∀fe. FINITE fe ⇒ ∀ve. (verify_fcs fe s = SOME ve) ⇒ FINITE ve`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [verify_fcs_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN POP_ASSUM MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES] THEN
Cases_on `e` THEN ASM_SIMP_TAC (srw_ss()) [fcs_acc_def] THEN
SRW_TAC [][] THEN SRW_TAC [][] THEN IMP_RES_TAC term_fcs_FINITE);

val verify_fcs_covers_all = Q.store_thm(
"verify_fcs_covers_all",
`FINITE fe ∧ (verify_fcs fe s = SOME ve) ∧ (a,v) ∈ fe ⇒
 ∃fcs. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧ fcs SUBSET ve`,
Q_TAC SUFF_TAC
`∀fe. FINITE fe ⇒ ∀ve. (verify_fcs fe s = SOME ve) ∧ (a,v) ∈ fe ⇒
 ∃fcs. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧ fcs SUBSET ve`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [verify_fcs_def,ITSET_EMPTY] THEN1 (
  POP_ASSUM MP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES,fcs_acc_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] ) THEN
Q.PAT_ASSUM `X = SOME ve` MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES] THEN
Cases_on `e` THEN SRW_TAC [][fcs_acc_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [SUBSET_TRANS,SUBSET_UNION]);

val verify_fcs_minimal = Q.store_thm(
"verify_fcs_minimal",
`FINITE fe ∧ (verify_fcs fe s = SOME ve) ∧ (a,v) ∈ ve ⇒
 ∃b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* s (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs`,
Q_TAC SUFF_TAC
`∀fe. FINITE fe ⇒ ∀ve. (verify_fcs fe s = SOME ve) ∧ (a,v) ∈ ve ⇒
 ∃b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* s (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
ASM_SIMP_TAC (srw_ss())  [verify_fcs_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `X = SOME ve` MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES] THEN
Cases_on `e` THEN SRW_TAC [][fcs_acc_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);

val verify_fcs_SOME = LIST_CONJ [verify_fcs_FINITE, verify_fcs_covers_all, verify_fcs_minimal];

val verify_fcs_NONE = Q.store_thm(
"verify_fcs_NONE",
`FINITE fe ∧ (verify_fcs fe s = NONE) ⇒
 ∃a v. (a,v) ∈ fe ∧ (term_fcs a (nwalk* s (Sus [] v)) = NONE)`,
Q_TAC SUFF_TAC
`∀t. FINITE t ⇒ (verify_fcs t s = NONE) ⇒
    ∃a v. (a,v) IN t ∧ (term_fcs a (nwalk* s (Sus [] v)) = NONE)`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SIMP_TAC (srw_ss()) [verify_fcs_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `FINITE t` ASSUME_TAC THEN
Q.PAT_ASSUM `e NOTIN fcs` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [fcs_acc_RECURSES,DELETE_NON_ELEMENT] THEN
Cases_on `e` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [fcs_acc_def] THEN
METIS_TAC []);

val verify_fcs_INSERT = Q.store_thm(
"verify_fcs_INSERT",
`FINITE fe ∧
 (verify_fcs fe s = SOME ve) ∧
 (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ⇒
 (verify_fcs ((a,v) INSERT fe) s = SOME (ve ∪ fcs))`,
SRW_TAC [][verify_fcs_def,fcs_acc_RECURSES,fcs_acc_def] THEN
REVERSE (Cases_on `(a,v) ∈ fe`) THEN1 (
  FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] ) THEN
`(a,v) INSERT (fe DELETE (a,v)) = fe` by SRW_TAC [][] THEN
(fcs_acc_RECURSES |> Q.INST [`e`|->`(a,v)`,`t`|->`fe DELETE (a,v)`,`b`|->`SOME {}`] |>
 SIMP_RULE (srw_ss()) [fcs_acc_def] |> MP_TAC) THEN
SRW_TAC [][] THEN SRW_TAC [][UNION_IDEMPOT,GSYM UNION_ASSOC]);

val verify_fcs_decompose = Q.store_thm(
"verify_fcs_decompose",
`(verify_fcs ((a,v) INSERT fe) s = SOME ve) ∧ FINITE fe ⇒
 ∃ve0 fcs.
 (verify_fcs fe s = SOME ve0) ∧
 (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧
 (ve = ve0 ∪ fcs)`,
SRW_TAC [][] THEN
Cases_on `(a,v) ∈ fe` THEN1 (
  IMP_RES_TAC verify_fcs_SOME THEN
  FULL_SIMP_TAC (srw_ss()) [ABSORPTION] THEN
  RES_TAC THEN Q.EXISTS_TAC `fcs` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF,EXTENSION] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [verify_fcs_def,fcs_acc_RECURSES,fcs_acc_def,DELETE_NON_ELEMENT]);

val verify_fcs_UNION_I = Q.store_thm(
"verify_fcs_UNION_I",
`FINITE fe1 ∧ FINITE fe2 ∧
 (verify_fcs fe1 s = SOME ve1) ∧ (verify_fcs fe2 s = SOME ve2) ⇒
 (verify_fcs (fe1 ∪ fe2) s = SOME (ve1 ∪ ve2))`,
Q_TAC SUFF_TAC
`∀fe1. FINITE fe1 ⇒
 ∀fe2 ve1 ve2.
 FINITE fe2 ∧ (verify_fcs fe1 s = SOME ve1) ∧ (verify_fcs fe2 s = SOME ve2) ==>
(verify_fcs (fe1 UNION fe2) s = SOME (ve1 ∪ ve2))` THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN SRW_TAC [][] THEN
`∃ve0 fcs. (verify_fcs fe1 s = SOME ve0) ∧ (ve1 = ve0 ∪ fcs) ∧
(term_fcs (FST e) (nwalk* s (Sus [] (SND e))) = SOME fcs)` by
(Cases_on `e` THEN IMP_RES_TAC verify_fcs_decompose THEN
 ASM_SIMP_TAC (srw_ss()) []) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`fe2`,`ve0`,`ve2`] MP_TAC) THEN
SRW_TAC [][INSERT_UNION_EQ] THEN
Q.MATCH_ABBREV_TAC `X = SOME (ve0 ∪ fcs ∪ ve2)` THEN
Q_TAC SUFF_TAC `X = SOME (ve0 ∪ ve2 ∪ fcs)` THEN1 METIS_TAC [UNION_COMM,UNION_ASSOC] THEN
Q.UNABBREV_TAC `X` THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
MATCH_MP_TAC verify_fcs_INSERT THEN SRW_TAC [][]);

val verify_fcs_UNION_E = Q.store_thm(
"verify_fcs_UNION_E",
`FINITE (fe1 ∪ fe2) ∧
(verify_fcs (fe1 ∪ fe2) s = SOME ve) ⇒
 ∃ve1 ve2.
 (verify_fcs fe1 s = SOME ve1) ∧
 (verify_fcs fe2 s = SOME ve2) ∧
 (ve = ve1 ∪ ve2)`,
Q_TAC SUFF_TAC
`∀fe1. FINITE fe1 ⇒
 ∀fe2 ve. FINITE fe2 ∧ (verify_fcs (fe1 ∪ fe2) s = SOME ve) ⇒
 ∃ve1 ve2. (verify_fcs fe1 s = SOME ve1) ∧
           (verify_fcs fe2 s = SOME ve2) ∧
           (ve = ve1 ∪ ve2)` THEN1 METIS_TAC [FINITE_UNION] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN
`∃ve0 fcs. (verify_fcs (fe1 ∪ fe2) s = SOME ve0) ∧ (ve = ve0 ∪ fcs) ∧
(term_fcs (FST e) (nwalk* s (Sus [] (SND e))) = SOME fcs)` by (
  FULL_SIMP_TAC (srw_ss()) [INSERT_UNION_EQ] THEN
  `FINITE (fe1 ∪ fe2)` by METIS_TAC [FINITE_UNION] THEN
  Cases_on `e` THEN IMP_RES_TAC verify_fcs_decompose THEN
  ASM_SIMP_TAC (srw_ss()) []) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`fe2`,`ve0`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `ve1 ∪ fcs` THEN SRW_TAC [][] THEN1 (
  MATCH_MP_TAC verify_fcs_INSERT THEN SRW_TAC [][] ) THEN
METIS_TAC [UNION_COMM,UNION_ASSOC]);

val verify_fcs_UNION = Q.store_thm(
"verify_fcs_UNION",
`FINITE fe1 ∧ FINITE fe2 ⇒
 ((∃ve1 ve2. (verify_fcs fe1 s = SOME ve1) ∧ (verify_fcs fe2 s = SOME ve2) ∧ (ve = ve1 ∪ ve2)) ⇔
  (verify_fcs (fe1 ∪ fe2) s = SOME ve))`,
SRW_TAC [][EQ_IMP_THM] THEN1
METIS_TAC [verify_fcs_UNION_I] THEN
IMP_RES_TAC FINITE_UNION THEN
METIS_TAC [verify_fcs_UNION_E]);

val fresh_verify_fcs = Q.store_thm(
"fresh_verify_fcs",
`nwfs s ∧ fresh fe a t ∧ FINITE fe ∧
 (verify_fcs fe s = SOME fex)
 ⇒ fresh fex a (nwalk* s t)`,
Induct_on `t` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (psrw_ss()) [fresh_def] THEN
`∃fcs. fresh fcs a (apply_pi (REVERSE (REVERSE l)) (nwalk* s (Sus [] n))) ∧ fcs SUBSET fex`
by METIS_TAC [verify_fcs_SOME,term_fcs_fresh,term_fcs_minimal,lemma27,verify_fcs_covers_all] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi] THEN
Cases_on `nvwalk s l n` THEN FULL_SIMP_TAC (psrw_ss()) [fresh_def] THEN1 (
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] ) THEN
METIS_TAC [fresh_extra_fcs]);

val nwalkstar_subterm_exists = Q.store_thm(
"nwalkstar_subterm_exists",
`nwfs s ⇒ ∀t. (∀a c. (nwalk* s t = Tie a c) ⇒
                 ∃t2. nwalk* s t2 = c) ∧
             (∀c1 c2. (nwalk* s t = nPair c1 c2) ⇒
                     (∃t2. nwalk* s t2 = c1) ∧
                     (∃t2. nwalk* s t2 = c2))`,
STRIP_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL [
  Cases_on `nvwalk s l n` THEN FULL_SIMP_TAC (srw_ss()) [], ALL_TAC,
  Cases_on `nvwalk s l n` THEN FULL_SIMP_TAC (srw_ss()) [], ALL_TAC,
  Cases_on `nvwalk s l n` THEN FULL_SIMP_TAC (srw_ss()) [], ALL_TAC
] THEN METIS_TAC []);

val equiv_verify_fcs = Q.store_thm(
"equiv_verify_fcs",
`equiv fe t1 t2 ∧ nwfs s ∧ FINITE fe ∧ (verify_fcs fe s = SOME fex) ⇒
   equiv fex (nwalk* s t1) (nwalk* s t2)`,
MAP_EVERY Q.ID_SPEC_TAC [`t2`,`t1`] THEN
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC equiv_ind THEN
SRW_TAC [][] THEN1 (
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`p1`,`v`] MP_TAC) THEN
  (nvwalk_modulo_pi |> Q.SPECL_THEN [`s`,`p2`,`v`] MP_TAC) THEN
  SRW_TAC [][] THEN
  (fresh_ds_equiv |> GEN_ALL |> Q.SPECL [`nwalk* s (Sus [] v)`,`p2`,`p1`,`fex`] |> MP_TAC) THEN
  ASM_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi] THEN
  STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][] THEN RES_TAC THEN
  IMP_RES_TAC verify_fcs_SOME THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][] THEN
  METIS_TAC [nwalkstar_subterm_exists] )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  FULL_SIMP_TAC (srw_ss()) [nwalkstar_apply_pi] THEN
  IMP_RES_TAC fresh_verify_fcs )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][] THEN
  METIS_TAC [nwalkstar_subterm_exists] ))

val nunify_FINITE_fe = Q.store_thm(
"nunify_FINITE_fe",
`∀s fe t1 t2 sx fex. nwfs s ∧ FINITE fe ∧ (nunify (s,fe) t1 t2 = SOME (sx,fex)) ⇒
 FINITE fex`,
HO_MATCH_MP_TAC nunify_ind THEN
REPEAT STRIP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `nunify X Y Z = XX` MP_TAC  THEN
ASM_SIMP_TAC (srw_ss()) [Once nunify_def,LET_THM,nvwalk_case_thms] THEN
SRW_TAC [][] THEN SRW_TAC [][] THENL [
  METIS_TAC [unify_eq_vars_SOME,FINITE_dis_set,unify_eq_vars_preserves_s],
  METIS_TAC [term_fcs_FINITE],
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [nunify_uP,uP_def]
]);

val fresh_SUBMAP = Q.store_thm(
"fresh_SUBMAP",
`fresh fcs a (nwalk* s t) ∧ nwfs s ⇒ ∃fe. fresh fe a t ∧ ∀b w. (b,w) ∈ fe ⇒ fresh fcs b (nwalk* s (Sus [] w))`,
Induct_on `t` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (psrw_ss()) [fresh_def] THENL [
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][],
  Q.HO_MATCH_ABBREV_TAC `∃fe. X ∈ fe ∧ Z fe` THEN
  Q.EXISTS_TAC `{X}` THEN
  UNABBREV_ALL_TAC THEN
  SRW_TAC [][] THEN
  (fresh_apply_pi |> Q.INST [`pi`|->`REVERSE l`,`t`|->`nwalk* s (Sus l n)`] |> MP_TAC) THEN
  ASM_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi],
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][],
  Q.EXISTS_TAC `fe ∪ fe'` THEN SRW_TAC [][] THEN
  METIS_TAC [fresh_extra_fcs,SUBSET_UNION],
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] ])

val equiv_SUBSET = Q.store_thm(
"equiv_SUBSET",
`equiv fe t1 t2 ∧ fe SUBSET fex ⇒ equiv fex t1 t2`,
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
MAP_EVERY Q.ID_SPEC_TAC [`t2`,`t1`] THEN
HO_MATCH_MP_TAC equiv_ind THEN
SRW_TAC [][] THEN
SRW_TAC [][Once equiv_cases] THEN1 (
MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`] THEN
SRW_TAC [][] THEN METIS_TAC [SUBSET_DEF] ) THEN
METIS_TAC [fresh_extra_fcs])

val fresh_drop_NOTIN_nvars = Q.store_thm(
"fresh_drop_NOTIN_nvars",
`fresh fe a t ∧ v NOTIN nvars t ⇒ fresh (fe DIFF {(b,u) | u = v}) a t`,
Induct_on `t` THEN SRW_TAC [][fresh_def] THEN SRW_TAC [][])

val term_fcs_IN_nvars = Q.store_thm(
"term_fcs_IN_nvars",
`(term_fcs a t = SOME fe) ∧ (b,v) IN fe ⇒ v IN nvars t`,
SRW_TAC [][] THEN
`fresh fe a t` by IMP_RES_TAC term_fcs_fresh THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC fresh_drop_NOTIN_nvars THEN
POP_ASSUM (Q.SPEC_THEN `b` STRIP_ASSUME_TAC) THEN
IMP_RES_TAC term_fcs_minimal THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF])

val fresh_drop_IN_FDOM = Q.store_thm(
"fresh_drop_IN_FDOM",
`nwfs s ∧ fresh fe a (nwalk* s t) ∧ v IN FDOM s ⇒ fresh (fe DIFF {(b,u) | u = v}) a (nwalk* s t)`,
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `v NOTIN nvars (nwalk* s t)` THEN1 SRW_TAC [][fresh_drop_NOTIN_nvars] THEN
SRW_TAC [][GSYM noc_eq_nvars_nwalkstar,IN_DEF] THEN
METIS_TAC [noc_NOTIN_FDOM])

val term_fcs_NOTIN_FDOM = Q.store_thm(
"term_fcs_NOTIN_FDOM",
`nwfs s ∧ (term_fcs a (nwalk* s t) = SOME fe) ∧ (b,v) IN fe ⇒ v NOTIN FDOM s`,
SRW_TAC [][] THEN
`fresh fe a (nwalk* s t)` by IMP_RES_TAC term_fcs_fresh THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC fresh_drop_IN_FDOM THEN
POP_ASSUM (Q.SPEC_THEN `b` STRIP_ASSUME_TAC) THEN
IMP_RES_TAC term_fcs_minimal THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF])

val verify_fcs_NOTIN_FDOM = Q.store_thm(
"verify_fcs_NOTIN_FDOM",
`(verify_fcs fe s = SOME ve) ∧ (a,v) ∈ ve ∧ nwfs s ∧ FINITE fe ⇒ v ∉ FDOM s`,
STRIP_TAC THEN IMP_RES_TAC verify_fcs_SOME THEN
IMP_RES_TAC term_fcs_NOTIN_FDOM)

val verify_fcs_SUBSET = Q.store_thm(
"verify_fcs_SUBSET",
`FINITE fex ∧ (verify_fcs fex s = SOME vex) ∧ fe SUBSET fex ⇒
 ∃ve. (verify_fcs fe s = SOME ve) ∧ ve SUBSET vex`,
SRW_TAC [][] THEN
IMP_RES_TAC SUBSET_FINITE THEN
Cases_on `verify_fcs fe s` THEN SRW_TAC [][] THEN1 (
  IMP_RES_TAC verify_fcs_NONE THEN
  IMP_RES_TAC SUBSET_DEF THEN
  IMP_RES_TAC verify_fcs_covers_all THEN
  FULL_SIMP_TAC (srw_ss()) []) THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF,FORALL_PROD] THEN
SRW_TAC [][] THEN
`∃b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* s (Sus [] w)) = SOME fcs) ∧ (p_1,p_2) ∈ fcs`
by METIS_TAC [verify_fcs_minimal] THEN
`fcs SUBSET vex` by METIS_TAC [verify_fcs_covers_all,optionTheory.SOME_11] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF])

val term_fcs_apply_pi = Q.store_thm(
"term_fcs_apply_pi",
`(term_fcs a t = SOME fcs) ⇒
 (term_fcs (lswapstr pi a) (apply_pi pi t) = SOME fcs)`,
Q.ID_SPEC_TAC `fcs` THEN
Induct_on `t` THEN SRW_TAC [][] THEN1 (
  FULL_SIMP_TAC (srw_ss()) [term_fcs_def] )
THEN1 (
  FULL_SIMP_TAC (psrw_ss()) [term_fcs_def, REVERSE_APPEND] THEN
  SRW_TAC [][GSYM pmact_decompose] THEN
  SIMP_TAC (psrw_ss()) [] )
THEN1 (
  SRW_TAC [][Once term_fcs_def] THEN1 (
    FULL_SIMP_TAC (srw_ss()) [Once term_fcs_def] ) THEN
  Q.PAT_ASSUM `term_fcs a X = SOME fcs` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def])
THEN1 (
  SRW_TAC [][Once term_fcs_def] THEN
  Q.PAT_ASSUM `term_fcs a X = SOME fcs` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  FULL_SIMP_TAC (srw_ss()) []) THEN
FULL_SIMP_TAC (srw_ss()) [term_fcs_def])

val term_fcs_nwalkstar = Q.store_thm(
"term_fcs_nwalkstar",
`nwfs s ∧
 (term_fcs b t = SOME fcs) ∧
 (term_fcs b (nwalk* s t) = SOME fcs2) ∧
 (a,v) ∈ fcs ⇒
 ∃fcs1. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs1) ∧
        fcs1 ⊆ fcs2`,
STRIP_TAC THEN
NTAC 4 (POP_ASSUM MP_TAC) THEN
SPEC_ALL_TAC [`t`,`s`] THEN
Q.ID_SPEC_TAC `t` THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
REPEAT STRIP_TAC THEN
`nwalk* s t = nwalk* s (nwalk s t)` by METIS_TAC [nwalkstar_nwalk] THEN
Cases_on `nwalk s t` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  Q.PAT_ASSUM `term_fcs X Y = SOME fcs2` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  SRW_TAC [][apply_pi_eql] )
THEN1 (
  `n ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  Cases_on `t` THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,Once term_fcs_def,EXTENSION] THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l'`,`n'`] |> GSYM |> MP_TAC) THEN
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql] THEN
  SRW_TAC [][REVERSE_APPEND,pmact_decompose] THEN
  METIS_TAC [] )
THEN1 (
  Q.PAT_ASSUM `term_fcs X Y = SOME fcs2` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN1 (
    Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
    SRW_TAC [][apply_pi_eql] THEN
    SRW_TAC [][Once term_fcs_def]) THEN
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN1 (
    Q.PAT_ASSUM `term_fcs b X = SOME fcs` MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def,EXTENSION] THEN
    SRW_TAC [][] THEN RES_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
    SRW_TAC [][apply_pi_eql] THEN
    SRW_TAC [][Once term_fcs_def,nwalkstar_apply_pi] THEN
    Q.EXISTS_TAC `fcs2` THEN SRW_TAC [][] THEN
    MATCH_MP_TAC term_fcs_apply_pi THEN SRW_TAC [][] ) THEN
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `term_fcs b X = SOME fcs` MP_TAC THEN
  SRW_TAC [] [Once term_fcs_def] THEN
  METIS_TAC [] )
THEN1 (
  Q.PAT_ASSUM `term_fcs b Y = SOME fcs2` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Q.PAT_ASSUM `term_fcs b X = SOME fcs` MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def,EXTENSION] THEN
    SRW_TAC [][] THEN RES_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
    SRW_TAC [][apply_pi_eql] THEN
    SRW_TAC [][Once term_fcs_def,nwalkstar_apply_pi] THEN
    Q.EXISTS_TAC `x1 ∪ x2` THEN SRW_TAC [][] THEN
    MAP_EVERY Q.EXISTS_TAC [`x1`,`x2`] THEN SRW_TAC [][] THEN
    MATCH_MP_TAC term_fcs_apply_pi THEN SRW_TAC [][] ) THEN
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `term_fcs b X = SOME fcs` MP_TAC THEN
  SRW_TAC [] [Once term_fcs_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  RES_TAC THEN METIS_TAC [SUBSET_UNION,SUBSET_TRANS] )
THEN
  Q.PAT_ASSUM `term_fcs b Y = SOME fcs2` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  SRW_TAC [][apply_pi_eql] )

val verify_fcs_SUBMAP = Q.store_thm(
"verify_fcs_SUBMAP",
`FINITE fe ∧ (verify_fcs fe sx = SOME fex) ∧ nwfs sx ∧ s SUBMAP sx ⇒
 ∃fe1. (verify_fcs fe s = SOME fe1) ∧
 ∀a v. (a,v) ∈ fe1 ⇒
∃fcs. (term_fcs a (nwalk* sx (Sus [] v)) = SOME fcs) ∧ fcs ⊆ fex`,
REPEAT STRIP_TAC THEN
Cases_on `verify_fcs fe s` THEN1 (
  IMP_RES_TAC verify_fcs_NONE THEN
  IMP_RES_TAC term_fcs_NONE THEN
  IMP_RES_TAC verify_fcs_SOME THEN
  IMP_RES_TAC term_fcs_fresh THEN
  METIS_TAC [nwalkstar_SUBMAP,fresh_SUBMAP] ) THEN
Q.EXISTS_TAC `x` THEN SIMP_TAC (srw_ss()) [] THEN
REPEAT STRIP_TAC THEN
`∃b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* s (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs`
by METIS_TAC [verify_fcs_minimal] THEN
`∃fcs2. (term_fcs b (nwalk* sx (Sus [] w)) = SOME fcs2) ∧ fcs2 ⊆ fex`
by METIS_TAC[verify_fcs_covers_all] THEN
`∃fcs. (term_fcs a (nwalk* sx (Sus [] v)) = SOME fcs) ∧ fcs ⊆ fcs2` by (
  MATCH_MP_TAC (GEN_ALL term_fcs_nwalkstar) THEN
  MAP_EVERY Q.EXISTS_TAC [`nwalk* s (Sus [] w)`,`fcs`,`b`] THEN
  SRW_TAC [][] THEN
  METIS_TAC [nwalkstar_SUBMAP] ) THEN
METIS_TAC [SUBSET_TRANS])

val verify_fcs_term_fcs = Q.store_thm(
"verify_fcs_term_fcs",
`(term_fcs a t = SOME fcs) ∧
 (term_fcs a (nwalk* s t) = SOME fex) ∧ nwfs s ⇒
 (verify_fcs fcs s = SOME fex)`,
MAP_EVERY Q.ID_SPEC_TAC [`fcs`,`fex`] THEN
Induct_on `t` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  FULL_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] )
THEN1 (
  Q.PAT_ASSUM `term_fcs a (Sus X Y) = Z` MP_TAC THEN
  ASM_SIMP_TAC (psrw_ss()) [term_fcs_def] THEN
  SRW_TAC [][] THEN
  SRW_TAC [][verify_fcs_def,fcs_acc_RECURSES,fcs_acc_def,ITSET_EMPTY] THEN
  (nwalkstar_apply_pi |> UNDISCH |>
   Q.SPEC `Sus [] n` |> Q.INST [`pi`|->`l`] |>
   DISCH_ALL |>
   SIMP_RULE (psrw_ss()) [] |> MP_TAC) THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (term_fcs_apply_pi |>
   Q.INST [`t`|->`apply_pi l (nwalk* s (Sus [] n))`,`fcs`|->`fex`,`pi`|->`REVERSE l`] |>
   SIMP_RULE (srw_ss()) [] |> MP_TAC) THEN
  SRW_TAC [][])
THEN1 (
  Q.PAT_ASSUM `term_fcs a (Tie Y X) = SOME fcs` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  Q.PAT_ASSUM `term_fcs a (Tie Y X) = SOME fex` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN SRW_TAC [][])
THEN1 (
  Q.PAT_ASSUM `term_fcs a X = SOME fcs` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  Q.PAT_ASSUM `term_fcs a X = SOME fex` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC term_fcs_SOME THEN
  SRW_TAC [][verify_fcs_UNION_I]) THEN
FULL_SIMP_TAC (srw_ss()) [term_fcs_def] THEN
SRW_TAC [][])

val verify_fcs_iter_SUBMAP = Q.store_thm(
"verify_fcs_iter_SUBMAP",
`(verify_fcs fe s = SOME ve0) ∧
 (verify_fcs fe sx = SOME ve) ∧
 s SUBMAP sx ∧ nwfs sx ∧ FINITE fe ⇒
 (verify_fcs ve0 sx = SOME ve)`,
Q_TAC SUFF_TAC
`∀fe. FINITE fe ⇒ ∀ve0 ve.
 (verify_fcs fe s = SOME ve0) ∧
 (verify_fcs fe sx = SOME ve) ∧
 s SUBMAP sx ∧ nwfs sx ⇒
 (verify_fcs ve0 sx = SOME ve)` THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][] THEN SRW_TAC [][] THEN
Cases_on `e` THEN
IMP_RES_TAC verify_fcs_decompose THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q_TAC SUFF_TAC
`verify_fcs fcs' sx = SOME fcs` THEN1 (
  STRIP_TAC THEN
  IMP_RES_TAC term_fcs_SOME THEN
  IMP_RES_TAC verify_fcs_SOME THEN
  SRW_TAC [][verify_fcs_UNION_I]) THEN
MATCH_MP_TAC (GEN_ALL verify_fcs_term_fcs) THEN
MAP_EVERY Q.EXISTS_TAC [`nwalk* s (Sus [] r)`,`q`] THEN
METIS_TAC [nwalkstar_SUBMAP,nwfs_SUBMAP])

val verify_fcs_idem = Q.store_thm(
"verify_fcs_idem",
`nwfs s ∧ FINITE fe ∧ (verify_fcs fe s = SOME fex) ⇒ (verify_fcs fex s = SOME fex)`,
METIS_TAC [verify_fcs_iter_SUBMAP, SUBMAP_REFL])

val unify_eq_vars_adds_same_fcs = Q.store_thm(
"unify_eq_vars_adds_same_fcs",
`∀ds. FINITE ds ⇒ ∃fu. ∀fe sx fex. (unify_eq_vars ds v (s,fe) = SOME (sx,fex)) ⇒ (fex = fe ∪ fu)`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][]
THEN1 (Q.EXISTS_TAC `{}` THEN SRW_TAC [][]) THEN
Cases_on `term_fcs e (nwalk* s (Sus [] v))` THEN1 (
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_decompose THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
Q.EXISTS_TAC `fu ∪ x` THEN SRW_TAC [][] THEN
IMP_RES_TAC unify_eq_vars_decompose THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [UNION_ASSOC]);

val unify_eq_vars_ignores_fe = Q.store_thm(
"unify_eq_vars_ignores_fe",
`(unify_eq_vars ds v (s,fe) = SOME (sx,fex)) ∧ FINITE ds ⇒
 ∀fe'.∃fex'. (unify_eq_vars ds v (s,fe') = SOME (s,fex'))`,
SRW_TAC [][] THEN
Cases_on `unify_eq_vars ds v (s,fe')` THEN1 (
  IMP_RES_TAC unify_eq_vars_NONE THEN
  IMP_RES_TAC unify_eq_vars_preserves_s THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_SOME THEN
  RES_TAC) THEN
Cases_on `x` THEN
IMP_RES_TAC unify_eq_vars_preserves_s THEN
SRW_TAC [][]);

val nunify_ignores_fe = Q.store_thm(
"nunify_ignores_fe",
`∀s fe t1 t2 sx fex.
   nwfs s ∧ (nunify (s,fe) t1 t2 = SOME (sx,fex)) ⇒
   ∀fe'. ∃fex'. nunify (s,fe') t1 t2 = SOME (sx,fex')`,
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][] THEN
POP_ASSUM MP_TAC THEN
MAP_EVERY Cases_on [`nwalk s t1`,`nwalk s t2`] THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN SRW_TAC [][] THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN SRW_TAC [][] THEN1 (
  `FINITE (dis_set l l')` by METIS_TAC [FINITE_dis_set] THEN
  IMP_RES_TAC unify_eq_vars_preserves_s THEN SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_adds_same_fcs THEN
  POP_ASSUM (Q.SPECL_THEN [`n`,`s`] MP_TAC) THEN
  SRW_TAC [][] THEN
  Cases_on `unify_eq_vars (dis_set l l') n (s,fe')` THEN1 (
    IMP_RES_TAC unify_eq_vars_ignores_fe THEN
    POP_ASSUM (Q.SPEC_THEN `fe'` MP_TAC) THEN SRW_TAC [][] ) THEN
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC unify_eq_vars_preserves_s THEN SRW_TAC [][]) THEN
Q.PAT_ASSUM `unify X Y Z = Z2` ASSUME_TAC THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`nwfs q` by METIS_TAC [nunify_uP,uP_def] THEN
Q.PAT_ASSUM `nunify (q,r) Y Z = X` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) C2 C2' = SOME (q,r)` [] THEN
`∃r'. nunify (s,fe') C2 C2' = SOME (q,r')` by METIS_TAC [] THEN
SRW_TAC [][]);

val nunify_ignores_fe_NONE = Q.store_thm(
"nunify_ignores_fe_NONE",
`nwfs s ∧ (nunify (s,fe) t1 t2 = NONE) ⇒
 ∀fe'. nunify (s,fe') t1 t2 = NONE`,
SRW_TAC [][] THEN
Cases_on `nunify (s,fe') t1 t2` THEN
SRW_TAC [][] THEN Cases_on `x` THEN
SRW_TAC [][] THEN
(nunify_ignores_fe |>
 Q.SPECL [`s`,`fe'`,`t1`,`t2`,`q`,`r`] |>
 MP_TAC) THEN
SRW_TAC [][] THEN Q.EXISTS_TAC `fe` THEN
SRW_TAC [][]);

val nunify_adds_same_fcs = Q.store_thm(
"nunify_adds_same_fcs",
`nwfs s ⇒
 ∃fu.
   ∀fe sx fex.
      (nunify (s,fe) t1 t2 = SOME (sx,fex)) ⇒ (fex = fe ∪ fu)`,
Q_TAC SUFF_TAC
`∀s (fe:fe) t1 t2. nwfs s ⇒ ∃fu.∀fe sx fex. (nunify (s,fe) t1 t2 = SOME (sx,fex))
⇒ (fex = fe ∪ fu)` THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][] THEN
MAP_EVERY Cases_on [`nwalk s t1`,`nwalk s t2`] THEN
SRW_TAC [][] THEN SRW_TAC [][Once nunify_def,LET_THM]
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  ASM_SIMP_TAC (psrw_ss()) [] THEN
  Cases_on `n = n'` THEN SRW_TAC [][] THEN1 (
    (unify_eq_vars_adds_same_fcs |> Q.SPEC `dis_set l l'` |>
     Q.INST [`v`|->`n`] |> MP_TAC) THEN
    SRW_TAC [][] ) THEN
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 ( Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = Tie s1 C1` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = Tie s2 C2` [] THEN
  Cases_on `s1 = s2` THEN SRW_TAC [][] THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `term_fcs s1 (nwalk* s C2)` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.EXISTS_TAC `fu ∪ x` THEN SRW_TAC [][] THEN
  METIS_TAC [UNION_ASSOC,UNION_COMM] )
THEN1 (Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = nPair t1a t1d` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = nPair t2a t2d` [] THEN
  Cases_on `nunify (s,fe) t1a t2a` THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    IMP_RES_TAC nunify_ignores_fe_NONE THEN
    FULL_SIMP_TAC (srw_ss()) [] ) THEN
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `nwfs q` by METIS_TAC [nunify_uP,uP_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC nunify_ignores_fe THEN
  Q.EXISTS_TAC `fu ∪ fu'` THEN SRW_TAC [][] THEN
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `fe'` MP_TAC) THEN
  SRW_TAC [][] THEN RES_TAC THEN
  METIS_TAC [UNION_ASSOC] )
THEN1 (Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (Q.EXISTS_TAC `{}` THEN SRW_TAC [][] ));

val nomunify_unifier = Q.store_thm(
"nomunify_unifier",
`nwfs s ∧ FINITE fe ∧ (nomunify (s,fe) t1 t2 = SOME (sx,fex)) ==>
   FINITE fex ∧ nwfs sx ∧ s SUBMAP sx ∧ (equiv fex (nwalk* sx t1) (nwalk* sx t2))`,
Q_TAC SUFF_TAC
`!s fe t1 t2 sx fex. nwfs s ∧ FINITE fe ∧ (nomunify (s,fe) t1 t2 = SOME (sx,fex)) ==>
   (equiv fex (nwalk* sx t1) (nwalk* sx t2))`
THEN1 (SIMP_TAC (srw_ss()) [nomunify_def] THEN
       STRIP_TAC THEN REPEAT GEN_TAC THEN
       STRIP_TAC THEN
       Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       CONJ1_TAC THEN1 METIS_TAC [nunify_FINITE_fe,verify_fcs_SOME] THEN
       CONJ1_TAC THEN1 METIS_TAC [nunify_uP,uP_def] THEN
       CONJ1_TAC THEN1 METIS_TAC [nunify_uP,uP_def] THEN
       FIRST_X_ASSUM (Q.SPEC_THEN `s` (MP_TAC o SPEC_ALL)) THEN
       SRW_TAC [][] ) THEN
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][nomunify_def,UNCURRY] THEN
`∃sx fx0. x = (sx,fx0)` by (Cases_on `x` THEN SRW_TAC [][]) THEN SRW_TAC [][] THEN
`nwfs sx /\ s SUBMAP sx` by METIS_TAC [nunify_uP,uP_def] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_PROD] THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,nvwalk_case_thms,LET_THM] THEN
SRW_TAC [][] THEN1 (
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  Cases_on `t1` THEN Cases_on `t2` THEN
  FULL_SIMP_TAC (srw_ss()) [nwalk_def,nvwalk_case_thms,Once equiv_cases]) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalk* sx t1) (nwalk* sx t2)` THEN
  `(nwalk* sx t1 = nwalk* sx (nwalk s t1)) /\
   (nwalk* sx t2 = nwalk* sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  `nvwalk sx l n = Nom s'`
  by (ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,Abbr`sx`,FLOOKUP_UPDATE]) THEN
  FULL_SIMP_TAC (srw_ss()) []) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalk* sx t1) (nwalk* sx t2)` THEN
  `(nwalk* sx t1 = nwalk* sx (nwalk s t1)) /\
   (nwalk* sx t2 = nwalk* sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  `nvwalk sx l n = Nom s'`
  by (ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,Abbr`sx`,FLOOKUP_UPDATE]) THEN
  FULL_SIMP_TAC (srw_ss()) []) THEN1 (
  `s = sx` by METIS_TAC [unify_eq_vars_preserves_s,FINITE_dis_set] THEN
  SRW_TAC [][] THEN
  `equiv fx0 (nwalk* s t1) (nwalk* s t2)`
  by (IMP_RES_TAC unify_eq_vars_equiv THEN
      METIS_TAC [nwalkstar_nwalk]) THEN
  `FINITE fx0` by METIS_TAC [unify_eq_vars_SOME,FINITE_dis_set] THEN
  METIS_TAC [verify_fcs_SOME,equiv_verify_fcs,nwalkstar_idempotent]) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  IMP_RES_TAC nwalk_to_var THEN SRW_TAC [][] THEN
  IMP_RES_TAC NOT_FDOM_nvwalk THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nvwalk s p1 u1 = Sus l n` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nvwalk s p2 u2 = Sus l' n'` [] THEN
  MP_TAC (Q.SPECL [`p1`,`u1`,`s`] (Q.INST [`pu`|->`l`,`u`|->`n`] (UNDISCH nvwalk_SUBMAP_var))) THEN
  MP_TAC (Q.SPECL [`p2`,`u2`,`s`] (Q.INST [`pu`|->`l'`,`u`|->`n'`] (UNDISCH nvwalk_SUBMAP_var))) THEN
  SRW_TAC [][] THEN
  SRW_TAC [][Once nvwalk_def,FLOOKUP_UPDATE,nvwalk_case_thms,Abbr`sx`] THEN
  ASM_SIMP_TAC (psrw_ss()) [] ) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
  SRW_TAC [][Abbr`sx`,Once nvwalk_def,FLOOKUP_UPDATE] ) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
  SRW_TAC [][Abbr`sx`,Once nvwalk_def,FLOOKUP_UPDATE] ) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][Abbr`sx`,Once nvwalk_def,FLOOKUP_UPDATE] ) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  Q.PAT_ASSUM `nwalk* sx t2 = Z` MP_TAC THEN
  SRW_TAC [][Once nvwalk_def,Abbr`sx`,FLOOKUP_UPDATE] THEN
  SIMP_TAC (psrw_ss()) [] ) THEN1 (
  Q.PAT_ASSUM `nunify X Y Z = X2` ASSUME_TAC THEN
  Q.PAT_ASSUM `verify_fcs X Y = Z` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  SRW_TAC [][Once equiv_cases] ) THEN1 (
  Q.PAT_ASSUM `term_fcs X Y = Z` ASSUME_TAC THEN
  Q.PAT_ASSUM `nunify X Y Z = X2` ASSUME_TAC THEN
  Q.PAT_ASSUM `X ≠ Y` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC term_fcs_SOME THEN
  Q.PAT_ASSUM `verify_fcs X Y = Z` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  REVERSE (SRW_TAC [][Once equiv_cases]) THEN1
    METIS_TAC [nwalkstar_apply_pi] THEN
  Q.MATCH_RENAME_TAC `fresh fex a (nwalk* sx c)` [] THEN
  Q_TAC SUFF_TAC `fresh fex a (nwalk* sx (nwalk* s c))`
  THEN1 METIS_TAC [nwalkstar_SUBMAP] THEN
  MATCH_MP_TAC (GEN_ALL fresh_verify_fcs) THEN
  Q.EXISTS_TAC `fx0` THEN
  SRW_TAC [][] THEN1 (
    MATCH_MP_TAC (GEN_ALL fresh_extra_fcs) THEN
    Q.EXISTS_TAC `fcs` THEN SRW_TAC [][] THEN
    METIS_TAC [nunify_extends_fe,UNION_SUBSET] ) THEN
  MATCH_MP_TAC nunify_FINITE_fe THEN METIS_TAC [FINITE_UNION] ) THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `t2` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
  Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][Abbr`sx`,Once nvwalk_def,FLOOKUP_UPDATE] ) THEN1 (
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nunify X Y Z = SOME (q,r)` ASSUME_TAC THEN
  Q.PAT_ASSUM `nunify X Y Z = SOME (sx,fx0)` ASSUME_TAC THEN
  Q.PAT_ASSUM `verify_fcs X Y = Z` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = nPair t1a t1d` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = nPair t2a t2d` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) t1a t2a = SOME (sa, fea)` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (sa,fea) t1d t2d = SOME (sd, fed)` [] THEN
  `nwfs sa ∧ sa SUBMAP sd` by METIS_TAC [nunify_uP,uP_def] THEN
  `FINITE fea ∧ fea SUBSET fed ∧ FINITE fed`
    by METIS_TAC [nunify_FINITE_fe,nunify_extends_fe] THEN
  SRW_TAC [][Once equiv_cases] THEN
  `∃fad. (verify_fcs fea sd = SOME fad) ∧ fad SUBSET fex`
  by METIS_TAC [verify_fcs_SUBSET] THEN
  `∃faa. verify_fcs fea sa = SOME faa`
  by (METIS_TAC [verify_fcs_SUBMAP] ) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `verify_fcs faa sd = SOME fad` by METIS_TAC [verify_fcs_iter_SUBMAP] THEN
  MATCH_MP_TAC (GEN_ALL equiv_SUBSET) THEN
  Q.EXISTS_TAC `fad` THEN SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `equiv fad (nwalk* sd (nwalk* sa t1a)) (nwalk* sd (nwalk* sa t2a))`
  THEN1 METIS_TAC [nwalkstar_SUBMAP] THEN
  MATCH_MP_TAC (GEN_ALL equiv_verify_fcs) THEN
  MAP_EVERY Q.EXISTS_TAC [`faa`] THEN SRW_TAC [][] THEN
  IMP_RES_TAC verify_fcs_SOME)
THEN1 (
  Q.MATCH_ABBREV_TAC `equiv fex (nwalkstar sx t1) (nwalkstar sx t2)` THEN
  `(nwalkstar sx t1 = nwalkstar sx (nwalk s t1)) /\
   (nwalkstar sx t2 = nwalkstar sx (nwalk s t2))`
     by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
  Q.PAT_ASSUM `nwfs s` MP_TAC THEN
  MP_TAC (Q.INST[`t`|->`t1`]nwalk_SUBMAP) THEN
  MP_TAC (Q.INST[`t`|->`t2`]nwalk_SUBMAP) THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][Abbr`sx`,Once nvwalk_def,FLOOKUP_UPDATE] ) THEN
METIS_TAC [nwalkstar_nwalk,equiv_refl]);

val nomunify_fcs_consistent = Q.store_thm(
"nomunify_fcs_consistent",
`!s fe t1 t2 sx fex. nwfs s ∧ FINITE fe ∧ (nomunify (s,fe) t1 t2 = SOME (sx,fex)) ∧ (a,v) ∈ fex ==>
     fresh fex a (nwalk* sx (Sus [] v))`,
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][nomunify_def,UNCURRY] THEN
`∃sx fx0. x = (sx,fx0)` by (Cases_on `x` THEN SRW_TAC [][]) THEN SRW_TAC [][] THEN
`nwfs sx /\ s SUBMAP sx` by METIS_TAC [nunify_uP,uP_def] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_PROD] THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,nvwalk_case_thms,LET_THM] THEN
SRW_TAC [][] THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC unify_eq_vars_preserves_s THEN
  IMP_RES_TAC unify_eq_vars_FINITE THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  SRW_TAC [][] THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC term_fcs_FINITE THEN
  NTAC 3 ( POP_ASSUM MP_TAC )
  THEN ASM_SIMP_TAC (srw_ss()) []  )
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  Cases_on `x` THEN
  NTAC 3 (POP_ASSUM MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  STRIP_TAC THEN
  `nwfs q ∧ FINITE r` by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe] THEN
  SRW_TAC [][])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def])
THEN1 (
  IMP_RES_TAC verify_fcs_NOTIN_FDOM THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def]));

val nomunify_solves_fe = Q.store_thm(
"nomunify_solves_fe",
`!s fe t1 t2 sx fex. nwfs s ∧ FINITE fe ∧ (nomunify (s,fe) t1 t2 = SOME (sx,fex)) ∧ (a,v) ∈ fe ==>
     fresh fex a (nwalk* sx (Sus [] v))`,
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][nomunify_def,UNCURRY] THEN
`∃sx fx0. x = (sx,fx0)` by (Cases_on `x` THEN SRW_TAC [][]) THEN SRW_TAC [][] THEN
`nwfs sx /\ s SUBMAP sx` by METIS_TAC [nunify_uP,uP_def] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_PROD] THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,nvwalk_case_thms,LET_THM] THEN
SRW_TAC [][] THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC unify_eq_vars_preserves_s THEN
  IMP_RES_TAC unify_eq_vars_extends_fe THEN
  IMP_RES_TAC unify_eq_vars_FINITE THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `(a,v) ∈ fx0` by METIS_TAC [SUBSET_DEF] THEN
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  POP_ASSUM MP_TAC THEN SRW_TAC [][] )
THEN1 (
  IMP_RES_TAC term_fcs_FINITE THEN
  NTAC 3 (POP_ASSUM MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  `nwfs q ∧ FINITE r ∧ fe SUBSET r`
  by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe,nunify_extends_fe] THEN
  `(a,v) ∈ r` by METIS_TAC [SUBSET_DEF] THEN
  SRW_TAC [][] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  IMP_RES_TAC term_fcs_fresh THEN
  IMP_RES_TAC fresh_extra_fcs THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] ))

val _ = set_fixity "COMPAT" (Infix(NONASSOC,450))

val COMPAT_def = Define`
(sx,fex) COMPAT (s,fe) =
nwfs s ∧ nwfs sx ∧ FINITE fe ∧ FINITE fex ∧
∃ve vex. (verify_fcs fe s = SOME ve) ∧
         (verify_fcs fex sx = SOME vex) ∧
!t1 t2. equiv ve (nwalk* s t1) (nwalk* s t2) ⇒ equiv vex (nwalk* sx t1) (nwalk* sx t2)`

val COMPAT_REFL = Q.store_thm(
"COMPAT_REFL",
`nwfs s ∧ FINITE fe ∧ (verify_fcs fe s = SOME ve) ==>
(s,fe) COMPAT (s,fe) ∧
(s,ve) COMPAT (s,fe) ∧
(s,fe) COMPAT (s,ve) ∧
(s,ve) COMPAT (s,ve)
`,
SRW_TAC [][COMPAT_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`FINITE ve` by IMP_RES_TAC verify_fcs_SOME THEN
SRW_TAC [][] THEN
IMP_RES_TAC verify_fcs_idem THEN
FULL_SIMP_TAC (srw_ss()) [])

val COMPAT_TRANS = Q.store_thm(
"COMPAT_TRANS",
`p2 COMPAT p1 /\ p1 COMPAT p0 ==> p2 COMPAT p0`,
MAP_EVERY Cases_on [`p0`,`p1`,`p2`] THEN
SRW_TAC [][COMPAT_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][])

val SUBMAP_COMPAT = Q.store_thm(
"SUBMAP_COMPAT",
`nwfs sx ∧ s SUBMAP sx ∧ FINITE fe ∧ (verify_fcs fe sx = SOME ve) ⇒
 (sx,fe) COMPAT (s,fe)`,
STRIP_TAC THEN
IMP_RES_TAC nwfs_SUBMAP THEN
SRW_TAC [][COMPAT_def] THEN
IMP_RES_TAC verify_fcs_SUBMAP THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `equiv ve (nwalk* sx (nwalk* s t1)) (nwalk* sx (nwalk* s t2))`
THEN1 METIS_TAC [nwalkstar_SUBMAP] THEN
MATCH_MP_TAC (GEN_ALL equiv_verify_fcs) THEN
Q.EXISTS_TAC `fe1` THEN
SRW_TAC [][] THEN1
IMP_RES_TAC verify_fcs_SOME THEN
MATCH_MP_TAC verify_fcs_iter_SUBMAP THEN
SRW_TAC [][] )

val SUBSET_COMPAT = Q.store_thm(
"SUBSET_COMPAT",
`nwfs s ∧ (verify_fcs fex s = SOME vex) ∧ FINITE fex ∧ fe SUBSET fex ⇒
 (s,fex) COMPAT (s,fe)`,
SRW_TAC [][COMPAT_def] THEN1
METIS_TAC [SUBSET_FINITE] THEN
`∃ve. ve SUBSET vex ∧ (verify_fcs fe s = SOME ve)`
by METIS_TAC [verify_fcs_SUBSET] THEN
SRW_TAC [][] THEN
METIS_TAC [equiv_SUBSET])

val nomunify_COMPAT = Q.store_thm(
"nomunify_COMPAT",
`nwfs s ∧ FINITE fe ∧ (nomunify (s,fe) t1 t2 = SOME (su,fu)) ⇒ (su,fu) COMPAT (s,fe)`,
SRW_TAC [][nomunify_def] THEN
Cases_on `x` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
Q.MATCH_ASSUM_RENAME_TAC `verify_fcs fu0 su = SOME fu` [] THEN
`s SUBMAP su ∧ nwfs su` by METIS_TAC [nunify_uP,uP_def] THEN
`fe SUBSET fu0` by METIS_TAC [nunify_extends_fe] THEN
`FINITE fu0` by METIS_TAC [nunify_FINITE_fe] THEN
MATCH_MP_TAC (GEN_ALL COMPAT_TRANS) THEN
Q.EXISTS_TAC `(su,fe)` THEN
REVERSE CONJ_TAC THEN1 (
  MATCH_MP_TAC (GEN_ALL SUBMAP_COMPAT) THEN
  IMP_RES_TAC verify_fcs_SUBSET THEN
  SRW_TAC [][] ) THEN
MATCH_MP_TAC (GEN_ALL COMPAT_TRANS) THEN
Q.EXISTS_TAC `(su,fu0)` THEN
CONJ_TAC THEN1 (
  METIS_TAC [COMPAT_REFL] ) THEN
MATCH_MP_TAC (GEN_ALL SUBSET_COMPAT) THEN
SRW_TAC [][])

val nvwalk_irrelevant_FUPDATE = Q.store_thm(
"nvwalk_irrelevant_FUPDATE",
`nwfs (s|+(vx,tx)) /\ vx NOTIN FDOM s ==>
  !p v.~(nvR s)^* vx v ==> (nvwalk (s|+(vx,tx)) p v = nvwalk s p v)`,
STRIP_TAC THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
HO_MATCH_MP_TAC nvwalk_ind THEN
SRW_TAC [][] THEN
`vx <> v` by METIS_TAC [RTC_REFL] THEN
Cases_on `FLOOKUP s v` THEN1 (
  `v NOTIN FDOM s /\ v NOTIN FDOM (s|+(vx,tx))`
     by (POP_ASSUM MP_TAC THEN SRW_TAC [][FLOOKUP_DEF]) THEN
  SRW_TAC [][NOT_FDOM_nvwalk] ) THEN
Cases_on `is_Sus x` THEN1 (
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `nvR s v' v` by FULL_SIMP_TAC (srw_ss()) [nvR_def] THEN
  `~(nvR s)^* vx v'` by METIS_TAC [RTC_SUBSET,RTC_TRANSITIVE,transitive_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `p'` MP_TAC) THEN
  SRW_TAC [][] THEN
  ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,SimpLHS,FLOOKUP_UPDATE,nvwalk_case_thms] THEN
  ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,SimpRHS,FLOOKUP_UPDATE,nvwalk_case_thms] )
THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,SimpLHS,FLOOKUP_UPDATE,nvwalk_case_thms] THEN
ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,SimpRHS,FLOOKUP_UPDATE,nvwalk_case_thms])

val nvR_SUBMAP = Q.prove(
`s SUBMAP sx ==> nvR s u v ==> nvR sx u v`,
Cases_on `FLOOKUP s v` THEN
SRW_TAC [][nvR_def] THEN
`FLOOKUP sx v = SOME x` by METIS_TAC [FLOOKUP_SUBMAP] THEN
SRW_TAC [][])

val TC_nvR_SUBMAP = Q.store_thm(
"TC_nvR_SUBMAP",
`s SUBMAP sx ==> !u v.(nvR s)^+ u v ==> (nvR sx)^+ u v`,
STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT THEN
SRW_TAC [][] THEN1 METIS_TAC [TC_SUBSET,nvR_SUBMAP] THEN
METIS_TAC [TC_RULES])

val nvwalk_FUPDATE_var = Q.store_thm(
"nvwalk_FUPDATE_var",
`nwfs (s |+ (vx,tx)) ∧ vx ∉ FDOM s ⇒
 (nvwalk (s |+ (vx,tx)) [] vx = nwalk s tx)`,
STRIP_TAC THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
Cases_on `is_Sus tx` THEN1 (
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def,SimpLHS,FLOOKUP_UPDATE,nvwalk_case_thms] THEN
  Q_TAC SUFF_TAC `~(nvR s)^* vx v` THEN1 METIS_TAC [nvwalk_irrelevant_FUPDATE] THEN
  Cases_on `vx = v` THEN1 (
    `nvR (s|+(vx,Sus p v)) vx v` by FULL_SIMP_TAC (srw_ss()) [nvR_def,FLOOKUP_UPDATE] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [nwfs_no_cycles] THEN
    METIS_TAC [TC_SUBSET] ) THEN
    SRW_TAC [][RTC_CASES_TC] THEN
    FULL_SIMP_TAC (srw_ss()) [nwfs_no_cycles] THEN
    `s SUBMAP (s|+(vx,Sus p v))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    IMP_RES_TAC TC_nvR_SUBMAP THEN
    `nvR (s|+(vx,Sus p v)) v vx` by FULL_SIMP_TAC (srw_ss()) [nvR_def,FLOOKUP_UPDATE] THEN
    METIS_TAC [TC_RULES] ) THEN
Cases_on `tx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][Once nvwalk_def,SimpLHS,FLOOKUP_UPDATE])

val nwalkstar_irrelevant_FUPDATE = Q.store_thm(
"nwalkstar_irrelevant_FUPDATE",
`nwfs (s|+(vx,tx)) ∧ vx ∉ FDOM s ∧ ¬ noc s t vx ⇒
 (nwalk* (s|+(vx,tx)) t = nwalk* s t)`,
Q_TAC SUFF_TAC
`nwfs (s|+(vx,tx)) ∧ vx ∉ FDOM s ⇒
∀t. ¬ noc s t vx ⇒ (nwalk* (s|+(vx,tx)) t = nwalk* s t)`
THEN1 METIS_TAC [] THEN
STRIP_TAC THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
HO_MATCH_MP_TAC (Q.INST [`s`|->`s|+(vx,tx)`]nwalkstar_ind) THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
`vx ∉ nvars (nwalk* s (Sus l n))`
by (SRW_TAC [][GSYM noc_eq_nvars_nwalkstar,IN_DEF]) THEN
(TC_nvR_nvars_nwalkstar |> UNDISCH |>
 Q.SPECL [`Sus l n`,`vx`] |>
 SIMP_RULE (srw_ss()) [LEFT_FORALL_IMP_THM] |>
 CONTRAPOS |> MP_TAC) THEN
SRW_TAC [][] THEN
`n ≠ vx` by (
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  Q.PAT_ASSUM `vx ∉ FDOM s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_nvwalk] ) THEN
`~(nvR s)^* vx n` by METIS_TAC [RTC_CASES_TC] THEN
IMP_RES_TAC nvwalk_irrelevant_FUPDATE THEN
Q.PAT_ASSUM `nwfs (s|+(vx,tx))` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `nvwalk s l n` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [noc_eq_nvars_nwalkstar] THEN
METIS_TAC [IN_DEF,IN_UNION])

val extension_is_nwfs = Q.store_thm(
"extension_is_nwfs",
`nwfs (s|+(vx,tx)) ∧ vx ∉ FDOM s ⇒
 nwfs s ∧ ¬ noc s tx vx`,
STRIP_TAC THEN
`s SUBMAP (s|+(vx,tx))` by METIS_TAC [SUBMAP_FUPDATE_EQN] THEN
CONJ1_TAC THEN1 (
  METIS_TAC [nwfs_no_cycles,TC_nvR_SUBMAP] ) THEN
STRIP_TAC THEN
IMP_RES_TAC noc_TC_nvR THEN
`nvR (s|+(vx,tx)) u vx` by (
  SRW_TAC [][nvR_def,FLOOKUP_UPDATE] ) THEN
IMP_RES_TAC RTC_CASES_TC THEN1
  METIS_TAC [nwfs_no_cycles,TC_SUBSET] THEN
IMP_RES_TAC TC_nvR_SUBMAP THEN
METIS_TAC [nwfs_no_cycles,TC_RULES]);

val nwalkstar_FUPDATE_var = Q.store_thm(
"nwalkstar_FUPDATE_var",
`nwfs (s|+(vx,tx)) ∧ vx ∉ FDOM s ⇒
 (nwalk* (s|+(vx,tx)) (Sus [] vx) = nwalk* s tx)`,
STRIP_TAC THEN
`nwfs s` by METIS_TAC [nwfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
Q_TAC SUFF_TAC
`nwalk* (s|+(vx,tx)) (nwalk s tx) = nwalk* s (nwalk s tx)`
THEN1 (
  `nwalk (s|+(vx,tx)) (Sus [] vx) = nwalk s tx`
  by (SRW_TAC [][nvwalk_FUPDATE_var]) THEN
  METIS_TAC [nwalkstar_nwalk] ) THEN
MATCH_MP_TAC nwalkstar_irrelevant_FUPDATE THEN
SRW_TAC [][] THEN
IMP_RES_TAC extension_is_nwfs THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC (srw_ss()) [noc_eq_nvars_nwalkstar] THEN
METIS_TAC [nwalkstar_nwalk]);

val equiv_extend = Q.store_thm ((* Lemma 3.3 ; nominal version of nwalkstar_extend ?*)
"equiv_extend",
`nwfs s1 ∧ nwfs (s|+(vx,apply_pi (REVERSE pi) tx)) ∧ vx ∉ FDOM s ∧
 equiv fe (nwalk* s1 (Sus pi vx)) (nwalk* s1 (nwalk* s tx)) ⇒
 ∀t. equiv fe (nwalk* s1 (nwalk* (s|+(vx,apply_pi (REVERSE pi) tx)) t)) (nwalk* s1 (nwalk* s t))`,
STRIP_TAC THEN
Q.ABBREV_TAC `sx = (s|+(vx,apply_pi (REVERSE pi) tx))` THEN
`nwfs s ∧ s SUBMAP sx` by METIS_TAC [nwfs_SUBMAP,SUBMAP_FUPDATE_EQN] THEN
HO_MATCH_MP_TAC nwalkstar_ind THEN SRW_TAC [][] THEN
`(nwalk* s t = nwalk* s (nwalk s t)) ∧
 (nwalk* sx t = nwalk* sx (nwalk s t))`
 by METIS_TAC [nwalkstar_nwalk,nwalkstar_nwalk_SUBMAP] THEN
Cases_on `nwalk s t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  `n ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  REVERSE (Cases_on `n = vx`) THEN1 (
    `nwalk* sx (Sus l n) = nwalk* s (Sus l n)`
    by (Q.UNABBREV_TAC `sx` THEN
        MATCH_MP_TAC nwalkstar_irrelevant_FUPDATE THEN
        SRW_TAC [][noc_eq_nvars_nwalkstar,NOT_FDOM_nvwalk] ) THEN
    POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] ) THEN
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `equiv fe (nwalk* s1 (nwalk* sx (Sus [] n))) (nwalk* s1 (nwalk* s (Sus [] n)))`
  THEN1 ( STRIP_TAC THEN
          IMP_RES_TAC equiv_apply_pi THEN
          POP_ASSUM (K ALL_TAC) THEN
          POP_ASSUM (Q.SPEC_THEN `l` MP_TAC) THEN
          ASM_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi] ) THEN
  MATCH_MP_TAC equiv_sym THEN
  `equiv fe (apply_pi (REVERSE pi) (nwalk* s1 (Sus pi n)))
   (apply_pi (REVERSE pi) (nwalk* s1 (nwalk* s tx)))`
  by (MATCH_MP_TAC equiv_apply_pi THEN SRW_TAC [][]) THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi] THEN
  ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  `nwalk* sx (Sus [] n) = nwalk* s (apply_pi (REVERSE pi) tx)`
  by (Q.UNABBREV_TAC `sx` THEN
      MATCH_MP_TAC nwalkstar_FUPDATE_var THEN
      SRW_TAC [][] ) THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] )
THEN1 (SRW_TAC [][Once equiv_cases])
THEN1 (SRW_TAC [][Once equiv_cases]));

val nvars_nwalkstar_subterm = Q.store_thm(
"nvars_nwalkstar_subterm",
`nwfs s ⇒
 ((∃v1. v1 ∈ nvars t ∧ v2 ∈ nvars (nwalk* s (Sus [] v1))) ⇔ v2 ∈ nvars (nwalk* s t))`,
STRIP_TAC THEN EQ_TAC THEN1 (
  STRIP_TAC THEN
  IMP_RES_TAC noc_eq_nvars_nwalkstar THEN
  IMP_RES_TAC noc_TC_nvR THEN
  IMP_RES_TAC noc_NOTIN_FDOM THEN
  FULL_SIMP_TAC (srw_ss()) [RTC_CASES_TC] THEN
  SRW_TAC [][] THEN1
    IMP_RES_TAC NOT_FDOM_nwalkstar THEN
  METIS_TAC [TC_nvR_nvars_nwalkstar]) THEN
SPEC_ALL_TAC [`s`,`t`] THEN
Q.ID_SPEC_TAC `t` THEN
HO_MATCH_MP_TAC nwalkstar_ind THEN
SRW_TAC [][] THEN
`nwalk* s t = (nwalk* s (nwalk s t))` by METIS_TAC [nwalkstar_nwalk] THEN
Cases_on `nwalk s t` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
  `n ∉ FDOM s` by METIS_TAC [nvwalk_to_var] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l'`,`n'`] |> GSYM |> MP_TAC) THEN
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql] )
THEN1 (
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [apply_pi_eql,nwalkstar_apply_pi] )
THEN1 (
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [apply_pi_eql,nwalkstar_apply_pi] THEN
  SRW_TAC [][] THEN METIS_TAC [])
THEN1 (
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [apply_pi_eql,nwalkstar_apply_pi] THEN
  SRW_TAC [][] THEN METIS_TAC []));

val equiv_ties_fcs = Q.store_thm(
"equiv_ties_fcs",
`equiv fe (Tie a1 t1) (Tie a2 t2) ∧ a1 ≠ a2 ⇒
 ∃fcs. (term_fcs a1 t2 = SOME fcs) ∧ fcs SUBSET fe`,
SRW_TAC [][Once equiv_cases] THEN
Cases_on `term_fcs a1 t2` THEN1 (
  IMP_RES_TAC term_fcs_NONE ) THEN
IMP_RES_TAC term_fcs_minimal THEN
SRW_TAC [][])

val fresh_FINITE = Q.store_thm(
"fresh_FINITE",
`fresh fe a t ⇒ ∃fcs. fcs SUBSET fe ∧ FINITE fcs ∧ fresh fcs a t`,
Induct_on `t` THEN ASM_SIMP_TAC (psrw_ss()) [fresh_def] THEN SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `x ∈ fe` [] THEN
  Q.EXISTS_TAC `{x}` THEN SRW_TAC [][] )
THEN1 (
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  RES_TAC THEN METIS_TAC [] )
THEN1 (
  RES_TAC THEN
  Q.EXISTS_TAC `fcs ∪ fcs'` THEN
  SRW_TAC [][] THEN
  METIS_TAC [fresh_extra_fcs,SUBSET_UNION] )
THEN Q.EXISTS_TAC `{}` THEN SRW_TAC [][] );

val equiv_FINITE = Q.store_thm(
"equiv_FINITE",
`∀t1 t2. equiv fe t1 t2 ⇒ ∃fcs. fcs SUBSET fe ∧ FINITE fcs ∧ equiv fcs t1 t2`,
HO_MATCH_MP_TAC equiv_ind THEN SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  Q.EXISTS_TAC `IMAGE (λa. (a,v)) (dis_set p1 p2)` THEN
  SRW_TAC [][SUBSET_DEF] THEN1 SRW_TAC [][] THEN
  MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`] THEN
  SRW_TAC [][] )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  Q.EXISTS_TAC `fcs` THEN SRW_TAC [][] )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  IMP_RES_TAC fresh_FINITE THEN
  Q.EXISTS_TAC `fcs ∪ fcs'` THEN
  SRW_TAC [][] THEN1 (
    METIS_TAC [fresh_extra_fcs,SUBSET_UNION] )
  THEN METIS_TAC [equiv_SUBSET,SUBSET_UNION] )
THEN1 (
  SRW_TAC [][Once equiv_cases] THEN
  Q.EXISTS_TAC `fcs ∪ fcs'` THEN
  SRW_TAC [][] THEN
  METIS_TAC [equiv_SUBSET,SUBSET_UNION] )
THEN Q.EXISTS_TAC `{}` THEN SRW_TAC [][])

val term_fcs_irrelevant_nwalkstar = Q.store_thm(
"term_fcs_irrelevant_nwalkstar",
`(term_fcs b t = SOME fcs) ∧
 (term_fcs b (nwalk* s t) = SOME fcs2) ∧
 (a,v) ∈ fcs ∧ v ∉ FDOM s ∧
 nwfs s ⇒
 (a,v) ∈ fcs2`,
SRW_TAC [][] THEN
`∃fcs1. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs1) ∧ fcs1 ⊆ fcs2`
by METIS_TAC [term_fcs_nwalkstar] THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def,EXTENSION] THEN
SRW_TAC [][SUBSET_DEF] THEN METIS_TAC []);

val ee = equiv_extend |> UNDISCH |> SPEC_ALL |> DISCH_ALL |> Q.GEN `tx` |> Q.GEN `pi`

val nomunify_mgu2 = Q.store_thm(
"nomunify_mgu2",
`∀s fe t1 t2 sx fex.
(nomunify (s,fe) t1 t2 = SOME (sx,fex)) ∧
(equiv fe2 (nwalk* s2 (nwalk* s t1)) (nwalk* s2 (nwalk* s t2))) ∧ nwfs s2 ∧ nwfs s ∧ FINITE fe
⇒ (∀t. equiv fe2 (nwalk* s2 (nwalk* sx t)) (nwalk* s2 (nwalk* s t)))`,
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][] THEN
`nwfs sx ∧ s SUBMAP sx ∧ FINITE fex ∧ equiv fex (nwalk* sx t1) (nwalk* sx t2)`
by (IMP_RES_TAC nomunify_unifier THEN SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [nomunify_def] THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Nom a` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`Nom a`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  METIS_TAC [equiv_sym] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Nom a` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`Nom a`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  METIS_TAC [equiv_sym] )
THEN1 (
  Cases_on `x` THEN
  IMP_RES_TAC unify_eq_vars_preserves_s THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = Sus pi1 vx` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = Sus pi2 v2` [] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi1`,`Sus pi2 v2`] |> SIMP_RULE (psrw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Tie a c` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`Tie a c`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = nPair c1 c2` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`nPair c1 c2`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = nConst c` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`nConst c`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Tie a c` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`Tie a c`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  METIS_TAC [equiv_sym])
THEN1 (
  POP_ASSUM MP_TAC THEN SRW_TAC [][] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  Q.PAT_ASSUM `equiv fe2 X Y` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once equiv_cases] )
THEN1 (
  NTAC 2 (POP_ASSUM MP_TAC) THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  `FINITE fcs` by METIS_TAC [term_fcs_FINITE] THEN
  Q.PAT_ASSUM `equiv fe2 X Y` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once equiv_cases,nwalkstar_apply_pi] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = nPair c1 c2` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`nPair c1 c2`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  METIS_TAC [equiv_sym])
THEN1 (
  Cases_on `x` THEN Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) t1a t2a = SOME (sa,fa)` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (sa,fa) t1d t2d = SOME (sd,fd)` [] THEN
  `nwfs sa ∧ FINITE fa ∧ fa ⊆ fd ∧ FINITE fd ∧ sa SUBMAP sd ∧ nwfs sd`
  by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe,nunify_extends_fe] THEN
  `∃fad. (verify_fcs fa sd = SOME fad)` by METIS_TAC [verify_fcs_SUBSET] THEN
  `∃faa. (verify_fcs fa sa = SOME faa)`
  by METIS_TAC [verify_fcs_SUBMAP] THEN
  NTAC 2 (Q.PAT_ASSUM `!X.Y` MP_TAC) THEN
  SRW_TAC [][] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  Q.PAT_ASSUM `equiv fe2 X Y` MP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  METIS_TAC [equiv_trans,equiv_refl,equiv_sym] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = Sus pi vx` ["X"] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s X = nConst c` ["X"] THEN
  MATCH_MP_TAC (ee |> Q.SPECL [`pi`,`nConst c`] |> SIMP_RULE (srw_ss()) []) THEN
  `vx ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  `(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
   (nwalk* s t2 = nwalk* s (nwalk s t2))` by METIS_TAC [nwalkstar_nwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  METIS_TAC [equiv_sym]));

val term_fcs_equiv = Q.store_thm(
"term_fcs_equiv",
`equiv fe t1 t2 ∧ (term_fcs a t1 = SOME fcs1) ∧ fcs1 ⊆ fe ⇒
 ∃fcs2. (term_fcs a t2 = SOME fcs2) ∧ fcs2 ⊆ fe`,
Q_TAC SUFF_TAC
`∀t1 t2. equiv fe t1 t2 ⇒ ∀fcs.
(term_fcs a t1 = SOME fcs) ∧ fcs ⊆ fe ⇒ ∃fcs2. (term_fcs a t2 = SOME fcs2) ∧ fcs2 ⊆ fe`
THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC equiv_ind THEN
STRIP_TAC THEN1
  NTAC 2 (SRW_TAC [][Once term_fcs_def])
THEN STRIP_TAC THEN1 (
  NTAC 2 (ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def]) THEN
  SRW_TAC [][dis_set_def,SUBSET_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `lswapstr (REVERSE p1) a = lswapstr (REVERSE p2) a` THEN1 METIS_TAC [] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `lswapstr (REVERSE p1) (lswapstr p1 (lswapstr (REVERSE p2) a)) ≠ lswapstr (REVERSE p2) a`
  by METIS_TAC [] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [])
THEN STRIP_TAC THEN1 (
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `term_fcs a X = Y` MP_TAC THEN
  NTAC 2 (SRW_TAC [][Once term_fcs_def]) )
THEN STRIP_TAC THEN1 (
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `term_fcs a X = Y` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN1 (
    SRW_TAC [][Once term_fcs_def] THEN
    Cases_on `term_fcs a t2` THEN1
      IMP_RES_TAC term_fcs_NONE THEN
    IMP_RES_TAC term_fcs_minimal THEN
    METIS_TAC [] ) THEN
  SRW_TAC [][Once term_fcs_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC term_fcs_apply_pi THEN
  POP_ASSUM (Q.SPEC_THEN `REVERSE [(a1,a2)]` MP_TAC) THEN
  SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC (srw_ss()) [])
THEN STRIP_TAC THEN1 (
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `term_fcs a X = Y` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  SRW_TAC [][Once term_fcs_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN NTAC 2 (SRW_TAC [][Once term_fcs_def]));

val nvwalk_SUBMAP_idem = Q.store_thm(
"nvwalk_SUBMAP_idem",
`nwfs sx ∧ s SUBMAP sx ⇒ ∀pi v. nwalk s (nvwalk sx pi v) = nvwalk sx pi v`,
STRIP_TAC THEN IMP_RES_TAC nwfs_SUBMAP THEN
HO_MATCH_MP_TAC (Q.INST[`s`|->`sx`]nvwalk_ind) THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP sx v` THEN1 (
  Cases_on `FLOOKUP s v` THEN
  IMP_RES_TAC FLOOKUP_SUBMAP THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  NTAC 3 (SRW_TAC [][Once nvwalk_def]) ) THEN
Cases_on `x` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
TRY (
  NTAC 2 (ASM_SIMP_TAC (psrw_ss()) [Once nvwalk_def]) THEN
  NO_TAC ) THEN
ASM_SIMP_TAC (srw_ss()) [Once nvwalk_def] THEN
ASM_SIMP_TAC (srw_ss()) [Once nvwalk_def,SimpRHS] THEN
SELECT_ELIM_TAC THEN
SRW_TAC [][] THEN
METIS_TAC [nvwalk_eq_perms,permeq_refl,app_permeq_monotone]);

val nwalkstar_SUBMAP_idem = Q.store_thm(
"nwalkstar_SUBMAP_idem",
`nwfs sx ∧ s SUBMAP sx ⇒ ∀t.nwalk* s (nwalk* sx t) = nwalk* sx t`,
STRIP_TAC THEN IMP_RES_TAC nwfs_SUBMAP THEN
HO_MATCH_MP_TAC (Q.INST[`s`|->`sx`]nwalkstar_ind) THEN
SRW_TAC [][] THEN
`nwalk* sx t = nwalk* sx (nwalk sx t)` by METIS_TAC [nwalkstar_nwalk] THEN
Cases_on `nwalk s t` THEN
MP_TAC nwalk_SUBMAP THEN SRW_TAC [][] THEN
Cases_on `nwalk sx t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN
Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
Cases_on `nvwalk sx l' n'` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
IMP_RES_TAC nvwalk_to_var THEN
Q.MATCH_ASSUM_RENAME_TAC `v ∉ FDOM sx` [] THEN
`v ∉ FDOM s` by METIS_TAC [SUBMAP_DEF,SUBSET_DEF] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [NOT_FDOM_nvwalk]);

val unify_eq_vars_NOTIN_FDOM = Q.store_thm(
"unify_eq_vars_NOTIN_FDOM",
`FINITE ds ∧ nwfs s ∧ (unify_eq_vars ds v (s,fe) = SOME (s',fex)) ∧ (b,w) ∉ fe ∧ (b,w) ∈ fex ⇒ w ∉ FDOM s`,
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
STRIP_TAC THEN
SPEC_ALL_TAC [`ds`] THEN
POP_ASSUM MP_TAC THEN
Q.ID_SPEC_TAC `ds` THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SIMP_TAC (srw_ss()) [unify_eq_vars_def,ITSET_EMPTY] THEN
SRW_TAC [][] THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `X = SOME fex'` MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT,fcs_acc_RECURSES,fcs_acc_def,image_lem] THEN
FULL_SIMP_TAC (srw_ss()) [GSYM DELETE_NON_ELEMENT] THEN
SRW_TAC [][GSYM DELETE_NON_ELEMENT] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  FIRST_X_ASSUM (Q.SPECL_THEN [`s`,`v`,`{}`,`s`,`x1`,`b`,`w`] MP_TAC)
  THEN SRW_TAC [][] ) THEN
MATCH_MP_TAC (GEN_ALL term_fcs_NOTIN_FDOM) THEN
MAP_EVERY Q.EXISTS_TAC [`Sus [] v`,`x2`,`b`,`e`] THEN
SRW_TAC [][]);

val nunify_fcs_NOTIN_FDOM = Q.store_thm (
"nunify_fcs_NOTIN_FDOM",
`∀s fe t1 t2 sx fex. nwfs s ∧ FINITE fe ∧
(nunify (s,fe) t1 t2 = SOME (sx,fex)) ∧ (a,v) ∉ fe ∧ (a,v) ∈ fex ⇒
v ∉ FDOM s`,
HO_MATCH_MP_TAC nunify_ind THEN SRW_TAC [][] THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
ASM_SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  IMP_RES_TAC unify_eq_vars_NOTIN_FDOM THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  NTAC 2 (POP_ASSUM MP_TAC) THEN
  SRW_TAC [][] THEN
  Cases_on `(a,v) ∈ fcs` THEN1 (
    IMP_RES_TAC term_fcs_NOTIN_FDOM ) THEN
  IMP_RES_TAC term_fcs_FINITE THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
Cases_on `x` THEN SRW_TAC [][] THEN
Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) t1a t2a = SOME (sa,fa)` [] THEN
Cases_on `(a,v) ∈ fa` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`nwfs sa ∧ FINITE fa ∧ s SUBMAP sa` by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe] THEN
METIS_TAC [SUBMAP_DEF,SUBSET_DEF]);

val GEN_SUBMAP_FUPDATE_EQN = Q.store_thm(
"GEN_SUBMAP_FUPDATE_EQN",
`f SUBMAP g |+ (k,v) ⇔ k ∉ FDOM f ∧ f SUBMAP g ∨ k ∈ FDOM f ∧ (f \\ k) SUBMAP g ∧ (f ' k = v)`,
SRW_TAC [][EQ_IMP_THM] THEN1 (
  Cases_on `k ∈ FDOM f` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [SUBMAP_DEF] THEN
  SRW_TAC [][DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM] THEN
  METIS_TAC []  ) THEN
FULL_SIMP_TAC (srw_ss()) [SUBMAP_DEF,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM] THEN
SRW_TAC [][])

val fresh_term_fcs = Q.store_thm(
"fresh_term_fcs",
`fresh fe a t ⇒ (∃fcs. (term_fcs a t = SOME fcs) ∧ fcs ⊆ fe)`,
SRW_TAC [][] THEN Cases_on `term_fcs a t` THEN
IMP_RES_TAC term_fcs_NONE THEN
IMP_RES_TAC term_fcs_minimal THEN
SRW_TAC [][]);

val equiv_fcs_q = `
  (equiv_fcs (Nom a) (Nom b) = if a = b then SOME {} else NONE) ∧
  (equiv_fcs (Sus p1 v1) (Sus p2 v2) =
   if v1 = v2 then SOME {(a,v1) | a ∈ dis_set p1 p2} else NONE) ∧
  (equiv_fcs (Tie a1 t1) (Tie a2 t2) =
   if a1 = a2 then equiv_fcs t1 t2
   else OPTION_MAP2 $UNION (term_fcs a1 t2) (equiv_fcs t1 (apply_pi [(a1,a2)] t2))) ∧
  (equiv_fcs (nPair t1a t1d) (nPair t2a t2d) = OPTION_MAP2 $UNION (equiv_fcs t1a t2a) (equiv_fcs t1d t2d)) ∧
  (equiv_fcs (nConst c1) (nConst c2) = if c1 = c2 then SOME {} else NONE) ∧
  (equiv_fcs t1 t2 = NONE)`

val equiv_fcs_def = RWDefine equiv_fcs_q;
val _ = store_term_thm("equiv_fcs_def_print",TermWithCase equiv_fcs_q);

val equiv_fcs_minimal = Q.store_thm(
"equiv_fcs_minimal",
`∀t1 t2. equiv fe t1 t2 ⇒ ∃fe0. (equiv_fcs t1 t2 = SOME fe0) ∧ fe0 ⊆ fe`,
HO_MATCH_MP_TAC equiv_ind THEN
ASM_SIMP_TAC (psrw_ss()) [] THEN
SRW_TAC [][] THEN1 (
  SRW_TAC [][SUBSET_DEF] THEN
  RES_TAC )
THEN1 (
  IMP_RES_TAC fresh_term_fcs THEN
  SRW_TAC [][] ) THEN
SRW_TAC [][]);

val equiv_fcs_equiv = Q.store_thm(
"equiv_fcs_equiv",
`∀t1 t2 fe. (equiv_fcs t1 t2 = SOME fe) ⇒ equiv fe t1 t2`,
Induct THEN Cases_on `t2` THEN
FULL_SIMP_TAC (psrw_ss()) [] THEN
SRW_TAC [][] THEN
SRW_TAC [][Once equiv_cases] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [permeq_refl,equiv_SUBSET,SUBSET_UNION,fresh_extra_fcs,term_fcs_fresh]);

val nwalk_apply_pi = Q.store_thm(
"nwalk_apply_pi",
`nwfs s ⇒ (nwalk s (apply_pi pi t) = apply_pi pi (nwalk s t))`,
Induct_on `t` THEN ASM_SIMP_TAC (psrw_ss()) [] THEN
SRW_TAC [][] THEN
(nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> MP_TAC) THEN
(nvwalk_modulo_pi |> Q.SPECL [`s`,`pi ++ l`,`n`] |> MP_TAC) THEN
SRW_TAC [][apply_pi_decompose]);

val _ = add_rule {
  fixity = Infix(NONASSOC,450),
  term_name = "equiv",
  block_style = (AroundEachPhrase,(PP.INCONSISTENT,2)),
  paren_style = OnlyIfNecessary,
  pp_elements =
  [BreakSpace(1,2),TOK"⊢",BreakSpace(1,2),TM,BreakSpace(1,2),TOK"≈",BreakSpace(1,2)] }

val _ = add_rule {
  fixity = Infix(NONASSOC,450),
  term_name = "fresh",
  block_style = (AroundEachPhrase,(PP.INCONSISTENT,2)),
  paren_style = OnlyIfNecessary,
  pp_elements =
  [BreakSpace(1,2),TOK"⊢",BreakSpace(1,2),TM,BreakSpace(1,2),TOK"#",BreakSpace(1,2)] }

val equiv_fcs_nwalkstar = Q.store_thm(
"equiv_fcs_nwalkstar",
`(equiv_fcs t1 t2 = SOME fe1) ∧
 (equiv_fcs (nwalk* s t1) (nwalk* s t2) = SOME fe2) ∧
 (a,v) ∈ fe1 ∧ nwfs s ⇒
 ∃fcs. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧ fcs ⊆ fe2`,
MAP_EVERY Q.ID_SPEC_TAC [`fe2`,`fe1`,`t2`,`t1`] THEN
Induct THEN Cases_on `t2` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN1 (
  SRW_TAC [][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `equiv_fcs (nwalk* s (Sus p1 v)) (nwalk* s (Sus p2 v)) = SOME fe2` [] THEN
  `equiv fe2 (apply_pi p1 (nwalk* s (Sus [] v))) (apply_pi p2 (nwalk* s (Sus [] v)))` by (
    IMP_RES_TAC equiv_fcs_equiv THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi] ) THEN
  IMP_RES_TAC equiv_ds_fresh THEN
  IMP_RES_TAC fresh_term_fcs THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  SRW_TAC [][] THEN1 (
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [] ) THEN
  Q.PAT_ASSUM `a1 ≠ a2` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    IMP_RES_TAC term_fcs_nwalkstar THEN
    Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [SUBSET_UNION,SUBSET_TRANS] ) THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM nwalkstar_apply_pi] THEN
  RES_TAC THEN
  METIS_TAC [SUBSET_UNION,SUBSET_TRANS] )
THEN1 (
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  RES_TAC THEN
  METIS_TAC [SUBSET_UNION,SUBSET_TRANS] ));

val term_fcs_SUBMAP = Q.store_thm(
"term_fcs_SUBMAP",
`(term_fcs a (nwalk* s t) = SOME fcs) ∧ nwfs s ⇒
 ∃fe0. (term_fcs a t = SOME fe0) ∧
 ∀b w. (b,w) ∈ fe0 ⇒ ∃fe1. (term_fcs b (nwalk* s (Sus [] w)) = SOME fe1) ∧ fe1 ⊆ fcs`,
REPEAT STRIP_TAC THEN
IMP_RES_TAC term_fcs_fresh THEN
IMP_RES_TAC fresh_SUBMAP THEN
IMP_RES_TAC fresh_term_fcs THEN
Q.MATCH_ASSUM_RENAME_TAC `term_fcs a t = SOME fe0` [] THEN
Q.EXISTS_TAC `fe0` THEN CONJ_TAC THEN1 SRW_TAC [][] THEN
REPEAT STRIP_TAC THEN
`(b,w) ∈ fe` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
RES_TAC THEN
IMP_RES_TAC fresh_term_fcs THEN
SRW_TAC [][])

val term_fcs_nwalkstar_backwards = Q.store_thm(
"term_fcs_nwalkstar_backwards",
`nwfs s ∧ (term_fcs b (nwalk* s t) = SOME fcs) ∧ (a,v) ∈ fcs ∧
 (term_fcs b t = SOME fe0) ⇒
 ∃c w fe1. (c,w) ∈ fe0 ∧ (term_fcs c (nwalk* s (Sus [] w)) = SOME fe1) ∧ (a,v) ∈ fe1`,
STRIP_TAC THEN
NTAC 3 (POP_ASSUM MP_TAC) THEN
SPEC_ALL_TAC [`t`,`s`] THEN
Q.ID_SPEC_TAC `t` THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
REPEAT STRIP_TAC THEN
`nwalk* s t = nwalk* s (nwalk s t)` by METIS_TAC [nwalkstar_nwalk] THEN
Cases_on `nwalk s t` THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  FULL_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  `n ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  FULL_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
  SRW_TAC [][] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l'`,`n'`] |> GSYM |> MP_TAC) THEN
  ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql] THEN
  SRW_TAC [][REVERSE_APPEND,pmact_decompose] )
THEN1 (
  Q.PAT_ASSUM `X = SOME fcs` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  Cases_on `b = s'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Q.PAT_ASSUM `X = SOME fe0` MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
    SRW_TAC [][] THEN SRW_TAC [][] THEN
    (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
    ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql] THEN
    SRW_TAC [][Once term_fcs_def,nwalkstar_apply_pi] THEN
    Q.EXISTS_TAC `fcs` THEN SRW_TAC [][] THEN
    MATCH_MP_TAC term_fcs_apply_pi THEN
    SRW_TAC [][] ) THEN
  Q.PAT_ASSUM `X = SOME fe0` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  METIS_TAC [] )
THEN1 (
  Q.PAT_ASSUM `X = SOME fcs` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Q.PAT_ASSUM `X = SOME fe0` MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
    SRW_TAC [][] THEN SRW_TAC [][] THEN
    (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
    ASM_SIMP_TAC (psrw_ss()) [apply_pi_eql] THEN
    SRW_TAC [][Once term_fcs_def,nwalkstar_apply_pi] THEN
    Q.EXISTS_TAC `x1 ∪ x2` THEN SRW_TAC [][] THEN
    MAP_EVERY Q.EXISTS_TAC [`x1`,`x2`] THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC term_fcs_apply_pi THEN
    SRW_TAC [][] ) THEN
  Q.PAT_ASSUM `X = SOME fe0` MP_TAC THEN
  ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [Once term_fcs_def] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [])

val nomunify_equiv_fcs = Q.store_thm(
"nomunify_equiv_fcs",
`(nomunify (s,fe) t1 t2 = SOME (sx,fex)) ∧ (a,v) ∈ fex ∧ nwfs s ∧ FINITE fe ⇒
 (∃ b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* sx (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs) ∨
 (a,v) ∈ THE (equiv_fcs (nwalk* sx t1) (nwalk* sx t2))`,
Q_TAC SUFF_TAC
`∀s fe t1 t2 sx sxx b w fex fcs fem fev. (nunify (s,fe) t1 t2 = SOME (sx,fex)) ∧ (b,w) ∉ fe ∧ (b,w) ∈ fex ∧
  nwfs sxx ∧ sx SUBMAP sxx ∧
  (term_fcs b (nwalk* sxx (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs ∧
  nwfs s ∧ FINITE fe ∧ (equiv_fcs (nwalk* sxx t1) (nwalk* sxx t2) = SOME fem) ⇒
 (a,v) ∈ fem` THEN1 (
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC nomunify_unifier THEN
  NTAC 3 (Q.PAT_ASSUM `!X.Y` (K ALL_TAC)) THEN
  IMP_RES_TAC equiv_fcs_minimal THEN
  FULL_SIMP_TAC (srw_ss()) [nomunify_def,EXISTS_PROD] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) t1 t2 = SOME (sx,fx)` [] THEN
  `FINITE fx` by IMP_RES_TAC nunify_FINITE_fe THEN
  `∃b w fcs. (b,w) ∈ fx ∧ (term_fcs b (nwalk* sx (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs`
  by (MATCH_MP_TAC (GEN_ALL verify_fcs_minimal) THEN SRW_TAC [][]) THEN
  Q.PAT_ASSUM `nwfs sx` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `(b,w) ∈ fe` THEN1 METIS_TAC [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`s`,`fe`,`t1`,`t2`,`sx`,`sx`,`b`,`w`,`fx`,`fcs`,`fe0`] MP_TAC) THEN
  SRW_TAC [][] ) THEN
HO_MATCH_MP_TAC nunify_ind THEN REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `nunify p t1 t2 = SOME px` MP_TAC THEN
Q.PAT_ASSUM `nwfs s` MP_TAC THEN
Cases_on `nwalk s t1` THEN Cases_on `nwalk s t2` THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  POP_ASSUM MP_TAC THEN SRW_TAC [][] THEN1 (
    IMP_RES_TAC unify_eq_vars_preserves_s THEN
    IMP_RES_TAC unify_eq_vars_minimal THEN
    NTAC 2 (FULL_SIMP_TAC (srw_ss()) []) THEN
    SRW_TAC [][] THEN
    `(nwalk* sxx t1 = nwalk* sxx (nwalk s t1)) ∧
     (nwalk* sxx t2 = nwalk* sxx (nwalk s t2))`
    by METIS_TAC [nwalkstar_nwalk_SUBMAP] THEN
    Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
    `n ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
    FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
    IMP_RES_TAC equiv_fcs_equiv THEN
    `equiv fem (apply_pi l (nwalk* sxx (Sus [] n))) (apply_pi l' (nwalk* sxx (Sus [] n)))` by (
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC (psrw_ss()) [GSYM nwalkstar_apply_pi] ) THEN
    IMP_RES_TAC equiv_ds_fresh THEN
    Q.PAT_ASSUM `X = SOME fcs'` MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    IMP_RES_TAC term_fcs_minimal THEN
    FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] ) THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  POP_ASSUM MP_TAC THEN SRW_TAC [][] THEN1 (
    POP_ASSUM MP_TAC THEN
    `nwfs sx ∧ s SUBMAP sx` by METIS_TAC [nunify_uP,uP_def] THEN
    `(nwalk* sxx t1 = nwalk* sxx (nwalk s t1)) ∧
     (nwalk* sxx t2 = nwalk* sxx (nwalk s t2))`
    by METIS_TAC [nwalkstar_nwalk_SUBMAP,SUBMAP_TRANS] THEN
    Q.PAT_ASSUM `nwfs sxx` ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`sxx`,`b`,`w`] THEN
    SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = Tie a1 c1` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = Tie a2 c2` [] THEN
  `nwfs sx ∧ s SUBMAP sx` by METIS_TAC [nunify_uP,uP_def] THEN
  `(nwalk* sxx t1 = nwalk* sxx (nwalk s t1)) ∧
   (nwalk* sxx t2 = nwalk* sxx (nwalk s t2))`
  by METIS_TAC [nwalkstar_nwalk_SUBMAP,SUBMAP_TRANS] THEN
  IMP_RES_TAC equiv_fcs_equiv THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  STRIP_TAC THEN IMP_RES_TAC equiv_ties_fcs THEN
  Cases_on `(b,w) ∈ fcs'` THEN1 (
    (term_fcs_nwalkstar |>
     Q.INST [`s`|->`sxx`,`t`|->`nwalk* s c2`,`b`|->`a1`,`a`|->`b`,
             `v`|->`w`,`fcs`|->`fcs'`,`fcs2`|->`fcs''`] |>
     MP_TAC) THEN
    `nwalk* sxx (nwalk* s c2) = nwalk* sxx c2` by METIS_TAC [nwalkstar_SUBMAP,SUBMAP_TRANS] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] ) THEN
 Q.PAT_ASSUM `nwfs sxx` ASSUME_TAC THEN
 IMP_RES_TAC term_fcs_FINITE THEN
 FULL_SIMP_TAC (srw_ss()) [nwalkstar_apply_pi] THEN
 DISJ2_TAC THEN
 FIRST_X_ASSUM MATCH_MP_TAC THEN
 MAP_EVERY Q.EXISTS_TAC [`sxx`,`b`,`w`] THEN
 SRW_TAC [][nwalkstar_apply_pi])
THEN1 (
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) t1a t2a = SOME (sa,fa)` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (sa,fa) t1d t2d = SOME (sd,fd)` [] THEN
  `nwfs sa ∧ FINITE fa ∧ fa ⊆ fd ∧ FINITE fd ∧ s SUBMAP sa ∧ sa SUBMAP sd ∧ nwfs sd`
  by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe,nunify_extends_fe] THEN
  `(nwalk* sxx t1 = nwalk* sxx (nwalk s t1)) ∧
   (nwalk* sxx t2 = nwalk* sxx (nwalk s t2))`
  by METIS_TAC [nwalkstar_nwalk_SUBMAP,SUBMAP_TRANS] THEN
  Q.PAT_ASSUM `nwfs sxx` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  REVERSE (Cases_on `(b,w) ∈ fa`) THEN1 (
    NTAC 2 (FIRST_X_ASSUM (Q.SPECL_THEN [`sxx`,`b`,`w`] MP_TAC)) THEN
    SRW_TAC [][] ) THEN
  NTAC 2 (FIRST_X_ASSUM (Q.SPECL_THEN [`sxx`,`b`,`w`] MP_TAC)) THEN
  SRW_TAC [][] THEN
  DISJ1_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
  METIS_TAC [SUBMAP_TRANS] ))

val nomunify_mgu1 = Q.store_thm(
"nomunify_mgu1",
`(nomunify (s,fe) t1 t2 = SOME (sx,fex)) ∧ (a,v) ∈ fex ∧
(equiv fe2 (nwalk* s2 (nwalk* s t1)) (nwalk* s2 (nwalk* s t2))) ∧ nwfs s2 ∧ nwfs s ∧ FINITE fe
⇒ (∃ b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* sx (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs) ∨
fresh fe2 a (nwalk* s2 (Sus [] v))`,
REPEAT STRIP_TAC THEN
(nomunify_equiv_fcs |> SIMP_RULE bool_ss [GSYM AND_IMP_INTRO] |> funpow 4 UNDISCH |> STRIP_ASSUME_TAC )
THEN1 METIS_TAC [] THEN DISJ2_TAC THEN
`equiv fex (nwalk* sx t1) (nwalk* sx t2)` by METIS_TAC [nomunify_unifier] THEN
`∀t. equiv fe2 (nwalk* s2 (nwalk* sx t)) (nwalk* s2 (nwalk* s t))` by METIS_TAC [nomunify_mgu2] THEN
`equiv fe2 (nwalk* s2 (nwalk* sx t1)) (nwalk* s2 (nwalk* sx t2))` by METIS_TAC [equiv_trans,equiv_sym] THEN
IMP_RES_TAC equiv_fcs_minimal THEN
Q_TAC SUFF_TAC `∃fcs. (term_fcs a (nwalk* s2 (Sus [] v)) = SOME fcs) ∧ fcs ⊆ fe0`
THEN1 METIS_TAC [fresh_extra_fcs,term_fcs_fresh,SUBSET_TRANS] THEN
MATCH_MP_TAC (GEN_ALL equiv_fcs_nwalkstar) THEN
MAP_EVERY Q.EXISTS_TAC [`nwalk* sx t2`,`nwalk* sx t1`,`fe0'`] THEN
FULL_SIMP_TAC (srw_ss()) [])

val nomunify_mgu = Q.store_thm(
"nomunify_mgu",
`nwfs s ∧ FINITE fe ∧ (nomunify (s,fe) t1 t2 = SOME (sx,fex)) ∧
 nwfs s2 ∧ equiv fe2 (nwalk* s2 (nwalk* s t1)) (nwalk* s2 (nwalk* s t2)) ⇒
 (∀a v. (a,v) ∈ fex ⇒
   (∃b w fcs. (b,w) ∈ fe ∧ (term_fcs b (nwalk* sx (Sus [] w)) = SOME fcs) ∧ (a,v) ∈ fcs) ∨
   fresh fe2 a (nwalk* s2 (Sus [] v))) ∧
 (∀t. equiv fe2 (nwalk* s2 (nwalk* sx t)) (nwalk* s2 (nwalk* s t)))`,
REPEAT STRIP_TAC THEN1
(MATCH_MP_TAC nomunify_mgu1 THEN
 METIS_TAC []) THEN
METIS_TAC [nomunify_mgu2])

val equiv_consistent_exists = Q.store_thm(
"equiv_consistent_exists",
`equiv fe (nwalk* s t1) (nwalk* s t2) ∧ nwfs s ⇒ ∃fec.
 FINITE fec ∧
 (verify_fcs fec s = SOME fec) ∧
 equiv fec (nwalk* s t1) (nwalk* s t2)`,
Q_TAC SUFF_TAC
`∀fe w1 w2. equiv fe w1 w2 ⇒
∀t1 t2 s. FINITE fe ∧ nwfs s ∧ (nwalk* s t1 = w1) ∧ (nwalk* s t2 = w2) ⇒
  ∃fec. FINITE fec ∧ verify_fcs fec s ≠ NONE ∧ equiv fec w1 w2`
THEN1 (
  SRW_TAC [][] THEN
  IMP_RES_TAC equiv_FINITE THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`fcs`,`nwalk* s t1`,`nwalk* s t2`] MP_TAC) THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`t1`,`t2`,`s`] MP_TAC) THEN
  SRW_TAC [][] THEN
  Cases_on `verify_fcs fec s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.EXISTS_TAC `x` THEN SRW_TAC [][] THEN1
  METIS_TAC [verify_fcs_FINITE] THEN1
  METIS_TAC [verify_fcs_idem] THEN
  METIS_TAC [equiv_verify_fcs,nwalkstar_idempotent]) THEN
STRIP_TAC THEN HO_MATCH_MP_TAC equiv_ind THEN
SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] )
THEN1 (
  Q.EXISTS_TAC `IMAGE (λa. (a,v)) (dis_set p1 p2)` THEN SRW_TAC [][] THEN1 (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    IMP_RES_TAC verify_fcs_NONE THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `v ∉ FDOM s` by METIS_TAC [nwalkstar_to_var] THEN
    Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
    FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,Once term_fcs_def] ) THEN
  SRW_TAC [][Once equiv_cases] THEN
  METIS_TAC [permeq_refl] )
THEN1 (
  IMP_RES_TAC nwalkstar_subterm_exists THEN
  SRW_TAC [][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk* s t1 = Tie a (nwalk* s c1)`[] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk* s t2 = Tie a (nwalk* s c2)`[] THEN
  NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`c1`,`c2`,`s`] MP_TAC) THEN
  SRW_TAC [][] THEN
  SRW_TAC [][Once equiv_cases] THEN
  METIS_TAC [] )
THEN1 (
  IMP_RES_TAC nwalkstar_subterm_exists THEN
  SRW_TAC [][] THEN
  NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk* s t1 = Tie a1 (nwalk* s c1)`[] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk* s t2' = Tie a2 (nwalk* s c2)`[] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`c1`,`apply_pi [(a1,a2)] c2`,`s`] MP_TAC) THEN
  SRW_TAC [][nwalkstar_apply_pi] THEN
  SRW_TAC [][Once equiv_cases] THEN
  IMP_RES_TAC fresh_FINITE THEN
  IMP_RES_TAC fresh_term_fcs THEN
  IMP_RES_TAC term_fcs_FINITE THEN
  Cases_on `verify_fcs fec s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  `verify_fcs (fcs' ∪ fec) s = SOME (fcs' ∪ x)` by (
    MATCH_MP_TAC verify_fcs_UNION_I THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC (GEN_ALL verify_fcs_term_fcs) THEN
    MAP_EVERY Q.EXISTS_TAC [`nwalk* s c2`,`a1`] THEN
    METIS_TAC [nwalkstar_idempotent] ) THEN
  Q.EXISTS_TAC `fcs' ∪ fec` THEN SRW_TAC [][] THEN1
  METIS_TAC [term_fcs_fresh,fresh_extra_fcs,SUBSET_UNION] THEN
  METIS_TAC [equiv_SUBSET,SUBSET_UNION])
THEN1 (
  IMP_RES_TAC nwalkstar_subterm_exists THEN
  SRW_TAC [][] THEN
  POP_ASSUM (K ALL_TAC) THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk* s t1 = nPair (nwalk* s t1a) (nwalk* s t1d)` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk* s t2 = nPair (nwalk* s t2a) (nwalk* s t2d)` [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`t1d`,`t2d`,`s`] MP_TAC) THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`t1a`,`t2a`,`s`] MP_TAC) THEN
  SRW_TAC [][] THEN
  SRW_TAC [][Once equiv_cases] THEN
  Cases_on `verify_fcs fec s` THEN
  Cases_on `verify_fcs fec' s` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `verify_fcs (fec ∪ fec') s = SOME (x ∪ x')` by (
    MATCH_MP_TAC verify_fcs_UNION_I THEN
    SRW_TAC [][] ) THEN
  Q.EXISTS_TAC `fec ∪ fec'` THEN SRW_TAC [][] THEN
  METIS_TAC [equiv_SUBSET,SUBSET_UNION] ) THEN
Q.EXISTS_TAC `{}` THEN SRW_TAC [][])

val unify_eq_vars_verify_fcs = Q.store_thm(
"unify_eq_vars_verify_fcs",
`(verify_fcs fe s = SOME ve) ∧ nwfs s ∧ FINITE ds ∧ FINITE fe ∧
 (unify_eq_vars ds v (s,fe) = SOME (s',fe')) ⇒
 (∃ve'. verify_fcs fe' s' = SOME ve')`,
SRW_TAC [][] THEN
Cases_on `verify_fcs fe' s'` THEN SRW_TAC [][] THEN
IMP_RES_TAC unify_eq_vars_FINITE THEN
IMP_RES_TAC unify_eq_vars_preserves_s THEN
IMP_RES_TAC verify_fcs_NONE THEN
Cases_on `(a,v') ∈ fe` THEN1 (
  IMP_RES_TAC verify_fcs_covers_all THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] ) THEN
`∃ b fcs. (term_fcs b (nwalk* s (Sus [] v)) = SOME fcs) ∧ (a,v') ∈ fcs`
by METIS_TAC [unify_eq_vars_minimal] THEN
SRW_TAC [][] THEN
IMP_RES_TAC term_fcs_NOTIN_FDOM THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,Once term_fcs_def])

val nwalk_nwalkstar = Q.store_thm(
"nwalk_nwalkstar",
`nwfs s ⇒ ∀t. nwalk s (nwalk* s t) = nwalk* s t`,
STRIP_TAC THEN HO_MATCH_MP_TAC nwalkstar_ind THEN
STRIP_TAC THEN
`nwalk* s t = nwalk* s (nwalk s t)` by METIS_TAC [nwalkstar_nwalk] THEN
Cases_on `nwalk s t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`n ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk])

val nomunify_eqs = Q.store_thm(
"nomunify_eqs",
`∀s fe t1 t2 q1 q2 t ve.
 (nwalk s t1 = apply_pi q1 t) ∧
 (nwalk s t2 = apply_pi q2 t) ∧ nwfs s ∧
 (∀a. a ∈ dis_set q1 q2 ⇒ term_fcs a (nwalk* s t) ≠ NONE) ∧
 (verify_fcs fe s = SOME ve) ∧ FINITE fe
 ⇒
 ∃fex. nomunify (s,fe) t1 t2 = SOME (s,fex)`,
HO_MATCH_MP_TAC nunify_ind THEN
SRW_TAC [][nomunify_def,EXISTS_PROD] THEN
Q.PAT_ASSUM `nwfs s` MP_TAC THEN
SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN
Cases_on `t` THEN ASM_SIMP_TAC (psrw_ss()) [] THEN1 (
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  FULL_SIMP_TAC (srw_ss()) [Once term_fcs_def] )
THEN1 (
  SRW_TAC [][] THEN
  Q.ABBREV_TAC `ds = dis_set (q1 ++ l) (q2 ++ l)` THEN
  REVERSE (Cases_on `unify_eq_vars ds n (s,fe)`) THEN1 (
    Cases_on `x` THEN
    IMP_RES_TAC unify_eq_vars_preserves_s THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC (GEN_ALL unify_eq_vars_verify_fcs) THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [FINITE_dis_set] ) THEN
  IMP_RES_TAC unify_eq_vars_NONE THEN
  FULL_SIMP_TAC (psrw_ss()) [Abbr`ds`] THEN
  `n ∉ FDOM s` by METIS_TAC [nwalk_to_var] THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def] THEN
  METIS_TAC [IN_SING] )
THEN1 (
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [nwalk_apply_pi] THEN
    Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = Tie X (apply_pi Y t)` ["X","Y"] THEN
    MAP_EVERY Q.EXISTS_TAC [`q1`,`q2`,`nwalk s t`] THEN
    SRW_TAC [][] THEN
    Q.PAT_ASSUM `!X.Y` MP_TAC THEN
    SRW_TAC [][Once term_fcs_def] THEN
    POP_ASSUM (Q.SPEC_THEN `a` MP_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][nwalkstar_nwalk] ) THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = Tie (lswapstr q1 a) (apply_pi q1 t)` [] THEN
  `lswapstr (REVERSE q2) (lswapstr q1 a) ∈ dis_set q1 q2` by (
    ASM_SIMP_TAC (srw_ss()) [dis_set_def] THEN
    FULL_SIMP_TAC (srw_ss())[pmact_eql] ) THEN
  Q.PAT_ASSUM `!X.Y` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  `lswapstr (REVERSE q2) (lswapstr q1 a) ≠ a` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    METIS_TAC [pmact_inverse] ) THEN
  `∃fcs. term_fcs (lswapstr q1 a) (apply_pi q2 (nwalk* s t)) = SOME fcs` by (
    FIRST_X_ASSUM (Q.SPEC_THEN `lswapstr (REVERSE q2) (lswapstr q1 a)` MP_TAC) THEN
    SRW_TAC [][] THEN
    Cases_on `term_fcs (lswapstr (REVERSE q2) (lswapstr q1 a)) (nwalk* s t)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    (term_fcs_apply_pi |>
     Q.INST [`a`|->`lswapstr (REVERSE q2) (lswapstr q1 a)`,`t`|->`nwalk* s t`,
             `pi`|->`q2`,`fcs`|->`x`] |> MP_TAC) THEN
    SRW_TAC [][] ) THEN
  FULL_SIMP_TAC (srw_ss()) [nwalkstar_apply_pi] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [nwalk_apply_pi] THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM apply_pi_decompose] THEN
  MAP_EVERY Q.EXISTS_TAC [`q1`,`(lswapstr q1 a, lswapstr q2 a)::q2`,`nwalk s t`] THEN
  SRW_TAC [][] THEN
  `verify_fcs fcs s = SOME fcs` by (
    MATCH_MP_TAC (GEN_ALL verify_fcs_term_fcs) THEN
    MAP_EVERY Q.EXISTS_TAC [`nwalk* s (apply_pi q2 t)`,`lswapstr q1 a`] THEN
    SRW_TAC [][nwalkstar_apply_pi] THEN
    METIS_TAC [nwalkstar_idempotent] ) THEN
  Q.EXISTS_TAC `ve ∪ fcs` THEN
  IMP_RES_TAC term_fcs_FINITE THEN
  SRW_TAC [][] THEN1 (
    FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
    ASM_SIMP_TAC (srw_ss()) [nwalkstar_nwalk] THEN
    Cases_on `a = a'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `lswapstr q1 a' = lswapstr q2 a'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
      Cases_on `lswapstr q2 a' = lswapstr q2 a` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `lswapstr q2 a' = lswapstr q1 a` THEN
      FULL_SIMP_TAC (srw_ss()) [] ) THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `a'` MP_TAC) THEN
    SRW_TAC [][] ) THEN
  MATCH_MP_TAC verify_fcs_UNION_I THEN
  SRW_TAC [][] )
THEN1 (
  SRW_TAC [][EXISTS_PROD] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [nwalk_apply_pi] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = nPair (apply_pi q1 ta) (apply_pi q1 td)` [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`q1`,`q2`,`nwalk s ta`] MP_TAC) THEN
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `!X.Y` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [nwalkstar_nwalk] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nunify (s,fe) X Y = SOME (s,fu)` ["X","Y"] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`s`,`fu`] MP_TAC) THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [nwalk_apply_pi] THEN
  IMP_RES_TAC nunify_FINITE_fe THEN
  MAP_EVERY Q.EXISTS_TAC [`q1`,`q2`,`nwalk s td`] THEN
  SRW_TAC [][] THEN
  METIS_TAC [nwalkstar_nwalk] ) )

val nvars_measure = Q.store_thm(
"nvars_measure",
`v ∈ nvars t ∧ ¬ is_Sus t ∧ nwfs s ⇒
 measure (npair_count o (nwalk* s)) (Sus [] v) t`,
Induct_on `t` THEN SRW_TAC [][] THEN
Q.MATCH_ASSUM_RENAME_TAC `v ∈ nvars tt` [] THEN
Cases_on `tt` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [measure_thm] THEN
(npair_count_nwalkstar_ignores_pi |>
 UNDISCH |>
 Q.SPECL [`Sus [] n`,`l`] |>
 MP_TAC) THEN
ASM_SIMP_TAC (psrw_ss()++ARITH_ss) [])

val npair_count_apply_pi = RWstore_thm(
"npair_count_apply_pi",
`npair_count (apply_pi pi t) = npair_count t`,
Induct_on `t` THEN SRW_TAC [][])

val equiv_depth_eq = Q.store_thm(
"equiv_depth_eq",
`∀t1 t2. equiv fe t1 t2 ⇒ (npair_count t1 = npair_count t2)`,
HO_MATCH_MP_TAC equiv_ind THEN SRW_TAC [][])

val noc_subterm_nequiv = Q.store_thm(
"noc_subterm_nequiv",
`noc s t v ∧ ¬ is_Sus t ∧ nwfs s ∧ nwfs s2 ⇒
¬ equiv fe (nwalk* s2 (Sus pi v)) (nwalk* s2 (nwalk* s t))`,
STRIP_TAC THEN
`v ∈ nvars (nwalk* s t)` by METIS_TAC [noc_eq_nvars_nwalkstar] THEN
`~is_Sus (nwalk* s t)` by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
IMP_RES_TAC nvars_measure THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC noc_NOTIN_FDOM THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (psrw_ss()) [measure_thm,NOT_FDOM_nvwalk] THEN
`npair_count (nwalk* s2 (apply_pi pi (Sus [] v))) < npair_count (nwalk* s2 (nwalk* s t))`
by (Q.PAT_ASSUM `nwfs s2` ASSUME_TAC THEN FULL_SIMP_TAC (psrw_ss()) [nwalkstar_apply_pi]) THEN
FULL_SIMP_TAC (psrw_ss()) [] THEN
METIS_TAC [equiv_depth_eq,LESS_NOT_EQ])

val nwalk_to_var_NOT_FDOM = Q.prove(
`nwfs s ∧ (nwalk s t = Sus p v) ⇒ v ∉ FDOM s`,
METIS_TAC [nwalk_to_var])

val term_fcs_equiv_NONE = Q.store_thm(
"term_fcs_equiv_NONE",
`(term_fcs a t1 = NONE) ∧ equiv fe t1 t2 ∧ (term_fcs a t2 = SOME fcs) ⇒ ¬ (fcs ⊆ fe)`,
SRW_TAC [][] THEN
IMP_RES_TAC term_fcs_NONE THEN
IMP_RES_TAC term_fcs_fresh THEN
IMP_RES_TAC equiv_sym THEN
IMP_RES_TAC equiv_fresh THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`fresh fe a t2` by METIS_TAC [fresh_extra_fcs] THEN
RES_TAC THEN RES_TAC)

val term_fcs_apply_pi_NONE = Q.store_thm(
"term_fcs_apply_pi_NONE",
`(term_fcs a t = NONE) ⇔ (term_fcs (lswapstr pi a) (apply_pi pi t) = NONE)`,
Cases_on `term_fcs a t` THEN
Cases_on `term_fcs (lswapstr pi a) (apply_pi pi t)` THEN
SRW_TAC [][] THEN1 (
  (term_fcs_apply_pi |>
   Q.INST [`a`|->`lswapstr pi a`,`t`|->`apply_pi pi t`,`pi`|->`REVERSE pi`,`fcs`|->`x`] |>
   MP_TAC) THEN
  SRW_TAC [][] ) THEN
(term_fcs_apply_pi |>
 Q.INST [`fcs`|->`x`] |>
 MP_TAC) THEN
SRW_TAC [][])

val term_fcs_nwalkstar_NONE = Q.store_thm(
"term_fcs_nwalkstar_NONE",
`nwfs s ∧ (term_fcs a t = SOME fcs) ∧
 (term_fcs a (nwalk* s t) = NONE) ⇒
 (verify_fcs fcs s = NONE)`,
STRIP_TAC THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
MAP_EVERY Q.ID_SPEC_TAC [`fcs`,`t`] THEN
HO_MATCH_MP_TAC nwalkstar_ind THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
`nwalk* s t = nwalk* s (nwalk s t)` by METIS_TAC [nwalkstar_nwalk] THEN
Cases_on `nwalk s t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
  Q.PAT_ASSUM `X = NONE` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][verify_fcs_def,fcs_acc_RECURSES] THEN
  SRW_TAC [][fcs_acc_def,ITSET_EMPTY] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  SRW_TAC [][apply_pi_eql,Once term_fcs_def] )
THEN1 (
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  Cases_on `t` THEN FULL_SIMP_TAC (psrw_ss()) [] THEN
  `n ∉ FDOM s` by METIS_TAC [nvwalk_to_var] THEN
  FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
  FULL_SIMP_TAC (srw_ss()) [Once term_fcs_def] )
THEN1 (
  Q.PAT_ASSUM `X = NONE` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `X = SOME fcs` MP_TAC THEN
  ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  SRW_TAC [][] THEN
  SRW_TAC [][verify_fcs_def,fcs_acc_RECURSES] THEN
  SRW_TAC [][fcs_acc_def,ITSET_EMPTY] THEN
  (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
  SRW_TAC [][apply_pi_eql,Once term_fcs_def,nwalkstar_apply_pi] THEN
  METIS_TAC [term_fcs_apply_pi_NONE] )
THEN1 (
  Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Q.PAT_ASSUM `X = SOME fcs` MP_TAC THEN
    ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
    SRW_TAC [][] THEN
    SRW_TAC [][verify_fcs_def,fcs_acc_RECURSES] THEN
    SRW_TAC [][fcs_acc_def,ITSET_EMPTY] THEN
    (nvwalk_modulo_pi |> Q.SPECL [`s`,`l`,`n`] |> GSYM |> MP_TAC) THEN
    SRW_TAC [][apply_pi_eql,Once term_fcs_def,nwalkstar_apply_pi] THEN
    Q.PAT_ASSUM `X = NONE` MP_TAC THEN
    SRW_TAC [][Once term_fcs_def] THEN
    METIS_TAC [term_fcs_apply_pi_NONE] ) THEN
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `X = SOME fcs` MP_TAC THEN
  ASM_SIMP_TAC (psrw_ss()) [Once term_fcs_def] THEN
  Q.PAT_ASSUM `X = NONE` MP_TAC THEN
  SRW_TAC [][Once term_fcs_def] THEN
  Cases_on `verify_fcs (x1 ∪ x2) s` THEN SRW_TAC [][] THEN
  RES_TAC THEN
  METIS_TAC [verify_fcs_UNION,term_fcs_FINITE,optionTheory.NOT_SOME_NONE] ) THEN
FULL_SIMP_TAC (srw_ss()) [term_fcs_def])

val verify_fcs_iter_SUBMAP_exists = Q.store_thm(
"verify_fcs_iter_SUBMAP_exists",
`(verify_fcs fe s = SOME ve) ∧ nwfs sx ∧ s SUBMAP sx ∧ FINITE fe ∧
 (verify_fcs ve sx = SOME vex) ⇒
 (∃fex. verify_fcs fe sx = SOME fex)`,
STRIP_TAC THEN Cases_on `verify_fcs fe sx` THEN SRW_TAC [][] THEN
`∃a v. (a,v) ∈ fe ∧ (term_fcs a (nwalk* sx (Sus [] v)) = NONE)`
by METIS_TAC [verify_fcs_NONE] THEN
`∃fcs. (term_fcs a (nwalk* s (Sus [] v)) = SOME fcs) ∧ fcs ⊆ ve`
by METIS_TAC [verify_fcs_covers_all] THEN
`nwalk* sx (Sus [] v) = nwalk* sx (nwalk* s (Sus [] v))`
by METIS_TAC [nwalkstar_SUBMAP] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC term_fcs_nwalkstar_NONE THEN
IMP_RES_TAC verify_fcs_FINITE THEN
IMP_RES_TAC verify_fcs_SUBSET THEN
FULL_SIMP_TAC (srw_ss()) [])

val equiv_nomunify = Q.store_thm(
"equiv_nomunify",
`equiv fe2 (nwalk* s2 (nwalk* s t1)) (nwalk* s2 (nwalk* s t2)) ∧ nwfs s2 ∧ nwfs s ⇒
 ∃sx.∀fe. FINITE fe ∧ (verify_fcs fe sx ≠ NONE) ⇒
       ∃fex. (nomunify (s,fe) t1 t2 = SOME (sx,fex))`,
Q_TAC SUFF_TAC
`∀fe2 s fe t1 t2 ve2. equiv fe2 (nwalk* s2 (nwalk* s t1)) (nwalk* s2 (nwalk* s t2))
                  ∧ nwfs s2 ∧ nwfs s ∧ FINITE (fe:fe) ∧ FINITE fe2 ∧ (verify_fcs fe2 s2 = SOME ve2) ⇒
     ∃sx fu fv. (nunify (s,{}) t1 t2 = SOME (sx,fu)) ∧ (verify_fcs fu sx = SOME fv)` THEN1 (
  SRW_TAC [][] THEN
  `∃fcs. FINITE fcs ∧ (verify_fcs fcs s2 = SOME fcs) ∧ equiv fcs (nwalk* s2 (nwalk* s t1)) (nwalk* s2 (nwalk* s t2))`
  by METIS_TAC [equiv_consistent_exists] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`fcs`,`s`,`{}`,`t1`,`t2`,`fcs`] MP_TAC) THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [nomunify_def,EXISTS_PROD] THEN
  Q.EXISTS_TAC `sx` THEN SRW_TAC [][] THEN
  `∃f2. nunify (s,fe) t1 t2 = SOME (sx,f2)`
  by METIS_TAC [nunify_ignores_fe] THEN
  SRW_TAC [][] THEN
  `∃ff.∀fe fex. (nunify (s,fe) t1 t2 = SOME (sx,fex)) ⇒ (fex = fe ∪ ff)`
  by METIS_TAC [nunify_adds_same_fcs] THEN
  RES_TAC THEN SRW_TAC [][] THEN
  Cases_on `verify_fcs fe sx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.EXISTS_TAC `x ∪ fv` THEN
  MATCH_MP_TAC verify_fcs_UNION_I THEN
  IMP_RES_TAC nunify_FINITE_fe THEN
  FULL_SIMP_TAC (srw_ss()) []) THEN
STRIP_TAC THEN HO_MATCH_MP_TAC nunify_ind THEN
SRW_TAC [][nomunify_def,EXISTS_PROD] THEN
`(nwalk* s t1 = nwalk* s (nwalk s t1)) ∧
 (nwalk* s t2 = nwalk* s (nwalk s t2))`
by METIS_TAC [nwalkstar_nwalk] THEN
MAP_EVERY Cases_on [`nwalk s t1`,`nwalk s t2`] THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
Q.PAT_ASSUM `nwfs s` MP_TAC THEN
SIMP_TAC (psrw_ss()) [Once nunify_def,LET_THM] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC nwalk_to_var_NOT_FDOM THEN
Q.PAT_ASSUM `nwfs s` ASSUME_TAC THEN
Q.PAT_ASSUM `nwfs s2` ASSUME_TAC THEN
FULL_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
TRY ( FULL_SIMP_TAC (srw_ss()) [Once equiv_cases] THEN NO_TAC)
THEN1 (
  Cases_on `n = n'` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `s` THEN
  Q.ABBREV_TAC `ds = dis_set l l'` THEN
  Cases_on `unify_eq_vars ds n (s,fe)` THEN1 (
    IMP_RES_TAC unify_eq_vars_NONE THEN
    FULL_SIMP_TAC (srw_ss()) [Abbr`ds`] THEN
    POP_ASSUM (Q.SPEC_THEN `{(a,n)}` MP_TAC) THEN
    ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk,fresh_def] ) THEN
  Cases_on `x` THEN IMP_RES_TAC unify_eq_vars_preserves_s THEN
  SRW_TAC [][] THEN
  IMP_RES_TAC unify_eq_vars_ignores_fe THEN
  FULL_SIMP_TAC (srw_ss()) [Abbr`ds`] THEN
  POP_ASSUM (Q.SPEC_THEN `{}` STRIP_ASSUME_TAC) THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (GEN_ALL unify_eq_vars_verify_fcs) THEN
  METIS_TAC [FINITE_dis_set,FINITE_EMPTY,verify_fcs_empty])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s Z = Tie a t` ["Z"] THEN
  (noc_subterm_nequiv |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`Tie a t`,`pi`|->`l`,`fe`|->`fe2`] |>
   MP_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [noc_ignores_pi])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s Z = nPair c1 c2` ["Z"] THEN
  (noc_subterm_nequiv |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`nPair c1 c2`,`pi`|->`l`,`fe`|->`fe2`] |>
   MP_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [noc_ignores_pi])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s Z = nPair c1 c2` ["Z"] THEN
  (noc_subterm_nequiv |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`nPair c1 c2`,`pi`|->`l`,`fe`|->`fe2`] |>
   MP_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [noc_ignores_pi])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s Z = Tie a t` ["Z"] THEN
  (noc_subterm_nequiv |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`Tie a t`,`pi`|->`l`,`fe`|->`fe2`] |>
   MP_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [noc_ignores_pi,equiv_sym])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = Tie a1 c1` [] THEN
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = Tie a2 c2` [] THEN
  Cases_on `a1 = a2` THEN SRW_TAC [][] THEN1 (
    POP_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [Once equiv_cases] ) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `equiv fe2 X Y` MP_TAC THEN
  SRW_TAC [][Once equiv_cases] THEN
  IMP_RES_TAC fresh_term_fcs THEN
  `∃fe0. term_fcs a1 (nwalk* s c2) = SOME fe0`
  by METIS_TAC [term_fcs_SUBMAP] THEN
  IMP_RES_TAC term_fcs_FINITE THEN
  FULL_SIMP_TAC (srw_ss()) [nwalkstar_apply_pi] THEN
  `∃fe1. nunify (s,fe0) c1 (apply_pi [(a1,a2)] c2) = SOME (sx,fe1)`
  by METIS_TAC [nunify_ignores_fe] THEN
  `fe1 = fe0 ∪ fu` by (
    IMP_RES_TAC nunify_adds_same_fcs THEN
    POP_ASSUM (Q.SPECL_THEN [`apply_pi [(a1,a2)] c2`,`c1`] STRIP_ASSUME_TAC) THEN
    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] ) THEN
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `verify_fcs fe0 sx ≠ NONE` THEN1 (
    Cases_on `verify_fcs fe0 sx` THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `x ∪ fv` THEN
    MATCH_MP_TAC verify_fcs_UNION_I THEN
    METIS_TAC [nunify_FINITE_fe,FINITE_EMPTY] ) THEN
  `∀t. equiv fe2 (nwalk* s2 (nwalk* sx t)) (nwalk* s2 (nwalk* s t))` by (
    MATCH_MP_TAC nomunify_mgu2 THEN
    MAP_EVERY Q.EXISTS_TAC [`{}`,`c1`,`apply_pi [(a1,a2)] c2`,`fv`] THEN
    SRW_TAC [][nomunify_def,EXISTS_PROD,nwalkstar_apply_pi] ) THEN
    `fresh fe2 a1 (nwalk* s2 (nwalk* sx c2))`
    by METIS_TAC [equiv_fresh,equiv_trans,equiv_sym] THEN
    `∃fcs4. (term_fcs a1 (nwalk* s2 (nwalk* sx c2)) = SOME fcs4) ∧ fcs4 ⊆ fe2` by
      METIS_TAC [fresh_term_fcs] THEN
    `s SUBMAP sx ∧ nwfs sx` by METIS_TAC [nunify_uP,uP_def] THEN
    `∃fcs3. (term_fcs a1 (nwalk* sx (nwalk* s c2)) = SOME fcs3)` by
      METIS_TAC [term_fcs_SUBMAP,nwalkstar_SUBMAP] THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    `∃a v. (a,v) ∈ fe0 ∧ (term_fcs a (nwalk* sx (Sus [] v)) = NONE)`
    by METIS_TAC [verify_fcs_NONE] THEN
    METIS_TAC [term_fcs_nwalkstar,optionTheory.NOT_SOME_NONE] )
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s Z = nPair c1 c2` ["Z"] THEN
  (noc_subterm_nequiv |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`nPair c1 c2`,`pi`|->`l`,`fe`|->`fe2`] |>
   MP_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [noc_ignores_pi,equiv_sym])
THEN1 (
  Q.MATCH_ASSUM_RENAME_TAC `nwalk s Z = nPair c1 c2` ["Z"] THEN
  (noc_subterm_nequiv |> CONTRAPOS |>
   Q.INST [`v`|->`n`,`t`|->`nPair c1 c2`,`pi`|->`l`,`fe`|->`fe2`] |>
   MP_TAC) THEN
  FULL_SIMP_TAC (srw_ss()) [noc_ignores_pi,equiv_sym]) THEN
SRW_TAC [][EXISTS_PROD] THEN
Q.MATCH_ASSUM_RENAME_TAC `nwalk s t1 = nPair t1a t1d` [] THEN
Q.MATCH_ASSUM_RENAME_TAC `nwalk s t2 = nPair t2a t2d` [] THEN
Q.PAT_ASSUM `equiv fe2 X Y` MP_TAC THEN
SRW_TAC [][Once equiv_cases] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃fe1. nunify (s,fe) t1a t2a = SOME (sx,fe1)`
by METIS_TAC [nunify_ignores_fe] THEN
`fe1 = fe ∪ fu` by (
  IMP_RES_TAC nunify_adds_same_fcs THEN
  POP_ASSUM (Q.SPECL_THEN [`t2a`,`t1a`] STRIP_ASSUME_TAC) THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] ) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∀t. equiv fe2 (nwalk* s2 (nwalk* sx t)) (nwalk* s2 (nwalk* s t))` by (
  MATCH_MP_TAC nomunify_mgu2 THEN
  MAP_EVERY Q.EXISTS_TAC [`{}`,`t1a`,`t2a`,`fv`] THEN
  SRW_TAC [][nomunify_def,EXISTS_PROD,nwalkstar_apply_pi] ) THEN
`equiv fe2 (nwalk* s2 (nwalk* sx t1d)) (nwalk* s2 (nwalk* sx t2d))`
by METIS_TAC [equiv_trans,equiv_sym] THEN
`nwfs sx ∧ FINITE fu` by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe,FINITE_EMPTY] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.MATCH_ASSUM_RENAME_TAC `nunify (s,{}) t1a t2a = SOME (sa,fa)` [] THEN
Q.MATCH_ASSUM_RENAME_TAC `nunify (sa,{}) t1d t2d = SOME (sd,fd)` [] THEN
Q.MATCH_ASSUM_RENAME_TAC `verify_fcs fa sa = SOME faa` [] THEN
Q.MATCH_ASSUM_RENAME_TAC `verify_fcs fd sd = SOME fdd` [] THEN
`∃fe1. nunify (sa,fa) t1d t2d = SOME (sd,fe1)`
by METIS_TAC [nunify_ignores_fe] THEN
`fe1 = fa ∪ fd` by (
  IMP_RES_TAC nunify_adds_same_fcs THEN
  REPEAT (FIRST_X_ASSUM (Q.SPECL_THEN [`t2d`,`t1d`] STRIP_ASSUME_TAC)) THEN
  RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] ) THEN
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `verify_fcs fa sd ≠ NONE` THEN1 (
  Cases_on `verify_fcs fa sd` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `x ∪ fdd` THEN
  MATCH_MP_TAC verify_fcs_UNION_I THEN
  METIS_TAC [nunify_FINITE_fe,FINITE_EMPTY] ) THEN
Q_TAC SUFF_TAC `verify_fcs faa sd ≠ NONE` THEN1 (
  Cases_on `verify_fcs faa sd` THEN SRW_TAC [][] THEN
  `nwfs sd ∧ sa SUBMAP sd ∧ FINITE fa` by METIS_TAC [nunify_uP,uP_def,nunify_FINITE_fe,FINITE_EMPTY] THEN
  METIS_TAC [verify_fcs_iter_SUBMAP_exists,optionTheory.NOT_SOME_NONE] ) THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`FINITE faa` by METIS_TAC [verify_fcs_FINITE] THEN
`∃a v. (a,v) ∈ faa ∧ (term_fcs a (nwalk* sd (Sus [] v)) = NONE)` by
  METIS_TAC [verify_fcs_NONE] THEN
(nomunify_mgu1 |>
 Q.INST [`fe`|->`{}`,`t1`|->`t1a`,`t2`|->`t2a`,`sx`|->`sa`,`fex`|->`faa`] |>
 MP_TAC) THEN
SRW_TAC [][nomunify_def] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC fresh_term_fcs THEN
`∀t. equiv fe2 (nwalk* s2 (nwalk* sd t)) (nwalk* s2 (nwalk* sa t))` by (
  MATCH_MP_TAC nomunify_mgu2 THEN
  MAP_EVERY Q.EXISTS_TAC [`{}`,`t1d`,`t2d`,`fdd`] THEN
  SRW_TAC [][nomunify_def,EXISTS_PROD,nwalkstar_apply_pi] ) THEN
`equiv fe2 (nwalk* s2 (nwalk* s (Sus [] v))) (nwalk* s2 (nwalk* sd (Sus [] v)))`
by METIS_TAC [equiv_trans,equiv_sym] THEN
(term_fcs_equiv |>
 Q.INST [`fe`|->`fe2`,`t1`|->`nwalk* s2 (nwalk* s (Sus [] v))`,`t2`|->`nwalk* s2 (nwalk* sd (Sus [] v))`,
         `fcs1`|->`fcs`] |> MP_TAC) THEN
`v ∉ FDOM sa` by METIS_TAC [verify_fcs_NOTIN_FDOM] THEN
`s SUBMAP sa` by METIS_TAC [nunify_uP,uP_def] THEN
`v ∉ FDOM s` by METIS_TAC [SUBMAP_DEF] THEN
ASM_SIMP_TAC (psrw_ss()) [NOT_FDOM_nvwalk] THEN
SRW_TAC [][] THEN
Cases_on `fcs2 ⊆ fe2` THEN SRW_TAC [][] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC term_fcs_SUBMAP THEN
FULL_SIMP_TAC (srw_ss()) [])

val _ = export_theory ();
