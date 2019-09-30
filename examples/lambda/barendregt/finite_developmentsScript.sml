open HolKernel Parse boolLib

open bossLib metisLib boolSimps

open chap3Theory chap2Theory labelledTermsTheory termTheory binderLib
open term_posnsTheory chap11_1Theory
open pathTheory BasicProvers nomsetTheory pred_setTheory

local open pred_setLib in end
val _ = augment_srw_ss [boolSimps.LET_ss]

val _ = new_theory "finite_developments";

fun Save_Thm(n, th) = save_thm(n,th) before export_rewrites [n]
fun Store_Thm(n, t, tac) = store_thm(n, t, tac) before export_rewrites [n]

val _ = hide "set"

val RUNION_COMM = relationTheory.RUNION_COMM
val RUNION = relationTheory.RUNION

(* finiteness of developments : section 11.2 of Barendregt *)

(* ----------------------------------------------------------------------
    substitutivity etc
   ---------------------------------------------------------------------- *)

val lsubstitutive_def = Define`
  lsubstitutive R = !M (N:lterm) v L. R M N ==> R ([L/v]M) ([L/v]N)
`;

val lpermutative_def = Define`
  lpermutative R = !M (N:lterm) pi. R M N ==> R (ltpm pi M) (ltpm pi N)
`;

val RUNION_lsubstitutive = store_thm(
  "RUNION_lsubstitutive",
  ``!R1 R2. lsubstitutive R1 /\ lsubstitutive R2 ==>
            lsubstitutive (R1 RUNION R2)``,
  SRW_TAC [][lsubstitutive_def, relationTheory.RUNION] THEN SRW_TAC [][]);

val lsubstitutive_lpermutative = store_thm(
  "lsubstitutive_lpermutative",
  ``lsubstitutive R ==> lpermutative R``,
  SRW_TAC [][lsubstitutive_def, lpermutative_def] THEN
  Induct_on `pi` THEN SRW_TAC [][] THEN
  `?x y. h = (x,y)` by (Cases_on `h` THEN METIS_TAC []) THEN
  SRW_TAC [][] THEN
  `(ltpm ((x,y)::pi) M = ltpm [(x,y)] (ltpm pi M)) /\
   (ltpm ((x,y)::pi) N = ltpm [(x,y)] (ltpm pi N))`
     by SRW_TAC [][GSYM pmact_decompose] THEN
  SRW_TAC [][] THEN
  Q.MATCH_ABBREV_TAC `R (ltpm [(x,y)] MM) (ltpm [(x,y)] NN)` THEN
  Q_TAC (NEW_TAC "z") `{x;y} UNION FV MM UNION FV NN` THEN
  Q_TAC SUFF_TAC `(ltpm [(x,y)] MM = [VAR y/z] ([VAR x/y] ([VAR z/x] MM))) /\
                  (ltpm [(x,y)] NN = [VAR y/z] ([VAR x/y] ([VAR z/x] NN)))`
        THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM fresh_ltpm_subst, GSYM pmact_decompose] THEN
  Q_TAC SUFF_TAC `[(x,y)] == [(y,z); (x,y); (z,x)]`
        THEN1 METIS_TAC [nomsetTheory.pmact_permeq] THEN
  SRW_TAC [][nomsetTheory.permeq_def, FUN_EQ_THM] THEN
  Cases_on `x' = x` THEN SRW_TAC [][] THEN
  Cases_on `x' = z` THEN SRW_TAC [][] THEN
  Cases_on `x' = y` THEN SRW_TAC [][]);

(* ----------------------------------------------------------------------
    define redex labelled reduction for unlabelled and labelled terms
   ---------------------------------------------------------------------- *)

val _ =
    "Defining redex-labelled reduction for unlabelled and labelled terms\n";

(* unlabelled terms *)
val (labelled_redn_rules, labelled_redn_ind, labelled_redn_cases) =
    Hol_reln`(!x y. R (x:term) y ==> labelled_redn R x [] y) /\
             (!z x y pos.
                   labelled_redn R x pos y ==>
                   labelled_redn R (x @@ z) (Lt::pos) (y @@ z)) /\
             (!z x y pos.
                   labelled_redn R x pos y ==>
                   labelled_redn R (z @@ x) (Rt::pos) (z @@ y)) /\
             (!v x y pos.
                   labelled_redn R x pos y ==>
                   labelled_redn R (LAM v x) (In::pos) (LAM v y))`;

val strong_labelled_redn_ind = save_thm(
  "strong_labelled_redn_ind",
  IndDefLib.derive_strong_induction (labelled_redn_rules, labelled_redn_ind));

val labelled_redn_bvc_ind = store_thm(
  "labelled_redn_bvc_ind",
  ``!P X. FINITE X /\
          (!v M N. ~(v IN X) /\ ~(v IN FV N) ==>
                   P (LAM v M @@ N) [] ([N/v]M)) /\
          (!z x y pos. P x pos y ==> P (x @@ z) (Lt::pos) (y @@ z)) /\
          (!z x y pos. P x pos y ==> P (z @@ x) (Rt::pos) (z @@ y)) /\
          (!v x y pos. ~(v IN X) /\ P x pos y ==>
                       P (LAM v x) (In::pos) (LAM v y)) ==>
          !M pos N. labelled_redn beta M pos N ==> P M pos N``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!M pos N. labelled_redn beta M pos N ==>
                   !p. P (tpm p M) pos (tpm p N)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC labelled_redn_ind THEN SRW_TAC [][beta_def] THENL [
    SRW_TAC [][tpm_subst] THEN
    Q.MATCH_ABBREV_TAC `P (LAM v M @@ N) [] ([N/v]M)` THEN
    Q_TAC (NEW_TAC "z") `X UNION FV M UNION FV N` THEN
    `LAM v M = LAM z (tpm [(z,v)] M)` by SRW_TAC [][tpm_ALPHA] THEN
    `[N/v] M = [N/z] ([VAR z/v] M)` by SRW_TAC [][lemma15a] THEN
    SRW_TAC [][GSYM pmact_decompose, GSYM fresh_tpm_subst],

    Q.MATCH_ABBREV_TAC `P (LAM vv MM) (In::pos) (LAM vv NN)` THEN
    Q_TAC (NEW_TAC "z") `X UNION FV MM UNION FV NN` THEN
    `(LAM vv MM = LAM z (tpm [(z,vv)] MM)) /\
     (LAM vv NN = LAM z (tpm [(z,vv)] NN))`
        by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose]
  ]);

val labelled_redn_beta_tpm_imp = store_thm(
  "labelled_redn_beta_tpm_imp",
  ``!M pos N. labelled_redn beta M pos N ==>
              !pi. labelled_redn beta (tpm pi M) pos (tpm pi N)``,
  HO_MATCH_MP_TAC labelled_redn_ind THEN
  SRW_TAC [][beta_def, labelled_redn_rules] THEN
  SRW_TAC [][tpm_subst] THEN
  METIS_TAC [beta_def, labelled_redn_rules]);

val labelled_redn_beta_tpm_eqn = store_thm(
  "labelled_redn_beta_tpm_eqn",
  ``labelled_redn beta (tpm p M) pos N =
    labelled_redn beta M pos (tpm (REVERSE p) N)``,
  METIS_TAC [labelled_redn_beta_tpm_imp, pmact_inverse]);


(* relationship to unlabelled reductions *)
val cc_labelled_redn = store_thm(
  "cc_labelled_redn",
  ``!R M N. compat_closure R M N ==> ?pos. labelled_redn R M pos N``,
  GEN_TAC THEN HO_MATCH_MP_TAC compat_closure_ind THEN
  PROVE_TAC [labelled_redn_rules]);

val labelled_redn_cc = store_thm(
  "labelled_redn_cc",
  ``!R M pos N. labelled_redn R M pos N ==> compat_closure R M N``,
  GEN_TAC THEN HO_MATCH_MP_TAC labelled_redn_ind THEN
  PROVE_TAC [compat_closure_rules]);

(* labelled terms *)
val (lrcc_rules, lrcc_ind, lrcc_cases) =
    Hol_reln`(!x y. R x y ==> lrcc R x [] y) /\
             (!x y z r. lrcc R x r y ==>
                        lrcc R (x @@ z) (Lt::r) (y @@ z)) /\
             (!x y z r. lrcc R x r y ==>
                        lrcc R (z @@ x) (Rt::r) (z @@ y)) /\
             (!x y v r. lrcc R x r y ==>
                        lrcc R (LAM v x) (In::r) (LAM v y)) /\
             (!x y n v z r.
                        lrcc R x r y ==>
                        lrcc R (LAMi n v z x) (Rt::r) (LAMi n v z y)) /\
             (!x y n v z r.
                        lrcc R x r y ==>
                        lrcc R (LAMi n v x z) (Lt::In::r) (LAMi n v y z))`;

val strong_lrcc_ind = save_thm(
  "strong_lrcc_ind",
  IndDefLib.derive_strong_induction(lrcc_rules, lrcc_ind));

val lrcc_bvc_b01_ind = store_thm(
  "lrcc_bvc_b01_ind",
  ``!P X.
       FINITE X /\
       (!v M N. ~(v IN X) /\ ~(v IN FV N) ==>
                P (LAM v M @@ N) [] ([N/v]M)) /\
       (!n v M N. ~(v IN X) /\ ~(v IN FV N) ==>
                  P (LAMi n v M N) [] ([N/v]M)) /\
       (!M M' N pos. P M pos M' ==> P (M @@ N) (Lt::pos) (M' @@ N)) /\
       (!M N N' pos. P N pos N' ==> P (M @@ N) (Rt::pos) (M @@ N')) /\
       (!v M M' pos. ~(v IN X) /\ P M pos M' ==>
                 P (LAM v M) (In::pos) (LAM v M')) /\
       (!n v M M' N pos. ~(v IN FV N) /\ ~(v IN X) /\ P M pos M' ==>
                         P (LAMi n v M N) (Lt::In::pos) (LAMi n v M' N)) /\
       (!n v M N N' pos. ~(v IN FV N) /\ ~(v IN X) /\ ~(v IN FV N') /\
                         P N pos N' ==>
                         P (LAMi n v M N) (Rt::pos) (LAMi n v M N')) ==>
       !M pos N. lrcc (beta0 RUNION beta1) M pos N ==> P M pos N``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M pos N. lrcc (beta0 RUNION beta1) M pos N ==>
                            !p. P (ltpm p M) pos (ltpm p N)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC lrcc_ind THEN SRW_TAC [][beta0_def, beta1_def, RUNION]
  THENL [
    SRW_TAC [][ltpm_subst] THEN
    Q.MATCH_ABBREV_TAC `P (LAMi n vv MM NN) [] ([NN/vv]MM)` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `X UNION FV MM UNION FV NN` THEN
    `LAMi n vv MM NN = LAMi n z (ltpm [(z,vv)] MM) NN`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    `[NN/vv]MM = [NN/z] ([VAR z/vv] MM)` by SRW_TAC [][l15a] THEN
    SRW_TAC [][GSYM fresh_ltpm_subst],
    SRW_TAC [][ltpm_subst] THEN
    Q.MATCH_ABBREV_TAC `P (LAM vv MM @@ NN) [] ([NN/vv]MM)` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `X UNION FV MM UNION FV NN` THEN
    `LAM vv MM = LAM z (ltpm [(z,vv)] MM)` by SRW_TAC [][ltpm_ALPHA] THEN
    `[NN/vv]MM = [NN/z] ([VAR z/vv] MM)` by SRW_TAC [][l15a] THEN
    SRW_TAC [][GSYM fresh_ltpm_subst],
    Q.MATCH_ABBREV_TAC `P (LAM vv MM) (In::pos) (LAM vv NN)` THEN
    Q_TAC (NEW_TAC "z") `X UNION FV MM UNION FV NN` THEN
    `(LAM vv MM = LAM z (ltpm [(z,vv)] MM)) /\
     (LAM vv NN = LAM z (ltpm [(z,vv)] NN))` by SRW_TAC [][ltpm_ALPHA] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose],
    Q.MATCH_ABBREV_TAC `P (LAMi n vv ZZ MM) (Rt::Pos) (LAMi n vv ZZ NN)` THEN
    Q_TAC (NEW_TAC "z") `FV ZZ UNION FV MM UNION FV NN UNION X` THEN
    `(LAMi n vv ZZ MM = LAMi n z (ltpm [(z,vv)] ZZ) MM) /\
     (LAMi n vv ZZ NN = LAMi n z (ltpm [(z,vv)] ZZ) NN)`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose],
    Q.MATCH_ABBREV_TAC
      `P (LAMi n vv MM ZZ) (Lt::In::pos) (LAMi n vv NN ZZ)` THEN
    Q_TAC (NEW_TAC "z") `FV ZZ UNION FV MM UNION FV NN UNION X` THEN
    `(LAMi n vv MM ZZ = LAMi n z (ltpm [(z,vv)] MM) ZZ) /\
     (LAMi n vv NN ZZ = LAMi n z (ltpm [(z,vv)] NN) ZZ)`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose]
  ]);

val lrcc_bvc_ind = store_thm(
  "lrcc_bvc_ind",
  ``!P X.
       FINITE X /\
       lpermutative R /\
       (!M N. R M N ==> P M [] N) /\
       (!M M' N pos. P M pos M' ==> P (M @@ N) (Lt::pos) (M' @@ N)) /\
       (!M N N' pos. P N pos N' ==> P (M @@ N) (Rt::pos) (M @@ N')) /\
       (!v M M' pos. ~(v IN X) /\ P M pos M' ==>
                 P (LAM v M) (In::pos) (LAM v M')) /\
       (!n v M M' N pos. ~(v IN FV N) /\ ~(v IN X) /\ P M pos M' ==>
                         P (LAMi n v M N) (Lt::In::pos) (LAMi n v M' N)) /\
       (!n v M N N' pos. ~(v IN FV N) /\ ~(v IN X) /\ ~(v IN FV N') /\
                         P N pos N' ==>
                         P (LAMi n v M N) (Rt::pos) (LAMi n v M N')) ==>
       !M pos N. lrcc R M pos N ==> P M pos N``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M pos N. lrcc R M pos N ==>
                            !p. P (ltpm p M) pos (ltpm p N)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC lrcc_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [lpermutative_def],
    Q.MATCH_ABBREV_TAC `P (LAM vv MM) (In::pos) (LAM vv NN)` THEN
    Q_TAC (NEW_TAC "z") `X UNION FV MM UNION FV NN` THEN
    `(LAM vv MM = LAM z (ltpm [(z,vv)] MM)) /\
     (LAM vv NN = LAM z (ltpm [(z,vv)] NN))` by SRW_TAC [][ltpm_ALPHA] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose],
    Q.MATCH_ABBREV_TAC `P (LAMi n vv ZZ MM) (Rt::Pos) (LAMi n vv ZZ NN)` THEN
    Q_TAC (NEW_TAC "z") `FV ZZ UNION FV MM UNION FV NN UNION X` THEN
    `(LAMi n vv ZZ MM = LAMi n z (ltpm [(z,vv)] ZZ) MM) /\
     (LAMi n vv ZZ NN = LAMi n z (ltpm [(z,vv)] ZZ) NN)`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose],
    Q.MATCH_ABBREV_TAC
      `P (LAMi n vv MM ZZ) (Lt::In::pos) (LAMi n vv NN ZZ)` THEN
    Q_TAC (NEW_TAC "z") `FV ZZ UNION FV MM UNION FV NN UNION X` THEN
    `(LAMi n vv MM ZZ = LAMi n z (ltpm [(z,vv)] MM) ZZ) /\
     (LAMi n vv NN ZZ = LAMi n z (ltpm [(z,vv)] NN) ZZ)`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][Abbr`MM`, Abbr`NN`, GSYM pmact_decompose]
  ]);


val lrcc_labelled_redn = store_thm(
  "lrcc_labelled_redn",
  ``!x r y.
      lrcc (beta0 RUNION beta1) x r y ==>
      labelled_redn beta (strip_label x) r (strip_label y)``,
  HO_MATCH_MP_TAC lrcc_bvc_b01_ind THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][strip_label_subst, labelled_redn_rules] THEN
  METIS_TAC [beta_def, labelled_redn_rules]);

val strip_path_label_def = Define`strip_path_label = pmap strip_label I`;

val strip_path_label_thm = store_thm(
  "strip_path_label_thm",
  ``(!x. strip_path_label (stopped_at x) = stopped_at (strip_label x)) /\
    (!x r p.
         strip_path_label (pcons x r p) =
            pcons (strip_label x) r (strip_path_label p))``,
  SRW_TAC [][strip_path_label_def, pmap_thm, combinTheory.I_THM]);
val _ = export_rewrites ["strip_path_label_thm"]

val first_strip_path_label = store_thm(
  "first_strip_path_label",
  ``!p. first (strip_path_label p) = strip_label (first p)``,
  GEN_TAC THEN
  Q.ISPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][first_thm, strip_path_label_thm]);
val _ = export_rewrites ["first_strip_path_label"]

(* ----------------------------------------------------------------------
    proofs begin
   ---------------------------------------------------------------------- *)

val lemma11_2_1 = store_thm(
  "lemma11_2_1",
  ``!sigma'.
       okpath (lrcc (beta0 RUNION beta1)) sigma' ==>
       okpath (labelled_redn beta) (strip_path_label sigma')``,
  Q_TAC SUFF_TAC
        `!sigma.
            (?sigma'. (sigma = strip_path_label sigma') /\
                      okpath (lrcc (beta0 RUNION beta1)) sigma') ==>
            okpath (labelled_redn beta) sigma` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN
  SRW_TAC [][Once EXISTS_path, SimpL ``(==>)``] THEN
  SRW_TAC [][] THEN PROVE_TAC [lrcc_labelled_redn]);

val beta0_lsubstitutive = store_thm(
  "beta0_lsubstitutive",
  ``lsubstitutive beta0``,
  SRW_TAC [][lsubstitutive_def, beta0_def] THEN
  Q_TAC (NEW_TAC "z") `{v; v'} UNION FV t UNION FV L` THEN
  `LAMi n v' t u = LAMi n z (ltpm [(z,v')] t) u`
     by SRW_TAC [][ltpm_ALPHAi] THEN
  ASM_SIMP_TAC (srw_ss()) [lSUB_THM] THEN
  MAP_EVERY Q.EXISTS_TAC [`n`, `z`, `[L/v] ([VAR z/v'] t)`, `[L/v]u`] THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM lSUBSTITUTION_LEMMA, l15a,
                           fresh_ltpm_subst]);

val beta1_lsubstitutive = store_thm(
  "beta1_lsubstitutive",
  ``lsubstitutive beta1``,
  SIMP_TAC (srw_ss()) [lsubstitutive_def, beta1_def, lSUB_THM,
                       GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN
  Q_TAC (NEW_TAC "z") `{v; v'} UNION FV t UNION FV L` THEN
  `LAM v' t = LAM z (ltpm [(z,v')] t)` by SRW_TAC [][ltpm_ALPHA] THEN
  MAP_EVERY Q.EXISTS_TAC [`z`, `[L/v]([VAR z/v']t)`] THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM lSUBSTITUTION_LEMMA, l15a,
                           fresh_ltpm_subst]);

val lrcc_lsubstitutive = store_thm(
  "lrcc_lsubstitutive",
  ``!R. lsubstitutive R ==>
        !M pos N.
           lrcc R M pos N ==> !v L. lrcc R ([L/v]M) pos ([L/v]N)``,
  GEN_TAC THEN REPEAT STRIP_TAC THEN
  Q.UNDISCH_THEN `lrcc R M pos N` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`N`, `pos`, `M`] THEN
  HO_MATCH_MP_TAC lrcc_bvc_ind THEN Q.EXISTS_TAC `v INSERT FV L` THEN
  SRW_TAC [][lsubstitutive_lpermutative, lrcc_rules] THEN
  METIS_TAC [lsubstitutive_def, lrcc_rules]);

val labelled_redn_beta_sub = store_thm(
  "labelled_redn_beta_sub",
  ``!M pos N. labelled_redn beta M pos N ==>
              !t v. labelled_redn beta ([t/v]M) pos ([t/v]N)``,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`N`, `pos`, `M`] THEN
  HO_MATCH_MP_TAC labelled_redn_bvc_ind THEN
  Q.EXISTS_TAC `v INSERT FV t` THEN
  SRW_TAC [][labelled_redn_rules, SUB_THM] THEN
  METIS_TAC [substitution_lemma, labelled_redn_rules, beta_def]);

val lrcc_beta_sub = store_thm(
  "lrcc_beta_sub",
  ``!M pos N. lrcc (beta0 RUNION beta1) M pos N ==>
              !v t. lrcc (beta0 RUNION beta1) ([t/v]M) pos ([t/v]N)``,
  PROVE_TAC [lrcc_lsubstitutive, beta0_lsubstitutive, beta1_lsubstitutive,
             RUNION_lsubstitutive]);

val lrcc_b01_ltpm_imp = store_thm(
  "lrcc_b01_ltpm_imp",
  ``!M pos N. lrcc (beta0 RUNION beta1) M pos N ==>
              lrcc (beta0 RUNION beta1) (ltpm p M) pos (ltpm p N)``,
  HO_MATCH_MP_TAC lrcc_ind THEN
  SRW_TAC [][lrcc_rules, beta0_def, beta1_def, RUNION] THEN
  SRW_TAC [][ltpm_subst] THEN
  METIS_TAC [lrcc_rules, RUNION, beta0_def, beta1_def]);

val lrcc_b01_ltpm_eqn = store_thm(
  "lrcc_b01_ltpm_eqn",
  ``lrcc (beta0 RUNION beta1) (ltpm p M) pos N =
    lrcc (beta0 RUNION beta1) M pos (ltpm (REVERSE p) N)``,
  METIS_TAC [lrcc_b01_ltpm_imp, pmact_inverse]);

val lrcc_lcc = store_thm(
  "lrcc_lcc",
  ``!M pos N. lrcc R M pos N ==> lcompat_closure R M N``,
  HO_MATCH_MP_TAC lrcc_ind THEN PROVE_TAC [lcompat_closure_rules]);

val lrcc_beta_lam = store_thm(
  "lrcc_beta_lam",
  ``!pos v t N.
        lrcc (beta0 RUNION beta1) (LAM v t) pos N =
        ?pos0 N0.
            lrcc (beta0 RUNION beta1) t pos0 N0 /\
            (pos = In :: pos0) /\ (N = LAM v N0)``,
  SRW_TAC [][Once lrcc_cases, SimpLHS] THEN
  SRW_TAC [][relationTheory.RUNION, beta0_def, beta1_def, lLAM_eq_thm,
             ltpm_eqr, EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [lrcc_b01_ltpm_eqn, pmact_flip_args] THENL [
    MAP_EVERY IMP_RES_TAC [lrcc_lcc, lcc_beta_FV] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    PROVE_TAC [basic_swapTheory.swapstr_def],
    METIS_TAC []
  ]);

val rcc_beta_matched = prove(
  ``!M pos N.
       labelled_redn beta M pos N ==>
       !M'. (M = strip_label M') ==>
            ?N'. lrcc (beta0 RUNION beta1) M' pos N' /\
                 (N = strip_label N')``,
  HO_MATCH_MP_TAC labelled_redn_ind THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [beta_matched, lrcc_rules],
    POP_ASSUM MP_TAC THEN
    `∃s. (M' = VAR s) ∨ (∃t1 t2. M' = t1 @@ t2) ∨ (∃v t. M' = LAM v t) ∨
         (∃n v t1 t2. M' = LAMi n v t1 t2)`
      by (Q.SPEC_THEN `M'` STRUCT_CASES_TAC lterm_CASES THEN SRW_TAC [][] THEN
          METIS_TAC []) THEN
    SRW_TAC [][] THENL [
      PROVE_TAC [strip_label_thm, lrcc_rules],
      POP_ASSUM (Q.SPEC_THEN `LAM v t1` MP_TAC) THEN
      SRW_TAC [][lrcc_beta_lam] THEN
      Q.EXISTS_TAC `LAMi n v N0 t2` THEN
      SRW_TAC [][lrcc_rules]
    ],
    POP_ASSUM MP_TAC THEN
    Q.SPEC_THEN `M'` STRUCT_CASES_TAC lterm_CASES THEN
    SRW_TAC [][] THEN
    PROVE_TAC [strip_label_thm, lrcc_rules],
    POP_ASSUM MP_TAC THEN SRW_TAC [][strip_label_eq_lam] THEN
    PROVE_TAC [strip_label_thm, lrcc_rules]
  ]);

val rcc_bmatched =
    (SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] o
     SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM]) rcc_beta_matched

val _ = print "Defining the lifting of reductions and paths\n";

val lift_redn_def = new_specification (
  "lift_redn_def", ["lift_redn"],
  prove(``?g.
             !pos N M'.
                labelled_redn beta (strip_label M') pos N ==>
                lrcc (beta0 RUNION beta1) M' pos (g M' pos N) /\
                (N = strip_label (g M' pos N))``,
        STRIP_ASSUME_TAC rcc_bmatched THEN
        Q.EXISTS_TAC `\M' pos N. f pos N M'` THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []));

val lift_path0 =
    ISPEC ``\X : (lterm # (term, redpos list) path).
              let M' = FST X in
              let q = SND X in
              let x = first q in
              if is_stopped q then (M', NONE)
              else let r = first_label q in
              let t = tail q in
              let y' = lift_redn M' r (first t) in
                (M', SOME (r, (y', t)))`` path_Axiom

val lift_path_exists = prove(
  ``?h:lterm -> (term, redpos list) path -> (lterm, redpos list) path.
       (!M' x. h M' (stopped_at x) = stopped_at M') /\
       (!M' x r p.
               h M' (pcons x r p) =
                 pcons M' r (h (lift_redn M' r (first p)) p))``,
  STRIP_ASSUME_TAC lift_path0 THEN
  Q.EXISTS_TAC `\M' p. g (M', p)` THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM (fn th => SIMP_TAC (srw_ss()) [SimpLHS, Once th]) THEN
  SRW_TAC [][]);

val lift_path_def = new_specification (
  "lift_path_def", ["lift_path"], lift_path_exists);

val first_lift_path = store_thm(
  "first_lift_path",
  ``!M' p. first (lift_path M' p) = M'``,
  REPEAT GEN_TAC THEN
  Q.ISPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][lift_path_def]);

val strip_path_label_lift_path = store_thm(
  "strip_path_label_lift_path",
  ``!p M'. okpath (labelled_redn beta) p /\ (strip_label M' = first p) ==>
           (strip_path_label (lift_path M' p) = p)``,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [path_bisimulation] THEN
  Q.EXISTS_TAC `\x y. ?M'. (x = strip_path_label (lift_path M' y)) /\
                           okpath (labelled_redn beta) y /\
                           (strip_label M' = first y)` THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    `(?x. q2 = stopped_at x) \/
     (?x r p'. (q2 = pcons x r p') /\ labelled_redn beta x r (first p') /\
               okpath (labelled_redn beta) p')` by PROVE_TAC [okpath_cases]
    THEN SRW_TAC [][lift_path_def, strip_path_label_thm] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    PROVE_TAC [lift_redn_def]
  ]);

val strip_path_label_okpath = store_thm(
  "strip_path_label_okpath",
  ``!M' p. okpath (labelled_redn beta) p /\ (first p = strip_label M') ==>
           okpath (lrcc (beta0 RUNION beta1)) (lift_path M' p)``,
  Q_TAC SUFF_TAC
        `!p'. (?M' p. okpath (labelled_redn beta) p /\
                      (first p = strip_label M') /\
                      (p' = lift_path M' p)) ==>
              okpath (lrcc (beta0 RUNION beta1)) p'` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN
  SIMP_TAC (srw_ss()) [Once okpath_cases, SimpL ``(==>)``] THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [lift_path_def, first_lift_path] THEN
  PROVE_TAC [lift_redn_def]);

val lemma11_2_2 = store_thm(
  "lemma11_2_2",
  ``!sigma.
       okpath (labelled_redn beta) sigma ==>
       !M'. (strip_label M' = first sigma) ==>
            ?sigma'. (first sigma' = M') /\
                     (strip_path_label sigma' = sigma) /\
                     okpath (lrcc (beta0 RUNION beta1)) sigma'``,
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `lift_path M' sigma` THEN
  SRW_TAC [][first_lift_path, strip_path_label_okpath,
             strip_path_label_lift_path]);

(* support the notation of saying that a redex position is \in a
   term *)

val is_redex_occurrence_def =
    Define`is_redex_occurrence pos M = ?N. labelled_redn beta M pos N`;

val is_redex_occurrence_thm = store_thm(
  "is_redex_occurrence_thm",
  ``(!s p. is_redex_occurrence p (VAR s) = F) /\
    (!t u p. is_redex_occurrence p (t @@ u) <=>
                is_abs t /\ (p = []) \/
                (p = Lt :: TL p) /\ is_redex_occurrence (TL p) t \/
                (p = Rt :: TL p) /\ is_redex_occurrence (TL p) u) /\
    (!v t p. is_redex_occurrence p (LAM v t) <=>
                (p = In :: TL p) /\ is_redex_occurrence (TL p) t)``,
  SIMP_TAC pureSimps.pure_ss [is_redex_occurrence_def] THEN
  REPEAT CONJ_TAC THEN
  SRW_TAC [][SimpLHS, Once labelled_redn_cases] THEN
  SRW_TAC [][beta_def, EQ_IMP_THM] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    PROVE_TAC [is_abs_thm, term_CASES],
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC [],
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC [],
    FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm] THEN
    PROVE_TAC [labelled_redn_beta_sub, fresh_tpm_subst],
    PROVE_TAC []
  ]);

val redexes_all_occur_def =
    Define`redexes_all_occur posS M =
               !s. s IN posS ==> is_redex_occurrence s M`

val _ = overload_on("IN", ``is_redex_occurrence``);
val _ = overload_on("SUBSET", ``redexes_all_occur``);

val redex_posns_redex_occurrence = store_thm(
  "redex_posns_redex_occurrence",
  ``!t. redex_posns t = {p | p IN t}``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][redex_posns_thm, is_redex_occurrence_thm, EXTENSION] THEN
  SRW_TAC [][EQ_IMP_THM] THEN PROVE_TAC [lemma14a, listTheory.TL]);

val IN_term_IN_redex_posns = store_thm(
  "IN_term_IN_redex_posns",
  ``!x M. x IN M <=> x IN redex_posns M``,
  SRW_TAC [][redex_posns_redex_occurrence]);

val ordering = prove(
  ``(?f:lterm -> num -> 'a. P f) = (?f. P (\n t. f t n))``,
  EQ_TAC THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `λt n. f n t` THEN SRW_TAC [ETA_ss][],
    METIS_TAC []
  ]);
val n_posns_exists =
    parameter_ltm_recursion
        |> INST_TYPE [alpha |-> ``:posn set``, ``:ρ`` |-> ``:num``]
        |> Q.INST [`vr` |-> `\s n. {}`, `A` |-> `{}`,
                   `apm` |-> `discrete_pmact`,
                   `ap` |-> `\r1 r2 t1 t2 n.
                               IMAGE (CONS Lt) (r1 n) ∪ IMAGE (CONS Rt) (r2 n)`,
                   `lm` |-> `\r v t n. IMAGE (CONS In) (r n)`,
                   `li` |-> `\r1 r2 m v t1 t2 n.
                               IMAGE (APPEND [Lt; In]) (r1 n) UNION
                               IMAGE (CONS Rt) (r2 n) UNION
                               (if n = m then {[]} else {})`,
                   `ppm` |-> `discrete_pmact`]
        |> SIMP_RULE (srw_ss()) [fnpm_def, ordering]
        |> CONV_RULE (DEPTH_CONV (nomdatatype.rename_vars [("p", "n")]) THENC
                      BINDER_CONV (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])))

val n_posns_def = new_specification("n_posns_def", ["n_posns"],
                                    n_posns_exists);
val _ = export_rewrites ["n_posns_def"]

val n_posns_vsubst_invariant = Store_Thm(
  "n_posns_vsubst_invariant",
  ``!M m u w. n_posns m ([VAR u/w] M) = n_posns m M``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `M` THEN
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `{u;w}` THEN SRW_TAC [][lSUB_VAR]);

(* ----------------------------------------------------------------------
    n_label : labels (some of) a term's redexes, producing an lterm
   ---------------------------------------------------------------------- *)

(* first a little constant to apply t2 to t1, creating a LAMi redex, if the
   left argument t1 is a LAM. *)
val ordering = prove(
  ``(?f:lterm -> num # lterm -> lterm. P f) <=>
    (?f. P (\t1 (n,t2). f n t1 t2))``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `\n t1 t2. f t1 (n, t2)` THEN SRW_TAC [][] THEN
    CONV_TAC (DEPTH_CONV pairLib.PAIRED_ETA_CONV) THEN SRW_TAC [ETA_ss][],
    METIS_TAC []
  ])
val rAPP_exists =
    parameter_ltm_recursion
        |> INST_TYPE [alpha |-> ``:lterm``,
                      ``:ρ`` |-> ``:num # lterm``]
        |> Q.INST [`ap` |-> `\rt ru t u (n,p). (t @@ u) @@ p`,
             `vr` |-> `\s (n,p). VAR s @@ p`,
             `lm` |-> `\rt v t (n,p). LAMi n v t p`,
             `li` |-> `\rt ru n v t u (m,p). LAMi n v t u @@ p`,
             `apm` |-> `lterm_pmact`, `ppm` |-> `pair_pmact discrete_pmact lterm_pmact`, `A` |-> `{}`]
        |> SIMP_RULE (srw_ss()) [ltpm_ALPHA, ltpm_ALPHAi, ordering,
                                 pairTheory.FORALL_PROD]
        |> CONV_RULE (DEPTH_CONV
                      (nomdatatype.rename_vars [("p_1", "n"), ("p_2", "M")]))
        |> nomdatatype.elim_unnecessary_atoms
             {finite_fv = labelledTermsTheory.FINITE_FV} []

val rAPP_def = new_specification("rAPP_def", ["rAPP"], rAPP_exists)
val _ = export_rewrites ["rAPP_def"]

val rAPP_LAMs = Store_Thm(
  "rAPP_LAMs",
  ``(rAPP n (LAM v t) M = LAMi n v t M) ∧
    (rAPP m (LAMi n v t1 t2) M = LAMi n v t1 t2 @@ M)``,
  CONJ_TAC THENL [
    Q_TAC (NEW_TAC "z") `FV t ∪ FV M` THEN
    `(LAM v t = LAM z (ltpm [(z,v)] t)) ∧
     (LAMi n v t M = LAMi n z (ltpm [(z,v)] t) M)`
       by SRW_TAC [][ltpm_ALPHA, ltpm_ALPHAi] THEN
    SRW_TAC [][],
    Q_TAC (NEW_TAC "z") `FV t1 ∪ FV M` THEN
    `(LAMi n v t1 t2 = LAMi n z (ltpm [(z,v)] t1) t2)`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][]
  ])

val FINITE_UPPERBOUND_SETS = store_thm(
  "FINITE_UPPERBOUND_SETS",
  ``!L P. FINITE L /\ (!s. s IN P ==> s SUBSET L) ==> FINITE P``,
  Q_TAC SUFF_TAC `!L. FINITE L ==> !P. (!s. s IN P ==> s SUBSET L) ==>
                                       FINITE P`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THENL [
    Q_TAC SUFF_TAC `(P = {}) \/ (P = {{}})` THEN1 SRW_TAC [][DISJ_IMP_THM] THEN
    Q.ISPEC_THEN `P` FULL_STRUCT_CASES_TAC SET_CASES THEN SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [EXTENSION] THEN SRW_TAC [][] THEN
    SRW_TAC [][EQ_IMP_THM],
    `P = {s | s IN P /\ e IN s} UNION {s | s IN P /\ ~(e IN s)}`
       by (SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
    POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THENL [
      `{s | s IN P /\ e IN s} =
         IMAGE ((INSERT) e) (IMAGE (\s. s DELETE e) {s | s IN P /\ e IN s})`
        by (ONCE_REWRITE_TAC [EXTENSION] THEN
            SRW_TAC [DNF_ss][] THEN
            SRW_TAC [][EQ_IMP_THM] THENL [
              Q.EXISTS_TAC `x` THEN SRW_TAC [][EXTENSION] THEN
              Cases_on `x' = e` THEN SRW_TAC [][],
              Q.MATCH_ABBREV_TAC `e INSERT (s DELETE e) IN P` THEN
              `e INSERT s DELETE e = s`
                 by (SRW_TAC [][EXTENSION] THEN
                     Cases_on `x = e` THEN SRW_TAC [][]) THEN
              SRW_TAC [][],
              SRW_TAC [][]
            ]) THEN
      POP_ASSUM SUBST1_TAC THEN
      MATCH_MP_TAC IMAGE_FINITE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC [],
      FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC []
    ]
  ]);

val ltpm_if = prove(
  ``ltpm [(x,y)] (if P then M else N) =
    if P then ltpm [(x,y)] M else ltpm [(x,y)] N``,
  SRW_TAC [][]);

open nomdatatype
val ordering = prove(
  ``(?f : term -> num # posn set -> lterm. P f) <=>
    (?f. P (\t (n,ps). f n t ps))``,
  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `\n t ps. f t (n, ps)` THEN SRW_TAC [][] THEN
    CONV_TAC (DEPTH_CONV pairLib.PAIRED_ETA_CONV) THEN
    SRW_TAC [ETA_ss][],
    METIS_TAC []
  ]) ;
val nlabel_exists =
    parameter_tm_recursion
        |> INST_TYPE [alpha |-> ``:lterm``, ``:ρ`` |-> ``:num # posn set``]
        |> Q.INST
            [`apm` |-> `lterm_pmact`, `A` |-> `{}`, `ppm` |-> `discrete_pmact`,
             `vr` |-> `\s nps. VAR s`,
             `ap` |-> `\rt ru t u (n,ps).
                        if [] IN ps then
                          rAPP n
                               (rt (n,{p | Lt::p IN ps}))
                               (ru (n,{p | Rt::p IN ps}))
                        else
                          (rt (n,{p | Lt::p IN ps})) @@
                          (ru (n,{p | Rt::p IN ps}))`,
             `lm` |-> `\rt v t (n,ps).
                          LAM v (rt (n,
                                     {p | In::p IN ps} INTER redex_posns t))`]
            |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD, fnpm_def,
                                     ltpm_if, ordering]
            |> prove_alpha_fcbhyp {ppm = ``discrete_pmact : (num # posn set) pmact``,
                                   alphas = [ltpm_ALPHA],
                                   rwts = []}
            |> CONV_RULE (DEPTH_CONV
                              (rename_vars [("p_1", "n"), ("p_2", "ps")]))

val nlabel_def = new_specification("nlabel_def", ["nlabel"], nlabel_exists)

val FV_rAPP = Store_Thm(
  "FV_rAPP",
  ``!M. FV (rAPP n M N) = FV M UNION FV N``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `FV N` THEN
  SRW_TAC [][]);

val FV_nlabel = Store_Thm(
  "FV_nlabel",
  ``!M n ps. FV (nlabel n M ps) = FV M``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][nlabel_def] THEN SRW_TAC [][]);

val rAPP_vsubst_commutes = store_thm(
  "rAPP_vsubst_commutes",
  ``!M. [VAR v/u](rAPP n M N) = rAPP n ([VAR v/u]M) ([VAR v/u]N)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `FV N UNION {u;v}` THEN SRW_TAC [][lSUB_VAR]);

val nlabel_vsubst_commutes = store_thm(
  "nlabel_vsubst_commutes",
  ``!n M w u ps. nlabel n ([VAR w/u] M) ps = [VAR w/u](nlabel n M ps)``,
  REPEAT GEN_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`ps`, `M`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;w}` THEN
  SRW_TAC [][SUB_THM, nlabel_def, SUB_VAR] THEN
  SRW_TAC [][rAPP_vsubst_commutes]);

val strip_label_rAPP = Store_Thm(
  "strip_label_rAPP",
  ``strip_label (rAPP n M N) = strip_label M @@ strip_label N``,
  Q.SPEC_THEN `M` STRUCT_CASES_TAC lterm_CASES THEN SRW_TAC [][]);
val strip_label_nlabel = Store_Thm(
  "strip_label_nlabel",
  ``!M ps. strip_label (nlabel n M ps) = M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][nlabel_def] THEN
  SRW_TAC [][]);

val not_abs_rAPP_APP = Store_Thm(
  "not_abs_rAPP_APP",
  ``~is_abs (strip_label M) ==> (rAPP n M N = M @@ N)``,
  Q.SPEC_THEN `M` STRUCT_CASES_TAC lterm_CASES THEN SRW_TAC [][]);

val nlabel_eq_inter = store_thm(
  "nlabel_eq_inter",
  ``!M m ps. nlabel m M ps = nlabel m M (ps INTER redex_posns M)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][nlabel_def] THENL [
    SRW_TAC [][redex_posns_thm] THEN
    Cases_on `is_abs M` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][GSPEC_AND],
    SRW_TAC [][redex_posns_thm] THEN SRW_TAC [][GSPEC_AND]
  ]);

val nlabel_thm = store_thm(
  "nlabel_thm",
  ``(!n s ps. nlabel n (VAR s) ps = VAR s) /\
    (!b v t u ps.
              nlabel n (LAM v t @@ u) ps =
               if [] IN ps then
                 LAMi n v (nlabel n t { p | Lt::In::p IN ps})
                          (nlabel n u { p | Rt :: p IN ps})
               else
                 LAM v (nlabel n t { p | Lt::In::p IN ps}) @@
                 (nlabel n u { p | Rt :: p IN ps})) /\
    (!t u n ps.
        ~is_abs t ==> (nlabel n (t @@ u) ps =
                       nlabel n t { p | Lt::p IN ps} @@
                       nlabel n u { p | Rt::p IN ps})) /\
    (!v t n ps. nlabel n (LAM v t) ps =
                LAM v (nlabel n t { p | In::p IN ps }))``,
  SRW_TAC [][nlabel_def, GSYM nlabel_eq_inter]);

val n_posns_nlabel = store_thm(
  "n_posns_nlabel",
  ``!M n ps. (n_posns n (nlabel n M ps) = ps INTER redex_posns M) /\
             !m. ~(m = n) ==> (n_posns m (nlabel n M ps) = {})``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][n_posns_def, nlabel_thm, redex_posns_thm] THENL [
    `?var b. M = LAM var b` by PROVE_TAC [term_CASES, is_abs_thm] THEN
    FULL_SIMP_TAC (srw_ss())[nlabel_thm, n_posns_def, redex_posns_thm] THEN
    SRW_TAC [][n_posns_def] THENL [
      `IMAGE (APPEND [Lt; In])
             (n_posns n (nlabel n b {p | Lt::In::p IN ps})) =
       IMAGE (CONS Lt)
             (IMAGE (CONS In)
                    (n_posns n (nlabel n b
                               { p | In :: p IN { q | Lt :: q IN ps}})))` by
          SRW_TAC [][EXTENSION, GSYM RIGHT_EXISTS_AND_THM] THEN
      ASM_SIMP_TAC bool_ss [] THEN
      SRW_TAC [][EXTENSION, GSYM RIGHT_EXISTS_AND_THM,
                 GSYM LEFT_EXISTS_AND_THM] THEN
      EQ_TAC THEN SRW_TAC [][] THEN SRW_TAC [][],
      `nlabel n b { p | Lt::In::p IN ps} =
       nlabel n b { p | In::p IN { q | Lt :: q IN ps}}` by
              SRW_TAC [][EXTENSION] THEN
      ASM_SIMP_TAC bool_ss [] THEN
      SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][] THEN
      PROVE_TAC []
    ],
    `?var b. M = LAM var b` by PROVE_TAC [term_CASES, is_abs_thm] THEN
    FULL_SIMP_TAC (srw_ss()) [nlabel_thm, n_posns_def, redex_posns_thm,
                              IMAGE_EQ_EMPTY] THEN
    SRW_TAC [][n_posns_def, IMAGE_EQ_EMPTY] THEN
    `nlabel n b { p | Lt::In::p IN ps} =
     nlabel n b { p | In::p IN { q | Lt :: q IN ps}}` by
            SRW_TAC [][EXTENSION] THEN
    ASM_SIMP_TAC bool_ss [],
    SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][],
    SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][]
  ]);

(* notation (M, S) in 11.2.3 correponds to ``nlabel 0 M S`` *)

(*val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 510),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "from", HardSpace 1, TM,
                                 BreakSpace(1,0), TOK "to", HardSpace 1],
                  term_name = "from_to"}


val from_to_def =
    Define`sigma from M to N =
              finite sigma /\ (first sigma = M) /\ (last sigma = N)`;
*)


val lv_posns_def = Define`lv_posns v t = v_posns v (strip_label t)`

val lv_posns_thm = store_thm(
  "lv_posns_thm",
  ``(!v s. lv_posns v (VAR s : lterm) = if s = v then {[]} else {}) /\
    (!v M N. lv_posns v (M @@ N : lterm) =
               IMAGE (CONS Lt) (lv_posns v M) UNION
               IMAGE (CONS Rt) (lv_posns v N)) /\
    (!v M. lv_posns v (LAM v M : lterm) = {}) /\
    (!v w M. ~(v = w) ==>
             (lv_posns v (LAM w M:lterm) = IMAGE (CONS In) (lv_posns v M))) /\
    (!v n M N. lv_posns v (LAMi n v M N:lterm) =
                  IMAGE (CONS Rt) (lv_posns v N)) /\
    (!v w n M N.
             ~(v = w) ==>
             (lv_posns v (LAMi n w M N:lterm) =
                  IMAGE (APPEND [Lt; In]) (lv_posns v M) UNION
                  IMAGE (CONS Rt) (lv_posns v N)))``,
  SRW_TAC [][lv_posns_def, v_posns_thm, strip_label_thm,
             GSYM IMAGE_COMPOSE,
             combinTheory.o_DEF] THEN
  Q_TAC SUFF_TAC `(\x. Lt::In::x) = APPEND [Lt;In]` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM]);

val lv_posns_vsubst = store_thm(
  "lv_posns_vsubst",
  ``!M x y z.
       lv_posns x ([VAR y/z] M) =
         if x = y then lv_posns x M UNION lv_posns z M
         else if x = z then {} else lv_posns x M``,
  SRW_TAC [][lv_posns_def, v_posns_vsubst, strip_label_subst,
             strip_label_thm]);

val n_posns_sub = store_thm(
  "n_posns_sub",
  ``!M t v n. n_posns n ([t/v] M) =
                n_posns n M UNION
                { APPEND vp np | vp IN lv_posns v M /\ np IN n_posns n t }``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `M` THEN
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `v INSERT FV t` THEN SRW_TAC [][] THENL [
    SRW_TAC [][lv_posns_thm, lSUB_THM, n_posns_def, EXTENSION],

    SRW_TAC [][lv_posns_thm, lSUB_THM, n_posns_def,
               EXTENSION, EQ_IMP_THM,
               GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
               RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM] THEN
    PROVE_TAC [],

    SRW_TAC [][lSUB_THM, n_posns_def, lv_posns_thm] THEN
    ASM_SIMP_TAC (srw_ss()) [EXTENSION] THEN GEN_TAC THEN
    EQ_TAC THEN SRW_TAC [][GSYM RIGHT_EXISTS_AND_THM, lv_posns_vsubst,
                           GSYM LEFT_EXISTS_AND_THM] THEN
    PROVE_TAC [],

    SRW_TAC [][lSUB_THM, n_posns_def, lv_posns_thm, lv_posns_vsubst] THEN
    SRW_TAC [][EXTENSION, EQ_IMP_THM,
               GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
               RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM] THEN
    PROVE_TAC [],

    SRW_TAC [][lSUB_THM, n_posns_def, lv_posns_thm, lv_posns_vsubst] THEN
    SRW_TAC [][EXTENSION, EQ_IMP_THM,
               GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
               RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM] THEN
    PROVE_TAC []
  ]);

val lrcc_new_labels = store_thm(
  "lrcc_new_labels",
  ``!x r y.
       lrcc (beta0 RUNION beta1) x r y ==>
       !n. (n_posns n x = EMPTY) ==> (n_posns n y = EMPTY)``,
  HO_MATCH_MP_TAC lrcc_ind THEN REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [beta0_def, relationTheory.RUNION, beta1_def,
                         DISJ_IMP_THM, FORALL_AND_THM,
                         GSYM LEFT_FORALL_IMP_THM, n_posns_def,
                         EMPTY_UNION,
                         IMAGE_EQ_EMPTY, n_posns_sub] THEN
    SRW_TAC [][EXTENSION],
    SIMP_TAC (srw_ss()) [n_posns_def, IMAGE_EQ_EMPTY],
    SIMP_TAC (srw_ss()) [n_posns_def, IMAGE_EQ_EMPTY],
    SIMP_TAC (srw_ss()) [n_posns_def, IMAGE_EQ_EMPTY],
    SIMP_TAC (srw_ss()) [n_posns_def, IMAGE_EQ_EMPTY],
    SIMP_TAC (srw_ss()) [n_posns_def, IMAGE_EQ_EMPTY]
  ]);

val nlabel_null_labelling = store_thm(
  "nlabel_null_labelling",
  ``!M n. nlabel n M {} = null_labelling M``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][nlabel_thm] THEN
  Cases_on `is_abs M` THENL [
    `?var b. M = LAM var b` by PROVE_TAC [term_CASES, is_abs_thm] THEN
    FULL_SIMP_TAC (srw_ss()) [nlabel_thm],
    SRW_TAC [][nlabel_thm]
  ]);

val n_posns_strip_label = store_thm(
  "n_posns_strip_label",
  ``!M' n. n_posns n M' SUBSET (strip_label M')``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][redexes_all_occur_def, n_posns_def, strip_label_thm,
             is_redex_occurrence_thm]
  THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    SRW_TAC [][] THEN PROVE_TAC [],
    PROVE_TAC [],
    PROVE_TAC [],
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN RES_TAC
  ]);

val rpos_UNION_11 = store_thm(
  "rpos_UNION_11",
  ``!s1 s2 t1 t2.
        (IMAGE (CONS Lt) s1 UNION IMAGE (CONS Rt) s2 =
         IMAGE (CONS Lt) t1 UNION IMAGE (CONS Rt) t2) <=>
        (s1 = t1) /\ (s2 = t2)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, EXTENSION,
                       DISJ_IMP_THM, FORALL_AND_THM,
                       GSYM LEFT_FORALL_IMP_THM] THEN
  PROVE_TAC []);

val IMAGE_CONS_11 = store_thm(
  "IMAGE_CONS_11",
  ``!h s1 s2. (IMAGE (CONS h) s1 = IMAGE (CONS h) s2) = (s1 = s2)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, EXTENSION,
                       DISJ_IMP_THM, FORALL_AND_THM,
                       GSYM LEFT_FORALL_IMP_THM]);

val IMAGE_APPEND = prove(
  ``!h t s X. IMAGE (APPEND (h::t)) X = IMAGE (CONS h) (IMAGE (APPEND t) X)``,
  SIMP_TAC (srw_ss()) [EXTENSION, EQ_IMP_THM,
                       GSYM LEFT_FORALL_IMP_THM]);

val LAMI_partly_11 = prove(
  ``!x y z w a b. (LAMi x y z w = LAMi x y a b) <=> (z = a) /\ (w = b)``,
  SRW_TAC [][lLAMi_eq_thm])


val stripped_equal = store_thm(
  "stripped_equal",
  ``!M' N'. (strip_label M' = strip_label N') /\ ~(M' = N') ==>
            ?n. ~(n_posns n M' = n_posns n N')``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  ASM_SIMP_TAC (srw_ss()) [strip_label_thm] THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][strip_label_thm] THEN
    Q.PAT_X_ASSUM `X = strip_label yy` (MP_TAC o SYM) THEN
    Q.SPEC_THEN `N'` FULL_STRUCT_CASES_TAC lterm_CASES THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][strip_label_thm] THEN
    Q.PAT_X_ASSUM `X = strip_label yy` (MP_TAC o SYM) THEN
    `(∃s. N' = VAR s) ∨ (∃t1 t2. N' = t1 @@ t2) ∨ (∃v t. N' = LAM v t) ∨
     (∃n v t1 t2. N' = LAMi n v t1 t2)`
       by (Q.SPEC_THEN `N'` FULL_STRUCT_CASES_TAC lterm_CASES THEN
           SRW_TAC [][] THEN METIS_TAC []) THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [rpos_UNION_11] THENL [
      METIS_TAC [],
      METIS_TAC [],
      Q.EXISTS_TAC `n` THEN SRW_TAC [][EXTENSION] THEN
      Q.EXISTS_TAC `[]` THEN SRW_TAC [][]
    ],
    SRW_TAC [][strip_label_thm] THEN
    Q.PAT_X_ASSUM `X = strip_label yy` (MP_TAC o SYM) THEN
    SRW_TAC [][strip_label_eq_lam] THEN
    SRW_TAC [][IMAGE_CONS_11] THEN PROVE_TAC [],
    MAP_EVERY Q.X_GEN_TAC [`v`, `n`, `t2`, `t1`] THEN
    SRW_TAC [][strip_label_thm] THEN
    Q.PAT_X_ASSUM `X = strip_label yy` (MP_TAC o SYM) THEN
    SRW_TAC [][strip_label_eq_redex] THENL [
      Q.EXISTS_TAC `n` THEN SRW_TAC [][EXTENSION] THEN
      Q.EXISTS_TAC `[]` THEN SRW_TAC [][],
      Cases_on `n = n'` THENL [
        FULL_SIMP_TAC (srw_ss()) [] THENL [
          Q.PAT_X_ASSUM `MM:lterm ≠ NN` MP_TAC THEN
          Q.MATCH_ABBREV_TAC `MM ≠ NN ==> GOAL` THEN
          Q.UNABBREV_TAC `GOAL` THEN markerLib.RM_ALL_ABBREVS_TAC THEN
          STRIP_TAC THEN
          `?m. ~(n_posns m MM = n_posns m NN)` by METIS_TAC [] THEN
          Q.EXISTS_TAC `m` THEN
          FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
          Q.EXISTS_TAC `Lt::In::x` THEN
          SRW_TAC [][] THEN SRW_TAC [][],

          Q.PAT_X_ASSUM `MM:lterm ≠ NN` MP_TAC THEN
          Q.MATCH_ABBREV_TAC `MM ≠ NN ==> GOAL` THEN
          Q.UNABBREV_TAC `GOAL` THEN markerLib.RM_ALL_ABBREVS_TAC THEN
          STRIP_TAC THEN
          `?m. ~(n_posns m MM = n_posns m NN)` by METIS_TAC [] THEN
          Q.EXISTS_TAC `m` THEN
          FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
          Q.EXISTS_TAC `Rt::x` THEN
          SRW_TAC [][] THEN SRW_TAC [][]
        ],
        Q.EXISTS_TAC `n'` THEN SRW_TAC [][EXTENSION] THEN
        Q.EXISTS_TAC `[]` THEN SRW_TAC [][]
      ]
    ]
  ]);

val nlabel_app_no_nil = store_thm(
  "nlabel_app_no_nil",
  ``!t u ps.
       ~([] IN ps) ==>
       (nlabel n (t @@ u) ps =
        nlabel n t { p | Lt::p IN ps} @@ nlabel n u { p | Rt::p IN ps})``,
  REPEAT STRIP_TAC THEN
  Cases_on `is_abs t` THENL [
    `?var b. t = LAM var b` by PROVE_TAC [term_CASES, is_abs_thm] THEN
    SRW_TAC [][nlabel_thm],
    SRW_TAC [][nlabel_thm]
  ]);

val nlabel_n_posns = store_thm(
  "nlabel_n_posns",
  ``!M' n. (!m. ~(m = n) ==> (n_posns m M' = {})) ==>
           (nlabel n (strip_label M') (n_posns n M') = M')``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][strip_label_thm, nlabel_thm],
    SRW_TAC [][n_posns_def, nlabel_thm, strip_label_thm,
               IMAGE_EQ_EMPTY, EMPTY_UNION,
               nlabel_app_no_nil],
    SRW_TAC [][n_posns_def, nlabel_thm, strip_label_thm,
               IMAGE_EQ_EMPTY],
    SRW_TAC [][n_posns_def, nlabel_thm, strip_label_thm,
               IMAGE_EQ_EMPTY,
               EMPTY_UNION] THEN
    SRW_TAC [][] THENL [
      FULL_SIMP_TAC (srw_ss()) [],
      FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN METIS_TAC []
    ]
  ]);

val labelled_term_component_equality = store_thm(
  "labelled_term_component_equality",
  ``!M' N'. (M' = N') <=> (strip_label M' = strip_label N') /\
                          (!n. n_posns n M' = n_posns n N')``,
  SRW_TAC [][EQ_IMP_THM] THEN SPOSE_NOT_THEN ASSUME_TAC THEN
  PROVE_TAC [stripped_equal]);

val residuals_exist = store_thm(
  "residuals_exist",
  ``!sigma. okpath (labelled_redn beta) sigma /\ finite sigma ==>
            !posS.
                   ?posS'.
                      (last (lift_path (nlabel 0 (first sigma) posS) sigma) =
                       nlabel 0 (last sigma) posS') /\
                      posS' SUBSET redex_posns (last sigma)``,
  HO_MATCH_MP_TAC finite_okpath_ind THEN
  SIMP_TAC (srw_ss()) [first_thm, last_thm, lift_path_def] THEN
  REPEAT CONJ_TAC THENL [
    PROVE_TAC [nlabel_eq_inter, IN_INTER, SUBSET_DEF],
    MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN REPEAT STRIP_TAC THEN
    Q.ABBREV_TAC `y = first p` THEN
    Q.ABBREV_TAC `x' = nlabel 0 x posS` THEN
    Q.ABBREV_TAC `y' = lift_redn x' r y` THEN
    Q_TAC SUFF_TAC `?posS'. (y' = nlabel 0 y posS')` THEN1
          PROVE_TAC [] THEN
    `strip_label x' = x` by PROVE_TAC [strip_label_nlabel] THEN
    `lrcc (beta0 RUNION beta1) x' r y' /\ (strip_label y' = y)` by
       PROVE_TAC [lift_redn_def] THEN
    `!m. ~(m = 0) ==> (n_posns m x' = {})` by PROVE_TAC [n_posns_nlabel] THEN
    `!m. ~(m = 0) ==> (n_posns m y' = {})` by PROVE_TAC [lrcc_new_labels] THEN
    Q.EXISTS_TAC `n_posns 0 y'` THEN
    PROVE_TAC [n_posns_strip_label, nlabel_n_posns]
  ]);

val residuals_def = new_specification (
  "residuals_def", ["residuals"],
  SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,
                     SKOLEM_THM] residuals_exist);

val residuals_can_ignore = store_thm(
  "residuals_can_ignore",
  ``!sigma ps.
       okpath (labelled_redn beta) sigma /\ finite sigma ==>
       (residuals sigma ps =
          residuals sigma (ps INTER redex_posns (first sigma)))``,
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `M = first sigma` THEN
  Q.ABBREV_TAC `N = last sigma` THEN
  Q.ABBREV_TAC `r1 = residuals sigma ps` THEN
  Q.ABBREV_TAC `r2 = residuals sigma (ps INTER redex_posns M)` THEN
  Q.ABBREV_TAC `N1 = nlabel 0 N r1` THEN
  Q.ABBREV_TAC `N2 = nlabel 0 N r2` THEN
  Q.ABBREV_TAC `M1 = nlabel 0 M ps` THEN
  Q.ABBREV_TAC `M2 = nlabel 0 M (ps INTER redex_posns M)` THEN
  `(last (lift_path M1 sigma) = N1) /\ (r1 SUBSET redex_posns N) /\
   (last (lift_path M2 sigma) = N2) /\ (r2 SUBSET redex_posns N)`
     by METIS_TAC [residuals_def] THEN
  `M1 = M2` by PROVE_TAC [nlabel_eq_inter] THEN
  `N1 = N2` by PROVE_TAC [] THEN
  `r1 INTER (redex_posns N) = r2 INTER (redex_posns N)`
      by PROVE_TAC [labelled_term_component_equality, n_posns_nlabel] THEN
  PROVE_TAC [SUBSET_INTER_ABSORPTION]);

val redex_posns_FINITE = store_thm(
  "redex_posns_FINITE",
  ``!M. FINITE (redex_posns M)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][redex_posns_thm]);

val residuals_FINITE = store_thm(
  "residuals_FINITE",
  ``!sigma ps.
        okpath (labelled_redn beta) sigma /\ finite sigma ==>
        FINITE (residuals sigma ps)``,
  PROVE_TAC [residuals_def, redex_posns_FINITE, SUBSET_FINITE]);

val residuals_EMPTY = store_thm(
  "residuals_EMPTY",
  ``!p. okpath (labelled_redn beta) p /\ finite p ==> (residuals p {} = {})``,
  HO_MATCH_MP_TAC finite_okpath_ind THEN REPEAT STRIP_TAC THENL [
    Q.SPEC_THEN `stopped_at x` (Q.SPEC_THEN `{}` MP_TAC o
                          REWRITE_RULE [okpath_thm, finite_thm])
                         residuals_def THEN
    SIMP_TAC (srw_ss())[last_thm, first_thm, lift_path_def,
                        labelled_term_component_equality,
                        strip_label_nlabel] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (Q.SPEC_THEN  `0`
                                (ASSUME_TAC o
                                 SIMP_RULE (srw_ss()) [n_posns_nlabel])) THEN
    PROVE_TAC [SUBSET_INTER_ABSORPTION],
    Q.SPEC_THEN `pcons x r p` MP_TAC residuals_def THEN
    ASM_SIMP_TAC (srw_ss())[last_thm, first_thm, lift_path_def,
                            strip_label_nlabel, finite_thm, okpath_thm] THEN
    DISCH_THEN (Q.SPEC_THEN `{}` MP_TAC) THEN
    `lift_redn (nlabel 0 x {}) r (first p) = nlabel 0 (first p) {}` by
        (SRW_TAC [][labelled_term_component_equality,
                    strip_label_nlabel]
         THENL[
           PROVE_TAC [lift_redn_def, strip_label_nlabel],
           Q.ABBREV_TAC `x' = nlabel 0 x {}` THEN
           `lrcc (beta0 RUNION beta1) (nlabel 0 x {}) r
                                      (lift_redn x' r (first p))` by
              PROVE_TAC [strip_label_nlabel, lift_redn_def] THEN
           `!n. n_posns n x' = {}` by
               PROVE_TAC [n_posns_nlabel, INTER_EMPTY] THEN
           `!n. n_posns n (nlabel 0 (first p) {}) = {}` by
               PROVE_TAC [n_posns_nlabel, INTER_EMPTY] THEN
           PROVE_TAC [lrcc_new_labels]
         ]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Q.SPEC_THEN `p` MP_TAC residuals_def THEN
    ASM_SIMP_TAC bool_ss [] THEN
    DISCH_THEN (Q.SPEC_THEN `{}` STRIP_ASSUME_TAC) THEN
    SIMP_TAC (srw_ss())[labelled_term_component_equality,
                        strip_label_nlabel] THEN
    STRIP_TAC THEN
    `{} INTER redex_posns (last p) =
         residuals (pcons x r p) {} INTER redex_posns (last p)` by
           PROVE_TAC [n_posns_nlabel] THEN
    POP_ASSUM MP_TAC THEN SRW_TAC [][] THEN
    PROVE_TAC [SUBSET_INTER_ABSORPTION]
  ]);

val nlabel_11 = store_thm(
  "nlabel_11",
  ``!t1 t2 n ps1 ps2. (nlabel n t1 ps1 = nlabel n t2 ps2) ==>
                      (t1 = t2) /\
                      (ps1 INTER redex_posns t1 = ps2 INTER redex_posns t1)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  `(n_posns n (nlabel n t1 ps1) = n_posns n (nlabel n t2 ps2)) /\
   (strip_label (nlabel n t1 ps1) = strip_label (nlabel n t2 ps2))` by
     PROVE_TAC [labelled_term_component_equality] THEN
  PROVE_TAC [n_posns_nlabel, strip_label_nlabel]);

val residuals_stopped_at = store_thm(
  "residuals_stopped_at",
  ``!x ps.
       residuals (stopped_at x) ps = ps INTER redex_posns x``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `stopped_at x` MP_TAC residuals_def THEN
  SIMP_TAC (srw_ss()) [lift_path_def] THEN
  DISCH_THEN (Q.SPEC_THEN `ps` STRIP_ASSUME_TAC) THEN
  `ps INTER (redex_posns x) =
     residuals (stopped_at x) ps INTER (redex_posns x)`
     by PROVE_TAC [nlabel_11] THEN
  PROVE_TAC [SUBSET_INTER_ABSORPTION]);

val residual1_def = Define`
  residual1 x r y ps = n_posns 0 (lift_redn (nlabel 0 x ps) r y)
`;

val residuals_pcons = store_thm(
  "residuals_pcons",
  ``!x r p ps.
        okpath (labelled_redn beta) p /\ finite p /\
        labelled_redn beta x r (first p) ==>
        (residuals (pcons x r p) ps =
         residuals p (residual1 x r (first p) ps))``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `pcons x r p` MP_TAC residuals_def THEN
  ASM_SIMP_TAC (srw_ss()) [lift_path_def, residual1_def] THEN
  DISCH_THEN (Q.SPEC_THEN `ps` MP_TAC) THEN
  Q.ABBREV_TAC `x' = nlabel 0 x ps` THEN
  Q.ABBREV_TAC `y = first p` THEN
  Q.ABBREV_TAC `y' = lift_redn x' r y` THEN
  `strip_label x' = x` by PROVE_TAC [strip_label_nlabel] THEN
  `(strip_label y' = y) /\ lrcc (beta0 RUNION beta1) x' r y'`
     by PROVE_TAC [lift_redn_def] THEN
  Q.SPEC_THEN `p` MP_TAC residuals_def THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `n_posns 0 y'` MP_TAC) THEN
  `!m. ~(m = 0) ==> (n_posns m x' = {})` by PROVE_TAC [n_posns_nlabel] THEN
  `!m. ~(m = 0) ==> (n_posns m y' = {})` by PROVE_TAC [lrcc_new_labels] THEN
  `nlabel 0 y (n_posns 0 y') = y'` by PROVE_TAC [nlabel_n_posns] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC nlabel_11 THEN
  PROVE_TAC [SUBSET_INTER_ABSORPTION]);

val residual1_SUBSET = store_thm(
  "residual1_SUBSET",
  ``!x r y ps. labelled_redn beta x r y ==>
               residual1 x r y ps SUBSET redex_posns y``,
  SRW_TAC [][residual1_def, redex_posns_redex_occurrence, SUBSET_DEF] THEN
  `x = strip_label (nlabel 0 x ps)` by SRW_TAC [][strip_label_nlabel] THEN
  `y = strip_label (lift_redn (nlabel 0 x ps) r y)` by
     PROVE_TAC [lift_redn_def] THEN
  PROVE_TAC [n_posns_strip_label, redexes_all_occur_def]);

val labelled_redn_lam = store_thm(
  "labelled_redn_lam",
  ``!v t r y.
       labelled_redn beta (LAM v t) r y =
       ?t' r'. labelled_redn beta t r' t' /\ (y = LAM v t') /\ (r = In::r')``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    SRW_TAC [][beta_def, Once labelled_redn_cases, SimpL ``(==>)``] THEN
    FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm, tpm_eqr, pmact_flip_args] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [labelled_redn_beta_tpm_eqn] THEN
    `!a. a IN FV (tpm [(v,v')] y') ==> a IN FV t`
      by METIS_TAC [labelled_redn_cc, cc_beta_FV_SUBSET,
                    SUBSET_DEF] THEN
    POP_ASSUM (Q.SPEC_THEN `v'` MP_TAC) THEN SRW_TAC [][],
    SRW_TAC [][] THEN SRW_TAC [][labelled_redn_rules]
  ]);

val labelled_redn_var = store_thm(
  "labelled_redn_var",
  ``~labelled_redn beta (VAR s) r t``,
  SRW_TAC [][Once labelled_redn_cases, beta_def]);
val _ = export_rewrites ["labelled_redn_var"]

val labelled_redn_vposn_sub = store_thm(
  "labelled_redn_vposn_sub",
  ``!body v x r y p.
         p IN v_posns v body /\
         labelled_redn beta x r y ==>
         ?M. labelled_redn beta ([x/v] body) (APPEND p r) M``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`p`, `body`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV x` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]THEN REPEAT CONJ_TAC THEN
  METIS_TAC [labelled_redn_rules, listTheory.APPEND]);

val BIGUNION_IMAGE_SING = prove(
  ``!s f. BIGUNION (IMAGE (\x. {f x}) s) = IMAGE f s``,
  SRW_TAC [][EXTENSION, EQ_IMP_THM, FORALL_AND_THM] THEN
  PROVE_TAC [IN_INSERT, NOT_IN_EMPTY]);

val lv_posns_nlabel = store_thm(
  "lv_posns_nlabel",
  ``!t v ps n. lv_posns v (nlabel n (strip_label t) ps) = lv_posns v t``,
  SRW_TAC [][lv_posns_def]);

val lv_posns_null_labelling = store_thm(
  "lv_posns_null_labelling",
  ``!t v ps. lv_posns v (null_labelling (strip_label t)) = lv_posns v t``,
  SRW_TAC [][lv_posns_def]);

val position_maps_exist = store_thm(
  "position_maps_exist",
  ``!x r y.
       labelled_redn beta x r y ==>
       ?f:redpos list -> redpos list set.
           !x'. (strip_label x' = x) ==>
                !y'. lrcc (beta0 RUNION beta1) x' r y' ==>
                     (strip_label y' = y) /\
                     !n. n_posns n y' =
                         BIGUNION (IMAGE f (n_posns n x'))``,
  HO_MATCH_MP_TAC simple_induction THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][],

    MAP_EVERY Q.X_GEN_TAC [`M`, `N`] THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss())
             [Once labelled_redn_cases, beta_def, SimpL ``(==>)``] THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
    REPEAT CONJ_TAC THENL [
      MAP_EVERY Q.X_GEN_TAC [`bv`, `body`] THEN SRW_TAC [][] THEN
      SRW_TAC [][RUNION, beta0_def, beta1_def, DISJ_IMP_THM,
                 Once lrcc_cases] THEN
      SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
      CONV_TAC EXISTS_AND_REORDER_CONV THEN
      CONJ_TAC THEN1
        (SRW_TAC [][strip_label_subst] THEN
         FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm, fresh_tpm_subst, lemma15a]) THEN
      SRW_TAC [][Once lrcc_cases, RUNION, beta0_def, beta1_def] THEN
      SIMP_TAC (srw_ss() ++ DNF_ss) [n_posns_sub] THEN

      Q.EXISTS_TAC `\p. if p = [] then {}
                        else if (HD p = Lt) /\ (HD (TL p) = In) then
                          {TL (TL p)}
                        else IMAGE (\vp. APPEND vp (TL p))
                                   (v_posns bv body)` THEN
      SRW_TAC [][] THEN
      REPEAT STRIP_TAC THEN
      (`v_posns bv body = lv_posns v t`
           by FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm, lv_posns_def] THEN
       POP_ASSUM SUBST_ALL_TAC THEN
       SRW_TAC [][n_posns_def, GSYM IMAGE_COMPOSE,
                  combinTheory.o_DEF, BIGUNION_IMAGE_SING] THEN
       (SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
        ASM_REWRITE_TAC [] THENL [
          DISJ2_TAC THEN
          Q.EXISTS_TAC `IMAGE (\vp. APPEND vp np) (lv_posns v t)` THEN
          SRW_TAC [][] THEN Q.EXISTS_TAC `np` THEN PROVE_TAC [],
          PROVE_TAC []
        ])),

      MAP_EVERY Q.X_GEN_TAC [`M'`, `pos`] THEN STRIP_TAC THEN
      RES_TAC THEN
      REPEAT (Q.PAT_X_ASSUM `!r y. labelled_redn beta X r y ==> Q X r y`
                          (K ALL_TAC)) THEN
      ONCE_REWRITE_TAC [lrcc_cases] THEN
      SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
      CONV_TAC EXISTS_AND_REORDER_CONV THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC [],
        REPEAT VAR_EQ_TAC THEN
        FULL_SIMP_TAC (srw_ss() ++ DNF_ss)
                      [strip_label_eq_lam, labelled_redn_lam,
                       lrcc_beta_lam] THEN
        SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
        ALL_TAC
      ] THEN
      Q.EXISTS_TAC `\p. if p = [] then {[]}
                        else if HD p = Lt then IMAGE (CONS Lt) (f (TL p))
                        else {p}` THEN
      SRW_TAC [][n_posns_def, GSYM IMAGE_COMPOSE,
                 BIGUNION_IMAGE_SING, combinTheory.o_DEF]
      THENL [
        FIRST_X_ASSUM (Q.SPEC_THEN `x` (ASSUME_TAC o REWRITE_RULE [])) THEN
        RES_TAC THEN
        REWRITE_TAC [EXTENSION] THEN
        SRW_TAC [ETA_ss][GSYM LEFT_EXISTS_AND_THM,
                                   GSYM RIGHT_EXISTS_AND_THM,
                                   EQ_IMP_THM] THEN PROVE_TAC [],
        ALL_TAC,
        ALL_TAC
      ] THEN
      FIRST_X_ASSUM
        (Q.SPEC_THEN `LAM v x` (ASSUME_TAC o SIMP_RULE (srw_ss()) [])) THEN
      `lrcc (beta0 RUNION beta1) (LAM v x) (In::r) (LAM v y)`
        by PROVE_TAC [lrcc_rules] THEN RES_TAC THEN
      POP_ASSUM MP_TAC THEN
      SIMP_TAC (srw_ss()) [n_posns_def] THEN
      REWRITE_TAC [EXTENSION] THEN
      SRW_TAC [ETA_ss]
              [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
               EQ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
      PROVE_TAC [],

      MAP_EVERY Q.X_GEN_TAC [`N'`,`pos`] THEN STRIP_TAC THEN RES_TAC THEN
      REPEAT (Q.PAT_X_ASSUM `!r y. labelled_redn beta X r y ==> Q X r y`
                          (K ALL_TAC)) THEN
      ONCE_REWRITE_TAC [lrcc_cases] THEN SRW_TAC [][] THEN
      SRW_TAC [DNF_ss][] THEN CONV_TAC EXISTS_AND_REORDER_CONV THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC [],
        PROVE_TAC [],
        ALL_TAC
      ] THEN
      Q.EXISTS_TAC `\p. if p = [] then {[]}
                        else if HD p = Rt then IMAGE (CONS Rt) (f (TL p))
                        else {p}` THEN
      SRW_TAC [][n_posns_def, GSYM IMAGE_COMPOSE,
                 BIGUNION_IMAGE_SING, combinTheory.o_DEF] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `x` (ASSUME_TAC o REWRITE_RULE [])) THEN
      RES_TAC THEN
      REWRITE_TAC [EXTENSION] THEN
      SRW_TAC [ETA_ss][GSYM LEFT_EXISTS_AND_THM,
                       GSYM RIGHT_EXISTS_AND_THM,
                       EQ_IMP_THM] THEN PROVE_TAC []
    ],

    MAP_EVERY Q.X_GEN_TAC [`bv`, `body`] THEN
    SRW_TAC [][labelled_redn_lam] THEN RES_TAC THEN
    Q.PAT_X_ASSUM `!r y. labelled_redn beta X r y ==> Q X r y`
                (K ALL_TAC) THEN
    Q.EXISTS_TAC `\p. IMAGE (CONS In) (f (TL p))` THEN
    SIMP_TAC (srw_ss())[strip_label_eq_lam, GSYM LEFT_FORALL_IMP_THM,
                        lrcc_beta_lam, n_posns_def] THEN
    REPEAT STRIP_TAC THENL [
      PROVE_TAC [],
      RES_TAC THEN
      REWRITE_TAC [EXTENSION] THEN
      SRW_TAC [][GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
                 EQ_IMP_THM] THEN PROVE_TAC []
    ]
  ]);

val residual1_pointwise_union = store_thm(
  "residual1_pointwise_union",
  ``!x r y.
       labelled_redn beta x r y ==>
       !ps1 ps2.
          residual1 x r y (ps1 UNION ps2) =
          residual1 x r y ps1 UNION residual1 x r y ps2``,
  SRW_TAC [][] THEN
  Q.ABBREV_TAC `x' = nlabel 0 x (ps1 UNION ps2)` THEN
  `strip_label x' = x` by PROVE_TAC [strip_label_nlabel] THEN
  Q.ABBREV_TAC `x1' = nlabel 0 x ps1` THEN
  Q.ABBREV_TAC `x2' = nlabel 0 x ps2` THEN
  `(strip_label x1' = x) /\ (strip_label x2' = x)`
     by PROVE_TAC [strip_label_nlabel] THEN
  Q.ABBREV_TAC `y' = lift_redn x' r y` THEN
  Q.ABBREV_TAC `y1' = lift_redn x1' r y` THEN
  Q.ABBREV_TAC `y2' = lift_redn x2' r y` THEN
  `lrcc (beta0 RUNION beta1) x' r y' /\ (strip_label y' = y) /\
   lrcc (beta0 RUNION beta1) x1' r y1' /\ (strip_label y1' = y) /\
   lrcc (beta0 RUNION beta1) x2' r y2' /\ (strip_label y2' = y)`
     by PROVE_TAC [lift_redn_def] THEN
  ASM_SIMP_TAC (srw_ss())[residual1_def] THEN
  `?f. !x' y'. (strip_label x' = x) /\
               lrcc (beta0 RUNION beta1) x' r y' ==>
               (n_posns 0 y' = BIGUNION (IMAGE f (n_posns 0 x')))`
     by PROVE_TAC [position_maps_exist] THEN
  `(n_posns 0 y' = BIGUNION (IMAGE f (n_posns 0 x'))) /\
   (n_posns 0 y1' = BIGUNION (IMAGE f (n_posns 0 x1'))) /\
   (n_posns 0 y2' = BIGUNION (IMAGE f (n_posns 0 x2')))` by PROVE_TAC [] THEN
  ASM_REWRITE_TAC [] THEN
  MAP_EVERY Q.UNABBREV_TAC [`x'`, `x1'`, `x2'`] THEN
  SIMP_TAC (srw_ss()) [n_posns_nlabel] THEN
  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
  REWRITE_TAC [EXTENSION] THEN
  SRW_TAC [][EQ_IMP_THM, GSYM LEFT_EXISTS_AND_THM,
             GSYM RIGHT_EXISTS_AND_THM] THEN
  PROVE_TAC []);

val residuals_pointwise_union = store_thm(
  "residuals_pointwise_union",
  ``!sigma.
       okpath (labelled_redn beta) sigma /\ finite sigma ==>
       !ps1 ps2. residuals sigma (ps1 UNION ps2) =
                 residuals sigma ps1 UNION residuals sigma ps2``,
  HO_MATCH_MP_TAC finite_okpath_ind THEN REPEAT STRIP_TAC THENL [
    SRW_TAC [][residuals_stopped_at, EXTENSION] THEN
    PROVE_TAC [],
    SRW_TAC [][residuals_pcons, residuals_pcons, residual1_pointwise_union]
  ]);

val lemma11_2_5 = store_thm(
  "lemma11_2_5",
  ``!sigma.
       okpath (labelled_redn beta) sigma /\ finite sigma ==>
       !r ps. residuals sigma (r INSERT ps) =
              residuals sigma {r} UNION residuals sigma ps``,
  REPEAT STRIP_TAC THEN
  CONV_TAC
    (LAND_CONV (ONCE_REWRITE_CONV [INSERT_SING_UNION])) THEN
  SRW_TAC [][residuals_pointwise_union]);

val lemma11_2_6 = store_thm(
  "lemma11_2_6",
  ``!sigma tau ps.
       finite sigma /\ okpath (labelled_redn beta) sigma /\
       finite tau /\ okpath (labelled_redn beta) tau /\
       (last sigma = first tau) ==>
       (residuals (plink sigma tau) ps = residuals tau (residuals sigma ps))``,
  Q_TAC SUFF_TAC
    `!sigma. okpath (labelled_redn beta) sigma /\ finite sigma ==>
             !tau ps.  finite tau /\ okpath (labelled_redn beta) tau /\
                       (last sigma = first tau) ==>
                       (residuals (plink sigma tau) ps =
                        residuals tau (residuals sigma ps))` THEN1
    PROVE_TAC [] THEN
  HO_MATCH_MP_TAC finite_okpath_ind THEN
  SRW_TAC [][residuals_stopped_at, residuals_pcons, first_plink,
             okpath_plink] THEN
  PROVE_TAC [residuals_can_ignore]);

(* skipping lemma11_2_8 because this requires me to invent a multi-label
   constant; maybe one that takes a finite map from positions to labels and
   labels a term accordingly. *)

(* definition 11.2.11 *)
val development_f_def = Define`
  development_f X =
      { (stopped_at x, ps) | T } UNION
      { (pcons x r p, ps) | (p, residual1 x r (first p) ps) IN X /\ r IN ps /\
                            labelled_redn beta x r (first p) }
`;

val development_f_monotone = store_thm(
  "development_f_monotone",
  ``monotone development_f``,
  SRW_TAC [][fixedPointTheory.monotone_def, SUBSET_DEF,
             development_f_def]);

val development0_def = Define`
  development0 sigma ps <=> (sigma, ps) IN gfp development_f
`;

val development0_coinduction = store_thm(
  "development0_coinduction",
  ``!P.
       (!sigma ps. P sigma ps ==>
                   (?x. (sigma = stopped_at x)) \/
                   (?x r p. (sigma = pcons x r p) /\ r IN ps /\
                            labelled_redn beta x r (first p) /\
                            P p (residual1 x r (first p) ps))) ==>
       !sigma ps. P sigma ps ==> development0 sigma ps``,
  GEN_TAC THEN STRIP_TAC THEN
  Q.SPEC_THEN `{ p | P (FST p) (SND p) }`
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [SUBSET_DEF,
                                                  pairTheory.FORALL_PROD])
              (MATCH_MP fixedPointTheory.gfp_coinduction
                        development_f_monotone) THEN
  SIMP_TAC (srw_ss()) [development0_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC (srw_ss()) [development_f_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN SRW_TAC [][]);

val development0_cases = save_thm(
  "development0_cases",
  (GEN_ALL o CONV_RULE (RENAME_VARS_CONV ["sigma", "ps"]) o
   SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD,
                         development_f_def, GSYM development0_def] o
   CONV_RULE (REWR_CONV EXTENSION) o
   CONJUNCT1)
    (MATCH_MP fixedPointTheory.gfp_greatest_fixedpoint
              (SPEC_ALL development_f_monotone)));

val term_posset_development_def = Define`
  term_posset_development M posset sigma <=>
      (first sigma = M) /\ posset SUBSET M /\ development0 sigma posset
`;

val _ = overload_on ("development", ``term_posset_development``);

val development_thm = store_thm(
  "development_thm",
  ``(stopped_at x IN development M ps <=> (M = x) /\ ps SUBSET M) /\
    (pcons x r p IN development M ps  <=>
             (M = x) /\ ps SUBSET M /\
             labelled_redn beta x r (first p) /\ r IN ps /\
             p IN development (first p) (residual1 x r (first p) ps))``,
  REPEAT STRIP_TAC THEN
  `!sigma M ps. sigma IN development M ps <=> development M ps sigma`
     by SRW_TAC [][SPECIFICATION] THEN
  SRW_TAC [][term_posset_development_def] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [development0_cases])) THEN
  SRW_TAC [][EQ_IMP_THM, redexes_all_occur_def, IN_term_IN_redex_posns] THEN
  PROVE_TAC [residual1_SUBSET, SUBSET_DEF]);

val development_cases = store_thm(
  "development_cases",
  ``!M ps sigma.
       sigma IN development M ps <=>
           (sigma = stopped_at M) /\ ps SUBSET M \/
           (?r p. (sigma = pcons M r p) /\ ps SUBSET M /\ r IN ps /\
                  labelled_redn beta M r (first p) /\
                  p IN development (first p) (residual1 M r (first p) ps))``,
  REPEAT GEN_TAC THEN
  Q.ISPEC_THEN `sigma` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][development_thm, EQ_IMP_THM]);

val developments_ok = store_thm(
  "developments_ok",
  ``!M sigma ps. sigma IN development M ps ==>
                 okpath (labelled_redn beta) sigma``,
  Q_TAC SUFF_TAC
      `!sigma. (?M ps. sigma IN development M ps)  ==>
                 okpath (labelled_redn beta) sigma` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN
  METIS_TAC [development_cases, pcons_11, stopped_at_not_pcons]);

val complete_development_def = Define`
  complete_development M ps sigma <=>
    finite sigma /\ sigma IN development M ps /\ (residuals sigma ps = {})
`;

val complete_development_thm = store_thm(
  "complete_development_thm",
  ``sigma IN complete_development M ps <=>
      finite sigma /\ sigma IN development M ps /\ (residuals sigma ps = {})``,
  SRW_TAC [][SPECIFICATION, complete_development_def]);

val term_development_def = Define`
  term_development M sigma = development M (redex_posns M) sigma
`;

val _ = overload_on ("development", ``term_development``);

val term_development_thm = store_thm(
  "term_development_thm",
  ``sigma IN development M <=> sigma IN development M (redex_posns M)``,
  SRW_TAC [][SPECIFICATION, term_development_def]);

val first_lift_path = store_thm(
  "first_lift_path",
  ``!p M. first (lift_path M p) = M``,
  SIMP_TAC (srw_ss()) [Once FORALL_path, lift_path_def]);

val lrcc_RUNION = store_thm(
  "lrcc_RUNION",
  ``!R M r N. lrcc R M r N ==> lrcc (R RUNION R') M r N``,
  GEN_TAC THEN HO_MATCH_MP_TAC lrcc_ind THEN
  PROVE_TAC [lrcc_rules, relationTheory.RUNION]);

val pick_a_beta = store_thm(
  "pick_a_beta",
  ``!M r N. lrcc (beta0 RUNION beta1) M r N <=>
            (?n. r IN n_posns n M) /\ lrcc beta0 M r N \/
            (!n. ~(r IN n_posns n M)) /\ lrcc beta1 M r N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC lrcc_ind THEN
    SRW_TAC [][n_posns_def, beta0_def, relationTheory.RUNION, beta1_def] THEN
    SRW_TAC [COND_elim_ss][n_posns_def] THEN
    PROVE_TAC [lrcc_rules, beta0_def, beta1_def],
    PROVE_TAC [lrcc_RUNION, RUNION_COMM]
  ]);

val lterm_INJECTIVITY_LEMMA1 = store_thm(
  "lterm_INJECTIVITY_LEMMA1",
  ``!v1 v2 t1 t2. (LAM v1 t1 = LAM v2 t2) ==> (t2 = [VAR v2/v1] t1)``,
  SRW_TAC [][lLAM_eq_thm] THEN SRW_TAC [][fresh_ltpm_subst, l15a]);
val lterm_INJECTIVITY_LEMMA1i = store_thm(
  "lterm_INJECTIVITY_LEMMA1i",
  ``!n1 n2 v1 v2 t1 t2 u1 u2.
        (LAMi n1 v1 t1 u1 = LAMi n2 v2 t2 u2) ==>
        (n1 = n2) /\ (u1 = u2) /\ (t2 = [VAR v2/v1] t1)``,
  SRW_TAC [][lLAMi_eq_thm] THEN SRW_TAC [][fresh_ltpm_subst, l15a]);

val lrcc_lpermutative = store_thm(
  "lrcc_lpermutative",
  ``lpermutative R ==>
    !M p N. lrcc R M p N ==> !pi. lrcc R (ltpm pi M) p (ltpm pi N)``,
  STRIP_TAC THEN HO_MATCH_MP_TAC lrcc_ind THEN SRW_TAC [][] THEN
  METIS_TAC [lrcc_rules, lpermutative_def]);

val beta0_lpermutative = store_thm(
  "beta0_lpermutative",
  ``lpermutative beta0``,
  SRW_TAC [][lpermutative_def, beta0_def] THEN
  SRW_TAC [][ltpm_subst] THEN METIS_TAC []);

val beta1_lpermutative = store_thm(
  "beta1_lpermutative",
  ``lpermutative beta1``,
  SRW_TAC [][lpermutative_def, beta1_def] THEN
  SRW_TAC [][ltpm_subst] THEN METIS_TAC []);

val lrcc_beta01_exclusive = store_thm(
  "lrcc_beta01_exclusive",
  ``!M r N. lrcc beta0 M r N ==> ~lrcc beta1 M r N``,
  HO_MATCH_MP_TAC lrcc_ind THEN REPEAT CONJ_TAC THEN
  SIMP_TAC (srw_ss()) [DECIDE ``(~p ==> ~q) <=> (q ==> p)``] THEN
  SIMP_TAC (srw_ss()) [Once lrcc_cases, SimpL ``(==>)``] THEN1
    SIMP_TAC (srw_ss() ++ DNF_ss) [beta0_def, beta1_def, Once lrcc_cases] THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [lLAMi_eq_thm, lLAM_eq_thm,
                                 lrcc_lpermutative, beta1_lpermutative]);

val lrcc_det = store_thm(
  "lrcc_det",
  ``!M r N. lrcc (beta0 RUNION beta1) M r N ==>
            !N'. lrcc (beta0 RUNION beta1) M r N' = (N' = N)``,
  REPEAT STRIP_TAC THEN SRW_TAC [][EQ_IMP_THM] THEN
  Q.ABBREV_TAC `M0 = strip_label M` THEN
  Q.ABBREV_TAC `N0 = strip_label N` THEN
  `labelled_redn beta M0 r N0` by PROVE_TAC [lrcc_labelled_redn] THEN
  `?f. !y. lrcc (beta0 RUNION beta1) M r y ==>
           (strip_label y = N0) /\
           !n. n_posns n y = BIGUNION (IMAGE f (n_posns n M))` by
     PROVE_TAC [position_maps_exist] THEN
  REWRITE_TAC [labelled_term_component_equality] THEN PROVE_TAC []);

val labelled_redn_det = store_thm(
  "labelled_redn_det",
  ``!M r N. labelled_redn beta M r N ==>
            !L. labelled_redn beta M r L = (L = N)``,
  REPEAT STRIP_TAC THEN SRW_TAC [][EQ_IMP_THM] THEN
  Q.ABBREV_TAC `M' = null_labelling M` THEN
  `M = strip_label M'` by SRW_TAC [][strip_null_labelling, Abbr`M'`] THEN
  Q.ABBREV_TAC `N' = lift_redn M' r N` THEN
  Q.ABBREV_TAC `L' = lift_redn M' r L` THEN
  `lrcc (beta0 RUNION beta1) M' r N' /\ (strip_label N' = N) /\
   lrcc (beta0 RUNION beta1) M' r L' /\ (strip_label L' = L)` by
     PROVE_TAC [lift_redn_def] THEN
  PROVE_TAC [lrcc_det]);

val lemma11_2_12 = store_thm(
  "lemma11_2_12",
  ``!M sigma ps.
       sigma IN development M ps <=>
       (M = first sigma) /\ ps SUBSET M /\
       okpath (labelled_redn beta) sigma /\
       okpath (lrcc beta0) (lift_path (nlabel 0 (first sigma) ps) sigma)``,
  Q_TAC SUFF_TAC
    `(!sigma' : (lterm, redpos list) path.
        (?x sigma ps.
             sigma IN development x ps /\
             (sigma' = lift_path (nlabel 0 (first sigma) ps) sigma)) ==>
        okpath (lrcc beta0) sigma') /\
     (!(sigma : (term, redpos list) path) ps.
        okpath (labelled_redn beta) sigma /\
        okpath (lrcc beta0) (lift_path (nlabel 0 (first sigma) ps) sigma) ==>
        development0 sigma ps)` THEN1
     PROVE_TAC [developments_ok, term_posset_development_def,
                SPECIFICATION] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC okpath_co_ind THEN
    MAP_EVERY Q.X_GEN_TAC [`x`, `r`, `sigma'`] THEN
    CONV_TAC (LAND_CONV (RENAME_VARS_CONV ["M", "sigma", "ps"])) THEN
    SIMP_TAC (srw_ss()) [Once development_cases, SimpL ``(==>)``] THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [lift_path_def] THEN SRW_TAC [][] THENL [
      SRW_TAC [][first_lift_path] THEN
      Q.ABBREV_TAC `M' = nlabel 0 M ps` THEN
      Q.ABBREV_TAC `y = first p` THEN
      Q.ABBREV_TAC `y' = lift_redn M' r y` THEN
      `strip_label M' = M` by PROVE_TAC [strip_label_nlabel] THEN
      `lrcc (beta0 RUNION beta1) M' r y'` by PROVE_TAC [lift_redn_def] THEN
      `r IN redex_posns M`
         by (ASM_SIMP_TAC (srw_ss())[redex_posns_redex_occurrence,
                                     is_redex_occurrence_def] THEN
             PROVE_TAC []) THEN
      `r IN n_posns 0 M'`
        by PROVE_TAC [n_posns_nlabel, IN_INTER] THEN
      PROVE_TAC [pick_a_beta],
      Q.ABBREV_TAC `M' = nlabel 0 M ps` THEN
      Q.ABBREV_TAC `y = first p` THEN
      Q.ABBREV_TAC `y' = lift_redn M' r y` THEN
      Q.EXISTS_TAC `y` THEN Q.EXISTS_TAC `p` THEN
      Q.EXISTS_TAC `residual1 M r y ps` THEN
      ASM_SIMP_TAC (srw_ss()) [residual1_def] THEN
      `strip_label M' = M` by PROVE_TAC [strip_label_nlabel] THEN
      `(y = strip_label y') /\ lrcc (beta0 RUNION beta1) M' r y'`
         by PROVE_TAC [lift_redn_def] THEN
      `!n. ~(n = 0) ==> (n_posns n M' = {})` by PROVE_TAC [n_posns_nlabel] THEN
      `!n. ~(n = 0) ==> (n_posns n y' = {})`
         by PROVE_TAC [lrcc_new_labels] THEN
      ASM_SIMP_TAC (srw_ss()) [nlabel_n_posns]
    ],
    HO_MATCH_MP_TAC development0_coinduction THEN REPEAT GEN_TAC THEN
    Q.ISPEC_THEN `sigma` STRUCT_CASES_TAC path_cases THEN
    SRW_TAC [][lift_path_def, first_lift_path] THEN
    Q.ABBREV_TAC `x' = nlabel 0 x ps` THEN
    Q.ABBREV_TAC `y = first q` THEN
    Q.ABBREV_TAC `y' = lift_redn x' r y` THENL [
      `lrcc (beta0 RUNION beta1) x' r y'` by PROVE_TAC [lrcc_RUNION] THEN
      `?n. r IN n_posns n x'` by PROVE_TAC [lrcc_beta01_exclusive,
                                            pick_a_beta] THEN
      `n = 0` by PROVE_TAC [n_posns_nlabel, NOT_IN_EMPTY] THEN
      PROVE_TAC [IN_INTER, n_posns_nlabel],
      ASM_SIMP_TAC (srw_ss()) [residual1_def] THEN
      Q_TAC SUFF_TAC `nlabel 0 y (n_posns 0 y') = y'` THEN1 PROVE_TAC [] THEN
      `!n. ~(n = 0) ==> (n_posns n x' = {})` by PROVE_TAC [n_posns_nlabel] THEN
      `lrcc (beta0 RUNION beta1) x' r y'` by PROVE_TAC [lrcc_RUNION] THEN
      `!n. ~(n = 0) ==> (n_posns n y' = {})`
         by PROVE_TAC [lrcc_new_labels] THEN
      `strip_label x' = x` by PROVE_TAC [strip_label_nlabel] THEN
      `y = strip_label y'` by PROVE_TAC [lift_redn_def] THEN
      PROVE_TAC [nlabel_n_posns]
    ]
  ]);

val lvar_posns_def = Define`
  lvar_posns t = var_posns (strip_label t)
`;

val (update_weighing_def, update_weighing_swap) =
    define_recursive_term_function`
      (update_weighing (t @@ u:term) =
         \rp w p.
            case rp of
              [] => (let vps = IMAGE TL (bv_posns t)
                     in
                       if ?vp l. vp IN vps /\ (APPEND vp l = p) then
                         w (Rt :: @l. ?vp. vp IN vps /\ (APPEND vp l = p))
                       else w (Lt :: In :: p))
            | Lt::rp0 => if HD p = Lt then
                           update_weighing t rp0 (\p. w(Lt::p)) (TL p)
                         else w p
            | Rt::rp0 => if HD p = Rt then
                           update_weighing u rp0 (\p. w(Rt::p)) (TL p)
                         else w p) /\
      (update_weighing (LAM v t) =
        \rp w p. update_weighing t (TL rp) (\p. w (In::p)) (TL p))
`;

val update_weighing_thm = store_thm(
  "update_weighing_thm",
  ``(update_weighing (t @@ u) [] w =
       let vps = IMAGE TL (bv_posns t)
       in
           \p. if ?vp l. vp IN vps /\ (APPEND vp l = p) then
                 w (Rt :: @l. ?vp. vp IN vps /\ (APPEND vp l = p))
               else
                 w (Lt::In::p)) /\
    (update_weighing (LAM v t) (In::pos0) w =
       let w0 = update_weighing t pos0 (\p. w (In::p))
       in
         \p. w0 (TL p)) /\
    (update_weighing (t @@ u) (Lt::pos0) w =
       let w0 = update_weighing t pos0 (\p. w (Lt::p))
       in
         \p. if HD p = Lt then w0 (TL p) else w p) /\
    (update_weighing (t @@ u) (Rt::pos0) w =
       let w0 = update_weighing u pos0 (\p. w (Rt::p))
       in
         \p. if HD p = Rt then w0 (TL p) else w p)``,
  SRW_TAC [][update_weighing_def]);

val update_weighing_vsubst = store_thm(
  "update_weighing_vsubst",
  ``!t p u v w. p IN redex_posns t ==>
                (update_weighing ([VAR v/u]t) p w = update_weighing t p w)``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`w`, `p`,`t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][redex_posns_thm, SUB_THM] THEN
  SRW_TAC [][update_weighing_thm]);

val beta0_redex_posn = store_thm(
  "beta0_redex_posn",
  ``!x r y. lrcc beta0 x r y ==> r IN redex_posns (strip_label x)``,
  HO_MATCH_MP_TAC lrcc_ind THEN
  SIMP_TAC (srw_ss() ++ DNF_ss)
           [redex_posns_thm, strip_label_thm, beta0_def]);

val nonzero_def = Define`
  nonzero (t:lterm) w = !p. p IN lvar_posns t ==> 0 < w p
`;

val term_weight_def = Define`
  term_weight (t:term) w = SUM_IMAGE w (var_posns t)
`;

val lterm_weight_def = Define`
  lterm_weight (t: lterm) w = SUM_IMAGE w (lvar_posns t)
`;

val delete_non_element =
    #1 (EQ_IMP_RULE (SPEC_ALL DELETE_NON_ELEMENT))

val SUM_IMAGE_IMAGE = store_thm(
  "SUM_IMAGE_IMAGE",
  ``!g. (!x y. (g x = g y) = (x = y)) ==>
        !s. FINITE s ==>
        !f. SUM_IMAGE f (IMAGE g s) = SUM_IMAGE (f o g) s``,
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THEN
  SRW_TAC [][SUM_IMAGE_THM, delete_non_element]);

val inter_images = prove(
  ``!s t f g. (!x y. ~(f x = g y)) ==> (IMAGE f s INTER IMAGE g t = {})``,
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val lterm_weight_thm = store_thm(
  "lterm_weight_thm",
  ``(lterm_weight (VAR s) w = w []) /\
    (lterm_weight (t1 @@ t2) w =
       lterm_weight t1 (\p. w (Lt::p)) +
       lterm_weight t2 (\p. w (Rt::p))) /\
    (lterm_weight (LAM v t) w =
       lterm_weight t (\p. w (In::p))) /\
    (lterm_weight (LAMi n v t1 t2) w =
       lterm_weight t1 (\p. w (Lt::In::p)) +
       lterm_weight t2 (\p. w (Rt :: p)))``,
  SIMP_TAC (srw_ss()) [lterm_weight_def, lvar_posns_def, var_posns_thm,
                       strip_label_thm, SUM_IMAGE_SING,
                       SUM_IMAGE_THM,
                       SUM_IMAGE_IMAGE, inter_images,
                       GSYM IMAGE_COMPOSE,
                       combinTheory.o_DEF, SUM_IMAGE_UNION
                       ]);

val term_weight_thm = store_thm(
  "term_weight_thm",
  ``(!s. term_weight (VAR s) w = w []) /\
    (!t u. term_weight (t @@ u) w = term_weight t (\p. w (Lt::p)) +
                                    term_weight u (\p. w (Rt::p))) /\
    (!v t. term_weight (LAM v t) w = term_weight t (\p. w (In::p)))``,
  SIMP_TAC (srw_ss()) [term_weight_def, var_posns_def,
                       SUM_IMAGE_SING,
                       SUM_IMAGE_THM,
                       SUM_IMAGE_IMAGE, inter_images,
                       GSYM IMAGE_COMPOSE,
                       combinTheory.o_DEF, SUM_IMAGE_UNION
                       ]);

val term_weight_vsubst = Store_Thm(
  "term_weight_vsubst",
  ``!t w u v. term_weight ([VAR v/u] t) w = term_weight t w``,
  SIMP_TAC (srw_ss()) [term_weight_def]);

val term_weight_swap = Store_Thm(
  "term_weight_swap",
  ``term_weight (tpm p t) w = term_weight t w``,
  SIMP_TAC (srw_ss()) [term_weight_def]);

val lterm_term_weight = store_thm(
  "lterm_term_weight",
  ``!t w. lterm_weight t w = term_weight (strip_label t) w``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][lterm_weight_thm, term_weight_thm, strip_label_thm]);

val w_at_exists =
  (CONV_RULE (QUANT_CONV (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) o
   SIMP_RULE (srw_ss()) [term_weight_thm] o
   Q.INST [`lm` |-> `\rt v t p w. if p = [] then term_weight (LAM v t) w
                                  else rt (TL p) (\p. w (In::p))`,
           `ap` |-> `\rt ru t u p w.
                         case p of
                           (Lt::p0) => rt p0 (\p. w (Lt::p))
                         | (Rt::p0) => ru p0 (\p. w (Rt::p))
                         | _ => term_weight (t @@ u) w`,
           `vr` |-> `\s p w. term_weight (VAR s) w`,
           `apm` |-> `discrete_pmact`] o SPEC_ALL o
   INST_TYPE [alpha |-> ``:redpos list -> (redpos list -> num) -> num``])
  tm_recursion_nosideset

val weight_at_def = new_specification(
  "weight_at_def", ["weight_at"],
  prove(
    ``?weight_at.
         (!t w.
             weight_at [] w t = term_weight t w) /\
         (!p w v t.
             weight_at (In::p) w (LAM v t) = weight_at p (\p. w (In::p)) t) /\
         (!p w t u.
              weight_at (Lt::p) w (t @@ u) = weight_at p (\p. w (Lt::p)) t) /\
         (!p w t u.
              weight_at (Rt::p) w (t @@ u) = weight_at p (\p. w (Rt::p)) u) /\
         (!p w t pi. weight_at p w (tpm pi t) = weight_at p w t)``,
    STRIP_ASSUME_TAC w_at_exists THEN
    Q.EXISTS_TAC `\p w t. f t p w` THEN SRW_TAC [][] THEN
    Q.ISPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
    SRW_TAC [][term_weight_thm]));

val weight_at_swap = Save_Thm(
  "weight_at_swap",
  last (CONJUNCTS weight_at_def));

val weight_at_vsubst = Store_Thm(
  "weight_at_vsubst",
  ``!t w v u p. p IN valid_posns t ==>
                (weight_at p w ([VAR v/u] t) = weight_at p w t)``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`p`, `w`, `t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][valid_posns_thm, SUB_THM] THEN
  SRW_TAC [][weight_at_def, term_weight_thm]);

val weight_at_thm = save_thm(
  "weight_at_thm",
  LIST_CONJ (butlast (CONJUNCTS weight_at_def)));

val decreasing_def = Define`
  decreasing t w <=>
    !n p1 p2. p1 IN n_posns n t /\
              p2 IN bv_posns_at (APPEND p1 [Lt]) (strip_label t) ==>
              weight_at (APPEND p1 [Rt]) w (strip_label t) <
              weight_at p2 w (strip_label t)
`;

val n_posns_lam_posns = store_thm(
  "n_posns_lam_posns",
  ``!t n p.  p IN n_posns n t ==>
             (APPEND p [Lt]) IN lam_posns (strip_label t)``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][lam_posns_def, n_posns_def, strip_label_thm] THEN
  SRW_TAC [][] THEN TRY (PROVE_TAC []) THEN
  FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN RES_TAC);

val n_posn_valid_posns = store_thm(
  "n_posn_valid_posns",
  ``!t n p. p IN n_posns n t ==>
            APPEND p [Rt] IN valid_posns (strip_label t) /\
            APPEND p [Lt] IN valid_posns (strip_label t)``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][strip_label_thm, valid_posns_thm, n_posns_def] THEN
  SRW_TAC [][] THEN TRY (PROVE_TAC []) THEN
  FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN RES_TAC);

val decreasing_thm = store_thm(
  "decreasing_thm",
  ``(!s. decreasing (VAR s : lterm) w <=> T) /\
    (!t u. decreasing (t @@ u : lterm) w <=>
                decreasing t (\p. w (Lt::p)) /\
                decreasing u (\p. w (Rt::p))) /\
    (!v t. decreasing (LAM v t : lterm) w = decreasing t (\p. w (In::p))) /\
    (!n v t u. decreasing (LAMi n v t u : lterm) w <=>
                 decreasing t (\p. w (Lt::In::p)) /\
                 decreasing u (\p. w (Rt::p)) /\
                 !p. p IN lv_posns v t ==>
                     lterm_weight u (\p. w (Rt::p)) <
                     weight_at p (\p. w (Lt::In::p)) (strip_label t))``,
  SRW_TAC [][decreasing_def, n_posns_def, strip_label_thm, RIGHT_AND_OVER_OR,
             DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM,
             GSYM LEFT_EXISTS_AND_THM, FORALL_AND_THM] THEN
  SIMP_TAC (srw_ss() ++ SatisfySimps.SATISFY_ss)
           [GSYM AND_IMP_INTRO, bv_posns_at_thm, n_posns_lam_posns,
            GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
            weight_at_thm, n_posn_valid_posns] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    RES_TAC,
    RES_TAC,
    FIRST_X_ASSUM (Q.SPECL_THEN [`n`, `[]`, `Lt::In::p`] MP_TAC) THEN
    SIMP_TAC (srw_ss()) [weight_at_thm, bv_posns_thm, lterm_term_weight] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [lv_posns_def],
    RES_TAC,
    RES_TAC,
    Cases_on `n = n'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [weight_at_thm, bv_posns_thm, lterm_term_weight,
                              lv_posns_def]
  ]);

val nonzero_def = Define`
  nonzero t w = !p. p IN lvar_posns t ==> 0 < w p
`;

val nonzero_thm = store_thm(
  "nonzero_thm",
  ``(!s w. nonzero (VAR s : lterm) w <=> 0 < w []) /\
    (!t u w. nonzero (t @@ u : lterm) w <=>
                nonzero t (\p. w (Lt::p)) /\
                nonzero u (\p. w (Rt::p))) /\
   (!v t w. nonzero (LAM v t : lterm) w <=> nonzero t (\p. w (In::p))) /\
   (!n v t u. nonzero (LAMi n v t u : lterm) w <=>
                nonzero t (\p. w (Lt::In::p)) /\
                nonzero u (\p. w (Rt::p)))``,
  SRW_TAC [][nonzero_def, lvar_posns_def, var_posns_thm, strip_label_thm,
             DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM]);

val weight_at_times_constant = store_thm(
  "weight_at_times_constant",
  ``!t w c p. p IN valid_posns t ==>
              (weight_at p ($* c o w) t = c * weight_at p w t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SIMP_TAC (srw_ss()) [valid_posns_thm, weight_at_thm, term_weight_thm,
                       DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM,
                       FORALL_AND_THM, combinTheory.o_DEF] THEN
  REPEAT STRIP_TAC THENL [
    Q.PAT_X_ASSUM `!w c p. p IN valid_posns t' ==> Q w p c`
                (Q.SPECL_THEN [`\p. w (Rt::p)`, `c`, `[]`] MP_TAC) THEN
    SRW_TAC [][weight_at_thm] THEN
    Q.PAT_X_ASSUM `!w c p. p IN valid_posns t ==> Q w p c`
                (Q.SPECL_THEN [`\p. w (Lt::p)`, `c`, `[]`] MP_TAC) THEN
    SRW_TAC [][weight_at_thm, arithmeticTheory.LEFT_ADD_DISTRIB],
    POP_ASSUM (Q.SPECL_THEN [`\p. w (In::p)`, `c`, `[]`] MP_TAC) THEN
    SRW_TAC [][weight_at_thm]
  ]);

val decreasing_times_constant = store_thm(
  "decreasing_times_constant",
  ``!t w. decreasing t w ==> !c. 0 < c ==> decreasing t ($* c o w)``,
  SRW_TAC [][decreasing_def] THEN
  `APPEND p1 [Rt] IN valid_posns (strip_label t)`
     by PROVE_TAC [n_posn_valid_posns] THEN
  `APPEND p1 [Lt] IN lam_posns (strip_label t)`
     by PROVE_TAC [n_posns_lam_posns] THEN
  `p2 IN valid_posns (strip_label t)`
     by PROVE_TAC [bv_posns_at_SUBSET_var_posns,
                   var_posns_SUBSET_valid_posns] THEN RES_TAC THEN
  SRW_TAC [numSimps.SUC_FILTER_ss][weight_at_times_constant,
                                   arithmeticTheory.LESS_MULT_MONO]);

val weight_at_var_posn = store_thm(
  "weight_at_var_posn",
  ``!t p w. p IN var_posns t ==> (weight_at p w t = w p)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][var_posns_thm, weight_at_vsubst,
             var_posns_SUBSET_valid_posns] THEN
  SRW_TAC [][var_posns_SUBSET_valid_posns, weight_at_thm, term_weight_thm]);

val decreasing_weights_exist = store_thm(
  "decreasing_weights_exist",
  ``!t. ?w. nonzero t w /\ decreasing t w``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SIMP_TAC (srw_ss())[decreasing_thm, nonzero_thm] THEN REPEAT CONJ_TAC THENL [
    Q.EXISTS_TAC `\p. 1` THEN SRW_TAC [][],
    REPEAT STRIP_TAC THEN
    Q.EXISTS_TAC `\p. if HD p = Lt then w (TL p) else w' (TL p)` THEN
    SRW_TAC [ETA_ss][],
    REPEAT STRIP_TAC THEN
    Q.EXISTS_TAC `w o TL` THEN
    SRW_TAC [ETA_ss][combinTheory.o_THM],
    Q_TAC SUFF_TAC
      `∀v t1 t2.
          (∃w. nonzero t1 w ∧ decreasing t1 w) ∧
          (∃w. nonzero t2 w ∧ decreasing t2 w) ==>
          ∃w.
             nonzero t1 (λp. w (Lt::In::p)) ∧ nonzero t2 (λp. w (Rt::p)) ∧
             decreasing t1 (λp. w (Lt::In::p)) ∧
             decreasing t2 (λp. w (Rt::p)) ∧
             ∀p. p ∈ lv_posns v t1 ==>
                 lterm_weight t2 (λp. w (Rt::p)) <
                    weight_at p (λp. w (Lt::In::p)) (strip_label t1)`
      THEN1 METIS_TAC [] THEN
    MAP_EVERY Q.X_GEN_TAC [`v`, `t1`,`t2`] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `w1` STRIP_ASSUME_TAC)
                                (Q.X_CHOOSE_THEN `w2` STRIP_ASSUME_TAC)) THEN
    Q.EXISTS_TAC `\p. if HD p = Lt then
                        (lterm_weight t2 w2 + 1) * w1 (TL (TL p))
                      else w2 (TL p)` THEN
    SRW_TAC [ETA_ss][nonzero_def] THENL [
      `0 < w1 p` by PROVE_TAC [nonzero_def] THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [nonzero_def, arithmeticTheory.RIGHT_ADD_DISTRIB],
      PROVE_TAC [nonzero_def],
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [decreasing_times_constant, GSYM combinTheory.o_DEF],
      `p IN valid_posns (strip_label t1)`
         by PROVE_TAC [lv_posns_def, v_posns_SUBSET_var_posns,
                       var_posns_SUBSET_valid_posns] THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [weight_at_times_constant, GSYM combinTheory.o_DEF] THEN
      Q_TAC SUFF_TAC `(!c n. 0 < c ==> n < (n + 1) * c) /\
                      0 < weight_at p w1 (strip_label t1)`
            THEN1 PROVE_TAC [] THEN
      `p IN var_posns (strip_label t1)`
         by PROVE_TAC [lv_posns_def, v_posns_SUBSET_var_posns] THEN
      ASM_SIMP_TAC (srw_ss()) [weight_at_var_posn] THEN
      `0 < w1 p` by PROVE_TAC [nonzero_def, lvar_posns_def] THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Induct THEN SRW_TAC [ARITH_ss][arithmeticTheory.MULT_CLAUSES]
    ]
  ]);

val weighted_reduction_def = Define`
  weighted_reduction (M', w0) r (N', w) <=>
    lrcc beta0 M' r N' /\ (w = update_weighing (strip_label M') r w0)
`;


val op on = BasicProvers.on;
infix 8 on;

val lrcc_redex_posn = store_thm(
  "lrcc_redex_posn",
  ``!M r N. lrcc beta0 M r N ==> r IN redex_posns (strip_label M)``,
  HO_MATCH_MP_TAC lrcc_ind THEN
  SRW_TAC [][redex_posns_thm, strip_label_thm, beta0_def] THEN
  SRW_TAC [][redex_posns_thm, strip_label_thm]);

val labelled_redn_beta_redex_posn = store_thm(
  "labelled_redn_beta_redex_posn",
  ``!M r N. labelled_redn beta M r N ==> r IN redex_posns M``,
  HO_MATCH_MP_TAC labelled_redn_ind THEN
  SRW_TAC [][redex_posns_thm, beta_def] THEN
  SRW_TAC [][redex_posns_thm]);

val weighted_reduction_preserves_nonzero_weighing = store_thm(
  "weighted_reduction_preserves_nonzero_weighing",
  ``!M' w0 r N' w.
       weighted_reduction (M', w0) r (N', w) /\
       nonzero M' w0 ==> nonzero N' w``,
  Q_TAC SUFF_TAC
    `!M' r N'.
        lrcc beta0 M' r N' ==>
        !w. nonzero M' w ==>
            nonzero N' (update_weighing (strip_label M') r w)` THEN1
    SRW_TAC [][weighted_reduction_def] THEN
  HO_MATCH_MP_TAC strong_lrcc_ind THEN
  SIMP_TAC (srw_ss())[update_weighing_thm, strip_label_thm] THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [] [beta0_def, nonzero_def, lvar_posns_def, var_posns_thm,
                strip_label_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss)
                  [strip_label_thm, var_posns_thm, var_posns_subst,
                   bv_posns_thm, strip_label_subst, update_weighing_thm]
    THENL [
      `!vp l. ~(vp IN v_posns v (strip_label t) /\ (APPEND vp l = p))`
          by (REPEAT STRIP_TAC THEN
              `vp IN var_posns (strip_label t)`
                 by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
              `l = []` by PROVE_TAC [no_var_posns_in_var_posn_prefix] THEN
              FULL_SIMP_TAC (srw_ss()) []) THEN
      SRW_TAC [][],
      (fn th => REWRITE_TAC [th] THEN STRIP_ASSUME_TAC th) on
      (`?vp l. vp IN v_posns v (strip_label t) /\
               (APPEND vp l = APPEND p1 p2)`, PROVE_TAC []) THEN
      SELECT_ELIM_TAC THEN CONJ_TAC THEN1 PROVE_TAC [] THEN
      GEN_TAC THEN
      DISCH_THEN (Q.X_CHOOSE_THEN `vp1` STRIP_ASSUME_TAC) THEN
      `vp1 IN var_posns (strip_label t) /\ p1 IN var_posns (strip_label t)`
         by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
      `vp1 = p1` by
         (`APPEND p1 p2 = APPEND vp1 x` by PROVE_TAC [] THEN
          POP_ASSUM MP_TAC THEN
          SIMP_TAC (srw_ss() ++ DNF_ss) [APPEND_CASES] THEN
          SRW_TAC [][] THEN PROVE_TAC [no_var_posns_in_var_posn_prefix]) THEN
      FULL_SIMP_TAC (srw_ss()) []
    ],
    SIMP_TAC (srw_ss() ++ ETA_ss) [nonzero_thm, strip_label_thm],
    SIMP_TAC (srw_ss() ++ ETA_ss) [nonzero_thm, strip_label_thm],
    SRW_TAC [][nonzero_thm, strip_label_thm] THEN
    IMP_RES_TAC lrcc_redex_posn THEN
    SRW_TAC [ETA_ss][update_weighing_vsubst],
    SIMP_TAC (srw_ss() ++ ETA_ss) [nonzero_thm, strip_label_thm],
    SRW_TAC [][nonzero_thm, strip_label_thm] THEN
    IMP_RES_TAC lrcc_redex_posn THEN
    SRW_TAC [ETA_ss][]
  ]);

val wterm_ordering_def = Define`
  wterm_ordering (N, w) (M, w0) <=> lterm_weight N w < lterm_weight M w0
`;

val WF_wterm_ordering = store_thm(
  "WF_wterm_ordering",
  ``WF wterm_ordering``,
  `wterm_ordering = measure (\p. lterm_weight (FST p) (SND p))`
     by SIMP_TAC (srw_ss()) [prim_recTheory.measure_def, FUN_EQ_THM,
                             pairTheory.FORALL_PROD, wterm_ordering_def,
                             relationTheory.inv_image_def] THEN
  SRW_TAC [][prim_recTheory.WF_measure]);

val weighing_at_def = Define`weighing_at l w = w o APPEND l`;

val CARD_IMAGE = prove(
  ``!f s. (!x y. (f x = f y) = (x = y)) /\ FINITE s ==>
          (CARD (IMAGE f s) = CARD s)``,
  Q_TAC SUFF_TAC
        `!f. (!x y. (f x = f y) = (x = y)) ==>
             !s. FINITE s ==> (CARD (IMAGE f s) = CARD s)`
             THEN1 PROVE_TAC [] THEN
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][]);

val CARD_UNION_BETTER = prove(
  ``!s. FINITE s ==>
        !t. FINITE t ==>
            (CARD (s UNION t) = CARD s + CARD t - CARD (s INTER t))``,
  REPEAT STRIP_TAC THEN
  `CARD (s INTER t) <= CARD s`
     by PROVE_TAC [CARD_INTER_LESS_EQ] THEN
  `CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t`
     by PROVE_TAC [CARD_UNION] THEN
  DECIDE_TAC);

val v_posns_LE_term_weight = store_thm(
  "v_posns_LE_term_weight",
  ``!t v w. SUM_IMAGE w (v_posns v t) <= term_weight t w``,
  SIMP_TAC (srw_ss()) [term_weight_def] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_IMAGE_SUBSET_LE THEN
  PROVE_TAC [SUBSET_DEF, v_posns_SUBSET_var_posns,
             var_posns_FINITE]);

val size_vsubst = prove(
  ``!M:term. size ([VAR v/u] M) = size M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val old_induction = prove(
  ``!P. (!x. P (VAR x)) /\
        (!t u. P t /\ P u ==> P (t @@ u)) /\
        (!x u. (!y'. P ([VAR y'/x] u)) ==> P (LAM x u)) ==>
        !u:term. P u``,
  REPEAT STRIP_TAC THEN
  completeInduct_on `size u` THEN GEN_TAC THEN
  Q.SPEC_THEN `u` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][] THENL [
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
    SRW_TAC [numSimps.ARITH_ss][],
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
    SRW_TAC [numSimps.ARITH_ss][size_vsubst]
  ]);


val weight_at_subst = store_thm(
  "weight_at_subst",
  ``!t u v p w.
       p IN valid_posns ([u/v] t) ==>
       (weight_at p (update_weighing ((LAM v t) @@ u) [] w) ([u/v] t) =
        if ?vp l. vp IN v_posns v t /\ (APPEND vp l = p) then
          weight_at (@l. ?vp. vp IN v_posns v t /\ (APPEND vp l = p))
                    (\p. w (Rt::p))
                    u
        else
          let vps = { p' | (?p''. p' = APPEND p p'') /\
                           p' IN v_posns v t }
          in
            weight_at p (\p. w (Lt::In::p)) t -
            SUM_IMAGE (\p. w (Lt::In::p)) vps +
            CARD vps * term_weight u (\p. w (Rt::p)))``,

  HO_MATCH_MP_TAC old_induction THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [ARITH_ss]
            [v_posns_thm, term_weight_thm, valid_posns_thm,
             SUB_THM, update_weighing_def, bv_posns_thm,
             weight_at_thm, SUM_IMAGE_THM] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][v_posns_thm, valid_posns_thm, SUB_THM] THENL [
      SIMP_TAC (srw_ss() ++ DNF_ss) [weight_at_thm, term_weight_thm] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`u`,`v`,`[]`] MP_TAC) THEN
      SRW_TAC [][weight_at_thm, GSPEC_OR] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`u`,`v`,`[]`] MP_TAC) THEN
      SRW_TAC [][weight_at_thm, GSPEC_OR] THEN
      FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [update_weighing_def, bv_posns_thm,
                                          v_posns_thm] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `\q. if HD q = Lt then
                                        w (HD q :: HD (TL q) :: Lt ::
                                           TL (TL q))
                                      else w q`
                     (ASSUME_TAC o SIMP_RULE (srw_ss()) [])) THEN
      POP_ASSUM (fn th =>
                    REWRITE_TAC [CONV_RULE
                                   (ONCE_DEPTH_CONV (SWAP_VARS_CONV)) th]) THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `\q. if HD q = Lt then
                                        w (HD q :: HD (TL q) :: Rt ::
                                           TL (TL q))
                                      else w q`
                     (ASSUME_TAC o SIMP_RULE (srw_ss()) [])) THEN
      POP_ASSUM (fn th =>
                    REWRITE_TAC [CONV_RULE
                                   (ONCE_DEPTH_CONV (SWAP_VARS_CONV)) th]) THEN
      SRW_TAC [][NIL_IN_v_posns] THENL [
        `{[Lt]} UNION {[Rt]} = {[Lt]; [Rt]}` by SRW_TAC [][EXTENSION] THEN
        SRW_TAC [ARITH_ss][v_posns_thm, term_weight_thm, GSPEC_EQ,
                           SUM_IMAGE_THM,
                           SUM_IMAGE_DELETE],
        `{p' | ?x. (p' = Rt::x) /\ x IN v_posns v t'} =
         IMAGE (CONS Rt) (v_posns v t')` by SRW_TAC [][EXTENSION] THEN
        SRW_TAC [][v_posns_thm, term_weight_thm, GSPEC_EQ,
                   GSYM INSERT_SING_UNION,
                   SUM_IMAGE_THM, delete_non_element,
                   arithmeticTheory.MULT_CLAUSES, SUM_IMAGE_IMAGE,
                   combinTheory.o_DEF, CARD_IMAGE] THEN
        DECIDE_TAC,
        `{p' | ?x. (p' = Lt::x) /\ x IN v_posns v t} =
         IMAGE (CONS Lt) (v_posns v t)` by SRW_TAC [][EXTENSION] THEN
        SRW_TAC [] [v_posns_thm, term_weight_thm, GSPEC_EQ,
                    SUM_IMAGE_IMAGE,
                    GSYM (ONCE_REWRITE_RULE [UNION_COMM]
                                            INSERT_SING_UNION),
                    SUM_IMAGE_THM, delete_non_element,
                    combinTheory.o_DEF, arithmeticTheory.MULT_CLAUSES,
                    CARD_IMAGE] THEN DECIDE_TAC,
        `{p' | ?x. (p' = Rt::x) /\ x IN v_posns v t'} =
         IMAGE (CONS Rt) (v_posns v t')` by SRW_TAC [][EXTENSION] THEN
        `{p' | ?x. (p' = Lt::x) /\ x IN v_posns v t} =
         IMAGE (CONS Lt) (v_posns v t)` by SRW_TAC [][EXTENSION] THEN
        SRW_TAC [] [v_posns_thm, term_weight_thm, GSPEC_EQ,
                    SUM_IMAGE_IMAGE,
                    SUM_IMAGE_THM, delete_non_element,
                    combinTheory.o_DEF, arithmeticTheory.MULT_CLAUSES,
                    CARD_IMAGE, SUM_IMAGE_UNION] THEN
        `!x y. IMAGE (CONS Lt) x INTER IMAGE (CONS Rt) y = {}` by
            (SRW_TAC [][EXTENSION] THEN
             SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
             FULL_SIMP_TAC (srw_ss()) []) THEN
        SRW_TAC [][SUM_IMAGE_THM, CARD_UNION_BETTER,
                   arithmeticTheory.RIGHT_ADD_DISTRIB, CARD_IMAGE] THEN
        Q.SPECL_THEN [`t'`, `v`, `\p. w(Lt::In::Rt::p)`] MP_TAC
                     v_posns_LE_term_weight THEN
        Q.SPECL_THEN [`t`, `v`, `\p. w(Lt::In::Lt::p)`] MP_TAC
                     v_posns_LE_term_weight THEN
        numLib.ARITH_TAC
      ],

      SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
      `!p p1 p2 r. ~((p = Lt::p1) /\ (p = Rt::p2) /\ r)`
          by SIMP_TAC (srw_ss()) [] THEN ASM_REWRITE_TAC [] THEN
      POP_ASSUM (K ALL_TAC) THEN RES_THEN MP_TAC THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl))) THEN
      ASM_SIMP_TAC (srw_ss()) [weight_at_thm] THEN
      CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
      DISCH_THEN (Q.SPEC_THEN `\p. if HD p = Lt then
                                     w (Lt::In::Lt::TL (TL p))
                                   else w p` MP_TAC) THEN
      SIMP_TAC (srw_ss()) [] THEN
      Cases_on `?l vp. vp IN v_posns v t /\ (APPEND vp l = x)` THENL [
        ASM_SIMP_TAC (srw_ss()) [] THEN
        DISCH_THEN (fn th => REWRITE_TAC [SYM th]) THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm, v_posns_thm] THEN
        CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
        REWRITE_TAC [],
        ASM_SIMP_TAC (srw_ss()) [] THEN
        `{p | ?a b. (p = Lt::APPEND x a) /\ (p = Lt::b) /\ b IN v_posns v t} =
         IMAGE (CONS Lt) {p | ?a. (p = APPEND x a) /\ p IN v_posns v t}`
           by SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
        `FINITE {p | ?a. (p = APPEND x a) /\ p IN v_posns v t}`
           by (MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                      (Q.SPEC `t` var_posns_FINITE)) THEN
               SRW_TAC [][SUBSET_DEF] THEN
               PROVE_TAC [v_posns_SUBSET_var_posns]) THEN
        `x IN valid_posns t`
            by (FULL_SIMP_TAC (srw_ss()) [valid_posns_subst] THEN
                PROVE_TAC []) THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [CARD_IMAGE, SUM_IMAGE_IMAGE,
                                           combinTheory.o_DEF,
                                           weight_at_thm] THEN
        DISCH_THEN (fn th => REWRITE_TAC [SYM th]) THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm, v_posns_thm] THEN
        CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
        REWRITE_TAC []
      ],

      SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
      `!p p1 p2 r. ~((p = Rt::p1) /\ (p = Lt::p2) /\ r)`
          by SIMP_TAC (srw_ss()) [] THEN ASM_REWRITE_TAC [] THEN
      POP_ASSUM (K ALL_TAC) THEN RES_THEN MP_TAC THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl))) THEN
      ASM_SIMP_TAC (srw_ss()) [weight_at_thm] THEN
      CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
      DISCH_THEN (Q.SPEC_THEN `\p. if HD p = Lt then
                                     w (Lt::In::Rt::TL (TL p))
                                   else w p` MP_TAC) THEN
      SIMP_TAC (srw_ss()) [] THEN
      Cases_on `?l vp. vp IN v_posns v t' /\ (APPEND vp l = x)` THENL [
        ASM_SIMP_TAC (srw_ss()) [] THEN
        DISCH_THEN (fn th => REWRITE_TAC [SYM th]) THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm, v_posns_thm] THEN
        CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
        REWRITE_TAC [],

        ASM_SIMP_TAC (srw_ss()) [] THEN
        `{p | ?a b. (p = Rt::APPEND x a) /\ (p = Rt::b) /\ b IN v_posns v t'} =
         IMAGE (CONS Rt) {p | ?a. (p = APPEND x a) /\ p IN v_posns v t'}`
           by SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
        `FINITE {p | ?a. (p = APPEND x a) /\ p IN v_posns v t'}`
           by (MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                      (Q.SPEC `t'` var_posns_FINITE)) THEN
               SRW_TAC [][SUBSET_DEF] THEN
               PROVE_TAC [v_posns_SUBSET_var_posns]) THEN
        `x IN valid_posns t'`
            by (FULL_SIMP_TAC (srw_ss()) [valid_posns_subst] THEN
                PROVE_TAC []) THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [CARD_IMAGE, SUM_IMAGE_IMAGE,
                                           combinTheory.o_DEF,
                                           weight_at_thm] THEN
        DISCH_THEN (fn th => REWRITE_TAC [SYM th]) THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm, v_posns_thm] THEN
        CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
        REWRITE_TAC []
      ]
    ],

    (* abstraction case *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    Q_TAC (NEW_TAC "z") `{x;v} UNION FV t UNION FV u` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [SUB_THM, v_posns_thm] THEN
    SIMP_TAC (srw_ss()) [valid_posns_thm] THEN STRIP_TAC THENL [
      ASM_SIMP_TAC (srw_ss()) [term_weight_thm, weight_at_thm] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`z`,`u`,`v`,`[]`] MP_TAC) THEN
      ASM_SIMP_TAC (srw_ss()) [weight_at_thm, term_weight_thm] THEN
      DISCH_THEN (Q.SPEC_THEN `\p. if HD p = Lt then
                                     w (Lt::In::In::(TL (TL p)))
                                   else w p` MP_TAC) THEN
      Cases_on `[] IN v_posns v ([VAR z/x] t)` THENL [
        ASM_SIMP_TAC (srw_ss()) [] THEN
        `~(x = v) /\ (t = VAR v)`
           by (FULL_SIMP_TAC (srw_ss()) [v_posns_vsubst] THEN
               POP_ASSUM MP_TAC THEN SRW_TAC [][NIL_IN_v_posns]) THEN
        ASM_SIMP_TAC (srw_ss()) [SUB_THM, term_weight_thm] THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm, v_posns_thm,
                      GSPEC_EQ, SUM_IMAGE_SING] THEN
        DECIDE_TAC,
        ASM_SIMP_TAC (srw_ss()) [] THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_thm, bv_posns_thm, v_posns_thm] THEN
        CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
        DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
        Cases_on `v = x` THEN
        ASM_SIMP_TAC (srw_ss()) [SUM_IMAGE_IMAGE, CARD_IMAGE,
                                 v_posns_FINITE, combinTheory.o_DEF,
                                 v_posns_vsubst,
                                 SUM_IMAGE_THM]
      ],

      Cases_on `v = x` THENL [
        SRW_TAC [][update_weighing_thm, SUB_TWICE_ONE_VAR, SUB_THM,
                   bv_posns_thm, v_posns_thm, v_posns_vsubst,
                   SUM_IMAGE_THM],
        ALL_TAC
      ] THEN
      ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [weight_at_thm] THEN GEN_TAC THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`z`,`u`,`v`,`x'`] MP_TAC) THEN
      SIMP_TAC (srw_ss() ++ DNF_ss) [update_weighing_def, bv_posns_thm] THEN
      ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [v_posns_thm, v_posns_vsubst] THEN
      DISCH_THEN (Q.SPEC_THEN `\p. if HD p = Lt then
                                     w (Lt::In::In::(TL (TL p)))
                                   else w p` MP_TAC) THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SWAP_VARS_CONV)) THEN
      DISCH_THEN (fn th => SIMP_TAC (srw_ss()) [th]) THEN
      COND_CASES_TAC THEN SRW_TAC [][] THEN
      `{p | ?a b. (p = In::APPEND x' a) /\ (p = In::b) /\
                   b IN v_posns v t} =
       IMAGE (CONS In) { p | ?a. (p = APPEND x' a) /\ (p IN v_posns v t)}`
            by SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      `FINITE {p | ?a. (p = APPEND x' a) /\ (p IN v_posns v t)}`
          by (MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                     (Q.SPEC `t` var_posns_FINITE)) THEN
              ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                           [SUBSET_DEF] THEN
              PROVE_TAC [v_posns_SUBSET_var_posns]) THEN
      ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [SUM_IMAGE_IMAGE, CARD_IMAGE,
                                           combinTheory.o_DEF]
    ]
  ]);

val list_append_lemma = prove( (* thanks be to KG! *)
  ``!m n. ((m = APPEND m n) = (n = [])) /\
          ((APPEND m n = m) = (n = [])) /\
          ((m = APPEND n m) = (n = [])) /\
          ((APPEND n m = m) = (n = []))``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o Q.AP_TERM `LENGTH`) THEN
  SRW_TAC [][DECIDE ``((x + y = x) = (y = 0)) /\ ((y + x = x) = (y = 0)) /\
                      ((x = x + y) = (y = 0)) /\ ((x = y + x) = (y = 0))``]
  THEN PROVE_TAC [listTheory.LENGTH_NIL]);

val _ = augment_srw_ss [rewrites [list_append_lemma]]

val lv_posns_n_posns = store_thm(
  "lv_posns_n_posns",
  ``!t p n v. ~(p IN n_posns n t /\ p IN lv_posns v t)``,
  REPEAT STRIP_TAC THEN
  `APPEND p [Lt] IN lam_posns (strip_label t)`
     by PROVE_TAC [n_posns_lam_posns] THEN
  `APPEND p [Lt] IN valid_posns (strip_label t)`
     by PROVE_TAC [lam_posns_SUBSET_valid_posns] THEN
  `p IN var_posns (strip_label t)`
     by PROVE_TAC [v_posns_SUBSET_var_posns, lv_posns_def] THEN
  PROVE_TAC [cant_be_deeper_than_var_posns, listTheory.NOT_NIL_CONS]);

val CARD_SUM_IMAGE_LE = prove(
  ``!s. FINITE s /\
        (!e. e IN s ==> c < f e) ==>
        CARD s * c <= SUM_IMAGE f s``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [DNF_ss] [arithmeticTheory.MULT_CLAUSES,
                    SUM_IMAGE_THM, delete_non_element] THEN
  FULL_SIMP_TAC (srw_ss() ++ARITH_ss)[]);

val CARD_SUM_IMAGE_LT = prove(
  ``!s. FINITE s /\ ~(s = {}) /\ (!e. e IN s ==> c < f e) ==>
        CARD s * c < SUM_IMAGE f s``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [DNF_ss] [arithmeticTheory.MULT_CLAUSES,
                    SUM_IMAGE_THM, delete_non_element] THEN
  Cases_on `s = {}` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)[]);


val weight_at_SUM_IMAGE = store_thm(
  "weight_at_SUM_IMAGE",
  ``!t p w.
       p IN valid_posns t ==>
       (weight_at p w t = SUM_IMAGE w ({ p' | (?p''. APPEND p p'' = p') /\
                                              p' IN var_posns t}))``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][valid_posns_thm, var_posns_thm, GSPEC_EQ,
             SUM_IMAGE_THM, weight_at_thm,
             term_weight_thm, arithmeticTheory.ADD_CLAUSES]
  THENL [
    SRW_TAC [][weight_at_thm, term_weight_def, var_posns_thm] THEN
    REPEAT AP_TERM_TAC THEN SRW_TAC [][EXTENSION],
    SRW_TAC [CONJ_ss, DNF_ss][weight_at_thm] THEN
    `(\p. w (Lt::p)) = w o CONS Lt` by SRW_TAC [][FUN_EQ_THM] THEN
    `FINITE {p' | ?p''. (APPEND x p'' = p') /\ p' IN var_posns t}`
       by (MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                  (Q.SPEC `t` var_posns_FINITE)) THEN
           SRW_TAC [][SUBSET_DEF]) THEN
    ASM_SIMP_TAC (srw_ss()) [GSYM SUM_IMAGE_IMAGE] THEN
    REPEAT AP_TERM_TAC THEN SRW_TAC [DNF_ss][EXTENSION],
    SRW_TAC [CONJ_ss, DNF_ss][weight_at_thm] THEN
    `(\p. w (Rt::p)) = w o CONS Rt` by SRW_TAC [][FUN_EQ_THM] THEN
    `FINITE {p' | ?p''. (APPEND x p'' = p') /\ p' IN var_posns t'}`
       by (MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                  (Q.SPEC `t'` var_posns_FINITE)) THEN
           SRW_TAC [][SUBSET_DEF]) THEN
    ASM_SIMP_TAC (srw_ss()) [GSYM SUM_IMAGE_IMAGE] THEN
    REPEAT AP_TERM_TAC THEN SRW_TAC [DNF_ss][EXTENSION],
    SRW_TAC [][weight_at_thm, term_weight_def, var_posns_thm] THEN
    REPEAT AP_TERM_TAC THEN SRW_TAC [DNF_ss][EXTENSION],
    SRW_TAC [CONJ_ss, DNF_ss][weight_at_thm] THEN
    `(\p. w (In::p)) = w o CONS In` by SRW_TAC [][FUN_EQ_THM] THEN
    `FINITE {p' | ?p''. (APPEND x p'' = p') /\ p' IN var_posns t}`
       by (MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                  (Q.SPEC `t` var_posns_FINITE)) THEN
           SRW_TAC [][SUBSET_DEF]) THEN
    ASM_SIMP_TAC (srw_ss()) [GSYM SUM_IMAGE_IMAGE] THEN
    REPEAT AP_TERM_TAC THEN SRW_TAC [DNF_ss][EXTENSION]
  ]);

val FV_weights_update_weighing = store_thm(
  "FV_weights_update_weighing",
  ``!x r y.
       labelled_redn beta x r y ==>
       !p v. p IN v_posns v y ==>
             ?p'. p' IN v_posns v x /\
                  (!wf. weight_at p (update_weighing x r wf) y =
                        weight_at p' wf x)``,
  HO_MATCH_MP_TAC strong_labelled_redn_ind THEN
  SIMP_TAC (srw_ss())[update_weighing_def, v_posns_thm, beta_def] THEN
  REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THENL [
    `p IN var_posns ([arg/x'] body) /\
     p IN valid_posns ([arg/x'] body)`
       by PROVE_TAC [v_posns_SUBSET_var_posns,
                     var_posns_SUBSET_valid_posns] THEN
    FULL_SIMP_TAC (srw_ss()) [v_posns_subst, v_posns_thm, rator_thm,
                              bv_posns_thm] THEN
    Cases_on `v = x'` THENL [
      FULL_SIMP_TAC (srw_ss()) [v_posns_thm] THEN
      Q.EXISTS_TAC `Rt::p2` THEN
      `p2 IN var_posns arg /\ p2 IN valid_posns arg`
          by PROVE_TAC [v_posns_SUBSET_var_posns,
                        var_posns_SUBSET_valid_posns] THEN
      REPEAT VAR_EQ_TAC THEN
      ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [weight_at_thm,
                                         weight_at_var_posn] THEN
      `!vp l.
          vp IN v_posns v body /\ (APPEND vp l = APPEND p1 p2) <=>
          (vp = p1) /\ (l = p2)`
         by (ASM_SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN STRIP_TAC THEN
             PROVE_TAC [APPEND_var_posns, v_posns_SUBSET_var_posns]) THEN
      ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [update_weighing_thm, bv_posns_thm],
      FULL_SIMP_TAC (srw_ss()) [v_posns_thm] THENL [
        Q.EXISTS_TAC `Lt::In::p` THEN
        `p IN var_posns body /\ p IN valid_posns body`
           by PROVE_TAC [v_posns_SUBSET_var_posns,
                         var_posns_SUBSET_valid_posns] THEN
        ASM_SIMP_TAC (srw_ss()) [weight_at_thm, valid_posns_thm,
                                 weight_at_var_posn] THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm] THEN
        GEN_TAC THEN COND_CASES_TAC THENL [
          POP_ASSUM STRIP_ASSUME_TAC THEN
          `l = []` by PROVE_TAC [v_posns_SUBSET_var_posns,
                                 no_var_posns_in_var_posn_prefix] THEN
          FULL_SIMP_TAC (srw_ss()) [] THEN
          PROVE_TAC [v_posns_injective],
          REWRITE_TAC []
        ],
        Q.EXISTS_TAC `Rt::p2` THEN
        `p2 IN var_posns arg /\ p2 IN valid_posns arg`
           by PROVE_TAC [v_posns_SUBSET_var_posns,
                         var_posns_SUBSET_valid_posns] THEN
        ASM_SIMP_TAC (srw_ss()) [weight_at_thm, valid_posns_thm] THEN
        REPEAT VAR_EQ_TAC THEN
        ASM_SIMP_TAC (srw_ss()) [weight_at_var_posn] THEN
        ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                     [update_weighing_def, bv_posns_thm] THEN
        `!vp l. vp IN v_posns x' body /\ (APPEND vp l = APPEND p1 p2) <=>
                (vp = p1) /\ (l = p2)`
            by (ASM_SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN
                REPEAT GEN_TAC THEN STRIP_TAC THEN
                PROVE_TAC [APPEND_var_posns, v_posns_SUBSET_var_posns]) THEN
        ASM_SIMP_TAC (srw_ss()) []
      ]
    ],

    RES_THEN (Q.X_CHOOSE_THEN `p1` STRIP_ASSUME_TAC) THEN
    `x' IN valid_posns y /\ p1 IN valid_posns x`
       by PROVE_TAC [v_posns_SUBSET_var_posns,
                     var_posns_SUBSET_valid_posns] THEN
    Q.EXISTS_TAC `Lt::p1` THEN
    ASM_SIMP_TAC (srw_ss() ++ ETA_ss) [weight_at_thm],

    Q.EXISTS_TAC `Rt::x'` THEN
    `x' IN valid_posns z` by PROVE_TAC [v_posns_SUBSET_var_posns,
                                        var_posns_SUBSET_valid_posns] THEN
    ASM_SIMP_TAC (srw_ss())[weight_at_thm],

    Q.EXISTS_TAC `Lt::x'` THEN
    `x' IN valid_posns z` by PROVE_TAC [v_posns_SUBSET_var_posns,
                                        var_posns_SUBSET_valid_posns] THEN
    ASM_SIMP_TAC (srw_ss())[weight_at_thm],

    RES_THEN (Q.X_CHOOSE_THEN `p1` STRIP_ASSUME_TAC) THEN
    `x' IN valid_posns y /\ p1 IN valid_posns x`
       by PROVE_TAC [v_posns_SUBSET_var_posns,
                     var_posns_SUBSET_valid_posns] THEN
    Q.EXISTS_TAC `Rt::p1` THEN
    ASM_SIMP_TAC (srw_ss() ++ ETA_ss) [weight_at_thm],

    `r IN redex_posns x` by PROVE_TAC [labelled_redn_beta_redex_posn] THEN
    ASM_SIMP_TAC (srw_ss()) [update_weighing_vsubst] THEN
    Cases_on `v = v'` THEN FULL_SIMP_TAC (srw_ss()) [v_posns_thm] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
    RES_THEN (Q.X_CHOOSE_THEN `p1` STRIP_ASSUME_TAC) THEN
    `x' IN valid_posns y /\ p1 IN valid_posns x`
       by PROVE_TAC [v_posns_SUBSET_var_posns,
                     var_posns_SUBSET_valid_posns] THEN
    Q.EXISTS_TAC `p1` THEN
    ASM_SIMP_TAC (srw_ss() ++ ETA_ss) [weight_at_thm]
  ]);

val nonzero_term_weight = store_thm(
  "nonzero_term_weight",
  ``!t w. nonzero t w ==> 0 < lterm_weight t w``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][nonzero_thm, lterm_weight_thm] THEN
  RES_TAC THEN SRW_TAC [ARITH_ss][]);

val weighted_reduction_reduces_ordering = store_thm(
  "weighted_reduction_reduces_ordering",
  ``!M w0 N w r.  weighted_reduction (M, w0) r (N, w) /\
                  decreasing M w0 /\ nonzero M w0 ==>
                  decreasing N w /\ nonzero N w /\
                  wterm_ordering (N, w) (M, w0)``,
  Q_TAC SUFF_TAC
    `!M r N. lrcc beta0 M r N ==>
             !w0 w. decreasing M w0 /\ nonzero M w0 /\
                    (w = update_weighing (strip_label M) r w0) ==>
                    decreasing N w /\ wterm_ordering (N, w) (M, w0)` THEN1
    (SRW_TAC [][weighted_reduction_def] THEN
     PROVE_TAC [weighted_reduction_preserves_nonzero_weighing,
                weighted_reduction_def]) THEN
  HO_MATCH_MP_TAC strong_lrcc_ind THEN REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss() ++ DNF_ss)
             [beta0_def, strip_label_thm, decreasing_thm,
              nonzero_thm] THEN REPEAT STRIP_TAC
    THENL [
      ASM_SIMP_TAC (srw_ss()) [decreasing_def] THEN
      REPEAT STRIP_TAC THEN
      `strip_label ([u/v] t) = [strip_label u/v] (strip_label t)`
         by SRW_TAC [][strip_label_subst] THEN
      FULL_SIMP_TAC bool_ss [] THEN
      `p1 ++ [Rt] ∈ valid_posns ([strip_label u/v](strip_label t))`
        by PROVE_TAC [n_posn_valid_posns] THEN
      SRW_TAC [][weight_at_subst] THENL [
        SIMP_TAC (srw_ss() ++ DNF_ss) [bv_posns_thm, update_weighing_def,
                                       v_posns_thm] THEN
        (* p1 : the position within t of a marked redex
           vp : at least the RHS of this redex was within u, originally and
                has been substituted into t.  vp is the position of the
                variable v within t where the substitution happened.
            l : appended onto vp, gives the position of the RHS of the
                redex within t.  On its own, gives the position within u of
                that.
           p2 : position of a bound variable within the LHS of the redex *)
        `p1 ++ [Lt] ∈ lam_posns ([strip_label u/v] (strip_label t))`
           by PROVE_TAC [n_posns_lam_posns] THEN
        `p2 ∈ var_posns ([strip_label u/v] (strip_label t))`
           by PROVE_TAC [bv_posns_at_SUBSET_var_posns] THEN
        ASM_SIMP_TAC (srw_ss()) [weight_at_var_posn] THEN
        Q.ASM_CASES_TAC
          `∃bvp m. bvp ∈ v_posns v (strip_label t) /\ (bvp ++ m = p2)`
        THENL [
          (* the bound variable was also within u, meaning that the whole
             redex was within u *)
          ASM_SIMP_TAC (srw_ss()) [] THEN
          `vp ∈ var_posns (strip_label t)`
            by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
          `?p'. (p1 = vp ++ p') /\ (p' ∈ n_posns n u)`
              by (`p2 IN var_posns (strip_label t) /\
                   ~(p2 IN v_posns v (strip_label t)) \/
                   ?bvp' m'. (p2 = APPEND bvp' m') /\
                             bvp' IN v_posns v (strip_label t) /\
                             m' IN var_posns (strip_label u)`
                     by (FULL_SIMP_TAC (srw_ss()) [var_posns_subst] THEN
                         PROVE_TAC []) THEN
                  FULL_SIMP_TAC (srw_ss()) [] THENL [
                    (* p2 in var_posns (strip_label t) *)
                    FULL_SIMP_TAC (srw_ss()) [] THEN
                    `bvp IN var_posns (strip_label t)`
                       by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
                    `m = []`
                       by PROVE_TAC [no_var_posns_in_var_posn_prefix] THEN
                    FULL_SIMP_TAC (srw_ss()) [],

                    `bvp IN var_posns (strip_label t) /\
                     bvp' IN var_posns (strip_label t)`
                       by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
                    `(bvp' = bvp) /\ (m' = m)`
                       by PROVE_TAC [APPEND_var_posns] THEN
                    NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
                    `(vp = p1) /\ (l = [Rt]) \/
                     (?vpplus. (p1 = APPEND vp vpplus) /\
                               (l = APPEND vpplus [Rt]) /\ ~(vpplus = [])) \/
                     (?p1plus. (vp = APPEND p1 p1plus) /\
                               ([Rt] = APPEND p1plus l) /\ ~(p1plus = []))`
                        by FULL_SIMP_TAC (srw_ss()) [APPEND_CASES]
                    THENL [
                      Q.EXISTS_TAC `[]` THEN
                      FULL_SIMP_TAC (srw_ss()) [n_posns_sub] THENL [
                        PROVE_TAC [lv_posns_n_posns, lv_posns_def],
                        `vp' IN var_posns (strip_label t) /\
                         p1 IN var_posns (strip_label t)`
                           by PROVE_TAC [v_posns_SUBSET_var_posns,
                                         lv_posns_def] THEN
                        PROVE_TAC [no_var_posns_in_var_posn_prefix]
                      ],
                      Q.EXISTS_TAC `vpplus` THEN
                      FULL_SIMP_TAC (srw_ss()) [n_posns_sub] THENL [
                        `APPEND vp (APPEND vpplus [Lt]) IN
                           valid_posns (strip_label t)`
                           by PROVE_TAC [n_posn_valid_posns,
                                         listTheory.APPEND_ASSOC] THEN
                        PROVE_TAC [cant_be_deeper_than_var_posns,
                                   listTheory.APPEND_eq_NIL],
                        Q_TAC SUFF_TAC `vpplus = np` THEN1 SRW_TAC [][] THEN
                        `vp' IN var_posns (strip_label t)`
                            by PROVE_TAC [v_posns_SUBSET_var_posns,
                                          lv_posns_def] THEN
                        PROVE_TAC [APPEND_var_posns]
                      ],
                      `l = []` by (Cases_on `p1plus` THEN
                                   FULL_SIMP_TAC (srw_ss()) []) THEN
                      POP_ASSUM SUBST_ALL_TAC THEN
                      ASM_REWRITE_TAC [list_append_lemma,
                                       GSYM listTheory.APPEND_ASSOC,
                                       listTheory.APPEND_eq_NIL] THEN
                      FULL_SIMP_TAC (srw_ss()) [lam_posns_subst] THENL [
                        FULL_SIMP_TAC (srw_ss()) [bv_posns_at_subst] THEN
                        `APPEND bvp m IN valid_posns (strip_label t)`
                           by PROVE_TAC [bv_posns_at_SUBSET_var_posns,
                                         var_posns_SUBSET_valid_posns] THEN
                        `m = []`
                           by PROVE_TAC [cant_be_deeper_than_var_posns] THEN
                        FULL_SIMP_TAC (srw_ss()) [] THEN
                        PROVE_TAC [v_posns_arent_bv_posns],
                        FULL_SIMP_TAC (srw_ss()) [APPEND_CASES] THENL [
                          REPEAT VAR_EQ_TAC THEN
                          PROVE_TAC [listTheory.NOT_NIL_CONS,
                                     no_var_posns_in_var_posn_prefix,
                                     v_posns_SUBSET_var_posns],
                          `!x y z. ([x : redpos] = APPEND y z) <=>
                                   (y = [x]) /\ (z = []) \/
                                   (y = []) /\ (z = [x])`
                              by (REPEAT GEN_TAC THEN
                                  Cases_on `y` THEN SRW_TAC [][] THEN
                                  PROVE_TAC []) THEN
                          FULL_SIMP_TAC (srw_ss()) [] THEN
                          REPEAT VAR_EQ_TAC THEN
                          FULL_SIMP_TAC (srw_ss()) [n_posns_sub] THEN
                          POP_ASSUM (K ALL_TAC) THENL [
                            `APPEND p1 [Lt] IN lam_posns (strip_label t)`
                               by PROVE_TAC [n_posns_lam_posns] THEN
                            PROVE_TAC [lam_posns_var_posns,
                                       v_posns_SUBSET_var_posns],
                            `vp IN var_posns (strip_label t)`
                              by PROVE_TAC [lv_posns_def,
                                            v_posns_SUBSET_var_posns] THEN
                            VAR_EQ_TAC THEN
                            `APPEND vp (APPEND np [Lt]) IN
                               var_posns (strip_label t)`
                              by PROVE_TAC [listTheory.APPEND_ASSOC,
                                            v_posns_SUBSET_var_posns] THEN
                            PROVE_TAC [listTheory.NOT_NIL_CONS,
                                       listTheory.APPEND_eq_NIL,
                                       no_var_posns_in_var_posn_prefix]
                          ],
                          REPEAT VAR_EQ_TAC THEN
                          IMP_RES_TAC v_posns_SUBSET_var_posns THEN
                          FULL_SIMP_TAC bool_ss
                                        [GSYM listTheory.APPEND_ASSOC] THEN
                          PROVE_TAC [listTheory.APPEND_eq_NIL,
                                     listTheory.NOT_NIL_CONS,
                                     no_var_posns_in_var_posn_prefix]
                        ]
                      ]
                    ]
                  ]) THEN
          SELECT_ELIM_TAC THEN CONJ_TAC THEN1
            (ASM_SIMP_TAC bool_ss [GSYM listTheory.APPEND_ASSOC] THEN
             PROVE_TAC []) THEN
          SRW_TAC [][] THEN
          `vp' IN var_posns (strip_label t)`
             by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
          `(vp' = vp) /\ (x = APPEND p' [Rt])`
             by PROVE_TAC [listTheory.APPEND_ASSOC, APPEND_var_posns] THEN
          NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
          SELECT_ELIM_TAC THEN CONJ_TAC THEN1 PROVE_TAC [] THEN
          SRW_TAC [][] THEN
          `vp' IN var_posns (strip_label t) /\
           bvp IN var_posns (strip_label t)`
             by PROVE_TAC [v_posns_SUBSET_var_posns] THEN
          `(vp' = bvp) /\ (x = m)` by PROVE_TAC [APPEND_var_posns] THEN
          NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
          `APPEND p' [Lt] IN lam_posns (strip_label u)`
              by (FULL_SIMP_TAC (srw_ss()) [lam_posns_subst] THENL [
                    `APPEND vp (APPEND p' [Lt]) IN
                       valid_posns (strip_label t)`
                       by PROVE_TAC [lam_posns_SUBSET_valid_posns,
                                     listTheory.APPEND_ASSOC] THEN
                    PROVE_TAC [cant_be_deeper_than_var_posns,
                               listTheory.APPEND_eq_NIL,
                               listTheory.NOT_NIL_CONS],
                    PROVE_TAC [listTheory.APPEND_ASSOC,
                               APPEND_var_posns,
                               v_posns_SUBSET_var_posns]
                  ]) THEN
          `bvp ++ m ∈
             IMAGE (APPEND vp) (bv_posns_at (APPEND p' [Lt]) (strip_label u))`
             by PROVE_TAC [bv_posns_at_subst2, listTheory.APPEND_ASSOC] THEN
          POP_ASSUM MP_TAC THEN
          ASM_SIMP_TAC (srw_ss() ++ SatisfySimps.SATISFY_ss)
                       [APPEND_var_posns] THEN SRW_TAC [][] THEN
          `m ∈ var_posns (strip_label u)`
             by PROVE_TAC [bv_posns_at_SUBSET_var_posns] THEN
          `w0 (Rt::m) = weight_at m (\p. w0 (Rt::p)) (strip_label u)`
              by SRW_TAC [][weight_at_var_posn] THEN
          SRW_TAC [][] THEN
          PROVE_TAC [decreasing_def],

          ASM_SIMP_TAC (srw_ss()) [] THEN
          SELECT_ELIM_TAC THEN CONJ_TAC THEN1 PROVE_TAC [] THEN
          `p1 ∈ n_posns n t`
              by (FULL_SIMP_TAC (srw_ss()) [n_posns_sub, lv_posns_def] THEN
                  REPEAT VAR_EQ_TAC THEN
                  `∃m. p2 = vp' ++ np ++ [Lt] ++ m`
                      by PROVE_TAC [bv_posns_at_prefix_posn,
                                    listTheory.APPEND_ASSOC] THEN
                  `p2 = vp' ++ (np ++ ([Lt] ++ m))`
                      by FULL_SIMP_TAC (srw_ss()) [] THEN
                  PROVE_TAC []) THEN
          `p1 ++ [Lt] ∈ lam_posns (strip_label t)`
              by PROVE_TAC [n_posns_lam_posns] THEN
          FULL_SIMP_TAC (srw_ss()) [bv_posns_at_subst] THEN
          Q.X_GEN_TAC `m` THEN
          DISCH_THEN (Q.X_CHOOSE_THEN `vp1` STRIP_ASSUME_TAC) THEN
          `(vp1 = vp) /\ (m = l)`
             by PROVE_TAC [APPEND_var_posns, v_posns_SUBSET_var_posns] THEN
          NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
          `(l = [])` by
             (`(vp = p1) /\ (l = [Rt]) \/
               (?m. (vp = APPEND p1 m) /\ ([Rt] = APPEND m l) /\ ~(m = [])) \/
               (?m. (p1 = APPEND vp m) /\ (l = APPEND m [Rt]) /\ ~(m = []))`
                  by FULL_SIMP_TAC (srw_ss()) [APPEND_CASES]
              THENL [
                `APPEND vp [Lt] IN valid_posns (strip_label t)`
                   by PROVE_TAC [lam_posns_SUBSET_valid_posns] THEN
                PROVE_TAC [cant_be_deeper_than_var_posns,
                           listTheory.NOT_NIL_CONS,
                           v_posns_SUBSET_var_posns],
                Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) [],
                `?p. p2 = p1 ++ [Lt] ++ [In] ++ p`
                    by PROVE_TAC [bv_posns_at_prefix_posn] THEN
                `p2 = vp ++ (m ++ ([Lt] ++ In::p))`
                    by FULL_SIMP_TAC (srw_ss()) [] THEN
                PROVE_TAC []
              ]) THEN
          POP_ASSUM SUBST_ALL_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [weight_at_def, lterm_term_weight] THEN
          MATCH_MP_TAC arithmeticTheory.LESS_TRANS THEN
          Q.EXISTS_TAC
            `weight_at (APPEND p1 [Rt]) (\p. w0 (Lt::In::p)) (strip_label t)`
            THEN
          CONJ_TAC THENL [
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_SIMP_TAC (srw_ss()) [lv_posns_def],
            ALL_TAC
          ] THEN
          `p2 IN var_posns (strip_label t)`
              by PROVE_TAC [bv_posns_at_SUBSET_var_posns] THEN
          Q.ABBREV_TAC `fw = \p. w0 (Lt::In::p)` THEN
          `w0 (Lt::In::p2) = fw p2` by SRW_TAC [][Abbr`fw`] THEN
          ` _ = weight_at p2 fw (strip_label t)`
              by PROVE_TAC [weight_at_var_posn] THEN
          POP_ASSUM SUBST_ALL_TAC THEN
          PROVE_TAC [decreasing_def]
        ],

        `p1 IN n_posns n t`
          by (FULL_SIMP_TAC (srw_ss()) [n_posns_sub, lv_posns_def] THEN
              REPEAT VAR_EQ_TAC THEN PROVE_TAC [listTheory.APPEND_ASSOC]) THEN
        `APPEND p1 [Lt] IN lam_posns ([strip_label u/v] (strip_label t)) /\
         APPEND p1 [Lt] IN lam_posns (strip_label t)`
           by PROVE_TAC [n_posns_lam_posns] THEN
        `p2 IN var_posns ([strip_label u/v] (strip_label t))`
           by PROVE_TAC [bv_posns_at_SUBSET_var_posns] THEN
        FULL_SIMP_TAC (srw_ss()) [bv_posns_at_subst] THEN
        `p2 IN var_posns (strip_label t)`
           by PROVE_TAC [bv_posns_at_SUBSET_var_posns] THEN
        `p2 IN valid_posns (strip_label t) /\
         p2 IN valid_posns ([strip_label u/v] (strip_label t))`
           by PROVE_TAC [var_posns_SUBSET_valid_posns] THEN
        ASM_SIMP_TAC (srw_ss()) [weight_at_subst] THEN
        `!vp l. vp IN v_posns v (strip_label t) /\ (APPEND vp l = p2) <=> F`
            by (REPEAT GEN_TAC THEN
                REWRITE_TAC [] THEN STRIP_TAC THEN
                `l = []` by PROVE_TAC [no_var_posns_in_var_posn_prefix,
                                       v_posns_SUBSET_var_posns] THEN
                FULL_SIMP_TAC (srw_ss()) [] THEN
                PROVE_TAC [v_posns_arent_bv_posns]) THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        `{p' | (?p''. p' = APPEND p2 p'') /\
               p' IN v_posns v (strip_label t)} = {}`
            by (SRW_TAC [][EXTENSION, GSYM IMP_DISJ_THM] THEN
                STRIP_TAC THEN
                `p'' = []` by PROVE_TAC [no_var_posns_in_var_posn_prefix,
                                         v_posns_SUBSET_var_posns] THEN
                FULL_SIMP_TAC (srw_ss()) [] THEN
                PROVE_TAC [v_posns_arent_bv_posns]) THEN
        ASM_SIMP_TAC (srw_ss()) [SUM_IMAGE_THM,
                                 arithmeticTheory.ADD_CLAUSES] THEN
        Q.ABBREV_TAC
          `vpset = {p' | (?p''. p' = APPEND (APPEND p1 [Rt]) p'') /\
                         p' IN v_posns v (strip_label t) }` THEN
        MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS THEN
        Q.EXISTS_TAC
          `weight_at (APPEND p1 [Rt]) (\p. w0 (Lt::In::p)) (strip_label t)`
          THEN
        REVERSE CONJ_TAC THEN1
          (Q.ABBREV_TAC `fw = (\p. w0 (Lt::In::p))` THEN
           PROVE_TAC [decreasing_def]) THEN
        MATCH_MP_TAC (DECIDE``z <= y /\ y <= x ==> x - y + z <= x``) THEN
        CONJ_TAC THENL [
          MATCH_MP_TAC CARD_SUM_IMAGE_LE THEN
          `vpset SUBSET v_posns v (strip_label t)`
             by SRW_TAC [][SUBSET_DEF, Abbr`vpset`] THEN
          `FINITE vpset` by PROVE_TAC [SUBSET_FINITE,
                                       v_posns_FINITE] THEN
          ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
          `e IN v_posns v (strip_label t) /\ e IN var_posns (strip_label t)`
             by PROVE_TAC [SUBSET_DEF,
                           v_posns_SUBSET_var_posns] THEN
          Q.ABBREV_TAC `fw = \p. w0 (Lt::In::p)` THEN
          `fw e = weight_at e fw (strip_label t)`
             by PROVE_TAC [weight_at_var_posn] THEN
          ASM_SIMP_TAC (srw_ss()) [GSYM lterm_term_weight, lv_posns_def],
          Q.ABBREV_TAC `lfw = \p. w0 (Lt::In::p)` THEN
          `APPEND p1 [Rt] IN valid_posns (strip_label t)`
             by PROVE_TAC [n_posn_valid_posns] THEN
          ASM_SIMP_TAC (srw_ss()) [weight_at_SUM_IMAGE] THEN
          MATCH_MP_TAC SUM_IMAGE_SUBSET_LE THEN
          UNABBREV_ALL_TAC THEN
          SRW_TAC [][SUBSET_DEF] THENL [
            MATCH_MP_TAC (MATCH_MP SUBSET_FINITE
                                   (Q.SPEC `strip_label t`
                                           var_posns_FINITE)) THEN
            SRW_TAC [][SUBSET_DEF],
            PROVE_TAC [],
            PROVE_TAC [v_posns_SUBSET_var_posns]
          ]
        ]
      ],

      ASM_SIMP_TAC (srw_ss()) [wterm_ordering_def, lterm_term_weight] THEN
      `strip_label ([u/v] t) = [strip_label u/v] (strip_label t)`
         by SRW_TAC [][strip_label_subst] THEN
      ASM_SIMP_TAC (srw_ss()) [GSYM weight_at_def, weight_at_subst,
                               strip_label_thm] THEN
      Cases_on `v_posns v (strip_label t) = {}` THENL [
        SRW_TAC [][SUM_IMAGE_THM,
                   arithmeticTheory.ADD_CLAUSES] THEN
        SRW_TAC [][weight_at_thm, term_weight_def, var_posns_thm,
                   SUM_IMAGE_UNION] THEN
        `!s t. IMAGE (CONS Lt) s INTER IMAGE (CONS Rt) t = {}`
            by (SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
                Cases_on `x` THEN SRW_TAC [][] THEN Cases_on `h` THEN
                SRW_TAC [][]) THEN
        SRW_TAC [][SUM_IMAGE_THM, SUM_IMAGE_IMAGE,
                   combinTheory.o_DEF] THEN
        `~(v IN FV t)` by PROVE_TAC [v_posns_FV_EQ, FV_strip_label] THEN
        SRW_TAC [][GSYM lvar_posns_def, GSYM lterm_weight_def] THEN
        METIS_TAC [nonzero_term_weight],
        ALL_TAC
      ] THEN
      COND_CASES_TAC THENL [
        `strip_label t = VAR v` by PROVE_TAC [NIL_IN_v_posns] THEN
        ASM_SIMP_TAC (srw_ss()) [weight_at_thm, term_weight_thm] THEN
        Q_TAC SUFF_TAC `0 < w0 [Lt; In]` THEN1 SRW_TAC [ARITH_ss][] THEN
        `!p. p IN var_posns (strip_label t) ==> 0 < w0 (Lt::In::p)`
           by FULL_SIMP_TAC (srw_ss()) [nonzero_def, lvar_posns_def] THEN
        PROVE_TAC [v_posns_SUBSET_var_posns],
        ALL_TAC
      ] THEN
      ASM_SIMP_TAC (srw_ss()) [weight_at_thm, term_weight_thm] THEN
      MATCH_MP_TAC (DECIDE ``x < y ==> x < y + z``) THEN
      MATCH_MP_TAC (DECIDE ``z < y /\ y <= x ==> x - y + z < x``) THEN
      CONJ_TAC THENL [
        MATCH_MP_TAC CARD_SUM_IMAGE_LT THEN
        FULL_SIMP_TAC (srw_ss() ++ SatisfySimps.SATISFY_ss)
                      [lterm_term_weight, weight_at_var_posn,
                       v_posns_SUBSET_var_posns, lv_posns_def],
        SIMP_TAC (srw_ss()) [term_weight_def] THEN
        MATCH_MP_TAC SUM_IMAGE_SUBSET_LE THEN
        SRW_TAC [SatisfySimps.SATISFY_ss]
                [v_posns_SUBSET_var_posns, SUBSET_DEF]
      ]
    ],

    (* beta reduction on left of application *)
    SIMP_TAC (srw_ss() ++ ETA_ss)
             [update_weighing_def, strip_label_thm,
              decreasing_thm, nonzero_thm, wterm_ordering_def,
              lterm_term_weight, term_weight_thm],
    (* beta reduction on right of application *)
    SIMP_TAC (srw_ss() ++ ETA_ss)
             [update_weighing_def, strip_label_thm,
              decreasing_thm, nonzero_thm, wterm_ordering_def,
              lterm_term_weight, term_weight_thm],
    (* beta reduction under lambda abstraction *)
    SIMP_TAC (srw_ss() ++ ETA_ss)
             [update_weighing_def, strip_label_thm,
              decreasing_thm, nonzero_thm, wterm_ordering_def,
              lterm_term_weight, term_weight_thm],

    (* beta reduction on RHS of marked redex *)
    SIMP_TAC (srw_ss() ++ ETA_ss)
             [update_weighing_def, strip_label_thm,
              decreasing_thm, nonzero_thm, wterm_ordering_def,
              lterm_term_weight, term_weight_thm,
              lv_posns_def] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS THEN
    Q.EXISTS_TAC `term_weight (strip_label M) (\p. w0 (Rt::p))` THEN
    ASM_SIMP_TAC (srw_ss() ++ SatisfySimps.SATISFY_ss) [] THEN
    Q.ABBREV_TAC `wf = \p. w0 (Rt::p)` THEN
    PROVE_TAC [DECIDE ``x <= y <=> x < y \/ (x = y)``],

    (* beta reduction within LHS of marked redex *)
    SIMP_TAC (srw_ss() ++ ETA_ss)
             [update_weighing_def, strip_label_thm,
              decreasing_thm, nonzero_thm, wterm_ordering_def,
              lterm_term_weight, term_weight_thm, lv_posns_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    `r IN redex_posns (strip_label M)` by PROVE_TAC [beta0_redex_posn] THEN
    ASM_SIMP_TAC (srw_ss()) [update_weighing_vsubst] THEN
    REPEAT STRIP_TAC THEN
    `labelled_redn beta (strip_label M) r (strip_label N)`
       by PROVE_TAC [lrcc_RUNION, lrcc_labelled_redn] THEN
    IMP_RES_THEN (IMP_RES_THEN (Q.X_CHOOSE_THEN `p1` STRIP_ASSUME_TAC))
                 FV_weights_update_weighing THEN
    ASM_SIMP_TAC (srw_ss()) []
  ]);


val WF_path_finite0 = prove(
  ``!R P L. WF R /\ (!x r y. P x /\ L x r y ==> P y /\ R y x) ==>
            !x p. (x = first p) /\ okpath L p /\ P (first p) ==>
                  finite p``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM (HO_MATCH_MP_TAC o
               MATCH_MP relationTheory.WF_INDUCTION_THM) THEN
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `p` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
              pathTheory.path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);

val WF_path_finite = save_thm("WF_path_finite",
                              SIMP_RULE bool_ss [] WF_path_finite0);


val path_case_def =
  Define`path_case f g p = if is_stopped p then f (first p)
                           else g (first p) (first_label p) (tail p)`;

val path_case_thm = store_thm(
  "path_case_thm",
  ``!f g. (!x. path_case f g (stopped_at x) = f x) /\
          (!x r y. path_case f g (pcons x r y) = g x r y)``,
  SRW_TAC [][path_case_def]);


(* the lift_weighing function computes (among other things) the weighing
   asserted to exist by Barendregt's Lemma 11.2.19 *)
val lift_weighing_t =
  ``\w_sigma.
       path_case (\x. ((x, FST w_sigma), NONE))
                 (\x r y. ((x, FST w_sigma),
                           SOME (r,
                                 (update_weighing (strip_label x) r
                                                  (FST w_sigma), y))))
                 (SND w_sigma)``

val lift_weighing_def = new_specification(
  "lift_weighing_def", ["lift_weighing"],
  prove(``?f. (!w x. f w (stopped_at x) = stopped_at (x, w)) /\
              (!w x r y. f w (pcons x r y) =
                         pcons (x, w) r
                               (f (update_weighing (strip_label x) r w) y))``,
        STRIP_ASSUME_TAC (ISPEC lift_weighing_t pathTheory.path_Axiom) THEN
        Q.EXISTS_TAC `\w p. g (w, p)` THEN
        SIMP_TAC (srw_ss()) [] THEN
        REPEAT STRIP_TAC THEN
        POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
        SRW_TAC [][path_case_thm]));

val pstrip_weights_def = Define`
  pstrip_weights = pmap (FST : lterm # (redpos list -> num) -> lterm) I
`;

val pstrip_lift_weighing = store_thm(
  "pstrip_lift_weighing",
  ``!p w. pstrip_weights (lift_weighing w p) = p``,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [pathTheory.path_bisimulation] THEN
  Q.EXISTS_TAC `\x y. ?w. x = pstrip_weights (lift_weighing w y)` THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    Q.ISPEC_THEN `q2` STRUCT_CASES_TAC pathTheory.path_cases THEN
    SRW_TAC [][lift_weighing_def, pstrip_weights_def, pathTheory.pmap_thm] THEN
    PROVE_TAC []
  ]);

val first_lift_weighing = store_thm(
  "first_lift_weighing",
  ``!p w. first (lift_weighing w p) = (first p, w)``,
  REPEAT GEN_TAC THEN
  Q.ISPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][lift_weighing_def]);

val finite_lift_weighing = store_thm(
  "finite_lift_weighing",
  ``!p w : redpos list -> num. finite (lift_weighing w p) = finite p``,
  Q_TAC SUFF_TAC
     `(!p : (lterm, redpos list) path.
            finite p ==>
            !w : redpos list -> num. finite (lift_weighing w p)) /\
      (!p. finite p ==>
           !(w : redpos list -> num)  (p' : (lterm, redpos list) path).
                   (p = lift_weighing w p') ==> finite p')`
      THEN1 PROVE_TAC [] THEN
  CONJ_TAC THEN HO_MATCH_MP_TAC finite_path_ind THEN
  SIMP_TAC (srw_ss()) [lift_weighing_def] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THENL [ ALL_TAC, STRIP_TAC THEN REPEAT GEN_TAC] THEN
  Q.ISPEC_THEN `p'` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][lift_weighing_def] THEN PROVE_TAC []);

val beta0_weighted_reduction_lift_weighing = store_thm(
  "beta0_weighted_reduction_lift_weighing",
  ``!p. okpath (lrcc beta0) p ==>
        !w. okpath weighted_reduction (lift_weighing w p)``,
  Q_TAC SUFF_TAC
      `!p2. (?w p. (p2 = lift_weighing w p) /\ okpath (lrcc beta0) p) ==>
            okpath weighted_reduction p2` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC pathTheory.okpath_co_ind THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  Q.ISPEC_THEN `p` FULL_STRUCT_CASES_TAC path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [lift_weighing_def, first_lift_weighing] THEN
  CONJ_TAC THENL [
    SRW_TAC [][weighted_reduction_def],
    PROVE_TAC []
  ]);

val beta0_paths_finite = store_thm(
  "beta0_paths_finite",
  ``!p. okpath (lrcc beta0) p ==> finite p``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `first p` STRIP_ASSUME_TAC decreasing_weights_exist THEN
  `okpath weighted_reduction (lift_weighing w p)`
       by PROVE_TAC [beta0_weighted_reduction_lift_weighing] THEN
  Q_TAC SUFF_TAC `finite (lift_weighing w p)`
        THEN1 PROVE_TAC [finite_lift_weighing] THEN
  MATCH_MP_TAC
    (SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] WF_path_finite) THEN
  Q.EXISTS_TAC `wterm_ordering` THEN
  REWRITE_TAC [WF_wterm_ordering] THEN
  Q.EXISTS_TAC `\tw. decreasing (FST tw) (SND tw) /\
                     nonzero (FST tw) (SND tw)` THEN
  Q.EXISTS_TAC `weighted_reduction` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, first_lift_weighing] THEN
  PROVE_TAC [weighted_reduction_reduces_ordering]);

val lrcc_lcompat_closure = store_thm(
  "lrcc_lcompat_closure",
  ``!R x y. lcompat_closure R x y = ?r. lrcc R x r y``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `(!x y. lcompat_closure R x y ==> ?r. lrcc R x r y)`
                  THEN1 PROVE_TAC [lrcc_lcc] THEN
  HO_MATCH_MP_TAC lcompat_closure_ind THEN SRW_TAC [][] THEN
  PROVE_TAC [lrcc_rules]);

val inv_lemma = prove(
  ``inv R = \x y. R y x``,
  SRW_TAC [][FUN_EQ_THM, relationTheory.inv_DEF])

val TC_inv = GSYM relationTheory.inv_TC

val prop11_2_20 = store_thm(
  "prop11_2_20",
  ``WF (inv (lcompat_closure beta0))``,
  REWRITE_TAC [lrcc_lcompat_closure, GSYM pathTheory.SN_def, inv_lemma,
               pathTheory.SN_finite_paths_EQ, beta0_paths_finite]);

val finite_lift_path = store_thm(
  "finite_lift_path",
  ``!M p. finite (lift_path M p) = finite p``,
  Q_TAC SUFF_TAC
        `(!p. finite p ==> !M : lterm. finite (lift_path M p)) /\
         (!p'. finite p' ==>
               !M : lterm p. (p' = lift_path M p) ==> finite p)`
         THEN1 PROVE_TAC [] THEN CONJ_TAC THEN
  HO_MATCH_MP_TAC finite_path_ind THENL [
    SRW_TAC [][lift_path_def],
    ALL_TAC
  ] THEN
  Q_TAC SUFF_TAC
    `(!(x : lterm) M p. (stopped_at x = lift_path M p) ==> finite p) /\
     (!(x : lterm) r p. finite p /\
              (!M q. (p = lift_path M q) ==> finite q) ==>
              !M q. (pcons x r p = lift_path M q) ==> finite q)` THEN1
              PROVE_TAC [] THEN
  REPEAT STRIP_TAC THENL [
    Q.ISPEC_THEN `p` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases,
    Q.ISPEC_THEN `q` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases
  ] THEN FULL_SIMP_TAC (srw_ss()) [lift_path_def] THEN PROVE_TAC []);

val theorem11_2_21 = store_thm(
  "theorem11_2_21",
  ``!M p. p IN development M ==> finite p``,
  REWRITE_TAC [term_development_thm] THEN
  PROVE_TAC [lemma11_2_12, beta0_paths_finite, finite_lift_path]);

val FD = save_thm("FD", theorem11_2_21)

val extend_path_maximally = store_thm(
  "extend_path_maximally",
  ``!R. SN R ==>
        !x. ?p. finite p /\ (first p = x) /\ okpath R p /\
                !r y. ~R (last p) r y``,
  REWRITE_TAC [SN_def] THEN GEN_TAC THEN
  DISCH_THEN (HO_MATCH_MP_TAC o MATCH_MP relationTheory.WF_INDUCTION_THM) THEN
  SRW_TAC [][] THEN
  Cases_on `?r y. R x r y` THENL [
    POP_ASSUM STRIP_ASSUME_TAC THEN
    RES_TAC THEN Q.EXISTS_TAC `pcons x r p` THEN
    SRW_TAC [][],
    Q.EXISTS_TAC `stopped_at x` THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val finite_strip_path_label = store_thm (
  "finite_strip_path_label",
  ``!p. finite (strip_path_label p) = finite p``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC
          `!q. finite q ==> !p. (q = strip_path_label p) ==> finite p`
          THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC finite_path_ind THEN REPEAT STRIP_TAC THEN
    Q.ISPEC_THEN `p` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
    FULL_SIMP_TAC (srw_ss()) [strip_path_label_thm],
    HO_MATCH_MP_TAC finite_path_ind THEN
    SRW_TAC [][strip_path_label_thm]
  ]);

val okpath_RUNION = store_thm(
  "okpath_RUNION",
  ``!R1 R2 p. okpath (lrcc R1) p ==> okpath (lrcc (R1 RUNION R2)) p``,
  GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC okpath_co_ind THEN
  SRW_TAC [][lrcc_RUNION]);

val lift_path_plink = store_thm(
  "lift_path_plink",
  ``!p1 M p2.
       finite p1 /\ (last p1 = first p2) ==>
       (lift_path M (plink p1 p2) =
        plink (lift_path M p1) (lift_path (last (lift_path M p1)) p2))``,
  SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC finite_path_ind THEN
  SRW_TAC [][lift_path_def, first_plink]);

val lift_path_strip_path_label = store_thm(
  "lift_path_strip_path_label",
  ``!p. okpath (lrcc (beta0 RUNION beta1)) p ==>
        (lift_path (first p) (strip_path_label p) = p)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [path_bisimulation] THEN
  Q.EXISTS_TAC `\x y. okpath (lrcc (beta0 RUNION beta1)) y /\
                      (x = lift_path (first y) (strip_path_label y)) ` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  GEN_TAC THEN
  Q.ISPEC_THEN `q2` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][lift_path_def, strip_path_label_thm, first_strip_path_label] THEN
  Q_TAC SUFF_TAC `lift_redn x r (strip_label (first q)) = first q`
        THEN1 SRW_TAC [][] THEN
  IMP_RES_TAC lrcc_labelled_redn THEN
  IMP_RES_TAC lift_redn_def THEN
  PROVE_TAC [lrcc_det]);

val n_posns_beta0 = store_thm(
  "n_posns_beta0",
  ``!M p n. p IN n_posns n M ==> ?N. lrcc beta0 M p N``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  REVERSE (SRW_TAC [][n_posns_def]) THEN1
    (FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN RES_TAC THEN
     ONCE_REWRITE_TAC [lrcc_cases] THEN SRW_TAC [][beta0_def] THEN
     PROVE_TAC []) THEN
  PROVE_TAC [lrcc_rules, l14a]);

val corollary11_2_22i = store_thm(
  "corollary11_2_22i",
  ``!M ps p. p IN development M ps ==>
           ?p'. (last p = first p') /\
                (plink p p') IN complete_development M ps``,
  REWRITE_TAC [lemma11_2_12, complete_development_thm] THEN
  REPEAT STRIP_TAC THEN
  `SN (lrcc beta0)` by PROVE_TAC [SN_finite_paths_EQ, beta0_paths_finite] THEN
  Q.ABBREV_TAC `p' = lift_path (nlabel 0 (first p) ps) p` THEN
  `?p2. finite p2 /\ (first p2 = last p') /\ okpath (lrcc beta0) p2 /\
        !r y. ~lrcc beta0 (last p2) r y`
        by PROVE_TAC [extend_path_maximally] THEN
  `finite p /\ finite p'`
        by PROVE_TAC [finite_lift_path, beta0_paths_finite] THEN
  `last p = strip_label (last p')`
        by PROVE_TAC [strip_label_nlabel, residuals_def] THEN
  Q.EXISTS_TAC `strip_path_label p2` THEN
  ASM_SIMP_TAC (srw_ss()) [first_strip_path_label, first_plink,
                           finite_strip_path_label] THEN
  `last p = first (strip_path_label p2)`
        by PROVE_TAC [first_strip_path_label] THEN
  `okpath (labelled_redn beta) (strip_path_label p2)`
        by PROVE_TAC [okpath_RUNION, lemma11_2_1] THEN
  `okpath (lrcc (beta0 RUNION beta1)) p2` by PROVE_TAC [okpath_RUNION] THEN
  REPEAT CONJ_TAC THENL [
    ASM_SIMP_TAC (srw_ss()) [lift_path_plink],
    ASM_SIMP_TAC (srw_ss()) [lift_path_plink, first_lift_path] THEN
    Q_TAC SUFF_TAC `lift_path (last p') (strip_path_label p2) = p2`
                  THEN1 SRW_TAC [][] THEN
    PROVE_TAC [lift_path_strip_path_label],
    `finite (strip_path_label p2)` by SRW_TAC [][finite_strip_path_label] THEN
    ASM_SIMP_TAC (srw_ss()) [lemma11_2_6] THEN
    Q.SPEC_THEN `strip_path_label p2` MP_TAC residuals_def THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (Q.SPEC_THEN `residuals p ps` STRIP_ASSUME_TAC) THEN
    `nlabel 0 (first (strip_path_label p2)) (residuals p ps) = first p2`
        by (ASM_SIMP_TAC (srw_ss()) [labelled_term_component_equality,
                                     strip_label_nlabel,
                                     first_strip_path_label] THEN
            Q.SPEC_THEN `p` MP_TAC residuals_def THEN
            ASM_REWRITE_TAC [first_strip_path_label] THEN
            DISCH_THEN (Q.SPEC_THEN `ps` STRIP_ASSUME_TAC o GSYM) THEN
            ASM_SIMP_TAC bool_ss []) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Q.PAT_X_ASSUM `last x = y` MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [lift_path_strip_path_label] THEN
    DISCH_THEN (MP_TAC o Q.AP_TERM `n_posns 0`) THEN
    POP_ASSUM (ASSUME_TAC o
               REWRITE_RULE [SUBSET_INTER_ABSORPTION]) THEN
    ASM_SIMP_TAC (srw_ss()) [n_posns_nlabel] THEN
    DISCH_THEN (fn th => REWRITE_TAC [SYM th]) THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    `?p. p IN n_posns 0 (last p2)`
        by PROVE_TAC [SET_CASES, IN_INSERT] THEN
    PROVE_TAC [n_posns_beta0]
  ]);

(* corollary11_2_22ii requires a proof of K\"onig's lemma *)

val RTC_lcc_rules = store_thm(
  "RTC_lcc_rules",
  ``!x y. RTC (lcompat_closure R) x y ==>
          (!z. RTC (lcompat_closure R) (x @@ z) (y @@ z) /\
               RTC (lcompat_closure R) (z @@ x) (z @@ y)) /\
          !v.  RTC (lcompat_closure R) (LAM v x) (LAM v y) /\
               !n w. RTC (lcompat_closure R) (LAMi n v w x) (LAMi n v w y) /\
                     RTC (lcompat_closure R) (LAMi n v x w) (LAMi n v y w)``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  PROVE_TAC [relationTheory.RTC_RULES, lcompat_closure_rules]);

val lcc_cosubstitutive = store_thm(
  "lcc_cosubstitutive",
  ``!P M N v. lcompat_closure R M N ==>
              RTC (lcompat_closure R) ([M/v] P) ([N/v] P)``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `P` THEN
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `v INSERT FV M UNION FV N` THEN SRW_TAC [][lSUB_VAR] THEN
  PROVE_TAC [relationTheory.RTC_RULES, relationTheory.RTC_RTC,
             RTC_lcc_rules]);

val strong_lcc_ind =
    IndDefLib.derive_strong_induction
      (lcompat_closure_rules, lcompat_closure_ind)

val beta0_LAMi = store_thm(
  "beta0_LAMi",
  ``beta0 (LAMi n v M N) P = (P = [N/v] M)``,
  SRW_TAC [][beta0_def, EQ_IMP_THM, lLAMi_eq_thm] THEN
  SRW_TAC [][fresh_ltpm_subst, l15a] THEN
  PROVE_TAC []);

val lcc_b0_tpm_imp = store_thm(
  "lcc_b0_tpm_imp",
  ``!M N. lcompat_closure beta0 M N ==>
          !p. lcompat_closure beta0 (ltpm p M) (ltpm p N)``,
  HO_MATCH_MP_TAC lcompat_closure_ind THEN
  SRW_TAC [][lcompat_closure_rules, beta0_def] THEN
  SRW_TAC [][ltpm_subst] THEN METIS_TAC [lcompat_closure_rules, beta0_def]);

val lcc_beta0_LAMi = store_thm(
  "lcc_beta0_LAMi",
  ``lcompat_closure beta0 (LAMi n v M N) P <=>
      (P = [N/v] M) \/
      (?P0. lcompat_closure beta0 M P0 /\ (P = LAMi n v P0 N)) \/
      (?P0. lcompat_closure beta0 N P0 /\ (P = LAMi n v M P0))``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [lcompat_closure_cases])) THEN
  SRW_TAC [][EQ_IMP_THM, beta0_LAMi] THENL [
    DISJ2_TAC THEN DISJ1_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [lLAMi_eq_thm] THEN
    Q.EXISTS_TAC `ltpm [(v,v')] y` THEN
    SRW_TAC [][pmact_flip_args, lcc_b0_tpm_imp] THEN
    PROVE_TAC [lcc_beta_FV, lrcc_RUNION, lrcc_lcompat_closure],
    DISJ2_TAC THEN DISJ2_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [lLAMi_eq_thm, pmact_flip_args],
    PROVE_TAC [],
    PROVE_TAC []
  ]);

val lcc_beta0_app = store_thm(
  "lcc_beta0_app",
  ``!M N P. lcompat_closure beta0 (M @@ N) P <=>
            (?P0. lcompat_closure beta0 M P0 /\ (P = P0 @@ N)) \/
            (?P0. lcompat_closure beta0 N P0 /\ (P = M @@ P0))``,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [lcompat_closure_cases])) THEN
  SRW_TAC [][beta0_def, EQ_IMP_THM] THEN PROVE_TAC []);

val lcc_beta0_LAM = store_thm(
  "lcc_beta0_LAM",
  ``!v M P. lcompat_closure beta0 (LAM v M) P <=>
            ?P0. lcompat_closure beta0 M P0 /\ (P = LAM v P0)``,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [lcompat_closure_cases])) THEN
  SRW_TAC [][beta0_def, EQ_IMP_THM] THENL [
    FULL_SIMP_TAC (srw_ss()) [lLAM_eq_thm] THEN
    Q.EXISTS_TAC `ltpm [(v,v')] y` THEN
    SRW_TAC [][lcc_b0_tpm_imp, pmact_flip_args] THEN
    PROVE_TAC [lcc_beta_FV, lrcc_RUNION, lrcc_lcompat_closure],

    PROVE_TAC []
  ]);


val beta0_WCR = store_thm(
  "beta0_WCR",
  ``weak_diamond (lcompat_closure beta0)``,
  SIMP_TAC (srw_ss()) [weak_diamond_def, RIGHT_FORALL_IMP_THM,
                       GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC strong_lcc_ind THEN REPEAT STRIP_TAC THENL [
    (* beta0 (base) case *)
    FULL_SIMP_TAC (srw_ss()) [beta0_def] THEN
    REPEAT VAR_EQ_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [lcc_beta0_LAMi] THENL [
      PROVE_TAC [relationTheory.RTC_RULES],
      `beta0 (LAMi n v P0 u) ([u/v] P0)` by PROVE_TAC [beta0_def] THEN
      `lcompat_closure beta0 (LAMi n v P0 u) ([u/v] P0)`
         by PROVE_TAC [lcompat_closure_rules] THEN
      `RTC (lcompat_closure beta0) (LAMi n v P0 u) ([u/v] P0)`
         by PROVE_TAC [relationTheory.RTC_RULES] THEN
      Q.EXISTS_TAC `([u/v] P0)` THEN
      PROVE_TAC [lrcc_lcompat_closure, lrcc_lsubstitutive,
                 beta0_lsubstitutive, relationTheory.RTC_RULES],
      `beta0 (LAMi n v t P0) ([P0/v] t)` by PROVE_TAC [beta0_def] THEN
      `lcompat_closure beta0 (LAMi n v t P0) ([P0/v] t)`
         by PROVE_TAC [lcompat_closure_rules] THEN
      Q.EXISTS_TAC `[P0/v] t` THEN
      PROVE_TAC [lcc_cosubstitutive, relationTheory.RTC_RULES]
    ],

    (* app right case *)
    FULL_SIMP_TAC (srw_ss()) [lcc_beta0_app] THEN
    PROVE_TAC [relationTheory.RTC_RULES, RTC_lcc_rules],

    (* app left case *)
    FULL_SIMP_TAC (srw_ss()) [lcc_beta0_app] THEN
    PROVE_TAC [relationTheory.RTC_RULES, RTC_lcc_rules],

    (* lam case *)
    FULL_SIMP_TAC (srw_ss()) [lcc_beta0_LAM] THEN
    PROVE_TAC [RTC_lcc_rules],

    (* LAMi body moves case *)
    REPEAT (POP_ASSUM MP_TAC) THEN
    Q_TAC SUFF_TAC
          `!x y z n v z'.
              lcompat_closure beta0 x y /\
              (!z. lcompat_closure beta0 x z ==>
                   ?u. RTC (lcompat_closure beta0) y u /\
                       RTC (lcompat_closure beta0) z u) /\
              lcompat_closure beta0 (LAMi n v x z) z' ==>
              ?u. RTC (lcompat_closure beta0) (LAMi n v y z) u /\
                  RTC (lcompat_closure beta0) z' u` THEN1 METIS_TAC [] THEN
    SRW_TAC [][lcc_beta0_LAMi] THENL [
      Q.EXISTS_TAC `[z/v] y` THEN
      `beta0 (LAMi n v y z) ([z/v] y)` by PROVE_TAC [beta0_def] THEN
      `lcompat_closure beta0 (LAMi n v y z) ([z/v] y)`
         by PROVE_TAC [lcompat_closure_rules] THEN
      PROVE_TAC [lrcc_lcompat_closure, lrcc_lsubstitutive,
                 beta0_lsubstitutive, relationTheory.RTC_RULES],
      PROVE_TAC [RTC_lcc_rules],
      PROVE_TAC [RTC_lcc_rules, relationTheory.RTC_RULES]
    ],

    (* LAMi argument moves *)
    REPEAT (POP_ASSUM MP_TAC) THEN
    Q_TAC SUFF_TAC
          `!x y z n v z'.
              lcompat_closure beta0 x y /\
              (!z. lcompat_closure beta0 x z ==>
                   ?u. RTC (lcompat_closure beta0) y u /\
                       RTC (lcompat_closure beta0) z u) /\
              lcompat_closure beta0 (LAMi n v z x) z' ==>
              ?u. RTC (lcompat_closure beta0) (LAMi n v z y) u /\
                  RTC (lcompat_closure beta0) z' u` THEN1 METIS_TAC [] THEN
    SRW_TAC [][lcc_beta0_LAMi] THENL [
      Q.EXISTS_TAC `[y/v] z` THEN
      `beta0 (LAMi n v z y) ([y/v] z)` by PROVE_TAC [beta0_def] THEN
      `lcompat_closure beta0 (LAMi n v z y) ([y/v] z)`
         by PROVE_TAC [lcompat_closure_rules] THEN
      PROVE_TAC [lcc_cosubstitutive, relationTheory.RTC_RULES],
      PROVE_TAC [RTC_lcc_rules, relationTheory.RTC_RULES],
      PROVE_TAC [RTC_lcc_rules]
    ]
  ]);

val newman_recast = store_thm(
  "newman_recast",
  ``WF (inv R) /\ weak_diamond R ==> diamond_property (RTC R)``,
  SRW_TAC [][relationTheory.Newmans_lemma,
             GSYM relationTheory.CR_def,
             GSYM relationTheory.SN_def]);

val CR_beta0 = store_thm(
  "CR_beta0",
  ``diamond_property (RTC (lcompat_closure beta0))``,
  PROVE_TAC [newman_recast, prop11_2_20, beta0_WCR]);

val okpath_RTC = store_thm(
  "okpath_RTC",
  ``!R p.
        okpath R p /\ finite p ==>
        RTC (\x y. ?l. R x l y) (first p) (last p)``,
  GEN_TAC THEN HO_MATCH_MP_TAC finite_okpath_ind THEN
  SRW_TAC [][relationTheory.RTC_RULES] THEN
  Q.SPEC_THEN `RR` (MATCH_MP_TAC o CONJUNCT2) relationTheory.RTC_RULES THEN
  PROVE_TAC []);

val unique_nforms = store_thm(
  "unique_nforms",
  ``!R x y z. diamond_property (RTC R) /\
              RTC R x y /\ RTC R x z /\ (!u. ~R y u) /\ (!u. ~R z u) ==>
              (y = z)``,
  REPEAT STRIP_TAC THEN
  `?w. RTC R y w /\ RTC R z w` by PROVE_TAC [diamond_property_def] THEN
  PROVE_TAC [relationTheory.RTC_CASES1]);

val beta0_n_posns = store_thm(
  "beta0_n_posns",
  ``!M p N. lrcc beta0 M p N ==> ?n. p IN n_posns n M``,
  HO_MATCH_MP_TAC lrcc_ind THEN
  SRW_TAC [][n_posns_def, beta0_def] THENL [
    SRW_TAC [COND_elim_ss][n_posns_def],
    PROVE_TAC [],
    PROVE_TAC []
  ]);


(* definitions 11_2_26 *)
val SN_beta0 = save_thm(
  "SN_beta0",
  REWRITE_RULE [lrcc_lcompat_closure, inv_lemma, GSYM SN_def] prop11_2_20);

val cpl_uexists = store_thm(
  "cpl_uexists",
  ``!M'. ?!N'. RTC (lcompat_closure beta0) M' N' /\
               !N''. ~ lcompat_closure beta0 N' N''``,
  SRW_TAC [][EXISTS_UNIQUE_THM] THENL [
    Q.SPEC_THEN `M'` STRIP_ASSUME_TAC
                (MATCH_MP extend_path_maximally SN_beta0) THEN
    Q.EXISTS_TAC `last p` THEN
    IMP_RES_TAC okpath_RTC THEN
    FULL_SIMP_TAC (srw_ss()) [lrcc_lcompat_closure] THEN
    FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [GSYM lrcc_lcompat_closure] THEN
    PROVE_TAC [],
    PROVE_TAC [unique_nforms, CR_beta0]
  ]);

val cpl_exists =
    (CONV_RULE SKOLEM_CONV o
     CONJUNCT1 o
     CONV_RULE (BINDER_CONV EXISTS_UNIQUE_CONV THENC FORALL_AND_CONV))
    cpl_uexists

val lterm_cpl_def =
    new_specification("lterm_cpl_def", ["lterm_cpl"], cpl_exists)

val term_posset_cpl_def = Define`
  term_posset_cpl (M, FS) = strip_label (lterm_cpl (nlabel 0 M FS))
`;

val _ = overload_on("Cpl", ``lterm_cpl``);
val _ = overload_on("Cpl", ``term_posset_cpl``);

val lterm_cpl_unique = store_thm(
  "lterm_cpl_unique",
  ``!M' N'. RTC (lcompat_closure beta0) M' N' /\
            (!N''. ~lcompat_closure beta0 N' N'') ==>
            (N' = Cpl M')``,
  REPEAT GEN_TAC THEN
  ASSUME_TAC (CONJUNCT2 (CONV_RULE (BINDER_CONV EXISTS_UNIQUE_CONV THENC
                                    FORALL_AND_CONV) cpl_uexists)) THEN
  POP_ASSUM (Q.SPECL_THEN [`M'`, `N'`, `Cpl M'`] MP_TAC) THEN
  REWRITE_TAC [lterm_cpl_def]);

val Cpl_complete_development = store_thm(
  "Cpl_complete_development",
  ``!M ps s. s IN complete_development M ps ==> (last s = Cpl (M, ps))``,
  SRW_TAC [][complete_development_thm, lemma11_2_12] THEN
  Q.ABBREV_TAC `M = first s` THEN
  Q.ABBREV_TAC `M' = nlabel 0 M ps` THEN
  Q.ABBREV_TAC `s' = lift_path M' s` THEN
  `finite s'` by PROVE_TAC [finite_lift_path] THEN
  `RTC (lcompat_closure beta0) M' (last s')` by
     (`M' = first s'` by PROVE_TAC [first_lift_path] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `!R. lcompat_closure R = \x y. ?r. lrcc R x r y`
          by SRW_TAC [][lrcc_lcompat_closure, FUN_EQ_THM] THEN
      SRW_TAC [][] THEN MATCH_MP_TAC okpath_RTC THEN SRW_TAC [][]) THEN
  `(last s' = nlabel 0 (last s) (residuals s ps))`
      by PROVE_TAC [residuals_def] THEN
  ASM_SIMP_TAC (srw_ss())[term_posset_cpl_def] THEN
  `!n. n_posns n (last s') = {}`
             by (GEN_TAC THEN Cases_on `n` THEN
                 SRW_TAC [][n_posns_nlabel]) THEN
  `!N''. ~lcompat_closure beta0 (last s') N''`
      by PROVE_TAC [beta0_n_posns, lrcc_lcompat_closure,
                    NOT_IN_EMPTY] THEN
  `Cpl M' = last s'` by PROVE_TAC [lterm_cpl_unique] THEN
  SRW_TAC [][strip_label_nlabel]);

val FDbang = store_thm(
  "FDbang",
  ``(s IN development M ==> finite s) /\
    (s IN development M ps ==>
       ?s'. (last s = first s') /\ plink s s' IN complete_development M ps) /\
    (!s1 s2.
        s1 IN complete_development M ps /\ s2 IN complete_development M ps ==>
              (last s1 = last s2))``,
  PROVE_TAC [FD, corollary11_2_22i, Cpl_complete_development]);

(* written as

       ---->>
         1

   in Barendregt *)


val fd_grandbeta_def = Define`
  fd_grandbeta M N = ?FS. (Cpl(M, FS) = N) /\ FS SUBSET M
`;

val n_posns_null_labelling = store_thm(
  "n_posns_null_labelling",
  ``!n t. n_posns n (null_labelling t) = {}``,
  SRW_TAC [][GSYM (Q.SPECL [`M`, `0`] nlabel_null_labelling)] THEN
  Cases_on `n = 0` THEN SRW_TAC [][n_posns_nlabel]);

val lrcc_beta0_LAM = store_thm(
  "lrcc_beta0_LAM",
  ``!v t p N. lrcc beta0 (LAM v t) p N =
              ?t' r. (N = LAM v t') /\ (p = In :: r) /\ lrcc beta0 t r t'``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    IMP_RES_TAC beta0_n_posns THEN
    `lrcc (beta0 RUNION beta1) (LAM v t) p N` by PROVE_TAC [pick_a_beta] THEN
    `?p0 N0. lrcc (beta0 RUNION beta1) t p0 N0 /\
             (N = LAM v N0) /\ (p = In::p0)` by PROVE_TAC [lrcc_beta_lam] THEN
    `p0 IN n_posns n t` by FULL_SIMP_TAC (srw_ss()) [n_posns_def] THEN
    PROVE_TAC [pick_a_beta],
    PROVE_TAC [lrcc_rules]
  ]);

val lcompat_closure_RUNION_MONOTONE = store_thm(
  "lcompat_closure_RUNION_MONOTONE",
  ``!R1 x y. lcompat_closure R1 x y ==> lcompat_closure (R1 RUNION R2) x y``,
  GEN_TAC THEN HO_MATCH_MP_TAC lcompat_closure_ind THEN
  PROVE_TAC [lcompat_closure_rules, relationTheory.RUNION]);

val lcompat_closure_RUNION_distrib = store_thm(
  "lcompat_closure_RUNION_distrib",
  ``!R1 R2. lcompat_closure R1 RUNION lcompat_closure R2 =
            lcompat_closure (R1 RUNION R2)``,
  ASM_SIMP_TAC (srw_ss())[FUN_EQ_THM, relationTheory.RUNION, EQ_IMP_THM,
                          DISJ_IMP_THM, FORALL_AND_THM] THEN
  REPEAT CONJ_TAC THENL [
    PROVE_TAC [lcompat_closure_RUNION_MONOTONE],
    PROVE_TAC [lcompat_closure_RUNION_MONOTONE, RUNION_COMM],
    Q_TAC SUFF_TAC
      `!R x y. lcompat_closure R x y ==>
               !R1 R2. (R = R1 RUNION R2) ==>
                       lcompat_closure R1 x y \/ lcompat_closure R2 x y` THEN1
      PROVE_TAC [] THEN GEN_TAC THEN
    HO_MATCH_MP_TAC lcompat_closure_ind THEN SRW_TAC [][] THEN
    PROVE_TAC [relationTheory.RUNION, lcompat_closure_rules]
  ]);

val beta0_reduce_at_single_label = store_thm(
  "beta0_reduce_at_single_label",
  ``!x pos y. lrcc beta0 (nlabel 0 x {pos}) pos y ==>
              (!n. n_posns n y = {})``,
  HO_MATCH_MP_TAC simple_induction THEN REPEAT CONJ_TAC THEN
  SIMP_TAC (srw_ss()) [nlabel_thm] THENL [
    ONCE_REWRITE_TAC [lrcc_cases] THEN SRW_TAC [][beta0_def],
    MAP_EVERY Q.X_GEN_TAC [`f`,`x`] THEN Cases_on `is_abs f` THENL [
      `?v body. f = LAM v body` by PROVE_TAC [is_abs_thm, term_CASES] THEN
      ASM_SIMP_TAC (srw_ss()) [nlabel_thm] THEN STRIP_TAC THEN
      REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      VAR_EQ_TAC THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      ONCE_REWRITE_TAC [lrcc_cases] THENL [
        ASM_SIMP_TAC (srw_ss()) [beta0_LAMi, n_posns_sub,
                                 nlabel_null_labelling,
                                 n_posns_null_labelling, EXTENSION],
        SRW_TAC [][beta0_def, n_posns_def, IMAGE_EQ_EMPTY,
                   nlabel_null_labelling, n_posns_null_labelling] THEN
        RES_TAC THEN SRW_TAC [][]
      ],
      ASM_SIMP_TAC (srw_ss()) [nlabel_thm] THEN
      STRIP_TAC THEN
      ONCE_REWRITE_TAC [lrcc_cases] THEN
      SRW_TAC [][beta0_def, n_posns_def, IMAGE_EQ_EMPTY,
                 nlabel_null_labelling, n_posns_null_labelling] THEN
      RES_TAC THEN SRW_TAC [][]
    ],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SRW_TAC [][lrcc_beta0_LAM] THEN
    SRW_TAC [][n_posns_def, IMAGE_EQ_EMPTY] THEN
    PROVE_TAC []
  ]);

val lemma11_2_28i = store_thm(
  "lemma11_2_28i",
  ``RTC (compat_closure beta) = TC fd_grandbeta``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN CONJ_TAC THENL [
      (* TC fd_grandbeta is reflexive *)
      Q.X_GEN_TAC `x` THEN
      Q.ISPEC_THEN `fd_grandbeta` (MATCH_MP_TAC o CONJUNCT1)
                   relationTheory.TC_RULES THEN
      SRW_TAC [][fd_grandbeta_def] THEN Q.EXISTS_TAC `{}` THEN
      SRW_TAC [][term_posset_cpl_def, redexes_all_occur_def] THEN
      Q.ABBREV_TAC `x' = nlabel 0 x {}` THEN
      `RTC (lcompat_closure beta0) x' x'`
         by PROVE_TAC [relationTheory.RTC_RULES] THEN
      `!n. n_posns n x' = {}` by PROVE_TAC [INTER_EMPTY,
                                            n_posns_nlabel] THEN
      `!y'. ~lcompat_closure beta0 x' y'`
         by PROVE_TAC [NOT_IN_EMPTY, lrcc_lcompat_closure,
                       beta0_n_posns] THEN
      `Cpl x' = x'` by PROVE_TAC [lterm_cpl_unique] THEN
      SRW_TAC [][strip_label_nlabel, Abbr`x'`],
      MAP_EVERY Q.X_GEN_TAC [`x`,`y`,`z`] THEN REPEAT STRIP_TAC THEN
      Q.ISPEC_THEN `fd_grandbeta` (MATCH_MP_TAC o CONJUNCT2)
                   relationTheory.TC_RULES THEN
      Q.EXISTS_TAC `y` THEN SRW_TAC [][] THEN
      Q.ISPEC_THEN `fd_grandbeta` (MATCH_MP_TAC o CONJUNCT1)
                   relationTheory.TC_RULES THEN
      SRW_TAC [][fd_grandbeta_def, term_posset_cpl_def] THEN
      IMP_RES_TAC cc_labelled_redn THEN
      Q.EXISTS_TAC `{pos}` THEN
      Q.ABBREV_TAC `M' = nlabel 0 x {pos}` THEN
      Q.ABBREV_TAC `N' = lift_redn M' pos y` THEN
      `lrcc (beta0 RUNION beta1) M' pos N' /\ (y = strip_label N')` by
          METIS_TAC [lift_redn_def, strip_label_nlabel] THEN
      `pos IN redex_posns x`
         by (SRW_TAC [][redex_posns_redex_occurrence,
                        is_redex_occurrence_def] THEN PROVE_TAC []) THEN
      `pos IN n_posns 0 M'` by SRW_TAC [][n_posns_nlabel, Abbr`M'`] THEN
      `lrcc beta0 M' pos N'` by PROVE_TAC [pick_a_beta] THEN
      `!n. n_posns n N' = {}` by PROVE_TAC [beta0_reduce_at_single_label] THEN
      `RTC (lcompat_closure beta0) M' N'`
         by PROVE_TAC [relationTheory.RTC_RULES, lrcc_lcompat_closure] THEN
      `!N''. ~lcompat_closure beta0 N' N''`
         by PROVE_TAC [NOT_IN_EMPTY, lrcc_lcompat_closure,
                       beta0_n_posns] THEN
      `Cpl M' = N'` by PROVE_TAC [lterm_cpl_unique] THEN
      SRW_TAC [][strip_label_nlabel, redexes_all_occur_def,
                 IN_term_IN_redex_posns]
    ],
    HO_MATCH_MP_TAC relationTheory.TC_INDUCT THEN CONJ_TAC THENL [
      MAP_EVERY Q.X_GEN_TAC [`M`, `N`] THEN
      SRW_TAC [][fd_grandbeta_def, term_posset_cpl_def] THEN
      Q.SPEC_THEN `nlabel 0 M FS` STRIP_ASSUME_TAC lterm_cpl_def THEN
      Q.ABBREV_TAC `M' = nlabel 0 M FS` THEN
      `RTC (lcompat_closure beta0 RUNION lcompat_closure beta1) M' (Cpl M')`
         by PROVE_TAC [RUNION_RTC_MONOTONE] THEN
      FULL_SIMP_TAC (srw_ss()) [lcompat_closure_RUNION_distrib] THEN
      `RTC (compat_closure beta) (strip_label M') (strip_label (Cpl M'))` by
        PROVE_TAC [lemma11_1_6ii] THEN
      Q.UNABBREV_TAC `M'` THEN FULL_SIMP_TAC (srw_ss()) [strip_label_nlabel],
      PROVE_TAC [relationTheory.RTC_RTC]
    ]
  ]);

val complete_developments_are_developments = store_thm(
  "complete_developments_are_developments",
  ``!s. s IN complete_development M ps ==> s IN development M ps``,
  SRW_TAC [][complete_development_thm]);

val complete_developments_always_exist = store_thm(
  "complete_developments_always_exist",
  ``!M ps. ps SUBSET M ==> ?s. s IN complete_development M ps``,
  REPEAT STRIP_TAC THEN
  `stopped_at M IN development M ps` by SRW_TAC [][development_thm] THEN
  IMP_RES_TAC corollary11_2_22i THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);


val development_SUBSET = store_thm(
  "development_SUBSET",
  ``!s M FS1 FS2. s IN development M FS1 /\ FS1 SUBSET FS2 /\ FS2 SUBSET M ==>
                  s IN development M FS2``,
  REWRITE_TAC [SPECIFICATION] THEN
  SIMP_TAC (srw_ss()) [term_posset_development_def] THEN
  Q_TAC SUFF_TAC
     `!s FS2. (?FS1. FS1 SUBSET FS2 /\ development0 s FS1) ==>
              development0 s FS2` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC development0_coinduction THEN GEN_TAC THEN
  Q.ISPEC_THEN `s` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [development0_cases]) THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    PROVE_TAC [SUBSET_DEF],
    `?FS'. FS2 = FS1 UNION FS'`
       by (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, EXTENSION] THEN
           PROVE_TAC []) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [residual1_pointwise_union] THEN
    PROVE_TAC [SUBSET_UNION]
  ]);

val redex_occurrences_SUBSET = store_thm(
  "redex_occurrences_SUBSET",
  ``!s M. s SUBSET M <=> s SUBSET (redex_posns M)``,
  SRW_TAC [][redexes_all_occur_def, IN_term_IN_redex_posns, SUBSET_DEF]);

val linking_developments = store_thm(
  "linking_developments",
  ``!s t M FS.
       s IN development M FS /\ finite s /\
       t IN development (last s) (residuals s FS) ==>
       (plink s t) IN development M FS``,
  SRW_TAC [][lemma11_2_12, first_plink, okpath_plink,
             lift_path_plink, okpath_plink, first_lift_path,
             finite_lift_path] THEN
  Q_TAC SUFF_TAC `last (lift_path (nlabel 0 (first s) FS) s) =
                  nlabel 0 (first t) (residuals s FS)` THEN1 PROVE_TAC [] THEN
  PROVE_TAC [residuals_def]);

val wf_development = store_thm(
  "wf_development",
  ``!M FS s. s IN development M FS ==> (first s = M) /\ FS SUBSET M``,
  SRW_TAC [][term_posset_development_def, SPECIFICATION]);

val lemma11_2_28ii = store_thm(
  "lemma11_2_28ii",
  ``diamond_property fd_grandbeta``,
  Q_TAC SUFF_TAC
        `!M M1 M2. fd_grandbeta M M1 /\ fd_grandbeta M M2 ==>
                   ?N. fd_grandbeta M1 N /\ fd_grandbeta M2 N`
        THEN1 SRW_TAC [][diamond_property_def] THEN
  REPEAT STRIP_TAC THEN
  `?FS1 FS2. (M1 = Cpl(M, FS1)) /\ (M2 = Cpl(M, FS2)) /\ FS1 SUBSET M /\
             FS2 SUBSET M` by
      PROVE_TAC [fd_grandbeta_def] THEN
  `(FS1 UNION FS2) SUBSET M` by
      FULL_SIMP_TAC (srw_ss()) [redex_occurrences_SUBSET] THEN
  `?s1 s2. s1 IN complete_development M FS1 /\ (last s1 = M1) /\
           s2 IN complete_development M FS2 /\ (last s2 = M2)`
      by METIS_TAC [complete_developments_always_exist,
                    Cpl_complete_development] THEN
  `finite s1 /\ okpath (labelled_redn beta) s1 /\
   finite s2 /\ okpath (labelled_redn beta) s2`
      by PROVE_TAC [complete_development_thm, lemma11_2_12] THEN
  `residuals s1 FS2 SUBSET M1 /\ residuals s2 FS1 SUBSET M2`
      by PROVE_TAC [residuals_def, redex_occurrences_SUBSET] THEN
  `?s1' s2'. s1' IN complete_development M1 (residuals s1 FS2) /\
             s2' IN complete_development M2 (residuals s2 FS1)`
      by PROVE_TAC [complete_developments_always_exist] THEN
  `(residuals s1 FS1 = {}) /\ (residuals s1' (residuals s1 FS2) = {}) /\
   (residuals s2 FS2 = {}) /\ (residuals s2' (residuals s2 FS1) = {})`
      by PROVE_TAC [complete_development_thm] THEN
  `(residuals s1 (FS1 UNION FS2) = residuals s1 FS2) /\
   (residuals s2 (FS1 UNION FS2) = residuals s2 FS1)`
      by SRW_TAC [][residuals_pointwise_union] THEN
  `plink s1 s1' IN development M (FS1 UNION FS2) /\
   plink s2 s2' IN development M (FS1 UNION FS2)`
      by PROVE_TAC [linking_developments, development_SUBSET,
                    SUBSET_UNION,
                    complete_developments_are_developments] THEN
  `(first s1' = last s1) /\ (first s2' = last s2) /\ finite s1' /\ finite s2'`
      by PROVE_TAC [complete_development_thm, wf_development] THEN
  `okpath (labelled_redn beta) s1' /\ okpath (labelled_redn beta) s2'`
      by PROVE_TAC [lemma11_2_12, complete_developments_are_developments] THEN
  `(residuals (plink s1 s1') (FS1 UNION FS2) = {}) /\
   (residuals (plink s2 s2') (FS1 UNION FS2) = {})`
      by SRW_TAC [][lemma11_2_6] THEN
  `(plink s1 s1') IN complete_development M (FS1 UNION FS2) /\
   (plink s2 s2') IN complete_development M (FS1 UNION FS2)`
      by PROVE_TAC [complete_development_thm, finite_plink] THEN
  `(last s1' = Cpl(M, FS1 UNION FS2)) /\ (last s2' = Cpl(M, FS1 UNION FS2))`
      by PROVE_TAC [Cpl_complete_development, last_plink] THEN
  Q.EXISTS_TAC `Cpl(M, FS1 UNION FS2)` THEN
  SIMP_TAC (srw_ss()) [fd_grandbeta_def] THEN
  CONJ_TAC THENL [
    Q.EXISTS_TAC `residuals s1 FS2`,
    Q.EXISTS_TAC `residuals s2 FS1`
  ] THEN PROVE_TAC [Cpl_complete_development]);

val corollary11_2_29 = store_thm(
  "corollary11_2_29",
  ``CR beta``,
  SRW_TAC [][CR_def, lemma11_2_28i, lemma11_2_28ii,
             relationTheory.diamond_TC_diamond]);

val _ = export_theory();
