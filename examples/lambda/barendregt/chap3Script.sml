open HolKernel Parse boolLib bossLib;

open boolSimps metisLib basic_swapTheory relationTheory listTheory hurdUtils;

local open pred_setLib in end;

open binderLib BasicProvers nomsetTheory termTheory chap2Theory appFOLDLTheory;
open horeductionTheory

val _ = new_theory "chap3";

val SUBSET_DEF = pred_setTheory.SUBSET_DEF

(* definition from p30 *)
val beta_def = Define`beta M N = ?x body arg. (M = LAM x body @@ arg) /\
                                              (N = [arg/x]body)`;
val _ = Unicode.unicode_version {u = UnicodeChars.beta, tmnm = "beta"}

val beta_alt = store_thm(
  "beta_alt",
  ``!X M N. FINITE X ==>
            (beta M N = ?x body arg. (M = LAM x body @@ arg) /\
                                     (N = [arg/x] body) /\
                                     ~(x IN X))``,
  SRW_TAC [][beta_def, EQ_IMP_THM] THENL [
    SRW_TAC [][LAM_eq_thm] THEN
    Q_TAC (NEW_TAC "z") `x INSERT FV body UNION X` THEN
    MAP_EVERY Q.EXISTS_TAC [`z`, `tpm [(x,z)] body`] THEN
    SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `tpm [(x,z)] body = [VAR z/x]body`
          THEN1 SRW_TAC [][lemma15a] THEN
    SRW_TAC [][GSYM fresh_tpm_subst, pmact_flip_args],
    METIS_TAC []
  ]);

val strong_bvc_term_ind = store_thm(
  "strong_bvc_term_ind",
  ``!P fv. (!s x. P (VAR s) x) /\
           (!M N x. (!x. P M x) /\ (!x. P N x) ==> P (M @@ N) x) /\
           (!v x M. ~(v IN fv x) /\ (!x. P M x) ==> P (LAM v M) x) /\
           (!x. FINITE (fv x)) ==>
           !t x. P t x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t p x. P (tpm p t) x` THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN
  Q.ABBREV_TAC `u = lswapstr p v` THEN
  Q.ABBREV_TAC `M = tpm p t` THEN
  Q_TAC (NEW_TAC "z") `u INSERT FV M UNION fv x` THEN
  `LAM u M = LAM z (tpm [(z, u)] M)` by SRW_TAC [][tpm_ALPHA] THEN
  `tpm [(z,u)] M = tpm ((z,u)::p) t`
     by SRW_TAC [][Abbr`M`, GSYM pmact_decompose] THEN
  SRW_TAC [][])

val _ = set_fixity "-b->" (Infix(NONASSOC, 450))
val _ = overload_on("-b->", ``compat_closure beta``)
val _ = set_fixity "-b->*" (Infix(NONASSOC, 450))
val _ = overload_on ("-b->*", ``RTC (-b->)``)

val ubeta_arrow = "-" ^ UnicodeChars.beta ^ "->"
val _ = Unicode.unicode_version {u = ubeta_arrow, tmnm = "-b->"}
val _ = Unicode.unicode_version {u = ubeta_arrow^"*", tmnm = "-b->*"}


Theorem permutative_beta[simp]:
  permutative beta
Proof
  dsimp[permutative_def, beta_def, LAM_eq_thm, PULL_EXISTS, tpm_subst]
QED

Theorem beta_tpm[simp]:
  beta (tpm π M) (tpm π N) ⇔ beta M N
Proof
  metis_tac[permutative_def, permutative_beta, pmact_inverse]
QED

(* slightly strengthened in the beta-case compared to the naive application
   of cc_gen_ind *)
Theorem ccbeta_gen_ind:
  (!v M N X. v NOTIN FV N /\ v NOTIN fv X ==>
             P ((LAM v M) @@ N) ([N/v]M) X) /\
  (!M1 M2 N X. (!X. P M1 M2 X) ==> P (M1 @@ N) (M2 @@ N) X) /\
  (!M N1 N2 X. (!X. P N1 N2 X) ==> P (M @@ N1) (M @@ N2) X) /\
  (!v M1 M2 X. v NOTIN fv X /\ (!X. P M1 M2 X) ==>
               P (LAM v M1) (LAM v M2) X) /\
  (!X. FINITE (fv X)) ==>
  !M N. M -b-> N ==> !X. P M N X
Proof
  STRIP_TAC THEN
  ho_match_mp_tac cc_gen_ind >> qexists ‘fv’ >> simp[] >>
  rw[beta_def] >>
  rename [‘P (LAM u M @@ N) ([N/u] M) X’] >>
  Q_TAC (NEW_TAC "v") ‘u INSERT FV M ∪ fv X ∪ FV N’ >>
  ‘LAM u M = LAM v ([VAR v/u] M)’ by simp[SIMPLE_ALPHA] >>
  ‘[N/u] M = [N/v]([VAR v/u] M)’ by simp[lemma15a]>> simp[]
QED

Theorem ccbeta_ind =
        ccbeta_gen_ind |> SPEC_ALL
                       |> Q.INST [‘fv’ |-> ‘\x. X’, ‘P’ |-> ‘\M N X. P' M N’]
                       |> Q.INST [‘P'’ |-> ‘P’]
                       |> SRULE[] |> Q.GENL [‘P’, ‘X’]

val beta_substitutive = store_thm(
  "beta_substitutive",
  ``substitutive beta``,
  SRW_TAC [][substitutive_def] THEN
  Q.SPEC_THEN `v INSERT FV N` ASSUME_TAC beta_alt THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.EXISTS_TAC `x` THEN SRW_TAC [][SUB_THM, GSYM substitution_lemma]);

val cc_beta_subst = store_thm(
  "cc_beta_subst",
  ``!M N. M -b-> N ==> !P v. [P/v]M -b-> [P/v]N``,
  METIS_TAC [beta_substitutive, compat_closure_substitutive,
             substitutive_def]);

val reduction_beta_subst = store_thm(
  "reduction_beta_subst",
  ``!M N. M -b->* N ==> !P v. [P/v]M -b->* [P/v]N``,
  METIS_TAC [beta_substitutive, reduction_substitutive, substitutive_def]);

val cc_beta_FV_SUBSET = store_thm(
  "cc_beta_FV_SUBSET",
  ``!M N. M -b-> N ==> FV N SUBSET FV M``,
  HO_MATCH_MP_TAC ccbeta_ind THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][SUBSET_DEF, FV_SUB] THEN PROVE_TAC []);

Theorem cc_beta_tpm:
  !M N. M -b-> N ==> !p. tpm p M -b-> tpm p N
Proof
  HO_MATCH_MP_TAC ccbeta_ind THEN qexists ‘{}’ >> SRW_TAC [][tpm_subst] THEN
  METIS_TAC [compat_closure_rules, beta_def]
QED

val cc_beta_tpm_eqn = store_thm(
  "cc_beta_tpm_eqn",
  ``tpm pi M -b-> N <=> M -b-> tpm (REVERSE pi) N``,
  METIS_TAC [pmact_inverse, cc_beta_tpm]);

val cc_beta_thm = store_thm(
  "cc_beta_thm",
  ``(!s t. VAR s -b-> t <=> F) /\
    (!M N P. M @@ N -b-> P <=>
               (?v M0. (M = LAM v M0) /\ (P = [N/v]M0)) \/
               (?M'. (P = M' @@ N) /\ M -b-> M') \/
               (?N'. (P = M @@ N') /\ N -b-> N')) /\
    (!v M N. LAM v M -b-> N <=> ?N0. (N = LAM v N0) /\ M -b-> N0)``,
  REPEAT CONJ_TAC THEN
  SIMP_TAC (srw_ss()) [beta_def, SimpLHS, Once compat_closure_cases] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  SRW_TAC [][] THEN SRW_TAC [][] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    REPEAT (POP_ASSUM MP_TAC) THEN
    Q_TAC SUFF_TAC
          `!v w M N P.
                 (LAM v M = LAM w N) ==>
                 compat_closure beta N P ==>
                 ?M0. (LAM w P = LAM v M0) /\
                      compat_closure beta M M0` THEN1 PROVE_TAC [] THEN
    SRW_TAC [][LAM_eq_thm] THEN Q.EXISTS_TAC `tpm [(v,w)] P` THEN
    SRW_TAC [][pmact_flip_args, cc_beta_tpm_eqn] THEN
    METIS_TAC [cc_beta_FV_SUBSET, SUBSET_DEF],
    PROVE_TAC []
  ]);

val ccbeta_rwt = store_thm(
  "ccbeta_rwt",
  ``(VAR s -b-> N <=> F) /\
    (LAM x M -b-> N <=> ?N0. (N = LAM x N0) /\ M -b-> N0) /\
    (LAM x M @@ N -b-> P <=>
       (?M'. (P = LAM x M' @@ N) /\ M -b-> M') \/
       (?N'. (P = LAM x M @@ N') /\ N -b-> N') \/
       (P = [N/x]M)) /\
    (~is_abs M ==>
      (M @@ N -b-> P <=>
        (?M'. (P = M' @@ N) /\ M -b-> M') \/
        (?N'. (P = M @@ N') /\ N -b-> N')))``,
  SRW_TAC [][cc_beta_thm] THENL [
    SRW_TAC [][EQ_IMP_THM, LAM_eq_thm] THEN SRW_TAC [][] THENL [
      METIS_TAC [fresh_tpm_subst, lemma15a],
      SRW_TAC [boolSimps.DNF_ss][tpm_eqr]
    ],
    Q_TAC SUFF_TAC `!v M'. M <> LAM v M'` THEN1 METIS_TAC[] THEN
    Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

Theorem ccbeta_LAMl_rwt :
    !vs M N. LAMl vs M -b-> N <=> ?M'. N = LAMl vs M' /\ M -b-> M'
Proof
    Induct_on ‘vs’
 >> rw [ccbeta_rwt] (* only one goal left *)
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘M'’ >> art [])
 >> Q.EXISTS_TAC ‘LAMl vs M'’ >> rw []
QED

val beta_normal_form_bnf = store_thm(
  "beta_normal_form_bnf",
  ``normal_form beta = bnf``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, normal_form_def,
                       FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC `!t. ~bnf t ==> can_reduce beta t` THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC nc_INDUCTION2 THEN
    Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THENL [
      PROVE_TAC [can_reduce_rules],
      PROVE_TAC [can_reduce_rules],
      Q_TAC SUFF_TAC `redex beta (t @@ t')` THEN1
            PROVE_TAC [can_reduce_rules] THEN
      SRW_TAC [][redex_def, beta_def] THEN PROVE_TAC [is_abs_thm, term_CASES],
      PROVE_TAC [lemma14a, can_reduce_rules]
    ],
    Q_TAC SUFF_TAC `!t. can_reduce beta t ==> ~bnf t` THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC can_reduce_ind THEN SRW_TAC [][redex_def, beta_def] THEN
    SRW_TAC [][]
  ]);

val nf_of_def = Define`nf_of R M N <=> normal_form R N /\ conversion R M N`;

val prop3_10 = store_thm(
  "prop3_10",
  ``!R M N.
       compat_closure R M N = ?P Q c. one_hole_context c /\ (M = c P) /\
                                      (N = c Q) /\ R P Q``,
  GEN_TAC THEN SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC compat_closure_ind THEN SRW_TAC [][] THENL [
      MAP_EVERY Q.EXISTS_TAC [`M`,`N`,`\x.x`] THEN
      SRW_TAC [][one_hole_context_rules],
      MAP_EVERY Q.EXISTS_TAC [`P`,`Q`,`\t. z @@ c t`] THEN
      SRW_TAC [][one_hole_context_rules],
      MAP_EVERY Q.EXISTS_TAC [`P`,`Q`,`\t. c t @@ z`] THEN
      SRW_TAC [][one_hole_context_rules],
      MAP_EVERY Q.EXISTS_TAC [`P`,`Q`,`\t. LAM v (c t)`] THEN
      SRW_TAC [][one_hole_context_rules]
    ],
    PROVE_TAC [compat_closure_compatible, compatible_def,
               compat_closure_rules]
  ]);

val corollary3_2_1 = store_thm(
  "corollary3_2_1",
  ``!R M. normal_form R M ==> (!N. ~compat_closure R M N) /\
                              (!N. reduction R M N ==> (M = N))``,
  SIMP_TAC (srw_ss()) [normal_form_def] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `!N. ~compat_closure R M N` ASSUME_TAC THENL [
    GEN_TAC THEN POP_ASSUM MP_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC (srw_ss())[] THEN
    MAP_EVERY Q.ID_SPEC_TAC [`N`, `M`] THEN
    HO_MATCH_MP_TAC compat_closure_ind THEN
    PROVE_TAC [can_reduce_rules, redex_def],
    ALL_TAC
  ] THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  PROVE_TAC [RTC_CASES1]);

val bnf_reduction_to_self = store_thm(
  "bnf_reduction_to_self",
  ``bnf M ==> (M -b->* N <=> (N = M))``,
  METIS_TAC [corollary3_2_1, beta_normal_form_bnf, RTC_RULES]);

local open relationTheory
in
val diamond_property_def = save_thm("diamond_property_def", diamond_def)
end
val _ = overload_on("diamond_property", ``relation$diamond``)

(* This is not the same CR as appears in relationTheory. There
     CR R = diamond (RTC R)
   Here,
     CR R = diamond (RTC (compat_closure R))
   In other words, this formulation allows us to write
     CR beta
   rather than having to write
     CR (compat_closure beta)
*)
val CR_def = Define`CR R = diamond_property (reduction R)`;

val theorem3_13 = store_thm(
  "theorem3_13",
  ``!R. CR R ==>
        !M N. conversion R M N ==> ?Z. reduction R M Z /\ reduction R N Z``,
  GEN_TAC THEN STRIP_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  HO_MATCH_MP_TAC equiv_closure_ind THEN REVERSE (SRW_TAC [][]) THEN1
    (`?Z2. reduction R Z Z2 /\ reduction R Z' Z2` by
        PROVE_TAC [CR_def, diamond_property_def] THEN
     PROVE_TAC [reduction_rules]) THEN
  PROVE_TAC [reduction_rules]);

val corollary3_3_1 = store_thm(
  "corollary3_3_1",
  ``!R. CR R ==> (!M N. nf_of R M N ==> reduction R M N) /\
                 (!M N1 N2. nf_of R M N1 /\ nf_of R M N2 ==> (N1 = N2))``,
  SRW_TAC [][nf_of_def] THENL [
    PROVE_TAC [corollary3_2_1, theorem3_13],
    `conversion R N1 N2` by
       (FULL_SIMP_TAC (srw_ss()) [] THEN
        PROVE_TAC [equiv_closure_rules]) THEN
    `?Z. reduction R N1 Z /\ reduction R N2 Z` by
       PROVE_TAC [theorem3_13] THEN
    PROVE_TAC [corollary3_2_1]
  ]);


val diamond_TC = diamond_TC_diamond

val bvc_cases = store_thm(
  "bvc_cases",
  ``!X. FINITE X ==>
        !t. (?s. t = VAR s) \/ (?t1 t2. t = t1 @@ t2) \/
            (?v t0. ~(v IN X) /\ (t = LAM v t0))``,
  SRW_TAC [][] THEN
  Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][LAM_eq_thm] THEN
  SRW_TAC [boolSimps.DNF_ss][] THEN
  SRW_TAC [][Once tpm_eqr] THEN
  Q_TAC (NEW_TAC "z") `v INSERT X UNION FV t0` THEN
  METIS_TAC []);

(* Definition 3.2.3 [1, p60] (one-step parallel beta-reduction) *)
Inductive grandbeta :
[~REFL[simp]:]
  !M. grandbeta M M
[~ABS:]
  !M M' x. grandbeta M M' ==> grandbeta (LAM x M) (LAM x M')
[~APP:]
  !M N M' N'. grandbeta M M' /\ grandbeta N N' ==> grandbeta (M @@ N) (M' @@ N')
[~BETA:]
  !M N M' N' x. grandbeta M M' /\ grandbeta N N' ==>
                grandbeta ((LAM x M) @@ N) ([N'/x] M')
End

val _ = set_fixity "=b=>" (Infix(NONASSOC,450))
val _ = overload_on ("=b=>", ``grandbeta``)
val _ = set_fixity "=b=>*" (Infix(NONASSOC,450))
val _ = overload_on ("=b=>*", ``RTC grandbeta``)

val gbarrow = "=" ^ UnicodeChars.beta ^ "=>"
val _ = Unicode.unicode_version {u = gbarrow, tmnm = "=b=>"}
val _ = Unicode.unicode_version {u = gbarrow ^ "*", tmnm = "=b=>*"}

val grandbeta_bvc_gen_ind = store_thm(
  "grandbeta_bvc_gen_ind",
  ``!P fv.
        (!M x. P M M x) /\
        (!v M1 M2 x. v NOTIN fv x /\ (!x. P M1 M2 x) ==>
                     P (LAM v M1) (LAM v M2) x) /\
        (!M1 M2 N1 N2 x. (!x. P M1 M2 x) /\ (!x. P N1 N2 x) ==>
                         P (M1 @@ N1) (M2 @@ N2) x) /\
        (!M1 M2 N1 N2 v x.
                  v NOTIN fv x /\ v NOTIN FV N1 /\ v NOTIN FV N2 /\
                  (!x. P M1 M2 x) /\ (!x. P N1 N2 x) ==>
                  P ((LAM v M1) @@ N1) ([N2/v]M2) x) /\
        (!x. FINITE (fv x)) ==>
        !M N. M =b=> N ==> !x. P M N x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M N. grandbeta M N ==> !p x. P (tpm p M) (tpm p N) x`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC grandbeta_ind THEN SRW_TAC [][] THENL [
    Q.ABBREV_TAC `M' = tpm p M` THEN
    Q.ABBREV_TAC `N' = tpm p N` THEN
    Q.ABBREV_TAC `v = lswapstr p x` THEN
    Q_TAC (NEW_TAC "z") `v INSERT fv x' UNION FV M' UNION FV N'` THEN
    `(LAM v M' = LAM z (tpm ((z,v)::p) M)) /\
     (LAM v N' = LAM z (tpm ((z,v)::p) N))`
       by (ONCE_REWRITE_TAC [tpm_CONS] THEN
           SRW_TAC [][Abbr`M'`, Abbr`N'`, tpm_ALPHA]) THEN
    SRW_TAC [][],
    Q.MATCH_ABBREV_TAC `P (LAM (lswapstr p v0) (tpm p ML) @@ tpm p MR)
                          (tpm p ([NR/v0] NL)) ctx`  THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    SRW_TAC [][tpm_subst] THEN
    Q.ABBREV_TAC `v = lswapstr p v0` THEN
    Q.ABBREV_TAC `M1 = tpm p ML` THEN
    Q.ABBREV_TAC `N1 = tpm p MR` THEN
    Q.ABBREV_TAC `M2 = tpm p NL` THEN
    Q.ABBREV_TAC `N2 = tpm p NR` THEN
    Q_TAC (NEW_TAC "z")
          `v INSERT fv ctx UNION FV N1 UNION FV N2 UNION FV M1 UNION
           FV M2` THEN
    `LAM v M1 = LAM z (tpm [(z,v)] M1)` by SRW_TAC [][tpm_ALPHA] THEN
    `[N2/v]M2 = [N2/z](tpm [(z,v)] M2)`
       by SRW_TAC [][fresh_tpm_subst, lemma15a] THEN
    SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SRW_TAC [][Abbr`N1`,Abbr`N2`] THEN
    `(tpm [(z,v)] M1 = tpm ((z,v)::p) ML) /\
     (tpm [(z,v)] M2 = tpm ((z,v)::p) NL)`
        by SRW_TAC [][GSYM pmact_decompose, Abbr`M1`,Abbr`M2`] THEN
    SRW_TAC [][]
  ]);

val grandbeta_bvc_ind = save_thm(
  "grandbeta_bvc_ind",
  (Q.GEN `P` o Q.GEN `X` o
   SIMP_RULE bool_ss [] o
   SPECL [``(\M:term N:term x:'a. P M N:bool)``, ``\x:'a. X:string -> bool``])
  grandbeta_bvc_gen_ind);

val exercise3_3_1 = store_thm(
  "exercise3_3_1",
  ``!M N. M -b-> N ==> M =b=> N``,
  HO_MATCH_MP_TAC compat_closure_ind THEN SRW_TAC [][beta_def] THEN
  PROVE_TAC [grandbeta_rules]);

val app_grandbeta = store_thm(  (* property 3 on p. 37 *)
  "app_grandbeta",
  ``!M N L. M @@ N =b=> L <=>
               (?M' N'. M =b=> M' /\ N =b=> N' /\ (L = M' @@ N')) \/
               (?x P P' N'. (M = LAM x P) /\ P =b=> P' /\
                            N =b=> N' /\ (L = [N'/x]P'))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    SIMP_TAC (srw_ss()) [SimpL ``(==>)``, Once grandbeta_cases] THEN
    SIMP_TAC (srw_ss()) [DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM,
                         grandbeta_rules] THEN PROVE_TAC [],
    SRW_TAC [][] THEN PROVE_TAC [grandbeta_rules]
  ]);

val grandbeta_permutative = store_thm(
  "grandbeta_permutative",
  ``!M N. M =b=> N ==> !pi. tpm pi M =b=> tpm pi N``,
  HO_MATCH_MP_TAC grandbeta_ind THEN SRW_TAC [][tpm_subst] THEN
  METIS_TAC [grandbeta_rules]);

val grandbeta_permutative_eqn = store_thm(
  "grandbeta_permutative_eqn",
  ``tpm pi M =b=> tpm pi N  <=>  M =b=> N``,
  METIS_TAC [pmact_inverse, grandbeta_permutative]);
val _ = export_rewrites ["grandbeta_permutative_eqn"]

val grandbeta_substitutive = store_thm(
  "grandbeta_substitutive",
  ``!M N. M =b=> N ==> [P/x]M =b=> [P/x]N``,
  HO_MATCH_MP_TAC grandbeta_bvc_ind THEN
  Q.EXISTS_TAC `x INSERT FV P` THEN
  SRW_TAC [][SUB_THM, grandbeta_rules] THEN
  SRW_TAC [][lemma2_11, grandbeta_rules]);

val grandbeta_FV = store_thm(
  "grandbeta_FV",
  ``!M N. M =b=> N ==> FV N SUBSET FV M``,
  HO_MATCH_MP_TAC grandbeta_ind THEN
  SRW_TAC [][SUBSET_DEF, FV_SUB] THEN
  PROVE_TAC []);

val abs_grandbeta = store_thm(
  "abs_grandbeta",
  ``!M N v. LAM v M =b=> N <=> ∃N0. N = LAM v N0 /\ M =b=> N0``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    SIMP_TAC (srw_ss()) [Once grandbeta_cases, SimpL ``(==>)``] THEN
    SIMP_TAC (srw_ss()) [DISJ_IMP_THM, grandbeta_rules] THEN
    SRW_TAC [][LAM_eq_thm] THENL [
      PROVE_TAC [],
      SRW_TAC [][LAM_eq_thm, tpm_eqr, pmact_flip_args] THEN
      PROVE_TAC [SUBSET_DEF, grandbeta_FV]
    ],
    PROVE_TAC [grandbeta_rules]
  ]);

val lemma3_15 = save_thm("lemma3_15", abs_grandbeta);

val redex_grandbeta = store_thm(
  "redex_grandbeta",
  ``LAM v M @@ N =b=> L <=>
        (∃M' N'. M =b=> M' /\ N =b=> N' /\
                 (L = LAM v M' @@ N')) \/
        (∃M' N'. M =b=> M' /\ N =b=> N' /\ (L = [N'/v]M'))``,
  SRW_TAC [][app_grandbeta, EQ_IMP_THM] THENL [
    PROVE_TAC [abs_grandbeta],
    FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm] THEN DISJ2_TAC THENL [
      METIS_TAC [],
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`tpm [(v,x)] P'`, `N'`] THEN
      SRW_TAC [][] THEN
      `v NOTIN FV P'`
        by METIS_TAC [grandbeta_FV, SUBSET_DEF] THEN
      SRW_TAC [][fresh_tpm_subst, lemma15a]
    ],
    METIS_TAC [grandbeta_rules],
    METIS_TAC []
  ]);

val var_grandbeta = store_thm(
  "var_grandbeta",
  ``!v N. VAR v =b=> N <=> (N = VAR v)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [grandbeta_cases] THEN
  SRW_TAC [][]);

val grandbeta_cosubstitutive = store_thm(
  "grandbeta_cosubstitutive",
  ``!M. N =b=> N' ==> [N/x] M =b=> [N'/x] M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `x INSERT FV N UNION FV N'` THEN
  SRW_TAC [][grandbeta_rules, SUB_VAR]);

(* property 1 on p37, and Barendregt's lemma 3.2.4 *)
val grandbeta_subst = store_thm(
  "grandbeta_subst",
  ``M =b=> M' /\ N =b=> N' ==> [N/x]M =b=> [N'/x]M'``,
  Q_TAC SUFF_TAC
        `!M M'. M =b=> M' ==> N =b=> N' ==>
                [N/x] M =b=> [N'/x]M'` THEN1
        METIS_TAC [] THEN
  HO_MATCH_MP_TAC grandbeta_bvc_ind THEN
  Q.EXISTS_TAC `x INSERT FV N UNION FV N'` THEN
  SRW_TAC [][SUB_THM, grandbeta_rules] THENL [
    METIS_TAC [grandbeta_cosubstitutive],
    RES_TAC THEN
    SRW_TAC [][lemma2_11, grandbeta_rules]
  ]);

val strong_grandbeta_ind =
    IndDefLib.derive_strong_induction (grandbeta_rules, grandbeta_ind)

val strong_grandbeta_bvc_gen_ind =
    (GEN_ALL o
     SIMP_RULE (srw_ss()) [grandbeta_rules, FORALL_AND_THM,
                           GSYM CONJ_ASSOC] o
     Q.SPEC `\M N x. P M N x /\ grandbeta M N`)
    grandbeta_bvc_gen_ind

val lemma3_16 = store_thm( (* p. 37 *)
  "lemma3_16",
  ``diamond_property grandbeta``,
  Q_TAC SUFF_TAC `!M M1. M =b=> M1 ==>
                         !M2. M =b=> M2 ==>
                              ?M3. M1 =b=> M3 /\ M2 =b=> M3` THEN1
    PROVE_TAC [diamond_property_def] THEN
  HO_MATCH_MP_TAC strong_grandbeta_bvc_gen_ind THEN Q.EXISTS_TAC `FV` THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT CONJ_TAC THENL [
    (* reflexive case *)
    PROVE_TAC [grandbeta_rules],
    (* lambda case *)
    MAP_EVERY Q.X_GEN_TAC [`v`, `M`,`M1`, `M2`] THEN REPEAT STRIP_TAC THEN
    `?P. (M2 = LAM v P) /\ M =b=> P` by PROVE_TAC [abs_grandbeta] THEN
    SRW_TAC [][] THEN PROVE_TAC [grandbeta_rules],
    (* app case *)
    MAP_EVERY Q.X_GEN_TAC [`f`,`g`,`x`,`y`, `fx'`] THEN STRIP_TAC THEN
    STRIP_TAC THEN
    `(?f' x'. (fx' = f' @@ x') /\ f =b=> f' /\ x =b=> x') \/
     (?v P P' x'. (f = LAM v P) /\ P =b=> P' /\ x =b=> x' /\
                  (fx' = [x'/v]P'))` by
        (FULL_SIMP_TAC (srw_ss()) [app_grandbeta] THEN PROVE_TAC [])
    THENL [
      METIS_TAC [grandbeta_rules],
      `?P2. (g = LAM v P2) /\ P =b=> P2` by
          PROVE_TAC [abs_grandbeta] THEN
      SRW_TAC [][] THEN
      `?ff. LAM v P2 =b=> ff /\ LAM v P' =b=> ff` by
         PROVE_TAC [grandbeta_rules] THEN
      `?xx. y =b=> xx /\ x' =b=> xx` by PROVE_TAC [] THEN
      `?PP. P' =b=> PP /\ (ff = LAM v PP)` by
         PROVE_TAC [abs_grandbeta] THEN
      SRW_TAC [][] THEN
      `P2 =b=> PP` by PROVE_TAC [abs_grandbeta, term_11] THEN
      PROVE_TAC [grandbeta_rules, grandbeta_subst]
    ],
    (* beta-redex case *)
    MAP_EVERY Q.X_GEN_TAC [`M`, `M'`, `N`, `N'`, `x`, `M2`] THEN
    SRW_TAC [][redex_grandbeta] THENL [
      (* other reduction didn't beta-reduce *)
      `?Mfin. M' =b=> Mfin /\ M'' =b=> Mfin` by METIS_TAC [] THEN
      `?Nfin. N' =b=> Nfin /\ N'' =b=> Nfin` by METIS_TAC [] THEN
      Q.EXISTS_TAC `[Nfin/x]Mfin` THEN
      METIS_TAC [grandbeta_rules, grandbeta_subst],
      (* other reduction also beta-reduced *)
      `?Mfin. M' =b=> Mfin /\ M'' =b=> Mfin` by METIS_TAC [] THEN
      `?Nfin. N' =b=> Nfin /\ N'' =b=> Nfin` by METIS_TAC [] THEN
      Q.EXISTS_TAC `[Nfin/x]Mfin` THEN
      METIS_TAC [grandbeta_rules, grandbeta_subst]
    ]
  ]);

Theorem theorem3_17:
  TC grandbeta = reduction beta
Proof
  ‘RTC grandbeta = reduction beta’ suffices_by
    (disch_then (simp o single o GSYM) >> simp[cj 1 $ GSYM TC_RC_EQNS] >>
     simp[FUN_EQ_THM, RC_DEF, EQ_IMP_THM, DISJ_IMP_THM] >>
     metis_tac[reflexive_TC, reflexive_def, grandbeta_rules]) >>
  irule RTC_BRACKETS_RTC_EQN >> conj_tac >~
  [‘_ -β-> _ ⇒ _’] >- metis_tac[exercise3_3_1] >>
  Induct_on ‘grandbeta’ >> metis_tac[reduction_rules, beta_def]
QED

Theorem RTC_grandbeta:
  RTC grandbeta = reduction beta
Proof
  simp[GSYM TC_RC_EQNS, theorem3_17]
QED

val beta_CR = store_thm(
  "beta_CR",
  ``CR beta``,
  PROVE_TAC [CR_def, lemma3_16, theorem3_17, diamond_TC]);

val betaCR_square = store_thm(
  "betaCR_square",
  ``M -b->* N1 /\ M -b->* N2 ==> ?N. N1 -b->* N /\ N2 -b->* N``,
  METIS_TAC [beta_CR, diamond_property_def, CR_def]);

val bnf_triangle = store_thm(
  "bnf_triangle",
  ``M -b->* N /\ M -b->* N' /\ bnf N ==> N' -b->* N``,
  METIS_TAC [betaCR_square, bnf_reduction_to_self]);

Theorem Omega_betaloops[simp] :
    Omega -b-> N <=> N = Omega
Proof
    FULL_SIMP_TAC (srw_ss()) [ccbeta_rwt, Omega_def]
QED

Theorem Omega_starloops[simp] :
    Omega -b->* N <=> N = Omega
Proof
    Suff ‘!M N. M -b->* N ==> (M = Omega) ==> (N = Omega)’
 >- METIS_TAC [RTC_RULES]
 >> HO_MATCH_MP_TAC RTC_INDUCT >> SRW_TAC [][]
 >> FULL_SIMP_TAC std_ss [Omega_betaloops]
QED

Theorem Omega_app_betaloops[local] :
    Omega @@ A -b-> N ==> ?A'. N = Omega @@ A'
Proof
    ‘~is_abs Omega’ by rw [Omega_def]
 >> rw [ccbeta_rwt]
 >- (Q.EXISTS_TAC ‘A’ >> rw [])
 >> Q.EXISTS_TAC ‘N'’ >> rw []
QED

Theorem Omega_app_starloops :
    Omega @@ A -β->* N ⇒ ∃A'. N = Omega @@ A'
Proof
    Suff ‘!M N. M -b->* N ==> !A. M = Omega @@ A ==> ?A'. N = Omega @@ A'’
 >- METIS_TAC [RTC_RULES]
 >> HO_MATCH_MP_TAC RTC_INDUCT >> SRW_TAC [][]
 >> ‘?A'. M' = Omega @@ A'’ by METIS_TAC [Omega_app_betaloops]
 >> Q.PAT_X_ASSUM ‘!A. M' = Omega @@ A ==> P’ (MP_TAC o (Q.SPEC ‘A'’))
 >> RW_TAC std_ss []
QED

Theorem Omega_appstar_betaloops[local] :
    !N. Omega @* Ms -b-> N ==> ?Ms'. N = Omega @* Ms'
Proof
    Induct_on ‘Ms’ using SNOC_INDUCT
 >- (rw [] >> Q.EXISTS_TAC ‘[]’ >> rw [])
 >> rw [appstar_SNOC]
 >> ‘~is_abs (Omega @* Ms)’ by rw [Omega_def]
 >> fs [ccbeta_rwt]
 >- (Q.PAT_X_ASSUM ‘!N. P’ (MP_TAC o (Q.SPEC ‘M'’)) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘SNOC x Ms'’ >> rw [])
 >> Q.EXISTS_TAC ‘SNOC N' Ms’ >> rw []
QED

Theorem Omega_appstar_starloops :
    Omega @* Ms -b->* N ==> ?Ms'. N = Omega @* Ms'
Proof
    Suff ‘!M N. M -b->* N ==> !Ms. M = Omega @* Ms ==> ?Ms'. N = Omega @* Ms'’
 >- METIS_TAC [RTC_RULES]
 >> HO_MATCH_MP_TAC RTC_INDUCT >> SRW_TAC [][]
 >- (Q.EXISTS_TAC ‘Ms’ >> rw [])
 >> ‘?Ms'. M' = Omega @* Ms'’ by METIS_TAC [Omega_appstar_betaloops]
 >> Q.PAT_X_ASSUM ‘!Ms. M' = Omega @* Ms ==> P’ (MP_TAC o (Q.SPEC ‘Ms'’))
 >> RW_TAC std_ss []
QED

val lameq_betaconversion = store_thm(
  "lameq_betaconversion",
  ``!M N. M == N <=> conversion beta M N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC lameq_ind THEN REPEAT STRIP_TAC THENL [
      Q_TAC SUFF_TAC `beta (LAM x M @@ N) ([N/x] M)` THEN1
        PROVE_TAC [conversion_rules] THEN
      SRW_TAC [][beta_def] THEN PROVE_TAC [],
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_compatible, compatible_def, rightctxt,
                 rightctxt_thm],
      PROVE_TAC [conversion_compatible, compatible_def, leftctxt],
      PROVE_TAC [conversion_compatible, compatible_def, absctxt]
    ],
    SIMP_TAC (srw_ss()) [] THEN
    HO_MATCH_MP_TAC equiv_closure_ind THEN REPEAT CONJ_TAC THEN1
      (HO_MATCH_MP_TAC compat_closure_ind THEN SRW_TAC [][beta_def] THEN
       PROVE_TAC [lameq_rules]) THEN
    PROVE_TAC [lameq_rules]
  ]);

val prop3_18 = save_thm("prop3_18", lameq_betaconversion);

(* |- !M N. M == N ==> ?Z. M -b->* Z /\ N -b->* Z *)
Theorem lameq_CR = REWRITE_RULE [GSYM lameq_betaconversion, beta_CR]
                                (Q.SPEC ‘beta’ theorem3_13)

val ccbeta_lameq = store_thm(
  "ccbeta_lameq",
  ``!M N. M -b-> N ==> M == N``,
  SRW_TAC [][lameq_betaconversion, EQC_R]);

val betastar_lameq = store_thm(
  "betastar_lameq",
  ``!M N. M -b->* N ==> M == N``,
  SRW_TAC [][lameq_betaconversion, RTC_EQC]);

val betastar_lameq_bnf = store_thm(
  "betastar_lameq_bnf",
  ``bnf N ==> (M -b->* N <=> M == N)``,
  METIS_TAC [theorem3_13, beta_CR, betastar_lameq, bnf_reduction_to_self,
             lameq_betaconversion]);

(* moved here from churchnumScript.sml *)
Theorem lameq_triangle :
    M == N ∧ M == P ∧ bnf N ∧ bnf P ⇒ (N = P)
Proof
  METIS_TAC [betastar_lameq_bnf, lameq_rules, bnf_reduction_to_self]
QED

(* |- !M N. M =b=> N ==> M -b->* N *)
Theorem grandbeta_imp_betastar =
    (REWRITE_RULE [theorem3_17] (Q.ISPEC ‘grandbeta’ TC_SUBSET))
 |> (Q.SPECL [‘M’, ‘N’]) |> (Q.GENL [‘M’, ‘N’])

Theorem grandbeta_imp_lameq :
    !M N. M =b=> N ==> M == N
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC betastar_lameq
 >> MATCH_MP_TAC grandbeta_imp_betastar >> art []
QED

(* |- !R x y z. R^+ x y /\ R^+ y z ==> R^+ x z *)
Theorem TC_TRANS[local] = REWRITE_RULE [transitive_def] TC_TRANSITIVE

Theorem abs_betastar :
    !x M Z. LAM x M -b->* Z <=> ?N'. (Z = LAM x N') /\ M -b->* N'
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- (rw [] >> PROVE_TAC [reduction_rules])
 (* stage work *)
 >> REWRITE_TAC [SYM theorem3_17]
 >> Q.ID_SPEC_TAC ‘Z’
 >> HO_MATCH_MP_TAC (Q.ISPEC ‘grandbeta’ TC_INDUCT_ALT_RIGHT)
 >> rpt STRIP_TAC
 >- (FULL_SIMP_TAC std_ss [abs_grandbeta] \\
     Q.EXISTS_TAC ‘N0’ >> art [] \\
     MATCH_MP_TAC TC_SUBSET >> art [])
 >> Q.PAT_X_ASSUM ‘Z = LAM x N'’ (FULL_SIMP_TAC std_ss o wrap)
 >> FULL_SIMP_TAC std_ss [abs_grandbeta]
 >> Q.EXISTS_TAC ‘N0’ >> art []
 >> MATCH_MP_TAC TC_TRANS
 >> Q.EXISTS_TAC ‘N'’ >> art []
 >> MATCH_MP_TAC TC_SUBSET >> art []
QED

val lameq_consistent = store_thm(
  "lameq_consistent",
  ``consistent $==``,
  SRW_TAC [][consistent_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`S`,`K`] THEN STRIP_TAC THEN
  `conversion beta S K` by PROVE_TAC [prop3_18] THEN
  `?Z. reduction beta S Z /\ reduction beta K Z` by
     PROVE_TAC [theorem3_13, beta_CR] THEN
  `normal_form beta S` by PROVE_TAC [S_beta_normal, beta_normal_form_bnf] THEN
  `normal_form beta K` by PROVE_TAC [K_beta_normal, beta_normal_form_bnf] THEN
  `S = K` by PROVE_TAC [corollary3_2_1] THEN
  FULL_SIMP_TAC (srw_ss()) [S_def, K_def]);

val has_bnf_thm = store_thm(
  "has_bnf_thm",
  ``has_bnf M <=> ?N. M -b->* N /\ bnf N``,
  EQ_TAC THENL [
    METIS_TAC [lameq_betaconversion, chap2Theory.has_bnf_def, theorem3_13,
               beta_CR, beta_normal_form_bnf, corollary3_2_1],
    SRW_TAC [][chap2Theory.has_bnf_def, lameq_betaconversion] THEN
    METIS_TAC [RTC_EQC]
  ]);

val Omega_reachable_no_bnf = store_thm(
  "Omega_reachable_no_bnf",
  ``M -b->* Omega ==> ~has_bnf M``,
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [has_bnf_thm] THEN
  `Omega -b->* N` by METIS_TAC [bnf_triangle] THEN
  `N = Omega` by FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val weak_diamond_def =
    save_thm("weak_diamond_def", WCR_def)
val _ = overload_on("weak_diamond", ``relation$WCR``)

(* likewise, these definitions of WCR and SN, differ from those in
   relation by wrapping the argument in a call to compat_closure
*)
val WCR_def = (* definition 3.20, p39 *) Define`
  WCR R = weak_diamond (compat_closure R)
`;

val SN_def = Define`SN R = relation$SN (compat_closure R)`;

val newmans_lemma = store_thm( (* lemma3_22, p39 *)
  "newmans_lemma",
  ``!R. SN R /\ WCR R ==> CR R``,
  SIMP_TAC (srw_ss()) [SN_def, WCR_def, Newmans_lemma,
                       CR_def,
                       GSYM relationTheory.diamond_def,
                       GSYM relationTheory.CR_def]);

val commute_def =  (* p43 *)
    Define`commute R1 R2 = !x x1 x2. R1 x x1 /\ R2 x x2 ==>
                                     ?x3. R2 x1 x3 /\ R1 x2 x3`;

val commute_COMM = store_thm(
  "commute_COMM",
  ``commute R1 R2 = commute R2 R1``,
  PROVE_TAC [commute_def]);

val diamond_RC = diamond_RC_diamond
  (* |- !R. diamond_property R ==> diamond_property (RC R) *)

val diamond_RTC = store_thm(
  "diamond_RTC",
  ``!R. diamond_property R ==> diamond_property (RTC R)``,
  PROVE_TAC [diamond_TC, diamond_RC, TC_RC_EQNS]);

val hr_lemma0 = prove(
  ``!R1 R2. diamond_property R1 /\ diamond_property R2 /\ commute R1 R2 ==>
            diamond_property (RTC (R1 RUNION R2))``,
  REPEAT STRIP_TAC THEN
  Q_TAC SUFF_TAC `diamond_property (R1 RUNION R2)` THEN1
        PROVE_TAC [diamond_RTC] THEN
  FULL_SIMP_TAC (srw_ss()) [diamond_property_def, commute_def,
                            RUNION] THEN
  PROVE_TAC []);

val CC_RUNION_MONOTONE = store_thm(
  "CC_RUNION_MONOTONE",
  ``!R1 x y. compat_closure R1 x y ==> compat_closure (R1 RUNION R2) x y``,
  GEN_TAC THEN HO_MATCH_MP_TAC compat_closure_ind THEN
  PROVE_TAC [compat_closure_rules, RUNION]);

val CC_RUNION_DISTRIB = store_thm(
  "CC_RUNION_DISTRIB",
  ``!R1 R2. compat_closure (R1 RUNION R2) =
            compat_closure R1 RUNION compat_closure R2``,
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC
     `(!x y. compat_closure (R1 RUNION R2) x y ==>
             (compat_closure R1 RUNION compat_closure R2) x y) /\
      (!x y. (compat_closure R1 RUNION compat_closure R2) x y ==>
             compat_closure (R1 RUNION R2) x y)` THEN1
     SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC compat_closure_ind THEN
    PROVE_TAC [compat_closure_rules, RUNION],
    SRW_TAC [][RUNION] THEN
    PROVE_TAC [RUNION_COMM, CC_RUNION_MONOTONE]
  ]);

val hindley_rosen_lemma = store_thm( (* p43 *)
  "hindley_rosen_lemma",
  ``(!R1 R2. diamond_property R1 /\ diamond_property R2 /\ commute R1 R2 ==>
             diamond_property (RTC (R1 RUNION R2))) /\
    (!R1 R2. CR R1 /\ CR R2 /\ commute (reduction R1) (reduction R2) ==>
             CR (R1 RUNION R2))``,
  CONJ_TAC THENL [
    MATCH_ACCEPT_TAC hr_lemma0,
    SRW_TAC [][CR_def] THEN
    `diamond_property (RTC (RTC (compat_closure R1) RUNION
                            RTC (compat_closure R2)))`
        by PROVE_TAC [hr_lemma0] THEN
    FULL_SIMP_TAC (srw_ss()) [RTC_RUNION, CC_RUNION_DISTRIB]
  ]);

val eta_def =
    Define`eta M N <=> ∃v. M = LAM v (N @@ VAR v) ∧ v ∉ FV N`;

val _ = Unicode.unicode_version {u = UnicodeChars.eta, tmnm = "eta"}

val eta_normal_form_enf = store_thm(
  "eta_normal_form_enf",
  ``normal_form eta = enf``,
  Q_TAC SUFF_TAC `(!x. ~enf x ==> can_reduce eta x) /\
                  (!x. can_reduce eta x ==> ~enf x)` THEN1
    (SIMP_TAC (srw_ss())[normal_form_def, FUN_EQ_THM, EQ_IMP_THM,
                         FORALL_AND_THM] THEN PROVE_TAC []) THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{}` THEN
    SRW_TAC [][] THENL [
      PROVE_TAC [can_reduce_rules],
      PROVE_TAC [can_reduce_rules],
      PROVE_TAC [can_reduce_rules, lemma14a],
      Q_TAC SUFF_TAC `?u. eta (LAM y x) u` THEN1
            PROVE_TAC [can_reduce_rules, redex_def] THEN
      FULL_SIMP_TAC (srw_ss()) [is_comb_APP_EXISTS, eta_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rand_thm, rator_thm] THEN PROVE_TAC []
    ],
    HO_MATCH_MP_TAC can_reduce_ind THEN
    SRW_TAC [][redex_def, eta_def] THEN
    SRW_TAC [][]
  ]);

val no_eta_thm = store_thm(
  "no_eta_thm",
  ``(!s t. ~(eta (VAR s) t)) /\
    (!t u v. ~(eta (t @@ u) v))``,
  SRW_TAC [][eta_def]);

val cc_eta_thm = store_thm(
  "cc_eta_thm",
  ``(!s t. compat_closure eta (VAR s) t <=> F) /\
    (!t u v. compat_closure eta (t @@ u) v <=>
             (?t'. (v = t' @@ u) /\ compat_closure eta t t') \/
             (?u'. (v = t @@ u') /\ compat_closure eta u u'))``,
  REPEAT CONJ_TAC THEN
  SIMP_TAC (srw_ss()) [SimpLHS, Once compat_closure_cases] THEN
  SIMP_TAC (srw_ss()) [no_eta_thm, EQ_IMP_THM, DISJ_IMP_THM,
                       GSYM LEFT_FORALL_IMP_THM, RIGHT_AND_OVER_OR,
                       LEFT_AND_OVER_OR, FORALL_AND_THM,
                       is_comb_APP_EXISTS, GSYM LEFT_EXISTS_AND_THM]);

val eta_substitutive = store_thm(
  "eta_substitutive",
  ``substitutive eta``,
  SRW_TAC [][substitutive_def, eta_def] THEN
  Q_TAC (NEW_TAC "z") `{v;v'} UNION FV M' UNION FV N` THEN
  `LAM v (M' @@ VAR v) = LAM z ([VAR z/v] (M' @@ VAR v))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN
  ` _ = LAM z ([VAR z/v] M' @@ VAR z)` by SRW_TAC [][SUB_THM] THEN
  ASM_SIMP_TAC (srw_ss()) [SUB_THM, lemma14b] THEN
  Q.EXISTS_TAC `z` THEN SRW_TAC [][FV_SUB]);

val cc_eta_subst = store_thm(
  "cc_eta_subst",
  ``!M N. compat_closure eta M N ==>
          !P v. compat_closure eta ([P/v] M) ([P/v] N)``,
  METIS_TAC [eta_substitutive, compat_closure_substitutive, substitutive_def]);

val cc_eta_tpm = store_thm(
  "cc_eta_tpm",
  ``!M N. compat_closure eta M N ==>
          compat_closure eta (tpm pi M) (tpm pi N)``,
  METIS_TAC [compat_closure_permutative, substitutive_implies_permutative,
             eta_substitutive, permutative_def])
val cc_eta_tpm_eqn = store_thm(
  "cc_eta_tpm_eqn",
  ``compat_closure eta (tpm pi M) N =
    compat_closure eta M (tpm (REVERSE pi) N)``,
  METIS_TAC [cc_eta_tpm, pmact_inverse]);

val eta_deterministic = store_thm(
  "eta_deterministic",
  ``!M N1 N2. eta M N1 /\ eta M N2 ==> (N1 = N2)``,
  SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [eta_def, LAM_eq_thm, tpm_fresh]);

val cc_eta_FV_SUBSET = store_thm(
  "cc_eta_FV_SUBSET",
  ``!M N. compat_closure eta M N ==> FV N SUBSET FV M``,
  HO_MATCH_MP_TAC compat_closure_ind THEN
  SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
  Q_TAC SUFF_TAC `!M N. eta M N ==> !s. s IN FV N ==> s IN FV M` THEN1
        PROVE_TAC [] THEN
  SIMP_TAC (srw_ss()) [eta_def, GSYM LEFT_FORALL_IMP_THM]);

val cc_eta_LAM = store_thm(
  "cc_eta_LAM",
  ``!t v u. compat_closure eta (LAM v t) u <=>
            (?t'. (u = LAM v t') /\ compat_closure eta t t') \/
            eta (LAM v t) u``,
  SIMP_TAC (srw_ss()) [Once compat_closure_cases, SimpLHS] THEN
  SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)[LAM_eq_thm, EQ_IMP_THM, tpm_eqr,
                                          cc_eta_tpm_eqn, pmact_flip_args] THEN
  REPEAT STRIP_TAC THEN DISJ1_TAC THEN
  Q_TAC SUFF_TAC `~(v' IN FV (tpm [(v,v')] y))` THEN1 SRW_TAC [][] THEN
  METIS_TAC [cc_eta_FV_SUBSET, SUBSET_DEF]);

val eta_LAM = store_thm(
  "eta_LAM",
  ``!v t u. eta (LAM v t) u <=> t = u @@ VAR v ∧ v ∉ FV u``,
  SRW_TAC [][eta_def, LAM_eq_thm, EQ_IMP_THM] THEN SRW_TAC [][tpm_fresh] THEN
  SRW_TAC [boolSimps.DNF_ss][]);

val CR_eta_lemma = prove(
  ``!M M1 M2. eta M M1 /\ compat_closure eta M M2 /\ ~(M1 = M2) ==>
              ?M3. compat_closure eta M1 M3 /\ compat_closure eta M2 M3``,
  REPEAT STRIP_TAC THEN
  `?v. (M = LAM v (M1 @@ VAR v)) /\ ~(v IN FV M1)` by PROVE_TAC [eta_def] THEN
  FULL_SIMP_TAC (srw_ss()) [cc_eta_LAM, cc_eta_thm] THENL [
    Q.EXISTS_TAC `rator t'` THEN
    SRW_TAC [][eta_LAM] THEN
    METIS_TAC [cc_eta_FV_SUBSET, SUBSET_DEF],
    FULL_SIMP_TAC (srw_ss()) [eta_LAM]
  ]);

val cc_strong_ind =
    IndDefLib.derive_strong_induction (compat_closure_rules, compat_closure_ind)

val eta_diamond = prove(
  ``!M M1. compat_closure eta M M1 ==>
           !M2. compat_closure eta M M2 /\ ~(M1 = M2) ==>
                ?M3. compat_closure eta M1 M3 /\
                     compat_closure eta M2 M3``,
  HO_MATCH_MP_TAC cc_strong_ind THEN REPEAT CONJ_TAC THENL [
    PROVE_TAC [CR_eta_lemma],

    SRW_TAC [][cc_eta_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [cc_eta_thm],

    SRW_TAC [][cc_eta_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [cc_eta_thm],

    SRW_TAC [][cc_eta_LAM, eta_LAM] THEN
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [cc_eta_LAM, cc_eta_thm] THEN
    METIS_TAC [cc_eta_FV_SUBSET, SUBSET_DEF]
  ]);

val eta_CR = store_thm(
  "eta_CR",
  ``CR eta``,
  Q_TAC SUFF_TAC `diamond_property (RC (compat_closure eta))` THEN1
        (SRW_TAC [][CR_def] THEN
         PROVE_TAC [TC_RC_EQNS, diamond_TC]) THEN
  SIMP_TAC (srw_ss()) [diamond_property_def, RC_DEF,
                       RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM,
                       DISJ_IMP_THM, FORALL_AND_THM] THEN
  PROVE_TAC [eta_diamond]);

val wonky_diamond_commutes = store_thm( (* Barendregt, lemma 3.3.6 *)
  "wonky_diamond_commutes",
  ``!R1 R2.
        (!x y z. R1 x y /\ R2 x z ==> ?w. RTC R1 z w /\ RC R2 y w) ==>
        commute (RTC R1) (RTC R2)``,
  REPEAT STRIP_TAC THEN
  `!x y. RTC R1 x y ==> !z. R2 x z ==> ?w. RTC R1 z w /\ RTC R2 y w` by
      (HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
       CONJ_TAC THENL [
         PROVE_TAC [RTC_RULES],
         MAP_EVERY Q.X_GEN_TAC [`x`,`y`,`z`] THEN REPEAT STRIP_TAC THEN
         `?w. RC R2 y w /\ RTC R1 z' w` by PROVE_TAC [] THEN
         FULL_SIMP_TAC (srw_ss()) [RC_DEF] THEN
         PROVE_TAC [RTC_RTC, RTC_RULES]
       ]) THEN
  Q_TAC SUFF_TAC
        `!x y. RTC R2 x y ==> !z. RTC R1 x z ==>
                                  ?w. RTC R2 z w /\ RTC R1 y w` THEN1
        (SRW_TAC [][commute_def] THEN PROVE_TAC []) THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN
  PROVE_TAC [RTC_RULES, RTC_RTC]);

val eta_cosubstitutive = store_thm(
  "eta_cosubstitutive",
  ``!P M N x. compat_closure eta M N ==> reduction eta ([M/x] P) ([N/x] P)``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `P` THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `x INSERT FV M UNION FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THEN
  PROVE_TAC [reduction_rules]);

val ccredex = prove(
  ``compat_closure beta (LAM v M @@ N) ([N/v]M)``,
  SRW_TAC [][cc_beta_thm] THEN METIS_TAC [])

val strong_ccbeta_gen_ind = save_thm(
  "strong_ccbeta_gen_ind",
    (GEN_ALL o
     SIMP_RULE (srw_ss() ++ SatisfySimps.SATISFY_ss)
               [compat_closure_rules, FORALL_AND_THM, ccredex,
                GSYM CONJ_ASSOC] o
     Q.INST [`P` |-> `\M N x. P M N x /\ compat_closure beta M N`])
    ccbeta_gen_ind)

val eta_beta_commute = store_thm(
  "eta_beta_commute",
  ``commute (reduction eta) (reduction beta)``,
  SIMP_TAC (srw_ss()) [] THEN
  MATCH_MP_TAC wonky_diamond_commutes THEN
  Q_TAC SUFF_TAC
        `!M P. M -b-> P ==>
               !N. compat_closure eta M N ==>
                   ?Q. reduction eta P Q /\ RC (-b->) N Q`
        THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC strong_ccbeta_gen_ind THEN
  Q.EXISTS_TAC `FV` THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [cc_eta_thm, cc_eta_LAM] THENL [
      Q.EXISTS_TAC `[P/v]t''` THEN
      `compat_closure eta ([P/v]M) ([P/v]t'')`
         by METIS_TAC [cc_eta_subst] THEN
      `compat_closure beta (LAM v t'' @@ P) ([P/v]t'')`
         by METIS_TAC [beta_def, compat_closure_rules] THEN
      METIS_TAC [RC_DEF, reduction_rules],
      FULL_SIMP_TAC (srw_ss()) [eta_LAM, SUB_THM, lemma14b] THEN
      Q.EXISTS_TAC `t' @@ P` THEN
      METIS_TAC [reduction_rules, RC_DEF],
      Q.EXISTS_TAC `[u'/v]M` THEN
      METIS_TAC [RC_DEF, eta_cosubstitutive, beta_def,
                 compat_closure_rules]
    ],

    FULL_SIMP_TAC (srw_ss()) [cc_eta_thm] THEN
    METIS_TAC [compat_closure_rules, RC_DEF,
               reduction_rules],
    FULL_SIMP_TAC (srw_ss()) [cc_eta_thm] THEN
    METIS_TAC [compat_closure_rules, RC_DEF,
               reduction_rules],

    FULL_SIMP_TAC (srw_ss()) [cc_eta_LAM, eta_LAM] THENL [
      METIS_TAC [compat_closure_rules, RC_DEF,
                 reduction_rules],
      FULL_SIMP_TAC (srw_ss()) [cc_beta_thm] THENL [
        SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `v = v'` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
          METIS_TAC [reduction_rules, RC_DEF],
          `LAM v ([VAR v/v'] M0) = LAM v' M0`
             by METIS_TAC [SIMPLE_ALPHA] THEN
          METIS_TAC [reduction_rules, RC_DEF]
        ],
        `v NOTIN FV M'` by METIS_TAC [cc_beta_FV_SUBSET, SUBSET_DEF] THEN
        `compat_closure eta (LAM v (M' @@ VAR v)) M'`
           by SRW_TAC [][cc_eta_LAM, eta_LAM] THEN
        METIS_TAC [RC_DEF, reduction_rules]
      ]
    ]
  ])

val beta_eta_CR = store_thm(
  "beta_eta_CR",
  ``CR (beta RUNION eta)``,
  MATCH_MP_TAC (CONJUNCT2 hindley_rosen_lemma) THEN
  PROVE_TAC [beta_CR, eta_CR, eta_beta_commute, commute_COMM]);

val beta_eta_lameta = store_thm(
  "beta_eta_lameta",
  ``conversion (beta RUNION eta) = lameta``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [] THEN
    HO_MATCH_MP_TAC equiv_closure_ind THEN
    REPEAT CONJ_TAC THEN1
      (HO_MATCH_MP_TAC compat_closure_ind THEN
       REPEAT CONJ_TAC THEN1
          (SRW_TAC [][beta_def, eta_def, RUNION] THEN
           PROVE_TAC [lameta_rules]) THEN
       PROVE_TAC [lameta_rules]) THEN
    PROVE_TAC [lameta_rules],
    CONV_TAC (RENAME_VARS_CONV ["M", "N"]) THEN HO_MATCH_MP_TAC lameta_ind THEN
    REPEAT STRIP_TAC THENL [
      `(beta RUNION eta) (LAM x M @@ N) ([N/x]M)` by
         (SRW_TAC [][beta_def, RUNION] THEN PROVE_TAC []) THEN
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_rules],
      PROVE_TAC [conversion_compatible, compatible_def, rightctxt,
                 rightctxt_thm],
      PROVE_TAC [conversion_compatible, compatible_def, leftctxt],
      PROVE_TAC [conversion_compatible, compatible_def, absctxt],
      `(beta RUNION eta) (LAM x (N @@ VAR x)) N` by
         (SRW_TAC [][eta_def, RUNION] THEN PROVE_TAC []) THEN
      PROVE_TAC [conversion_rules]
    ]
  ]);

val beta_eta_normal_form_benf = store_thm(
  "beta_eta_normal_form_benf",
  ``normal_form (beta RUNION eta) = benf``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, benf_def, FORALL_AND_THM,
                       normal_form_def] THEN CONJ_TAC
  THENL [
    Q_TAC SUFF_TAC `!M. ~bnf M \/ ~enf M ==> can_reduce (beta RUNION eta) M`
          THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC simple_induction THEN REPEAT CONJ_TAC THENL [
      SRW_TAC [][bnf_thm, enf_thm], (* var case *)
      MAP_EVERY Q.X_GEN_TAC [`f`, `x`] THEN (* app case *)
      SRW_TAC [][bnf_thm, enf_thm] THENL [
        PROVE_TAC [can_reduce_rules],
        PROVE_TAC [can_reduce_rules],
        `redex (beta RUNION eta) (f @@ x)` by
         (SRW_TAC [][redex_def, RUNION, beta_def,
                     EXISTS_OR_THM] THEN
          PROVE_TAC [is_abs_thm, term_CASES]) THEN
        PROVE_TAC [can_reduce_rules],
        PROVE_TAC [can_reduce_rules],
        PROVE_TAC [can_reduce_rules]
      ],

      MAP_EVERY Q.X_GEN_TAC [`x`, `M`] THEN
      SRW_TAC [][bnf_thm, enf_thm] THENL [
        PROVE_TAC [can_reduce_rules, lemma14a],
        PROVE_TAC [can_reduce_rules, lemma14a],
        Q_TAC SUFF_TAC `redex (beta RUNION eta) (LAM x M)` THEN1
            PROVE_TAC [can_reduce_rules] THEN
        SRW_TAC [][redex_def, RUNION, eta_def] THEN
        PROVE_TAC [is_comb_rator_rand]
      ]
    ],
    Q_TAC SUFF_TAC `!x. can_reduce (beta RUNION eta) x ==> ~bnf x \/ ~enf x`
          THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC can_reduce_ind THEN
    SIMP_TAC (srw_ss()) [bnf_thm, enf_thm, DISJ_IMP_THM, redex_def,
                         RUNION, GSYM LEFT_FORALL_IMP_THM,
                         beta_def, eta_def]
  ]);

val lameta_consistent = store_thm(
  "lameta_consistent",
  ``consistent lameta``,
  SIMP_TAC (srw_ss()) [consistent_def, GSYM beta_eta_lameta] THEN
  MAP_EVERY Q.EXISTS_TAC [`S`, `K`] THEN STRIP_TAC THEN
  `?Z. reduction (beta RUNION eta) S Z /\ reduction (beta RUNION eta) K Z` by
     PROVE_TAC [theorem3_13, beta_eta_CR] THEN
  `normal_form (beta RUNION eta) S` by
       SRW_TAC [][beta_eta_normal_form_benf, benf_def, bnf_thm, enf_thm,
                  S_def] THEN
  `normal_form (beta RUNION eta) K` by
       SRW_TAC [][beta_eta_normal_form_benf, benf_def, bnf_thm, enf_thm,
                  K_def] THEN
  `S = K` by PROVE_TAC [corollary3_2_1] THEN
  FULL_SIMP_TAC (srw_ss()) [S_def, K_def]);

val is_comb_subst = store_thm(
  "is_comb_subst",
  ``!t u v. is_comb t ==> is_comb ([u/v]t)``,
  SIMP_TAC (srw_ss()) [SUB_THM, is_comb_APP_EXISTS,
                       GSYM LEFT_FORALL_IMP_THM]);

val rator_isub_commutes = store_thm(
  "rator_isub_commutes",
  ``!R t. is_comb t ==> (rator (t ISUB R) = rator t ISUB R)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [ISUB_def, pairTheory.FORALL_PROD,
                           rator_subst_commutes, is_comb_subst]);

(* ----------------------------------------------------------------------
    Reordering β and η steps

    Following Takahashi "Parallel Reductions in λ-Calculus", 1995,
      §3: Postponement Theorem
   ---------------------------------------------------------------------- *)

Overload "-η->" = “compat_closure eta”
Overload "-η->*" = “reduction eta”
Overload "-βη->" = “compat_closure (beta RUNION eta)”
Overload "-βη->*" = “reduction (beta RUNION eta)”

val _ = set_fixity "-βη->" (Infix(NONASSOC, 450))
val _ = set_fixity "-βη->*" (Infix(NONASSOC, 450))
val _ = set_fixity "-η->" (Infix(NONASSOC, 450))
val _ = set_fixity "-η->*" (Infix(NONASSOC, 450))

Theorem eta_FV_EQN:
  eta M N ⇒ FV N = FV M
Proof
  simp[eta_def, PULL_EXISTS] >> rpt strip_tac >>
  ASM_SET_TAC[]
QED

Theorem cc_eta_FV_EQN:
  ∀M N. compat_closure η M N ⇒ FV N = FV M
Proof
  ho_match_mp_tac cc_ind >> qexists ‘{}’>> rpt strip_tac >> gvs[eta_FV_EQN] >>
  metis_tac[permutative_def, substitutive_implies_permutative, eta_substitutive]
QED

Theorem eta_beta_reorder0[local]:
  ∀M0 M1. compat_closure eta M0 M1 ⇒
          ∀M. compat_closure eta M0 M1 ∧
              (M1 -β-> M ⇒
               ∃M1'. M0 -β->* M1' ∧ RTC (compat_closure eta) M1' M)
Proof
  ho_match_mp_tac cc_gen_ind >> qexists ‘FV’ >> simp[] >> rpt strip_tac >>
  gs[FORALL_AND_THM, compat_closure_rules]
  >- (assume_tac eta_substitutive >> drule substitutive_implies_permutative >>
      simp[permutative_def]) >~
  [‘η M0 M1’]
  >- (gs[eta_def] >> irule_at (Pat ‘_ -β->* _’) RTC_SINGLE >>
      irule_at Any compat_closure_LAM >>
      irule_at Any compat_closure_APPL >> first_assum $ irule_at Any >>
      irule RTC_SINGLE >> irule compat_closure_R >> simp[eta_def] >>
      irule_at Any EQ_REFL >> metis_tac[cc_beta_FV_SUBSET, SUBSET_DEF]) >~
  [‘M1 @@ M2 -β-> M’, ‘compat_closure η M0 M1’]
  >- (qpat_x_assum ‘_ @@ _ -β-> _’ mp_tac >>
      simp[Once compat_closure_cases] >> rpt strip_tac >> gvs[] >~
      [‘compat_closure η M0 M1’, ‘M1 -β-> M1'’, ‘M0 @@ M2 -β->* _’]
      >- (irule_at (Pat ‘_ -β->* _’) (cj 6 reduction_rules) >>
          irule_at (Pat ‘reduction η _ _’) (cj 6 reduction_rules) >>
          metis_tac[]) >~
      [‘compat_closure η M0 M1’, ‘M2 -β-> M3’, ‘M0 @@ M2 -β->* _’]
      >- (irule_at (Pat ‘_ -β->* _’) RTC_SINGLE >>
          irule_at Any compat_closure_APPR >>
          first_assum $ irule_at Any >>
          irule_at Any RTC_SINGLE >>
          simp[compat_closure_APPL]) >~
      [‘compat_closure η M0 M1’, ‘β (M1 @@ M2) M’, ‘M0 @@ M2 -β->* _’]
      >- (qpat_x_assum ‘β _ _’ mp_tac >> simp[beta_def, PULL_EXISTS] >>
          rw[] >> rename [‘LAM v M01’] >>
          ‘(∃u. M0 = LAM u (LAM v M01 @@ VAR u) ∧ u # LAM v M01) ∨
           ∃M00. M0 = LAM v M00 ∧ compat_closure η M00 M01’
            by (qpat_x_assum ‘compat_closure _ _ _’ mp_tac >>
                simp[Once compat_closure_cases, SimpL “$==>”] >>
                simp[eta_def] >> rpt strip_tac >> simp[] >~
                [‘N1 = LAM u (LAM v M1 @@ VAR u)’] >- metis_tac[] >>
                disj2_tac >> gvs[LAM_eq_thm] >>
                simp[tpm_eqr] >> simp[pmact_flip_args, cc_eta_tpm] >>
                metis_tac[cc_eta_FV_EQN])
          >- (gvs[] >> irule_at (Pat ‘_ -β->* _’) (cj 2 RTC_RULES) >>
              irule_at Any compat_closure_R >> simp[beta_def, PULL_EXISTS] >>
              irule_at Any EQ_REFL >> simp[lemma14b, SUB_THM] >>
              irule_at (Pat ‘_ -β->* _’) RTC_SINGLE >>
              irule_at Any compat_closure_R >> simp[beta_def, PULL_EXISTS] >>
              irule_at Any EQ_REFL >> simp[]) >>
          gvs[] >> irule_at (Pat ‘_ -β->* _’) RTC_SINGLE >>
          irule_at Any compat_closure_R >> simp[beta_def, PULL_EXISTS] >>
          irule_at Any EQ_REFL >> simp[] >>
          irule RTC_SINGLE >> simp[cc_eta_subst])) >~
  [‘compat_closure η M10 M1’, ‘M0 @@ M1 -β-> M’]
  >- (qpat_x_assum ‘_ -β-> _’ mp_tac >>
      simp[Once compat_closure_cases] >> rw[] >~
      [‘β (M0 @@ M1) M’, ‘compat_closure η M10 M1’]
      >- (gvs[beta_def] >>
          irule_at (Pat ‘_ -β->* _’) RTC_SINGLE >>
          irule_at Any compat_closure_R >> simp[beta_def, PULL_EXISTS] >>
          irule_at Any EQ_REFL >> simp[eta_cosubstitutive]) >~
      [‘compat_closure η M10 M1’, ‘M1 -β-> M1'’, ‘M0 @@ M10 -β->* _’]
      >- (irule_at (Pat ‘_ -β->* _’) (cj 5 reduction_rules) >>
          irule_at Any (cj 5 reduction_rules) >> metis_tac[]) >~
      [‘M0 -β-> M01’]
      >- (irule_at (Pat ‘_ -β->* _’) RTC_SINGLE >>
          irule_at Any compat_closure_APPL >> first_assum $ irule_at Any >>
          simp[compat_closure_rules, reduction_rules])) >~
  [‘compat_closure η M0 M1’, ‘LAM v M1 -β-> M’]
  >- (gvs[ccbeta_rwt] >>
      irule_at (Pat ‘_ -β->* _’) (cj 7 reduction_rules) >>
      irule_at Any (cj 7 reduction_rules) >> metis_tac[])
QED

Theorem eta_beta_reorder:
  compat_closure η M0 M1 ∧ M1 -β-> M ⇒
  ∃M1'. M0 -β->* M1' ∧ reduction eta M1' M
Proof
  metis_tac[eta_beta_reorder0]
QED



Theorem strong_grandbeta_gen_ind =
        grandbeta_bvc_gen_ind
          |> SPEC_ALL
          |> Q.INST [‘P’ |-> ‘λM N x. P M N x /\ grandbeta M N’]
          |> SRULE[grandbeta_rules, FORALL_AND_THM,
                   GSYM CONJ_ASSOC]
          |> GEN_ALL

Theorem has_bnf_LAM[simp]:
  has_bnf (LAM v M) ⇔ has_bnf M
Proof
  simp[has_bnf_thm, abs_betastar, PULL_EXISTS]
QED

Theorem ccbeta_beta:
  LAM v M @@ N -β-> [N/v]M
Proof
  simp[ccbeta_rwt]
QED

Theorem appEQvsubst[simp]:
  M @@ N = [VAR u/v] P ⇔
    ∃M0 N0. P = M0 @@ N0 ∧ M = [VAR u/v] M0 ∧ N = [VAR u/v]N0
Proof
  Cases_on ‘P’ using term_CASES >> rw[SUB_VAR, SUB_THM]
QED

Theorem lamEQvsubst:
  v ≠ u ∧ v ≠ w ⇒
  (LAM v M = [VAR u/w] P ⇔ ∃M0. P = LAM v M0 ∧ M = [VAR u/w]M0)
Proof
  Cases_on ‘P’ using term_CASES >> rw[SUB_VAR, SUB_THM] >>
  rename [‘LAM v M = [VAR u/w] (LAM x M')’] >>
  Q_TAC (NEW_TAC "z") ‘{x;u;w;v} ∪ FV M ∪ FV M'’ >>
  Cases_on ‘w = x’ >> gvs[lemma14b]
  >- (simp[LAM_eq_thm, EQ_IMP_THM] >> simp[tpm_eqr] >> rw[] >>
      simp[pmact_flip_args] >> gvs[lemma14b]) >>
  ‘LAM x M' = LAM z ([VAR z/x] M')’ by simp[SIMPLE_ALPHA] >>
  simp[SUB_THM] >> gvs[LAM_eq_thm] >> simp[tpm_eqr] >>
  gvs[FV_SUB] >> rw[] >> gvs[] >>
  Cases_on ‘v = x’ >> gvs[] >> simp[pmact_flip_args]
QED

Theorem varsubst_betaL:
  [VAR v/u] M -β-> N ⇒ ∃N0. M -β-> N0 ∧ N = [VAR v/u]N0
Proof
  ‘∀M0 N. M0 -β-> N ⇒
          ∀vuM v u M. vuM = (v,u,M) ∧ M0 = [VAR v/u]M ⇒
                      ∃N0. M -β-> N0 ∧ N = [VAR v/u]N0’
    suffices_by metis_tac[] >>
  ho_match_mp_tac strong_ccbeta_gen_ind >>
  qexists ‘λ(v,u,M). {v;u} ∪ FV M’ >> rw[] >> gvs[]
  >- (gvs[lamEQvsubst] >> irule_at Any ccbeta_beta >>
      simp[substitution_lemma])
  >- metis_tac[compat_closure_rules]
  >- metis_tac[compat_closure_rules]
  >- (gvs[lamEQvsubst, PULL_EXISTS] >> metis_tac[compat_closure_LAM]) >>
  PairCases_on ‘vuM’ >> simp[]
QED

Theorem varsubst_betastarL:
  ∀M N v u. [VAR v/u] M -β->* N ⇒ ∃N0. M -β->* N0 ∧ N = [VAR v/u]N0
Proof
  Induct_on ‘RTC’ >> rw[] >- metis_tac[RTC_REFL] >>
  drule_then strip_assume_tac varsubst_betaL >> gvs[] >>
  first_x_assum (resolve_then Any mp_tac EQ_REFL) >> rw[] >>
  metis_tac[RTC_RULES]
QED

Theorem has_bnf_appVAR_LR:
  ∀M N s. M @@ VAR s -β->* N ∧ bnf N ⇒ has_bnf M
Proof
  Induct_on ‘RTC’>> rw[] >> gs[]
  >- (simp[has_bnf_thm] >> metis_tac[RTC_REFL]) >>
  rename [‘M @@ VAR s -β-> M'’] >>
  qpat_x_assum ‘_ -β-> _’ mp_tac >>
  simp[Once compat_closure_cases] >> rw[]
  >- (gvs[beta_def] >> drule_then strip_assume_tac varsubst_betastarL >>
      gvs[] >> metis_tac[has_bnf_thm])
  >- gvs[cc_beta_thm] >>
  first_x_assum (resolve_then Any mp_tac EQ_REFL) >>
  simp[has_bnf_thm, PULL_EXISTS] >> metis_tac[RTC_RULES]
QED

Theorem has_bnf_appVAR_RL:
  ∀M N. M -β->* N ∧ bnf N ⇒ has_bnf (M @@ VAR s)
Proof
  Induct_on ‘RTC’ >> rw[]
  >- (Cases_on ‘M’ using term_CASES >> simp[has_bnf_thm] >~
      [‘LAM v M @@ VAR u’]
      >- (irule_at Any RTC_SUBSET >> irule_at Any ccbeta_beta >>
          gvs[]) >>
      irule_at Any RTC_REFL >> simp[]) >>
  gvs[has_bnf_thm] >>
  irule_at Any (cj 2 RTC_RULES) >>
  first_assum $ irule_at (Pat ‘_ -β->* _’) >> simp[] >>
  simp[compat_closure_rules]
QED

Theorem has_bnf_VAR[simp]:
  has_bnf (VAR s)
Proof
  metis_tac[bnf_thm, RTC_REFL, has_bnf_thm]
QED

Theorem has_bnf_varapp[simp]:
  ∀s M. has_bnf (VAR s @@ M) ⇔ has_bnf M
Proof
  simp[has_bnf_thm, PULL_EXISTS, EQ_IMP_THM, FORALL_AND_THM] >>
  conj_tac >> Induct_on ‘RTC’ >> rw[] >> gvs[] >~
  [‘VAR s @@ M -β-> M2’]
  >- (gvs[ccbeta_rwt] >> metis_tac[RTC_RULES]) >~
  [‘M -β-> P’]
  >- (irule_at Any (cj 2 RTC_RULES) >>
      irule_at Any compat_closure_APPR >> metis_tac[]) >>
  irule_at Any RTC_REFL >> simp[]
QED

Theorem app_becomes_abs:
  M @@ N =β=> P ∧ is_abs P ⇒ is_abs M
Proof
  CCONTR_TAC >> gvs[] >> qpat_x_assum ‘M @@ N =β=> P’ mp_tac >>
  simp[Once grandbeta_cases] >> rpt strip_tac >> gvs[]
QED

Theorem LAMl_beta_cong:
  ∀M N. M -β-> N ⇒ LAMl vs M -β-> LAMl vs N
Proof
  Induct_on ‘vs’ >> simp[] >> metis_tac[compat_closure_rules]
QED

Theorem LAMl_betastar_cong:
  ∀M N. M -β->* N ⇒ LAMl vs M -β->* LAMl vs N
Proof
  Induct_on ‘RTC’ >> metis_tac[reduction_rules, LAMl_beta_cong]
QED

Theorem has_benf_thm:
  has_benf M ⇔ ∃N. M -βη->* N ∧ benf N
Proof
  rw[has_benf_def, GSYM beta_eta_lameta, EQ_IMP_THM,
     GSYM beta_eta_normal_form_benf]
  >- (drule_at Any theorem3_13 >>
      drule_then strip_assume_tac corollary3_2_1 >> simp[beta_eta_CR] >>
      strip_tac >> first_x_assum drule >> metis_tac[]) >>
  metis_tac[conversion_rules]
QED

Theorem tpm_eta[simp]:
  eta (tpm p M) (tpm p N) ⇔ eta M N
Proof
  simp[eta_def] >> iff_tac >> rw[] >> simp[] >~
  [‘LAM _ _ = LAM _ _’]
  >- (irule_at Any EQ_REFL >> simp[]) >>
  rename [‘tpm p M = LAM v (tpm p M0 @@ VAR v)’] >>
  ‘M = tpm p⁻¹ (LAM v (tpm p M0 @@ VAR v))’ by metis_tac[tpm_eqr]>> gvs[] >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem eta_reduces_size:
  ∀M N. M -η-> N ⇒ size N < size M
Proof
  ho_match_mp_tac cc_ind >> qexists‘{}’ >> rw[] >>
  gvs[eta_def]
QED

Theorem SN_eta:
  chap3$SN η
Proof
  simp[SN_def, relationTheory.SN_def] >> irule WF_SUBSET >>
  simp[]>> qexists ‘measure size’ >> simp[eta_reduces_size]
QED

Theorem reduction_RUNION1:
  reduction R1 M N ⇒ reduction (R1 RUNION R2) M N
Proof
  Induct_on ‘RTC’ >> simp[] >> rpt strip_tac >>
  irule (cj 2 RTC_RULES) >> gs[CC_RUNION_DISTRIB, RUNION] >> metis_tac[]
QED

Theorem reduction_RUNION2:
  reduction R2 M N ⇒ reduction (R1 RUNION R2) M N
Proof
  Induct_on ‘RTC’ >> simp[] >> rpt strip_tac >>
  irule (cj 2 RTC_RULES) >> gs[CC_RUNION_DISTRIB, RUNION] >> metis_tac[]
QED


(* ----------------------------------------------------------------------
    Congruence and rewrite rules for -b-> and -b->*
   ---------------------------------------------------------------------- *)

val RTC1_step = CONJUNCT2 (SPEC_ALL RTC_RULES)

val betastar_LAM = store_thm(
  "betastar_LAM",
  ``!M N. LAM x M -b->* LAM x N  <=>  M -b->* N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `!M N. M -b->* N ==>
                          !v M0 N0. (M = LAM v M0) /\ (N = LAM v N0) ==>
                                    M0 -b->* N0` THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC RTC_INDUCT THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [ccbeta_rwt] THEN
    METIS_TAC [RTC_RULES],

    HO_MATCH_MP_TAC RTC_INDUCT THEN
    SRW_TAC [][] THEN
    METIS_TAC [compat_closure_rules, RTC_RULES]
  ]);
val _ = export_rewrites ["betastar_LAM"]

val betastar_LAM_I = store_thm(
  "betastar_LAM_I",
  ``!v M N. M -b->* N ==> LAM v M -b->* LAM v N``,
  METIS_TAC [betastar_LAM]);

val betastar_APPr = store_thm(
  "betastar_APPr",
  ``!M N. M -b->* N ==> P @@ M -b->* P @@ N``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [RTC1_step, compat_closure_rules]);

val betastar_APPl = store_thm(
  "betastar_APPl",
  ``!M N. M -b->* N ==> M @@ P -b->* N @@ P``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [RTC1_step, compat_closure_rules]);

val betastar_APPlr = store_thm(
  "betastar_APPlr",
  ``M -b->* M' ==> N -b->* N' ==> M @@ N -b->* M' @@ N'``,
  METIS_TAC [RTC_CASES_RTC_TWICE, betastar_APPl, betastar_APPr]);

val beta_betastar = store_thm(
  "beta_betastar",
  ``LAM v M @@ N -b->* [N/v]M``,
  SRW_TAC [][ccbeta_rwt, RTC_SINGLE]);

val betastar_eq_cong = store_thm(
  "betastar_eq_cong",
  ``bnf N ==> M -b->* M' ==> (M -b->* N  <=> M' -b->* N)``,
  METIS_TAC [bnf_triangle, RTC_CASES_RTC_TWICE]);

(* |- !x y z. x -b->* y /\ y -b->* z ==> x -b->* z *)
Theorem betastar_TRANS =
        RTC_TRANSITIVE |> Q.ISPEC ‘compat_closure beta’
                       |> REWRITE_RULE [transitive_def]

val _ = export_theory();
val _ = html_theory "chap3";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
