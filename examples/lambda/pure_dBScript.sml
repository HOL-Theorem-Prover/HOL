open HolKernel boolLib Parse bossLib pred_setTheory termTheory BasicProvers

open arithmeticTheory boolSimps

local open string_numTheory in end

val _ = new_theory "pure_dB"

(* the type of pure de Bruijn terms *)
val _ = Hol_datatype`pdb = dV of num | dAPP of pdb => pdb | dABS of pdb`

(* Definitions of lift and substitution from Nipkow's "More Church-Rosser
   proofs" *)
val lift_def = Define`
  (lift (dV i) k = if i < k then dV i else dV (i + 1)) /\
  (lift (dAPP s t) k = dAPP (lift s k) (lift t k)) /\
  (lift (dABS s) k = dABS (lift s (k + 1)))
`;
val _ = export_rewrites ["lift_def"]

(* "Nipkow" substitution *)
val nsub_def = Define`
  (nsub s k (dV i) = if k < i then dV (i - 1)
                       else if i = k then s else dV i) /\
  (nsub s k (dAPP t u) = dAPP (nsub s k t) (nsub s k u)) /\
  (nsub s k (dABS t) = dABS (nsub (lift s 0) (k + 1) t))
`;
val _ = export_rewrites ["nsub_def"]

(* substitution that corresponds to substitution in the lambda-calculus;
   no variable decrementing in the dV clause *)
val sub_def = Define`
  (sub s k (dV i) = if i = k then s else dV i) /\
  (sub s k (dAPP t u) = dAPP (sub s k t) (sub s k u)) /\
  (sub s k (dABS t) = dABS (sub (lift s 0) (k + 1) t))
`;
val _ = export_rewrites ["sub_def"]

(* a variable-binding lambda-equivalent for dB terms *)
val dLAM_def = Define`
  dLAM v body = dABS (sub (dV 0) (v + 1) (lift body 0))
`

(* the set of free indices in a term *)
val dFV_def = Define`
  (dFV (dV i) = {i}) /\
  (dFV (dAPP t u) = dFV t UNION dFV u) /\
  (dFV (dABS t) = IMAGE PRE (dFV t DELETE 0))
`
val _ = export_rewrites ["dFV_def"]

val FINITE_dFV = store_thm(
  "FINITE_dFV",
  ``FINITE (dFV t)``,
  Induct_on `t` THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_dFV"]

(* guarded increment of a string: it's untouched if the corresponding index
   is less than the guard, otherwise it's bumped, and then pushed back into
   the string type *)
val ginc_def = Define`
  ginc gd s = if s2n s < gd then s else n2s (s2n s + 1)
`

val ginc_0 = store_thm(
  "ginc_0",
  ``ginc 0 s = n2s (s2n s + 1)``,
  SRW_TAC [][ginc_def])

val ginc_11 = store_thm(
  "ginc_11",
  ``(ginc g s1 = ginc g s2) = (s1 = s2)``,
  SRW_TAC [][ginc_def] THENL [
    `s2n s1 < s2n s2` by DECIDE_TAC THEN
    `~(s1 = s2)` by METIS_TAC [DECIDE ``~(x < x)``] THEN
    SRW_TAC [][] THEN STRIP_TAC THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    `s2n s2 < s2n s1` by DECIDE_TAC THEN
    `~(s1 = s2)` by METIS_TAC [DECIDE ``~(x < x)``] THEN
    SRW_TAC [][] THEN STRIP_TAC THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);
val _ = export_rewrites ["ginc_11"]

val ginc_neq = store_thm(
  "ginc_neq",
  ``~(ginc (s2n s1) s2 = s1)``,
  SRW_TAC [][ginc_def] THENL [
    STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
    STRIP_TAC THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);
val _ = export_rewrites ["ginc_neq"]

(* incrementing a permutation, defined in terms of the underlying list of
   pairs representation *)
val inc_pm_def = Define`
  (inc_pm g [] = []) /\
  (inc_pm g ((x,y)::rest) = (ginc g x, ginc g y) :: inc_pm g rest)
`;
val _ = export_rewrites ["inc_pm_def"]

val inc_pm_APPEND = store_thm(
  "inc_pm_APPEND",
  ``!pi1 pi2. inc_pm g (pi1 ++ pi2) = inc_pm g pi1 ++ inc_pm g pi2``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

(* characterisation of what an incremented permutation does to a string *)
val lswapstr_inc_pm = store_thm(
  "lswapstr_inc_pm",
  ``!pi g s. lswapstr (inc_pm g pi) s =
                if s2n s < g then ginc g (lswapstr pi s)
                else if s2n s = g then s
                else ginc g (lswapstr pi (n2s (s2n s - 1)))``,
  Induct THENL [
    SRW_TAC [ARITH_ss][ginc_def],
    ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
    SRW_TAC [][] THEN
    SRW_TAC [][basic_swapTheory.swapstr_def]
  ]);

val inc_pm_permeq = store_thm(
  "inc_pm_permeq",
  ``!p1 p2. (p1 == p2) ==> (inc_pm g p1 == inc_pm g p2)``,
  SIMP_TAC (srw_ss()) [nomsetTheory.permeq_def, lswapstr_inc_pm,
                       FUN_EQ_THM]);

(* definition of permutation over de Bruijn terms *)
val dpm_def = Define`
  (dpm pi (dV i) = dV (s2n (lswapstr pi (n2s i)))) /\
  (dpm pi (dAPP t u) = dAPP (dpm pi t) (dpm pi u)) /\
  (dpm pi (dABS t) = dABS (dpm (inc_pm 0 pi) t))
`;
val _ = export_rewrites ["dpm_def"]

(* proof that dB terms + dpm form a nominal set *)
val dpm_is_perm = store_thm(
  "dpm_is_perm",
  ``is_perm dpm``,
  SIMP_TAC (srw_ss()) [nomsetTheory.is_perm_def] THEN REPEAT CONJ_TAC THENL [
    Induct_on `x` THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][basic_swapTheory.lswapstr_APPEND,
                                  inc_pm_APPEND],
    SIMP_TAC (srw_ss()) [FUN_EQ_THM, GSYM RIGHT_FORALL_IMP_THM,
                         nomsetTheory.permeq_def] THEN
    Induct_on `x` THEN SRW_TAC [][lswapstr_inc_pm]
  ]);
val _ = export_rewrites ["dpm_is_perm"]

(* being a nominal set gives us properties of dpm "for free" *)
val dpm_flip_args = store_thm(
  "dpm_flip_args",
  ``dpm ((x,y)::pi) t = dpm ((y,x)::pi) t``,
  SRW_TAC [][nomsetTheory.is_perm_flip_args]);

val dpm_sing_inv = store_thm(
  "dpm_sing_inv",
  ``dpm [h] (dpm [h] t) = t``,
  SRW_TAC [][nomsetTheory.is_perm_sing_inv]);
val _ = export_rewrites ["dpm_sing_inv"]

(* dFVs gives the free indices of a dB term as strings *)
val dFVs_def = Define`dFVs t = IMAGE n2s (dFV t)`
val dFVs_thm = store_thm(
  "dFVs_thm",
  ``(dFVs (dV i) = {n2s i}) /\
    (dFVs (dAPP t u) = dFVs t UNION dFVs u) /\
    (dFVs (dABS t) = IMAGE (\s. n2s (s2n s - 1)) (dFVs t DELETE n2s 0))``,
  SRW_TAC [][dFVs_def] THEN
  SRW_TAC [][EXTENSION, EQ_IMP_THM] THENL [
    SRW_TAC [boolSimps.DNF_ss][] THEN
    METIS_TAC [arithmeticTheory.PRE_SUB1],
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN
    METIS_TAC [arithmeticTheory.PRE_SUB1]
  ]);
val _ = export_rewrites ["dFVs_thm"]

val FINITE_dFVs = store_thm(
  "FINITE_dFVs",
  ``FINITE (dFVs t)``,
  SRW_TAC [][dFVs_def]);
val _ = export_rewrites ["FINITE_dFVs"]

(* this and the next result establish that dFVs gives the support of a
   dB term *)
val dpm_apart = store_thm(
  "dpm_apart",
  ``!x y. x IN dFVs t /\ ~(y IN dFVs t) ==> ~(dpm [(x,y)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][] THENL [
    STRIP_TAC THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [],
    METIS_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SRW_TAC [][ginc_0] THENL [
      Q.MATCH_ABBREV_TAC `n2s (s2n v - 1 + 1) IN dFVs t` THEN
      Q_TAC SUFF_TAC `~(s2n v = 0)` THEN1 SRW_TAC [ARITH_ss][] THEN
      METIS_TAC [string_numTheory.n2s_s2n],
      FIRST_X_ASSUM (Q.SPEC_THEN `n2s (s2n y + 1)` MP_TAC) THEN
      SRW_TAC [][]
    ]
  ]);

val dpm_fresh = store_thm(
  "dpm_fresh",
  ``!x y. ~(x IN dFVs t) /\ ~(y IN dFVs t) ==> (dpm [(x,y)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][ginc_0] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT (FIRST_X_ASSUM
          (fn th => Q.SPEC_THEN `n2s (s2n x + 1)` MP_TAC th THEN
                    Q.SPEC_THEN `n2s (s2n y + 1)` MP_TAC th)) THEN
  SRW_TAC [][]);

val dpm_supp = store_thm(
  "dpm_supp",
  ``supp dpm = dFVs``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN SRW_TAC [][] THEN
  MATCH_MP_TAC nomsetTheory.supp_unique_apart THEN
  SRW_TAC [][dpm_apart, nomsetTheory.support_def] THEN
  MATCH_MP_TAC dpm_fresh THEN SRW_TAC [][]);
val _ = export_rewrites ["dpm_supp"]


(* this is enough to establish de Bruijn terms as a nominal type for the
   purposes of function definition.  I.e., now we can define functions
   that have dB terms as their range *)
val _ = binderLib.range_database :=
        Binarymap.insert(!binderLib.range_database, "pdb",
                         {nullfv = ``dABS (dV 0)``,
                          rewrites = [],
                          inst = ["rFV" |-> (fn () => ``pure_dB$dFVs``),
                                  "rswap" |-> (fn () =>
                                                  ``\x y t. dpm [(x,y)] t``),
                                  "apm" |-> (fn () => ``pure_dB$dpm``)]})



(* substitution of a fresh variable is actually a permutation *)
val fresh_dpm_sub = prove(
  ``!i j M. ~(j IN dFV M) ==> (sub (dV j) i M = dpm [(n2s j, n2s i)] M)``,
  Induct_on `M` THEN SRW_TAC [][ginc_0] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `j + 1` MP_TAC) THEN SRW_TAC [][PRE_SUB1]);



val ginc_0n = prove(
  ``ginc 0 (ginc n s) = ginc (n + 1) (ginc 0 s)``,
  SRW_TAC [][ginc_def]);

val inc_pm_0n = prove(
  ``!pi. inc_pm 0 (inc_pm n pi) = inc_pm (n + 1) (inc_pm 0 pi)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ginc_0n])

(* interaction of lifting and permutation *)
val lift_dpm = store_thm(
  "lift_dpm",
  ``!n pi. lift (dpm pi M) n = dpm (inc_pm n pi) (lift M n)``,
  Induct_on `M` THEN SRW_TAC [][lswapstr_inc_pm] THENL [
    SRW_TAC [][ginc_def],
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
    SRW_TAC [][ginc_def],
    SRW_TAC [ARITH_ss][ginc_def],
    SRW_TAC [ARITH_ss][ginc_def],
    SRW_TAC [][inc_pm_0n]
  ]);

(* substitution and permutation are clean *)
val dpm_sub = store_thm(
  "dpm_sub",
  ``!pi M j N.
        dpm pi (sub M j N) = sub (dpm pi M) (s2n (lswapstr pi (n2s j)))
                                         (dpm pi N)``,
  Induct_on `N` THEN SRW_TAC [][lswapstr_inc_pm, lift_dpm] THEN
  SRW_TAC [][ginc_0]);

(* thus, so too is dLAM *)
val dpm_dLAM = store_thm(
  "dpm_dLAM",
  ``dpm pi (dLAM j t) = dLAM (s2n (lswapstr pi (n2s j))) (dpm pi t)``,
  SRW_TAC [][dLAM_def, dpm_sub, lift_dpm, lswapstr_inc_pm] THEN
  SRW_TAC [][ginc_0])
val _ = export_rewrites ["dpm_dLAM"]

(* some standard results about substitution *)
val sub_14a = store_thm(
  "sub_14a",
  ``!i t. sub (dV i) i t = t``,
  Induct_on `t` THEN SRW_TAC [][]);

val sub_14b = store_thm(
  "sub_14b",
  ``!M i N. ~(i IN dFV N) ==> (sub M i N = N)``,
  Induct_on `N` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `i + 1` MP_TAC) THEN
  SRW_TAC [ARITH_ss][])

val sub_15a = store_thm(
  "sub_15a",
  ``!M i j N. ~(i IN dFV M) ==>
              (sub N i (sub (dV i) j M) = sub N j M)``,
  Induct_on `M` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `i + 1` MP_TAC) THEN SRW_TAC [ARITH_ss][]);

open chap2Theory

(* from Nipkow *)
val tn_lift_lemma1 = prove(
  ``!t i k. i < k ==> (lift (lift t i) k = lift (lift t (k - 1)) i)``,
  Induct THEN SRW_TAC [ARITH_ss][])

(* result needed to establish the substitution lemma *)
val lift_sub = store_thm(
  "lift_sub",
  ``!M i N n.
       n <= i ==>
       (lift (sub M i N) n = sub (lift M n) (i + 1) (lift N n))``,
  Induct_on `N` THEN
  SRW_TAC [ARITH_ss][tn_lift_lemma1])

val sn_iso_num = prove(
  ``((s = n2s n) = (n = s2n s)) /\ ((n2s n = s) = (n = s2n s))``,
  METIS_TAC [string_numTheory.s2n_n2s, string_numTheory.n2s_s2n])

val sub1_11 = prove(
  ``~(x = 0) /\ ~(y = 0) ==> ((x - 1 = y - 1) = (x = y))``,
  DECIDE_TAC)

val dFV_lift = store_thm(
  "dFV_lift",
  ``!n. dFV (lift M n) = { m | m IN dFV M /\ m < n } UNION
                         { m + 1 | m IN dFV M /\ n <= m }``,
  Induct_on `M` THEN SRW_TAC [][EXTENSION] THEN
  SRW_TAC [ARITH_ss][] THENL [
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    EQ_TAC THEN SRW_TAC [][] THEN SRW_TAC [][],

    REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    EQ_TAC THEN SRW_TAC [][PRE_SUB1] THEN SRW_TAC [][] THENL [
      FULL_SIMP_TAC (srw_ss() ++ CONJ_ss) [sub1_11] THEN
      DISJ1_TAC THEN DECIDE_TAC,

      FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
      ASM_SIMP_TAC (srw_ss() ++ CONJ_ss ++ ARITH_ss) [],

      Q.EXISTS_TAC `x'` THEN SRW_TAC [][] THEN
      SRW_TAC [ARITH_ss][],

      Q.EXISTS_TAC `x' + 1` THEN SRW_TAC [][] THEN
      SRW_TAC [ARITH_ss][]
    ]
  ]);

(* The substitution lemma, in dB guise *)
val sub_lemma = store_thm(
  "nsub_lemma",
  ``!M N i j L. ~(i = j) /\ ~(j IN dFV M) ==>
                (sub M i (sub N j L) =
                 sub (sub M i N) j (sub M i L))``,
  Induct_on `L` THEN
  SRW_TAC [][sub_14b, lift_sub] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][dFV_lift]);

(* which allows us to prove that substitution interacts with dLAM in the way
   we'd expect *)
val sub_dLAM = store_thm(
  "sub_dLAM",
  ``~(i IN dFV N) /\ ~(i = j) ==>
    (sub N j (dLAM i M) = dLAM i (sub N j M))``,
  SRW_TAC [][dLAM_def] THEN
  SRW_TAC [][Once sub_lemma, dFV_lift] THEN
  SRW_TAC [][lift_sub]);

val dFVs_lift = store_thm(
  "dFVs_lift",
  ``!n. dFVs (lift M n) = { n2s m | m IN dFV M /\ m < n } UNION
                          { n2s (m + 1) | m IN dFV M /\ n <= m }``,
  SRW_TAC [][dFVs_def, dFV_lift, EXTENSION, EQ_IMP_THM] THEN
  SRW_TAC [][]);

(* free variables of a substitution *)
val dFVs_sub = store_thm(
  "dFVs_sub",
  ``!M j. dFVs (sub M j N) = if j IN dFV N then
                                   (dFVs N DELETE n2s j) UNION dFVs M
                                 else dFVs N``,
  SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss) [] THEN
  SIMP_TAC (srw_ss()) [tautLib.TAUT_PROVE ``p \/ q = ~p ==> q``,
                       FORALL_AND_THM, sub_14b] THEN
  Induct_on `N` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    Cases_on `j IN dFV N'` THEN
    SRW_TAC [][sub_14b] THEN
    SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][] THEN
    Cases_on `x = n2s j` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [dFVs_def],

    Cases_on `j IN dFV N` THEN
    SRW_TAC [][sub_14b] THEN
    SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][] THEN
    Cases_on `x = n2s j` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [dFVs_def],

    SRW_TAC [][EXTENSION, EQ_IMP_THM,
               DECIDE ``~(x = 0) ==> (PRE x + 1 = x)``] THEN
    SRW_TAC [][] THENL [
      DISJ1_TAC THEN CONJ_TAC THENL [
        METIS_TAC [],
        Q.MATCH_ABBREV_TAC `~(s2n s - 1 = PRE x)` THEN
        Q_TAC SUFF_TAC `~(s2n s = 0)` THEN1
           (SRW_TAC [ARITH_ss][CANCEL_SUB, PRE_SUB1] THEN
            STRIP_TAC THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        METIS_TAC [string_numTheory.n2s_s2n]
      ],

      FULL_SIMP_TAC (srw_ss()) [sn_iso_num, sub1_11, PRE_SUB1] THEN
      ASM_SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss) [sn_iso_num, sub1_11] THEN
      FULL_SIMP_TAC (srw_ss()) [dFVs_lift] THEN
      SRW_TAC [][dFVs_def],

      Q.UNDISCH_THEN `~(x = 0)` ASSUME_TAC THEN
      Q.PAT_ASSUM `~(s' = n2s 0)` ASSUME_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [sn_iso_num, sub1_11, PRE_SUB1] THEN
      ASM_SIMP_TAC (srw_ss() ++ CONJ_ss) [sn_iso_num, sub1_11],

      ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [dFVs_lift] THEN
      DISJ2_TAC THEN Q.EXISTS_TAC `s2n x'` THEN
      FULL_SIMP_TAC (srw_ss()) [dFVs_def]
    ]
  ]);

(* and thus, the free variables of dLAM *)
val dFVs_dLAM = store_thm(
  "dFVs_dLAM",
  ``dFVs (dLAM i bod) = dFVs bod DELETE (n2s i)``,
  SRW_TAC [][dLAM_def, dFVs_sub, dFV_lift, dFVs_lift] THEN
  SRW_TAC [DNF_ss][EXTENSION] THEN
  SRW_TAC [][sn_iso_num, dFVs_def] THEN
  METIS_TAC []);
val _ = export_rewrites ["dFVs_dLAM"]

(* now that we know what the free variables of dLAM are, the definition
   below can go through *)
val (fromTerm_def,fromTerm_tpm) = binderLib.define_recursive_term_function`
  (fromTerm (VAR s) = dV (s2n s)) /\
  (fromTerm (t @@ u) = dAPP (fromTerm t) (fromTerm u)) /\
  (fromTerm (LAM v t) = dLAM (s2n v) (fromTerm t))
`
val _ = export_rewrites ["fromTerm_def"]

val fromTerm_eq0 = prove(
  ``((fromTerm t = dV j) = (t = VAR (n2s j))) /\
    ((dV j = fromTerm t) = (t = VAR (n2s j))) /\
    ((fromTerm t = dAPP d1 d2) = (?t1 t2. (t = t1 @@ t2) /\
                                          (d1 = fromTerm t1) /\
                                          (d2 = fromTerm t2)))``,
  SRW_TAC [][] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][fromTerm_def, dLAM_def, sn_iso_num] THEN METIS_TAC []);

(* Can now show that the appropriate functions in dB and term really do
   match up *)

(* free variables *)
val dFVs_fromTerm = store_thm(
  "dFVs_fromTerm",
  ``!N. dFVs (fromTerm N) = FV N``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);
val _ = export_rewrites ["dFVs_fromTerm"]

val IN_dFV = store_thm(
  "IN_dFV",
  ``x IN dFV t = n2s x IN dFVs t``,
  SRW_TAC [][dFVs_def]);

(* substitution *)
val fromTerm_subst = store_thm(
  "fromTerm_subst",
  ``!M. fromTerm ([N/v] M) = sub (fromTerm N) (s2n v) (fromTerm M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, fromTerm_def, sub_dLAM, IN_dFV]);


val lift_11 = store_thm(
  "lift_11",
  ``!M1 M2 n. (lift M1 n = lift M2 n) = (M1 = M2)``,
  Induct_on `M1` THEN SRW_TAC [][] THEN Cases_on `M2` THEN
  SRW_TAC [][] THEN DECIDE_TAC);

val fromTerm_eqlam = prove(
  ``(fromTerm t = dLAM i d) = ?t0. (t = LAM (n2s i) t0) /\ (d = fromTerm t0)``,
  EQ_TAC THENL [
    Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
    SRW_TAC [][fromTerm_def, dLAM_def] THEN
    Cases_on `i = s2n v` THENL [
      FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm, fresh_dpm_sub, dFV_lift,
                               nomsetTheory.is_perm_injective, lift_11],
      `~(i IN dFV (fromTerm t0)) /\ ~(s2n v IN dFV d)`
         by (FIRST_X_ASSUM (MP_TAC o AP_TERM ``dFV``) THEN
             REWRITE_TAC [EXTENSION] THEN
             DISCH_THEN (fn th => Q.SPEC_THEN `i + 1` MP_TAC th THEN
                                  Q.SPEC_THEN `s2n v + 1` MP_TAC th) THEN
             SRW_TAC [][IN_dFV, dFVs_sub, dFVs_lift]) THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM ``dpm [(n2s 0, n2s (i + 1))]``) THEN
      ASM_SIMP_TAC (srw_ss()) [fresh_dpm_sub, dFV_lift] THEN
      ASM_SIMP_TAC (srw_ss()) [GSYM fresh_dpm_sub, dFV_lift] THEN
      ONCE_REWRITE_TAC [dpm_flip_args] THEN
      `~(i + 1 IN dFV (sub (dV 0) (s2n v + 1) (lift (fromTerm t0) 0)))`
         by (SRW_TAC [][dFVs_sub, IN_dFV] THEN
             SRW_TAC [][dFVs_def, dFV_lift]) THEN
      ASM_SIMP_TAC (srw_ss())[GSYM fresh_dpm_sub] THEN
      ASM_SIMP_TAC (srw_ss()) [sub_15a, dFV_lift] THEN
      ASM_SIMP_TAC (srw_ss()) [fresh_dpm_sub, dFV_lift] THEN
      `[(n2s (i + 1), n2s (s2n v + 1))] = inc_pm 0 [(n2s i, v)]`
         by SRW_TAC [][inc_pm_def, ginc_0] THEN
      ASM_SIMP_TAC bool_ss [GSYM lift_dpm, lift_11] THEN
      SRW_TAC [][] THEN ONCE_REWRITE_TAC [GSYM fromTerm_tpm] THEN
      Q.EXISTS_TAC `tpm [(n2s i,v)] t0` THEN
      SRW_TAC [][LAM_eq_thm, sn_iso_num] THEN
      FULL_SIMP_TAC (srw_ss()) [IN_dFV, tpm_flip_args]
    ],
    SRW_TAC [][] THEN SRW_TAC [][fromTerm_def]
  ])

val fromTerm_eqn = save_thm(
  "fromTerm_eqn",
  CONJ fromTerm_eq0 fromTerm_eqlam)

(* fromTerm is injective *)
val fromTerm_11 = store_thm(
  "fromTerm_11",
  ``!t1 t2. (fromTerm t1 = fromTerm t2) = (t1 = t2)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][fromTerm_def] THEN SRW_TAC [][fromTerm_eqn] THEN
  METIS_TAC []);



val onto_lemma = prove(
  ``!t i n. ~(i IN dFV t) ==>
            ?t0. t = sub (dV n) i (lift t0 n)``,
  Induct_on `t` THEN SRW_TAC [][] THENL [
    Cases_on `n = n'` THENL [
      Cases_on `i < n'` THENL [
        Q.EXISTS_TAC `dV i` THEN SRW_TAC [][],
        Q.EXISTS_TAC `dV (i - 1)` THEN SRW_TAC [ARITH_ss][]
      ],
      Cases_on `n < n'` THENL [
        Q.EXISTS_TAC `dV n` THEN SRW_TAC [ARITH_ss][],
        Q.EXISTS_TAC `dV (n - 1)` THEN SRW_TAC [ARITH_ss][]
      ]
    ],
    `?t0 t0'. (t = sub (dV n) i (lift t0 n)) /\
              (t' = sub (dV n) i (lift t0' n))`
       by METIS_TAC [] THEN
    Q.EXISTS_TAC `dAPP t0 t0'` THEN SRW_TAC [][],

    Q.REFINE_EXISTS_TAC `dABS t0` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `i + 1` MP_TAC) THEN
    SRW_TAC [ARITH_ss][]
  ])

val onto_lemma2 = prove(
  ``!t. ?j. !i. i IN dFV t ==> i < j``,
  Induct THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][],
    Q.EXISTS_TAC `if j < j' then j' else j` THEN
    SRW_TAC [ARITH_ss][] THEN RES_TAC THEN DECIDE_TAC,
    SRW_TAC [DNF_ss][] THEN
    Q.EXISTS_TAC `SUC j` THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN DECIDE_TAC
  ])

val dfresh_exists = store_thm(
  "dfresh_exists",
  ``!t. ?v. ~(v IN dFV t)``,
  STRIP_TAC THEN Q.SPEC_THEN `t` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.EXISTS_TAC `j` THEN STRIP_TAC THEN RES_TAC THEN
  FULL_SIMP_TAC (srw_ss()) []);

(* a cases theorem for dB based around dLAM rather than dSUB *)
val db_cases' = store_thm(
  "db_cases'",
  ``!t. (?i. t = dV i) \/ (?t0 t1. t = dAPP t0 t1) \/
        (?i t0. t = dLAM i t0)``,
  Cases_on `t` THEN SRW_TAC [][dLAM_def] THEN
  Q.MATCH_ABBREV_TAC `?i t0. p = sub (dV 0) (i + 1) (lift t0 0)` THEN
  `?i. !j. j IN dFV p ==> j < i` by METIS_TAC [onto_lemma2] THEN
  `~(i + 1 IN dFV p)`
     by (STRIP_TAC THEN RES_TAC THEN DECIDE_TAC) THEN
  METIS_TAC [onto_lemma]);

val sub_nsub = store_thm(
  "sub_nsub",
  ``!N i n M.
       n <= i ==>
       (sub N i M = nsub N n (sub (dV n) (i + 1) (lift M n)))``,
  Induct_on `M` THEN SRW_TAC [][] THENL [
    SRW_TAC [ARITH_ss][] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    SRW_TAC [ARITH_ss][],
    SRW_TAC [ARITH_ss][]
  ]);


(* Nipkow's definition of beta reduction *)
val (dbeta_rules, dbeta_ind, dbeta_cases) = Hol_reln`
  (!s t. dbeta (dAPP (dABS s) t) (nsub t 0 s)) /\
  (!s t u. dbeta s t ==> dbeta (dAPP s u) (dAPP t u)) /\
  (!s t u. dbeta s t ==> dbeta (dAPP u s) (dAPP u t)) /\
  (!s t. dbeta s t ==> dbeta (dABS s) (dABS t))
`;

(* all of the "lambda-calculus" redexes reduce appropriately under dbeta *)
val alt_dbeta_rule = store_thm(
  "alt_dbeta_rule",
  ``dbeta (dAPP (dLAM i M) N) (sub N i M)``,
  SRW_TAC [][dLAM_def] THEN
  Q_TAC SUFF_TAC `sub N i M =
                  nsub N 0 (sub (dV 0) (i + 1) (lift M 0))`
        THEN1 (DISCH_THEN SUBST1_TAC THEN
               MATCH_ACCEPT_TAC (hd (CONJUNCTS dbeta_rules))) THEN
  MATCH_MP_TAC sub_nsub THEN SRW_TAC [][]);

(* an alternative reduction relation that is a stepping stone between
   dbeta and beta-reduction on quotiented terms *)
val (dbeta'_rules, dbeta'_ind, dbeta'_cases) = Hol_reln`
  (!i M N. dbeta' (dAPP (dLAM i M) N) (sub N i M)) /\
  (!M N Z. dbeta' M N ==> dbeta' (dAPP M Z) (dAPP N Z)) /\
  (!M N Z. dbeta' M N ==> dbeta' (dAPP Z M) (dAPP Z N)) /\
  (!M N i. dbeta' M N ==> dbeta' (dLAM i M) (dLAM i N))
`;

val dABS_renamed = store_thm(
  "dABS_renamed",
  ``!M. ~(v IN dFV (dABS M)) ==> ?t0. dABS M = dLAM v t0``,
  SRW_TAC [][dLAM_def] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `v + 1` MP_TAC) THEN
  SRW_TAC [ARITH_ss][onto_lemma])

val dbeta'_dpm = prove(
  ``!M N. dbeta' M N ==> !pi. dbeta' (dpm pi M) (dpm pi N)``,
  HO_MATCH_MP_TAC dbeta'_ind THEN SRW_TAC [][dpm_sub, dbeta'_rules]);

val dbeta'_dpm_calc = store_thm(
  "dbeta'_dpm_calc",
  ``!M N. dbeta' (dpm pi M) N = dbeta' M (dpm (REVERSE pi) N)``,
  METIS_TAC [dbeta'_dpm, nomsetTheory.is_perm_inverse, dpm_is_perm])

(* We can construct a lift permutation.
     inc_as_pm lim n
   constructs a permutation that will bring about the effect of
     lift M lim
   as long as n is as big as the biggest free index in M
*)
val lifting_pm_def = Define`
  lifting_pm lim n = if n < lim then []
                    else if n = lim then [(n2s n, n2s (n + 1))]
                    else lifting_pm lim (n - 1) ++ [(n2s n, n2s (n + 1))]
`

val lifting_pm_behaves = store_thm(
  "lifting_pm_behaves",
  ``!n lim i.
      lswapstr (lifting_pm lim n) (n2s i) =
          if i < lim then n2s i
          else if i <= n then n2s (i + 1)
          else if i = n + 1 then n2s lim
          else n2s i``,
  Induct THEN ONCE_REWRITE_TAC [lifting_pm_def] THENL [
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    REPEAT GEN_TAC THEN Cases_on `SUC n < lim` THENL [
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `i < lim` THEN1 SRW_TAC [][] THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      SRW_TAC [][] THEN DECIDE_TAC,

      ASM_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `SUC n = lim` THENL [
        ASM_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `i < lim` THEN1 SRW_TAC [ARITH_ss][] THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        SRW_TAC [ARITH_ss][] THEN
        SRW_TAC [ARITH_ss][basic_swapTheory.swapstr_def],

        ASM_SIMP_TAC (srw_ss()) [basic_swapTheory.lswapstr_APPEND] THEN
        Cases_on `i < lim` THEN1
          SRW_TAC [ARITH_ss][basic_swapTheory.swapstr_def] THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `i <= n` THEN1
          SRW_TAC [ARITH_ss][basic_swapTheory.swapstr_def] THEN
        Cases_on `i = SUC n` THEN1 SRW_TAC [ARITH_ss][] THEN
        ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
        SRW_TAC [ARITH_ss][]
      ]
    ]
  ]);

(* interaction of inc_pm with lifting_pm *)
val inc_pm0_lifting_pm = store_thm(
  "inc_pm0_lifting_pm",
  ``!m n. inc_pm 0 (lifting_pm m n) = lifting_pm (m + 1) (n + 1)``,
  Induct_on `n` THEN ONCE_REWRITE_TAC [lifting_pm_def] THENL [
    SRW_TAC [][ginc_0] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

    SRW_TAC [][ginc_0, inc_pm_APPEND, ADD1]
  ])

val lifts_are_specific_dpms = store_thm(
  "lifts_are_specific_dpms",
  ``!M n. (!i. i IN dFV M ==> i <= n) ==>
          !m. lift M m = dpm (lifting_pm m n) M``,
  Induct THEN SRW_TAC [][] THENL [
    SRW_TAC [][lifting_pm_behaves],
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [inc_pm0_lifting_pm] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
    Cases_on `i = 0` THENL [
      SRW_TAC [][],
      RES_TAC THEN DECIDE_TAC
    ]
  ]);

val lifts_are_dpms = store_thm(
  "lifts_are_dpms",
  ``!M n. ?pi. lift M n = dpm pi M``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `M` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.EXISTS_TAC `lifting_pm n j` THEN MATCH_MP_TAC lifts_are_specific_dpms THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN DECIDE_TAC);

val dbeta'_lift = store_thm(
  "dbeta'_lift",
  ``dbeta' (lift M n) (lift N n) = dbeta' M N``,
  Q.SPEC_THEN `M` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.SPEC_THEN `N` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.ABBREV_TAC `k = if j < j' then j' else j` THEN
  `(lift M n = dpm (lifting_pm n k) M) /\ (lift N n = dpm (lifting_pm n k) N)`
     by (CONJ_TAC THEN MATCH_MP_TAC lifts_are_specific_dpms THEN
         REPEAT STRIP_TAC THEN RES_TAC THEN Q.UNABBREV_TAC `k` THEN
         DECIDE_TAC) THEN
  SRW_TAC [][dbeta'_dpm_calc, nomsetTheory.is_perm_inverse])

val dbeta_dbeta' = store_thm(
  "dbeta_dbeta'",
  ``!M N. dbeta M N ==> dbeta' M N``,
  HO_MATCH_MP_TAC dbeta_ind THEN SRW_TAC [][dbeta'_rules] THENL [
    Q.SPEC_THEN `dABS s` STRIP_ASSUME_TAC db_cases' THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss()) [dLAM_def] THEN
    SRW_TAC [][GSYM sub_nsub] THEN
    SRW_TAC [][GSYM dLAM_def, dbeta'_rules],

    `?v. ~(v IN dFV (dABS s)) /\ ~(v IN dFV (dABS t))`
       by (Q_TAC SUFF_TAC `?v. ~(v IN dFV (dAPP (dABS s) (dABS t)))`
                 THEN1 SRW_TAC [][] THEN
           METIS_TAC [dfresh_exists]) THEN
    `?s' t'. (dABS s = dLAM v s') /\ (dABS t = dLAM v t')`
       by METIS_TAC [dABS_renamed] THEN
    Q_TAC SUFF_TAC `dbeta' s' t'` THEN1 SRW_TAC [][dbeta'_rules] THEN
    FULL_SIMP_TAC (srw_ss()) [dLAM_def, fresh_dpm_sub, dFV_lift,
                              dbeta'_dpm_calc, dbeta'_lift]
  ]);

(* nsub must be icky - just look at how it behaves under permutations *)
val dpm_nsub = store_thm(
  "dpm_nsub",
  ``!M i pi.
       dpm pi (nsub M i N) = nsub (dpm pi M) i (dpm (inc_pm i pi) N)``,
  Induct_on `N` THENL [
    SIMP_TAC (srw_ss()) [] THEN REPEAT GEN_TAC THEN Cases_on `i < n` THENL [
      ASM_SIMP_TAC (srw_ss()) [] THEN
      `lswapstr (inc_pm i pi) (n2s n) = ginc i (lswapstr pi (n2s (n - 1)))`
         by (SRW_TAC [][lswapstr_inc_pm] THEN
             FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      Q.ABBREV_TAC `s = lswapstr pi (n2s (n - 1))` THEN
      SRW_TAC [][ginc_def] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      Cases_on `s2n s < i` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

      ASM_SIMP_TAC (srw_ss()) [] THEN Cases_on `i = n` THENL [
        ASM_SIMP_TAC (srw_ss()) [] THEN
        SRW_TAC [][lswapstr_inc_pm],
        `lswapstr (inc_pm i pi) (n2s n) = ginc i (lswapstr pi (n2s n))`
           by SRW_TAC [ARITH_ss][lswapstr_inc_pm] THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        Q.ABBREV_TAC `s = lswapstr pi (n2s n)` THEN
        SRW_TAC [][ginc_def] THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
        Cases_on `s2n s < i` THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
      ]
    ],

    SRW_TAC [][],

    SRW_TAC [][] THEN ASM_SIMP_TAC (srw_ss()) [lift_dpm] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    Q.ID_SPEC_TAC `i` THEN Induct_on `pi` THEN1 SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ginc_0] THEN
    SRW_TAC [][ginc_def]
  ]);

val dbeta_dpm = store_thm(
  "dbeta_dpm",
  ``!M N. dbeta M N ==> !pi. dbeta (dpm pi M) (dpm pi N)``,
  HO_MATCH_MP_TAC dbeta_ind THEN SRW_TAC [][dbeta_rules, dpm_nsub])

val dbeta_lift = store_thm(
  "dbeta_lift",
  ``dbeta (lift M n) (lift N n) = dbeta M N``,
  Q.SPEC_THEN `M` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.SPEC_THEN `N` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.ABBREV_TAC `k = if j < j' then j' else j` THEN
  `(lift M n = dpm (lifting_pm n k) M) /\ (lift N n = dpm (lifting_pm n k) N)`
     by (CONJ_TAC THEN MATCH_MP_TAC lifts_are_specific_dpms THEN
         REPEAT STRIP_TAC THEN RES_TAC THEN Q.UNABBREV_TAC `k` THEN
         DECIDE_TAC) THEN
  METIS_TAC [dbeta_dpm, nomsetTheory.is_perm_inverse, dpm_is_perm])

val dbeta'_dbeta = store_thm(
  "dbeta'_dbeta",
  ``!M N. dbeta' M N ==> dbeta M N``,
  HO_MATCH_MP_TAC dbeta'_ind THEN
  SRW_TAC [][dbeta_rules, alt_dbeta_rule] THEN
  SRW_TAC [][dLAM_def, fresh_dpm_sub, dFV_lift, dbeta_rules, dbeta_dpm,
             dbeta_lift])

val dbeta_dbeta'_eqn = store_thm(
  "dbeta_dbeta'_eqn",
  ``dbeta = dbeta'``,
  SRW_TAC [][FUN_EQ_THM] THEN METIS_TAC [dbeta'_dbeta, dbeta_dbeta'])

(* We've shown that dbeta and dbeta' are equivalent.  Now we use this to
   show that dbeta matches up with beta on terms, and then we're all done *)

(* both of the next two proofs begin by rewriting dbeta to dbeta', using
   dbeta_dbeta'_eqn *)
open chap3Theory
val ccbeta_dbeta1 = prove(
  ``!M N. compat_closure beta M N ==> dbeta (fromTerm M) (fromTerm N)``,
  REWRITE_TAC [dbeta_dbeta'_eqn] THEN HO_MATCH_MP_TAC compat_closure_ind THEN
  SRW_TAC [][beta_def, dbeta'_rules] THEN
  SRW_TAC [][fromTerm_subst, dbeta'_rules])

val ccbeta_dbeta2 = prove(
  ``!M N. dbeta M N ==> !M0 N0. (M = fromTerm M0) /\ (N = fromTerm N0) ==>
                                compat_closure beta M0 N0``,
  REWRITE_TAC [dbeta_dbeta'_eqn] THEN HO_MATCH_MP_TAC dbeta'_ind THEN
  SRW_TAC [][fromTerm_eqn, compat_closure_rules] THEN
  FULL_SIMP_TAC (srw_ss()) [fromTerm_11] THEN
  SRW_TAC [][compat_closure_rules] THEN
  `sub (fromTerm t2) i (fromTerm t0) = fromTerm ([t2/n2s i] t0)`
     by SRW_TAC [][fromTerm_subst] THEN
  FULL_SIMP_TAC (srw_ss()) [fromTerm_11] THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (hd (CONJUNCTS (SPEC_ALL compat_closure_rules))) THEN
  SRW_TAC [][beta_def] THEN METIS_TAC [])

val dbeta_ccbeta_eqn = store_thm(
  "dbeta_ccbeta_eqn",
  ``dbeta (fromTerm M) (fromTerm N) = compat_closure beta M N``,
  METIS_TAC [ccbeta_dbeta2, ccbeta_dbeta1]);

(* to finish, a demonstration that fromTerm is also onto, using a size
   measure on dB terms.  Could alternatively prove an induction
   principle for dB in terms of dLAM.  *)
val dbsize_def = Define`
  (dbsize (dV i) = 1) /\
  (dbsize (dAPP d1 d2) = dbsize d1 + dbsize d2 + 1) /\
  (dbsize (dABS d) = dbsize d + 1)
`
val _ = export_rewrites ["dbsize_def"]

val dbsize_sub = store_thm(
  "dbsize_sub",
  ``!n i M. dbsize (sub (dV n) i M) = dbsize M``,
  Induct_on `M` THEN SRW_TAC [][]);
val _ = export_rewrites ["dbsize_sub"]

val dbsize_lift = store_thm(
  "dbsize_lift",
  ``!n M. dbsize (lift M n) = dbsize M``,
  Induct_on `M` THEN SRW_TAC [][]);
val _ = export_rewrites ["dbsize_lift"]

val dbsize_dLAM = store_thm(
  "dbsize_dLAM",
  ``dbsize (dLAM i t) = dbsize t + 1``,
  SRW_TAC [][dLAM_def])
val _ = export_rewrites ["dbsize_dLAM"]

val fromTerm_onto = store_thm(
  "fromTerm_onto",
  ``!d. ?t. (d = fromTerm t)``,
  GEN_TAC THEN completeInduct_on `dbsize d` THEN
  FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
  GEN_TAC THEN Q.SPEC_THEN `d` STRIP_ASSUME_TAC db_cases' THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    STRIP_TAC THEN Q.EXISTS_TAC `VAR (n2s i)` THEN SRW_TAC [][],
    SRW_TAC [][] THEN
    POP_ASSUM (fn th => Q.SPEC_THEN `t0` MP_TAC th THEN
                        Q.SPEC_THEN `t1` MP_TAC th) THEN
    SRW_TAC [ARITH_ss][] THEN
    Q.EXISTS_TAC `t' @@ t` THEN SRW_TAC [][],

    SRW_TAC [][] THEN POP_ASSUM (Q.SPEC_THEN `t0` MP_TAC) THEN
    SRW_TAC [ARITH_ss][] THEN
    Q.EXISTS_TAC `LAM (n2s i) t` THEN SRW_TAC [][]
  ]);

val _ = export_theory();
