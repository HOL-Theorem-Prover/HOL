open HolKernel boolLib Parse bossLib pred_setTheory termTheory BasicProvers

open arithmeticTheory boolSimps

local open string_numTheory chap2Theory chap3Theory in end

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "pure_dB"

val _ = set_fixity "=" (Infix(NONASSOC, 100))

(* the type of pure de Bruijn terms *)
val _ = Datatype`pdb = dV num | dAPP pdb pdb | dABS pdb`

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

val IN_dFV_thm = store_thm(
  "IN_dFV_thm",
  ``(j IN dFV (dV i) = (i = j)) /\
    (j IN dFV (dAPP t u) = j IN dFV t \/ j IN dFV u) /\
    (j IN dFV (dABS t) = j + 1 IN dFV t)``,
  SRW_TAC [][dFV_def, EQ_IMP_THM] THENL [
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [ADD1],
    Q.EXISTS_TAC `j + 1` THEN SRW_TAC [ARITH_ss][]
  ]);
val _ = export_rewrites ["IN_dFV_thm"]

val FINITE_dFV = store_thm(
  "FINITE_dFV",
  ``FINITE (dFV t)``,
  Induct_on `t` THEN SRW_TAC [][dFV_def]);
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
  SIMP_TAC (srw_ss()) [nomsetTheory.permeq_thm, lswapstr_inc_pm,
                       FUN_EQ_THM]);

(* definition of permutation over de Bruijn terms *)
val raw_dpm_def = Define`
  (raw_dpm pi (dV i) = dV (s2n (lswapstr pi (n2s i)))) /\
  (raw_dpm pi (dAPP t u) = dAPP (raw_dpm pi t) (raw_dpm pi u)) /\
  (raw_dpm pi (dABS t) = dABS (raw_dpm (inc_pm 0 pi) t))
`;
val _ = export_rewrites ["raw_dpm_def"]
val _ = overload_on("d_pmact",``mk_pmact raw_dpm``);
val _ = overload_on("dpm",``pmact d_pmact``);

(* proof that dB terms + dpm form a nominal set *)
val dpm_raw = store_thm(
  "dpm_raw",
  ``dpm = raw_dpm``,
  SRW_TAC [][GSYM nomsetTheory.pmact_bijections] THEN
  SIMP_TAC (srw_ss()) [nomsetTheory.is_pmact_def] THEN REPEAT CONJ_TAC THENL [
    Induct_on `x` THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][nomsetTheory.pmact_decompose, inc_pm_APPEND],
    SIMP_TAC (srw_ss()) [FUN_EQ_THM, GSYM RIGHT_FORALL_IMP_THM,
                         nomsetTheory.permeq_thm] THEN
    Induct_on `x` THEN SRW_TAC [][lswapstr_inc_pm]
  ]);
val dpm_thm = save_thm(
"dpm_thm",
raw_dpm_def |> SUBS [GSYM dpm_raw]);
val _ = export_rewrites ["dpm_thm"]

(* being a nominal set gives us properties of dpm "for free" *)

(* dFVs gives the free indices of a dB term as strings *)
val dFVs_def = Define`dFVs t = IMAGE n2s (dFV t)`
val IN_dFVs_thm = store_thm(
  "IN_dFVs_thm",
  ``(s IN dFVs (dV i) = (i = s2n s)) /\
    (s IN dFVs (dAPP t u) = s IN dFVs t \/ s IN dFVs u) /\
    (s IN dFVs (dABS t) = n2s (s2n s + 1) IN dFVs t)``,
  SRW_TAC [][dFVs_def] THENL [
    SRW_TAC [][EQ_IMP_THM],
    METIS_TAC [],
    SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `s2n s` THEN SRW_TAC [][]
  ]);
val _ = export_rewrites ["IN_dFVs_thm"]

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
    FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [],
    METIS_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SRW_TAC [][ginc_0]
  ]);

val dpm_fresh = store_thm(
  "dpm_fresh",
  ``!x y. ~(x IN dFVs t) /\ ~(y IN dFVs t) ==> (dpm [(x,y)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][ginc_0] THEN
  SRW_TAC [][basic_swapTheory.swapstr_def] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val dpm_supp = store_thm(
  "dpm_supp",
  ``supp d_pmact = dFVs``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN SRW_TAC [][] THEN
  MATCH_MP_TAC nomsetTheory.supp_unique_apart THEN
  SRW_TAC [][dpm_apart, nomsetTheory.support_def] THEN
  MATCH_MP_TAC dpm_fresh THEN SRW_TAC [][]);
val _ = export_rewrites ["dpm_supp"]


(* this is enough to establish de Bruijn terms as a nominal type for the
   purposes of function definition.  I.e., now we can define functions
   that have dB terms as their range *)
val _ = binderLib.type_db :=
        Binarymap.insert(!binderLib.type_db, {Thy="pure_dB", Name = "pdb"},
                         binderLib.NTI {
                         nullfv = ``dABS (dV 0)``,
                         pm_rewrites = [],
                         pm_constant = ``d_pmact``,
                         fv_rewrites = [],
                         recursion_thm = NONE,
                         binders = []})

(* substitution of a fresh variable is actually a permutation *)
val fresh_dpm_sub = store_thm(
  "fresh_dpm_sub",
  ``!i j M. ~(j IN dFV M) ==> (sub (dV j) i M = dpm [(n2s j, n2s i)] M)``,
  Induct_on `M` THEN SRW_TAC [][ginc_0]);

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
val nipkow_lift_lemma1 = store_thm(
  "nipkow_lift_lemma1",
  ``!t i k. i < k ==> (lift (lift t i) k = lift (lift t (k - 1)) i)``,
  Induct THEN SRW_TAC [ARITH_ss][])

(* result needed to establish the substitution lemma *)
val lift_sub = store_thm(
  "lift_sub",
  ``!M i N n.
       n <= i ==>
       (lift (sub M i N) n = sub (lift M n) (i + 1) (lift N n))``,
  Induct_on `N` THEN
  SRW_TAC [ARITH_ss][nipkow_lift_lemma1])

val sn_iso_num = prove(
  ``((s = n2s n) = (n = s2n s)) /\ ((n2s n = s) = (n = s2n s))``,
  METIS_TAC [string_numTheory.s2n_n2s, string_numTheory.n2s_s2n])

val IN_dFV_lift = store_thm(
  "IN_dFV_lift",
  ``!n m. m IN dFV (lift M n) = m IN dFV M /\ m < n \/
                                m - 1 IN dFV M /\ n < m``,
  Induct_on `M` THEN SRW_TAC [ARITH_ss][] THENL [
    METIS_TAC [],
    SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss ++ CONJ_ss)
             [EQ_IMP_THM]
  ])
val _ = export_rewrites ["IN_dFV_lift"]

(* The substitution lemma, in dB guise *)
val sub_lemma = store_thm(
  "sub_lemma",
  ``!M N i j L. ~(i = j) /\ ~(j IN dFV M) ==>
                (sub M i (sub N j L) =
                 sub (sub M i N) j (sub M i L))``,
  Induct_on `L` THEN
  SRW_TAC [][sub_14b, lift_sub] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][]);

(* which allows us to prove that substitution interacts with dLAM in the way
   we'd expect *)
val sub_dLAM = store_thm(
  "sub_dLAM",
  ``~(i IN dFV N) /\ ~(i = j) ==>
    (sub N j (dLAM i M) = dLAM i (sub N j M))``,
  SRW_TAC [][dLAM_def] THEN
  SRW_TAC [][Once sub_lemma] THEN
  SRW_TAC [][lift_sub]);

val dFVs_lift = store_thm(
  "dFVs_lift",
  ``!n. dFVs (lift M n) = { n2s m | m IN dFV M /\ m < n } UNION
                          { n2s (m + 1) | m IN dFV M /\ n <= m }``,
  SRW_TAC [][dFVs_def, EXTENSION, EQ_IMP_THM] THEN
  SRW_TAC [][] THENL [
    DISJ2_TAC THEN Q.EXISTS_TAC `x' - 1` THEN SRW_TAC [ARITH_ss][],
    SRW_TAC [ARITH_ss][]
  ]);

(* free variables of a substitution *)
val IN_dFV = store_thm(
  "IN_dFV",
  ``x IN dFV t = n2s x IN dFVs t``,
  SRW_TAC [][dFVs_def]);

val dFVs_sub1 = prove(
  ``!M j. j IN dFV N ==>
          (dFVs (sub M j N) = (dFVs N DELETE n2s j) UNION dFVs M)``,
  SIMP_TAC (srw_ss()) [EXTENSION] THEN Induct_on `N` THENL [
    SRW_TAC [CONJ_ss][],
    SRW_TAC [][] THEN METIS_TAC [IN_dFV, sub_14b],
    SRW_TAC [][dFVs_lift, IN_dFV, sn_iso_num] THEN METIS_TAC []
  ]);

val dFVs_sub = store_thm(
  "dFVs_sub",
  ``!M j. dFVs (sub M j N) = if j IN dFV N then
                               (dFVs N DELETE n2s j) UNION dFVs M
                             else dFVs N``,
  SRW_TAC [][EXTENSION, dFVs_sub1, sub_14b]);

(* and thus, the free variables of dLAM *)
val dFVs_dLAM = store_thm(
  "dFVs_dLAM",
  ``dFVs (dLAM i bod) = dFVs bod DELETE (n2s i)``,
  SRW_TAC [ARITH_ss][dLAM_def, dFVs_sub, dFVs_lift, EXTENSION, IN_dFV] THEN
  METIS_TAC [sn_iso_num]);
val _ = export_rewrites ["dFVs_dLAM"]

val dpm_ALPHA = store_thm(
  "dpm_ALPHA",
  ``u ∉ dFVs t ==> (dLAM (s2n u) (dpm [(u,v)] t) = dLAM (s2n v) t)``,
  SRW_TAC [][dLAM_def, lift_dpm] THEN
  `sub (dV 0) (s2n u + 1) (dpm [(ginc 0 u, ginc 0 v)] (lift t 0)) =
   dpm [(ginc 0 u, ginc 0 v)] (sub (dV 0) (s2n v + 1) (lift t 0))`
     by SRW_TAC [][dpm_sub, ginc_0] THEN
  POP_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC dpm_fresh THEN
  SRW_TAC [][dFVs_sub, ginc_0, dFVs_lift, IN_dFV] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val _ = augment_srw_ss [simpLib.name_ss "fromTerm_def" (rewrites [dpm_ALPHA])]

(* now that we know what the free variables of dLAM are, the definition
   below can go through *)
val (fromTerm_def,fromTerm_tpm) = binderLib.define_recursive_term_function`
  (fromTerm (VAR s) = dV (s2n s)) /\
  (fromTerm (t @@ u) = dAPP (fromTerm t) (fromTerm u)) /\
  (fromTerm (LAM v t) = dLAM (s2n v) (fromTerm t))
`
val _ = export_rewrites ["fromTerm_def"]
val _ = diminish_srw_ss ["fromTerm_def"]

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
  REWRITE_TAC [EXTENSION] THEN
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN METIS_TAC []);
val _ = export_rewrites ["dFVs_fromTerm"]

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
      FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm, fresh_dpm_sub,
                               nomsetTheory.pmact_injective, lift_11],
      `i ∉ dFV (fromTerm t0) /\ s2n v ∉ dFV d`
         by (FIRST_X_ASSUM (MP_TAC o AP_TERM ``dFV``) THEN
             REWRITE_TAC [EXTENSION] THEN
             DISCH_THEN (fn th => Q.SPEC_THEN `i + 1` MP_TAC th THEN
                                  Q.SPEC_THEN `s2n v + 1` MP_TAC th) THEN
             SRW_TAC [ARITH_ss][IN_dFV, dFVs_sub, dFVs_lift]) THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM ``dpm [(n2s 0, n2s (i + 1))]``) THEN
      ASM_SIMP_TAC std_ss [fresh_dpm_sub, IN_dFV_lift,
                           nomsetTheory.pmact_sing_inv] THEN
      ASM_SIMP_TAC (srw_ss()) [GSYM fresh_dpm_sub] THEN
      ONCE_REWRITE_TAC [nomsetTheory.pmact_flip_args] THEN
      `i + 1 ∉ dFV (sub (dV 0) (s2n v + 1) (lift (fromTerm t0) 0))`
         by (SRW_TAC [ARITH_ss][dFVs_sub, IN_dFV] THEN
             SRW_TAC [][dFVs_def]) THEN
      ASM_SIMP_TAC (srw_ss())[GSYM fresh_dpm_sub] THEN
      ASM_SIMP_TAC (srw_ss()) [sub_15a] THEN
      ASM_SIMP_TAC (srw_ss()) [fresh_dpm_sub] THEN
      `[(n2s (i + 1), n2s (s2n v + 1))] = inc_pm 0 [(n2s i, v)]`
         by SRW_TAC [][inc_pm_def, ginc_0] THEN
      ASM_SIMP_TAC bool_ss [GSYM lift_dpm, lift_11] THEN
      SRW_TAC [][] THEN ONCE_REWRITE_TAC [GSYM fromTerm_tpm] THEN
      Q.EXISTS_TAC `tpm [(n2s i,v)] t0` THEN
      SRW_TAC [][LAM_eq_thm, sn_iso_num] THEN
      FULL_SIMP_TAC (srw_ss()) [IN_dFV, nomsetTheory.pmact_flip_args]
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

(* an alternative reduction relation that is a stepping stone between
   dbeta and beta-reduction on quotiented terms *)
val (dbeta'_rules, dbeta'_ind, dbeta'_cases) = Hol_reln`
  (!i M N. dbeta' (dAPP (dLAM i M) N) (sub N i M)) /\
  (!M N Z. dbeta' M N ==> dbeta' (dAPP M Z) (dAPP N Z)) /\
  (!M N Z. dbeta' M N ==> dbeta' (dAPP Z M) (dAPP Z N)) /\
  (!M N i. dbeta' M N ==> dbeta' (dLAM i M) (dLAM i N))
`;

open chap3Theory
val dbeta'_ccbeta = store_thm(
  "dbeta'_ccbeta",
  ``!t u. dbeta' t u ==> !M N. (t = fromTerm M) /\ (u = fromTerm N) ==>
                               compat_closure beta M N``,
  HO_MATCH_MP_TAC dbeta'_ind THEN
  SRW_TAC [][fromTerm_eqn] THEN
  FULL_SIMP_TAC (srw_ss()) [fromTerm_11, compat_closure_rules] THEN
  MATCH_MP_TAC (hd (CONJUNCTS (SPEC_ALL compat_closure_rules))) THEN
  SRW_TAC [][beta_def] THEN MAP_EVERY Q.EXISTS_TAC [`n2s i`, `t0`] THEN
  SRW_TAC [][] THEN ONCE_REWRITE_TAC [GSYM fromTerm_11] THEN
  REWRITE_TAC [fromTerm_subst] THEN SRW_TAC [][]);
val ccbeta_dbeta' = store_thm(
  "ccbeta_dbeta'",
  ``!M N. compat_closure beta M N ==> dbeta' (fromTerm M) (fromTerm N)``,
  HO_MATCH_MP_TAC compat_closure_ind THEN
  SRW_TAC [][dbeta'_rules, beta_def] THEN
  SRW_TAC [][fromTerm_def, fromTerm_subst, dbeta'_rules]);

val dbeta'_eq_ccbeta = store_thm(
  "dbeta'_eq_ccbeta",
  ``dbeta' (fromTerm M) (fromTerm N) = compat_closure beta M N``,
  METIS_TAC [ccbeta_dbeta', dbeta'_ccbeta]);

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

val sub_nsub15a = store_thm(
  "sub_nsub15a",
  ``!d2 d1 i j. i + 1 NOTIN dFV d2 /\ j <= i ==>
                (sub d1 i (nsub (dV i) j d2) = nsub d1 j d2)``,
  Induct THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [],
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
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

val dABS_renamed = store_thm(
  "dABS_renamed",
  ``!M. ~(v IN dFV (dABS M)) ==> ?t0. dABS M = dLAM v t0``,
  SRW_TAC [][dLAM_def] THEN SRW_TAC [ARITH_ss][onto_lemma])

(* conversely, the de Bruijn redexes reduce under dbeta' *)
val alt_dbeta'_rule = store_thm(
  "alt_dbeta'_rule",
  ``dbeta' (dAPP (dABS t) u) (nsub u 0 t)``,
  `?z. ~(z IN dFV (dABS t))` by METIS_TAC [dfresh_exists] THEN
  `?t0. dABS t = dLAM z t0` by METIS_TAC [dABS_renamed] THEN
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `nsub u 0 t = sub u z t0` THEN1 SRW_TAC [][dbeta'_rules] THEN
  FULL_SIMP_TAC (srw_ss()) [dLAM_def] THEN
  SRW_TAC [][GSYM sub_nsub]);

val dbeta'_dpm = prove(
  ``!M N. dbeta' M N ==> !pi. dbeta' (dpm pi M) (dpm pi N)``,
  HO_MATCH_MP_TAC dbeta'_ind THEN SRW_TAC [][dpm_sub, dbeta'_rules]);

val dbeta'_dpm_calc = store_thm(
  "dbeta'_dpm_calc",
  ``!M N. dbeta' (dpm pi M) N = dbeta' M (dpm (REVERSE pi) N)``,
  METIS_TAC [dbeta'_dpm, nomsetTheory.pmact_inverse])

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

        ASM_SIMP_TAC (srw_ss()) [nomsetTheory.pmact_decompose] THEN
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
    Cases_on `i` THENL [
      SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss()) [ADD1]
    ]
  ]);

val lifts_are_dpms = store_thm(
  "lifts_are_dpms",
  ``!M n. ?pi. lift M n = dpm pi M``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `M` STRIP_ASSUME_TAC onto_lemma2 THEN
  Q.EXISTS_TAC `lifting_pm n j` THEN MATCH_MP_TAC lifts_are_specific_dpms THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN DECIDE_TAC);

val dABS_rules_are_dLAM_compatible = store_thm(
  "dABS_rules_are_dLAM_compatible",
  ``(!p t u. R (dpm p t) (dpm p u) = R t u) ==>
    ((!t u. R t u ==> R (dABS t) (dABS u))
      =
     !i t u. R t u ==> R (dLAM i t) (dLAM i u))``,
  STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    SRW_TAC [][dLAM_def, fresh_dpm_sub] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `t` STRIP_ASSUME_TAC onto_lemma2 THEN
    Q.SPEC_THEN `u` STRIP_ASSUME_TAC onto_lemma2 THEN
    Q.ABBREV_TAC `k = if j < j' then j' else j` THEN
    `(lift t 0 = dpm (lifting_pm 0 k) t) /\
     (lift u 0 = dpm (lifting_pm 0 k) u)`
        by (CONJ_TAC THEN MATCH_MP_TAC lifts_are_specific_dpms THEN
            REPEAT STRIP_TAC THEN RES_TAC THEN Q.UNABBREV_TAC `k` THEN
            DECIDE_TAC) THEN
    SRW_TAC [][],

    `?v. ~(v IN dFV (dABS t)) /\ ~(v IN dFV (dABS u))`
       by (Q_TAC SUFF_TAC `?v. ~(v IN dFV (dAPP (dABS t) (dABS u)))`
                 THEN1 SRW_TAC [][] THEN
           METIS_TAC [dfresh_exists]) THEN
    `?t' u'. (dABS t = dLAM v t') /\ (dABS u = dLAM v u')`
       by METIS_TAC [dABS_renamed] THEN
    Q_TAC SUFF_TAC `R t' u'` THEN1 SRW_TAC [][] THEN
    Q.UNDISCH_THEN `R t u` MP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [dLAM_def, fresh_dpm_sub] THEN
    Q.SPEC_THEN `t'` STRIP_ASSUME_TAC onto_lemma2 THEN
    Q.SPEC_THEN `u'` STRIP_ASSUME_TAC onto_lemma2 THEN
    Q.ABBREV_TAC `k = if j < j' then j' else j` THEN
    `(lift t' 0 = dpm (lifting_pm 0 k) t') /\
     (lift u' 0 = dpm (lifting_pm 0 k) u')`
        by (CONJ_TAC THEN MATCH_MP_TAC lifts_are_specific_dpms THEN
            REPEAT STRIP_TAC THEN RES_TAC THEN Q.UNABBREV_TAC `k` THEN
            DECIDE_TAC) THEN
    SRW_TAC [][]
  ]);

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
  SRW_TAC [][dbeta'_dpm_calc, nomsetTheory.pmact_inverse])

val dbeta_dbeta' = store_thm(
  "dbeta_dbeta'",
  ``!M N. dbeta M N ==> dbeta' M N``,
  HO_MATCH_MP_TAC dbeta_ind THEN SRW_TAC [][dbeta'_rules] THENL [
    SRW_TAC [][alt_dbeta'_rule],
    Q_TAC SUFF_TAC `!p t u. dbeta' (dpm p t) (dpm p u) = dbeta' t u`
          THEN1 METIS_TAC [dABS_rules_are_dLAM_compatible, dbeta'_rules] THEN
    SRW_TAC [][dbeta'_dpm_calc, nomsetTheory.pmact_inverse]
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
  METIS_TAC [dbeta_dpm, nomsetTheory.pmact_inverse])

val dbeta'_dbeta = store_thm(
  "dbeta'_dbeta",
  ``!M N. dbeta' M N ==> dbeta M N``,
  HO_MATCH_MP_TAC dbeta'_ind THEN
  SRW_TAC [][dbeta_rules, alt_dbeta_rule] THEN
  METIS_TAC [dABS_rules_are_dLAM_compatible, dbeta_rules, dbeta_dpm,
             nomsetTheory.pmact_inverse]);

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

(* ----------------------------------------------------------------------
    toTerm (inverse of fromTerm)
   ---------------------------------------------------------------------- *)
val toTerm_def = new_specification(
  "toTerm_def", ["toTerm"],
  CONV_RULE SKOLEM_CONV fromTerm_onto);

val fromtoTerm = save_thm("fromtoTerm", GSYM toTerm_def)
val _ = export_rewrites ["fromtoTerm"]

val toTerm_11 = Store_thm(
  "toTerm_11",
  ``(toTerm d1 = toTerm d2) <=> (d1 = d2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `fromTerm`) THEN
  SRW_TAC [][]);

val toTerm_onto = store_thm(
  "toTerm_onto",
  ``!t. ?d. toTerm d = t``,
  METIS_TAC [fromTerm_11, fromtoTerm]);

val tofromTerm = Store_thm(
  "tofromTerm",
  ``toTerm (fromTerm t) = t``,
  METIS_TAC [toTerm_onto, toTerm_11, fromtoTerm])

val toTerm_eqn = store_thm(
  "toTerm_eqn",
  ``(toTerm x = y) <=> (fromTerm y = x)``,
  SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][])

val toTerm_thm = Store_thm(
  "toTerm_thm",
  ``(toTerm (dV i) = VAR (n2s i)) /\
    (toTerm (dAPP M N) = toTerm M @@ toTerm N) /\
    (toTerm (dLAM i M) = LAM (n2s i) (toTerm M))``,
  SRW_TAC [][toTerm_eqn]);

val lemma = prove(
  ``!i j. i + j + 1 NOTIN dFV M ==>
          (sub (dV j) (i + j + 1) (lift (nsub (dV (i + j)) j M) j) = M)``,
  Induct_on `M` THEN SRW_TAC [][] THENL [
    SRW_TAC [ARITH_ss][],
    SRW_TAC [ARITH_ss][],
    SRW_TAC [ARITH_ss][],
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)[] THEN
    FIRST_X_ASSUM (Q.SPECL_THEN [`i`, `j + 1`] MP_TAC) THEN
    SRW_TAC [ARITH_ss][]
  ]);

val dABS_dLAM = store_thm(
  "dABS_dLAM",
  ``i + 1 NOTIN dFV M ==> (dABS M = dLAM i (nsub (dV i) 0 M))``,
  SIMP_TAC (srw_ss()) [dLAM_def] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  Q.SPECL_THEN [`i`, `0`] ASSUME_TAC lemma THEN
  FULL_SIMP_TAC (srw_ss()) []);

val dABS_dLAM_exists = store_thm(
  "dABS_dLAM_exists",
  ``!M. ?i N. dABS M = dLAM i N``,
  Q.X_GEN_TAC `M` THEN Q.SPEC_THEN `dABS M` STRIP_ASSUME_TAC db_cases' THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);

val toTerm_dABS = store_thm(
  "toTerm_dABS",
  ``s2n v + 1 NOTIN dFV M ==>
      (toTerm (dABS M) = LAM v (toTerm (nsub (dV (s2n v)) 0 M)))``,
  SRW_TAC [][toTerm_eqn, dABS_dLAM]);

(* ----------------------------------------------------------------------
    bnf
   ---------------------------------------------------------------------- *)

val _ = overload_on ("is_dABS", ``\d. is_abs (toTerm d)``)

val is_dABS_thm = Store_thm(
  "is_dABS_thm",
  ``(is_dABS (dV v) = F) /\
    (is_dABS (dAPP d1 d2) = F) /\
    (is_dABS (dABS d) = T) /\
    (is_dABS (dLAM v d) = T)``,
  SRW_TAC [][] THEN
  `?i N. dABS d = dLAM i N` by METIS_TAC [dABS_dLAM_exists] THEN
  SRW_TAC [][]);

val is_dABS_vnsub_invariant = Store_thm(
  "is_dABS_vnsub_invariant",
  ``!d i j. is_dABS (nsub (dV i) j d) <=> is_dABS d``,
  Induct THEN SRW_TAC [][]);

val is_dABS_vsub_invariant = Store_thm(
  "is_dABS_vsub_invariant",
  ``!d i j. is_dABS (sub (dV i) j d) <=> is_dABS d``,
  Induct THEN SRW_TAC [][]);

val is_dABS_lift_invariant = Store_thm(
  "is_dABS_lift_invariant",
  ``!d j. is_dABS (lift d j) = is_dABS d``,
  Induct THEN SRW_TAC [][]);

val dbnf_def = Define`
  (dbnf (dV i) = T) /\
  (dbnf (dAPP d1 d2) = dbnf d1 /\ dbnf d2 /\ ~is_dABS d1) /\
  (dbnf (dABS d) = dbnf d)
`;
val _ = export_rewrites ["dbnf_def"]

val dbnf_vnsub_invariant = Store_thm(
  "dbnf_vnsub_invariant",
  ``!d i j. dbnf (nsub (dV i) j d) <=> dbnf d``,
  Induct THEN SRW_TAC [][]);

val dbnf_vsub_invariant = Store_thm(
  "dbnf_vsub_invariant",
  ``!d i j. dbnf (sub (dV i) j d) <=> dbnf d``,
  Induct THEN SRW_TAC [][]);

val dbnf_lift_invariant = Store_thm(
  "dbnf_lift_invariant",
  ``!d j. dbnf (lift d j) = dbnf d``,
  Induct THEN SRW_TAC [][]);

val dbnf_dLAM = Store_thm(
  "dbnf_dLAM",
  ``dbnf (dLAM i d) = dbnf d``,
  SRW_TAC [][dLAM_def]);

val dbnf_fromTerm = Store_thm(
  "dbnf_fromTerm",
  ``!t. dbnf (fromTerm t) = bnf t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val bnf_toTerm = Store_thm(
  "bnf_toTerm",
  ``!d. bnf (toTerm d) = dbnf d``,
  METIS_TAC [fromTerm_onto, fromtoTerm, dbnf_fromTerm]);

(* ----------------------------------------------------------------------
    Eta reduction
   ---------------------------------------------------------------------- *)

(* Nipkow's definition *)
val (neta_rules, neta_ind, neta_cases) = Hol_reln`
  (!t u.    ~(0 IN dFV t) ==> neta (dABS (dAPP t (dV 0))) (nsub u 0 t)) /\
  (!t t' u. neta t t'     ==> neta (dAPP t u) (dAPP t' u)) /\
  (!t u u'. neta u u'     ==> neta (dAPP t u) (dAPP t u')) /\
  (!t t'.   neta t t'     ==> neta (dABS t) (dABS t'))
`;

(* "traditional" style, using dLAM *)
val (eta_rules, eta_ind, eta_cases) = Hol_reln`
  (!t i.    ~(i IN dFV t) ==> eta (dLAM i (dAPP t (dV i))) t) /\
  (!t t' u. eta t t'      ==> eta (dAPP t u) (dAPP t' u)) /\
  (!t u u'. eta u u'      ==> eta (dAPP t u) (dAPP t u')) /\
  (!i t t'. eta t t'      ==> eta (dLAM i t) (dLAM i t'))
`;

val nsub_lift = store_thm(
  "nsub_lift",
  ``!t u n. nsub u n (lift t n) = t``,
  Induct_on `t` THEN SRW_TAC [ARITH_ss][]);
val _ = export_rewrites ["nsub_lift"]

val IN_dFV_dpm = store_thm(
  "IN_dFV_dpm",
  ``!t p i. i IN dFV (dpm p t) = s2n (lswapstr (REVERSE p) (n2s i)) IN dFV t``,
  SRW_TAC [][IN_dFV] THEN REWRITE_TAC [SYM dpm_supp] THEN
  `supp d_pmact (dpm p t) = ssetpm p (supp d_pmact t)`
     by METIS_TAC [nomsetTheory.perm_supp] THEN
  SRW_TAC [][]);

val REVERSE_inc_pm = store_thm(
  "REVERSE_inc_pm",
  ``!p x. REVERSE (inc_pm x p) = inc_pm x (REVERSE p)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, inc_pm_APPEND]);

val nipkow_eta_lemma = store_thm(
  "nipkow_eta_lemma",
  ``!t i. ~(i IN dFV t) ==> !u v. nsub u i t = nsub v i t``,
  Induct THEN SRW_TAC [][]);

val neta_dpm = store_thm(
  "neta_dpm",
  ``!t u. neta t u ==> !p. neta (dpm p t) (dpm p u)``,
  HO_MATCH_MP_TAC neta_ind THEN SRW_TAC [][neta_rules] THEN
  SRW_TAC [][lswapstr_inc_pm] THEN
  Q.MATCH_ABBREV_TAC `neta (dABS (dAPP tm (dV 0))) tm'` THEN
  Q_TAC SUFF_TAC `~(0 IN dFV tm) /\ (tm' = nsub u 0 tm)`
        THEN1 SRW_TAC [][neta_rules] THEN
  UNABBREV_ALL_TAC THEN
  SRW_TAC [][dpm_nsub,nipkow_eta_lemma, IN_dFV_dpm, REVERSE_inc_pm,
             lswapstr_inc_pm]);

val alt_neta_redex = prove(
  ``~(i IN dFV t) ==> neta (dLAM i (dAPP t (dV i))) t``,
  SRW_TAC [][dLAM_def] THEN
  Q.MATCH_ABBREV_TAC `neta (dABS (dAPP tm (dV 0))) t` THEN
  Q_TAC SUFF_TAC `~(0 IN dFV tm) /\ (t = nsub (dV 0) 0 tm)`
        THEN1 SRW_TAC [][neta_rules] THEN
  `~((i + 1) IN dFV (lift t 0))` by SRW_TAC [][] THEN
  `tm = lift t 0` by METIS_TAC [sub_14b] THEN
  SRW_TAC [][]);

val eta_neta = store_thm(
  "eta_neta",
  ``!t u. eta t u ==> neta t u``,
  HO_MATCH_MP_TAC eta_ind THEN
  SRW_TAC [][neta_rules, alt_neta_redex] THEN
  METIS_TAC [neta_rules, dABS_rules_are_dLAM_compatible, neta_dpm,
             nomsetTheory.pmact_inverse]);

val nipkow_free_sub_lemmma = store_thm(
  "nipkow_free_sub_lemmma",
  ``!s t i k.
      i IN dFV (nsub t k s) = k IN dFV s /\ i IN dFV t \/
                              if i < k then i IN dFV s
                              else i + 1 IN dFV s``,
  Induct THEN SRW_TAC [ARITH_ss][] THEN METIS_TAC []);

val lift_nsub = store_thm(
  "lift_nsub",
  ``!t n u. ~(n IN dFV t) ==> (lift (nsub u n t) n = t)``,
  Induct THEN SRW_TAC [ARITH_ss][]);

val eta_dpm = store_thm(
  "eta_dpm",
  ``!t u. eta t u ==> !p. eta (dpm p t) (dpm p u)``,
  HO_MATCH_MP_TAC eta_ind THEN SRW_TAC [][eta_rules] THEN
  MATCH_MP_TAC (hd (CONJUNCTS eta_rules)) THEN
  SRW_TAC [][IN_dFV_dpm]);

val eta_dpm_eqn = store_thm(
  "eta_dpm_eqn",
  ``eta (dpm p t) (dpm p u) = eta t u``,
  METIS_TAC [nomsetTheory.pmact_inverse, eta_dpm]);

val alt_eta_redex = prove(
  ``~(0 IN dFV t) ==> eta (dABS (dAPP t (dV 0))) (nsub u 0 t)``,
  STRIP_TAC THEN
  `?z. ~(z IN dFV (dABS (dAPP t (dV 0))))`
     by METIS_TAC [dfresh_exists] THEN
  `~(z + 1 IN dFV t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
  `~(z IN dFV (nsub u 0 t))` by SRW_TAC [][nipkow_free_sub_lemmma] THEN
  Q_TAC SUFF_TAC `dABS (dAPP t (dV 0)) = dLAM z (dAPP (nsub u 0 t) (dV z))`
        THEN1 SRW_TAC [][eta_rules] THEN
  SRW_TAC [][dLAM_def] THEN
  SRW_TAC [][sub_14b, nipkow_eta_lemma, lift_nsub]);

val neta_eta = store_thm(
  "neta_eta",
  ``!t u. neta t u ==> eta t u``,
  HO_MATCH_MP_TAC neta_ind THEN SRW_TAC [][eta_rules, alt_eta_redex] THEN
  METIS_TAC [eta_dpm_eqn, dABS_rules_are_dLAM_compatible, eta_rules]);

val neta_eq_eta = store_thm(
  "neta_eq_eta",
  ``neta = eta``,
  SRW_TAC [][FUN_EQ_THM] THEN METIS_TAC [neta_eta, eta_neta]);

val eta_lam_eta = store_thm(
  "eta_lam_eta",
  ``!t u. eta t u ==> !M N. (t = fromTerm M) /\ (u = fromTerm N) ==>
                            compat_closure eta M N``,
  HO_MATCH_MP_TAC eta_ind THEN SRW_TAC [][fromTerm_eqn] THEN
  FULL_SIMP_TAC (srw_ss()) [fromTerm_11, IN_dFV] THENL [
    `eta (LAM (n2s i) (t1 @@ VAR (n2s i))) t1`
       by (SRW_TAC [][eta_def] THEN METIS_TAC []) THEN
    METIS_TAC [compat_closure_rules],
    METIS_TAC [compat_closure_rules],
    METIS_TAC [compat_closure_rules],
    METIS_TAC [compat_closure_rules]
  ]);

val lam_eta_eta = store_thm(
  "lam_eta_eta",
  ``!M N. compat_closure eta M N ==> eta (fromTerm M) (fromTerm N)``,
  HO_MATCH_MP_TAC compat_closure_ind THEN
  SRW_TAC [][eta_rules, eta_def] THEN
  SRW_TAC [][] THEN MATCH_MP_TAC (hd (CONJUNCTS eta_rules)) THEN
  SRW_TAC [][IN_dFV]);

val eta_eq_lam_eta = store_thm(
  "eta_eq_lam_eta",
  ``eta (fromTerm M) (fromTerm N) = compat_closure eta M N``,
  METIS_TAC [eta_lam_eta, lam_eta_eta]);

val _ = export_theory();
