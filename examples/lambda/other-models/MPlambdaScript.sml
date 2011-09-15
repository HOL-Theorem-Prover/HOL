open HolKernel Parse boolLib bossLib binderLib
open nomsetTheory

local open stringTheory in end

fun Store_thm (n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

val _ = new_theory "MPlambda"

val _ = Hol_datatype `MPterm = Var of string
                             | Parameter of string
                             | App of MPterm => MPterm
                             | Abs of string => MPterm`;

val psub_def = Define`
  (psub a p (Var s) = Var s) /\
  (psub a p (Parameter q) = if p = q then a else Parameter q) /\
  (psub a p (App t1 t2) = App (psub a p t1) (psub a p t2)) /\
  (psub a p (Abs v t) = Abs v (psub a p t))
`;
val _ = export_rewrites ["psub_def"]

val params_def = Define`
  (params (Var s) = {}) /\
  (params (Parameter p) = {p}) /\
  (params (App t1 t2) = params t1 UNION params t2) /\
  (params (Abs v t) = params t)
`;
val _ = export_rewrites ["params_def"]

val vsub_def = Define`
  (vsub a v (Var u) = if u = v then a else Var u) /\
  (vsub a v (Parameter p) = Parameter p) /\
  (vsub a v (App t1 t2) = App (vsub a v t1) (vsub a v t2)) /\
  (vsub a v (Abs u t) = if u = v then Abs u t
                        else Abs u (vsub a v t))
`;
val _ = export_rewrites ["vsub_def"]

val allvars_def = Define`
  (allvars (Parameter p) = {}) /\
  (allvars (Var v) = {v}) /\
  (allvars (App t1 t2) = allvars t1 UNION allvars t2) /\
  (allvars (Abs v t) = v INSERT allvars t)
`;
val _= export_rewrites ["allvars_def"]

val FINITE_allvars = Store_thm(
  "FINITE_allvars",
  ``!t. FINITE (allvars t)``,
  Induct THEN SRW_TAC [][]);

val vsub_14a = Store_thm(
  "vsub_14a",
  ``~(v IN allvars t) ==> (vsub N v t = t)``,
  Induct_on `t` THEN SRW_TAC [][]);

val pvsub_vsub_collapse = store_thm(
  "pvsub_vsub_collapse",
  ``!M p v1 v2. ~(v2 IN allvars M) ==>
                (vsub (Parameter p) v2 (vsub (Var v2) v1 M) =
                 vsub (Parameter p) v1 M)``,
  Induct THEN SRW_TAC [][]);

val params_vvsub = Store_thm(
  "params_vvsub",
  ``params (vsub (Var v1) v2 M) = params M``,
  Induct_on `M` THEN SRW_TAC [][]);

val shape_lemma = store_thm(
  "shape_lemma",
  ``!M p. ?v M'. (M = vsub (Parameter p) v M') /\ ~(p IN params M')``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []THENL [
    Q.X_GEN_TAC `s` THEN SRW_TAC [][] THEN
    Q_TAC (NEW_TAC "z") `{s}` THEN
    MAP_EVERY Q.EXISTS_TAC [`z`, `Var s`] THEN SRW_TAC [][],

    Q.X_GEN_TAC `s` THEN SRW_TAC [][] THEN
    Cases_on `s = p` THENL [
      MAP_EVERY Q.EXISTS_TAC [`x`, `Var x`] THEN SRW_TAC [][],
      MAP_EVERY Q.EXISTS_TAC [`x`, `Parameter s`] THEN SRW_TAC [][]
    ],

    GEN_TAC THEN
    `?v1 M1. (M = vsub (Parameter p) v1 M1) /\ ~(p IN params M1)`
       by METIS_TAC [] THEN
    `?v2 M2. (M' = vsub (Parameter p) v2 M2) /\ ~(p IN params M2)`
       by METIS_TAC [] THEN
    Q_TAC (NEW_TAC "z") `allvars M1 UNION allvars M2 UNION {v1;v2}` THEN
    `(M = vsub (Parameter p) z (vsub (Var z) v1 M1)) /\
     (M' = vsub (Parameter p) z (vsub (Var z) v2 M2))`
       by METIS_TAC [pvsub_vsub_collapse] THEN
    MAP_EVERY Q.EXISTS_TAC
              [`z`, `App (vsub (Var z) v1 M1) (vsub (Var z) v2 M2)`] THEN
    SRW_TAC [][pvsub_vsub_collapse],

    Q.X_GEN_TAC `s` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `p` STRIP_ASSUME_TAC) THEN
    REVERSE (Cases_on `s = v`) THEN1
      (MAP_EVERY Q.EXISTS_TAC [`v`, `Abs s M'`] THEN SRW_TAC [][]) THEN
    SRW_TAC [][] THEN
    Q_TAC (NEW_TAC "z") `s INSERT allvars M'` THEN
    MAP_EVERY Q.EXISTS_TAC [`z`, `Abs s (vsub (Var z) s M')`] THEN
    SRW_TAC [][pvsub_vsub_collapse]
  ]);

val (vclosed_rules, vclosed_ind, vclosed_cases) = Hol_reln`
  (!p. vclosed (Parameter p)) /\
  (!p v t. vclosed (vsub (Parameter p) v t) ==>
           vclosed (Abs v t)) /\
  (!t1 t2. vclosed t1 /\ vclosed t2 ==> vclosed (App t1 t2))
`;

val FINITE_params = Store_thm(
  "FINITE_params",
  ``!t. FINITE (params t)``,
  Induct THEN SRW_TAC [][]);

val psub_14a = Store_thm(
  "psub_14a",
  ``!M p N. ~(p IN params M) ==> (psub N p M = M)``,
  Induct THEN SRW_TAC [][]);


val vsub_is_psub_alpha = store_thm(
  "vsub_is_psub_alpha",
  ``!M p N v. ~(p IN params M) ==>
              (psub N p (vsub (Parameter p) v M) = vsub N v M)``,
  Induct THEN SRW_TAC [][]);

val vars_def = Define`
  (vars (Var u) = {u}) /\
  (vars (Parameter p) = {}) /\
  (vars (App t1 t2) = vars t1 UNION vars t2) /\
  (vars (Abs v t) = vars t DIFF {v})
`;
val _ = export_rewrites ["vars_def"]

val vsub_14a = Store_thm(
  "vsub_14a",
  ``!M v N. ~(v IN vars M) ==> (vsub N v M = M)``,
  Induct THEN SRW_TAC [][]);


val raw_MPpm_def = Define`
  (raw_MPpm pi (Parameter s) = Parameter (lswapstr pi s)) /\
  (raw_MPpm pi (Var v) = Var v) /\
  (raw_MPpm pi (App t1 t2) = App (raw_MPpm pi t1) (raw_MPpm pi t2)) /\
  (raw_MPpm pi (Abs v t) = Abs v (raw_MPpm pi t))
`;
val _ = export_rewrites ["raw_MPpm_def"]

val _ = overload_on("MP_pmact",``mk_pmact raw_MPpm``);
val _ = overload_on("MPpm", ``pmact MP_pmact``);

val MPpm_raw = store_thm(
  "MPpm_raw",
  ``MPpm = raw_MPpm``,
  SRW_TAC [][GSYM pmact_bijections] THEN
  SRW_TAC [][is_pmact_def] THENL [
    Induct_on `x` THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][pmact_decompose],
    FULL_SIMP_TAC (srw_ss()) [permeq_thm, FUN_EQ_THM] THEN
    Induct THEN SRW_TAC [][]
  ]);

val MPpm_thm = save_thm(
"MPpm_thm",
raw_MPpm_def |> SUBS [GSYM MPpm_raw]);
val _ = export_rewrites["MPpm_thm"];

val MPpm_fresh = Store_thm(
  "MPpm_fresh",
  ``!M x y. ~(x IN params M) /\ ~(y IN params M) ==>
            (MPpm [(x,y)] M = M)``,
  Induct THEN SRW_TAC [][]);

val MPpm_NIL = Store_thm(
  "MPpm_NIL",
  ``MPpm [] t = t``,
  Induct_on `t` THEN SRW_TAC [][]);

val supp_MPpm = Store_thm(
  "supp_MPpm",
  ``supp MP_pmact = params``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def] THEN
  Induct_on `x` THEN SRW_TAC [][] THEN METIS_TAC []);

val MPpm_vsub = store_thm(
  "MPpm_vsub",
  ``!M v pi N. MPpm pi (vsub M v N) = vsub (MPpm pi M) v (MPpm pi N)``,
  Induct_on `N` THEN SRW_TAC [][]);

val vclosed_MPpm = store_thm(
  "vclosed_MPpm",
  ``!M. vclosed M ==> !pi. vclosed (MPpm pi M)``,
  HO_MATCH_MP_TAC vclosed_ind THEN SRW_TAC [][vclosed_rules, MPpm_vsub] THEN
  METIS_TAC [vclosed_rules]);

val vars_pvsub = store_thm(
  "vars_pvsub",
  ``!p v M. vars (vsub (Parameter p) v M) = vars M DELETE v``,
  Induct_on `M` THEN SRW_TAC [][] THEN
  SRW_TAC [][pred_setTheory.EXTENSION] THEN METIS_TAC []);


val vclosed_empty_vars = store_thm(
  "vclosed_empty_vars",
  ``!t. vclosed t ==> (vars t = {})``,
  HO_MATCH_MP_TAC vclosed_ind THEN SRW_TAC [][vars_pvsub] THEN
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION]);


val vclosed_var = Store_thm(
  "vclosed_var",
  ``!v. ~(vclosed (Var v))``,
  ONCE_REWRITE_TAC [vclosed_cases] THEN SRW_TAC [][]);

val vclosed_parameter = Store_thm(
  "vclosed_parameter",
  ``vclosed (Parameter p)``,
  ONCE_REWRITE_TAC [vclosed_cases] THEN SRW_TAC [][]);

val _ = set_fixity "=" (Infix(NONASSOC, 100))

val vclosed_app = Store_thm(
  "vclosed_app",
  ``vclosed (App t1 t2) = vclosed t1 /\ vclosed t2``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [vclosed_cases])) THEN
  SRW_TAC [][]);

val vclosed_abs = store_thm(
  "vclosed_abs",
  ``vclosed (Abs v t) = ?p. vclosed (vsub (Parameter p) v t)``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [vclosed_cases])) THEN
  SRW_TAC [][]);

val pvsub_eq_app = prove(
  ``(vsub (Parameter p) v M = App t1 t2) =
      ?M1 M2. (M = App M1 M2) /\ (vsub (Parameter p) v M1 = t1) /\
              (vsub (Parameter p) v M2 = t2)``,
  Cases_on `M` THEN SRW_TAC [][]);

val pvsub_eq_param = prove(
  ``(vsub (Parameter p1) v M = Parameter p2) =
       (M = Var v) /\ (p1 = p2) \/
       (M = Parameter p2)``,
  Cases_on `M` THEN SRW_TAC [][]);

val pvsub_eq_abs = prove(
  ``(vsub (Parameter p) v M = Abs s t) =
       (?M0. ~(s = v) /\ (M = Abs s M0) /\ (vsub (Parameter p) v M0 = t)) \/
       (v = s) /\ (M = Abs s t)``,
  Cases_on `M` THEN SRW_TAC [][] THEN METIS_TAC []);

val independent_pvsub = prove(
  ``!p1 p2 v1 v2 M.
      ~(v1 = v2) ==> (vsub (Parameter p1) v1 (vsub (Parameter p2) v2 M) =
                      vsub (Parameter p2) v2 (vsub (Parameter p1) v1 M))``,
  Induct_on `M` THEN SRW_TAC [][])

val IN_params_MPpm = store_thm(
  "IN_params_MPpm",
  ``x IN params (MPpm pi M) = lswapstr (REVERSE pi) x IN params M``,
  Induct_on `M` THEN SRW_TAC [][pmact_eql]);

val independent_psub_vsub = prove(
  ``!M v p1 p2 p3.
      ~(p2 = p3) ==>
      (psub (Parameter p1) p2 (vsub (Parameter p3) v M) =
       vsub (Parameter p3) v (psub (Parameter p1) p2 M))``,
  Induct THEN SRW_TAC [][]);

val (cvclosed_rules, cvclosed_ind, cvclosed_cases) = Hol_reln`
  (!p. cvclosed (Parameter p)) /\
  (!M N. cvclosed M /\ cvclosed N ==> cvclosed (App M N)) /\
  (!v p M. ~(p IN params M) /\ cvclosed (vsub (Parameter p) v M) ==>
           cvclosed (Abs v M))
`;

val cvclosed_eqns = prove(
  ``cvclosed (Parameter p) /\
    (cvclosed (App M N) = cvclosed M /\ cvclosed N) /\
    (cvclosed (Abs v M) = ?p. ~(p IN params M) /\
                              cvclosed (vsub (Parameter p) v M))``,
  REPEAT CONJ_TAC THEN1
    (ONCE_REWRITE_TAC [cvclosed_cases] THEN SRW_TAC [][]) THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [cvclosed_cases])) THEN
  SRW_TAC [][]);

val cvclosed_strongctxt_ind = prove(
  ``!P f. (!x. FINITE (f x)) /\
          (!p x. P (Parameter p) x) /\
          (!M N y. (!x. P M x)  /\ (!x. P N x) ==> P (App M N) y) /\
          (!v p M y. ~(p IN f y) /\ ~(p IN params M) /\
                     (!x. P (vsub (Parameter p) v M) x) ==>
                     P (Abs v M) y)
        ==>
          !M. cvclosed M ==> !x. P M x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M. cvclosed M ==> !pi x. P (MPpm pi M) x`
        THEN1 METIS_TAC [MPpm_NIL] THEN
  HO_MATCH_MP_TAC cvclosed_ind THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [MPpm_vsub] THEN
  Q_TAC (NEW_TAC "z") `f x UNION params (MPpm pi M)` THEN
  Q.EXISTS_TAC `z` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`(stringpm pi p, z) :: pi`, `x'`] MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `MPpm [(stringpm pi p, z)] (MPpm pi M) = MPpm pi M`
    by SRW_TAC [][MPpm_fresh, IN_params_MPpm, stringpm_raw] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM pmact_decompose]);

val cvclosed_strong_ind =
(Q.GEN `P` o Q.GEN `X` o
 SIMP_RULE (srw_ss()) [] o
 Q.SPECL [`\t u. P t`, `\u. X`] o
 INST_TYPE [alpha |-> ``:one``]) cvclosed_strongctxt_ind

val notin_pvsub_I = prove(
  ``~(p1 = p2) /\ ~(p1 IN params M) ==>
    ~(p1 IN params (vsub (Parameter p2) v M))``,
  Induct_on `M` THEN SRW_TAC [][]);

val cvclosed_p_indep = prove(
  ``!t. cvclosed t ==>
        !pp't0 v p p' t0.
            ((p, p', t0) = pp't0) /\ (t = vsub (Parameter p) v t0) ==>
            cvclosed (vsub (Parameter p') v t0)``,
  HO_MATCH_MP_TAC cvclosed_strongctxt_ind THEN
  Q.EXISTS_TAC `\(p,p',t0). {p;p'} UNION params t0` THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][cvclosed_eqns, pvsub_eq_abs, pvsub_eq_param, pvsub_eq_app] THEN
  SRW_TAC [][cvclosed_eqns] THENL [
    METIS_TAC [],
    METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.EXISTS_TAC `p` THEN CONJ_TAC THENL [
      MATCH_MP_TAC notin_pvsub_I THEN SRW_TAC [][],
      METIS_TAC [independent_pvsub]
    ],
    METIS_TAC []
  ]);

val cvclosed_pickany = save_thm(
  "cvclosed_pickany",
  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] cvclosed_p_indep);

val cvclosed_vclosed = prove(
  ``!t. cvclosed t ==> vclosed t``,
  HO_MATCH_MP_TAC cvclosed_ind THEN SRW_TAC [][vclosed_rules] THEN
  METIS_TAC [vclosed_rules]);

val vclosed_cvclosed = prove(
  ``!t. vclosed t ==> cvclosed t``,
  HO_MATCH_MP_TAC vclosed_ind THEN SRW_TAC [][cvclosed_rules] THEN
  MATCH_MP_TAC (last (CONJUNCTS cvclosed_rules)) THEN
  Q_TAC (NEW_TAC "z") `params t` THEN
  METIS_TAC [cvclosed_pickany]);

val cv_eq_vclosed = store_thm(
  "cv_eq_vclosed",
  ``cvclosed = vclosed``,
  SRW_TAC [] [FUN_EQ_THM, vclosed_cvclosed, cvclosed_vclosed, EQ_IMP_THM]);

val vclosed_strong_ind = save_thm(
  "vclosed_strong_ind",
  REWRITE_RULE [cv_eq_vclosed] cvclosed_strong_ind)

val double_pvsub = Store_thm(
  "double_pvsub",
  ``vsub (Parameter p1) v (vsub (Parameter p2) v t) =
    vsub (Parameter p2) v t``,
  Induct_on `t` THEN SRW_TAC [][]);

val vclosed_pvsub = store_thm(
  "vclosed_pvsub",
  ``!t. vclosed t ==> !p v. vclosed (vsub (Parameter p) v t)``,
  HO_MATCH_MP_TAC vclosed_ind THEN SRW_TAC [][vclosed_rules] THEN
  METIS_TAC [vclosed_rules, double_pvsub, independent_pvsub]);

val cofin_vclosed_ind = store_thm(
  "cofin_vclosed_ind",
  ``!P. (!p. P (Parameter p)) /\
        (!v t X. FINITE X /\
                 (!p. ~(p IN X) ==> P (vsub (Parameter p) v t)) ==>
                 P (Abs v t)) /\
        (!t1 t2. P t1 /\ P t2 ==> P (App t1 t2)) ==>
        !t. vclosed t ==> P t``,
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t. vclosed t ==> !pi. P (MPpm pi t)`
        THEN1 METIS_TAC [MPpm_NIL] THEN
  HO_MATCH_MP_TAC vclosed_strong_ind THEN
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  Q.EXISTS_TAC `params (MPpm pi t)` THEN
  FULL_SIMP_TAC (srw_ss()) [MPpm_vsub] THEN
  Q.X_GEN_TAC `p1` THEN STRIP_TAC THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `[(p1,stringpm pi p)] ++ pi` MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q_TAC SUFF_TAC `MPpm ((p1,stringpm pi p)::pi) t = MPpm pi t`
        THEN1 SRW_TAC [][] THEN
  `MPpm [(p1,stringpm pi p)] (MPpm pi t) = MPpm pi t`
     by SRW_TAC [][MPpm_fresh, IN_params_MPpm, stringpm_raw] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM pmact_decompose]);

val (avclosed_rules, avclosed_ind, avclosed_cases) = Hol_reln`
  (!p. avclosed (Parameter p)) /\
  (!t1 t2. avclosed t1 /\ avclosed t2 ==> avclosed (App t1 t2)) /\
  (!v t. (!p. avclosed (vsub (Parameter p) v t)) ==>
         avclosed (Abs v t))
`;

val avclosed_pickany = prove(
  ``!t. avclosed t ==>
        !v p p' t0. (t = vsub (Parameter p) v t0) ==>
                    avclosed (vsub (Parameter p') v t0)``,
  HO_MATCH_MP_TAC avclosed_ind THEN
  SRW_TAC [][pvsub_eq_app, pvsub_eq_param, pvsub_eq_abs] THEN
  SRW_TAC [][avclosed_rules] THENL [
    METIS_TAC [avclosed_rules],
    MATCH_MP_TAC (last (CONJUNCTS avclosed_rules)) THEN
    METIS_TAC [independent_pvsub],
    MATCH_MP_TAC (last (CONJUNCTS avclosed_rules)) THEN
    METIS_TAC []
  ]);

(* page 12 *)
val avclosed_alpha = store_thm(
  "avclosed_alpha",
  ``avclosed (vsub (Parameter p) v t) ==>
    !q. avclosed (vsub (Parameter q) v t)``,
  METIS_TAC [avclosed_pickany]);

val vclosed_avclosed = store_thm(
  "vclosed_avclosed",
  ``!t. vclosed t ==> avclosed t``,
  HO_MATCH_MP_TAC vclosed_strong_ind THEN
  SRW_TAC [][avclosed_rules] THEN
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THEN
  MATCH_MP_TAC (last (CONJUNCTS avclosed_rules)) THEN SRW_TAC [][] THEN
  METIS_TAC [avclosed_pickany]);

val avclosed_vclosed = prove(
  ``!t. avclosed t ==> vclosed t``,
  HO_MATCH_MP_TAC avclosed_ind THEN SRW_TAC [][vclosed_abs]);

val avclosed_eq_vclosed = prove(
  ``avclosed = vclosed``,
  SRW_TAC [][FUN_EQ_THM, EQ_IMP_THM, vclosed_avclosed, avclosed_vclosed]);

val vclosed_avclosed_ind = save_thm(
  "vclosed_avclosed_ind",
  REWRITE_RULE [avclosed_eq_vclosed] avclosed_ind);

val sub = ``\t (p,v). vsub (Parameter p) v t``
val FOLDL_Parameter = prove(
  ``!l. FOLDL ^sub (Parameter p) l = Parameter p``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val FOLDL_Var = prove(
  ``!l. (?p. FOLDL ^sub (Var s) l = Parameter p) \/
        (FOLDL ^sub (Var s) l = Var s)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][FOLDL_Parameter]);

val FOLDL_App = prove(
  ``!l t1 t2. FOLDL ^sub (App t1 t2) l =
              App (FOLDL ^sub t1 l) (FOLDL ^sub t2 l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

val FOLDL_Abs = prove(
  ``!l v t. FOLDL ^sub (Abs v t) l =
            Abs v (FOLDL ^sub t (FILTER (\ (p,u). ~(u = v)) l))``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][]);

val vsub_FOLDL = prove(
  ``!l t p s. vsub (Parameter p) s (FOLDL ^sub t l) =
              FOLDL ^sub t (l ++ [(p,s)])``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

val vars_pvsub = prove(
  ``vars (vsub (Parameter p) v t) = vars t DELETE v``,
  SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
  Induct_on `t` THEN SRW_TAC [][] THEN
  METIS_TAC []);


val vars_FOLDL = prove(
  ``!l t. vars (FOLDL ^sub t l) = vars t DIFF set (MAP SND l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, vars_pvsub] THEN
  SRW_TAC [][pred_setTheory.EXTENSION] THEN METIS_TAC []);

val empty_vars_vclosed = store_thm(
  "empty_vars_vclosed",
  ``!t. (vars t = {}) ==> vclosed t``,
  Q_TAC SUFF_TAC
    `!t l. (vars (FOLDL (\t (p,v). vsub (Parameter p) v t) t l) = {}) ==>
           vclosed (FOLDL (\t (p,v). vsub (Parameter p) v t) t l)`
    THEN1 METIS_TAC [listTheory.FOLDL] THEN
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [FOLDL_App, FOLDL_Parameter, FOLDL_Abs] THENL [
    MAP_EVERY Q.X_GEN_TAC [`s`,`l`] THEN
    Q.SPEC_THEN `l` STRIP_ASSUME_TAC FOLDL_Var THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][] THEN
    MATCH_MP_TAC (List.nth(CONJUNCTS vclosed_rules, 1)) THEN
    SRW_TAC [][vsub_FOLDL] THEN Q.EXISTS_TAC `p` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [vars_FOLDL, pred_setTheory.EXTENSION] THEN
    METIS_TAC []
  ]);

val (mpbeta_rules, mpbeta_ind, mpbeta_cases) = Hol_reln`
  (!M N M'. mpbeta M M' ==> mpbeta (App M N) (App M' N)) /\
  (!M N N'. mpbeta N N' ==> mpbeta (App M N) (App M N')) /\
  (!u v M N p. ~(p IN params M) /\ ~(p IN params N) /\
               mpbeta (vsub (Parameter p) u M) (vsub (Parameter p) v N) ==>
               mpbeta (Abs u M) (Abs v N)) /\
  (!x M N. vclosed (Abs x M) /\ vclosed N ==>
           mpbeta (App (Abs x M) N) (vsub N x M))
`;

open chap3Theory
val (convert_rules, convert_ind, convert_cases) = Hol_reln`
  (!p. convert (Parameter p) (VAR p)) /\
  (!t1 t2 M N. convert t1 M /\ convert t2 N ==>
               convert (App t1 t2) (M @@ N)) /\
  (!u v t M. ~(u IN params t) /\ convert (vsub (Parameter u) v t) M ==>
             convert (Abs v t) (LAM u M))
`;

val convert_param = Store_thm(
  "convert_param",
  ``convert (Parameter p) t = (t = VAR p)``,
  ONCE_REWRITE_TAC [convert_cases] THEN SRW_TAC [][]);

val convert_app = store_thm(
  "convert_app",
  ``convert (App M N) t = ?t0 t1. convert M t0 /\ convert N t1 /\
                                  (t = t0 @@ t1)``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [convert_cases])) THEN
  SRW_TAC [][] THEN METIS_TAC []);

val convert_abs = save_thm(
  "convert_abs",
  (SIMP_RULE (srw_ss()) [] o Q.SPEC `Abs v M`) convert_cases)

val UNION_DELETE = prove(
  ``(s UNION t) DELETE e = (s DELETE e) UNION (t DELETE e)``,
  SRW_TAC [][pred_setTheory.EXTENSION] THEN METIS_TAC []);

val params_vsub = store_thm(
  "params_vsub",
  ``!t p v. ~(p IN params t) ==>
            (params (vsub (Parameter p) v t) DELETE p = params t)``,
  Induct THEN SRW_TAC [][UNION_DELETE] THEN
  SRW_TAC [][pred_setTheory.EXTENSION] THEN METIS_TAC []);

val convert_MPpm = prove(
  ``!t M. convert t M ==> !pi. convert (MPpm pi t) (tpm pi M)``,
  HO_MATCH_MP_TAC convert_ind THEN
  SRW_TAC [][convert_rules, MPpm_vsub] THEN
  MATCH_MP_TAC (last (CONJUNCTS convert_rules)) THEN
  SRW_TAC [][IN_params_MPpm]);

val convert_MPpm_E = Store_thm(
  "convert_MPpm_E",
  ``convert (MPpm pi t) (tpm pi M) = convert t M``,
  METIS_TAC [convert_MPpm, pmact_inverse]);

val convert_strong_ind = store_thm(
  "convert_strong_ind",
  ``!P f. (!x. FINITE (f x)) /\
          (!p c. P (Parameter p) (VAR p) c) /\
          (!t1 t2 M N c.
               (!d1. P t1 M d1) /\ convert t1 M /\
               (!d2. P t2 N d2) /\ convert t2 N ==>
               P (App t1 t2) (M @@ N) c) /\
          (!u v t M c. ~(u IN params t) /\ ~(u IN f c) /\
                       convert (vsub (Parameter u) v t) M /\
                       (!d. P (vsub (Parameter u) v t) M d) ==>
                       P (Abs v t) (LAM u M) c)
        ==>
          !t M. convert t M ==> !c. P t M c``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t M. convert t M ==>
                        convert t M /\
                        !c pi. P (MPpm pi t) (tpm pi M) c`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC convert_ind THEN
  SRW_TAC [][convert_rules, MPpm_vsub] THEN
  Q_TAC (NEW_TAC "z") `FV (tpm pi M) UNION f c UNION params (MPpm pi t)` THEN
  `LAM (lswapstr pi u) (tpm pi M) = LAM z (tpm [(z, lswapstr pi u)] (tpm pi M))`
     by SRW_TAC [][termTheory.tpm_ALPHA] THEN
  SRW_TAC [][] THEN
  `MPpm ((z,lswapstr pi u)::pi) t = MPpm [(z,lswapstr pi u)] (MPpm pi t)`
     by SRW_TAC [][GSYM pmact_decompose] THEN
  ` _ = MPpm pi t`
     by SRW_TAC [][MPpm_fresh, IN_params_MPpm] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][]
    THEN1 (`convert (MPpm ((z,lswapstr pi u)::pi) (vsub (Parameter u) v t))
                    (tpm ((z,lswapstr pi u)::pi) M)`
              by METIS_TAC [convert_MPpm_E] THEN
           POP_ASSUM MP_TAC THEN
           ASM_SIMP_TAC bool_ss [MPpm_vsub] THEN
           SRW_TAC [][GSYM pmact_decompose]) THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`d`, `((z,lswapstr pi u)::pi)`] MP_TAC) THEN
  SRW_TAC [][GSYM pmact_decompose]);

val convert_params = store_thm(
  "convert_params",
  ``!t M. convert t M ==> (params t = FV M)``,
  HO_MATCH_MP_TAC convert_ind THEN
  SRW_TAC [][] THEN METIS_TAC [params_vsub]);

val vclosed_convert = store_thm(
  "vclosed_convert",
  ``!t. vclosed t ==> ?M. convert t M``,
  HO_MATCH_MP_TAC vclosed_strong_ind THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][] THEN METIS_TAC [convert_rules]);

val convert_vclosed = store_thm(
  "convert_vclosed",
  ``!t M. convert t M ==> vclosed t``,
  HO_MATCH_MP_TAC convert_ind THEN SRW_TAC [][vclosed_abs] THEN
  METIS_TAC []);

val convert_vsub = prove(
  ``!t M. convert t M ==>
          !t0p1p2 v p1 p2 t0.
              (t0p1p2 = (t0,p1,p2)) /\
              (vsub (Parameter p1) v t0 = t) /\
              ~(p1 IN params t0) /\ ~(p2 IN params t0) ==>
              convert (vsub (Parameter p2) v t0) (tpm [(p1,p2)] M)``,
  HO_MATCH_MP_TAC convert_strong_ind THEN
  Q.EXISTS_TAC `\ (t0,p1,p2). {p1;p2} UNION params t0` THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  REPEAT CONJ_TAC THENL [
    (* parameter case *)
    SRW_TAC [][pvsub_eq_param] THEN
    FULL_SIMP_TAC (srw_ss()) [convert_rules],

    (* App case *)
    SRW_TAC [][pvsub_eq_app] THEN
    FULL_SIMP_TAC (srw_ss()) [convert_rules],

    (* Abs case *)
    MAP_EVERY Q.X_GEN_TAC [`u`, `v`, `t`, `M`, `t0`, `p1`, `p2`] THEN
    STRIP_TAC THEN Q.X_GEN_TAC `v'` THEN STRIP_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [pvsub_eq_abs] THENL [
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      MATCH_MP_TAC (last (CONJUNCTS convert_rules)) THEN
      SRW_TAC [][notin_pvsub_I] THEN
      METIS_TAC [independent_pvsub, notin_pvsub_I],

      MATCH_MP_TAC (last (CONJUNCTS convert_rules)) THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `convert (MPpm [(p1,p2)] (vsub (Parameter u) v t))
               (tpm [(p1,p2)] M)`
         by SRW_TAC [][] THEN
      Q_TAC SUFF_TAC `MPpm [(p1,p2)] (vsub (Parameter u) v t) =
                      vsub (Parameter u) v t`
            THEN1 METIS_TAC [] THEN
      SRW_TAC [][MPpm_vsub]
    ]
  ]);

val convert_vsub_thm = save_thm(
  "convert_vsub_thm",
  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] convert_vsub)

val convert_unique = store_thm(
  "convert_unique",
  ``!t M. convert t M ==> !N. convert t N ==> (M = N)``,
  HO_MATCH_MP_TAC convert_ind THEN REPEAT CONJ_TAC THENL [
    ONCE_REWRITE_TAC [convert_cases] THEN SRW_TAC [][],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [convert_cases] THEN SRW_TAC [][] THEN
    SRW_TAC [][],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [convert_cases] THEN SRW_TAC [][] THEN
    SRW_TAC [][termTheory.LAM_eq_thm] THEN
    Cases_on `u = u'` THEN1 METIS_TAC [] THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    `FV M' = params (vsub (Parameter u') v t)`
      by METIS_TAC [convert_params] THEN
    SRW_TAC [][notin_pvsub_I] THEN
    METIS_TAC [convert_vsub_thm, pmact_flip_args]
  ]);

val convert_onto = store_thm(
  "convert_onto",
  ``!M. ?t. convert t M``,
  HO_MATCH_MP_TAC termTheory.simple_induction THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `Parameter s` THEN SRW_TAC [][convert_rules],
    Q.EXISTS_TAC `App t t'` THEN SRW_TAC [][convert_rules],
    Q.SPECL_THEN [`t`, `v`]
                 (Q.X_CHOOSE_THEN `u` (Q.X_CHOOSE_THEN `t0` STRIP_ASSUME_TAC))
                 shape_lemma THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `Abs u t0` THEN METIS_TAC [convert_rules]
  ])

val params_vsub_upperbound = prove(
  ``p IN params (vsub N v M) ==> p IN params N \/ p IN params M``,
  Induct_on `M` THEN SRW_TAC [][] THEN METIS_TAC []);

val params_vsub_lowerbound = prove(
  ``p IN params M ==> p IN params (vsub N v M)``,
  Induct_on `M` THEN SRW_TAC [][] THEN METIS_TAC []);

val mpbeta_params = store_thm(
  "mpbeta_params",
  ``!t u. mpbeta t u ==> !p. p IN params u ==> p IN params t``,
  HO_MATCH_MP_TAC mpbeta_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    METIS_TAC [],
    METIS_TAC [],
    `p' IN params (Parameter p) \/ p' IN params M`
       by METIS_TAC [params_vsub_lowerbound, params_vsub_upperbound] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [params_vsub_upperbound]
  ]);

val vsub_vclosed = store_thm(
  "vsub_vclosed",
  ``!t. vclosed t ==> (vsub t' v t = t)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC vclosed_empty_vars THEN
  SRW_TAC [][vsub_14a]);

val general_vsub_commute = store_thm(
  "general_vsub_commute",
  ``vclosed t1 /\ vclosed t2 /\ ~(v1 = v2) ==>
    (vsub t1 v1 (vsub t2 v2 t) = vsub t2 v2 (vsub t1 v1 t))``,
  Induct_on `t` THEN SRW_TAC [][vsub_vclosed] THEN METIS_TAC []);

val convert_sub = store_thm(
  "convert_sub",
  ``~(p IN params t1) /\
    convert (vsub (Parameter p) v t1) M /\
    convert t2 N ==>
    convert (vsub t2 v t1) ([N/p] M)``,
  Q_TAC SUFF_TAC
        `!t M. convert t M ==>
               !t1pt2 t1 t2 p v N.
                  (t1pt2 = (t1,p,t2)) /\
                  ~(p IN params t1) /\
                  (vsub (Parameter p) v t1 = t) /\
                  convert t2 N ==>
                  convert (vsub t2 v t1) ([N/p] M)`
        THEN1 SRW_TAC [][] THEN
  HO_MATCH_MP_TAC convert_strong_ind THEN
  Q.EXISTS_TAC `\ (t1,p,t2). {p} UNION params t1 UNION params t2` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][pvsub_eq_param, pvsub_eq_app, pvsub_eq_abs] THEN
  FULL_SIMP_TAC (srw_ss()) [termTheory.SUB_THM, convert_rules] THENL [
    `FV N = params p_2` by SRW_TAC [][convert_params] THEN
    SRW_TAC [][termTheory.SUB_THM] THEN
    MATCH_MP_TAC (last (CONJUNCTS convert_rules)) THEN
    `~(u IN params (vsub p_2 v' M0))`
      by METIS_TAC [params_vsub_upperbound] THEN
    SRW_TAC [][] THEN
    `vclosed p_2` by METIS_TAC [convert_vclosed] THEN
    `vsub (Parameter u) v (vsub p_2 v' M0) =
     vsub p_2 v' (vsub (Parameter u) v M0)`
       by SRW_TAC [][general_vsub_commute] THEN
    SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SRW_TAC [][general_vsub_commute, notin_pvsub_I],

    `FV N = params p_2` by SRW_TAC [][convert_params] THEN
    SRW_TAC [][termTheory.SUB_THM] THEN
    MATCH_MP_TAC (last (CONJUNCTS convert_rules)) THEN
    Q_TAC SUFF_TAC `~(p_1' IN FV M)` THEN1 SRW_TAC [][termTheory.lemma14b] THEN
    `FV M = params (vsub (Parameter u) v t)`
       by SRW_TAC [][convert_params] THEN
    SRW_TAC [][notin_pvsub_I]
  ]);


val mpbeta_MPpm = prove(
  ``!t u. mpbeta t u ==> !pi. mpbeta (MPpm pi t) (MPpm pi u)``,
  HO_MATCH_MP_TAC mpbeta_ind THEN
  SRW_TAC [][mpbeta_rules, MPpm_vsub] THENL [
    MATCH_MP_TAC (List.nth(CONJUNCTS mpbeta_rules, 2)) THEN
    Q.EXISTS_TAC `stringpm pi p` THEN SRW_TAC [][IN_params_MPpm],
    MATCH_MP_TAC (last (CONJUNCTS mpbeta_rules)) THEN
    `MPpm pi (Abs x M) = Abs x (MPpm pi M)` by SRW_TAC [][] THEN
    METIS_TAC [vclosed_MPpm]
  ]);

val mpbeta_strong_ind =
    IndDefLib.derive_strong_induction(mpbeta_rules, mpbeta_ind)

val mpbeta_ccbeta = store_thm(
  "mpbeta_ccbeta",
  ``!t u. mpbeta t u ==>
          !M N. convert t M /\ convert u N ==> compat_closure beta M N``,
  HO_MATCH_MP_TAC mpbeta_strong_ind THEN
  SRW_TAC [][compat_closure_rules, convert_abs, convert_app] THENL [
    METIS_TAC [compat_closure_rules, convert_unique],
    METIS_TAC [compat_closure_rules, convert_unique],
    SRW_TAC [boolSimps.DNF_ss][cc_beta_thm, termTheory.LAM_eq_thm,
                               termTheory.tpm_eqr] THEN
    Cases_on `u' = u''` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      SRW_TAC [][] THEN
      `convert (vsub (Parameter p) u M) (tpm [(p,u')] M'') /\
       convert (vsub (Parameter p) v N) (tpm [(p,u')] M''')`
         by METIS_TAC [convert_vsub_thm, pmact_flip_args] THEN
      METIS_TAC [cc_beta_tpm_eqn, pmact_inverse],
      `~(u' IN FV M''')`
        by (`FV M''' = params (vsub (Parameter u'') v N)`
               by SRW_TAC [][convert_params] THEN
            SRW_TAC [][] THEN
            Cases_on `u' = p` THEN1 SRW_TAC [][notin_pvsub_I] THEN
            `mpbeta (MPpm [(u'',p)] (vsub (Parameter p) u M))
                    (MPpm [(u'',p)] (vsub (Parameter p) v N))`
               by SRW_TAC [][mpbeta_MPpm] THEN
            POP_ASSUM MP_TAC THEN
            SRW_TAC [][MPpm_vsub, MPpm_fresh] THEN
            Q_TAC SUFF_TAC
                  `~(u' IN params (vsub (Parameter u'') u (MPpm [(u'',p)] M)))`
                  THEN1 METIS_TAC [mpbeta_params] THEN
            SRW_TAC [][notin_pvsub_I, IN_params_MPpm]) THEN
      `convert (vsub (Parameter p) u M) (tpm [(u',p)] M'') /\
       convert (vsub (Parameter p) v N) (tpm [(u'',p)] M''')`
         by METIS_TAC [convert_vsub_thm] THEN
      `compat_closure beta (tpm [(u',p)] M'') (tpm [(u'',p)] M''')`
         by METIS_TAC [] THEN
      `compat_closure beta M'' (tpm [(u',p)] (tpm [(u'',p)] M'''))`
         by METIS_TAC [cc_beta_tpm, pmact_sing_inv] THEN
      Q_TAC SUFF_TAC `tpm [(u',p)] (tpm [(u'',p)] M''') = tpm [(u'',u')] M'''`
            THEN1 METIS_TAC [] THEN
      Cases_on `p = u'` THEN1 SRW_TAC [][] THEN
      Cases_on `p = u''` THEN1 SRW_TAC [][pmact_flip_args] THEN
      ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
      SRW_TAC [][] THEN
      `~(p IN FV M''') /\ ~(u' IN FV M''')`
        by METIS_TAC [convert_params, notin_pvsub_I] THEN
      SRW_TAC [][termTheory.tpm_fresh]
    ],

    `N' = [t1/u]M''` by METIS_TAC [convert_sub, convert_unique] THEN
    SRW_TAC [][cc_beta_thm] THEN METIS_TAC []
  ]);


val alpha_def = Define`alpha t1 t2 = ?M. convert t1 M /\ convert t2 M`

val alpha_trans = store_thm(
  "alpha_trans",
  ``alpha t1 t2 /\ alpha t2 t3 ==> alpha t1 t3``,
  SRW_TAC [][alpha_def] THEN METIS_TAC [convert_unique]);

val alpha_sym = store_thm(
  "alpha_sym",
  ``alpha t1 t2 ==> alpha t2 t1``,
  SRW_TAC [][alpha_def] THEN METIS_TAC []);

val alpha_prefl = store_thm(
  "alpha_prefl",
  ``alpha t t = vclosed t``,
  SRW_TAC [][alpha_def] THEN METIS_TAC [convert_vclosed, vclosed_convert]);

val convert_to_app = prove(
  ``convert t (M1 @@ M2) = ?t1 t2. (t = App t1 t2) /\ convert t1 M1 /\
                                   convert t2 M2``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [convert_cases])) THEN
  SRW_TAC [][]);

val convert_to_lam = prove(
  ``convert t (LAM v M) = ?u t0. (t = Abs u t0) /\ ~(v IN params t0) /\
                                 convert (vsub (Parameter v) u t0) M``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [convert_cases])) THEN
  SRW_TAC [boolSimps.DNF_ss][termTheory.LAM_eq_thm, termTheory.tpm_eqr] THEN
  SRW_TAC [][EQ_IMP_THM] THEN
  Q_TAC SUFF_TAC `~(v IN params t')`
        THEN1 METIS_TAC [convert_vsub_thm, pmact_flip_args,
                         pmact_sing_inv] THEN
  `~(v IN FV (tpm [(v,u)] M))` by SRW_TAC [][] THEN
  `~(v IN params (vsub (Parameter u) v' t'))`
    by METIS_TAC [convert_params] THEN
  METIS_TAC [params_vsub_lowerbound]);

val alpha_app = prove(
  ``alpha (App t1 t2) t = ?t1' t2'. (t = App t1' t2') /\
                                    alpha t1 t1' /\ alpha t2 t2'``,
  SRW_TAC [boolSimps.DNF_ss][alpha_def, convert_app, convert_to_app] THEN
  METIS_TAC []);

(* Curiously, only need to alpha-convert after a reduction, and not
   before. *)
val ccbeta_beta = store_thm(
  "ccbeta_beta",
  ``!M N. compat_closure beta M N ==>
          !t u. convert t M /\ convert u N ==>
                (alpha O mpbeta) t u``,
  HO_MATCH_MP_TAC ccbeta_ind THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][relationTheory.O_DEF, convert_to_app, convert_to_lam] THENL [
    IMP_RES_TAC convert_vclosed THEN
    Q.EXISTS_TAC `vsub t2 u' t0` THEN CONJ_TAC THENL [
      MATCH_MP_TAC (last (CONJUNCTS mpbeta_rules)) THEN
      SRW_TAC [][vclosed_abs] THEN METIS_TAC [],
      SRW_TAC [][alpha_def] THEN METIS_TAC [convert_sub]
    ],

    `?y. mpbeta t1 y /\ alpha y t1'` by METIS_TAC [] THEN
    Q.EXISTS_TAC `App y t2` THEN
    IMP_RES_TAC convert_vclosed THEN
    SRW_TAC [][alpha_app, alpha_prefl] THEN
    SRW_TAC [][mpbeta_rules, alpha_app, alpha_prefl] THEN
    SRW_TAC [][alpha_def] THEN METIS_TAC [],

    `?y. mpbeta t2 y /\ alpha y t2'` by METIS_TAC [] THEN
    Q.EXISTS_TAC `App t1 y` THEN
    IMP_RES_TAC convert_vclosed THEN
    SRW_TAC [][alpha_app, alpha_prefl] THEN
    SRW_TAC [][mpbeta_rules, alpha_app, alpha_prefl] THEN
    SRW_TAC [][alpha_def] THEN METIS_TAC [],

    `?y. mpbeta (vsub (Parameter v) u' t0) y /\
         alpha y (vsub (Parameter v) u'' t0')`
       by METIS_TAC [] THEN
    `?v1 t1. (y = vsub (Parameter v) v1 t1) /\ ~(v IN params t1)`
       by METIS_TAC [shape_lemma] THEN
    Q.EXISTS_TAC `Abs v1 t1` THEN CONJ_TAC THENL [
       MATCH_MP_TAC (List.nth(CONJUNCTS mpbeta_rules, 2)) THEN
       Q.EXISTS_TAC `v` THEN SRW_TAC [][],
       ALL_TAC
    ] THEN
    SRW_TAC [boolSimps.DNF_ss][alpha_def, convert_abs] THEN
    MAP_EVERY Q.EXISTS_TAC [`v`, `N`, `v`, `N`] THEN
    FULL_SIMP_TAC (srw_ss()) [alpha_def] THEN METIS_TAC [convert_unique]
  ]);


val _ = export_theory()
