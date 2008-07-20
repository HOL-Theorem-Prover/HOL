open HolKernel boolLib Parse bossLib BasicProvers metisLib

open basic_swapTheory pred_setTheory nomsetTheory binderLib

val export_rewrites = export_rewrites "preterm";

val _ = new_theory "preterm";

val _ = Hol_datatype `preterm = var of string
                              | app of preterm => preterm
                              | lam of string => preterm`;

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before export_rewrites [s])

val fv_def = Define`
  (fv (var s) = {s}) /\
  (fv (app t u) = fv t UNION fv u) /\
  (fv (lam v t) = fv t DELETE v)
`;
val _ = export_rewrites ["fv_def"]

val finite_fv = Store_Thm(
  "finite_fv",
  ``!t. FINITE (fv t)``,
  Induct THEN SRW_TAC [][]);

val ptpm_def = Define`
  (ptpm p (var s) = var (perm_of p s)) /\
  (ptpm p (app t u) = app (ptpm p t) (ptpm p u)) /\
  (ptpm p (lam v t) = lam (perm_of p v) (ptpm p t))
`;
val _ = export_rewrites ["ptpm_def"]

val ptpm_INVERSE = Store_Thm(
  "ptpm_INVERSE",
  ``!p. (ptpm p (ptpm (REVERSE p) t) = t) /\
        (ptpm (REVERSE p) (ptpm p t) = t)``,
  Induct_on `t` THEN SRW_TAC [][]);

val ptpm_NIL = Store_Thm(
  "ptpm_NIL",
  ``ptpm [] t = t``,
  Induct_on `t` THEN SRW_TAC [][]);

val ptpm_id_front = Store_Thm(
  "ptpm_id_front",
  ``!x t. ptpm ((x,x)::t) M = ptpm t M``,
  Induct_on `M` THEN SRW_TAC [][]);

val ptpm_sing_inv = Store_Thm(
  "ptpm_sing_inv",
  ``ptpm [h] (ptpm [h] t) = t``,
  METIS_TAC [ptpm_INVERSE, listTheory.REVERSE_DEF, listTheory.APPEND]);

val ptpm_is_perm = Store_Thm(
  "ptpm_is_perm",
  ``is_perm ptpm``,
  SRW_TAC [][is_perm_def, FUN_EQ_THM, permeq_def] THENL [
    Induct_on `x` THEN SRW_TAC [][lswapstr_APPEND],
    Induct_on `x` THEN SRW_TAC [][]
  ]);

val ptpm_fv = Store_Thm(
  "ptpm_fv",
  ``fv (ptpm p t) = setpm perm_of p (fv t)``,
  Induct_on `t` THEN
  SRW_TAC [][perm_EMPTY, perm_INSERT, perm_UNION, perm_DELETE]);

val allatoms_def = Define`
  (allatoms (var s) = {s}) /\
  (allatoms (app t1 t2) = allatoms t1 UNION allatoms t2) /\
  (allatoms (lam v t) = v INSERT allatoms t)
`;
val _ = export_rewrites ["allatoms_def"]

val allatoms_finite = Store_Thm(
  "allatoms_finite",
  ``FINITE (allatoms t)``,
  Induct_on `t` THEN SRW_TAC [][]);

val allatoms_supports = store_thm(
  "allatoms_supports",
  ``support ptpm t (allatoms t)``,
  SRW_TAC [][support_def] THEN Induct_on `t` THEN
  SRW_TAC [][swapstr_def]);

val allatoms_fresh = store_thm(
  "allatoms_fresh",
  ``!x y. ~(x IN allatoms t) /\ ~(y IN allatoms t) ==> (ptpm [(x,y)] t = t)``,
  METIS_TAC [allatoms_supports, support_def]);

val allatoms_apart = store_thm(
  "allatoms_apart",
  ``~(a IN allatoms t) /\ b IN allatoms t ==> ~(ptpm [(a,b)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][swapstr_def] THEN
  METIS_TAC []);

val allatoms_supp = store_thm(
  "allatoms_supp",
  ``supp ptpm t = allatoms t``,
  MATCH_MP_TAC supp_unique THEN
  SRW_TAC [][allatoms_supports, SUBSET_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [support_def] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `?y. ~(y IN allatoms t) /\ ~(y IN s')`
     by (Q.SPEC_THEN `allatoms t UNION s'` MP_TAC NEW_def THEN
         SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC [allatoms_apart]);

val allatoms_perm = store_thm(
  "allatoms_perm",
  ``allatoms (ptpm p t) = setpm perm_of p (allatoms t)``,
  Induct_on `t` THEN SRW_TAC [][perm_INSERT, perm_EMPTY, perm_UNION]);

val (aeq_rules, aeq_ind, aeq_cases) = Hol_reln`
  (!s. aeq (var s) (var s)) /\
  (!t1 t2 u1 u2. aeq t1 t2 /\ aeq u1 u2 ==> aeq (app t1 u1) (app t2 u2)) /\
  (!u v z t1 t2.
      aeq (ptpm [(u,z)] t1) (ptpm [(v,z)] t2) /\
      ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\ ~(z = v) ==>
               aeq (lam u t1) (lam v t2))
`;

val aeq_app = List.nth(CONJUNCTS aeq_rules, 1)
val aeq_lam = List.nth(CONJUNCTS aeq_rules, 2)

val aeq_distinct = store_thm(
  "aeq_distinct",
  ``~(aeq (var s) (app t u)) /\ ~(aeq (var s) (lam v t)) /\
    ~(aeq (app t u) (lam v t'))``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][]);

val ptpm_sing_to_back = store_thm(
  "ptpm_sing_to_back",
  ``ptpm [(perm_of p u, perm_of p v)] (ptpm p t) = ptpm p (ptpm [(u,v)] t)``,
  Induct_on `t` THEN SRW_TAC [][GSYM perm_of_swapstr]);

val aeq_ptpm_lemma = store_thm(
  "aeq_ptpm_lemma",
  ``!t u. aeq t u ==> !p. aeq (ptpm p t) (ptpm p u)``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  MATCH_MP_TAC aeq_lam THEN
  Q.EXISTS_TAC `perm_of p z` THEN
  SRW_TAC [][allatoms_perm, ptpm_sing_to_back, perm_IN]);

val aeq_ptpm_eqn = store_thm(
  "aeq_ptpm_eqn",
  ``aeq (ptpm p t) u = aeq t (ptpm (REVERSE p) u)``,
  METIS_TAC [aeq_ptpm_lemma, ptpm_INVERSE]);

val fv_SUBSET_allatoms = store_thm(
  "fv_SUBSET_allatoms",
  ``!t. fv t SUBSET allatoms t``,
  SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN Induct THEN SRW_TAC [][] THEN
  METIS_TAC []);

val aeq_fv = store_thm(
  "aeq_fv",
  ``!t u. aeq t u ==> (fv t = fv u)``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][EXTENSION, ptpm_fv, perm_IN] THEN
  Cases_on `x = u` THEN SRW_TAC [][] THENL [
    Cases_on `u = v` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `swapstr v z u` (MP_TAC o SYM)) THEN
    SRW_TAC [][] THEN SRW_TAC [][swapstr_def] THEN
    METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
    Cases_on `x = v` THEN SRW_TAC [][] THENL [
      FIRST_X_ASSUM (Q.SPEC_THEN `swapstr u z v` MP_TAC) THEN
      SRW_TAC [][] THEN SRW_TAC [][swapstr_def] THEN
      METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
      Cases_on `z = x` THEN SRW_TAC [][] THENL [
        METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
        FIRST_X_ASSUM (Q.SPEC_THEN `x` MP_TAC) THEN
        SRW_TAC [][swapstr_def]
      ]
    ]
  ]);

val aeq_refl = Store_Thm(
  "aeq_refl",
  ``aeq t t``,
  Induct_on `t` THEN SRW_TAC [][aeq_rules] THEN
  MATCH_MP_TAC aeq_lam THEN SRW_TAC [][aeq_ptpm_eqn] THEN
  Q.SPEC_THEN `s INSERT allatoms t` MP_TAC NEW_def THEN SRW_TAC [][] THEN
  METIS_TAC []);

val ptpm_flip_args = store_thm(
  "ptpm_flip_args",
  ``!x y t. ptpm ((y,x)::t) M = ptpm ((x,y)::t) M``,
  Induct_on `M` THEN SRW_TAC [][]);

val aeq_sym = store_thm(
  "aeq_sym",
  ``!t u. aeq t u ==> aeq u t``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  METIS_TAC [aeq_lam]);

val aeq_app_inversion = store_thm(
  "aeq_app_inversion",
  ``aeq (app t u) v = ?t' u'. (v = app t' u') /\
                              aeq t t' /\ aeq u u'``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN SRW_TAC [][]);

val aeq_lam_inversion = store_thm(
  "aeq_lam_inversion",
  ``aeq (lam v M) N = ?v' M' z. (N = lam v' M') /\
                                ~(z = v') /\ ~(z = v) /\ ~(z IN allatoms M) /\
                                ~(z IN allatoms M') /\
                                aeq (ptpm [(v,z)] M) (ptpm [(v',z)] M')``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN SRW_TAC [][] THEN
  METIS_TAC []);

val aeq_ptm_11 = store_thm(
  "aeq_ptm_11",
  ``(aeq (var s1) (var s2) = (s1 = s2)) /\
    (aeq (app t1 u1) (app t2 u2) = aeq t1 t2 /\ aeq u1 u2) /\
    (aeq (lam v t1) (lam v t2) = aeq t1 t2)``,
  SRW_TAC [][aeq_app_inversion, aeq_lam_inversion, aeq_ptpm_eqn,
             EQ_IMP_THM]
  THENL [
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][],
    Q_TAC (NEW_TAC "z") `v INSERT allatoms t1 UNION allatoms t2` THEN
    Q.EXISTS_TAC `z` THEN SRW_TAC [][]
  ]);




val aeq_strong_ind = IndDefLib.derive_strong_induction (aeq_rules, aeq_ind)

(* proof follows that on p169 of Andy Pitts, Information and Computation 186
   article: Nominal logic, a first order theory of names and binding *)
val aeq_trans = store_thm(
  "aeq_trans",
  ``!t u v. aeq t u /\ aeq u v ==> aeq t v``,
  Q_TAC SUFF_TAC `!t u. aeq t u ==> !v. aeq u v ==> aeq t v`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC aeq_ind THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][],
    SRW_TAC [][aeq_app_inversion],
    Q_TAC SUFF_TAC
          `!a a' b t t'.
             (!t''. aeq (ptpm [(a',b)] t') t'' ==> aeq (ptpm [(a,b)] t) t'') /\
             ~(b IN allatoms t) /\ ~(b IN allatoms t') /\
             ~(b = a) /\ ~(b = a') ==>
             !t''. aeq (lam a' t') t'' ==> aeq (lam a t) t''`
          THEN1 METIS_TAC [] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    CONV_TAC (LAND_CONV (REWRITE_CONV [aeq_lam_inversion])) THEN
    DISCH_THEN
      (Q.X_CHOOSE_THEN `a''`
         (Q.X_CHOOSE_THEN `t'''`
              (Q.X_CHOOSE_THEN `c` STRIP_ASSUME_TAC))) THEN
    `?d. ~(d = a) /\ ~(d = a') /\ ~(d = a'') /\ ~(d = b) /\ ~(d = c) /\
         ~(d IN allatoms t) /\ ~(d IN allatoms t') /\ ~(d IN allatoms t'')`
       by (Q.SPEC_THEN `{a;a';a'';b;c} UNION allatoms t UNION allatoms t' UNION
                        allatoms t''` MP_TAC NEW_def THEN
           SRW_TAC [][] THEN METIS_TAC []) THEN
    `!t''. aeq (ptpm [(b,d)] (ptpm [(a',b)] t')) (ptpm [(b,d)] t'') ==>
           aeq (ptpm [(b,d)] (ptpm [(a,b)] t)) (ptpm [(b,d)] t'')`
       by FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    POP_ASSUM (Q.SPEC_THEN `ptpm [(b,d)] t''`
                           (ASSUME_TAC o Q.GEN `t''` o
                            SIMP_RULE (srw_ss()) [])) THEN
    POP_ASSUM (MP_TAC o
               ONCE_REWRITE_RULE [GSYM ptpm_sing_to_back]) THEN
    `!x y t. ~(x IN allatoms t) /\ ~(y IN allatoms t) ==>
             (ptpm [(x,y)] t = t)`
       by METIS_TAC [allatoms_supports, support_def] THEN
    SRW_TAC [][swapstr_def] THEN
    `aeq (ptpm [(c,d)] (ptpm [(a',c)] t'))
         (ptpm [(c,d)] (ptpm [(a'',c)] t'''))`
       by FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM ptpm_sing_to_back]) THEN
    `~(d IN allatoms t''')` by FULL_SIMP_TAC (srw_ss()) [allatoms_def] THEN
    SRW_TAC [][swapstr_def] THEN
    `aeq (ptpm [(a,d)] t) (ptpm [(a'',d)] t''')` by METIS_TAC [] THEN
    METIS_TAC [aeq_lam]
  ]);

open relationTheory
val aeq_equiv = store_thm(
  "aeq_equiv",
  ``!t1 t2. aeq t1 t2 = (aeq t1 = aeq t2)``,
  SIMP_TAC (srw_ss()) [GSYM ALT_equivalence, equivalence_def, reflexive_def,
                       symmetric_def, transitive_def] THEN
  METIS_TAC [aeq_trans, aeq_sym]);

val alt_aeq_lam = store_thm(
  "alt_aeq_lam",
  ``(!z. ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\ ~(z = v) ==>
         aeq (ptpm [(u,z)] t1) (ptpm [(v,z)] t2)) ==>
    aeq (lam u t1) (lam v t2)``,
  STRIP_TAC THEN MATCH_MP_TAC aeq_lam THEN
  `?z. ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\ ~(z = v)`
      by (Q.SPEC_THEN `allatoms t1 UNION allatoms t2 UNION {u;v}`
                      MP_TAC NEW_def THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC []);

val fresh_swap = store_thm(
  "fresh_swap",
  ``!x y. ~(x IN fv t) /\ ~(y IN fv t) ==> aeq t (ptpm [(x, y)] t)``,
  SIMP_TAC (srw_ss()) [] THEN Induct_on `t` THEN
  ASM_SIMP_TAC (srw_ss()) [aeq_rules] THEN
  REPEAT STRIP_TAC THEN SRW_TAC [][] THEN
  MATCH_MP_TAC alt_aeq_lam THEN REPEAT STRIP_TAC THEN
  `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms]
  THENL [
    Cases_on `s = x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
      SRW_TAC [][swapstr_def, aeq_ptpm_eqn],
      ALL_TAC
    ] THEN Cases_on `s = y` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
      SRW_TAC [][swapstr_def, ptpm_flip_args, aeq_ptpm_eqn],
      SRW_TAC [][swapstr_def, aeq_ptpm_eqn]
    ],
    Cases_on `s = x` THEN1 SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
    SRW_TAC [][swapstr_def, ptpm_flip_args, aeq_ptpm_eqn],
    Cases_on `s = y` THEN1 SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
    SRW_TAC [][swapstr_def, aeq_ptpm_eqn]
  ]);

val lam_aeq_thm = store_thm(
  "lam_aeq_thm",
  ``aeq (lam u t1) (lam v t2) =
       (u = v) /\ aeq t1 t2 \/
       ~(u = v) /\ ~(u IN fv t2) /\ aeq t1 (ptpm [(u,v)] t2)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM] THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][aeq_lam_inversion] THEN
    `~(z IN fv t1) /\ ~(z IN fv t2)`
       by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
    Cases_on `u = v` THEN1 FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    `~(u IN fv t2)`
        by (STRIP_TAC THEN
            `u IN fv (ptpm [(v,z)] t2)`
               by SRW_TAC [][ptpm_fv, perm_IN, swapstr_def] THEN
            `u IN fv (ptpm [(u,z)] t1)` by METIS_TAC [aeq_fv] THEN
            FULL_SIMP_TAC (srw_ss()) [ptpm_fv, perm_IN, swapstr_def]) THEN
    FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    Q.PAT_ASSUM `aeq X Y` MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
    SRW_TAC [][swapstr_def] THEN
    MATCH_MP_TAC aeq_trans THEN
    Q.EXISTS_TAC `ptpm [(u,v)] (ptpm [(u,z)] t2)`  THEN
    FULL_SIMP_TAC (srw_ss()) [ptpm_flip_args, aeq_ptpm_eqn, fresh_swap],

    SRW_TAC [][] THEN MATCH_MP_TAC alt_aeq_lam THEN SRW_TAC [][aeq_ptpm_eqn],

    SRW_TAC [][] THEN MATCH_MP_TAC alt_aeq_lam THEN
    SRW_TAC [][aeq_ptpm_eqn] THEN
    `~(z IN fv t2)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
    ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
    SRW_TAC [][swapstr_def, ptpm_flip_args] THEN
    MATCH_MP_TAC aeq_trans THEN Q.EXISTS_TAC `ptpm [(u,v)] t2` THEN
    SRW_TAC [][aeq_ptpm_eqn, fresh_swap]
  ]);

val lam_respects_aeq = store_thm(
  "lam_respects_aeq",
  ``!v t1 t2. aeq t1 t2 ==> aeq (lam v t1) (lam v t2)``,
  SRW_TAC [][] THEN MATCH_MP_TAC aeq_lam THEN SRW_TAC [][aeq_ptpm_eqn] THEN
  Q.SPEC_THEN `v INSERT allatoms t1 UNION allatoms t2` MP_TAC NEW_def THEN
  SRW_TAC [][] THEN METIS_TAC []);

val app_respects_aeq = aeq_app

val var_respects_aeq = store_thm(
  "var_respects_aeq",
  ``!s1 s2. (s1 = s2) ==> aeq (var s1) (var s2)``,
  SRW_TAC [][]);

val _ = export_theory ();

