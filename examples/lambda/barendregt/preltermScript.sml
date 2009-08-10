(* This is an -*- sml -*- file *)
open HolKernel boolLib Parse bossLib BasicProvers metisLib NEWLib

open basic_swapTheory pred_setTheory nomsetTheory termTheory

val _ = new_theory "prelterm";

val _ = Hol_datatype `l0term = var of string
                              | app of l0term => l0term
                              | lam of string => l0term
                              | lami of num => string => l0term => l0term`

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before export_rewrites [s])
fun Save_Thm(s, th) = (save_thm(s, th) before export_rewrites [s])

val fv_def = Define`
  (fv (var s) = {s}) /\
  (fv (app t u) = fv t UNION fv u) /\
  (fv (lam v t) = fv t DELETE v) /\
  (fv (lami n v t1 t2) = (fv t1 DELETE v) UNION fv t2)
`;
val _ = export_rewrites ["fv_def"]

val finite_fv = Store_Thm(
  "finite_fv",
  ``!t. FINITE (fv t)``,
  Induct THEN SRW_TAC [][]);

val ptpm_def = Define`
  (ptpm p (var s) = var (perm_of p s)) /\
  (ptpm p (app t u) = app (ptpm p t) (ptpm p u)) /\
  (ptpm p (lam v t) = lam (perm_of p v) (ptpm p t)) /\
  (ptpm p (lami n v t u) = lami n (perm_of p v) (ptpm p t) (ptpm p u))
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
  (allatoms (lam v t) = v INSERT allatoms t) /\
  (allatoms (lami n v t u) = v INSERT allatoms t UNION allatoms u)
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
  ``a IN allatoms t /\ ~(b IN allatoms t) ==> ~(ptpm [(a,b)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][swapstr_def] THEN
  METIS_TAC []);

val allatoms_supp = store_thm(
  "allatoms_supp",
  ``supp ptpm t = allatoms t``,
  MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][allatoms_supports, allatoms_apart]);

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
               aeq (lam u t1) (lam v t2)) /\
  (!u v z n t1 t2 u1 u2.
      aeq (ptpm [(u,z)] t1) (ptpm [(v,z)] t2) /\ aeq u1 u2 /\
      ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\ ~(z = v) ==>
      aeq (lami n u t1 u1) (lami n v t2 u2))
`;

val aeq_app = List.nth(CONJUNCTS aeq_rules, 1)
val aeq_lam = List.nth(CONJUNCTS aeq_rules, 2)
val aeq_lami = List.nth (CONJUNCTS aeq_rules, 3)

val aeq_distinct = store_thm(
  "aeq_distinct",
  ``~(aeq (var s) (app t u)) /\ ~(aeq (var s) (lam v t)) /\
    ~(aeq (var s) (lami n v t u)) /\
    ~(aeq (app t u) (lam v t')) /\ ~(aeq (app t u) (lami n v t' u')) /\
    ~(aeq (lam v t) (lami n v' t' u'))``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][]);

val ptpm_sing_to_back = store_thm(
  "ptpm_sing_to_back",
  ``ptpm [(perm_of p u, perm_of p v)] (ptpm p t) = ptpm p (ptpm [(u,v)] t)``,
  Induct_on `t` THEN SRW_TAC [][GSYM perm_of_swapstr]);

val aeq_ptpm_lemma = store_thm(
  "aeq_ptpm_lemma",
  ``!t u. aeq t u ==> !p. aeq (ptpm p t) (ptpm p u)``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THENL [
    MATCH_MP_TAC aeq_lam THEN
    Q.EXISTS_TAC `perm_of p z` THEN
    SRW_TAC [][allatoms_perm, ptpm_sing_to_back, perm_IN],
    MATCH_MP_TAC aeq_lami THEN
    Q.EXISTS_TAC `perm_of p z` THEN
    SRW_TAC [][allatoms_perm, ptpm_sing_to_back, perm_IN]
  ]);

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
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][EXTENSION, ptpm_fv, perm_IN] THENL [
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
    ],
    Cases_on `x = u` THEN SRW_TAC [][] THENL [
      Cases_on `u = v` THEN SRW_TAC [][] THEN
      Q.PAT_ASSUM `!x. swapstr u z x IN fv t1 = Z`
                  (Q.SPEC_THEN `swapstr v z u` (MP_TAC o SYM)) THEN
      SRW_TAC [][] THEN SRW_TAC [][swapstr_def] THEN
      METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
      Cases_on `x = v` THEN SRW_TAC [][] THENL [
        Q.PAT_ASSUM `!x. swapstr u z x IN fv t1 = Z`
                    (Q.SPEC_THEN `swapstr u z v` MP_TAC) THEN
        SRW_TAC [][] THEN SRW_TAC [][swapstr_def] THEN
        METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
        Cases_on `z = x` THEN SRW_TAC [][] THENL [
          METIS_TAC [fv_SUBSET_allatoms, SUBSET_DEF],
          Q.PAT_ASSUM `!x. swapstr u z x IN fv t1 = Z`
                      (Q.SPEC_THEN `x` MP_TAC) THEN
          SRW_TAC [][swapstr_def]
        ]
      ]
    ]
  ]);


val aeq_refl = Store_Thm(
  "aeq_refl",
  ``aeq t t``,
  Induct_on `t` THEN ASM_SIMP_TAC (srw_ss())[aeq_rules] THENL [
    Q.X_GEN_TAC `s` THEN
    MATCH_MP_TAC aeq_lam THEN SRW_TAC [][aeq_ptpm_eqn] THEN
    Q.SPEC_THEN `s INSERT allatoms t` MP_TAC NEW_def THEN SRW_TAC [][] THEN
    METIS_TAC [],
    Q.X_GEN_TAC `s` THEN GEN_TAC THEN
    MATCH_MP_TAC aeq_lami THEN SRW_TAC [][aeq_ptpm_eqn] THEN
    Q.SPEC_THEN `s INSERT allatoms t` MP_TAC NEW_def THEN SRW_TAC [][] THEN
    METIS_TAC []
  ]);

val ptpm_flip_args = store_thm(
  "ptpm_flip_args",
  ``!x y t. ptpm ((y,x)::t) M = ptpm ((x,y)::t) M``,
  Induct_on `M` THEN SRW_TAC [][]);

val aeq_sym = store_thm(
  "aeq_sym",
  ``!t u. aeq t u ==> aeq u t``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  METIS_TAC [aeq_lam, aeq_lami]);

val aeq_app_inversion = store_thm(
  "aeq_app_inversion",
  ``aeq (app t u) v = ?t' u'. (v = app t' u') /\
                              aeq t t' /\ aeq u u'``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN SRW_TAC [][]);

val aeq_app_11 = SIMP_RULE (srw_ss()) []
                           (Q.INST [`v` |-> `app t' u'`] aeq_app_inversion)
val aeq_var_11 = prove(
  ``aeq (var s1) (var s2) = (s1 = s2)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][] THEN METIS_TAC []);


val aeq_lam_inversion = store_thm(
  "aeq_lam_inversion",
  ``aeq (lam v M) N = ?v' M' z. (N = lam v' M') /\
                                ~(z = v') /\ ~(z = v) /\ ~(z IN allatoms M) /\
                                ~(z IN allatoms M') /\
                                aeq (ptpm [(v,z)] M) (ptpm [(v',z)] M')``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN SRW_TAC [][] THEN
  METIS_TAC []);

val aeq_lami_inversion = store_thm(
  "aeq_lami_inversion",
  ``aeq (lami n v M N) P =
      ?v' M' N' z. (P = lami n v' M' N') /\
                   ~(z = v') /\ ~(z = v) /\
                   ~(z IN allatoms M) /\ ~(z IN allatoms M') /\
                   aeq (ptpm [(v,z)] M) (ptpm [(v',z)] M') /\
                   aeq N N'``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN SRW_TAC [][] THEN
  METIS_TAC []);

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
    METIS_TAC [aeq_lam],
    Q_TAC SUFF_TAC
          `!a a' n b t t' u u'.
             (!t''. aeq (ptpm [(a',b)] t') t'' ==> aeq (ptpm [(a,b)] t) t'') /\
             ~(b IN allatoms t) /\ ~(b IN allatoms t') /\
             ~(b = a) /\ ~(b = a') /\
             (!u''. aeq u' u'' ==> aeq u u'') ==>
             !t''. aeq (lami n a' t' u') t'' ==> aeq (lami n a t u) t''`
           THEN1 (STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
                  FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    CONV_TAC (LAND_CONV (REWRITE_CONV [aeq_lami_inversion])) THEN
    DISCH_THEN
      (Q.X_CHOOSE_THEN `a''`
         (Q.X_CHOOSE_THEN `t'''`
            (Q.X_CHOOSE_THEN `u''`
               (Q.X_CHOOSE_THEN `c` STRIP_ASSUME_TAC)))) THEN
    `?d. ~(d = a) /\ ~(d = a') /\ ~(d = a'') /\ ~(d = b) /\ ~(d = c) /\
         ~(d IN allatoms t) /\ ~(d IN allatoms t') /\ ~(d IN allatoms t'')`
       by (Q.SPEC_THEN `{a;a';a'';b;c} UNION allatoms t UNION allatoms t' UNION
                        allatoms t''` MP_TAC NEW_def THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    `!t''. aeq (ptpm [(b,d)] (ptpm [(a',b)] t')) (ptpm [(b,d)] t'') ==>
           aeq (ptpm [(b,d)] (ptpm [(a,b)] t)) (ptpm [(b,d)] t'')`
       by FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    POP_ASSUM (Q.SPEC_THEN `ptpm [(b,d)] t''`
                           (ASSUME_TAC o Q.GEN `t''` o
                            SIMP_RULE (srw_ss()) [])) THEN
    POP_ASSUM (MP_TAC o
               ONCE_REWRITE_RULE [GSYM ptpm_sing_to_back]) THEN
    SRW_TAC [][allatoms_fresh, swapstr_def] THEN
    `aeq (ptpm [(c,d)] (ptpm [(a',c)] t'))
         (ptpm [(c,d)] (ptpm [(a'',c)] t'''))`
       by FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM ptpm_sing_to_back]) THEN
    `~(d IN allatoms t''')` by FULL_SIMP_TAC (srw_ss()) [allatoms_def] THEN
    SRW_TAC [][allatoms_fresh, swapstr_def] THEN
    `aeq (ptpm [(a,d)] t) (ptpm [(a'',d)] t''')` by METIS_TAC [] THEN
    METIS_TAC [aeq_lami]
  ]);

open relationTheory
val aeq_equiv = store_thm(
  "aeq_equiv",
  ``!t1 t2. aeq t1 t2 = (aeq t1 = aeq t2)``,
  SIMP_TAC (srw_ss()) [GSYM ALT_equivalence, equivalence_def, reflexive_def,
                       symmetric_def, transitive_def] THEN
  METIS_TAC [aeq_trans, aeq_sym]);

val swapstr_safe = prove(
  ``(swapstr x y x = y) /\ (swapstr y x x = y)``,
  SRW_TAC [][swapstr_def]);

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

val alt_aeq_lami = store_thm(
  "alt_aeq_lami",
  ``(!z. ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\ ~(z = v) ==>
         aeq (ptpm [(u,z)] t1) (ptpm [(v,z)] t2)) /\ aeq u1 u2 ==>
    aeq (lami n u t1 u1) (lami n v t2 u2)``,
  STRIP_TAC THEN MATCH_MP_TAC aeq_lami THEN
  `?z. ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\ ~(z = v)`
      by (Q.SPEC_THEN `allatoms t1 UNION allatoms t2 UNION {u;v}`
                      MP_TAC NEW_def THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC []);

val fresh_swap = store_thm(
  "fresh_swap",
  ``!x y. ~(x IN fv t) /\ ~(y IN fv t) ==> aeq t (ptpm [(x, y)] t)``,
  SIMP_TAC (srw_ss()) [] THEN Induct_on `t` THEN
  ASM_SIMP_TAC (srw_ss()) [aeq_rules, swapstr_safe] THENL [
    Q.X_GEN_TAC `s` THEN
    REPEAT STRIP_TAC THEN SRW_TAC [][] THEN
    MATCH_MP_TAC alt_aeq_lam THEN REPEAT STRIP_TAC THEN
    `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms]
    THENL [
      Cases_on `s = x` THEN FULL_SIMP_TAC (srw_ss()) [swapstr_safe] THENL [
        ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
        SRW_TAC [][swapstr_def, aeq_ptpm_eqn],
        ALL_TAC
      ] THEN Cases_on `s = y` THENL [
        FULL_SIMP_TAC (srw_ss()) [swapstr_safe] THEN
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
    ],
    Q.X_GEN_TAC `s` THEN
    REPEAT STRIP_TAC THEN SRW_TAC [][swapstr_safe] THEN
    MATCH_MP_TAC alt_aeq_lami THEN REPEAT STRIP_TAC THEN
    TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN NO_TAC) THEN
    `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms]
    THENL [
      Cases_on `s = x` THEN FULL_SIMP_TAC (srw_ss()) [swapstr_safe] THENL [
        ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
        SRW_TAC [][swapstr_def, aeq_ptpm_eqn],
        ALL_TAC
      ] THEN Cases_on `s = y` THENL [
        FULL_SIMP_TAC (srw_ss()) [swapstr_safe] THEN
        ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
        SRW_TAC [][swapstr_def, aeq_ptpm_eqn, ptpm_flip_args],
        SRW_TAC [][swapstr_def, aeq_ptpm_eqn]
      ],
      Cases_on `s = x` THEN1 SRW_TAC [][] THEN
      ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
      SRW_TAC [][swapstr_def, ptpm_flip_args, aeq_ptpm_eqn],
      Cases_on `s = y` THEN1 SRW_TAC [][] THEN
      ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
      SRW_TAC [][swapstr_def, aeq_ptpm_eqn]
    ]
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

val lami_nfixed = store_thm(
  "lami_nfixed",
  ``aeq (lami n v M1 N1) (lami m u M2 N2) ==> (n = m)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][]);

val lami_aeq_thm = store_thm(
  "lami_aeq_thm",
  ``aeq (lami m u M1 N1) (lami n v M2 N2) =
        (u = v) /\ (m = n) /\ aeq M1 M2 /\ aeq N1 N2 \/
        ~(u = v) /\ (m = n) /\ ~(u IN fv M2) /\ aeq M1 (ptpm [(u,v)] M2) /\
        aeq N1 N2``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM] THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][aeq_lami_inversion] THEN
    `~(z IN fv M1) /\ ~(z IN fv M2)`
        by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
    Cases_on `u = v` THEN1 FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    `~(u IN fv M2)`
        by (STRIP_TAC THEN
            `u IN fv (ptpm [(v,z)] M2)`
              by SRW_TAC [][perm_IN, swapstr_def] THEN
            `u IN fv (ptpm [(u,z)] M1)` by METIS_TAC [aeq_fv] THEN
            FULL_SIMP_TAC (srw_ss()) [perm_IN, swapstr_def]) THEN
    FULL_SIMP_TAC (srw_ss()) [aeq_ptpm_eqn] THEN
    Q.PAT_ASSUM `aeq M1 (ptpm X Z)` MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
    SRW_TAC [][swapstr_def] THEN
    MATCH_MP_TAC aeq_trans THEN
    Q.EXISTS_TAC `ptpm [(u,v)] (ptpm [(u,z)] M2)` THEN
    FULL_SIMP_TAC (srw_ss()) [ptpm_flip_args, aeq_ptpm_eqn, fresh_swap],

    SRW_TAC [][] THEN MATCH_MP_TAC alt_aeq_lami THEN
    SRW_TAC [][aeq_ptpm_eqn],

    SRW_TAC [][] THEN MATCH_MP_TAC alt_aeq_lami THEN
    SRW_TAC [][aeq_ptpm_eqn] THEN
    ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
    `~(z IN fv M2)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
    SRW_TAC [][swapstr_def, ptpm_flip_args] THEN
    MATCH_MP_TAC aeq_trans THEN Q.EXISTS_TAC `ptpm [(u,v)] M2` THEN
    SRW_TAC [][aeq_ptpm_eqn, fresh_swap]
  ]);

val lam_respects_aeq = prove(
  ``!v t1 t2. aeq t1 t2 ==> aeq (lam v t1) (lam v t2)``,
  SRW_TAC [][lam_aeq_thm]);

val app_respects_aeq = aeq_app

val var_respects_aeq = prove(
  ``!s1 s2. (s1 = s2) ==> aeq (var s1) (var s2)``,
  SRW_TAC [][]);

val lami_respects_aeq = prove(
  ``!n v M1 M2 N1 N2. aeq M1 M2 /\ aeq N1 N2 ==>
                      aeq (lami n v M1 N1) (lami n v M2 N2)``,
  SRW_TAC [][lami_aeq_thm]);

val alt_aeq_ind = store_thm(
  "alt_aeq_ind",
  ``(!s. P (var s) (var s)) /\
    (!t1 t2 u1 u2.
         P t1 t2 /\ P u1 u2 ==> P (app t1 u1) (app t2 u2)) /\
    (!u v t1 t2.
         (!z. ~(z IN allatoms t1) /\ ~(z IN allatoms t2) /\ ~(z = u) /\
              ~(z = v) ==> P (ptpm [(u,z)] t1) (ptpm [(v,z)] t2)) ==>
         P (lam u t1) (lam v t2)) /\
    (!n u v M1 M2 N1 N2.
         (!z. ~(z IN allatoms M1) /\ ~(z IN allatoms M2) /\ ~(z = u) /\
              ~(z = v) ==> P (ptpm [(u,z)] M1) (ptpm [(v,z)] M2)) /\
         P N1 N2 ==> P (lami n u M1 N1) (lami n v M2 N2)) ==>
    !t1 t2. aeq t1 t2 ==> P t1 t2``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t1 t2. aeq t1 t2 ==> !pi. P (ptpm pi t1) (ptpm pi t2)`
        THEN1 METIS_TAC [ptpm_NIL] THEN
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][] THENL [
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    Q.ABBREV_TAC `zz = perm_of (REVERSE pi) z'` THEN
    `z' = perm_of pi zz` by SRW_TAC [][Abbr`zz`] THEN
    SRW_TAC [][ptpm_sing_to_back] THEN
    `~(zz IN allatoms t1) /\ ~(zz IN allatoms t2) /\ ~(zz = u) /\ ~(zz = v)`
          by FULL_SIMP_TAC (srw_ss()) [Abbr`zz`, allatoms_perm, perm_IN,
                                       is_perm_eql] THEN
    REPEAT (FIRST_X_ASSUM
              (K ALL_TAC o assert (free_in ``z':string`` o concl))) THEN
    `(ptpm [(u,zz)] t1 = ptpm [(z,zz)] (ptpm [(u,z)] t1)) /\
     (ptpm [(v,zz)] t2 = ptpm [(z,zz)] (ptpm [(v,z)] t2))`
        by (ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
            SRW_TAC [][swapstr_def, allatoms_fresh]) THEN
    METIS_TAC [is_perm_decompose, ptpm_is_perm],

    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
    Q.ABBREV_TAC `zz = perm_of (REVERSE pi) z'` THEN
    `z' = perm_of pi zz` by SRW_TAC [][Abbr`zz`] THEN
    SRW_TAC [][ptpm_sing_to_back] THEN
    `~(zz IN allatoms t1) /\ ~(zz IN allatoms t2) /\ ~(zz = u) /\ ~(zz = v)`
          by FULL_SIMP_TAC (srw_ss()) [Abbr`zz`, allatoms_perm, perm_IN,
                                       is_perm_eql] THEN
    REPEAT (FIRST_X_ASSUM
              (K ALL_TAC o assert (free_in ``z':string`` o concl))) THEN
    `(ptpm [(u,zz)] t1 = ptpm [(z,zz)] (ptpm [(u,z)] t1)) /\
     (ptpm [(v,zz)] t2 = ptpm [(z,zz)] (ptpm [(v,z)] t2))`
        by (ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
            SRW_TAC [][swapstr_def, allatoms_fresh]) THEN
    METIS_TAC [is_perm_decompose, ptpm_is_perm]
  ]);

val _ = export_theory()
