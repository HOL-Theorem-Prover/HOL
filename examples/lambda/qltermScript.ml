(* This is an -*- sml -*- file *)
open HolKernel boolLib Parse bossLib BasicProvers metisLib NEWLib

open basic_swapTheory pred_setTheory nomsetTheory termTheory

local open swapTheory in end

val _ = new_theory "labelledTerms";

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
    ~(aeq (app t u) (lam v t')) /\ ~(aeq (app t u) (lami n v t' u'))``,
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
  Induct_on `t` THEN SRW_TAC [][aeq_rules] THENL [
    MATCH_MP_TAC aeq_lam THEN SRW_TAC [][aeq_ptpm_eqn] THEN
    Q.SPEC_THEN `s INSERT allatoms t` MP_TAC NEW_def THEN SRW_TAC [][] THEN
    METIS_TAC [],
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

val aeq_strong_ind = IndDefRules.derive_strong_induction (CONJUNCTS aeq_rules,
                                                          aeq_ind)

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

(* could perform quotient now *)

(* rather, show connection with nomset concepts *)

val lamf = ``lamf : string -> 'a -> 'a``
val h = ``\a':string. ^lamf a' ((s:(string # string) list->'a)
                                 (pi ++ [(a',a)]))``

val limf = ``limf : num -> string -> 'a -> 'a -> 'a``
val i = ``\a':string.
             ^limf n a' ((s:(string # string) list -> 'a) (pi ++ [(a',a)]))``
val limf_pm = ``fnpm (K I : num pm) (fnpm perm_of (fnpm apm (fnpm apm apm)))``




val lamf_supp_t = ``supp (fnpm perm_of (fnpm apm apm)) ^lamf``
val limf_supp_t = ``supp ^limf_pm ^limf``

val finite_supp = prove(
  ``is_perm pm /\ support pm a X /\ FINITE X ==> FINITE(supp pm a)``,
  METIS_TAC [supp_smallest, SUBSET_FINITE]);

val perm_fnapp = prove(
  ``is_perm pm1 /\ is_perm pm2 ==>
    (pm2 pi (f x) = (fnpm pm1 pm2 pi f) (pm1 pi x))``,
  SRW_TAC [][fnpm_def, is_perm_inverse]);

val supp_fresh = prove(
  ``is_perm pm /\ ~(x IN supp pm a) /\ ~(y IN supp pm a) ==>
    (pm [(x,y)] a = a)``,
  METIS_TAC [supp_supports, support_def]);

val supp_freshf = prove(
  ``is_perm pm1 /\ is_perm pm2 /\
    ~(x IN supp (fnpm pm1 pm2) f) /\ ~(y IN supp (fnpm pm1 pm2) f) ==>
    !a. pm2 [(x,y)] (f a) = f (pm1 [(x,y)] a)``,
  REPEAT STRIP_TAC THEN
  `pm2 [(x,y)] (f a) = fnpm pm1 pm2 [(x,y)] f (pm1 [(x,y)] a)`
     by SRW_TAC [][GSYM perm_fnapp] THEN
  SRW_TAC [][supp_fresh]);

val support_freshf = prove(
  ``is_perm pm1 /\ is_perm pm2 /\ ~(x IN A) /\ ~(y IN A) /\
    support (fnpm pm1 pm2) f A ==>
    !a. pm2 [(x,y)] (f a) = f (pm1 [(x,y)] a)``,
  SRW_TAC [][support_def] THEN
  `pm2 [(x,y)] (f a) = fnpm pm1 pm2 [(x,y)] f (pm1 [(x,y)] a)`
     by SRW_TAC [][GSYM perm_fnapp] THEN
  SRW_TAC [][]);

val is_perm_sing_inv = store_thm(
  "is_perm_sing_inv",
  ``is_perm pm ==> (pm [h] (pm [h] x) = x)``,
  METIS_TAC [listTheory.REVERSE_DEF, listTheory.APPEND, is_perm_inverse]);

val lamf_support_t = ``support (fnpm perm_of (fnpm apm apm)) lamf A``
val app_support_t = ``support (fnpm apm (fnpm apm apm)) ap A``
val var_support_t = ``support (fnpm perm_of apm) vr A``
val limf_support_t = ``support ^limf_pm limf A``

val lamf_support_fresh = UNDISCH (UNDISCH (prove(
  ``^lamf_support_t ==> is_perm apm ==>
    !x y v a.
      ~(x IN A) /\ ~(y IN A) ==>
        (apm [(x,y)] (lamf v a) = lamf (swapstr x y v) (apm [(x,y)] a))``,
  REPEAT STRIP_TAC THEN
  `apm [(x,y)] (lamf v a) =
       fnpm apm apm [(x,y)] (lamf v) (apm [(x,y)] a)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `swapstr x y v = perm_of [(x,y)] v` by SRW_TAC [][] THEN
  POP_ASSUM SUBST1_TAC THEN MATCH_MP_TAC support_freshf THEN
  SRW_TAC [][])))

val limf_support_fresh = UNDISCH (UNDISCH (prove(
  ``^limf_support_t ==> is_perm apm ==>
    !x y v n a1 a2.
       ~(x IN A) /\ ~(y IN A) ==>
       (apm [(x,y)] (limf n v a1 a2) =
          limf n (swapstr x y v) (apm [(x,y)] a1) (apm [(x,y)] a2))``,
  REPEAT STRIP_TAC THEN
  `apm [(x,y)] (limf n v a1 a2) =
       fnpm apm apm [(x,y)] (limf n v a1) (apm [(x,y)] a2)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `fnpm apm apm [(x,y)] (limf n v a1) =
       fnpm apm (fnpm apm apm) [(x,y)] (limf n v) (apm [(x,y)] a1)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `fnpm apm (fnpm apm apm) [(x,y)] (limf n v) =
       fnpm perm_of (fnpm apm (fnpm apm apm)) [(x,y)] (limf n)
            (swapstr x y v)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `fnpm perm_of (fnpm apm (fnpm apm apm)) [(x,y)] (limf n) =
     ^limf_pm [(x,y)] limf n`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  METIS_TAC [support_def])));

val h_supp_t = ``supp (fnpm perm_of apm) ^h``
val i_supp_t = ``supp (fnpm perm_of (fnpm apm apm)) ^i``

val ctxt00 = ``^lamf_support_t /\ ^limf_support_t /\ FINITE A /\ is_perm apm``
val ctxt_s_supp =
    ``support (fnpm (cpmpm) apm) s sS /\ FINITE sS``
val ctxt_s12_supp =
    ``support (fnpm (cpmpm) apm) s1 sS1 /\
      FINITE sS1 /\
      support (fnpm (cpmpm) apm) s2 sS2 /\
      FINITE sS2``

val ssupport_fresh = UNDISCH (UNDISCH (prove(
  ``support (fnpm (cpmpm) apm) s sS ==>
    is_perm apm ==>
    !x y p.
      ~(x IN sS) /\ ~(y IN sS) ==>
      (apm [(x,y)] (s p) = s (cpmpm [(x,y)] p))``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (Q.GEN `A` support_freshf) THEN Q.EXISTS_TAC `sS` THEN
  SRW_TAC [][])));

val s1support_fresh = Q.INST [`s` |-> `s1`, `sS` |-> `sS1`] ssupport_fresh
val s2support_fresh = Q.INST [`s` |-> `s2`, `sS` |-> `sS2`] ssupport_fresh

val h_supported_by = prove(
  ``!a s sS pi.
       ^ctxt00 /\ ^ctxt_s_supp ==>
       support (fnpm perm_of apm) ^h (a INSERT (A UNION patoms pi UNION sS))``,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASSUME_TAC [lamf_support_fresh, ssupport_fresh] THEN
  SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, cpmpm_APPENDlist]);
val i_supported_by = prove(
  ``!a s1 s2 sS1 sS2 pi.
       ^ctxt00 /\ ^ctxt_s_supp ==>
       support (fnpm perm_of (fnpm apm apm)) ^i
               (a INSERT A UNION patoms pi UNION sS)``,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASSUME_TAC [limf_support_fresh, ssupport_fresh] THEN
  SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, cpmpm_APPENDlist,
             is_perm_sing_inv]);

val cond16 = ``?a'. ~(a' IN A) /\ !x. ~(a' IN supp apm (^lamf a' x))``
val cond16i = ``?a'. ~(a' IN A) /\
                      !n x. ~(a' IN supp (fnpm apm apm) (^limf n a' x))``

val cond16_implies_freshness_ok = prove(
  ``!a s A sS.
       ^ctxt00 /\ ^ctxt_s_supp /\ ^cond16 ==>
       ?a'. ~(a' IN ^h_supp_t) /\ ~(a' IN supp apm (^h a'))``,
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `h = ^h` THEN
  `!a'' x. ~(a'' IN A) /\ ~(a' = a'') ==>
           ~(a'' IN supp apm (lamf a'' (apm [(a',a'')] x)))`
      by (REPEAT GEN_TAC THEN STRIP_TAC THEN
          `lamf a'' = fnpm apm apm [(a',a'')] (lamf a')`
              by SRW_TAC [][fnpm_def, FUN_EQ_THM, is_perm_sing_inv,
                            lamf_support_fresh] THEN
          SRW_TAC [][fnpm_def, is_perm_sing_inv, perm_supp]) THEN
  Q_TAC (NEW_TAC "a''") `{a;a'} UNION A UNION sS UNION patoms pi` THEN
  `support (fnpm perm_of apm) h (a INSERT A UNION patoms pi UNION sS)`
     by (Q.UNABBREV_ALL_TAC THEN MATCH_MP_TAC h_supported_by THEN
         SRW_TAC [][]) THEN
  Q.EXISTS_TAC `a''` THEN SRW_TAC [][] THENL [
    `~(a'' IN a INSERT A UNION patoms pi UNION sS)` by SRW_TAC [][] THEN
    `FINITE (a INSERT A UNION patoms pi UNION sS)` by SRW_TAC [][] THEN
    METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm, perm_of_is_perm],
    Q.UNABBREV_TAC `h` THEN
    FIRST_X_ASSUM
      (Q.SPECL_THEN [`a''`, `apm [(a',a'')] (s (pi ++ [(a'',a)]))`]
         MP_TAC) THEN
    SRW_TAC [][is_perm_sing_inv]
  ]);

val cond16i_implies_freshness_ok = prove(
  ``!a s sS A.
       ^ctxt00 /\ ^ctxt_s_supp /\ ^cond16i ==>
       ?a'. ~(a' IN ^i_supp_t) /\ ~(a' IN supp (fnpm apm apm) (^i a'))``,
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `i = ^i` THEN
  `!a'' n x. ~(a'' IN A) /\ ~(a' = a'') ==>
             ~(a'' IN supp (fnpm apm apm) (limf n a'' (apm [(a',a'')] x)))`
      by (REPEAT GEN_TAC THEN STRIP_TAC THEN
          `limf n' a'' = fnpm apm (fnpm apm apm) [(a',a'')] (limf n' a')`
              by SRW_TAC [][fnpm_def, FUN_EQ_THM, is_perm_sing_inv,
                            limf_support_fresh] THEN
          SRW_TAC [][fnpm_def, is_perm_sing_inv, perm_supp]) THEN
  Q_TAC (NEW_TAC "a''") `{a;a'} UNION A UNION sS UNION patoms pi` THEN
  `support (fnpm perm_of (fnpm apm apm)) i
           (a INSERT A UNION patoms pi UNION sS)`
     by (Q.UNABBREV_ALL_TAC THEN MATCH_MP_TAC i_supported_by THEN
         SRW_TAC [][]) THEN
  Q.EXISTS_TAC `a''` THEN SRW_TAC [][] THENL [
    `~(a'' IN a INSERT A UNION patoms pi UNION sS)`
       by SRW_TAC [][] THEN
    `FINITE (a INSERT A UNION patoms pi UNION sS)`
       by SRW_TAC [][] THEN
    METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm, perm_of_is_perm],
    Q.UNABBREV_TAC `i` THEN
    FIRST_X_ASSUM
      (Q.SPECL_THEN [`a''`, `n`, `apm [(a',a'')] (s (pi ++ [(a'',a)]))`]
         MP_TAC) THEN
    SRW_TAC [][is_perm_sing_inv]
  ]);

val base =
    SPECL [``\(s:string) p. vr (perm_of p s) : 'a``]
          (INST_TYPE [alpha |-> ``:(string # string) list -> 'a``]
                     (TypeBase.axiom_of "l0term"))
val full0 = Q.SPECL [`\t u r1 r2 p. ap (r1 p) (r2 p)`,
                    `\a t s pi. fresh apm ^h`,
                    `\n a t1 t2 s s2 pi. fresh (fnpm apm apm) ^i (s2 pi)`] base

val full = SIMP_RULE (srw_ss()) [FUN_EQ_THM] full0


val fndefn = #2 (dest_exists (concl full))

val swapstr_perm_of = store_thm(
  "swapstr_perm_of",
  ``swapstr x y (perm_of pi s) =
    perm_of (cpmpm [(x,y)] pi) (swapstr x y s)``,
  Induct_on `pi` THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, listpm_def, pairpm_def] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN SRW_TAC [][]);

val rawfinite_support = prove(
  ``^fndefn /\ ^ctxt00 /\ ^cond16 /\ ^cond16i /\ ^var_support_t /\
    ^app_support_t ==>
    support (fnpm ptpm (fnpm (cpmpm) apm)) fn A``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] THEN
  Q_TAC SUFF_TAC
        `!t pi x y.  ~(x IN A) /\ ~(y IN A) ==>
                     (apm [(x,y)] (fn (ptpm [(x,y)] t) (cpmpm [(x,y)] pi)) =
                      fn t pi)`
        THEN1 PROVE_TAC [] THEN
  Induct THEN SRW_TAC [][fnpm_def] THENL [
    `(!s. apm [(x,y)] (vr s) = vr (perm_of [(x,y)] s))`
        by (MATCH_MP_TAC support_freshf THEN SRW_TAC [][]) THEN
    SRW_TAC [][swapstr_perm_of, is_perm_sing_inv],

    `!a b pi. apm pi (ap a b) =
              fnpm apm apm pi (ap a) (apm pi b)`
        by SRW_TAC [][fnpm_def, is_perm_inverse] THEN
    SRW_TAC [][] THEN
    `!t. fnpm apm apm [(x,y)] (ap t) = ap (apm [(x,y)] t)`
        by (MATCH_MP_TAC support_freshf THEN SRW_TAC [][]) THEN
    SRW_TAC [][],

    Q.MATCH_ABBREV_TAC `apm [(x,y)] (fresh apm g) = fresh apm h` THEN
    `h = fnpm perm_of apm [(x,y)] g`
       by (MAP_EVERY Q.UNABBREV_TAC [`g`, `h`] THEN
           SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `a` THEN
           SRW_TAC [][fnpm_def, lamf_support_fresh] THEN
           `cpmpm [(x,y)] pi ++ [(swapstr x y a, swapstr x y s)] =
                cpmpm [(x,y)] (pi ++ [(a,s)])`
              by SRW_TAC [][cpmpm_APPENDlist] THEN
           SRW_TAC [][]) THEN
    POP_ASSUM (fn th =>
                  Q_TAC SUFF_TAC `fcond apm h` THEN1
                        SRW_TAC [][fresh_equivariant, is_perm_eql,
                                   is_perm_sing_inv, th]) THEN
    Q.UNABBREV_ALL_TAC THEN
    `support (fnpm (cpmpm) apm) (fn t) (A UNION allatoms t)`
       by (SIMP_TAC (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] THEN
           MAP_EVERY Q.X_GEN_TAC [`c`, `d`] THEN REPEAT STRIP_TAC THEN
           `!x. apm [(c,d)] (fn t x) =
                fnpm (cpmpm) apm [(c,d)] (fn t) (cpmpm [(c,d)] x)`
             by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
           SRW_TAC [][is_perm_sing_inv] THEN
           `fnpm (cpmpm) apm [(c,d)] (fn t) =
            fnpm ptpm (fnpm (cpmpm) apm) [(c,d)] fn
                 (ptpm [(c,d)] t)`
             by SRW_TAC [][fnpm_def] THEN
           `ptpm [(c,d)] t = t`
             by PROVE_TAC [allatoms_supports, support_def] THEN
           SRW_TAC [][] THEN
           NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN SRW_TAC [][fnpm_def]) THEN
    Q.ABBREV_TAC `bigA = A UNION allatoms t UNION patoms pi` THEN
    `support (fnpm perm_of (fnpm apm apm)) lamf bigA /\
     support (fnpm (cpmpm) apm) (fn t) bigA /\
     support (cpmpm) pi bigA`
       by FULL_SIMP_TAC (srw_ss()) [support_def, Abbr`bigA`] THEN
    SRW_TAC [][fcond_def] THENL [
      Q.MATCH_ABBREV_TAC `FINITE (supp pm h)` THEN
      Q_TAC SUFF_TAC `?X. FINITE X /\ support pm h X`
            THEN1 METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                             perm_of_is_perm] THEN
      Q.EXISTS_TAC `s INSERT A UNION patoms pi UNION (A UNION allatoms t)` THEN
      SRW_TAC [][Abbr`bigA`, Abbr`h`, Abbr`pm`] THEN
      MATCH_MP_TAC h_supported_by THEN
      SRW_TAC [][],

      MATCH_MP_TAC (BETA_RULE cond16_implies_freshness_ok) THEN
      MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t`] THEN
      SRW_TAC [][] THEN METIS_TAC []
    ],

    Q.MATCH_ABBREV_TAC
      `apm [(x,y)] (fresh (fnpm apm apm) g arg1) =
       fresh (fnpm apm apm) h arg2` THEN
    `h = fnpm perm_of (fnpm apm apm) [(x,y)] g`
       by (MAP_EVERY Q.UNABBREV_TAC [`g`, `h`] THEN
           SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `a` THEN
           SRW_TAC [][fnpm_def, limf_support_fresh, is_perm_sing_inv] THEN
           `cpmpm [(x,y)] pi ++ [(swapstr x y a, swapstr x y s)] =
                cpmpm [(x,y)] (pi ++ [(a,s)])`
              by SRW_TAC [][cpmpm_APPENDlist, listpm_def, pairpm_def] THEN
           SRW_TAC [][]) THEN
    `arg2 = apm [(x,y)] arg1` by SRW_TAC [][Abbr`arg1`, Abbr`arg2`,
                                            is_perm_sing_inv] THEN
    Q.PAT_ASSUM `h = foo` (fn th =>
                  Q_TAC SUFF_TAC `fcond (fnpm apm apm) h` THEN1
                        (`apm [(x,y)] (fresh (fnpm apm apm) g arg1) =
                          fnpm apm apm [(x,y)] (fresh (fnpm apm apm) g)
                                               (apm [(x,y)] arg1)`
                             by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN

                         SRW_TAC [][fresh_equivariant, th])) THEN
    Q.UNABBREV_ALL_TAC THEN
    `support (fnpm (cpmpm) apm) (fn t)
             (A UNION allatoms t)`
       by (SIMP_TAC (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] THEN
           MAP_EVERY Q.X_GEN_TAC [`c`, `d`] THEN REPEAT STRIP_TAC THEN
           `!x. apm [(c,d)] (fn t x) =
                fnpm (cpmpm) apm [(c,d)] (fn t)
                     (cpmpm [(c,d)] x)`
             by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
           SRW_TAC [][is_perm_sing_inv] THEN
           `fnpm (cpmpm) apm [(c,d)] (fn t) =
            fnpm ptpm (fnpm (cpmpm) apm) [(c,d)] fn
                 (ptpm [(c,d)] t)`
             by SRW_TAC [][fnpm_def] THEN
           `ptpm [(c,d)] t = t`
             by PROVE_TAC [allatoms_supports, support_def] THEN
           SRW_TAC [][] THEN
           NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN SRW_TAC [][fnpm_def]) THEN
    Q.ABBREV_TAC `bigA = A UNION allatoms t UNION patoms pi` THEN
    `support (fnpm perm_of (fnpm apm apm)) lamf bigA /\
     support (fnpm (cpmpm) apm) (fn t) bigA /\
     support (cpmpm) pi bigA`
       by FULL_SIMP_TAC (srw_ss()) [support_def, Abbr`bigA`] THEN
    SRW_TAC [][fcond_def] THENL [
      Q.MATCH_ABBREV_TAC `FINITE (supp pm h)` THEN
      Q_TAC SUFF_TAC `?X. FINITE X /\ support pm h X`
            THEN1 METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                             perm_of_is_perm] THEN
      Q.EXISTS_TAC
        `s INSERT A UNION patoms pi UNION (A UNION allatoms t)` THEN
      SRW_TAC [][Abbr`bigA`, Abbr`h`, Abbr`pm`] THEN
      MATCH_MP_TAC i_supported_by THEN
      SRW_TAC [][],

      MATCH_MP_TAC (BETA_RULE cond16i_implies_freshness_ok) THEN
      MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms t`, `A`] THEN
      SRW_TAC [][] THEN METIS_TAC []
    ]
  ]);

val eqperms_ok = prove(
  ``^fndefn ==>
    !t p1 p2. (p1 == p2) ==> (fn t p1 = fn t p2)``,
  STRIP_TAC THEN Induct THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [permeq_def],
    METIS_TAC [],
    Q_TAC SUFF_TAC `!a. fn t (p1 ++ [(a,s)]) = fn t (p2 ++ [(a,s)])` THEN1
          SRW_TAC [][] THEN
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC app_permeq_monotone THEN
    SRW_TAC [][permeq_refl],
    Q_TAC SUFF_TAC `(!a. fn t (p1 ++ [(a,s)]) = fn t (p2 ++ [(a,s)])) /\
                    (fn t' p1 = fn t' p2)` THEN1 SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC app_permeq_monotone THEN SRW_TAC [][permeq_refl]
  ]);

val perm_of_unchanged = store_thm(
  "perm_of_unchanged",
  ``!p. ~(s IN patoms p) ==> (perm_of p s = s)``,
  Induct THEN SIMP_TAC (srw_ss()) [patoms_def, pairTheory.FORALL_PROD] THEN
  SRW_TAC [][swapstr_def]);

val fn_support_fresh = UNDISCH (UNDISCH (prove(
  ``support (fnpm ptpm (fnpm (cpmpm) apm)) fn A ==>
    is_perm apm ==>
    !x y M p.
       ~(x IN A) /\ ~(y IN A) ==>
       (apm [(x,y)] (fn M p) =
          fn (ptpm [(x,y)] M) (cpmpm [(x,y)] p))``,
  REPEAT STRIP_TAC THEN
  `apm [(x,y)] (fn M p) =
       fnpm (cpmpm) apm [(x,y)] (fn M)
            (cpmpm [(x,y)] p)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  MATCH_MP_TAC support_freshf THEN SRW_TAC [][])))

val perms_move = prove(
  ``^fndefn /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\ ^cond16i /\
    ^ctxt00 ==>
    !t p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)``,
  STRIP_TAC THEN Induct THEN
  SRW_TAC [][lswapstr_APPEND] THEN
  SRW_TAC [][GSYM lswapstr_APPEND] THENL [
    Q.MATCH_ABBREV_TAC `fresh apm f = fresh apm g` THEN
    `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
       by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    ASSUME_TAC fn_support_fresh THEN
    Q.ABBREV_TAC
      `bigS = s INSERT A UNION allatoms t UNION patoms p1 UNION patoms p2` THEN
    ASSUME_TAC allatoms_fresh THEN
    ASSUME_TAC lamf_support_fresh THEN
    Q.PAT_ASSUM `!p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)` (K ALL_TAC) THEN
    `support (fnpm perm_of apm) f bigS /\ support (fnpm perm_of apm) g bigS`
       by (SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, Abbr`f`, Abbr`g`,
                      Abbr`bigS`, cpmpm_APPENDlist, listpm_def, pairpm_def] THEN
           SRW_TAC [][swapstr_perm_of, swapstr_def]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `?b. ~(b IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(b IN supp (fnpm perm_of apm) f) /\ ~(b IN supp (fnpm perm_of apm) g)`
        by METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `FINITE (supp (fnpm perm_of apm) f) /\ FINITE (supp (fnpm perm_of apm) g)`
        by METIS_TAC [supp_smallest, SUBSET_FINITE, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `fcond apm f /\ fcond apm g`
        by (SRW_TAC [][fcond_def] THENL [
              `f = \c. lamf c ((\p. fn t (p ++ p2)) (p1 ++ [(c, perm_of p2 s)]))`
                 by SRW_TAC [][Abbr`f`] THEN
              POP_ASSUM SUBST1_TAC THEN
              MATCH_MP_TAC cond16_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC
                        [`A`, `A UNION allatoms t UNION patoms p2`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, cpmpm_APPENDlist,
                           is_perm_sing_inv],
                METIS_TAC []
              ],
              Q.UNABBREV_TAC `g` THEN
              MATCH_MP_TAC cond16_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def,
                           is_perm_sing_inv],
                METIS_TAC []
              ]
            ]) THEN
    `(fresh apm f = f b) /\ (fresh apm g = g b)` by METIS_TAC [fresh_def] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`] THEN
    Q_TAC SUFF_TAC `p1 ++ [(b,perm_of p2 s)] ++ p2 == p1 ++ p2 ++ [(b,s)]`
          THEN1 (STRIP_TAC THEN
                 Q_TAC SUFF_TAC
                       `fn t (p1 ++ [(b,perm_of p2 s)] ++ p2) =
                        fn t (p1 ++ p2 ++ [(b,s)])` THEN1 SRW_TAC [][] THEN
                 MP_TAC eqperms_ok THEN SRW_TAC [][]) THEN
    REWRITE_TAC [GSYM listTheory.APPEND_ASSOC] THEN
    MATCH_MP_TAC app_permeq_monotone THEN
    SRW_TAC [][permeq_refl] THEN
    `(perm_of p2 b, perm_of p2 s) :: p2 == p2 ++ [(b,s)]`
        by METIS_TAC [permeq_swap_ends, permeq_sym] THEN
    Q_TAC SUFF_TAC `perm_of p2 b = b` THEN1 METIS_TAC [] THEN
    `~(b IN patoms p2)` by FULL_SIMP_TAC (srw_ss()) [Abbr`bigS`] THEN
    SRW_TAC [][perm_of_unchanged],

    AP_THM_TAC THEN
    Q.MATCH_ABBREV_TAC `fresh (fnpm apm apm) f = fresh (fnpm apm apm) g` THEN
    `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
       by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    ASSUME_TAC fn_support_fresh THEN
    Q.ABBREV_TAC
      `bigS = s INSERT A UNION allatoms t UNION patoms p1 UNION patoms p2` THEN
    ASSUME_TAC limf_support_fresh THEN
    Q.PAT_ASSUM `!p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)` (K ALL_TAC) THEN
    Q.PAT_ASSUM `!p1 p2. fn (ptpm p2 t') p1 = fn t' (p1 ++ p2)`
                (K ALL_TAC) THEN
    `support (fnpm perm_of (fnpm apm apm)) f bigS /\
     support (fnpm perm_of (fnpm apm apm)) g bigS`
       by (SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, Abbr`f`, Abbr`g`,
                      Abbr`bigS`, cpmpm_APPENDlist, listpm_def, pairpm_def,
                      allatoms_fresh] THEN
           SRW_TAC [][swapstr_perm_of, swapstr_def, is_perm_sing_inv]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `?b. ~(b IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(b IN supp (fnpm perm_of (fnpm apm apm)) f) /\
     ~(b IN supp (fnpm perm_of (fnpm apm apm)) g)`
        by METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `FINITE (supp (fnpm perm_of (fnpm apm apm)) f) /\
     FINITE (supp (fnpm perm_of (fnpm apm apm)) g)`
        by METIS_TAC [supp_smallest, SUBSET_FINITE, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `fcond (fnpm apm apm) f /\ fcond (fnpm apm apm) g`
        by (SRW_TAC [][fcond_def] THENL [
              `f = \c. limf n c
                          ((\p. fn t (p ++ p2)) (p1 ++ [(c, perm_of p2 s)]))`
                 by SRW_TAC [][Abbr`f`] THEN
              POP_ASSUM SUBST1_TAC THEN
              MATCH_MP_TAC cond16i_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC
                        [`A UNION allatoms t UNION patoms p2`, `A`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, cpmpm_APPENDlist,
                           is_perm_sing_inv, allatoms_fresh],
                METIS_TAC []
              ],
              Q.UNABBREV_TAC `g` THEN
              MATCH_MP_TAC cond16i_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms t`, `A`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def,
                           is_perm_sing_inv, allatoms_fresh],
                METIS_TAC []
              ]
            ]) THEN
    `(fresh (fnpm apm apm) f = f b) /\ (fresh (fnpm apm apm) g = g b)`
       by METIS_TAC [fresh_def] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`] THEN
    Q_TAC SUFF_TAC `p1 ++ [(b,perm_of p2 s)] ++ p2 == p1 ++ p2 ++ [(b,s)]`
          THEN1 (STRIP_TAC THEN
                 Q_TAC SUFF_TAC
                       `fn t (p1 ++ [(b,perm_of p2 s)] ++ p2) =
                        fn t (p1 ++ p2 ++ [(b,s)])` THEN1 SRW_TAC [][] THEN
                 MP_TAC eqperms_ok THEN SRW_TAC [][]) THEN
    REWRITE_TAC [GSYM listTheory.APPEND_ASSOC] THEN
    MATCH_MP_TAC app_permeq_monotone THEN
    SRW_TAC [][permeq_refl] THEN
    `(perm_of p2 b, perm_of p2 s) :: p2 == p2 ++ [(b,s)]`
        by METIS_TAC [permeq_swap_ends, permeq_sym] THEN
    Q_TAC SUFF_TAC `perm_of p2 b = b` THEN1 METIS_TAC [] THEN
    `~(b IN patoms p2)` by FULL_SIMP_TAC (srw_ss()) [Abbr`bigS`] THEN
    SRW_TAC [][perm_of_unchanged]
  ]);

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

val fn_respectful = prove(
  ``^fndefn /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\ ^cond16i /\
    ^ctxt00 /\
    aeq t1 t2 ==> !p. fn t1 p = fn t2 p``,
  STRIP_TAC THEN
  Q.UNDISCH_THEN `aeq t1 t2` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`t2`, `t1`] THEN
  HO_MATCH_MP_TAC alt_aeq_ind THEN SRW_TAC [][] THEN
  `!t p1 p2. fn (ptpm p1 t) p2 = fn t (p2 ++ p1)`
      by (MATCH_MP_TAC perms_move THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM (ASSUME_TAC o GSYM) THEN SRW_TAC [][] THENL [
    ALL_TAC,
    AP_THM_TAC
  ] THEN
  Q.MATCH_ABBREV_TAC `fresh somepm f = fresh somepm g` THEN
  `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
     by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
         METIS_TAC [])
  THENL [
    Q.UNABBREV_TAC `somepm` THEN
    Q.ABBREV_TAC
      `bigS = {u;v} UNION A UNION patoms p UNION allatoms t1 UNION
              allatoms t2` THEN
    `support (fnpm perm_of apm) f bigS /\ support (fnpm perm_of apm) g bigS`
       by (SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, Abbr`f`, Abbr`bigS`,
                      lamf_support_fresh, fn_support_fresh, Abbr`g`] THEN
           ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
           SRW_TAC [][] THEN SRW_TAC [][swapstr_def, allatoms_fresh]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `FINITE (supp (fnpm perm_of apm) f) /\ FINITE (supp (fnpm perm_of apm) g)`
       by METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                     perm_of_is_perm] THEN
    `fcond apm f /\ fcond apm g`
       by (SRW_TAC [][fcond_def] THENL [
             Q.UNABBREV_TAC `f`,
             Q.UNABBREV_TAC `g`
           ] THEN
           FIRST_X_ASSUM (ASSUME_TAC o GSYM o assert (is_forall o concl)) THEN
           POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
           MATCH_MP_TAC cond16_implies_freshness_ok THENL [
             MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t1`],
             MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t2`]
           ] THEN SRW_TAC [][] THEN
           SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, fn_support_fresh,
                      allatoms_fresh, is_perm_sing_inv] THEN
           METIS_TAC []) THEN
    `?z. ~(z IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(z IN supp (fnpm perm_of apm) f) /\ ~(z IN supp (fnpm perm_of apm) g)`
        by METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `(fresh apm f = f z) /\ (fresh apm g = g z)` by METIS_TAC [fresh_def] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`, is_perm_flip_args, Abbr`bigS`] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    Q.ABBREV_TAC
      `bigS = {u;v} UNION A UNION patoms p UNION allatoms M1 UNION
              allatoms M2` THEN
    `support (fnpm perm_of somepm) f bigS /\
     support (fnpm perm_of somepm) g bigS`
       by (SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, Abbr`f`, Abbr`bigS`,
                      limf_support_fresh, fn_support_fresh, Abbr`g`,
                      Abbr`somepm`, is_perm_sing_inv] THEN
           ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
           SRW_TAC [][] THEN SRW_TAC [][swapstr_def, allatoms_fresh]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `FINITE (supp (fnpm perm_of somepm) f) /\
     FINITE (supp (fnpm perm_of somepm) g)`
       by METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                     perm_of_is_perm] THEN
    `is_perm somepm` by SRW_TAC [][Abbr`somepm`] THEN
    `fcond somepm f /\ fcond somepm g`
       by (SRW_TAC [][fcond_def] THENL [
             Q.UNABBREV_TAC `f`,
             Q.UNABBREV_TAC `g`
           ] THEN
           FIRST_X_ASSUM (ASSUME_TAC o GSYM o assert (is_forall o concl)) THEN
           POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
           Q.UNABBREV_TAC `somepm` THEN
           MATCH_MP_TAC cond16i_implies_freshness_ok THENL [
             MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms M1`,`A`],
             MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms M2`,`A`]
           ] THEN SRW_TAC [][] THEN
           SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, fn_support_fresh,
                      allatoms_fresh, is_perm_sing_inv] THEN
           METIS_TAC []) THEN
    `?z. ~(z IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(z IN supp (fnpm perm_of somepm) f) /\
     ~(z IN supp (fnpm perm_of somepm) g)`
        by PROVE_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `(fresh somepm f = f z) /\ (fresh somepm g = g z)`
       by METIS_TAC [fresh_def] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`, is_perm_flip_args, Abbr`bigS`] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val better_lam_clause0 = prove(
  ``^fndefn /\ ^ctxt00 /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\
    ^cond16i /\
    ~(z = v) /\ ~(z IN A) /\ ~(z IN allatoms t) ==>
    (fn (lam z (ptpm [(z,v)] t)) [] = lamf z (fn (ptpm [(z,v)] t) []))``,
  REPEAT STRIP_TAC THEN
  `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
  `aeq (lam z (ptpm [(z,v)] t)) (lam v t)` by SRW_TAC [][lam_aeq_thm] THEN
  `fn (lam z (ptpm [(z,v)] t)) [] = fn (lam v t) []`
     by (MATCH_MP_TAC fn_respectful THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THEN
  `!t p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)`
     by (MATCH_MP_TAC perms_move THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM (fn th => SIMP_TAC (srw_ss()) [th]) THEN
  Q.MATCH_ABBREV_TAC `fresh apm f = lamf z (fn t [(z,v)])` THEN
  `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
     by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
         METIS_TAC []) THEN
  Q.ABBREV_TAC `bigS = v INSERT A UNION allatoms t` THEN
  `support (fnpm perm_of apm) f bigS`
     by (SRW_TAC [][lamf_support_fresh, fn_support_fresh, support_def,
                    fnpm_def, FUN_EQ_THM, Abbr`f`, listpm_def, pairpm_def,
                    allatoms_fresh, Abbr`bigS`] THEN
         SRW_TAC [][swapstr_def]) THEN
  `FINITE bigS /\ ~(z IN bigS)` by SRW_TAC [][Abbr`bigS`] THEN
  `~(z IN supp (fnpm perm_of apm) f) /\ FINITE (supp (fnpm perm_of apm) f)`
      by METIS_TAC [supp_smallest, SUBSET_FINITE, SUBSET_DEF, fnpm_is_perm,
                    perm_of_is_perm] THEN
  Q_TAC SUFF_TAC `fcond apm f`
        THEN1 (STRIP_TAC THEN
               `fresh apm f = f z` by METIS_TAC [fresh_def] THEN
               SRW_TAC [][Abbr`f`]) THEN
  SRW_TAC [][fcond_def] THEN
  Q.UNABBREV_TAC `f` THEN
  MATCH_MP_TAC ((REWRITE_RULE [listTheory.APPEND] o
                 Q.INST [`pi` |-> `[]`]) cond16_implies_freshness_ok) THEN
  MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t`] THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, fn_support_fresh,
               allatoms_fresh, is_perm_sing_inv],
    METIS_TAC []
  ]);

val silly_new_lemma = prove(
  ``~(x = NEW (x INSERT allatoms t)) /\
    ~(NEW (x INSERT allatoms t) IN allatoms t)``,
  Q.SPEC_THEN `x INSERT allatoms t` MP_TAC NEW_def THEN
  SRW_TAC [][]);

val better_lam_clause =
    (REWRITE_RULE [silly_new_lemma] o
     Q.INST [`v` |-> `NEW (z INSERT allatoms t)`] o
     REWRITE_RULE [] o
     SIMP_RULE pure_ss [ptpm_sing_inv, allatoms_perm, perm_IN,
                        perm_of_is_perm, listTheory.REVERSE_DEF,
                        listTheory.APPEND, lswapstr_def, pairTheory.FST,
                        pairTheory.SND, swapstr_def] o
     Q.INST [`t` |-> `ptpm [(z,v)] t`]) better_lam_clause0

val better_lami_clause0 = prove(
  ``^fndefn /\ ^ctxt00 /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\
    ^cond16i /\
    ~(z = v) /\ ~(z IN A) /\ ~(z IN allatoms t) ==>
    (fn (lami n z (ptpm [(z,v)] t) t') [] =
       limf n z (fn (ptpm [(z,v)] t) []) (fn t' []))``,
  REPEAT STRIP_TAC THEN
  `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
  `aeq (lami n z (ptpm [(z,v)] t) t') (lami n v t t')`
     by SRW_TAC [][lami_aeq_thm] THEN
  `fn (lami n z (ptpm [(z,v)] t) t') [] = fn (lami n v t t') []`
     by (MATCH_MP_TAC fn_respectful THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THEN
  `!t p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)`
     by (MATCH_MP_TAC perms_move THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM (fn th => SIMP_TAC (srw_ss()) [th]) THEN
  AP_THM_TAC THEN
  Q.MATCH_ABBREV_TAC `fresh spm f = limf n z (fn t [(z,v)])` THEN
  `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
     by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
         METIS_TAC []) THEN
  Q.ABBREV_TAC `bigS = v INSERT A UNION allatoms t` THEN
  `support (fnpm perm_of spm) f bigS`
     by (SRW_TAC [][limf_support_fresh, fn_support_fresh, support_def,
                    fnpm_def, FUN_EQ_THM, Abbr`f`, listpm_def, pairpm_def,
                    allatoms_fresh, Abbr`bigS`, Abbr`spm`,
                    is_perm_sing_inv] THEN
         SRW_TAC [][swapstr_def]) THEN
  `FINITE bigS /\ ~(z IN bigS)` by SRW_TAC [][Abbr`bigS`] THEN
  `~(z IN supp (fnpm perm_of spm) f) /\ FINITE (supp (fnpm perm_of spm) f)`
      by PROVE_TAC [supp_smallest, SUBSET_FINITE, SUBSET_DEF, fnpm_is_perm,
                    perm_of_is_perm] THEN
  Q_TAC SUFF_TAC `fcond spm f`
        THEN1 (STRIP_TAC THEN
               `fresh spm f = f z` by METIS_TAC [fresh_def] THEN
               SRW_TAC [][Abbr`f`]) THEN
  SRW_TAC [][fcond_def, Abbr`spm`] THEN
  Q.UNABBREV_TAC `f` THEN
  MATCH_MP_TAC ((REWRITE_RULE [listTheory.APPEND] o
                 Q.INST [`pi` |-> `[]`]) cond16i_implies_freshness_ok) THEN
  MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms t`, `A`] THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, fn_support_fresh,
               allatoms_fresh, is_perm_sing_inv],
    METIS_TAC []
  ]);

val better_lami_clause =
    (REWRITE_RULE [silly_new_lemma] o
     Q.INST [`v` |-> `NEW (z INSERT allatoms t)`] o
     REWRITE_RULE [] o
     SIMP_RULE pure_ss [ptpm_sing_inv, allatoms_perm, perm_IN,
                        perm_of_is_perm, listTheory.REVERSE_DEF,
                        listTheory.APPEND, lswapstr_def, pairTheory.FST,
                        pairTheory.SND, swapstr_def] o
     Q.INST [`t` |-> `ptpm [(z,v)] t`]) better_lami_clause0


val recursion0 = prove(
  ``^cond16 /\ ^cond16i /\ ^ctxt00 /\ ^var_support_t /\ ^app_support_t ==>
    ?f :: respects (aeq ===> (=)).
        ((!s. f (var s) = vr s) /\
         (!t1 t2. f (app t1 t2) = ap (f t1) (f t2)) /\
         (!v t. ~(v IN A) ==> (f (lam v t) = lamf v (f t))) /\
         (!n v t1 t2. ~(v IN A) ==>
                      (f (lami n v t1 t2) = limf n v (f t1) (f t2)))) /\
        (!x y t. ~(x IN A) /\ ~(y IN A) ==>
                 (f (ptpm [(x,y)] t) = apm [(x,y)] (f t)))``,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC full THEN
  SRW_TAC [][RES_EXISTS_THM, quotientTheory.IN_RESPECTS,
             quotientTheory.FUN_REL] THEN
  Q.EXISTS_TAC `\t. fn t []` THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][] THEN MATCH_MP_TAC fn_respectful THEN
    SRW_TAC [][] THEN METIS_TAC [],
    SRW_TAC [][],
    SRW_TAC [][],
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC better_lam_clause THEN SRW_TAC [][] THEN METIS_TAC [],
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC better_lami_clause THEN SRW_TAC [][] THEN METIS_TAC [],
    `support (fnpm ptpm (fnpm cpmpm apm)) fn A`
       by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    ASSUME_TAC fn_support_fresh THEN
    SRW_TAC [][]
  ]);

fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = Prefix, fname = s, func = t};

val [FV_thm, simple_lterm_induction, ltpm_thm, LAM_distinct, LAM_11,
     LAM_eq_thm, LAMi_eq_thm, FRESH_swap0,
     (* tpm_is_perm,*) ltm_recursion, FINITE_FV,
     ltpm_sing_inv, ltpm_NIL, ltpm_flip_args, ltpm_id_front, ltpm_FV,
     ltpm_inverse] =
    quotient.define_equivalence_type
    {
     name = "lterm", equiv = aeq_equiv,
     defs = map mk_def [("LAM", ``lam``), ("APP", ``app``),
                        ("VAR", ``var``), ("FV", ``fv``), ("LAMi", ``lami``),
                        ("ltpm", ``ptpm``)],
     welldefs = [lam_respects_aeq, app_respects_aeq, var_respects_aeq,
                 lami_respects_aeq, aeq_fv,
                 SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] aeq_ptpm_lemma
                 ],
     old_thms = [fv_def, TypeBase.induction_of "l0term", ptpm_def,
                 aeq_distinct, CONJ aeq_var_11 aeq_app_11,
                 lam_aeq_thm, lami_aeq_thm, fresh_swap, (* ptpm_is_perm,*)
                 Q.INST [`lamf` |-> `lm`, `limf` |-> `li`] recursion0,
                 finite_fv,
                 ptpm_sing_inv, ptpm_NIL, ptpm_flip_args, ptpm_id_front,
                 ptpm_fv, ptpm_INVERSE]}

val _ = Save_Thm("ltpm_NIL", ltpm_NIL)

val ltpm_fresh = save_thm("ltpm_fresh", GSYM FRESH_swap0)
val _ = save_thm("simple_lterm_induction", simple_lterm_induction)

val _ = Save_Thm("lterm_distinct", LAM_distinct);
val _ = Save_Thm("lterm_11", LAM_11);
val _ = Save_Thm("ltpm_thm", ltpm_thm);
val _ = Save_Thm("FV_thm", FV_thm);
val _ = Save_Thm("FINITE_FV", FINITE_FV);
val _ = Save_Thm("ltpm_sing_inv", ltpm_sing_inv);

val _ = save_thm("LAM_eq_thm", LAM_eq_thm);
val _ = save_thm("ltm_recursion", ltm_recursion)

val _ = save_thm("ltpm_flip_args", ltpm_flip_args)
val _ = save_thm("ltpm_id_front", ltpm_id_front)
val _ = export_rewrites ["ltpm_id_front"]

val _ = save_thm("ltpm_FV", ltpm_FV)
val _ = export_rewrites ["ltpm_FV"]

val _ = save_thm("ltpm_inverse", ltpm_inverse)
val _ = export_rewrites ["ltpm_inverse"]

val ltpm_is_perm = Store_Thm(
  "ltpm_is_perm",
  ``is_perm ltpm``,
  SRW_TAC [][is_perm_def, FUN_EQ_THM, permeq_def] THEN
  Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][lswapstr_APPEND]);

val subst_lemma = prove(
  ``~(y = v) /\ ~(x = v) /\ ~(x IN FV N) /\ ~(y IN FV N) ==>
    (ltpm [(x,y)] (if swapstr x y s = v then N else VAR (swapstr x y s)) =
     (if s = v then N else VAR s))``,
  SRW_TAC [][swapstr_eq_left, FRESH_swap]);

val FV_apart = store_thm(
  "FV_apart",
  ``!t. ~(x IN FV t) /\ (y IN FV t) ==> ~(ltpm [(x,y)] t = t)``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    SRW_TAC [][LAM_eq_thm] THEN
    Cases_on `x = s` THEN SRW_TAC [][swapstr_def],
    SRW_TAC [][swapstr_def, LAM_eq_thm],
    SRW_TAC [][LAMi_eq_thm] THEN
    Cases_on `x = s` THEN SRW_TAC [][swapstr_def],
    SRW_TAC [][LAMi_eq_thm],
    SRW_TAC [][LAMi_eq_thm, swapstr_def],
    SRW_TAC [][LAMi_eq_thm, swapstr_def]
  ]);

val supp_tpm = Store_Thm(
  "supp_tpm",
  ``supp ltpm = FV``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def, FRESH_swap] THEN
  METIS_TAC [FV_apart, ltpm_flip_args]);

val silly_lemma = prove(``?x. ~(x = y) /\ ~(x IN FV M)``,
                        Q.SPEC_THEN `y INSERT FV M` MP_TAC NEW_def THEN
                        SRW_TAC [][] THEN METIS_TAC [])

val supp_partial_LAMi = prove(
  ``supp (fnpm ltpm ltpm) (LAMi n a t) = FV t DELETE a``,
  MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][FUN_EQ_THM, support_def, fnpm_def, LAMi_eq_thm] THEN
  SRW_TAC [][FRESH_swap] THENL [
    Cases_on `a = x` THEN1 SRW_TAC [][swapstr_def, FRESH_swap] THEN
    Cases_on `a = y` THEN SRW_TAC [][swapstr_def, FRESH_swap],
    SRW_TAC [boolSimps.CONJ_ss][swapstr_def],
    SRW_TAC [boolSimps.CONJ_ss][swapstr_def, ltpm_flip_args],
    METIS_TAC [FV_apart, ltpm_flip_args],
    Cases_on `a = b` THEN SRW_TAC [][swapstr_def]
  ]);



val subst_exists =
    (SIMP_RULE (srw_ss()) [SKOLEM_THM, FORALL_AND_THM] o
     Q.GEN `N` o Q.GEN `x` o
     SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def, subst_lemma,
                           silly_lemma, supp_partial_LAMi] o
     Q.INST [`A` |-> `x INSERT FV N`, `apm` |-> `ltpm`,
             `vr` |-> `\s. if s = x then N else VAR s`,
             `ap` |-> `APP`,
             `lm` |-> `LAM`, `li` |-> `LAMi`] o
     SPEC_ALL o
     INST_TYPE [alpha |-> ``:lterm``]) ltm_recursion

val SUB_DEF = new_specification("lSUB_DEF", ["SUB"], subst_exists)

val lterm_bvc_induction = store_thm(
  "lterm_bvc_induction",
  ``!P X. FINITE X /\
          (!s. P (VAR s)) /\
          (!M N. P M /\ P N ==> P (APP M N)) /\
          (!v M. ~(v IN X) /\ P M ==> P (LAM v M)) /\
          (!n v M N. ~(v IN X) /\ ~(v IN FV N) /\ P M /\ P N ==>
                     P (LAMi n v M N)) ==>
          !t. P t``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t pi. P (ltpm pi t)` THEN1 METIS_TAC [ltpm_NIL] THEN
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][] THENL [
    `?z. ~(z = perm_of pi s) /\ ~(z IN FV (ltpm pi t)) /\ ~(z IN X)`
       by (Q.SPEC_THEN `perm_of pi s INSERT FV (ltpm pi t) UNION X`
                       MP_TAC NEW_def THEN
           SRW_TAC [][] THEN METIS_TAC []) THEN
    Q_TAC SUFF_TAC `LAM (perm_of pi s) (ltpm pi t) =
                    LAM z (ltpm ((z,perm_of pi s)::pi) t)`
          THEN1 SRW_TAC [][] THEN
    SRW_TAC [][LAM_eq_thm, perm_IN, lswapstr_APPEND, swapstr_def,
               ltpm_flip_args]
    THENL [
      FULL_SIMP_TAC (srw_ss()) [perm_IN],
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      SRW_TAC [][is_perm_eql, is_perm_decompose, is_perm_inverse]
    ],
    `?z. ~(z = perm_of pi s) /\ ~(z IN FV (ltpm pi t)) /\ ~(z IN X) /\
         ~(z IN FV (ltpm pi t'))`
       by (Q.SPEC_THEN `perm_of pi s INSERT FV (ltpm pi t) UNION X UNION
                        FV (ltpm pi t')`
                       MP_TAC NEW_def THEN
           SRW_TAC [][] THEN METIS_TAC []) THEN
    Q_TAC SUFF_TAC `LAMi n (perm_of pi s) (ltpm pi t) (ltpm pi t') =
                    LAMi n z (ltpm ((z,perm_of pi s)::pi) t) (ltpm pi t')`
          THEN1 SRW_TAC [][] THEN
    SRW_TAC [][LAMi_eq_thm, perm_IN, lswapstr_APPEND, swapstr_def] THENL [
      FULL_SIMP_TAC (srw_ss()) [perm_IN],
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      SRW_TAC [][is_perm_eql, is_perm_decompose, is_perm_inverse,
                 ltpm_flip_args]
    ]
  ]);

val swap_subst = store_thm(
  "swap_subst",
  ``!t. ~(u IN FV t) ==> ([VAR u/v] t = ltpm [(u,v)] t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_DEF] THEN SRW_TAC [][swapstr_def]);

val l14a = store_thm(
  "l14a",
  ``!t. [VAR v/v] t = t``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][SUB_DEF]);

val l14b = store_thm(
  "l14b",
  ``!t. ~(v IN FV t) ==> ([u/v]t = t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SRW_TAC [][SUB_DEF]);

val l15a = store_thm(
  "l15a",
  ``!t. ~(v IN FV t) ==> ([u/v] ([VAR v/x] t) = [u/x] t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{x;v} UNION FV u` THEN
  SRW_TAC [][SUB_DEF]);

(* establish that the nc type has appropriate nominal logic properties *)
open swapTheory
val lswap_is_perm = Store_Thm(
  "lswap_is_perm",
  ``is_perm lswap``,
  SRW_TAC [][is_perm_def, permeq_def, FUN_EQ_THM] THEN
  Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC ncTheory.simple_induction THEN
  SRW_TAC [][lswapstr_APPEND]);

val FV_lswap = Store_Thm(
  "FV_lswap",
  ``!t. x IN FV (lswap pi t) = lswapstr (REVERSE pi) x IN FV t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][lswapstr_eql]);

val lswap_subst = store_thm(
  "lswap_subst",
  ``!t. lswap pi ([N/v] t) = [lswap pi N/lswapstr pi v] (lswap pi t)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `v INSERT FV N` THEN SRW_TAC [][SUB_THM, SUB_VAR]);

val lswap_fresh = store_thm(
  "lswap_fresh",
  ``!t. ~(x IN FV t) /\ ~(y IN FV t) ==> (lswap [(x,y)] t = t)``,
  SRW_TAC [][lswap_def, swap_identity]);

val lswap_apart = store_thm(
  "lswap_apart",
  ``!t. x IN FV t /\ ~(y IN FV t) ==> ~(lswap [(x,y)] t = t)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    SRW_TAC [][LAM_INJ_swap] THEN
    Cases_on `y = v` THEN SRW_TAC [][],
    SRW_TAC [][LAM_INJ_swap]
  ]);

val supp_lswap = Store_Thm(
  "supp_lswap",
  ``supp lswap t = FV t``,
  MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][lswap_fresh, lswap_apart, support_def]);



val supp_subst_partial = store_thm(
  "supp_subst_partial",
  ``supp (fnpm lswap lswap) (\t2. [t2/v] t) = FV t DELETE v``,
  MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][support_def, FUN_EQ_THM] THEN
  REWRITE_TAC [fnpm_def] THEN
  SRW_TAC [][lswap_subst, is_perm_sing_inv, lswap_fresh] THENL [
    Cases_on `x = v` THEN SRW_TAC [][lemma14b] THEN
    Cases_on `y = v` THEN SRW_TAC [][lemma14b],
    `lswap [(x,v)] t = [VAR x/v] t`
       by SRW_TAC [][lswap_def, fresh_var_swap] THEN
    SRW_TAC [][lemma15a],
    `lswap [(v,y)] t = [VAR y/v] t`
       by (SRW_TAC [][lswap_def] THEN
           METIS_TAC [swap_comm, fresh_var_swap]) THEN
    SRW_TAC [][lemma15a],
    SRW_TAC [][lswap_def],
    Cases_on `b = v` THEN SRW_TAC [][] THENL [
      SRW_TAC [][lemma14b] THEN SRW_TAC [][lswap_apart],
      Q.EXISTS_TAC `VAR v` THEN SRW_TAC [][lemma14a, lswap_apart]
    ],
    Cases_on `b IN FV t` THENL [
      Q.EXISTS_TAC `VAR a` THEN SRW_TAC [][lemma14a] THEN
      STRIP_TAC THEN
      `b IN FV (lswap [(a,b)] t) = b IN FV ([VAR a/b] t)`
         by METIS_TAC [] THEN
      POP_ASSUM MP_TAC THEN SRW_TAC [][FV_SUB],
      SRW_TAC [][lemma14b, lswap_apart]
    ]
  ]);

val phi_exists =
    (SIMP_RULE (srw_ss()) [is_perm_sing_inv, lswap_subst,
                           supp_subst_partial] o
     REWRITE_RULE [fnpm_def] o
     SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] o
     Q.INST [`apm` |-> `lswap`,
             `A` |-> `{}`,
             `vr` |-> `VAR`,
             `ap` |-> `(@@)`,
             `lm` |-> `LAM`,
             `li` |-> `\n v t1 t2. [t2/v]t1`] o SPEC_ALL o
     INST_TYPE [alpha |-> ``:'a nc``])
    ltm_recursion

val phi_thm = new_specification("phi_thm", ["phi"], phi_exists)


val supp_lamax_app = prove(
  ``supp (fnpm lswap lswap) (\t2. (LAM v t1) @@ t2) = FV t1 DELETE v``,
  MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][support_def, FUN_EQ_THM] THEN
  REWRITE_TAC [fnpm_def] THEN
  SRW_TAC [][is_perm_sing_inv, lswap_fresh] THEN
  SRW_TAC [][LAM_INJ_swap] THEN
  Cases_on `b = v` THEN SRW_TAC [][] THEN
  SRW_TAC [][lswap_apart]);

val strip_label_exists =
    (SIMP_RULE (srw_ss()) [is_perm_sing_inv, supp_lamax_app] o
     REWRITE_RULE [fnpm_def] o
     SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] o
     Q.INST [`apm` |-> `lswap`,
             `A` |-> `{}`,
             `vr` |-> `VAR`,
             `ap` |-> `(@@)`,
             `lm` |-> `LAM`,
             `li` |-> `\n v t1 t2. (LAM v t1) @@ t2`] o SPEC_ALL o
     INST_TYPE [alpha |-> ``:'a nc``])
    ltm_recursion

val strip_label_thm = new_specification("strip_label_thm", ["strip_label"],
                                        strip_label_exists)

val _ = export_theory()



