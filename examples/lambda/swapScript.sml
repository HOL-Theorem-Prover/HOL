open HolKernel Parse boolLib

open simpLib boolSimps bossLib BasicProvers metisLib

val _ = new_theory "swap"

open ncTheory ncLib pred_setTheory chap2Theory

(* ----------------------------------------------------------------------
    Basic swapping on strings
   ---------------------------------------------------------------------- *)

val swapstr_def = Define`
  swapstr x y (s:string) = if s = x then y else if s = y then x else s
`;

val swapstr_inverse = store_thm(
  "swapstr_inverse",
  ``(swapstr x y (swapstr x y s) = s) /\
    (swapstr x y (swapstr y x s) = s)``,
  SRW_TAC [][swapstr_def] THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SRW_TAC [][] THEN PROVE_TAC []);
val _ = export_rewrites ["swapstr_inverse"]

val swapstr_comm = store_thm(
  "swapstr_comm",
  ``swapstr x y s = swapstr y x s``,
  SRW_TAC [][swapstr_def]);

val swapstr_11 = store_thm(
  "swapstr_11",
  ``((swapstr x y s1 = swapstr x y s2) = (s1 = s2)) /\
    ((swapstr x y s1 = swapstr y x s2) = (s1 = s2))``,
  SRW_TAC [][swapstr_def] THEN PROVE_TAC []);
val _ = export_rewrites ["swapstr_11"]

val swapstr_id = store_thm(
  "swapstr_id",
  ``swapstr x x s = s``,
  SRW_TAC [][swapstr_def]);
val _ = export_rewrites ["swapstr_id"]

fun simp_cond_tac (asl, g) = let
  val eqn = find_term (fn t => is_eq t andalso is_var (lhs t) andalso
                               is_var (rhs t)) g
in
  ASM_CASES_TAC eqn THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
  ASM_SIMP_TAC bool_ss []
end (asl, g)
val swapstr_swapstr = store_thm(
  "swapstr_swapstr",
  ``swapstr x y (swapstr u v s) =
    swapstr (swapstr x y u) (swapstr x y v) (swapstr x y s)``,
  REWRITE_TAC [swapstr_def] THEN
  REPEAT simp_cond_tac);



(* ----------------------------------------------------------------------
    Swapping over sets of strings
   ---------------------------------------------------------------------- *)

val swapset_def = Define`
  swapset x y ss = IMAGE (swapstr x y) ss
`;

val swapset_inverse = store_thm(
  "swapset_inverse",
  ``(swapset x y (swapset x y s) = s) /\
    (swapset x y (swapset y x s) = s)``,
  SRW_TAC [][swapset_def, EXTENSION, GSYM RIGHT_EXISTS_AND_THM]);
val _ = export_rewrites ["swapset_inverse"]

val swapset_comm = store_thm(
  "swapset_comm",
  ``swapset x y s = swapset y x s``,
  METIS_TAC [swapset_def, swapstr_comm]);

val swapset_11 = store_thm(
  "swapset_11",
  ``((swapset x y s1 = swapset x y s2) = (s1 = s2)) /\
    ((swapset x y s1 = swapset y x s2) = (s1 = s2))``,
  SRW_TAC [][swapset_def, EXTENSION] THEN
  METIS_TAC [swapstr_11]);
val _ = export_rewrites ["swapset_11"]

val swapset_id = store_thm(
  "swapset_id",
  ``swapset x x s = s``,
  SRW_TAC [][swapset_def, EXTENSION]);
val _ = export_rewrites ["swapset_id"]

val swapset_UNION = store_thm(
  "swapset_UNION",
  ``swapset x y (P UNION Q) = swapset x y P UNION swapset x y Q``,
  SRW_TAC [][swapset_def]);


val swapset_EMPTY = store_thm(
  "swapset_EMPTY",
  ``swapset u v {} = {}``,
  SRW_TAC [][swapset_def]);
val _ = export_rewrites ["swapset_EMPTY"]

val swapset_INSERT = store_thm(
  "swapset_INSERT",
  ``swapset u v (x INSERT s) = swapstr u v x INSERT swapset u v s``,
  SRW_TAC [][swapset_def]);
val _ = export_rewrites ["swapset_INSERT"]


(* ----------------------------------------------------------------------
    Swapping over terms
   ---------------------------------------------------------------------- *)


val con_case_t = ``\c:'a. CON c``
val var_case_t = ``\s:string. VAR (swapstr x y s)``
val app_case_t = ``\(old1 : 'a nc) (old2 : 'a nc) t1:'a nc t2 . t1 @@ t2``
val abs_case_t = ``\(tf: string -> 'a nc) (rf : string -> 'a nc).
                      let nv = NEW ({x;y} UNION FV (ABS tf))
                      in LAM nv (rf nv)``

val thm0 =
  GENL [``x:string``, ``y:string``]
       (BETA_RULE
          (ISPECL [con_case_t, var_case_t, app_case_t, abs_case_t]
                  nc_RECURSION_WEAK))

val thm1 = SIMP_RULE bool_ss [SKOLEM_THM, FORALL_AND_THM, ABS_DEF] thm0

val swap_def = new_specification("swap_def", ["swap"], thm1);

val swap_id = store_thm(
  "swap_id",
  ``!t. swap x x t = t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][swap_def] THEN
  MATCH_MP_TAC (GSYM ALPHA) THEN NEW_ELIM_TAC);

val swap_comm = store_thm(
  "swap_comm",
  ``!t. swap x y t = swap y x t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][swap_def] THEN
  POP_ASSUM (Q.SPEC_THEN `NEW ({x;y} UNION (FV t DELETE x'))` SUBST1_TAC) THEN
  Q_TAC SUFF_TAC `{x;y} = {y;x}` THEN1 PROVE_TAC [] THEN
  SRW_TAC [][pred_setTheory.EXTENSION] THEN PROVE_TAC []);

val fresh_var_swap = store_thm(
  "fresh_var_swap",
  ``!t v u. ~(v IN FV t) ==> ([VAR v/u] t = swap v u t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][SUB_THM, swap_def],
    SRW_TAC [][SUB_VAR, swap_def, swapstr_def],
    SRW_TAC [][SUB_THM, swap_def],
    REPEAT STRIP_TAC THEN SRW_TAC [][swap_def] THEN
    NEW_ELIM_TAC THEN Q.X_GEN_TAC `w` THEN STRIP_TAC THENL [
      (* w different from the bound variable of the lambda abstraction *)
      `~(w IN FV (LAM x t))` by SRW_TAC [][] THEN
      `LAM x t = LAM w ([VAR w/x] t)` by SRW_TAC [][ALPHA] THEN
      SRW_TAC [][SUB_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SRW_TAC [][FV_SUB] THEN FULL_SIMP_TAC (srw_ss()) [],
      (* w equal to bound variable of lambda abstraction *)
      SRW_TAC [][SUB_THM, lemma14a] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `w` MP_TAC) THEN SRW_TAC [][lemma14a] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC (srw_ss()) []
    ]
  ]);


val FV_swap = store_thm(
  "FV_swap",
  ``!t u v. FV (swap u v t) = swapset u v (FV t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][swap_def, swapset_def],
    SRW_TAC [][swap_def, swapset_def],
    SRW_TAC [][swap_def, swapset_def],
    REPEAT STRIP_TAC THEN SRW_TAC [][swap_def] THEN
    NEW_ELIM_TAC THEN Q.X_GEN_TAC `w` THEN SRW_TAC [][] THENL [
      SRW_TAC [][FV_SUB] THENL [
        `~(w = x)` by PROVE_TAC [] THEN
        SRW_TAC [][swapset_UNION] THEN
        `swapstr u v w = w` by SRW_TAC [][swapstr_def] THEN
        SRW_TAC [][dBTheory.UNION_DELETE, pred_setTheory.SING_DELETE] THEN
        SRW_TAC [][GSYM pred_setTheory.DELETE_NON_ELEMENT] THEN
        SIMP_TAC (srw_ss())[swapset_def] THEN
        Q.X_GEN_TAC `y` THEN
        Cases_on `y IN FV t` THEN SRW_TAC [][] THEN
        Cases_on `w = swapstr u v y` THEN SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [],
        `FV t DELETE x = FV t`
           by SRW_TAC [][GSYM pred_setTheory.DELETE_NON_ELEMENT] THEN
        SRW_TAC [][GSYM pred_setTheory.DELETE_NON_ELEMENT] THEN
        SIMP_TAC (srw_ss()) [swapset_def] THEN Q.X_GEN_TAC `y` THEN
        Cases_on `w = swapstr u v y` THEN SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [swapstr_def] THEN
        RES_TAC
      ],
      SRW_TAC [][lemma14a] THEN
      SRW_TAC [][swapset_def, EXTENSION, EQ_IMP_THM] THENL [
        Q.EXISTS_TAC `x'` THEN  SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [swapstr_def],
        PROVE_TAC [],
        ASM_SIMP_TAC (srw_ss() ++ COND_elim_ss) [swapstr_def]
      ]
    ]
  ]);
val _ = export_rewrites ["FV_swap"]

val size_swap = store_thm(
  "size_swap",
  ``!t x y. size (swap x y t) = size t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][swap_def, size_thm]);
val _ = export_rewrites ["size_swap"]

val pvh_induction = store_thm(
  "pvh_induction",
  ``!P. (!s. P (VAR s)) /\ (!k. P (CON k)) /\
        (!t u. P t /\ P u ==> P (t @@ u)) /\
        (!v t. (!t'. (size t' = size t) ==> P t') ==> P (LAM v t)) ==>
        (!t. P t)``,
  GEN_TAC THEN STRIP_TAC THEN
  completeInduct_on `size t` THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [numSimps.ARITH_ss][size_thm]);

val swap_vsubst = store_thm(
  "swap_vsubst",
  ``!t u v x y. swap u v ([VAR x/y] t) =
                [VAR (swapstr u v x)/swapstr u v y] (swap u v t)``,
  HO_MATCH_MP_TAC pvh_induction THEN REPEAT STRIP_TAC THENL [
    SRW_TAC [][SUB_VAR, swap_def],
    SRW_TAC [][SUB_THM, swap_def],
    SRW_TAC [][SUB_THM, swap_def],
    Q_TAC (NEW_TAC "z") `{u; v; v'; x; y} UNION FV t` THEN
    `LAM v t = LAM z ([VAR z/v] t)` by SRW_TAC [][ALPHA] THEN
    Q.ABBREV_TAC `M = [VAR z/v] t` THEN
    `size M = size t` by SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss()) [SUB_THM] THEN
    `swap u v' (LAM z ([VAR x/y] M)) =
       LAM z ([VAR (swapstr u v' x)/swapstr u v' y] (swap u v' M))`
      by (CONV_TAC (LAND_CONV (REWRITE_CONV [swap_def])) THEN
          NEW_ELIM_TAC THEN Q.X_GEN_TAC `a` THEN
          STRIP_TAC THENL [
            `(swapstr u v' a = a) /\ (swapstr u v' z = z)`
                by SRW_TAC [][swapstr_def] THEN
            ASM_SIMP_TAC (srw_ss()) [] THEN
            Q.ABBREV_TAC `uv'x = swapstr u v' x` THEN
            Q.ABBREV_TAC `uv'y = swapstr u v' y` THEN
            `~(a IN FV ([VAR uv'x/uv'y] (swap u v' M)))`
               by (`[VAR uv'x/uv'y] (swap u v' M) = swap u v' ([VAR x/y] M)`
                       by SRW_TAC [][] THEN
                   POP_ASSUM SUBST_ALL_TAC THEN
                   SIMP_TAC (srw_ss()) [] THEN
                   ASM_SIMP_TAC (srw_ss()) [swapset_def] THEN
                   Q_TAC SUFF_TAC `!x. (a = swapstr u v' x) ==> (x = a)` THEN1
                         PROVE_TAC [] THEN
                   SRW_TAC [][swapstr_def]) THEN
            ASM_SIMP_TAC (srw_ss()) [GSYM SIMPLE_ALPHA],
            ASM_SIMP_TAC (srw_ss()) [lemma14a]
          ]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [swap_def] THEN NEW_ELIM_TAC THEN
    Q.X_GEN_TAC `a` THEN STRIP_TAC THENL [
      `(swapstr u v' a = a) /\ (swapstr u v' z = z)`
          by SRW_TAC [][swapstr_def] THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      `~(a IN FV (swap u v' M))`
          by (SIMP_TAC (srw_ss()) [swapset_def] THEN
              `!x. (a = swapstr u v' x) ==> (x = a)`
                 by SRW_TAC [][swapstr_def] THEN
              PROVE_TAC []) THEN
      ASM_SIMP_TAC (srw_ss())[GSYM SIMPLE_ALPHA] THEN
      MATCH_MP_TAC (GSYM (last (CONJUNCTS SUB_THM))) THEN
      SRW_TAC [][swapstr_def],
      ASM_SIMP_TAC (srw_ss()) [lemma14a] THEN
      MATCH_MP_TAC (GSYM (last (CONJUNCTS SUB_THM))) THEN
      SRW_TAC [][swapstr_def]
    ]
  ]);

val swap_LAM = prove(
  ``swap x y (LAM v t) = LAM (swapstr x y v) (swap x y t)``,
  SRW_TAC [][swap_def] THEN NEW_ELIM_TAC THEN Q.X_GEN_TAC `a` THEN
  STRIP_TAC THENL [
    SRW_TAC [][swap_vsubst] THEN
    `swapstr x y a = a` by SRW_TAC [][swapstr_def] THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC (GSYM SIMPLE_ALPHA) THEN
    SRW_TAC [][swapset_def] THEN
    Q_TAC SUFF_TAC `!z. (swapstr x y z = a) ==> (z = a)`
      THEN1 METIS_TAC [] THEN
    SRW_TAC [][swapstr_def],
    SRW_TAC [][lemma14a, swapstr_def]
  ]);

val swap_thm = store_thm(
  "swap_thm",
  ``(swap x y (VAR s) = VAR (swapstr x y s)) /\
    (swap x y (CON k) = CON k) /\
    (swap x y (t @@ u) = swap x y t @@ swap x y u) /\
    (swap x y (LAM v t) = LAM (swapstr x y v) (swap x y t))``,
  SRW_TAC [][swap_LAM] THEN SRW_TAC [][swap_def]);

val swap_swap = store_thm(
  "swap_swap",
  ``!t u v x y. swap x y (swap u v t) =
                swap (swapstr x y u) (swapstr x y v) (swap x y t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][swap_thm],
    SRW_TAC [][swap_thm, SYM swapstr_swapstr],
    REPEAT STRIP_TAC THEN SIMP_TAC (srw_ss()) [swap_thm] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    SRW_TAC [][swap_thm, SYM swapstr_swapstr] THEN
    METIS_TAC [lemma14a]
  ]);

val swap_inverse_lemma = prove(
  ``!t. swap x y (swap x y t) = t``,
  HO_MATCH_MP_TAC pvh_induction THEN SRW_TAC [][swap_thm]);

val swap_inverse = store_thm(
  "swap_inverse",
  ``(swap x y (swap x y t) = t) /\ (swap y x (swap x y t) = t)``,
  METIS_TAC [swap_inverse_lemma, swap_comm]);
val _ = export_rewrites ["swap_inverse"]

val _ = export_theory();
