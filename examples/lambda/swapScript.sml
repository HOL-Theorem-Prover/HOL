open HolKernel Parse boolLib

open simpLib boolSimps bossLib BasicProvers metisLib

val _ = new_theory "swap"

open ncTheory NEWLib pred_setTheory

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
  ``swapstr (swapstr x y u) (swapstr x y v) (swapstr x y s) =
    swapstr x y (swapstr u v s)``,
  REWRITE_TAC [swapstr_def] THEN
  REPEAT simp_cond_tac);
val _ = export_rewrites ["swapstr_swapstr"]

val swapstr_swapstr2 = store_thm(
  "swapstr_swapstr2",
  ``swapstr x y (swapstr (swapstr x y a) (swapstr x y b) s) =
    swapstr a b (swapstr x y s)``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM swapstr_swapstr])) THEN
  REWRITE_TAC [swapstr_inverse]);
val _ = export_rewrites ["swapstr_swapstr2"]

val swapstr_eq_normalise = store_thm(
  "swapstr_eq_normalise",
  ``(s = swapstr x y t) = (swapstr x y s = t)``,
  SRW_TAC [][swapstr_def] THEN PROVE_TAC []);
val _ = export_rewrites ["swapstr_eq_normalise"]

val swapstr_identity = store_thm(
  "swapstr_identity",
  ``~(x = s) /\ ~(y = s) ==>
    (swapstr x y s = s) /\ ((swapstr x y t = s) = (t = s))``,
  SRW_TAC [][swapstr_def]);
val _ = export_rewrites ["swapstr_identity"]

val swapstr_rewrites = store_thm(
  "swapstr_rewrites",
  ``(swapstr x y y = x) /\ (swapstr x y x = y)``,
  SRW_TAC [][swapstr_def]);
val _ = export_rewrites ["swapstr_rewrites"]




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

val swapset_FINITE = store_thm(
  "swapset_FINITE",
  ``FINITE (swapset x y s) = FINITE s``,
  SRW_TAC [][swapset_def, EQ_IMP_THM]);
val _ = export_rewrites ["swapset_FINITE"]

val IN_swapset_lemma = prove(
  ``x IN swapset y z s = if x = y then z IN s
                         else if x = z then y IN s
                         else x IN s``,
  SRW_TAC [][swapset_def, swapstr_def] THEN METIS_TAC []);

val swapstr_IN_swapset0 = prove(
  ``swapstr x y s IN swapset x y set = s IN set``,
  SIMP_TAC (srw_ss()) [IN_swapset_lemma, swapstr_def] THEN
  MAP_EVERY Cases_on [`s = x`, `s = y`] THEN SRW_TAC [][]);

val IN_swapset = store_thm(
  "IN_swapset",
  ``s IN swapset x y t = swapstr x y s IN t``,
  METIS_TAC [swapstr_inverse, swapstr_IN_swapset0]);
val _ = export_rewrites ["IN_swapset"]

val swapset_11 = store_thm(
  "swapset_11",
  ``((swapset x y s1 = swapset x y s2) = (s1 = s2)) /\
    ((swapset x y s1 = swapset y x s2) = (s1 = s2))``,
  SRW_TAC [][EXTENSION] THEN
  METIS_TAC [swapstr_inverse]);
val _ = export_rewrites ["swapset_11"]

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
val _ = export_rewrites ["swap_id"]

val swap_comm = store_thm(
  "swap_comm",
  ``!t. swap x y t = swap y x t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][swap_def] THEN
  POP_ASSUM (Q.SPEC_THEN `NEW ({x;y} UNION (FV t DELETE x'))` SUBST1_TAC) THEN
  Q_TAC SUFF_TAC `{x;y} = {y;x}` THEN1 PROVE_TAC [] THEN
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

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
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THEN
  SRW_TAC [][swap_def, swapset_UNION] THEN
  NEW_ELIM_TAC THEN Q.X_GEN_TAC `w` THEN SRW_TAC [][] THENL [
    SRW_TAC [][FV_SUB] THENL [
      `~(w = x)` by PROVE_TAC [] THEN
      SRW_TAC [][swapset_UNION] THEN
      `swapstr u v w = w` by SRW_TAC [][] THEN
      SRW_TAC [][dBTheory.UNION_DELETE] THEN
      SRW_TAC [][GSYM DELETE_NON_ELEMENT],
      `FV t DELETE x = FV t`
         by SRW_TAC [][GSYM DELETE_NON_ELEMENT] THEN
      SRW_TAC [][GSYM DELETE_NON_ELEMENT]
    ],
    SRW_TAC [][lemma14a, EXTENSION, EQ_IMP_THM]
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
            ASM_SIMP_TAC (srw_ss()) [] THEN
            Q.ABBREV_TAC `uv'x = swapstr u v' x` THEN
            Q.ABBREV_TAC `uv'y = swapstr u v' y` THEN
            `~(a IN FV ([VAR uv'x/uv'y] (swap u v' M)))`
               by (`[VAR uv'x/uv'y] (swap u v' M) = swap u v' ([VAR x/y] M)`
                       by SRW_TAC [][] THEN
                   POP_ASSUM SUBST_ALL_TAC THEN
                   ASM_SIMP_TAC (srw_ss()) []) THEN
            ASM_SIMP_TAC (srw_ss()) [GSYM SIMPLE_ALPHA],
            ASM_SIMP_TAC (srw_ss()) [lemma14a]
          ]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [swap_def] THEN NEW_ELIM_TAC THEN
    Q.X_GEN_TAC `a` THEN STRIP_TAC THENL [
      `~(a IN FV (swap u v' M))` by ASM_SIMP_TAC (srw_ss()) [] THEN
      ASM_SIMP_TAC (srw_ss())[GSYM SIMPLE_ALPHA] THEN
      MATCH_MP_TAC (GSYM (last (CONJUNCTS SUB_THM))) THEN
      SRW_TAC [][],
      ASM_SIMP_TAC (srw_ss()) [lemma14a] THEN
      MATCH_MP_TAC (GSYM (last (CONJUNCTS SUB_THM))) THEN
      SRW_TAC [][]
    ]
  ]);

val swap_LAM = prove(
  ``swap x y (LAM v t) = LAM (swapstr x y v) (swap x y t)``,
  SRW_TAC [][swap_def] THEN NEW_ELIM_TAC THEN Q.X_GEN_TAC `a` THEN
  STRIP_TAC THENL [
    SRW_TAC [][swap_vsubst] THEN
    MATCH_MP_TAC (GSYM SIMPLE_ALPHA) THEN
    SRW_TAC [][],
    SRW_TAC [][lemma14a]
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
  ``!t u v x y. swap (swapstr x y u) (swapstr x y v) (swap x y t) =
                swap x y (swap u v t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][swap_thm],
    SRW_TAC [][swap_thm],
    REPEAT STRIP_TAC THEN SIMP_TAC (srw_ss()) [swap_thm] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    SRW_TAC [][swap_thm] THEN
    METIS_TAC [lemma14a]
  ]);
val _ = export_rewrites ["swap_swap"]

val swap_swap2 = store_thm(
  "swap_swap2",
  ``swap x y (swap (swapstr x y a) (swapstr x y b) t) =
    swap a b (swap x y t)``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM swap_swap])) THEN
  REWRITE_TAC [swapstr_inverse]);
val _ = export_rewrites ["swap_swap2"]

val swap_inverse_lemma = prove(
  ``!t. swap x y (swap x y t) = t``,
  HO_MATCH_MP_TAC pvh_induction THEN SRW_TAC [][swap_thm]);

val swap_inverse = store_thm(
  "swap_inverse",
  ``(swap x y (swap x y t) = t) /\ (swap y x (swap x y t) = t)``,
  METIS_TAC [swap_inverse_lemma, swap_comm]);
val _ = export_rewrites ["swap_inverse"]

val swap_ALPHA = store_thm(
  "swap_ALPHA",
  ``~(v IN FV M) ==> (LAM v (swap v u M) = LAM u M)``,
  SRW_TAC [][GSYM fresh_var_swap, GSYM SIMPLE_ALPHA]);

val swap_subst = store_thm(
  "swap_subst",
  ``!M N v x y.
      swap x y ([N/v] M) = [swap x y N / swapstr x y v] (swap x y M)``,
  HO_MATCH_MP_TAC pvh_induction THEN REPEAT STRIP_TAC THENL [
    SRW_TAC [][SUB_VAR, swap_thm],
    SRW_TAC [][SUB_THM, swap_thm],
    SRW_TAC [][SUB_THM, swap_thm],
    Q_TAC (NEW_TAC "z") `{v; v'; x; y} UNION FV M UNION FV N` THEN
    `LAM v M = LAM z ([VAR z/v] M)` by SRW_TAC [][ALPHA] THEN
    Q.ABBREV_TAC `M' = [VAR z/v] M` THEN
    `size M' = size M` by SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss()) [SUB_THM] THEN
    ASM_SIMP_TAC (srw_ss()) [swap_thm] THEN
    `~(z IN FV (swap x y N))` by SRW_TAC [][] THEN
    `~(swapstr x y v = z)` by SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss()) [SUB_THM]
  ]);

val swap_subst_out = store_thm(
  "swap_subst_out",
  ``[N/v] (swap x y M) = swap x y ([swap x y N/swapstr x y v] M)``,
  METIS_TAC [swap_subst, swap_inverse]);

val swap_11 = store_thm(
  "swap_11",
  ``((swap x y t1 = swap x y t2) = (t1 = t2)) /\
    ((swap x y t1 = swap y x t2) = (t1 = t2))``,
  Q_TAC SUFF_TAC `!t1 t2. (swap x y t1 = swap x y t2) = (t1 = t2)` THEN1
        METIS_TAC [swap_comm] THEN
  HO_MATCH_MP_TAC pvh_induction THEN REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `t2` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][swap_thm] THEN EQ_TAC THENL [
    Cases_on `v = x'` THENL [
      SRW_TAC [][],
      `~(swapstr x y v = swapstr x y x')` by SRW_TAC [][] THEN STRIP_TAC THEN
      `~(v IN FV u) /\ ~(x' IN FV t1)`
          by (IMP_RES_TAC LAM_INJ_ALPHA_FV THEN
              FULL_SIMP_TAC (srw_ss()) []) THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP INJECTIVITY_LEMMA1) THEN
      SRW_TAC [][swap_subst_out, swap_thm, FV_swap, SIMPLE_ALPHA]
    ],
    Cases_on `v = x'` THENL [
      SRW_TAC [][],
      STRIP_TAC THEN
      `~(v IN FV u) /\ ~(x' IN FV t1)` by METIS_TAC [LAM_INJ_ALPHA_FV] THEN
      `t1 = [VAR v/x'] u` by PROVE_TAC [INJECTIVITY_LEMMA1] THEN
      ` _ = swap v x' u` by PROVE_TAC [fresh_var_swap] THEN
      `swap x y t1 = swap (swapstr x y v) (swapstr x y x') (swap x y u)`
           by SRW_TAC [][] THEN
      POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][swap_ALPHA]
    ]
  ]);
val _ = export_rewrites ["swap_11"]

(* ----------------------------------------------------------------------
    supporting recursion over lambda calculus terms using swap
   ---------------------------------------------------------------------- *)

val fresh_new_subst0 = prove(
  ``FINITE X ==>
    ((let v = NEW (FV (LAM x u) UNION X) in f v ([VAR v/x] u)) =
     (let v = NEW (FV (LAM x u) UNION X) in f v (swap v x u)))``,
  STRIP_TAC THEN NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][fresh_var_swap, lemma14a]);

val fresh_new_subst =
    (SIMP_RULE bool_ss [FINITE_EMPTY,
                        UNION_EMPTY] o
     Q.INST [`f` |-> `\v t. lam (hom t : 'b) v t  : 'b`,
             `X` |-> `EMPTY`] o
     INST_TYPE [alpha |-> beta, beta |-> alpha]) fresh_new_subst0


val lemma =
    (SIMP_RULE bool_ss [ASSUME ``FINITE (X:string set)``,
                        ABS_DEF, fresh_new_subst0] o
     Q.INST [`lam` |->
              `\r t. let v = NEW (FV (ABS t) UNION X) in lam (r v) v (t v) `] o
     SPEC_ALL) nc_RECURSION

val LET_RAND' = prove(
  ``(let x = M in P (N x)) = P (let x = M in N x)``,
  SRW_TAC [][]);

val swapping_def = Define`
  swapping f fv =
    (!x z. f x x z = z) /\
    (!x y u v z. f x y (f u v z) =
                   f (swapstr x y u) (swapstr x y v) (f x y z)) /\
    (!x y z. f x y (f x y z) = z) /\
    (!x y z z'. (f x y z = f x y z') = (z = z')) /\
    (!x y z. ~(x IN fv z) /\ ~(y IN fv z) ==> (f x y z = z))
`

val LET_NEW_congruence = store_thm(
  "LET_NEW_congruence",
  ``(X = Y:string set) ==> FINITE Y ==> (!v. ~(v IN Y) ==> (P v = Q v)) ==>
    (LET P (NEW X)  = LET Q (NEW Y))``,
  SRW_TAC [][] THEN NEW_ELIM_TAC THEN SRW_TAC [][]);

val swap_RECURSION_generic = store_thm(
  "swap_RECURSION_generic",
  ``swapping rswap rFV /\
    FINITE X /\
    (!k. rFV (con k) SUBSET X) /\
    (!s. rFV (var s) SUBSET (s INSERT X)) /\
    (!t' u' t u. rFV t' SUBSET (FV t UNION X) /\
                 rFV u' SUBSET (FV u UNION X) ==>
                 rFV (app t' u' t u) SUBSET FV (t @@ u) UNION X) /\
    (!t' v t. rFV t' SUBSET (FV t UNION X) ==>
              rFV (lam t' v t) SUBSET (FV (LAM v t) UNION X)) /\
    (!k x y. ~(x IN X) /\ ~(y IN X) ==> (rswap x y (con k) = con k)) /\
    (!s x y. ~(x IN X) /\ ~(y IN X) ==>
             (rswap x y (var s) = var (swapstr x y  s))) /\
    (!t t' u u' x y.
         ~(x IN X) /\ ~(y IN X) ==>
         (rswap x y (app t' u' t u) =
          app (rswap x y t') (rswap x y u') (swap x y t) (swap x y u))) /\
    (!t' t x y v.
         ~(x IN X) /\ ~(y IN X) ==>
         (rswap x y (lam t' v t) =
          lam (rswap x y t') (swapstr x y v) (swap x y t))) ==>
    ?hom : 'a nc -> 'b.
      ((!k. hom (CON k) = con k) /\
       (!s. hom (VAR s) = var s) /\
       (!t u. hom (t @@ u) = app (hom t) (hom u) t u) /\
       (!v t. ~(v IN X) ==> (hom (LAM v t) = lam (hom t) v t))) /\
      (!t x y. ~(x IN X) /\ ~(y IN X) ==>
               (hom (swap x y t) = rswap x y (hom t))) /\
      (!t. rFV (hom t) SUBSET FV t UNION X)``,
  SRW_TAC [][swapping_def] THEN
  STRIP_ASSUME_TAC
    (CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV lemma)) THEN
  Q.EXISTS_TAC `hom` THEN
  ASM_SIMP_TAC bool_ss [] THEN
  `!t. rFV (hom t) SUBSET FV t UNION X`
     by (HO_MATCH_MP_TAC nc_INDUCTION THEN
         ASM_SIMP_TAC (srw_ss()) [GSYM INSERT_SING_UNION] THEN
         REPEAT STRIP_TAC THEN
         NEW_ELIM_TAC THEN SRW_TAC [][] THENL [
           MATCH_MP_TAC SUBSET_TRANS THEN
           Q.EXISTS_TAC `FV (LAM v (swap v x t)) UNION X` THEN
           CONJ_TAC THENL [
             ASM_SIMP_TAC bool_ss [FV_THM, GSYM fresh_var_swap],
             `LAM v (swap v x t) = LAM x t`
                by ASM_SIMP_TAC bool_ss
                                [GSYM fresh_var_swap, SIMPLE_ALPHA] THEN
             ASM_SIMP_TAC bool_ss [] THEN SRW_TAC [][]
           ],
           FULL_SIMP_TAC (srw_ss()) [] THEN
           FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [lemma14a]
         ]) THEN
  ASM_SIMP_TAC bool_ss [] THEN
  Q.PAT_ASSUM `!u w x y v.
                  P ==> (rswap x y (lam u v w) = Z)` (ASSUME_TAC o GSYM) THEN
  `!t' t x y v.
      ~(x IN X) /\ ~(y IN X) ==>
      (lam (rswap x y t') v (swap x y t) =
       rswap x y (lam t' (swapstr x y v) t))`
    by PROVE_TAC [swapstr_inverse] THEN
  Q.PAT_ASSUM `!x y u v z. rswap x y (rswap u v z) = Z`
              (ASSUME_TAC o GSYM) THEN
  `!t x y. ~(x IN X) /\ ~(y IN X) ==> (hom (swap x y t) = rswap x y (hom t))`
    by (HO_MATCH_MP_TAC pvh_induction THEN REPEAT CONJ_TAC THEN
        TRY (SRW_TAC [][swap_thm] THEN NO_TAC) THEN
        REPEAT STRIP_TAC THEN
        Cases_on `x = y` THEN1 SRW_TAC [][] THEN
        `?z. ~(z IN {v;x;y} UNION X UNION FV t)`
            by SRW_TAC [][dBTheory.FRESH_string] THEN
        POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) []) THEN
        `LAM v t = LAM z ([VAR z/v] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
        Q.ABBREV_TAC `M = [VAR z/v] t` THEN
        `size t = size M` by SRW_TAC [][] THEN
        POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM (K ALL_TAC) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        `hom (swap x y (LAM z M)) = rswap x y (lam (hom M) z M)`
          by (ASM_SIMP_TAC bool_ss [swap_thm, swapstr_def] THEN
              NEW_ELIM_TAC THEN ASM_REWRITE_TAC [] THEN
              Q.X_GEN_TAC `a` THEN REVERSE (SRW_TAC [][]) THEN1
                ASM_SIMP_TAC bool_ss [swapstr_def] THEN
              Q.ABBREV_TAC `N = lam (hom M) z M` THEN
              `rswap a z (rswap x y N) =
                 rswap x y (rswap x y (rswap a z (rswap x y N)))`
                    by SRW_TAC [][] THEN
              ` _ = rswap x y (rswap (swapstr x y a) (swapstr x y z)
                                     (rswap x y (rswap x y N)))`
                    by SRW_TAC [][] THEN
              ` _ = rswap x y (rswap (swapstr x y a) (swapstr x y z) N)`
                    by SRW_TAC [][] THEN
              SRW_TAC [][] THEN
              FIRST_X_ASSUM MATCH_MP_TAC THEN
              `rFV (lam (hom M) z M) SUBSET FV M DELETE z UNION X`
                 by METIS_TAC [] THEN
              REPEAT STRIP_TAC THENL [
                `swapstr x y a IN FV M DELETE z UNION X`
                    by PROVE_TAC [SUBSET_DEF] THEN
                POP_ASSUM MP_TAC THEN SRW_TAC [][] THEN
                SRW_TAC [][swapstr_def],
                `z IN FV M DELETE z UNION X`
                    by PROVE_TAC [SUBSET_DEF] THEN
                POP_ASSUM MP_TAC THEN SRW_TAC [][]
              ]) THEN
        POP_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC bool_ss [] THEN
        NEW_ELIM_TAC THEN ASM_REWRITE_TAC [] THEN Q.X_GEN_TAC `a` THEN
        REVERSE (SRW_TAC [][]) THEN1 SRW_TAC [][] THEN
        Q_TAC SUFF_TAC
          `~(a IN rFV (lam (hom M) z M)) /\ ~(z IN rFV (lam (hom M) z M))`
              THEN1 PROVE_TAC [] THEN
        `rFV (lam (hom M) z M) SUBSET FV M DELETE z UNION X`
           by PROVE_TAC [] THEN
        REPEAT STRIP_TAC THENL [
          `a IN FV M DELETE z UNION X` by PROVE_TAC [SUBSET_DEF] THEN
          POP_ASSUM MP_TAC THEN SRW_TAC [][],
          `z IN FV M DELETE z UNION X` by PROVE_TAC [SUBSET_DEF] THEN
          POP_ASSUM MP_TAC THEN SRW_TAC [][]
        ]) THEN
  ASM_SIMP_TAC bool_ss [] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN NEW_ELIM_TAC THEN SRW_TAC [][] THENL [
    Cases_on `v = v'` THEN1 SRW_TAC [][] THEN
    SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `~(v' IN rFV (lam (hom t) v t)) /\
                    ~(v IN rFV (lam (hom t) v t))` THEN1
          SRW_TAC [][] THEN
    PROVE_TAC [SUBSET_DEF, IN_DELETE, IN_UNION],
    SRW_TAC [][]
  ]);

val swap_RECURSION_nosideset = save_thm(
  "swap_RECURSION_nosideset",
  SIMP_RULE (srw_ss()) [] (Q.INST [`X` |-> `{}`] swap_RECURSION_generic));

val null_swapping = store_thm(
  "null_swapping",
  ``swapping (\x y z. z) (\z. {})``,
  SRW_TAC [][swapping_def]);

val swap_identity = store_thm(
  "swap_identity",
  ``!t x y. ~(x IN FV t) /\ ~(y IN FV t) ==> (swap x y t = t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SIMP_TAC (srw_ss()) [swap_thm] THEN
  MAP_EVERY Q.X_GEN_TAC [`v`, `t`] THEN STRIP_TAC THEN
  MAP_EVERY Q.X_GEN_TAC [`x`, `y`] THEN STRIP_TAC THENL [
    `swap x y t = t` by METIS_TAC [lemma14a] THEN
    Cases_on `v = x` THEN SRW_TAC [][swapstr_def] THEN
    MATCH_MP_TAC INJECTIVITY_LEMMA3 THEN Q.EXISTS_TAC `v` THEN
    SRW_TAC [][lemma14b],
    SRW_TAC [][] THEN METIS_TAC [swap_ALPHA, swap_comm],
    SRW_TAC [][] THEN METIS_TAC [swap_ALPHA, swap_comm],
    SRW_TAC [][]
  ]);

val nc_swapping = store_thm(
  "nc_swapping",
  ``swapping swap FV``,
  SIMP_TAC (srw_ss()) [swap_swap, swapping_def, swap_identity]);

val swapping_implies_empty_swap = store_thm(
  "swapping_implies_empty_swap",
  ``swapping sw fv /\ (fv t = {}) ==> !x y. sw x y t = t``,
  SRW_TAC [][swapping_def]);



val swap_RECURSION_simple = save_thm(
  "swap_RECURSION_simple",
  (SIMP_RULE (srw_ss()) [null_swapping] o
   Q.INST [`rswap` |-> `\x y z. z`, `rFV` |-> `\z. {}`])
    swap_RECURSION_nosideset);

(* examples

val enf_lam = ``\t' v t. t' /\ is_comb t ==> (rand t = VAR v) ==>
                         v IN FV (rator t)``

val g = ``!t' t x y v. ^enf_lam t' (swapstr x y v) (swap x y t) = ^enf_lam t' v t``

val _ = SIMP_CONV (srw_ss()) [GSYM swap_thm] g

val simple_recursor_lam = ``\t' v t : 'a nc. LAM v t'``
val g = ``!t' t x y v. ^simple_recursor_lam (swap x y t') (swapstr x y v) (swap x y t) = swap x y (^simple_recursor_lam t' v t)``

val _ = SIMP_CONV (srw_ss()) [GSYM swap_thm] g

*)


val _ = export_theory();
