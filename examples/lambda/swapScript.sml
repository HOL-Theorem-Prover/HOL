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

val SUB_LAM_SWAP_RWT = store_thm(
  "SUB_LAM_SWAP_RWT",
  ``!u v x t. [VAR v/u] (LAM x t) =
              let z = NEW ({v;u;x} UNION FV t) in
                LAM z ([VAR v/u](swap z x t))``,
  REPEAT GEN_TAC THEN
  Q_TAC (NEW_TAC "z") `{v;u;x} UNION FV t`  THEN
  `LAM x t = LAM z (swap z x t)` by SRW_TAC [][swap_ALPHA] THEN
  SRW_TAC [][SUB_THM]);

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

val swap_induction = store_thm(
  "swap_induction",
  ``!P. (!s. P (VAR s)) /\ (!k. P (CON k)) /\
        (!t u. P t /\ P u ==> P(t @@ u)) /\
        (!v t. (!u. ~(u IN FV t) ==> P(swap u v t)) ==> P (LAM v t)) ==>
        !t. P t``,
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][GSYM fresh_var_swap]);

(* ----------------------------------------------------------------------
    supporting recursion over lambda calculus terms using swap
   ---------------------------------------------------------------------- *)

val swapping_def = Define`
  swapping f fv =
    (!x z. f x x z = z) /\
    (* (!x y u v z. f x y (f u v z) =
                   f (swapstr x y u) (swapstr x y v) (f x y z)) /\ *)
    (!x y z. f x y (f x y z) = z) /\
    (* (!x y z z'. (f x y z = f x y z') = (z = z')) /\ *)
    (!x y z. ~(x IN fv z) /\ ~(y IN fv z) ==> (f x y z = z)) /\
    (!x y z s. s IN fv (f x y z) = swapstr x y s IN fv z)
`

val LET_NEW_congruence = store_thm(
  "LET_NEW_congruence",
  ``(X = Y:string set) ==> FINITE Y ==> (!v. ~(v IN Y) ==> (P v = Q v)) ==>
    (LET P (NEW X)  = LET Q (NEW Y))``,
  SRW_TAC [][] THEN NEW_ELIM_TAC THEN SRW_TAC [][]);

val null_swapping = store_thm(
  "null_swapping",
  ``swapping (\x y z. z) (K {})``,
  (* can't write \x. {} for second argument above; it tweaks a bug in
     HO_PART_MATCH *)
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

val str_swapping = store_thm(
  "str_swapping",
  ``swapping swapstr (\s. {s})``,
  REWRITE_TAC [swapping_def] THEN SRW_TAC [][]);

val swapping_implies_empty_swap = store_thm(
  "swapping_implies_empty_swap",
  ``swapping sw fv /\ (fv t = {}) ==> !x y. sw x y t = t``,
  SRW_TAC [][swapping_def]);

val swapping_implies_identity_swap = store_thm(
  "swapping_implies_identity_swap",
  ``!sw fv x y t. swapping sw fv /\ ~(x IN fv t) /\ ~(y IN fv t) ==>
                  (sw x y t = t)``,
  SRW_TAC [][swapping_def]);


val swapfn_def = Define`
  swapfn (dswap:string -> string -> 'a -> 'a)
         (rswap:string -> string -> 'b -> 'b)
         x y f d = rswap x y (f (dswap x y d))
`;

val fresh_new_subst0 = prove(
  ``FINITE X /\ (!p. FINITE (pFV p)) ==>
    ((let v = NEW (FV (LAM x u) UNION pFV p UNION X) in f v ([VAR v/x] u)) =
     (let v = NEW (FV (LAM x u) UNION pFV p UNION X) in f v (swap v x u)))``,
  STRIP_TAC THEN NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][fresh_var_swap, lemma14a]);


val lemma =
    (SIMP_RULE bool_ss [FUN_EQ_THM, ABS_DEF, fresh_new_subst0,
                        ASSUME ``FINITE (X:string set)``,
                        ASSUME ``!p:'b. FINITE (pFV p : string set)``] o
     Q.INST [`lam` |->
             `\r t p.
                 let v = NEW (FV (ABS t) UNION pFV p UNION X)
                 in
                   lam (r v) v (t v) p`] o
     INST_TYPE [beta |-> (beta --> gamma)] o
     CONJUNCT1 o
     CONV_RULE EXISTS_UNIQUE_CONV o
     SPEC_ALL)
    nc_RECURSION


val swap_RECURSION_pgeneric = store_thm(
  "swap_RECURSION_pgeneric",
  ``swapping rswap rFV /\ swapping pswap pFV /\

    FINITE X /\ (!p. FINITE (pFV p)) /\

    (!k p. rFV (con k p) SUBSET (X UNION pFV p)) /\
    (!s p. rFV (var s p) SUBSET (s INSERT pFV p UNION X)) /\
    (!t' u' t u p.
        (!p. rFV (t' p) SUBSET (FV t UNION pFV p UNION X)) /\
        (!p. rFV (u' p) SUBSET (FV u UNION pFV p UNION X)) ==>
        rFV (app t' u' t u p) SUBSET FV t UNION FV u UNION pFV p UNION X) /\
    (!t' v t p.
        (!p. rFV (t' p) SUBSET (FV t UNION pFV p UNION X)) ==>
        rFV (lam t' v t p) SUBSET (FV (LAM v t) UNION pFV p UNION X)) /\

    (!k x y p. ~(x IN X) /\ ~(y IN X) ==>
               (rswap x y (con k p) = con k (pswap x y p))) /\
    (!s x y p. ~(x IN X) /\ ~(y IN X) ==>
               (rswap x y (var s p) = var (swapstr x y s) (pswap x y p))) /\
    (!t t' u u' x y p.
         ~(x IN X) /\ ~(y IN X) ==>
         (rswap x y (app t' u' t u p) =
          app (swapfn pswap rswap x y t') (swapfn pswap rswap x y u')
              (swap x y t) (swap x y u)
              (pswap x y p))) /\
    (!t' t x y v p.
         ~(x IN X) /\ ~(y IN X) ==>
         (rswap x y (lam t' v t p) =
          lam (swapfn pswap rswap x y t')
              (swapstr x y v) (swap x y t) (pswap x y p))) ==>
    ?hom : 'a nc -> 'b -> 'c.
      ((!k p. hom (CON k) p = con k p) /\
       (!s p. hom (VAR s) p = var s p) /\
       (!t u p. hom (t @@ u) p = app (hom t) (hom u) t u p) /\
       (!v t p. ~(v IN X UNION pFV p) ==>
                (hom (LAM v t) p = lam (hom t) v t p))) /\
      (!t p x y. ~(x IN X) /\ ~(y IN X) ==>
                 (hom (swap x y t) p = rswap x y (hom t (pswap x y p)))) /\
      (!t p. rFV (hom t p) SUBSET FV t UNION pFV p UNION X)``,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC lemma THEN
  Q.EXISTS_TAC `hom` THEN ASM_SIMP_TAC bool_ss [] THEN
  `!t p. rFV (hom t p) SUBSET FV t UNION pFV p UNION X`
     by (HO_MATCH_MP_TAC nc_INDUCTION THEN ASM_SIMP_TAC (srw_ss()) [] THEN
         REPEAT CONJ_TAC THENL [
           PROVE_TAC [UNION_COMM],
           ASM_SIMP_TAC (srw_ss()) [GSYM INSERT_SING_UNION, INSERT_UNION_EQ],
           REPEAT STRIP_TAC THEN NEW_ELIM_TAC THEN
           ASM_SIMP_TAC bool_ss [] THEN
           Q.X_GEN_TAC `u` THEN REPEAT STRIP_TAC THENL [
             `FV t DELETE x = FV (LAM x t)` by SRW_TAC [][] THEN
             POP_ASSUM SUBST_ALL_TAC THEN
             `LAM x t = LAM u (swap u x t)` by SRW_TAC [][swap_ALPHA] THEN
             POP_ASSUM SUBST_ALL_TAC THEN
             FIRST_ASSUM MATCH_MP_TAC THEN
             `swap u x t = [VAR u/x] t` by SRW_TAC [][fresh_var_swap] THEN
             ASM_SIMP_TAC bool_ss [],
             SRW_TAC [][] THEN
             `FV t DELETE u = FV (LAM u t)` by SRW_TAC [][] THEN
             POP_ASSUM SUBST_ALL_TAC THEN
             FIRST_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
             METIS_TAC [lemma14a]
           ]
         ]) THEN
  ASM_SIMP_TAC bool_ss [] THEN
  `(!x y p. pswap x y (pswap x y p) = p) /\ (!x p. pswap x x p = p) /\
   (!x r. rswap x x r = r)`
     by FULL_SIMP_TAC (srw_ss()) [swapping_def] THEN
  `!t p x y. ~(x IN X) /\ ~(y IN X) ==>
             (hom (swap x y t) p = rswap x y (hom t (pswap x y p)))`
      by (HO_MATCH_MP_TAC pvh_induction THEN REPEAT CONJ_TAC THEN
          TRY (SRW_TAC [][swap_thm] THEN NO_TAC) THENL [
            MAP_EVERY Q.X_GEN_TAC [`t`,`u`] THEN
            SRW_TAC [][swap_thm] THEN
            `(hom (swap x y t) = swapfn pswap rswap x y (hom t)) /\
             (hom (swap x y u) = swapfn pswap rswap x y (hom u))`
               by SRW_TAC [][FUN_EQ_THM, swapfn_def] THEN
            SRW_TAC [][],
            REPEAT STRIP_TAC THEN
            Cases_on `x = y` THEN1 SRW_TAC [][] THEN
            Q.SPEC_THEN `{x;y;v} UNION FV t UNION X UNION pFV p`
                        MP_TAC dBTheory.FRESH_string THEN
            CONV_TAC
              (LAND_CONV
                 (SIMP_CONV
                    (srw_ss())
                    [Q.ASSUME `FINITE (X:string set)`,
                     Q.ASSUME `!p:'b. FINITE (pFV p:string set)`])) THEN
            DISCH_THEN (Q.X_CHOOSE_THEN `z` STRIP_ASSUME_TAC) THEN
            `LAM v t = LAM z ([VAR z/v] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
            Q.ABBREV_TAC `M = [VAR z/v] t` THEN
            `size t = size M` by SRW_TAC [][] THEN
            POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM (K ALL_TAC) THEN
            POP_ASSUM SUBST_ALL_TAC THEN
            `hom (swap x y (LAM z M)) p =
               rswap x y (lam (hom M) z M (pswap x y p))`
               by (SRW_TAC [][swap_thm] THEN
                   NEW_ELIM_TAC THEN ASM_SIMP_TAC bool_ss [] THEN
                   Q.X_GEN_TAC `a` THEN
                   REVERSE (SRW_TAC [][]) THEN1
                           (SRW_TAC [][] THEN
                            REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
                            SRW_TAC [][FUN_EQ_THM, swapfn_def]) THEN
                   `hom (swap a z (swap x y M)) =
                      swapfn pswap rswap a z (hom (swap x y M))`
                        by SRW_TAC [][swapfn_def, FUN_EQ_THM] THEN
                   `pswap a z p = p`
                      by PROVE_TAC [swapping_implies_identity_swap] THEN
                   `lam (hom (swap a z (swap x y M))) a
                        (swap a z (swap x y M)) p =
                      rswap a z
                          (lam (hom (swap x y M)) z (swap x y M) p)`
                      by SRW_TAC [][] THEN
                   POP_ASSUM SUBST_ALL_TAC THEN
                   `swapfn pswap rswap x y (hom M) = hom (swap x y M)`
                       by SRW_TAC [][FUN_EQ_THM, swapfn_def] THEN
                   POP_ASSUM SUBST_ALL_TAC THEN
                   MATCH_MP_TAC swapping_implies_identity_swap THEN
                   Q.EXISTS_TAC `rFV` THEN ASM_REWRITE_TAC [] THEN
                   `rFV (lam (hom (swap x y M)) z (swap x y M) p)
                        SUBSET
                    FV (LAM z (swap x y M)) UNION pFV p UNION X`
                       by SRW_TAC [][] THEN
                   POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
                   METIS_TAC []) THEN
            POP_ASSUM SUBST_ALL_TAC THEN REPEAT AP_TERM_TAC THEN
            ASM_SIMP_TAC bool_ss [] THEN
            NEW_ELIM_TAC THEN ASM_REWRITE_TAC [] THEN
            Q.X_GEN_TAC `a` THEN
            REVERSE (SRW_TAC [][]) THEN1 REWRITE_TAC [swap_id] THEN
            `~(z IN pFV (pswap x y p))`
               by FULL_SIMP_TAC (srw_ss()) [swapping_def] THEN
            `pswap a z (pswap x y p) = pswap x y p`
               by (MATCH_MP_TAC swapping_implies_identity_swap THEN
                   Q.EXISTS_TAC `pFV` THEN ASM_REWRITE_TAC []) THEN
            MATCH_MP_TAC EQ_TRANS THEN
            Q.EXISTS_TAC `rswap a z (lam (hom M) z M (pswap x y p))` THEN
            CONJ_TAC THENL [
              ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
              MATCH_MP_TAC swapping_implies_identity_swap THEN
              Q.EXISTS_TAC `rFV` THEN ASM_REWRITE_TAC [] THEN
              `rFV (lam (hom M) z M (pswap x y p)) SUBSET
               FV (LAM z M) UNION pFV (pswap x y p) UNION X`
                  by SRW_TAC [][] THEN
              POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
              PROVE_TAC [],
              SRW_TAC [][] THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
              SRW_TAC [][FUN_EQ_THM, swapfn_def]
            ]
          ]) THEN
  ASM_SIMP_TAC bool_ss [] THEN SRW_TAC [][] THEN
  NEW_ELIM_TAC THEN ASM_SIMP_TAC bool_ss [] THEN
  Q.X_GEN_TAC `u` THEN STRIP_TAC THENL [
    `hom (swap u v t) = swapfn pswap rswap u v (hom t)`
       by SRW_TAC [][FUN_EQ_THM, swapfn_def] THEN
    `pswap u v p = p` by PROVE_TAC [swapping_implies_identity_swap] THEN
    `lam (hom (swap u v t)) u (swap u v t) p = rswap u v (lam (hom t) v t p)`
       by SRW_TAC [][] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC swapping_implies_identity_swap THEN
    Q.EXISTS_TAC `rFV` THEN
    ASM_REWRITE_TAC [] THEN
    `rFV (lam (hom t) v t p) SUBSET FV (LAM v t) UNION pFV p UNION X`
       by SRW_TAC [][] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [SUBSET_DEF] THEN SRW_TAC [][] THEN
    METIS_TAC [],
    SRW_TAC [][]
  ]);



val one_eta = prove(
  ``(\u. f ()) = f``,
  SRW_TAC [][FUN_EQ_THM] THEN Cases_on `u` THEN SRW_TAC [][]);
val exists_fn_dom_one = prove(
  ``(?f: 'a -> one -> 'b. P f) = (?f: 'a -> 'b. P (\x u. f x))``,
  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `\a. f a ()` THEN BETA_TAC THEN REWRITE_TAC [one_eta] THEN
    SRW_TAC [ETA_ss][],
    METIS_TAC []
  ]);

val forall_fn_dom_one = prove(
  ``(!f : one -> 'b. P f) = (!f: 'b. P (K f))``,
  SRW_TAC [][EQ_IMP_THM] THEN
  `f = K (f ())` by SRW_TAC [][combinTheory.K_DEF, one_eta] THEN
  POP_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC []);
val forall_one_one = prove(
  ``(!p:one. P p) = P ()``,
  SRW_TAC [][EQ_IMP_THM] THEN Cases_on `p` THEN SRW_TAC [][]);


val swap_RECURSION_generic = save_thm(
  "swap_RECURSION_generic",
  (SIMP_RULE (srw_ss()) [null_swapping, exists_fn_dom_one, swapfn_def,
                         forall_fn_dom_one, forall_one_one] o
   Q.INST [`pFV` |-> `K {}`,
           `pswap` |-> `\x y u. u`,
           `var` |-> `\s p. var s`,
           `con` |-> `\k p. con k`,
           `app` |-> `\rt ru t u p. app (rt()) (ru()) t u`,
           `lam` |-> `\rt v t p. lam (rt()) v t`] o
   INST_TYPE [beta |-> ``:one``, gamma |-> beta])
  swap_RECURSION_pgeneric);

val swap_RECURSION_nosideset = save_thm(
  "swap_RECURSION_nosideset",
  SIMP_RULE (srw_ss()) [] (Q.INST [`X` |-> `{}`] swap_RECURSION_generic));

val swap_RECURSION_simple = save_thm(
  "swap_RECURSION_simple",
  (SIMP_RULE (srw_ss()) [null_swapping] o
   Q.INST [`rswap` |-> `\x y z. z`, `rFV` |-> `K {}`])
    swap_RECURSION_nosideset);


(* examples

* ENF *

val enf_lam = ``\t' v t. t' /\ is_comb t ==> (rand t = VAR v) ==>
                         v IN FV (rator t)``

val g = ``!t' t x y v. ^enf_lam t' (swapstr x y v) (swap x y t) = ^enf_lam t' v t``

val _ = SIMP_CONV (srw_ss()) [GSYM swap_thm] g

val simple_recursor_lam = ``\t' v t : 'a nc. LAM v t'``
val g = ``!t' t x y v. ^simple_recursor_lam (swap x y t') (swapstr x y v) (swap x y t) = swap x y (^simple_recursor_lam t' v t)``

val _ = SIMP_CONV (srw_ss()) [GSYM swap_thm] g

* SUBSTITUTION *

open BasicProvers simpLib pred_setTheory boolSimps SingleStep NEWLib
     ncTheory
val pswap = ``\x y. (swapstr x y ## swap x y)``
val pFV = ``\p : string # 'a nc. FST p INSERT FV (SND p)``

val swap_if = prove(``swap x y (if p then q else r) =
                      if p then swap x y q else swap x y r``,
                    SRW_TAC [][])

val pair_swapping = prove(
  ``swapping (\x y. swapstr x y ## swap x y) (\p. FST p INSERT FV (SND p))``,
  REWRITE_TAC [swapping_def] THEN
  SIMP_TAC (srw_ss())[pairTheory.FORALL_PROD, swap_identity]);


val forall_prod =
    CONV_RULE (RHS_CONV (RENAME_VARS_CONV ["z", "M"])) pairTheory.FORALL_PROD

val reorder = prove(
  ``(?f: 'a -> 'b # 'c -> 'd.  P f) =
    (?f: 'c -> 'b -> 'a -> 'd. P (\a bc. f (SND bc) (FST bc) a))``,
  SRW_TAC [][EQ_IMP_THM] THEN TRY (metisLib.METIS_TAC []) THEN
  Q.EXISTS_TAC `\c b a. f a (b, c)` THEN SRW_TAC [ETA_ss][]);

val result0 =
    (REWRITE_RULE [] o
     CONV_RULE (LAND_CONV (EQT_INTRO o PROVE [])) o
     CONV_RULE
       (LAND_CONV (SIMP_CONV (srw_ss() ++ COND_elim_ss)
                             [SUBSET_DEF, swap_thm, RIGHT_AND_OVER_OR,
                              LEFT_AND_OVER_OR, DISJ_IMP_THM,
                              swap_identity])) o
     SIMP_RULE (srw_ss()) [forall_prod] o
     SIMP_RULE (srw_ss()) [SUBSET_UNION, nc_swapping,
                           swapfn_def, swap_thm, swap_if,
                           pair_swapping, reorder] o
     Q.INST [`X` |-> `{}`,
             `app` |-> `\rt ru t u p. rt p @@ ru p`,
             `con` |-> `\k p. CON k`,
             `var` |-> `\s p . if s = FST p then SND p else VAR s`,
             `lam` |-> `\rt u t p. LAM u (rt p)`,
             `rswap` |-> `swap`, `rFV` |-> `FV`,
             `pswap` |-> `^pswap`, `pFV` |-> `^pFV`] o
     INST_TYPE [beta |-> ``:string # 'a nc``, gamma |-> ``:'a nc``])
    swap_RECURSION_pgeneric

val hom_def = new_specification ("hom_def", ["hom"], result0)

val l14b = prove(
  ``!t v M. ~(v IN FV t) ==> (hom M v t = t)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][hom_def] THENL [
    Q_TAC (NEW_TAC "z") `FV M UNION FV t UNION {v';v}` THEN
    `LAM v t = LAM z (swap z v t)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [][hom_def] THEN Cases_on `v' = v` THEN SRW_TAC [][],
    Q_TAC (NEW_TAC "z") `FV M UNION FV t UNION {v}` THEN
    `LAM v t = LAM z (swap z v t)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [][hom_def]
  ]);

val hom_lam_eq_var = prove(
  ``hom M v (LAM v t) = LAM v t``,
  SRW_TAC [][l14b]);

val l14a = prove(
  ``!t v. hom (VAR v) v t = t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][hom_def] THEN
  Cases_on `v = v'` THEN1 SRW_TAC [][l14b] THEN
  Q_TAC (NEW_TAC "z") `FV t UNION {v;v'}` THEN
  `LAM v t = LAM z (swap z v t)` by SRW_TAC [][swap_ALPHA] THEN
  SRW_TAC [][hom_def]);


*)


val _ = export_theory();
