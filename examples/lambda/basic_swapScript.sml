open HolKernel Parse boolLib bossLib BasicProvers boolSimps

local open stringTheory pred_setTheory in end;

val _ = new_theory "basic_swap";

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before
                            BasicProvers.export_rewrites [s])

(* ----------------------------------------------------------------------
    swapping over strings
   ---------------------------------------------------------------------- *)

val swapstr_def = Define`
  swapstr x y (s:string) = if x = s then y else if y = s then x else s
`;

val swapstr_id = Store_Thm(
  "swapstr_id",
  ``swapstr x x s = s``,
  SRW_TAC [][swapstr_def]);

val swapstr_inverse = Store_Thm(
  "swapstr_inverse",
  ``swapstr x y (swapstr x y s) = s``,
  SRW_TAC [][swapstr_def] THEN METIS_TAC []);

val swapstr_eq_left = store_thm(
  "swapstr_eq_left",
  ``(swapstr x y s = t) = (s = swapstr x y t)``,
  SRW_TAC [][swapstr_def] THEN METIS_TAC []);

val swapstr_11 = Store_Thm(
  "swapstr_11",
  ``(swapstr x y s1 = swapstr x y s2) = (s1 = s2)``,
  SRW_TAC [][swapstr_eq_left]);

fun simp_cond_tac (asl, g) = let
  val eqn = find_term (fn t => is_eq t andalso is_var (lhs t) andalso
                               is_var (rhs t)) g
in
  ASM_CASES_TAC eqn THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
  ASM_SIMP_TAC bool_ss []
end (asl, g)

val swapstr_swapstr = Store_Thm(
  "swapstr_swapstr",
  ``swapstr (swapstr x y u) (swapstr x y v) (swapstr x y s) =
    swapstr x y (swapstr u v s)``,
  REWRITE_TAC [swapstr_def] THEN REPEAT simp_cond_tac);

val swapstr_comm = Store_Thm(
  "swapstr_comm",
  ``swapstr y x s = swapstr x y s``,
  SRW_TAC [][swapstr_def] THEN METIS_TAC []);

val swapstr_thm = Store_Thm(
  "swapstr_thm",
  ``(swapstr x y x = y) /\ (swapstr x y y = x) /\
    (~(x = a) /\ ~(y = a) ==> (swapstr x y a = a))``,
  SRW_TAC [][swapstr_def]);

(* ----------------------------------------------------------------------
    swapping lists of pairs over strings (a foldr)
   ---------------------------------------------------------------------- *)

val lswapstr_def = Define`
  (lswapstr [] s = s) /\
  (lswapstr (h::t) s = swapstr (FST h) (SND h) (lswapstr t s))
`;
val _ = export_rewrites ["lswapstr_def"]

val lswapstr_APPEND = store_thm(
  "lswapstr_APPEND",
  ``lswapstr (p1 ++ p2) s = lswapstr p1 (lswapstr p2 s)``,
  Induct_on `p1` THEN SRW_TAC [][lswapstr_def]);

val lswapstr_inverse = store_thm(
  "lswapstr_inverse",
  ``!p s. (lswapstr (REVERSE p) (lswapstr p s) = s) /\
          (lswapstr p (lswapstr (REVERSE p) s) = s)``,
  Induct THEN SRW_TAC [][lswapstr_def, lswapstr_APPEND]);
val _ = export_rewrites ["lswapstr_inverse"]

val lswapstr_11 = store_thm(
  "lswapstr_11",
  ``(lswapstr p s = lswapstr p t) = (s = t)``,
  METIS_TAC [lswapstr_inverse]);
val _ = export_rewrites ["lswapstr_11"]

val lswapstr_eql = store_thm(
  "lswapstr_eql",
  ``(lswapstr p s = t) = (s = lswapstr (REVERSE p) t)``,
  METIS_TAC [lswapstr_inverse]);

val lswapstr_eqr = store_thm(
  "lswapstr_eqr",
  ``(s = lswapstr p t) = (lswapstr (REVERSE p) s =  t)``,
  METIS_TAC [lswapstr_inverse]);

val lswapstr_sing_to_back = store_thm(
  "lswapstr_sing_to_back",
  ``!p u v s. swapstr (lswapstr p u) (lswapstr p v) (lswapstr p s) =
              lswapstr p (swapstr u v s)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

(* ----------------------------------------------------------------------
    NEW constant
   ---------------------------------------------------------------------- *)

val INFINITE_STR_UNIV = store_thm(
  "INFINITE_STR_UNIV",
  ``INFINITE (UNIV : string set)``,
  SRW_TAC [][pred_setTheory.INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\st. STRING (CHR 0) st` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `""` THEN SRW_TAC [][]);

val new_exists = store_thm(
  "new_exists",
  ``!s : string set. FINITE s ==> ?x. ~(x IN s)``,
  Q_TAC SUFF_TAC `INFINITE (UNIV : string set)`
        THEN1 METIS_TAC [pred_setTheory.IN_UNIV,
                         pred_setTheory.IN_INFINITE_NOT_FINITE] THEN
  SRW_TAC [][INFINITE_STR_UNIV]);

val NEW_def =
    new_specification
      ("NEW_def", ["NEW"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] new_exists)

val NEW_ELIM_RULE = store_thm(
  "NEW_ELIM_RULE",
  ``!P X. FINITE X /\ (!v:string. ~(v IN X) ==> P v) ==>
          P (NEW X)``,
  PROVE_TAC [NEW_def]);

val _ = export_theory();
