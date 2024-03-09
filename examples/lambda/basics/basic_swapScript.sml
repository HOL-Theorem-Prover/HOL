open HolKernel Parse boolLib bossLib BasicProvers boolSimps

local open stringTheory pred_setTheory in end;

val _ = new_theory "basic_swap";

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

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

val raw_lswapstr_def = Define`
  (raw_lswapstr [] s = s) /\
  (raw_lswapstr (h::t) s = swapstr (FST h) (SND h) (raw_lswapstr t s))
`;
val _ = export_rewrites ["raw_lswapstr_def"]

val raw_lswapstr_APPEND = store_thm(
  "raw_lswapstr_APPEND",
  ``raw_lswapstr (p1 ++ p2) s = raw_lswapstr p1 (raw_lswapstr p2 s)``,
  Induct_on `p1` THEN SRW_TAC [][raw_lswapstr_def]);

val raw_lswapstr_inverse = store_thm(
  "raw_lswapstr_inverse",
  ``!p s. (raw_lswapstr (REVERSE p) (raw_lswapstr p s) = s) /\
          (raw_lswapstr p (raw_lswapstr (REVERSE p) s) = s)``,
  Induct THEN SRW_TAC [][raw_lswapstr_def, raw_lswapstr_APPEND]);
val _ = export_rewrites ["raw_lswapstr_inverse"]

val raw_lswapstr_11 = store_thm(
  "raw_lswapstr_11",
  ``(raw_lswapstr p s = raw_lswapstr p t) = (s = t)``,
  METIS_TAC [raw_lswapstr_inverse]);
val _ = export_rewrites ["raw_lswapstr_11"]

val raw_lswapstr_eql = store_thm(
  "raw_lswapstr_eql",
  ``(raw_lswapstr p s = t) = (s = raw_lswapstr (REVERSE p) t)``,
  METIS_TAC [raw_lswapstr_inverse]);

val raw_lswapstr_eqr = store_thm(
  "raw_lswapstr_eqr",
  ``(s = raw_lswapstr p t) = (raw_lswapstr (REVERSE p) s =  t)``,
  METIS_TAC [raw_lswapstr_inverse]);

val raw_lswapstr_sing_to_back = store_thm(
  "raw_lswapstr_sing_to_back",
  ``!p u v s. swapstr (raw_lswapstr p u) (raw_lswapstr p v) (raw_lswapstr p s) =
              raw_lswapstr p (swapstr u v s)``,
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

(* |- !s. FINITE s ==> NEW s NOTIN s *)
val NEW_def =
    new_specification
      ("NEW_def", ["NEW"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] new_exists)

val NEW_ELIM_RULE = store_thm(
  "NEW_ELIM_RULE",
  ``!P X. FINITE X /\ (!v:string. ~(v IN X) ==> P v) ==>
          P (NEW X)``,
  PROVE_TAC [NEW_def]);

(* ‘NEWS n s’ generates n fresh names from the excluded set ‘s’ *)
Definition NEWS :
    NEWS      0  s = [] /\
    NEWS (SUC n) s = NEW s :: NEWS n (NEW s INSERT s)
End

Theorem NEWS_0[simp] :
    NEWS 0 s = []
Proof
    rw [NEWS]
QED

(* NOTE: this is the old FRESH_list_def *)
Theorem NEWS_def :
    !n s. FINITE s ==>
          ALL_DISTINCT (NEWS n s) /\ DISJOINT (set (NEWS n s)) s /\
          LENGTH (NEWS n s) = n
Proof
    Induct_on ‘n’ >- rw [NEWS]
 >> Q.X_GEN_TAC ‘s’ >> DISCH_TAC
 >> simp [NEWS]
 >> Q.PAT_X_ASSUM ‘!s. FINITE s ==> P’ (MP_TAC o (Q.SPEC ‘NEW s INSERT s’))
 >> rw []
 >> MATCH_MP_TAC NEW_def
 >> ASM_REWRITE_TAC []
QED

Theorem NEWS_prefix :
    !m n s. FINITE s /\ m <= n ==> NEWS m s <<= NEWS n s
Proof
    Induct_on ‘m’
 >> rw [NEWS]
 >> Cases_on ‘n’ >> rw [NEWS]
QED

val _ = export_theory();
val _ = html_theory "basic_swap";
