open HolKernel Parse boolLib bossLib BasicProvers boolSimps

local open stringTheory pred_setTheory in end;

val _ = new_theory "basic_swap";

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

(* ----------------------------------------------------------------------
    new type of atoms, allowing different sorts of atoms
   ---------------------------------------------------------------------- *)
val _ = Hol_datatype`atom =
  Atom of string => string`;

val atom_sort_def = Define`
  atom_sort (Atom s n) = s`;

val atom_name_def = Define`
  atom_name (Atom s n) = n`;

val _ = export_rewrites["atom_sort_def","atom_name_def"];

(* ----------------------------------------------------------------------
    atom swapping
   ---------------------------------------------------------------------- *)

val swap_def = Define`
  swap x y s = if atom_sort x = atom_sort y then
                 if x = s then y else if y = s then x else s
               else s`;

val swap_id = Store_Thm(
  "swap_id",
  ``swap x x s = s``,
  SRW_TAC [][swap_def]);

val swap_inverse = Store_Thm(
  "swap_inverse",
  ``swap x y (swap x y s) = s``,
  SRW_TAC [][swap_def] THEN METIS_TAC []);

val swap_eq_left = store_thm(
  "swap_eq_left",
  ``(swap x y s = t) = (s = swap x y t)``,
  SRW_TAC [][swap_def] THEN METIS_TAC []);

val swap_11 = Store_Thm(
  "swap_11",
  ``(swap x y s1 = swap x y s2) = (s1 = s2)``,
  SRW_TAC [][swap_eq_left]);

fun simp_cond_tac (asl, g) = let
  val eqn = find_term (fn t => is_eq t andalso is_var (lhs t) andalso
                               is_var (rhs t)) g
in
  ASM_CASES_TAC eqn THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
  ASM_SIMP_TAC bool_ss []
end (asl, g)

val swap_swap = Store_Thm(
  "swap_swap",
  ``swap (swap x y u) (swap x y v) (swap x y s) =
    swap x y (swap u v s)``,
  REWRITE_TAC [swap_def] THEN
  REVERSE (Cases_on `atom_sort x = atom_sort y`) THEN1
    SRW_TAC [][] THEN
  REPEAT simp_cond_tac THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []);

val swap_comm = Store_Thm(
  "swap_comm",
  ``swap y x s = swap x y s``,
  SRW_TAC [][swap_def] THEN METIS_TAC []);

val swap_thm = Store_Thm(
  "swap_thm",
  ``((atom_sort x = atom_sort y) ==> (swap x y x = y)) /\
    ((atom_sort x = atom_sort y) ==> (swap x y y = x)) /\
    (~(atom_sort x = atom_sort y) ==> (swap x y a = a)) /\
    (~(x = a) /\ ~(y = a) ==> (swap x y a = a))``,
  SRW_TAC [][swap_def]);

(* ----------------------------------------------------------------------
    swapping lists of pairs of atoms (a foldr)
   ---------------------------------------------------------------------- *)

val lswap_def = Define`
  (lswap [] s = s) /\
  (lswap (h::t) s = swap (FST h) (SND h) (lswap t s))
`;
val _ = export_rewrites ["lswap_def"]

val lswap_APPEND = store_thm(
  "lswap_APPEND",
  ``lswap (p1 ++ p2) s = lswap p1 (lswap p2 s)``,
  Induct_on `p1` THEN SRW_TAC [][lswap_def]);

val lswap_inverse = store_thm(
  "lswap_inverse",
  ``!p s. (lswap (REVERSE p) (lswap p s) = s) /\
          (lswap p (lswap (REVERSE p) s) = s)``,
  Induct THEN SRW_TAC [][lswap_def, lswap_APPEND]);
val _ = export_rewrites ["lswap_inverse"]

val lswap_11 = store_thm(
  "lswap_11",
  ``(lswap p s = lswap p t) = (s = t)``,
  METIS_TAC [lswap_inverse]);
val _ = export_rewrites ["lswap_11"]

val lswap_eql = store_thm(
  "lswap_eql",
  ``(lswap p s = t) = (s = lswap (REVERSE p) t)``,
  METIS_TAC [lswap_inverse]);

val lswap_eqr = store_thm(
  "lswap_eqr",
  ``(s = lswap p t) = (lswap (REVERSE p) s =  t)``,
  METIS_TAC [lswap_inverse]);

val lswap_sing_to_back = store_thm(
  "lswap_sing_to_back",
  ``!p u v s. swap (lswap p u) (lswap p v) (lswap p s) =
              lswap p (swap u v s)``,
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
  ``!A s. FINITE A ==> ?a. ~(a IN A) /\ (atom_sort a = s)``,
  SRW_TAC [][] THEN
  `?n. ~(n IN (IMAGE atom_name A))` by
    METIS_TAC [pred_setTheory.IN_UNIV,
               pred_setTheory.IMAGE_FINITE,
               pred_setTheory.IN_INFINITE_NOT_FINITE,
               INFINITE_STR_UNIV] THEN
  Q.EXISTS_TAC `Atom s n` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM (Q.SPEC_THEN `Atom s n` MP_TAC) THEN
  SRW_TAC [][])

val NEW_def =
    new_specification
      ("NEW_def", ["NEW"],
       SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] new_exists)

val NEW_ELIM_RULE = store_thm(
  "NEW_ELIM_RULE",
  ``!P A s. FINITE A /\ (!a. ~(a IN A) /\ (atom_sort a = s) ==> P a) ==>
            P (NEW A s)``,
  PROVE_TAC [NEW_def]);

val _ = export_theory();
