(* ========================================================================== *)
(* FILE    : basic_swapScript.sml                                             *)
(* TITLE   : Some "basic" logic about swapping strings and the "new" operator *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*         : 2023-2024 Michael Norrish and Chun Tian                          *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open boolSimps arithmeticTheory stringTheory pred_setTheory numLib hurdUtils
     listTheory rich_listTheory pairTheory numpairTheory
     string_numTheory listRangeTheory;

val _ = new_theory "basic_swap";

(* ----------------------------------------------------------------------
    swapping over strings
   ---------------------------------------------------------------------- *)

val swapstr_def = Define`
  swapstr x y (s:string) = if x = s then y else if y = s then x else s
`;

Theorem swapstr_id[simp] :
    swapstr x x s = s
Proof
  SRW_TAC [][swapstr_def]
QED

Theorem swapstr_inverse[simp] :
    swapstr x y (swapstr x y s) = s
Proof
  SRW_TAC [][swapstr_def] THEN METIS_TAC []
QED

Theorem swapstr_eq_left :
    (swapstr x y s = t) <=> (s = swapstr x y t)
Proof
  SRW_TAC [][swapstr_def] THEN METIS_TAC []
QED

Theorem swapstr_11[simp] :
    (swapstr x y s1 = swapstr x y s2) <=> (s1 = s2)
Proof
  SRW_TAC [][swapstr_eq_left]
QED

fun simp_cond_tac (asl, g) = let
  val eqn = find_term (fn t => is_eq t andalso is_var (lhs t) andalso
                               is_var (rhs t)) g
in
  ASM_CASES_TAC eqn THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
  ASM_SIMP_TAC bool_ss []
end (asl, g)

Theorem swapstr_swapstr[simp] :
    swapstr (swapstr x y u) (swapstr x y v) (swapstr x y s) =
    swapstr x y (swapstr u v s)
Proof
  REWRITE_TAC [swapstr_def] THEN REPEAT simp_cond_tac
QED

Theorem swapstr_comm[simp] :
    swapstr y x s = swapstr x y s
Proof
  SRW_TAC [][swapstr_def] THEN METIS_TAC []
QED

Theorem swapstr_thm[simp] :
    (swapstr x y x = y) /\ (swapstr x y y = x) /\
    (~(x = a) /\ ~(y = a) ==> (swapstr x y a = a))
Proof
  SRW_TAC [][swapstr_def]
QED

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
  Induct THEN ASM_SIMP_TAC (srw_ss()) [FORALL_PROD]);

(* ----------------------------------------------------------------------
    NEW constant
   ---------------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------------
    Primitive definitions on string/name allocations
   ---------------------------------------------------------------------- *)

(* The "width" of a finite set of strings is their maximal nsnd o s2n *)
Definition string_width_def :
    string_width s = MAX_SET (IMAGE (nsnd o s2n) s)
End

Theorem string_width_thm :
    !x s. FINITE s /\ x IN s ==> nsnd (s2n x) <= string_width s
Proof
    rw [string_width_def]
 >> irule MAX_SET_PROPERTY
 >> CONJ_TAC
 >- (MATCH_MP_TAC IMAGE_FINITE >> art [])
 >> rw []
 >> Q.EXISTS_TAC ‘x’ >> art []
QED

(* The primitive ‘alloc’ allocates a ranged list of variables in the row *)
Definition alloc_def :
    alloc r m n = MAP (n2s o npair r) [m ..< n]
End

Theorem alloc_NIL[simp] :
    alloc r n n = []
Proof
    rw [alloc_def]
QED

Theorem alloc_thm :
    !r m n. ALL_DISTINCT (alloc r m n) /\ LENGTH (alloc r m n) = n - m
Proof
    rw [alloc_def]
 >> MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw []
QED

Theorem alloc_prefix :
    !r m n n'. n <= n' ==> alloc r m n <<= alloc r m n'
Proof
    rw [alloc_def]
 >> MATCH_MP_TAC isPREFIX_MAP
 >> MATCH_MP_TAC isPREFIX_listRangeLHI >> art []
QED

(* ----------------------------------------------------------------------
   RNEWS for allocating a row of names excluding a (non-empty) finite set
   ---------------------------------------------------------------------- *)

Definition RNEWS :
    RNEWS r n s = let d = SUC (string_width s) in alloc r d (d + n)
End

Theorem RNEWS_0[simp] :
    RNEWS r 0 s = []
Proof
    rw [RNEWS]
QED

Theorem RNEWS_def :
    !r n s.
        FINITE s ==>
        ALL_DISTINCT (RNEWS r n s) /\ DISJOINT (set (RNEWS r n s)) s /\
        LENGTH (RNEWS r n s) = n
Proof
    rw [RNEWS, alloc_thm]
 >> rw [DISJOINT_ALT', alloc_def, MEM_MAP]
 >> rw [Once DISJ_COMM]
 >> STRONG_DISJ_TAC
 >> MP_TAC (Q.SPECL [‘n2s (r *, y)’, ‘s’] string_width_thm)
 >> rw []
QED

Theorem RNEWS_prefix :
    !r m n s. m <= n ==> RNEWS r m s <<= RNEWS r n s
Proof
    rw [RNEWS, alloc_prefix]
QED

Theorem RNEWS_set :
    !r n s. set (RNEWS r n s) =
            {v | ?j. v = n2s (r *, j) /\
                     string_width s < j /\ j <= string_width s + n}
Proof
    rw [RNEWS, alloc_def, Once EXTENSION, MEM_GENLIST, MEM_MAP]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘y’ >> rw [])
 >> Q.EXISTS_TAC ‘j’ >> rw []
QED

Theorem RNEWS_11 :
    !r1 r2 n1 n2 X. 0 < n1 \/ 0 < n2 ==>
                   (RNEWS r1 n1 X = RNEWS r2 n2 X <=> r1 = r2 /\ n1 = n2)
Proof
    rpt GEN_TAC
 >> DISCH_TAC
 >> reverse EQ_TAC >- rw []
 >> rw [RNEWS, alloc_def, Once LIST_EQ_REWRITE]
 >> fs [EL_MAP]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘0’ >> art []
QED

(* NOTE: if n1 and n2 may take 0, at least we know that ‘n1 = n2’ *)
Theorem RNEWS_11' :
    !r1 r2 n1 n2 X. RNEWS r1 n1 X = RNEWS r2 n2 X ==> n1 = n2
Proof
    rw [RNEWS, alloc_def, Once LIST_EQ_REWRITE]
QED

(* ----------------------------------------------------------------------
    The old NEWS constant for allocating a list of fresh names
   ---------------------------------------------------------------------- *)

(* ‘NEWS n s’ generates n fresh names from the excluded set ‘s’ *)
Overload NEWS = “RNEWS 0”

(* This is the old equivalent definition of FRESH_list_def:
   |- !n s.
        FINITE s ==>
        ALL_DISTINCT (NEWS n s) /\ DISJOINT (set (NEWS n s)) s /\
        LENGTH (NEWS n s) = n
 *)
Theorem NEWS_def = Q.SPEC ‘0’ RNEWS_def

(* |- !m n s. m <= n ==> NEWS m s <<= NEWS n s *)
Theorem NEWS_prefix = Q.SPEC ‘0’ RNEWS_prefix

(* ----------------------------------------------------------------------
    rank and ranks - infinite set of all fresh names of certain ranks
   ---------------------------------------------------------------------- *)

Definition ROW_DEF :
    ROW r = IMAGE (\i. n2s (r *, i)) UNIV
End

Theorem ROW :
    !r. ROW r = {v | ?j. v = n2s (r *, j)}
Proof
    rw [Once EXTENSION, ROW_DEF]
QED

Theorem alloc_SUBSET_ROW :
    !r m n. set (alloc r m n) SUBSET ROW r
Proof
    rw [alloc_def, ROW, SUBSET_DEF, MEM_MAP]
 >> Q.EXISTS_TAC ‘y’ >> rw []
QED

Theorem ROW_DISJOINT :
    !r1 r2. r1 <> r2 ==> DISJOINT (ROW r1) (ROW r2)
Proof
    rw [DISJOINT_ALT, ROW]
 >> rw [n2s_11]
QED

Definition RANK_DEF :
    RANK r = BIGUNION (IMAGE ROW (count r))
End

Theorem RANK :
    !r. RANK r = {v | ?i j. v = n2s (i *, j) /\ i < r}
Proof
    rw [Once EXTENSION, ROW, RANK_DEF]
 >> EQ_TAC >> rw [] >- fs []
 >> Q.EXISTS_TAC ‘{v | ?j. v = n2s (i *, j)}’
 >> rw []
 >> Q.EXISTS_TAC ‘i’ >> rw []
QED

Theorem RANK_0[simp] :
    RANK 0 = {}
Proof
    rw [RANK]
QED

Theorem RANK_MONO :
    !r1 r2. r1 <= r2 ==> RANK r1 SUBSET RANK r2
Proof
    rw [RANK, SUBSET_DEF]
 >> qexistsl_tac [‘i’, ‘j’] >> rw []
QED

Theorem RANK_MONO' :
    !r. RANK r SUBSET RANK (SUC r)
Proof
    Q.X_GEN_TAC ‘r’
 >> MATCH_MP_TAC RANK_MONO >> rw []
QED

Theorem RANK_ROW_DISJOINT :
    !r1 r2 n. r1 <= r2 ==> DISJOINT (RANK r1) (ROW r2)
Proof
    rw [DISJOINT_ALT, ROW, RANK]
 >> fs []
QED

Theorem RANK_ROW_DISJOINT' :
    !r n. DISJOINT (RANK r) (ROW r)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC RANK_ROW_DISJOINT >> rw []
QED

Theorem ROW_SUBSET_RANK :
    !r1 r2. r1 < r2 ==> ROW r1 SUBSET RANK r2
Proof
    rw [SUBSET_DEF, RANK, ROW]
 >> qexistsl_tac [‘r1’, ‘j’] >> art []
QED

Theorem alloc_SUBSET_RANK :
    !r1 r2 m n. r1 < r2 ==> set (alloc r1 m n) SUBSET RANK r2
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘ROW r1’ >> rw [alloc_SUBSET_ROW]
 >> MATCH_MP_TAC ROW_SUBSET_RANK >> art []
QED

Theorem RNEWS_SUBSET_ROW :
    !r n s. FINITE s ==> set (RNEWS r n s) SUBSET ROW r
Proof
    rw [RNEWS_set, SUBSET_DEF, ROW]
 >> Q.EXISTS_TAC ‘j’ >> rw []
QED

Theorem DISJOINT_RNEWS :
    !r1 r2 n1 n2 s1 s2. FINITE s1 /\ FINITE s2 /\ r1 <> r2 ==>
        DISJOINT (set (RNEWS r1 n1 s1)) (set (RNEWS r2 n2 s2))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘ROW r2’ >> rw [RNEWS_SUBSET_ROW]
 >> MATCH_MP_TAC DISJOINT_SUBSET'
 >> Q.EXISTS_TAC ‘ROW r1’ >> rw [RNEWS_SUBSET_ROW]
 >> MATCH_MP_TAC ROW_DISJOINT >> art []
QED

Theorem DISJOINT_RANK_RNEWS :
    !r1 r2 n s.
        FINITE s /\ r1 <= r2 ==> DISJOINT (RANK r1) (set (RNEWS r2 n s))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_SUBSET
 >> Q.EXISTS_TAC ‘ROW r2’
 >> rw [RANK_ROW_DISJOINT, RNEWS_SUBSET_ROW]
QED

(* |- !r1 r2 n s.
        FINITE s /\ r1 <= r2 ==> DISJOINT (set (RNEWS r2 n s)) (RANK r1)
 *)
Theorem DISJOINT_RNEWS_RANK =
    ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_RANK_RNEWS

Theorem DISJOINT_RANK_RNEWS' :
    !r n s. FINITE s ==> DISJOINT (RANK r) (set (RNEWS r n s))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DISJOINT_RANK_RNEWS >> rw []
QED

(* |- !r n s. FINITE s ==> DISJOINT (set (RNEWS r n s)) (RANK r) *)
Theorem DISJOINT_RNEWS_RANK' =
    ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_RANK_RNEWS'

Theorem RNEWS_SUBSET_RANK :
    !r1 r2 n s. FINITE s /\ r1 < r2 ==>
                set (RNEWS r1 n s) SUBSET RANK r2
Proof
    rw [SUBSET_DEF, RNEWS_set, RANK]
 >> qexistsl_tac [‘r1’, ‘j’] >> rw []
QED

val _ = export_theory ();
val _ = html_theory "basic_swap";
