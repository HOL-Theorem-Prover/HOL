(* ------------------------------------------------------------------------- *)
(* List of Range of Numbers                                                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib BasicProvers;

open arithmeticTheory TotalDefn simpLib numSimps numLib listTheory metisLib
     pred_setTheory listSimps dividesTheory;

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val qabbrev_tac = Q.ABBREV_TAC;
val qexists_tac = Q.EXISTS_TAC;
fun simp l = ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) l;
fun fs l = FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) l;
fun rfs l = REV_FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) l;
val rw = SRW_TAC [ARITH_ss];

val _ = new_theory "listRange";

(* ------------------------------------------------------------------------- *)
(* Range Conjunction and Disjunction                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: a <= j /\ j <= a <=> (j = a) *)
(* Proof: trivial by arithmetic. *)
val every_range_sing = store_thm(
  "every_range_sing",
  ``!a j. a <= j /\ j <= a <=> (j = a)``,
  decide_tac);

(* Theorem: a <= b ==>
    ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ !j. a + 1 <= j /\ j <= b ==> f j)) *)
(* Proof:
   If part: !j. a <= j /\ j <= b ==> f j ==>
              f a /\ !j. a + 1 <= j /\ j <= b ==> f j
      This is trivial since a + 1 = SUC a.
   Only-if part: f a /\ !j. a + 1 <= j /\ j <= b ==> f j ==>
                 !j. a <= j /\ j <= b ==> f j
      Note a <= j <=> a = j or a < j      by arithmetic
      If a = j, this is trivial.
      If a < j, then a + 1 <= j, also trivial.
*)
val every_range_cons = store_thm(
  "every_range_cons",
  ``!f a b. a <= b ==>
    ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ !j. a + 1 <= j /\ j <= b ==> f j))``,
  rw[EQ_IMP_THM] >>
  `(a = j) \/ (a < j)` by decide_tac >-
  fs[] >>
  fs[]);

(* Theorem: a <= b ==> ((!j. PRE a <= j /\ j <= b ==> f j) <=> (f (PRE a) /\ !j. a <= j /\ j <= b ==> f j)) *)
(* Proof:
       !j. PRE a <= j /\ j <= b ==> f j
   <=> !j. (PRE a = j \/ a <= j) /\ j <= b ==> f j             by arithmetic
   <=> !j. (j = PRE a ==> f j) /\ a <= j /\ j <= b ==> f j     by RIGHT_AND_OVER_OR, DISJ_IMP_THM
   <=> !j. a <= j /\ j <= b ==> f j /\ f (PRE a)
*)
Theorem every_range_split_head:
  !f a b. a <= b ==>
          ((!j. PRE a <= j /\ j <= b ==> f j) <=> (f (PRE a) /\ !j. a <= j /\ j <= b ==> f j))
Proof
  rpt strip_tac >>
  `!j. PRE a <= j <=> PRE a = j \/ a <= j` by decide_tac >>
  metis_tac[]
QED

(* Theorem: a <= b ==> ((!j. a <= j /\ j <= SUC b ==> f j) <=> (f (SUC b) /\ !j. a <= j /\ j <= b ==> f j)) *)
(* Proof:
       !j. a <= j /\ j <= SUC b ==> f j
   <=> !j. a <= j /\ (j <= b \/ j = SUC b) ==> f j             by arithmetic
   <=> !j. a <= j /\ j <= b ==> f j /\ (j = SUC b ==> f j)     by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> !j. a <= j /\ j <= b ==> f j /\ f (SUC b)
*)
Theorem every_range_split_last:
  !f a b. a <= b ==>
          ((!j. a <= j /\ j <= SUC b ==> f j) <=> (f (SUC b) /\ !j. a <= j /\ j <= b ==> f j))
Proof
  rpt strip_tac >>
  `!j. j <= SUC b <=> j <= b \/ j = SUC b` by decide_tac >>
  metis_tac[]
QED

(* Theorem: a <= b ==> ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ f b /\ !j. a < j /\ j < b ==> f j)) *)
(* Proof:
       !j. a <= j /\ j <= b ==> f j
   <=> !j. (a < j \/ a = j) /\ (j < b \/ j = b) ==> f j                  by arithmetic
   <=> !j. a = j ==> f j /\ j = b ==> f j /\ !j. a < j /\ j < b ==> f j  by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> f a /\ f b /\ !j. a < j /\ j < b ==> f j
*)
Theorem every_range_less_ends:
  !f a b. a <= b ==>
          ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ f b /\ !j. a < j /\ j < b ==> f j))
Proof
  rpt strip_tac >>
  `!m n. m <= n <=> m < n \/ m = n` by decide_tac >>
  metis_tac[]
QED

(* Theorem: a < b /\ f a /\ ~f b ==>
            ?m. a <= m /\ m < b /\ (!j. a <= j /\ j <= m ==> f j) /\ ~f (SUC m) *)
(* Proof:
   Let s = {p | a <= p /\ p < b /\ (!j. a <= j /\ j <= p ==> f j)}
   Pick m = MAX_SET s.
   Note f a ==> a IN s             by every_range_sing
     so s <> {}                    by MEMBER_NOT_EMPTY
   Also s SUBSET (count b)         by SUBSET_DEF
     so FINITE s                   by FINITE_COUNT, SUBSET_FINITE
    ==> m IN s                     by MAX_SET_IN_SET
   Thus a <= m /\ m < b /\ (!j. a <= j /\ j <= m ==> f j)
   It remains to show: ~f (SUC m).
   By contradiction, suppose f (SUC m).
   Since m < b, SUC m <= b.
   But ~f b, so SUC m <> b         by given
   Thus a <= m < SUC m, and SUC m < b,
    and !j. a <= j /\ j <= SUC m ==> f j)
    ==> SUC m IN s                 by every_range_split_last
   Then SUC m <= m                 by X_LE_MAX_SET
   which is impossible             by LESS_SUC
*)
Theorem every_range_span_max:
  !f a b. a < b /\ f a /\ ~f b ==>
          ?m. a <= m /\ m < b /\ (!j. a <= j /\ j <= m ==> f j) /\ ~f (SUC m)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {p | a <= p /\ p < b /\ (!j. a <= j /\ j <= p ==> f j)}` >>
  qabbrev_tac `m = MAX_SET s` >>
  qexists_tac `m` >>
  `a IN s` by fs[every_range_sing, Abbr`s`] >>
  `s SUBSET (count b)` by fs[SUBSET_DEF, Abbr`s`] >>
  `FINITE s /\ s <> {}` by metis_tac[FINITE_COUNT, SUBSET_FINITE, MEMBER_NOT_EMPTY] >>
  `m IN s` by fs[MAX_SET_IN_SET, Abbr`m`] >>
  rfs[Abbr`s`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `s = {p | a <= p /\ p < b /\ (!j. a <= j /\ j <= p ==> f j)}` >>
  `SUC m <> b` by metis_tac[] >>
  `a <= SUC m /\ SUC m < b` by decide_tac >>
  `SUC m IN s` by fs[every_range_split_last, Abbr`s`] >>
  `SUC m <= m` by simp[X_LE_MAX_SET, Abbr`m`] >>
  decide_tac
QED

(* Theorem: a < b /\ ~f a /\ f b ==>
           ?m. a < m /\ m <= b /\ (!j. m <= j /\ j <= b ==> f j) /\ ~f (PRE m) *)
(* Proof:
   Let s = {p | a < p /\ p <= b /\ (!j. p <= j /\ j <= b ==> f j)}
   Pick m = MIN_SET s.
   Note f b ==> b IN s             by every_range_sing
     so s <> {}                    by MEMBER_NOT_EMPTY
    ==> m IN s                     by MIN_SET_IN_SET
   Thus a < m /\ m <= b /\ (!j. m <= j /\ j <= b ==> f j)
   It remains to show: ~f (PRE m).
   By contradiction, suppose f (PRE m).
   Since a < m, a <= PRE m.
   But ~f a, so PRE m <> a         by given
   Thus a < PRE m, and PRE m <= b,
    and !j. PRE m <= j /\ j <= b ==> f j)
    ==> PRE m IN s                 by every_range_split_head
   Then m <= PRE m                 by MIN_SET_PROPERTY
   which is impossible             by PRE_LESS, a < m ==> 0 < m
*)
Theorem every_range_span_min:
  !f a b. a < b /\ ~f a /\ f b ==>
          ?m. a < m /\ m <= b /\ (!j. m <= j /\ j <= b ==> f j) /\ ~f (PRE m)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {p | a < p /\ p <= b /\ (!j. p <= j /\ j <= b ==> f j)}` >>
  qabbrev_tac `m = MIN_SET s` >>
  qexists_tac `m` >>
  `b IN s` by fs[every_range_sing, Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `m IN s` by fs[MIN_SET_IN_SET, Abbr`m`] >>
  rfs[Abbr`s`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `s = {p | a < p /\ p <= b /\ (!j. p <= j /\ j <= b ==> f j)}` >>
  `PRE m <> a` by metis_tac[] >>
  `a < PRE m /\ PRE m <= b` by decide_tac >>
  `PRE m IN s` by fs[every_range_split_head, Abbr`s`] >>
  `m <= PRE m` by simp[MIN_SET_PROPERTY, Abbr`m`] >>
  decide_tac
QED

(* Theorem: ?j. a <= j /\ j <= a <=> (j = a) *)
(* Proof: trivial by arithmetic. *)
val exists_range_sing = store_thm(
  "exists_range_sing",
  ``!a. ?j. a <= j /\ j <= a <=> (j = a)``,
  metis_tac[LESS_EQ_REFL]);

(* Theorem: a <= b ==>
    ((?j. a <= j /\ j <= b /\ f j) <=> (f a \/ ?j. a + 1 <= j /\ j <= b /\ f j)) *)
(* Proof:
   If part: ?j. a <= j /\ j <= b /\ f j ==>
              f a \/ ?j. a + 1 <= j /\ j <= b /\ f j
      This is trivial since a + 1 = SUC a.
   Only-if part: f a /\ ?j. a + 1 <= j /\ j <= b /\ f j ==>
                 ?j. a <= j /\ j <= b /\ f j
      Note a <= j <=> a = j or a < j      by arithmetic
      If a = j, this is trivial.
      If a < j, then a + 1 <= j, also trivial.
*)
val exists_range_cons = store_thm(
  "exists_range_cons",
  ``!f a b. a <= b ==>
    ((?j. a <= j /\ j <= b /\ f j) <=> (f a \/ ?j. a + 1 <= j /\ j <= b /\ f j))``,
  rw[EQ_IMP_THM] >| [
    `(a = j) \/ (a < j)` by decide_tac >-
    fs[] >>
    `a + 1 <= j` by decide_tac >>
    metis_tac[],
    metis_tac[LESS_EQ_REFL],
    `a <= j` by decide_tac >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* List Range                                                                *)
(* ------------------------------------------------------------------------- *)

val listRangeINC_def = Define`
  listRangeINC m n = GENLIST (\i. m + i) (n + 1 - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRangeINC" }

val listRangeINC_SING = store_thm(
  "listRangeINC_SING",
  ``[m .. m] = [m]``,
  SIMP_TAC (srw_ss()) [listRangeINC_def]);
val _ = export_rewrites ["listRangeINC_SING"]

val MEM_listRangeINC = store_thm(
  "MEM_listRangeINC",
  ``MEM x [m .. n] <=> m <= x /\ x <= n``,
  SIMP_TAC (srw_ss() ++ ARITH_ss)
           [listRangeINC_def, MEM_GENLIST, EQ_IMP_THM] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRangeINC"]

val listRangeINC_CONS = store_thm(
  "listRangeINC_CONS",
  ``m <= n ==> ([m .. n] = m :: [m+1 .. n])``,
  SIMP_TAC (srw_ss()) [listRangeINC_def] THEN STRIP_TAC THEN
  `(n + 1 - m = SUC (n - m)) /\ (n + 1 - (m + 1) = n - m)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [GENLIST_CONS, GENLIST_FUN_EQ]);

val listRangeINC_EMPTY = store_thm(
  "listRangeINC_EMPTY",
  ``n < m ==> ([m .. n] = [])``,
  SRW_TAC [][listRangeINC_def] THEN
  `n + 1 - m = 0` by DECIDE_TAC THEN SRW_TAC[][]);

val listRangeLHI_def = Define`
  listRangeLHI m n = GENLIST (\i. m + i) (n - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..<",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRangeLHI" }

val listRangeLHI_EQ = store_thm(
  "listRangeLHI_EQ",
  ``[m ..< m] = []``,
  SRW_TAC[][listRangeLHI_def]);
val _ = export_rewrites ["listRangeLHI_EQ"]

val MEM_listRangeLHI = store_thm(
  "MEM_listRangeLHI",
  ``MEM x [m ..< n] <=> m <= x /\ x < n``,
  SRW_TAC[ARITH_ss][listRangeLHI_def, MEM_GENLIST, EQ_IMP_THM] THEN
  Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRangeLHI"]

val listRangeLHI_EMPTY = store_thm(
  "listRangeLHI_EMPTY",
  ``hi <= lo ==> ([lo ..< hi] = [])``,
  SRW_TAC[][listRangeLHI_def] THEN
  `hi - lo = 0` by DECIDE_TAC THEN
  SRW_TAC[][]);

val listRangeLHI_CONS = store_thm(
  "listRangeLHI_CONS",
  ``lo < hi ==> ([lo ..< hi] = lo :: [lo + 1 ..< hi])``,
  SRW_TAC[][listRangeLHI_def] THEN
  `hi - lo = SUC (hi - (lo + 1))` by DECIDE_TAC THEN
  SRW_TAC[ARITH_ss][listTheory.GENLIST_CONS, listTheory.GENLIST_FUN_EQ]);

val listRangeLHI_ALL_DISTINCT = store_thm(
  "listRangeLHI_ALL_DISTINCT",
  ``ALL_DISTINCT [lo ..< hi]``,
  Induct_on `hi - lo` THEN SRW_TAC[][listRangeLHI_EMPTY] THEN
  `lo < hi` by DECIDE_TAC THEN
  SRW_TAC[ARITH_ss][listRangeLHI_CONS]);
val _ = export_rewrites ["listRangeLHI_ALL_DISTINCT"]

val LENGTH_listRangeLHI = store_thm(
  "LENGTH_listRangeLHI",
  ``LENGTH [lo ..< hi] = hi - lo``,
  SRW_TAC[][listRangeLHI_def]);
val _ = export_rewrites ["LENGTH_listRangeLHI"]

val EL_listRangeLHI = store_thm(
  "EL_listRangeLHI",
  ``lo + i < hi ==> (EL i [lo ..< hi] = lo + i)``,
  Q.ID_SPEC_TAC `i` THEN Induct_on `hi - lo` THEN
  SRW_TAC[ARITH_ss][listRangeLHI_EMPTY] THEN
  `lo < hi` by DECIDE_TAC THEN
  SRW_TAC[ARITH_ss][listRangeLHI_CONS] THEN
  Cases_on `i` THEN
  SRW_TAC[ARITH_ss][]);

(* Theorem: [m .. n] = [m ..< SUC n] *)
(* Proof:
   = [m .. n]
   = GENLIST (\i. m + i) (n + 1 - m)     by listRangeINC_def
   = [m ..< (n + 1)]                     by listRangeLHI_def
   = [m ..< SUC n]                       by ADD1
*)
Theorem listRangeINC_to_LHI:
  !m n. [m .. n] = [m ..< SUC n]
Proof
  rw[listRangeLHI_def, listRangeINC_def, ADD1]
QED

(* Theorem: set [1 .. n] = IMAGE SUC (count n) *)
(* Proof:
       x IN set [1 .. n]
   <=> 1 <= x /\ x <= n                  by listRangeINC_MEM
   <=> 0 < x /\ PRE x < n                by arithmetic
   <=> 0 < SUC (PRE x) /\ PRE x < n      by SUC_PRE, 0 < x
   <=> x IN IMAGE SUC (count n)          by IN_COUNT, IN_IMAGE
*)
Theorem listRangeINC_SET:
  !n. set [1 .. n] = IMAGE SUC (count n)
Proof
  rw[EXTENSION, EQ_IMP_THM] >>
  `0 < x /\ PRE x < n` by decide_tac >>
  metis_tac[SUC_PRE]
QED

(* Theorem: LENGTH [m .. n] = n + 1 - m *)
(* Proof:
     LENGTH [m .. n]
   = LENGTH (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = n + 1 - m                                 by LENGTH_GENLIST
*)
val listRangeINC_LEN = store_thm(
  "listRangeINC_LEN",
  ``!m n. LENGTH [m .. n] = n + 1 - m``,
  rw[listRangeINC_def]);

(* Theorem: ([m .. n] = []) <=> (n + 1 <= m) *)
(* Proof:
              [m .. n] = []
   <=> LENGTH [m .. n] = 0         by LENGTH_NIL
   <=>       n + 1 - m = 0         by listRangeINC_LEN
   <=>          n + 1 <= m         by arithmetic
*)
val listRangeINC_NIL = store_thm(
  "listRangeINC_NIL",
  ``!m n. ([m .. n] = []) <=> (n + 1 <= m)``,
  metis_tac[listRangeINC_LEN, LENGTH_NIL, DECIDE``(n + 1 - m = 0) <=> (n + 1 <= m)``]);

(* Rename a theorem *)
val listRangeINC_MEM = save_thm("listRangeINC_MEM",
    MEM_listRangeINC |> GEN ``x:num`` |> GEN ``n:num`` |> GEN ``m:num``);
(*
val listRangeINC_MEM = |- !m n x. MEM x [m .. n] <=> m <= x /\ x <= n: thm
*)

(*
EL_listRangeLHI
|- lo + i < hi ==> EL i [lo ..< hi] = lo + i
*)

(* Theorem: m + i <= n ==> (EL i [m .. n] = m + i) *)
(* Proof: by listRangeINC_def *)
val listRangeINC_EL = store_thm(
  "listRangeINC_EL",
  ``!m n i. m + i <= n ==> (EL i [m .. n] = m + i)``,
  rw[listRangeINC_def]);

(* Theorem: EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. MEM x [m .. n] ==> P x      by EVERY_MEM
   <=> !x. m <= x /\ x <= n ==> P x    by MEM_listRangeINC
*)
val listRangeINC_EVERY = store_thm(
  "listRangeINC_EVERY",
  ``!P m n. EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeINC]);


(* Theorem: EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. MEM x [m .. n] /\ P x      by EXISTS_MEM
   <=> ?x. m <= x /\ x <= n /\ P e    by MEM_listRangeINC
*)
val listRangeINC_EXISTS = store_thm(
  "listRangeINC_EXISTS",
  ``!P m n. EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x``,
  metis_tac[EXISTS_MEM, MEM_listRangeINC]);

(* Theorem: EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n]) *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. m <= x /\ x <= n ==> P x        by listRangeINC_EVERY
   <=> ~(?x. m <= x /\ x <= n /\ ~(P x))   by negation
   <=> ~(EXISTS ($~ o P) [m .. m])         by listRangeINC_EXISTS
*)
val listRangeINC_EVERY_EXISTS = store_thm(
  "listRangeINC_EVERY_EXISTS",
  ``!P m n. EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n])``,
  rw[listRangeINC_EVERY, listRangeINC_EXISTS]);

(* Theorem: EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n]) *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. m <= x /\ x <= m /\ P x           by listRangeINC_EXISTS
   <=> ~(!x. m <= x /\ x <= n ==> ~(P x))    by negation
   <=> ~(EVERY ($~ o P) [m .. n])            by listRangeINC_EVERY
*)
val listRangeINC_EXISTS_EVERY = store_thm(
  "listRangeINC_EXISTS_EVERY",
  ``!P m n. EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n])``,
  rw[listRangeINC_EXISTS, listRangeINC_EVERY]);

(* Theorem: m <= n + 1 ==> ([m .. (n + 1)] = SNOC (n + 1) [m .. n]) *)
(* Proof:
     [m .. (n + 1)]
   = GENLIST (\i. m + i) ((n + 1) + 1 - m)                      by listRangeINC_def
   = GENLIST (\i. m + i) (1 + (n + 1 - m))                      by arithmetic
   = GENLIST (\i. m + i) (n + 1 - m) ++ GENLIST (\t. (\i. m + i) (t + n + 1 - m)) 1  by GENLIST_APPEND
   = [m .. n] ++ GENLIST (\t. (\i. m + i) (t + n + 1 - m)) 1    by listRangeINC_def
   = [m .. n] ++ [(\t. (\i. m + i) (t + n + 1 - m)) 0]          by GENLIST_1
   = [m .. n] ++ [m + n + 1 - m]                                by function evaluation
   = [m .. n] ++ [n + 1]                                        by arithmetic
   = SNOC (n + 1) [m .. n]                                      by SNOC_APPEND
*)
val listRangeINC_SNOC = store_thm(
  "listRangeINC_SNOC",
  ``!m n. m <= n + 1 ==> ([m .. (n + 1)] = SNOC (n + 1) [m .. n])``,
  rw[listRangeINC_def] >>
  `(n + 2 - m = 1 + (n + 1 - m)) /\ (n + 1 - m + m = n + 1)` by decide_tac >>
  rw_tac std_ss[GENLIST_APPEND, GENLIST_1]);

(* Theorem: m <= n + 1 ==> (FRONT [m .. (n + 1)] = [m .. n]) *)
(* Proof:
     FRONT [m .. (n + 1)]
   = FRONT (SNOC (n + 1) [m .. n]))    by listRangeINC_SNOC
   = [m .. n]                          by FRONT_SNOC
*)
Theorem listRangeINC_FRONT:
  !m n. m <= n + 1 ==> (FRONT [m .. (n + 1)] = [m .. n])
Proof
  simp[listRangeINC_SNOC, FRONT_SNOC]
QED

(* Theorem: m <= n ==> (LAST [m .. n] = n) *)
(* Proof:
   Let ls = [m .. n]
   Note ls <> []                   by listRangeINC_NIL
     so LAST ls
      = EL (PRE (LENGTH ls)) ls    by LAST_EL
      = EL (PRE (n + 1 - m)) ls    by listRangeINC_LEN
      = EL (n - m) ls              by arithmetic
      = n                          by listRangeINC_EL
   Or
      LAST [m .. n]
    = LAST (GENLIST (\i. m + i) (n + 1 - m))   by listRangeINC_def
    = LAST (GENLIST (\i. m + i) (SUC (n - m))  by arithmetic, m <= n
    = (\i. m + i) (n - m)                      by GENLIST_LAST
    = m + (n - m)                              by function application
    = n                                        by m <= n
   Or
    If n = 0, then m <= 0 means m = 0.
      LAST [0 .. 0] = LAST [0] = 0 = n   by LAST_DEF
    Otherwise n = SUC k.
      LAST [m .. n]
    = LAST (SNOC n [m .. k])             by listRangeINC_SNOC, ADD1
    = n                                  by LAST_SNOC
*)
Theorem listRangeINC_LAST:
  !m n. m <= n ==> (LAST [m .. n] = n)
Proof
  rpt strip_tac >>
  Cases_on `n` >-
  fs[] >>
  metis_tac[listRangeINC_SNOC, LAST_SNOC, ADD1]
QED

(* Theorem: REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n] *)
(* Proof:
     REVERSE [m .. n]
   = REVERSE (GENLIST (\i. m + i) (n + 1 - m))              by listRangeINC_def
   = GENLIST (\x. (\i. m + i) (PRE (n + 1 - m) - x)) (n + 1 - m)   by REVERSE_GENLIST
   = GENLIST (\x. (\i. m + i) (n - m - x)) (n + 1 - m)      by PRE
   = GENLIST (\x. (m + n - m - x) (n + 1 - m)               by function application
   = GENLIST (\x. n - x) (n + 1 - m)                        by arithmetic

     MAP (\x. n - x + m) [m .. n]
   = MAP (\x. n - x + m) (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = GENLIST ((\x. n - x + m) o (\i. m + i)) (n + 1 - m)    by MAP_GENLIST
   = GENLIST (\i. n - (m + i) + m) (n + 1 - m)              by function composition
   = GENLIST (\i. n - i) (n + 1 - m)                        by arithmetic
*)
val listRangeINC_REVERSE = store_thm(
  "listRangeINC_REVERSE",
  ``!m n. REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n]``,
  rpt strip_tac >>
  `(\m'. PRE (n + 1 - m) - m' + m) = ((\x. n - x + m) o (\i. i + m))`
      by rw[FUN_EQ_THM, combinTheory.o_THM] >>
  rw[listRangeINC_def, REVERSE_GENLIST, MAP_GENLIST]);

(* Theorem: REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n] *)
(* Proof:
    REVERSE (MAP f [m .. n])
  = MAP f (REVERSE [m .. n])                by MAP_REVERSE
  = MAP f (MAP (\x. n - x + m) [m .. n])    by listRangeINC_REVERSE
  = MAP (f o (\x. n - x + m)) [m .. n]      by MAP_MAP_o
*)
val listRangeINC_REVERSE_MAP = store_thm(
  "listRangeINC_REVERSE_MAP",
  ``!f m n. REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n]``,
  metis_tac[MAP_REVERSE, listRangeINC_REVERSE, MAP_MAP_o]);

(* Theorem: MAP f [(m + 1) .. (n + 1)] = MAP (f o SUC) [m .. n] *)
(* Proof:
   Note (\i. (m + 1) + i) = SUC o (\i. (m + i))                 by FUN_EQ_THM
     MAP f [(m + 1) .. (n + 1)]
   = MAP f (GENLIST (\i. (m + 1) + i) ((n + 1) + 1 - (m + 1)))  by listRangeINC_def
   = MAP f (GENLIST (\i. (m + 1) + i) (n + 1 - m))              by arithmetic
   = MAP f (GENLIST (SUC o (\i. (m + i))) (n + 1 - m))          by above
   = MAP (f o SUC) (GENLIST (\i. (m + i)) (n + 1 - m))          by MAP_GENLIST
   = MAP (f o SUC) [m .. n]                                     by listRangeINC_def
*)
val listRangeINC_MAP_SUC = store_thm(
  "listRangeINC_MAP_SUC",
  ``!f m n. MAP f [(m + 1) .. (n + 1)] = MAP (f o SUC) [m .. n]``,
  rpt strip_tac >>
  `(\i. (m + 1) + i) = SUC o (\i. (m + i))` by rw[FUN_EQ_THM] >>
  rw[listRangeINC_def, MAP_GENLIST]);

(* Theorem: a <= b /\ b <= c ==> ([a .. b] ++ [(b + 1) .. c] = [a .. c]) *)
(* Proof:
   By listRangeINC_def, this is to show:
      GENLIST (\i. a + i) (b + 1 - a) ++ GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\i. a + i) (c + 1 - a)
   Let f = \i. a + i.
   Note (\t. f (t + (b + 1 - a))) = (\i. b + (i + 1))     by FUN_EQ_THM
   Thus GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\t. f (t + (b + 1 - a))) (c - b)  by GENLIST_FUN_EQ
   Now (c - b) + (b + 1 - a) = c + 1 - a                   by a <= b /\ b <= c
   The result follows                                      by GENLIST_APPEND
*)
val listRangeINC_APPEND = store_thm(
  "listRangeINC_APPEND",
  ``!a b c. a <= b /\ b <= c ==> ([a .. b] ++ [(b + 1) .. c] = [a .. c])``,
  rw[listRangeINC_def] >>
  qabbrev_tac `f = \i. a + i` >>
  `(\t. f (t + (b + 1 - a))) = (\i. b + (i + 1))` by rw[FUN_EQ_THM, Abbr`f`] >>
  `GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\t. f (t + (b + 1 - a))) (c - b)` by rw[GSYM GENLIST_FUN_EQ] >>
  `(c - b) + (b + 1 - a) = c + 1 - a` by decide_tac >>
  metis_tac[GENLIST_APPEND]);

(* Theorem: SUM [m .. n] = SUM [1 .. n] - SUM [1 .. (m - 1)] *)
(* Proof:
   If m = 0,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           SUM [0 .. n]
         = SUM (0::[1 .. n])              by listRangeINC_CONS
         = 0 + SUM [1 .. n]               by SUM_CONS
         = SUM [1 .. n] - 0               by arithmetic
         = SUM [1 .. n] - SUM []          by SUM_NIL
   If m = 1,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           SUM [1 .. n]
         = SUM [1 .. n] - 0               by arithmetic
         = SUM [1 .. n] - SUM []          by SUM_NIL
   Otherwise 1 < m, or 1 <= m - 1.
   If n < m,
      Then SUM [m .. n] = 0               by listRangeINC_EMPTY
      If n = 0,
         Then SUM [1 .. 0] = 0            by listRangeINC_EMPTY
          and 0 - SUM [1 .. (m - 1)] = 0  by integer subtraction
      If n <> 0,
         Then 1 <= n /\ n <= m - 1        by arithmetic
          ==> [1 .. m - 1] =
              [1 .. n] ++ [(n + 1) .. (m - 1)]         by listRangeINC_APPEND
           or SUM [1 .. m - 1]
            = SUM [1 .. n] + SUM [(n + 1) .. (m - 1)]  by SUM_APPEND
         Thus SUM [1 .. n] - SUM [1 .. m - 1] = 0      by subtraction
   If ~(n < m), then m <= n.
      Note m - 1 < n /\ (m - 1 + 1 = m)                by arithmetic
      Thus [1 .. n] = [1 .. (m - 1)] ++ [m .. n]       by listRangeINC_APPEND
        or SUM [1 .. n]
         = SUM [1 .. (m - 1)] + SUM [m .. n]           by SUM_APPEND
      The result follows                               by subtraction
*)
val listRangeINC_SUM = store_thm(
  "listRangeINC_SUM",
  ``!m n. SUM [m .. n] = SUM [1 .. n] - SUM [1 .. (m - 1)]``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[listRangeINC_EMPTY, listRangeINC_CONS] >>
  Cases_on `m = 1` >-
  rw[listRangeINC_EMPTY] >>
  Cases_on `n < m` >| [
    Cases_on `n = 0` >-
    rw[listRangeINC_EMPTY] >>
    `1 <= n /\ n <= m - 1` by decide_tac >>
    `[1 .. m - 1] = [1 .. n] ++ [(n + 1) .. (m - 1)]` by rw[listRangeINC_APPEND] >>
    `SUM [1 .. m - 1] = SUM [1 .. n] + SUM [(n + 1) .. (m - 1)]` by rw[GSYM SUM_APPEND] >>
    `SUM [m .. n] = 0` by rw[listRangeINC_EMPTY] >>
    decide_tac,
    `1 <= m - 1 /\ m - 1 <= n /\ (m - 1 + 1 = m)` by decide_tac >>
    `[1 .. n] = [1 .. (m - 1)] ++ [m .. n]` by metis_tac[listRangeINC_APPEND] >>
    `SUM [1 .. n] = SUM [1 .. (m - 1)] + SUM [m .. n]` by rw[GSYM SUM_APPEND] >>
    decide_tac
  ]);

(* Theorem: [1 .. n] = GENLIST SUC n *)
(* Proof: by listRangeINC_def *)
val listRangeINC_1_n = store_thm(
  "listRangeINC_1_n",
  ``!n. [1 .. n] = GENLIST SUC n``,
  rpt strip_tac >>
  `(\i. i + 1) = SUC` by rw[FUN_EQ_THM] >>
  rw[listRangeINC_def]);

(* Theorem: MAP f [1 .. n] = GENLIST (f o SUC) n *)
(* Proof:
     MAP f [1 .. n]
   = MAP f (GENLIST SUC n)     by listRangeINC_1_n
   = GENLIST (f o SUC) n       by MAP_GENLIST
*)
val listRangeINC_MAP = store_thm(
  "listRangeINC_MAP",
  ``!f n. MAP f [1 .. n] = GENLIST (f o SUC) n``,
  rw[listRangeINC_1_n, MAP_GENLIST]);

(* Theorem: SUM (MAP f [1 .. (SUC n)]) = f (SUC n) + SUM (MAP f [1 .. n]) *)
(* Proof:
      SUM (MAP f [1 .. (SUC n)])
    = SUM (MAP f (SNOC (SUC n) [1 .. n]))       by listRangeINC_SNOC
    = SUM (SNOC (f (SUC n)) (MAP f [1 .. n]))   by MAP_SNOC
    = f (SUC n) + SUM (MAP f [1 .. n])          by SUM_SNOC
*)
val listRangeINC_SUM_MAP = store_thm(
  "listRangeINC_SUM_MAP",
  ``!f n. SUM (MAP f [1 .. (SUC n)]) = f (SUC n) + SUM (MAP f [1 .. n])``,
  rw[listRangeINC_SNOC, MAP_SNOC, SUM_SNOC, ADD1]);

(* Theorem: m < j /\ j <= n ==> [m .. n] = [m .. j-1] ++ j::[j+1 .. n] *)
(* Proof:
   Note m < j implies m <= j-1.
     [m .. n]
   = [m .. j-1] ++ [j .. n]        by listRangeINC_APPEND, m <= j-1
   = [m .. j-1] ++ j::[j+1 .. n]   by listRangeINC_CONS, j <= n
*)
Theorem listRangeINC_SPLIT:
  !m n j. m < j /\ j <= n ==> [m .. n] = [m .. j-1] ++ j::[j+1 .. n]
Proof
  rpt strip_tac >>
  `m <= j - 1 /\ j - 1 <= n /\ (j - 1) + 1 = j` by decide_tac >>
  `[m .. n] = [m .. j-1] ++ [j .. n]` by metis_tac[listRangeINC_APPEND] >>
  simp[listRangeINC_CONS]
QED

(* Theorem: [m ..< (n + 1)] = [m .. n] *)
(* Proof:
     [m ..< (n + 1)]
   = GENLIST (\i. m + i) (n + 1 - m)     by listRangeLHI_def
   = [m .. n]                            by listRangeINC_def
*)
Theorem listRangeLHI_to_INC:
  !m n. [m ..< (n + 1)] = [m .. n]
Proof
  rw[listRangeLHI_def, listRangeINC_def]
QED

(* Theorem: set [0 ..< n] = count n *)
(* Proof:
       x IN set [0 ..< n]
   <=> 0 <= x /\ x < n         by listRangeLHI_MEM
   <=> x < n                   by arithmetic
   <=> x IN count n            by IN_COUNT
*)
Theorem listRangeLHI_SET:
  !n. set [0 ..< n] = count n
Proof
  simp[EXTENSION]
QED

(* Theorem alias *)
Theorem  listRangeLHI_LEN = LENGTH_listRangeLHI |> GEN_ALL |> SPEC ``m:num`` |> SPEC ``n:num`` |> GEN_ALL;
(* val listRangeLHI_LEN = |- !n m. LENGTH [m ..< n] = n - m: thm *)

(* Theorem: ([m ..< n] = []) <=> n <= m *)
(* Proof:
   If n = 0, LHS = T, RHS = T    hence true.
   If n <> 0, then n = SUC k     by num_CASES
       [m ..< n] = []
   <=> [m ..< SUC k] = []        by n = SUC k
   <=> [m .. k] = []             by listRangeLHI_to_INC
   <=> k + 1 <= m                by listRangeINC_NIL
   <=>     n <= m                by ADD1
*)
val listRangeLHI_NIL = store_thm(
  "listRangeLHI_NIL",
  ``!m n. ([m ..< n] = []) <=> n <= m``,
  rpt strip_tac >>
  Cases_on `n` >-
  rw[listRangeLHI_def] >>
  rw[listRangeLHI_to_INC, listRangeINC_NIL, ADD1]);

(* Theorem: MEM x [m ..< n] <=> m <= x /\ x < n *)
(* Proof: by MEM_listRangeLHI *)
val listRangeLHI_MEM = store_thm(
  "listRangeLHI_MEM",
  ``!m n x. MEM x [m ..< n] <=> m <= x /\ x < n``,
  rw[MEM_listRangeLHI]);

(* Theorem: m + i < n ==> EL i [m ..< n] = m + i *)
(* Proof: EL_listRangeLHI *)
val listRangeLHI_EL = store_thm(
  "listRangeLHI_EL",
  ``!m n i. m + i < n ==> (EL i [m ..< n] = m + i)``,
  rw[EL_listRangeLHI]);

(* Theorem: EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x *)
(* Proof:
       EVERY P [m ..< n]
   <=> !x. MEM x [m ..< n] ==> P e      by EVERY_MEM
   <=> !x. m <= x /\ x < n ==> P e    by MEM_listRangeLHI
*)
val listRangeLHI_EVERY = store_thm(
  "listRangeLHI_EVERY",
  ``!P m n. EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeLHI]);

(* Theorem: m <= n ==> ([m ..< n + 1] = SNOC n [m ..< n]) *)
(* Proof:
   If n = 0,
      Then m = 0               by m <= n
      LHS = [0 ..< 1] = [0]
      RHS = SNOC 0 [0 ..< 0]
          = SNOC 0 []          by listRangeLHI_def
          = [0] = LHS          by SNOC
   If n <> 0,
      Then n = (n - 1) + 1     by arithmetic
       [m ..< n + 1]
     = [m .. n]                by listRangeLHI_to_INC
     = SNOC n [m .. n - 1]     by listRangeINC_SNOC, m <= (n - 1) + 1
     = SNOC n [m ..< n]        by listRangeLHI_to_INC
*)
val listRangeLHI_SNOC = store_thm(
  "listRangeLHI_SNOC",
  ``!m n. m <= n ==> ([m ..< n + 1] = SNOC n [m ..< n])``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `m = 0` by decide_tac >>
    rw[listRangeLHI_def],
    `n = (n - 1) + 1` by decide_tac >>
    `[m ..< n + 1] = [m .. n]` by rw[listRangeLHI_to_INC] >>
    `_ = SNOC n [m .. n - 1]` by metis_tac[listRangeINC_SNOC] >>
    `_ = SNOC n [m ..< n]` by rw[GSYM listRangeLHI_to_INC] >>
    rw[]
  ]);

(* Theorem: m <= n ==> (FRONT [m .. < n + 1] = [m .. <n]) *)
(* Proof:
     FRONT [m ..< n + 1]
   = FRONT (SNOC n [m ..< n]))     by listRangeLHI_SNOC
   = [m ..< n]                     by FRONT_SNOC
*)
Theorem listRangeLHI_FRONT:
  !m n. m <= n ==> (FRONT [m ..< n + 1] = [m ..< n])
Proof
  simp[listRangeLHI_SNOC, FRONT_SNOC]
QED

(* Theorem: m <= n ==> (LAST [m ..< n + 1] = n) *)
(* Proof:
      LAST [m ..< n + 1]
    = LAST (SNOC n [m ..< n])      by listRangeLHI_SNOC
    = n                            by LAST_SNOC
*)
Theorem listRangeLHI_LAST:
  !m n. m <= n ==> (LAST [m ..< n + 1] = n)
Proof
  simp[listRangeLHI_SNOC, LAST_SNOC]
QED

(* Theorem: REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n] *)
(* Proof:
   If n = 0,
      LHS = REVERSE []            by listRangeLHI_def
          = []                    by REVERSE_DEF
          = MAP f [] = RHS        by MAP
   If n <> 0,
      Then n = k + 1 for some k   by num_CASES, ADD1
        REVERSE [m ..< n]
      = REVERSE [m .. k]                   by listRangeLHI_to_INC
      = MAP (\x. k - x + m) [m .. k]       by listRangeINC_REVERSE
      = MAP (\x. n - 1 - x + m) [m ..< n]  by listRangeLHI_to_INC
*)
val listRangeLHI_REVERSE = store_thm(
  "listRangeLHI_REVERSE",
  ``!m n. REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n]``,
  rpt strip_tac >>
  Cases_on `n` >-
  rw[listRangeLHI_def] >>
  `REVERSE [m ..< SUC n'] = REVERSE [m .. n']` by rw[listRangeLHI_to_INC, ADD1] >>
  `_ = MAP (\x. n' - x + m) [m .. n']` by rw[listRangeINC_REVERSE] >>
  `_ = MAP (\x. n' - x + m) [m ..< (SUC n')]` by rw[GSYM listRangeLHI_to_INC, ADD1] >>
  rw[]);

(* Theorem: REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n] *)
(* Proof:
    REVERSE (MAP f [m ..< n])
  = MAP f (REVERSE [m ..< n])                    by MAP_REVERSE
  = MAP f (MAP (\x. n - 1 - x + m) [m ..< n])    by listRangeLHI_REVERSE
  = MAP (f o (\x. n - 1 - x + m)) [m ..< n]      by MAP_MAP_o
*)
val listRangeLHI_REVERSE_MAP = store_thm(
  "listRangeLHI_REVERSE_MAP",
  ``!f m n. REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n]``,
  metis_tac[MAP_REVERSE, listRangeLHI_REVERSE, MAP_MAP_o]);

(* Theorem: MAP f [(m + 1) ..< (n + 1)] = MAP (f o SUC) [m ..< n] *)
(* Proof:
   Note (\i. (m + 1) + i) = SUC o (\i. (m + i))             by FUN_EQ_THM
     MAP f [(m + 1) ..< (n + 1)]
   = MAP f (GENLIST (\i. (m + 1) + i) ((n + 1) - (m + 1)))  by listRangeLHI_def
   = MAP f (GENLIST (\i. (m + 1) + i) (n - m))              by arithmetic
   = MAP f (GENLIST (SUC o (\i. (m + i))) (n - m))          by above
   = MAP (f o SUC) (GENLIST (\i. (m + i)) (n - m))          by MAP_GENLIST
   = MAP (f o SUC) [m ..< n]                                by listRangeLHI_def
*)
val listRangeLHI_MAP_SUC = store_thm(
  "listRangeLHI_MAP_SUC",
  ``!f m n. MAP f [(m + 1) ..< (n + 1)] = MAP (f o SUC) [m ..< n]``,
  rpt strip_tac >>
  `(\i. (m + 1) + i) = SUC o (\i. (m + i))` by rw[FUN_EQ_THM] >>
  rw[listRangeLHI_def, MAP_GENLIST]);

(* Theorem: a <= b /\ b <= c ==> [a ..< b] ++ [b ..< c] = [a ..< c] *)
(* Proof:
   If a = b,
       LHS = [a ..< a] ++ [a ..< c]
           = [] ++ [a ..< c]        by listRangeLHI_def
           = [a ..< c] = RHS        by APPEND
   If a <> b,
      Then a < b,                   by a <= b
        so b <> 0, and c <> 0       by b <= c
      Let b = b' + 1, c = c' + 1    by num_CASES, ADD1
      Then a <= b' /\ b' <= c.
        [a ..< b] ++ [b ..< c]
      = [a .. b'] ++ [b' + 1 .. c']   by listRangeLHI_to_INC
      = [a .. c']                     by listRangeINC_APPEND
      = [a ..< c]                     by listRangeLHI_to_INC
*)
val listRangeLHI_APPEND = store_thm(
  "listRangeLHI_APPEND",
  ``!a b c. a <= b /\ b <= c ==> ([a ..< b] ++ [b ..< c] = [a ..< c])``,
  rpt strip_tac >>
  `(a = b) \/ (a < b)` by decide_tac >-
  rw[listRangeLHI_def] >>
  `b <> 0 /\ c <> 0` by decide_tac >>
  `?b' c'. (b = b' + 1) /\ (c = c' + 1)` by metis_tac[num_CASES, ADD1] >>
  `a <= b' /\ b' <= c` by decide_tac >>
  `[a ..< b] ++ [b ..< c] = [a .. b'] ++ [b' + 1 .. c']` by rw[listRangeLHI_to_INC] >>
  `_ = [a .. c']` by rw[listRangeINC_APPEND] >>
  `_ = [a ..< c]` by rw[GSYM listRangeLHI_to_INC] >>
  rw[]);

(* Theorem: SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m] *)
(* Proof:
   If n = 0,
      LHS = SUM [m ..< 0] = SUM [] = 0        by listRangeLHI_EMPTY
      RHS = SUM [1 ..< 0] - SUM [1 ..< m]
          = SUM [] - SUM [1 ..< m]            by listRangeLHI_EMPTY
          = 0 - SUM [1 ..< m] = 0 = LHS       by integer subtraction
   If m = 0,
      LHS = SUM [0 ..< n]
          = SUM (0 :: [1 ..< n])              by listRangeLHI_CONS
          = 0 + SUM [1 ..< n]                 by SUM
          = SUM [1 ..< n]                     by arithmetic
      RHS = SUM [1 ..< n] - SUM [1 ..< 0]     by integer subtraction
          = SUM [1 ..< n] - SUM []            by listRangeLHI_EMPTY
          = SUM [1 ..< n] - 0                 by SUM
          = LHS
   Otherwise,
      n <> 0, and m <> 0.
      Let n = n' + 1, m = m' + 1              by num_CASES, ADD1
         SUM [m ..< n]
       = SUM [m .. n']                        by listRangeLHI_to_INC
       = SUM [1 .. n'] - SUM [1 .. m - 1]     by listRangeINC_SUM
       = SUM [1 .. n'] - SUM [1 .. m']        by m' = m - 1
       = SUM [1 ..< n] - SUM [1 ..< m]        by listRangeLHI_to_INC
*)
val listRangeLHI_SUM = store_thm(
  "listRangeLHI_SUM",
  ``!m n. SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m]``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[listRangeLHI_EMPTY] >>
  Cases_on `m = 0` >-
  rw[listRangeLHI_EMPTY, listRangeLHI_CONS] >>
  `?n' m'. (n = n' + 1) /\ (m = m' + 1)` by metis_tac[num_CASES, ADD1] >>
  `SUM [m ..< n] = SUM [m .. n']` by rw[listRangeLHI_to_INC] >>
  `_ = SUM [1 .. n'] - SUM [1 .. m - 1]` by rw[GSYM listRangeINC_SUM] >>
  `_ = SUM [1 .. n'] - SUM [1 .. m']` by rw[] >>
  `_ = SUM [1 ..< n] - SUM [1 ..< m]` by rw[GSYM listRangeLHI_to_INC] >>
  rw[]);

(* Theorem: [0 ..< n] = GENLIST I n *)
(* Proof: by listRangeINC_def *)
val listRangeLHI_0_n = store_thm(
  "listRangeLHI_0_n",
  ``!n. [0 ..< n] = GENLIST I n``,
  rpt strip_tac >>
  `(\i:num. i) = I` by rw[FUN_EQ_THM] >>
  rw[listRangeLHI_def]);

(* Theorem: MAP f [0 ..< n] = GENLIST f n *)
(* Proof:
     MAP f [0 ..< n]
   = MAP f (GENLIST I n)     by listRangeLHI_0_n
   = GENLIST (f o I) n       by MAP_GENLIST
   = GENLIST f n             by I_THM
*)
val listRangeLHI_MAP = store_thm(
  "listRangeLHI_MAP",
  ``!f n. MAP f [0 ..< n] = GENLIST f n``,
  rw[listRangeLHI_0_n, MAP_GENLIST]);

(* Theorem: SUM (MAP f [0 ..< (SUC n)]) = f n + SUM (MAP f [0 ..< n]) *)
(* Proof:
      SUM (MAP f [0 ..< (SUC n)])
    = SUM (MAP f (SNOC n [0 ..< n]))       by listRangeLHI_SNOC
    = SUM (SNOC (f n) (MAP f [0 ..< n]))   by MAP_SNOC
    = f n + SUM (MAP f [0 ..< n])          by SUM_SNOC
*)
val listRangeLHI_SUM_MAP = store_thm(
  "listRangeLHI_SUM_MAP",
  ``!f n. SUM (MAP f [0 ..< (SUC n)]) = f n + SUM (MAP f [0 ..< n])``,
  rw[listRangeLHI_SNOC, MAP_SNOC, SUM_SNOC, ADD1]);

(* Theorem: m <= j /\ j < n ==> [m ..< n] = [m ..< j] ++ j::[j+1 ..< n] *)
(* Proof:
   Note j < n implies j <= n.
     [m ..< n]
   = [m ..< j] ++ [j ..< n]        by listRangeLHI_APPEND, j <= n
   = [m ..< j] ++ j::[j+1 ..< n]   by listRangeLHI_CONS, j < n
*)
Theorem listRangeLHI_SPLIT:
  !m n j. m <= j /\ j < n ==> [m ..< n] = [m ..< j] ++ j::[j+1 ..< n]
Proof
  rpt strip_tac >>
  `[m ..< n] = [m ..< j] ++ [j ..< n]` by simp[listRangeLHI_APPEND] >>
  simp[listRangeLHI_CONS]
QED

(* listRangeTheory.listRangeLHI_ALL_DISTINCT  |- ALL_DISTINCT [lo ..< hi] *)

(* Theorem: ALL_DISTINCT [m .. n] *)
(* Proof:
       ALL_DISTINCT [m .. n]
   <=> ALL_DISTINCT [m ..< n + 1]              by listRangeLHI_to_INC
   <=> T                                       by listRangeLHI_ALL_DISTINCT
*)
Theorem listRangeINC_ALL_DISTINCT:
  !m n. ALL_DISTINCT [m .. n]
Proof
  metis_tac[listRangeLHI_to_INC, listRangeLHI_ALL_DISTINCT]
QED

(* Theorem:  m <= n ==> EVERY P [m - 1 .. n] <=> (P (m - 1) /\ EVERY P [m ..n]) *)
(* Proof:
       EVERY P [m - 1 .. n]
   <=> !x. m - 1 <= x /\ x <= n ==> P x                by listRangeINC_EVERY
   <=> !x. (m - 1 = x \/ m <= x) /\ x <= n ==> P x     by arithmetic
   <=> !x. (x = m - 1 ==> P x) /\ m <= x /\ x <= n ==> P x
                                                       by RIGHT_AND_OVER_OR, DISJ_IMP_THM
   <=> P (m - 1) /\ EVERY P [m .. n]                   by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_split_head:
  !P m n. m <= n ==> (EVERY P [m - 1 .. n] <=> P (m - 1) /\ EVERY P [m ..n])
Proof
  rw[listRangeINC_EVERY] >>
  `!x. m <= x + 1 <=> m - 1 = x \/ m <= x` by decide_tac >>
  (rw[EQ_IMP_THM] >> metis_tac[])
QED

(* Theorem: m <= n ==> (EVERY P [m .. (n + 1)] <=> P (n + 1) /\ EVERY P [m .. n]) *)
(* Proof:
       EVERY P [m .. (n + 1)]
   <=> !x. m <= x /\ x <= n + 1 ==> P x                by listRangeINC_EVERY
   <=> !x. m <= x /\ (x <= n \/ x = n + 1) ==> P x     by arithmetic
   <=> !x. m <= x /\ x <= n ==> P x /\ P (n + 1)       by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> P (n + 1) /\ EVERY P [m .. n]                   by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_split_last:
  !P m n. m <= n ==> (EVERY P [m .. (n + 1)] <=> P (n + 1) /\ EVERY P [m .. n])
Proof
  rw[listRangeINC_EVERY] >>
  `!x. x <= n + 1 <=> x <= n \/ x = n + 1` by decide_tac >>
  metis_tac[]
QED

(* Theorem: m <= n ==> (EVERY P [m .. n] <=> P n /\ EVERY P [m ..< n]) *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. m <= x /\ x <= n ==> P x                by listRangeINC_EVERY
   <=> !x. m <= x /\ (x < n \/ x = n) ==> P x      by arithmetic
   <=> !x. m <= x /\ x < n ==> P x /\ P n          by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> P n /\ EVERY P [m ..< n]                    by listRangeLHI_EVERY
*)
Theorem listRangeINC_EVERY_less_last:
  !P m n. m <= n ==> (EVERY P [m .. n] <=> P n /\ EVERY P [m ..< n])
Proof
  rw[listRangeINC_EVERY, listRangeLHI_EVERY] >>
  `!x. x <= n <=> x < n \/ x = n` by decide_tac >>
  metis_tac[]
QED

(* Theorem: m < n /\ P m /\ ~P n ==>
            ?k. m <= k /\ k < n /\ EVERY P [m .. k] /\ ~P (SUC k) *)
(* Proof:
       m < n /\ P m /\ ~P n
   ==> ?k. m <= k /\ k < m /\
       (!j. m <= j /\ j <= k ==> P j) /\ ~P (SUC k)    by every_range_span_max
   ==> ?k. m <= k /\ k < m /\
       EVERY P [m .. k] /\ ~P (SUC k)                  by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_span_max:
  !P m n. m < n /\ P m /\ ~P n ==>
          ?k. m <= k /\ k < n /\ EVERY P [m .. k] /\ ~P (SUC k)
Proof
  simp[listRangeINC_EVERY, every_range_span_max]
QED

(* Theorem: m < n /\ ~P m /\ P n ==>
            ?k. m < k /\ k <= n /\ EVERY P [k .. n] /\ ~P (PRE k) *)
(* Proof:
       m < n /\ P m /\ ~P n
   ==> ?k. m < k /\ k <= n /\
       (!j. k <= j /\ j <= n ==> P j) /\ ~P (PRE k)    by every_range_span_min
   ==> ?k. m < k /\ k <= n /\
       EVERY P [k .. n] /\ ~P (PRE k)                  by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_span_min:
  !P m n. m < n /\ ~P m /\ P n ==>
          ?k. m < k /\ k <= n /\ EVERY P [k .. n] /\ ~P (PRE k)
Proof
  simp[listRangeINC_EVERY, every_range_span_min]
QED

(* temporarily make divides an infix *)
val _ = temp_set_fixity "divides" (Infixl 480);

(* Theorem: 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n] *)
(* Proof:
   Note x divdes n ==> x <= n     by DIVIDES_LE, 0 < n
     so MEM x [m .. n]            by listRangeINC_MEM
*)
val listRangeINC_has_divisors = store_thm(
  "listRangeINC_has_divisors",
  ``!m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n]``,
  rw[listRangeINC_MEM, DIVIDES_LE]);

(* Theorem: 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1] *)
(* Proof:
   Note the condition implies:
        MEM x [m .. n]         by listRangeINC_has_divisors
      = MEM x [m ..< n + 1]    by listRangeLHI_to_INC
*)
val listRangeLHI_has_divisors = store_thm(
  "listRangeLHI_has_divisors",
  ``!m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1]``,
  metis_tac[listRangeINC_has_divisors, listRangeLHI_to_INC]);

val _ = export_theory();
