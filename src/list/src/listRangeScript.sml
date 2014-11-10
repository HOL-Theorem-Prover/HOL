open HolKernel Parse boolLib
open BasicProvers TotalDefn simpLib numSimps numLib

open listTheory

val _ = new_theory "listRange";

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



val _ = export_theory();
