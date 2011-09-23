open HolKernel bossLib boolLib Parse
open BasicProvers

open finite_mapTheory

(* an fmaptree is a type of tree, where branching is controlled by a
   finite-map.  The one constructor is

    FTNode : 'a -> ('k |-> ('a,'k)fmaptree) -> ('a,'k)fmaptree

   This is rather like a trie.

   There is an induction principle (ft_ind), where you are able to assume
   that your predicate P holds of every subtree.
*)

val _ = new_theory "fmaptree";

val construct_def = Define`
  construct a kfm kl =
    case kl of
      [] => SOME a
    | h :: t => if h IN FDOM kfm then kfm ' h t
                else NONE
`;

val (wf_rules, wf_ind, wf_cases) = Hol_reln`
  !a fm. (!k. k IN FDOM fm ==> wf (fm ' k)) ==> wf (construct a fm)
`;

val wf_NIL_SOME = prove(
  ``wf f ==> ?a. f [] = SOME a``,
  ONCE_REWRITE_TAC [wf_cases] THEN SRW_TAC [][] THEN
  SRW_TAC [][construct_def]);

val construct_11 = prove(
  ``(!k. k IN FDOM f ==> wf (f ' k)) /\
    (!k. k IN FDOM g ==> wf (g ' k)) ==>
    ((construct a f = construct b g) = (a = b) /\ (f = g))``,
  SRW_TAC [] [EQ_IMP_THM, FUN_EQ_THM, construct_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `[]` MP_TAC) THEN SRW_TAC [][],
    SIMP_TAC (srw_ss()) [fmap_EXT, pred_setTheory.EXTENSION] THEN
    `!x. x IN FDOM f = x IN FDOM g`
        by (GEN_TAC THEN
            FIRST_X_ASSUM (Q.SPEC_THEN `[x]` MP_TAC) THEN SRW_TAC [][] THENL [
              `?a. f ' x [] = SOME a` by METIS_TAC [wf_NIL_SOME],
              `?a. g ' x [] = SOME a` by METIS_TAC [wf_NIL_SOME]
            ] THEN
            SRW_TAC [][]) THEN
    SRW_TAC [][] THEN
    FIRST_X_ASSUM (MP_TAC o Q.GEN `t` o SPEC ``x::t``) THEN
    SRW_TAC [][FUN_EQ_THM]
  ]);

val fmaptrees_exist = new_type_definition(
  "fmaptree",
  prove(``?(f: 'key list -> 'value option). wf f``,
        Q.EXISTS_TAC `construct ARB FEMPTY` THEN
        ONCE_REWRITE_TAC [wf_cases] THEN
        MAP_EVERY Q.EXISTS_TAC [`ARB`, `FEMPTY`] THEN
        SRW_TAC [][]))

val fmap_bij_thm = define_new_type_bijections {ABS = "fromF", REP = "toF",
                                               name = "fmap_bij_thm",
                                               tyax = fmaptrees_exist}

val bij_nchotomy = prove(
  ``!a. ?c. wf c /\ (a = fromF c)``,
  METIS_TAC [fmap_bij_thm])

val FTNode_def = Define`
  FTNode i fm = fromF (construct i (toF o_f fm))
`;

val toF_composed_wf = prove(
  ``!k. k IN FDOM f1 ==> wf ((toF o_f f1) ' k)``,
  SRW_TAC [][o_f_FAPPLY, fmap_bij_thm]);

val fromF_11 = prove(
  ``wf x /\ wf y ==> ((fromF x = fromF y) = (x = y))``,
  METIS_TAC [fmap_bij_thm]);

val toF_11 = prove(``(toF f = toF g) = (f = g)``, METIS_TAC [fmap_bij_thm]);

val toF_o_f_11 = prove(
  ``((toF o_f f) = (toF o_f g)) = (f = g)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [fmap_EXT, o_f_FAPPLY] THEN
  `!x. x IN FDOM g ==> (toF (f ' x) = toF (g ' x))`
      by METIS_TAC [o_f_FAPPLY] THEN
  FULL_SIMP_TAC (srw_ss()) [toF_11]);

val FTNode_11 = store_thm(
  "FTNode_11",
  ``(FTNode i1 f1 = FTNode i2 f2) = (i1 = i2) /\ (f1 = f2)``,
  SRW_TAC [][FTNode_def, fromF_11, wf_rules, toF_composed_wf,
             construct_11, toF_o_f_11]);
val _ = export_rewrites ["FTNode_11"]

val fmaptree_nchotomy = store_thm(
  "fmaptree_nchotomy",
  ``!ft. ?i fm. ft = FTNode i fm``,
  GEN_TAC THEN Q.SPEC_THEN `ft` STRUCT_CASES_TAC bij_nchotomy THEN
  SRW_TAC [][FTNode_def, fromF_11, wf_rules, toF_composed_wf] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [wf_cases]) THEN
  SRW_TAC [][] THEN SRW_TAC [][construct_11, toF_composed_wf] THEN
  Q.EXISTS_TAC `fromF o_f fm` THEN
  SRW_TAC [][fmap_EXT, o_f_FAPPLY] THEN METIS_TAC [fmap_bij_thm]);

val item_map_def = new_specification("item_map_def",
  ["item", "map"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] fmaptree_nchotomy);

val (item_thm, map_thm) =
    CONJ_PAIR (GSYM (SIMP_RULE (srw_ss()) [FORALL_AND_THM]
                               (ISPEC ``FTNode i fm`` item_map_def)))

val _ = (save_thm("item_thm", item_thm); export_rewrites ["item_thm"])
val _ = (save_thm("map_thm", map_thm); export_rewrites ["map_thm"])

val apply_path_def = Define`
  (apply_path [] ft = SOME ft) /\
  (apply_path (h::t) ft = if h IN FDOM (map ft) then apply_path t (map ft ' h)
                          else NONE)
`;

val update_at_path_def = Define`
  (update_at_path [] a ft = SOME (FTNode a (map ft))) /\
  (update_at_path (h::t) a ft =
     if h IN FDOM (map ft) then
       case update_at_path t a (map ft ' h) of
         NONE => NONE
       | SOME ft' => SOME (FTNode (item ft) (map ft |+ (h,ft')))
     else NONE)
`;

val fupd_at_path_def = Define`
  (fupd_at_path [] f ft = f ft) /\
  (fupd_at_path (h::t) f ft =
     if h IN FDOM (map ft) then
       case fupd_at_path t f (map ft ' h) of
         NONE => NONE
       | SOME ft' => SOME (FTNode (item ft) (map ft |+ (h, ft')))
     else NONE)
`;

val forall_ft = prove(
  ``(!ft. P ft) = (!f. wf f ==> P (fromF f))``,
  METIS_TAC [fmap_bij_thm])

val wf_strong_ind = IndDefLib.derive_strong_induction(wf_rules, wf_ind)

val ft_ind = store_thm(
  "ft_ind",
  ``!P. (!a fm. (!k. k IN FDOM fm ==> P (fm ' k)) ==> P (FTNode a fm)) ==>
        !ft. P ft``,
  SIMP_TAC (srw_ss()) [forall_ft, FTNode_def] THEN GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC wf_strong_ind THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`a`, `fromF o_f fm`] MP_TAC) THEN
  SRW_TAC [][o_f_FAPPLY] THEN
  Q_TAC SUFF_TAC `toF o fromF o_f fm = fm`
        THEN1 (DISCH_THEN (SUBST1_TAC o SYM) THEN SRW_TAC [][]) THEN
  SRW_TAC [][fmap_EXT, o_f_FAPPLY] THEN METIS_TAC [fmap_bij_thm]);

open pred_setTheory boolSimps
val list_GSPEC_cases = prove(
  ``{ l | P l } = (if P [] then {[]} else {}) UNION
                  { h :: t | P (h :: t) }``,
  SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][] THEN
  Cases_on `x` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []);

val applicable_paths_FINITE = store_thm(
  "applicable_paths_FINITE",
  ``!ft. FINITE { p | ?ft'. apply_path p ft = SOME ft' }``,
  HO_MATCH_MP_TAC ft_ind THEN SRW_TAC [][] THEN
  CONV_TAC (RAND_CONV (HO_REWR_CONV list_GSPEC_cases)) THEN
  SRW_TAC [][apply_path_def] THEN
  SRW_TAC [COND_elim_ss, DNF_ss, CONJ_ss][] THEN
  Q.MATCH_ABBREV_TAC `FINITE s` THEN
  `s = BIGUNION (IMAGE (\k. IMAGE (CONS k)
                                  { p | ?ft'. apply_path p (fm ' k) =
                                              SOME ft' })
                       (FDOM fm))`
     by (SRW_TAC [DNF_ss][Once EXTENSION, Abbr`s`] THEN METIS_TAC []) THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THEN SRW_TAC [][IMAGE_FINITE]);

val apply_path_SNOC = store_thm(
  "apply_path_SNOC",
  ``!ft x p. apply_path (p ++ [x]) ft =
             case apply_path p ft of
               NONE => NONE
             | SOME ft' => FLOOKUP (map ft') x``,
  Induct_on `p` THEN
  SRW_TAC [][apply_path_def, finite_mapTheory.FLOOKUP_DEF]);

(* ----------------------------------------------------------------------
    recursion principle
   ---------------------------------------------------------------------- *)

val (relrec_rules, relrec_ind, relrec_cases) = Hol_reln`
  !i fm rfm. (FDOM rfm = FDOM fm) /\
             (!d. d IN FDOM fm ==> relrec h (fm ' d) (rfm ' d))
          ==>
             relrec h (FTNode i fm) (h i rfm fm)
`;

val relrec_fn = prove(
  ``!ft r1. relrec h ft r1 ==> !r2. relrec h ft r2 ==> (r1 = r2)``,
  HO_MATCH_MP_TAC relrec_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [relrec_cases] THEN SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `rfm = rfm'` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][fmap_EXT]);

val relrec_total = prove(
  ``!ft. ?r. relrec h ft r``,
  HO_MATCH_MP_TAC ft_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [relrec_cases] THEN SRW_TAC [][] THEN
  `?f. !k. k IN FDOM fm ==> relrec h (fm ' k) (f k)`
     by METIS_TAC [] THEN
  Q.EXISTS_TAC `FUN_FMAP f (FDOM fm)` THEN
  SRW_TAC [][FUN_FMAP_DEF]);

val fmtreerec_def = Define`
  fmtreerec h ft = @r. relrec h ft r
`;

val fmtreerec_thm = store_thm(
  "fmtreerec_thm",
  ``fmtreerec h (FTNode i fm) = h i (fmtreerec h o_f fm) fm``,
  SRW_TAC [][fmtreerec_def] THEN
  ONCE_REWRITE_TAC [relrec_cases] THEN SRW_TAC [][] THEN
  SELECT_ELIM_TAC THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `FUN_FMAP (\k. @r. relrec h (fm ' k) r) (FDOM fm)` THEN
    SRW_TAC [][FUN_FMAP_DEF] THEN SELECT_ELIM_TAC THEN
    METIS_TAC [relrec_total],
    `fmtreerec h = \ft. @r. relrec h ft r`
       by SRW_TAC [][FUN_EQ_THM, fmtreerec_def] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    SRW_TAC [][fmap_EXT, o_f_DEF] THEN METIS_TAC [relrec_fn]
  ]);

val fmtree_Axiom = store_thm(
  "fmtree_Axiom",
  ``!h. ?f. !i fm. f (FTNode i fm) = h i fm (f o_f fm)``,
  GEN_TAC THEN Q.EXISTS_TAC `fmtreerec (\i r f. h i f r)` THEN
  SRW_TAC [][fmtreerec_thm]);

val _ = export_theory()


