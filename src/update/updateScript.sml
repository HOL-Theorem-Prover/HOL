(* ========================================================================= *)
(* FILE          : updateScript.sml                                          *)
(* DESCRIPTION   : Function update with lists                                *)
(* DATE          : 2011                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open rich_listTheory sortingTheory;

val _ = new_theory "update";

(* ------------------------------------------------------------------------
   Definitions
   ------------------------------------------------------------------------ *)

val FIND_def = Define`
  (FIND P [] = NONE) /\
  (FIND P (h::t) = if P h then SOME h else FIND P t)`;

val OVERRIDE_def = tDefine "OVERRIDE"
  `(OVERRIDE [] = []) /\
   (OVERRIDE (x::t) = x :: OVERRIDE (FILTER (\y. FST x <> FST y) t))`
  (WF_REL_TAC `measure LENGTH`
   THEN SRW_TAC [] [rich_listTheory.LENGTH_FILTER_LEQ,
          DECIDE ``!a b. a <= b ==> a < SUC b``]);

val LIST_UPDATE_def = Define`
  (LIST_UPDATE [] = I) /\
  (LIST_UPDATE (h::t) = (FST h =+ SND h) o LIST_UPDATE t)`;

(* ------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------ *)

val LIST_UPDATE_LOOKUP = Q.store_thm("LIST_UPDATE_LOOKUP",
  `!l f i.
     LIST_UPDATE l f i =
       case FIND (\x. FST x = i) l
       of SOME (_,e) => e
        | NONE => f i`,
  Induct
  THEN SRW_TAC [] [LIST_UPDATE_def, FIND_def, combinTheory.UPDATE_def]
  THEN Cases_on `h`
  THEN SRW_TAC [] []);

val FILTER_OVERRIDE_lem = Q.prove(
  `(((\y. x <> y) o FST) = (\y. x <> FST y)) /\
   (((\y. x <> y /\ P y) o FST) = (\y. x <> FST y /\ P (FST y)))`,
  SRW_TAC [] [FUN_EQ_THM]
  THEN METIS_TAC []);

val FILTER_OVERRIDE = Q.prove(
  `!P l.
     OVERRIDE (FILTER (P o FST) l) =
     FILTER (P o FST) (OVERRIDE l)`,
  Induct_on `l` THEN SRW_TAC [] [OVERRIDE_def]
  THEN Q.PAT_ASSUM `!P. x`
         (fn thm =>
            Q.SPEC_THEN `\y. FST h <> y` ASSUME_TAC thm
            THEN Q.SPEC_THEN `\y. FST h <> y /\ P y` ASSUME_TAC thm)
  THEN FULL_SIMP_TAC (srw_ss())
         [FILTER_OVERRIDE_lem, rich_listTheory.FILTER_FILTER]
  THEN SRW_TAC [] [FILTER_EQ]
  THEN METIS_TAC []);

val FIND_FILTER = Q.prove(
  `!l i j.
     i <> j ==>
     (FIND (\x. FST x = i) (FILTER (\y. j <> FST y) l) =
      FIND (\x. FST x = i) l)`,
  Induct_on `l` THEN SRW_TAC [] [FIND_def]);

val FIND_OVERRIDE = Q.prove(
  `!l i j.
     i <> j ==>
     (FIND (\x. FST x = i) (OVERRIDE (FILTER (\y. j <> FST y) l)) =
      FIND (\x. FST x = i) (OVERRIDE l))`,
  Induct
  THEN SRW_TAC [] [OVERRIDE_def, FIND_def]
  THEN Q.SPEC_THEN `\y. FST h <> y`
         (ASSUME_TAC o REWRITE_RULE [FILTER_OVERRIDE_lem])
         FILTER_OVERRIDE
  THEN ASM_SIMP_TAC std_ss [FIND_FILTER]);

val LIST_UPDATE_OVERRIDE = Q.store_thm("LIST_UPDATE_OVERRIDE",
  `!l. LIST_UPDATE l = LIST_UPDATE (OVERRIDE l)`,
  REWRITE_TAC [FUN_EQ_THM]
  THEN Induct_on `l`
  THEN SRW_TAC [] [OVERRIDE_def, LIST_UPDATE_def, combinTheory.UPDATE_def]
  THEN SRW_TAC [] [LIST_UPDATE_LOOKUP, FIND_OVERRIDE]);

(* ------------------------------------------------------------------------ *)

val FIND_APPEND_lem = Q.prove(
  `!h l1 l2.
     ~MEM (FST h) (MAP FST l1) ==>
     (FIND (\x. FST x = FST h) (l1 ++ l2) = FIND (\x. FST x = FST h) l2)`,
  Induct_on `l1` THEN SRW_TAC [] [FIND_def]);

val FIND_APPEND_lem2 = Q.prove(
  `!y l1 l2.
     FST h <> y ==>
     (FIND (\x. FST x = y) (l1 ++ h::l2) =
      FIND (\x. FST x = y) (l1 ++ l2))`,
  Induct_on `l1` THEN SRW_TAC [] [FIND_def]);

val FIND_ALL_DISTINCT = Q.prove(
  `!l1 l2 y.
      ALL_DISTINCT (MAP FST l1) /\ PERM l1 l2 ==>
      (FIND (\x. FST x = y) l1 = FIND (\x. FST x = y) l2)`,
  Induct
  THEN SRW_TAC [] [FIND_def]
  THENL [
    FULL_SIMP_TAC std_ss [sortingTheory.PERM_CONS_EQ_APPEND]
    THEN Q.ISPEC_THEN `FST` IMP_RES_TAC sortingTheory.PERM_MAP
    THEN `!x. MEM x (MAP FST l1) = MEM x (MAP FST (M ++ N))`
      by IMP_RES_TAC sortingTheory.PERM_MEM_EQ
    THEN `~MEM (FST h) (MAP FST M)`
      by METIS_TAC [listTheory.MEM_APPEND, listTheory.MAP_APPEND]
    THEN SRW_TAC [] [FIND_APPEND_lem, FIND_def],
    FULL_SIMP_TAC std_ss [sortingTheory.PERM_CONS_EQ_APPEND]
    THEN SRW_TAC [] [FIND_APPEND_lem2]
  ]);

val LIST_UPDATE_ALL_DISTINCT = Q.store_thm("LIST_UPDATE_ALL_DISTINCT",
  `!l1 l2.
      ALL_DISTINCT (MAP FST l2) /\ PERM l1 l2 ==>
      (LIST_UPDATE l1 = LIST_UPDATE l2)`,
  SRW_TAC [] [FUN_EQ_THM, LIST_UPDATE_LOOKUP]
  THEN METIS_TAC [FIND_ALL_DISTINCT, sortingTheory.PERM_SYM]);

val ALL_DISTINCT_OVERRIDE = Q.prove(
  `!l. ALL_DISTINCT (MAP FST (OVERRIDE l))`,
  Induct
  THEN SRW_TAC [] [OVERRIDE_def, listTheory.MEM_FILTER,
         listTheory.FILTER_ALL_DISTINCT,
         FILTER_OVERRIDE |> Q.SPEC `\y. FST h <> y`
                         |> REWRITE_RULE [FILTER_OVERRIDE_lem],
         FILTER_MAP |> Q.ISPECL [`\y. FST h <> y`,`FST`]
                    |> REWRITE_RULE [FILTER_OVERRIDE_lem] |> GSYM]);

val ALL_DISTINCT_QSORT = Q.prove(
  `!l R. ALL_DISTINCT (MAP FST l) ==> ALL_DISTINCT (MAP FST (QSORT R l))`,
  METIS_TAC [sortingTheory.QSORT_PERM, sortingTheory.PERM_MAP,
    sortingTheory.ALL_DISTINCT_PERM]);

val LIST_UPDATE_SORT_OVERRIDE = Q.store_thm("LIST_UPDATE_SORT_OVERRIDE",
  `!R l. LIST_UPDATE l = LIST_UPDATE (QSORT R (OVERRIDE l))`,
  METIS_TAC [LIST_UPDATE_OVERRIDE, LIST_UPDATE_ALL_DISTINCT,
    sortingTheory.QSORT_PERM, ALL_DISTINCT_OVERRIDE, ALL_DISTINCT_QSORT]);

(* ------------------------------------------------------------------------ *)

val LIST_UPDATE1 = Q.prove(
  `(!l1 l2 r1 r2.
     (l1 =+ r1) o (l2 =+ r2) = LIST_UPDATE [(l1,r1); (l2,r2)]) /\
   (!l r t. (l =+ r) o LIST_UPDATE t = LIST_UPDATE ((l,r)::t)) /\
   (!l1 l2 r1 r2 f.
      (l1 =+ r1) ((l2 =+ r2) f) = LIST_UPDATE [(l1,r1); (l2,r2)] f) /\
   (!l r t f. (l =+ r) (LIST_UPDATE t f) = LIST_UPDATE ((l,r)::t) f)`,
  SRW_TAC [] [LIST_UPDATE_def]);

val LIST_UPDATE2 = Q.prove(
  `(!l1 l2. LIST_UPDATE l1 o LIST_UPDATE l2 = LIST_UPDATE (l1 ++ l2)) /\
   (!l1 l2 r. LIST_UPDATE l1 o (l2 =+ r) = LIST_UPDATE (SNOC (l2,r) l1)) /\
   (!l1 l2 f.
      LIST_UPDATE l1 (LIST_UPDATE l2 f) = LIST_UPDATE (l1 ++ l2) f) /\
   (!l1 l2 r f. LIST_UPDATE l1 ((l2 =+ r) f) = LIST_UPDATE (SNOC (l2,r) l1) f)`,
  REPEAT CONJ_TAC
  THEN Induct THEN SRW_TAC [] [LIST_UPDATE_def]);

val LIST_UPDATE_THMS = Theory.save_thm("LIST_UPDATE_THMS",
   CONJ LIST_UPDATE1 LIST_UPDATE2);

(* ------------------------------------------------------------------------
   Duplicate theorems about update from combinTheory
   ------------------------------------------------------------------------ *)

val _ = List.map Theory.save_thm
  (let open combinTheory in
    [("APPLY_UPDATE_ID", APPLY_UPDATE_ID),
     ("APPLY_UPDATE_THM", APPLY_UPDATE_THM),
     ("SAME_KEY_UPDATE_DIFFER", SAME_KEY_UPDATE_DIFFER),
     ("UPDATE_APPLY_ID", UPDATE_APPLY_ID),
     ("UPDATE_APPLY_IMP_ID", UPDATE_APPLY_IMP_ID),
     ("UPDATE_COMMUTES", UPDATE_COMMUTES),
     ("UPDATE_EQ", UPDATE_EQ),
     ("UPDATE_def", UPDATE_def)]
   end)

(* ------------------------------------------------------------------------ *)

val _ = export_theory();
