(* ========================================================================= *)
(* FILE          : updateScript.sml                                          *)
(* DESCRIPTION   : Function update with lists                                *)
(* DATE          : 2011                                                      *)
(* ========================================================================= *)
Theory update
Ancestors
  rich_list sorting


(* ------------------------------------------------------------------------
   Definitions
   ------------------------------------------------------------------------ *)

Theorem FIND_def = listTheory.FIND_thm

Definition OVERRIDE_def:
  (OVERRIDE [] = []) /\
  (OVERRIDE (x::t) = x :: OVERRIDE (FILTER (\y. FST x <> FST y) t))
Termination
  WF_REL_TAC `measure LENGTH`
   THEN SRW_TAC [] [rich_listTheory.LENGTH_FILTER_LEQ,
          DECIDE ``!a b. a <= b ==> a < SUC b``]
End

Definition LIST_UPDATE_def:
  (LIST_UPDATE [] = I) /\
  (LIST_UPDATE (h::t) = (FST h =+ SND h) o LIST_UPDATE t)
End

(* ------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------ *)

Theorem LIST_UPDATE_LOOKUP:
   !l f i.
     LIST_UPDATE l f i =
       case FIND (\x. FST x = i) l
       of SOME (_,e) => e
        | NONE => f i
Proof
  Induct
  THEN SRW_TAC [] [LIST_UPDATE_def, FIND_def, combinTheory.UPDATE_def]
  THEN Cases_on `h`
  THEN SRW_TAC [] []
QED

Theorem FILTER_OVERRIDE_lem[local]:
   (((\y. x <> y) o FST) = (\y. x <> FST y)) /\
   (((\y. x <> y /\ P y) o FST) = (\y. x <> FST y /\ P (FST y)))
Proof
  SRW_TAC [] [FUN_EQ_THM]
  THEN METIS_TAC []
QED

Theorem FILTER_OVERRIDE[local]:
   !P l.
     OVERRIDE (FILTER (P o FST) l) =
     FILTER (P o FST) (OVERRIDE l)
Proof
  Induct_on `l` THEN SRW_TAC [] [OVERRIDE_def]
  THEN Q.PAT_ASSUM `!P. x`
         (fn thm =>
            Q.SPEC_THEN `\y. FST h <> y` ASSUME_TAC thm
            THEN Q.SPEC_THEN `\y. FST h <> y /\ P y` ASSUME_TAC thm)
  THEN FULL_SIMP_TAC (srw_ss())
         [FILTER_OVERRIDE_lem, rich_listTheory.FILTER_FILTER]
  THEN SRW_TAC [] [FILTER_EQ]
  THEN METIS_TAC []
QED

Theorem FIND_FILTER[local]:
   !l i j.
     i <> j ==>
     (FIND (\x. FST x = i) (FILTER (\y. j <> FST y) l) =
      FIND (\x. FST x = i) l)
Proof
  Induct_on `l` THEN SRW_TAC [] [FIND_def]
QED

Theorem FIND_OVERRIDE[local]:
   !l i j.
     i <> j ==>
     (FIND (\x. FST x = i) (OVERRIDE (FILTER (\y. j <> FST y) l)) =
      FIND (\x. FST x = i) (OVERRIDE l))
Proof
  Induct
  THEN SRW_TAC [] [OVERRIDE_def, FIND_def]
  THEN Q.SPEC_THEN `\y. FST h <> y`
         (ASSUME_TAC o REWRITE_RULE [FILTER_OVERRIDE_lem])
         FILTER_OVERRIDE
  THEN ASM_SIMP_TAC std_ss [FIND_FILTER]
QED

Theorem LIST_UPDATE_OVERRIDE:
   !l. LIST_UPDATE l = LIST_UPDATE (OVERRIDE l)
Proof
  REWRITE_TAC [FUN_EQ_THM]
  THEN Induct_on `l`
  THEN SRW_TAC [] [OVERRIDE_def, LIST_UPDATE_def, combinTheory.UPDATE_def]
  THEN SRW_TAC [] [LIST_UPDATE_LOOKUP, FIND_OVERRIDE]
QED

(* ------------------------------------------------------------------------ *)

Theorem FIND_APPEND_lem[local]:
   !h l1 l2.
     ~MEM (FST h) (MAP FST l1) ==>
     (FIND (\x. FST x = FST h) (l1 ++ l2) = FIND (\x. FST x = FST h) l2)
Proof
  Induct_on `l1` THEN SRW_TAC [] [FIND_def]
QED

Theorem FIND_APPEND_lem2[local]:
   !y l1 l2.
     FST h <> y ==>
     (FIND (\x. FST x = y) (l1 ++ h::l2) =
      FIND (\x. FST x = y) (l1 ++ l2))
Proof
  Induct_on `l1` THEN SRW_TAC [] [FIND_def]
QED

Theorem FIND_ALL_DISTINCT[local]:
   !l1 l2 y.
      ALL_DISTINCT (MAP FST l1) /\ PERM l1 l2 ==>
      (FIND (\x. FST x = y) l1 = FIND (\x. FST x = y) l2)
Proof
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
  ]
QED

Theorem LIST_UPDATE_ALL_DISTINCT:
   !l1 l2.
      ALL_DISTINCT (MAP FST l2) /\ PERM l1 l2 ==>
      (LIST_UPDATE l1 = LIST_UPDATE l2)
Proof
  SRW_TAC [] [FUN_EQ_THM, LIST_UPDATE_LOOKUP]
  THEN METIS_TAC [FIND_ALL_DISTINCT, sortingTheory.PERM_SYM]
QED

Theorem ALL_DISTINCT_OVERRIDE[local]:
   !l. ALL_DISTINCT (MAP FST (OVERRIDE l))
Proof
  Induct
  THEN SRW_TAC [] [OVERRIDE_def, listTheory.MEM_FILTER,
         listTheory.FILTER_ALL_DISTINCT,
         FILTER_OVERRIDE |> Q.SPEC `\y. FST h <> y`
                         |> REWRITE_RULE [FILTER_OVERRIDE_lem],
         FILTER_MAP |> Q.ISPECL [`\y. FST h <> y`,`FST`]
                    |> REWRITE_RULE [FILTER_OVERRIDE_lem] |> GSYM]
QED

Theorem ALL_DISTINCT_QSORT[local]:
   !l R. ALL_DISTINCT (MAP FST l) ==> ALL_DISTINCT (MAP FST (QSORT R l))
Proof
  METIS_TAC [sortingTheory.QSORT_PERM, sortingTheory.PERM_MAP,
    sortingTheory.ALL_DISTINCT_PERM]
QED

Theorem LIST_UPDATE_SORT_OVERRIDE:
   !R l. LIST_UPDATE l = LIST_UPDATE (QSORT R (OVERRIDE l))
Proof
  METIS_TAC [LIST_UPDATE_OVERRIDE, LIST_UPDATE_ALL_DISTINCT,
    sortingTheory.QSORT_PERM, ALL_DISTINCT_OVERRIDE, ALL_DISTINCT_QSORT]
QED

(* ------------------------------------------------------------------------ *)

Theorem LIST_UPDATE1[local]:
   (!l1 l2 r1 r2.
     (l1 =+ r1) o (l2 =+ r2) = LIST_UPDATE [(l1,r1); (l2,r2)]) /\
   (!l r t. (l =+ r) o LIST_UPDATE t = LIST_UPDATE ((l,r)::t)) /\
   (!l1 l2 r1 r2 f.
      (l1 =+ r1) ((l2 =+ r2) f) = LIST_UPDATE [(l1,r1); (l2,r2)] f) /\
   (!l r t f. (l =+ r) (LIST_UPDATE t f) = LIST_UPDATE ((l,r)::t) f)
Proof
  SRW_TAC [] [LIST_UPDATE_def]
QED

Theorem LIST_UPDATE2[local]:
   (!l1 l2. LIST_UPDATE l1 o LIST_UPDATE l2 = LIST_UPDATE (l1 ++ l2)) /\
   (!l1 l2 r. LIST_UPDATE l1 o (l2 =+ r) = LIST_UPDATE (SNOC (l2,r) l1)) /\
   (!l1 l2 f.
      LIST_UPDATE l1 (LIST_UPDATE l2 f) = LIST_UPDATE (l1 ++ l2) f) /\
   (!l1 l2 r f. LIST_UPDATE l1 ((l2 =+ r) f) = LIST_UPDATE (SNOC (l2,r) l1) f)
Proof
  REPEAT CONJ_TAC
  THEN Induct THEN SRW_TAC [] [LIST_UPDATE_def]
QED

Theorem LIST_UPDATE_THMS =
   CONJ LIST_UPDATE1 LIST_UPDATE2;

(* ------------------------------------------------------------------------
   Duplicate theorems about update from combinTheory
   ------------------------------------------------------------------------ *)

Theorem APPLY_UPDATE_ID = combinTheory.APPLY_UPDATE_ID
Theorem APPLY_UPDATE_THM = combinTheory.APPLY_UPDATE_THM
Theorem SAME_KEY_UPDATE_DIFFER = combinTheory.SAME_KEY_UPDATE_DIFFER
Theorem UPDATE_APPLY_ID = combinTheory.UPDATE_APPLY_ID
Theorem UPDATE_APPLY_IMP_ID = combinTheory.UPDATE_APPLY_IMP_ID
Theorem UPDATE_COMMUTES = combinTheory.UPDATE_COMMUTES
Theorem UPDATE_EQ = combinTheory.UPDATE_EQ
Theorem UPDATE_def = combinTheory.UPDATE_def

(* ------------------------------------------------------------------------ *)
