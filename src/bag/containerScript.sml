(*---------------------------------------------------------------------------
       Mapping finite sets (and bags) into lists. Needs a constraint
       that the set (bag) is finite. One might think to introduce this
       function via a constant specification, but in this case,
       TFL technology makes an easy job of it.
 ---------------------------------------------------------------------------*)

structure containerScript =
struct

open HolKernel Parse boolLib pred_setTheory listTheory bagTheory
     Defn TotalDefn SingleStep BasicProvers sortingTheory finite_mapTheory
     listSimps bossLib;

(* ---------------------------------------------------------------------*)
(* Create the new theory.						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "container";
  (* this theory may be for the chop; the set-related theorems are now all
     in listTheory.  The bag-related ones might end up there too if we
     decided to allow bag to move back in the build order.  Alternatively,
     the bag-related theorems could just go into bagTheory... *)

val SET_TO_LIST_THM = save_thm("SET_TO_LIST_THM", listTheory.SET_TO_LIST_THM)
val SET_TO_LIST_IND = save_thm("SET_TO_LIST_IND", listTheory.SET_TO_LIST_IND);

(*---------------------------------------------------------------------------
      Map a list into a set.
 ---------------------------------------------------------------------------*)

val LIST_TO_SET_THM = save_thm("LIST_TO_SET_THM", listTheory.LIST_TO_SET_THM)

(*---------------------------------------------------------------------------
            Some consequences
 ---------------------------------------------------------------------------*)

val SET_TO_LIST_INV = save_thm("SET_TO_LIST_INV", listTheory.SET_TO_LIST_INV)
val SET_TO_LIST_CARD = save_thm("SET_TO_LIST_CARD", listTheory.SET_TO_LIST_CARD)
val SET_TO_LIST_IN_MEM = save_thm("SET_TO_LIST_IN_MEM",
                                  listTheory.SET_TO_LIST_IN_MEM)
val MEM_SET_TO_LIST = save_thm("MEM_SET_TO_LIST", listTheory.MEM_SET_TO_LIST)
val SET_TO_LIST_SING = save_thm("SET_TO_LIST_SING", listTheory.SET_TO_LIST_SING)
val UNION_APPEND = save_thm("UNION_APPEND", listTheory.UNION_APPEND);
val LIST_TO_SET_APPEND = save_thm("LIST_TO_SET_APPEND",
                                  listTheory.LIST_TO_SET_APPEND)
val FINITE_LIST_TO_SET = save_thm("FINITE_LIST_TO_SET",
                                  listTheory.FINITE_LIST_TO_SET)

(*---------------------------------------------------------------------------
    Lists and bags. Note that we also have SET_OF_BAG and BAG_OF_SET
    in bagTheory.
 ---------------------------------------------------------------------------*)

val LIST_TO_BAG =
  Define
    `(LIST_TO_BAG [] = {||})
 /\  (LIST_TO_BAG (h::t) = BAG_INSERT h (LIST_TO_BAG t))`;

val BAG_TO_LIST = Hol_defn "BAG_TO_LIST"
    `BAG_TO_LIST bag =
       if FINITE_BAG bag
         then if bag = EMPTY_BAG then []
              else BAG_CHOICE bag :: BAG_TO_LIST (BAG_REST bag)
         else ARB`;

val (BAG_TO_LIST_EQN,BAG_TO_LIST_IND) =
Defn.tprove
 (BAG_TO_LIST,
  WF_REL_TAC `measure BAG_CARD`
   THEN PROVE_TAC [PSUB_BAG_CARD, PSUB_BAG_REST]);

val BAG_TO_LIST_THM = save_thm("BAG_TO_LIST_THM",
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME ``FINITE_BAG bag``] BAG_TO_LIST_EQN));

val BAG_TO_LIST_IND = save_thm("BAG_TO_LIST_IND",BAG_TO_LIST_IND);

(*---------------------------------------------------------------------------
       Some consequences.
 ---------------------------------------------------------------------------*)

val BAG_TO_LIST_INV = Q.store_thm("BAG_TO_LIST_INV",
`!b. FINITE_BAG b ==> (LIST_TO_BAG(BAG_TO_LIST b) = b)`,
 recInduct BAG_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH BAG_TO_LIST_THM]
   THEN RW_TAC bool_ss [LIST_TO_BAG]
   THEN PROVE_TAC [BAG_INSERT_CHOICE_REST,FINITE_SUB_BAG,SUB_BAG_REST]);


val BAG_TO_LIST_CARD = Q.store_thm("BAG_TO_LIST_CARD",
`!b. FINITE_BAG b ==> (LENGTH (BAG_TO_LIST b) = BAG_CARD b)`,
 recInduct BAG_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH BAG_TO_LIST_THM]
   THEN RW_TAC bool_ss [listTheory.LENGTH,CONJUNCT1 BAG_CARD_THM]
   THEN `FINITE_BAG (BAG_REST bag)` by PROVE_TAC [FINITE_SUB_BAG,SUB_BAG_REST]
   THEN RW_TAC bool_ss []
   THEN `BAG_CARD bag = BAG_CARD (BAG_REST bag) + 1` by
        PROVE_TAC [BAG_INSERT_CHOICE_REST, BAG_CARD_THM]
   THEN RW_TAC bool_ss [arithmeticTheory.ADD1]);


val BAG_IN_MEM = Q.store_thm("BAG_IN_MEM",
`!b. FINITE_BAG b ==> !x. BAG_IN x b = MEM x (BAG_TO_LIST b)`,
 recInduct BAG_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH BAG_TO_LIST_THM]
   THEN RW_TAC bool_ss [listTheory.MEM,NOT_IN_EMPTY_BAG]
   THEN PROVE_TAC [FINITE_SUB_BAG,SUB_BAG_REST,
                   BAG_INSERT_CHOICE_REST,BAG_IN_BAG_INSERT]);

(* version with the equation the "rewrite" way round *)
val MEM_BAG_TO_LIST = Q.store_thm
("MEM_BAG_TO_LIST",
 `!b. FINITE_BAG b ==> !x. MEM x (BAG_TO_LIST b) = BAG_IN x b`,
  PROVE_TAC [BAG_IN_MEM]);

val _ = export_rewrites ["MEM_BAG_TO_LIST"];



val LIST_TO_BAG_APPEND = store_thm ("LIST_TO_BAG_APPEND",
``!l1 l2.
LIST_TO_BAG (l1 ++ l2) =
BAG_UNION (LIST_TO_BAG l1) (LIST_TO_BAG l2)``,
Induct_on `l1` THENL [
  SIMP_TAC list_ss [LIST_TO_BAG, BAG_UNION_EMPTY],
  ASM_SIMP_TAC list_ss [LIST_TO_BAG, BAG_UNION_INSERT]
]);


val INN_LIST_TO_BAG = store_thm ("IN_LIST_TO_BAG",
``!n h l. BAG_INN h n (LIST_TO_BAG l) = (LENGTH (FILTER ($= h) l) >= n)``,
Induct_on `l` THENL [
  SIMP_TAC list_ss [LIST_TO_BAG, BAG_INN_EMPTY_BAG],
  ASM_SIMP_TAC list_ss [LIST_TO_BAG, BAG_INN_BAG_INSERT, COND_RAND, COND_RATOR]
]);


val IN_LIST_TO_BAG = store_thm ("IN_LIST_TO_BAG",
``!h l. BAG_IN h (LIST_TO_BAG l) = MEM h l``,
Induct_on `l` THENL [
  SIMP_TAC list_ss [LIST_TO_BAG, NOT_IN_EMPTY_BAG],
  ASM_SIMP_TAC list_ss [LIST_TO_BAG, BAG_IN_BAG_INSERT]
]);

val LIST_TO_BAG_EQ_EMPTY = store_thm ("LIST_TO_BAG_EQ_EMPTY",
``!l. (LIST_TO_BAG l = EMPTY_BAG) = (l = [])``,
Cases_on `l` THEN
SIMP_TAC list_ss [LIST_TO_BAG,
		  BAG_INSERT_NOT_EMPTY]);


val PERM_LIST_TO_BAG = store_thm ("PERM_LIST_TO_BAG",
``!l1 l2. (LIST_TO_BAG l1 = LIST_TO_BAG l2) = PERM l1 l2``,
SIMP_TAC std_ss [BAG_EXTENSION, INN_LIST_TO_BAG, PERM_DEF] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [] THEN
REWRITE_TAC[LIST_EQ_REWRITE] THEN
STRIP_TAC THEN GEN_TAC THEN

POP_ASSUM (ASSUME_TAC o Q.GEN `m` o Q.SPECL [`m`, `x`]) THEN
Q.ABBREV_TAC `m1 = LENGTH (FILTER ($= x) l1)` THEN
Q.ABBREV_TAC `m2 = LENGTH (FILTER ($= x) l2)` THEN
Q.PAT_ASSUM `!m. X` (fn thm => 
			ASSUME_TAC (Q.SPEC `m1` thm) THEN
			ASSUME_TAC (Q.SPEC `m2` thm)) THEN
FULL_SIMP_TAC arith_ss [] THEN
REPEAT STRIP_TAC THEN
`MEM (EL x' (FILTER ($= x) l1)) (FILTER ($= x) l1) /\
 MEM (EL x' (FILTER ($= x) l2)) (FILTER ($= x) l2)` by ALL_TAC THEN1 (
   `x' < m2` by bossLib.DECIDE_TAC THEN
   METIS_TAC[MEM_EL]
) THEN
FULL_SIMP_TAC list_ss [MEM_FILTER] THEN
METIS_TAC[]);





(*---------------------------------------------------------------------------
    finate  and bags. 
 ---------------------------------------------------------------------------*)

val BAG_OF_FMAP = Define `BAG_OF_FMAP f b =
  \x. CARD (\k. (k IN FDOM b) /\ (x = f k (b ' k)))`


val BAG_OF_FMAP_THM = store_thm ("BAG_OF_FMAP_THM",
``(!f. (BAG_OF_FMAP f FEMPTY = EMPTY_BAG)) /\
  (!f b k v. (BAG_OF_FMAP f (b |+ (k, v)) =
             BAG_INSERT (f k v) (BAG_OF_FMAP f (b \\ k))))``,
SIMP_TAC std_ss [BAG_OF_FMAP, FDOM_FEMPTY, NOT_IN_EMPTY, EMPTY_BAG,
		 combinTheory.K_DEF,
		 BAG_INSERT, FDOM_FUPDATE, IN_INSERT,
		 GSYM EMPTY_DEF, CARD_EMPTY] THEN
ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN SIMP_TAC std_ss [] THEN
Cases_on `x = f k v` THENL [  
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
     FAPPLY_FUPDATE_THM, FDOM_DOMSUB, IN_DELETE,
     DOMSUB_FAPPLY_THM] THEN
   `(\k'. ((k' = k) \/ k' IN FDOM b) /\
           (f k v = f k' ((if k' = k then v else b ' k')))) =
           k INSERT (\k'. (k' IN FDOM b /\ ~(k' = k)) /\ (f k v = f k' (b ' k')))` by ALL_TAC THEN1 (
     SIMP_TAC std_ss [EXTENSION, IN_INSERT, IN_ABS] THEN
     GEN_TAC THEN Cases_on `x' = k` THEN ASM_REWRITE_TAC[]
   ) THEN
   ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   Q.ABBREV_TAC `ks = (\k'. (k' IN FDOM b /\ k' <> k) /\ (f k v = f k' (b ' k')))` THEN
   `FINITE ks` by ALL_TAC THEN1 (
      Tactical.REVERSE (`ks = ks INTER FDOM b` by ALL_TAC) THEN1 (
         ONCE_ASM_REWRITE_TAC[] THEN
         MATCH_MP_TAC FINITE_INTER THEN
	 REWRITE_TAC[FDOM_FINITE]
      ) THEN
      Q.UNABBREV_TAC `ks` THEN
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
      PROVE_TAC[]
   ) THEN
   `~(k IN ks)` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `ks` THEN
      SIMP_TAC std_ss [IN_ABS]
   ) THEN
   ASM_SIMP_TAC arith_ss [CARD_INSERT],


   FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
      FAPPLY_FUPDATE_THM, FDOM_DOMSUB, IN_DELETE,
      DOMSUB_FAPPLY_THM] THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN SIMP_TAC std_ss [] THEN
   Cases_on `x' = k` THEN (
      ASM_SIMP_TAC std_ss []
   )
]);



val BAG_IN_BAG_OF_FMAP = store_thm ("BAG_IN_BAG_OF_FMAP",
``!x f b. BAG_IN x (BAG_OF_FMAP f b) =
          ?k. k IN FDOM b /\ (x = f k (b ' k))``,
SIMP_TAC std_ss [BAG_OF_FMAP, BAG_IN, BAG_INN] THEN
`!X. (X >= (1:num)) = ~(X = 0)` by bossLib.DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT GEN_TAC THEN
`FINITE (\k. k IN FDOM b /\ (x = f k (b ' k)))` by ALL_TAC THEN1 (
   `(\k. k IN FDOM b /\ (x = f k (b ' k))) =
    (\k. k IN FDOM b /\ (x = f k (b ' k))) INTER (FDOM b)` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
      METIS_TAC[]
   ) THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FINITE_INTER THEN
   REWRITE_TAC[FDOM_FINITE]
) THEN
ASM_SIMP_TAC std_ss [CARD_EQ_0] THEN
SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS]);



val FINITE_BAG_OF_FMAP = store_thm ("FINITE_BAG_OF_FMAP",
``!f b. FINITE_BAG (BAG_OF_FMAP f b)``,
GEN_TAC THEN HO_MATCH_MP_TAC fmap_INDUCT THEN
SIMP_TAC std_ss [BAG_OF_FMAP_THM, FINITE_EMPTY_BAG,
                 DOMSUB_NOT_IN_DOM, FINITE_BAG_INSERT]);



val _ = export_theory ();

end;
