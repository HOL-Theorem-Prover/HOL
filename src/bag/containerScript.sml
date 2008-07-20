(*---------------------------------------------------------------------------
       Mapping finite sets (and bags) into lists. Needs a constraint
       that the set (bag) is finite. One might think to introduce this
       function via a constant specification, but in this case,
       TFL technology makes an easy job of it.
 ---------------------------------------------------------------------------*)

structure containerScript =
struct

open HolKernel Parse boolLib pred_setTheory listTheory bagTheory
     Defn TotalDefn SingleStep BasicProvers;

val export_rewrites = BasicProvers.export_rewrites "container";

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


val _ = export_theory ();

end;
