(*---------------------------------------------------------------------------
       Mapping finite sets (and bags) into lists. Needs a constraint
       that the set (bag) is finite. One might think to introduce this
       function via a constant specification, but in this case,
       TFL technology makes an easy job of it.
 ---------------------------------------------------------------------------*)

structure containerScript =
struct

open HolKernel boolLib pred_setTheory listTheory bagTheory
     Defn TotalDefn SingleStep BasicProvers;

(* ---------------------------------------------------------------------*)
(* Create the new theory.						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "container";

val _ = Defn.def_suffix := "";

(*---------------------------------------------------------------------------
       Map finite sets into lists.
 ---------------------------------------------------------------------------*)

val SET_TO_LIST_defn = Hol_defn "SET_TO_LIST"
  `SET_TO_LIST s =
     if FINITE s then
        if s={} then []
        else CHOICE s :: SET_TO_LIST (REST s)
     else ARB`;

(*---------------------------------------------------------------------------
       Termination of SET_TO_LIST.
 ---------------------------------------------------------------------------*)

val (SET_TO_LIST_EQN, SET_TO_LIST_IND) =
 Defn.tprove (SET_TO_LIST_defn,
   TotalDefn.WF_REL_TAC `measure CARD` THEN
   PROVE_TAC [CARD_PSUBSET, REST_PSUBSET]);

(*---------------------------------------------------------------------------
      Desired recursion equation.

      FINITE s |- SET_TO_LIST s = if s = {} then []
                               else CHOICE s::SET_TO_LIST (REST s)

 ---------------------------------------------------------------------------*)

val SET_TO_LIST_THM = save_thm("SET_TO_LIST_THM",
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME (Term`FINITE s`)] SET_TO_LIST_EQN));

val SET_TO_LIST_IND = save_thm("SET_TO_LIST_IND",SET_TO_LIST_IND);

(*---------------------------------------------------------------------------
      Map a list into a set.
 ---------------------------------------------------------------------------*)

val LIST_TO_SET_THM = Q.store_thm
("LIST_TO_SET_THM",
 `(LIST_TO_SET []     = {}) /\
  (LIST_TO_SET (h::t) = h INSERT (LIST_TO_SET t))`,
 SRW_TAC [][EXTENSION]);

val _ = export_rewrites ["LIST_TO_SET_THM"];


(*---------------------------------------------------------------------------
            Some consequences
 ---------------------------------------------------------------------------*)

val SET_TO_LIST_INV = Q.store_thm("SET_TO_LIST_INV",
`!s. FINITE s ==> (LIST_TO_SET(SET_TO_LIST s) = s)`,
 recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [LIST_TO_SET_THM]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, CHOICE_INSERT_REST]);

val SET_TO_LIST_CARD = Q.store_thm("SET_TO_LIST_CARD",
`!s. FINITE s ==> (LENGTH (SET_TO_LIST s) = CARD s)`,
 recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [listTheory.LENGTH,CARD_EMPTY]
   THEN RW_TAC bool_ss [REST_DEF, FINITE_DELETE]
   THEN `FINITE (REST s)` by PROVE_TAC [REST_DEF,FINITE_DELETE]
   THEN PROVE_TAC[CHOICE_INSERT_REST,CARD_INSERT,CHOICE_NOT_IN_REST,REST_DEF]);

val SET_TO_LIST_IN_MEM = Q.store_thm("SET_TO_LIST_IN_MEM",
`!s. FINITE s ==> !x. x IN s = MEM x (SET_TO_LIST s)`,
 recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [listTheory.MEM,NOT_IN_EMPTY]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, IN_INSERT, CHOICE_INSERT_REST]);

(* this version of the above is a more likely rewrite: a complicated LHS
   turns into a simple RHS *)
val MEM_SET_TO_LIST = Q.store_thm
("MEM_SET_TO_LIST",
 `!s. FINITE s ==> !x. MEM x (SET_TO_LIST s) = x IN s`,
 PROVE_TAC [SET_TO_LIST_IN_MEM]);

val _ = export_rewrites ["MEM_SET_TO_LIST"];

val UNION_APPEND = Q.store_thm
 ("UNION_APPEND",
  `!l1 l2.
     (LIST_TO_SET l1) UNION (LIST_TO_SET l2) = LIST_TO_SET (APPEND l1 l2)`,
  Induct
   THEN RW_TAC bool_ss [LIST_TO_SET_THM,UNION_EMPTY,listTheory.APPEND]
   THEN PROVE_TAC [INSERT_UNION_EQ]);

(* I think this version is the more likely rewrite *)
val LIST_TO_SET_APPEND = Q.store_thm
("LIST_TO_SET_APPEND",
 `!l1 l2. LIST_TO_SET (APPEND l1 l2) = LIST_TO_SET l1 UNION LIST_TO_SET l2`,
 REWRITE_TAC [UNION_APPEND]);
val _ = export_rewrites ["LIST_TO_SET_APPEND"]

val FINITE_LIST_TO_SET = Q.store_thm
("FINITE_LIST_TO_SET",
 `!l. FINITE (LIST_TO_SET l)`,
 Induct THEN SRW_TAC [][]);

val _ = export_rewrites ["FINITE_LIST_TO_SET"];

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
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME (Term`FINITE_BAG bag`)] BAG_TO_LIST_EQN));

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
