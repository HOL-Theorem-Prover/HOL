(*---------------------------------------------------------------------------
       Mapping finite sets into lists. Needs a constraint that 
       the set is finite. One might think to introduce this 
       function via a constant specification, but in this case, 
       TFL technology makes an easy job of it.
 ---------------------------------------------------------------------------*)

structure containerScript =
struct

open HolKernel boolLib pred_setTheory listTheory SingleStep BasicProvers;

infix THEN; infix 8 by;


(* ---------------------------------------------------------------------*)
(* Create the new theory.						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "container";

(*---------------------------------------------------------------------------
       Map finite sets into lists.
 ---------------------------------------------------------------------------*)

val SET2LIST_defn = Defn.Hol_defn "SET2LIST"
  `SET2LIST s = 
     if FINITE s then 
        if s={} then []
        else CHOICE s :: SET2LIST (REST s) 
     else ARB`;

(*---------------------------------------------------------------------------
       Termination of SET2LIST.
 ---------------------------------------------------------------------------*)

val (SET2LIST_eqn0, SET2LIST_IND) =
 Defn.tprove (SET2LIST_defn,
   TotalDefn.WF_REL_TAC `measure CARD` THEN 
   PROVE_TAC [CARD_PSUBSET, REST_PSUBSET]);

(*---------------------------------------------------------------------------
      Desired recursion equation.

      FINITE s |- SET2LIST s = if s = {} then [] 
                               else CHOICE s::SET2LIST (REST s)

 ---------------------------------------------------------------------------*)

val SET2LIST_THM = save_thm("SET2LIST_THM",
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME (Term`FINITE s`)] SET2LIST_eqn0));

val SET2LIST_IND = save_thm("SET2LIST_IND",SET2LIST_IND);

(*---------------------------------------------------------------------------
      Map a list into a set.
 ---------------------------------------------------------------------------*)

val LIST2SET = Defn.eqns_of(
Defn.Hol_defn "LIST2SET"
   `(LIST2SET []     = {}) 
 /\ (LIST2SET (h::t) = h INSERT (LIST2SET t))`);


(*---------------------------------------------------------------------------
            Some consequences
 ---------------------------------------------------------------------------*)

val SET2LIST_INV = Q.store_thm("SET2LIST_INV",
`!s. FINITE s ==> (LIST2SET(SET2LIST s) = s)`,
 recInduct SET2LIST_IND
   THEN RW_TAC bool_ss [] 
   THEN ONCE_REWRITE_TAC [UNDISCH SET2LIST_THM]
   THEN RW_TAC bool_ss [LIST2SET]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, CHOICE_INSERT_REST]);

val SET2LIST_CARD = Q.store_thm("SET2LIST_CARD",
`!s. FINITE s ==> (LENGTH (SET2LIST s) = CARD s)`,
 recInduct SET2LIST_IND
   THEN RW_TAC bool_ss [] 
   THEN ONCE_REWRITE_TAC [UNDISCH SET2LIST_THM]
   THEN RW_TAC bool_ss [listTheory.LENGTH,CARD_EMPTY]
   THEN RW_TAC bool_ss [REST_DEF, FINITE_DELETE]
   THEN `FINITE (REST s)` by PROVE_TAC [REST_DEF,FINITE_DELETE]
   THEN PROVE_TAC[CHOICE_INSERT_REST,CARD_INSERT,CHOICE_NOT_IN_REST,REST_DEF]);

val SET2LIST_IN_MEM = Q.store_thm("SET2LIST_IN_MEM",
`!s. FINITE s ==> !x. x IN s = MEM x (SET2LIST s)`,
 recInduct SET2LIST_IND
   THEN RW_TAC bool_ss [] 
   THEN ONCE_REWRITE_TAC [UNDISCH SET2LIST_THM]
   THEN RW_TAC bool_ss [listTheory.MEM,NOT_IN_EMPTY]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, IN_INSERT, CHOICE_INSERT_REST]);


(*---------------------------------------------------------------------------
     Already have SET_OF_BAG and BAG_OF_SET in bagTheory.
 ---------------------------------------------------------------------------*)

val LIST2BAG = 
  Define 
    `(LIST2BAG [] = {||}) 
 /\  (LIST2BAG (h::t) = BAG_INSERT h (LIST2BAG t))`;

val BAG2LIST = Hol_defn "BAG2LIST"
    `BAG2LIST bag = 
       if FINITE_BAG bag
         then if bag = EMPTY_BAG then []
              else BAG_CHOICE bag :: BAG2LIST (BAG_REST bag)
         else ARB`;

val (BAG2LIST_EQN,BAG2LIST_IND) =
Defn.tprove
 (BAG2LIST,
  WF_REL_TAC `measure BAG_CARD`
   THEN PROVE_TAC [PSUB_BAG_CARD, PSUB_BAG_REST]);

val BAG2LIST_THM = 
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME (Term`FINITE_BAG bag`)] BAG2LIST_EQN);


(*
val BAG2LIST_INV = Q.store_thm("BAG2LIST_INV",
`!b. FINITE_BAG b ==> (LIST2BAG(BAG2LIST b) = b)`,
 recInduct BAG2LIST_IND
   THEN RW_TAC bool_ss [] 
   THEN ONCE_REWRITE_TAC [UNDISCH SET2LIST_THM]
   THEN RW_TAC bool_ss [LIST2SET]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, CHOICE_INSERT_REST]);

val SET2LIST_CARD = Q.store_thm("SET2LIST_CARD",
`!s. FINITE s ==> (LENGTH (SET2LIST s) = CARD s)`,
 recInduct SET2LIST_IND
   THEN RW_TAC bool_ss [] 
   THEN ONCE_REWRITE_TAC [UNDISCH SET2LIST_THM]
   THEN RW_TAC bool_ss [listTheory.LENGTH,CARD_EMPTY]
   THEN RW_TAC bool_ss [REST_DEF, FINITE_DELETE]
   THEN `FINITE (REST s)` by PROVE_TAC [REST_DEF,FINITE_DELETE]
   THEN PROVE_TAC[CHOICE_INSERT_REST,CARD_INSERT,CHOICE_NOT_IN_REST,REST_DEF]);

val SET2LIST_IN_MEM = Q.store_thm("SET2LIST_IN_MEM",
`!s. FINITE s ==> !x. x IN s = MEM x (SET2LIST s)`,
 recInduct SET2LIST_IND
   THEN RW_TAC bool_ss [] 
   THEN ONCE_REWRITE_TAC [UNDISCH SET2LIST_THM]
   THEN RW_TAC bool_ss [listTheory.MEM,NOT_IN_EMPTY]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, IN_INSERT, CHOICE_INSERT_REST]);
*)

(*---------------------------------------------------------------------------
      Also a connection to finite maps ?
 ---------------------------------------------------------------------------*)


val _ = export_theory ();

end;
