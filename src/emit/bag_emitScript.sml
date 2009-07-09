open HolKernel boolLib bossLib Parse;
open EmitML bagTheory;
open set_emitTheory;

val _ = new_theory "bag_emit";

(*---------------------------------------------------------------------------*)
(* The ML representation of bags is a datatype, not a function. So we need   *)
(* to re-create the functional aspect, via BAG_VAL.                          *)
(*---------------------------------------------------------------------------*)

fun ARITH q = EQT_ELIM (numLib.ARITH_CONV (Parse.Term q));

val BAG_VAL_DEF = Q.new_definition
("BAG_VAL_DEF",`BAG_VAL b x = b(x)`);

val BAG_VAL_THM = Q.prove
(`(!x. BAG_VAL EMPTY_BAG x = 0) /\
  (!x b e. BAG_VAL (BAG_INSERT e b) x =
     if (e=x) then 1 + BAG_VAL b x else BAG_VAL b x)`,
 CONJ_TAC THENL
 [RW_TAC arith_ss [EMPTY_BAG,BAG_VAL_DEF],
  RW_TAC arith_ss [BAG_VAL_DEF] THEN METIS_TAC [BAG_VAL_DEF,BAG_INSERT]]);

val BAG_IN_EQNS = Q.prove
(`(!x. BAG_IN x {||} = F) /\
  !x y. BAG_IN x (BAG_INSERT y b) = (x = y) \/ BAG_IN x b`,
METIS_TAC [NOT_IN_EMPTY_BAG,BAG_IN_BAG_INSERT]);

val BAG_INN_EQN = Q.prove
(`BAG_INN e n b = BAG_VAL b e >= n`,
 RW_TAC arith_ss [BAG_VAL_DEF, BAG_INN]);

val BAG_DIFF_EQNS = Q.store_thm
("BAG_DIFF_EQNS",
 `(!b:'a bag. BAG_DIFF b {||} = b) /\
  (!b:'a bag. BAG_DIFF {||} b = {||}) /\
  (!(x:'a) b (y:'a). BAG_DIFF (BAG_INSERT x b) {|y|} =
            if x = y then b else BAG_INSERT x (BAG_DIFF b {|y|})) /\
  (!(b1:'a bag) y (b2:'a bag).
      BAG_DIFF b1 (BAG_INSERT y b2) = BAG_DIFF (BAG_DIFF b1 {|y|}) b2)`,
 RW_TAC arith_ss [BAG_DIFF,FUN_EQ_THM,BAG_INSERT,EMPTY_BAG] THEN
 RW_TAC arith_ss []);

val BAG_INTER_EQNS = Q.store_thm
("BAG_INTER_EQNS",
 `(!b:'a bag. BAG_INTER {||} b = {||}) /\
  (!b: 'a bag. BAG_INTER b {||} = {||}) /\
  (!(x:'a) b1 (b2:'a bag).
     BAG_INTER (BAG_INSERT x b1) b2 =
        if BAG_IN x b2
           then BAG_INSERT x (BAG_INTER b1 (BAG_DIFF b2 {|x|}))
           else BAG_INTER b1 b2)`,
 RW_TAC arith_ss [BAG_INTER, EMPTY_BAG,FUN_EQ_THM,BAG_INSERT,BAG_DIFF]
 THEN RW_TAC arith_ss []
 THEN FULL_SIMP_TAC arith_ss []
 THEN RW_TAC arith_ss []
 THEN FULL_SIMP_TAC arith_ss [BAG_IN, BAG_INN]
 THEN REPEAT (POP_ASSUM MP_TAC)
 THEN RW_TAC arith_ss []);

val BAG_MERGE_EQNS = Q.store_thm
("BAG_MERGE_EQNS",
 `(!b:'a bag. BAG_MERGE {||} b = b) /\
  (!b:'a bag. BAG_MERGE b {||} = b) /\
  (!x:'a. !b1 b2:'a bag.
         BAG_MERGE (BAG_INSERT x b1) b2 =
             BAG_INSERT x (BAG_MERGE b1 (BAG_DIFF b2 {|x|})))`,
 RW_TAC arith_ss [BAG_MERGE, EMPTY_BAG,FUN_EQ_THM,BAG_INSERT,BAG_DIFF]
 THEN RW_TAC arith_ss []
 THEN FULL_SIMP_TAC arith_ss []);

val SUB_BAG_EQNS = Q.store_thm
("SUB_BAG_EQNS",
 `(!b:'a bag. SUB_BAG {||} b = T) /\
  (!x:'a. !b1 b2:'a bag.
      SUB_BAG (BAG_INSERT x b1) b2 =
             BAG_IN x b2 /\ SUB_BAG b1 (BAG_DIFF b2 {|x|}))`,
 RW_TAC arith_ss [SUB_BAG_EMPTY,SUB_BAG, BAG_INSERT, BAG_INN,
          BAG_IN, BAG_DIFF,EMPTY_BAG, ARITH`!m. 0 >= m = (m=0n)`]
  THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RW_TAC arith_ss []
  THEN RW_TAC arith_ss []
  THEN POP_ASSUM MP_TAC THEN RW_TAC arith_ss [] THENL
  [FULL_SIMP_TAC bool_ss [ARITH `a+1n >= n = a >=n \/ (n=a+1)`]
   THENL [RES_TAC THEN FULL_SIMP_TAC arith_ss [],
         `b1(x) >= n-1` by DECIDE_TAC THEN
         RES_THEN MP_TAC THEN REWRITE_TAC [] THEN DECIDE_TAC],
  RES_THEN MP_TAC THEN ASM_REWRITE_TAC [] THEN DECIDE_TAC]);

val PSUB_BAG_LEM = Q.prove
(`!b1 b2.PSUB_BAG b1 b2 = SUB_BAG b1 b2 /\ ~SUB_BAG b2 b1`,
 METIS_TAC [SUB_BAG_PSUB_BAG,PSUB_BAG_ANTISYM]);

val SET_OF_BAG_EQNS = Q.prove
(`(SET_OF_BAG ({||}:'a bag) = ({}:'a set)) /\
  (!(x:'a) b. SET_OF_BAG (BAG_INSERT x b) = x INSERT (SET_OF_BAG b))`,
 REWRITE_TAC [SET_OF_BAG_INSERT] THEN
 RW_TAC arith_ss [SET_OF_BAG,EMPTY_BAG,FUN_EQ_THM,NOT_IN_EMPTY_BAG,
                pred_setTheory.EMPTY_DEF]);

val BAG_OF_SET_EQNS = Q.prove
(`(BAG_OF_SET ({}:'a set) = ({||}:'a bag)) /\
  (!(x:'a) (s:'a set).
      BAG_OF_SET (x INSERT s) = if x IN s then BAG_OF_SET s
                                 else BAG_INSERT x (BAG_OF_SET s))`,
 RW_TAC bool_ss [SET_OF_EMPTY] THEN
 RW_TAC arith_ss [BAG_OF_SET,FUN_EQ_THM,BAG_INSERT] THEN
 METIS_TAC [pred_setTheory.IN_INSERT]);

val defs =
  map DEFN_NOSIG
    [BAG_VAL_THM, BAG_IN_EQNS, BAG_INN_EQN,
     INST_TYPE [beta |-> alpha]
       (CONJ (CONJUNCT1 (CONJUNCT2 BAG_UNION_EMPTY))
             (CONJUNCT1 (SPEC_ALL (Q.SPEC `x` BAG_UNION_INSERT)))),
     BAG_DIFF_EQNS, BAG_INTER_EQNS, BAG_MERGE_EQNS,
     SUB_BAG_EQNS, PSUB_BAG_LEM,
     CONJ BAG_FILTER_EMPTY (BAG_FILTER_BAG_INSERT),
     CONJ (INST_TYPE [alpha |-> beta, beta |-> alpha] BAG_IMAGE_EMPTY)
          (UNDISCH (SPEC_ALL BAG_IMAGE_FINITE_INSERT)),
     CONJ BAG_CARD_EMPTY (UNDISCH (SPEC_ALL (CONJUNCT2 BAG_CARD_THM))),
     SET_OF_BAG_EQNS, (*BAG_OF_SET_EQNS,*)
     BAG_DISJOINT]

val (tyg,tmg) = (type_grammar(),term_grammar())
val tyg' = type_grammar.remove_abbreviation tyg "bag"
val _ = temp_set_grammars(tyg',tmg)
val _ = new_type("bag",1)

val _ = eSML "bag"
  (ABSDATATYPE (["'a"], `bag = EMPTY_BAG | BAG_INSERT of 'a => bag`)
   :: OPEN ["num", "set"]
   :: MLSIG "type num = numML.num"
   :: MLSIG "type 'a set = 'a setML.set"
   :: MLSIG "val EMPTY_BAG    : 'a bag"
   :: MLSIG "val BAG_INSERT   : 'a * 'a bag -> 'a bag"
   :: MLSIG "val BAG_VAL      : ''a bag -> ''a -> num"
   :: MLSIG "val BAG_IN       : ''a -> ''a bag -> bool"
   :: MLSIG "val BAG_INN      : ''a -> num -> ''a bag -> bool"
   :: MLSIG "val BAG_UNION    : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val BAG_DIFF     : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val BAG_INTER    : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val BAG_MERGE    : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val SUB_BAG      : ''a bag -> ''a bag -> bool"
   :: MLSIG "val PSUB_BAG     : ''a bag -> ''a bag -> bool"
   :: MLSIG "val BAG_DISJOINT : ''a bag -> ''a bag -> bool"
   :: MLSIG "val BAG_FILTER   : ('a -> bool) -> 'a bag -> 'a bag"
   :: MLSIG "val BAG_IMAGE    : ('a -> 'b) -> 'a bag -> 'b bag"
   :: MLSIG "val BAG_CARD     : 'a bag -> num"
   :: MLSIG "val SET_OF_BAG   : 'a bag -> 'a set"
(* :: MLSIG "val BAG_OF_SET   : ''a set -> ''a bag" *)
   :: defs)

(*
  (MLSIGSTRUCT ["type num = NumML.num", "type 'a set = 'a SetML.set", "",
       "type 'a bag = EMPTY_BAG | BAG_INSERT of 'a * 'a bag"]
*)

val _ = eCAML "bag"
  (MLSIGSTRUCT ["type num = NumML.num", "type 'a set = 'a SetML.set"] @
   ABSDATATYPE (["'a"], `bag = EMPTY_BAG | BAG_INSERT of 'a => bag`) ::
   OPEN ["num", "set"] ::
   map MLSIG
      ["val _BAG_VAL      : 'a bag -> 'a -> num",
       "val _BAG_IN       : 'a -> 'a bag -> bool",
       "val _BAG_INN      : 'a -> num -> 'a bag -> bool",
       "val _BAG_UNION    : 'a bag -> 'a bag -> 'a bag",
       "val _BAG_DIFF     : 'a bag -> 'a bag -> 'a bag",
       "val _BAG_INTER    : 'a bag -> 'a bag -> 'a bag",
       "val _BAG_MERGE    : 'a bag -> 'a bag -> 'a bag",
       "val _SUB_BAG      : 'a bag -> 'a bag -> bool",
       "val _PSUB_BAG     : 'a bag -> 'a bag -> bool",
       "val _BAG_DISJOINT : 'a bag -> 'a bag -> bool",
       "val _BAG_FILTER   : ('a -> bool) -> 'a bag -> 'a bag",
       "val _BAG_IMAGE    : ('a -> 'b) -> 'a bag -> 'b bag",
       "val _BAG_CARD     : 'a bag -> num",
       "val _SET_OF_BAG   : 'a bag -> 'a set",
       "val bag_of_list  : 'a list -> 'a bag",
       "val list_of_bag  : 'a bag -> 'a list"] @
   map MLSTRUCT
      ["let bag_of_list l = ListML._FOLDL (function s -> function a ->\n\
       \    BAG_INSERT(a,s)) EMPTY_BAG l", "",
       "let rec list_of_bag b = match b with EMPTY_BAG -> []\n\
       \  | BAG_INSERT(a,s) -> a::list_of_bag s", ""] @
   defs)

val _ = export_theory ();
