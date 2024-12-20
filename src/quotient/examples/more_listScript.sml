open HolKernel Parse boolLib;

val _ = new_theory "more_list";


(*
app load [
          "numTheory", "listTheory", "rich_listTheory", "listLib", "pred_setLib",
          "more_setTheory",
          "arithLib", "Psyntax" ];
*)

open combinTheory numTheory arithmeticTheory
     listTheory rich_listTheory listLib more_setTheory
     numLib Psyntax ;


open tactics;



val MAP2_APPEND = store_thm
   ("MAP2_APPEND",
    “!s1 s2 t1 t2 (f:'a->'b->'c).
          (LENGTH s1 = LENGTH s2) ==>
          (MAP2 f (APPEND s1 t1) (APPEND s2 t2) =
          APPEND (MAP2 f s1 s2) (MAP2 f t1 t2))”,
    LIST_INDUCT_TAC
    THENL
       [ LIST_INDUCT_TAC
         THEN REWRITE_TAC[LENGTH,APPEND,MAP2,SUC_NOT],

         GEN_TAC
         THEN LIST_INDUCT_TAC
         THEN REWRITE_TAC[LENGTH,NOT_SUC]
         THEN REWRITE_TAC[ADD1,EQ_MONO_ADD_EQ]
         THEN REWRITE_TAC[APPEND,MAP2]
         THEN REPEAT GEN_TAC
         THEN DISCH_TAC
         THEN RES_TAC
         THEN ASM_REWRITE_TAC[]
      ]
   );

val AND_EL = store_thm
   ("AND_EL",
    “(AND_EL [] = T) /\
        (!x l. AND_EL (CONS x l) = (x /\ AND_EL l))”,
    REWRITE_TAC[AND_EL_DEF]
    THEN REWRITE_TAC[ALL_EL]
    THEN REWRITE_TAC[combinTheory.I_THM]
   );

val AND_EL_APPEND = store_thm
   ("AND_EL_APPEND",
    “!s t. AND_EL (APPEND s t) = (AND_EL s /\ AND_EL t)”,
    REWRITE_TAC[AND_EL_DEF]
    THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[APPEND,ALL_EL]
    THEN ASM_REWRITE_TAC[CONJ_ASSOC]
   );

(* =============================================================== *)
(* LENGTH_FILTER says that if we filter a list into two using P    *)
(* as a predicate, then the sum of the lengths of the two parts    *)
(* must equal the length of the whole.                             *)
(* =============================================================== *)

val LENGTH_FILTER = store_thm
   ("LENGTH_FILTER",
    “!(l:'a list) P.
          LENGTH (FILTER P l) + LENGTH (FILTER ($~ o P) l) = LENGTH l”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER]
    THENL
       [ REWRITE_TAC[LENGTH,ADD_0],

         REWRITE_TAC[o_THM]
         THEN REPEAT GEN_TAC
         THEN COND_CASES_TAC
         THEN ASM_REWRITE_TAC[LENGTH,ADD_CLAUSES]
      ]
   );

(* =============================================================== *)
(* Applying LENGTH_FILTER to a specific filter, we can calculate   *)
(* the length of the partitions of num lists where the partition   *)
(* separates the bottom of a range from the larger members.        *)
(* For all lists of numbers l, the number of elements of value n   *)
(* or more equals the number of elements of value n plus the       *)
(* number of elements of value more than n.                        *)
(* =============================================================== *)

Theorem LENGTH_FILTER_LESS_EQ:
  !l n.  LENGTH (FILTER (\y. n = y) l) + LENGTH (FILTER (\y. n < y) l) =
         LENGTH (FILTER (\y. n <= y) l)
Proof
    REWRITE_TAC
    [(GENL [“l:num list”,“n:num”]
      o REWRITE_RULE[ARITH_PROVE “ (n=y) /\ (n <= y) <=> (n = y)”,
                     ARITH_PROVE “~(n=y) /\ (n <= y) <=> (n < y)”]
      o CONV_RULE (DEPTH_CONV BETA_CONV)
      o REWRITE_RULE[FILTER_FILTER,o_THM]
      o ISPECL[“FILTER (\y. n <= y) l”,“\y:num. n = y”])
     LENGTH_FILTER]
QED


(*
FILTER_MAP;
    |- !f1 f2 l. FILTER f1 (MAP f2 l) = MAP f2 (FILTER (f1 o f2) l)
*)


val SL =
    new_recursive_definition
      {rec_axiom = listTheory.list_Axiom,
       name      = "SL",
       def       = “(SL NIL = {}) /\
                       (SL (CONS (y:'a) l) = y INSERT (SL l))”};


val SL_APPEND = store_thm
  ("SL_APPEND",
 “!(l1: 'a list) l2. SL (APPEND l1 l2) = (SL l1 UNION SL l2)”,
    LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[APPEND,SL,UNION]
   );


val SL_FLAT = store_thm
  ("SL_FLAT",
 “!(l: 'a list list). SL (FLAT l) = UNION_SET (SL (MAP SL l))”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[FLAT,MAP,SL,UNION_SET]
    THEN ASM_REWRITE_TAC[SL_APPEND]
   );

val SL_MAP = store_thm
  ("SL_MAP",
 “!l (f: 'a->'b). SL (MAP f l) = IMAGE f (SL l)”,
    LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[MAP,SL,IMAGE]
   );

val DELETE_DIFF_SL =
 store_thm
  ("DELETE_DIFF_SL",
   “!xs s (e:'a).
        s DELETE e DIFF SL xs = s DIFF SL (e::xs)”,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC[SL,DIFFF]
  );


val DL =
    new_recursive_definition
      {rec_axiom = listTheory.list_Axiom,
       name      = "DL",
       def       = “(DL NIL = T) /\
                       (DL (CONS (y:'a) l) = (~(y IN SL l) /\ DL l))”};



val _ = export_theory();

val _ = print_theory_to_file "-" "more_list.lst";

val _ = html_theory "more_list";
