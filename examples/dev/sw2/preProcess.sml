
(*----------------------------------------------------------------------------------*)
(* Apply the rewrite rules in bool_ss to simplify boolean connectives and           *)
(*   conditional expressions                                                        *)
(* It contains all of the de Morgan theorems for moving negations in over the       *)
(* connectives (conjunction, disjunction, implication and conditional expressions). *)
(* It also contains the rules specifying the behaviour of the connectives when the  *)
(* constants T and F appear as their arguments.                                     *)
(* The arith_ss simpset extends std_ss by adding the ability to decide formulas of  *)
(* Presburger arithmetic, and to normalise arithmetic expressions                   *)
(*----------------------------------------------------------------------------------*)

val AND_COND = store_thm (
  "AND_COND",
  ``(if c1 /\ c2 then e1 else e2) = 
    let x = e2 in
      (if c1 then 
         if c2 then e1 else x
       else x)``,
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
  );

val OR_COND = store_thm (
  "OR_COND",
  ``(if c1 \/ c2 then e1 else e2) = 
    let x = e1 in
      (if c1 then x else
       if c2 then x else e2)``,
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
  );

val BRANCH_NORM = store_thm (
  "BRANCH_NORM",
  ``((if a > b then x else y) = (if a <= b then y else x)) /\ 
    ((if a >= b then x else y) = (if b <= a then x else y)) /\
    ((if a < b then x else y) = (if b <= a then y else x))
  ``,
   RW_TAC arith_ss [] THEN
   FULL_SIMP_TAC std_ss [arithmeticTheory.GREATER_DEF, arithmeticTheory.GREATER_EQ,
          arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL] THEN
   METIS_TAC [arithmeticTheory.LESS_EQ_ANTISYM]
  );

val PRE_PROCESS_RULE = SIMP_RULE arith_ss [AND_COND, OR_COND, BRANCH_NORM];
