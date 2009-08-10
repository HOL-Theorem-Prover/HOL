structure preProcess  =
struct

local

(* quietdec := true; *)

open HolKernel Parse boolSyntax boolLib bossLib pairSyntax;

(* quietdec := false; *)

in

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

(* Conjunction in condtions *)
val AND_COND = Q.prove
 (`(if c1 /\ c2 then e1 else e2) =
     let x = e2 in
      (if c1 then
         if c2 then e1 else x
       else x)`,
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
  );

(* Disjunction in condtions *)
val OR_COND = Q.prove (
  `(if c1 \/ c2 then e1 else e2) =
    let x = e1 in
      (if c1 then x else
       if c2 then x else e2)`,
   RW_TAC std_ss [LET_THM] THEN
   METIS_TAC []
  );

(* Normalize the conditions in branches *)
val BRANCH_NORM = Q.prove (
  `((if a > b then x else y) = (if a <= b then y else x)) /\
    ((if a >= b then x else y) = (if b <= a then x else y)) /\
    ((if a < b then x else y) = (if b <= a then y else x))
  `,
   RW_TAC arith_ss [] THEN
   FULL_SIMP_TAC std_ss [arithmeticTheory.GREATER_DEF, arithmeticTheory.GREATER_EQ,
          arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL] THEN
   METIS_TAC [arithmeticTheory.LESS_EQ_ANTISYM]
  );

(* Pre-processing *)
val PRE_PROCESS_RULE = SIMP_RULE arith_ss [AND_COND, OR_COND, BRANCH_NORM];

(*---------------------------------------------------------------------------*)

end (* local *)

end (* struct *)
