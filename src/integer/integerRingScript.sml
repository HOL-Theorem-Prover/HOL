(*
load "ringLib";
load "integerTheory";
load "bossLib";
*)

open HolKernel Parse boolLib bossLib integerTheory ringTheory;

infix THEN THENL THENC o;
infix 8 by;

val _ = new_theory "integerRing";

val ARW_TAC = RW_TAC arith_ss;

val int_is_ring = store_thm
    ("int_is_ring",
     --`is_ring (ring int_0 int_1 $+ $* $~)`--,
ARW_TAC [ is_ring_def, ring_accessors, INT_0, INT_1,
          INT_ADD_RINV, INT_RDISTRIB,
          INT_ADD_ASSOC, INT_MUL_ASSOC, INT_ADD_LID, INT_MUL_LID] THEN
MAP_FIRST MATCH_ACCEPT_TAC [ INT_ADD_SYM, INT_MUL_SYM ]);

val int_ring_thms = ringLib.store_ring { Name = "int", Theory = int_is_ring };


(* equations to put any expression build on + * ~ & int_0 int_1
   under the (unique) following forms:  &n  or ~&n *)
val int_calculate = store_thm
    ("int_calculate",
     --`    ( &n +  &m = &(n+m))
         /\ (~&n +  &m = if n<=m then &(m-n) else ~&(n-m))
         /\ ( &n + ~&m = if m<=n then &(n-m) else ~&(m-n))
         /\ (~&n + ~&m = ~&(n+m))

         /\ ( &n *  &m =  &(n*m))
         /\ (~&n *  &m = ~&(n*m))
         /\ ( &n * ~&m = ~&(n*m))
         /\ (~&n * ~&m =  &(n*m))

         /\ (( &n =  &m) = (n=m)) 
         /\ (( &n = ~&m) = (n=0)/\(m=0))
         /\ ((~&n =  &m) = (n=0)/\(m=0))
         /\ ((~&n = ~&m) = (n=m))

         /\ (~~x = x : int)
         /\ (~0 = 0 : int)   `--,
REWRITE_TAC [INT_ADD_CALCULATE,INT_MUL_CALCULATE,INT_EQ_CALCULATE]);


(* Note: AND_CLAUSES is not lazy *)
local open numeralTheory
in
val int_rewrites = save_thm("int_rewrites", LIST_CONJ
  [ int_calculate, INT_0, INT_1,
    numeral_lt, numeral_lte, numeral_sub, iSUB_THM, AND_CLAUSES ]);
end;

val _ = export_theory();
