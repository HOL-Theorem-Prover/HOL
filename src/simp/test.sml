load"simpLib";
open Simplifier Simpsets arith_ss ;
infix ++;
trace_level := 5;
quotation := true; open Parse;

(* reduction in operand *)
SIMP_PROVE bool_ss [] (--`((P:'a) = P') ==> (P' = P)`--);

(* reduction in operand *)
SIMP_PROVE bool_ss [] (--`((P:'a) = P') ==> ((Q P:'b) = Q P')`--);

(* reduction in operator *)
SIMP_PROVE bool_ss [] (--`(P = P') ==> (P (Q:'a) = (P' Q:'b))`--);

(* reductions in both *)
SIMP_PROVE bool_ss [] (--`(P = P') /\ (Q = Q') ==> ((P:'b->'a) Q = P' Q')`--);

(* reduction inside abs. *)
SIMP_PROVE bool_ss [] (--`(P = P') ==> ((!x:'a. P x) = (!x. P' x))`--);

(* solving side conditions with a dproc (SATISFY) *)

(* making reductions with a dproc *)
(*Fails! *)
val ss = mk_simpset [BOOL_ss,SATISFY_ss];
SIMP_PROVE ss [] (--`Q 0 1 ==> ?x y. Q x y`--);;
SIMP_PROVE ss [] (--`Q 1 1 /\ (!z:num. R z 0) ==> ?x y z. Q x y /\ R z 0`--);;

(* making reductions with a conversion (BETA_CONV) *)
SIMP_PROVE bool_ss [] (--`(\x. Q x 0:num) 1 = Q 1 0`--);;

(* unwinding *)
val ss = mk_simpset [BOOL_ss,UNWIND_ss];
SIMP_CONV ss [] (--`?a b:num. (0 = a) /\ P a b`--);;
SIMP_CONV ss [] (--`!a b:num. (1 + 2 = a) ==> P a b`--);;
SIMP_CONV ss [] (--`!a b:num. G ==> R /\ (3 = a) ==> P a b`--);;

(* reprocessing of non-trivial context
Before adding reprocessing the "else" branch of the following
would not have been simplified *)

SIMP_PROVE bool_ss [boolTheory.DE_MORGAN_THM]
      (--`((P \/ Q) => x | ~P) = (P \/ Q ==> x)`--);


(* multiple beta convs *)
SIMP_CONV bool_ss [] (--`(\x y z. P x y z:num) 1 2 3`--);

(* arithmetic *)
trace_level := 1;;
SIMP_PROVE arith_ss [] (--`P (x + 2) = (P (2 + x):'a)`--);

SIMP_CONV arith_ss [] (--`1 < 2 => 3 | 4`--);
SIMP_CONV arith_ss [] (--`(x > z + 1) /\ ( y + 1 > x + 1) => (y > x) | Z`--);
SIMP_CONV arith_ss [] (--`(x > 20 + 1) /\ ( y + 1 > x + 1) => (y > 15) | Z`--);
profile2 SIMP_CONV arith_ss (--`(x > z + 1) /\ ( y + 1 > x + 1) => (y > x) | Z`--);


(* cached arithmetic *)
CACHED_ARITH [] (--`1 < 2`--);;
CACHED_ARITH [] (--`1 < 2`--);;  (* cache hit - success *)
CACHED_ARITH [] (--`3 < 1`--);;
CACHED_ARITH [] (--`3 < 1`--);; (* cache hit, failure *)

(* semi-congruence closure via conditional rewriting *)
val CC = SIMP_PROVE bool_ss [] (--`!P:'a->'b. (x = x') ==> (P x = P x')`--);
val CC2 = SIMP_PROVE bool_ss [] (--`!P:'a->'b->'c. (x = x') /\ (y = y') ==> (P x y = P x' y')`--);
SIMP_PROVE arith_ss [CC,CC2] (--`y >= z ==> z >= y ==> (P y (x + 2):bool = P z (2 + x))`--);








