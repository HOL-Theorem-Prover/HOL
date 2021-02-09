(* Proof of irrationality of sqrt 2 *)
load "tacticToe"; open tacticToe;
load "dividesTheory";
load "gcdTheory";
load "arithmeticTheory";
open arithmeticTheory dividesTheory;
load "tttUnfold"; tttUnfold.ttt_record ();
mlibUseful.trace_level := 0;

(* 2 divides a *)
val thm1 = TAC_PROOF (([], ``(divides 2 (a*a)) ==> divides 2 a``),
  REWRITE_TAC [divides_def] THEN ttt);
val thm2 = tactictoe
``(a*a=2*(b*b)) ==> divides 2 (a*a)``;
val thm3 = tactictoe
``(a*a=2*(b*b)) ==> divides 2 a``;

(* 2 divides b *)
val thm4 = tactictoe
``divides 2 a ==> divides (2*2) (a*a)``;
val thm5 = tactictoe
``a*a=2*(b*b) ==> divides (2*2) (2*(b*b))``;
val thm6 = tactictoe
``divides (2*x) (2*y) ==> divides x y``;
val thm7 = tactictoe
``divides (2*2) (2*(b*b)) ==> divides 2 (b*b)``;
val thm8 = tactictoe
``a*a=2*(b*b) ==> divides 2 (b*b)``;
val thm9 = tactictoe
``a*a=2*(b*b) ==> divides 2 b``;

(* contradiction *)
val thm10 = tactictoe
``(divides 2 a /\ divides 2 b) ==> divides 2 (gcd a b)``;
val thm11 = tactictoe
``a*a=2*(b*b) ==> divides 2 (gcd a b)``;
val thm12 = tactictoe
``~ ((x = 1) /\ divides 2 x)``;
val thm13 = tactictoe
``~ (gcd a b = 1 /\ divides 2 (gcd a b))``;
val thm14 = tactictoe
``~ (gcd a b = 1 /\ a*a=2*(b*b))``;
