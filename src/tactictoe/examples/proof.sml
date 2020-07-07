load "tacticToe"; open tacticToe;
load "dividesTheory"; load "gcdTheory";

val thm1 = tactictoe ``(a * a = 2 * (b * b)) ==> divides 2 a``;

val thm2_l1 = tactictoe ``divides x y ==> divides (x * x) (y * y)``;
val thm2_l2 = METIS_PROVE [thm2_l1] ``divides 2 a ==> divides (2 * 2) (a * a)``;
val thm2_l3 = tactictoe ``(a * a = 2 * (b * b)) ==> divides (2 * 2) (2 * (b * b))``;

val thm2_l4 = tactictoe ``divides (2 * a) (2 * b) ==> divides a b``;
val thm2_l5 = tactictoe ``divides (2 * 2) (2 * (b * b)) ==> divides 2 (b * b)``;
val thm2_l6 = tactictoe ``divides 2 (b * b) ==> divides 2 b``;
val thm2_l7 = tactictoe ``divides (2 * 2) (2 * (b * b)) ==> divides 2 b``;
val thm2 = tactictoe ``(a * a = 2 * (b * b)) ==> divides 2 b``;

val thm3 = tactictoe ``divides 2 a /\ divides 2 b ==> divides 2 (gcd a b)``;
val thm4 = tactictoe ``~(divides 2 1)``;
val thm5 = tactictoe ``~ ((divides 2 a /\ divides 2 b) /\ (gcd a b = 1))``;

val thm6 = tactictoe ``~((a * a = 2 * (b * b)) /\ (gcd a b = 1))``;
