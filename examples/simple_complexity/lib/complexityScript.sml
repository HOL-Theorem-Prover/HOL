(* ------------------------------------------------------------------------- *)
(* Computational Complexity                                                  *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "complexity";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory arithmeticTheory dividesTheory gcdTheory
     listTheory rich_listTheory logrootTheory numberTheory combinatoricsTheory
     primeTheory;

open bitsizeTheory;

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Computational Complexity Documentation                                    *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
   f1 .+. f2          = fun_sum f1 f2
   f1 .*. f2          = fun_prod f1 f2
   s1 |+| s2          = set_sum s1 s2
   s1 |*| s2          = set_prod s1 s2
   poly_O m           = big_O (POLY m)
   O_poly n           = big_O ((POLY n) o size)
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Big O Notation:
   big_O_def           |- !g. big_O g = {f | ?k c. !n. k < n ==> f n <= c * g n}
   big_O_element       |- !f g. f IN big_O g <=> ?k c. !n. k < n ==> f n <= c * g n
   big_O_self          |- !g. g IN big_O g
   big_O_cong          |- !f1 f2 g. f1 IN big_O g /\ (!n. f1 n = f2 n) ==> f2 IN big_O g
   big_O_has_zero      |- !g. K 0 IN big_O g
   big_O_1             |- !m. K m IN big_O (K 1)
   big_O_nonempty      |- !g. big_O g <> {}

   Sum and Product of Functions and Sets:
   fun_sum_def         |- !f1 f2. (f1 .+. f2) = (\n. f1 n + f2 n)
   fun_prod_def        |- !f1 f2. (f1 .*. f2) = (\n. f1 n * f2 n)
   set_sum_def         |- !s1 s2. s1 |+| s2 = {f1 .+. f2 | f1 IN s1 /\ f2 IN s2}
   set_sum_element     |- !f1 f2 s1 s2. f1 IN s1 /\ f2 IN s2 ==> f1 .+. f2 IN s1 |+| s2
   set_sum_eqn         |- !f1 f2 s1 s2 x. x IN s1 |+| s2 <=> ?f1 f2. f1 IN s1 /\ f2 IN s2 /\ x = f1 .+. f2
   set_prod_def        |- !s1 s2. s1 |*| s2 = {f1 .*. f2 | f1 IN s1 /\ f2 IN s2}
   set_prod_element    |- !f1 f2 s1 s2. f1 IN s1 /\ f2 IN s2 ==> f1 .*. f2 IN s1 |*| s2
   set_prod_eqn        |- !f1 f2 s1 s2 x. x IN s1 |*| s2 <=> ?f1 f2. f1 IN s1 /\ f2 IN s2 /\ x = f1 .*. f2
   fun_sum_comm        |- !f1 f2. f1 .+. f2 = f2 .+. f1
   fun_sum_assoc       |- !f1 f2 f3. f1 .+. f2 .+. f3 = f1 .+. (f2 .+. f3)
   fun_prod_comm       |- !f1 f2. f1 .*. f2 = f2 .*. f1
   fun_prod_assoc      |- !f1 f2 f3. f1 .*. f2 .*. f3 = f1 .*. (f2 .*. f3)
   fun_sum_zero        |- !f. f .+. K 0 = f /\ K 0 .+. f = f
   fun_prod_one        |- !f. f .*. K 1 = f /\ K 1 .*. f = f
   fun_sum_mono        |- !f1 f2. MONO f1 /\ MONO f2 ==> MONO (f1 .+. f2)
   fun_prod_mono       |- !f1 f2. MONO f1 /\ MONO f2 ==> MONO (f1 .*. f2)

   Theorems for Complexity Class:
   big_O_sum           |- !f1 f2 g1 g2. f1 IN big_O g1 /\ f2 IN big_O g2 ==> f1 .+. f2 IN big_O (g1 .+. g2)
   big_O_sum_subset    |- !g1 g2. big_O g1 |+| big_O g2 SUBSET big_O (g1 .+. g2)
   big_O_prod          |- !f1 f2 g1 g2. f1 IN big_O g1 /\ f2 IN big_O g2 ==> f1 .*. f2 IN big_O (g1 .*. g2)

   Big O Classes:
   big_O_linear        |- !f1 f2 g. f1 IN big_O g /\ f2 IN big_O g ==>
                          !a b. (\n. a * f1 n + b * f2 n) IN big_O g
   big_O_add           |- !f1 f2 g. f1 IN big_O g /\ f2 IN big_O g ==> f1 .+. f2 IN big_O g
   big_O_sum_self      |- !g. big_O g |+| big_O g = big_O g

   Poly O Classes:
   POLY_def            |- !m. POLY m = (\n. n ** m)
   POLY_0              |- POLY 0 = K 1
   POLY_1              |- POLY 1 = I
   POLY_ascending      |- !m. MONO (POLY m)
   poly_O_has_poly     |- !m. POLY m IN poly_O m
   poly_O_add_constant |- !f m. f IN poly_O m ==> !c. (\n. f n + c) IN poly_O m
   poly_O_mult_constant|- !f m. f IN poly_O m ==> !c. (\n. c * f n) IN poly_O m
   poly_O_nonempty     |- !n. poly_O n <> {}
   poly_O_constant     |- !c0. K c0 IN poly_O 0
   big_O_poly_sum      |- !a b. big_O (POLY a .+. POLY b) SUBSET poly_O (MAX a b)
   big_O_poly_sum_3    |- !a b c. big_O ((POLY a .+. POLY b) .+. POLY c) SUBSET poly_O (MAX (MAX a b) c)
   big_O_sum_poly      |- !f g a b. f IN poly_O a /\ g IN poly_O b ==> f .+. g IN poly_O (MAX a b)
   big_O_poly_prod     |- !a b. big_O (POLY a .*. POLY b) SUBSET poly_O (a + b)
   big_O_poly_prod_3   |- !a b c. big_O ((POLY a .*. POLY b) .*. POLY c) SUBSET poly_O (a + b + c)
   big_O_prod_poly     |- !f g a b. f IN poly_O a /\ g IN poly_O b ==> f .*. g IN poly_O (a + b)
   big_O_poly          |- !a b. (\n. a * n ** b) IN poly_O b
   big_O_example       |- !n. (\n. n ** 3 + TWICE n + 10) IN poly_O 3
   poly_O_linear       |- !c0 c1. (\n. c1 * n + c0) IN poly_O 1
   poly_O_quadratic    |- !c0 c1 c2. (\n. c2 * n ** 2 + c1 * n + c0) IN poly_O 2
   poly_O_constant_exists  |- !s t c. ?g. g IN poly_O 0 /\ t + c <= g s + t
   poly_O_linear_exists    |- !n s t b c. n <= s ==> ?g. g IN poly_O 1 /\ t + (b * n + c) <= g s + t
   poly_O_quadratic_exists |- !n s t a b c. n <= s ==>
                              ?g. g IN poly_O 2 /\ t + (a * n ** 2 + b * n + c) <= g s + t

   poly_O_has_constant |- !m. big_O (K 1) SUBSET poly_O m
   poly_O_multiple     |- !f m. f IN poly_O m ==> !a. (\n. f (a * n)) IN poly_O m
   poly_O_add_linear   |- !f1 f2 m. f1 IN poly_O m /\ f2 IN poly_O m ==>
                          !a b. (\n. f1 (a * n) + f2 (b * n)) IN poly_O m
   poly_O_subset       |- !m n. m <= n ==> poly_O m SUBSET poly_O n
   poly_O_sum          |- !n. poly_O n |+| poly_O n = poly_O n
   poly_O_sum_subset   |- !m n. poly_O n |+| poly_O m SUBSET poly_O (MAX n m)

   Big O theorem with size:
   big_O_K_subset            |- !f. FUN_POS f ==> !c. big_O (K c) SUBSET big_O f
   big_O_compose_K           |- !f1 f2 c. MONO f1 /\ f2 IN big_O (K c) ==>
                                      ?d. f1 o f2 IN big_O (K d)
   big_O_constant            |- !g c. FUN_POS g ==> K c IN big_O g
   POLY_size_pos             |- !k x. 0 < (POLY k o size) x
   big_O_size_linear         |- !a b. (\n. a * size n + b) IN big_O size
   big_O_size_linear_0       |- !a. (\n. a * size n) IN big_O size
   big_O_size_quadratic      |- !a b c. (\n. a * size n ** 2 + b * size n + c) IN O_poly 2
   big_O_size_quadratic_0    |- !a. (\n. a * size n ** 2) IN O_poly 2
   big_O_size_quadratic_1    |- !a b. (\n. a * size n ** 2 + b * size n) IN O_poly 2
   big_O_size_quadratic_2    |- !a b. (\n. a * size n ** 2 + b) IN O_poly 2
   big_O_dominance           |- !f1 f2 g k.
                                (!n. k < n ==> f1 n <= f2 n) /\ f2 IN big_O g ==> f1 IN big_O g

   Polynomial Complexity Class:
   O_poly_thm    |- !f m. f IN O_poly m <=> ?h k. !n. h < n ==> f n <= k * size n ** m
   O_poly_good   |- !f m. f IN O_poly m <=> ?h k. 0 < k /\ !n. h < n ==> f n <= k * size n ** m
   O_poly_eq_O_poly_ulog
                 |- !n. O_poly n = big_O (POLY n o ulog)
   big_O_poly_eq_O_poly
                 |- !c n. 0 < c ==> big_O (POLY 1 o (\x. c * size x ** n)) = O_poly n
   big_O_size_subset_big_O_ulog
                 |- !k. big_O (\n. size n ** k) SUBSET big_O (\n. ulog n ** k)
   big_O_ulog_subset_big_O_size
                 |- !k. big_O (\n. ulog n ** k) SUBSET big_O (\n. size n ** k)
   big_O_ulog_eq_big_O_size
                 |- !k. big_O (\n. size n ** k) = big_O (\n. ulog n ** k)
*)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Big O Notation                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define big_O as a set *)
val big_O_def = Define`
    big_O (g:num -> num) =
      { f:num -> num | ?k c. !n. k < n ==> f n <= c * (g n) }
`;
(* As n exceeds k, f(n) is bounded from above by some multiple of g(n) *)

(* Theorem: f IN big_O g <=> ?k c. !n. k < n ==> f n <= c * (g n) *)
(* Proof: by big_O_def *)
val big_O_element = store_thm(
  "big_O_element",
  ``!f g. f IN big_O g <=> ?k c. !n. k < n ==> f n <= c * (g n)``,
  rw[big_O_def]);

(* Theorem: g IN big_O g *)
(* Proof:
   By big_O_def, this is to show:
      ?k c. !n. k < n ==> g n <= c * g n
   Take any k, say k = 0, but take c = 1.
   Then g n = 1 * g n     by MULT_LEFT_1
   The result follows.
*)
val big_O_self = store_thm(
  "big_O_self",
  ``!g. g IN big_O g``,
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  rw[]);

(* Theorem: f1 IN big_O g /\ (!n. f1 n = f2 n) ==> f2 IN big_O g *)
(* Proof: by big_O_def, take same k and c. *)
val big_O_cong = store_thm(
  "big_O_cong",
  ``!f1 f2 g. f1 IN big_O g /\ (!n. f1 n = f2 n) ==> f2 IN big_O g``,
  rw[big_O_def] >>
  metis_tac[]);

(* Theorem: (K 0) IN big_O g *)
(* Proof: by big_O_def *)
val big_O_has_zero = store_thm(
  "big_O_has_zero",
  ``!g. (K 0) IN big_O g``,
  rw[big_O_def]);

(* Theorem: (K m) IN big_O (K 1) *)
(* Proof: by big_O_def, take k = 0 and c = m. *)
val big_O_1 = store_thm(
  "big_O_1",
  ``!m. (K m) IN big_O (K 1)``,
  rw[big_O_def] >>
  map_every qexists_tac [`0`, `m`] >>
  decide_tac);

(* Theorem: big_O g <> {} *)
(* Proof:
   Note (K 0) IN big_O g     by big_O_has_zero
   Thus big_O g <> {}        by MEMBER_NOT_EMPTY
*)
val big_O_nonempty = store_thm(
  "big_O_nonempty",
  ``!g. big_O g <> {}``,
  metis_tac[big_O_has_zero, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Sum and Product of Functions and Sets                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the sum of functions *)
val fun_sum_def = Define`
    fun_sum (f1:num -> num) (f2:num -> num) = (\n. f1 n + f2 n)
`;

(* Overload the sum of two functions *)
val _ = overload_on(".+.", ``\f1:num -> num f2:num -> num. fun_sum f1 f2``);
val _ = set_fixity ".+." (Infixl 500); (* same as addition *)

(* Define the product of functions *)
val fun_prod_def = Define`
    fun_prod (f1:num -> num) (f2:num -> num) = (\n. f1 n * f2 n)
`;

(* Overload the product of two functions *)
val _ = overload_on(".*.", ``\f1:num -> num f2:num -> num. fun_prod f1 f2``);
val _ = set_fixity ".*." (Infixl 600); (* same as multiplication *)

(* NOT export these simple definitions to avoid functional form. *)
(* val _ = export_rewrites ["fun_sum_def", "fun_prod_def"]; *)

(* Define sum of two numeric function sets *)
val set_sum_def = Define`
    set_sum (s1:(num -> num) -> bool) (s2:(num -> num) -> bool) =
       {(f1 .+. f2) | f1 IN s1 /\ f2 IN s2}
`;
(* Overload on set_sum *)
val _ = overload_on("|+|", ``set_sum``);
val _ = set_fixity "|+|" (Infixl 500); (* same as numeric addition *)

(*
> set_sum_def;
val it = |- !s1 s2. (s1 |+| s2) = {f1 .+. f2 | f1 IN s1 /\ f2 IN s2}: thm
*)

(* Theorem: f1 IN s1 /\ f2 IN s2 ==> (f1 .+. f2) IN (s1 |+| s2) *)
(* Proof: by set_sum_def *)
val set_sum_element = store_thm(
  "set_sum_element",
  ``!f1 f2 s1 s2. f1 IN s1 /\ f2 IN s2 ==> (f1 .+. f2) IN (s1 |+| s2)``,
  rw[set_sum_def] >>
  metis_tac[]);

(* Theorem: x IN s1 |+| s2 <=> ?f1 f2. f1 IN s1 /\ f2 IN s2 /\ (x = f1 .+. f2) *)
(* Proof: by set_sum_def *)
val set_sum_eqn = store_thm(
  "set_sum_eqn",
  ``!f1 f2 s1 s2 x. x IN s1 |+| s2 <=> ?f1 f2. f1 IN s1 /\ f2 IN s2 /\ (x = f1 .+. f2)``,
  rw[set_sum_def] >>
  metis_tac[]);

(* Define product of two numeric function sets *)
val set_prod_def = Define`
    set_prod (s1:(num -> num) -> bool) (s2:(num -> num) -> bool) =
       {(f1 .*. f2) | f1 IN s1 /\ f2 IN s2}
`;
(* Overload on set_prod *)
val _ = overload_on("|*|", ``set_prod``);
val _ = set_fixity "|*|" (Infixl 600); (* same as numeric multiplication *)

(*
> set_prod_def;
val it = |- !s1 s2. (s1 |*| s2) = {f1 .*. f2 | f1 IN s1 /\ f2 IN s2}: thm
*)

(* Theorem: f1 IN s1 /\ f2 IN s2 ==> (f1 .*. f2) IN (s1 |*| s2) *)
(* Proof: by set_prod_def *)
val set_prod_element = store_thm(
  "set_prod_element",
  ``!f1 f2 s1 s2. f1 IN s1 /\ f2 IN s2 ==> (f1 .*. f2) IN (s1 |*| s2)``,
  rw[set_prod_def] >>
  metis_tac[]);

(* Theorem: x IN s1 |*| s2 <=> ?f1 f2. f1 IN s1 /\ f2 IN s2 /\ (x = f1 .*. f2) *)
(* Proof: by set_prod_def *)
val set_prod_eqn = store_thm(
  "set_prod_eqn",
  ``!f1 f2 s1 s2 x. x IN s1 |*| s2 <=> ?f1 f2. f1 IN s1 /\ f2 IN s2 /\ (x = f1 .*. f2)``,
  rw[set_prod_def] >>
  metis_tac[]);

(* Theorem: f1 .+. f2 = f2 .+. f1 *)
(* Proof: by fun_sum_def, FUN_EQ_THM, ADD_COMM *)
val fun_sum_comm = store_thm(
  "fun_sum_comm",
  ``!f1 f2. f1 .+. f2 = f2 .+. f1``,
  rw[fun_sum_def]);

(* Theorem: (f1 .+. f2) .+. f3 = f1 .+. (f2 .+. f3) *)
(* Proof: by fun_sum_def, FUN_EQ_THM, ADD_ASSOC *)
val fun_sum_assoc = store_thm(
  "fun_sum_assoc",
  ``!f1 f2 f3. (f1 .+. f2) .+. f3 = f1 .+. (f2 .+. f3)``,
  rw[fun_sum_def]);

(* Theorem: f1 .*. f2 = f2 .*. f1 *)
(* Proof: by fun_prod_def, FUN_EQ_THM, MULT_COMM *)
val fun_prod_comm = store_thm(
  "fun_prod_comm",
  ``!f1 f2. f1 .*. f2 = f2 .*. f1``,
  rw[fun_prod_def]);

(* Theorem: (f1 .*. f2) .*. f3 = f1 .*. (f2 .*. f3) *)
(* Proof: by fun_prod_def, FUN_EQ_THM, MULT_ASSOC *)
val fun_prod_assoc = store_thm(
  "fun_prod_assoc",
  ``!f1 f2 f3. (f1 .*. f2) .*. f3 = f1 .*. (f2 .*. f3)``,
  rw[fun_prod_def]);

(* Theorem: f .+. (K 0) = f /\ (K 0) .+. f = f *)
(* Proof: by fun_sum_def *)
val fun_sum_zero = store_thm(
  "fun_sum_zero",
  ``!f. f .+. (K 0) = f /\ (K 0) .+. f = f``,
  rw[fun_sum_def, FUN_EQ_THM]);

(* Theorem: f .*. (K 1) = f /\ (K 1) .*. f = f *)
(* Proof: by fun_prod_def *)
val fun_prod_one = store_thm(
  "fun_prod_one",
  ``!f. f .*. (K 1) = f /\ (K 1) .*. f = f``,
  rw[fun_prod_def, FUN_EQ_THM]);

(* Theorem: MONO f1 /\ MONO f2 ==> MONO (f1 .+. f2) *)
(* Proof:
   Let x <= y,
   Note f1 x <= f1 y                     by MONO f1
    and f2 x <= f2 y                     by MONO f2
   Thus f1 x + f2 x <= f1 y + f2 y       by LE_MONO_ADD2
     or (f1 .+. f2) x <= (f1 .+. f2) y   by fun_sum_def
    ==> MONO (f1 .+. f2)
*)
val fun_sum_mono = store_thm(
  "fun_sum_mono",
  ``!f1 f2. MONO f1 /\ MONO f2 ==> MONO (f1 .+. f2)``,
  rw[fun_sum_def, LE_MONO_ADD2]);

(* Theorem: MONO f1 /\ MONO f2 ==> MONO (f1 .*. f2) *)
(* Proof:
   Let x <= y,
   Note f1 x <= f1 y                     by MONO f1
    and f2 x <= f2 y                     by MONO f2
   Thus f1 x * f2 x <= f1 y * f2 y       by LESS_MONO_MULT2
     or (f1 .*. f2) x <= (f1 .*. f2) y   by fun_prod_def
    ==> MONO (f1 .*. f2)
*)
val fun_prod_mono = store_thm(
  "fun_prod_mono",
  ``!f1 f2. MONO f1 /\ MONO f2 ==> MONO (f1 .*. f2)``,
  rw[fun_prod_def, LESS_MONO_MULT2]);

(* ------------------------------------------------------------------------- *)
(* Theorems for Complexity Class                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f1 IN big_O g1 /\ f2 IN big_O g2 ==> (f1 .+. f2) IN big_O (g1 .+. g2) *)
(* Proof:
   By big_O_def, fun_sum_def, this is to show:
      !n. k1 < n ==> f1 n <= c1 * g1 n /\
      !n. k2 < n ==> f1 n <= c2 * g1 n ==>
      ?k c. !n. k < n ==> f1 n + f2 n <= c * (g1 n + g2 n)
   Let k = MAX k1 k2, c = MAX c1 c2. Take this k and c.
   Then k1 <= k /\ k2 <= k                 by MAX_IS_MAX
    and c1 <= c /\ c2 <= c                 by MAX_IS_MAX
   Thus f1 n <= c * g1 n                   by LESS_MONO_MULT, LESS_EQ_TRANS, k1 < n
    and f2 n <= c * g2 n                   by LESS_MONO_MULT, LESS_EQ_TRANS, k2 < n
    ==> f1 n + f2 n <= c * (g1 n + g2 n)   by LEFT_ADD_DISTRIB
*)
val big_O_sum = store_thm(
  "big_O_sum",
  ``!f1 f2 g1 g2. f1 IN big_O g1 /\ f2 IN big_O g2 ==> (f1 .+. f2) IN big_O (g1 .+. g2)``,
  rw[big_O_def, fun_sum_def] >>
  qexists_tac `MAX k k'` >>
  qexists_tac `MAX c c'` >>
  rpt strip_tac >>
  qabbrev_tac `d = MAX c c'` >>
  `f1 n <= c * g1 n /\ f2 n <= c' * g2 n` by fs[] >>
  `c * g1 n <= d * g1 n /\ c' * g2 n <= d * g2 n` by rw[Abbr`d`] >>
  `f1 n + f2 n <= d * g1 n + d * g2 n` by rw[] >>
  `d * g1 n + d * g2 n = d * (g1 n + g2 n)` by rw[] >>
  decide_tac);

(* Theorem: (big_O g1) |+| (big_O g2) SUBSET big_O (g1 .+. g2) *)
(* Proof:
   By set_sum_def, SUBSET_DEF, this is to show:
      f1 IN big_O g1 /\ f2 IN big_O g2 ==> f1 .+. f2 IN big_O (g1 .+. g2)
   This is true             by big_O_sum
*)
val big_O_sum_subset = store_thm(
  "big_O_sum_subset",
  ``!g1 g2. (big_O g1) |+| (big_O g2) SUBSET big_O (g1 .+. g2)``,
  rw[set_sum_def, SUBSET_DEF] >>
  rw[big_O_sum]);

(* Theorem: f1 IN big_O g1 /\ f2 IN big_O g2 ==> (f1 .*. f2) IN big_O (g1 .*. g2) *)
(* Proof:
   By big_O_def, fun_prod_def, this is to show:
      !n. k1 < n ==> f1 n <= c1 * g1 n /\
      !n. k2 < n ==> f1 n <= c2 * g1 n ==>
      ?k c. !n. k < n ==> f1 n + f2 n <= c * (g1 n + g2 n)
   Let k = MAX k1 k2, c = MAX c1 c2. Take this k and (SQ c).
   Then k1 <= k /\ k2 <= k                 by MAX_IS_MAX
    and c1 <= c /\ c2 <= c                 by MAX_IS_MAX
   Thus f1 n <= (MAX c1 c2) * g1 n         by LESS_MONO_MULT, LESS_EQ_TRANS, k1 < n
    and f2 n <= (MAX c1 c2) * g2 n         by LESS_MONO_MULT, LESS_EQ_TRANS, k2 < n
    ==> f1 n * f2 n <= (SQ c) * (g1 n * g2 n)   by LESS_MONO_MULT2
*)
val big_O_prod = store_thm(
  "big_O_prod",
  ``!f1 f2 g1 g2. f1 IN big_O g1 /\ f2 IN big_O g2 ==> (f1 .*. f2) IN big_O (g1 .*. g2)``,
  rw[big_O_def, fun_prod_def] >>
  qexists_tac `MAX k k'` >>
  qexists_tac `(MAX c c') * (MAX c c')` >>
  rpt strip_tac >>
  qabbrev_tac `d = MAX c c'` >>
  `f1 n <= c * g1 n /\ f2 n <= c' * g2 n` by fs[] >>
  `c * g1 n <= d * g1 n /\ c' * g2 n <= d * g2 n` by rw[Abbr`d`] >>
  `f1 n <= d * g1 n /\ f2 n <= d * g2 n` by decide_tac >>
  `(d * g1 n) * (d * g2 n) = (SQ d) * g1 n * g2 n` by rw[] >>
  metis_tac[LESS_MONO_MULT2]);

(* ------------------------------------------------------------------------- *)
(* Big O Classes                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f1 IN big_O g /\ f2 IN big_O g ==> !a b. (\n. a * f1 n + b * f2 n) IN big_O g *)
(* Proof:
   Note f1 IN big_O g
    ==> ?k1 c1. !n. k1 < n ==> f1 n <= c1 * g n    by big_O_def
   Note f2 IN big_O g
    ==> ?k2 c2. !n. k2 < n ==> f2 n <= c2 * g n    by big_O_def
   Let k = MAX k1 k2, and c = a * c1 + b * c2.
   Then k1 <= k /\ k2 <= k                         by MAX_IS_MAX
   Thus for n > k, n > k1 and n > k2.
    ==> a * f1 n + b * f2 n
     <= a * (c1 * g n) + b * (c2 * g n)            by above
      = (a * c1 + b * c2) * g n                    by RIGHT_ADD_DISTRIB
      = c * g n                                    by above
*)
val big_O_linear = store_thm(
  "big_O_linear",
  ``!f1 f2 g. f1 IN big_O g /\ f2 IN big_O g ==> !a b. (\n. a * f1 n + b * f2 n) IN big_O g``,
  rw[big_O_def] >>
  qabbrev_tac `m = MAX k k'` >>
  `k <= m /\ k' <= m` by rw[Abbr`m`] >>
  qexists_tac `m` >>
  qexists_tac `a * c + b * c'` >>
  rpt strip_tac >>
  `k < n /\ k' < n` by decide_tac >>
  `a * f1 n <= a * (c * g n)` by rw[] >>
  `b * f2 n <= b * (c' * g n)` by rw[] >>
  `a * f1 n + b * f2 n <= a * (c * g n) + b * (c' * g n)` by decide_tac >>
  `a * (c * g n) + b * (c' * g n) = (a * c + b * c') * g n` by rw[] >>
  decide_tac);

(* Theorem: f1 IN big_O g /\ f2 IN big_O g ==> (\n. f1 n + f2 n) IN big_O g *)
(* Proof: by fun_sum_def, big_O_linear *)
val big_O_add = store_thm(
  "big_O_add",
  ``!f1 f2 g. f1 IN big_O g /\ f2 IN big_O g ==> (f1 .+. f2) IN big_O g``,
  rpt strip_tac >>
  `(f1 .+. f2) = (\n. 1 * f1 n + 1 * f2 n)` by rw[fun_sum_def, FUN_EQ_THM] >>
  `(\n. 1 * f1 n + 1 * f2 n) IN big_O g` by rw[big_O_linear] >>
  fs[]);

(* Theorem: (big_O g) |+| (big_O g) = (big_O g) *)
(* Proof:
   By SUBSET_ANTISYM, to show:
   (1) (big_O g) |+| (big_O g) SUBSET (big_O g)
       By SUBSET_DEF,
           x IN (big_O g) |+| (big_O g)
       ==> ?f1 f2. f1 IN big_O g /\ f2 IN big_O g /\ x = f1 .+. f2  by set_sum_def
       ==> ?f1 f2. f1 .+. f2 = x IN (big_O g)                       by big_O_add
       ==> x IN big_O g, hence true.
   (2) (big_O g) ==> (big_O g) |+| (big_O g)
       This is to show:
            x IN big_O g ==> ?f1 f2. f1 IN big_O g /\ f2 IN big_O g /\ x = f1 .+. f2
       Take f1 = x, f2 = K 0.
       Then f1 = x IN big_O g          by given
        and f2 = (K 0) IN big_O g      by big_O_has_zero
        and f1 .+. f2 = x .+. (K 0)
                      = x              by fun_sum_zero
*)
val big_O_sum_self = store_thm(
  "big_O_sum_self",
  ``!g. (big_O g) |+| (big_O g) = (big_O g)``,
  rw[set_sum_def, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  rw[big_O_add] >>
  qexists_tac `x` >>
  qexists_tac `K 0` >>
  rw[fun_sum_zero, big_O_has_zero]);

(* ------------------------------------------------------------------------- *)
(* Poly O Classes                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the standard polynomial functions *)
val POLY_def = Define`
    POLY m = (\n:num. n ** m)
`;
(* Overload the polynomial class *)
val _ = overload_on("poly_O", ``\m. big_O (POLY m)``);

(* NOT export POLY_def to avoid expansion of poly_O in rw[], fs[], simp[]. *)

(* Theorem: POLY 0 = K 1 *)
(* Proof:
     POLY 0
   = (\n. n ** 0)     by POLY_def
   = (\n. 1)          by EXP_0
   = K 1              by FUN_EQ_THM
*)
val POLY_0 = store_thm(
  "POLY_0",
  ``POLY 0 = K 1``,
  rw[POLY_def, FUN_EQ_THM]);

(* Theorem: POLY 1 = I *)
(* Proof:
     POLY 1
   = (\n. n ** 1)     by POLY_def
   = (\n. n)          by EXP_1
   = I                by I_THM
*)
val POLY_1 = store_thm(
  "POLY_1",
  ``POLY 1 = I``,
  rw[POLY_def, FUN_EQ_THM]);

(* Theorem: MONO (POLY m) *)
(* Proof:
   By notation of MONO, this is to show:
      x <= y ==> POLY m x <= POLY m y
   or x <= y ==> x ** m <= y ** m       by POLY_def
   which is true                        by EXP_EXP_LE_MONO
*)
val POLY_ascending = store_thm(
  "POLY_ascending",
  ``!m. MONO (POLY m)``,
  rw[POLY_def]);

(* Theorem: POLY m IN poly_O m *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      ?k c. !n. k < n ==> 0 < c
   Take any k, put c = 1.
*)
val poly_O_has_poly = store_thm(
  "poly_O_has_poly",
  ``!m. POLY m IN poly_O m``,
  rw[big_O_def, POLY_def] >>
  metis_tac[DECIDE``0 < 1``]);

(* Theorem: f IN poly_O m ==> !c. (\n. f n + c) IN poly_O m *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
       !n. k < n ==> f n <= c * n ** m
   ==> ?k c''. !n. k < n ==> c' + f n <= c'' * n ** m
   Take the same k, but use (c' + c) for c''.
   Then c'' * n ** m
      = (c' + c) * n ** m
      = c' * n ** m + c * n ** m     by RIGHT_ADD_DISTRIB
      >= c' * n ** m + f n           by given
      >= c' + f n                    by ZERO_LT_EXP, or ONE_LE_EXP, 0 < n
*)
val poly_O_add_constant = store_thm(
  "poly_O_add_constant",
  ``!f m. f IN poly_O m ==> !c. (\n. f n + c) IN poly_O m``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `k` >>
  qexists_tac `c' + c` >>
  rw[RIGHT_ADD_DISTRIB] >>
  `c' <= c' * n ** m` by rw[] >>
  metis_tac[LE_MONO_ADD2, ADD_COMM]);

(* Theorem: f IN poly_O m ==> !c. (\n. c * f n) IN poly_O m *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
       !n. k < n ==> f n <= c * n ** m
   ==> ?k c''. !n. k < n ==> c' * f n <= c'' * n ** m
   Take the same k, but use (c' * c) for c''.
   Then c'' * n ** m
      = (c' * c) * n ** m
      = c' * (c * n ** m)     by MULT_ASSOC
      >= c' * f n             by LE_MULT_LCANCEL, given
*)
val poly_O_mult_constant = store_thm(
  "poly_O_mult_constant",
  ``!f m. f IN poly_O m ==> !c. (\n. c * f n) IN poly_O m``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `k` >>
  qexists_tac `c' * c` >>
  metis_tac[LE_MULT_LCANCEL, MULT_ASSOC]);

(* Theorem: poly_O n <> {} *)
(* Proof: by big_O_nonempty *)
val poly_O_nonempty = store_thm(
  "poly_O_nonempty",
  ``!n. poly_O n <> {}``,
  rw[big_O_nonempty]);

(* Theorem: (K c0) IN poly_O 0 *)
(* Proof: by big_O_def, POLY_def, arithmetic. *)
val poly_O_constant = store_thm(
  "poly_O_constant",
  ``!c0. (K c0) IN poly_O 0``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `c0` >>
  fs[]);

(* Theorem: big_O (POLY a .+. POLY b) SUBSET poly_O (MAX a b) *)
(* Proof:
   By big_O_def, fun_sum_def, POLY_def, SUBSET_DEF, this is to show:
      !n. k < n ==> x n <= c * (n ** a + n ** b) ==>
      ?k c. !n. k < n ==> x n <= c * n ** MAX a b
   Take the same k and (2 * c).
   Let m = MAX a b.
   Note 0 < n                    by k < n
   Then n ** a <= n ** m         by EXP_BASE_LEQ_MONO_IMP, MAX_IS_MAX, 0 < n
    and n ** b <= n ** m         by EXP_BASE_LEQ_MONO_IMP, MAX_IS_MAX, 0 < n
        x n
     <= c * (n ** a + n ** b)    by given
     <= c * (n ** m + n ** m)    by above
      = 2 * c * n ** m           by arithmetic
*)
val big_O_poly_sum = store_thm(
  "big_O_poly_sum",
  ``!a b. big_O (POLY a .+. POLY b) SUBSET poly_O (MAX a b)``,
  rw[big_O_def, fun_sum_def, POLY_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `2 * c` >>
  rpt strip_tac >>
  qabbrev_tac `m = MAX a b` >>
  `0 < n` by decide_tac >>
  `n ** a <= n ** m /\ n ** b <= n ** m` by metis_tac[EXP_BASE_LEQ_MONO_IMP, MAX_IS_MAX] >>
  `x n <= c * (n ** a + n ** b)` by rw[] >>
  `c * (n ** a + n ** b) <= c * (n ** m + n ** m)` by rw[] >>
  `c * (n ** m + n ** m) = 2 * c * n ** m` by rw[] >>
  decide_tac);

(* Theorem: big_O (POLY a .+. POLY b .+. POLY c) SUBSET poly_O (MAX (MAX a b) c) *)
(* Proof:
   By big_O_def, fun_sum_def, POLY_def, SUBSET_DEF, this is to show:
      !n. k < n ==> x n <= c' * (n ** a + (n ** b + n ** c)) ==>
      ?k c'. !n. k < n ==> x n <= c' * n ** MAX (MAX a b) c
   Take the same k and (3 * c').
   Let m = MAX (MAX a b) c.
   Note 0 < n                       by k < n
    and a <= m /\ b <= m /\ c <= m  by MAX_DEF
   Then n ** a <= n ** m            by EXP_BASE_LEQ_MONO_IMP, 0 < n
    and n ** b <= n ** m            by EXP_BASE_LEQ_MONO_IMP, 0 < n
    and n ** c <= n ** m            by EXP_BASE_LEQ_MONO_IMP, 0 < n
        x n
     <= c' * (n ** a + (n ** b + n ** c))    by given
     <= c' * (n ** m + (n ** m + n ** m))    by above
      = 3 * c' * n ** m                      by arithmetic
*)
val big_O_poly_sum_3 = store_thm(
  "big_O_poly_sum_3",
  ``!a b c. big_O (POLY a .+. POLY b .+. POLY c) SUBSET poly_O (MAX (MAX a b) c)``,
  rw[big_O_def, fun_sum_def, POLY_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `3 * c'` >>
  rpt strip_tac >>
  qabbrev_tac `m = MAX (MAX a b) c` >>
  `0 < n` by decide_tac >>
  `a <= m /\ b <= m /\ c <= m` by rw[MAX_DEF, Abbr`m`] >>
  `n ** a <= n ** m /\ n ** b <= n ** m /\ n ** c <= n ** m` by metis_tac[EXP_BASE_LEQ_MONO_IMP] >>
  `x n <= c' * (n ** a + (n ** b + n ** c))` by rw[] >>
  `c' * (n ** a + (n ** b + n ** c)) <= c' * (n ** m + (n ** m + n ** m))` by rw[] >>
  `c' * (n ** m + (n ** m + n ** m)) = 3 * c' * n ** m` by rw[] >>
  decide_tac);

(* Theorem: f IN poly_O a /\ g IN poly_O b ==> f .+. g IN poly_O (MAX a b) *)
(* Proof:
       f IN poly_O a /\ g IN poly_O b
   ==> (f .+. g) IN big_O (POLY a .+. POLY b))   by big_O_sum
   ==> (f .+. g) IN poly_O (MAX a b)             by big_O_poly_sum, SUBSET_DEF
*)
val big_O_sum_poly = store_thm(
  "big_O_sum_poly",
  ``!f g a b. f IN poly_O a /\ g IN poly_O b ==> f .+. g IN poly_O (MAX a b)``,
  metis_tac[big_O_sum, big_O_poly_sum, SUBSET_DEF]);

(* Theorem: big_O (POLY a .*. POLY b) SUBSET poly_O (a + b) *)
(* Proof:
   By big_O_def, fun_prod_def, POLY_def, SUBSET_DEF, this is to show:
      !n. k < n ==> x n <= c * (n ** a * n ** b) ==>
      ?k c. !n. k < n ==> x n <= c * n ** (a + b)
   Take the same k and c.
        x n
     <= c * (n ** a * n ** b)    by given
     <= c * n ** (a + b)         by EXP_ADD
*)
val big_O_poly_prod = store_thm(
  "big_O_poly_prod",
  ``!a b. big_O (POLY a .*. POLY b) SUBSET poly_O (a + b)``,
  rw[big_O_def, fun_prod_def, POLY_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `c` >>
  rpt strip_tac >>
  `x n <= c * (n ** a * n ** b)` by rw[] >>
  `c * (n ** a * n ** b) = c * n ** (a + b)` by rw[EXP_ADD] >>
  decide_tac);

(* Theorem: big_O (POLY a .*. POLY b .*. POLY c) SUBSET poly_O (a + b + c) *)
(* Proof:
   By big_O_def, fun_prod_def, POLY_def, SUBSET_DEF, this is to show:
      !n. k < n ==> x n <= c' * n ** a * n ** b * n ** c ==>
      ?k c'. !n. k < n ==> x n <= c' * n ** (a + (b + c))
   Take the same k and c'.
        x n
     <= c' * (n ** a * n ** b * n ** c)    by given
     <= c' * n ** (a + b + c)              by EXP_ADD
*)
val big_O_poly_prod_3 = store_thm(
  "big_O_poly_prod_3",
  ``!a b c. big_O (POLY a .*. POLY b .*. POLY c) SUBSET poly_O (a + b + c)``,
  rw[big_O_def, fun_prod_def, POLY_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `c'` >>
  rpt strip_tac >>
  `x n <= c' * (n ** a * n ** b * n ** c)` by rw[] >>
  `c' * (n ** a * n ** b * n ** c) = c' * n ** (a + (b + c))` by rw[EXP_ADD] >>
  decide_tac);

(* Theorem: f IN poly_O a /\ g IN poly_O b ==> f .*. g IN poly_O (a + b) *)
(* Proof:
       f IN poly_O a /\ g IN poly_O b
   ==> (f .*. g) IN big_O (POLY a .*. POLY b)   by big_O_prod
   ==> (f .*. g) IN poly_O (a + b)              by big_O_poly_prod, SUBSET_DEF
*)
val big_O_prod_poly = store_thm(
  "big_O_prod_poly",
  ``!f g a b. f IN poly_O a /\ g IN poly_O b ==> f .*. g IN poly_O (a + b)``,
  metis_tac[big_O_prod, big_O_poly_prod, SUBSET_DEF]);

(* Theorem: (\n. a * n ** b) IN poly_O b *)
(* Proof: by big_O_def, POLY_def, take k = 0 and c = a. *)
val big_O_poly = store_thm(
  "big_O_poly",
  ``!a b. (\n. a * n ** b) IN poly_O b``,
  rw[big_O_def, POLY_def] >>
  map_every qexists_tac [`0`, `a`] >>
  fs[]);

(* Theorem: (\n. n ** 3 + TWICE n + 10) IN poly_O 3 *)
(* Proof:
   Let f = \n. n ** 3 + 2 * n + 10.
       f1 = \n. 1 * n ** 3,
       f2 = \n. 2 * n ** 1,
       f3 = \n. 10 * n ** 0.
   Then f1 IN poly_O 3                 by big_O_poly
    and f2 IN poly_O 1                 by big_O_poly
    and f3 IN poly_O 0                 by big_O_poly
    ==> f1 .+. f2 IN poly_O (MAX 3 1)  by big_O_sum_poly
   Let f4 = (f1 .+. f2).
   Then f4 IN poly_O 3                 by MAX_DEF
   Note f = f4 .+. f3                  by FUN_EQ_THM
    and f IN poly_O (MAX 3 0)          by big_O_sum_poly
     or f IN poly_O 3                  by MAX_DEF
*)
val big_O_example = store_thm(
  "big_O_example",
  ``!n. (\n. n ** 3 + TWICE n + 10) IN poly_O 3``,
  rpt strip_tac >>
  qabbrev_tac `f = \n. n ** 3 + 2 * n + 10` >>
  qabbrev_tac `f1 = \n. 1 * n ** 3` >>
  qabbrev_tac `f2 = \n. 2 * n ** 1` >>
  qabbrev_tac `f3 = \n. 10 * n ** 0` >>
  `f1 IN poly_O 3` by rw[big_O_poly, Abbr`f1`] >>
  `f2 IN poly_O 1` by rw[big_O_poly, Abbr`f2`] >>
  `f3 IN poly_O 0` by rw[big_O_poly, Abbr`f3`] >>
  `(MAX 3 1 = 3) /\ (MAX 3 0 = 3)` by rw[] >>
  `f1 .+. f2 IN poly_O (MAX 3 1)` by rw[big_O_sum_poly] >>
  `f1 .+. f2 IN poly_O 3` by metis_tac[] >>
  qabbrev_tac `f4 = (f1 .+. f2)` >>
  `f = (f4 .+. f3)` by rw[fun_sum_def, FUN_EQ_THM, Abbr`f`, Abbr`f1`, Abbr`f2`, Abbr`f3`, Abbr`f4`] >>
  `f IN poly_O (MAX 3 0)` by rw[big_O_sum_poly] >>
  metis_tac[]);

(* Theorem: (\n. c1 * n + c0) IN poly_O 1 *)
(* Proof: by big_O_def, POLY_def, arithmetic. *)
val poly_O_linear = store_thm(
  "poly_O_linear",
  ``!c0 c1. (\n. c1 * n + c0) IN poly_O 1``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `c0` >>
  qexists_tac `1 + c1` >>
  rpt strip_tac >>
  `c0 + c1 * n <= n + c1 * n` by rw[] >>
  `n + c1 * n = (1 + c1) * n` by rw[] >>
  decide_tac);

(* Theorem: (\n. c2 * n ** 2 + c1 * n + c0) IN poly_O 2 *)
(* Proof: by big_O_def, POLY_def, arithmetic. *)
val poly_O_quadratic = store_thm(
  "poly_O_quadratic",
  ``!c0 c1 c2. (\n. c2 * n ** 2 + c1 * n + c0) IN poly_O 2``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `c0 + c1` >>
  qexists_tac `1 + c2` >>
  rpt strip_tac >>
  `1 <= n` by decide_tac >>
  `n = n - 1 + 1` by decide_tac >>
  `c0 + (c1 * n + c2 * n ** 2) = (c0 + c1 * n) + c2 * n ** 2` by decide_tac >>
  `_ = c0 + (c1 * (n - 1) + c1) + c2 * n ** 2` by metis_tac[LEFT_ADD_DISTRIB, MULT_RIGHT_1] >>
  `_ = c1 * (n - 1) + (c0 + c1) + c2 * n ** 2` by decide_tac >>
  `c1 * (n - 1) + (c0 + c1) + c2 * n ** 2 <= c1 * (n - 1) + n + c2 * n ** 2` by rw[] >>
  `c1 * (n - 1) + n + c2 * n ** 2 <= n * (n - 1) + n + c2 * n ** 2` by rw[] >>
  `n * (n - 1) + n + c2 * n ** 2 = n * n + c2 * n ** 2` by metis_tac[LEFT_ADD_DISTRIB, MULT_RIGHT_1] >>
  `_ = (1 + c2) * n ** 2` by rw[GSYM EXP_2] >>
  decide_tac);

(* Theorem: ?g. g IN poly_O 0 /\ t + c <= g s + t *)
(* Proof:
   Take g = K c,
   Then g IN poly_O 0                by poly_O_constant
    and c = g s                      by function application
     or t + c <= g s + t             by arithmetic
*)
val poly_O_constant_exists = store_thm(
  "poly_O_constant_exists",
  ``!s t c. ?g. g IN poly_O 0 /\ t + c <= g s + t``,
  rpt strip_tac >>
  qexists_tac `K c` >>
  fs[] >>
  metis_tac[poly_O_constant]);

(* Theorem: n <= s ==> ?g. g IN poly_O 1 /\ t + (b * n + c) <= g s + t *)
(* Proof:
   Take g = (\n. b * n + c),
   Then g IN poly_O 1                by poly_O_linear
    and b * n + c
     <= b * s + c                    by n <= s
      = g s                          by function application
     or t + (b * n + c) <= g s + t   by arithmetic
*)
val poly_O_linear_exists = store_thm(
  "poly_O_linear_exists",
  ``!n s t b c. n <= s ==> ?g. g IN poly_O 1 /\ t + (b * n + c) <= g s + t``,
  rpt strip_tac >>
  qexists_tac `\n. b * n + c` >>
  fs[] >>
  `(\n. b * n + c) IN poly_O 1` by metis_tac[poly_O_linear] >>
  fs[]);

(* Theorem: n <= s ==> ?g. g IN poly_O 2 /\ t + (a * n ** 2 + b * n + c) <= g s + t *)
(* Proof:
   Take g = (\n. a * n ** 2 + b * n + c),
   Then g IN poly_O 1                by poly_O_linear
    and a * n ** 2 + b * n + c
     <= a * s ** 2 + b * s + c       by EXP_EXP_LE_MONO, n <= s
      = g s                          by function application
     or t + (a * n ** 2 + b * n + c)
     <= g s + t                      by arithmetic
*)
val poly_O_quadratic_exists = store_thm(
  "poly_O_quadratic_exists",
  ``!n s t a b c. n <= s ==> ?g. g IN poly_O 2 /\ t + (a * n ** 2 + b * n + c) <= g s + t``,
  rpt strip_tac >>
  qexists_tac `\n. a * n ** 2 + b * n + c` >>
  fs[] >>
  `(\n'. a * n' ** 2 + b * n' + c) IN poly_O 2` by metis_tac[poly_O_quadratic] >>
  fs[] >>
  `a * n ** 2 <= a * s ** 2` by rw[] >>
  `b * n <= b * s` by rw[] >>
  decide_tac);

(* Theorem: big_O (K 1) SUBSET poly_O m *)
(* Proof:
   By big_O_def, POLY_def and SUBSET_DEF, this is to show:
      !n. k < n ==> x n <= c ==> ?k c. !n. k < n ==> x n <= c * n ** m
   Take the same k, the same c.
   Then if k < n
    ==> x n <= c             by implication
    and 0 < n ** m           by EXP_POS, 0 < n, from k < n
     so   c <= c * n ** m    by arithmetic
   Thus x n <= c * n ** m
*)
val poly_O_has_constant = store_thm(
  "poly_O_has_constant",
  ``!m. big_O (K 1) SUBSET poly_O m``,
  rw[big_O_def, POLY_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `c` >>
  rpt strip_tac >>
  `x n <= c` by rw[] >>
  `c <= c * n ** m` by rw[EXP_POS] >>
  decide_tac);

(* Theorem: f IN poly_O m ==> !a. (\n. f (a * n)) IN poly_O m *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      !n. k < n ==> f n <= c * n ** m ==> ?k c. !n. k < n ==> f (a * n) <= c * n ** m
   Take the same k.
   If a = 0,
      Take c = f 0.
      Then if k < n, then 0 < n      by arithmetic
        so 0 < n ** m                by EXP_POS
       ==> f 0 <= f 0 * n ** m       by LE_MULT_CANCEL_LBARE
        or f (a * n) <= c * n ** m   by a * n = 0, c = f 0.
   If a <> 0,
      Take c as c * a ** m.
      Then if k < n, then 0 < n      by arithmetic
       ==> n <= a * n                by LE_MULT_CANCEL_LBARE
      Thus k < a * n
       ==> f (a * n)
        <= c * (a * n) ** m          by implication
         = c * a ** m * n ** m       by EXP_BASE_MULT
*)
val poly_O_multiple = store_thm(
  "poly_O_multiple",
  ``!f m. f IN poly_O m ==> !a. (\n. f (a * n)) IN poly_O m``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `k` >>
  Cases_on `a = 0` >| [
    qexists_tac `f 0` >>
    simp[],
    qexists_tac `c * a ** m` >>
    rpt strip_tac >>
    `n <= a * n` by rw[] >>
    `k < a * n` by decide_tac >>
    `f (a * n) <= c * (a * n) ** m` by rw[] >>
    `c * (a * n) ** m = c * a ** m * n ** m` by rw[EXP_BASE_MULT] >>
    decide_tac
  ]);

(* Theorem: f1 IN poly_O m /\ f2 IN poly_O m ==> !a b. (\n. f1 (a * n) + f2 (b * n)) IN poly_O m *)
(* Proof:
   Let g1 = \n. f1 (a * n), g2 = \n. f2 (b * n).
   Then g1 IN poly_O m                   by poly_O_multiple
    and g2 IN poly_O m                   by poly_O_multiple
   Note g1 .+. g2
      = (\n. f1 (a * n) + f2 (b * n))    by fun_sum_def, FUN_EQ_THM
    and (g1 .+. g2) IN poly_O m          by big_O_add
*)
val poly_O_add_linear = store_thm(
  "poly_O_add_linear",
  ``!f1 f2 m. f1 IN poly_O m /\ f2 IN poly_O m ==> !a b. (\n. f1 (a * n) + f2 (b * n)) IN poly_O m``,
  rpt strip_tac >>
  qabbrev_tac `g1 = \n. f1 (a * n)` >>
  qabbrev_tac `g2 = \n. f2 (b * n)` >>
  `g1 IN poly_O m` by rw[poly_O_multiple, Abbr`g1`] >>
  `g2 IN poly_O m` by rw[poly_O_multiple, Abbr`g2`] >>
  `(g1 .+. g2) = (\n. f1 (a * n) + f2 (b * n))` by rw[fun_sum_def, FUN_EQ_THM, Abbr`g1`, Abbr`g2`] >>
  `(g1 .+. g2) IN poly_O m` by rw[big_O_add] >>
  rfs[]);

(* Theorem: m <= n ==> poly_O m SUBSET poly_O n *)
(* Proof:
   By big_O_def, POLY_def, SUBSET_DEF, this is to show:
      m <= n /\ !n'. k < n' ==> x n' <= c * n' ** m ==> ?c. !n'. k < n' ==> x n' <= c * n' ** n
   Take the same k, and the same c.
   Then if k < n',
    ==> x n' <= c * n' ** m          by implication
   Note n' ** m <= n' ** n           by EXP_BASE_LEQ_MONO_IMP, 0 < n'
    ==> c * n' ** m <= c * n' ** n   by LE_MULT_LCANCEL
   Thus x n' <= c * n' ** n          by arithmetic
*)
val poly_O_subset = store_thm(
  "poly_O_subset",
  ``!m n. m <= n ==> poly_O m SUBSET poly_O n``,
  rw[big_O_def, POLY_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `c` >>
  rpt strip_tac >>
  `x n' <= c * n' ** m` by rw[] >>
  `c * n' ** m <= c * n' ** n` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  decide_tac);

(* Theorem: (poly_O n) |+| (poly_O n) = poly_O n *)
(* Proof: by big_O_sum_self, with g = POLY n. *)
val poly_O_sum = store_thm(
  "poly_O_sum",
  ``!n. (poly_O n) |+| (poly_O n) = poly_O n``,
  rw[big_O_sum_self]);

(* Theorem: poly_O n |+| poly_O m SUBSET poly_O (MAX n m) *)
(* Proof:
   Note poly_O n |+| poly_O m SUBSET big_O (POLY n .+. POLY m)    by big_O_sum_subset
    and big_O (POLY n .+. POLY m) SUBSET poly_O (MAX n m)         by big_O_poly_sum
    The result follows                                            by SUBSET_TRANS
*)
val poly_O_sum_subset = store_thm(
  "poly_O_sum_subset",
  ``!m n. poly_O n |+| poly_O m SUBSET poly_O (MAX n m)``,
  metis_tac[big_O_sum_subset, big_O_poly_sum, SUBSET_TRANS]);


(* ------------------------------------------------------------------------- *)
(* Big O theorem with size                                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload positive function *)
val _ = overload_on ("FUN_POS", ``\f. (!x. 0 < f x)``);

(* Theorem: FUN_POS f ==> !c. big_O (K c) SUBSET big_O f *)
(* Proof:
   By big_O_def, this is to show:
       !n. k < n ==> x n <= c * c'
   ==> ?k c. !n. k < n ==> x n <= c * f n
   Take the same k, take (c * c') as c.
   Since 0 < f n, so 1 <= f n, hence true.
*)
val big_O_K_subset = store_thm(
  "big_O_K_subset",
  ``!f. FUN_POS f ==> !c. big_O (K c) SUBSET big_O f``,
  rw[big_O_def, SUBSET_DEF] >>
  qexists_tac `k` >>
  qexists_tac `c * c'` >>
  rw[] >>
  `0 < f n /\ x n <= c * c'` by fs[] >>
  `1 <= f n` by decide_tac >>
  `c * c' <= c * c' * f n` by rw[] >>
  decide_tac);

(*
size_pos |- FUN_POS size
*)

(* Theorem: MONO f1 /\ f2 IN big_O (K c) ==> ?d. f1 o f2 IN big_O (K d) *)
(* Proof:
   Note ?k c2. !n. k < n ==> f2 n <= c2 * c     by big_O_def, f2 IN big_O (K c)
   Take same k,
   Then for all n > k, f1 (f2 n) <= f1 (c2 * c) by MONO f1
*)
val big_O_compose_K = store_thm(
  "big_O_compose_K",
  ``!f1 f2 c. MONO f1 /\ f2 IN big_O (K c) ==> ?d. f1 o f2 IN big_O (K d)``,
  rw[big_O_def] >>
  qexists_tac `f1 (c * c')` >>
  qexists_tac `k` >>
  qexists_tac `1` >>
  rw[]);

(* Theorem: FUN_POS g ==> (K c) IN big_O g *)
(* Proof:
   By big_O_def, this is to show:
      ?k d. !n. k < n ==> c <= d * g n
   Note 0 < g n        by FUN_POS g
     so 1 <= g n       by arithmetic
     or c <= c * g n
   Take k = 0, same c.
*)
val big_O_constant = store_thm(
  "big_O_constant",
  ``!g c. FUN_POS g ==> (K c) IN big_O g``,
  rw[big_O_def] >>
  map_every qexists_tac [`0`, `c`] >>
  rpt strip_tac >>
  `0 < g n` by rw[] >>
  `1 <= g n` by decide_tac >>
  rw[]);

(* Theorem: FUN_POS (POLY k o size) *)
(* Proof:
   This is to show: !n. 0 < (POLY k o size) n
     (POLY k o size) n
   = (size n) ** k
   > 0                  by size_pos, EXP_POS
*)
val POLY_size_pos = store_thm(
  "POLY_size_pos",
  ``!k. FUN_POS (POLY k o size)``,
  rw[POLY_def] >>
  rw[size_pos]);

(* Theorem: (\n. a * size n + b) IN big_O size *)
(* Proof:
   By big_O_def, this is to show:
      ?k c. !n. k < n ==> b + a * size n <= c * size n
   Note 1 <= size n                  by one_le_size
     so b <= b * size n              by arithmetic
   Then    b + a * size n
        <= b * size n + a * size n   by above
         = (b + a) * size n          by RIGHT_ADD_DISTRIB
   Take k = 0, c = a + b, the result follows.
*)
val big_O_size_linear = store_thm(
  "big_O_size_linear",
  ``!a b. (\n. a * size n + b) IN big_O size``,
  rw[big_O_def] >>
  map_every qexists_tac [`0`, `a + b`] >>
  rpt strip_tac >>
  simp[RIGHT_ADD_DISTRIB] >>
  `1 <= size n` by rw[one_le_size] >>
  `b <= b * size n` by rw[] >>
  decide_tac);

(* Theorem: (\n. a * size n) IN big_O size *)
(* Proof: by big_O_size_linear *)
val big_O_size_linear_0 = store_thm(
  "big_O_size_linear_0",
  ``!a. (\n. a * size n) IN big_O size``,
  rpt strip_tac >>
  `(\n. a * size n) = (\n. a * size n + 0)` by rw[FUN_EQ_THM] >>
  `(\n. a * size n + 0) IN big_O size` by rw[big_O_size_linear] >>
  fs[]);

(* Theorem: (\n. a * size n ** 2 + b * size n + c) IN big_O (POLY 2 o size) *)
(* Proof:
   By big_O_def and POLY_def, this is to show:
      ?k c'. !n. k < n ==> c + (a * size n ** 2 + b * size n) <= c' * size n ** 2
   Note 1 <= size n                    by one_le_size
     so b <= b * size n                by arithmetic
    and b * size <= b * (size n) ** 2  by EXP_2
   also c <= c * (size n) **2          by EXP_2
   Then    c + b * size n + a * (size n) ** 2
        <= c * (size n) ** 2 + b * (size n) ** 2 + a * (size n) ** 2   by above
         = (c + b + a) * (size n) **           by RIGHT_ADD_DISTRIB
   Take k = 0, c' = a + b + c, the result follows.
*)
val big_O_size_quadratic = store_thm(
  "big_O_size_quadratic",
  ``!a b c. (\n. a * size n ** 2 + b * size n + c) IN big_O (POLY 2 o size)``,
  rw[big_O_def, POLY_def] >>
  map_every qexists_tac [`0`, `a + b + c`] >>
  rpt strip_tac >>
  simp[RIGHT_ADD_DISTRIB] >>
  `1 <= size n` by rw[one_le_size] >>
  `b * size n <= b * (size n * size n)` by rw[] >>
  `b * size n <= b * (size n) ** 2` by metis_tac[EXP_2] >>
  `c <= c * (size n * size n)` by rw[] >>
  `c <= c * (size n) ** 2` by metis_tac[EXP_2] >>
  decide_tac);

(* Theorem: (\n. a * size n ** 2 ) IN big_O (POLY 2 o size) *)
(* Proof: by big_O_size_quadratic *)
val big_O_size_quadratic_0 = store_thm(
  "big_O_size_quadratic_0",
  ``!a. (\n. a * size n ** 2) IN big_O (POLY 2 o size)``,
  rpt strip_tac >>
  `(\n. a * (size n) ** 2) = (\n. a * (size n) ** 2 + 0 * size n + 0)` by rw[FUN_EQ_THM] >>
  `(\n. a * (size n) ** 2 + 0 * size n + 0) IN big_O (POLY 2 o size)` by rw[big_O_size_quadratic] >>
  fs[]);

(* Theorem: (\n. a * size n ** 2 + b * size n) IN big_O (POLY 2 o size) *)
(* Proof: by big_O_size_quadratic *)
val big_O_size_quadratic_1 = store_thm(
  "big_O_size_quadratic_1",
  ``!a b. (\n. a * size n ** 2 + b * size n) IN big_O (POLY 2 o size)``,
  rpt strip_tac >>
  `(\n. a * (size n) ** 2 + b * size n) = (\n. a * (size n) ** 2 + b * size n + 0)` by rw[FUN_EQ_THM] >>
  `(\n. a * (size n) ** 2 + b * size n + 0) IN big_O (POLY 2 o size)` by rw[big_O_size_quadratic] >>
  fs[]);

(* Theorem: (\n. a * size n ** 2 + b) IN big_O (POLY 2 o size) *)
(* Proof: by big_O_size_quadratic *)
val big_O_size_quadratic_2 = store_thm(
  "big_O_size_quadratic_2",
  ``!a b. (\n. a * size n ** 2 + b) IN big_O (POLY 2 o size)``,
  rpt strip_tac >>
  `(\n. a * (size n) ** 2 + b) = (\n. a * (size n) ** 2 + 0 * size n + b)` by rw[FUN_EQ_THM] >>
  `(\n. a * (size n) ** 2 + 0 * size n + b) IN big_O (POLY 2 o size)` by rw[big_O_size_quadratic] >>
  fs[]);

(* Theorem: (!n. k < n ==> f1 n <= f2 n) /\ f2 IN big_O g ==> f1 IN big_O g *)
(* Proof:
   By big_O_def, this is to show:
      ?t c. !n. t < n ==> f1 n <= c * g n
   Note ?h c. !n. h < n ==> f2 n <= c * g n    by big_O_def, f2 IN big_O g
   Take t = MAX k h, and the same c.
   Note k <= t /\ h <= t                       by MAX_IS_MAX
     so t < n
    ==> f1 n <= f2 n /\ f2 n <= c * g n
    ==> f1 n <= c * g n                        by LESS_EQ_TRANS
*)
val big_O_dominance = store_thm(
  "big_O_dominance",
  ``!f1 f2 g k. (!n. k < n ==> f1 n <= f2 n) /\ f2 IN big_O g ==> f1 IN big_O g``,
  rw[big_O_def] >>
  qexists_tac `MAX k k'` >>
  qexists_tac `c` >>
  rpt strip_tac >>
  `k <= MAX k k' /\ k' <= MAX k k'` by rw[] >>
  `k < n /\ k' < n` by decide_tac >>
  metis_tac[LESS_EQ_TRANS]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Complexity Class                                               *)
(* ------------------------------------------------------------------------- *)

(* Define polynomial complexity class based on (size ** n)  *)
val _ = overload_on("O_poly", ``\n. big_O ((POLY n) o size)``);


(* Theorem: f IN O_poly m <=> ?h k. (!n. h < n ==> f n <= k * (size n) ** m) *)
(* Proof: by big_O_def, POLY_def *)
val O_poly_thm = store_thm(
  "O_poly_thm",
  ``!f m. f IN O_poly m <=> ?h k. (!n. h < n ==> f n <= k * (size n) ** m)``,
  rw[big_O_def, POLY_def]);

(* Theorem: f IN O_poly m <=> ?h k. 0 < k /\ (!n. h < n ==> f n <= k * (size n) ** m) *)
(* Proof:
   If part: f IN O_poly m ==> ?h k. 0 < k /\ !n. h < n ==> f n <= k * size n ** m
      Note ?h k. (!n. h < n ==> f n <= k * (size n) ** m)   by O_poly_thm
      Take same h, but use (SUC k).
      Then k * (size n) ** m <= SUC k * (size n) ** m       by k < SUC k
      The result follows.
   Only-if part: 0 < k /\ !n. h < n ==> f n <= k * size n ** m ==> f IN O_poly m
      True by O_poly_thm.
*)
val O_poly_good = store_thm(
  "O_poly_good",
  ``!f m. f IN O_poly m <=> ?h k. 0 < k /\ (!n. h < n ==> f n <= k * (size n) ** m)``,
  rw[EQ_IMP_THM] >| [
    `?h k. (!n. h < n ==> f n <= k * (size n) ** m)` by rw[GSYM O_poly_thm] >>
    qexists_tac `h` >>
    qexists_tac `SUC k` >>
    rw_tac std_ss[] >>
    `f n <= k * size n ** m` by fs[] >>
    `k * size n ** m <= SUC k * size n ** m` by fs[] >>
    decide_tac,
    metis_tac[O_poly_thm]
  ]);

(* O_poly n is the same as big_O ((POLY n) o ulog) *)

(* Theorem: O_poly n = big_O ((POLY n) o ulog) *)
(* Proof:
   If part: x IN O_poly n ==> x IN big_O ((POLY n) o ulog)
      Expand by definitions,
        x n' <= k * size n' ** n
             <= k * (1 + ulog n') ** n         by size_ulog
             <= k * (ulog n' + ulog n') ** n   by ulog_pos, 1 < n'
              = k * (2 * ulog n') ** n         by arithmetic
              = (k * 2 ** n) * (ulog n') ** n  by EXP_BASE_MULT
      Take k = MAX 1 h, and c = k * 2 ** n.
   Only-if part: x IN big_O ((POLY n) o ulog) ==> x IN O_poly n
      Expand by definitions,
        x n' <= c * ulog n' ** n
             <= c * size n' ** n               by size_ulog
*)
val O_poly_eq_O_poly_ulog = store_thm(
  "O_poly_eq_O_poly_ulog",
  ``!n. O_poly n = big_O ((POLY n) o ulog)``,
  rw[EXTENSION, O_poly_thm, big_O_def, POLY_def] >>
  rw[EQ_IMP_THM] >| [
    qexists_tac `MAX 1 h` >>
    qexists_tac `k * 2 ** n` >>
    rpt strip_tac >>
    `1 < n'` by metis_tac[MAX_LT] >>
    `0 < ulog n'` by rw[] >>
    `1 + ulog n' <= 2 * ulog n'` by decide_tac >>
    `size n' <= 1 + ulog n'` by rw[size_ulog] >>
    `x n' <= k * size n' ** n` by fs[] >>
    `k * size n' ** n <= k * (2 * ulog n') ** n` by rw[] >>
    `k * (2 * ulog n') ** n = k * 2 ** n * ulog n' ** n` by rw[EXP_BASE_MULT] >>
    decide_tac,
    qexists_tac `k` >>
    qexists_tac `c` >>
    rpt strip_tac >>
    `x n' <= c * ulog n' ** n` by fs[] >>
    `c * ulog n' ** n <= c * size n' ** n` by rw[size_ulog] >>
    decide_tac
  ]);

(* Theorem: 0 < c ==> (big_O (POLY 1 o (\x. c * (size x) ** n)) = O_poly n) *)
(* Proof: by big_O_def, POLY_def, O_poly_thm *)
val big_O_poly_eq_O_poly = store_thm(
  "big_O_poly_eq_O_poly",
  ``!c n. 0 < c ==> (big_O (POLY 1 o (\x. c * (size x) ** n)) = O_poly n)``,
  rw[big_O_def, POLY_def, O_poly_thm, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  metis_tac[] >>
  qexists_tac `h` >>
  qexists_tac `k` >>
  rw[] >>
  `1 <= c` by decide_tac >>
  `x n' <= k * size n' ** n` by rw[] >>
  `k * size n' ** n <= c * (k * size n' ** n)` by rw[] >>
  decide_tac);

(* Theorem: big_O (\n. (size n) ** k) SUBSET big_O (\n. (ulog n) ** k) *)
(* Proof:
   Expand by big_O_def, ulog_by_size, SUBSET_DEF, this is to show:
      !n. k' < n ==> f n <= c * size n ** k
   ==> ?k' c.
      !n. k' < n ==> f n <= c * (if perfect_power n 2 then size n - 1 else size n) ** k

   Take (MAX 1 k') as k', (c * 2 ** k) as c.
   This is to show:
   (1) perfect_power n 2 ==> f n <= c * 2 ** k * (size n - 1) ** k
       Note ?e. n = 2 ** e       by perfect_power_def
        and size n = 1 + e       by size_2_exp
         so size n - 1 = e       by arithmetic
       Note 1 < n /\ k' < n      by MAX_DEF
         so 0 < e                by EXP_0, n = 2 ** e, 1 < n
         or 1 + e <= 2 * e       by arithmetic
       By implication,
          f n <= c * (1 + e) ** k     by k' < n
              <= c * (2 * e) ** k     by EXP_EXP_LE_MONO
               = c * 2 ** k * e ** k  by EXP_BASE_MULT
               = c * 2 ** k * (size n - 1) ** k

   (2) ~perfect_power n 2 ==> f n <= c * 2 ** k * (size n) ** k
       Note 1 < n /\ k' < n           by MAX_DEF
       By implication,
          f n <= c * size n ** k            by k' < n
              <= c * 2 ** k * size n ** k   by EXP_POS, 0 < 2 ** k
*)
val big_O_size_subset_big_O_ulog = store_thm(
  "big_O_size_subset_big_O_ulog",
  ``!k. big_O (\n. (size n) ** k) SUBSET big_O (\n. (ulog n) ** k)``,
  rw[big_O_def, ulog_by_size, SUBSET_DEF] >>
  qexists_tac `MAX 1 k'` >>
  qexists_tac `c * 2 ** k` >>
  rw[] >| [
    `?e. n = 2 ** e` by rw[GSYM perfect_power_def] >>
    `size n = 1 + e` by rw[size_2_exp] >>
    `0 < e` by metis_tac[EXP_0, LESS_NOT_EQ, NOT_ZERO] >>
    `1 + e <= 2 * e` by decide_tac >>
    `x n <= c * (1 + e) ** k` by metis_tac[] >>
    `c * (1 + e) ** k <= c * (2 * e) ** k` by rw[] >>
    `c * (2 * e) ** k = c * 2 ** k * e ** k` by rw[EXP_BASE_MULT] >>
    rw[],
    `x n <= c * size n ** k` by metis_tac[] >>
    `c * size n ** k <= c * 2 ** k * size n ** k` by rw[] >>
    decide_tac
  ]);

(* Theorem: big_O (\n. ulog n ** k) SUBSET big_O (\n. size n ** k) *)
(* Proof:
   Expand by big_O_def, size_by_ulog, SUBSET_DEF, this is to show:
      !n. k' < n ==> f n <= c * ulog n ** k
   ==> ?k' c.
      !n. k' < n ==> f n <= c * (if n = 0 \/ perfect_power n 2 then 1 + ulog n else ulog n) ** k
   Take same k' and c.
   If perfect_power n 2,
      By implication,
         f n <= c * ulog n ** k         by k' < n
             <= c * (ulog n + 1) ** k   by EXP_EXP_LE_MONO
   If ~perfect_power n 2,
      By implication,
         f n <= c * ulog n ** k         by k' < n
*)
val big_O_ulog_subset_big_O_size = store_thm(
  "big_O_ulog_subset_big_O_size",
  ``!k. big_O (\n. ulog n ** k) SUBSET big_O (\n. size n ** k)``,
  rw[big_O_def, size_by_ulog, SUBSET_DEF] >>
  qexists_tac `k'` >>
  qexists_tac `c` >>
  rw[] >>
  `x n <= c * ulog n ** k` by metis_tac[] >>
  `c * (ulog n) ** k <= c * (ulog n + 1) ** k` by rw[] >>
  decide_tac);

(* Theorem: big_O (\n. size n ** k) = big_O (\n. ulog n ** k) *)
(* Proof:
   By SUBSET_ANTISYM, this is to show:
   (1) big_O (\n. size n ** k) SUBSET big_O (\n. ulog n ** k)
       This is true by big_O_size_subset_big_O_ulog.
   (2) big_O (\n. ulog n ** k) SUBSET big_O (\n. size n ** k)
       This is true by big_O_ulog_subset_big_O_size.
*)
val big_O_size_eq_big_O_ulog = store_thm(
  "big_O_size_eq_big_O_ulog",
  ``!k. big_O (\n. size n ** k) = big_O (\n. ulog n ** k)``,
  rw[big_O_size_subset_big_O_ulog, big_O_ulog_subset_big_O_size, SUBSET_ANTISYM]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
