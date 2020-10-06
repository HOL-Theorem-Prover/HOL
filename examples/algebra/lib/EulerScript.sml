(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "Euler";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "helperFunctionTheory"; *)
(* (* val _ = load "helperNumTheory"; -- in helperFunctionTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in helperFunctionTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* open dependent theories *)
open pred_setTheory listTheory;
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open arithmeticTheory dividesTheory gcdTheory;


(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function Documentation                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   natural n    = IMAGE SUC (count n)
   upto n       = count (SUC n)
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   Residues:
   residue_def       |- !n. residue n = {i | 0 < i /\ i < n}
   residue_element   |- !n j. j IN residue n ==> 0 < j /\ j < n
   residue_0         |- residue 0 = {}
   residue_1         |- residue 1 = {}
   residue_nonempty  |- !n. 1 < n ==> residue n <> {}
   residue_no_zero   |- !n. 0 NOTIN residue n
   residue_no_self   |- !n. n NOTIN residue n
!  residue_thm       |- !n. residue n = count n DIFF {0}
   residue_insert    |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n)
   residue_delete    |- !n. 0 < n ==> (residue n DELETE n = residue n)
   residue_suc       |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n)
   residue_count     |- !n. 0 < n ==> (count n = 0 INSERT residue n)
   residue_finite    |- !n. FINITE (residue n)
   residue_card      |- !n. 0 < n ==> (CARD (residue n) = n - 1)
   residue_prime_neq |- !p a n. prime p /\ a IN residue p /\ n <= p ==>
                        !x. x IN residue n ==> (a * n) MOD p <> (a * x) MOD p
   prod_set_residue  |- !n. PROD_SET (residue n) = FACT (n - 1)

   Naturals:
   natural_element  |- !n j. j IN natural n <=> 0 < j /\ j <= n
   natural_property |- !n. natural n = {j | 0 < j /\ j <= n}
   natural_finite   |- !n. FINITE (natural n)
   natural_card     |- !n. CARD (natural n) = n
   natural_not_0    |- !n. 0 NOTIN natural n
   natural_0        |- natural 0 = {}
   natural_1        |- natural 1 = {1}
   natural_has_1    |- !n. 0 < n ==> 1 IN natural n
   natural_has_last |- !n. 0 < n ==> n IN natural n
   natural_suc      |- !n. natural (SUC n) = SUC n INSERT natural n
   natural_thm      |- !n. natural n = set (GENLIST SUC n)
   natural_divisor_natural   |- !n a b. 0 < n /\ a IN natural n /\ b divides a ==> b IN natural n
   natural_cofactor_natural  |- !n a b. 0 < n /\ 0 < a /\ b IN natural n /\ a divides b ==>
                                        b DIV a IN natural n
   natural_cofactor_natural_reduced
                             |- !n a b. 0 < n /\ a divides n /\ b IN natural n /\ a divides b ==>
                                        b DIV a IN natural (n DIV a)

   Uptos:
   upto_finite      |- !n. FINITE (upto n)
   upto_card        |- !n. CARD (upto n) = SUC n
   upto_has_last    |- !n. n IN upto n
   upto_split_first |- !n. upto n = {0} UNION natural n
   upto_split_last  |- !n. upto n = count n UNION {n}
   upto_by_count    |- !n. upto n = n INSERT count n
   upto_by_natural  |- !n. upto n = 0 INSERT natural n
   natural_by_upto  |- !n. natural n = upto n DELETE 0

   Euler Set and Totient Function:
   Euler_def            |- !n. Euler n = {i | 0 < i /\ i < n /\ coprime n i}
   totient_def          |- !n. totient n = CARD (Euler n)
   Euler_element        |- !n x. x IN Euler n <=> 0 < x /\ x < n /\ coprime n x
!  Euler_thm            |- !n. Euler n = residue n INTER {j | coprime j n}
   Euler_finite         |- !n. FINITE (Euler n)
   Euler_0              |- Euler 0 = {}
   Euler_1              |- Euler 1 = {}
   Euler_has_1          |- !n. 1 < n ==> 1 IN Euler n
   Euler_nonempty       |- !n. 1 < n ==> Euler n <> {}
   Euler_empty          |- !n. (Euler n = {}) <=> (n = 0 \/ n = 1)
   Euler_card_upper_le  |- !n. totient n <= n
   Euler_card_upper_lt  |- !n. 1 < n ==> totient n < n
   Euler_card_bounds    |- !n. totient n <= n /\ (1 < n ==> 0 < totient n /\ totient n < n)
   Euler_prime          |- !p. prime p ==> (Euler p = residue p)
   Euler_card_prime     |- !p. prime p ==> (totient p = p - 1)

   Summation of Geometric Sequence:
   sigma_geometric_natural_eqn   |- !p. 0 < p ==>
                                    !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1)
   sigma_geometric_natural       |- !p. 1 < p ==>
                                    !n. SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) DIV (p - 1)

   Useful Theorems:
   PROD_SET_IMAGE_EXP_NONZERO    |- !n m. 1 < n /\ 0 < m ==>
                                         (PROD_SET (IMAGE (\j. n ** j) (count m)) =
                                          PROD_SET (IMAGE (\j. n ** j) (residue m)))
*)

(* ------------------------------------------------------------------------- *)
(* Count-based Sets                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Residues -- close-relative of COUNT                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the set of residues = nonzero remainders *)
val residue_def = zDefine `residue n = { i | (0 < i) /\ (i < n) }`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: j IN residue n ==> 0 < j /\ j < n *)
(* Proof: by residue_def. *)
val residue_element = store_thm(
  "residue_element",
  ``!n j. j IN residue n ==> 0 < j /\ j < n``,
  rw[residue_def]);

(* Theorem: residue 0 = EMPTY *)
(* Proof: by residue_def *)
val residue_0 = store_thm(
  "residue_0",
  ``residue 0 = {}``,
  simp[residue_def]);

(* Theorem: residue 1 = EMPTY *)
(* Proof: by definition. *)
val residue_1 = store_thm(
  "residue_1",
  ``residue 1 = {}``,
  simp[residue_def]);

(* Theorem: 1 < n ==> residue n <> {} *)
(* Proof:
   By residue_def, this is to show: 1 < n ==> ?x. x <> 0 /\ x < n
   Take x = 1, this is true.
*)
val residue_nonempty = store_thm(
  "residue_nonempty",
  ``!n. 1 < n ==> residue n <> {}``,
  rw[residue_def, EXTENSION] >>
  metis_tac[DECIDE``1 <> 0``]);

(* Theorem: 0 NOTIN residue n *)
(* Proof: by residue_def *)
val residue_no_zero = store_thm(
  "residue_no_zero",
  ``!n. 0 NOTIN residue n``,
  simp[residue_def]);

(* Theorem: n NOTIN residue n *)
(* Proof: by residue_def *)
val residue_no_self = store_thm(
  "residue_no_self",
  ``!n. n NOTIN residue n``,
  simp[residue_def]);

(* Theorem: residue n = (count n) DIFF {0} *)
(* Proof:
     residue n
   = {i | 0 < i /\ i < n}   by residue_def
   = {i | i < n /\ i <> 0}  by NOT_ZERO_LT_ZERO
   = {i | i < n} DIFF {0}   by IN_DIFF
   = (count n) DIFF {0}     by count_def
*)
val residue_thm = store_thm(
  "residue_thm[compute]",
  ``!n. residue n = (count n) DIFF {0}``,
  rw[residue_def, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``residue 10``;
val it = |- residue 10 = {9; 8; 7; 6; 5; 4; 3; 2; 1}: thm
*)

(* Theorem: For n > 0, residue (SUC n) = n INSERT residue n *)
(* Proof:
     residue (SUC n)
   = {1, 2, ..., n}
   = n INSERT {1, 2, ..., (n-1) }
   = n INSERT residue n
*)
val residue_insert = store_thm(
  "residue_insert",
  ``!n. 0 < n ==> (residue (SUC n) = n INSERT residue n)``,
  srw_tac[ARITH_ss][residue_def, EXTENSION]);

(* Theorem: (residue n) DELETE n = residue n *)
(* Proof: Because n is not in (residue n). *)
val residue_delete = store_thm(
  "residue_delete",
  ``!n. 0 < n ==> ((residue n) DELETE n = residue n)``,
  rpt strip_tac >>
  `n NOTIN (residue n)` by rw[residue_def] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem alias: rename *)
val residue_suc = save_thm("residue_suc", residue_insert);
(* val residue_suc = |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n): thm *)

(* Theorem: count n = 0 INSERT (residue n) *)
(* Proof: by definition. *)
val residue_count = store_thm(
  "residue_count",
  ``!n. 0 < n ==> (count n = 0 INSERT (residue n))``,
  srw_tac[ARITH_ss][residue_def, EXTENSION]);

(* Theorem: FINITE (residue n) *)
(* Proof: by FINITE_COUNT.
   If n = 0, residue 0 = {}, hence FINITE.
   If n > 0, count n = 0 INSERT (residue n)  by residue_count
   hence true by FINITE_COUNT and FINITE_INSERT.
*)
val residue_finite = store_thm(
  "residue_finite",
  ``!n. FINITE (residue n)``,
  Cases >-
  rw[residue_def] >>
  metis_tac[residue_count, FINITE_INSERT, count_def, FINITE_COUNT, DECIDE ``0 < SUC n``]);

(* Theorem: For n > 0, CARD (residue n) = n-1 *)
(* Proof:
   Since 0 INSERT (residue n) = count n by residue_count
   the result follows by CARD_COUNT.
*)
val residue_card = store_thm(
  "residue_card",
  ``!n. 0 < n ==> (CARD (residue n) = n-1)``,
  rpt strip_tac >>
  `0 NOTIN (residue n)` by rw[residue_def] >>
  `0 INSERT (residue n) = count n` by rw[residue_count] >>
  `SUC (CARD (residue n)) = n` by metis_tac[residue_finite, CARD_INSERT, CARD_COUNT] >>
  decide_tac);

(* Theorem: For prime m, a in residue m, n <= m, a*n MOD m <> a*x MOD m  for all x in residue n *)
(* Proof:
   Assume the contrary, that a*n MOD m = a*x MOD m
   Since a in residue m and m is prime, MOD_MULT_LCANCEL gives: n MOD m = x MOD m
   If n = m, n MOD m = 0, but x MOD m <> 0, hence contradiction.
   If n < m, then since x < n <= m, n = x, contradicting x < n.
*)
val residue_prime_neq = store_thm(
  "residue_prime_neq",
  ``!p a n. prime p /\ a IN (residue p) /\ n <= p ==> !x. x IN (residue n) ==> (a*n) MOD p <> (a*x) MOD p``,
  rw[residue_def] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `(a MOD p <> 0) /\ (x MOD p <> 0)` by rw_tac arith_ss[] >>
  `n MOD p = x MOD p` by metis_tac[MOD_MULT_LCANCEL] >>
  Cases_on `n = p` >-
  metis_tac [DIVMOD_ID] >>
  `n < p` by decide_tac >>
  `(n MOD p = n) /\ (x MOD p = x)` by rw_tac arith_ss[] >>
  decide_tac);

(* Idea: the product of residues is a factorial. *)

(* Theorem: PROD_SET (residue n) = FACT (n - 1) *)
(* Proof:
   By induction on n.
   Base: PROD_SET (residue 0) = FACT (0 - 1)
        PROD_SET (residue 0)
      = PROD_SET {}           by residue_0
      = 1                     by PROD_SET_EMPTY
      = FACT 0                by FACT_0
      = FACT (0 - 1)          by arithmetic
   Step: PROD_SET (residue n) = FACT (n - 1) ==>
         PROD_SET (residue (SUC n)) = FACT (SUC n - 1)
      If n = 0,
        PROD_SET (residue (SUC 0))
      = PROD_SET (residue 1)  by ONE
      = PROD_SET {}           by residue_1
      = 1                     by PROD_SET_EMPTY
      = FACT 0                by FACT_0

      If n <> 0, then 0 < n.
      Note FINITE (residue n)                by residue_finite
        PROD_SET (residue (SUC n))
      = PROD_SET (n INSERT residue n)        by residue_insert
      = n * PROD_SET ((residue n) DELETE n)  by PROD_SET_THM
      = n * PROD_SET (residue n)             by residue_delete
      = n * FACT (n - 1)                     by induction hypothesis
      = FACT (SUC (n - 1))                   by FACT
      = FACT (SUC n - 1)                     by arithmetic
*)
val prod_set_residue = store_thm(
  "prod_set_residue",
  ``!n. PROD_SET (residue n) = FACT (n - 1)``,
  Induct >-
  simp[residue_0, PROD_SET_EMPTY, FACT_0] >>
  Cases_on `n = 0` >-
  simp[residue_1, PROD_SET_EMPTY, FACT_0] >>
  `FINITE (residue n)` by rw[residue_finite] >>
  `n = SUC (n - 1)` by decide_tac >>
  `SUC (n - 1) = SUC n - 1` by decide_tac >>
  `PROD_SET (residue (SUC n)) = PROD_SET (n INSERT residue n)` by rw[residue_insert] >>
  `_ = n * PROD_SET ((residue n) DELETE n)` by rw[PROD_SET_THM] >>
  `_ = n * PROD_SET (residue n)` by rw[residue_delete] >>
  `_ = n * FACT (n - 1)` by rw[] >>
  metis_tac[FACT]);

(* ------------------------------------------------------------------------- *)
(* Naturals -- counting from 1 rather than 0, and inclusive.                 *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of natural numbers (like count) *)
val _ = overload_on("natural", ``\n. IMAGE SUC (count n)``);

(* Theorem: j IN (natural n) <=> 0 < j /\ j <= n *)
(* Proof:
   Note j <> 0                     by natural_not_0
       j IN (natural n)
   ==> j IN IMAGE SUC (count n)    by notation
   ==> ?x. x < n /\ (j = SUC x)    by IN_IMAGE
   Since SUC x <> 0                by numTheory.NOT_SUC
   Hence j <> 0,
     and x  < n ==> SUC x < SUC n  by LESS_MONO_EQ
      or j < SUC n                 by above, j = SUC x
    thus j <= n                    by prim_recTheory.LESS_THM
*)
val natural_element = store_thm(
  "natural_element",
  ``!n j. j IN (natural n) <=> 0 < j /\ j <= n``,
  rw[EQ_IMP_THM] >>
  `j <> 0` by decide_tac >>
  `?m. j = SUC m` by metis_tac[num_CASES] >>
  `m < n` by decide_tac >>
  metis_tac[]);

(* Theorem: natural n = {j| 0 < j /\ j <= n} *)
(* Proof: by natural_element, IN_IMAGE *)
val natural_property = store_thm(
  "natural_property",
  ``!n. natural n = {j| 0 < j /\ j <= n}``,
  rw[EXTENSION, natural_element]);

(* Theorem: FINITE (natural n) *)
(* Proof: FINITE_COUNT, IMAGE_FINITE *)
val natural_finite = store_thm(
  "natural_finite",
  ``!n. FINITE (natural n)``,
  rw[]);

(* Theorem: CARD (natural n) = n *)
(* Proof:
     CARD (natural n)
   = CARD (IMAGE SUC (count n))  by notation
   = CARD (count n)              by CARD_IMAGE_SUC
   = n                           by CARD_COUNT
*)
val natural_card = store_thm(
  "natural_card",
  ``!n. CARD (natural n) = n``,
  rw[CARD_IMAGE_SUC]);

(* Theorem: 0 NOTIN (natural n) *)
(* Proof: by NOT_SUC *)
val natural_not_0 = store_thm(
  "natural_not_0",
  ``!n. 0 NOTIN (natural n)``,
  rw[]);

(* Theorem: natural 0 = {} *)
(* Proof:
     natural 0
   = IMAGE SUC (count 0)    by notation
   = IMAGE SUC {}           by COUNT_ZERO
   = {}                     by IMAGE_EMPTY
*)
val natural_0 = store_thm(
  "natural_0",
  ``natural 0 = {}``,
  rw[]);

(* Theorem: natural 1 = {1} *)
(* Proof:
     natural 1
   = IMAGE SUC (count 1)    by notation
   = IMAGE SUC {0}          by count_add1
   = {SUC 0}                by IMAGE_DEF
   = {1}                    by ONE
*)
val natural_1 = store_thm(
  "natural_1",
  ``natural 1 = {1}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: 0 < n ==> 1 IN (natural n) *)
(* Proof: by natural_element, LESS_OR, ONE *)
val natural_has_1 = store_thm(
  "natural_has_1",
  ``!n. 0 < n ==> 1 IN (natural n)``,
  rw[natural_element]);

(* Theorem: 0 < n ==> n IN (natural n) *)
(* Proof: by natural_element *)
val natural_has_last = store_thm(
  "natural_has_last",
  ``!n. 0 < n ==> n IN (natural n)``,
  rw[natural_element]);

(* Theorem: natural (SUC n) = (SUC n) INSERT (natural n) *)
(* Proof:
       natural (SUC n)
   <=> {j | 0 < j /\ j <= (SUC n)}              by natural_property
   <=> {j | 0 < j /\ (j <= n \/ (j = SUC n))}   by LE
   <=> {j | j IN (natural n) \/ (j = SUC n)}    by natural_property
   <=> (SUC n) INSERT (natural n)               by INSERT_DEF
*)
val natural_suc = store_thm(
  "natural_suc",
  ``!n. natural (SUC n) = (SUC n) INSERT (natural n)``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: natural n = set (GENLIST SUC n) *)
(* Proof:
   By induction on n.
   Base: natural 0 = set (GENLIST SUC 0)
      LHS = natural 0 = {}         by natural_0
      RHS = set (GENLIST SUC 0)
          = set []                 by GENLIST_0
          = {}                     by LIST_TO_SET
   Step: natural n = set (GENLIST SUC n) ==>
         natural (SUC n) = set (GENLIST SUC (SUC n))
         natural (SUC n)
       = SUC n INSERT natural n                 by natural_suc
       = SUC n INSERT (set (GENLIST SUC n))     by induction hypothesis
       = set (SNOC (SUC n) (GENLIST SUC n))     by LIST_TO_SET_SNOC
       = set (GENLIST SUC (SUC n))              by GENLIST
*)
val natural_thm = store_thm(
  "natural_thm",
  ``!n. natural n = set (GENLIST SUC n)``,
  Induct >-
  rw[] >>
  rw[natural_suc, LIST_TO_SET_SNOC, GENLIST]);

(* Theorem: 0 < n /\ a IN (natural n) /\ b divides a ==> b IN (natural n) *)
(* Proof:
   By natural_element, this is to show:
   (1) 0 < a /\ b divides a ==> 0 < b
       True by divisor_pos
   (2) 0 < a /\ b divides a ==> b <= n
       Since b divides a
         ==> b <= a                     by DIVIDES_LE, 0 < a
         ==> b <= n                     by LESS_EQ_TRANS
*)
val natural_divisor_natural = store_thm(
  "natural_divisor_natural",
  ``!n a b. 0 < n /\ a IN (natural n) /\ b divides a ==> b IN (natural n)``,
  rw[natural_element] >-
  metis_tac[divisor_pos] >>
  metis_tac[DIVIDES_LE, LESS_EQ_TRANS]);

(* Theorem: 0 < n /\ 0 < a /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural n) *)
(* Proof:
   Let c = b DIV a.
   By natural_element, this is to show:
      0 < a /\ 0 < b /\ b <= n /\ a divides b ==> 0 < c /\ c <= n
   Since a divides b ==> b = c * a               by DIVIDES_EQN, 0 < a
      so b = a * c                               by MULT_COMM
      or c divides b                             by divides_def
    Thus 0 < c /\ c <= b                         by divides_pos
      or c <= n                                  by LESS_EQ_TRANS
*)
val natural_cofactor_natural = store_thm(
  "natural_cofactor_natural",
  ``!n a b. 0 < n /\ 0 < a /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural n)``,
  rewrite_tac[natural_element] >>
  ntac 4 strip_tac >>
  qabbrev_tac `c = b DIV a` >>
  `b = c * a` by rw[GSYM DIVIDES_EQN, Abbr`c`] >>
  `c divides b` by metis_tac[divides_def, MULT_COMM] >>
  `0 < c /\ c <= b` by metis_tac[divides_pos] >>
  decide_tac);

(* Theorem: 0 < n /\ a divides n /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural (n DIV a)) *)
(* Proof:
   Let c = b DIV a.
   By natural_element, this is to show:
      0 < n /\ a divides b /\ 0 < b /\ b <= n /\ a divides b ==> 0 < c /\ c <= n DIV a
   Note 0 < a                                    by ZERO_DIVIES, 0 < n
   Since a divides b ==> b = c * a               by DIVIDES_EQN, 0 < a [1]
      or c divides b                             by divides_def, MULT_COMM
    Thus 0 < c, since 0 divides b means b = 0.   by ZERO_DIVIDES, b <> 0
     Now n = (n DIV a) * a                       by DIVIDES_EQN, 0 < a [2]
    With b <= n, c * a <= (n DIV a) * a          by [1], [2]
   Hence c <= n DIV a                            by LE_MULT_RCANCEL, a <> 0
*)
val natural_cofactor_natural_reduced = store_thm(
  "natural_cofactor_natural_reduced",
  ``!n a b. 0 < n /\ a divides n /\
           b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural (n DIV a))``,
  rewrite_tac[natural_element] >>
  ntac 4 strip_tac >>
  qabbrev_tac `c = b DIV a` >>
  `a <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  `(b = c * a) /\ (n = (n DIV a) * a)` by rw[GSYM DIVIDES_EQN, Abbr`c`] >>
  `c divides b` by metis_tac[divides_def, MULT_COMM] >>
  `0 < c` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  metis_tac[LE_MULT_RCANCEL]);

(* ------------------------------------------------------------------------- *)
(* Uptos -- counting from 0 and inclusive.                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload on another count-related set *)
val _ = overload_on("upto", ``\n. count (SUC n)``);

(* Theorem: FINITE (upto n) *)
(* Proof: by FINITE_COUNT *)
val upto_finite = store_thm(
  "upto_finite",
  ``!n. FINITE (upto n)``,
  rw[]);

(* Theorem: CARD (upto n) = SUC n *)
(* Proof: by CARD_COUNT *)
val upto_card = store_thm(
  "upto_card",
  ``!n. CARD (upto n) = SUC n``,
  rw[]);

(* Theorem: n IN (upto n) *)
(* Proof: byLESS_SUC_REFL *)
val upto_has_last = store_thm(
  "upto_has_last",
  ``!n. n IN (upto n)``,
  rw[]);

(* Theorem: upto n = {0} UNION (natural n) *)
(* Proof:
   By UNION_DEF, EXTENSION, this is to show:
   (1) x < SUC n ==> (x = 0) \/ ?x'. (x = SUC x') /\ x' < n
       If x = 0, trivially true.
       If x <> 0, x = SUC m.
          Take x' = m,
          then SUC m = x < SUC n ==> m < n   by LESS_MONO_EQ
   (2) (x = 0) \/ ?x'. (x = SUC x') /\ x' < n ==> x < SUC n
       If x = 0, 0 < SUC n                   by SUC_POS
       If ?x'. (x = SUC x') /\ x' < n,
          x' < n ==> SUC x' = x < SUC n      by LESS_MONO_EQ
*)
val upto_split_first = store_thm(
  "upto_split_first",
  ``!n. upto n = {0} UNION (natural n)``,
  rw[EXTENSION, EQ_IMP_THM] >>
  Cases_on `x` >-
  rw[] >>
  metis_tac[LESS_MONO_EQ]);

(* Theorem: upto n = (count n) UNION {n} *)
(* Proof:
   By UNION_DEF, EXTENSION, this is to show:
   (1) x < SUC n ==> x < n \/ (x = n)
       True by LESS_THM.
   (2) x < n \/ (x = n) ==> x < SUC n
       True by LESS_THM.
*)
val upto_split_last = store_thm(
  "upto_split_last",
  ``!n. upto n = (count n) UNION {n}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: upto n = n INSERT (count n) *)
(* Proof:
     upto n
   = count (SUC n)             by notation
   = {x | x < SUC n}           by count_def
   = {x | (x = n) \/ (x < n)}  by prim_recTheory.LESS_THM
   = x INSERT {x| x < n}       by INSERT_DEF
   = x INSERT (count n)        by count_def
*)
val upto_by_count = store_thm(
  "upto_by_count",
  ``!n. upto n = n INSERT (count n)``,
  rw[EXTENSION]);

(* Theorem: upto n = 0 INSERT (natural n) *)
(* Proof:
     upto n
   = count (SUC n)             by notation
   = {x | x < SUC n}           by count_def
   = {x | ((x = 0) \/ (?m. x = SUC m)) /\ x < SUC n)}            by num_CASES
   = {x | (x = 0 /\ x < SUC n) \/ (?m. x = SUC m /\ x < SUC n)}  by SUC_POS
   = 0 INSERT {SUC m | SUC m < SUC n}   by INSERT_DEF
   = 0 INSERT {SUC m | m < n}           by LESS_MONO_EQ
   = 0 INSERT (IMAGE SUC (count n))     by IMAGE_DEF
   = 0 INSERT (natural n)               by notation
*)
val upto_by_natural = store_thm(
  "upto_by_natural",
  ``!n. upto n = 0 INSERT (natural n)``,
  rw[EXTENSION] >>
  metis_tac[num_CASES, LESS_MONO_EQ, SUC_POS]);

(* Theorem: natural n = count (SUC n) DELETE 0 *)
(* Proof:
     count (SUC n) DELETE 0
   = {x | x < SUC n} DELETE 0    by count_def
   = {x | x < SUC n} DIFF {0}    by DELETE_DEF
   = {x | x < SUC n /\ x <> 0}   by DIFF_DEF
   = {SUC m | SUC m < SUC n}     by num_CASES
   = {SUC m | m < n}             by LESS_MONO_EQ
   = IMAGE SUC (count n)         by IMAGE_DEF
   = natural n                   by notation
*)
val natural_by_upto = store_thm(
  "natural_by_upto",
  ``!n. natural n = count (SUC n) DELETE 0``,
  (rw[EXTENSION, EQ_IMP_THM] >> metis_tac[num_CASES, LESS_MONO_EQ]));

(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function                                            *)
(* ------------------------------------------------------------------------- *)

(* Euler's totient function *)
val Euler_def = zDefine`
  Euler n = { i | 0 < i /\ i < n /\ (gcd n i = 1) }
`;
(* that is, Euler n = { i | i in (residue n) /\ (gcd n i = 1) }`; *)
(* use zDefine as this is not computationally effective. *)

val totient_def = Define`
  totient n = CARD (Euler n)
`;

(* Theorem: x IN (Euler n) <=> 0 < x /\ x < n /\ coprime n x *)
(* Proof: by Euler_def. *)
val Euler_element = store_thm(
  "Euler_element",
  ``!n x. x IN (Euler n) <=> 0 < x /\ x < n /\ coprime n x``,
  rw[Euler_def]);

(* Theorem: Euler n = (residue n) INTER {j | coprime j n} *)
(* Proof: by Euler_def, residue_def, EXTENSION, IN_INTER *)
val Euler_thm = store_thm(
  "Euler_thm[compute]",
  ``!n. Euler n = (residue n) INTER {j | coprime j n}``,
  rw[Euler_def, residue_def, GCD_SYM, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``Euler 10``;
val it = |- Euler 10 = {9; 7; 3; 1}: thm
> EVAL ``totient 10``;
val it = |- totient 10 = 4: thm
*)

(* Theorem: FINITE (Euler n) *)
(* Proof:
   Since (Euler n) SUBSET count n  by Euler_def, SUBSET_DEF
     and FINITE (count n)          by FINITE_COUNT
     ==> FINITE (Euler n)          by SUBSET_FINITE
*)
val Euler_finite = store_thm(
  "Euler_finite",
  ``!n. FINITE (Euler n)``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  metis_tac[FINITE_COUNT, SUBSET_FINITE]);

(* Theorem: Euler 0 = {} *)
(* Proof: by Euler_def *)
val Euler_0 = store_thm(
  "Euler_0",
  ``Euler 0 = {}``,
  rw[Euler_def]);

(* Theorem: Euler 1 = {} *)
(* Proof: by Euler_def *)
val Euler_1 = store_thm(
  "Euler_1",
  ``Euler 1 = {}``,
  rw[Euler_def]);

(* Theorem: 1 < n ==> 1 IN (Euler n) *)
(* Proof: by Euler_def *)
val Euler_has_1 = store_thm(
  "Euler_has_1",
  ``!n. 1 < n ==> 1 IN (Euler n)``,
  rw[Euler_def]);

(* Theorem: 1 < n ==> (Euler n) <> {} *)
(* Proof: by Euler_has_1, MEMBER_NOT_EMPTY *)
val Euler_nonempty = store_thm(
  "Euler_nonempty",
  ``!n. 1 < n ==> (Euler n) <> {}``,
  metis_tac[Euler_has_1, MEMBER_NOT_EMPTY]);

(* Theorem: (Euler n = {}) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: Euler n = {} ==> n = 0 \/ n = 1
      By contradiction, suppose ~(n = 0 \/ n = 1).
      Then 1 < n, but Euler n <> {}   by Euler_nonempty
      This contradicts Euler n = {}.
   Only-if part: n = 0 \/ n = 1 ==> Euler n = {}
      Note Euler 0 = {}               by Euler_0
       and Euler 1 = {}               by Euler_1
*)
val Euler_empty = store_thm(
  "Euler_empty",
  ``!n. (Euler n = {}) <=> ((n = 0) \/ (n = 1))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `1 < n` by decide_tac >>
    metis_tac[Euler_nonempty],
    rw[Euler_0],
    rw[Euler_1]
  ]);

(* Theorem: totient n <= n *)
(* Proof:
   Since (Euler n) SUBSET count n  by Euler_def, SUBSET_DEF
     and FINITE (count n)          by FINITE_COUNT
     and (CARD (count n) = n       by CARD_COUNT
   Hence CARD (Euler n) <= n       by CARD_SUBSET
      or totient n <= n            by totient_def
*)
val Euler_card_upper_le = store_thm(
  "Euler_card_upper_le",
  ``!n. totient n <= n``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  metis_tac[totient_def, CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);

(* Theorem: 1 < n ==> totient n < n *)
(* Proof:
   First, (Euler n) SUBSET count n     by Euler_def, SUBSET_DEF
     Now, ~(coprime 0 n)               by coprime_0L, n <> 1
      so  0 NOTIN (Euler n)            by Euler_def
     but  0 IN (count n)               by IN_COUNT, 0 < n
    Thus  (Euler n) <> (count n)       by EXTENSION
     and  (Euler n) PSUBSET (count n)  by PSUBSET_DEF
   Since  FINITE (count n)             by FINITE_COUNT
     and  (CARD (count n) = n          by CARD_COUNT
   Hence  CARD (Euler n) < n           by CARD_PSUBSET
      or  totient n < n                by totient_def
*)
val Euler_card_upper_lt = store_thm(
  "Euler_card_upper_lt",
  ``!n. 1 < n ==> totient n < n``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  `0 < n /\ n <> 1` by decide_tac >>
  `~(coprime 0 n)` by metis_tac[coprime_0L] >>
  `0 NOTIN (Euler n)` by rw[Euler_def] >>
  `0 IN (count n)` by rw[] >>
  `(Euler n) <> (count n)` by metis_tac[EXTENSION] >>
  `(Euler n) PSUBSET (count n)` by rw[PSUBSET_DEF] >>
  metis_tac[totient_def, CARD_PSUBSET, FINITE_COUNT, CARD_COUNT]);

(* Theorem: (totient n <= n) /\ (1 < n ==> 0 < totient n /\ totient n < n) *)
(* Proof:
   This is to show:
   (1) totient n <= n,
       True by Euler_card_upper_le.
   (2) 1 < n ==> 0 < totient n
       Since (Euler n) <> {}      by Euler_nonempty
        Also FINITE (Euler n)     by Euler_finite
       Hence CARD (Euler n) <> 0  by CARD_EQ_0
          or 0 < totient n        by totient_def
   (3) 1 < n ==> totient n < n
       True by Euler_card_upper_lt.
*)
val Euler_card_bounds = store_thm(
  "Euler_card_bounds",
  ``!n. (totient n <= n) /\ (1 < n ==> 0 < totient n /\ totient n < n)``,
  rw[] >-
  rw[Euler_card_upper_le] >-
 (`(Euler n) <> {}` by rw[Euler_nonempty] >>
  `FINITE (Euler n)` by rw[Euler_finite] >>
  `totient n <> 0` by metis_tac[totient_def, CARD_EQ_0] >>
  decide_tac) >>
  rw[Euler_card_upper_lt]);

(* Theorem: For prime p, (Euler p = residue p) *)
(* Proof:
   By Euler_def, residue_def, this is to show:
   For prime p, gcd p x = 1   for 0 < x < p.
   Since x < p, x does not divide p, result follows by PRIME_GCD.
   or, this is true by prime_coprime_all_lt
*)
val Euler_prime = store_thm(
  "Euler_prime",
  ``!p. prime p ==> (Euler p = residue p)``,
  rw[Euler_def, residue_def, EXTENSION, EQ_IMP_THM] >>
  rw[prime_coprime_all_lt]);

(* Theorem: For prime p, totient p = p - 1 *)
(* Proof:
      totient p
    = CARD (Euler p)    by totient_def
    = CARD (residue p)  by Euler_prime
    = p - 1             by residue_card, and prime p > 0.
*)
val Euler_card_prime = store_thm(
  "Euler_card_prime",
  ``!p. prime p ==> (totient p = p - 1)``,
  rw[totient_def, Euler_prime, residue_card, PRIME_POS]);

(* ------------------------------------------------------------------------- *)
(* Summation of Geometric Sequence                                           *)
(* ------------------------------------------------------------------------- *)

(* Geometric Series:
   Let s = p + p ** 2 + p ** 3
   p * s = p ** 2 + p ** 3 + p ** 4
   p * s - s = p ** 4 - p
   (p - 1) * s = p * (p ** 3 - 1)
*)

(* Theorem: 0 < p ==> !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) *)
(* Proof:
   By induction on n.
   Base: (p - 1) * SIGMA (\j. p ** j) (natural 0) = p * (p ** 0 - 1)
      LHS = (p - 1) * SIGMA (\j. p ** j) (natural 0)
          = (p - 1) * SIGMA (\j. p ** j) {}          by natural_0
          = (p - 1) * 0                              by SUM_IMAGE_EMPTY
          = 0                                        by MULT_0
      RHS = p * (p ** 0 - 1)
          = p * (1 - 1)                              by EXP
          = p * 0                                    by SUB_EQUAL_0
          = 0 = LHS                                  by MULT_0
   Step: (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) ==>
         (p - 1) * SIGMA (\j. p ** j) (natural (SUC n)) = p * (p ** SUC n - 1)
      Note FINITE (natural n)                        by natural_finite
       and (SUC n) NOTIN (natural n)                 by natural_element
      Also p <= p ** (SUC n)                         by X_LE_X_EXP, SUC_POS
       and 1 <= p                                    by 0 < p
      thus p ** (SUC n) <> 0                         by EXP_POS, 0 < p
        so p ** (SUC n) <= p * p ** (SUC n)          by LE_MULT_LCANCEL, p ** (SUC n) <> 0
        (p - 1) * SIGMA (\j. p ** j) (natural (SUC n))
      = (p - 1) * SIGMA (\j. p ** j) ((SUC n) INSERT (natural n))                   by natural_suc
      = (p - 1) * ((p ** SUC n) + SIGMA (\j. p ** j) ((natural n) DELETE (SUC n)))  by SUM_IMAGE_THM
      = (p - 1) * ((p ** SUC n) + SIGMA (\j. p ** j) (natural n))                   by DELETE_NON_ELEMENT
      = (p - 1) * (p ** SUC n) + (p - 1) * SIGMA (\j. p ** j) (natural n)           by LEFT_ADD_DISTRIB
      = (p - 1) * (p ** SUC n) + p * (p ** n - 1)        by induction hypothesis
      = (p - 1) * (p ** SUC n) + (p * p ** n - p)        by LEFT_SUB_DISTRIB
      = (p - 1) * (p ** SUC n) + (p ** (SUC n) - p)      by EXP
      = (p * p ** SUC n - p ** SUC n) + (p ** SUC n - p) by RIGHT_SUB_DISTRIB
      = (p * p ** SUC n - p ** SUC n + p ** SUC n - p    by LESS_EQ_ADD_SUB, p <= p ** (SUC n)
      = p ** p ** SUC n - p                              by SUB_ADD, p ** (SUC n) <= p * p ** (SUC n)
      = p * (p ** SUC n - 1)                             by LEFT_SUB_DISTRIB
 *)
val sigma_geometric_natural_eqn = store_thm(
  "sigma_geometric_natural_eqn",
  ``!p. 0 < p ==> !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[natural_0, SUM_IMAGE_EMPTY, EXP, MULT_0] >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `(SUC n) NOTIN (natural n)` by rw[natural_element] >>
  qabbrev_tac `q = p ** SUC n` >>
  `p <= q` by rw[X_LE_X_EXP, Abbr`q`] >>
  `1 <= p` by decide_tac >>
  `q <> 0` by rw[EXP_POS, Abbr`q`] >>
  `q <= p * q` by rw[LE_MULT_LCANCEL] >>
  `(p - 1) * SIGMA (\j. p ** j) (natural (SUC n))
  = (p - 1) * SIGMA (\j. p ** j) ((SUC n) INSERT (natural n))` by rw[natural_suc] >>
  `_ = (p - 1) * (q + SIGMA (\j. p ** j) ((natural n) DELETE (SUC n)))` by rw[SUM_IMAGE_THM, Abbr`q`] >>
  `_ = (p - 1) * (q + SIGMA (\j. p ** j) (natural n))` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = (p - 1) * q + (p - 1) * SIGMA (\j. p ** j) (natural n)` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (p - 1) * q + p * (p ** n - 1)` by rw[] >>
  `_ = (p - 1) * q + (p * p ** n - p)` by rw[LEFT_SUB_DISTRIB] >>
  `_ = (p - 1) * q + (q - p)` by rw[EXP, Abbr`q`] >>
  `_ = (p * q - q) + (q - p)` by rw[RIGHT_SUB_DISTRIB] >>
  `_ = (p * q - q + q) - p` by rw[LESS_EQ_ADD_SUB] >>
  `_ = p * q - p` by rw[SUB_ADD] >>
  `_ = p * (q - 1)` by rw[LEFT_SUB_DISTRIB] >>
  rw[]);

(* Theorem: 1 < p ==> !n. SIGMA (\j. p ** j) (natural n) = (p * (p ** n - 1)) DIV (p - 1) *)
(* Proof:
   Since 1 < p,
     ==> 0 < p - 1, and 0 < p                          by arithmetic
   Let t = SIGMA (\j. p ** j) (natural n)
    With 0 < p,
         (p - 1) * t = p * (p ** n - 1)                by sigma_geometric_natural_eqn, 0 < p
   Hence           t = (p * (p ** n - 1)) DIV (p - 1)  by DIV_SOLVE, 0 < (p - 1)
*)
val sigma_geometric_natural = store_thm(
  "sigma_geometric_natural",
  ``!p. 1 < p ==> !n. SIGMA (\j. p ** j) (natural n) = (p * (p ** n - 1)) DIV (p - 1)``,
  rpt strip_tac >>
  `0 < p - 1 /\ 0 < p` by decide_tac >>
  rw[sigma_geometric_natural_eqn, DIV_SOLVE]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note:
   count m = {i | i < m}                  defined in pred_set
   residue m = {i | 0 < i /\ i < m}       defined in Euler
   The difference i = 0 gives n ** 0 = 1, which does not make a difference for PROD_SET.
*)

(* Theorem: 1 < n /\ 0 < m ==>
    (PROD_SET (IMAGE (\j. n ** j) (count m)) = PROD_SET (IMAGE (\j. n ** j) (residue m))) *)
(* Proof:
   Since 0 IN count m  by IN_COUNT, 0 < m
     and (IMAGE (\j. n ** j) (count m)) DELETE 1 = IMAGE (\j. n ** j) (residue m)
                                                            by IMAGE_DEF, EXP_EQ_1, EXP
     PROD_SET (IMAGE (\j. n ** j) (count m))
   = PROD_SET (IMAGE (\j. n ** j) (0 INSERT count m))       by ABSORPTION
   = PROD_SET ((\j. n ** j) 0 INSERT IMAGE (\j. n ** j) (count m))     by IMAGE_INSERT
   = n ** 0 * PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE n ** 0)  by PROD_SET_THM
   = PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE 1)     by EXP
   = PROD_SET ((IMAGE (\j. n ** j) (residue m)))            by above
*)
val PROD_SET_IMAGE_EXP_NONZERO = store_thm(
  "PROD_SET_IMAGE_EXP_NONZERO",
  ``!n m. 1 < n /\ 0 < m ==>
    (PROD_SET (IMAGE (\j. n ** j) (count m)) = PROD_SET (IMAGE (\j. n ** j) (residue m)))``,
  rpt strip_tac >>
  `0 IN count m` by rw[] >>
  `FINITE (IMAGE (\j. n ** j) (count m))` by rw[] >>
  `(IMAGE (\j. n ** j) (count m)) DELETE 1 = IMAGE (\j. n ** j) (residue m)` by
  (rw[residue_def, IMAGE_DEF, EXTENSION, EQ_IMP_THM] >-
  metis_tac[EXP, NOT_ZERO_LT_ZERO] >-
  metis_tac[] >>
  `j <> 0 /\ n <> 1` by decide_tac >>
  metis_tac[EXP_EQ_1]
  ) >>
  `PROD_SET (IMAGE (\j. n ** j) (count m)) = PROD_SET (IMAGE (\j. n ** j) (0 INSERT count m))` by metis_tac[ABSORPTION] >>
  `_ = PROD_SET ((\j. n ** j) 0 INSERT IMAGE (\j. n ** j) (count m))` by rw[] >>
  `_ = n ** 0 * PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE n ** 0)` by rw[PROD_SET_THM] >>
  `_ = PROD_SET ((IMAGE (\j. n ** j) (count m)) DELETE 1)` by rw[EXP] >>
  `_ = PROD_SET ((IMAGE (\j. n ** j) (residue m)))` by rw[] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
