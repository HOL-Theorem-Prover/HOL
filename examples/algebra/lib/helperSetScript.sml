(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Sets.             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperSet";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory;

(* val _ = load "helperNumTheory"; *)
open helperNumTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open arithmeticTheory dividesTheory;
open gcdTheory; (* for P_EUCLIDES *)


(* ------------------------------------------------------------------------- *)
(* HelperSet Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   countFrom m n        = IMAGE ($+ m) (count n)
   s =|= u # v          = split s u v
   EVERY_FINITE  P      = !s. s IN P ==> FINITE s
   PAIR_DISJOINT P      = !s t. s IN P /\ t IN P /\ ~(s = t) ==> DISJOINT s t
   SET_ADDITIVE f       = (f {} = 0) /\
                          (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) + f (s INTER t) = f s + f t))
   SET_MULTIPLICATIVE f = (f {} = 1) /\
                          (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) * f (s INTER t) = f s * f t))
   f PERMUTES s         = BIJ f s s
   PPOW s               = (POW s) DIFF {s}
*)
(* Definitions and Theorems (# are exported):

   Logic Theorems:
   EQ_IMP2_THM         |- !A B. (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> B ==> A)
   BOOL_EQ             |- !b1 b2 f. (b1 <=> b2) ==> (f b1 = f b2)
   IMP_IMP             |- !b c d. b /\ (c ==> d) ==> (b ==> c) ==> d
   AND_IMP_OR_NEG      |- !p q. p /\ q ==> p \/ ~q
   OR_IMP_IMP          |- !p q r. (p \/ q ==> r) ==> p /\ ~q ==> r
   PUSH_IN_INTO_IF     |- !b x s t. x IN (if b then s else t) <=> if b then x IN s else x IN t

   Set Theorems:
   IN_SUBSET           |- !s t. s SUBSET t <=> !x. x IN s ==> x IN t
   DISJOINT_DIFF       |- !s t. DISJOINT (s DIFF t) t /\ DISJOINT t (s DIFF t)
   DISJOINT_DIFF_IFF   |- !s t. DISJOINT s t <=> (s DIFF t = s)
   UNION_DIFF_EQ_UNION |- !s t. s UNION (t DIFF s) = s UNION t
   INTER_DIFF          |- !s t. (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {})
   SUBSET_SING         |- !s x. {x} SUBSET s /\ SING s <=> (s = {x})
   INTER_SING          |- !s x. x IN s ==> (s INTER {x} = {x})
   ONE_ELEMENT_SING    |- !s a. s <> {} /\ (!k. k IN s ==> (k = a)) ==> (s = {a})
   SING_ONE_ELEMENT    |- !s. s <> {} ==> (SING s <=> !x y. x IN s /\ y IN s ==> (x = y))
   SING_ELEMENT        |- !s. SING s ==> !x y. x IN s /\ y IN s ==> (x = y)
   SING_TEST           |- !s. SING s <=> s <> {} /\ !x y. x IN s /\ y IN s ==> (x = y)
   SING_INTER          |- !s x. {x} INTER s = if x IN s then {x} else {}
   IN_SING_OR_EMPTY    |- !b x y. x IN (if b then {y} else {}) ==> (x = y)
   SING_CARD_1         |- !s. SING s ==> (CARD s = 1)
   CARD_EQ_1           |- !s. FINITE s ==> ((CARD s = 1) <=> SING s)
   INSERT_DELETE_COMM  |- !s x y. x <> y ==> ((x INSERT s) DELETE y = x INSERT s DELETE y)
   INSERT_DELETE_NON_ELEMENT
                       |- !x s. x NOTIN s ==> (x INSERT s) DELETE x = s
   SUBSET_INTER_SUBSET |- !s t u. s SUBSET u ==> s INTER t SUBSET u
   DIFF_DIFF_EQ_INTER  |- !s t. s DIFF (s DIFF t) = s INTER t
   SET_EQ_BY_DIFF      |- !s t. (s = t) <=> s SUBSET t /\ (t DIFF s = {})
   SUBSET_INSERT_BOTH  |- !s1 s2 x. s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2
   INSERT_SUBSET_SUBSET|- !s t x. x NOTIN s /\ x INSERT s SUBSET t ==> s SUBSET t DELETE x
   DIFF_DELETE         |- !s t x. s DIFF t DELETE x = s DIFF (x INSERT t)
   SUBSET_DIFF_CARD    |- !a b. FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b)
   SUBSET_SING_IFF     |- !s x. s SUBSET {x} <=> (s = {}) \/ (s = {x})
   SUBSET_CARD_EQ      |- !s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)
   IMAGE_SUBSET_TARGET |- !f s t. (!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t
   SURJ_CARD_IMAGE     |- !f s t. SURJ f s t ==> CARD (IMAGE f s) = CARD t

   Image and Bijection:
   INJ_CONG            |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t)
   SURJ_CONG           |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t)
   BIJ_CONG            |- !f g s t. (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t)
   INJ_ELEMENT         |- !f s t x. INJ f s t /\ x IN s ==> f x IN t
   SURJ_ELEMENT        |- !f s t x. SURJ f s t /\ x IN s ==> f x IN t
   BIJ_ELEMENT         |- !f s t x. BIJ f s t /\ x IN s ==> f x IN t
   INJ_UNIV            |- !f s t. INJ f s t ==> INJ f s univ(:'b)
   INJ_SUBSET_UNIV     |- !f s. INJ f univ(:'a) univ(:'b) ==> INJ f s univ(:'b)
   INJ_IMAGE_BIJ_ALT   |- !f s. INJ f s univ(:'b) ==> BIJ f s (IMAGE f s)
   INJ_IMAGE_EQ        |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                ((IMAGE f s = IMAGE f t) <=> (s = t))
   INJ_IMAGE_INTER     |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                (IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t)
   INJ_IMAGE_DISJOINT  |- !P f. INJ f P univ(:'b) ==> !s t. s SUBSET P /\ t SUBSET P ==>
                                (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t))
   INJ_I               |- !s. INJ I s univ(:'a)
   INJ_I_IMAGE         |- !s f. INJ I (IMAGE f s) univ(:'b)
   BIJ_THM             |- !f s t. BIJ f s t <=>
                          (!x. x IN s ==> f x IN t) /\ !y. y IN t ==> ?!x. x IN s /\ (f x = y)
   BIJ_IS_INJ          |- !f s t. BIJ f s t ==>
                          !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)
   BIJ_IS_SURJ         |- !f s t. BIJ f s t ==> !x. x IN t ==> ?y. y IN s /\ f y = x
   BIJ_FINITE_IFF      |- !f s t. BIJ f s t ==> (FINITE s <=> FINITE t)
   INJ_EQ_11           |- !f s x y. INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y))
   INJ_IMP_11          |- !f. INJ f univ(:'a) univ(:'b) ==> !x y. f x = f y <=> x = y
   BIJ_I_SAME          |- !s. BIJ I s s
   IMAGE_K             |- !s. s <> {} ==> !e. IMAGE (K e) s = {e}
   IMAGE_ELEMENT_CONDITION  |- !f. (!x y. (f x = f y) ==> (x = y)) ==> !s e. e IN s <=> f e IN IMAGE f s
   BIGUNION_ELEMENTS_SING   |- !s. BIGUNION (IMAGE (\x. {x}) s) = s
   IMAGE_DIFF          |- !s t f. s SUBSET t /\ INJ f t univ(:'b) ==>
                                  (IMAGE f (t DIFF s) = IMAGE f t DIFF IMAGE f s)

   More Theorems and Sets for Counting:
   COUNT_0             |- count 0 = {}
   COUNT_1             |- count 1 = {0}
   COUNT_NOT_SELF      |- !n. n NOTIN count n
   COUNT_EQ_EMPTY      |- !n. (count n = {}) <=> (n = 0)
   COUNT_SUBSET        |- !m n. m <= n ==> count m SUBSET count n
   COUNT_SUC_SUBSET    |- !n t. count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t
   DIFF_COUNT_SUC      |- !n t. t DIFF count (SUC n) = t DIFF count n DELETE n
   COUNT_SUC_BY_SUC    |- !n. count (SUC n) = 0 INSERT IMAGE SUC (count n)
   IMAGE_COUNT_SUC     |- !f n. IMAGE f (count (SUC n)) = f n INSERT IMAGE f (count n)
   IMAGE_COUNT_SUC_BY_SUC
                       |- !f n. IMAGE f (count (SUC n)) = f 0 INSERT IMAGE (f o SUC) (count n)
   countFrom_0         |- !m. countFrom m 0 = {}
   countFrom_SUC       |- !m n m n. countFrom m (SUC n) = m INSERT countFrom (m + 1) n
   countFrom_first     |- !m n. 0 < n ==> m IN countFrom m n
   countFrom_less      |- !m n x. x < m ==> x NOTIN countFrom m n
   count_by_countFrom     |- !n. count n = countFrom 0 n
   count_SUC_by_countFrom |- !n. count (SUC n) = 0 INSERT countFrom 1 n

   CARD_UNION_3_EQN    |- !a b c. FINITE a /\ FINITE b /\ FINITE c ==>
                                  (CARD (a UNION b UNION c) =
                                   CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
                                   CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c))
   CARD_UNION_3_DISJOINT
                       |- !a b c. FINITE a /\ FINITE b /\ FINITE c /\
                                  DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
                                  (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c)

   Maximum and Minimum of a Set:
   MAX_SET_LESS        |- !s n. FINITE s /\ MAX_SET s < n ==> !x. x IN s ==> x < n
   MAX_SET_TEST        |- !s. FINITE s /\ s <> {} ==>
                          !x. x IN s /\ (!y. y IN s ==> y <= x) ==> (x = MAX_SET s)
   MIN_SET_TEST        |- !s. s <> {} ==>
                          !x. x IN s /\ (!y. y IN s ==> x <= y) ==> (x = MIN_SET s)
   MAX_SET_TEST_IFF    |- !s. FINITE s /\ s <> {} ==> !x. x IN s ==>
                              ((MAX_SET s = x) <=> !y. y IN s ==> y <= x)
   MIN_SET_TEST_IFF    |- !s. s <> {} ==> !x. x IN s ==>
                              ((MIN_SET s = x) <=> !y. y IN s ==> x <= y)
   MAX_SET_EMPTY       |- MAX_SET {} = 0
   MAX_SET_SING        |- !e. MAX_SET {e} = e
   MAX_SET_IN_SET      |- !s. FINITE s /\ s <> {} ==> MAX_SET s IN s
   MAX_SET_PROPERTY    |- !s. FINITE s ==> !x. x IN s ==> x <= MAX_SET s
   MIN_SET_SING        |- !e. MIN_SET {e} = e
   MIN_SET_IN_SET      |- !s. s <> {} ==> MIN_SET s IN s
   MIN_SET_PROPERTY    |- !s. s <> {} ==> !x. x IN s ==> MIN_SET s <= x
   MAX_SET_DELETE      |- !s. FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==>
                              (MAX_SET (s DELETE MIN_SET s) = MAX_SET s)
   MAX_SET_EQ_0        |- !s. FINITE s ==> ((MAX_SET s = 0) <=> (s = {}) \/ (s = {0}))
   MIN_SET_EQ_0        |- !s. s <> {} ==> ((MIN_SET s = 0) <=> 0 IN s)
   MAX_SET_IMAGE_SUC_COUNT  |- !n. MAX_SET (IMAGE SUC (count n)) = n
   MAX_SET_IMAGE_with_HALF  |- !f c x. HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c}
   MAX_SET_IMAGE_with_DIV   |- !f b c x. 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c}
   MAX_SET_IMAGE_with_DEC   |- !f b c x. x - b <= c ==> f x <= MAX_SET {f x | x - b <= c}

   Finite and Cardinality Theorems:
   INJ_CARD_IMAGE_EQN  |- !f s. INJ f s univ(:'b) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
   FINITE_INJ_AS_SURJ  |- !f s t. INJ f s t /\ FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> SURJ f s t
   FINITE_INJ_IS_SURJ  |- !f s t. FINITE s /\ FINITE t /\
                                  CARD s = CARD t /\ INJ f s t ==> SURJ f s t
   FINITE_INJ_IS_BIJ   |- !f s t. FINITE s /\ FINITE t /\
                                  CARD s = CARD t /\ INJ f s t ==> BIJ f s t
   FINITE_COUNT_IMAGE  |- !P n. FINITE {P x | x < n}
   FINITE_BIJ_PROPERTY |- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)
   FINITE_CARD_IMAGE   |- !s f. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
   CARD_IMAGE_SUC      |- !s. FINITE s ==> (CARD (IMAGE SUC s) = CARD s)
   CARD_UNION_DISJOINT |- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)
   FINITE_BIJ_COUNT_CARD    |- !s. FINITE s ==> ?f. BIJ f (count (CARD s)) s
   image_mod_subset_count   |- !s n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET count n
   card_mod_image           |- !s n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n
   card_mod_image_nonzero   |- !s n. 0 < n /\ 0 NOTIN IMAGE (\x. x MOD n) s ==>
                                               CARD (IMAGE (\x. x MOD n) s) < n

   Partition Property:
   finite_partition_property      |- !s. FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s))
   finite_partition_by_predicate  |- !s. FINITE s ==> !P. (let u = {x | x IN s /\ P x} in
                                           let v = {x | x IN s /\ ~P x} in
                                           FINITE u /\ FINITE v /\ s =|= u # v)
   partition_by_subset    |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v)
   partition_by_element   |- !s x. x IN s ==> s =|= {x} # s DELETE x

   Splitting of a set:
   SPLIT_EMPTY       |- !s t. s =|= {} # t <=> s = t
   SPLIT_UNION       |- !s u v a b. s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a
   SPLIT_EQ          |- !s u v. s =|= u # v <=> u SUBSET s /\ v = s DIFF u
   SPLIT_SYM         |- !s u v. s =|= u # v <=> s =|= v # u
   SPLIT_SYM_IMP     |- !s u v. s =|= u # v ==> s =|= v # u
   SPLIT_SING        |- !s v x. s =|= {x} # v <=> x IN s /\ v = s DELETE x
   SPLIT_SUBSETS     |- !s u v. s =|= u # v ==> u SUBSET s /\ v SUBSET s
   SPLIT_FINITE      |- !s u v. FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v
   SPLIT_CARD        |- !s u v. FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v)
   SPLIT_EQ_DIFF     |- !s u v. s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u)
   SPLIT_BY_SUBSET   |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v)
   SUBSET_DIFF_DIFF  |- !s t. t SUBSET s ==> (s DIFF (s DIFF t) = t)
   SUBSET_DIFF_EQ    |- !s1 s2 t. s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2)

   Bijective Inverses:
   BIJ_LINV_ELEMENT  |- !f s t. BIJ f s t ==> !x. x IN t ==> LINV f s x IN s
   BIJ_LINV_THM      |- !f s t. BIJ f s t ==>
                                (!x. x IN s ==> (LINV f s (f x) = x)) /\ !x. x IN t ==> (f (LINV f s x) = x)
   BIJ_RINV_INV      |- !f s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
                                             !x. x IN s ==> (RINV f s (f x) = x)
   BIJ_RINV_BIJ      |- !f s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s
   LINV_SUBSET       |- !f s t. INJ f t univ(:'b) /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x)

   Iteration, Summation and Product:
   ITSET_SING           |- !f x b. ITSET f {x} b = f x b
   ITSET_PROPERTY       |- !s f b. FINITE s /\ s <> {} ==>
                                   (ITSET f s b = ITSET f (REST s) (f (CHOICE s) b))
   ITSET_CONG           |- !f g. (f = g) ==> (ITSET f = ITSET g)
   ITSET_REDUCTION      |- !f. (!x y z. f x (f y z) = f y (f x z)) ==>
                           !s x b. FINITE s /\ x NOTIN s ==> (ITSET f (x INSERT s) b = f x (ITSET f s b))

   Rework of ITSET Theorems:
   closure_comm_assoc_fun_def        |- !f s. closure_comm_assoc_fun f s <=>
                                        (!x y. x IN s /\ y IN s ==> f x y IN s) /\
                                         !x y z. x IN s /\ y IN s /\ z IN s ==> (f x (f y z) = f y (f x z))
   SUBSET_COMMUTING_ITSET_INSERT     |- !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
                                        !x b::t. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)
   SUBSET_COMMUTING_ITSET_REDUCTION  |- !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
                                        !x b::t. ITSET f s (f x b) = f x (ITSET f s b)
   SUBSET_COMMUTING_ITSET_RECURSES   |- !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
                                        !x b::t. ITSET f (x INSERT s) b = f x (ITSET f (s DELETE x) b)

   SUM_IMAGE and PROD_IMAGE Theorems:
   SUM_IMAGE_EMPTY      |- !f. SIGMA f {} = 0
   SUM_IMAGE_INSERT     |- !f s. FINITE s ==> !e. e NOTIN s ==> (SIGMA f (e INSERT s) = f e + SIGMA f s)
   SUM_IMAGE_AS_SUM_SET |- !s. FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==>
                               (SIGMA f s = SUM_SET (IMAGE f s))
   SUM_IMAGE_DOUBLET    |- !f x y. x <> y ==> SIGMA f {x; y} = f x + f y
   SUM_IMAGE_TRIPLET    |- !f x y z. x <> y /\ y <> z /\ z <> x ==> SIGMA f {x; y; z} = f x + f y + f z
   SIGMA_CONSTANT       |- !s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s)
   SUM_IMAGE_CONSTANT   |- !s. FINITE s ==> !c. SIGMA (K c) s = c * CARD s
   SIGMA_CARD_CONSTANT  |- !n s. FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s
   SIGMA_CARD_SAME_SIZE_SETS
                        |- !n s. FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s
   SIGMA_CARD_FACTOR    |- !n s. FINITE s /\ (!e. e IN s ==> n divides CARD e) ==> n divides SIGMA CARD s
   SIGMA_CONG           |- !s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (SIGMA f1 s = SIGMA f2 s)
   CARD_AS_SIGMA        |- !s. FINITE s ==> (CARD s = SIGMA (\x. 1) s)
   CARD_EQ_SIGMA        |- !s. FINITE s ==> (CARD s = SIGMA (K 1) s)
   SIGMA_LE_SIGMA       |- !s. FINITE s ==> !f g. (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s
   SUM_IMAGE_UNION_EQN  |- !s t. FINITE s /\ FINITE t ==>
                           !f. SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t
   SUM_IMAGE_DISJOINT   |- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==>
                           !f. SIGMA f (s UNION t) = SIGMA f s + SIGMA f t
   SUM_IMAGE_MONO_LT    |- !s. FINITE s /\ s <> {} ==>
                           !f g. (!x. x IN s ==> f x < g x) ==> SIGMA f s < SIGMA g s
   SUM_IMAGE_PSUBSET_LT |- !f s t. FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==>
                                   SIGMA f t < SIGMA f s
   card_le_sigma_card   |- !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) ==>
                               CARD s <= SIGMA CARD s
   card_eq_sigma_card   |- !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) /\
                               CARD s = SIGMA CARD s ==> !e. e IN s ==> CARD e = 1

   PROD_IMAGE_EMPTY     |- !f. PI f {} = 1
   PROD_IMAGE_INSERT    |- !s. FINITE s ==> !f e. e NOTIN s ==> (PI f (e INSERT s) = f e * PI f s)
   PROD_IMAGE_DELETE    |- !s. FINITE s ==> !f e. 0 < f e ==>
                               (PI f (s DELETE e) = if e IN s then PI f s DIV f e else PI f s)
   PROD_IMAGE_CONG      |- !s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)
   PI_CONSTANT          |- !s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s)
   PROD_IMAGE_CONSTANT  |- !s. FINITE s ==> !c. PI (K c) s = c ** CARD s

   SUM_SET and PROD_SET Theorems:
   SUM_SET_INSERT       |- !s x. FINITE s /\ x NOTIN s ==> (SUM_SET (x INSERT s) = x + SUM_SET s)
   SUM_SET_IMAGE_EQN    |- !s. FINITE s ==> !f. INJ f s univ(:num) ==> (SUM_SET (IMAGE f s) = SIGMA f s)
   SUM_SET_COUNT        |- !n. SUM_SET (count n) = n * (n - 1) DIV 2

   PROD_SET_SING        |- !x. PROD_SET {x} = x
   PROD_SET_NONZERO     |- !s. FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s
   PROD_SET_LESS        |- !s. FINITE s /\ s <> {} /\ 0 NOTIN s ==>
                           !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)
   PROD_SET_LESS_SUC    |- !s. FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s)
   PROD_SET_DIVISORS    |- !s. FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s)
   PROD_SET_INSERT      |- !x s. FINITE s /\ x NOTIN s ==> (PROD_SET (x INSERT s) = x * PROD_SET s)
   PROD_SET_IMAGE_EQN   |- !s. FINITE s ==> !f. INJ f s univ(:num) ==> (PROD_SET (IMAGE f s) = PI f s)
   PROD_SET_IMAGE_EXP   |- !n. 1 < n ==> !m. PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** SUM_SET (count m)
   PROD_SET_ELEMENT_DIVIDES     |- !s x. FINITE s /\ x IN s ==> x divides PROD_SET s
   PROD_SET_LESS_EQ             |- !s. FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
                                       (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)
   PROD_SET_LE_CONSTANT         |- !s. FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s
   PROD_SET_PRODUCT_GE_CONSTANT |- !s. FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
                                       (!x. x IN s ==> n <= f x * g x) ==>
                                       n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)
   PROD_SET_PRODUCT_BY_PARTITION |- !s. FINITE s ==>
                                    !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v)

   Partition and Equivalent Class:
   equiv_class_element    |- !R s x y. y IN equiv_class R s x <=> y IN s /\ R x y
   partition_on_empty     |- !R. partition R {} = {}
   partition_element      |- !R s t. t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x)
   partition_elements     |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s
   partition_as_image     |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s
   partition_cong         |- !R1 R2 s1 s2. (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2)
   partition_element_not_empty
                          |- !R s e. R equiv_on s /\ e IN partition R s ==> e <> {}
   equiv_class_not_empty  |- !R s x. R equiv_on s /\ x IN s ==> equiv_class R s x <> {}
   partition_element_exists
                          |- !R s x. R equiv_on s ==> (x IN s <=> ?e. e IN partition R s /\ x IN e)
   equal_partition_card   |- !R s n. FINITE s /\ R equiv_on s /\
                             (!e. e IN partition R s ==> (CARD e = n)) ==> (CARD s = n * CARD (partition R s))
   equal_partition_factor |- !R s n. FINITE s /\ R equiv_on s /\
                             (!e. e IN partition R s ==> CARD e = n) ==> n divides CARD s
   factor_partition_card  |- !R s n. FINITE s /\ R equiv_on s /\
                             (!e. e IN partition R s ==> n divides CARD e) ==> n divides CARD s

   pair_disjoint_subset        |- !s t. t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t
   disjoint_bigunion_add_fun   |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)
   set_additive_card           |- SET_ADDITIVE CARD
   disjoint_bigunion_card      |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  (CARD (BIGUNION P) = SIGMA CARD P)
   CARD_BIGUNION_PAIR_DISJOINT |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                      CARD (BIGUNION P) = SIGMA CARD P
   set_additive_sigma          |- !f. SET_ADDITIVE (SIGMA f)
   disjoint_bigunion_sigma     |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P
   set_add_fun_by_partition    |- !R s. R equiv_on s /\ FINITE s ==>
                                  !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s))
   set_card_by_partition       |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
   set_sigma_by_partition      |- !R s. R equiv_on s /\ FINITE s ==>
                                  !f. SIGMA f s = SIGMA (SIGMA f) (partition R s)
   disjoint_bigunion_mult_fun  |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
                                  !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)
   set_mult_fun_by_partition   |- !R s. R equiv_on s /\ FINITE s ==>
                                  !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s))
   sum_image_by_composition    |- !s. FINITE s ==> !g. INJ g s univ(:'a) ==>
                                  !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s
   sum_image_by_permutation    |- !s. FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s
   sum_image_by_composition_with_partial_inj
                               |- !s. FINITE s ==> !f. (f {} = 0) ==>
                     !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:'b -> bool)) ==>
                                    (SIGMA f (IMAGE g s) = SIGMA (f o g) s)
   sum_image_by_composition_without_inj
                               |- !s. FINITE s ==>
                         !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
                                    (SIGMA f (IMAGE g s) = SIGMA (f o g) s)

   Pre-image Theorems:
   preimage_def               |- !f s y. preimage f s y = {x | x IN s /\ (f x = y)}
   preimage_element           |- !f s x y. x IN preimage f s y <=> x IN s /\ (f x = y)
   in_preimage                |- !f s x y. x IN preimage f s y <=> x IN s /\ (f x = y)
   preimage_subset            |- !f s y. preimage f s y SUBSET s
   preimage_finite            |- !f s y. FINITE s ==> FINITE (preimage f s y)
   preimage_property          |- !f s y x. x IN preimage f s y ==> (f x = y)
   preimage_of_image          |- !f s x. x IN s ==> x IN preimage f s (f x)
   preimage_choice_property   |- !f s y. y IN IMAGE f s ==>
                                 CHOICE (preimage f s y) IN s /\ (f (CHOICE (preimage f s y)) = y)
   preimage_inj               |- !f s. INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x})
   preimage_inj_choice        |- !f s. INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x)
   preimage_image_inj         |- !f s. INJ (preimage f s) (IMAGE f s) (POW s)

   Set of Proper Subsets:
   IN_PPOW         |- !s e. e IN PPOW s ==> e PSUBSET s
   FINITE_PPOW     |- !s. FINITE s ==> FINITE (PPOW s)
   CARD_PPOW       |- !s. FINITE s ==> (CARD (PPOW s) = PRE (2 ** CARD s)
   CARD_PPOW_EQN   |- !s. FINITE s ==> (CARD (PPOW s) = 2 ** CARD s - 1)

   Useful Theorems:
   in_prime        |- !p. p IN prime <=> prime p
   PROD_SET_EUCLID |- !s. FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b

*)

(* ------------------------------------------------------------------------- *)
(* Logic Theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> (B ==> A)) *)
(* Proof: by logic. *)
val EQ_IMP2_THM = store_thm(
  "EQ_IMP2_THM",
  ``!A B. (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> (B ==> A))``,
  metis_tac[]);

(* Theorem: (b1 = b2) ==> (f b1 = f b2) *)
(* Proof: by substitution. *)
val BOOL_EQ = store_thm(
  "BOOL_EQ",
  ``!b1:bool b2:bool f. (b1 = b2) ==> (f b1 = f b2)``,
  simp[]);

(* Theorem: b /\ (c ==> d) ==> ((b ==> c) ==> d) *)
(* Proof: by logical implication. *)
val IMP_IMP = store_thm(
  "IMP_IMP",
  ``!b c d. b /\ (c ==> d) ==> ((b ==> c) ==> d)``,
  metis_tac[]);

(* Theorem: p /\ q ==> p \/ ~q *)
(* Proof:
   Note p /\ q ==> p          by AND1_THM
    and p ==> p \/ ~q         by OR_INTRO_THM1
   Thus p /\ q ==> p \/ ~q
*)
val AND_IMP_OR_NEG = store_thm(
  "AND_IMP_OR_NEG",
  ``!p q. p /\ q ==> p \/ ~q``,
  metis_tac[]);

(* Theorem: (p \/ q ==> r) ==> (p /\ ~q ==> r) *)
(* Proof:
       (p \/ q) ==> r
     = ~(p \/ q) \/ r      by IMP_DISJ_THM
     = (~p /\ ~q) \/ r     by DE_MORGAN_THM
   ==> (~p \/ q) \/ r      by AND_IMP_OR_NEG
     = ~(p /\ ~q) \/ r     by DE_MORGAN_THM
     = (p /\ ~q) ==> r     by IMP_DISJ_THM
*)
val OR_IMP_IMP = store_thm(
  "OR_IMP_IMP",
  ``!p q r. ((p \/ q) ==> r) ==> ((p /\ ~q) ==> r)``,
  metis_tac[]);

(* Theorem: x IN (if b then s else t) <=> if b then x IN s else x IN t *)
(* Proof: by boolTheory.COND_RAND:
   |- !f b x y. f (if b then x else y) = if b then f x else f y
*)
val PUSH_IN_INTO_IF = store_thm(
  "PUSH_IN_INTO_IF",
  ``!b x s t. x IN (if b then s else t) <=> if b then x IN s else x IN t``,
  rw_tac std_ss[]);

(* ------------------------------------------------------------------------- *)
(* Set Theorems.                                                             *)
(* ------------------------------------------------------------------------- *)

(* use of IN_SUBSET *)
val IN_SUBSET = save_thm("IN_SUBSET", SUBSET_DEF);
(*
val IN_SUBSET = |- !s t. s SUBSET t <=> !x. x IN s ==> x IN t: thm
*)

(* Theorem: DISJOINT (s DIFF t) t /\ DISJOINT t (s DIFF t) *)
(* Proof:
       DISJOINT (s DIFF t) t
   <=> (s DIFF t) INTER t = {}              by DISJOINT_DEF
   <=> !x. x IN (s DIFF t) INTER t <=> F    by MEMBER_NOT_EMPTY
       x IN (s DIFF t) INTER t
   <=> x IN (s DIFF t) /\ x IN t            by IN_INTER
   <=> (x IN s /\ x NOTIN t) /\ x IN t      by IN_DIFF
   <=> x IN s /\ (x NOTIN t /\ x IN t)
   <=> x IN s /\ F
   <=> F
   Similarly for DISJOINT t (s DIFF t)
*)
val DISJOINT_DIFF = store_thm(
  "DISJOINT_DIFF",
  ``!s t. (DISJOINT (s DIFF t) t) /\ (DISJOINT t (s DIFF t))``,
  (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[]));

(* Theorem: DISJOINT s t <=> ((s DIFF t) = s) *)
(* Proof: by DISJOINT_DEF, DIFF_DEF, EXTENSION *)
val DISJOINT_DIFF_IFF = store_thm(
  "DISJOINT_DIFF_IFF",
  ``!s t. DISJOINT s t <=> ((s DIFF t) = s)``,
  rw[DISJOINT_DEF, DIFF_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: s UNION (t DIFF s) = s UNION t *)
(* Proof:
   By EXTENSION,
     x IN (s UNION (t DIFF s))
   = x IN s \/ x IN (t DIFF s)                    by IN_UNION
   = x IN s \/ (x IN t /\ x NOTIN s)              by IN_DIFF
   = (x IN s \/ x IN t) /\ (x IN s \/ x NOTIN s)  by LEFT_OR_OVER_AND
   = (x IN s \/ x IN t) /\ T                      by EXCLUDED_MIDDLE
   = x IN (s UNION t)                             by IN_UNION
*)
val UNION_DIFF_EQ_UNION = store_thm(
  "UNION_DIFF_EQ_UNION",
  ``!s t. s UNION (t DIFF s) = s UNION t``,
  rw_tac std_ss[EXTENSION, IN_UNION, IN_DIFF] >>
  metis_tac[]);

(* Theorem: (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {}) *)
(* Proof: by DISJOINT_DIFF, GSYM DISJOINT_DEF *)
val INTER_DIFF = store_thm(
  "INTER_DIFF",
  ``!s t. (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {})``,
  rw[DISJOINT_DIFF, GSYM DISJOINT_DEF]);

(* Theorem: {x} SUBSET s /\ SING s <=> (s = {x}) *)
(* Proof:
   Note {x} SUBSET s ==> x IN s           by SUBSET_DEF
    and SING s ==> ?y. s = {y}            by SING_DEF
   Thus x IN {y} ==> x = y                by IN_SING
*)
val SUBSET_SING = store_thm(
  "SUBSET_SING",
  ``!s x. {x} SUBSET s /\ SING s <=> (s = {x})``,
  metis_tac[SING_DEF, IN_SING, SUBSET_DEF]);

(* Theorem: !x. x IN s ==> s INTER {x} = {x} *)
(* Proof:
     s INTER {x}
   = {x | x IN s /\ x IN {x}}   by INTER_DEF
   = {x' | x' IN s /\ x' = x}   by IN_SING
   = {x}                        by EXTENSION
*)
val INTER_SING = store_thm(
  "INTER_SING",
  ``!s x. x IN s ==> (s INTER {x} = {x})``,
  rw[INTER_DEF, EXTENSION, EQ_IMP_THM]);

(* Theorem: A non-empty set with all elements equal to a is the singleton {a} *)
(* Proof: by singleton definition. *)
val ONE_ELEMENT_SING = store_thm(
  "ONE_ELEMENT_SING",
  ``!s a. s <> {} /\ (!k. k IN s ==> (k = a)) ==> (s = {a})``,
  rw[EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: s <> {} ==> (SING s <=> !x y. x IN s /\ y IN s ==> (x = y)) *)
(* Proof:
   If part: SING s ==> !x y. x IN s /\ y IN s ==> (x = y))
      SING s ==> ?t. s = {t}    by SING_DEF
      x IN s ==> x = t          by IN_SING
      y IN s ==> y = t          by IN_SING
      Hence x = y
   Only-if part: !x y. x IN s /\ y IN s ==> (x = y)) ==> SING s
     True by ONE_ELEMENT_SING
*)
val SING_ONE_ELEMENT = store_thm(
  "SING_ONE_ELEMENT",
  ``!s. s <> {} ==> (SING s <=> !x y. x IN s /\ y IN s ==> (x = y))``,
  metis_tac[SING_DEF, IN_SING, ONE_ELEMENT_SING]);

(* Theorem: SING s ==> (!x y. x IN s /\ y IN s ==> (x = y)) *)
(* Proof:
   Note SING s <=> ?z. s = {z}       by SING_DEF
    and x IN {z} <=> x = z           by IN_SING
    and y IN {z} <=> y = z           by IN_SING
   Thus x = y
*)
val SING_ELEMENT = store_thm(
  "SING_ELEMENT",
  ``!s. SING s ==> (!x y. x IN s /\ y IN s ==> (x = y))``,
  metis_tac[SING_DEF, IN_SING]);
(* Note: the converse really needs s <> {} *)

(* Theorem: SING s <=> s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y)) *)
(* Proof:
   If part: SING s ==> s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y))
      True by SING_EMPTY, SING_ELEMENT.
   Only-if part:  s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y)) ==> SING s
      True by SING_ONE_ELEMENT.
*)
val SING_TEST = store_thm(
  "SING_TEST",
  ``!s. SING s <=> s <> {} /\ (!x y. x IN s /\ y IN s ==> (x = y))``,
  metis_tac[SING_EMPTY, SING_ELEMENT, SING_ONE_ELEMENT]);

(* Theorem: x IN (if b then {y} else {}) ==> (x = y) *)
(* Proof: by IN_SING, MEMBER_NOT_EMPTY *)
val IN_SING_OR_EMPTY = store_thm(
  "IN_SING_OR_EMPTY",
  ``!b x y. x IN (if b then {y} else {}) ==> (x = y)``,
  rw[]);

(* Theorem: {x} INTER s = if x IN s then {x} else {} *)
(* Proof: by EXTENSION *)
val SING_INTER = store_thm(
  "SING_INTER",
  ``!s x. {x} INTER s = if x IN s then {x} else {}``,
  rw[EXTENSION] >>
  metis_tac[]);

(* Theorem: SING s ==> (CARD s = 1) *)
(* Proof:
   Note s = {x} for some x   by SING_DEF
     so CARD s = 1           by CARD_SING
*)
Theorem SING_CARD_1:
  !s. SING s ==> (CARD s = 1)
Proof
  metis_tac[SING_DEF, CARD_SING]
QED

(* Note: SING s <=> (CARD s = 1) cannot be proved.
Only SING_IFF_CARD1  |- !s. SING s <=> (CARD s = 1) /\ FINITE s
That is: FINITE s /\ (CARD s = 1) ==> SING s
*)

(* Theorem: FINITE s ==> ((CARD s = 1) <=> SING s) *)
(* Proof:
   If part: CARD s = 1 ==> SING s
      Since CARD s = 1
        ==> s <> {}        by CARD_EMPTY
        ==> ?x. x IN s     by MEMBER_NOT_EMPTY
      Claim: !y . y IN s ==> y = x
      Proof: By contradiction, suppose y <> x.
             Then y NOTIN {x}             by EXTENSION
               so CARD {y; x} = 2         by CARD_DEF
              and {y; x} SUBSET s         by SUBSET_DEF
             thus CARD {y; x} <= CARD s   by CARD_SUBSET
             This contradicts CARD s = 1.
      Hence SING s         by SING_ONE_ELEMENT (or EXTENSION, SING_DEF)
      Or,
      With x IN s, {x} SUBSET s         by SUBSET_DEF
      If s <> {x}, then {x} PSUBSET s   by PSUBSET_DEF
      so CARD {x} < CARD s              by CARD_PSUBSET
      But CARD {x} = 1                  by CARD_SING
      and this contradicts CARD s = 1.

   Only-if part: SING s ==> CARD s = 1
      Since SING s
        <=> ?x. s = {x}    by SING_DEF
        ==> CARD {x} = 1   by CARD_SING
*)
val CARD_EQ_1 = store_thm(
  "CARD_EQ_1",
  ``!s. FINITE s ==> ((CARD s = 1) <=> SING s)``,
  rw[SING_DEF, EQ_IMP_THM] >| [
    `1 <> 0` by decide_tac >>
    `s <> {} /\ ?x. x IN s` by metis_tac[CARD_EMPTY, MEMBER_NOT_EMPTY] >>
    qexists_tac `x` >>
    spose_not_then strip_assume_tac >>
    `{x} PSUBSET s` by rw[PSUBSET_DEF] >>
    `CARD {x} < CARD s` by rw[CARD_PSUBSET] >>
    `CARD {x} = 1` by rw[CARD_SING] >>
    decide_tac,
    rw[CARD_SING]
  ]);

(* Theorem: x <> y ==> ((x INSERT s) DELETE y = x INSERT (s DELETE y)) *)
(* Proof:
       z IN (x INSERT s) DELETE y
   <=> z IN (x INSERT s) /\ z <> y                by IN_DELETE
   <=> (z = x \/ z IN s) /\ z <> y                by IN_INSERT
   <=> (z = x /\ z <> y) \/ (z IN s /\ z <> y)    by RIGHT_AND_OVER_OR
   <=> (z = x) \/ (z IN s /\ z <> y)              by x <> y
   <=> (z = x) \/ (z IN DELETE y)                 by IN_DELETE
   <=> z IN  x INSERT (s DELETE y)                by IN_INSERT
*)
val INSERT_DELETE_COMM = store_thm(
  "INSERT_DELETE_COMM",
  ``!s x y. x <> y ==> ((x INSERT s) DELETE y = x INSERT (s DELETE y))``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: x NOTIN s ==> (x INSERT s) DELETE x = s *)
(* Proof:
    (x INSERT s) DELETE x
   = s DELETE x         by DELETE_INSERT
   = s                  by DELETE_NON_ELEMENT
*)
Theorem INSERT_DELETE_NON_ELEMENT:
  !x s. x NOTIN s ==> (x INSERT s) DELETE x = s
Proof
  simp[DELETE_INSERT, DELETE_NON_ELEMENT]
QED

(* Theorem: s SUBSET u ==> (s INTER t) SUBSET u *)
(* Proof:
   Note (s INTER t) SUBSET s     by INTER_SUBSET
    ==> (s INTER t) SUBSET u     by SUBSET_TRANS
*)
val SUBSET_INTER_SUBSET = store_thm(
  "SUBSET_INTER_SUBSET",
  ``!s t u. s SUBSET u ==> (s INTER t) SUBSET u``,
  metis_tac[INTER_SUBSET, SUBSET_TRANS]);

(* Theorem: s DIFF (s DIFF t) = s INTER t *)
(* Proof: by IN_DIFF, IN_INTER *)
val DIFF_DIFF_EQ_INTER = store_thm(
  "DIFF_DIFF_EQ_INTER",
  ``!s t. s DIFF (s DIFF t) = s INTER t``,
  rw[EXTENSION] >>
  metis_tac[]);

(* Theorem: (s = t) <=> (s SUBSET t /\ (t DIFF s = {})) *)
(* Proof:
       s = t
   <=> s SUBSET t /\ t SUBSET s       by SET_EQ_SUBSET
   <=> s SUBSET t /\ (t DIFF s = {})  by SUBSET_DIFF_EMPTY
*)
val SET_EQ_BY_DIFF = store_thm(
  "SET_EQ_BY_DIFF",
  ``!s t. (s = t) <=> (s SUBSET t /\ (t DIFF s = {}))``,
  rw[SET_EQ_SUBSET, SUBSET_DIFF_EMPTY]);

(* in pred_setTheory:
SUBSET_DELETE_BOTH |- !s1 s2 x. s1 SUBSET s2 ==> s1 DELETE x SUBSET s2 DELETE x
*)

(* Theorem: s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2 *)
(* Proof: by SUBSET_DEF *)
Theorem SUBSET_INSERT_BOTH:
  !s1 s2 x. s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2
Proof
  simp[SUBSET_DEF]
QED

(* Theorem: x NOTIN s /\ (x INSERT s) SUBSET t ==> s SUBSET (t DELETE x) *)
(* Proof: by SUBSET_DEF *)
val INSERT_SUBSET_SUBSET = store_thm(
  "INSERT_SUBSET_SUBSET",
  ``!s t x. x NOTIN s /\ (x INSERT s) SUBSET t ==> s SUBSET (t DELETE x)``,
  rw[SUBSET_DEF]);

(* DIFF_INSERT  |- !s t x. s DIFF (x INSERT t) = s DELETE x DIFF t *)

(* Theorem: (s DIFF t) DELETE x = s DIFF (x INSERT t) *)
(* Proof: by EXTENSION *)
val DIFF_DELETE = store_thm(
  "DIFF_DELETE",
  ``!s t x. (s DIFF t) DELETE x = s DIFF (x INSERT t)``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b) *)
(* Proof:
   Note FINITE b                   by SUBSET_FINITE
     so a INTER b = b              by SUBSET_INTER2
        CARD (a DIFF b)
      = CARD a - CARD (a INTER b)  by CARD_DIFF
      = CARD a - CARD b            by above
*)
Theorem SUBSET_DIFF_CARD:
  !a b. FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b)
Proof
  metis_tac[CARD_DIFF, SUBSET_FINITE, SUBSET_INTER2]
QED

(* Theorem: s SUBSET {x} <=> ((s = {}) \/ (s = {x})) *)
(* Proof:
   Note !y. y IN s ==> y = x   by SUBSET_DEF, IN_SING
   If s = {}, then trivially true.
   If s <> {},
     then ?y. y IN s           by MEMBER_NOT_EMPTY, s <> {}
       so y = x                by above
      ==> s = {x}              by EXTENSION
*)
Theorem SUBSET_SING_IFF:
  !s x. s SUBSET {x} <=> ((s = {}) \/ (s = {x}))
Proof
  rw[SUBSET_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t) *)
(* Proof:
   If part: CARD s = CARD t ==> s = t
      By contradiction, suppose s <> t.
      Then s PSUBSET t         by PSUBSET_DEF
        so CARD s < CARD t     by CARD_PSUBSET, FINITE t
      This contradicts CARD s = CARD t.
   Only-if part is trivial.
*)
Theorem SUBSET_CARD_EQ:
  !s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `s PSUBSET t` by rw[PSUBSET_DEF] >>
  `CARD s < CARD t` by rw[CARD_PSUBSET] >>
  decide_tac
QED

(* Theorem: (!x. x IN s ==> f x IN t) <=> (IMAGE f s) SUBSET t *)
(* Proof:
   If part: (!x. x IN s ==> f x IN t) ==> (IMAGE f s) SUBSET t
       y IN (IMAGE f s)
   ==> ?x. (y = f x) /\ x IN s   by IN_IMAGE
   ==> f x = y IN t              by given
   hence (IMAGE f s) SUBSET t    by SUBSET_DEF
   Only-if part: (IMAGE f s) SUBSET t ==>  (!x. x IN s ==> f x IN t)
       x IN s
   ==> f x IN (IMAGE f s)        by IN_IMAGE
   ==> f x IN t                  by SUBSET_DEF
*)
val IMAGE_SUBSET_TARGET = store_thm(
  "IMAGE_SUBSET_TARGET",
  ``!f s t. (!x. x IN s ==> f x IN t) <=> (IMAGE f s) SUBSET t``,
  metis_tac[IN_IMAGE, SUBSET_DEF]);

(* Theorem: SURJ f s t ==> CARD (IMAGE f s) = CARD t *)
(* Proof:
   Note IMAGE f s = t              by IMAGE_SURJ
   Thus CARD (IMAGE f s) = CARD t  by above
*)
Theorem SURJ_CARD_IMAGE:
  !f s t. SURJ f s t ==> CARD (IMAGE f s) = CARD t
Proof
  simp[IMAGE_SURJ]
QED

(* ------------------------------------------------------------------------- *)
(* Image and Bijection                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t) *)
(* Proof: by INJ_DEF *)
val INJ_CONG = store_thm(
  "INJ_CONG",
  ``!f g s t. (!x. x IN s ==> (f x = g x)) ==> (INJ f s t <=> INJ g s t)``,
  rw[INJ_DEF]);

(* Theorem: (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t) *)
(* Proof: by SURJ_DEF *)
val SURJ_CONG = store_thm(
  "SURJ_CONG",
  ``!f g s t. (!x. x IN s ==> (f x = g x)) ==> (SURJ f s t <=> SURJ g s t)``,
  rw[SURJ_DEF] >>
  metis_tac[]);

(* Theorem: (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t) *)
(* Proof: by BIJ_DEF, INJ_CONG, SURJ_CONG *)
val BIJ_CONG = store_thm(
  "BIJ_CONG",
  ``!f g s t. (!x. x IN s ==> (f x = g x)) ==> (BIJ f s t <=> BIJ g s t)``,
  rw[BIJ_DEF] >>
  metis_tac[INJ_CONG, SURJ_CONG]);

(*
BIJ_LINV_BIJ |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
Cannot prove |- !f s t. BIJ f s t <=> BIJ (LINV f s) t s
because LINV f s depends on f!
*)

(* Theorem: INJ f s t /\ x IN s ==> f x IN t *)
(* Proof: by INJ_DEF *)
val INJ_ELEMENT = store_thm(
  "INJ_ELEMENT",
  ``!f s t x. INJ f s t /\ x IN s ==> f x IN t``,
  rw_tac std_ss[INJ_DEF]);

(* Theorem: SURJ f s t /\ x IN s ==> f x IN t *)
(* Proof: by SURJ_DEF *)
val SURJ_ELEMENT = store_thm(
  "SURJ_ELEMENT",
  ``!f s t x. SURJ f s t /\ x IN s ==> f x IN t``,
  rw_tac std_ss[SURJ_DEF]);

(* Theorem: BIJ f s t /\ x IN s ==> f x IN t *)
(* Proof: by BIJ_DEF *)
val BIJ_ELEMENT = store_thm(
  "BIJ_ELEMENT",
  ``!f s t x. BIJ f s t /\ x IN s ==> f x IN t``,
  rw_tac std_ss[BIJ_DEF, INJ_DEF]);

(* Theorem: INJ f s t ==> INJ f s UNIV *)
(* Proof:
   Note s SUBSET s                        by SUBSET_REFL
    and t SUBSET univ(:'b)                by SUBSET_UNIV
     so INJ f s t ==> INJ f s univ(:'b)   by INJ_SUBSET
*)
val INJ_UNIV = store_thm(
  "INJ_UNIV",
  ``!f s t. INJ f s t ==> INJ f s UNIV``,
  metis_tac[INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV]);

(* Theorem: INJ f UNIV UNIV ==> INJ f s UNIV *)
(* Proof:
   Note s SUBSET univ(:'a)                               by SUBSET_UNIV
   and univ(:'b) SUBSET univ('b)                         by SUBSET_REFL
     so INJ f univ(:'a) univ(:'b) ==> INJ f s univ(:'b)  by INJ_SUBSET
*)
val INJ_SUBSET_UNIV = store_thm(
  "INJ_SUBSET_UNIV",
  ``!(f:'a -> 'b) (s:'a -> bool). INJ f UNIV UNIV ==> INJ f s UNIV``,
  metis_tac[INJ_SUBSET, SUBSET_UNIV, SUBSET_REFL]);

(* Theorem: INJ f s UNIV ==> BIJ f s (IMAGE f s) *)
(* Proof: by definitions. *)
val INJ_IMAGE_BIJ_ALT = store_thm(
  "INJ_IMAGE_BIJ_ALT",
  ``!f s. INJ f s UNIV ==> BIJ f s (IMAGE f s)``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: INJ f P univ(:'b) ==>
            !s t. s SUBSET P /\ t SUBSET P ==> ((IMAGE f s = IMAGE f t) <=> (s = t)) *)
(* Proof:
   If part: IMAGE f s = IMAGE f t ==> s = t
      Claim: s SUBSET t
      Proof: by SUBSET_DEF, this is to show: x IN s ==> x IN t
             x IN s
         ==> f x IN (IMAGE f s)            by INJ_DEF, IN_IMAGE
          or f x IN (IMAGE f t)            by given
         ==> ?x'. x' IN t /\ (f x' = f x)  by IN_IMAGE
         But x IN P /\ x' IN P             by SUBSET_DEF
        Thus f x' = f x ==> x' = x         by INJ_DEF

      Claim: t SUBSET s
      Proof: similar to above              by INJ_DEF, IN_IMAGE, SUBSET_DEF

       Hence s = t                         by SUBSET_ANTISYM

   Only-if part: s = t ==> IMAGE f s = IMAGE f t
      This is trivially true.
*)
val INJ_IMAGE_EQ = store_thm(
  "INJ_IMAGE_EQ",
  ``!P f. INJ f P univ(:'b) ==>
   !s t. s SUBSET P /\ t SUBSET P ==> ((IMAGE f s = IMAGE f t) <=> (s = t))``,
  rw[EQ_IMP_THM] >>
  (irule SUBSET_ANTISYM >> rpt conj_tac) >| [
    rw[SUBSET_DEF] >>
    `?x'. x' IN t /\ (f x' = f x)` by metis_tac[IMAGE_IN, IN_IMAGE] >>
    metis_tac[INJ_DEF, SUBSET_DEF],
    rw[SUBSET_DEF] >>
    `?x'. x' IN s /\ (f x' = f x)` by metis_tac[IMAGE_IN, IN_IMAGE] >>
    metis_tac[INJ_DEF, SUBSET_DEF]
  ]);

(* Note: pred_setTheory.IMAGE_INTER
|- !f s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t
*)

(* Theorem: INJ f P univ(:'b) ==>
            !s t. s SUBSET P /\ t SUBSET P ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t)) *)
(* Proof: by EXTENSION, INJ_DEF, SUBSET_DEF *)
val INJ_IMAGE_INTER = store_thm(
  "INJ_IMAGE_INTER",
  ``!P f. INJ f P univ(:'b) ==>
   !s t. s SUBSET P /\ t SUBSET P ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))``,
  rw[EXTENSION] >>
  metis_tac[INJ_DEF, SUBSET_DEF]);

(* tobe: helperSet, change P to P *)

(* Theorem: INJ f P univ(:'b) ==>
            !s t. s SUBSET P /\ t SUBSET P ==> (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t)) *)
(* Proof:
       DISJOINT (IMAGE f s) (IMAGE f t)
   <=> (IMAGE f s) INTER (IMAGE f t) = {}     by DISJOINT_DEF
   <=>           IMAGE f (s INTER t) = {}     by INJ_IMAGE_INTER, INJ f P univ(:'b)
   <=>                    s INTER t  = {}     by IMAGE_EQ_EMPTY
   <=> DISJOINT s t                           by DISJOINT_DEF
*)
val INJ_IMAGE_DISJOINT = store_thm(
  "INJ_IMAGE_DISJOINT",
  ``!P f. INJ f P univ(:'b) ==>
   !s t. s SUBSET P /\ t SUBSET P ==> (DISJOINT s t <=> DISJOINT (IMAGE f s) (IMAGE f t))``,
  metis_tac[DISJOINT_DEF, INJ_IMAGE_INTER, IMAGE_EQ_EMPTY]);

(* Theorem: INJ I s univ(:'a) *)
(* Proof:
   Note !x. I x = x                                           by I_THM
     so !x. x IN s ==> I x IN univ(:'a)                       by IN_UNIV
    and !x y. x IN s /\ y IN s ==> (I x = I y) ==> (x = y)    by above
  Hence INJ I s univ(:'b)                                     by INJ_DEF
*)
val INJ_I = store_thm(
  "INJ_I",
  ``!s:'a -> bool. INJ I s univ(:'a)``,
  rw[INJ_DEF]);

(* Theorem: INJ I (IMAGE f s) univ(:'b) *)
(* Proof:
  Since !x. x IN (IMAGE f s) ==> x IN univ(:'b)          by IN_UNIV
    and !x y. x IN (IMAGE f s) /\ y IN (IMAGE f s) ==>
              (I x = I y) ==> (x = y)                    by I_THM
  Hence INJ I (IMAGE f s) univ(:'b)                      by INJ_DEF
*)
val INJ_I_IMAGE = store_thm(
  "INJ_I_IMAGE",
  ``!s f. INJ I (IMAGE f s) univ(:'b)``,
  rw[INJ_DEF]);

(* Theorem: BIJ f s t <=> (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) y IN t ==> ?!x. x IN s /\ (f x = y)
       x exists by SURJ_DEF, and x is unique by INJ_DEF.
   (2) x IN s /\ y IN s /\ f x = f y ==> x = y
       true by INJ_DEF.
   (3) x IN t ==> ?y. y IN s /\ (f y = x)
       true by SURJ_DEF.
*)
val BIJ_THM = store_thm(
  "BIJ_THM",
  ``!f s t. BIJ f s t <=> (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?!x. x IN s /\ (f x = y))``,
  rw_tac std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >> metis_tac[]);

(* Theorem: BIJ f s t ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y) *)
(* Proof: by BIJ_DEF, INJ_DEF *)
Theorem BIJ_IS_INJ:
  !f s t. BIJ f s t ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)
Proof
  rw[BIJ_DEF, INJ_DEF]
QED

(* Theorem: BIJ f s t ==> !x. x IN t ==> ?y. y IN s /\ f y = x *)
(* Proof: by BIJ_DEF, SURJ_DEF. *)
Theorem BIJ_IS_SURJ:
  !f s t. BIJ f s t ==> !x. x IN t ==> ?y. y IN s /\ f y = x
Proof
  simp[BIJ_DEF, SURJ_DEF]
QED

(* Can remove in helperSet: FINITE_BIJ_PROPERTY
|- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ CARD s = CARD t
pred_setTheory.FINITE_BIJ
|- !f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ CARD s = CARD t
*)

(* Idea: improve FINITE_BIJ with iff of finiteness of s and t. *)

(* Theorem: BIJ f s t ==> (FINITE s <=> FINITE t) *)
(* Proof:
   If part: FINITE s ==> FINITE t
      This is true                 by FINITE_BIJ
   Only-if part: FINITE t ==> FINITE s
      Note BIJ (LINV f s) t s      by BIJ_LINV_BIJ
      Thus FINITE s                by FINITE_BIJ
*)
Theorem BIJ_FINITE_IFF:
  !f s t. BIJ f s t ==> (FINITE s <=> FINITE t)
Proof
  metis_tac[FINITE_BIJ, BIJ_LINV_BIJ]
QED

(* Theorem: INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y)) *)
(* Proof: by INJ_DEF *)
Theorem INJ_EQ_11:
  !f s x y. INJ f s s /\ x IN s /\ y IN s ==> ((f x = f y) <=> (x = y))
Proof
  metis_tac[INJ_DEF]
QED

(* Theorem: INJ f univ(:'a) univ(:'b) ==> !x y. f x = f y <=> x = y *)
(* Proof: by INJ_DEF, IN_UNIV. *)
Theorem INJ_IMP_11:
  !f. INJ f univ(:'a) univ(:'b) ==> !x y. f x = f y <=> x = y
Proof
  metis_tac[INJ_DEF, IN_UNIV]
QED
(* This is better than INJ_EQ_11 above. *)

(* Theorem: BIJ I s s *)
(* Proof: by definitions. *)
val BIJ_I_SAME = store_thm(
  "BIJ_I_SAME",
  ``!s. BIJ I s s``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: s <> {} ==> !e. IMAGE (K e) s = {e} *)
(* Proof:
       IMAGE (K e) s
   <=> {(K e) x | x IN s}    by IMAGE_DEF
   <=> {e | x IN s}          by K_THM
   <=> {e}                   by EXTENSION, if s <> {}
*)
val IMAGE_K = store_thm(
  "IMAGE_K",
  ``!s. s <> {} ==> !e. IMAGE (K e) s = {e}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: (!x y. (f x = f y) ==> (x = y)) ==> (!s e. e IN s <=> f e IN IMAGE f s) *)
(* Proof:
   If part: e IN s ==> f e IN IMAGE f s
     True by IMAGE_IN.
   Only-if part: f e IN IMAGE f s ==> e IN s
     ?x. (f e = f x) /\ x IN s   by IN_IMAGE
     f e = f x ==> e = x         by given implication
     Hence x IN s
*)
val IMAGE_ELEMENT_CONDITION = store_thm(
  "IMAGE_ELEMENT_CONDITION",
  ``!f:'a -> 'b. (!x y. (f x = f y) ==> (x = y)) ==> (!s e. e IN s <=> f e IN IMAGE f s)``,
  rw[EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: BIGUNION (IMAGE (\x. {x}) s) = s *)
(* Proof:
       z IN BIGUNION (IMAGE (\x. {x}) s)
   <=> ?t. z IN t /\ t IN (IMAGE (\x. {x}) s)   by IN_BIGUNION
   <=> ?t. z IN t /\ (?y. y IN s /\ (t = {y}))  by IN_IMAGE
   <=> z IN {z} /\ (?y. y IN s /\ {z} = {y})    by picking t = {z}
   <=> T /\ z IN s                              by picking y = z, IN_SING
   Hence  BIGUNION (IMAGE (\x. {x}) s) = s      by EXTENSION
*)
val BIGUNION_ELEMENTS_SING = store_thm(
  "BIGUNION_ELEMENTS_SING",
  ``!s. BIGUNION (IMAGE (\x. {x}) s) = s``,
  rw[EXTENSION, EQ_IMP_THM] >-
  metis_tac[] >>
  qexists_tac `{x}` >>
  metis_tac[IN_SING]);

(* Theorem: s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s)) *)
(* Proof: by SUBSET_DEF, INJ_DEF, EXTENSION, IN_IMAGE, IN_DIFF *)
Theorem IMAGE_DIFF:
  !s t f. s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s))
Proof
  rw[SUBSET_DEF, INJ_DEF, EXTENSION] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* More Theorems and Sets for Counting                                       *)
(* ------------------------------------------------------------------------- *)

(* Have simple (count n) *)

(* Theorem: count 1 = {0} *)
(* Proof: rename COUNT_ZERO *)
val COUNT_0 = save_thm("COUNT_0", COUNT_ZERO);
(* val COUNT_0 = |- count 0 = {}: thm *)

(* Theorem: count 1 = {0} *)
(* Proof: by count_def, EXTENSION *)
val COUNT_1 = store_thm(
  "COUNT_1",
  ``count 1 = {0}``,
  rw[count_def, EXTENSION]);

(* Theorem: n NOTIN (count n) *)
(* Proof: by IN_COUNT *)
val COUNT_NOT_SELF = store_thm(
  "COUNT_NOT_SELF",
  ``!n. n NOTIN (count n)``,
  rw[]);

(* Theorem: (count n = {}) <=> (n = 0) *)
(* Proof:
   Since FINITE (count n)         by FINITE_COUNT
     and CARD (count n) = n       by CARD_COUNT
      so count n = {} <=> n = 0   by CARD_EQ_0
*)
val COUNT_EQ_EMPTY = store_thm(
  "COUNT_EQ_EMPTY",
  ``!n. (count n = {}) <=> (n = 0)``,
  metis_tac[FINITE_COUNT, CARD_COUNT, CARD_EQ_0]);

(* Theorem: m <= n ==> count m SUBSET count n *)
(* Proof: by LENGTH_TAKE_EQ *)
val COUNT_SUBSET = store_thm(
  "COUNT_SUBSET",
  ``!m n. m <= n ==> count m SUBSET count n``,
  rw[SUBSET_DEF]);

(* Theorem: count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t *)
(* Proof:
       count (SUC n) SUBSET t
   <=> (n INSERT count n) SUBSET t     by COUNT_SUC
   <=> n IN t /\ (count n) SUBSET t    by INSERT_SUBSET
   <=> (count n) SUBSET t /\ n IN t    by CONJ_COMM
*)
val COUNT_SUC_SUBSET = store_thm(
  "COUNT_SUC_SUBSET",
  ``!n t. count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t``,
  metis_tac[COUNT_SUC, INSERT_SUBSET]);

(* Theorem: t DIFF (count (SUC n)) = t DIFF (count n) DELETE n *)
(* Proof:
     t DIFF (count (SUC n))
   = t DIFF (n INSERT count n)    by COUNT_SUC
   = t DIFF (count n) DELETE n    by EXTENSION
*)
val DIFF_COUNT_SUC = store_thm(
  "DIFF_COUNT_SUC",
  ``!n t. t DIFF (count (SUC n)) = t DIFF (count n) DELETE n``,
  rw[EXTENSION, EQ_IMP_THM]);

(* COUNT_SUC  |- !n. count (SUC n) = n INSERT count n *)

(* Theorem: count (SUC n) = 0 INSERT (IMAGE SUC (count n)) *)
(* Proof: by EXTENSION *)
val COUNT_SUC_BY_SUC = store_thm(
  "COUNT_SUC_BY_SUC",
  ``!n. count (SUC n) = 0 INSERT (IMAGE SUC (count n))``,
  rw[EXTENSION, EQ_IMP_THM] >>
  (Cases_on `x` >> simp[]));

(* Theorem: IMAGE f (count (SUC n)) = (f n) INSERT IMAGE f (count n) *)
(* Proof:
     IMAGE f (count (SUC n))
   = IMAGE f (n INSERT (count n))    by COUNT_SUC
   = f n INSERT IMAGE f (count n)    by IMAGE_INSERT
*)
val IMAGE_COUNT_SUC = store_thm(
  "IMAGE_COUNT_SUC",
  ``!f n. IMAGE f (count (SUC n)) = (f n) INSERT IMAGE f (count n)``,
  rw[COUNT_SUC]);

(* Theorem: IMAGE f (count (SUC n)) = (f 0) INSERT IMAGE (f o SUC) (count n) *)
(* Proof:
     IMAGE f (count (SUC n))
   = IMAGE f (0 INSERT (IMAGE SUC (count n)))    by COUNT_SUC_BY_SUC
   = f 0 INSERT IMAGE f (IMAGE SUC (count n))    by IMAGE_INSERT
   = f 0 INSERT IMAGE (f o SUC) (count n)        by IMAGE_COMPOSE
*)
val IMAGE_COUNT_SUC_BY_SUC = store_thm(
  "IMAGE_COUNT_SUC_BY_SUC",
  ``!f n. IMAGE f (count (SUC n)) = (f 0) INSERT IMAGE (f o SUC) (count n)``,
  rw[COUNT_SUC_BY_SUC, IMAGE_COMPOSE]);

(* Introduce countFrom m n, the set {m, m + 1, m + 2, ...., m + n - 1} *)
val _ = overload_on("countFrom", ``\m n. IMAGE ($+ m) (count n)``);

(* Theorem: countFrom m 0 = {} *)
(* Proof:
     countFrom m 0
   = IMAGE ($+ m) (count 0)     by notation
   = IMAGE ($+ m) {}            by COUNT_0
   = {}                         by IMAGE_EMPTY
*)
val countFrom_0 = store_thm(
  "countFrom_0",
  ``!m. countFrom m 0 = {}``,
  rw[]);

(* Theorem: countFrom m (SUC n) = m INSERT countFrom (m + 1) n *)
(* Proof: by IMAGE_COUNT_SUC_BY_SUC *)
val countFrom_SUC = store_thm(
  "countFrom_SUC",
  ``!m n. !m n. countFrom m (SUC n) = m INSERT countFrom (m + 1) n``,
  rpt strip_tac >>
  `$+ m o SUC = $+ (m + 1)` by rw[FUN_EQ_THM] >>
  rw[IMAGE_COUNT_SUC_BY_SUC]);

(* Theorem: 0 < n ==> m IN countFrom m n *)
(* Proof: by IN_COUNT *)
val countFrom_first = store_thm(
  "countFrom_first",
  ``!m n. 0 < n ==> m IN countFrom m n``,
  rw[] >>
  metis_tac[ADD_0]);

(* Theorem: x < m ==> x NOTIN countFrom m n *)
(* Proof: by IN_COUNT *)
val countFrom_less = store_thm(
  "countFrom_less",
  ``!m n x. x < m ==> x NOTIN countFrom m n``,
  rw[]);

(* Theorem: count n = countFrom 0 n *)
(* Proof: by EXTENSION *)
val count_by_countFrom = store_thm(
  "count_by_countFrom",
  ``!n. count n = countFrom 0 n``,
  rw[EXTENSION]);

(* Theorem: count (SUC n) = 0 INSERT countFrom 1 n *)
(* Proof:
      count (SUC n)
   = 0 INSERT IMAGE SUC (count n)     by COUNT_SUC_BY_SUC
   = 0 INSERT IMAGE ($+ 1) (count n)  by FUN_EQ_THM
   = 0 INSERT countFrom 1 n           by notation
*)
val count_SUC_by_countFrom = store_thm(
  "count_SUC_by_countFrom",
  ``!n. count (SUC n) = 0 INSERT countFrom 1 n``,
  rpt strip_tac >>
  `SUC = $+ 1` by rw[FUN_EQ_THM] >>
  rw[COUNT_SUC_BY_SUC]);

(* Inclusion-Exclusion for two sets:

CARD_UNION
|- !s. FINITE s ==> !t. FINITE t ==>
       (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)
CARD_UNION_EQN
|- !s t. FINITE s /\ FINITE t ==>
         (CARD (s UNION t) = CARD s + CARD t - CARD (s INTER t))
CARD_UNION_DISJOINT
|- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==>
         (CARD (s UNION t) = CARD s + CARD t)
*)

(* Inclusion-Exclusion for three sets. *)

(* Theorem: FINITE a /\ FINITE b /\ FINITE c ==>
            (CARD (a UNION b UNION c) =
             CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
             CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)) *)
(* Proof:
   Note FINITE (a UNION b)                            by FINITE_UNION
    and FINITE (a INTER c)                            by FINITE_INTER
    and FINITE (b INTER c)                            by FINITE_INTER
   Also (a INTER c) INTER (b INTER c)
       = a INTER b INTER c                            by EXTENSION
    and CARD (a INTER b) <= CARD a                    by CARD_INTER_LESS_EQ
    and CARD (a INTER b INTER c) <= CARD (b INTER c)  by CARD_INTER_LESS_EQ, INTER_COMM

        CARD (a UNION b UNION c)
      = CARD (a UNION b) + CARD c - CARD ((a UNION b) INTER c)
                                                      by CARD_UNION_EQN
      = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a UNION b) INTER c)          by CARD_UNION_EQN
      = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a INTER c) UNION (b INTER c))
                                                      by UNION_OVER_INTER
      = (CARD a + CARD b - CARD (a INTER b)) + CARD c -
        (CARD (a INTER c) + CARD (b INTER c) - CARD ((a INTER c) INTER (b INTER c)))
                                                      by CARD_UNION_EQN
      = CARD a + CARD b + CARD c - CARD (a INTER b) -
        (CARD (a INTER c) + CARD (b INTER c) - CARD (a INTER b INTER c))
                                                      by CARD (a INTER b) <= CARD a
      = CARD a + CARD b + CARD c - CARD (a INTER b) -
        (CARD (b INTER c) + CARD (a INTER c) - CARD (a INTER b INTER c))
                                                      by ADD_COMM
      = CARD a + CARD b + CARD c - CARD (a INTER b)
        + CARD (a INTER b INTER c) - CARD (b INTER c) - CARD (a INTER c)
                                                      by CARD (a INTER b INTER c) <= CARD (b INTER c)
      = CARD a + CARD b + CARD c + CARD (a INTER b INTER c)
        - CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)
                                                      by arithmetic
*)
Theorem CARD_UNION_3_EQN:
  !a b c. FINITE a /\ FINITE b /\ FINITE c ==>
          (CARD (a UNION b UNION c) =
           CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
           CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c))
Proof
  rpt strip_tac >>
  `FINITE (a UNION b) /\ FINITE (a INTER c) /\ FINITE (b INTER c)` by rw[] >>
  (`(a INTER c) INTER (b INTER c) = a INTER b INTER c` by (rw[EXTENSION] >> metis_tac[])) >>
  `CARD (a INTER b) <= CARD a` by rw[CARD_INTER_LESS_EQ] >>
  `CARD (a INTER b INTER c) <= CARD (b INTER c)` by metis_tac[INTER_COMM, CARD_INTER_LESS_EQ] >>
  `CARD (a UNION b UNION c)
      = CARD (a UNION b) + CARD c - CARD ((a UNION b) INTER c)` by rw[CARD_UNION_EQN] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a UNION b) INTER c)` by rw[CARD_UNION_EQN] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a INTER c) UNION (b INTER c))` by fs[UNION_OVER_INTER, INTER_COMM] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) + CARD c -
        (CARD (a INTER c) + CARD (b INTER c) - CARD (a INTER b INTER c))` by metis_tac[CARD_UNION_EQN] >>
  decide_tac
QED

(* Simplification of the above result for 3 disjoint sets. *)

(* Theorem: FINITE a /\ FINITE b /\ FINITE c /\
            DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
            (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c) *)
(* Proof: by DISJOINT_DEF, CARD_UNION_3_EQN *)
Theorem CARD_UNION_3_DISJOINT:
  !a b c. FINITE a /\ FINITE b /\ FINITE c /\
           DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
           (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c)
Proof
  rw[DISJOINT_DEF] >>
  rw[CARD_UNION_3_EQN]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum and Minimum of a Set                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ MAX_SET s < n ==> !x. x IN s ==> x < n *)
(* Proof:
   Since x IN s, s <> {}     by MEMBER_NOT_EMPTY
   Hence x <= MAX_SET s      by MAX_SET_DEF
    Thus x < n               by LESS_EQ_LESS_TRANS
*)
val MAX_SET_LESS = store_thm(
  "MAX_SET_LESS",
  ``!s n. FINITE s /\ MAX_SET s < n ==> !x. x IN s ==> x < n``,
  metis_tac[MEMBER_NOT_EMPTY, MAX_SET_DEF, LESS_EQ_LESS_TRANS]);

(* Theorem: FINITE s /\ s <> {} ==> !x. x IN s /\ (!y. y IN s ==> y <= x) ==> (x = MAX_SET s) *)
(* Proof:
   Let m = MAX_SET s.
   Since m IN s /\ x <= m       by MAX_SET_DEF
     and m IN s ==> m <= x      by implication
   Hence x = m.
*)
val MAX_SET_TEST = store_thm(
  "MAX_SET_TEST",
  ``!s. FINITE s /\ s <> {} ==> !x. x IN s /\ (!y. y IN s ==> y <= x) ==> (x = MAX_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MAX_SET s` >>
  `m IN s /\ x <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `m <= x` by rw[] >>
  decide_tac);

(* Theorem: s <> {} ==> !x. x IN s /\ (!y. y IN s ==> x <= y) ==> (x = MIN_SET s) *)
(* Proof:
   Let m = MIN_SET s.
   Since m IN s /\ m <= x     by MIN_SET_LEM
     and m IN s ==> x <= m    by implication
   Hence x = m.
*)
val MIN_SET_TEST = store_thm(
  "MIN_SET_TEST",
  ``!s. s <> {} ==> !x. x IN s /\ (!y. y IN s ==> x <= y) ==> (x = MIN_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  `m IN s /\ m <= x` by rw[MIN_SET_LEM, Abbr`m`] >>
  `x <= m` by rw[] >>
  decide_tac);

(* Theorem: FINITE s /\ s <> {} ==> !x. x IN s ==> ((MAX_SET s = x) <=> (!y. y IN s ==> y <= x)) *)
(* Proof:
   Let m = MAX_SET s.
   If part: y IN s ==> y <= m, true  by MAX_SET_DEF
   Only-if part: !y. y IN s ==> y <= x ==> m = x
      Note m IN s /\ x <= m          by MAX_SET_DEF
       and m IN s ==> m <= x         by implication
   Hence x = m.
*)
Theorem MAX_SET_TEST_IFF:
  !s. FINITE s /\ s <> {} ==>
      !x. x IN s ==> ((MAX_SET s = x) <=> (!y. y IN s ==> y <= x))
Proof
  rpt strip_tac >>
  qabbrev_tac `m = MAX_SET s` >>
  rw[EQ_IMP_THM] >- rw[MAX_SET_DEF, Abbr‘m’] >>
  `m IN s /\ x <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `m <= x` by rw[] >>
  decide_tac
QED

(* Theorem: s <> {} ==> !x. x IN s ==> ((MIN_SET s = x) <=> (!y. y IN s ==> x <= y)) *)
(* Proof:
   Let m = MIN_SET s.
   If part: y IN s ==> m <= y, true by  MIN_SET_LEM
   Only-if part: !y. y IN s ==> x <= y ==> m = x
      Note m IN s /\ m <= x     by MIN_SET_LEM
       and m IN s ==> x <= m    by implication
   Hence x = m.
*)
Theorem MIN_SET_TEST_IFF:
  !s. s <> {} ==> !x. x IN s ==> ((MIN_SET s = x) <=> (!y. y IN s ==> x <= y))
Proof
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  rw[EQ_IMP_THM] >- rw[MIN_SET_LEM, Abbr‘m’] >>
  `m IN s /\ m <= x` by rw[MIN_SET_LEM, Abbr`m`] >>
  `x <= m` by rw[] >> decide_tac
QED

(* Theorem: MAX_SET {} = 0 *)
(* Proof: by MAX_SET_REWRITES *)
val MAX_SET_EMPTY = save_thm("MAX_SET_EMPTY", MAX_SET_REWRITES |> CONJUNCT1);
(* val MAX_SET_EMPTY = |- MAX_SET {} = 0: thm *)

(* Theorem: MAX_SET {e} = e *)
(* Proof: by MAX_SET_REWRITES *)
val MAX_SET_SING = save_thm("MAX_SET_SING", MAX_SET_REWRITES |> CONJUNCT2 |> GEN_ALL);
(* val MAX_SET_SING = |- !e. MAX_SET {e} = e: thm *)

(* Theorem: FINITE s /\ s <> {} ==> MAX_SET s IN s *)
(* Proof: by MAX_SET_DEF *)
val MAX_SET_IN_SET = store_thm(
  "MAX_SET_IN_SET",
  ``!s. FINITE s /\ s <> {} ==> MAX_SET s IN s``,
  rw[MAX_SET_DEF]);

(* Theorem: FINITE s ==> !x. x IN s ==> x <= MAX_SET s *)
(* Proof: by in_max_set *)
val MAX_SET_PROPERTY = save_thm("MAX_SET_PROPERTY", in_max_set);
(* val MAX_SET_PROPERTY = |- !s. FINITE s ==> !x. x IN s ==> x <= MAX_SET s: thm *)

(* Note: MIN_SET {} is undefined. *)

(* Theorem: MIN_SET {e} = e *)
(* Proof: by MIN_SET_THM *)
val MIN_SET_SING = save_thm("MIN_SET_SING", MIN_SET_THM |> CONJUNCT1);
(* val MIN_SET_SING = |- !e. MIN_SET {e} = e: thm *)

(* Theorem: s <> {} ==> MIN_SET s IN s *)
(* Proof: by MIN_SET_LEM *)
val MIN_SET_IN_SET = save_thm("MIN_SET_IN_SET",
    MIN_SET_LEM |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* val MIN_SET_IN_SET = |- !s. s <> {} ==> MIN_SET s IN s: thm *)

(* Theorem: s <> {} ==> !x. x IN s ==> MIN_SET s <= x *)
(* Proof: by MIN_SET_LEM *)
val MIN_SET_PROPERTY = save_thm("MIN_SET_PROPERTY",
    MIN_SET_LEM |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* val MIN_SET_PROPERTY =|- !s. s <> {} ==> !x. x IN s ==> MIN_SET s <= x: thm *)


(* Theorem: FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==> (MAX_SET (s DELETE (MIN_SET s)) = MAX_SET s) *)
(* Proof:
   Let m = MIN_SET s, t = s DELETE m.
    Then t SUBSET s              by DELETE_SUBSET
      so FINITE t                by SUBSET_FINITE]);
   Since m IN s                  by MIN_SET_IN_SET
      so t <> {}                 by DELETE_EQ_SING, s <> {m}
     ==> ?x. x IN t              by MEMBER_NOT_EMPTY
     and x IN s /\ x <> m        by IN_DELETE
    From x IN s ==> m <= x       by MIN_SET_PROPERTY
    With x <> m ==> m < x        by LESS_OR_EQ
    Also x <= MAX_SET s          by MAX_SET_PROPERTY
    Thus MAX_SET s <> m          since m < x <= MAX_SET s
     But MAX_SET s IN s          by MAX_SET_IN_SET
    Thus MAX_SET s IN t          by IN_DELETE
     Now !y. y IN t ==>
             y IN s              by SUBSET_DEF
          or y <= MAX_SET s      by MAX_SET_PROPERTY
   Hence MAX_SET s = MAX_SET t   by MAX_SET_TEST
*)
val MAX_SET_DELETE = store_thm(
  "MAX_SET_DELETE",
  ``!s. FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==> (MAX_SET (s DELETE (MIN_SET s)) = MAX_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  qabbrev_tac `t = s DELETE m` >>
  `t SUBSET s` by rw[Abbr`t`] >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  `t <> {}` by metis_tac[MIN_SET_IN_SET, DELETE_EQ_SING] >>
  `?x. x IN t /\ x IN s /\ x <> m` by metis_tac[IN_DELETE, MEMBER_NOT_EMPTY] >>
  `m <= x` by rw[MIN_SET_PROPERTY, Abbr`m`] >>
  `m < x` by decide_tac >>
  `x <= MAX_SET s` by rw[MAX_SET_PROPERTY] >>
  `MAX_SET s <> m` by decide_tac >>
  `MAX_SET s IN t` by rw[MAX_SET_IN_SET, Abbr`t`] >>
  metis_tac[SUBSET_DEF, MAX_SET_PROPERTY, MAX_SET_TEST]);

(* Theorem: FINITE s ==> ((MAX_SET s = 0) <=> (s = {}) \/ (s = {0})) *)
(* Proof:
   If part: MAX_SET s = 0 ==> (s = {}) \/ (s = {0})
      By contradiction, suppose s <> {} /\ s <> {0}.
      Then ?x. x IN s /\ x <> 0      by ONE_ELEMENT_SING
      Thus x <= MAX_SET s            by in_max_set
        so MAX_SET s <> 0            by x <> 0
      This contradicts MAX_SET s = 0.
   Only-if part: (s = {}) \/ (s = {0}) ==> MAX_SET s = 0
      If s = {}, MAX_SET s = 0       by MAX_SET_EMPTY
      If s = {0}, MAX_SET s = 0      by MAX_SET_SING
*)
val MAX_SET_EQ_0 = store_thm(
  "MAX_SET_EQ_0",
  ``!s. FINITE s ==> ((MAX_SET s = 0) <=> (s = {}) \/ (s = {0}))``,
  (rw[EQ_IMP_THM] >> simp[]) >>
  CCONTR_TAC >>
  `s <> {} /\ s <> {0}` by metis_tac[] >>
  `?x. x IN s /\ x <> 0` by metis_tac[ONE_ELEMENT_SING] >>
  `x <= MAX_SET s` by rw[in_max_set] >>
  decide_tac);

(* Theorem: s <> {} ==> ((MIN_SET s = 0) <=> 0 IN s) *)
(* Proof:
   If part: MIN_SET s = 0 ==> 0 IN s
      This is true by MIN_SET_IN_SET.
   Only-if part: 0 IN s ==> MIN_SET s = 0
      Note MIN_SET s <= 0   by MIN_SET_LEM, 0 IN s
      Thus MIN_SET s = 0    by arithmetic
*)
val MIN_SET_EQ_0 = store_thm(
  "MIN_SET_EQ_0",
  ``!s. s <> {} ==> ((MIN_SET s = 0) <=> 0 IN s)``,
  rw[EQ_IMP_THM] >-
  metis_tac[MIN_SET_IN_SET] >>
  `MIN_SET s <= 0` by rw[MIN_SET_LEM] >>
  decide_tac);

(* Theorem: MAX_SET (IMAGE SUC (count n)) = n *)
(* Proof:
   By induction on n.
   Base case: MAX_SET (IMAGE SUC (count 0)) = 0
      LHS = MAX_SET (IMAGE SUC (count 0))
          = MAX_SET (IMAGE SUC {})       by COUNT_ZERO
          = MAX_SET {}                   by IMAGE_EMPTY
          = 0                            by MAX_SET_THM
          = RHS
   Step case: MAX_SET (IMAGE SUC (count n)) = n ==>
              MAX_SET (IMAGE SUC (count (SUC n))) = SUC n
      LHS = MAX_SET (IMAGE SUC (count (SUC n)))
          = MAX_SET (IMAGE SUC (n INSERT count n))           by COUNT_SUC
          = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))   by IMAGE_INSERT
          = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))      by MAX_SET_THM
          = MAX (SUC n) n                                    by induction hypothesis
          = SUC n                                            by LESS_SUC, MAX_DEF
          = RHS
*)
Theorem MAX_SET_IMAGE_SUC_COUNT:
  !n. MAX_SET (IMAGE SUC (count n)) = n
Proof
  Induct_on ‘n’ >-
  rw[] >>
  ‘MAX_SET (IMAGE SUC (count (SUC n))) =
   MAX_SET (IMAGE SUC (n INSERT count n))’ by rw[COUNT_SUC] >>
  ‘_ = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))’ by rw[] >>
  ‘_ = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))’ by rw[MAX_SET_THM] >>
  ‘_ = MAX (SUC n) n’ by rw[] >>
  ‘_ = SUC n’ by metis_tac[LESS_SUC, MAX_DEF, MAX_COMM] >>
  rw[]
QED

(* Theorem: HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c} *)
(* Proof:
   Let s = {f x | HALF x <= c}
   Note !x. HALF x <= c
    ==> SUC (2 * HALF x) <= SUC (2 * c)         by arithmetic
    and x <= SUC (2 * HALF x)                   by TWO_HALF_LE_THM
     so x <= SUC (2 * c) < 2 * c + 2            by arithmetic
   Thus s SUBSET (IMAGE f (count (2 * c + 2)))  by SUBSET_DEF
   Note FINITE (count (2 * c + 2))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by HALF x <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_HALF = store_thm(
  "MAX_SET_IMAGE_with_HALF",
  ``!f c x. HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | HALF x <= c}` >>
  `s SUBSET (IMAGE f (count (2 * c + 2)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `SUC (2 * HALF x'') <= SUC (2 * c)` by rw[] >>
  `x'' <= SUC (2 * HALF x'')` by rw[TWO_HALF_LE_THM] >>
  `x'' < 2 * c + 2` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  (`f x IN s` by (rw[Abbr`s`] >> metis_tac[])) >>
  rw[MAX_SET_PROPERTY]);

(*
Note: A more general version, replacing HALF x by g x, would be desirable.
However, there is no way to show FINITE s for arbitrary g x.
*)

(* Theorem: 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c} *)
(* Proof:
   Let s = {f x | x DIV b <= c}.
   Note !x. x DIV b <= c
    ==> b * SUC (x DIV b) <= b * SUC c          by arithmetic
    and x < b * SUC (x DIV b)                   by DIV_MULT_LESS_EQ, 0 < b
     so x < b * SUC c                           by arithmetic
   Thus s SUBSET (IMAGE f (count (b * SUC c)))  by SUBSET_DEF
   Note FINITE (count (b * SUC c))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by HALF x <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_DIV = store_thm(
  "MAX_SET_IMAGE_with_DIV",
  ``!f b c x. 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | x DIV b <= c}` >>
  `s SUBSET (IMAGE f (count (b * SUC c)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `b * SUC (x'' DIV b) <= b * SUC c` by rw[] >>
  `x'' < b * SUC (x'' DIV b)` by rw[DIV_MULT_LESS_EQ] >>
  `x'' < b * SUC c` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  (`f x IN s` by (rw[Abbr`s`] >> metis_tac[])) >>
  rw[MAX_SET_PROPERTY]);

(* Theorem: x - b <= c ==> f x <= MAX_SET {f x | x - b <= c} *)
(* Proof:
   Let s = {f x | x - b <= c}
   Note !x. x - b <= c ==> x <= b + c           by arithmetic
     so x <= 1 + b + c                          by arithmetic
   Thus s SUBSET (IMAGE f (count (1 + b + c)))  by SUBSET_DEF
   Note FINITE (count (1 + b + c))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by x - b <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_DEC = store_thm(
  "MAX_SET_IMAGE_with_DEC",
  ``!f b c x. x - b <= c ==> f x <= MAX_SET {f x | x - b <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | x - b <= c}` >>
  `s SUBSET (IMAGE f (count (1 + b + c)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `x'' < b + (c + 1)` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  `f x IN s` by
    (rw[Abbr`s`] >>
  `x <= b + c` by decide_tac >>
  metis_tac[]) >>
  rw[MAX_SET_PROPERTY]);

(* ------------------------------------------------------------------------- *)
(* Finite and Cardinality Theorems                                           *)
(* ------------------------------------------------------------------------- *)


(* Theorem: INJ f s UNIV /\ FINITE s ==> CARD (IMAGE f s) = CARD s *)
(* Proof:
   !x y. x IN s /\ y IN s /\ f x = f y == x = y   by INJ_DEF
   FINITE s ==> FINITE (IMAGE f s)                by IMAGE_FINITE
   Therefore   BIJ f s (IMAGE f s)                by BIJ_DEF, INJ_DEF, SURJ_DEF
   Hence       CARD (IMAGE f s) = CARD s          by FINITE_BIJ_CARD_EQ
*)
val INJ_CARD_IMAGE_EQN = store_thm(
  "INJ_CARD_IMAGE_EQN",
  ``!f s. INJ f s UNIV /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)``,
  rw[INJ_DEF] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `BIJ f s (IMAGE f s)` by rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[FINITE_BIJ_CARD_EQ]);


(* Theorem: FINTIE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> SURJ f s t *)
(* Proof:
   For any map f from s to t,
   (IMAGE f s) SUBSET t            by IMAGE_SUBSET_TARGET
   FINITE s ==> FINITE (IMAGE f s) by IMAGE_FINITE
   CARD (IMAGE f s) = CARD s       by INJ_CARD_IMAGE
                    = CARD t       by given
   Hence (IMAGE f s) = t           by SUBSET_EQ_CARD, FINITE t
   or SURJ f s t                   by IMAGE_SURJ
*)
val FINITE_INJ_AS_SURJ = store_thm(
  "FINITE_INJ_AS_SURJ",
  ``!f s t. INJ f s t /\ FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> SURJ f s t``,
  rw[INJ_DEF] >>
  `(IMAGE f s) SUBSET t` by rw[GSYM IMAGE_SUBSET_TARGET] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `CARD (IMAGE f s) = CARD t` by metis_tac[INJ_DEF, INJ_CARD_IMAGE, INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV] >>
  rw[SUBSET_EQ_CARD, IMAGE_SURJ]);

(* Reformulate theorem *)

(* Theorem: FINITE s /\ FINITE t /\ CARD s = CARD t /\
            INJ f s t ==> SURJ f s t *)
(* Proof: by FINITE_INJ_AS_SURJ *)
Theorem FINITE_INJ_IS_SURJ:
  !f s t. FINITE s /\ FINITE t /\ CARD s = CARD t /\
          INJ f s t ==> SURJ f s t
Proof
  simp[FINITE_INJ_AS_SURJ]
QED

(* Theorem: FINITE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> BIJ f s t *)
(* Proof:
   Note SURJ f s t             by FINITE_INJ_IS_SURJ
     so BIJ f s t              by BIJ_DEF, INJ f s t
*)
Theorem FINITE_INJ_IS_BIJ:
  !f s t. FINITE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> BIJ f s t
Proof
  simp[FINITE_INJ_IS_SURJ, BIJ_DEF]
QED

(* Note: FINITE_SURJ_IS_BIJ is not easy, see helperFunction. *)

(* Theorem: FINITE {P x | x < n}  *)
(* Proof:
   Since IMAGE (\i. P i) (count n) = {P x | x < n},
   this follows by
   IMAGE_FINITE  |- !s. FINITE s ==> !f. FINITE (IMAGE f s) : thm
   FINITE_COUNT  |- !n. FINITE (count n) : thm
*)
val FINITE_COUNT_IMAGE = store_thm(
  "FINITE_COUNT_IMAGE",
  ``!P n. FINITE {P x | x < n }``,
  rpt strip_tac >>
  `IMAGE (\i. P i) (count n) = {P x | x < n}` by rw[IMAGE_DEF] >>
  metis_tac[IMAGE_FINITE, FINITE_COUNT]);

(* Note: no need for CARD_IMAGE:

CARD_INJ_IMAGE      |- !f s. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)
FINITE_BIJ_CARD_EQ  |- !S. FINITE S ==> !t f. BIJ f S t /\ FINITE t ==> (CARD S = CARD t)
BIJ_LINV_BIJ        |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
*)

(* Theorem: FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t) *)
(* Proof:
   First, FINITE s /\ BIJ f s t ==> FINITE t
     BIJ f s t ==> SURJ f s t          by BIJ_DEF
               ==> IMAGE f s = t       by IMAGE_SURJ
     FINITE s  ==> FINITE (IMAGE f s)  by IMAGE_FINITE
     Hence FINITE t.
   Next, FINITE s /\ FINITE t /\ BIJ f s t ==> CARD s = CARD t
     by FINITE_BIJ_CARD_EQ.
*)
val FINITE_BIJ_PROPERTY = store_thm(
  "FINITE_BIJ_PROPERTY",
  ``!f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)``,
  ntac 4 strip_tac >>
  CONJ_ASM1_TAC >| [
    `SURJ f s t` by metis_tac[BIJ_DEF] >>
    `IMAGE f s = t` by rw[GSYM IMAGE_SURJ] >>
    rw[],
    metis_tac[FINITE_BIJ_CARD_EQ]
  ]);

(* Note:
> pred_setTheory.CARD_IMAGE;
val it = |- !s. FINITE s ==> CARD (IMAGE f s) <= CARD s: thm
*)

(* Theorem: For a 1-1 map f: s -> s, s and (IMAGE f s) are of the same size. *)
(* Proof:
   By finite induction on the set s:
   Base case: CARD (IMAGE f {}) = CARD {}
     True by IMAGE f {} = {}            by IMAGE_EMPTY
   Step case: !s. FINITE s /\ (CARD (IMAGE f s) = CARD s) ==> !e. e NOTIN s ==> (CARD (IMAGE f (e INSERT s)) = CARD (e INSERT s))
       CARD (IMAGE f (e INSERT s))
     = CARD (f e INSERT IMAGE f s)      by IMAGE_INSERT
     = SUC (CARD (IMAGE f s))           by CARD_INSERT: e NOTIN s, f e NOTIN s, for 1-1 map
     = SUC (CARD s)                     by induction hypothesis
     = CARD (e INSERT s)                by CARD_INSERT: e NOTIN s.
*)
Theorem FINITE_CARD_IMAGE:
  !s f. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==>
        (CARD (IMAGE f s) = CARD s)
Proof
  Induct_on ‘FINITE’ >> rw[]
QED

(* Theorem: !s. FINITE s ==> CARD (IMAGE SUC s)) = CARD s *)
(* Proof:
   Since !n m. SUC n = SUC m <=> n = m    by numTheory.INV_SUC
   This is true by FINITE_CARD_IMAGE.
*)
val CARD_IMAGE_SUC = store_thm(
  "CARD_IMAGE_SUC",
  ``!s. FINITE s ==> (CARD (IMAGE SUC s) = CARD s)``,
  rw[FINITE_CARD_IMAGE]);

(* Theorem: FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t) *)
(* Proof: by CARD_UNION_EQN, DISJOINT_DEF, CARD_EMPTY *)
val CARD_UNION_DISJOINT = store_thm(
  "CARD_UNION_DISJOINT",
  ``!s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)``,
  rw_tac std_ss[CARD_UNION_EQN, DISJOINT_DEF, CARD_EMPTY]);

(* Idea: improve FINITE_BIJ_COUNT to include CARD information. *)

(* Theorem: FINITE s ==> ?f. BIJ f (count (CARD s)) s *)
(* Proof:
   Note ?f b. BIJ f (count b) s    by FINITE_BIJ_COUNT
    and FINITE (count b)           by FINITE_COUNT
     so CARD s
      = CARD (count b)             by FINITE_BIJ
      = b                          by CARD_COUNT
*)
Theorem FINITE_BIJ_COUNT_CARD:
  !s. FINITE s ==> ?f. BIJ f (count (CARD s)) s
Proof
  rpt strip_tac >>
  imp_res_tac FINITE_BIJ_COUNT >>
  metis_tac[FINITE_COUNT, CARD_COUNT, FINITE_BIJ]
QED

(* Theorem: !n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET (count n) *)
(* Proof: by SUBSET_DEF, MOD_LESS. *)
val image_mod_subset_count = store_thm(
  "image_mod_subset_count",
  ``!s n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET (count n)``,
  rw[SUBSET_DEF] >>
  rw[MOD_LESS]);

(* Theorem: !n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n *)
(* Proof:
   Let t = IMAGE (\x. x MOD n) s
   Since   t SUBSET count n          by SUBSET_DEF, MOD_LESS
     Now   FINITE (count n)          by FINITE_COUNT
     and   CARD (count n) = n        by CARD_COUNT
      So   CARD t <= n               by CARD_SUBSET
*)
val card_mod_image = store_thm(
  "card_mod_image",
  ``!s n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE (\x. x MOD n) s` >>
  (`t SUBSET count n` by (rw[SUBSET_DEF, Abbr`t`] >> metis_tac[MOD_LESS])) >>
  metis_tac[CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);
(* not used *)

(* Theorem: !n. 0 < n /\ 0 NOTIN (IMAGE (\x. x MOD n) s) ==> CARD (IMAGE (\x. x MOD n) s) < n *)
(* Proof:
   Let t = IMAGE (\x. x MOD n) s
   Since   t SUBSET count n          by SUBSET_DEF, MOD_LESS
     Now   FINITE (count n)          by FINITE_COUNT
     and   CARD (count n) = n        by CARD_COUNT
      So   CARD t <= n               by CARD_SUBSET
     and   FINITE t                  by SUBSET_FINITE
     But   0 IN (count n)            by IN_COUNT
     yet   0 NOTIN t                 by given
   Hence   t <> (count n)            by NOT_EQUAL_SETS
      So   CARD t <> n               by SUBSET_EQ_CARD
     Thus  CARD t < n
*)
val card_mod_image_nonzero = store_thm(
  "card_mod_image_nonzero",
  ``!s n. 0 < n /\ 0 NOTIN (IMAGE (\x. x MOD n) s) ==> CARD (IMAGE (\x. x MOD n) s) < n``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE (\x. x MOD n) s` >>
  (`t SUBSET count n` by (rw[SUBSET_DEF, Abbr`t`] >> metis_tac[MOD_LESS])) >>
  `FINITE (count n) /\ (CARD (count n) = n) ` by rw[] >>
  `CARD t <= n` by metis_tac[CARD_SUBSET] >>
  `0 IN (count n)` by rw[] >>
  `t <> (count n)` by metis_tac[NOT_EQUAL_SETS] >>
  `CARD t <> n` by metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE] >>
  decide_tac);
(* not used *)

(* ------------------------------------------------------------------------- *)
(* Partition Property                                                        *)
(* ------------------------------------------------------------------------- *)

(* Overload partition by split *)
val _ = overload_on("split", ``\s u v. (s = u UNION v) /\ (DISJOINT u v)``);

(* Pretty printing of partition by split *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 2)),
                       fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                    term_name = "split",
                  pp_elements = [HardSpace 1, TOK "=|=", HardSpace 1, TM,
                                 BreakSpace(1,1), TOK "#", BreakSpace(1,1)]};

(* Theorem: FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s)) *)
(* Proof:
   If part: u = {} ==> v = s
      Note  s = {} UNION v        by given, u = {}
              = v                 by UNION_EMPTY
   Only-if part: v = s ==> u = {}
      Note FINITE u /\ FINITE v       by FINITE_UNION
       ==> CARD v = CARD u + CARD v   by CARD_UNION_DISJOINT
       ==>      0 = CARD u            by arithmetic
      Thus u = {}                     by CARD_EQ_0
*)
val finite_partition_property = store_thm(
  "finite_partition_property",
  ``!s. FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s))``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `FINITE u /\ FINITE v` by metis_tac[FINITE_UNION] >>
  `CARD v = CARD u + CARD v` by metis_tac[CARD_UNION_DISJOINT] >>
  `CARD u <> 0` by rw[CARD_EQ_0] >>
  decide_tac);

(* Theorem: FINITE s ==> !P. let u = {x | x IN s /\ P x} in let v = {x | x IN s /\ ~P x} in
            FINITE u /\ FINITE v /\ s =|= u # v *)
(* Proof:
   This is to show:
   (1) FINITE u, true      by SUBSET_DEF, SUBSET_FINITE
   (2) FINITE v, true      by SUBSET_DEF, SUBSET_FINITE
   (3) u UNION v = s       by IN_UNION
   (4) DISJOINT u v, true  by IN_DISJOINT, MEMBER_NOT_EMPTY
*)
Theorem finite_partition_by_predicate:
  !s. FINITE s ==>
      !P. let u = {x | x IN s /\ P x} ;
              v = {x | x IN s /\ ~P x}
          in
              FINITE u /\ FINITE v /\ s =|= u # v
Proof
  rw_tac std_ss[] >| [
    `u SUBSET s` by rw[SUBSET_DEF, Abbr`u`] >>
    metis_tac[SUBSET_FINITE],
    `v SUBSET s` by rw[SUBSET_DEF, Abbr`v`] >>
    metis_tac[SUBSET_FINITE],
    simp[EXTENSION, Abbr‘u’, Abbr‘v’] >>
    metis_tac[],
    simp[Abbr‘u’, Abbr‘v’, DISJOINT_DEF, EXTENSION] >> metis_tac[]
  ]
QED

(* Theorem: u SUBSET s ==> let v = s DIFF u in s =|= u # v *)
(* Proof:
   This is to show:
   (1) u SUBSET s ==> s = u UNION (s DIFF u), true   by UNION_DIFF
   (2) u SUBSET s ==> DISJOINT u (s DIFF u), true    by DISJOINT_DIFF
*)
val partition_by_subset = store_thm(
  "partition_by_subset",
  ``!s u. u SUBSET s ==> let v = s DIFF u in s =|= u # v``,
  rw[UNION_DIFF, DISJOINT_DIFF]);

(* Theorem: x IN s ==> s =|= {x} # (s DELETE x) *)
(* Proof:
   Note x IN s ==> {x} SUBSET s    by SUBSET_DEF, IN_SING
    and s DELETE x = s DIFF {x}    by DELETE_DEF
   Thus s =|= {x} # (s DELETE x)   by partition_by_subset
*)
val partition_by_element = store_thm(
  "partition_by_element",
  ``!s x. x IN s ==> s =|= {x} # (s DELETE x)``,
  metis_tac[partition_by_subset, DELETE_DEF, SUBSET_DEF, IN_SING]);

(* ------------------------------------------------------------------------- *)
(* Splitting of a set                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s =|= {} # t <=> (s = t) *)
(* Proof:
       s =|= {} # t
   <=> (s = {} UNION t) /\ (DISJOINT {} t)     by notation
   <=> (s = {} UNION t) /\ T                   by DISJOINT_EMPTY
   <=> s = t                                   by UNION_EMPTY
*)
val SPLIT_EMPTY = store_thm(
  "SPLIT_EMPTY",
  ``!s t. s =|= {} # t <=> (s = t)``,
  rw[]);

(* Theorem: s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a *)
(* Proof:
   Note s =|= u # v <=> (s = u UNION v) /\ (DISJOINT u v)   by notation
    and v =|= a # b <=> (v = a UNION b) /\ (DISJOINT a b)   by notation
   Let c = u UNION a.
   Then s = u UNION v                   by above
          = u UNION (a UNION b)         by above
          = (u UNION a) UNION b         by UNION_ASSOC
          = c UNION b
   Note  DISJOINT u v
     <=> DISJOINT u (a UNION b)
     <=> DISJOINT (a UNION b) u         by DISJOINT_SYM
     <=> DISJOINT a u /\ DISJOINT b u   by DISJOINT_UNION
     <=> DISJOINT u a /\ DISJOINT u b   by DISJOINT_SYM

   Thus  DISJOINT c b
     <=> DISJOINT (u UNION a) b         by above
     <=> DISJOINT u b /\ DISJOINT a b   by DISJOINT_UNION
     <=> T /\ T                         by above
     <=> T
   Therefore,
         s =|= c # b       by s = c UNION b /\ DISJOINT c b
     and c =|= u # a       by c = u UNION a /\ DISJOINT u a
*)
val SPLIT_UNION = store_thm(
  "SPLIT_UNION",
  ``!s u v a b. s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a``,
  metis_tac[DISJOINT_UNION, DISJOINT_SYM, UNION_ASSOC]);

(* Theorem: s =|= u # v <=> u SUBSET s /\ (v = s DIFF u) *)
(* Proof:
   Note s =|= u # v <=> (s = u UNION v) /\ (DISJOINT u v)   by notation
   If part: s =|= u # v ==> u SUBSET s /\ (v = s DIFF u)
      Note u SUBSET (u UNION v)         by SUBSET_UNION
           s DIFF u
         = (u UNION v) DIFF u           by s = u UNION v
         = v DIFF u                     by DIFF_SAME_UNION
         = v                            by DISJOINT_DIFF_IFF, DISJOINT_SYM

   Only-if part: u SUBSET s /\ (v = s DIFF u) ==> s =|= u # v
      Note s = u UNION (s DIFF u)       by UNION_DIFF, u SUBSET s
       and DISJOINT u (s DIFF u)        by DISJOINT_DIFF
      Thus s =|= u # v                  by notation
*)
val SPLIT_EQ = store_thm(
  "SPLIT_EQ",
  ``!s u v. s =|= u # v <=> u SUBSET s /\ (v = s DIFF u)``,
  rw[DISJOINT_DEF, SUBSET_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: (s =|= u # v) = (s =|= v # u) *)
(* Proof:
     s =|= u # v
   = (s = u UNION v) /\ DISJOINT u v    by notation
   = (s = v UNION u) /\ DISJOINT u v    by UNION_COMM
   = (s = v UNION u) /\ DISJOINT v u    by DISJOINT_SYM
   = s =|= v # u                        by notation
*)
val SPLIT_SYM = store_thm(
  "SPLIT_SYM",
  ``!s u v. (s =|= u # v) = (s =|= v # u)``,
  rw_tac std_ss[UNION_COMM, DISJOINT_SYM]);

(* Theorem: (s =|= u # v) ==> (s =|= v # u) *)
(* Proof: by SPLIT_SYM *)
val SPLIT_SYM_IMP = store_thm(
  "SPLIT_SYM_IMP",
  ``!s u v. (s =|= u # v) ==> (s =|= v # u)``,
  rw_tac std_ss[SPLIT_SYM]);

(* Theorem: s =|= {x} # v <=> (x IN s /\ (v = s DELETE x)) *)
(* Proof:
       s =|= {x} # v
   <=> {x} SUBSET s /\ (v = s DIFF {x})   by SPLIT_EQ
   <=> x IN s       /\ (v = s DIFF {x})   by SUBSET_DEF
   <=> x IN s       /\ (v = s DELETE x)   by DELETE_DEF
*)
val SPLIT_SING = store_thm(
  "SPLIT_SING",
  ``!s v x. s =|= {x} # v <=> (x IN s /\ (v = s DELETE x))``,
  rw[SPLIT_EQ, SUBSET_DEF, DELETE_DEF]);

(* Theorem: s =|= u # v ==> u SUBSET s /\ v SUBSET s *)
(* Proof: by SUBSET_UNION *)
Theorem SPLIT_SUBSETS:
  !s u v. s =|= u # v ==> u SUBSET s /\ v SUBSET s
Proof
  rw[]
QED

(* Theorem: FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v *)
(* Proof: by SPLIT_SUBSETS, SUBSET_FINITE *)
Theorem SPLIT_FINITE:
  !s u v. FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v
Proof
  simp[SPLIT_SUBSETS, SUBSET_FINITE]
QED

(* Theorem: FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v) *)
(* Proof:
   Note FINITE u /\ FINITE v   by SPLIT_FINITE
     CARD s
   = CARD (u UNION v)          by notation
   = CARD u + CARD v           by CARD_UNION_DISJOINT
*)
Theorem SPLIT_CARD:
  !s u v. FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v)
Proof
  metis_tac[CARD_UNION_DISJOINT, SPLIT_FINITE]
QED

(* Theorem: s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u) *)
(* Proof:
   If part: s =|= u # v ==> (u = s DIFF v) /\ (v = s DIFF u)
      True by EXTENSION, IN_UNION, IN_DISJOINT, IN_DIFF.
   Only-if part: (u = s DIFF v) /\ (v = s DIFF u) ==> s =|= u # v
      True by EXTENSION, IN_UNION, IN_DISJOINT, IN_DIFF.
*)
val SPLIT_EQ_DIFF = store_thm(
  "SPLIT_EQ_DIFF",
  ``!s u v. s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u)``,
  rpt strip_tac >>
  eq_tac >| [
    rpt strip_tac >| [
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DISJOINT, IN_DIFF],
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DISJOINT, IN_DIFF]
    ],
    rpt strip_tac >| [
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DIFF],
      metis_tac[IN_DISJOINT, IN_DIFF]
    ]
  ]);

(* Theorem alias *)
val SPLIT_BY_SUBSET = save_thm("SPLIT_BY_SUBSET", partition_by_subset);
(* val SPLIT_BY_SUBSET = |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v): thm *)

(* Theorem alias *)
val SUBSET_DIFF_DIFF = save_thm("SUBSET_DIFF_DIFF", DIFF_DIFF_SUBSET);
(* val SUBSET_DIFF_DIFF = |- !s t. t SUBSET s ==> (s DIFF (s DIFF t) = t) *)

(* Theorem: s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2) *)
(* Proof:
   Let u = t DIFF s2.
   Then u = t DIFF s1             by given
    ==> t =|= u # s1              by SPLIT_BY_SUBSET, s1 SUBSET t
   Thus s1 = t DIFF u             by SPLIT_EQ
           = t DIFF (t DIFF s2)   by notation
           = s2                   by SUBSET_DIFF_DIFF, s2 SUBSET t
*)
val SUBSET_DIFF_EQ = store_thm(
  "SUBSET_DIFF_EQ",
  ``!s1 s2 t. s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2)``,
  metis_tac[SPLIT_BY_SUBSET, SPLIT_EQ, SUBSET_DIFF_DIFF]);

(* ------------------------------------------------------------------------- *)
(* Bijective Inverses.                                                       *)
(* ------------------------------------------------------------------------- *)

(* In pred_setTheory:
LINV_DEF        |- !f s t. INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)
BIJ_LINV_INV    |- !f s t. BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)
BIJ_LINV_BIJ    |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
RINV_DEF        |- !f s t. SURJ f s t ==> !x. x IN t ==> (f (RINV f s x) = x)

That's it, must be missing some!
Must assume: !y. y IN t ==> RINV f s y IN s
*)

(* Theorem: BIJ f s t ==> !x. x IN t ==> (LINV f s x) IN s *)
(* Proof:
   Since BIJ f s t ==> BIJ (LINV f s) t s   by BIJ_LINV_BIJ
      so x IN t ==> (LINV f s x) IN s       by BIJ_DEF, INJ_DEF
*)
val BIJ_LINV_ELEMENT = store_thm(
  "BIJ_LINV_ELEMENT",
  ``!f s t. BIJ f s t ==> !x. x IN t ==> (LINV f s x) IN s``,
  metis_tac[BIJ_LINV_BIJ, BIJ_DEF, INJ_DEF]);

(* Theorem: (!x. x IN s ==> (LINV f s (f x) = x)) /\ (!x. x IN t ==> (f (LINV f s x) = x)) *)
(* Proof:
   Since BIJ f s t ==> INJ f s t      by BIJ_DEF
     and INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)    by LINV_DEF
    also BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)    by BIJ_LINV_INV
*)
val BIJ_LINV_THM = store_thm(
  "BIJ_LINV_THM",
  ``!(f:'a -> 'b) s t. BIJ f s t ==>
    (!x. x IN s ==> (LINV f s (f x) = x)) /\ (!x. x IN t ==> (f (LINV f s x) = x))``,
  metis_tac[BIJ_DEF, LINV_DEF, BIJ_LINV_INV]);

(* Theorem: BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
            !x. x IN s ==> (RINV f s (f x) = x) *)
(* Proof:
   BIJ f s t means INJ f s t /\ SURJ f s t     by BIJ_DEF
   Hence x IN s ==> f x IN t                   by INJ_DEF or SURJ_DEF
                ==> f (RINV f s (f x)) = f x   by RINV_DEF, SURJ f s t
                ==> RINV f s (f x) = x         by INJ_DEF
*)
val BIJ_RINV_INV = store_thm(
  "BIJ_RINV_INV",
  ``!(f:'a -> 'b) s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
   !x. x IN s ==> (RINV f s (f x) = x)``,
  rw[BIJ_DEF] >>
  `f x IN t` by metis_tac[INJ_DEF] >>
  `f (RINV f s (f x)) = f x` by metis_tac[RINV_DEF] >>
  metis_tac[INJ_DEF]);

(* Theorem: BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) INJ (RINV f s) t s
       By INJ_DEF, this is to show:
       x IN t /\ y IN t /\ RINV f s x = RINV f s y ==> x = y
       But  SURJ f s t           by BIJ_DEF
        so  f (RINV f s x) = x   by RINV_DEF, SURJ f s t
       and  f (RINV f s y) = y   by RINV_DEF, SURJ f s t
       Thus x = y.
   (2) SURJ (RINV f s) t s
       By SURJ_DEF, this is to show:
       x IN s ==> ?y. y IN t /\ (RINV f s y = x)
       But  INJ f s t            by BIJ_DEF
        so  f x IN t             by INJ_DEF
       and  RINV f s (f x) = x   by BIJ_RINV_INV
       Take y = f x to meet the criteria.
*)
val BIJ_RINV_BIJ = store_thm(
  "BIJ_RINV_BIJ",
  ``!(f:'a -> 'b) s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s``,
  rpt strip_tac >>
  rw[BIJ_DEF] >-
  metis_tac[INJ_DEF, BIJ_DEF, RINV_DEF] >>
  rw[SURJ_DEF] >>
  metis_tac[INJ_DEF, BIJ_DEF, BIJ_RINV_INV]);

(* Theorem: INJ f t univ(:'b) /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x) *)
(* Proof: by LINV_DEF, SUBSET_DEF *)
Theorem LINV_SUBSET:
  !(f:'a -> 'b) s t. INJ f t univ(:'b) /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x)
Proof
  metis_tac[LINV_DEF, SUBSET_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Iteration, Summation and Product                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ITSET f {x} b = f x b *)
(* Proof:
   Since FINITE {x}           by FINITE_SING
     ITSET f {x} b
   = ITSET f (REST {x}) (f (CHOICE {x} b)   by ITSET_THM
   = ITSET f {} (f x b)       by CHOICE_SING, REST_SING
   = f x b                    by ITSET_EMPTY
*)
val ITSET_SING = store_thm(
  "ITSET_SING",
  ``!f x b. ITSET f {x} b = f x b``,
  rw[ITSET_THM]);

(* Theorem: FINITE s /\ s <> {} ==> (ITSET f s b = ITSET f (REST s) (f (CHOICE s) b)) *)
(* Proof: by ITSET_THM. *)
val ITSET_PROPERTY = store_thm(
  "ITSET_PROPERTY",
  ``!s f b. FINITE s /\ s <> {} ==> (ITSET f s b = ITSET f (REST s) (f (CHOICE s) b))``,
  rw[ITSET_THM]);

(* Theorem: (f = g) ==> (ITSET f = ITSET g) *)
(* Proof: by congruence rule *)
val ITSET_CONG = store_thm(
  "ITSET_CONG",
  ``!f g. (f = g) ==> (ITSET f = ITSET g)``,
  rw[]);

(* Reduction of ITSET *)

(* Theorem: (!x y z. f x (f y z) = f y (f x z)) ==>
             !s x b. FINITE s /\ x NOTIN s ==> (ITSET f (x INSERT s) b = f x (ITSET f s b)) *)
(* Proof:
   Since x NOTIN s ==> s DELETE x = s   by DELETE_NON_ELEMENT
   The result is true                   by COMMUTING_ITSET_RECURSES
*)
val ITSET_REDUCTION = store_thm(
  "ITSET_REDUCTION",
  ``!f. (!x y z. f x (f y z) = f y (f x z)) ==>
   !s x b. FINITE s /\ x NOTIN s ==> (ITSET f (x INSERT s) b = f x (ITSET f s b))``,
  rw[COMMUTING_ITSET_RECURSES, DELETE_NON_ELEMENT]);

(* ------------------------------------------------------------------------- *)
(* Rework of ITSET Theorems                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define a function that gives closure and is commute_associative *)
val closure_comm_assoc_fun_def = Define`
    closure_comm_assoc_fun f s <=>
       (!x y. x IN s /\ y IN s ==> f x y IN s) /\ (* closure *)
       (!x y z. x IN s /\ y IN s /\ z IN s ==> (f x (f y z) = f y (f x z))) (* comm_assoc *)
`;

(* Theorem: FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
            !(x b):: t. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b) *)
(* Proof:
   By complete induction on CARD s.
   The goal is to show:
   ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)  [1]
   Applying ITSET_INSERT to LHS, this is to prove:
   ITSET f z (f y b) = ITSET f (s DELETE x) (f x b)
           |    |
           |    y = CHOICE (x INSERT s)
           +--- z = REST (x INSERT s)
   Note y NOTIN z   by CHOICE_NOT_IN_REST
   If x IN s,
       then x INSERT s = s                      by ABSORPTION
       thus y = CHOICE s, z = REST s            by x INSERT s = s

       If x = y,
       Since s = CHOICE s INSERT REST s         by CHOICE_INSERT_REST
               = y INSERT z                     by above y, z
       Hence z = s DELETE y                     by DELETE_INSERT
       Since CARD z < CARD s, apply induction:
       ITSET f (y INSERT z) b = ITSET f (z DELETE y) (f y b)  [2a]
       For the original goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f s b                        by x INSERT s = s
           = ITSET f (y INSERT z) b             by s = y INSERT z
           = ITSET f (z DELETE y) (f y b)       by induction hypothesis [2a]
           = ITSET f z (f y b)                  by DELETE_NON_ELEMENT, y NOTIN z
           = ITSET f (s DELETE y) (f y b)       by z = s DELETE y
           = ITSET f (s DELETE x) (f x b)       by x = y
           = RHS

       If x <> y, let u = z DELETE x.
       Note REST s = z = x INSERT u             by INSERT_DELETE
       Now s = x INSERT (y INSERT u)
             = x INSERT v, where v = y INSERT u, and x NOTIN z.
       Therefore (s DELETE x) = v               by DELETE_INSERT
       Since CARD v < CARD s, apply induction:
       ITSET f (x INSERT v) b = ITSET f (v DELETE x) (f x b)    [2b]
       For the original goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f s b                        by x INSERT s = s
           = ITSET f (x INSERT v) b             by s = x INSERT v
           = ITSET f (v DELETE x) (f x b)       by induction hypothesis [2b]
           = ITSET f v (f x b)                  by x NOTIN v
           = ITSET f (s DELETE x) (f x b)       by v = s DELETE x
           = RHS

   If x NOTIN s,
       then s DELETE x = x                      by DELETE_NON_ELEMENT
       To prove: ITSET f (x INSERT s) b = ITSET f s (f x b)    by [1]
       The CHOICE/REST of (x INSERT s) cannot be simplified, but can be replaced by:
       Note (x INSERT s) <> {}                  by NOT_EMPTY_INSERT
         y INSERT z
       = CHOICE (x INSERT s) INSERT (REST (x INSERT s))  by y = CHOICE (x INSERT s), z = REST (x INSERT s)
       = x INSERT s                                      by CHOICE_INSERT_REST

       If y = x,
          Then z = s                            by DELETE_INSERT, y INSERT z = x INSERT s, y = x.
          because s = s DELETE x                by DELETE_NON_ELEMENT, x NOTIN s.
                    = (x INSERT s) DELETE x     by DELETE_INSERT
                    = (y INSERT z) DELETE x     by above
                    = (y INSERT z) DELETE y     by y = x
                    = z DELETE y                by DELETE_INSERT
                    = z                         by DELETE_NON_ELEMENT, y NOTIN z.
       For the modified goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)  by ITSET_PROPERTY
           = ITSET f z (f y b)                           by y = CHOICE (x INSERT s), z = REST (x INSERT s)
           = ITSET f s (f x b)                           by z = s, y = x
           = RHS

       If y <> x,
       Then x IN z and y IN s                   by IN_INSERT, x INSERT s = y INSERT z and x <> y.
        and s = y INSERT (s DELETE y)           by INSERT_DELETE, y IN s
              = y INSERT u  where u = s DELETE y
       Then y NOTIN u                           by IN_DELETE
        and z = x INSERT u,
       because  x INSERT u
              = x INSERT (s DELETE y)           by u = s DELETE y
              = (x INSERT s) DELETE y           by DELETE_INSERT, x <> y
              = (y INSERT z) DELETE y           by x INSERT s = y INSERT z
              = z                               by INSERT_DELETE
        and x NOTIN u                           by IN_DELETE, u = s DELETE y, but x NOTIN s.
       Thus CARD u < CARD s                     by CARD_INSERT, s = y INSERT u.
       Apply induction:
       !x b. ITSET f (x INSERT u) b = ITSET f (u DELETE x) (f x b)  [2c]

       For the modified goal [1],
       LHS = ITSET f (x INSERT s) b
           = ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)  by ITSET_PROPERTY
           = ITSET f z (f y b)                  by z = REST (x INSERT s), y = CHOICE (x INSERT s)
           = ITSET f (x INSERT u) (f y b)       by z = x INSERT u
           = ITSET f (u DELETE x) (f x (f y b)) by induction hypothesis, [2c]
           = ITSET f u (f x (f y b))            by x NOTIN u
       RHS = ITSET f s (f x b)
           = ITSET f (y INSERT u) (f x b)       by s = y INSERT u
           = ITSET f (u DELETE y) (f y (f x b)) by induction hypothesis, [2c]
           = ITSET f u (f y (f x b))            by y NOTIN u
       Applying the commute_associativity of f, LHS = RHS.
*)
Theorem SUBSET_COMMUTING_ITSET_INSERT:
  !f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
          !(x b)::t. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)
Proof
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw[RES_FORALL_THM] >>
  rw[ITSET_INSERT] >>
  qabbrev_tac `y = CHOICE (x INSERT s)` >>
  qabbrev_tac `z = REST (x INSERT s)` >>
  `y NOTIN z` by metis_tac[CHOICE_NOT_IN_REST] >>
  `!x s. x IN s ==> (x INSERT s = s)` by rw[ABSORPTION] >>
  `!x s. x NOTIN s ==> (s DELETE x = s)` by rw[DELETE_NON_ELEMENT] >>
  Cases_on `x IN s` >| [
    `s = y INSERT z` by metis_tac[NOT_IN_EMPTY, CHOICE_INSERT_REST] >>
    `FINITE z` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
    `CARD s = SUC (CARD z)` by rw[] >>
    `CARD z < CARD s` by decide_tac >>
    `z = s DELETE y` by metis_tac[DELETE_INSERT] >>
    `z SUBSET t` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
    Cases_on `x = y` >- metis_tac[] >>
    `x IN z` by metis_tac[IN_INSERT] >>
    qabbrev_tac `u = z DELETE x` >>
    `z = x INSERT u` by rw[INSERT_DELETE, Abbr`u`] >>
    `x NOTIN u` by metis_tac[IN_DELETE] >>
    qabbrev_tac `v = y INSERT u` >>
    `s = x INSERT v` by simp[INSERT_COMM, Abbr `v`] >>
    `x NOTIN v` by rw[Abbr `v`] >>
    `FINITE v` by metis_tac[FINITE_INSERT] >>
    `CARD s = SUC (CARD v)` by metis_tac[CARD_INSERT] >>
    `CARD v < CARD s` by decide_tac >>
    `v SUBSET t` by metis_tac[INSERT_SUBSET, SUBSET_TRANS] >>
    `s DELETE x = v` by rw[DELETE_INSERT, Abbr `v`] >>
    `v = s DELETE x` by rw[] >>
    `y IN t` by metis_tac[NOT_INSERT_EMPTY, CHOICE_DEF, SUBSET_DEF] >>
    metis_tac[],
    `x INSERT s <> {}` by rw[] >>
    `y INSERT z = x INSERT s` by rw[CHOICE_INSERT_REST, Abbr`y`, Abbr`z`] >>
    Cases_on `x = y` >- metis_tac[DELETE_INSERT, ITSET_PROPERTY] >>
    `x IN z /\ y IN s` by metis_tac[IN_INSERT] >>
    qabbrev_tac `u = s DELETE y` >>
    `s = y INSERT u` by rw[INSERT_DELETE, Abbr`u`] >>
    `y NOTIN u` by metis_tac[IN_DELETE] >>
    `z = x INSERT u` by metis_tac[DELETE_INSERT, INSERT_DELETE] >>
    `x NOTIN u` by metis_tac[IN_DELETE] >>
    `FINITE u` by metis_tac[FINITE_DELETE, SUBSET_FINITE] >>
    `CARD u < CARD s` by rw[] >>
    `u SUBSET t` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
    `y IN t` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
    `f y b IN t /\ f x b IN t` by prove_tac[closure_comm_assoc_fun_def] >>
    `ITSET f z (f y b) = ITSET f (x INSERT u) (f y b)` by rw[] >>
    `_ = ITSET f (u DELETE x) (f x (f y b))` by metis_tac[] >>
    `_ = ITSET f u (f x (f y b))` by rw[] >>
    `ITSET f s (f x b) = ITSET f (y INSERT u) (f x b)` by rw[] >>
    `_ = ITSET f (u DELETE y) (f y (f x b))` by metis_tac[] >>
    `_ = ITSET f u (f y (f x b))` by rw[] >>
    `f x (f y b) = f y (f x b)` by prove_tac[closure_comm_assoc_fun_def] >>
    metis_tac[]
  ]
QED

(* This is a generalisation of COMMUTING_ITSET_INSERT, removing the requirement of commuting everywhere. *)

(* Theorem: FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
            !(x b)::t. ITSET f s (f x b) = f x (ITSET f s b) *)
(* Proof:
   By complete induction on CARD s.
   The goal is to show: ITSET f s (f x b) = f x (ITSET f s b)
   Base: s = {},
      LHS = ITSET f {} (f x b)
          = f x b                          by ITSET_EMPTY
          = f x (ITSET f {} b)             by ITSET_EMPTY
          = RHS
   Step: s <> {},
   Let s = y INSERT z, where y = CHOICE s, z = REST s.
   Then y NOTIN z                          by CHOICE_NOT_IN_REST
    But y IN t                             by CHOICE_DEF, SUBSET_DEF
    and z SUBSET t                         by REST_SUBSET, SUBSET_TRANS
   Also FINITE z                           by REST_SUBSET, SUBSET_FINITE
   Thus CARD s = SUC (CARD z)              by CARD_INSERT
     or CARD z < CARD s
   Note f x b IN t /\ f y b IN t           by closure_comm_assoc_fun_def

     LHS = ITSET f s (f x b)
         = ITSET f (y INSERT z) (f x b)        by s = y INSERT z
         = ITSET f (z DELETE y) (f y (f x b))  by SUBSET_COMMUTING_ITSET_INSERT, y, f x b IN t
         = ITSET f z (f y (f x b))             by DELETE_NON_ELEMENT, y NOTIN z
         = ITSET f z (f x (f y b))             by closure_comm_assoc_fun_def, x, y, b IN t
         = f x (ITSET f z (f y b))             by inductive hypothesis, CARD z < CARD s, x, f y b IN t
         = f x (ITSET f (z DELETE y) (f y b))  by DELETE_NON_ELEMENT, y NOTIN z
         = f x (ITSET f (y INSERT z) b)        by SUBSET_COMMUTING_ITSET_INSERT, y, f y b IN t
         = f x (ITSET f s b)                   by s = y INSERT z
         = RHS
*)
val SUBSET_COMMUTING_ITSET_REDUCTION = store_thm(
  "SUBSET_COMMUTING_ITSET_REDUCTION",
  ``!f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
     !(x b)::t. ITSET f s (f x b) = f x (ITSET f s b)``,
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw[RES_FORALL_THM] >>
  Cases_on `s = {}` >-
  rw[ITSET_EMPTY] >>
  `?y z. (y = CHOICE s) /\ (z = REST s) /\ (s = y INSERT z)` by rw[CHOICE_INSERT_REST] >>
  `y NOTIN z` by metis_tac[CHOICE_NOT_IN_REST] >>
  `y IN t` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
  `z SUBSET t` by metis_tac[REST_SUBSET, SUBSET_TRANS] >>
  `FINITE z` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
  `CARD s = SUC (CARD z)` by rw[] >>
  `CARD z < CARD s` by decide_tac >>
  `f x b IN t /\ f y b IN t /\ (f y (f x b) = f x (f y b))` by prove_tac[closure_comm_assoc_fun_def] >>
  metis_tac[SUBSET_COMMUTING_ITSET_INSERT, DELETE_NON_ELEMENT]);

(* This helps to prove the next generalisation. *)

(* Theorem: FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
            !(x b):: t. ITSET f (x INSERT s) b = f x (ITSET f (s DELETE x) b) *)
(* Proof:
   Note (s DELETE x) SUBSET t       by DELETE_SUBSET, SUBSET_TRANS
    and FINITE (s DELETE x)         by FINITE_DELETE, FINITE s
     ITSET f (x INSERT s) b
   = ITSET f (s DELETE x) (f x b)   by SUBSET_COMMUTING_ITSET_INSERT
   = f x (ITSET f (s DELETE x) b)   by SUBSET_COMMUTING_ITSET_REDUCTION, (s DELETE x) SUBSET t
*)
val SUBSET_COMMUTING_ITSET_RECURSES = store_thm(
  "SUBSET_COMMUTING_ITSET_RECURSES",
  ``!f s t. FINITE s /\ s SUBSET t /\ closure_comm_assoc_fun f t ==>
     !(x b):: t. ITSET f (x INSERT s) b = f x (ITSET f (s DELETE x) b)``,
  rw[RES_FORALL_THM] >>
  `(s DELETE x) SUBSET t` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
  `FINITE (s DELETE x)` by rw[] >>
  metis_tac[SUBSET_COMMUTING_ITSET_INSERT, SUBSET_COMMUTING_ITSET_REDUCTION]);

(* ------------------------------------------------------------------------- *)
(* SUM_IMAGE and PROD_IMAGE Theorems                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SIGMA f {} = 0 *)
(* Proof: by SUM_IMAGE_THM *)
val SUM_IMAGE_EMPTY = store_thm(
  "SUM_IMAGE_EMPTY",
  ``!f. SIGMA f {} = 0``,
  rw[SUM_IMAGE_THM]);

(* Theorem: FINITE s ==> !e. e NOTIN s ==> (SIGMA f (e INSERT s) = f e + (SIGMA f s)) *)
(* Proof:
     SIGMA f (e INSERT s)
   = f e + SIGMA f (s DELETE e)    by SUM_IMAGE_THM
   = f e + SIGMA f s               by DELETE_NON_ELEMENT
*)
val SUM_IMAGE_INSERT = store_thm(
  "SUM_IMAGE_INSERT",
  ``!f s. FINITE s ==> !e. e NOTIN s ==> (SIGMA f (e INSERT s) = f e + (SIGMA f s))``,
  rw[SUM_IMAGE_THM, DELETE_NON_ELEMENT]);

(* Theorem: FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SIGMA I (IMAGE f s)) *)
(* Proof:
   By finite induction on s.
   Base case: SIGMA f {} = SIGMA I {}
        SIGMA f {}
      = 0              by SUM_IMAGE_THM
      = SIGMA I {}     by SUM_IMAGE_THM
      = SUM_SET {}     by SUM_SET_DEF
   Step case: !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SUM_SET (IMAGE f s)) ==>
              e NOTIN s ==> SIGMA f (e INSERT s) = SUM_SET (f e INSERT IMAGE f s)
      Note FINITE s ==> FINITE (IMAGE f s)   by IMAGE_FINITE
       and e NOTIN s ==> f e NOTIN f s       by the injective property
        SIGMA f (e INSERT s)
      = f e + SIGMA f (s DELETE e))    by SUM_IMAGE_THM
      = f e + SIGMA f s                by DELETE_NON_ELEMENT
      = f e + SUM_SET (IMAGE f s))     by induction hypothesis
      = f e + SUM_SET ((IMAGE f s) DELETE (f e))   by DELETE_NON_ELEMENT, f e NOTIN f s
      = SUM_SET (f e INSERT IMAGE f s)             by SUM_SET_THM
*)
val SUM_IMAGE_AS_SUM_SET = store_thm(
  "SUM_IMAGE_AS_SUM_SET",
  ``!s. FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SUM_SET (IMAGE f s))``,
  HO_MATCH_MP_TAC FINITE_INDUCT >>
  rw[SUM_SET_DEF] >-
  rw[SUM_IMAGE_THM] >>
  rw[SUM_IMAGE_THM, SUM_IMAGE_DELETE] >>
  metis_tac[]);

(* Theorem: x <> y ==> SIGMA f {x; y} = f x + f y *)
(* Proof:
   Let s = {x; y}.
   Then FINITE s                   by FINITE_UNION, FINITE_SING
    and x INSERT s                 by INSERT_DEF
    and s DELETE x = {y}           by DELETE_DEF
        SIGMA f s
      = SIGMA f (x INSERT s)       by above
      = f x + SIGMA f (s DELETE x) by SUM_IMAGE_THM
      = f x + SIGMA f {y}          by above
      = f x + f y                  by SUM_IMAGE_SING
*)
Theorem SUM_IMAGE_DOUBLET:
  !f x y. x <> y ==> SIGMA f {x; y} = f x + f y
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {x; y}` >>
  `FINITE s` by fs[Abbr`s`] >>
  `x INSERT s = s` by fs[Abbr`s`] >>
  `s DELETE x = {x; y} DELETE x` by simp[Abbr`s`] >>
  `_ = if y = x then {} else {y}` by EVAL_TAC >>
  `_ = {y}` by simp[] >>
  metis_tac[SUM_IMAGE_THM, SUM_IMAGE_SING]
QED

(* Theorem: x <> y /\ y <> z /\ z <> x ==> SIGMA f {x; y; z} = f x + f y + f z *)
(* Proof:
   Let s = {x; y; z}.
   Then FINITE s                   by FINITE_UNION, FINITE_SING
    and x INSERT s                 by INSERT_DEF
    and s DELETE x = {y; z}        by DELETE_DEF
        SIGMA f s
      = SIGMA f (x INSERT s)       by above
      = f x + SIGMA f (s DELETE x) by SUM_IMAGE_THM
      = f x + SIGMA f {y; z}       by above
      = f x + f y + f z            by SUM_IMAGE_DOUBLET
*)
Theorem SUM_IMAGE_TRIPLET:
  !f x y z. x <> y /\ y <> z /\ z <> x ==> SIGMA f {x; y; z} = f x + f y + f z
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {x; y; z}` >>
  `FINITE s` by fs[Abbr`s`] >>
  `x INSERT s = s` by fs[Abbr`s`] >>
  `s DELETE x = {x; y; z} DELETE x` by simp[Abbr`s`] >>
  `_ = if y = x then if z = x then {} else {z}
      else y INSERT if z = x then {} else {z}` by EVAL_TAC >>
  `_ = {y; z}` by simp[] >>
  `SIGMA f s = f x + (f y + f z)` by metis_tac[SUM_IMAGE_THM, SUM_IMAGE_DOUBLET, SUM_IMAGE_SING] >>
  decide_tac
QED

(* Theorem: FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s) *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f {} = k * CARD {}
        SIGMA f {}
      = 0              by SUM_IMAGE_EMPTY
      = k * 0          by MULT_0
      = k * CARD {}    by CARD_EMPTY
   Step: SIGMA f s = k * CARD s /\ e NOTIN s /\ !x. x IN e INSERT s /\ f x = k ==>
         SIGMA f (e INSERT s) = k * CARD (e INSERT s)
      Note f e = k /\ !x. x IN s ==> f x = k   by IN_INSERT
        SIGMA f (e INSERT s)
      = f e + SIGMA f (s DELETE e)     by SUM_IMAGE_THM
      = k + SIGMA f s                  by DELETE_NON_ELEMENT, f e = k
      = k + k * CARD s                 by induction hypothesis
      = k * (1 + CARD s)               by LEFT_ADD_DISTRIB
      = k * SUC (CARD s)               by SUC_ONE_ADD
      = k * CARD (e INSERT s)          by CARD_INSERT
*)
val SIGMA_CONSTANT = store_thm(
  "SIGMA_CONSTANT",
  ``!s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (SIGMA f s = k * CARD s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  `(f e = k) /\ !x. x IN s ==> (f x = k)` by rw[] >>
  `SIGMA f (e INSERT s) = f e + SIGMA f (s DELETE e)` by rw[SUM_IMAGE_THM] >>
  `_ = k + SIGMA f s` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = k + k * CARD s` by rw[] >>
  `_ = k * (1 + CARD s)` by rw[] >>
  `_ = k * SUC (CARD s)` by rw[ADD1] >>
  `_ = k * CARD (e INSERT s)` by rw[CARD_INSERT] >>
  rw[]);

(* Theorem: FINITE s ==> !c. SIGMA (K c) s = c * CARD s *)
(* Proof: by SIGMA_CONSTANT. *)
val SUM_IMAGE_CONSTANT = store_thm(
  "SUM_IMAGE_CONSTANT",
  ``!s. FINITE s ==> !c. SIGMA (K c) s = c * CARD s``,
  rw[SIGMA_CONSTANT]);

(* Idea: If !e. e IN s, CARD e = n, SIGMA CARD s = n * CARD s. *)

(* Theorem: FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s *)
(* Proof: by SIGMA_CONSTANT, take f = CARD. *)
Theorem SIGMA_CARD_CONSTANT:
  !n s. FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s
Proof
  simp[SIGMA_CONSTANT]
QED

(* Theorem alias, or rename SIGMA_CARD_CONSTANT *)
Theorem SIGMA_CARD_SAME_SIZE_SETS = SIGMA_CARD_CONSTANT;
(* val SIGMA_CARD_SAME_SIZE_SETS =
   |- !n s. FINITE s /\ (!e. e IN s ==> CARD e = n) ==> SIGMA CARD s = n * CARD s: thm *)
(*
CARD_BIGUNION_SAME_SIZED_SETS
|- !n s. FINITE s /\ (!e. e IN s ==> FINITE e /\ CARD e = n) /\
         PAIR_DISJOINT s ==> CARD (BIGUNION s) = CARD s * n
*)

(* Theorem: If n divides CARD e for all e in s, then n divides SIGMA CARD s.
            FINITE s /\ (!e. e IN s ==> n divides (CARD e)) ==> n divides (SIGMA CARD s) *)
(* Proof:
   Use finite induction and SUM_IMAGE_THM.
   Base: n divides SIGMA CARD {}
         Note SIGMA CARD {} = 0        by SUM_IMAGE_THM
          and n divides 0              by ALL_DIVIDES_0
   Step: e NOTIN s /\ n divides (CARD e) ==> n divides SIGMA CARD (e INSERT s)
           SIGMA CARD (e INSERT s)
         = CARD e + SIGMA CARD (s DELETE e)      by SUM_IMAGE_THM
         = CARD e + SIGMA CARD s                 by DELETE_NON_ELEMENT
         Note n divides (CARD e)                 by given
          and n divides SIGMA CARD s             by induction hypothesis
         Thus n divides SIGMA CARD (e INSERT s)  by DIVIDES_ADD_1
*)
Theorem SIGMA_CARD_FACTOR:
  !n s. FINITE s /\ (!e. e IN s ==> n divides (CARD e)) ==> n divides (SIGMA CARD s)
Proof
  strip_tac >>
  Induct_on `FINITE` >>
  rw[] >-
  rw[SUM_IMAGE_THM] >>
  metis_tac[SUM_IMAGE_THM, DELETE_NON_ELEMENT, DIVIDES_ADD_1]
QED

(* Theorem: (!x. x IN s ==> (f1 x = f2 x)) ==> (SIGMA f1 s = SIGMA f2 s) *)
val SIGMA_CONG = store_thm(
  "SIGMA_CONG",
  ``!s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (SIGMA f1 s = SIGMA f2 s)``,
  rw[SUM_IMAGE_CONG]);

(* Theorem: FINITE s ==> (CARD s = SIGMA (\x. 1) s) *)
(* Proof:
   By finite induction:
   Base case: CARD {} = SIGMA (\x. 1) {}
     LHS = CARD {}
         = 0                 by CARD_EMPTY
     RHS = SIGMA (\x. 1) {}
         = 0 = LHS           by SUM_IMAGE_THM
   Step case: (CARD s = SIGMA (\x. 1) s) ==>
              !e. e NOTIN s ==> (CARD (e INSERT s) = SIGMA (\x. 1) (e INSERT s))
     CARD (e INSERT s)
   = SUC (CARD s)                             by CARD_DEF
   = SUC (SIGMA (\x. 1) s)                    by induction hypothesis
   = 1 + SIGMA (\x. 1) s                      by ADD1, ADD_COMM
   = (\x. 1) e + SIGMA (\x. 1) s              by function application
   = (\x. 1) e + SIGMA (\x. 1) (s DELETE e)   by DELETE_NON_ELEMENT
   = SIGMA (\x. 1) (e INSERT s)               by SUM_IMAGE_THM
*)
val CARD_AS_SIGMA = store_thm(
  "CARD_AS_SIGMA",
  ``!s. FINITE s ==> (CARD s = SIGMA (\x. 1) s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  conj_tac >-
  rw[SUM_IMAGE_THM] >>
  rpt strip_tac >>
  `CARD (e INSERT s) = SUC (SIGMA (\x. 1) s)` by rw[] >>
  `_ = 1 + SIGMA (\x. 1) s` by rw_tac std_ss[ADD1, ADD_COMM] >>
  `_ = (\x. 1) e + SIGMA (\x. 1) s` by rw[] >>
  `_ = (\x. 1) e + SIGMA (\x. 1) (s DELETE e)` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = SIGMA (\x. 1) (e INSERT s)` by rw[SUM_IMAGE_THM] >>
  decide_tac);

(* Theorem: FINITE s ==> (CARD s = SIGMA (K 1) s) *)
(* Proof: by CARD_AS_SIGMA, SIGMA_CONG *)
val CARD_EQ_SIGMA = store_thm(
  "CARD_EQ_SIGMA",
  ``!s. FINITE s ==> (CARD s = SIGMA (K 1) s)``,
  rw[CARD_AS_SIGMA, SIGMA_CONG]);

(* Theorem: FINITE s ==> !f g. (!x. x IN s ==> f x <= g x) ==> (SIGMA f s <= SIGMA g s) *)
(* Proof:
   By finite induction:
   Base case: !f g. (!x. x IN {} ==> f x <= g x) ==> SIGMA f {} <= SIGMA g {}
      True since SIGMA f {} = 0      by SUM_IMAGE_THM
   Step case: !f g. (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s ==>
    e NOTIN s ==>
    !x. x IN e INSERT s ==> f x <= g x ==> !f g. SIGMA f (e INSERT s) <= SIGMA g (e INSERT s)
           SIGMA f (e INSERT s) <= SIGMA g (e INSERT s)
    means  f e + SIGMA f (s DELETE e) <= g e + SIGMA g (s DELETE e)    by SUM_IMAGE_THM
       or  f e + SIGMA f s <= g e + SIGMA g s                          by DELETE_NON_ELEMENT
    Now, x IN e INSERT s ==> (x = e) or (x IN s)         by IN_INSERT
    Therefore  f e <= g e, and !x IN s, f x <= g x       by x IN (e INSERT s) implication
    or         f e <= g e, and SIGMA f s <= SIGMA g s    by induction hypothesis
    Hence      f e + SIGMA f s <= g e + SIGMA g s        by arithmetic
*)
val SIGMA_LE_SIGMA = store_thm(
  "SIGMA_LE_SIGMA",
  ``!s. FINITE s ==> !f g. (!x. x IN s ==> f x <= g x) ==> (SIGMA f s <= SIGMA g s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  conj_tac >-
  rw[SUM_IMAGE_THM] >>
  rw[SUM_IMAGE_THM, DELETE_NON_ELEMENT] >>
  `f e <= g e /\ SIGMA f s <= SIGMA g s` by rw[] >>
  decide_tac);

(* Theorem: FINITE s /\ FINITE t ==> !f. SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t *)
(* Proof:
   Note SIGMA f (s UNION t)
      = SIGMA f s + SIGMA f t - SIGMA f (s INTER t)    by SUM_IMAGE_UNION
    now s INTER t SUBSET s /\ s INTER t SUBSET t       by INTER_SUBSET
     so SIGMA f (s INTER t) <= SIGMA f s               by SUM_IMAGE_SUBSET_LE
    and SIGMA f (s INTER t) <= SIGMA f t               by SUM_IMAGE_SUBSET_LE
   thus SIGMA f (s INTER t) <= SIGMA f s + SIGMA f t   by arithmetic
   The result follows                                  by ADD_EQ_SUB
*)
val SUM_IMAGE_UNION_EQN = store_thm(
  "SUM_IMAGE_UNION_EQN",
  ``!s t. FINITE s /\ FINITE t ==> !f. SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t``,
  rpt strip_tac >>
  `SIGMA f (s UNION t) = SIGMA f s + SIGMA f t - SIGMA f (s INTER t)` by rw[SUM_IMAGE_UNION] >>
  `SIGMA f (s INTER t) <= SIGMA f s` by rw[SUM_IMAGE_SUBSET_LE, INTER_SUBSET] >>
  `SIGMA f (s INTER t) <= SIGMA f t` by rw[SUM_IMAGE_SUBSET_LE, INTER_SUBSET] >>
  `SIGMA f (s INTER t) <= SIGMA f s + SIGMA f t` by decide_tac >>
  rw[ADD_EQ_SUB]);

(* Theorem: FINITE s /\ FINITE t /\ DISJOINT s t ==> !f. SIGMA f (s UNION t) = SIGMA f s + SIGMA f t *)
(* Proof:
     SIGMA f (s UNION t)
   = SIGMA f s + SIGMA f t - SIGMA f (s INTER t)    by SUM_IMAGE_UNION
   = SIGMA f s + SIGMA f t - SIGMA f {}             by DISJOINT_DEF
   = SIGMA f s + SIGMA f t - 0                      by SUM_IMAGE_EMPTY
   = SIGMA f s + SIGMA f t                          by arithmetic
*)
val SUM_IMAGE_DISJOINT = store_thm(
  "SUM_IMAGE_DISJOINT",
  ``!s t. FINITE s /\ FINITE t /\ DISJOINT s t ==> !f. SIGMA f (s UNION t) = SIGMA f s + SIGMA f t``,
  rw_tac std_ss[SUM_IMAGE_UNION, DISJOINT_DEF, SUM_IMAGE_EMPTY]);

(* Theorem: FINITE s /\ s <> {} ==> !f g. (!x. x IN s ==> f x < g x) ==> SIGMA f s < SIGMA g s *)
(* Proof:
   Note s <> {} ==> ?x. x IN s       by MEMBER_NOT_EMPTY
   Thus ?x. x IN s /\ f x < g x      by implication
    and !x. x IN s ==> f x <= g x    by LESS_IMP_LESS_OR_EQ
    ==> SIGMA f s < SIGMA g s        by SUM_IMAGE_MONO_LESS
*)
val SUM_IMAGE_MONO_LT = store_thm(
  "SUM_IMAGE_MONO_LT",
  ``!s. FINITE s /\ s <> {} ==> !f g. (!x. x IN s ==> f x < g x) ==> SIGMA f s < SIGMA g s``,
  metis_tac[SUM_IMAGE_MONO_LESS, LESS_IMP_LESS_OR_EQ, MEMBER_NOT_EMPTY]);

(* Theorem: FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==> SIGMA f t < SIGMA f s *)
(* Proof:
   Note t SUBSET s /\ t <> s      by PSUBSET_DEF
   Thus SIGMA f t <= SIGMA f s    by SUM_IMAGE_SUBSET_LE
   By contradiction, suppose ~(SIGMA f t < SIGMA f s).
   Then SIGMA f t = SIGMA f s     by arithmetic [1]

   Let u = s DIFF t.
   Then DISJOINT u t                        by DISJOINT_DIFF
    and u UNION t = s                       by UNION_DIFF
   Note FINITE u /\ FINITE t                by FINITE_UNION
    ==> SIGMA f s = SIGMA f u + SIGMA f t   by SUM_IMAGE_DISJOINT
   Thus SIGMA f u = 0                       by arithmetic, [1]

    Now u SUBSET s                          by SUBSET_UNION
    and u <> {}                             by finite_partition_property, t <> s
   Thus ?x. x IN u                          by MEMBER_NOT_EMPTY
    and f x <> 0                            by SUBSET_DEF, implication
   This contradicts f x = 0                 by SUM_IMAGE_ZERO
*)
val SUM_IMAGE_PSUBSET_LT = store_thm(
  "SUM_IMAGE_PSUBSET_LT",
  ``!f s t. FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==> SIGMA f t < SIGMA f s``,
  rw[PSUBSET_DEF] >>
  `SIGMA f t <= SIGMA f s` by rw[SUM_IMAGE_SUBSET_LE] >>
  spose_not_then strip_assume_tac >>
  `SIGMA f t = SIGMA f s` by decide_tac >>
  qabbrev_tac `u = s DIFF t` >>
  `DISJOINT u t` by rw[DISJOINT_DIFF, Abbr`u`] >>
  `u UNION t = s` by rw[UNION_DIFF, Abbr`u`] >>
  `FINITE u /\ FINITE t` by metis_tac[FINITE_UNION] >>
  `SIGMA f s = SIGMA f u + SIGMA f t` by rw[GSYM SUM_IMAGE_DISJOINT] >>
  `SIGMA f u = 0` by decide_tac >>
  `u SUBSET s` by rw[] >>
  `u <> {}` by metis_tac[finite_partition_property] >>
  metis_tac[SUM_IMAGE_ZERO, SUBSET_DEF, MEMBER_NOT_EMPTY]);

(* Idea: Let s be a set of sets. If CARD s = SIGMA CARD s,
         and all elements in s are non-empty, then all elements in s are SING. *)

(* Theorem: FINITE s /\ (!e. e IN s ==> CARD e <> 0) ==> CARD s <= SIGMA CARD s *)
(* Proof:
   By finite induction on set s.
   Base: (!e. e IN {} ==> CARD e <> 0) ==> CARD {} <= SIGMA CARD {}
      LHS = CARD {} = 0            by CARD_EMPTY
      RHS = SIGMA CARD {} = 0      by SUM_IMAGE_EMPTY
      Hence true.
   Step: FINITE s /\ ((!e. e IN s ==> CARD e <> 0) ==> CARD s <= SIGMA CARD s) ==>
         !e. e NOTIN s ==>
             (!e'. e' IN e INSERT s ==> CARD e' <> 0) ==>
             CARD (e INSERT s) <= SIGMA CARD (e INSERT s)

      Note !e'. e' IN s
            ==> e' IN e INSERT s   by IN_INSERT, e NOTIN s
            ==> CARD e' <> 0       by implication, so induction hypothesis applies.
       and CARD e <> 0             by e IN e INSERT s
            CARD (e INSERT s)
          = SUC (CARD s)           by CARD_INSERT, e NOTIN s
          = 1 + CARD s             by SUC_ONE_ADD

         <= 1 + SIGMA CARD s       by induction hypothesis
         <= CARD e + SIGMA CARD s  by 1 <= CARD e
          = SIGMA (e INSERT s)     by SUM_IMAGE_INSERT, e NOTIN s.
*)
Theorem card_le_sigma_card:
  !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) ==> CARD s <= SIGMA CARD s
Proof
  Induct_on `FINITE` >>
  rw[] >>
  `CARD e <> 0` by fs[] >>
  `1 <= CARD e` by decide_tac >>
  fs[] >>
  simp[SUM_IMAGE_INSERT]
QED

(* Theorem: FINITE s /\ (!e. e IN s ==> CARD e <> 0) /\
            CARD s = SIGMA CARD s ==> !e. e IN s ==> CARD e = 1 *)
(* Proof:
   By finite induction on set s.
   Base: (!e. e IN {} ==> CARD e <> 0) /\ CARD {} = SIGMA CARD {} ==>
         !e. e IN {} ==> CARD e = 1
      Since e IN {} = F, this is trivially true.
   Step: !s. FINITE s /\
             ((!e. e IN s ==> CARD e <> 0) /\ CARD s = SIGMA CARD s ==>
              !e. e IN s ==> CARD e = 1) ==>
         !e. e NOTIN s ==>
             (!e'. e' IN e INSERT s ==> CARD e' <> 0) /\
             CARD (e INSERT s) = SIGMA CARD (e INSERT s) ==>
             !e'. e' IN e INSERT s ==> CARD e' = 1
      Note !e'. e' IN s
           ==> e' IN e INSERT s    by IN_INSERT, e NOTIN s
           ==> CARD e' <> 0        by implication, helps in induction hypothesis
      Also e IN e INSERT s         by IN_INSERT
        so CARD e <> 0             by implication

           CARD e + CARD s
        <= CARD e + SIGMA CARD s   by card_le_sigma_card
         = SIGMA CARD (e INSERT s) by SUM_IMAGE_INSERT, e NOTIN s
         = CARD (e INSERT s)       by given
         = SUC (CARD s)            by CARD_INSERT, e NOTIN s
         = 1 + CARD s              by SUC_ONE_ADD
      Thus CARD e <= 1             by arithmetic
        or CARD e = 1              by CARD e <> 0
       ==> CARD s = SIGMA CARD s   by arithmetic, helps in induction hypothesis
      Thus !e. e IN s ==> CARD e = 1               by induction hypothesis
      and  !e'. e' IN e INSERT s ==> CARD e' = 1   by CARD e = 1
*)
Theorem card_eq_sigma_card:
  !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) /\
      CARD s = SIGMA CARD s ==> !e. e IN s ==> CARD e = 1
Proof
  Induct_on `FINITE` >>
  simp[] >>
  ntac 6 strip_tac >>
  `CARD e <> 0 /\ !e. e IN s ==> CARD e <> 0` by fs[] >>
  imp_res_tac card_le_sigma_card >>
  `CARD e + CARD s <= CARD e + SIGMA CARD s` by decide_tac >>
  `CARD e + SIGMA CARD s = SIGMA CARD (e INSERT s)` by fs[SUM_IMAGE_INSERT] >>
  `_ = 1 + CARD s` by rw[] >>
  `CARD e <= 1` by fs[] >>
  `CARD e = 1` by decide_tac >>
  `CARD s = SIGMA CARD s` by fs[] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)

(* Theorem: PI f {} = 1 *)
(* Proof: by PROD_IMAGE_THM *)
val PROD_IMAGE_EMPTY = store_thm(
  "PROD_IMAGE_EMPTY",
  ``!f. PI f {} = 1``,
  rw[PROD_IMAGE_THM]);

(* Theorem: FINITE s ==> !f e. e NOTIN s ==> (PI f (e INSERT s) = (f e) * PI f s) *)
(* Proof: by PROD_IMAGE_THM, DELETE_NON_ELEMENT *)
val PROD_IMAGE_INSERT = store_thm(
  "PROD_IMAGE_INSERT",
  ``!s. FINITE s ==> !f e. e NOTIN s ==> (PI f (e INSERT s) = (f e) * PI f s)``,
  rw[PROD_IMAGE_THM, DELETE_NON_ELEMENT]);

(* Theorem: FINITE s ==> !f e. 0 < f e ==>
            (PI f (s DELETE e) = if e IN s then ((PI f s) DIV (f e)) else PI f s) *)
(* Proof:
   If e IN s,
     Note PI f (e INSERT s) = (f e) *  PI f (s DELETE e)   by PROD_IMAGE_THM
     Thus PI f (s DELETE e) = PI f (e INSERT s) DIV (f e)  by DIV_SOLVE_COMM, 0 < f e
                            = (PI f s) DIV (f e)           by ABSORPTION, e IN s.
   If e NOTIN s,
      PI f (s DELETE e) = PI f e                           by DELETE_NON_ELEMENT
*)
val PROD_IMAGE_DELETE = store_thm(
  "PROD_IMAGE_DELETE",
  ``!s. FINITE s ==> !f e. 0 < f e ==>
       (PI f (s DELETE e) = if e IN s then ((PI f s) DIV (f e)) else PI f s)``,
  rpt strip_tac >>
  rw_tac std_ss[] >-
  metis_tac[PROD_IMAGE_THM, DIV_SOLVE_COMM, ABSORPTION] >>
  metis_tac[DELETE_NON_ELEMENT]);
(* The original proof of SUM_IMAGE_DELETE is clumsy. *)

(* Theorem: (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s) *)
(* Proof:
   If INFINITE s,
        PI f1 s
      = ITSET (\e acc. f e * acc) s 1    by PROD_IMAGE_DEF
      = ARB                              by ITSET_def
      Similarly, PI f2 s = ARB = PI f1 s.
   If FINITE s,
      Apply finite induction on s.
      Base: PI f1 {} = PI f2 {}, true     by PROD_IMAGE_EMPTY
      Step: !f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s) ==>
            e NOTIN s /\ !x. x IN e INSERT s ==> (f1 x = f2 x) ==> PI f1 (e INSERT s) = PI f2 (e INSERT s)
            Note !x. x IN e INSERT s ==> (f1 x = f2 x)
             ==> (f1 e = f2 e) \/ !x. s IN s ==> (f1 x = f2 x)   by IN_INSERT
              PI f1 (e INSERT s)
            = (f1 e) * (PI f1 s)    by PROD_IMAGE_INSERT, e NOTIN s
            = (f1 e) * (PI f2 s)    by induction hypothesis
            = (f2 e) * (PI f2 s)    by f1 e = f2 e
            = PI f2 (e INSERT s)    by PROD_IMAGE_INSERT, e NOTIN s
*)
val PROD_IMAGE_CONG = store_thm(
  "PROD_IMAGE_CONG",
  ``!s f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)``,
  rpt strip_tac >>
  reverse (Cases_on `FINITE s`) >| [
    rw[PROD_IMAGE_DEF, Once ITSET_def] >>
    rw[Once ITSET_def],
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    qid_spec_tac `s` >>
    `!s. FINITE s ==> !f1 f2. (!x. x IN s ==> (f1 x = f2 x)) ==> (PI f1 s = PI f2 s)` suffices_by rw[] >>
    Induct_on `FINITE` >>
    rpt strip_tac >-
    rw[PROD_IMAGE_EMPTY] >>
    metis_tac[PROD_IMAGE_INSERT, IN_INSERT]
  ]);

(* Theorem: FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s) *)
(* Proof:
   By finite induction on s.
   Base: PI f {} = k ** CARD {}
         PI f {}
       = 1               by PROD_IMAGE_THM
       = c ** 0          by EXP
       = c ** CARD {}    by CARD_DEF
   Step: !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s) ==>
         e NOTIN s ==> PI f (e INSERT s) = k ** CARD (e INSERT s)
         PI f (e INSERT s)
       = ((f e) * PI (K c) (s DELETE e)    by PROD_IMAGE_THM
       = c * PI (K c) (s DELETE e)         by function application
       = c * PI (K c) s                    by DELETE_NON_ELEMENT
       = c * c ** CARD s                   by induction hypothesis
       = c ** (SUC (CARD s))               by EXP
       = c ** CARD (e INSERT s)            by CARD_INSERT, e NOTIN s
*)
val PI_CONSTANT = store_thm(
  "PI_CONSTANT",
  ``!s. FINITE s ==> !f k. (!x. x IN s ==> (f x = k)) ==> (PI f s = k ** CARD s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_IMAGE_THM] >>
  rw[PROD_IMAGE_THM, CARD_INSERT] >>
  fs[] >>
  metis_tac[DELETE_NON_ELEMENT, EXP]);

(* Theorem: FINITE s ==> !c. PI (K c) s = c ** (CARD s) *)
(* Proof: by PI_CONSTANT. *)
val PROD_IMAGE_CONSTANT = store_thm(
  "PROD_IMAGE_CONSTANT",
  ``!s. FINITE s ==> !c. PI (K c) s = c ** (CARD s)``,
  rw[PI_CONSTANT]);

(* ------------------------------------------------------------------------- *)
(* SUM_SET and PROD_SET Theorems                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ x NOTIN s ==> (SUM_SET (x INSERT s) = x + SUM_SET s) *)
(* Proof:
     SUM_SET (x INSERT s)
   = x + SUM_SET (s DELETE x)  by SUM_SET_THM
   = x + SUM_SET s             by DELETE_NON_ELEMENT
*)
val SUM_SET_INSERT = store_thm(
  "SUM_SET_INSERT",
  ``!s x. FINITE s /\ x NOTIN s ==> (SUM_SET (x INSERT s) = x + SUM_SET s)``,
  rw[SUM_SET_THM, DELETE_NON_ELEMENT]);

(* Theorem: FINITE s ==> !f. INJ f s UNIV ==> (SUM_SET (IMAGE f s) = SIGMA f s) *)
(* Proof:
   By finite induction on s.
   Base: SUM_SET (IMAGE f {}) = SIGMA f {}
         SUM_SET (IMAGE f {})
       = SUM_SET {}                  by IMAGE_EMPTY
       = 1                           by SUM_SET_EMPTY
       = SIGMA f {}                  by SUM_IMAGE_EMPTY
   Step: !f. INJ f s univ(:num) ==> (SUM_SET (IMAGE f s) = SIGMA f s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) ==> SUM_SET (IMAGE f (e INSERT s)) = SIGMA f (e INSERT s)
       Note INJ f s univ(:num)               by INJ_INSERT
        and f e NOTIN (IMAGE f s)            by IN_IMAGE
         SUM_SET (IMAGE f (e INSERT s))
       = SUM_SET (f e INSERT (IMAGE f s))    by IMAGE_INSERT
       = f e * SUM_SET (IMAGE f s)           by SUM_SET_INSERT
       = f e * SIGMA f s                     by induction hypothesis
       = SIGMA f (e INSERT s)                by SUM_IMAGE_INSERT
*)
val SUM_SET_IMAGE_EQN = store_thm(
  "SUM_SET_IMAGE_EQN",
  ``!s. FINITE s ==> !f. INJ f s UNIV ==> (SUM_SET (IMAGE f s) = SIGMA f s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[SUM_SET_EMPTY, SUM_IMAGE_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  rw[SUM_SET_INSERT, SUM_IMAGE_INSERT]);

(* Theorem: SUM_SET (count n) = (n * (n - 1)) DIV 2*)
(* Proof:
   By induction on n.
   Base case: SUM_SET (count 0) = 0 * (0 - 1) DIV 2
     LHS = SUM_SET (count 0)
         = SUM_SET {}           by COUNT_ZERO
         = 0                    by SUM_SET_THM
         = 0 DIV 2              by ZERO_DIV
         = 0 * (0 - 1) DIV 2    by MULT
         = RHS
   Step case: SUM_SET (count n) = n * (n - 1) DIV 2 ==>
              SUM_SET (count (SUC n)) = SUC n * (SUC n - 1) DIV 2
     If n = 0, to show: SUM_SET (count 1) = 0
        SUM_SET (count 1) = SUM_SET {0} = 0  by SUM_SET_SING
     If n <> 0, 0 < n.
     First, FINITE (count n)               by FINITE_COUNT
            n NOTIN (count n)              by IN_COUNT
     LHS = SUM_SET (count (SUC n))
         = SUM_SET (n INSERT count n)      by COUNT_SUC
         = n + SUM_SET (count n DELETE n)  by SUM_SET_THM
         = n + SUM_SET (count n)           by DELETE_NON_ELEMENT
         = n + n * (n - 1) DIV 2           by induction hypothesis
         = (n * 2 + n * (n - 1)) DIV 2     by ADD_DIV_ADD_DIV
         = (n * (2 + (n - 1))) DIV 2       by LEFT_ADD_DISTRIB
         = n * (n + 1) DIV 2               by arithmetic, 0 < n
         = (SUC n - 1) * (SUC n) DIV 2     by ADD1, SUC_SUB1
         = SUC n * (SUC n - 1) DIV 2       by MULT_COMM
         = RHS
*)
val SUM_SET_COUNT = store_thm(
  "SUM_SET_COUNT",
  ``!n. SUM_SET (count n) = (n * (n - 1)) DIV 2``,
  Induct_on `n` >-
  rw[] >>
  Cases_on `n = 0` >| [
    rw[] >>
    EVAL_TAC,
    `0 < n` by decide_tac >>
    `FINITE (count n)` by rw[] >>
    `n NOTIN (count n)` by rw[] >>
    `SUM_SET (count (SUC n)) = SUM_SET (n INSERT count n)` by rw[COUNT_SUC] >>
    `_ = n + SUM_SET (count n DELETE n)` by rw[SUM_SET_THM] >>
    `_ = n + SUM_SET (count n)` by metis_tac[DELETE_NON_ELEMENT] >>
    `_ = n + n * (n - 1) DIV 2` by rw[] >>
    `_ = (n * 2 + n * (n - 1)) DIV 2` by rw[ADD_DIV_ADD_DIV] >>
    `_ = (n * (2 + (n - 1))) DIV 2` by rw[LEFT_ADD_DISTRIB] >>
    `_ = n * (n + 1) DIV 2` by rw_tac arith_ss[] >>
    `_ = (SUC n - 1) * SUC n DIV 2` by rw[ADD1, SUC_SUB1] >>
    `_ = SUC n * (SUC n - 1) DIV 2 ` by rw[MULT_COMM] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)

(* Theorem: PROD_SET {x} = x *)
(* Proof:
   Since FINITE {x}           by FINITE_SING
     PROD_SET {x}
   = PROD_SET (x INSERT {})   by SING_INSERT
   = x * PROD_SET {}          by PROD_SET_THM
   = x                        by PROD_SET_EMPTY
*)
val PROD_SET_SING = store_thm(
  "PROD_SET_SING",
  ``!x. PROD_SET {x} = x``,
  rw[PROD_SET_THM, FINITE_SING]);

(* Theorem: FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: 0 NOTIN {} ==> 0 < PROD_SET {}
     Since PROD_SET {} = 1        by PROD_SET_THM
     Hence true.
   Step case: 0 NOTIN s ==> 0 < PROD_SET s ==>
              e NOTIN s /\ 0 NOTIN e INSERT s ==> 0 < PROD_SET (e INSERT s)
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)          by PROD_SET_THM
     = e * PROD_SET s                     by DELETE_NON_ELEMENT
     But e IN e INSERT s                  by COMPONENT
     Hence e <> 0, or 0 < e               by implication
     and !x. x IN s ==> x IN (e INSERT s) by IN_INSERT
     Thus 0 < PROD_SET s                  by induction hypothesis
     Henec 0 < e * PROD_SET s             by ZERO_LESS_MULT
*)
val PROD_SET_NONZERO = store_thm(
  "PROD_SET_NONZERO",
  ``!s. FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s``,
  `!s. FINITE s ==> 0 NOTIN s ==> 0 < PROD_SET s` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[PROD_SET_THM] >>
  fs[] >>
  `0 < e` by decide_tac >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[ZERO_LESS_MULT]);

(* Theorem: FINITE s /\ s <> {} /\ 0 NOTIN s ==>
            !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: {} <> {} ==> PROD_SET {} < PROD_SET (IMAGE f {})
     True since {} <> {} is false.
   Step case: s <> {} /\ 0 NOTIN s ==> !f. INJ f s univ(:num) ==> PROD_SET s < PROD_SET (IMAGE f s) ==>
              e NOTIN s /\ e INSERT s <> {} /\ 0 NOTIN e INSERT s /\ INJ f (e INSERT s) univ(:num) ==>
              PROD_SET (e INSERT s) < PROD_SET (IMAGE f (e INSERT s))
     Note INJ f (e INSERT s) univ(:num)
      ==> INJ f s univ(:num) /\
          !y. y IN s /\ (f e = f y) ==> (e = y)   by INJ_INSERT
     First,
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)           by PROD_SET_THM
     = e * PROD_SET s                      by DELETE_NON_ELEMENT
     Next,
       FINITE (IMAGE f s)                  by IMAGE_FINITE
       f e NOTIN IMAGE f s                 by IN_IMAGE, e NOTIN s
       PROD_SET (IMAGE f (e INSERT s))
     = f e * PROD_SET (IMAGE f s)          by PROD_SET_IMAGE_REDUCTION

     If s = {},
        to show: e * PROD_SET {} < f e * PROD_SET {}    by IMAGE_EMPTY
        which is true since PROD_SET {} = 1             by PROD_SET_THM
             and e < f e                                by given
     If s <> {},
     Since e IN e INSERT s                              by COMPONENT
     Hence 0 < e                                        by e <> 0
     and !x. x IN s ==> x IN (e INSERT s)               by IN_INSERT
     Thus PROD_SET s < PROD_SET (IMAGE f s)             by induction hypothesis
       or e * PROD_SET s < e * PROD_SET (IMAGE f s)     by LT_MULT_LCANCEL, 0 < e
     Note 0 < PROD_SET (IMAGE f s)                      by IN_IMAGE, !x. x < f x /\ x <> 0
       so e * PROD_SET (IMAGE f s) < f e * PROD_SET (IMAGE f s) by LT_MULT_LCANCEL, e < f e
     Hence PROD_SET (e INSERT s) < PROD_SET (IMAGE f (e INSERT s))
*)
val PROD_SET_LESS = store_thm(
  "PROD_SET_LESS",
  ``!s. FINITE s /\ s <> {} /\ 0 NOTIN s ==>
   !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)``,
  `!s. FINITE s ==> s <> {} /\ 0 NOTIN s ==>
    !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  fs[INJ_INSERT] >>
  `FINITE (IMAGE f s)` by rw[] >>
  `f e NOTIN IMAGE f s` by metis_tac[IN_IMAGE] >>
  `PROD_SET (IMAGE f (e INSERT s)) = f e * PROD_SET (IMAGE f s)` by rw[PROD_SET_IMAGE_REDUCTION] >>
  Cases_on `s = {}` >-
  rw[PROD_SET_SING, PROD_SET_THM] >>
  `0 < e` by decide_tac >>
  `PROD_SET s < PROD_SET (IMAGE f s)` by rw[] >>
  `e * PROD_SET s < e * PROD_SET (IMAGE f s)` by rw[] >>
  `e * PROD_SET (IMAGE f s) < (f e) * PROD_SET (IMAGE f s)` by rw[] >>
  `(IMAGE f (e INSERT s)) = (f e INSERT IMAGE f s)` by rw[] >>
  metis_tac[LESS_TRANS]);

(* Theorem: FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s) *)
(* Proof:
   Since !m n. SUC m = SUC n <=> m = n      by INV_SUC
    thus INJ INJ SUC s univ(:num)           by INJ_DEF
   Hence the result follows                 by PROD_SET_LESS
*)
val PROD_SET_LESS_SUC = store_thm(
  "PROD_SET_LESS_SUC",
  ``!s. FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s)``,
  rpt strip_tac >>
  (irule PROD_SET_LESS >> simp[]) >>
  rw[INJ_DEF]);

(* Theorem: FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: x IN {} /\ n divides x ==> n divides (PROD_SET {})
     True since x IN {} is false   by NOT_IN_EMPTY
   Step case: !n x. x IN s /\ n divides x ==> n divides (PROD_SET s) ==>
              e NOTIN s /\ x IN e INSERT s /\ n divides x ==> n divides (PROD_SET (e INSERT s))
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)   by PROD_SET_THM
     = e * PROD_SET s              by DELETE_NON_ELEMENT
     If x = e,
        n divides x
        means n divides e
        hence n divides PROD_SET (e INSERT s)   by DIVIDES_MULTIPLE, MULT_COMM
     If x <> e, x IN s             by IN_INSERT
        n divides (PROD_SET s)     by induction hypothesis
        hence n divides PROD_SET (e INSERT s)   by DIVIDES_MULTIPLE
*)
val PROD_SET_DIVISORS = store_thm(
  "PROD_SET_DIVISORS",
  ``!s. FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[NOT_IN_EMPTY] >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  `(x = e) \/ (x IN s)` by rw[GSYM IN_INSERT] >-
  metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
  metis_tac[DIVIDES_MULTIPLE]);

(* PROD_SET_IMAGE_REDUCTION |> ISPEC ``I:num -> num``; *)

(* Theorem: FINITE s /\ x NOTIN s ==> (PROD_SET (x INSERT s) = x * PROD_SET s) *)
(* Proof:
   Since !x. I x = x         by I_THM
     and !s. IMAGE I s = s   by IMAGE_I
    thus the result follows  by PROD_SET_IMAGE_REDUCTION
*)
val PROD_SET_INSERT = store_thm(
  "PROD_SET_INSERT",
  ``!x s. FINITE s /\ x NOTIN s ==> (PROD_SET (x INSERT s) = x * PROD_SET s)``,
  metis_tac[PROD_SET_IMAGE_REDUCTION, combinTheory.I_THM, IMAGE_I]);

(* Theorem: FINITE s ==> !f. INJ f s UNIV ==> (PROD_SET (IMAGE f s) = PI f s) *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET (IMAGE f {}) = PI f {}
         PROD_SET (IMAGE f {})
       = PROD_SET {}              by IMAGE_EMPTY
       = 1                        by PROD_SET_EMPTY
       = PI f {}                  by PROD_IMAGE_EMPTY
   Step: !f. INJ f s univ(:num) ==> (PROD_SET (IMAGE f s) = PI f s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) ==> PROD_SET (IMAGE f (e INSERT s)) = PI f (e INSERT s)
       Note INJ f s univ(:num)               by INJ_INSERT
        and f e NOTIN (IMAGE f s)            by IN_IMAGE
         PROD_SET (IMAGE f (e INSERT s))
       = PROD_SET (f e INSERT (IMAGE f s))   by IMAGE_INSERT
       = f e * PROD_SET (IMAGE f s)          by PROD_SET_INSERT
       = f e * PI f s                        by induction hypothesis
       = PI f (e INSERT s)                   by PROD_IMAGE_INSERT
*)
val PROD_SET_IMAGE_EQN = store_thm(
  "PROD_SET_IMAGE_EQN",
  ``!s. FINITE s ==> !f. INJ f s UNIV ==> (PROD_SET (IMAGE f s) = PI f s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, PROD_IMAGE_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  rw[PROD_SET_INSERT, PROD_IMAGE_INSERT]);

(* Theorem: PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** (SUM_SET (count m)) *)
(* Proof:
   By induction on m.
   Base case: PROD_SET (IMAGE (\j. n ** j) (count 0)) = n ** SUM_SET (count 0)
     LHS = PROD_SET (IMAGE (\j. n ** j) (count 0))
         = PROD_SET (IMAGE (\j. n ** j) {})          by COUNT_ZERO
         = PROD_SET {}                               by IMAGE_EMPTY
         = 1                                         by PROD_SET_THM
     RHS = n ** SUM_SET (count 0)
         = n ** SUM_SET {}                           by COUNT_ZERO
         = n ** 0                                    by SUM_SET_THM
         = 1                                         by EXP
         = LHS
   Step case: PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** SUM_SET (count m) ==>
              PROD_SET (IMAGE (\j. n ** j) (count (SUC m))) = n ** SUM_SET (count (SUC m))
     First,
          FINITE (count m)                                   by FINITE_COUNT
          FINITE (IMAGE (\j. n ** j) (count m))              by IMAGE_FINITE
          m NOTIN count m                                    by IN_COUNT
     and  (\j. n ** j) m NOTIN IMAGE (\j. n ** j) (count m)  by EXP_BASE_INJECTIVE, 1 < n

     LHS = PROD_SET (IMAGE (\j. n ** j) (count (SUC m)))
         = PROD_SET (IMAGE (\j. n ** j) (m INSERT count m))  by COUNT_SUC
         = n ** m * PROD_SET (IMAGE (\j. n ** j) (count m))  by PROD_SET_IMAGE_REDUCTION
         = n ** m * n ** SUM_SET (count m)                   by induction hypothesis
         = n ** (m + SUM_SET (count m))                      by EXP_ADD
         = n ** SUM_SET (m INSERT count m)                   by SUM_SET_INSERT
         = n ** SUM_SET (count (SUC m))                      by COUNT_SUC
         = RHS
*)
val PROD_SET_IMAGE_EXP = store_thm(
  "PROD_SET_IMAGE_EXP",
  ``!n. 1 < n ==> !m. PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** (SUM_SET (count m))``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[PROD_SET_THM] >>
  `FINITE (IMAGE (\j. n ** j) (count m))` by rw[] >>
  `(\j. n ** j) m NOTIN IMAGE (\j. n ** j) (count m)` by rw[] >>
  `m NOTIN count m` by rw[] >>
  `PROD_SET (IMAGE (\j. n ** j) (count (SUC m))) =
    PROD_SET (IMAGE (\j. n ** j) (m INSERT count m))` by rw[COUNT_SUC] >>
  `_ = n ** m * PROD_SET (IMAGE (\j. n ** j) (count m))` by rw[PROD_SET_IMAGE_REDUCTION] >>
  `_ = n ** m * n ** SUM_SET (count m)` by rw[] >>
  `_ = n ** (m + SUM_SET (count m))` by rw[EXP_ADD] >>
  `_ = n ** SUM_SET (m INSERT count m)` by rw[SUM_SET_INSERT] >>
  `_ = n ** SUM_SET (count (SUC m))` by rw[COUNT_SUC] >>
  decide_tac);

(* Theorem: FINITE s /\ x IN s ==> x divides PROD_SET s *)
(* Proof:
   Note !n x. x IN s /\ n divides x
    ==> n divides PROD_SET s           by PROD_SET_DIVISORS
    Put n = x, and x divides x = T     by DIVIDES_REFL
    and the result follows.
*)
val PROD_SET_ELEMENT_DIVIDES = store_thm(
  "PROD_SET_ELEMENT_DIVIDES",
  ``!s x. FINITE s /\ x IN s ==> x divides PROD_SET s``,
  metis_tac[PROD_SET_DIVISORS, DIVIDES_REFL]);

(* Theorem: FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
            (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s) *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET (IMAGE f {}) <= PROD_SET (IMAGE g {})
      Note PROD_SET (IMAGE f {})
         = PROD_SET {}              by IMAGE_EMPTY
         = 1                        by PROD_SET_EMPTY
      Thus true.
   Step: !f g. (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s) ==>
        e NOTIN s /\ !x. x IN e INSERT s ==> f x <= g x ==>
        PROD_SET (IMAGE f (e INSERT s)) <= PROD_SET (IMAGE g (e INSERT s))
        Note INJ f s univ(:num)     by INJ_INSERT
         and INJ g s univ(:num)     by INJ_INSERT
         and f e NOTIN (IMAGE f s)  by IN_IMAGE
         and g e NOTIN (IMAGE g s)  by IN_IMAGE
       Applying LE_MONO_MULT2,
          PROD_SET (IMAGE f (e INSERT s))
        = PROD_SET (f e INSERT IMAGE f s)  by INSERT_IMAGE
        = f e * PROD_SET (IMAGE f s)       by PROD_SET_INSERT
       <= g e * PROD_SET (IMAGE f s)       by f e <= g e
       <= g e * PROD_SET (IMAGE g s)       by induction hypothesis
        = PROD_SET (g e INSERT IMAGE g s)  by PROD_SET_INSERT
        = PROD_SET (IMAGE g (e INSERT s))  by INSERT_IMAGE
*)
val PROD_SET_LESS_EQ = store_thm(
  "PROD_SET_LESS_EQ",
  ``!s. FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
       (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  `g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `f e <= g e` by rw[] >>
  `PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)` by rw[] >>
  rw[PROD_SET_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET {} <= n ** CARD {}
      Note PROD_SET {}
         = 1             by PROD_SET_EMPTY
         = n ** 0        by EXP_0
         = n ** CARD {}  by CARD_EMPTY
   Step: !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> x <= n ==> PROD_SET (e INSERT s) <= n ** CARD (e INSERT s)
      Note !x. (x = e) \/ x IN s ==> x <= n   by IN_INSERT
         PROD_SET (e INSERT s)
       = e * PROD_SET s          by PROD_SET_INSERT
      <= n * PROD_SET s          by e <= n
      <= n * (n ** CARD s)       by induction hypothesis
       = n ** (SUC (CARD s))     by EXP
       = n ** CARD (e INSERT s)  by CARD_INSERT, e NOTIN s
*)
val PROD_SET_LE_CONSTANT = store_thm(
  "PROD_SET_LE_CONSTANT",
  ``!s. FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, EXP_0] >>
  fs[] >>
  `e <= n /\ PROD_SET s <= n ** CARD s` by rw[] >>
  rw[PROD_SET_INSERT, EXP, CARD_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\ (!x. x IN s ==> n <= f x * g x) ==>
            n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s) *)
(* Proof:
   By finite induction on s.
   Base: n ** CARD {} <= PROD_SET (IMAGE f {}) * PROD_SET (IMAGE g {})
      Note n ** CARD {}
         = n ** 0           by CARD_EMPTY
         = 1                by EXP_0
       and PROD_SET (IMAGE f {})
         = PROD_SET {}      by IMAGE_EMPTY
         = 1                by PROD_SET_EMPTY
   Step: !n f. INJ f s univ(:num) /\ INJ g s univ(:num) /\
               (!x. x IN s ==> n <= f x * g x) ==>
               n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) /\ INJ g (e INSERT s) univ(:num) /\
         !x. x IN e INSERT s ==> n <= f x * g x ==>
         n ** CARD (e INSERT s) <= PROD_SET (IMAGE f (e INSERT s)) * PROD_SET (IMAGE g (e INSERT s))
      Note INJ f s univ(:num) /\ INJ g s univ(:num)         by INJ_INSERT
       and f e NOTIN (IMAGE f s) /\ g e NOTIN (IMAGE g s)   by IN_IMAGE
         PROD_SET (IMAGE f (e INSERT s)) * PROD_SET (IMAGE g (e INSERT s))
       = PROD_SET (f e INSERT (IMAGE f s)) * PROD_SET (g e INSERT (IMAGE g s))   by INSERT_IMAGE
       = (f e * PROD_SET (IMAGE f s)) * (g e * PROD_SET (IMAGE g s))    by PROD_SET_INSERT
       = (f e * g e) * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))    by MULT_ASSOC, MULT_COMM
       >= n        * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))      by n <= f e * g e
       >= n        * n ** CARD s                                        by induction hypothesis
        = n ** (SUC (CARD s))                               by EXP
        = n ** (CARD (e INSERT s))                          by CARD_INSERT
*)
val PROD_SET_PRODUCT_GE_CONSTANT = store_thm(
  "PROD_SET_PRODUCT_GE_CONSTANT",
  ``!s. FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\ (!x. x IN s ==> n <= f x * g x) ==>
       n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, EXP_0] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s) /\ g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `n <= f e * g e /\ n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)` by rw[] >>
  `PROD_SET (f e INSERT IMAGE f s) * PROD_SET (g e INSERT IMAGE g s) =
    (f e * PROD_SET (IMAGE f s)) * (g e * PROD_SET (IMAGE g s))` by rw[PROD_SET_INSERT] >>
  `_ = (f e * g e) * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[EXP, CARD_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v) *)
(* Proof:
   By finite induction on s.
   Base: {} = u UNION v ==> PROD_SET {} = PROD_SET u * PROD_SET v
      Note u = {} and v = {}       by EMPTY_UNION
       and PROD_SET {} = 1         by PROD_SET_EMPTY
      Hence true.
   Step: !u v. (s = u UNION v) /\ DISJOINT u v ==> (PROD_SET s = PROD_SET u * PROD_SET v) ==>
         e NOTIN s /\ e INSERT s = u UNION v ==> PROD_SET (e INSERT s) = PROD_SET u * PROD_SET v
      Note e IN u \/ e IN v        by IN_INSERT, IN_UNION
      If e IN u,
         Then e NOTIN v            by IN_DISJOINT
         Let w = u DELETE e.
         Then e NOTIN w            by IN_DELETE
          and u = e INSERT w       by INSERT_DELETE
         Note s = w UNION v        by EXTENSION, IN_INSERT, IN_UNION
          ==> FINITE w             by FINITE_UNION
          and DISJOINT w v         by DISJOINT_INSERT
        PROD_SET (e INSERT s)
      = e * PROD_SET s                       by PROD_SET_INSERT, FINITE s
      = e * (PROD_SET w * PROD_SET v)        by induction hypothesis
      = (e * PROD_SET w) * PROD_SET v        by MULT_ASSOC
      = PROD_SET (e INSERT w) * PROD_SET v   by PROD_SET_INSERT, FINITE w
      = PROD_SET u * PROD_SET v

      Similarly for e IN v.
*)
val PROD_SET_PRODUCT_BY_PARTITION = store_thm(
  "PROD_SET_PRODUCT_BY_PARTITION",
  ``!s. FINITE s ==> !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  fs[PROD_SET_EMPTY] >>
  `e IN u \/ e IN v` by metis_tac[IN_INSERT, IN_UNION] >| [
    qabbrev_tac `w = u DELETE e` >>
    `u = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN v` by metis_tac[IN_DISJOINT] >>
    `s = w UNION v` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT w v` by metis_tac[DISJOINT_INSERT] >>
    `PROD_SET (e INSERT s) = e * PROD_SET s` by rw[PROD_SET_INSERT] >>
    `_ = e * (PROD_SET w * PROD_SET v)` by rw[] >>
    `_ = (e * PROD_SET w) * PROD_SET v` by rw[] >>
    `_ = PROD_SET u * PROD_SET v` by rw[PROD_SET_INSERT] >>
    rw[],
    qabbrev_tac `w = v DELETE e` >>
    `v = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN u` by metis_tac[IN_DISJOINT] >>
    `s = u UNION w` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT u w` by metis_tac[DISJOINT_INSERT, DISJOINT_SYM] >>
    `PROD_SET (e INSERT s) = e * PROD_SET s` by rw[PROD_SET_INSERT] >>
    `_ = e * (PROD_SET u * PROD_SET w)` by rw[] >>
    `_ = PROD_SET u * (e * PROD_SET w)` by rw[] >>
    `_ = PROD_SET u * PROD_SET v` by rw[PROD_SET_INSERT] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Partition and Equivalent Class                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: y IN equiv_class R s x <=> y IN s /\ R x y *)
(* Proof: by GSPECIFICATION *)
val equiv_class_element = store_thm(
  "equiv_class_element",
  ``!R s x y. y IN equiv_class R s x <=> y IN s /\ R x y``,
  rw[]);

(* Theorem: partition R {} = {} *)
(* Proof: by partition_def *)
val partition_on_empty = store_thm(
  "partition_on_empty",
  ``!R. partition R {} = {}``,
  rw[partition_def]);

(*
> partition_def;
val it = |- !R s. partition R s = {t | ?x. x IN s /\ (t = equiv_class R s x)}: thm
*)

(* Theorem: t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x) *)
(* Proof: by partition_def *)
Theorem partition_element:
  !R s t. t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x)
Proof
  rw[partition_def]
QED

(* Theorem: partition R s = IMAGE (equiv_class R s) s *)
(* Proof:
     partition R s
   = {t | ?x. x IN s /\ (t = {y | y IN s /\ R x y})}   by partition_def
   = {t | ?x. x IN s /\ (t = equiv_class R s x)}       by notation
   = IMAGE (equiv_class R s) s                         by IN_IMAGE
*)
val partition_elements = store_thm(
  "partition_elements",
  ``!R s. partition R s = IMAGE (equiv_class R s) s``,
  rw[partition_def, EXTENSION] >>
  metis_tac[]);

(* Theorem alias *)
val partition_as_image = save_thm("partition_as_image", partition_elements);
(* val partition_as_image =
   |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s: thm *)

(* Theorem: (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2) *)
(* Proof: by identity *)
val partition_cong = store_thm(
  "partition_cong",
  ``!R1 R2 s1 s2. (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2)``,
  rw[]);
(* Just in case this is needed. *)

(*
EMPTY_NOT_IN_partition
val it = |- R equiv_on s ==> {} NOTIN partition R s: thm
*)

(* Theorem: R equiv_on s /\ e IN partition R s ==> e <> {} *)
(* Proof: by EMPTY_NOT_IN_partition. *)
Theorem partition_element_not_empty:
  !R s e. R equiv_on s /\ e IN partition R s ==> e <> {}
Proof
  metis_tac[EMPTY_NOT_IN_partition]
QED

(* Theorem: R equiv_on s /\ x IN s ==> equiv_class R s x <> {} *)
(* Proof:
   Note equiv_class R s x IN partition_element R s     by partition_element
     so equiv_class R s x <> {}                        by partition_element_not_empty
*)
Theorem equiv_class_not_empty:
  !R s x. R equiv_on s /\ x IN s ==> equiv_class R s x <> {}
Proof
  metis_tac[partition_element, partition_element_not_empty]
QED

(* Theorem: R equiv_on s ==> (x IN s <=> ?e. e IN partition R s /\ x IN e) *)
(* Proof:
       x IN s
   <=> x IN (BIGUNION (partition R s))         by BIGUNION_partition
   <=> ?e. e IN partition R s /\ x IN e        by IN_BIGUNION
*)
Theorem partition_element_exists:
  !R s x. R equiv_on s ==> (x IN s <=> ?e. e IN partition R s /\ x IN e)
Proof
  rpt strip_tac >>
  imp_res_tac BIGUNION_partition >>
  metis_tac[IN_BIGUNION]
QED

(* Theorem: When the partitions are equal size of n, CARD s = n * CARD (partition of s).
           FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           (CARD s = n * CARD (partition R s)) *)
(* Proof:
   Note FINITE (partition R s)               by FINITE_partition
     so CARD s = SIGMA CARD (partition R s)  by partition_CARD
               = n * CARD (partition R s)    by SIGMA_CARD_CONSTANT
*)
val equal_partition_card = store_thm(
  "equal_partition_card",
  ``!R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           (CARD s = n * CARD (partition R s))``,
  rw_tac std_ss[partition_CARD, FINITE_partition, GSYM SIGMA_CARD_CONSTANT]);

(* Theorem: When the partitions are equal size of n, CARD s = n * CARD (partition of s).
           FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           n divides (CARD s) *)
(* Proof: by equal_partition_card, divides_def. *)
Theorem equal_partition_factor:
  !R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
          n divides (CARD s)
Proof
  metis_tac[equal_partition_card, divides_def, MULT_COMM]
QED

(* Theorem: When the partition size has a factor n, then n divides CARD s.
            FINITE s /\ R equiv_on s /\
            (!e. e IN partition R s ==> n divides (CARD e)) ==> n divides (CARD s)  *)
(* Proof:
   Note FINITE (partition R s)                by FINITE_partition
   Thus CARD s = SIGMA CARD (partition R s)   by partition_CARD
    But !e. e IN partition R s ==> n divides (CARD e)
    ==> n divides SIGMA CARD (partition R s)  by SIGMA_CARD_FACTOR
   Hence n divdes CARD s                      by above
*)
val factor_partition_card = store_thm(
  "factor_partition_card",
  ``!R s n. FINITE s /\ R equiv_on s /\
   (!e. e IN partition R s ==> n divides (CARD e)) ==> n divides (CARD s)``,
  metis_tac[FINITE_partition, partition_CARD, SIGMA_CARD_FACTOR]);

(* Note:
When a set s is partitioned by an equivalence relation R,
partition_CARD  |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
Can this be generalized to:   f s = SIGMA f (partition R s)  ?
If so, we can have         (SIGMA f) s = SIGMA (SIGMA f) (partition R s)
Sort of yes, but have to use BIGUNION, and for a set_additive function f.
*)

(* Overload every element finite of a superset *)
val _ = overload_on("EVERY_FINITE", ``\P. (!s. s IN P ==> FINITE s)``);

(*
> FINITE_BIGUNION;
val it = |- !P. FINITE P /\ EVERY_FINITE P ==> FINITE (BIGUNION P): thm
*)

(* Overload pairwise disjoint of a superset *)
val _ = overload_on("PAIR_DISJOINT", ``\P. (!s t. s IN P /\ t IN P /\ ~(s = t) ==> DISJOINT s t)``);

(*
> partition_elements_disjoint;
val it = |- R equiv_on s ==> PAIR_DISJOINT (partition R s): thm
*)

(* Theorem: t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t *)
(* Proof: by SUBSET_DEF *)
Theorem pair_disjoint_subset:
  !s t. t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t
Proof
  rw[SUBSET_DEF]
QED

(* Overload an additive set function *)
val _ = overload_on("SET_ADDITIVE",
   ``\f. (f {} = 0) /\ (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) + f (s INTER t) = f s + f t))``);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
            !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P) *)
(* Proof:
   By finite induction on P.
   Base: f (BIGUNION {}) = SIGMA f {}
         f (BIGUNION {})
       = f {}                by BIGUNION_EMPTY
       = 0                   by SET_ADDITIVE f
       = SIGMA f {} = RHS    by SUM_IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = SIGMA f (e INSERT P)
       Given !s. s IN e INSERT P ==> FINITE s
        thus !s. (s = e) \/ s IN P ==> FINITE s   by IN_INSERT
       hence FINITE e              by implication
         and EVERY_FINITE P        by IN_INSERT
         and FINITE (BIGUNION P)   by FINITE_BIGUNION
       Given PAIR_DISJOINT (e INSERT P)
          so PAIR_DISJOINT P               by IN_INSERT
         and !s. s IN P ==> DISJOINT e s   by IN_INSERT
       hence DISJOINT e (BIGUNION P)       by DISJOINT_BIGUNION
          so e INTER (BIGUNION P) = {}     by DISJOINT_DEF
         and f (e INTER (BIGUNION P)) = 0  by SET_ADDITIVE f
         f (BIGUNION (e INSERT P)
       = f (BIGUNION (e INSERT P)) + f (e INTER (BIGUNION P))     by ADD_0
       = f e + f (BIGUNION P)                                     by SET_ADDITIVE f
       = f e + SIGMA f P                   by induction hypothesis
       = f e + SIGMA f (P DELETE e)        by DELETE_NON_ELEMENT
       = SIGMA f (e INSERT P)              by SUM_IMAGE_THM
*)
val disjoint_bigunion_add_fun = store_thm(
  "disjoint_bigunion_add_fun",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)``,
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw_tac std_ss[BIGUNION_EMPTY, SUM_IMAGE_EMPTY] >>
  rw_tac std_ss[BIGUNION_INSERT, SUM_IMAGE_THM] >>
  `FINITE e /\ FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `EVERY_FINITE P /\ PAIR_DISJOINT P` by rw[] >>
  `!s. s IN P ==> DISJOINT e s` by metis_tac[IN_INSERT] >>
  `f (e INTER (BIGUNION P)) = 0` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) + f (e INTER (BIGUNION P))` by decide_tac >>
  `_ = f e + f (BIGUNION P)` by metis_tac[] >>
  `_ = f e + SIGMA f P` by prove_tac[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: SET_ADDITIVE CARD *)
(* Proof:
   Since CARD {} = 0                    by CARD_EMPTY
     and !s t. FINITE s /\ FINITE t
     ==> CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t   by CARD_UNION
   Hence SET_ADDITIVE CARD              by notation
*)
val set_additive_card = store_thm(
  "set_additive_card",
  ``SET_ADDITIVE CARD``,
  rw[FUN_EQ_THM, CARD_UNION]);

(* Note: DISJ_BIGUNION_CARD is only a prove_thm in pred_setTheoryScript.sml *)
(*
g `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)`
e (PSet_ind.SET_INDUCT_TAC FINITE_INDUCT);
Q. use of this changes P to s, s to s', how?
*)

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P) *)
(* Proof: by disjoint_bigunion_add_fun, set_additive_card *)
val disjoint_bigunion_card = store_thm(
  "disjoint_bigunion_card",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)``,
  rw[disjoint_bigunion_add_fun, set_additive_card]);

(* Theorem alias *)
Theorem CARD_BIGUNION_PAIR_DISJOINT = disjoint_bigunion_card;
(*
val CARD_BIGUNION_PAIR_DISJOINT =
   |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
          CARD (BIGUNION P) = SIGMA CARD P: thm
*)

(* Theorem: SET_ADDITIVE (SIGMA f) *)
(* Proof:
   Since SIGMA f {} = 0         by SUM_IMAGE_EMPTY
     and !s t. FINITE s /\ FINITE t
     ==> SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t   by SUM_IMAGE_UNION_EQN
   Hence SET_ADDITIVE (SIGMA f)
*)
val set_additive_sigma = store_thm(
  "set_additive_sigma",
  ``!f. SET_ADDITIVE (SIGMA f)``,
  rw[SUM_IMAGE_EMPTY, SUM_IMAGE_UNION_EQN]);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P *)
(* Proof: by disjoint_bigunion_add_fun, set_additive_sigma *)
val disjoint_bigunion_sigma = store_thm(
  "disjoint_bigunion_sigma",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P``,
  rw[disjoint_bigunion_add_fun, set_additive_sigma]);

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s)) *)
(* Proof:
   Let P = partition R s.
    Then FINITE s
     ==> FINITE P /\ !t. t IN P ==> FINITE t    by FINITE_partition
     and R equiv_on s
     ==> BIGUNION P = s               by BIGUNION_partition
     ==> PAIR_DISJOINT P              by partition_elements_disjoint
   Hence f (BIGUNION P) = SIGMA f P   by disjoint_bigunion_add_fun
      or f s = SIGMA f P              by above, BIGUNION_partition
*)
val set_add_fun_by_partition = store_thm(
  "set_add_fun_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition R s` >>
  `FINITE P /\ !t. t IN P ==> FINITE t` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  rw[disjoint_bigunion_add_fun]);

(* Theorem: R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s)) *)
(* Proof: by set_add_fun_by_partition, set_additive_card *)
val set_card_by_partition = store_thm(
  "set_card_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))``,
  rw[set_add_fun_by_partition, set_additive_card]);

(* This is pred_setTheory.partition_CARD *)

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SIGMA f s = SIGMA (SIGMA f) (partition R s) *)
(* Proof: by set_add_fun_by_partition, set_additive_sigma *)
val set_sigma_by_partition = store_thm(
  "set_sigma_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SIGMA f s = SIGMA (SIGMA f) (partition R s)``,
  rw[set_add_fun_by_partition, set_additive_sigma]);

(* Overload a multiplicative set function *)
val _ = overload_on("SET_MULTIPLICATIVE",
   ``\f. (f {} = 1) /\ (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) * f (s INTER t) = f s * f t))``);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
            !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P) *)
(* Proof:
   By finite induction on P.
   Base: f (BIGUNION {}) = PI f {}
         f (BIGUNION {})
       = f {}                by BIGUNION_EMPTY
       = 1                   by SET_MULTIPLICATIVE f
       = PI f {} = RHS       by PROD_IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = PI f (e INSERT P)
       Given !s. s IN e INSERT P ==> FINITE s
        thus !s. (s = e) \/ s IN P ==> FINITE s   by IN_INSERT
       hence FINITE e              by implication
         and EVERY_FINITE P        by IN_INSERT
         and FINITE (BIGUNION P)   by FINITE_BIGUNION
       Given PAIR_DISJOINT (e INSERT P)
          so PAIR_DISJOINT P               by IN_INSERT
         and !s. s IN P ==> DISJOINT e s   by IN_INSERT
       hence DISJOINT e (BIGUNION P)       by DISJOINT_BIGUNION
          so e INTER (BIGUNION P) = {}     by DISJOINT_DEF
         and f (e INTER (BIGUNION P)) = 1  by SET_MULTIPLICATIVE f
         f (BIGUNION (e INSERT P)
       = f (BIGUNION (e INSERT P)) * f (e INTER (BIGUNION P))     by MULT_RIGHT_1
       = f e * f (BIGUNION P)                                     by SET_MULTIPLICATIVE f
       = f e * PI f P                      by induction hypothesis
       = f e * PI f (P DELETE e)           by DELETE_NON_ELEMENT
       = PI f (e INSERT P)                 by PROD_IMAGE_THM
*)
val disjoint_bigunion_mult_fun = store_thm(
  "disjoint_bigunion_mult_fun",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)``,
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw_tac std_ss[BIGUNION_EMPTY, PROD_IMAGE_EMPTY] >>
  rw_tac std_ss[BIGUNION_INSERT, PROD_IMAGE_THM] >>
  `FINITE e /\ FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `EVERY_FINITE P /\ PAIR_DISJOINT P` by rw[] >>
  `!s. s IN P ==> DISJOINT e s` by metis_tac[IN_INSERT] >>
  `f (e INTER (BIGUNION P)) = 1` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) * f (e INTER (BIGUNION P))` by metis_tac[MULT_RIGHT_1] >>
  `_ = f e * f (BIGUNION P)` by metis_tac[] >>
  `_ = f e * PI f P` by prove_tac[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s)) *)
(* Proof:
   Let P = partition R s.
    Then FINITE s
     ==> FINITE P /\ EVERY_FINITE P   by FINITE_partition
     and R equiv_on s
     ==> BIGUNION P = s               by BIGUNION_partition
     ==> PAIR_DISJOINT P              by partition_elements_disjoint
   Hence f (BIGUNION P) = PI f P      by disjoint_bigunion_mult_fun
      or f s = PI f P                 by above, BIGUNION_partition
*)
val set_mult_fun_by_partition = store_thm(
  "set_mult_fun_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition R s` >>
  `FINITE P /\ !t. t IN P ==> FINITE t` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  rw[disjoint_bigunion_mult_fun]);

(* Theorem: FINITE s ==> !g. INJ g s univ(:'a) ==> !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f (IMAGE g {}) = SIGMA (f o g) {}
      LHS = SIGMA f (IMAGE g {})
          = SIGMA f {}                    by IMAGE_EMPTY
          = 0                             by SUM_IMAGE_EMPTY
          = SIGMA (f o g) {} = RHS        by SUM_IMAGE_EMPTY
   Step: e NOTIN s ==> SIGMA f (IMAGE g (e INSERT s)) = SIGMA (f o g) (e INSERT s)
      Note INJ g (e INSERT s) univ(:'a)
       ==> INJ g s univ(:'a) /\ g e IN univ(:'a) /\
           !y. y IN s /\ (g e = g y) ==> (e = y)       by INJ_INSERT
      Thus g e NOTIN (IMAGE g s)                       by IN_IMAGE
        SIGMA f (IMAGE g (e INSERT s))
      = SIGMA f (g e INSERT IMAGE g s)    by IMAGE_INSERT
      = f (g e) + SIGMA f (IMAGE g s)     by SUM_IMAGE_THM, g e NOTIN (IMAGE g s)
      = f (g e) + SIGMA (f o g) s         by induction hypothesis
      = (f o g) e + SIGMA (f o g) s       by composition
      = SIGMA (f o g) (e INSERT s)        by SUM_IMAGE_THM, e NOTIN s
*)
val sum_image_by_composition = store_thm(
  "sum_image_by_composition",
  ``!s. FINITE s ==> !g. INJ g s univ(:'a) ==> !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  `INJ g s univ(:'a) /\ g e IN univ(:'a) /\ !y. y IN s /\ (g e = g y) ==> (e = y)` by metis_tac[INJ_INSERT] >>
  `g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `(s DELETE e = s) /\ (IMAGE g s DELETE g e = IMAGE g s)` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[SUM_IMAGE_THM]);

(* Overload on permutation *)
val _ = overload_on("PERMUTES", ``\f s. BIJ f s s``);
val _ = set_fixity "PERMUTES" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s *)
(* Proof:
   Given permutate g s = BIJ g s s       by notation
     ==> INJ g s s /\ SURJ g s s         by BIJ_DEF
     Now SURJ g s s ==> IMAGE g s = s    by IMAGE_SURJ
    Also s SUBSET univ(:'a)              by SUBSET_UNIV
     and s SUBSET s                      by SUBSET_REFL
   Hence INJ g s univ(:'a)               by INJ_SUBSET
    With FINITE s,
      SIGMA (f o g) s
    = SIGMA f (IMAGE g s)                by sum_image_by_composition
    = SIGMA f s                          by above
*)
val sum_image_by_permutation = store_thm(
  "sum_image_by_permutation",
  ``!s. FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s``,
  rpt strip_tac >>
  `INJ g s s /\ SURJ g s s` by metis_tac[BIJ_DEF] >>
  `IMAGE g s = s` by rw[GSYM IMAGE_SURJ] >>
  `s SUBSET univ(:'a)` by rw[SUBSET_UNIV] >>
  `INJ g s univ(:'a)` by metis_tac[INJ_SUBSET, SUBSET_REFL] >>
  `SIGMA (f o g) s = SIGMA f (IMAGE g s)` by rw[sum_image_by_composition] >>
  rw[]);

(* Theorem: FINITE s ==> !f:('b -> bool) -> num. (f {} = 0) ==>
            !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:num -> bool)) ==>
            (SIGMA f (IMAGE g s) = SIGMA (f o g) s) *)
(* Proof:
   Let s1 = {x | x IN s /\ (g x = {})},
       s2 = {x | x IN s /\ (g x <> {})}.
    Then s = s1 UNION s2                             by EXTENSION
     and DISJOINT s1 s2                              by EXTENSION, DISJOINT_DEF
     and DISJOINT (IMAGE g s1) (IMAGE g s2)          by EXTENSION, DISJOINT_DEF
     Now s1 SUBSET s /\ s1 SUBSET s                  by SUBSET_DEF
   Since FINITE s                                    by given
    thus FINITE s1 /\ FINITE s2                      by SUBSET_FINITE
     and FINITE (IMAGE g s1) /\ FINITE (IMAGE g s2)  by IMAGE_FINITE

   Step 1: decompose left summation
         SIGMA f (IMAGE g s)
       = SIGMA f (IMAGE g (s1 UNION s2))             by above, s = s1 UNION s2
       = SIGMA f ((IMAGE g s1) UNION (IMAGE g s2))   by IMAGE_UNION
       = SIGMA f (IMAGE g s1) + SIGMA f (IMAGE g s2) by SUM_IMAGE_DISJOINT

   Claim: SIGMA f (IMAGE g s1) = 0
   Proof: If s1 = {},
            SIGMA f (IMAGE g {})
          = SIGMA f {}                               by IMAGE_EMPTY
          = 0                                        by SUM_IMAGE_EMPTY
          If s1 <> {},
            Note !x. x IN s1 ==> (g x = {})          by definition of s1
            Thus !y. y IN (IMAGE g s1) ==> (y = {})  by IN_IMAGE, IMAGE_EMPTY
           Since s1 <> {}, IMAGE g s1 = {{}}         by SING_DEF, IN_SING, SING_ONE_ELEMENT
            SIGMA f (IMAGE g {})
          = SIGMA f {{}}                             by above
          = f {}                                     by SUM_IMAGE_SING
          = 0                                        by given

   Step 2: decompose right summation
    Also SIGMA (f o g) s
       = SIGMA (f o g) (s1 UNION s2)                 by above, s = s1 UNION s2
       = SIGMA (f o g) s1 + SIGMA (f o g) s2         by SUM_IMAGE_DISJOINT

   Claim: SIGMA (f o g) s1 = 0
   Proof: Note !x. x IN s1 ==> (g x = {})            by definition of s1
             (f o g) x
            = f (g x)                                by function application
            = f {}                                   by above
            = 0                                      by given
          Hence SIGMA (f o g) s1
              = 0 * CARD s1                          by SIGMA_CONSTANT
              = 0                                    by MULT

   Claim: SIGMA f (IMAGE g s2) = SIGMA (f o g) s2
   Proof: Note !x. x IN s2 ==> g x <> {}             by definition of s2
          Thus INJ g s2 univ(:'b -> bool)            by given
          Hence SIGMA f (IMAGE g s2)
              = SIGMA (f o g) (s2)                   by sum_image_by_composition

   Result follows by combining all the claims and arithmetic.
*)
val sum_image_by_composition_with_partial_inj = store_thm(
  "sum_image_by_composition_with_partial_inj",
  ``!s. FINITE s ==> !f:('b -> bool) -> num. (f {} = 0) ==>
   !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:'b -> bool)) ==>
   (SIGMA f (IMAGE g s) = SIGMA (f o g) s)``,
  rpt strip_tac >>
  qabbrev_tac `s1 = {x | x IN s /\ (g x = {})}` >>
  qabbrev_tac `s2 = {x | x IN s /\ (g x <> {})}` >>
  (`s = s1 UNION s2` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION] >> metis_tac[])) >>
  (`DISJOINT s1 s2` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION, DISJOINT_DEF] >> metis_tac[])) >>
  (`DISJOINT (IMAGE g s1) (IMAGE g s2)` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION, DISJOINT_DEF] >> metis_tac[])) >>
  `s1 SUBSET s /\ s2 SUBSET s` by rw[Abbr`s1`, Abbr`s2`, SUBSET_DEF] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[SUBSET_FINITE] >>
  `FINITE (IMAGE g s1) /\ FINITE (IMAGE g s2)` by rw[] >>
  `SIGMA f (IMAGE g s) = SIGMA f ((IMAGE g s1) UNION (IMAGE g s2))` by rw[] >>
  `_ = SIGMA f (IMAGE g s1) + SIGMA f (IMAGE g s2)` by rw[SUM_IMAGE_DISJOINT] >>
  `SIGMA f (IMAGE g s1) = 0` by
  (Cases_on `s1 = {}` >-
  rw[SUM_IMAGE_EMPTY] >>
  `!x. x IN s1 ==> (g x = {})` by rw[Abbr`s1`] >>
  `!y. y IN (IMAGE g s1) ==> (y = {})` by metis_tac[IN_IMAGE, IMAGE_EMPTY] >>
  `{} IN {{}} /\ IMAGE g s1 <> {}` by rw[] >>
  `IMAGE g s1 = {{}}` by metis_tac[SING_DEF, IN_SING, SING_ONE_ELEMENT] >>
  `SIGMA f (IMAGE g s1) = f {}` by rw[SUM_IMAGE_SING] >>
  rw[]
  ) >>
  `SIGMA (f o g) s = SIGMA (f o g) s1 + SIGMA (f o g) s2` by rw[SUM_IMAGE_DISJOINT] >>
  `SIGMA (f o g) s1 = 0` by
    (`!x. x IN s1 ==> (g x = {})` by rw[Abbr`s1`] >>
  `!x. x IN s1 ==> ((f o g) x = 0)` by rw[] >>
  metis_tac[SIGMA_CONSTANT, MULT]) >>
  `SIGMA f (IMAGE g s2) = SIGMA (f o g) s2` by
      (`!x. x IN s2 ==> g x <> {}` by rw[Abbr`s2`] >>
  `INJ g s2 univ(:'b -> bool)` by rw[] >>
  rw[sum_image_by_composition]) >>
  decide_tac);

(* Theorem: FINITE s ==> !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
            (SIGMA f (IMAGE g s) = SIGMA (f o g) s) *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f (IMAGE g {}) = SIGMA (f o g) {}
        SIGMA f (IMAGE g {})
      = SIGMA f {}                 by IMAGE_EMPTY
      = 0                          by SUM_IMAGE_EMPTY
      = SIGMA (f o g) {}           by SUM_IMAGE_EMPTY
   Step: !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
         (SIGMA f (IMAGE g s) = SIGMA (f o g) s) ==>
         e NOTIN s /\ !x y. x IN e INSERT s /\ y IN e INSERT s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)
         ==> SIGMA f (IMAGE g (e INSERT s)) = SIGMA (f o g) (e INSERT s)
      Note !x y. ((x = e) \/ x IN s) /\ ((y = e) \/ y IN s) /\ (g x = g y) ==>
                 (x = y) \/ (f (g y) = 0)       by IN_INSERT
      If g e IN IMAGE g s,
         Then ?x. x IN s /\ (g x = g e)         by IN_IMAGE
          and x <> e /\ (f (g e) = 0)           by implication
           SIGMA f (g e INSERT IMAGE g s)
         = SIGMA f (IMAGE g s)                  by ABSORPTION, g e IN IMAGE g s
         = SIGMA (f o g) s                      by induction hypothesis
         = f (g x) + SIGMA (f o g) s            by ADD
         = (f o g) e + SIGMA (f o g) s          by o_THM
         = SIGMA (f o g) (e INSERT s)           by SUM_IMAGE_INSERT, e NOTIN s
      If g e NOTIN IMAGE g s,
           SIGMA f (g e INSERT IMAGE g s)
         = f (g e) + SIGMA f (IMAGE g s)        by SUM_IMAGE_INSERT, g e NOTIN IMAGE g s
         = f (g e) + SIGMA (f o g) s            by induction hypothesis
         = (f o g) e + SIGMA (f o g) s          by o_THM
         = SIGMA (f o g) (e INSERT s)           by SUM_IMAGE_INSERT, e NOTIN s
*)
val sum_image_by_composition_without_inj = store_thm(
  "sum_image_by_composition_without_inj",
  ``!s. FINITE s ==> !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
       (SIGMA f (IMAGE g s) = SIGMA (f o g) s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  fs[] >>
  Cases_on `g e IN IMAGE g s` >| [
    `?x. x IN s /\ (g x = g e)` by metis_tac[IN_IMAGE] >>
    `x <> e /\ (f (g e) = 0)` by metis_tac[] >>
    `SIGMA f (g e INSERT IMAGE g s) = SIGMA f (IMAGE g s)` by metis_tac[ABSORPTION] >>
    `_ = SIGMA (f o g) s` by rw[] >>
    `_ = (f o g) e + SIGMA (f o g) s` by rw[] >>
    `_ = SIGMA (f o g) (e INSERT s)` by rw[SUM_IMAGE_INSERT] >>
    rw[],
    `SIGMA f (g e INSERT IMAGE g s) = f (g e) + SIGMA f (IMAGE g s)` by rw[SUM_IMAGE_INSERT] >>
    `_ = f (g e) + SIGMA (f o g) s` by rw[] >>
    `_ = (f o g) e + SIGMA (f o g) s` by rw[] >>
    `_ = SIGMA (f o g) (e INSERT s)` by rw[SUM_IMAGE_INSERT] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Pre-image Theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

(*
- IN_IMAGE;
> val it = |- !y s f. y IN IMAGE f s <=> ?x. (y = f x) /\ x IN s : thm
*)

(* Define preimage *)
val preimage_def = Define `preimage f s y = { x | x IN s /\ (f x = y) }`;

(* Theorem: x IN (preimage f s y) <=> x IN s /\ (f x = y) *)
(* Proof: by preimage_def *)
val preimage_element = store_thm(
  "preimage_element",
  ``!f s x y. x IN (preimage f s y) <=> x IN s /\ (f x = y)``,
  rw[preimage_def]);

(* Theorem: x IN preimage f s y <=> (x IN s /\ (f x = y)) *)
(* Proof: by preimage_def *)
val in_preimage = store_thm(
  "in_preimage",
  ``!f s x y. x IN preimage f s y <=> (x IN s /\ (f x = y))``,
  rw[preimage_def]);
(* same as theorem above. *)

(* Theorem: (preimage f s y) SUBSET s *)
(* Proof:
       x IN preimage f s y
   <=> x IN s /\ f x = y           by in_preimage
   ==> x IN s
   Thus (preimage f s y) SUBSET s  by SUBSET_DEF
*)
Theorem preimage_subset:
  !f s y. (preimage f s y) SUBSET s
Proof
  simp[preimage_def, SUBSET_DEF]
QED

(* Theorem: FINITE s ==> FINITE (preimage f s y) *)
(* Proof:
   Note (preimage f s y) SUBSET s  by preimage_subset
   Thus FINITE (preimage f s y)    by SUBSET_FINITE
*)
Theorem preimage_finite:
  !f s y. FINITE s ==> FINITE (preimage f s y)
Proof
  metis_tac[preimage_subset, SUBSET_FINITE]
QED

(* Theorem: !x. x IN preimage f s y ==> f x = y *)
(* Proof: by definition. *)
val preimage_property = store_thm(
  "preimage_property",
  ``!f s y. !x. x IN preimage f s y ==> (f x = y)``,
  rw[preimage_def]);

(* This is bad: every pattern of f x = y (i.e. practically every equality!) will invoke the check: x IN preimage f s y! *)
(* val _ = export_rewrites ["preimage_property"]; *)

(* Theorem: x IN s ==> x IN preimage f s (f x) *)
(* Proof: by IN_IMAGE. preimage_def. *)
val preimage_of_image = store_thm(
  "preimage_of_image",
  ``!f s x. x IN s ==> x IN preimage f s (f x)``,
  rw[preimage_def]);

(* Theorem: y IN (IMAGE f s) ==> CHOICE (preimage f s y) IN s /\ f (CHOICE (preimage f s y)) = y *)
(* Proof:
   (1) prove: y IN IMAGE f s ==> CHOICE (preimage f s y) IN s
   By IN_IMAGE, this is to show:
   x IN s ==> CHOICE (preimage f s (f x)) IN s
   Now, preimage f s (f x) <> {}   since x is a pre-image.
   hence CHOICE (preimage f s (f x)) IN preimage f s (f x) by CHOICE_DEF
   hence CHOICE (preimage f s (f x)) IN s                  by preimage_def
   (2) prove: y IN IMAGE f s /\ CHOICE (preimage f s y) IN s ==> f (CHOICE (preimage f s y)) = y
   By IN_IMAGE, this is to show: x IN s ==> f (CHOICE (preimage f s (f x))) = f x
   Now, x IN preimage f s (f x)   by preimage_of_image
   hence preimage f s (f x) <> {}  by MEMBER_NOT_EMPTY
   thus  CHOICE (preimage f s (f x)) IN (preimage f s (f x))  by CHOICE_DEF
   hence f (CHOICE (preimage f s (f x))) = f x  by preimage_def
*)
val preimage_choice_property = store_thm(
  "preimage_choice_property",
  ``!f s y. y IN (IMAGE f s) ==> CHOICE (preimage f s y) IN s /\ (f (CHOICE (preimage f s y)) = y)``,
  rpt gen_tac >>
  strip_tac >>
  conj_asm1_tac >| [
    full_simp_tac std_ss [IN_IMAGE] >>
    `CHOICE (preimage f s (f x)) IN preimage f s (f x)` suffices_by rw[preimage_def] >>
    metis_tac[CHOICE_DEF, preimage_of_image, MEMBER_NOT_EMPTY],
    full_simp_tac std_ss [IN_IMAGE] >>
    `x IN preimage f s (f x)` by rw_tac std_ss[preimage_of_image] >>
    `CHOICE (preimage f s (f x)) IN (preimage f s (f x))` by metis_tac[CHOICE_DEF, MEMBER_NOT_EMPTY] >>
    full_simp_tac std_ss [preimage_def, GSPECIFICATION]
  ]);

(* Theorem: INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x}) *)
(* Proof:
     preimage f s (f x)
   = {x' | x' IN s /\ (f x' = f x)}    by preimage_def
   = {x' | x' IN s /\ (x' = x)}        by INJ_DEF
   = {x}                               by EXTENSION
*)
val preimage_inj = store_thm(
  "preimage_inj",
  ``!f s. INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x})``,
  rw[preimage_def, EXTENSION] >>
  metis_tac[INJ_DEF]);

(* Theorem: INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x) *)
(* Proof:
     CHOICE (preimage f s (f x))
   = CHOICE {x}                     by preimage_inj, INJ f s univ(:'b)
   = x                              by CHOICE_SING
*)
val preimage_inj_choice = store_thm(
  "preimage_inj_choice",
  ``!f s. INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x)``,
  rw[preimage_inj]);

(* Theorem: INJ (preimage f s) (IMAGE f s) (POW s) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN s ==> preimage f s (f x) IN POW s
       Let y = preimage f s (f x).
       Then y SUBSET s                         by preimage_subset
         so y IN (POW s)                       by IN_POW
   (2) x IN s /\ y IN s /\ preimage f s (f x) = preimage f s (f y) ==> f x = f y
       Note (f x) IN preimage f s (f x)        by in_preimage
         so (f y) IN preimage f s (f y)        by given
       Thus f x = f y                          by in_preimage
*)
Theorem preimage_image_inj:
  !f s. INJ (preimage f s) (IMAGE f s) (POW s)
Proof
  rw[INJ_DEF] >-
  simp[preimage_subset, IN_POW] >>
  metis_tac[in_preimage]
QED

(* ------------------------------------------------------------------------- *)
(* Set of Proper Subsets                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of all proper subsets of a set *)
val _ = overload_on ("PPOW", ``\s. (POW s) DIFF {s}``);

(* Theorem: !s e. e IN PPOW s ==> e PSUBSET s *)
(* Proof:
     e IN PPOW s
   = e IN ((POW s) DIFF {s})       by notation
   = (e IN POW s) /\ e NOTIN {s}   by IN_DIFF
   = (e SUBSET s) /\ e NOTIN {s}   by IN_POW
   = (e SUBSET s) /\ e <> s        by IN_SING
   = e PSUBSET s                   by PSUBSET_DEF
*)
val IN_PPOW = store_thm(
  "IN_PPOW",
  ``!s e. e IN PPOW s ==> e PSUBSET s``,
  rw[PSUBSET_DEF, IN_POW]);

(* Theorem: FINITE (PPOW s) *)
(* Proof:
   Since PPOW s = (POW s) DIFF {s},
       FINITE s
   ==> FINITE (POW s)     by FINITE_POW
   ==> FINITE ((POW s) DIFF {s})  by FINITE_DIFF
   ==> FINITE (PPOW s)            by above
*)
val FINITE_PPOW = store_thm(
  "FINITE_PPOW",
  ``!s. FINITE s ==> FINITE (PPOW s)``,
  rw[FINITE_POW]);

(* Theorem: FINITE s ==> CARD (PPOW s) = PRE (2 ** CARD s) *)
(* Proof:
     CARD (PPOW s)
   = CARD ((POW s) DIFF {s})      by notation
   = CARD (POW s) - CARD ((POW s) INTER {s})   by CARD_DIFF
   = CARD (POW s) - CARD {s}      by INTER_SING, since s IN POW s
   = 2 ** CARD s  - CARD {s}      by CARD_POW
   = 2 ** CARD s  - 1             by CARD_SING
   = PRE (2 ** CARD s)            by PRE_SUB1
*)
val CARD_PPOW = store_thm(
  "CARD_PPOW",
  ``!s. FINITE s ==> (CARD (PPOW s) = PRE (2 ** CARD s))``,
  rpt strip_tac >>
  `FINITE {s}` by rw[FINITE_SING] >>
  `FINITE (POW s)` by rw[FINITE_POW] >>
  `s IN (POW s)` by rw[IN_POW, SUBSET_REFL] >>
  `CARD (PPOW s) = CARD (POW s) - CARD ((POW s) INTER {s})` by rw[CARD_DIFF] >>
  `_ = CARD (POW s) - CARD {s}` by rw[INTER_SING] >>
  `_ = 2 ** CARD s  - CARD {s}` by rw[CARD_POW] >>
  `_ = 2 ** CARD s  - 1` by rw[CARD_SING] >>
  `_ = PRE (2 ** CARD s)` by rw[PRE_SUB1] >>
  rw[]);

(* Theorem: FINITE s ==> CARD (PPOW s) = PRE (2 ** CARD s) *)
(* Proof: by CARD_PPOW *)
val CARD_PPOW_EQN = store_thm(
  "CARD_PPOW_EQN",
  ``!s. FINITE s ==> (CARD (PPOW s) = (2 ** CARD s) - 1)``,
  rw[CARD_PPOW]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note:
> type_of ``prime``;
val it = ":num -> bool": hol_type

Thus prime is also a set, or prime = {p | prime p}
*)

(* Theorem: p IN prime <=> prime p *)
(* Proof: by IN_DEF *)
val in_prime = store_thm(
  "in_prime",
  ``!p. p IN prime <=> prime p``,
  rw[IN_DEF]);

(* Theorem: (Generalized Euclid's Lemma)
            If prime p divides a PROD_SET, it divides a member of the PROD_SET.
            FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b *)
(* Proof: by induction of the PROD_SET, apply Euclid's Lemma.
- P_EUCLIDES;
> val it =
    |- !p a b. prime p /\ p divides (a * b) ==> p divides a \/ p divides b : thm
   By finite induction on s.
   Base case: prime p /\ p divides (PROD_SET {}) ==> F
     Since PROD_SET {} = 1        by PROD_SET_THM
       and p divides 1 <=> p = 1  by DIVIDES_ONE
       but prime p ==> p <> 1     by NOT_PRIME_1
       This gives the contradiction.
   Step case: FINITE s /\ (!p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b) /\
              e NOTIN s /\ prime p /\ p divides (PROD_SET (e INSERT s)) ==>
              ?b. ((b = e) \/ b IN s) /\ p divides b
     Note PROD_SET (e INSERT s) = e * PROD_SET s   by PROD_SET_THM, DELETE_NON_ELEMENT, e NOTIN s.
     So prime p /\ p divides (PROD_SET (e INSERT s))
     ==> p divides e, or p divides (PROD_SET s)    by P_EUCLIDES
     If p divides e, just take b = e.
     If p divides (PROD_SET s), there is such b    by induction hypothesis
*)
val PROD_SET_EUCLID = store_thm(
  "PROD_SET_EUCLID",
  ``!s. FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b``,
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >-
  metis_tac[PROD_SET_EMPTY, DIVIDES_ONE, NOT_PRIME_1] >>
  `PROD_SET (e INSERT s) = e * PROD_SET s`
    by metis_tac[PROD_SET_THM, DELETE_NON_ELEMENT] >>
  Cases_on `p divides e` >-
  metis_tac[] >>
  metis_tac[P_EUCLIDES]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
