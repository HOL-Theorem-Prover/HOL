(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "triangle";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)

(* Get dependent theories local *)

(* Get dependent theories in lib *)
(* val _ = load "EulerTheory"; *)
open EulerTheory; (* for upto_by_count *)
(* (* val _ = load "helperFunctionTheory"; -- in EulerTheory *) *)
(* (* val _ = load "helperNumTheory"; -- in helperFunctionTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in helperFunctionTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* val _ = load "helperListTheory"; *)
open helperListTheory;

(* open dependent theories *)
open arithmeticTheory;
open pred_setTheory;
open listTheory;

(* open dependent theories *)
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* val _ = load "binomialTheory"; *)
open binomialTheory;

(* use listRange: [1 .. 3] = [1; 2; 3], [1 ..< 3] = [1; 2] *)
(* val _ = load "listRangeTheory"; *)
open listRangeTheory;
open rich_listTheory; (* for EVERY_REVERSE *)
open relationTheory; (* for RTC *)


(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle Documentation                                   *)
(* ------------------------------------------------------------------------- *)
(* Type: (# are temp)
   triple                = <| a: num; b: num; c: num |>
#  path                  = :num list
   Overloading:
   leibniz_vertical n    = [1 .. (n+1)]
   leibniz_up       n    = REVERSE (leibniz_vertical n)
   leibniz_horizontal n  = GENLIST (leibniz n) (n + 1)
   binomial_horizontal n = GENLIST (binomial n) (n + 1)
#  ta                    = (triplet n k).a
#  tb                    = (triplet n k).b
#  tc                    = (triplet n k).c
   p1 zigzag p2          = leibniz_zigzag p1 p2
   p1 wriggle p2         = RTC leibniz_zigzag p1 p2
   leibniz_col_arm a b n = MAP (\x. leibniz (a - x) b) [0 ..< n]
   leibniz_seg_arm a b n = MAP (\x. leibniz a (b + x)) [0 ..< n]

   leibniz_seg n k h     = IMAGE (\j. leibniz n (k + j)) (count h)
   leibniz_row n h       = IMAGE (leibniz n) (count h)
   leibniz_col h         = IMAGE (\i. leibniz i 0) (count h)
   lcm_run n             = list_lcm [1 .. n]
#  beta n k              = k * binomial n k
#  beta_horizontal n     = GENLIST (beta n o SUC) n
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   RTC_TRANS          |- R^* x y /\ R^* y z ==> R^* x z

   Leibniz Triangle (Denominator form):
#  leibniz_def        |- !n k. leibniz n k = (n + 1) * binomial n k
   leibniz_0_n        |- !n. leibniz 0 n = if n = 0 then 1 else 0
   leibniz_n_0        |- !n. leibniz n 0 = n + 1
   leibniz_n_n        |- !n. leibniz n n = n + 1
   leibniz_less_0     |- !n k. n < k ==> (leibniz n k = 0)
   leibniz_sym        |- !n k. k <= n ==> (leibniz n k = leibniz n (n - k))
   leibniz_monotone   |- !n k. k < HALF n ==> leibniz n k < leibniz n (k + 1)
   leibniz_pos        |- !n k. k <= n ==> 0 < leibniz n k
   leibniz_eq_0       |- !n k. (leibniz n k = 0) <=> n < k
   leibniz_alt        |- !n. leibniz n = (\j. (n + 1) * j) o binomial n
   leibniz_def_alt    |- !n k. leibniz n k = (\j. (n + 1) * j) (binomial n k)
   leibniz_up_eqn     |- !n. 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k
   leibniz_up         |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)
   leibniz_up_alt     |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
   leibniz_right_eqn  |- !n. 0 < n ==> !k. (k + 1) * leibniz n (k + 1) = (n - k) * leibniz n k
   leibniz_right      |- !n. 0 < n ==> !k. leibniz n (k + 1) = (n - k) * leibniz n k DIV (k + 1)
   leibniz_property   |- !n. 0 < n ==> !k. leibniz n k * leibniz (n - 1) k =
                                           leibniz n (k + 1) * (leibniz n k - leibniz (n - 1) k)
   leibniz_formula    |- !n k. k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k)))
   leibniz_recurrence |- !n. 0 < n ==> !k. k < n ==> (leibniz n (k + 1) = leibniz n k *
                                           leibniz (n - 1) k DIV (leibniz n k - leibniz (n - 1) k))
   leibniz_n_k        |- !n k. 0 < k /\ k <= n ==> (leibniz n k =
                                           leibniz n (k - 1) * leibniz (n - 1) (k - 1)
                                           DIV (leibniz n (k - 1) - leibniz (n - 1) (k - 1)))
   leibniz_lcm_exchange  |- !n. 0 < n ==> !k. lcm (leibniz n k) (leibniz (n - 1) k) =
                                              lcm (leibniz n k) (leibniz n (k + 1))
   leibniz_middle_lower  |- !n. 4 ** n <= leibniz (TWICE n) n

   LCM of a list of numbers:
#  list_lcm_def          |- (list_lcm [] = 1) /\ !h t. list_lcm (h::t) = lcm h (list_lcm t)
   list_lcm_nil          |- list_lcm [] = 1
   list_lcm_cons         |- !h t. list_lcm (h::t) = lcm h (list_lcm t)
   list_lcm_sing         |- !x. list_lcm [x] = x
   list_lcm_snoc         |- !x l. list_lcm (SNOC x l) = lcm x (list_lcm l)
   list_lcm_map_times    |- !n l. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l
   list_lcm_pos          |- !l. EVERY_POSITIVE l ==> 0 < list_lcm l
   list_lcm_pos_alt      |- !l. POSITIVE l ==> 0 < list_lcm l
   list_lcm_lower_bound  |- !l. EVERY_POSITIVE l ==> SUM l <= LENGTH l * list_lcm l
   list_lcm_lower_bound_alt          |- !l. POSITIVE l ==> SUM l <= LENGTH l * list_lcm l
   list_lcm_is_common_multiple       |- !x l. MEM x l ==> x divides (list_lcm l)
   list_lcm_is_least_common_multiple |- !l m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m
   list_lcm_append       |- !l1 l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2)
   list_lcm_append_3     |- !l1 l2 l3. list_lcm (l1 ++ l2 ++ l3) = list_lcm [list_lcm l1; list_lcm l2; list_lcm l3]
   list_lcm_reverse      |- !l. list_lcm (REVERSE l) = list_lcm l
   list_lcm_suc          |- !n. list_lcm [1 .. n + 1] = lcm (n + 1) (list_lcm [1 .. n])
   list_lcm_nonempty_lower      |- !l. l <> [] /\ EVERY_POSITIVE l ==> SUM l DIV LENGTH l <= list_lcm l
   list_lcm_nonempty_lower_alt  |- !l. l <> [] /\ POSITIVE l ==> SUM l DIV LENGTH l <= list_lcm l
   list_lcm_divisor_lcm_pair    |- !l x y. MEM x l /\ MEM y l ==> lcm x y divides list_lcm l
   list_lcm_lower_by_lcm_pair   |- !l x y. POSITIVE l /\ MEM x l /\ MEM y l ==> lcm x y <= list_lcm l
   list_lcm_upper_by_common_multiple
                                |- !l m. 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m
   list_lcm_by_FOLDR     |- !ls. list_lcm ls = FOLDR lcm 1 ls
   list_lcm_by_FOLDL     |- !ls. list_lcm ls = FOLDL lcm 1 ls

   Lists in Leibniz Triangle:

   Veritcal Lists in Leibniz Triangle
   leibniz_vertical_alt      |- !n. leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1)
   leibniz_vertical_0        |- leibniz_vertical 0 = [1]
   leibniz_vertical_len      |- !n. LENGTH (leibniz_vertical n) = n + 1
   leibniz_vertical_not_nil  |- !n. leibniz_vertical n <> []
   leibniz_vertical_pos      |- !n. EVERY_POSITIVE (leibniz_vertical n)
   leibniz_vertical_pos_alt  |- !n. POSITIVE (leibniz_vertical n)
   leibniz_vertical_mem      |- !n x. 0 < x /\ x <= n + 1 <=> MEM x (leibniz_vertical n)
   leibniz_vertical_snoc     |- !n. leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n)

   leibniz_up_0              |- leibniz_up 0 = [1]
   leibniz_up_len            |- !n. LENGTH (leibniz_up n) = n + 1
   leibniz_up_pos            |- !n. EVERY_POSITIVE (leibniz_up n)
   leibniz_up_mem            |- !n x. 0 < x /\ x <= n + 1 <=> MEM x (leibniz_up n)
   leibniz_up_cons           |- !n. leibniz_up (n + 1) = n + 2::leibniz_up n

   leibniz_horizontal_0      |- leibniz_horizontal 0 = [1]
   leibniz_horizontal_len    |- !n. LENGTH (leibniz_horizontal n) = n + 1
   leibniz_horizontal_el     |- !n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)
   leibniz_horizontal_mem    |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
   leibniz_horizontal_mem_iff   |- !n k. MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n
   leibniz_horizontal_member    |- !n x. MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k)
   leibniz_horizontal_element   |- !n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)
   leibniz_horizontal_head   |- !n. TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2]
   leibniz_horizontal_divisor|- !n k. k <= n ==> leibniz n k divides list_lcm (leibniz_horizontal n)
   leibniz_horizontal_pos    |- !n. EVERY_POSITIVE (leibniz_horizontal n)
   leibniz_horizontal_pos_alt|- !n. POSITIVE (leibniz_horizontal n)
   leibniz_horizontal_alt    |- !n. leibniz_horizontal n = MAP (\j. (n + 1) * j) (binomial_horizontal n)
   leibniz_horizontal_lcm_alt|- !n. list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)
   leibniz_horizontal_sum          |- !n. SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n)
   leibniz_horizontal_sum_eqn      |- !n. SUM (leibniz_horizontal n) = (n + 1) * 2 ** n:
   leibniz_horizontal_average      |- !n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) =
                                          SUM (binomial_horizontal n)
   leibniz_horizontal_average_eqn  |- !n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n

   Using Triplet and Paths:
   triplet_def               |- !n k. triplet n k =
                                           <|a := leibniz n k;
                                             b := leibniz (n + 1) k;
                                             c := leibniz (n + 1) (k + 1)
                                            |>
   leibniz_triplet_member    |- !n k. (ta = leibniz n k) /\
                                      (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1))
   leibniz_right_entry       |- !n k. (k + 1) * tc = (n + 1 - k) * tb
   leibniz_up_entry          |- !n k. (n + 2) * ta = (n + 1 - k) * tb
   leibniz_triplet_property  |- !n k. ta * tb = tc * (tb - ta)
   leibniz_triplet_lcm       |- !n k. lcm tb ta = lcm tb tc

   Zigzag Path in Leibniz Triangle:
   leibniz_zigzag_def        |- !p1 p2. p1 zigzag p2 <=>
                                ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)
   list_lcm_zigzag           |- !p1 p2. p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2)
   leibniz_zigzag_tail       |- !p1 p2. p1 zigzag p2 ==> !x. [x] ++ p1 zigzag [x] ++ p2
   leibniz_horizontal_zigzag |- !n k. k <= n ==>
                                TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
                                TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
   leibniz_triplet_0         |- leibniz_up 1 zigzag leibniz_horizontal 1

   Wriggle Paths in Leibniz Triangle:
   list_lcm_wriggle         |- !p1 p2. p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2)
   leibniz_zigzag_wriggle   |- !p1 p2. p1 zigzag p2 ==> p1 wriggle p2
   leibniz_wriggle_tail     |- !p1 p2. p1 wriggle p2 ==> !x. [x] ++ p1 wriggle [x] ++ p2
   leibniz_wriggle_refl     |- !p1. p1 wriggle p1
   leibniz_wriggle_trans    |- !p1 p2 p3. p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3
   leibniz_horizontal_wriggle_step  |- !n k. k <= n + 1 ==>
      TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle leibniz_horizontal (n + 1)
   leibniz_horizontal_wriggle |- !n. [leibniz (n + 1) 0] ++ leibniz_horizontal n wriggle leibniz_horizontal (n + 1)

   Path Transform keeping LCM:
   leibniz_up_wriggle_horizontal  |- !n. leibniz_up n wriggle leibniz_horizontal n
   leibniz_lcm_property           |- !n. list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)
   leibniz_vertical_divisor       |- !n k. k <= n ==> leibniz n k divides list_lcm (leibniz_vertical n)

   Lower Bound of Leibniz LCM:
   leibniz_horizontal_lcm_lower  |- !n. 2 ** n <= list_lcm (leibniz_horizontal n)
   leibniz_vertical_lcm_lower    |- !n. 2 ** n <= list_lcm (leibniz_vertical n)
   lcm_lower_bound               |- !n. 2 ** n <= list_lcm [1 .. (n + 1)]

   Leibniz LCM Invariance:
   leibniz_col_arm_0    |- !a b. leibniz_col_arm a b 0 = []
   leibniz_seg_arm_0    |- !a b. leibniz_seg_arm a b 0 = []
   leibniz_col_arm_1    |- !a b. leibniz_col_arm a b 1 = [leibniz a b]
   leibniz_seg_arm_1    |- !a b. leibniz_seg_arm a b 1 = [leibniz a b]
   leibniz_col_arm_len  |- !a b n. LENGTH (leibniz_col_arm a b n) = n
   leibniz_seg_arm_len  |- !a b n. LENGTH (leibniz_seg_arm a b n) = n
   leibniz_col_arm_el   |- !n k. k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b
   leibniz_seg_arm_el   |- !n k. k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k)
   leibniz_seg_arm_head |- !a b n. TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b]
   leibniz_col_arm_cons |- !a b n. leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b::leibniz_col_arm a b n

   leibniz_seg_arm_zigzag_step       |- !n k. k < n ==> !a b.
                   TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
                   TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
   leibniz_seg_arm_wriggle_step      |- !n k. k < n + 1 ==> !a b.
                   TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                   leibniz_seg_arm (a + 1) b (n + 1)
   leibniz_seg_arm_wriggle_row_arm   |- !a b n. [leibniz (a + 1) b] ++ leibniz_seg_arm a b n wriggle
                                                leibniz_seg_arm (a + 1) b (n + 1)
   leibniz_col_arm_wriggle_row_arm   |- !a b n. b <= a /\ n <= a + 1 - b ==>
                                                leibniz_col_arm a b n wriggle leibniz_seg_arm a b n
   leibniz_lcm_invariance            |- !a b n. b <= a /\ n <= a + 1 - b ==>
                                        (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n))
   leibniz_col_arm_n_0               |- !n. leibniz_col_arm n 0 (n + 1) = leibniz_up n
   leibniz_seg_arm_n_0               |- !n. leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n
   leibniz_up_wriggle_horizontal_alt |- !n. leibniz_up n wriggle leibniz_horizontal n
   leibniz_up_lcm_eq_horizontal_lcm  |- !n. list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n)

   Set GCD as Big Operator:
   big_gcd_def                |- !s. big_gcd s = ITSET gcd s 0
   big_gcd_empty              |- big_gcd {} = 0
   big_gcd_sing               |- !x. big_gcd {x} = x
   big_gcd_reduction          |- !s x. FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s))
   big_gcd_is_common_divisor  |- !s. FINITE s ==> !x. x IN s ==> big_gcd s divides x
   big_gcd_is_greatest_common_divisor
                              |- !s. FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides big_gcd s
   big_gcd_insert             |- !s. FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s)
   big_gcd_two                |- !x y. big_gcd {x; y} = gcd x y
   big_gcd_positive           |- !s. FINITE s /\ s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s
   big_gcd_map_times          |- !s. FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s

   Set LCM as Big Operator:
   big_lcm_def                |- !s. big_lcm s = ITSET lcm s 1
   big_lcm_empty              |- big_lcm {} = 1
   big_lcm_sing               |- !x. big_lcm {x} = x
   big_lcm_reduction          |- !s x. FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s))
   big_lcm_is_common_multiple |- !s. FINITE s ==> !x. x IN s ==> x divides big_lcm s
   big_lcm_is_least_common_multiple
                              |- !s. FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> big_lcm s divides m
   big_lcm_insert             |- !s. FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s)
   big_lcm_two                |- !x y. big_lcm {x; y} = lcm x y
   big_lcm_positive           |- !s. FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s
   big_lcm_map_times          |- !s. FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s

   LCM Lower bound using big LCM:
   leibniz_seg_def            |- !n k h. leibniz_seg n k h = {leibniz n (k + j) | j IN count h}
   leibniz_row_def            |- !n h. leibniz_row n h = {leibniz n j | j IN count h}
   leibniz_col_def            |- !h. leibniz_col h = {leibniz j 0 | j IN count h}
   leibniz_col_eq_natural     |- !n. leibniz_col n = natural n
   big_lcm_seg_transform      |- !n k h. lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) =
                                         big_lcm (leibniz_seg (n + 1) k (h + 1))
   big_lcm_row_transform      |- !n h. lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) =
                                       big_lcm (leibniz_row (n + 1) (h + 1))
   big_lcm_corner_transform   |- !n. big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1))
   big_lcm_count_lower_bound  |- !f n. (!x. x IN count (n + 1) ==> 0 < f x) ==>
                                       SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1)))
   big_lcm_natural_eqn        |- !n. big_lcm (natural (n + 1)) =
                                     (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))
   big_lcm_lower_bound        |- !n. 2 ** n <= big_lcm (natural (n + 1))
   big_lcm_eq_list_lcm        |- !l. big_lcm (set l) = list_lcm l

   List LCM depends only on its set of elements:
   list_lcm_absorption        |- !x l. MEM x l ==> (list_lcm (x::l) = list_lcm l)
   list_lcm_nub               |- !l. list_lcm (nub l) = list_lcm l
   list_lcm_nub_eq_if_set_eq  |- !l1 l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2))
   list_lcm_eq_if_set_eq      |- !l1 l2. (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2)

   Set LCM by List LCM:
   set_lcm_def                |- !s. set_lcm s = list_lcm (SET_TO_LIST s)
   set_lcm_empty              |- set_lcm {} = 1
   set_lcm_nonempty           |- !s. FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s)))
   set_lcm_sing               |- !x. set_lcm {x} = x
   set_lcm_eq_list_lcm        |- !l. set_lcm (set l) = list_lcm l
   set_lcm_eq_big_lcm         |- !s. FINITE s ==> (set_lcm s = big_lcm s)
   set_lcm_insert             |- !s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s)
   set_lcm_is_common_multiple        |- !x s. FINITE s /\ x IN s ==> x divides set_lcm s
   set_lcm_is_least_common_multiple  |- !s m. FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m
   pairwise_coprime_prod_set_eq_set_lcm
                             |- !s. FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)
   pairwise_coprime_prod_set_divides
                             |- !s m. FINITE s /\ PAIRWISE_COPRIME s /\
                                      (!x. x IN s ==> x divides m) ==> PROD_SET s divides m

   Nair's Trick (direct):
   lcm_run_by_FOLDL          |- !n. lcm_run n = FOLDL lcm 1 [1 .. n]
   lcm_run_by_FOLDR          |- !n. lcm_run n = FOLDR lcm 1 [1 .. n]
   lcm_run_0                 |- lcm_run 0 = 1
   lcm_run_1                 |- lcm_run 1 = 1
   lcm_run_suc               |- !n. lcm_run (n + 1) = lcm (n + 1) (lcm_run n)
   lcm_run_pos               |- !n. 0 < lcm_run n
   lcm_run_small             |- (lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\
                                (lcm_run 5 = 60) /\ (lcm_run 6 = 60) /\ (lcm_run 7 = 420) /\
                                (lcm_run 8 = 840) /\ (lcm_run 9 = 2520)
   lcm_run_divisors          |- !n. n + 1 divides lcm_run (n + 1) /\ lcm_run n divides lcm_run (n + 1)
   lcm_run_monotone          |- !n. lcm_run n <= lcm_run (n + 1)
   lcm_run_lower             |- !n. 2 ** n <= lcm_run (n + 1)
   lcm_run_leibniz_divisor   |- !n k. k <= n ==> leibniz n k divides lcm_run (n + 1)
   lcm_run_lower_odd         |- !n. n * 4 ** n <= lcm_run (TWICE n + 1)
   lcm_run_lower_even        |- !n. n * 4 ** n <= lcm_run (TWICE (n + 1))

   lcm_run_odd_lower         |- !n. ODD n ==> HALF n * HALF (2 ** n) <= lcm_run n
   lcm_run_even_lower        |- !n. EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n
   lcm_run_odd_lower_alt     |- !n. ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n
   lcm_run_even_lower_alt    |- !n. EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n
   lcm_run_lower_better      |- !n. 7 <= n ==> 2 ** n <= lcm_run n

   Nair's Trick (rework):
   lcm_run_odd_factor        |- !n. 0 < n ==> n * leibniz (TWICE n) n divides lcm_run (TWICE n + 1)
   lcm_run_lower_odd         |- !n. n * 4 ** n <= lcm_run (TWICE n + 1)
   lcm_run_lower_odd_iff     |- !n. ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n)
   lcm_run_lower_even_iff    |- !n. EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n)
   lcm_run_lower_better_iff  |- !n. 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n

   Nair's Trick (consecutive):
   lcm_upto_def              |- (lcm_upto 0 = 1) /\ !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n)
   lcm_upto_0                |- lcm_upto 0 = 1
   lcm_upto_SUC              |- !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n)
   lcm_upto_alt              |- (lcm_upto 0 = 1) /\ !n. lcm_upto (n + 1) = lcm (n + 1) (lcm_upto n)
   lcm_upto_1                |- lcm_upto 1 = 1
   lcm_upto_small            |- (lcm_upto 2 = 2) /\ (lcm_upto 3 = 6) /\ (lcm_upto 4 = 12) /\
                                (lcm_upto 5 = 60) /\ (lcm_upto 6 = 60) /\ (lcm_upto 7 = 420) /\
                                (lcm_upto 8 = 840) /\ (lcm_upto 9 = 2520) /\ (lcm_upto 10 = 2520)
   lcm_upto_eq_list_lcm      |- !n. lcm_upto n = list_lcm [1 .. n]
   lcm_upto_lower            |- !n. 2 ** n <= lcm_upto (n + 1)
   lcm_upto_divisors         |- !n. n + 1 divides lcm_upto (n + 1) /\ lcm_upto n divides lcm_upto (n + 1)
   lcm_upto_monotone         |- !n. lcm_upto n <= lcm_upto (n + 1)
   lcm_upto_leibniz_divisor  |- !n k. k <= n ==> leibniz n k divides lcm_upto (n + 1)
   lcm_upto_lower_odd        |- !n. n * 4 ** n <= lcm_upto (TWICE n + 1)
   lcm_upto_lower_even       |- !n. n * 4 ** n <= lcm_upto (TWICE (n + 1))
   lcm_upto_lower_better     |- !n. 7 <= n ==> 2 ** n <= lcm_upto n

   Simple LCM lower bounds:
   lcm_run_lower_simple      |- !n. HALF (n + 1) <= lcm_run n
   lcm_run_alt               |- !n. lcm_run n = lcm_run (n - 1 + 1)
   lcm_run_lower_good        |- !n. 2 ** (n - 1) <= lcm_run n

   Upper Bound by Leibniz Triangle:
   leibniz_eqn               |- !n k. leibniz n k = (n + 1 - k) * binomial (n + 1) k
   leibniz_right_alt         |- !n k. leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1)
   leibniz_binomial_identity         |- !m n k. k <= m /\ m <= n ==>
                   (leibniz n k * binomial (n - k) (m - k) = leibniz m k * binomial (n + 1) (m + 1))
   leibniz_divides_leibniz_factor    |- !m n k. k <= m /\ m <= n ==>
                                         leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
   leibniz_horizontal_member_divides |- !m n x. n <= TWICE m + 1 /\ m <= n /\
                                                MEM x (leibniz_horizontal n) ==>
                               x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
   lcm_run_divides_property  |- !m n. n <= TWICE m /\ m <= n ==>
                                      lcm_run n divides lcm_run m * binomial n m
   lcm_run_bound_recurrence  |- !m n. n <= TWICE m /\ m <= n ==> lcm_run n <= lcm_run m * binomial n m
   lcm_run_upper_bound       |- !n. lcm_run n <= 4 ** n

   Beta Triangle:
   beta_0_n        |- !n. beta 0 n = 0
   beta_n_0        |- !n. beta n 0 = 0
   beta_less_0     |- !n k. n < k ==> (beta n k = 0)
   beta_eqn        |- !n k. beta (n + 1) (k + 1) = leibniz n k
   beta_alt        |- !n k. 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1))
   beta_pos        |- !n k. 0 < k /\ k <= n ==> 0 < beta n k
   beta_eq_0       |- !n k. (beta n k = 0) <=> (k = 0) \/ n < k
   beta_sym        |- !n k. k <= n ==> (beta n k = beta n (n - k + 1))

   Beta Horizontal List:
   beta_horizontal_0            |- beta_horizontal 0 = []
   beta_horizontal_len          |- !n. LENGTH (beta_horizontal n) = n
   beta_horizontal_eqn          |- !n. beta_horizontal (n + 1) = leibniz_horizontal n
   beta_horizontal_alt          |- !n. 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1))
   beta_horizontal_mem          |- !n k. 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n)
   beta_horizontal_mem_iff      |- !n k. MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n
   beta_horizontal_member       |- !n x. MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)
   beta_horizontal_element      |- !n k. k < n ==> (EL k (beta_horizontal n) = beta n (k + 1))
   lcm_run_by_beta_horizontal   |- !n. 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n))
   lcm_run_beta_divisor         |- !n k. 0 < k /\ k <= n ==> beta n k divides lcm_run n
   beta_divides_beta_factor     |- !m n k. k <= m /\ m <= n ==> beta n k divides beta m k * binomial n m
   lcm_run_divides_property_alt |- !m n. n <= TWICE m /\ m <= n ==> lcm_run n divides binomial n m * lcm_run m
   lcm_run_upper_bound          |- !n. lcm_run n <= 4 ** n

   LCM Lower Bound using Maximum:
   list_lcm_ge_max               |- !l. POSITIVE l ==> MAX_LIST l <= list_lcm l
   lcm_lower_bound_by_list_lcm   |- !n. (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)]
   big_lcm_ge_max                |- !s. FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s
   lcm_lower_bound_by_big_lcm    |- !n. (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1))

   Consecutive LCM function:
   lcm_lower_bound_by_list_lcm_stirling  |- Stirling /\ (!n c. n DIV SQRT (c * (n - 1)) = SQRT (n DIV c)) ==>
                                            !n. ODD n ==> SQRT (n DIV (2 * pi)) * 2 ** n <= list_lcm [1 .. n]
   big_lcm_non_decreasing                |- !n. big_lcm (natural n) <= big_lcm (natural (n + 1))
   lcm_lower_bound_by_big_lcm_stirling   |- Stirling /\ (!n c. n DIV SQRT (c * (n - 1)) = SQRT (n DIV c)) ==>
                                            !n. ODD n ==> SQRT (n DIV (2 * pi)) * 2 ** n <= big_lcm (natural n)

   Extra Theorems:
   gcd_prime_product_property   |- !p m n. prime p /\ m divides n /\ ~(p * m divides n) ==> (gcd (p * m) n = m)
   lcm_prime_product_property   |- !p m n. prime p /\ m divides n /\ ~(p * m divides n) ==> (lcm (p * m) n = p * n)
   list_lcm_prime_factor        |- !p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)
   list_lcm_prime_factor_member |- !p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x

*)

(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(*

Leibniz Harmonic Triangle (fraction form)

       c <= r
r = 1  1
r = 2  1/2  1/2
r = 3  1/3  1/6   1/3
r = 4  1/4  1/12  1/12  1/4
r = 5  1/5  1/10  1/20  1/10  1/5

In general,  L(r,1) = 1/r,  L(r,c) = |L(r-1,c-1) - L(r,c-1)|

Solving, L(r,c) = 1/(r C(r-1,c-1)) = 1/(c C(r,c))
where C(n,m) is the binomial coefficient of Pascal Triangle.

c = 1 are the 1/(1 * natural numbers
c = 2 are the 1/(2 * triangular numbers)
c = 3 are the 1/(3 * tetrahedral numbers)

Sum of denominators of n-th row = n 2**(n-1).

Note that  L(r,c) = Integral(0,1) x ** (c-1) * (1-x) ** (r-c) dx

Another form:  L(n,1) = 1/n, L(n,k) = L(n-1,k-1) - L(n,k-1)
Solving,  L(n,k) = 1/ k C(n,k) = 1/ n C(n-1,k-1)

Still another notation  H(n,r) = 1/ (n+1)C(n,r) = (n-r)!r!/(n+1)!  for 0 <= r <= n

Harmonic Denominator Number Triangle (integer form)
g(d,n) = 1/H(d,n)     where H(d,h) is the Leibniz Harmonic Triangle
g(d,n) = (n+d)C(d,n)  where C(d,h) is the Pascal's Triangle.
g(d,n) = n(n+1)...(n+d)/d!

(k+1)-th row of Pascal's triangle:  x^4 + 4x^3 + 6x^2 + 4x + 1
Perform differentiation, d/dx -> 4x^3 + 12x^2 + 12x + 4
which is k-th row of Harmonic Denominator Number Triangle.

(k+1)-th row of Pascal's triangle: (x+1)^(k+1)
k-th row of Harmonic Denominator Number Triangle: d/dx[(x+1)^(k+1)]

  d/dx[(x+1)^(k+1)]
= d/dx[SUM C(k+1,j) x^j]    j = 0...(k+1)
= SUM C(k+1,j) d/dx[x^j]
= SUM C(k+1,j) j x^(j-1)    j = 1...(k+1)
= SUM C(k+1,j+1) (j+1) x^j  j = 0...k
= SUM D(k,j) x^j            with D(k,j) = (j+1) C(k+1,j+1)  ???

*)

(* Another presentation of triangles:

The harmonic triangle of Leibniz
    1/1   1/2   1/3   1/4    1/5   .... harmonic fractions
       1/2   1/6   1/12   1/20     .... successive difference
          1/3   1/12   1/30   ...
            1/4     1/20  ... ...
                1/5   ... ... ...

Pascal's triangle
    1    1   1   1   1   1   1     .... units
       1   2   3   4   5   6       .... sum left and above
         1   3   6   10  15  21
           1   4   10  20  35
             1   5   15  35
               1   6   21


*)

(* LCM Lemma

(n+1) lcm (C(n,0) to C(n,n)) = lcm (1 to (n+1))

m-th number in the n-th row of Leibniz triangle is:  1/ (n+1)C(n,m)

LHS = (n+1) LCM (C(n,0), C(n,1), ..., C(n,n)) = lcd of fractions in n-th row of Leibniz triangle.

Any such number is an integer linear combination of fractions on triangle’s sides
1/1, 1/2, 1/3, ... 1/n, and vice versa.

So LHS = lcd (1/1, 1/2, 1/3, ..., 1/n) = RHS = lcm (1,2,3, ..., (n+1)).

0-th row:               1
1-st row:           1/2  1/2
2-nd row:        1/3  1/6  1/3
3-rd row:    1/4  1/12  1/12  1/4
4-th row: 1/5  1/20  1/30  1/20  1/5

4-th row: 1/5 C(4,m), C(4,m) = 1 4 6 4 1, hence 1/5 1/20 1/30 1/20 1/5
  lcd (1/5 1/20 1/30 1/20 1/5)
= lcm (5, 20, 30, 20, 5)
= lcm (5 C(4,0), 5 C(4,1), 5 C(4,2), 5 C(4,3), 5 C(4,4))
= 5 lcm (C(4,0), C(4,1), C(4,2), C(4,3), C(4,4))

But 1/5 = harmonic
    1/20 = 1/4 - 1/5 = combination of harmonic
    1/30 = 1/12 - 1/20 = (1/3 - 1/4) - (1/4 - 1/5) = combination of harmonic

  lcd (1/5 1/20 1/30 1/20 1/5)
= lcd (combination of harmonic from 1/1 to 1/5)
= lcd (1/1 to 1/5)
= lcm (1 to 5)

Theorem:  lcd (1/x 1/y 1/z) = lcm (x y z)
Theorem:  lcm (kx ky kz) = k lcm (x y z)
Theorem:  lcd (combination of harmonic from 1/1 to 1/n) = lcd (1/1 to 1/n)
Then apply first theorem, lcd (1/1 to 1/n) = lcm (1 to n)
*)

(* LCM Bound
   0 < n ==> 2^(n-1) < lcm (1 to n)

  lcm (1 to n)
= n lcm (C(n-1,0) to C(n-1,n-1))  by LCM Lemma
>= n max (0 <= j <= n-1) C(n-1,j)
>= SUM (0 <= j <= n-1) C(n-1,j)
= 2^(n-1)

  lcm (1 to 5)
= 5 lcm (C(4,0), C(4,1), C(4,2), C(4,3), C(4,4))


>= C(4,0) + C(4,1) + C(4,2) + C(4,3) + C(4,4)
= (1 + 1)^4
= 2^4

  lcm (1 to 5)             = 1x2x3x4x5/2 = 60
= 5 lcm (1 4 6 4 1)        = 5 x 12
=  lcm (1 4 6 4 1)         --> unfold 5x to add 5 times
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
>= 1 + 4 + 6 + 4 + 1       --> pick one of each 5 C(n,m), i.e. diagonal
= (1 + 1)^4                --> fold back binomial
= 2^4                      = 16

Actually, can take 5 lcm (1 4 6 4 1) >= 5 x 6 = 30,
but this will need estimation of C(n, n/2), or C(2n,n), involving Stirling's formula.

Theorem: lcm (x y z) >= x  or lcm (x y z) >= y  or lcm (x y z) >= z

*)

(*

More generally, there is an identity for 0 <= k <= n:

(n+1) lcm (C(n,0), C(n,1), ..., C(n,k)) = lcm (n+1, n, n-1, ..., n+1-k)

This is simply that fact that any integer linear combination of
f(x), delta f(x), delta^2 f(x), ..., delta^k f(x)
is an integer linear combination of f(x), f(x-1), f(x-2), ..., f(x-k)
where delta is the difference operator, f(x) = 1/x, and x = n+1.

BTW, Leibnitz harmonic triangle too gives this identity.

That's correct, but the use of absolute values in the Leibniz triangle and
its specialized definition somewhat obscures the generic, linear nature of the identity.

  f(x) = f(n+1)   = 1/(n+1)
f(x-1) = f(n)     = 1/n
f(x-2) = f(n-1)   = 1/(n-1)
f(x-k) = f(n+1-k) = 1/(n+1-k)

        f(x) = f(n+1) = 1/(n+1) = 1/(n+1)C(n,0)
  delta f(x) = f(x-1) - f(x) = 1/n - 1/(n+1) = 1/n(n+1) = 1/(n+1)C(n,1)
             = C(1,0) f(x-1) - C(1,1) f(x)
delta^2 f(x) = delta f(x-1) - delta f(x) = 1/(n-1)n - 1/n(n+1)
             = (n(n+1) - n(n-1))/(n)(n+1)(n)(n-1)
             = 2n/n(n+1)n(n-1) = 1/(n+1)(n(n-1)/2) = 1/(n+1)C(n,2)
delta^2 f(x) = delta f(x-1) - delta f(x)
             = (f(x-2) - f(x-1)) - (f(x-1) - f(x))
             = f(x-2) - 2 f(x-1) + f(x)
             = C(2,0) f(x-2) - C(2,1) f(x-1) + C(2,2) f(x)
delta^3 f(x) = delta^2 f(x-1) - delta^2 f(x)
             = (f(x-3) - 2 f(x-2) + f(x-1)) - (f(x-2) - 2 f(x-1) + f(x))
             = f(x-3) - 3 f(x-2) + 3 f(x-1) - f(x)
             = C(3,0) f(x-3) - C(3,1) f(x-2) + C(3,2) f(x-2) - C(3,3) f(x)

delta^k f(x) = C(k,0) f(x-k) - C(k,1) f(x-k+1) + ... + (-1)^k C(k,k) f(x)
             = SUM(0 <= j <= k) (-1)^k C(k,j) f(x-k+j)
Also,
        f(x) = 1/(n+1)C(n,0)
  delta f(x) = 1/(n+1)C(n,1)
delta^2 f(x) = 1/(n+1)C(n,2)
delta^k f(x) = 1/(n+1)C(n,k)

so lcd (f(x), df(x), d^2f(x), ..., d^kf(x))
 = lcm ((n+1)C(n,0),(n+1)C(n,1),...,(n+1)C(n,k))   by lcd-to-lcm
 = lcd (f(x), f(x-1), f(x-2), ..., f(x-k))         by linear combination
 = lcm ((n+1), n, (n-1), ..., (n+1-k))             by lcd-to-lcm

How to formalize:
lcd (f(x), df(x), d^2f(x), ..., d^kf(x)) = lcd (f(x), f(x-1), f(x-2), ..., f(x-k))

Simple case: lcd (f(x), df(x)) = lcd (f(x), f(x-1))

  lcd (f(x), df(x))
= lcd (f(x), f(x-1) - f(x))
= lcd (f(x), f(x-1))

Can we have
  LCD {f(x), df(x)}
= LCD {f(x), f(x-1) - f(x)} = LCD {1/x, 1/(x-1) - 1/x}
= LCD {f(x), f(x-1), f(x)}  = lcm {x, x(x-1)}
= LCD {f(x), f(x-1)}        = x(x-1) = lcm {x, x-1} = LCD {1/x, 1/(x-1)}

*)

(* Step 1: From Pascal's Triangle to Leibniz's Triangle

Pascal's Triangle:

row 0    1
row 1    1   1
row 2    1   2   1
row 3    1   3   3   1
row 4    1   4   6   4   1
row 5    1   5  10  10   5  1

The rule is: boundary = 1, entry = up      + left-up
         or: C(n,0) = 1, C(n,k) = C(n-1,k) + C(n-1,k-1)

Multiple each row by successor of its index, i.e. row n -> (n + 1) (row n):
Multiples Triangle (or Modified Triangle):

1 * row 0   1
2 * row 1   2  2
3 * row 2   3  6  3
4 * row 3   4  12 12  4
5 * row 4   5  20 30 20  5
6 * row 5   6  30 60 60 30  6

The rule is: boundary = n, entry = left * left-up / (left - left-up)
         or: L(n,0) = n, L(n,k) = L(n,k-1) * L(n-1,k-1) / (L(n,k-1) - L(n-1,k-1))

Then   lcm(1, 2)
     = lcm(2)
     = lcm(2, 2)

       lcm(1, 2, 3)
     = lcm(lcm(1,2), 3)  using lcm(1,2,...,n,n+1) = lcm(lcm(1,2,...,n), n+1)
     = lcm(2, 3)         using lcm(1,2)
     = lcm(2*3/1, 3)     using lcm(L(n,k-1), L(n-1,k-1)) = lcm(L(n,k-1), L(n-1,k-1)/(L(n,k-1), L(n-1,k-1)), L(n-1,k-1))
     = lcm(6, 3)
     = lcm(3, 6, 3)

       lcm(1, 2, 3, 4)
     = lcm(lcm(1,2,3), 4)
     = lcm(lcm(6,3), 4)
     = lcm(6, 3, 4)
     = lcm(6, 3*4/1, 4)
     = lcm(6, 12, 4)
     = lcm(6*12/6, 12, 4)
     = lcm(12, 12, 4)
     = lcm(4, 12, 12, 4)

       lcm(1, 2, 3, 4, 5)
     = lcm(lcm(2,3,4), 5)
     = lcm(lcm(12,4), 5)
     = lcm(12, 4, 5)
     = lcm(12, 4*5/1, 5)
     = lcm(12, 20, 5)
     = lcm(12*20/8, 20, 5)
     = lcm(30, 20, 5)
     = lcm(5, 20, 30, 20, 5)

       lcm(1, 2, 3, 4, 5, 6)
     = lcm(lcm(1, 2, 3, 4, 5), 6)
     = lcm(lcm(30,20,5), 6)
     = lcm(30, 20, 5, 6)
     = lcm(30, 20, 5*6/1, 6)
     = lcm(30, 20, 30, 6)
     = lcm(30, 20*30/10, 30, 6)
     = lcm(20, 60, 30, 6)
     = lcm(20*60/40, 60, 30, 6)
     = lcm(30, 60, 30, 6)
     = lcm(6, 30, 60, 30, 6)

Invert each entry of Multiples Triangle into a unit fraction:
Leibniz's Triangle:

1/(1 * row 0)   1/1
1/(2 * row 1)   1/2  1/2
1/(3 * row 2)   1/3  1/6  1/3
1/(4 * row 3)   1/4  1/12 1/12 1/4
1/(5 * row 4)   1/5  1/20 1/30 1/20 1/5
1/(6 * row 5)   1/6  1/30 1/60 1/60 1/30 1/6

Theorem: In the Multiples Triangle, the vertical-lcm = horizontal-lcm.
i.e.    lcm (1, 2, 3) = lcm (3, 6, 3) = 6
        lcm (1, 2, 3, 4) = lcm (4, 12, 12, 4) = 12
        lcm (1, 2, 3, 4, 5) = lcm (5, 20, 30, 20, 5) = 60
        lcm (1, 2, 3, 4, 5, 6) = lcm (6, 30, 60, 60, 30, 6) = 60
Proof: With reference to Leibniz's Triangle, note: term = left-up - left
  lcm (5, 20, 30, 20, 5)
= lcm (5, 20, 30)                   by reduce repetition
= lcm (5, d(1/20), d(1/30))         by denominator of fraction
= lcm (5, d(1/4 - 1/5), d(1/30))    by term = left-up - left
= lcm (5, lcm(4, 5), d(1/12 - 1/20))     by denominator of fraction subtraction
= lcm (5, 4, lcm(12, 20))                by lcm (a, lcm (a, b)) = lcm (a, b)
= lcm (5, 4, lcm(d(1/12), d(1/20)))      to fraction again
= lcm (5, 4, lcm(d(1/3 - 1/4), d(1/4 - 1/5)))   by Leibniz's Triangle
= lcm (5, 4, lcm(lcm(3,4),     lcm(4,5)))       by fraction subtraction denominator
= lcm (5, 4, lcm(3, 4, 5))                      by lcm merge
= lcm (5, 4, 3)                                 merge again
= lcm (5, 4, 3, 2)                              by lcm include factor (!!!)
= lcm (5, 4, 3, 2, 1)                           by lcm include 1

Note: to make 30, need 12, 20
      to make 12, need 3, 4; to make 20, need 4, 5
  lcm (1, 2, 3, 4, 5)
= lcm (1, 2, lcm(3,4), lcm(4,5), 5)
= lcm (1, 2, d(1/3 - 1/4), d(1/4 - 1/5), 5)
= lcm (1, 2, d(1/12), d(1/20), 5)
= lcm (1, 2, 12, 20, 5)
= lcm (1, 2, lcm(12, 20), 20, 5)
= lcm (1, 2, d(1/12 - 1/20), 20, 5)
= lcm (1, 2, d(1/30), 20, 5)
= lcm (1, 2, 30, 20, 5)
= lcm (1, 30, 20, 5)             can drop factor !!
= lcm (30, 20, 5)                can drop 1
= lcm (5, 20, 30, 20, 5)

  lcm (1, 2, 3, 4, 5, 6)
= lcm (lcm (1, 2, 3, 4, 5), lcm(5,6), 6)
= lcm (lcm (5, 20, 30, 20, 5), d(1/5 - 1/6), 6)
= lcm (lcm (5, 20, 30, 20, 5), d(1/30), 6)
= lcm (lcm (5, 20, 30, 20, 5), 30, 6)
= lcm (lcm (5, 20, 30, 20, 5), 30, 6)
= lcm (5, 30, 20, 6)
= lcm (30, 20, 6)               can drop factor !!
= lcm (lcm(20, 30), 30, 6)
= lcm (d(1/20 - 1/30), 30, 6)
= lcm (d(1/60), 30, 6)
= lcm (60, 30, 6)
= lcm (6, 30, 60, 30, 6)

  lcm (1, 2)
= lcm (lcm(1,2), 2)
= lcm (2, 2)

  lcm (1, 2, 3)
= lcm (lcm(1, 2), 3)
= lcm (2, 3) --> lcm (2x3/(3-2), 3) = lcm (6, 3)
= lcm (lcm(2, 3), 3)   -->  lcm (6, 3) = lcm (3, 6, 3)
= lcm (d(1/2 - 1/3), 3)
= lcm (d(1/6), 3)
= lcm (6, 3) = lcm (3, 6, 3)

  lcm (1, 2, 3, 4)
= lcm (lcm(1, 2, 3), 4)
= lcm (lcm(6, 3), 4)
= lcm (6, 3, 4)
= lcm (6, lcm(3, 4), 4) --> lcm (6, 12, 4) = lcm (6x12/(12-6), 12, 4)
= lcm (6, d(1/3 - 1/4), 4)                 = lcm (12, 12, 4) = lcm (4, 12, 12, 4)
= lcm (6, d(1/12), 4)
= lcm (6, 12, 4)
= lcm (lcm(6, 12), 4)
= lcm (d(1/6 - 1/12), 4)
= lcm (d(1/12), 4)
= lcm (12, 4) = lcm (4, 12, 12, 4)

  lcm (1, 2, 3, 4, 5)
= lcm (lcm(1, 2, 3, 4), 5)
= lcm (lcm(12, 4), 5)
= lcm (12, 4, 5)
= lcm (12, lcm(4,5), 5) --> lcm (12, 20, 5) = lcm (12x20/(20-12), 20, 5)
= lcm (12, d(1/4 - 1/5), 5)                 = lcm (240/8, 20, 5) but lcm(12,20) != 30
= lcm (12, d(1/20), 5)                      = lcm (30, 20, 5)    use lcm(a,b,c) = lcm(ab/(b-a), b, c)
= lcm (12, 20, 5)
= lcm (lcm(12,20), 20, 5)
= lcm (d(1/12 - 1/20), 20, 5)
= lcm (d(1/30), 20, 5)
= lcm (30, 20, 5) = lcm (5, 20, 30, 20, 5)

  lcm (1, 2, 3, 4, 5, 6)
= lcm (lcm(1, 2, 3, 4, 5), 6)
= lcm (lcm(30, 20, 5), 6)
= lcm (30, 20, 5, 6)
= lcm (30, 20, lcm(5,6), 6) --> lcm (30, 20, 30, 6) = lcm (30, 20x30/(30-20), 30, 6)
= lcm (30, 20, d(1/5 - 1/6), 6)                     = lcm (30, 60, 30, 6)
= lcm (30, 20, d(1/30), 6)                          = lcm (30x60/(60-30), 60, 30, 6)
= lcm (30, 20, 30, 6)                               = lcm (60, 60, 30, 6)
= lcm (30, lcm(20,30), 30, 6)
= lcm (30, d(1/20 - 1/30), 30, 6)
= lcm (30, d(1/60), 30, 6)
= lcm (30, 60, 30, 6)
= lcm (lcm(30, 60), 60, 30, 6)
= lcm (d(1/30 - 1/60), 60, 30, 6)
= lcm (d(1/60), 60, 30, 6)
= lcm (60, 60, 30, 6)
= lcm (60, 30, 6) = lcm (6, 30, 60, 60, 30, 6)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: R^* x y /\ R^* y z ==> R^* x z *)
(* Proof: by RTC_TRANSITIVE, transitive_def *)
val RTC_TRANS = store_thm(
  "RTC_TRANS",
  ``R^* x y /\ R^* y z ==> R^* x z``,
  metis_tac[RTC_TRANSITIVE, transitive_def]);

(* ------------------------------------------------------------------------- *)
(* Leibniz Triangle (Denominator form)                                       *)
(* ------------------------------------------------------------------------- *)

(* Define Leibniz Triangle *)
val leibniz_def = Define`
  leibniz n k = (n + 1) * binomial n k
`;

(* export simple definition *)
val _ = export_rewrites["leibniz_def"];

(* Theorem: leibniz 0 n = if n = 0 then 1 else 0 *)
(* Proof:
     leibniz 0 n
   = (0 + 1) * binomial 0 n     by leibniz_def
   = if n = 0 then 1 else 0     by binomial_n_0
*)
val leibniz_0_n = store_thm(
  "leibniz_0_n",
  ``!n. leibniz 0 n = if n = 0 then 1 else 0``,
  rw[binomial_0_n]);

(* Theorem: leibniz n 0 = n + 1 *)
(* Proof:
     leibniz n 0
   = (n + 1) * binomial n 0     by leibniz_def
   = (n + 1) * 1                by binomial_n_0
   = n + 1
*)
val leibniz_n_0 = store_thm(
  "leibniz_n_0",
  ``!n. leibniz n 0 = n + 1``,
  rw[binomial_n_0]);

(* Theorem: leibniz n n = n + 1 *)
(* Proof:
     leibniz n n
   = (n + 1) * binomial n n     by leibniz_def
   = (n + 1) * 1                by binomial_n_n
   = n + 1
*)
val leibniz_n_n = store_thm(
  "leibniz_n_n",
  ``!n. leibniz n n = n + 1``,
  rw[binomial_n_n]);

(* Theorem: n < k ==> leibniz n k = 0 *)
(* Proof:
     leibniz n k
   = (n + 1) * binomial n k     by leibniz_def
   = (n + 1) * 0                by binomial_less_0
   = 0
*)
val leibniz_less_0 = store_thm(
  "leibniz_less_0",
  ``!n k. n < k ==> (leibniz n k = 0)``,
  rw[binomial_less_0]);

(* Theorem: k <= n ==> (leibniz n k = leibniz n (n-k)) *)
(* Proof:
     leibniz n k
   = (n + 1) * binomial n k       by leibniz_def
   = (n + 1) * binomial n (n-k)   by binomial_sym
   = leibniz n (n-k)              by leibniz_def
*)
val leibniz_sym = store_thm(
  "leibniz_sym",
  ``!n k. k <= n ==> (leibniz n k = leibniz n (n-k))``,
  rw[leibniz_def, GSYM binomial_sym]);

(* Theorem: k < HALF n ==> leibniz n k < leibniz n (k + 1) *)
(* Proof:
   Assume k < HALF n, and note that 0 < (n + 1).
                  leibniz n k < leibniz n (k + 1)
   <=> (n + 1) * binomial n k < (n + 1) * binomial n (k + 1)    by leibniz_def
   <=>           binomial n k < binomial n (k + 1)              by LT_MULT_LCANCEL
   <=>  T                                                       by binomial_monotone
*)
val leibniz_monotone = store_thm(
  "leibniz_monotone",
  ``!n k. k < HALF n ==> leibniz n k < leibniz n (k + 1)``,
  rw[leibniz_def, binomial_monotone]);

(* Theorem: k <= n ==> 0 < leibniz n k *)
(* Proof:
   Since leibniz n k = (n + 1) * binomial n k  by leibniz_def
     and 0 < n + 1, 0 < binomial n k           by binomial_pos
   Hence 0 < leibniz n k                       by ZERO_LESS_MULT
*)
val leibniz_pos = store_thm(
  "leibniz_pos",
  ``!n k. k <= n ==> 0 < leibniz n k``,
  rw[leibniz_def, binomial_pos, ZERO_LESS_MULT, DECIDE``!n. 0 < n + 1``]);

(* Theorem: (leibniz n k = 0) <=> n < k *)
(* Proof:
       leibniz n k = 0
   <=> (n + 1) * (binomial n k = 0)     by leibniz_def
   <=> binomial n k = 0                 by MULT_EQ_0, n + 1 <> 0
   <=> n < k                            by binomial_eq_0
*)
val leibniz_eq_0 = store_thm(
  "leibniz_eq_0",
  ``!n k. (leibniz n k = 0) <=> n < k``,
  rw[leibniz_def, binomial_eq_0]);

(* Theorem: leibniz n = (\j. (n + 1) * j) o (binomial n) *)
(* Proof: by leibniz_def and function equality. *)
val leibniz_alt = store_thm(
  "leibniz_alt",
  ``!n. leibniz n = (\j. (n + 1) * j) o (binomial n)``,
  rw[leibniz_def, FUN_EQ_THM]);

(* Theorem: leibniz n k = (\j. (n + 1) * j) (binomial n k) *)
(* Proof: by leibniz_def *)
val leibniz_def_alt = store_thm(
  "leibniz_def_alt",
  ``!n k. leibniz n k = (\j. (n + 1) * j) (binomial n k)``,
  rw_tac std_ss[leibniz_def]);

(*
Picture of Leibniz Triangle L-corner:
    b = L (n-1) k
    a = L n     k   c = L n (k+1)

a = L n k = (n+1) * (n, k, n-k) = (n+1, k, n-k) = (n+1)! / k! (n-k)!
b = L (n-1) k = n * (n-1, k, n-1-k) = (n , k, n-k-1) = n! / k! (n-k-1)! = a * (n-k)/(n+1)
c = L n (k+1) = (n+1) * (n, k+1, n-(k+1)) = (n+1, k+1, n-k-1) = (n+1)! / (k+1)! (n-k-1)! = a * (n-k)/(k+1)

a * b = a * a * (n-k)/(n+1)
a - b = a - a * (n-k)/(n+1) = a * (1 - (n-k)/(n+1)) = a * (n+1 - n+k)/(n+1) = a * (k+1)/(n+1)
Hence
  a * b /(a - b)
= [a * a * (n-k)/(n+1)] / [a * (k+1)/(n+1)]
= a * (n-k)/(k+1)
= c
or a * b = c * (a - b)
*)

(* Theorem: 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k *)
(* Proof:
     (n + 1) * leibniz (n - 1) k
   = (n + 1) * ((n-1 + 1) * binomial (n-1) k)     by leibniz_def
   = (n + 1) * (n * binomial (n-1) k)             by SUB_ADD, 1 <= n.
   = (n + 1) * ((n - k) * (binomial n k))         by binomial_up_eqn
   = ((n + 1) * (n - k)) * binomial n k           by MULT_ASSOC
   = ((n - k) * (n + 1)) * binomial n k           by MULT_COMM
   = (n - k) * ((n + 1) * binomial n k)           by MULT_ASSOC
   = (n - k) * leibniz n k                        by leibniz_def
*)
val leibniz_up_eqn = store_thm(
  "leibniz_up_eqn",
  ``!n. 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k``,
  rw[leibniz_def] >>
  `1 <= n` by decide_tac >>
  metis_tac[SUB_ADD, binomial_up_eqn, MULT_ASSOC, MULT_COMM]);

(* Theorem: 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1) *)
(* Proof:
   Since  (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k    by leibniz_up_eqn
          leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)  by DIV_SOLVE, 0 < n+1.
*)
val leibniz_up = store_thm(
  "leibniz_up",
  ``!n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)``,
  rw[leibniz_up_eqn, DIV_SOLVE]);

(* Theorem: 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k *)
(* Proof:
     leibniz (n - 1) k
   = (n - k) * leibniz n k DIV (n + 1)                  by leibniz_up, 0 < n
   = (n - k) * ((n + 1) * binomial n k) DIV (n + 1)     by leibniz_def
   = (n + 1) * ((n - k) * binomial n k) DIV (n + 1)     by MULT_ASSOC, MULT_COMM
   = (n - k) * binomial n k                             by MULT_DIV, 0 < n + 1
*)
val leibniz_up_alt = store_thm(
  "leibniz_up_alt",
  ``!n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k``,
  metis_tac[leibniz_up, leibniz_def, MULT_DIV, MULT_ASSOC, MULT_COMM, DECIDE``0 < x + 1``]);

(* Theorem: 0 < n ==> !k. (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k *)
(* Proof:
     (k + 1) * leibniz n (k+1)
   = (k + 1) * ((n + 1) * binomial n (k+1))   by leibniz_def
   = (k + 1) * (n + 1) * binomial n (k+1)     by MULT_ASSOC
   = (n + 1) * (k + 1) * binomial n (k+1)     by MULT_COMM
   = (n + 1) * ((k + 1) * binomial n (k+1))   by MULT_ASSOC
   = (n + 1) * ((n - k) * (binomial n k))     by binomial_right_eqn
   = ((n + 1) * (n - k)) * binomial n k       by MULT_ASSOC
   = ((n - k) * (n + 1)) * binomial n k       by MULT_COMM
   = (n - k) * ((n + 1) * binomial n k)       by MULT_ASSOC
   = (n - k) * leibniz n k                    by leibniz_def
*)
val leibniz_right_eqn = store_thm(
  "leibniz_right_eqn",
  ``!n. 0 < n ==> !k. (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k``,
  metis_tac[leibniz_def, MULT_COMM, MULT_ASSOC, binomial_right_eqn]);

(* Theorem: 0 < n ==> !k. leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k + 1) *)
(* Proof:
   Since  (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k    by leibniz_right_eqn
          leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k+1)  by DIV_SOLVE, 0 < k+1.
*)
val leibniz_right = store_thm(
  "leibniz_right",
  ``!n. 0 < n ==> !k. leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k+1)``,
  rw[leibniz_right_eqn, DIV_SOLVE]);

(* Note: Following is the property from Leibniz Harmonic Triangle:
   1 / leibniz n (k+1) = 1 / leibniz (n-1) k  - 1 / leibniz n k
                       = (leibniz n k - leibniz (n-1) k) / leibniz n k * leibniz (n-1) k
*)

(* The Idea:
                                                b
Actually, lcm a b = lcm b c = lcm c a     for   a c  in Leibniz Triangle.
The only relationship is: c = ab/(a - b), or ab = c(a - b).

Is this a theorem:  ab = c(a - b)  ==> lcm a b = lcm b c = lcm c a
Or in fractions,   1/c = 1/b - 1/a ==> lcm a b = lcm b c = lcm c a ?

lcm a b
= a b / (gcd a b)
= c(a - b) / (gcd a (a - b))
= ac(a - b) / gcd a (a-b) / a
= lcm (a (a-b)) c / a
= lcm (ca c(a-b)) / a
= lcm (ca ab) / a
= lcm (b c)

lcm a b = a b / gcd a b = a b / gcd a (a-b) = a b c / gcd ca c(a-b)
= c (a-b) c / gcd ca c(a-b) = lcm ca c(a-b) / a = lcm ca ab / a = lcm b c

  lcm b c
= b c / gcd b c
= a b c / gcd a*b a*c
= a b c / gcd c*(a-b) c*a
= a b / gcd (a-b) a
= a b / gcd b a
= lcm (a b)
= lcm a b

  lcm a c
= a c / gcd a c
= a b c / gcd b*a b*c
= a b c / gcd c*(a-b) b*c
= a b / gcd (a-b) b
= a b / gcd a b
= lcm a b

Yes!

This is now in LCM_EXCHANGE:
val it = |- !a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c): thm
*)

(* Theorem: 0 < n ==>
   !k. leibniz n k * leibniz (n-1) k = leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) *)
(* Proof:
   If n <= k,
      then  n-1 < k, and n < k+1.
      so    leibniz (n-1) k = 0         by leibniz_less_0, n-1 < k.
      and   leibniz n (k+1) = 0         by leibniz_less_0, n < k+1.
      Hence true                        by MULT_EQ_0
   Otherwise, k < n, or k <= n.
      then  (n+1) - (n-k) = k+1.

        (k + 1) * (c * (a - b))
      = (k + 1) * c * (a - b)                   by MULT_ASSOC
      = ((n+1) - (n-k)) * c * (a - b)           by above
      = (n - k) * a * (a - b)                   by leibniz_right_eqn
      = (n - k) * a * a - (n - k) * a * b       by LEFT_SUB_DISTRIB
      = (n + 1) * b * a - (n - k) * a * b       by leibniz_up_eqn
      = (n + 1) * (a * b) - (n - k) * (a * b)   by MULT_ASSOC, MULT_COMM
      = ((n+1) - (n-k)) * (a * b)               by RIGHT_SUB_DISTRIB
      = (k + 1) * (a * b)                       by above

      Since (k+1) <> 0, the result follows      by MULT_LEFT_CANCEL
*)
val leibniz_property = store_thm(
  "leibniz_property",
  ``!n. 0 < n ==>
   !k. leibniz n k * leibniz (n-1) k = leibniz n (k+1) * (leibniz n k - leibniz (n-1) k)``,
  rpt strip_tac >>
  Cases_on `n <= k` >-
  rw[leibniz_less_0] >>
  `(n+1) - (n-k) = k+1` by decide_tac >>
  `(k+1) <> 0` by decide_tac >>
  qabbrev_tac `a = leibniz n k` >>
  qabbrev_tac `b = leibniz (n - 1) k` >>
  qabbrev_tac `c = leibniz n (k + 1)` >>
  `(k + 1) * (c * (a - b)) = ((n+1) - (n-k)) * c * (a - b)` by rw_tac std_ss[MULT_ASSOC] >>
  `_ = (n - k) * a * (a - b)` by rw_tac std_ss[leibniz_right_eqn, Abbr`c`, Abbr`a`] >>
  `_ = (n - k) * a * a - (n - k) * a * b` by rw_tac std_ss[LEFT_SUB_DISTRIB] >>
  `_ = (n + 1) * b * a - (n - k) * a * b` by rw_tac std_ss[leibniz_up_eqn, Abbr`b`, Abbr`a`] >>
  `_ = (n + 1) * (a * b) - (n - k) * (a * b)` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `_ = ((n+1) - (n-k)) * (a * b)` by rw_tac std_ss[RIGHT_SUB_DISTRIB] >>
  `_ = (k + 1) * (a * b)` by rw_tac std_ss[] >>
  metis_tac[MULT_LEFT_CANCEL]);

(* Theorem: k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k))) *)
(* Proof:
   Note  (FACT k * FACT (n - k)) divides (FACT n)       by binomial_is_integer
    and  0 < FACT k * FACT (n - k)                      by FACT_LESS, ZERO_LESS_MULT
     leibniz n k
   = (n + 1) * binomial n k                             by leibniz_def
   = (n + 1) * (FACT n DIV (FACT k * FACT (n - k)))     by binomial_formula3
   = (n + 1) * FACT n DIV (FACT k * FACT (n - k))       by MULTIPLY_DIV
*)
val leibniz_formula = store_thm(
  "leibniz_formula",
  ``!n k. k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k)))``,
  metis_tac[leibniz_def, binomial_formula3, binomial_is_integer, FACT_LESS, MULTIPLY_DIV, ZERO_LESS_MULT]);

(* Theorem: 0 < n ==>
   !k. k < n ==> leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k) *)
(* Proof:
   By leibniz_property,
   leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) = leibniz n k * leibniz (n-1) k
   Since 0 < leibniz n k and 0 < leibniz (n-1) k     by leibniz_pos
      so 0 < (leibniz n k - leibniz (n-1) k)         by MULT_EQ_0
   Hence by MULT_COMM, DIV_SOLVE, 0 < (leibniz n k - leibniz (n-1) k),
   leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k)
*)
val leibniz_recurrence = store_thm(
  "leibniz_recurrence",
  ``!n. 0 < n ==>
   !k. k < n ==> (leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k))``,
  rpt strip_tac >>
  `k <= n /\ k <= (n-1)` by decide_tac >>
  `leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) = leibniz n k * leibniz (n-1) k` by rw[leibniz_property] >>
  `0 < leibniz n k /\ 0 < leibniz (n-1) k` by rw[leibniz_pos] >>
  `0 < (leibniz n k - leibniz (n-1) k)` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw_tac std_ss[DIV_SOLVE, MULT_COMM]);

(* Theorem: 0 < k /\ k <= n ==>
   (leibniz n k = leibniz n (k-1) * leibniz (n-1) (k-1) DIV (leibniz n (k-1) - leibniz (n-1) (k-1))) *)
(* Proof:
   Since 0 < k, k = SUC h     for some h
      or k = h + 1            by ADD1
     and h = k - 1            by arithmetic
   Since 0 < k and k <= n,
         0 < n and h < n.
   Hence true by leibniz_recurrence.
*)
val leibniz_n_k = store_thm(
  "leibniz_n_k",
  ``!n k. 0 < k /\ k <= n ==>
   (leibniz n k = leibniz n (k-1) * leibniz (n-1) (k-1) DIV (leibniz n (k-1) - leibniz (n-1) (k-1)))``,
  rpt strip_tac >>
  `?h. k = h + 1` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO, ADD1] >>
  `(h = k - 1) /\ h < n /\ 0 < n` by decide_tac >>
  metis_tac[leibniz_recurrence]);

(* Theorem: 0 < n ==>
   !k. lcm (leibniz n k) (leibniz (n-1) k) = lcm (leibniz n k) (leibniz n (k+1)) *)
(* Proof:
   By leibniz_property,
   leibniz n k * leibniz (n - 1) k = leibniz n (k + 1) * (leibniz n k - leibniz (n - 1) k)
   Hence true by LCM_EXCHANGE.
*)
val leibniz_lcm_exchange = store_thm(
  "leibniz_lcm_exchange",
  ``!n. 0 < n ==> !k. lcm (leibniz n k) (leibniz (n-1) k) = lcm (leibniz n k) (leibniz n (k+1))``,
  rw[leibniz_property, LCM_EXCHANGE]);

(* Theorem: 4 ** n <= leibniz (2 * n) n *)
(* Proof:
   Let m = 2 * n.
   Then n = HALF m                              by HALF_TWICE
   Let l1 = GENLIST (K (binomial m n)) (m + 1)
   and l2 = GENLIST (binomial m) (m + 1)
   Note LENGTH l1 = LENGTH l2 = m + 1           by LENGTH_GENLIST

   Claim: !k. k < m + 1 ==> EL k l2 <= EL k l1
   Proof: Note EL k l1 = binomial m n           by EL_GENLIST
           and EL k l2 = binomial m k           by EL_GENLIST
         Apply binomial m k <= binomial m n     by binomial_max
           The result follows

     leibniz m n
   = (m + 1) * binomial m n                     by leibniz_def
   = SUM (GENLIST (K (binomial m n)) (m + 1))   by SUM_GENLIST_K
   >= SUM (GENLIST (\k. binomial m k) (m + 1))  by SUM_LE, above
    = SUM (GENLIST (binomial m) (SUC m))        by ADD1
    = 2 ** m                                    by binomial_sum
    = 2 ** (2 * n)                              by notation
    = (2 ** 2) ** n                             by EXP_EXP_MULT
    = 4 ** n                                    by arithmetic
*)
val leibniz_middle_lower = store_thm(
  "leibniz_middle_lower",
  ``!n. 4 ** n <= leibniz (2 * n) n``,
  rpt strip_tac >>
  qabbrev_tac `m = 2 * n` >>
  `n = HALF m` by rw[HALF_TWICE, Abbr`m`] >>
  qabbrev_tac `l1 = GENLIST (K (binomial m n)) (m + 1)` >>
  qabbrev_tac `l2 = GENLIST (binomial m) (m + 1)` >>
  `!k. k < m + 1 ==> EL k l2 <= EL k l1` by rw[binomial_max, EL_GENLIST, Abbr`l1`, Abbr`l2`] >>
  `leibniz m n = (m + 1) * binomial m n` by rw[leibniz_def] >>
  `_ = SUM l1` by rw[SUM_GENLIST_K, Abbr`l1`] >>
  `SUM l2 = SUM (GENLIST (binomial m) (SUC m))` by rw[ADD1, Abbr`l2`] >>
  `_ = 2 ** m` by rw[binomial_sum] >>
  `_ = 4 ** n` by rw[EXP_EXP_MULT, Abbr`m`] >>
  metis_tac[SUM_LE, LENGTH_GENLIST]);

(* ------------------------------------------------------------------------- *)
(* Property of Leibniz Triangle                                              *)
(* ------------------------------------------------------------------------- *)

(*
binomial_recurrence |- !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
This means:
           B n k  + B n  k*
                       v
                    B n* k*
However, for the Leibniz Triangle, the recurrence is:
           L n k
           L n* k  -> L n* k* = (L n* k)(L n k) / (L n* k - L n k)
That is, it takes a different style, and has the property:
                    1 / L n* k* = 1 / L n k - 1 / L n* k
Why?
First, some verification.
Pascal:     [1]  3   3
                [4]  6 = 3 + 3 = 6
Leibniz:        12  12
               [20] 30 = 20 * 12 / (20 - 12) = 20 * 12 / 8 = 30
Now, the 20 comes from 4 = 3 + 1.
Originally,  30 = 5 * 6          by definition based on multiple
                = 5 * (3 + 3)    by Pascal
                = 4 * (3 + 3) + (3 + 3)
                = 12 + 12 + 6
In terms of factorials,  30 = 5 * 6 = 5 * B(4,2) = 5 * 4!/2!2!
                         20 = 5 * 4 = 5 * B(4,1) = 5 * 4!/1!3!
                         12 = 4 * 3 = 4 * B(3,1) = 4 * 3!/1!2!
So  1/30 = (2!2!)/(5 4!)     1 / n** B n* k* = k*! (n* - k* )! / n** n*! = (n - k)! k*! / n**!
    1/20 = (1!3!)/(5 4!)     1 / n** B n* k
    1/12 = (1!2!)/(4 3!)     1 / n* B n k
    1/12 - 1/20
  = (1!2!)/(4 3!) - (1!3!)/(5 4!)
  = (1!2!)/4! - (1!3!)/5!
  = 5(1!2!)/5! - (1!3!)/5!
  = (5(1!2!) - (1!3!))/5!
  = (5 1! - 3 1!) 2!/5!
  = (5 - 3)1! 2!/5!
  = 2! 2! / 5!

    1 / n B n k - 1 / n** B n* k
  = k! (n-k)! / n* n! - k! (n* - k)! / n** n*!
  = k! (n-k)! / n*! - k!(n* - k)! / n** n*!
  = (n** (n-k)! - (n* - k)!) k! / n** n*!
  = (n** - (n* - k)) (n - k)! k! / n** n*!
  = (k+1) (n - k)! k! / n** n*!
  = (n* - k* )! k*! / n** n*!
  = 1 / n** B n* k*

Direct without using unit fractions,

L n k = n* B n k = n* n! / k! (n-k)! = n*! / k! (n-k)!
L n* k = n** B n* k = n** n*! / k! (n* - k)! = n**! / k! (n* - k)!
L n* k* = n** B n* k* = n** n*! / k*! (n* - k* )! = n**! / k*! (n-k)!

(L n* k) * (L n k) = n**! n*! / k! (n* - k)! k! (n-k)!
(L n* k) - (L n k) = n**! / k! (n* - k)! - n*! / k! (n-k)!
                   = n**! / k! (n-k)!( 1/(n* - k) - 1/ n** )
                   = n**! / k! (n-k)! (n** - n* + k)/(n* - k)(n** )
                   = n**! / k! (n-k)! k* / (n* - k) n**
                   = n*! k* / k! (n* - k)!
(L n* k) * (L n k) / (L n* k) - (L n k)
= n**! /k! (n-k)! k*
= n**! /k*! (n-k)!
= L n* k*
So:    L n k
       L n* k --> L n* k*

Can the LCM be shown directly?
lcm (L n* k, L n k) = lcm (L n* k, L n* k* )
To prove this, need to show:
both have the same common multiples, and least is the same -- probably yes due to common L n* k.

In general, what is the condition for   lcm a b = lcm a c ?
Well,  lcm a b = a b / gcd a b,  lcm a c = a c / gcd a c
So it must be    a b gcd a c = a c gcd a b, or b * gcd a c = c * gcd a b.

It this true for Leibniz triangle?
Let a = 5, b = 4, c = 20.  b * gcd a c = 4 * gcd 5 20 = 4 * 5 = 20
                           c * gcd a b = 20 * gcd 5 4 = 20
Verify lcm a b = lcm 5 4 = 20 = 5 * 4 / gcd 5 4
       lcm a c = lcm 5 20 = 20 = 5 * 20 / gcd 5 20
       5 * 4 / gcd 5 4 = 5 * 20 / gcd 5 20
or        4 * gcd 5 20 = 20 * gcd 5 4

(L n k) * gcd (L n* k, L n* k* ) = (L n* k* ) * gcd (L n* k, L n k)

or n* B n k * gcd (n** B n* k, n** B n* k* ) = (n** B n* k* ) * gcd (n** B n* k, n* B n k)
By GCD_COMMON_FACTOR, !m n k. gcd (k * m) (k * n) = k * gcd m n
   n** n* B n k gcd (B n* k, B n* k* ) = (n** B n* k* ) * gcd (n** B n* k, n* B n k)
*)

(* Special Property of Leibniz Triangle
For:    L n k
        L n+ k --> L n+ k+

L n k  = n+! / k! (n-k)!
L n+ k = n++! / k! (n+ - k)! = n++ n+! / k! (n+ - k) k! = (n++ / n+ - k) L n k
L n+ k+ = n++! / k+! (n-k)! = (L n+ k) * (L n k) / (L n+ k - L n k) = (n++ / k+) L n k
Let g = gcd (L n+ k) (L n k), then L n+ k+ = lcm (L n+ k) (L n k) / (co n+ k - co n k)
where co n+ k = L n+ k / g, co n k = L n k / g.

    L n+ k = (n++ / n+ - k) L n k,
and L n+ k+ = (n++ / k+) L n k
e.g. L 3 1 = 12
     L 4 1 = 20, or (3++ / 3+ - 1) L 3 1 = (5/3) 12 = 20.
     L 4 2 = 30, or (3++ / 1+) L 3 1 = (5/2) 12 = 30.
so lcm (L 4 1) (L 3 1) = lcm (5/3)*12 12 = 12 * 5 = 60   since 3 must divide 12.
   lcm (L 4 1) (L 4 2) = lcm (5/3)*12 (5/2)*12 = 12 * 5 = 60  since 3, 2 must divide 12.

By LCM_COMMON_FACTOR |- !m n k. lcm (k * m) (k * n) = k * lcm m n
lcm a (a * b DIV c) = a * b

So the picture is:     (L n k)
                       (L n k) * (n+2)/(n-k+1)   (L n k) * (n+2)/(k+1)

A better picture:
Pascal:       (B n-1 k) = (n-1, k, n-k-1)
              (B n k)   = (n, k, n-k)     (B n k+1) = (n, k+1, n-k-1)
Leibniz:      (L n-1 k) = (n, k, n-k-1) = (L n k) / (n+1) * (n-k-1)
              (L n k)   = (n+1, k, n-k)   (L n k+1) = (n+1, k+1, n-k-1) = (L n k) / (n-k-1) * (k+1)
And we want:
    LCM (L, (n-k-1) * L DIV (n+1)) = LCM (L, (k+1) * L DIV (n-k-1)).

Theorem:   lcm a ((a * b) DIV c) = (a * b) DIV (gcd b c)
Assume this theorem,
LHS = L * (n-k-1) DIV gcd (n-k-1, n+1)
RHS = L * (k+1) DIV gcd (k+1, n-k-1)
Still no hope to show LHS = RHS !

LCM of fractions:
lcm (a/c, b/c) = lcm(a, b)/c
lcm (a/c, b/d) = ... = lcm(a, b)/gcd(c, d)
Hence lcm (a, a*b/c) = lcm(a*b/b, a*b/c) = a * b / gcd (b, c)
*)

(* Special Property of Leibniz Triangle -- another go
Leibniz:    L(5,1) = 30 = b
            L(6,1) = 42 = a   L(6,2) = 105 = c,  c = ab/(a - b), or ab = c(a - b)
Why is LCM 42 30 = LCM 42 105 = 210 = 2x3x5x7?
First, b = L(5,1) = 30 = (6,1,4) = 6!/1!4! = 7!/1!5! * (5/7) = a * (5/7) = 2x3x5
       a = L(6,1) = 42 = (7,1,5) = 7!/1!5! = 2x3x7 = b * (7/5) = c * (2/5)
       c = L(6,2) = 105 = (7,2,4) = 7!/2!4! = 7!/1!5! * (5/2) = a * (5/2) = 3x5x7
Any common multiple of a, b must have 5, 7 as factor, also with factor 2 (by common k = 1)
Any common multiple of a, c must have 5, 2 as factor, also with factor 7 (by common n = 6)
Also n = 5 implies a factor 6, k = 2 imples a factor 2.
LCM a b = a b / GCD a b
        = c (a - b) / GCD a b
        = (m c') (m a' - (m-1)b') / GCD (m a') (m-1 b')
LCM a c = a c / GCD a c
        = (m a') (m c') / GCD (m a') (m c')     where c' = a' + b' from Pascal triangle
        = m a' (a' + b') / GCD a' (a' + b')
        = m a' (a' + b') / GCD a' b'
        = a' c / GCD a' b'
Can we prove:    c(a - b) / GCD a b = c a' / GCD a' b'
or                 (a - b) GCD a' b' = a' GCD a b ?
or                a GCD a' b' = a' GCD a b + b GCD a' b' ?
or                    ab GCD a' b' = c a' GCD a b?
or                    m (b GCD a' b') = c GCD a b?
or                       b GCD a' b' = c' GCD a b?
b = (a DIV 7) * 5
c = (a DIV 2) * 5
lcm (a, b) = lcm (a, (a DIV 7) * 5) = lcm (a, 5)
lcm (a, c) = lcm (a, (a DIV 2) * 5) = lcm (a, 5)
Is this a theorem: lcm (a, (a DIV p) * b) = lcm (a, b) if p | a ?
Let c = lcm (a, b). Then a | c, b | c.
Since a = (a DIV p) * p, (a DIV p) * p | c.
Hence  ((a DIV p) * b) * p | b * c.
How to conclude ((a DIV p) * b) | c?

A counter-example:
lcm (42, 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 3) * 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 6) * 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 2) * 9) = 378 = 2x3x3x3x7.
lcm (42, (42 DIV 7) * 9) = 378 = 2x3x3x3x7.

LCM a c
= LCM a (ab/(a-b))    let g = GCD(a,b), a = gA, b=gB, coprime A,B.
= LCM gA gAB/(A-B)
= g LCM A AB/(A-B)
= (ab/LCM a b) LCM A AB/(A-B)
*)

(* ------------------------------------------------------------------------- *)
(* LCM of a list of numbers                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of a list of numbers *)
val list_lcm_def = Define`
  (list_lcm [] = 1) /\
  (list_lcm (h::t) = lcm h (list_lcm t))
`;

(* export simple definition *)
val _ = export_rewrites["list_lcm_def"];

(* Theorem: list_lcm [] = 1 *)
(* Proof: by list_lcm_def. *)
val list_lcm_nil = store_thm(
  "list_lcm_nil",
  ``list_lcm [] = 1``,
  rw[]);

(* Theorem: list_lcm (h::t) = lcm h (list_lcm t) *)
(* Proof: by list_lcm_def. *)
val list_lcm_cons = store_thm(
  "list_lcm_cons",
  ``!h t. list_lcm (h::t) = lcm h (list_lcm t)``,
  rw[]);

(* Theorem: list_lcm [x] = x *)
(* Proof:
     list_lcm [x]
   = lcm x (list_lcm [])    by list_lcm_cons
   = lcm x 1                by list_lcm_nil
   = x                      by LCM_1
*)
val list_lcm_sing = store_thm(
  "list_lcm_sing",
  ``!x. list_lcm [x] = x``,
  rw[]);

(* Theorem: list_lcm (SNOC x l) = list_lcm (x::l) *)
(* Proof:
   By induction on l.
   Base case: list_lcm (SNOC x []) = lcm x (list_lcm [])
     list_lcm (SNOC x [])
   = list_lcm [x]           by SNOC
   = lcm x (list_lcm [])    by list_lcm_def
   Step case: list_lcm (SNOC x l) = lcm x (list_lcm l) ==>
              !h. list_lcm (SNOC x (h::l)) = lcm x (list_lcm (h::l))
     list_lcm (SNOC x (h::l))
   = list_lcm (h::SNOC x l)        by SNOC
   = lcm h (list_lcm (SNOC x l))   by list_lcm_def
   = lcm h (lcm x (list_lcm l))    by induction hypothesis
   = lcm x (lcm h (list_lcm l))    by LCM_ASSOC_COMM
   = lcm x (list_lcm h::l)         by list_lcm_def
*)
val list_lcm_snoc = store_thm(
  "list_lcm_snoc",
  ``!x l. list_lcm (SNOC x l) = lcm x (list_lcm l)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[LCM_ASSOC_COMM]);

(* Theorem: list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l *)
(* Proof:
   By induction on l.
   Base case: !n. list_lcm (MAP (\k. n * k) []) = if [] = [] then 1 else n * list_lcm []
       list_lcm (MAP (\k. n * k) [])
     = list_lcm []                      by MAP
     = 1                                by list_lcm_nil
   Step case: !n. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l ==>
              !h n. list_lcm (MAP (\k. n * k) (h::l)) = if h::l = [] then 1 else n * list_lcm (h::l)
     Note h::l <> []                    by NOT_NIL_CONS
     If l = [], h::l = [h]
       list_lcm (MAP (\k. n * k) [h])
     = list_lcm [n * h]                 by MAP
     = n * h                            by list_lcm_sing
     = n * list_lcm [h]                 by list_lcm_sing
     If l <> [],
       list_lcm (MAP (\k. n * k) (h::l))
     = list_lcm ((n * h) :: MAP (\k. n * k) l)      by MAP
     = lcm (n * h) (list_lcm (MAP (\k. n * k) l))   by list_lcm_cons
     = lcm (n * h) (n * list_lcm l)                 by induction hypothesis
     = n * (lcm h (list_lcm l))                     by LCM_COMMON_FACTOR
     = n * list_lcm (h::l)                          by list_lcm_cons
*)
val list_lcm_map_times = store_thm(
  "list_lcm_map_times",
  ``!n l. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l``,
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw_tac std_ss[LCM_COMMON_FACTOR, MAP, list_lcm_cons]);

(* Theorem: EVERY_POSITIVE l ==> 0 < list_lcm l *)
(* Proof:
   By induction on l.
   Base case: EVERY_POSITIVE [] ==> 0 < list_lcm []
     Note  EVERY_POSITIVE [] = T      by EVERY_DEF
     Since list_lcm [] = 1            by list_lcm_nil
     Hence true since 0 < 1           by SUC_POS, ONE.
   Step case: EVERY_POSITIVE l ==> 0 < list_lcm l ==>
              !h. EVERY_POSITIVE (h::l) ==> 0 < list_lcm (h::l)
     Note EVERY_POSITIVE (h::l)
      ==> 0 < h and EVERY_POSITIVE l              by EVERY_DEF
     Since list_lcm (h::l) = lcm h (list_lcm l)   by list_lcm_cons
       and 0 < list_lcm l                         by induction hypothesis
        so h <= lcm h (list_lcm l)                by LCM_LE, 0 < h.
     Hence 0 < list_lcm (h::l)                    by LESS_LESS_EQ_TRANS
*)
val list_lcm_pos = store_thm(
  "list_lcm_pos",
  ``!l. EVERY_POSITIVE l ==> 0 < list_lcm l``,
  Induct >-
  rw[] >>
  metis_tac[EVERY_DEF, list_lcm_cons, LCM_LE, LESS_LESS_EQ_TRANS]);

(* Theorem: POSITIVE l ==> 0 < list_lcm l *)
(* Proof: by list_lcm_pos, EVERY_MEM *)
val list_lcm_pos_alt = store_thm(
  "list_lcm_pos_alt",
  ``!l. POSITIVE l ==> 0 < list_lcm l``,
  rw[list_lcm_pos, EVERY_MEM]);

(* Theorem: EVERY_POSITIVE l ==> SUM l <= (LENGTH l) * list_lcm l *)
(* Proof:
   By induction on l.
   Base case: EVERY_POSITIVE [] ==> SUM [] <= LENGTH [] * list_lcm []
     Note EVERY_POSITIVE [] = T      by EVERY_DEF
     Since SUM [] = 0                by SUM
       and LENGTH [] = 0             by LENGTH_NIL
     Hence true by MULT, as 0 <= 0   by LESS_EQ_REFL
   Step case: EVERY_POSITIVE l ==> SUM l <= LENGTH l * list_lcm l ==>
              !h. EVERY_POSITIVE (h::l) ==> SUM (h::l) <= LENGTH (h::l) * list_lcm (h::l)
     Note EVERY_POSITIVE (h::l)
      ==> 0 < h and EVERY_POSITIVE l          by EVERY_DEF
      ==> 0 < h and 0 < list_lcm l            by list_lcm_pos
     If l = [], LENGTH l = 0.
     SUM (h::[]) = SUM [h] = h                by SUM
       LENGTH (h::[]) * list_lcm (h::[])
     = 1 * list_lcm [h]                       by ONE
     = 1 * h                                  by list_lcm_sing
     = h                                      by MULT_LEFT_1
     If l <> [], LENGTH l <> 0                by LENGTH_NIL ... [1]
     SUM (h::l)
   = h + SUM l                                by SUM
   <= h + LENGTH l * list_lcm l               by induction hypothesis
   <= lcm h (list_lcm l) + LENGTH l * list_lcm l            by LCM_LE, 0 < h
   <= lcm h (list_lcm l) + LENGTH l * (lcm h (list_lcm l))  by LCM_LE, 0 < list_lcm l, [1]
   = (1 + LENGTH l) * (lcm h (list_lcm l))    by RIGHT_ADD_DISTRIB
   = SUC (LENGTH l) * (lcm h (list_lcm l))    by SUC_ONE_ADD
   = LENGTH (h::l) * (lcm h (list_lcm l))     by LENGTH
   = LENGTH (h::l) * list_lcm (h::l)          by list_lcm_cons
*)
val list_lcm_lower_bound = store_thm(
  "list_lcm_lower_bound",
  ``!l. EVERY_POSITIVE l ==> SUM l <= (LENGTH l) * list_lcm l``,
  Induct >>
  rw[] >>
  Cases_on `l = []` >-
  rw[] >>
  `lcm h (list_lcm l) + LENGTH l * (lcm h (list_lcm l)) = SUC (LENGTH l) * (lcm h (list_lcm l))` by rw[RIGHT_ADD_DISTRIB, SUC_ONE_ADD] >>
  `LENGTH l <> 0` by metis_tac[LENGTH_NIL] >>
  `0 < list_lcm l` by rw[list_lcm_pos] >>
  `h <= lcm h (list_lcm l) /\ list_lcm l <= lcm h (list_lcm l)` by rw[LCM_LE] >>
  `LENGTH l * list_lcm l <= LENGTH l * (lcm h (list_lcm l))` by rw[LE_MULT_LCANCEL] >>
  `h + SUM l <= h + LENGTH l * list_lcm l` by rw[] >>
  decide_tac);

(* Another version to eliminate EVERY by MEM. *)
val list_lcm_lower_bound_alt = save_thm("list_lcm_lower_bound_alt",
    list_lcm_lower_bound |> SIMP_RULE (srw_ss()) [EVERY_MEM]);
(* > list_lcm_lower_bound_alt;
val it = |- !l. POSITIVE l ==> SUM l <= LENGTH l * list_lcm l: thm
*)

(* Theorem: list_lcm l is a common multiple of its members.
            MEM x l ==> x divides (list_lcm l) *)
(* Proof:
   By induction on l.
   Base case: !x. MEM x [] ==> x divides (list_lcm [])
     True since MEM x [] = F     by MEM
   Step case: !x. MEM x l ==> x divides (list_lcm l) ==>
              !h x. MEM x (h::l) ==> x divides (list_lcm (h::l))
     Note MEM x (h::l) <=> x = h, or MEM x l       by MEM
      and list_lcm (h::l) = lcm h (list_lcm l)     by list_lcm_cons
     If x = h,
        divides h (lcm h (list_lcm l)) is true     by LCM_IS_LEAST_COMMON_MULTIPLE
     If MEM x l,
        x divides (list_lcm l)                     by induction hypothesis
        (list_lcm l) divides (lcm h (list_lcm l))  by LCM_IS_LEAST_COMMON_MULTIPLE
        Hence x divides (lcm h (list_lcm l))       by DIVIDES_TRANS
*)
val list_lcm_is_common_multiple = store_thm(
  "list_lcm_is_common_multiple",
  ``!x l. MEM x l ==> x divides (list_lcm l)``,
  Induct_on `l` >>
  rw[] >>
  metis_tac[LCM_IS_LEAST_COMMON_MULTIPLE, DIVIDES_TRANS]);

(* Theorem: If m is a common multiple of members of l, (list_lcm l) divides m.
           (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m *)
(* Proof:
   By induction on l.
   Base case: !m. (!x. MEM x [] ==> x divides m) ==> divides (list_lcm []) m
     Since list_lcm [] = 1       by list_lcm_nil
       and divides 1 m is true   by ONE_DIVIDES_ALL
   Step case: !m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m ==>
              !h m. (!x. MEM x (h::l) ==> x divides m) ==> divides (list_lcm (h::l)) m
     Note MEM x (h::l) <=> x = h, or MEM x l       by MEM
      and list_lcm (h::l) = lcm h (list_lcm l)     by list_lcm_cons
     Put x = h,   divides h m                      by MEM h (h::l) = T
     Put MEM x l, x divides m                      by MEM x (h::l) = T
         giving   (list_lcm l) divides m           by induction hypothesis
     Hence        divides (lcm h (list_lcm l)) m   by LCM_IS_LEAST_COMMON_MULTIPLE
*)
val list_lcm_is_least_common_multiple = store_thm(
  "list_lcm_is_least_common_multiple",
  ``!l m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m``,
  Induct >-
  rw[] >>
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(*
> EVAL ``list_lcm []``;
val it = |- list_lcm [] = 1: thm
> EVAL ``list_lcm [1; 2; 3]``;
val it = |- list_lcm [1; 2; 3] = 6: thm
> EVAL ``list_lcm [1; 2; 3; 4; 5]``;
val it = |- list_lcm [1; 2; 3; 4; 5] = 60: thm
> EVAL ``list_lcm (GENLIST SUC 5)``;
val it = |- list_lcm (GENLIST SUC 5) = 60: thm
> EVAL ``list_lcm (GENLIST SUC 4)``;
val it = |- list_lcm (GENLIST SUC 4) = 12: thm
> EVAL ``lcm 5 (list_lcm (GENLIST SUC 4))``;
val it = |- lcm 5 (list_lcm (GENLIST SUC 4)) = 60: thm
> EVAL ``SNOC 5 (GENLIST SUC 4)``;
val it = |- SNOC 5 (GENLIST SUC 4) = [1; 2; 3; 4; 5]: thm
> EVAL ``list_lcm (SNOC 5 (GENLIST SUC 4))``;
val it = |- list_lcm (SNOC 5 (GENLIST SUC 4)) = 60: thm
> EVAL ``GENLIST (\k. leibniz 5 k) (SUC 5)``;
val it = |- GENLIST (\k. leibniz 5 k) (SUC 5) = [6; 30; 60; 60; 30; 6]: thm
> EVAL ``list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))``;
val it = |- list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5)) = 60: thm
> EVAL ``list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))``;
val it = |- (list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))) <=> T: thm
> EVAL ``list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (leibniz 5) (SUC 5))``;
val it = |- (list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (leibniz 5) (SUC 5))) <=> T: thm
*)

(* Theorem: list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2) *)
(* Proof:
   By induction on l1.
   Base: !l2. list_lcm ([] ++ l2) = lcm (list_lcm []) (list_lcm l2)
      LHS = list_lcm ([] ++ l2)
          = list_lcm l2                      by APPEND
          = lcm 1 (list_lcm l2)              by LCM_1
          = lcm (list_lcm []) (list_lcm l2)  by list_lcm_nil
          = RHS
   Step:  !l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2) ==>
          !h l2. list_lcm (h::l1 ++ l2) = lcm (list_lcm (h::l1)) (list_lcm l2)
        list_lcm (h::l1 ++ l2)
      = list_lcm (h::(l1 ++ l2))                   by APPEND
      = lcm h (list_lcm (l1 ++ l2))                by list_lcm_cons
      = lcm h (lcm (list_lcm l1) (list_lcm l2))    by induction hypothesis
      = lcm (lcm h (list_lcm l1)) (list_lcm l2)    by LCM_ASSOC
      = lcm (list_lcm (h::l1)) (list_lcm l2)       by list_lcm_cons
*)
val list_lcm_append = store_thm(
  "list_lcm_append",
  ``!l1 l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2)``,
  Induct >-
  rw[] >>
  rw[LCM_ASSOC]);

(* Theorem: list_lcm (l1 ++ l2 ++ l3) = list_lcm [(list_lcm l1); (list_lcm l2); (list_lcm l3)] *)
(* Proof:
     list_lcm (l1 ++ l2 ++ l3)
   = lcm (list_lcm (l1 ++ l2)) (list_lcm l3)                    by list_lcm_append
   = lcm (lcm (list_lcm l1) (list_lcm l2)) (list_lcm l3)        by list_lcm_append
   = lcm (list_lcm l1) (lcm (list_lcm l2) (list_lcm l3))        by LCM_ASSOC
   = lcm (list_lcm l1) (list_lcm [(list_lcm l2); list_lcm l3])  by list_lcm_cons
   = list_lcm [list_lcm l1; list_lcm l2; list_lcm l3]           by list_lcm_cons
*)
val list_lcm_append_3 = store_thm(
  "list_lcm_append_3",
  ``!l1 l2 l3. list_lcm (l1 ++ l2 ++ l3) = list_lcm [(list_lcm l1); (list_lcm l2); (list_lcm l3)]``,
  rw[list_lcm_append, LCM_ASSOC, list_lcm_cons]);

(* Theorem: list_lcm (REVERSE l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: list_lcm (REVERSE []) = list_lcm []
       True since REVERSE [] = []          by REVERSE_DEF
   Step: list_lcm (REVERSE l) = list_lcm l ==>
         !h. list_lcm (REVERSE (h::l)) = list_lcm (h::l)
        list_lcm (REVERSE (h::l))
      = list_lcm (REVERSE l ++ [h])        by REVERSE_DEF
      = lcm (list_lcm (REVERSE l)) (list_lcm [h])   by list_lcm_append
      = lcm (list_lcm l) (list_lcm [h])             by induction hypothesis
      = lcm (list_lcm [h]) (list_lcm l)             by LCM_COMM
      = list_lcm ([h] ++ l)                         by list_lcm_append
      = list_lcm (h::l)                             by CONS_APPEND
*)
val list_lcm_reverse = store_thm(
  "list_lcm_reverse",
  ``!l. list_lcm (REVERSE l) = list_lcm l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `list_lcm (REVERSE (h::l)) = list_lcm (REVERSE l ++ [h])` by rw[] >>
  `_ = lcm (list_lcm (REVERSE l)) (list_lcm [h])` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm l) (list_lcm [h])` by rw[] >>
  `_ = lcm (list_lcm [h]) (list_lcm l)` by rw[LCM_COMM] >>
  `_ = list_lcm ([h] ++ l)` by rw[list_lcm_append] >>
  `_ = list_lcm (h::l)` by rw[] >>
  decide_tac);

(* Theorem: list_lcm [1 .. (n + 1)] = lcm (n + 1) (list_lcm [1 .. n])) *)
(* Proof:
     list_lcm [1 .. (n + 1)]
   = list_lcm (SONC (n + 1) [1 .. n])   by listRangeINC_SNOC, 1 <= n + 1
   = lcm (n + 1) (list_lcm [1 .. n])    by list_lcm_snoc
*)
val list_lcm_suc = store_thm(
  "list_lcm_suc",
  ``!n. list_lcm [1 .. (n + 1)] = lcm (n + 1) (list_lcm [1 .. n])``,
  rw[listRangeINC_SNOC, list_lcm_snoc]);

(* Theorem: l <> [] /\ EVERY_POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l *)
(* Proof:
   Note LENGTH l <> 0                           by LENGTH_NIL
    and SUM l <= LENGTH l * list_lcm l          by list_lcm_lower_bound
     so (SUM l) DIV (LENGTH l) <= list_lcm l    by DIV_LE
*)
val list_lcm_nonempty_lower = store_thm(
  "list_lcm_nonempty_lower",
  ``!l. l <> [] /\ EVERY_POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l``,
  metis_tac[list_lcm_lower_bound, DIV_LE, LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* Theorem: l <> [] /\ POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l *)
(* Proof:
   Note LENGTH l <> 0                           by LENGTH_NIL
    and SUM l <= LENGTH l * list_lcm l          by list_lcm_lower_bound_alt
     so (SUM l) DIV (LENGTH l) <= list_lcm l    by DIV_LE
*)
val list_lcm_nonempty_lower_alt = store_thm(
  "list_lcm_nonempty_lower_alt",
  ``!l. l <> [] /\ POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l``,
  metis_tac[list_lcm_lower_bound_alt, DIV_LE, LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* Theorem: MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l *)
(* Proof:
   Note x divides (list_lcm l)          by list_lcm_is_common_multiple
    and y divides (list_lcm l)          by list_lcm_is_common_multiple
    ==> (lcm x y) divides (list_lcm l)  by LCM_IS_LEAST_COMMON_MULTIPLE
*)
val list_lcm_divisor_lcm_pair = store_thm(
  "list_lcm_divisor_lcm_pair",
  ``!l x y. MEM x l /\ MEM y l ==> (lcm x y) divides list_lcm l``,
  rw[list_lcm_is_common_multiple, LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: POSITIVE l /\ MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l *)
(* Proof:
   Note (lcm x y) divides (list_lcm l)  by list_lcm_divisor_lcm_pair
    Now 0 < list_lcm l                  by list_lcm_pos_alt
   Thus (lcm x y) <= list_lcm l         by DIVIDES_LE
*)
val list_lcm_lower_by_lcm_pair = store_thm(
  "list_lcm_lower_by_lcm_pair",
  ``!l x y. POSITIVE l /\ MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l``,
  rw[list_lcm_divisor_lcm_pair, list_lcm_pos_alt, DIVIDES_LE]);

(* Theorem: 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m *)
(* Proof:
   Note list_lcm l divides m     by list_lcm_is_least_common_multiple
   Thus list_lcm l <= m          by DIVIDES_LE, 0 < m
*)
val list_lcm_upper_by_common_multiple = store_thm(
  "list_lcm_upper_by_common_multiple",
  ``!l m. 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m``,
  rw[list_lcm_is_least_common_multiple, DIVIDES_LE]);

(* Theorem: list_lcm ls = FOLDR lcm 1 ls *)
(* Proof:
   By induction on ls.
   Base: list_lcm [] = FOLDR lcm 1 []
         list_lcm []
       = 1                        by list_lcm_nil
       = FOLDR lcm 1 []           by FOLDR
   Step: list_lcm ls = FOLDR lcm 1 ls ==>
         !h. list_lcm (h::ls) = FOLDR lcm 1 (h::ls)
         list_lcm (h::ls)
       = lcm h (list_lcm ls)      by list_lcm_def
       = lcm h (FOLDR lcm 1 ls)   by induction hypothesis
       = FOLDR lcm 1 (h::ls)      by FOLDR
*)
val list_lcm_by_FOLDR = store_thm(
  "list_lcm_by_FOLDR",
  ``!ls. list_lcm ls = FOLDR lcm 1 ls``,
  Induct >> rw[]);

(* Theorem: list_lcm ls = FOLDL lcm 1 ls *)
(* Proof:
   Note COMM lcm  since !x y. lcm x y = lcm y x                    by LCM_COMM
    and ASSOC lcm since !x y z. lcm x (lcm y z) = lcm (lcm x y) z  by LCM_ASSOC
    Now list_lcm ls
      = FOLDR lcm 1 ls          by list_lcm_by FOLDR
      = FOLDL lcm 1 ls          by FOLDL_EQ_FOLDR, COMM lcm, ASSOC lcm
*)
val list_lcm_by_FOLDL = store_thm(
  "list_lcm_by_FOLDL",
  ``!ls. list_lcm ls = FOLDL lcm 1 ls``,
  simp[list_lcm_by_FOLDR] >>
  irule (GSYM FOLDL_EQ_FOLDR) >>
  rpt strip_tac >-
  rw[LCM_ASSOC, combinTheory.ASSOC_DEF] >>
  rw[LCM_COMM, combinTheory.COMM_DEF]);

(* ------------------------------------------------------------------------- *)
(* Lists in Leibniz Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Veritcal Lists in Leibniz Triangle                                        *)
(* ------------------------------------------------------------------------- *)

(* Define Vertical List in Leibniz Triangle *)
(*
val leibniz_vertical_def = Define `
  leibniz_vertical n = GENLIST SUC (SUC n)
`;

(* Use overloading for leibniz_vertical n. *)
val _ = overload_on("leibniz_vertical", ``\n. GENLIST ((+) 1) (n + 1)``);
*)

(* Define Vertical (downward list) in Leibniz Triangle *)

(* Use overloading for leibniz_vertical n. *)
val _ = overload_on("leibniz_vertical", ``\n. [1 .. (n+1)]``);

(* Theorem: leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1) *)
(* Proof:
     leibniz_vertical n
   = [1 .. (n+1)]                        by notation
   = GENLIST (\i. 1 + i) (n+1 + 1 - 1)   by listRangeINC_def
   = GENLIST (\i. 1 + i) (n + 1)         by arithmetic
*)
val leibniz_vertical_alt = store_thm(
  "leibniz_vertical_alt",
  ``!n. leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1)``,
  rw[listRangeINC_def]);

(* Theorem: leibniz_vertical 0 = [1] *)
(* Proof:
     leibniz_vertical 0
   = [1 .. (0+1)]         by notation
   = [1 .. 1]             by arithmetic
   = [1]                  by listRangeINC_SING
*)
val leibniz_vertical_0 = store_thm(
  "leibniz_vertical_0",
  ``leibniz_vertical 0 = [1]``,
  rw[]);

(* Theorem: LENGTH (leibniz_vertical n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_vertical n)
   = LENGTH [1 .. (n+1)]             by notation
   = n + 1 + 1 - 1                   by listRangeINC_LEN
   = n + 1                           by arithmetic
*)
val leibniz_vertical_len = store_thm(
  "leibniz_vertical_len",
  ``!n. LENGTH (leibniz_vertical n) = n + 1``,
  rw[listRangeINC_LEN]);

(* Theorem: leibniz_vertical n <> [] *)
(* Proof:
      LENGTH (leibniz_vertical n)
    = n + 1                         by leibniz_vertical_len
    <> 0                            by ADD1, SUC_NOT_ZERO
    Thus leibniz_vertical n <> []   by LENGTH_EQ_0
*)
val leibniz_vertical_not_nil = store_thm(
  "leibniz_vertical_not_nil",
  ``!n. leibniz_vertical n <> []``,
  metis_tac[leibniz_vertical_len, LENGTH_EQ_0, DECIDE``!n. n + 1 <> 0``]);

(* Theorem: EVERY_POSITIVE (leibniz_vertical n) *)
(* Proof:
       EVERY_POSITIVE (leibniz_vertical n)
   <=> EVERY_POSITIVE GENLIST (\i. 1 + i) (n+1)   by leibniz_vertical_alt
   <=> !i. i < n + 1 ==> 0 < 1 + i                by EVERY_GENLIST
   <=> !i. i < n + 1 ==> T                        by arithmetic
   <=> T
*)
val leibniz_vertical_pos = store_thm(
  "leibniz_vertical_pos",
  ``!n. EVERY_POSITIVE (leibniz_vertical n)``,
  rw[leibniz_vertical_alt, EVERY_GENLIST]);

(* Theorem: POSITIVE (leibniz_vertical n) *)
(* Proof: by leibniz_vertical_pos, EVERY_MEM *)
val leibniz_vertical_pos_alt = store_thm(
  "leibniz_vertical_pos_alt",
  ``!n. POSITIVE (leibniz_vertical n)``,
  rw[leibniz_vertical_pos, EVERY_MEM]);

(* Theorem: 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_vertical n) *)
(* Proof:
   Note: (leibniz_vertical n) has 1 to (n+1), inclusive:
       MEM x (leibniz_vertical n)
   <=> MEM x [1 .. (n+1)]              by notation
   <=> 1 <= x /\ x <= n + 1            by listRangeINC_MEM
   <=> 0 < x /\ x <= n + 1             by num_CASES, LESS_EQ_MONO
*)
val leibniz_vertical_mem = store_thm(
  "leibniz_vertical_mem",
  ``!n x. 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_vertical n)``,
  rw[]);

(* Theorem: leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n) *)
(* Proof:
     leibniz_vertical (n + 1)
   = [1 .. (n+1 +1)]                     by notation
   = SNOC (n+1 + 1) [1 .. (n+1)]         by listRangeINC_SNOC
   = SNOC (n + 2) (leibniz_vertical n)   by notation
*)
val leibniz_vertical_snoc = store_thm(
  "leibniz_vertical_snoc",
  ``!n. leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n)``,
  rw[listRangeINC_SNOC]);;

(* Use overloading for leibniz_up n. *)
val _ = overload_on("leibniz_up", ``\n. REVERSE (leibniz_vertical n)``);

(* Theorem: leibniz_up 0 = [1] *)
(* Proof:
     leibniz_up 0
   = REVERSE (leibniz_vertical 0)  by notation
   = REVERSE [1]                   by leibniz_vertical_0
   = [1]                           by REVERSE_SING
*)
val leibniz_up_0 = store_thm(
  "leibniz_up_0",
  ``leibniz_up 0 = [1]``,
  rw[]);

(* Theorem: LENGTH (leibniz_up n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_up n)
   = LENGTH (REVERSE (leibniz_vertical n))   by notation
   = LENGTH (leibniz_vertical n)             by LENGTH_REVERSE
   = n + 1                                   by leibniz_vertical_len
*)
val leibniz_up_len = store_thm(
  "leibniz_up_len",
  ``!n. LENGTH (leibniz_up n) = n + 1``,
  rw[leibniz_vertical_len]);

(* Theorem: EVERY_POSITIVE (leibniz_up n) *)
(* Proof:
       EVERY_POSITIVE (leibniz_up n)
   <=> EVERY_POSITIVE (REVERSE (leibniz_vertical n))   by notation
   <=> EVERY_POSITIVE (leibniz_vertical n)             by EVERY_REVERSE
   <=> T                                               by leibniz_vertical_pos
*)
val leibniz_up_pos = store_thm(
  "leibniz_up_pos",
  ``!n. EVERY_POSITIVE (leibniz_up n)``,
  rw[leibniz_vertical_pos, EVERY_REVERSE]);

(* Theorem: 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_up n) *)
(* Proof:
   Note: (leibniz_up n) has (n+1) downto 1, inclusive:
       MEM x (leibniz_up n)
   <=> MEM x (REVERSE (leibniz_vertical n))     by notation
   <=> MEM x (leibniz_vertical n)               by MEM_REVERSE
   <=> T                                        by leibniz_vertical_mem
*)
val leibniz_up_mem = store_thm(
  "leibniz_up_mem",
  ``!n x. 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_up n)``,
  rw[]);

(* Theorem: leibniz_up (n + 1) = (n + 2) :: (leibniz_up n) *)
(* Proof:
     leibniz_up (n + 1)
   = REVERSE (leibniz_vertical (n + 1))            by notation
   = REVERSE (SNOC (n + 2) (leibniz_vertical n))   by leibniz_vertical_snoc
   = (n + 2) :: (leibniz_up n)                     by REVERSE_SNOC
*)
val leibniz_up_cons = store_thm(
  "leibniz_up_cons",
  ``!n. leibniz_up (n + 1) = (n + 2) :: (leibniz_up n)``,
  rw[leibniz_vertical_snoc, REVERSE_SNOC]);

(* ------------------------------------------------------------------------- *)
(* Horizontal List in Leibniz Triangle                                       *)
(* ------------------------------------------------------------------------- *)

(* Define row (horizontal list) in Leibniz Triangle *)
(*
val leibniz_horizontal_def = Define `
  leibniz_horizontal n = GENLIST (leibniz n) (SUC n)
`;

(* Use overloading for leibniz_horizontal n. *)
val _ = overload_on("leibniz_horizontal", ``\n. GENLIST (leibniz n) (n + 1)``);
*)

(* Use overloading for leibniz_horizontal n. *)
val _ = overload_on("leibniz_horizontal", ``\n. GENLIST (leibniz n) (n + 1)``);

(*
> EVAL ``leibniz_horizontal 0``;
val it = |- leibniz_horizontal 0 = [1]: thm
> EVAL ``leibniz_horizontal 1``;
val it = |- leibniz_horizontal 1 = [2; 2]: thm
> EVAL ``leibniz_horizontal 2``;
val it = |- leibniz_horizontal 2 = [3; 6; 3]: thm
> EVAL ``leibniz_horizontal 3``;
val it = |- leibniz_horizontal 3 = [4; 12; 12; 4]: thm
> EVAL ``leibniz_horizontal 4``;
val it = |- leibniz_horizontal 4 = [5; 20; 30; 20; 5]: thm
> EVAL ``leibniz_horizontal 5``;
val it = |- leibniz_horizontal 5 = [6; 30; 60; 60; 30; 6]: thm
> EVAL ``leibniz_horizontal 6``;
val it = |- leibniz_horizontal 6 = [7; 42; 105; 140; 105; 42; 7]: thm
> EVAL ``leibniz_horizontal 7``;
val it = |- leibniz_horizontal 7 = [8; 56; 168; 280; 280; 168; 56; 8]: thm
> EVAL ``leibniz_horizontal 8``;
val it = |- leibniz_horizontal 8 = [9; 72; 252; 504; 630; 504; 252; 72; 9]: thm
*)

(* Theorem: leibniz_horizontal 0 = [1] *)
(* Proof:
     leibniz_horizontal 0
   = GENLIST (leibniz 0) (0 + 1)    by notation
   = GENLIST (leibniz 0) 1          by arithmetic
   = [leibniz 0 0]                  by GENLIST
   = [1]                            by leibniz_n_0
*)
val leibniz_horizontal_0 = store_thm(
  "leibniz_horizontal_0",
  ``leibniz_horizontal 0 = [1]``,
  rw_tac std_ss[GENLIST_1, leibniz_n_0]);

(* Theorem: LENGTH (leibniz_horizontal n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_horizontal n)
   = LENGTH (GENLIST (leibniz n) (n + 1))   by notation
   = n + 1                                  by LENGTH_GENLIST
*)
val leibniz_horizontal_len = store_thm(
  "leibniz_horizontal_len",
  ``!n. LENGTH (leibniz_horizontal n) = n + 1``,
  rw[]);

(* Theorem: k <= n ==> EL k (leibniz_horizontal n) = leibniz n k *)
(* Proof:
   Note k <= n means k < SUC n.
     EL k (leibniz_horizontal n)
   = EL k (GENLIST (leibniz n) (n + 1))   by notation
   = EL k (GENLIST (leibniz n) (SUC n))   by ADD1
   = leibniz n k                          by EL_GENLIST, k < SUC n.
*)
val leibniz_horizontal_el = store_thm(
  "leibniz_horizontal_el",
  ``!n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)``,
  rw[LESS_EQ_IMP_LESS_SUC]);

(* Theorem: k <= n ==> MEM (leibniz n k) (leibniz_horizontal n) *)
(* Proof:
   Note k <= n ==> k < (n + 1)
   Thus MEM (leibniz n k) (GENLIST (leibniz n) (n + 1))        by MEM_GENLIST
     or MEM (leibniz n k) (leibniz_horizontal n)               by notation
*)
val leibniz_horizontal_mem = store_thm(
  "leibniz_horizontal_mem",
  ``!n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)``,
  metis_tac[MEM_GENLIST, DECIDE``k <= n ==> k < n + 1``]);

(* Theorem: MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n *)
(* Proof:
   If part: (leibniz n k) (leibniz_horizontal n) ==> k <= n
      By contradiction, suppose n < k.
      Then leibniz n k = 0        by binomial_less_0, ~(k <= n)
       But ?m. m < n + 1 ==> 0 = leibniz n m    by MEM_GENLIST
        or m <= n ==> leibniz n m = 0           by m < n + 1
       Yet leibniz n m <> 0                     by leibniz_eq_0
      This is a contradiction.
   Only-if part: k <= n ==> (leibniz n k) (leibniz_horizontal n)
      By MEM_GENLIST, this is to show:
           ?m. m < n + 1 /\ (leibniz n k = leibniz n m)
      Note k <= n ==> k < n + 1,
      Take m = k, the result follows.
*)
val leibniz_horizontal_mem_iff = store_thm(
  "leibniz_horizontal_mem_iff",
  ``!n k. MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n``,
  rw_tac bool_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `leibniz n k = 0` by rw[leibniz_less_0] >>
    fs[MEM_GENLIST] >>
    `m <= n` by decide_tac >>
    fs[binomial_eq_0],
    rw[MEM_GENLIST] >>
    `k < n + 1` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n + 1 /\ (x = (n + 1) * binomial n m)) <=> ?k. k <= n /\ (x = (n + 1) * binomial n k)
   Since m < n + 1 <=> m <= n              by LE_LT1
   This is trivially true.
*)
val leibniz_horizontal_member = store_thm(
  "leibniz_horizontal_member",
  ``!n x. MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k)``,
  metis_tac[MEM_GENLIST, LE_LT1]);

(* Theorem: k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k) *)
(* Proof: by EL_GENLIST *)
val leibniz_horizontal_element = store_thm(
  "leibniz_horizontal_element",
  ``!n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)``,
  rw[EL_GENLIST]);

(* Theorem: TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2] *)
(* Proof:
     TAKE 1 (leibniz_horizontal (n + 1))
   = TAKE 1 (GENLIST (leibniz (n + 1)) (n + 1 + 1))                      by notation
   = TAKE 1 (GENLIST (leibniz (SUC n)) (SUC (SUC n)))                    by ADD1
   = TAKE 1 ((leibniz (SUC n) 0) :: GENLIST ((leibniz (SUC n)) o SUC) n) by GENLIST_CONS
   = (leibniz (SUC n) 0):: TAKE 0 (GENLIST ((leibniz (SUC n)) o SUC) n)  by TAKE_def
   = [leibniz (SUC n) 0]:: []                                            by TAKE_0
   = [SUC n + 1]                                                         by leibniz_n_0
   = [n + 2]                                                             by ADD1
*)
val leibniz_horizontal_head = store_thm(
  "leibniz_horizontal_head",
  ``!n. TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2]``,
  rpt strip_tac >>
  `(!n. n + 1 = SUC n) /\ (!n. n + 2 = SUC (SUC n))` by decide_tac >>
  rw[GENLIST_CONS, leibniz_n_0]);

(* Theorem: k <= n ==> (leibniz n k) divides list_lcm (leibniz_horizontal n) *)
(* Proof:
   Note MEM (leibniz n k) (leibniz_horizontal n)                by leibniz_horizontal_mem
     so (leibniz n k) divides list_lcm (leibniz_horizontal n)   by list_lcm_is_common_multiple
*)
val leibniz_horizontal_divisor = store_thm(
  "leibniz_horizontal_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides list_lcm (leibniz_horizontal n)``,
  rw[leibniz_horizontal_mem, list_lcm_is_common_multiple]);

(* Theorem: EVERY_POSITIVE (leibniz_horizontal n) *)
(* Proof:
   Let l = leibniz_horizontal n
   Then LENGTH l = n + 1                     by leibniz_horizontal_len
       EVERY_POSITIVE l
   <=> !k. k < LENGTH l ==> 0 < (EL k l)     by EVERY_EL
   <=> !k. k < n + 1 ==> 0 < (EL k l)        by above
   <=> !k. k <= n ==> 0 < EL k l             by arithmetic
   <=> !k. k <= n ==> 0 < leibniz n k        by leibniz_horizontal_el
   <=> T                                     by leibniz_pos
*)
Theorem leibniz_horizontal_pos:
  !n. EVERY_POSITIVE (leibniz_horizontal n)
Proof
  simp[EVERY_EL, binomial_pos]
QED

(* Theorem: POSITIVE (leibniz_horizontal n) *)
(* Proof: by leibniz_horizontal_pos, EVERY_MEM *)
val leibniz_horizontal_pos_alt = store_thm(
  "leibniz_horizontal_pos_alt",
  ``!n. POSITIVE (leibniz_horizontal n)``,
  metis_tac[leibniz_horizontal_pos, EVERY_MEM]);

(* Theorem: leibniz_horizontal n = MAP (\j. (n+1) * j) (binomial_horizontal n) *)
(* Proof:
     leibniz_horizontal n
   = GENLIST (leibniz n) (n + 1)                          by notation
   = GENLIST ((\j. (n + 1) * j) o (binomial n)) (n + 1)   by leibniz_alt
   = MAP (\j. (n + 1) * j) (GENLIST (binomial n) (n + 1)) by MAP_GENLIST
   = MAP (\j. (n + 1) * j) (binomial_horizontal n)        by notation
*)
val leibniz_horizontal_alt = store_thm(
  "leibniz_horizontal_alt",
  ``!n. leibniz_horizontal n = MAP (\j. (n+1) * j) (binomial_horizontal n)``,
  rw_tac std_ss[leibniz_alt, MAP_GENLIST]);

(* Theorem: list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n) *)
(* Proof:
   Since LENGTH (binomial_horizontal n) = n + 1             by binomial_horizontal_len
         binomial_horizontal n <> []                        by LENGTH_NIL ... [1]
     list_lcm (leibniz_horizontal n)
   = list_lcm (MAP (\j (n+1) * j) (binomial_horizontal n))  by leibniz_horizontal_alt
   = (n + 1) * list_lcm (binomial_horizontal n)             by list_lcm_map_times, [1]
*)
val leibniz_horizontal_lcm_alt = store_thm(
  "leibniz_horizontal_lcm_alt",
  ``!n. list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)``,
  rpt strip_tac >>
  `LENGTH (binomial_horizontal n) = n + 1` by rw[binomial_horizontal_len] >>
  `n + 1 <> 0` by decide_tac >>
  `binomial_horizontal n <> []` by metis_tac[LENGTH_NIL] >>
  rw_tac std_ss[leibniz_horizontal_alt, list_lcm_map_times]);

(* Theorem: SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n) *)
(* Proof:
     SUM (leibniz_horizontal n)
   = SUM (MAP (\j. (n + 1) * j) (binomial_horizontal n))   by leibniz_horizontal_alt
   = (n + 1) * SUM (binomial_horizontal n)                 by SUM_MULT
*)
val leibniz_horizontal_sum = store_thm(
  "leibniz_horizontal_sum",
  ``!n. SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n)``,
  rw[leibniz_horizontal_alt, SUM_MULT] >>
  `(\j. j * (n + 1)) = $* (n + 1)` by rw[FUN_EQ_THM] >>
  rw[]);

(* Theorem: SUM (leibniz_horizontal n) = (n + 1) * 2 ** n *)
(* Proof:
     SUM (leibniz_horizontal n)
   = (n + 1) * SUM (binomial_horizontal n)       by leibniz_horizontal_sum
   = (n + 1) * 2 ** n                            by binomial_horizontal_sum
*)
val leibniz_horizontal_sum_eqn = store_thm(
  "leibniz_horizontal_sum_eqn",
  ``!n. SUM (leibniz_horizontal n) = (n + 1) * 2 ** n``,
  rw[leibniz_horizontal_sum, binomial_horizontal_sum]);

(* Theorem: SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = SUM (binomial_horizontal n) *)
(* Proof:
   Note LENGTH (leibniz_horizontal n) = n + 1    by leibniz_horizontal_len
     so 0 < LENGTH (leibniz_horizontal n)        by 0 < n + 1

        SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n)
      = ((n + 1) * SUM (binomial_horizontal n))  DIV (n + 1)     by leibniz_horizontal_sum
      = SUM (binomial_horizontal n)                              by MULT_TO_DIV, 0 < n + 1
*)
val leibniz_horizontal_average = store_thm(
  "leibniz_horizontal_average",
  ``!n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = SUM (binomial_horizontal n)``,
  metis_tac[leibniz_horizontal_sum, leibniz_horizontal_len, MULT_TO_DIV, DECIDE``0 < n + 1``]);

(* Theorem: SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n *)
(* Proof:
        SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n)
      = SUM (binomial_horizontal n)    by leibniz_horizontal_average
      = 2 ** n                         by binomial_horizontal_sum
*)
val leibniz_horizontal_average_eqn = store_thm(
  "leibniz_horizontal_average_eqn",
  ``!n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n``,
  rw[leibniz_horizontal_average, binomial_horizontal_sum]);

(* ------------------------------------------------------------------------- *)
(* Transform from Vertical LCM to Horizontal LCM.                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Using Triplet and Paths                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define a triple type *)
val _ = Hol_datatype`
  triple = <| a: num;
              b: num;
              c: num
            |>
`;

(* A triplet is a triple composed of Leibniz node and children. *)
val triplet_def = Define`
    (triplet n k):triple =
        <| a := leibniz n k;
           b := leibniz (n + 1) k;
           c := leibniz (n + 1) (k + 1)
         |>
`;

(* can even do this after definition of triple type:

val triple_def = Define`
    triple n k =
        <| a := leibniz n k;
           b := leibniz (n + 1) k;
           c := leibniz (n + 1) (k + 1)
          |>
`;
*)

(* Overload elements of a triplet *)
(*
val _ = overload_on("tri_a", ``leibniz n k``);
val _ = overload_on("tri_b", ``leibniz (SUC n) k``);
val _ = overload_on("tri_c", ``leibniz (SUC n) (SUC k)``);

val _ = overload_on("tri_a", ``(triple n k).a``);
val _ = overload_on("tri_b", ``(triple n k).b``);
val _ = overload_on("tri_c", ``(triple n k).c``);
*)
val _ = temp_overload_on("ta", ``(triplet n k).a``);
val _ = temp_overload_on("tb", ``(triplet n k).b``);
val _ = temp_overload_on("tc", ``(triplet n k).c``);

(* Theorem: (ta = leibniz n k) /\ (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1)) *)
(* Proof: by triplet_def *)
val leibniz_triplet_member = store_thm(
  "leibniz_triplet_member",
  ``!n k. (ta = leibniz n k) /\ (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1))``,
  rw[triplet_def]);

(* Theorem: (k + 1) * tc = (n + 1 - k) * tb *)
(* Proof:
   Apply: > leibniz_right_eqn |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. (k + 1) * leibniz (n + 1) (k + 1) = (n + 1 - k) * leibniz (n + 1) k: thm
*)
val leibniz_right_entry = store_thm(
  "leibniz_right_entry",
  ``!(n k):num. (k + 1) * tc = (n + 1 - k) * tb``,
  rw_tac arith_ss[triplet_def, leibniz_right_eqn]);

(* Theorem: (n + 2) * ta = (n + 1 - k) * tb *)
(* Proof:
   Apply: > leibniz_up_eqn |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. (n + 1 + 1) * leibniz (n + 1 - 1) k = (n + 1 - k) * leibniz (n + 1) k: thm
*)
val leibniz_up_entry = store_thm(
  "leibniz_up_entry",
  ``!(n k):num. (n + 2) * ta = (n + 1 - k) * tb``,
  rw_tac std_ss[triplet_def, leibniz_up_eqn |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* Theorem: ta * tb = tc * (tb - ta) *)
(* Proof:
   Apply > leibniz_property |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. !k. leibniz (n + 1) k * leibniz (n + 1 - 1) k =
     leibniz (n + 1) (k + 1) * (leibniz (n + 1) k - leibniz (n + 1 - 1) k): thm
*)
val leibniz_triplet_property = store_thm(
  "leibniz_triplet_property",
  ``!(n k):num. ta * tb = tc * (tb - ta)``,
  rw_tac std_ss[triplet_def, MULT_COMM, leibniz_property |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* Direct proof of same result, for the paper. *)

(* Theorem: ta * tb = tc * (tb - ta) *)
(* Proof:
   If n < k,
      Note n < k ==> ta = 0               by triplet_def, leibniz_less_0
      also n + 1 < k + 1 ==> tc = 0       by triplet_def, leibniz_less_0
      Thus ta * tb = 0 = tc * (tb - ta)   by MULT_EQ_0
   If ~(n < k),
      Then (n + 2) - (n + 1 - k) = k + 1  by arithmetic, k <= n.

        (k + 1) * ta * tb
      = (n + 2 - (n + 1 - k)) * ta * tb
      = (n + 2) * ta * tb - (n + 1 - k) * ta * tb         by RIGHT_SUB_DISTRIB
      = (n + 1 - k) * tb * tb - (n + 1 - k) * ta * tb     by leibniz_up_entry
      = (n + 1 - k) * tb * tb - (n + 1 - k) * tb * ta     by MULT_ASSOC, MULT_COMM
      = (n + 1 - k) * tb * (tb - ta)                      by LEFT_SUB_DISTRIB
      = (k + 1) * tc * (tb - ta)                          by leibniz_right_entry

      Since k + 1 <> 0, the result follows                by MULT_LEFT_CANCEL
*)
Theorem leibniz_triplet_property[allow_rebind]:
  !n k:num. ta * tb = tc * (tb - ta)
Proof
  rpt strip_tac >>
  Cases_on ‘n < k’ >-
  rw[triplet_def, leibniz_less_0] >>
  ‘(n + 2) - (n + 1 - k) = k + 1’ by decide_tac >>
  ‘(k + 1) * ta * tb = (n + 2 - (n + 1 - k)) * ta * tb’ by rw[] >>
  ‘_ = (n + 2) * ta * tb - (n + 1 - k) * ta * tb’ by rw_tac std_ss[RIGHT_SUB_DISTRIB] >>
  ‘_ = (n + 1 - k) * tb * tb - (n + 1 - k) * ta * tb’ by rw_tac std_ss[leibniz_up_entry] >>
  ‘_ = (n + 1 - k) * tb * tb - (n + 1 - k) * tb * ta’ by metis_tac[MULT_ASSOC, MULT_COMM] >>
  ‘_ = (n + 1 - k) * tb * (tb - ta)’ by rw_tac std_ss[LEFT_SUB_DISTRIB] >>
  ‘_ = (k + 1) * tc * (tb - ta)’ by rw_tac std_ss[leibniz_right_entry] >>
  ‘k + 1 <> 0’ by decide_tac >>
  metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC]
QED

(* Theorem: lcm tb ta = lcm tb tc *)
(* Proof:
   Apply: > leibniz_lcm_exchange |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==>
            !k. lcm (leibniz (n + 1) k) (leibniz (n + 1 - 1) k) =
                lcm (leibniz (n + 1) k) (leibniz (n + 1) (k + 1)): thm
*)
val leibniz_triplet_lcm = store_thm(
  "leibniz_triplet_lcm",
  ``!(n k):num. lcm tb ta = lcm tb tc``,
  rw_tac std_ss[triplet_def, leibniz_lcm_exchange |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* ------------------------------------------------------------------------- *)
(* Zigzag Path in Leibniz Triangle                                           *)
(* ------------------------------------------------------------------------- *)

(* Define a path type *)
val _ = temp_type_abbrev("path", Type `:num list`);

(* Define paths reachable by one zigzag *)
val leibniz_zigzag_def = Define`
    leibniz_zigzag (p1: path) (p2: path) <=>
    ?(n k):num (x y):path. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)
`;
val _ = overload_on("zigzag", ``leibniz_zigzag``);
val _ = set_fixity "zigzag" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2) *)
(* Proof:
   Given p1 zigzag p2,
     ==> ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)  by leibniz_zigzag_def

     list_lcm p1
   = list_lcm (x ++ [tb; ta] ++ y)                      by above
   = lcm (list_lcm (x ++ [tb; ta])) (list_lcm y)        by list_lcm_append
   = lcm (list_lcm (x ++ ([tb; ta]))) (list_lcm y)      by APPEND_ASSOC
   = lcm (lcm (list_lcm x) (list_lcm ([tb; ta]))) (list_lcm y)   by list_lcm_append
   = lcm (lcm (list_lcm x) (lcm tb ta)) (list_lcm y)    by list_lcm_append, list_lcm_sing
   = lcm (lcm (list_lcm x) (lcm tb tc)) (list_lcm y)    by leibniz_triplet_lcm
   = lcm (lcm (list_lcm x) (list_lcm ([tb; tc]))) (list_lcm y)   by list_lcm_append, list_lcm_sing
   = lcm (list_lcm (x ++ ([tb; tc]))) (list_lcm y)      by list_lcm_append
   = lcm (list_lcm (x ++ [tb; tc])) (list_lcm y)        by APPEND_ASSOC
   = list_lcm (x ++ [tb; tc] ++ y)                      by list_lcm_append
   = list_lcm p2                                        by above
*)
val list_lcm_zigzag = store_thm(
  "list_lcm_zigzag",
  ``!p1 p2. p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2)``,
  rw_tac std_ss[leibniz_zigzag_def] >>
  `list_lcm (x ++ [tb; ta] ++ y) = lcm (list_lcm (x ++ [tb; ta])) (list_lcm y)` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm (x ++ ([tb; ta]))) (list_lcm y)` by rw[] >>
  `_ = lcm (lcm (list_lcm x) (lcm tb ta)) (list_lcm y)` by rw[list_lcm_append] >>
  `_ = lcm (lcm (list_lcm x) (lcm tb tc)) (list_lcm y)` by rw[leibniz_triplet_lcm] >>
  `_ = lcm (list_lcm (x ++ ([tb; tc]))) (list_lcm y)`  by rw[list_lcm_append] >>
  `_ = lcm (list_lcm (x ++ [tb; tc])) (list_lcm y)` by rw[] >>
  `_ = list_lcm (x ++ [tb; tc] ++ y)` by rw[list_lcm_append] >>
  rw[]);

(* Theorem: p1 zigzag p2 ==> !x. ([x] ++ p1) zigzag ([x] ++ p2) *)
(* Proof:
   Since p1 zigzag p2
     ==> ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)  by leibniz_zigzag_def

      [x] ++ p1
    = [x] ++ (x ++ [tb; ta] ++ y)        by above
    = [x] ++ x ++ [tb; ta] ++ y          by APPEND
      [x] ++ p2
    = [x] ++ (x ++ [tb; tc] ++ y)        by above
    = [x] ++ x ++ [tb; tc] ++ y          by APPEND
   Take new x = [x] ++ x, new y = y.
   Then ([x] ++ p1) zigzag ([x] ++ p2)   by leibniz_zigzag_def
*)
val leibniz_zigzag_tail = store_thm(
  "leibniz_zigzag_tail",
  ``!p1 p2. p1 zigzag p2 ==> !x. ([x] ++ p1) zigzag ([x] ++ p2)``,
  metis_tac[leibniz_zigzag_def, APPEND]);

(* Theorem: k <= n ==>
            TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
            TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n) *)
(* Proof:
   Since k <= n, k < n + 1, and k + 1 < n + 2.
   Hence k < LENGTH (leibniz_horizontal (n + 1)),

    Let x = TAKE k (leibniz_horizontal (n + 1))
    and y = DROP (k + 1) (leibniz_horizontal n)
        TAKE (k + 1) (leibniz_horizontal (n + 1))
      = TAKE (SUC k) (leibniz_horizontal (SUC n))   by ADD1
      = SNOC tb x                                   by TAKE_SUC_BY_TAKE, k < LENGTH (leibniz_horizontal (n + 1))
      = x ++ [tb]                                   by SNOC_APPEND
        TAKE (k + 2) (leibniz_horizontal (n + 1))
      = TAKE (SUC (SUC k)) (leibniz_horizontal (SUC n))   by ADD1
      = SNOC tc (SNOC tb x)                         by TAKE_SUC_BY_TAKE, k + 1 < LENGTH (leibniz_horizontal (n + 1))
      = x ++ [tb; tc]                               by SNOC_APPEND
        DROP k (leibniz_horizontal n)
      = ta :: y                                     by DROP_BY_DROP_SUC, k < LENGTH (leibniz_horizontal n)
      = [ta] ++ y                                   by CONS_APPEND
   Hence
    Let p1 = TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)
           = x ++ [tb] ++ [ta] ++ y
           = x ++ [tb; ta] ++ y                     by APPEND
    Let p2 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
           = x ++ [tb; tc] ++ y
   Therefore p1 zigzag p2                           by leibniz_zigzag_def
*)
val leibniz_horizontal_zigzag = store_thm(
  "leibniz_horizontal_zigzag",
  ``!n k. k <= n ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
                    TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)``,
  rpt strip_tac >>
  qabbrev_tac `x = TAKE k (leibniz_horizontal (n + 1))` >>
  qabbrev_tac `y = DROP (k + 1) (leibniz_horizontal n)` >>
  `k <= n + 1` by decide_tac >>
  `EL k (leibniz_horizontal n) = ta` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `EL k (leibniz_horizontal (n + 1)) = tb` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `EL (k + 1) (leibniz_horizontal (n + 1)) = tc` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `k < n + 1` by decide_tac >>
  `k < LENGTH (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_len] >>
  `TAKE (k + 1) (leibniz_horizontal (n + 1)) = TAKE (SUC k) (leibniz_horizontal (n + 1))` by rw[ADD1] >>
  `_ = SNOC tb x` by rw[TAKE_SUC_BY_TAKE, Abbr`x`] >>
  `_ = x ++ [tb]` by rw[] >>
  `SUC k < n + 2` by decide_tac >>
  `SUC k < LENGTH (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_len] >>
  `TAKE (k + 2) (leibniz_horizontal (n + 1)) = TAKE (SUC (SUC k)) (leibniz_horizontal (n + 1))` by rw[ADD1] >>
  `_ = SNOC tc (SNOC tb x)` by rw_tac std_ss[TAKE_SUC_BY_TAKE, ADD1, Abbr`x`] >>
  `_ = x ++ [tb; tc]` by rw[] >>
  `DROP k (leibniz_horizontal n) = [ta] ++ y` by rw[DROP_BY_DROP_SUC, ADD1, Abbr`y`] >>
  qabbrev_tac `p1 = TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)` >>
  qabbrev_tac `p2 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ y` >>
  `p1 = x ++ [tb; ta] ++ y` by rw[Abbr`p1`, Abbr`x`, Abbr`y`] >>
  `p2 = x ++ [tb; tc] ++ y` by rw[Abbr`p2`, Abbr`x`] >>
  metis_tac[leibniz_zigzag_def]);

(* Theorem: (leibniz_up 1) zigzag (leibniz_horizontal 1) *)
(* Proof:
   Since leibniz_up 1
       = [2; 1]                  by EVAL_TAC
       = [] ++ [2; 1] ++ []      by EVAL_TAC
     and leibniz_horizontal 1
       = [2; 2]                  by EVAL_TAC
       = [] ++ [2; 2] ++ []      by EVAL_TAC
     Now the first Leibniz triplet is:
         (triplet 0 0).a = 1     by EVAL_TAC
         (triplet 0 0).b = 2     by EVAL_TAC
         (triplet 0 0).c = 2     by EVAL_TAC
   Hence (leibniz_up 1) zigzag (leibniz_horizontal 1)   by leibniz_zigzag_def
*)
val leibniz_triplet_0 = store_thm(
  "leibniz_triplet_0",
  ``(leibniz_up 1) zigzag (leibniz_horizontal 1)``,
  `leibniz_up 1 = [] ++ [2; 1] ++ []` by EVAL_TAC >>
  `leibniz_horizontal 1 = [] ++ [2; 2] ++ []` by EVAL_TAC >>
  `((triplet 0 0).a = 1) /\ ((triplet 0 0).b = 2) /\ ((triplet 0 0).c = 2)` by EVAL_TAC >>
  metis_tac[leibniz_zigzag_def]);

(* ------------------------------------------------------------------------- *)
(* Wriggle Paths in Leibniz Triangle                                         *)
(* ------------------------------------------------------------------------- *)

(* Define paths reachable by many zigzags *)
(*
val leibniz_wriggle_def = Define`
    leibniz_wriggle (p1: path) (p2: path) <=>
    ?(m:num) (f:num -> path).
          (p1 = f 0) /\
          (p2 = f m) /\
          (!k. k < m ==> (f k) zigzag (f (SUC k)))
`;
*)

(* Define paths reachable by many zigzags by closure *)
val _ = overload_on("wriggle", ``RTC leibniz_zigzag``); (* RTC = reflexive transitive closure *)
val _ = set_fixity "wriggle" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2) *)
(* Proof:
   By RTC_STRONG_INDUCT.
   Base: list_lcm p1 = list_lcm p1, trivially true.
   Step: p1 zigzag p1' /\ p1' wriggle p2 /\ list_lcm p1' = list_lcm p2 ==> list_lcm p1 = list_lcm p2
         list_lcm p1
       = list_lcm p1'     by list_lcm_zigzag
       = list_lcm p2      by induction hypothesis
*)
val list_lcm_wriggle = store_thm(
  "list_lcm_wriggle",
  ``!p1 p2. p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  metis_tac[list_lcm_zigzag]);

(* Theorem: p1 zigzag p2 ==> p1 wriggle p2 *)
(* Proof:
     p1 wriggle p2
   = p1 (RTC zigzag) p2    by notation
   = p1 zigzag p2          by RTC_SINGLE
*)
val leibniz_zigzag_wriggle = store_thm(
  "leibniz_zigzag_wriggle",
  ``!p1 p2. p1 zigzag p2 ==> p1 wriggle p2``,
  rw[]);

(* Theorem: p1 wriggle p2 ==> !x. ([x] ++ p1) wriggle ([x] ++ p2) *)
(* Proof:
   By RTC_STRONG_INDUCT.
   Base: [x] ++ p1 wriggle [x] ++ p1
      True by RTC_REFL.
   Step: p1 zigzag p1' /\ p1' wriggle p2 /\ !x. [x] ++ p1' wriggle [x] ++ p2 ==>
         [x] ++ p1 wriggle [x] ++ p2
      Since p1 zigzag p1',
         so [x] ++ p1 zigzag [x] ++ p1'    by leibniz_zigzag_tail
         or [x] ++ p1 wriggle [x] ++ p1'   by leibniz_zigzag_wriggle
       With [x] ++ p1' wriggle [x] ++ p2   by induction hypothesis
      Hence [x] ++ p1 wriggle [x] ++ p2    by RTC_TRANS
*)
val leibniz_wriggle_tail = store_thm(
  "leibniz_wriggle_tail",
  ``!p1 p2. p1 wriggle p2 ==> !x. ([x] ++ p1) wriggle ([x] ++ p2)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  metis_tac[leibniz_zigzag_tail, leibniz_zigzag_wriggle, RTC_TRANS]);

(* Theorem: p1 wriggle p1 *)
(* Proof: by RTC_REFL *)
val leibniz_wriggle_refl = store_thm(
  "leibniz_wriggle_refl",
  ``!p1. p1 wriggle p1``,
  metis_tac[RTC_REFL]);

(* Theorem: p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3 *)
(* Proof: by RTC_TRANS *)
val leibniz_wriggle_trans = store_thm(
  "leibniz_wriggle_trans",
  ``!p1 p2 p3. p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3``,
  metis_tac[RTC_TRANS]);

(* Theorem: k <= n + 1 ==>
            TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
            leibniz_horizontal (n + 1) *)
(* Proof:
   By induction on the difference: n + 1 - k.
   Base: k = n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                       leibniz_horizontal (n + 1)
           TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)
         = TAKE (n + 2) (leibniz_horizontal (n + 1)) ++ DROP (n + 1) (leibniz_horizontal n)  by k = n + 1
         = leibniz_horizontal (n + 1) ++ []       by TAKE_LENGTH_ID, DROP_LENGTH_NIL
         = leibniz_horizontal (n + 1)             by APPEND_NIL
         Hence they wriggle to each other         by RTC_REFL
   Step: k <= n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                        leibniz_horizontal (n + 1)
        Let p1 = leibniz_horizontal (n + 1)
            p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_horizontal n)
            p3 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
       Then p2 zigzag p3                 by leibniz_horizontal_zigzag
        and p3 wriggle p1                by induction hypothesis
       Hence p2 wriggle p1               by RTC_RULES
*)
val leibniz_horizontal_wriggle_step = store_thm(
  "leibniz_horizontal_wriggle_step",
  ``!n k. k <= n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                        leibniz_horizontal (n + 1)``,
  Induct_on `n + 1 - k` >| [
    rpt strip_tac >>
    rw_tac arith_ss[] >>
    `n + 1 = k` by decide_tac >>
    rw[TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt],
    rpt strip_tac >>
    `v = n - k` by decide_tac >>
    `v = (n + 1) - (k + 1)` by decide_tac >>
    `k <= n` by decide_tac >>
    `k + 1 <= n + 1` by decide_tac >>
    `k + 1 + 1 = k + 2` by decide_tac >>
    qabbrev_tac `p1 = leibniz_horizontal (n + 1)` >>
    qabbrev_tac `p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_horizontal n)` >>
    qabbrev_tac `p3 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)` >>
    `p2 zigzag p3` by rw[leibniz_horizontal_zigzag, Abbr`p1`, Abbr`p2`, Abbr`p3`] >>
    metis_tac[RTC_RULES]
  ]);

(* Theorem: ([leibniz (n + 1) 0] ++ leibniz_horizontal n) wriggle leibniz_horizontal (n + 1) *)
(* Proof:
   Apply > leibniz_horizontal_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0];
   val it = |- TAKE 1 (leibniz_horizontal (n + 1)) ++ leibniz_horizontal n wriggle leibniz_horizontal (n + 1): thm
*)
val leibniz_horizontal_wriggle = store_thm(
  "leibniz_horizontal_wriggle",
  ``!n. ([leibniz (n + 1) 0] ++ leibniz_horizontal n) wriggle leibniz_horizontal (n + 1)``,
  rpt strip_tac >>
  `TAKE 1 (leibniz_horizontal (n + 1)) = [leibniz (n + 1) 0]` by rw[leibniz_horizontal_head, binomial_n_0] >>
  metis_tac[leibniz_horizontal_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0]]);

(* ------------------------------------------------------------------------- *)
(* Path Transform keeping LCM                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (leibniz_up n) wriggle (leibniz_horizontal n) *)
(* Proof:
   By induction on n.
   Base: leibniz_up 0 wriggle leibniz_horizontal 0
      Since leibniz_up 0 = [1]                             by leibniz_up_0
        and leibniz_horizontal 0 = [1]                     by leibniz_horizontal_0
      Hence leibniz_up 0 wriggle leibniz_horizontal 0      by leibniz_wriggle_refl
   Step: leibniz_up n wriggle leibniz_horizontal n ==>
         leibniz_up (SUC n) wriggle leibniz_horizontal (SUC n)
         Let x = leibniz (n + 1) 0.
         Then x = n + 2                                    by leibniz_n_0
          Now leibniz_up (n + 1) = [x] ++ (leibniz_up n)   by leibniz_up_cons
        Since leibniz_up n wriggle leibniz_horizontal n    by induction hypothesis
           so ([x] ++ (leibniz_up n)) wriggle
              ([x] ++ (leibniz_horizontal n))              by leibniz_wriggle_tail
          and ([x] ++ (leibniz_horizontal n)) wriggle
              (leibniz_horizontal (n + 1))                 by leibniz_horizontal_wriggle
        Hence leibniz_up (SUC n) wriggle
              leibniz_horizontal (SUC n)                   by leibniz_wriggle_trans, ADD1
*)
val leibniz_up_wriggle_horizontal = store_thm(
  "leibniz_up_wriggle_horizontal",
  ``!n. (leibniz_up n) wriggle (leibniz_horizontal n)``,
  Induct >-
  rw[leibniz_up_0, leibniz_horizontal_0] >>
  qabbrev_tac `x = leibniz (n + 1) 0` >>
  `x = n + 2` by rw[leibniz_n_0, Abbr`x`] >>
  `leibniz_up (n + 1) = [x] ++ (leibniz_up n)` by rw[leibniz_up_cons, Abbr`x`] >>
  `([x] ++ (leibniz_up n)) wriggle ([x] ++ (leibniz_horizontal n))` by rw[leibniz_wriggle_tail] >>
  `([x] ++ (leibniz_horizontal n)) wriggle (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_wriggle, Abbr`x`] >>
  metis_tac[leibniz_wriggle_trans, ADD1]);

(* Theorem: list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n) *)
(* Proof:
   Since leibniz_up n = REVERSE (leibniz_vertical n)    by notation
     and leibniz_up n wriggle leibniz_horizontal n      by leibniz_up_wriggle_horizontal
         list_lcm (leibniz_vertical n)
       = list_lcm (leibniz_up n)                        by list_lcm_reverse
       = list_lcm (leibniz_horizontal n)                by list_lcm_wriggle
*)
val leibniz_lcm_property = store_thm(
  "leibniz_lcm_property",
  ``!n. list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)``,
  metis_tac[leibniz_up_wriggle_horizontal, list_lcm_wriggle, list_lcm_reverse]);

(* This is a milestone theorem. *)

(* Theorem: k <= n ==> (leibniz n k) divides list_lcm (leibniz_vertical n) *)
(* Proof:
   Note (leibniz n k) divides list_lcm (leibniz_horizontal n)   by leibniz_horizontal_divisor
    ==> (leibniz n k) divides list_lcm (leibniz_vertical n)     by leibniz_lcm_property
*)
val leibniz_vertical_divisor = store_thm(
  "leibniz_vertical_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides list_lcm (leibniz_vertical n)``,
  metis_tac[leibniz_horizontal_divisor, leibniz_lcm_property]);

(* ------------------------------------------------------------------------- *)
(* Lower Bound of Leibniz LCM                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 2 ** n <= list_lcm (leibniz_horizontal n) *)
(* Proof:
   Note LENGTH (binomail_horizontal n) = n + 1    by binomial_horizontal_len
    and EVERY_POSITIVE (binomial_horizontal n) by binomial_horizontal_pos .. [1]
     list_lcm (leibniz_horizontal n)
   = (n + 1) * list_lcm (binomial_horizontal n)   by leibniz_horizontal_lcm_alt
   >= SUM (binomial_horizontal n)                 by list_lcm_lower_bound, [1]
   = 2 ** n                                       by binomial_horizontal_sum
*)
val leibniz_horizontal_lcm_lower = store_thm(
  "leibniz_horizontal_lcm_lower",
  ``!n. 2 ** n <= list_lcm (leibniz_horizontal n)``,
  rpt strip_tac >>
  `LENGTH (binomial_horizontal n) = n + 1` by rw[binomial_horizontal_len] >>
  `EVERY_POSITIVE (binomial_horizontal n)` by rw[binomial_horizontal_pos] >>
  `list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)` by rw[leibniz_horizontal_lcm_alt] >>
  `SUM (binomial_horizontal n) = 2 ** n` by rw[binomial_horizontal_sum] >>
  metis_tac[list_lcm_lower_bound]);

(* Theorem: 2 ** n <= list_lcm (leibniz_vertical n) *)
(* Proof:
    list_lcm (leibniz_vertical n)
  = list_lcm (leibniz_horizontal n)      by leibniz_lcm_property
  >= 2 ** n                              by leibniz_horizontal_lcm_lower
*)
val leibniz_vertical_lcm_lower = store_thm(
  "leibniz_vertical_lcm_lower",
  ``!n. 2 ** n <= list_lcm (leibniz_vertical n)``,
  rw_tac std_ss[leibniz_horizontal_lcm_lower, leibniz_lcm_property]);

(* Theorem: 2 ** n <= list_lcm [1 .. (n + 1)] *)
(* Proof: by leibniz_vertical_lcm_lower. *)
val lcm_lower_bound = store_thm(
  "lcm_lower_bound",
  ``!n. 2 ** n <= list_lcm [1 .. (n + 1)]``,
  rw[leibniz_vertical_lcm_lower]);

(* ------------------------------------------------------------------------- *)
(* Leibniz LCM Invariance                                                    *)
(* ------------------------------------------------------------------------- *)

(* Use overloading for leibniz_col_arm rooted at leibniz a b, of length n. *)
val _ = overload_on("leibniz_col_arm", ``\a b n. MAP (\x. leibniz (a - x) b) [0 ..< n]``);

(* Use overloading for leibniz_seg_arm rooted at leibniz a b, of length n. *)
val _ = overload_on("leibniz_seg_arm", ``\a b n. MAP (\x. leibniz a (b + x)) [0 ..< n]``);

(*
> EVAL ``leibniz_col_arm 5 1 4``;
val it = |- leibniz_col_arm 5 1 4 = [30; 20; 12; 6]: thm
> EVAL ``leibniz_seg_arm 5 1 4``;
val it = |- leibniz_seg_arm 5 1 4 = [30; 60; 60; 30]: thm
> EVAL ``list_lcm (leibniz_col_arm 5 1 4)``;
val it = |- list_lcm (leibniz_col_arm 5 1 4) = 60: thm
> EVAL ``list_lcm (leibniz_seg_arm 5 1 4)``;
val it = |- list_lcm (leibniz_seg_arm 5 1 4) = 60: thm
*)

(* Theorem: leibniz_col_arm a b 0 = [] *)
(* Proof:
     leibniz_col_arm a b 0
   = MAP (\x. leibniz (a - x) b) [0 ..< 0]     by notation
   = MAP (\x. leibniz (a - x) b) []            by listRangeLHI_def
   = []                                        by MAP
*)
val leibniz_col_arm_0 = store_thm(
  "leibniz_col_arm_0",
  ``!a b. leibniz_col_arm a b 0 = []``,
  rw[]);

(* Theorem: leibniz_seg_arm a b 0 = [] *)
(* Proof:
     leibniz_seg_arm a b 0
   = MAP (\x. leibniz a (b + x)) [0 ..< 0]     by notation
   = MAP (\x. leibniz a (b + x)) []            by listRangeLHI_def
   = []                                        by MAP
*)
val leibniz_seg_arm_0 = store_thm(
  "leibniz_seg_arm_0",
  ``!a b. leibniz_seg_arm a b 0 = []``,
  rw[]);

(* Theorem: leibniz_col_arm a b 1 = [leibniz a b] *)
(* Proof:
     leibniz_col_arm a b 1
   = MAP (\x. leibniz (a - x) b) [0 ..< 1]     by notation
   = MAP (\x. leibniz (a - x) b) [0]           by listRangeLHI_def
   = (\x. leibniz (a - x) b) 0 ::[]            by MAP
   = [leibniz a b]                             by function application
*)
val leibniz_col_arm_1 = store_thm(
  "leibniz_col_arm_1",
  ``!a b. leibniz_col_arm a b 1 = [leibniz a b]``,
  rw[listRangeLHI_def]);

(* Theorem: leibniz_seg_arm a b 1 = [leibniz a b] *)
(* Proof:
     leibniz_seg_arm a b 1
   = MAP (\x. leibniz a (b + x)) [0 ..< 1]     by notation
   = MAP (\x. leibniz a (b + x)) [0]           by listRangeLHI_def
   = (\x. leibniz a (b + x)) 0 :: []           by MAP
   = [leibniz a b]                             by function application
*)
val leibniz_seg_arm_1 = store_thm(
  "leibniz_seg_arm_1",
  ``!a b. leibniz_seg_arm a b 1 = [leibniz a b]``,
  rw[listRangeLHI_def]);

(* Theorem: LENGTH (leibniz_col_arm a b n) = n *)
(* Proof:
     LENGTH (leibniz_col_arm a b n)
   = LENGTH (MAP (\x. leibniz (a - x) b) [0 ..< n])   by notation
   = LENGTH [0 ..< n]                                 by LENGTH_MAP
   = LENGTH (GENLIST (\i. i) n)                       by listRangeLHI_def
   = m                                                by LENGTH_GENLIST
*)
val leibniz_col_arm_len = store_thm(
  "leibniz_col_arm_len",
  ``!a b n. LENGTH (leibniz_col_arm a b n) = n``,
  rw[]);

(* Theorem: LENGTH (leibniz_seg_arm a b n) = n *)
(* Proof:
     LENGTH (leibniz_seg_arm a b n)
   = LENGTH (MAP (\x. leibniz a (b + x)) [0 ..< n])   by notation
   = LENGTH [0 ..< n]                                 by LENGTH_MAP
   = LENGTH (GENLIST (\i. i) n)                       by listRangeLHI_def
   = m                                                by LENGTH_GENLIST
*)
val leibniz_seg_arm_len = store_thm(
  "leibniz_seg_arm_len",
  ``!a b n. LENGTH (leibniz_seg_arm a b n) = n``,
  rw[]);

(* Theorem: k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b *)
(* Proof:
   Note LENGTH [0 ..< n] = n                      by LENGTH_listRangeLHI
     EL k (leibniz_col_arm a b n)
   = EL k (MAP (\x. leibniz (a - x) b) [0 ..< n]) by notation
   = (\x. leibniz (a - x) b) (EL k [0 ..< n])     by EL_MAP
   = (\x. leibniz (a - x) b) k                    by EL_listRangeLHI
   = leibniz (a - k) b
*)
val leibniz_col_arm_el = store_thm(
  "leibniz_col_arm_el",
  ``!n k. k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b``,
  rw[EL_MAP, EL_listRangeLHI]);

(* Theorem: k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k) *)
(* Proof:
   Note LENGTH [0 ..< n] = n                      by LENGTH_listRangeLHI
     EL k (leibniz_seg_arm a b n)
   = EL k (MAP (\x. leibniz a (b + x)) [0 ..< n]) by notation
   = (\x. leibniz a (b + x)) (EL k [0 ..< n])     by EL_MAP
   = (\x. leibniz a (b + x)) k                    by EL_listRangeLHI
   = leibniz a (b + k)
*)
val leibniz_seg_arm_el = store_thm(
  "leibniz_seg_arm_el",
  ``!n k. k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k)``,
  rw[EL_MAP, EL_listRangeLHI]);

(* Theorem: TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b] *)
(* Proof:
   Note LENGTH (leibniz_seg_arm a b (n + 1)) = n + 1   by leibniz_seg_arm_len
    and 0 < n + 1                                      by ADD1, SUC_POS
     TAKE 1 (leibniz_seg_arm a b (n + 1))
   = TAKE (SUC 0) (leibniz_seg_arm a b (n + 1))        by ONE
   = SNOC (EL 0 (leibniz_seg_arm a b (n + 1))) []      by TAKE_SUC_BY_TAKE, TAKE_0
   = [EL 0 (leibniz_seg_arm a b (n + 1))]              by SNOC_NIL
   = leibniz a b                                       by leibniz_seg_arm_el
*)
val leibniz_seg_arm_head = store_thm(
  "leibniz_seg_arm_head",
  ``!a b n. TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b]``,
  metis_tac[leibniz_seg_arm_len, leibniz_seg_arm_el,
             ONE, TAKE_SUC_BY_TAKE, TAKE_0, SNOC_NIL, DECIDE``!n. 0 < n + 1 /\ (n + 0 = n)``]);

(* Theorem: leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b :: leibniz_col_arm a b n *)
(* Proof:
   Note (\x. leibniz (a + 1 - x) b) o SUC
      = (\x. leibniz (a + 1 - (x + 1)) b)     by FUN_EQ_THM
      = (\x. leibniz (a - x) b)               by arithmetic

     leibniz_col_arm (a + 1) b (n + 1)
   = MAP (\x. leibniz (a + 1 - x) b) [0 ..< (n + 1)]                  by notation
   = MAP (\x. leibniz (a + 1 - x) b) (0::[1 ..< (n+1)])               by listRangeLHI_CONS, 0 < n + 1
   = (\x. leibniz (a + 1 - x) b) 0 :: MAP (\x. leibniz (a + 1 - x) b) [1 ..< (n+1)]   by MAP
   = leibniz (a + 1) b :: MAP (\x. leibniz (a + 1 - x) b) [1 ..< (n+1)]       by function application
   = leibniz (a + 1) b :: MAP ((\x. leibniz (a + 1 - x) b) o SUC) [0 ..< n]   by listRangeLHI_MAP_SUC
   = leibniz (a + 1) b :: MAP (\x. leibniz (a - x) b) [0 ..< n]        by above
   = leibniz (a + 1) b :: leibniz_col_arm a b n                        by notation
*)
val leibniz_col_arm_cons = store_thm(
  "leibniz_col_arm_cons",
  ``!a b n. leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b :: leibniz_col_arm a b n``,
  rpt strip_tac >>
  `!a x. a + 1 - SUC x + 1 = a - x + 1` by decide_tac >>
  `!a x. a + 1 - SUC x = a - x` by decide_tac >>
  `(\x. leibniz (a + 1 - x) b) o SUC = (\x. leibniz (a + 1 - (x + 1)) b)` by rw[FUN_EQ_THM] >>
  `0 < n + 1` by decide_tac >>
  `leibniz_col_arm (a + 1) b (n + 1) = MAP (\x. leibniz (a + 1 - x) b) (0::[1 ..< (n+1)])` by rw[listRangeLHI_CONS] >>
  `_ = leibniz (a + 1) b :: MAP (\x. leibniz (a + 1 - x) b) [0+1 ..< (n+1)]` by rw[] >>
  `_ = leibniz (a + 1) b :: MAP ((\x. leibniz (a + 1 - x) b) o SUC) [0 ..< n]` by rw[listRangeLHI_MAP_SUC] >>
  `_ = leibniz (a + 1) b :: leibniz_col_arm a b n` by rw[] >>
  rw[]);

(* Theorem: k < n ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
    TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n) *)
(* Proof:
   Since k <= n, k < n + 1, and k + 1 < n + 2.
   Hence k < LENGTH (leibniz_seg_arm a b (n + 1)),

    Let x = TAKE k (leibniz_seg_arm a b (n + 1))
    and y = DROP (k + 1) (leibniz_seg_arm a b n)
        TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1))
      = TAKE (SUC k) (leibniz_seg_arm (a + 1) b (n + 1))   by ADD1
      = SNOC t.b x                                         by TAKE_SUC_BY_TAKE, k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))
      = x ++ [t.b]                                    by SNOC_APPEND
        TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1))
      = TAKE (SUC (SUC k)) (leibniz_seg_arm (a + 1) b (SUC n))   by ADD1
      = SNOC t.c (SNOC t.b x)                         by TAKE_SUC_BY_TAKE, SUC k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))
      = x ++ [t.b; t.c]                               by SNOC_APPEND
        DROP k (leibniz_seg_arm a b n)
      = t.a :: y                                      by DROP_BY_DROP_SUC, k < LENGTH (leibniz_seg_arm a b n)
      = [t.a] ++ y                                    by CONS_APPEND
   Hence
    Let p1 = TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)
           = x ++ [t.b] ++ [t.a] ++ y
           = x ++ [t.b; t.a] ++ y                     by APPEND
    Let p2 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
           = x ++ [t.b; t.c] ++ y
   Therefore p1 zigzag p2                             by leibniz_zigzag_def
*)
val leibniz_seg_arm_zigzag_step = store_thm(
  "leibniz_seg_arm_zigzag_step",
  ``!n k. k < n ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
    TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)``,
  rpt strip_tac >>
  qabbrev_tac `x = TAKE k (leibniz_seg_arm (a + 1) b (n + 1))` >>
  qabbrev_tac `y = DROP (k + 1) (leibniz_seg_arm a b n)` >>
  qabbrev_tac `t = triplet a (b + k)` >>
  `k < n + 1 /\ k + 1 < n + 1` by decide_tac >>
  `EL k (leibniz_seg_arm a b n) = t.a` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `EL k (leibniz_seg_arm (a + 1) b (n + 1)) = t.b` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `EL (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) = t.c` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `k < LENGTH (leibniz_seg_arm a b (n + 1))` by rw[leibniz_seg_arm_len] >>
  `TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) = TAKE (SUC k) (leibniz_seg_arm (a + 1) b (n + 1))` by rw[ADD1] >>
  `_ = SNOC t.b x` by rw[TAKE_SUC_BY_TAKE, Abbr`x`] >>
  `_ = x ++ [t.b]` by rw[] >>
  `SUC k < n + 1` by decide_tac >>
  `SUC k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))` by rw[leibniz_seg_arm_len] >>
  `k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))` by decide_tac >>
  `TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) = TAKE (SUC (SUC k)) (leibniz_seg_arm (a + 1) b (n + 1))` by rw[ADD1] >>
  `_ = SNOC t.c (SNOC t.b x)` by metis_tac[TAKE_SUC_BY_TAKE, ADD1] >>
  `_ = x ++ [t.b; t.c]` by rw[] >>
  `DROP k (leibniz_seg_arm a b n) = [t.a] ++ y` by rw[DROP_BY_DROP_SUC, ADD1, Abbr`y`] >>
  qabbrev_tac `p1 = TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)` >>
  qabbrev_tac `p2 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ y` >>
  `p1 = x ++ [t.b; t.a] ++ y` by rw[Abbr`p1`, Abbr`x`, Abbr`y`] >>
  `p2 = x ++ [t.b; t.c] ++ y` by rw[Abbr`p2`, Abbr`x`] >>
  metis_tac[leibniz_zigzag_def]);

(* Theorem: k < n + 1 ==> !a b.
            TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
            leibniz_seg_arm (a + 1) b (n + 1) *)
(* Proof:
   By induction on the difference: n - k.
   Base: k = n ==> TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                   leibniz_seg_arm a b (n + 1)
         Note LENGTH (leibniz_seg_arm (a + 1) b (n + 1)) = n + 1   by leibniz_seg_arm_len
          and LENGTH (leibniz_seg_arm a b n) = n                   by leibniz_seg_arm_len
           TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)
         = TAKE (n + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP n (leibniz_seg_arm a b n)  by k = n
         = leibniz_seg_arm a b n ++ []           by TAKE_LENGTH_ID, DROP_LENGTH_NIL
         = leibniz_seg_arm a b n                 by APPEND_NIL
         Hence they wriggle to each other        by RTC_REFL
   Step: k < n + 1 ==> TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                       leibniz_seg_arm a b (n + 1)
        Let p1 = leibniz_seg_arm (a + 1) b (n + 1)
            p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_seg_arm a b n)
            p3 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
       Then p2 zigzag p3                 by leibniz_seg_arm_zigzag_step
        and p3 wriggle p1                by induction hypothesis
       Hence p2 wriggle p1               by RTC_RULES
*)
val leibniz_seg_arm_wriggle_step = store_thm(
  "leibniz_seg_arm_wriggle_step",
  ``!n k. k < n + 1 ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
    leibniz_seg_arm (a + 1) b (n + 1)``,
  Induct_on `n - k` >| [
    rpt strip_tac >>
    `k = n` by decide_tac >>
    metis_tac[leibniz_seg_arm_len, TAKE_LENGTH_ID, DROP_LENGTH_NIL, APPEND_NIL, RTC_REFL],
    rpt strip_tac >>
    qabbrev_tac `p1 = leibniz_seg_arm (a + 1) b (n + 1)` >>
    qabbrev_tac `p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_seg_arm a b n)` >>
    qabbrev_tac `p3 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)` >>
    `p2 zigzag p3` by rw[leibniz_seg_arm_zigzag_step, Abbr`p1`, Abbr`p2`, Abbr`p3`] >>
    `v = n - (k + 1)` by decide_tac >>
    `k + 1 < n + 1` by decide_tac >>
    `k + 1 + 1 = k + 2` by decide_tac >>
    metis_tac[RTC_RULES]
  ]);

(* Theorem: ([leibniz (a + 1) b] ++ leibniz_seg_arm a b n) wriggle leibniz_seg_arm (a + 1) b (n + 1) *)
(* Proof:
   Apply > leibniz_seg_arm_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0];
   val it =
   |- 0 < n + 1 ==> !a b.
     TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ leibniz_seg_arm a b n wriggle
     leibniz_seg_arm (a + 1) b (n + 1):
   thm

   Note 0 < n + 1                                       by ADD1, SUC_POS
     [leibniz (a + 1) b] ++ leibniz_seg_arm a b n
   = TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ leibniz_seg_arm a b n           by leibniz_seg_arm_head
   = TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP 0 (leibniz_seg_arm a b n)  by DROP_0
   wriggle leibniz_seg_arm (a + 1) b (n + 1)            by leibniz_seg_arm_wriggle_step, put k = 0
*)
val leibniz_seg_arm_wriggle_row_arm = store_thm(
  "leibniz_seg_arm_wriggle_row_arm",
  ``!a b n. ([leibniz (a + 1) b] ++ leibniz_seg_arm a b n) wriggle leibniz_seg_arm (a + 1) b (n + 1)``,
  rpt strip_tac >>
  `0 < n + 1 /\ (0 + 1 = 1)` by decide_tac >>
  metis_tac[leibniz_seg_arm_head, leibniz_seg_arm_wriggle_step, DROP_0]);

(* Theorem: b <= a /\ n <= a + 1 - b ==> (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n) *)
(* Proof:
   By induction on n.
   Base: leibniz_col_arm a b 0 wriggle leibniz_seg_arm a b 0
      Since leibniz_col_arm a b 0 = []                     by leibniz_col_arm_0
        and leibniz_seg_arm a b 0 = []                     by leibniz_seg_arm_0
      Hence leibniz_col_arm a b 0 wriggle leibniz_seg_arm a b 0   by leibniz_wriggle_refl
   Step: !a b. leibniz_col_arm a b n wriggle leibniz_seg_arm a b n ==>
         leibniz_col_arm a b (SUC n) wriggle leibniz_seg_arm a b (SUC n)
         Induct_on a.
         Base: b <= 0 /\ SUC n <= 0 + 1 - b ==> leibniz_col_arm 0 b (SUC n) wriggle leibniz_seg_arm 0 b (SUC n)
         Note SUC n <= 1 - b ==> n = 0, since 0 <= b.
              leibniz_col_arm 0 b (SUC 0)
            = leibniz_col_arm 0 b 1                       by ONE
            = [leibniz 0 b]                               by leibniz_col_arm_1
              leibniz_seg_arm 0 b (SUC 0)
            = leibniz_seg_arm 0 b 1                       by ONE
            = [leibniz 0 b]                               by leibniz_seg_arm_1
         Hence leibniz_col_arm 0 b 1 wriggle
               leibniz_seg_arm 0 b 1                      by leibniz_wriggle_refl
         Step: b <= SUC a /\ SUC n <= SUC a + 1 - b ==> leibniz_col_arm (SUC a) b (SUC n) wriggle leibniz_seg_arm (SUC a) b (SUC n)
         Note n <= a + 1 - b
           If a + 1 = b,
              Then n = 0,
                leibniz_col_arm (SUC a) b (SUC 0)
              = leibniz_col_arm (SUC a) b 1               by ONE
              = [leibniz (SUC a) b]                       by leibniz_col_arm_1
              = leibniz_seg_arm (SUC a) b 1               by leibniz_seg_arm_1
              = leibniz_seg_arm (SUC a) b (SUC 0)         by ONE
          Hence leibniz_col_arm (SUC a) b 1 wriggle
                leibniz_seg_arm (SUC a) b 1               by leibniz_wriggle_refl
           If a + 1 <> b,
         Then b <= a, and induction hypothesis applies.
         Let x = leibniz (a + 1) b.
         Then leibniz_col_arm (a + 1) b (n + 1)
            = [x] ++ (leibniz_col_arm a b n)              by leibniz_col_arm_cons
        Since leibniz_col_arm a b n
              wriggle leibniz_seg_arm a b n               by induction hypothesis
           so ([x] ++ (leibniz_col_arm a b n)) wriggle
              ([x] ++ (leibniz_seg_arm a b n))            by leibniz_wriggle_tail
          and ([x] ++ (leibniz_seg_arm a b n)) wriggle
              (leibniz_seg_arm (a + 1) b (n + 1))         by leibniz_seg_arm_wriggle_row_arm
        Hence leibniz_col_arm a b (SUC n) wriggle
              leibniz_seg_arm a b (SUC n)                 by leibniz_wriggle_trans, ADD1
*)
val leibniz_col_arm_wriggle_row_arm = store_thm(
  "leibniz_col_arm_wriggle_row_arm",
  ``!a b n. b <= a /\ n <= a + 1 - b ==> (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n)``,
  Induct_on `n` >-
  rw[leibniz_col_arm_0, leibniz_seg_arm_0] >>
  rpt strip_tac >>
  Induct_on `a` >| [
    rpt strip_tac >>
    `n = 0` by decide_tac >>
    metis_tac[leibniz_col_arm_1, leibniz_seg_arm_1, ONE, leibniz_wriggle_refl],
    rpt strip_tac >>
    `n <= a + 1 - b` by decide_tac >>
    Cases_on `a + 1 = b` >| [
      `n = 0` by decide_tac >>
      metis_tac[leibniz_col_arm_1, leibniz_seg_arm_1, ONE, leibniz_wriggle_refl],
      `b <= a` by decide_tac >>
      qabbrev_tac `x = leibniz (a + 1) b` >>
      `leibniz_col_arm (a + 1) b (n + 1) = [x] ++ (leibniz_col_arm a b n)` by rw[leibniz_col_arm_cons, Abbr`x`] >>
      `([x] ++ (leibniz_col_arm a b n)) wriggle ([x] ++ (leibniz_seg_arm a b n))` by rw[leibniz_wriggle_tail] >>
      `([x] ++ (leibniz_seg_arm a b n)) wriggle (leibniz_seg_arm (a + 1) b (n + 1))` by rw[leibniz_seg_arm_wriggle_row_arm, Abbr`x`] >>
      metis_tac[leibniz_wriggle_trans, ADD1]
    ]
  ]);

(* Theorem: b <= a /\ n <= a + 1 - b ==> (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n)) *)
(* Proof:
   Since (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n)   by leibniz_col_arm_wriggle_row_arm
     the result follows                                            by list_lcm_wriggle
*)
val leibniz_lcm_invariance = store_thm(
  "leibniz_lcm_invariance",
  ``!a b n. b <= a /\ n <= a + 1 - b ==> (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n))``,
  rw[leibniz_col_arm_wriggle_row_arm, list_lcm_wriggle]);

(* This is a milestone theorem. *)

(* This is used to give another proof of leibniz_up_wriggle_horizontal *)

(* Theorem: leibniz_col_arm n 0 (n + 1) = leibniz_up n *)
(* Proof:
     leibniz_col_arm n 0 (n + 1)
   = MAP (\x. leibniz (n - x) 0) [0 ..< (n + 1)]      by notation
   = MAP (\x. leibniz (n - x) 0) [0 .. n]             by listRangeLHI_to_INC
   = MAP ((\x. leibniz x 0) o (\x. n - x)) [0 .. n]   by function composition
   = REVERSE (MAP (\x. leibniz x 0) [0 .. n])         by listRangeINC_REVERSE_MAP
   = REVERSE (MAP (\x. x + 1) [0 .. n])               by leibniz_n_0
   = REVERSE (MAP SUC [0 .. n])                       by ADD1
   = REVERSE (MAP (I o SUC) [0 .. n])                 by I_THM
   = REVERSE [1 .. (n+1)]                             by listRangeINC_MAP_SUC
   = REVERSE (leibniz_vertical n)                     by notation
   = leibniz_up n                                     by notation
*)
val leibniz_col_arm_n_0 = store_thm(
  "leibniz_col_arm_n_0",
  ``!n. leibniz_col_arm n 0 (n + 1) = leibniz_up n``,
  rpt strip_tac >>
  `(\x. x + 1) = SUC` by rw[FUN_EQ_THM] >>
  `(\x. leibniz x 0) o (\x. n - x + 0) = (\x. leibniz (n - x) 0)` by rw[FUN_EQ_THM] >>
  `leibniz_col_arm n 0 (n + 1) = MAP (\x. leibniz (n - x) 0) [0 .. n]` by rw[listRangeLHI_to_INC] >>
  `_ = MAP ((\x. leibniz x 0) o (\x. n - x + 0)) [0 .. n]` by rw[] >>
  `_ = REVERSE (MAP (\x. leibniz x 0) [0 .. n])` by rw[listRangeINC_REVERSE_MAP] >>
  `_ = REVERSE (MAP (\x. x + 1) [0 .. n])` by rw[leibniz_n_0] >>
  `_ = REVERSE (MAP SUC [0 .. n])` by rw[ADD1] >>
  `_ = REVERSE (MAP (I o SUC) [0 .. n])` by rw[] >>
  `_ = REVERSE [1 .. (n+1)]` by rw[GSYM listRangeINC_MAP_SUC] >>
  rw[]);

(* Theorem: leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n *)
(* Proof:
     leibniz_seg_arm n 0 (n + 1)
   = MAP (\x. leibniz n x) [0 ..< (n + 1)]       by notation
   = MAP (\x. leibniz n x) [0 .. n]              by listRangeLHI_to_INC
   = MAP (leibniz n) [0 .. n]                    by FUN_EQ_THM
   = MAP (leibniz n) (GENLIST (\i. i) (n + 1))   by listRangeINC_def
   = GENLIST ((leibniz n) o I) (n + 1)           by MAP_GENLIST
   = GENLIST (leibniz n) (n + 1)                 by I_THM
   = leibniz_horizontal n                        by notation
*)
val leibniz_seg_arm_n_0 = store_thm(
  "leibniz_seg_arm_n_0",
  ``!n. leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n``,
  rpt strip_tac >>
  `(\x. x) = I` by rw[FUN_EQ_THM] >>
  `(\x. leibniz n x) = leibniz n` by rw[FUN_EQ_THM] >>
  `leibniz_seg_arm n 0 (n + 1) = MAP (leibniz n) [0 .. n]` by rw_tac std_ss[listRangeLHI_to_INC] >>
  `_ = MAP (leibniz n) (GENLIST (\i. i) (n + 1))` by rw[listRangeINC_def] >>
  `_ = MAP (leibniz n) (GENLIST I (n + 1))` by metis_tac[] >>
  `_ = GENLIST ((leibniz n) o I) (n + 1)` by rw[MAP_GENLIST] >>
  `_ = GENLIST (leibniz n) (n + 1)` by rw[] >>
  rw[]);

(* Theorem: (leibniz_up n) wriggle (leibniz_horizontal n) *)
(* Proof:
   Note 0 <= n /\ n + 1 <= n + 1 - 0, so leibniz_col_arm_wriggle_row_arm applies.
     leibniz_up n
   = leibniz_col_arm n 0 (n + 1)         by leibniz_col_arm_n_0
   wriggle leibniz_seg_arm n 0 (n + 1)   by leibniz_col_arm_wriggle_row_arm
   = leibniz_horizontal n                by leibniz_seg_arm_n_0
*)
val leibniz_up_wriggle_horizontal_alt = store_thm(
  "leibniz_up_wriggle_horizontal_alt",
  ``!n. (leibniz_up n) wriggle (leibniz_horizontal n)``,
  rpt strip_tac >>
  `0 <= n /\ n + 1 <= n + 1 - 0` by decide_tac >>
  metis_tac[leibniz_col_arm_wriggle_row_arm, leibniz_col_arm_n_0, leibniz_seg_arm_n_0]);

(* Theorem: list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n) *)
(* Proof: by leibniz_up_wriggle_horizontal_alt, list_lcm_wriggle *)
val leibniz_up_lcm_eq_horizontal_lcm = store_thm(
  "leibniz_up_lcm_eq_horizontal_lcm",
  ``!n. list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n)``,
  rw[leibniz_up_wriggle_horizontal_alt, list_lcm_wriggle]);

(* This is another proof of the milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Set GCD as Big Operator                                                   *)
(* ------------------------------------------------------------------------- *)

(* Big Operators:
SUM_IMAGE_DEF   |- !f s. SIGMA f s = ITSET (\e acc. f e + acc) s 0: thm
PROD_IMAGE_DEF  |- !f s. PI f s = ITSET (\e acc. f e * acc) s 1: thm
*)

(* Define big_gcd for a set *)
val big_gcd_def = Define`
    big_gcd s = ITSET gcd s 0
`;

(* Theorem: big_gcd {} = 0 *)
(* Proof:
     big_gcd {}
   = ITSET gcd {} 0    by big_gcd_def
   = 0                 by ITSET_EMPTY
*)
val big_gcd_empty = store_thm(
  "big_gcd_empty",
  ``big_gcd {} = 0``,
  rw[big_gcd_def, ITSET_EMPTY]);

(* Theorem: big_gcd {x} = x *)
(* Proof:
     big_gcd {x}
   = ITSET gcd {x} 0    by big_gcd_def
   = gcd x 0            by ITSET_SING
   = x                  by GCD_0R
*)
val big_gcd_sing = store_thm(
  "big_gcd_sing",
  ``!x. big_gcd {x} = x``,
  rw[big_gcd_def, ITSET_SING]);

(* Theorem: FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s)) *)
(* Proof:
   Note big_gcd s = ITSET gcd s 0                   by big_lcm_def
   Since !x y z. gcd x (gcd y z) = gcd y (gcd x z)  by GCD_ASSOC_COMM
   The result follows                               by ITSET_REDUCTION
*)
val big_gcd_reduction = store_thm(
  "big_gcd_reduction",
  ``!s x. FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s))``,
  rw[big_gcd_def, ITSET_REDUCTION, GCD_ASSOC_COMM]);

(* Theorem: FINITE s ==> !x. x IN s ==> (big_gcd s) divides x *)
(* Proof:
   By finite induction on s.
   Base: x IN {} ==> big_gcd {} divides x
      True since x IN {} = F                           by MEMBER_NOT_EMPTY
   Step: !x. x IN s ==> big_gcd s divides x ==>
         e NOTIN s /\ x IN (e INSERT s) ==> big_gcd (e INSERT s) divides x
      Since e NOTIN s,
         so big_gcd (e INSERT s) = gcd e (big_gcd s)   by big_gcd_reduction
      By IN_INSERT,
      If x = e,
         to show: gcd e (big_gcd s) divides e, true    by GCD_IS_GREATEST_COMMON_DIVISOR
      If x <> e, x IN s,
         to show gcd e (big_gcd s) divides x,
         Since (big_gcd s) divides x                   by induction hypothesis, x IN s
           and (big_gcd s) divides gcd e (big_gcd s)   by GCD_IS_GREATEST_COMMON_DIVISOR
            so gcd e (big_gcd s) divides x             by DIVIDES_TRANS
*)
val big_gcd_is_common_divisor = store_thm(
  "big_gcd_is_common_divisor",
  ``!s. FINITE s ==> !x. x IN s ==> (big_gcd s) divides x``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[big_gcd_reduction, IN_INSERT, GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_TRANS]);

(* Theorem: FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides (big_gcd s) *)
(* Proof:
   By finite induction on s.
   Base: m divides big_gcd {}
      Since big_gcd {} = 0                        by big_gcd_empty
      Hence true                                  by ALL_DIVIDES_0
   Step: !m. (!x. x IN s ==> m divides x) ==> m divides big_gcd s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> m divides x ==> m divides big_gcd (e INSERT s)
      Note x IN e INSERT s ==> x = e \/ x IN s    by IN_INSERT
      Put x = e, then m divides e                 by x divides m, x = e
      Put x IN s, then m divides big_gcd s        by induction hypothesis
      Therefore, m divides gcd e (big_gcd s)      by GCD_IS_GREATEST_COMMON_DIVISOR
             or  m divides big_gcd (e INSERT s)   by big_gcd_reduction, e NOTIN s
*)
val big_gcd_is_greatest_common_divisor = store_thm(
  "big_gcd_is_greatest_common_divisor",
  ``!s. FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides (big_gcd s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_gcd_empty] >>
  metis_tac[big_gcd_reduction, GCD_IS_GREATEST_COMMON_DIVISOR, IN_INSERT]);

(* Theorem: FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s) *)
(* Proof:
   If x IN s,
      Then (big_gcd s) divides x          by big_gcd_is_common_divisor
           gcd x (big_gcd s)
         = gcd (big_gcd s) x              by GCD_SYM
         = big_gcd s                      by divides_iff_gcd_fix
         = big_gcd (x INSERT s)           by ABSORPTION
   If x NOTIN s, result is true           by big_gcd_reduction
*)
val big_gcd_insert = store_thm(
  "big_gcd_insert",
  ``!s. FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s)``,
  rpt strip_tac >>
  Cases_on `x IN s` >-
  metis_tac[big_gcd_is_common_divisor, divides_iff_gcd_fix, ABSORPTION, GCD_SYM] >>
  rw[big_gcd_reduction]);

(* Theorem: big_gcd {x; y} = gcd x y *)
(* Proof:
     big_gcd {x; y}
   = big_gcd (x INSERT y)          by notation
   = gcd x (big_gcd {y})           by big_gcd_insert
   = gcd x (big_gcd {y INSERT {}}) by notation
   = gcd x (gcd y (big_gcd {}))    by big_gcd_insert
   = gcd x (gcd y 0)               by big_gcd_empty
   = gcd x y                       by gcd_0R
*)
val big_gcd_two = store_thm(
  "big_gcd_two",
  ``!x y. big_gcd {x; y} = gcd x y``,
  rw[big_gcd_insert, big_gcd_empty]);

(* Theorem: FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} /\ !x. x IN {} ==> 0 < x ==> 0 < big_gcd {}
      True since {} <> {} = F
   Step: s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s ==>
         e NOTIN s /\ e INSERT s <> {} /\ !x. x IN e INSERT s ==> 0 < x ==> 0 < big_gcd (e INSERT s)
      Note 0 < e /\ !x. x IN s ==> 0 < x   by IN_INSERT
      If s = {},
           big_gcd (e INSERT {})
         = big_gcd {e}                     by IN_INSERT
         = e > 0                           by big_gcd_sing
      If s <> {},
        so 0 < big_gcd s                   by induction hypothesis
       ==> 0 < gcd e (big_gcd s)           by GCD_EQ_0
        or 0 < big_gcd (e INSERT s)        by big_gcd_insert
*)
val big_gcd_positive = store_thm(
  "big_gcd_positive",
  ``!s. FINITE s /\ s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s``,
  `!s. FINITE s ==> s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  `0 < e /\ (!x. x IN s ==> 0 < x)` by rw[] >>
  Cases_on `s = {}` >-
  rw[big_gcd_sing] >>
  metis_tac[big_gcd_insert, GCD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} ==> ..., must be true.
   Step: s <> {} ==> !!k. big_gcd (IMAGE ($* k) s) = k * big_gcd s ==>
         e NOTIN s ==> big_gcd (IMAGE ($* k) (e INSERT s)) = k * big_gcd (e INSERT s)
      If s = {},
         big_gcd (IMAGE ($* k) (e INSERT {}))
       = big_gcd (IMAGE ($* k) {e})        by IN_INSERT, s = {}
       = big_gcd {k * e}                   by IMAGE_SING
       = k * e                             by big_gcd_sing
       = k * big_gcd {e}                   by big_gcd_sing
       = k * big_gcd (e INSERT {})         by IN_INSERT, s = {}
     If s <> {},
         big_gcd (IMAGE ($* k) (e INSERT s))
       = big_gcd ((k * e) INSERT (IMAGE ($* k) s))   by IMAGE_INSERT
       = gcd (k * e) (big_gcd (IMAGE ($* k) s))      by big_gcd_insert
       = gcd (k * e) (k * big_gcd s)                 by induction hypothesis
       = k * gcd e (big_gcd s)                       by GCD_COMMON_FACTOR
       = k * big_gcd (e INSERT s)                    by big_gcd_insert
*)
val big_gcd_map_times = store_thm(
  "big_gcd_map_times",
  ``!s. FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s``,
  `!s. FINITE s ==> s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  Cases_on `s = {}` >-
  rw[big_gcd_sing] >>
  `big_gcd (IMAGE ($* k) (e INSERT s)) = gcd (k * e) (k * big_gcd s)` by rw[big_gcd_insert] >>
  `_ = k * gcd e (big_gcd s)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * big_gcd (e INSERT s)` by rw[big_gcd_insert] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Set LCM as Big Operator                                                   *)
(* ------------------------------------------------------------------------- *)

(* big_lcm s = ITSET (\e x. lcm e x) s 1 = ITSET lcm s 1, of course! *)
val big_lcm_def = Define`
    big_lcm s = ITSET lcm s 1
`;

(* Theorem: big_lcm {} = 1 *)
(* Proof:
     big_lcm {}
   = ITSET lcm {} 1     by big_lcm_def
   = 1                  by ITSET_EMPTY
*)
val big_lcm_empty = store_thm(
  "big_lcm_empty",
  ``big_lcm {} = 1``,
  rw[big_lcm_def, ITSET_EMPTY]);

(* Theorem: big_lcm {x} = x *)
(* Proof:
     big_lcm {x}
   = ITSET lcm {x} 1     by big_lcm_def
   = lcm x 1             by ITSET_SING
   = x                   by LCM_1
*)
val big_lcm_sing = store_thm(
  "big_lcm_sing",
  ``!x. big_lcm {x} = x``,
  rw[big_lcm_def, ITSET_SING]);

(* Theorem: FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s)) *)
(* Proof:
   Note big_lcm s = ITSET lcm s 1                   by big_lcm_def
   Since !x y z. lcm x (lcm y z) = lcm y (lcm x z)  by LCM_ASSOC_COMM
   The result follows                               by ITSET_REDUCTION
*)
val big_lcm_reduction = store_thm(
  "big_lcm_reduction",
  ``!s x. FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s))``,
  rw[big_lcm_def, ITSET_REDUCTION, LCM_ASSOC_COMM]);

(* Theorem: FINITE s ==> !x. x IN s ==> x divides (big_lcm s) *)
(* Proof:
   By finite induction on s.
   Base: x IN {} ==> x divides big_lcm {}
      True since x IN {} = F                           by MEMBER_NOT_EMPTY
   Step: !x. x IN s ==> x divides big_lcm s ==>
         e NOTIN s /\ x IN (e INSERT s) ==> x divides big_lcm (e INSERT s)
      Since e NOTIN s,
         so big_lcm (e INSERT s) = lcm e (big_lcm s)   by big_lcm_reduction
      By IN_INSERT,
      If x = e,
         to show: e divides lcm e (big_lcm s), true    by LCM_DIVISORS
      If x <> e, x IN s,
         to show x divides lcm e (big_lcm s),
         Since x divides (big_lcm s)                   by induction hypothesis, x IN s
           and (big_lcm s) divides lcm e (big_lcm s)   by LCM_DIVISORS
            so x divides lcm e (big_lcm s)             by DIVIDES_TRANS
*)
val big_lcm_is_common_multiple = store_thm(
  "big_lcm_is_common_multiple",
  ``!s. FINITE s ==> !x. x IN s ==> x divides (big_lcm s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[big_lcm_reduction, IN_INSERT, LCM_DIVISORS, DIVIDES_TRANS]);

(* Theorem: FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> (big_lcm s) divides m *)
(* Proof:
   By finite induction on s.
   Base: big_lcm {} divides m
      Since big_lcm {} = 1                        by big_lcm_empty
      Hence true                                  by ONE_DIVIDES_ALL
   Step: !m. (!x. x IN s ==> x divides m) ==> big_lcm s divides m ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> x divides m ==> big_lcm (e INSERT s) divides m
      Note x IN e INSERT s ==> x = e \/ x IN s    by IN_INSERT
      Put x = e, then e divides m                 by x divides m, x = e
      Put x IN s, then big_lcm s divides m        by induction hypothesis
      Therefore, lcm e (big_lcm s) divides m      by LCM_IS_LEAST_COMMON_MULTIPLE
             or  big_lcm (e INSERT s) divides m   by big_lcm_reduction, e NOTIN s
*)
val big_lcm_is_least_common_multiple = store_thm(
  "big_lcm_is_least_common_multiple",
  ``!s. FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> (big_lcm s) divides m``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_lcm_empty] >>
  metis_tac[big_lcm_reduction, LCM_IS_LEAST_COMMON_MULTIPLE, IN_INSERT]);

(* Theorem: FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s) *)
(* Proof:
   If x IN s,
      Then x divides (big_lcm s)          by big_lcm_is_common_multiple
           lcm x (big_lcm s)
         = big_lcm s                      by divides_iff_lcm_fix
         = big_lcm (x INSERT s)           by ABSORPTION
   If x NOTIN s, result is true           by big_lcm_reduction
*)
val big_lcm_insert = store_thm(
  "big_lcm_insert",
  ``!s. FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s)``,
  rpt strip_tac >>
  Cases_on `x IN s` >-
  metis_tac[big_lcm_is_common_multiple, divides_iff_lcm_fix, ABSORPTION] >>
  rw[big_lcm_reduction]);

(* Theorem: big_lcm {x; y} = lcm x y *)
(* Proof:
     big_lcm {x; y}
   = big_lcm (x INSERT y)          by notation
   = lcm x (big_lcm {y})           by big_lcm_insert
   = lcm x (big_lcm {y INSERT {}}) by notation
   = lcm x (lcm y (big_lcm {}))    by big_lcm_insert
   = lcm x (lcm y 1)               by big_lcm_empty
   = lcm x y                       by LCM_1
*)
val big_lcm_two = store_thm(
  "big_lcm_two",
  ``!x y. big_lcm {x; y} = lcm x y``,
  rw[big_lcm_insert, big_lcm_empty]);

(* Theorem: FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s *)
(* Proof:
   By finite induction on s.
   Base: !x. x IN {} ==> 0 < x ==> 0 < big_lcm {}
      big_lcm {} = 1 > 0     by big_lcm_empty
   Step: (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> 0 < x ==> 0 < big_lcm (e INSERT s)
      Note 0 < e /\ !x. x IN s ==> 0 < x   by IN_INSERT
        so 0 < big_lcm s                   by induction hypothesis
       ==> 0 < lcm e (big_lcm s)           by LCM_EQ_0
        or 0 < big_lcm (e INSERT s)        by big_lcm_insert
*)
val big_lcm_positive = store_thm(
  "big_lcm_positive",
  ``!s. FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_lcm_empty] >>
  `0 < e /\ (!x. x IN s ==> 0 < x)` by rw[] >>
  metis_tac[big_lcm_insert, LCM_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} ==> ..., must be true.
   Step: s <> {} ==> !!k. big_lcm (IMAGE ($* k) s) = k * big_lcm s ==>
         e NOTIN s ==> big_lcm (IMAGE ($* k) (e INSERT s)) = k * big_lcm (e INSERT s)
      If s = {},
         big_lcm (IMAGE ($* k) (e INSERT {}))
       = big_lcm (IMAGE ($* k) {e})        by IN_INSERT, s = {}
       = big_lcm {k * e}                   by IMAGE_SING
       = k * e                             by big_lcm_sing
       = k * big_lcm {e}                   by big_lcm_sing
       = k * big_lcm (e INSERT {})         by IN_INSERT, s = {}
     If s <> {},
         big_lcm (IMAGE ($* k) (e INSERT s))
       = big_lcm ((k * e) INSERT (IMAGE ($* k) s))   by IMAGE_INSERT
       = lcm (k * e) (big_lcm (IMAGE ($* k) s))      by big_lcm_insert
       = lcm (k * e) (k * big_lcm s)                 by induction hypothesis
       = k * lcm e (big_lcm s)                       by LCM_COMMON_FACTOR
       = k * big_lcm (e INSERT s)                    by big_lcm_insert
*)
val big_lcm_map_times = store_thm(
  "big_lcm_map_times",
  ``!s. FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s``,
  `!s. FINITE s ==> s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  Cases_on `s = {}` >-
  rw[big_lcm_sing] >>
  `big_lcm (IMAGE ($* k) (e INSERT s)) = lcm (k * e) (k * big_lcm s)` by rw[big_lcm_insert] >>
  `_ = k * lcm e (big_lcm s)` by rw[LCM_COMMON_FACTOR] >>
  `_ = k * big_lcm (e INSERT s)` by rw[big_lcm_insert] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* LCM Lower bound using big LCM                                             *)
(* ------------------------------------------------------------------------- *)

(* Laurent's leib.v and leib.html

Lemma leibn_lcm_swap m n :
   lcmn 'L(m.+1, n) 'L(m, n) = lcmn 'L(m.+1, n) 'L(m.+1, n.+1).
Proof.
rewrite ![lcmn 'L(m.+1, n) _]lcmnC.
by apply/lcmn_swap/leibnS.
Qed.

Notation "\lcm_ ( i < n ) F" :=
 (\big[lcmn/1%N]_(i < n ) F%N)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n  ) '/  '  F ']'") : nat_scope.

Canonical Structure lcmn_moid : Monoid.law 1 :=
  Monoid.Law lcmnA lcm1n lcmn1.
Canonical lcmn_comoid := Monoid.ComLaw lcmnC.

Lemma lieb_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) =
                   \lcm_(j < k.+1) 'L(n.+1, i + j).
Proof.
elim: k i => [i|k1 IH i].
  by rewrite big_ord_recr !big_ord0 /= lcmn1 lcm1n addn0.
rewrite big_ord_recl /= addn0.
rewrite lcmnA leibn_lcm_swap.
rewrite (eq_bigr (fun j : 'I_k1 => 'L(n, i.+1 + j))).
rewrite -lcmnA.
rewrite IH.
rewrite [RHS]big_ord_recl.
rewrite addn0; congr (lcmn _ _).
by apply: eq_bigr => j _; rewrite addnS.
move=> j _.
by rewrite addnS.
Qed.

Lemma leib_corner n : \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) 'L(n, i).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord_recr !big_ord0 /=.
rewrite big_ord_recr /= IH lcmnC.
rewrite (eq_bigr (fun i : 'I_n.+1 => 'L(n, 0 + i))) //.
by rewrite lieb_line.
Qed.

Lemma main_result n : 2^n.-1 <= \lcm_(i < n) i.+1.
Proof.
case: n => [|n /=]; first by rewrite big_ord0.
have <-: \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) i.+1.
  by apply: eq_bigr => i _; rewrite leibn0.
rewrite leib_corner.
have -> : forall j,  \lcm_(i < j.+1) 'L(n, i) = n.+1 *  \lcm_(i < j.+1) 'C(n, i).
  elim=> [|j IH]; first by rewrite !big_ord_recr !big_ord0 /= !lcm1n.
  by rewrite big_ord_recr [in RHS]big_ord_recr /= IH muln_lcmr.
rewrite (expnDn 1 1) /=  (eq_bigr (fun i : 'I_n.+1 => 'C(n, i))) =>
       [|i _]; last by rewrite !exp1n !muln1.
have <- : forall n m,  \sum_(i < n) m = n * m.
  by move=> m1 n1; rewrite sum_nat_const card_ord.
apply: leq_sum => i _.
apply: dvdn_leq; last by rewrite (bigD1 i) //= dvdn_lcml.
apply big_ind => // [x y Hx Hy|x H]; first by rewrite lcmn_gt0 Hx.
by rewrite bin_gt0 -ltnS.
Qed.

*)

(*
Lemma lieb_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) = \lcm_(j < k.+1) 'L(n.+1, i + j).

translates to:
      !n i k. lcm (leibniz (n + 1) i) (big_lcm {leibniz n (i + j) | j | j < k}) =
              big_lcm {leibniz (n+1) (i + j) | j | j < k + 1};

The picture is:

    n-th row:  L n i          L n (i+1) ....     L n (i + (k-1))
(n+1)-th row:  L (n+1) i

(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k)

If k = 1, this is:  L n i        transform to:
                    L (n+1) i                   L (n+1) i  L (n+1) (i+1)
which is Leibniz triplet.

In general, if true for k, then for the next (k+1)

    n-th row:  L n i          L n (i+1) ....     L n (i + (k-1))  L n (i + k)
(n+1)-th row:  L (n+1) i
=                                                                 L n (i + k)
(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k)
by induction hypothesis
=
(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k) L (n+1) (i + (k+1))
by Leibniz triplet.

*)

(* Introduce a segment, a partial horizontal row, in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_seg", ``\n k h. IMAGE (\j. leibniz n (k + j)) (count h)``);
(* This is a segment starting at leibniz n k, of length h *)

(* Introduce a horizontal row in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_row", ``\n h. IMAGE (leibniz n) (count h)``);
(* This is a row starting at leibniz n 0, of length h *)

(* Introduce a vertical column in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_col", ``\h. IMAGE (\i. leibniz i 0) (count h)``);
(* This is a column starting at leibniz 0 0, descending for a length h *)

(* Representations of paths based on indexed sets *)

(* Theorem: leibniz_seg n k h = {leibniz n (k + j) | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_seg_def = store_thm(
  "leibniz_seg_def",
  ``!n k h. leibniz_seg n k h = {leibniz n (k + j) | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_row n h = {leibniz n j | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_row_def = store_thm(
  "leibniz_row_def",
  ``!n h. leibniz_row n h = {leibniz n j | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_col h = {leibniz j 0 | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_col_def = store_thm(
  "leibniz_col_def",
  ``!h. leibniz_col h = {leibniz j 0 | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_col n = natural n *)
(* Proof:
     leibniz_col n
   = IMAGE (\i. leibniz i 0) (count n)    by notation
   = IMAGE (\i. i + 1) (count n)          by leibniz_n_0
   = IMAGE (\i. SUC i) (count n)          by ADD1
   = IMAGE SUC (count n)                  by FUN_EQ_THM
   = natural n                            by notation
*)
val leibniz_col_eq_natural = store_thm(
  "leibniz_col_eq_natural",
  ``!n. leibniz_col n = natural n``,
  rw[leibniz_n_0, ADD1, FUN_EQ_THM]);

(* The following can be taken as a generalisation of the Leibniz Triplet LCM exchange. *)
(* When length h = 1, the top row is a singleton, and the next row is a duplet, altogether a triplet. *)

(* Theorem: lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) = big_lcm (leibniz_seg (n + 1) k (h + 1)) *)
(* Proof:
   Let p = (\j. leibniz n (k + j)), q = (\j. leibniz (n + 1) (k + j)).
   Note q 0 = (leibniz (n + 1) k)                   by function application [1]
   The goal is: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count h))) = big_lcm (IMAGE q (count (h + 1)))

   By induction on h, length of the row.
   Base case: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count 0))) = big_lcm (IMAGE q (count (0 + 1)))
           lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count 0)))
         = lcm (q 0) (big_lcm (IMAGE p (count 0)))  by [1]
         = lcm (q 0) (big_lcm (IMAGE p {}))         by COUNT_ZERO
         = lcm (q 0) (big_lcm {})                   by IMAGE_EMPTY
         = lcm (q 0) 1                              by big_lcm_empty
         = q 0                                      by LCM_1
         = big_lcm {q 0}                            by big_lcm_sing
         = big_lcm (IMAEG q {0})                    by IMAGE_SING
         = big_lcm (IMAGE q (count 1))              by count_def, EXTENSION

   Step case: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count h))) = big_lcm (IMAGE q (count (h + 1))) ==>
              lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (upto h))) = big_lcm (IMAGE q (count (SUC h + 1)))
     Note !n. FINITE (count n)                      by FINITE_COUNT
      and !s. FINITE s ==> FINITE (IMAGE f s)       by IMAGE_FINITE
     Also p h = (triplet n (k + h)).a               by leibniz_triplet_member
          q h = (triplet n (k + h)).b               by leibniz_triplet_member
          q (h + 1) = (triplet n (k + h)).c         by leibniz_triplet_member
     Thus lcm (q h) (p h) = lcm (q h) (q (h + 1))   by leibniz_triplet_lcm

       lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (upto h)))
     = lcm (q 0) (big_lcm (IMAGE p (count (SUC h))))              by [1], notation
     = lcm (q 0) (big_lcm (IMAGE p (h INSERT count h)))           by upto_by_count
     = lcm (q 0) (big_lcm ((p h) INSERT (IMAGE p (count h))))     by IMAGE_INSERT
     = lcm (q 0) (lcm (p h) (big_lcm (IMAGE p (count h))))        by big_lcm_insert
     = lcm (p h) (lcm (q 0) (big_lcm (IMAGE p (count h))))        by LCM_ASSOC_COMM
     = lcm (p h) (big_lcm (IMAGE q (count (h + 1))))              by induction hypothesis
     = lcm (p h) (big_lcm (IMAGE q (count (SUC h))))              by ADD1
     = lcm (p h) (big_lcm (IMAGE q (h INSERT (count h)))          by upto_by_count
     = lcm (p h) (big_lcm ((q h) INSERT IMAGE q (count h)))       by IMAGE_INSERT
     = lcm (p h) (lcm (q h) (big_lcm (IMAGE q (count h))))        by big_lcm_insert
     = lcm (lcm (p h) (q h)) (big_lcm (IMAGE q (count h)))        by LCM_ASSOC
     = lcm (lcm (q h) (p h)) (big_lcm (IMAGE q (count h)))        by LCM_COM
     = lcm (lcm (q h) (q (h + 1))) (big_lcm (IMAGE q (count h)))  by leibniz_triplet_lcm
     = lcm (q (h + 1)) (lcm (q h) (big_lcm (IMAGE q (count h))))  by LCM_ASSOC, LCM_COMM
     = lcm (q (h + 1)) (big_lcm ((q h) INSERT IMAGE q (count h))) by big_lcm_insert
     = lcm (q (h + 1)) (big_lcm (IMAGE q (h INSERT count h))      by IMAGE_INSERT
     = lcm (q (h + 1)) (big_lcm (IMAGE q (count (h + 1))))        by upto_by_count, ADD1
     = big_lcm ((q (h + 1)) INSERT (IMAGE q (count (h + 1))))     by big_lcm_insert
     = big_lcm IMAGE q ((h + 1) INSERT (count (h + 1)))           by IMAGE_INSERT
     = big_lcm (IMAGE q (count (SUC (h + 1))))                    by upto_by_count
     = big_lcm (IMAGE q (count (SUC h + 1)))                      by ADD
*)
val big_lcm_seg_transform = store_thm(
  "big_lcm_seg_transform",
  ``!n k h. lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) =
           big_lcm (leibniz_seg (n + 1) k (h + 1))``,
  rpt strip_tac >>
  qabbrev_tac `p = (\j. leibniz n (k + j))` >>
  qabbrev_tac `q = (\j. leibniz (n + 1) (k + j))` >>
  Induct_on `h` >| [
    `count 0 = {}` by rw[] >>
    `count 1 = {0}` by rw[COUNT_1] >>
    rw_tac std_ss[IMAGE_EMPTY, big_lcm_empty, IMAGE_SING, LCM_1, big_lcm_sing, Abbr`p`, Abbr`q`],
    `leibniz (n + 1) k = q 0` by rw[Abbr`q`] >>
    simp[] >>
    `lcm (q h) (p h) = lcm (q h) (q (h + 1))` by
  (`p h = (triplet n (k + h)).a` by rw[leibniz_triplet_member, Abbr`p`] >>
    `q h = (triplet n (k + h)).b` by rw[leibniz_triplet_member, Abbr`q`] >>
    `q (h + 1) = (triplet n (k + h)).c` by rw[leibniz_triplet_member, Abbr`q`] >>
    rw[leibniz_triplet_lcm]) >>
    `lcm (q 0) (big_lcm (IMAGE p (count (SUC h)))) = lcm (q 0) (lcm (p h) (big_lcm (IMAGE p (count h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (p h) (lcm (q 0) (big_lcm (IMAGE p (count h))))` by rw[LCM_ASSOC_COMM] >>
    `_ = lcm (p h) (big_lcm (IMAGE q (count (SUC h))))` by metis_tac[ADD1] >>
    `_ = lcm (p h) (lcm (q h) (big_lcm (IMAGE q (count h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (q (h + 1)) (lcm (q h) (big_lcm (IMAGE q (count h))))` by metis_tac[LCM_ASSOC, LCM_COMM] >>
    `_ = lcm (q (h + 1)) (big_lcm (IMAGE q (count (SUC h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (q (h + 1)) (big_lcm (IMAGE q (count (h + 1))))` by rw[ADD1] >>
    `_ = big_lcm (IMAGE q (count (SUC (h + 1))))` by rw[upto_by_count, big_lcm_insert] >>
    metis_tac[ADD]
  ]);

(* Theorem: lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) = big_lcm (leibniz_row (n + 1) (h + 1)) *)
(* Proof:
   Note !n h. leibniz_row n h = leibniz_seg n 0 h   by FUN_EQ_THM
   Take k = 0 in big_lcm_seg_transform, the result follows.
*)
val big_lcm_row_transform = store_thm(
  "big_lcm_row_transform",
  ``!n h. lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) = big_lcm (leibniz_row (n + 1) (h + 1))``,
  rpt strip_tac >>
  `!n h. leibniz_row n h = leibniz_seg n 0 h` by rw[FUN_EQ_THM] >>
  metis_tac[big_lcm_seg_transform]);

(* Theorem: big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1)) *)
(* Proof:
   Let f = \i. leibniz i 0, then f 0 = leibniz 0 0.
   By induction on n.
   Base: big_lcm (leibniz_col (0 + 1)) = big_lcm (leibniz_row 0 (0 + 1))
         big_lcm (leibniz_col (0 + 1))
       = big_lcm (IMAGE f (count 1))              by notation
       = big_lcm (IMAGE f) {0})                   by COUNT_1
       = big_lcm {f 0}                            by IMAGE_SING
       = big_lcm {leibniz 0 0}                    by f 0
       = big_lcm (IMAGE (leibniz 0) {0})          by IMAGE_SING
       = big_lcm (IMAGE (leibniz 0) (count 1))    by COUNT_1

   Step: big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1)) ==>
         big_lcm (leibniz_col (SUC n + 1)) = big_lcm (leibniz_row (SUC n) (SUC n + 1))
         big_lcm (leibniz_col (SUC n + 1))
       = big_lcm (IMAGE f (count (SUC n + 1)))                             by notation
       = big_lcm (IMAGE f (count (SUC (n + 1))))                           by ADD
       = big_lcm (IMAGE f ((n + 1) INSERT (count (n + 1))))                by upto_by_count
       = big_lcm ((f (n + 1)) INSERT (IMAGE f (count (n + 1))))            by IMAGE_INSERT
       = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))               by big_lcm_insert
       = lcm (f (n + 1)) (big_lcm (IMAGE (leibniz n) (count (n + 1))))     by induction hypothesis
       = lcm (leibniz (n + 1) 0) (big_lcm (IMAGE (leibniz n) (count (n + 1))))  by f (n + 1)
       = big_lcm (IMAGE (leibniz (n + 1)) (count (n + 1 + 1)))             by big_lcm_line_transform
       = big_lcm (IMAGE (leibniz (SUC n)) (count (SUC n + 1)))             by ADD1
*)
val big_lcm_corner_transform = store_thm(
  "big_lcm_corner_transform",
  ``!n. big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1))``,
  Induct >-
  rw[COUNT_1, IMAGE_SING] >>
  qabbrev_tac `f = \i. leibniz i 0` >>
  `big_lcm (IMAGE f (count (SUC n + 1))) = big_lcm (IMAGE f (count (SUC (n + 1))))` by rw[ADD] >>
  `_ = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[upto_by_count, big_lcm_insert] >>
  `_ = lcm (leibniz (n + 1) 0) (big_lcm (IMAGE (leibniz n) (count (n + 1))))` by rw[Abbr`f`] >>
  `_ = big_lcm (IMAGE (leibniz (n + 1)) (count (n + 1 + 1)))` by rw[big_lcm_row_transform] >>
  `_ = big_lcm (IMAGE (leibniz (SUC n)) (count (SUC n + 1)))` by rw[ADD1] >>
  rw[]);

(* Theorem: (!x. x IN (count (n + 1)) ==> 0 < f x) ==>
            SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1))) *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST f (0 + 1)) <= (0 + 1) * big_lcm (IMAGE f (count (0 + 1)))
      LHS = SUM (GENLIST f 1)
          = SUM [f 0]                 by GENLIST_1
          = f 0                       by SUM
      RHS = 1 * big_lcm (IMAGE f (count 1))
          = big_lcm (IMAGE f {0})     by COUNT_1
          = big_lcm (f 0)             by IMAGE_SING
          = f 0                       by big_lcm_sing
      Thus LHS <= RHS                 by arithmetic
   Step: SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1))) ==>
         SUM (GENLIST f (SUC n + 1)) <= (SUC n + 1) * big_lcm (IMAGE f (count (SUC n + 1)))
      Note 0 < f (n + 1)                                by (n + 1) IN count (SUC n + 1)
       and !y. y IN count (n + 1) ==> y IN count (SUC n + 1)  by IN_COUNT
       and !x. x IN IMAGE f (count (n + 1)) ==> 0 < x   by IN_IMAGE, above
        so 0 < big_lcm (IMAGE f (count (n + 1)))        by big_lcm_positive
       and 0 < SUC n                                    by SUC_POS
      Thus f (n + 1) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))  by LCM_LE
       and big_lcm (IMAGE f (count (n + 1))) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))  by LCM_LE

      LHS = SUM (GENLIST f (SUC n + 1))
          = SUM (GENLIST f (SUC (n + 1)))                         by ADD
          = SUM (SNOC (f (n + 1)) (GENLIST f (n + 1)))            by GENLIST
          = SUM (GENLIST f (n + 1)) + f (n + 1)                   by SUM_SNOC
      RHS = (SUC n + 1) * big_lcm (IMAGE f (count (SUC n + 1)))
          = (SUC n + 1) * big_lcm (IMAGE f (count (SUC (n + 1)))) by ADD
          = (SUC n + 1) * big_lcm (IMAGE f ((n + 1) INSERT (count (n + 1))))      by upto_by_count
          = (SUC n + 1) * big_lcm ((f (n + 1)) INSERT (IMAGE f (count (n + 1))))  by IMAGE_INSERT
          = (SUC n + 1) * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))     by big_lcm_insert
          = SUC n * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))
            +    1 * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))    by RIGHT_ADD_DISTRIB
          >= SUC n * (big_lcm (IMAGE f (count (n + 1))))  + f (n + 1)       by LCM_LE
           = (n + 1) * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1)      by ADD1
          >= SUM (GENLIST f (n + 1)) + f (n + 1)                            by induction hypothesis
           = LHS                                                            by above
*)
val big_lcm_count_lower_bound = store_thm(
  "big_lcm_count_lower_bound",
  ``!f n. (!x. x IN (count (n + 1)) ==> 0 < f x) ==>
    SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1)))``,
  rpt strip_tac >>
  Induct_on `n` >| [
    rpt strip_tac >>
    `SUM (GENLIST f 1) = f 0` by rw[] >>
    `1 * big_lcm (IMAGE f (count 1)) = f 0` by rw[COUNT_1, big_lcm_sing] >>
    rw[],
    rpt strip_tac >>
    `big_lcm (IMAGE f (count (SUC n + 1))) = big_lcm (IMAGE f (count (SUC (n + 1))))` by rw[ADD] >>
    `_ = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[upto_by_count, big_lcm_insert] >>
    `!x. (SUC n + 1) * x = SUC n * x + x` by rw[] >>
    `0 < f (n + 1)` by rw[] >>
    `!y. y IN count (n + 1) ==> y IN count (SUC n + 1)` by rw[] >>
    `!x. x IN IMAGE f (count (n + 1)) ==> 0 < x` by metis_tac[IN_IMAGE] >>
    `0 < big_lcm (IMAGE f (count (n + 1)))` by rw[big_lcm_positive] >>
    `0 < SUC n` by rw[] >>
    `f (n + 1) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[LCM_LE] >>
    `big_lcm (IMAGE f (count (n + 1))) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[LCM_LE] >>
    `!a b c x. 0 < a /\ 0 < b /\ 0 < c /\ a <= x /\ b <= x ==> c * a + b <= c * x + x` by
  (rpt strip_tac >>
    `c * a <= c * x` by rw[] >>
    decide_tac) >>
    `SUC n * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1) <= (SUC n + 1) * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by metis_tac[] >>
    `SUC n * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1) = (n + 1) * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1)` by rw[ADD1] >>
    `SUM (GENLIST f (SUC n + 1)) = SUM (GENLIST f (SUC (n + 1)))` by rw[ADD] >>
    `_ = SUM (GENLIST f (n + 1)) + f (n + 1)` by rw[GENLIST, SUM_SNOC] >>
    metis_tac[LESS_EQ_TRANS, DECIDE``!a x y. 0 < a /\ x <= y ==> x + a <= y + a``]
  ]);

(* Theorem: big_lcm (natural (n + 1)) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1))) *)
(* Proof:
   Note SUC = \i. i + 1                                      by ADD1, FUN_EQ_THM
            = \i. leibniz i 0                                by leibniz_n_0
    and leibniz n = \j. (n + 1) * binomial n j               by leibniz_def, FUN_EQ_THM
     so !s. IMAGE SUC s = IMAGE (\i. leibniz i 0) s          by IMAGE_CONG
    and !s. IMAGE (leibniz n) s = IMAGE (\j. (n + 1) * binomial n j) s   by IMAGE_CONG
   also !s. IMAGE (binomial n) s = IMAGE (\j. binomial n j) s            by FUN_EQ_THM, IMAGE_CONG
    and count (n + 1) <> {}                                  by COUNT_EQ_EMPTY, n + 1 <> 0 [1]

     big_lcm (IMAGE SUC (count (n + 1)))
   = big_lcm (IMAGE (\i. leibniz i 0) (count (n + 1)))       by above
   = big_lcm (IMAGE (leibniz n) (count (n + 1)))             by big_lcm_corner_transform
   = big_lcm (IMAGE (\j. (n + 1) * binomial n j) (count (n + 1)))       by leibniz_def
   = big_lcm (IMAGE ($* (n + 1)) (IMAGE (binomial n) (count (n + 1))))  by IMAGE_COMPOSE, o_DEF
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))  by big_lcm_map_times, FINITE_COUNT, [1]
*)
val big_lcm_natural_eqn = store_thm(
  "big_lcm_natural_eqn",
  ``!n. big_lcm (natural (n + 1)) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))``,
  rpt strip_tac >>
  `SUC = \i. leibniz i 0` by rw[leibniz_n_0, FUN_EQ_THM] >>
  `leibniz n = \j. (n + 1) * binomial n j` by rw[leibniz_def, FUN_EQ_THM] >>
  `!s. IMAGE SUC s = IMAGE (\i. leibniz i 0) s` by rw[IMAGE_CONG] >>
  `!s. IMAGE (leibniz n) s = IMAGE (\j. (n + 1) * binomial n j) s` by rw[IMAGE_CONG] >>
  `!s. IMAGE (binomial n) s = IMAGE (\j. binomial n j) s` by rw[FUN_EQ_THM, IMAGE_CONG] >>
  `count (n + 1) <> {}` by rw[COUNT_EQ_EMPTY] >>
  `big_lcm (IMAGE SUC (count (n + 1))) = big_lcm (IMAGE (leibniz n) (count (n + 1)))` by rw[GSYM big_lcm_corner_transform] >>
  `_ = big_lcm (IMAGE (\j. (n + 1) * binomial n j) (count (n + 1)))` by rw[] >>
  `_ = big_lcm (IMAGE ($* (n + 1)) (IMAGE (binomial n) (count (n + 1))))` by rw[GSYM IMAGE_COMPOSE, combinTheory.o_DEF] >>
  `_ = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))` by rw[big_lcm_map_times] >>
  rw[]);

(* Theorem: 2 ** n <= big_lcm (natural (n + 1)) *)
(* Proof:
   Note !x. x IN (count (n + 1)) ==> 0 < (binomial n) x      by binomial_pos, IN_COUNT [1]
     big_lcm (natural (n + 1))
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))  by big_lcm_natural_eqn
   >= SUM (GENLIST (binomial n) (n + 1))                     by big_lcm_count_lower_bound, [1]
   = SUM (GENLIST (binomial n) (SUC n))                      by ADD1
   = 2 ** n                                                  by binomial_sum
*)
val big_lcm_lower_bound = store_thm(
  "big_lcm_lower_bound",
  ``!n. 2 ** n <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `!x. x IN (count (n + 1)) ==> 0 < (binomial n) x` by rw[binomial_pos] >>
  `big_lcm (IMAGE SUC (count (n + 1))) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))` by rw[big_lcm_natural_eqn] >>
  `SUM (GENLIST (binomial n) (n + 1)) = 2 ** n` by rw[GSYM binomial_sum, ADD1] >>
  metis_tac[big_lcm_count_lower_bound]);

(* Another proof of the milestone theorem. *)

(* Theorem: big_lcm (set l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: big_lcm (set []) = list_lcm []
       big_lcm (set [])
     = big_lcm {}        by LIST_TO_SET
     = 1                 by big_lcm_empty
     = list_lcm []       by list_lcm_nil
   Step: big_lcm (set l) = list_lcm l ==> !h. big_lcm (set (h::l)) = list_lcm (h::l)
     Note FINITE (set l)            by FINITE_LIST_TO_SET
       big_lcm (set (h::l))
     = big_lcm (h INSERT set l)     by LIST_TO_SET
     = lcm h (big_lcm (set l))      by big_lcm_insert, FINITE (set t)
     = lcm h (list_lcm l)           by induction hypothesis
     = list_lcm (h::l)              by list_lcm_cons
*)
val big_lcm_eq_list_lcm = store_thm(
  "big_lcm_eq_list_lcm",
  ``!l. big_lcm (set l) = list_lcm l``,
  Induct >-
  rw[big_lcm_empty] >>
  rw[big_lcm_insert]);

(* ------------------------------------------------------------------------- *)
(* List LCM depends only on its set of elements                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x l ==> (list_lcm (x::l) = list_lcm l) *)
(* Proof:
   By induction on l.
   Base: MEM x [] ==> (list_lcm [x] = list_lcm [])
      True by MEM x [] = F                         by MEM
   Step: MEM x l ==> (list_lcm (x::l) = list_lcm l) ==>
         !h. MEM x (h::l) ==> (list_lcm (x::h::l) = list_lcm (h::l))
      Note MEM x (h::l) ==> (x = h) \/ (MEM x l)   by MEM
      If x = h,
         list_lcm (h::h::l)
       = lcm h (lcm h (list_lcm l))   by list_lcm_cons
       = lcm (lcm h h) (list_lcm l)   by LCM_ASSOC
       = lcm h (list_lcm l)           by LCM_REF
       = list_lcm (h::l)              by list_lcm_cons
      If x <> h, MEM x l
         list_lcm (x::h::l)
       = lcm x (lcm h (list_lcm l))   by list_lcm_cons
       = lcm h (lcm x (list_lcm l))   by LCM_ASSOC_COMM
       = lcm h (list_lcm (x::l))      by list_lcm_cons
       = lcm h (list_lcm l)           by induction hypothesis, MEM x l
       = list_lcm (h::l)              by list_lcm_cons
*)
val list_lcm_absorption = store_thm(
  "list_lcm_absorption",
  ``!x l. MEM x l ==> (list_lcm (x::l) = list_lcm l)``,
  rpt strip_tac >>
  Induct_on `l` >-
  metis_tac[MEM] >>
  rw[MEM] >| [
    `lcm h (lcm h (list_lcm l)) = lcm (lcm h h) (list_lcm l)` by rw[LCM_ASSOC] >>
    rw[LCM_REF],
    `lcm x (lcm h (list_lcm l)) = lcm h (lcm x (list_lcm l))` by rw[LCM_ASSOC_COMM] >>
    `_  = lcm h (list_lcm (x::l))` by metis_tac[list_lcm_cons] >>
    rw[]
  ]);

(* Theorem: list_lcm (nub l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: list_lcm (nub []) = list_lcm []
      True since nub [] = []         by nub_nil
   Step: list_lcm (nub l) = list_lcm l ==> !h. list_lcm (nub (h::l)) = list_lcm (h::l)
      If MEM h l,
           list_lcm (nub (h::l))
         = list_lcm (nub l)         by nub_cons, MEM h l
         = list_lcm l               by induction hypothesis
         = list_lcm (h::l)          by list_lcm_absorption, MEM h l
      If ~(MEM h l),
           list_lcm (nub (h::l))
         = list_lcm (h::nub l)      by nub_cons, ~(MEM h l)
         = lcm h (list_lcm (nub l)) by list_lcm_cons
         = lcm h (list_lcm l)       by induction hypothesis
         = list_lcm (h::l)          by list_lcm_cons
*)
val list_lcm_nub = store_thm(
  "list_lcm_nub",
  ``!l. list_lcm (nub l) = list_lcm l``,
  Induct >-
  rw[nub_nil] >>
  metis_tac[nub_cons, list_lcm_cons, list_lcm_absorption]);

(* Theorem: (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2)) *)
(* Proof:
   By induction on l1.
   Base: !l2. (set [] = set l2) ==> (list_lcm (nub []) = list_lcm (nub l2))
        Note set [] = set l2 ==> l2 = []    by LIST_TO_SET_EQ_EMPTY
        Hence true.
   Step: !l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2)) ==>
         !h l2. (set (h::l1) = set l2) ==> (list_lcm (nub (h::l1)) = list_lcm (nub l2))
        If MEM h l1,
          Then h IN (set l1)            by notation
                set (h::l1)
              = h INSERT set l1         by LIST_TO_SET
              = set l1                  by ABSORPTION_RWT
           Thus set l1 = set l2,
             so list_lcm (nub (h::l1))
              = list_lcm (nub l1)       by nub_cons, MEM h l1
              = list_lcm (nub l2)       by induction hypothesis, set l1 = set l2

        If ~(MEM h l1),
          Then set (h::l1) = set l2
           ==> ?p1 p2. nub l2 = p1 ++ [h] ++ p2
                  and  set l1 = set (p1 ++ p2)            by LIST_TO_SET_REDUCTION

                list_lcm (nub (h::l1))
              = list_lcm (h::nub l1)                      by nub_cons, ~(MEM h l1)
              = lcm h (list_lcm (nub l1))                 by list_lcm_cons
              = lcm h (list_lcm (nub (p1 ++ p2)))         by induction hypothesis
              = lcm h (list_lcm (p1 ++ p2))               by list_lcm_nub
              = lcm h (lcm (list_lcm p1) (list_lcm p2))   by list_lcm_append
              = lcm (list_lcm p1) (lcm h (list_lcm p2))   by LCM_ASSOC_COMM
              = lcm (list_lcm p1) (list_lcm (h::p2))      by list_lcm_append
              = lcm (list_lcm p1) (list_lcm ([h] ++ p2))  by CONS_APPEND
              = list_lcm (p1 ++ ([h] ++ p2))              by list_lcm_append
              = list_lcm (p1 ++ [h] ++ p2)                by APPEND_ASSOC
              = list_lcm (nub l2)                         by above
*)
val list_lcm_nub_eq_if_set_eq = store_thm(
  "list_lcm_nub_eq_if_set_eq",
  ``!l1 l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2))``,
  Induct >-
  rw[LIST_TO_SET_EQ_EMPTY] >>
  rpt strip_tac >>
  Cases_on `MEM h l1` >-
  metis_tac[LIST_TO_SET, ABSORPTION_RWT, nub_cons] >>
  `?p1 p2. (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))` by metis_tac[LIST_TO_SET_REDUCTION] >>
  `list_lcm (nub (h::l1)) = list_lcm (h::nub l1)` by rw[nub_cons] >>
  `_ = lcm h (list_lcm (nub l1))` by rw[list_lcm_cons] >>
  `_ = lcm h (list_lcm (nub (p1 ++ p2)))` by metis_tac[] >>
  `_ = lcm h (list_lcm (p1 ++ p2))` by rw[list_lcm_nub] >>
  `_ = lcm h (lcm (list_lcm p1) (list_lcm p2))` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm p1) (lcm h (list_lcm p2))` by rw[LCM_ASSOC_COMM] >>
  `_ = lcm (list_lcm p1) (list_lcm ([h] ++ p2))` by rw[list_lcm_cons] >>
  metis_tac[list_lcm_append, APPEND_ASSOC]);

(* Theorem: (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2) *)
(* Proof:
      set l1 = set l2
   ==> list_lcm (nub l1) = list_lcm (nub l2)   by list_lcm_nub_eq_if_set_eq
   ==>       list_lcm l1 = list_lcm l2         by list_lcm_nub
*)
val list_lcm_eq_if_set_eq = store_thm(
  "list_lcm_eq_if_set_eq",
  ``!l1 l2. (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2)``,
  metis_tac[list_lcm_nub_eq_if_set_eq, list_lcm_nub]);

(* ------------------------------------------------------------------------- *)
(* Set LCM by List LCM                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of a set *)
(* none works!
val set_lcm_def = Define`
   (set_lcm {} = 1) /\
   !s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm (s DELETE x))
`;
val set_lcm_def = Define`
   (set_lcm {} = 1) /\
   (!s. FINITE s ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s))))
`;
val set_lcm_def = Define`
   set_lcm s = if s = {} then 1 else lcm (CHOICE s) (set_lcm (REST s))
`;
*)
val set_lcm_def = Define`
    set_lcm s = list_lcm (SET_TO_LIST s)
`;

(* Theorem: set_lcm {} = 1 *)
(* Proof:
     set_lcm {}
   = lcm_list (SET_TO_LIST {})   by set_lcm_def
   = lcm_list []                 by SET_TO_LIST_EMPTY
   = 1                           by list_lcm_nil
*)
val set_lcm_empty = store_thm(
  "set_lcm_empty",
  ``set_lcm {} = 1``,
  rw[set_lcm_def]);

(* Theorem: FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s))) *)
(* Proof:
     set_lcm s
   = list_lcm (SET_TO_LIST s)                         by set_lcm_def
   = list_lcm (CHOICE s::SET_TO_LIST (REST s))        by SET_TO_LIST_THM
   = lcm (CHOICE s) (list_lcm (SET_TO_LIST (REST s))) by list_lcm_cons
   = lcm (CHOICE s) (set_lcm (REST s))                by set_lcm_def
*)
val set_lcm_nonempty = store_thm(
  "set_lcm_nonempty",
  ``!s. FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s)))``,
  rw[set_lcm_def, SET_TO_LIST_THM, list_lcm_cons]);

(* Theorem: set_lcm {x} = x *)
(* Proof:
     set_lcm {x}
   = list_lcm (SET_TO_LIST {x})    by set_lcm_def
   = list_lcm [x]                  by SET_TO_LIST_SING
   = x                             by list_lcm_sing
*)
val set_lcm_sing = store_thm(
  "set_lcm_sing",
  ``!x. set_lcm {x} = x``,
  rw_tac std_ss[set_lcm_def, SET_TO_LIST_SING, list_lcm_sing]);

(* Theorem: set_lcm (set l) = list_lcm l *)
(* Proof:
   Let t = SET_TO_LIST (set l)
   Note FINITE (set l)                    by FINITE_LIST_TO_SET
   Then set t
      = set (SET_TO_LIST (set l))         by notation
      = set l                             by SET_TO_LIST_INV, FINITE (set l)

        set_lcm (set l)
      = list_lcm (SET_TO_LIST (set l))    by set_lcm_def
      = list_lcm t                        by notation
      = list_lcm l                        by list_lcm_eq_if_set_eq, set t = set l
*)
val set_lcm_eq_list_lcm = store_thm(
  "set_lcm_eq_list_lcm",
  ``!l. set_lcm (set l) = list_lcm l``,
  rw[FINITE_LIST_TO_SET, SET_TO_LIST_INV, set_lcm_def, list_lcm_eq_if_set_eq]);

(* Theorem: FINITE s ==> (set_lcm s = big_lcm s) *)
(* Proof:
     set_lcm s
   = list_lcm (SET_TO_LIST s)       by set_lcm_def
   = big_lcm (set (SET_TO_LIST s))  by big_lcm_eq_list_lcm
   = big_lcm s                      by SET_TO_LIST_INV, FINITE s
*)
val set_lcm_eq_big_lcm = store_thm(
  "set_lcm_eq_big_lcm",
  ``!s. FINITE s ==> (big_lcm s = set_lcm s)``,
  metis_tac[set_lcm_def, big_lcm_eq_list_lcm, SET_TO_LIST_INV]);

(* Theorem: FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s) *)
(* Proof: by big_lcm_insert, set_lcm_eq_big_lcm *)
val set_lcm_insert = store_thm(
  "set_lcm_insert",
  ``!s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s)``,
  rw[big_lcm_insert, GSYM set_lcm_eq_big_lcm]);

(* Theorem: FINITE s /\ x IN s ==> x divides (set_lcm s) *)
(* Proof:
   Note FINITE s /\ x IN s
    ==> MEM x (SET_TO_LIST s)               by MEM_SET_TO_LIST
    ==> x divides list_lcm (SET_TO_LIST s)  by list_lcm_is_common_multiple
     or x divides (set_lcm s)               by set_lcm_def
*)
val set_lcm_is_common_multiple = store_thm(
  "set_lcm_is_common_multiple",
  ``!x s. FINITE s /\ x IN s ==> x divides (set_lcm s)``,
  rw[set_lcm_def] >>
  `MEM x (SET_TO_LIST s)` by rw[MEM_SET_TO_LIST] >>
  rw[list_lcm_is_common_multiple]);

(* Theorem: FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m *)
(* Proof:
   Note FINITE s
    ==> !x. x IN s <=> MEM x (SET_TO_LIST s)    by MEM_SET_TO_LIST
   Thus list_lcm (SET_TO_LIST s) divides m      by list_lcm_is_least_common_multiple
     or                set_lcm s divides m      by set_lcm_def
*)
val set_lcm_is_least_common_multiple = store_thm(
  "set_lcm_is_least_common_multiple",
  ``!s m. FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m``,
  metis_tac[set_lcm_def, MEM_SET_TO_LIST, list_lcm_is_least_common_multiple]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s) *)
(* Proof:
   By finite induction on s.
   Base: set_lcm {} = PROD_SET {}
           set_lcm {}
         = 1                by set_lcm_empty
         = PROD_SET {}      by PROD_SET_EMPTY
   Step: PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s) ==>
         e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==> set_lcm (e INSERT s) = PROD_SET (e INSERT s)
      Note !z. z IN s ==> coprime e z  by IN_INSERT
      Thus coprime e (PROD_SET s)      by every_coprime_prod_set_coprime
           set_lcm (e INSERT s)
         = lcm e (set_lcm s)      by set_lcm_insert
         = lcm e (PROD_SET s)     by induction hypothesis
         = e * (PROD_SET s)       by LCM_COPRIME
         = PROD_SET (e INSERT s)  by PROD_SET_INSERT, e NOTIN s
*)
val pairwise_coprime_prod_set_eq_set_lcm = store_thm(
  "pairwise_coprime_prod_set_eq_set_lcm",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)``,
  `!s. FINITE s ==> PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[set_lcm_empty, PROD_SET_EMPTY] >>
  fs[] >>
  `!z. z IN s ==> coprime e z` by metis_tac[] >>
  `coprime e (PROD_SET s)` by rw[every_coprime_prod_set_coprime] >>
  `set_lcm (e INSERT s) = lcm e (set_lcm s)` by rw[set_lcm_insert] >>
  `_ = lcm e (PROD_SET s)` by rw[] >>
  `_ = e * (PROD_SET s)` by rw[LCM_COPRIME] >>
  `_ = PROD_SET (e INSERT s)` by rw[PROD_SET_INSERT] >>
  rw[]);

(* This is a generalisation of LCM_COPRIME |- !m n. coprime m n ==> (lcm m n = m * n)  *)

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s /\ (!x. x IN s ==> x divides m) ==> (PROD_SET s) divides m *)
(* Proof:
   Note PROD_SET s = set_lcm s      by pairwise_coprime_prod_set_eq_set_lcm
    and set_lcm s divides m         by set_lcm_is_least_common_multiple
    ==> (PROD_SET s) divides m
*)
val pairwise_coprime_prod_set_divides = store_thm(
  "pairwise_coprime_prod_set_divides",
  ``!s m. FINITE s /\ PAIRWISE_COPRIME s /\ (!x. x IN s ==> x divides m) ==> (PROD_SET s) divides m``,
  rw[set_lcm_is_least_common_multiple, GSYM pairwise_coprime_prod_set_eq_set_lcm]);

(* ------------------------------------------------------------------------- *)
(* Nair's Trick - using List LCM directly                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload on consecutive LCM *)
val _ = overload_on("lcm_run", ``\n. list_lcm [1 .. n]``);

(* Theorem: lcm_run n = FOLDL lcm 1 [1 .. n] *)
(* Proof:
     lcm_run n
   = list_lcm [1 .. n]      by notation
   = FOLDL lcm 1 [1 .. n]   by list_lcm_by_FOLDL
*)
val lcm_run_by_FOLDL = store_thm(
  "lcm_run_by_FOLDL",
  ``!n. lcm_run n = FOLDL lcm 1 [1 .. n]``,
  rw[list_lcm_by_FOLDL]);

(* Theorem: lcm_run n = FOLDL lcm 1 [1 .. n] *)
(* Proof:
     lcm_run n
   = list_lcm [1 .. n]      by notation
   = FOLDR lcm 1 [1 .. n]   by list_lcm_by_FOLDR
*)
val lcm_run_by_FOLDR = store_thm(
  "lcm_run_by_FOLDR",
  ``!n. lcm_run n = FOLDR lcm 1 [1 .. n]``,
  rw[list_lcm_by_FOLDR]);

(* Theorem: lcm_run 0 = 1 *)
(* Proof:
     lcm_run 0
   = list_lcm [1 .. 0]    by notation
   = list_lcm []          by listRangeINC_EMPTY, 0 < 1
   = 1                    by list_lcm_nil
*)
val lcm_run_0 = store_thm(
  "lcm_run_0",
  ``lcm_run 0 = 1``,
  rw[listRangeINC_EMPTY]);

(* Theorem: lcm_run 1 = 1 *)
(* Proof:
     lcm_run 1
   = list_lcm [1 .. 1]    by notation
   = list_lcm [1]         by leibniz_vertical_0
   = 1                    by list_lcm_sing
*)
val lcm_run_1 = store_thm(
  "lcm_run_1",
  ``lcm_run 1 = 1``,
  rw[leibniz_vertical_0, list_lcm_sing]);

(* Theorem alias *)
val lcm_run_suc = save_thm("lcm_run_suc", list_lcm_suc);
(* val lcm_run_suc = |- !n. lcm_run (n + 1) = lcm (n + 1) (lcm_run n): thm *)

(* Theorem: 0 < lcm_run n *)
(* Proof:
   Note EVERY_POSITIVE [1 .. n]     by listRangeINC_EVERY
     so lcm_run n
      = list_lcm [1 .. n]           by notation
      > 0                           by list_lcm_pos
*)
val lcm_run_pos = store_thm(
  "lcm_run_pos",
  ``!n. 0 < lcm_run n``,
  rw[list_lcm_pos, listRangeINC_EVERY]);

(* Theorem: (lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\ (lcm_run 5 = 60) /\ ...  *)
(* Proof: by evaluation *)
val lcm_run_small = store_thm(
  "lcm_run_small",
  ``(lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\ (lcm_run 5 = 60) /\
   (lcm_run 6 = 60) /\ (lcm_run 7 = 420) /\ (lcm_run 8 = 840) /\ (lcm_run 9 = 2520)``,
  EVAL_TAC);

(* Theorem: (n + 1) divides lcm_run (n + 1) /\ (lcm_run n) divides lcm_run (n + 1) *)
(* Proof:
   If n = 0,
      Then 0 + 1 = 1                by arithmetic
       and lcm_run 0 = 1            by lcm_run_0
      Hence true                    by ONE_DIVIDES_ALL
   If n <> 0,
      Then n - 1 + 1 = n                       by arithmetic, 0 < n
           lcm_run (n + 1)
         = list_lcm [1 .. (n + 1)]             by notation
         = list_lcm (SNOC (n + 1) [1 .. n])    by leibniz_vertical_snoc
         = lcm (n + 1) (list_lcm [1 .. n])     by list_lcm_snoc]
         = lcm (n + 1) (lcm_run n)             by notation
      Hence true                               by LCM_DIVISORS
*)
val lcm_run_divisors = store_thm(
  "lcm_run_divisors",
  ``!n. (n + 1) divides lcm_run (n + 1) /\ (lcm_run n) divides lcm_run (n + 1)``,
  strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `(n - 1 + 1 = n) /\ (n - 1 + 2 = n + 1)` by decide_tac >>
  `lcm_run (n + 1) = list_lcm (SNOC (n + 1) [1 .. n])` by metis_tac[leibniz_vertical_snoc] >>
  `_ = lcm (n + 1) (lcm_run n)` by rw[list_lcm_snoc] >>
  rw[LCM_DIVISORS]);

(* Theorem: lcm_run n <= lcm_run (n + 1) *)
(* Proof:
   Note lcm_run n divides lcm_run (n + 1)   by lcm_run_divisors
    and 0 < lcm_run (n + 1)  ]              by lcm_run_pos
     so lcm_run n <= lcm_run (n + 1)        by DIVIDES_LE
*)
Theorem lcm_run_monotone[allow_rebind]:
  !n. lcm_run n <= lcm_run (n + 1)
Proof rw[lcm_run_divisors, lcm_run_pos, DIVIDES_LE]
QED

(* Theorem: 2 ** n <= lcm_run (n + 1) *)
(* Proof:
     lcm_run (n + 1)
   = list_lcm [1 .. (n + 1)]   by notation
   >= 2 ** n                   by lcm_lower_bound
*)
val lcm_run_lower = save_thm("lcm_run_lower", lcm_lower_bound);
(*
val lcm_run_lower = |- !n. 2 ** n <= lcm_run (n + 1): thm
*)

(* Theorem: !n k. k <= n ==> leibniz n k divides lcm_run (n + 1) *)
(* Proof: by notation, leibniz_vertical_divisor *)
val lcm_run_leibniz_divisor = save_thm("lcm_run_leibniz_divisor", leibniz_vertical_divisor);
(*
val lcm_run_leibniz_divisor = |- !n k. k <= n ==> leibniz n k divides lcm_run (n + 1): thm
*)

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Let m = 2 * n.

   Claim: (m + 1) * binomial m n divides lcm_run (m + 1)       [1]
   Proof: Note n <= m                                          by LESS_MONO_MULT, 1 <= 2
           ==> (leibniz m n) divides lcm_run (m + 1)           by lcm_run_leibniz_divisor, n <= m
            or (m + 1) * binomial m n divides lcm_run (m + 1)  by leibniz_def

   Claim: n * binomial m n divides lcm_run (m + 1)             [2]
   Proof: Note 0 < m /\ n <= m - 1                             by 0 < n
           and m - 1 + 1 = m                                   by 0 < m
          Thus (leibniz (m - 1) n) divides lcm_run m           by lcm_run_leibniz_divisor, n <= m - 1
          Note (lcm_run m) divides lcm_run (m + 1)             by lcm_run_divisors
            so (leibniz (m - 1) n) divides lcm_run (m + 1)     by DIVIDES_TRANS
           and leibniz (m - 1) n
             = (m - n) * binomial m n                          by leibniz_up_alt
             = n * binomial m n                                by m - n = n

   Note coprime n (m + 1)                         by GCD_EUCLID, GCD_1, 1 < n
   Thus lcm (n * binomial m n) ((m + 1) * binomial m n)
      = n * (m + 1) * binomial m n                by LCM_COMMON_COPRIME
      = n * ((m + 1) * binomial m n)              by MULT_ASSOC
      = n * leibniz m n                           by leibniz_def
    ==> n * leibniz m n divides lcm_run (m + 1)   by LCM_DIVIDES, [1], [2]
   Note 0 < lcm_run (m + 1)                       by lcm_run_pos
     or n * leibniz m n <= lcm_run (m + 1)        by DIVIDES_LE, 0 < lcm_run (m + 1)
    Now          4 ** n <= leibniz m n            by leibniz_middle_lower
     so      n * 4 ** n <= n * leibniz m n        by LESS_MONO_MULT, MULT_COMM
     or      n * 4 ** n <= lcm_run (m + 1)        by LESS_EQ_TRANS
*)
val lcm_run_lower_odd = store_thm(
  "lcm_run_lower_odd",
  ``!n. n * 4 ** n <= lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = 2 * n` >>
  `(m + 1) * binomial m n divides lcm_run (m + 1)` by
  (`n <= m` by rw[Abbr`m`] >>
  metis_tac[lcm_run_leibniz_divisor, leibniz_def]) >>
  `n * binomial m n divides lcm_run (m + 1)` by
    (`0 < m /\ n <= m - 1` by rw[Abbr`m`] >>
  `m - 1 + 1 = m` by decide_tac >>
  `(leibniz (m - 1) n) divides lcm_run m` by metis_tac[lcm_run_leibniz_divisor] >>
  `(lcm_run m) divides lcm_run (m + 1)` by rw[lcm_run_divisors] >>
  `leibniz (m - 1) n = (m - n) * binomial m n` by rw[leibniz_up_alt] >>
  `_ = n * binomial m n` by rw[Abbr`m`] >>
  metis_tac[DIVIDES_TRANS]) >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  `lcm (n * binomial m n) ((m + 1) * binomial m n) = n * (m + 1) * binomial m n` by rw[LCM_COMMON_COPRIME] >>
  `_ = n * leibniz m n` by rw[leibniz_def, MULT_ASSOC] >>
  `n * leibniz m n divides lcm_run (m + 1)` by metis_tac[LCM_DIVIDES] >>
  `n * leibniz m n <= lcm_run (m + 1)` by rw[DIVIDES_LE, lcm_run_pos] >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  metis_tac[LESS_MONO_MULT, MULT_COMM, LESS_EQ_TRANS]);

(* Theorem: n * 4 ** n <= lcm_run (2 * (n + 1)) *)
(* Proof:
     lcm_run (2 * (n + 1))
   = lcm_run (2 * n + 2)        by arithmetic
   >= lcm_run (2 * n + 1)       by lcm_run_monotone
   >= n * 4 ** n                by lcm_run_lower_odd
*)
val lcm_run_lower_even = store_thm(
  "lcm_run_lower_even",
  ``!n. n * 4 ** n <= lcm_run (2 * (n + 1))``,
  rpt strip_tac >>
  `2 * (n + 1) = 2 * n + 1 + 1` by decide_tac >>
  metis_tac[lcm_run_monotone, lcm_run_lower_odd, LESS_EQ_TRANS]);

(* Theorem: ODD n ==> (HALF n) * HALF (2 ** n) <= lcm_run n *)
(* Proof:
   Let k = HALF n.
   Then n = 2 * k + 1              by ODD_HALF
    and HALF (2 ** n)
      = HALF (2 ** (2 * k + 1))    by above
      = HALF (2 ** (SUC (2 * k)))  by ADD1
      = HALF (2 * 2 ** (2 * k))    by EXP
      = 2 ** (2 * k)               by HALF_TWICE
      = 4 ** k                     by EXP_EXP_MULT
   Since k * 4 ** k <= lcm_run (2 * k + 1)  by lcm_run_lower_odd
   The result follows.
*)
val lcm_run_odd_lower = store_thm(
  "lcm_run_odd_lower",
  ``!n. ODD n ==> (HALF n) * HALF (2 ** n) <= lcm_run n``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `n = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
  `HALF (2 ** n) = HALF (2 ** (SUC (2 * k)))` by rw[ADD1] >>
  `_ = HALF (2 * 2 ** (2 * k))` by rw[EXP] >>
  `_ = 2 ** (2 * k)` by rw[HALF_TWICE] >>
  `_ = 4 ** k` by rw[EXP_EXP_MULT] >>
  metis_tac[lcm_run_lower_odd]);

Theorem HALF_MULT_EVEN'[local] = ONCE_REWRITE_RULE [MULT_COMM] HALF_MULT_EVEN

(* Theorem: EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n *)
(* Proof:
   If n = 0, HALF (n - 2) = 0, so trivially true.
   If n <> 0,
   Let h = HALF n.
   Then n = 2 * h         by EVEN_HALF
   Note h <> 0            by n <> 0
     so ?k. h = k + 1     by num_CASES, ADD1
     or n = 2 * k + 2     by n = 2 * (k + 1)
    and HALF (HALF (2 ** n))
      = HALF (HALF (2 ** (2 * k + 2)))        by above
      = HALF (HALF (2 ** SUC (SUC (2 * k))))  by ADD1
      = HALF (HALF (2 * (2 * 2 ** (2 * k))))  by EXP
      = 2 ** (2 * k)                          by HALF_TWICE
      = 4 ** k                                by EXP_EXP_MULT
   Also n - 2 = 2 * k                         by 0 < n, n = 2 * k + 2
     so HALF (n - 2) = k                      by HALF_TWICE
   Since k * 4 ** k <= lcm_run (2 * (k + 1))  by lcm_run_lower_even
   The result follows.
*)
Theorem lcm_run_even_lower:
  !n. EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >- rw[] >>
  qabbrev_tac `h = HALF n` >>
  `n = 2 * h` by rw[EVEN_HALF, Abbr`h`] >>
  `h <> 0` by rw[Abbr`h`] >>
  `?k. h = k + 1` by metis_tac[num_CASES, ADD1] >>
  `HALF (HALF (2 ** n)) = HALF (HALF (2 ** SUC (SUC (2 * k))))` by simp[ADD1] >>
  `_ = HALF (HALF (2 * (2 * 2 ** (2 * k))))` by rw[EXP, HALF_MULT_EVEN'] >>
  `_ = 2 ** (2 * k)` by rw[HALF_TWICE] >>
  `_ = 4 ** k` by rw[EXP_EXP_MULT] >>
  `n - 2 = 2 * k` by decide_tac >>
  `HALF (n - 2) = k` by rw[HALF_TWICE] >>
  metis_tac[lcm_run_lower_even]
QED

(* Theorem: ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   This follows by lcm_run_odd_lower
   if we can show: 2 ** n <= HALF n * HALF (2 ** n)

   Note HALF 5 = 2            by arithmetic
    and HALF 5 <= HALF n      by DIV_LE_MONOTONE, 0 < 2
   Also n <> 0                by 5 <= n
     so ?m. n = SUC m         by num_CASES
        HALF n * HALF (2 ** n)
      = HALF n * HALF (2 * 2 ** m)     by EXP
      = HALF n * 2 ** m                by HALF_TWICE
      >= 2 * 2 ** m                    by LESS_MONO_MULT
       = 2 ** (SUC m)                  by EXP
       = 2 ** n                        by n = SUC m
*)
val lcm_run_odd_lower_alt = store_thm(
  "lcm_run_odd_lower_alt",
  ``!n. ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  `2 ** n <= HALF n * HALF (2 ** n)` by
  (`HALF 5 = 2` by EVAL_TAC >>
  `HALF 5 <= HALF n` by rw[DIV_LE_MONOTONE] >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `HALF n * HALF (2 ** n) = HALF n * HALF (2 * 2 ** m)` by rw[EXP] >>
  `_ = HALF n * 2 ** m` by rw[HALF_TWICE] >>
  `2 * 2 ** m <= HALF n * 2 ** m` by rw[LESS_MONO_MULT] >>
  rw[EXP]) >>
  metis_tac[lcm_run_odd_lower, LESS_EQ_TRANS]);

(* Theorem: EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If n = 8,
      Then 2 ** 8 = 256         by arithmetic
       and lcm_run 8 = 840      by lcm_run_small
      Thus true.
   If n <> 8,
      Note ODD 9                by arithmetic
        so n <> 9               by ODD_EVEN
        or 10 <= n              by 8 <= n, n <> 9
      This follows by lcm_run_even_lower
      if we can show: 2 ** n <= HALF (n - 2) * HALF (HALF (2 ** n))

       Let m = n - 2.
      Then 8 <= m               by arithmetic
        or HALF 8 <= HALF m     by DIV_LE_MONOTONE, 0 < 2
       and HALF 8 = 4 = 2 * 2   by arithmetic
       Now n = SUC (SUC m)      by arithmetic
           HALF m * HALF (HALF (2 ** n))
         = HALF m * HALF (HALF (2 ** (SUC (SUC m))))    by above
         = HALF m * HALF (HALF (2 * (2 * 2 ** m)))      by EXP
         = HALF m * 2 ** m                              by HALF_TWICE
         >= 4 * 2 ** m          by LESS_MONO_MULT
          = 2 * (2 * 2 ** m)    by MULT_ASSOC
          = 2 ** (SUC (SUC m))  by EXP
          = 2 ** n              by n = SUC (SUC m)
*)
Theorem lcm_run_even_lower_alt:
  !n. EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n
Proof
  rpt strip_tac >>
  Cases_on `n = 8` >- rw[lcm_run_small] >>
  `2 ** n <= HALF (n - 2) * HALF (HALF (2 ** n))`
    by (`ODD 9` by rw[] >>
        `n <> 9` by metis_tac[ODD_EVEN] >>
        `8 <= n - 2` by decide_tac >>
        qabbrev_tac `m = n - 2` >>
        `n = SUC (SUC m)` by rw[Abbr`m`] >>
        ‘HALF m * HALF (HALF (2 ** n)) =
         HALF m * HALF (HALF (2 * (2 * 2 ** m)))’ by rw[EXP, HALF_MULT_EVEN'] >>
        `_ = HALF m * 2 ** m` by rw[HALF_TWICE] >>
        `HALF 8 <= HALF m` by rw[DIV_LE_MONOTONE] >>
        `HALF 8 = 4` by EVAL_TAC >>
        `2 * (2 * 2 ** m) <= HALF m * 2 ** m` by rw[LESS_MONO_MULT] >>
        rw[EXP]) >>
  metis_tac[lcm_run_even_lower, LESS_EQ_TRANS]
QED

(* Theorem: 7 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If EVEN n,
      Node ODD 7                 by arithmetic
        so n <> 7                by EVEN_ODD
        or 8 <= n                by arithmetic
      Hence true                 by lcm_run_even_lower_alt
   If ~EVEN n, then ODD n        by EVEN_ODD
      Note 7 <= n ==> 5 <= n     by arithmetic
      Hence true                 by lcm_run_odd_lower_alt
*)
val lcm_run_lower_better = store_thm(
  "lcm_run_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  `EVEN n \/ ODD n` by rw[EVEN_OR_ODD] >| [
    `ODD 7` by rw[] >>
    `n <> 7` by metis_tac[ODD_EVEN] >>
    rw[lcm_run_even_lower_alt],
    rw[lcm_run_odd_lower_alt]
  ]);


(* ------------------------------------------------------------------------- *)
(* Nair's Trick -- rework                                                    *)
(* ------------------------------------------------------------------------- *)

(*
Picture:
leibniz_lcm_property    |- !n. lcm_run (n + 1) = list_lcm (leibniz_horizontal n)
leibniz_horizontal_mem  |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
so:
lcm_run (2*n + 1) = list_lcm (leibniz_horizontal (2*n))
and leibniz_horizontal (2*n) has members: 0, 1, 2, ...., n, (n + 1), ....., (2*n)
note: n <= 2*n, always, (n+1) <= 2*n = (n+n) when 1 <= n.
thus:
Both  B = (leibniz 2*n n) and C = (leibniz 2*n n+1) divides lcm_run (2*n + 1),
  or  (lcm B C) divides lcm_run (2*n + 1).
But   (lcm B C) = (lcm B A)    where A = (leibniz 2*n-1 n).
By leibniz_def    |- !n k. leibniz n k = (n + 1) * binomial n k
By leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
 so B = (2*n + 1) * binomial 2*n n
and A = (2*n - n) * binomial 2*n n = n * binomial 2*n n
and lcm B A = lcm ((2*n + 1) * binomial 2*n n) (n * binomial 2*n n)
            = (lcm (2*n + 1) n) * binomial 2*n n        by LCM_COMMON_FACTOR
            = n * (2*n + 1) * binomial 2*n n            by coprime (2*n+1) n
            = n * (leibniz 2*n n)                       by leibniz_def
*)

(* Theorem: 0 < n ==> n * (leibniz (2 * n) n) divides lcm_run (2 * n + 1) *)
(* Proof:
   Note 1 <= n                 by 0 < n
   Let m = 2 * n,
   Then n <= 2 * n = m, and
        n + 1 <= n + n = m     by arithmetic
   Also coprime n (m + 1)      by GCD_EUCLID

   Identify a triplet:
   Let t = triplet (m - 1) n
   Then t.a = leibniz (m - 1) n       by triplet_def
        t.b = leibniz m n             by triplet_def
        t.c = leibniz m (n + 1)       by triplet_def

   Note MEM t.b (leibniz_horizontal m)        by leibniz_horizontal_mem, n <= m
    and MEM t.c (leibniz_horizontal m)        by leibniz_horizontal_mem, n + 1 <= m
    ==> lcm t.b t.c divides list_lcm (leibniz_horizontal m)  by list_lcm_divisor_lcm_pair
                          = lcm_run (m + 1)   by leibniz_lcm_property

   Let k = binomial m n.
        lcm t.b t.c
      = lcm t.b t.a                           by leibniz_triplet_lcm
      = lcm ((m + 1) * k) t.a                 by leibniz_def
      = lcm ((m + 1) * k) ((m - n) * k)       by leibniz_up_alt
      = lcm ((m + 1) * k) (n * k)             by m = 2 * n
      = n * (m + 1) * k                       by LCM_COMMON_COPRIME, LCM_SYM, coprime n (m + 1)
      = n * leibniz m n                       by leibniz_def
   Thus (n * leibniz m n) divides lcm_run (m + 1)
*)
val lcm_run_odd_factor = store_thm(
  "lcm_run_odd_factor",
  ``!n. 0 < n ==> n * (leibniz (2 * n) n) divides lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  qabbrev_tac `m = 2 * n` >>
  `n <= m /\ n + 1 <= m` by rw[Abbr`m`] >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  qabbrev_tac `t = triplet (m - 1) n` >>
  `t.a = leibniz (m - 1) n` by rw[triplet_def, Abbr`t`] >>
  `t.b = leibniz m n` by rw[triplet_def, Abbr`t`] >>
  `t.c = leibniz m (n + 1)` by rw[triplet_def, Abbr`t`] >>
  `t.b divides lcm_run (m + 1)` by metis_tac[lcm_run_leibniz_divisor] >>
  `t.c divides lcm_run (m + 1)` by metis_tac[lcm_run_leibniz_divisor] >>
  `lcm t.b t.c divides lcm_run (m + 1)` by rw[LCM_IS_LEAST_COMMON_MULTIPLE] >>
  qabbrev_tac `k = binomial m n` >>
  `lcm t.b t.c = lcm t.b t.a` by rw[leibniz_triplet_lcm, Abbr`t`] >>
  `_ = lcm ((m + 1) * k) ((m - n) * k)` by rw[leibniz_def, leibniz_up_alt, Abbr`k`] >>
  `_ = lcm ((m + 1) * k) (n * k)` by rw[Abbr`m`] >>
  `_ = n * (m + 1) * k` by rw[LCM_COMMON_COPRIME, LCM_SYM] >>
  `_ = n * leibniz m n` by rw[leibniz_def, Abbr`k`] >>
  metis_tac[]);

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Note     4 ** n <= leibniz (2 * n) n        by leibniz_middle_lower
     so n * 4 ** n <= n * leibniz (2 * n) n    by LESS_MONO_MULT, MULT_COMM
    Let k = n * leibniz (2 * n) n.
   Then k divides lcm_run (2 * n + 1)          by lcm_run_odd_factor
    Now       0 < lcm_run (2 * n + 1)          by lcm_run_pos
     so             k <= lcm_run (2 * n + 1)   by DIVIDES_LE
   Overall n * 4 ** n <= lcm_run (2 * n + 1)   by LESS_EQ_TRANS
*)
Theorem lcm_run_lower_odd[allow_rebind]:
  !n. n * 4 ** n <= lcm_run (2 * n + 1)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  `4 ** n <= leibniz (2 * n) n` by rw[leibniz_middle_lower] >>
  `n * 4 ** n <= n * leibniz (2 * n) n` by rw[LESS_MONO_MULT, MULT_COMM] >>
  `n * leibniz (2 * n) n <= lcm_run (2 * n + 1)` by rw[lcm_run_odd_factor, lcm_run_pos, DIVIDES_LE] >>
  rw[LESS_EQ_TRANS]
QED

(* Another direct proof of the same theorem *)

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n, or 1 <= n                 by arithmetic

   Let m = 2 * n,
   Then n <= 2 * n = m, and
        n + 1 <= n + n = m     by arithmetic, 1 <= n
   Also coprime n (m + 1)      by GCD_EUCLID

   Identify a triplet:
   Let t = triplet (m - 1) n
   Then t.a = leibniz (m - 1) n       by triplet_def
        t.b = leibniz m n             by triplet_def
        t.c = leibniz m (n + 1)       by triplet_def

   Note MEM t.b (leibniz_horizontal m)        by leibniz_horizontal_mem, n <= m
    and MEM t.c (leibniz_horizontal m)        by leibniz_horizontal_mem, n + 1 <= m
    and POSITIVE (leibniz_horizontal m)       by leibniz_horizontal_pos_alt
    ==> lcm t.b t.c <= list_lcm (leibniz_horizontal m)  by list_lcm_lower_by_lcm_pair
                     = lcm_run (m + 1)        by leibniz_lcm_property

   Let k = binomial m n.
        lcm t.b t.c
      = lcm t.b t.a                           by leibniz_triplet_lcm
      = lcm ((m + 1) * k) t.a                 by leibniz_def
      = lcm ((m + 1) * k) ((m - n) * k)       by leibniz_up_alt
      = lcm ((m + 1) * k) (n * k)             by m = 2 * n
      = n * (m + 1) * k                       by LCM_COMMON_COPRIME, LCM_SYM, coprime n (m + 1)
      = n * leibniz m n                       by leibniz_def
   Thus (n * leibniz m n) divides lcm_run (m + 1)

      Note     4 ** n <= leibniz m n          by leibniz_middle_lower
        so n * 4 ** n <= n * leibniz m n      by LESS_MONO_MULT, MULT_COMM
   Overall n * 4 ** n <= lcm_run (2 * n + 1)  by LESS_EQ_TRANS
*)
Theorem lcm_run_lower_odd[allow_rebind]:
  !n. n * 4 ** n <= lcm_run (2 * n + 1)
Proof
  rpt strip_tac >>
  Cases_on ‘n = 0’ >-
  rw[] >>
  qabbrev_tac ‘m = 2 * n’ >>
  ‘n <= m /\ n + 1 <= m’ by rw[Abbr‘m’] >>
  ‘coprime n (m + 1)’ by rw[GCD_EUCLID, Abbr‘m’] >>
  qabbrev_tac ‘t = triplet (m - 1) n’ >>
  ‘t.a = leibniz (m - 1) n’ by rw[triplet_def, Abbr‘t’] >>
  ‘t.b = leibniz m n’ by rw[triplet_def, Abbr‘t’] >>
  ‘t.c = leibniz m (n + 1)’ by rw[triplet_def, Abbr‘t’] >>
  ‘MEM t.b (leibniz_horizontal m)’ by metis_tac[leibniz_horizontal_mem] >>
  ‘MEM t.c (leibniz_horizontal m)’ by metis_tac[leibniz_horizontal_mem] >>
  ‘POSITIVE (leibniz_horizontal m)’ by metis_tac[leibniz_horizontal_pos_alt] >>
  ‘lcm t.b t.c <= lcm_run (m + 1)’ by metis_tac[leibniz_lcm_property, list_lcm_lower_by_lcm_pair] >>
  ‘lcm t.b t.c = n * leibniz m n’ by
  (qabbrev_tac ‘k = binomial m n’ >>
  ‘lcm t.b t.c = lcm t.b t.a’ by rw[leibniz_triplet_lcm, Abbr‘t’] >>
  ‘_ = lcm ((m + 1) * k) ((m - n) * k)’ by rw[leibniz_def, leibniz_up_alt, Abbr‘k’] >>
  ‘_ = lcm ((m + 1) * k) (n * k)’ by rw[Abbr‘m’] >>
  ‘_ = n * (m + 1) * k’ by rw[LCM_COMMON_COPRIME, LCM_SYM] >>
  ‘_ = n * leibniz m n’ by rw[leibniz_def, Abbr‘k’] >>
  rw[]) >>
  ‘4 ** n <= leibniz m n’ by rw[leibniz_middle_lower, Abbr‘m’] >>
  ‘n * 4 ** n <= n * leibniz m n’ by rw[LESS_MONO_MULT] >>
  metis_tac[LESS_EQ_TRANS]
QED

(* Theorem: ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n) *)
(* Proof:
   If part: 2 ** n <= lcm_run n ==> 5 <= n
      By contradiction, suppose n < 5.
      By ODD n, n = 1 or n = 3.
      If n = 1, LHS = 2 ** 1 = 2         by arithmetic
                RHS = lcm_run 1 = 1      by lcm_run_1
                Hence false.
      If n = 3, LHS = 2 ** 3 = 8         by arithmetic
                RHS = lcm_run 3 = 6      by lcm_run_small
                Hence false.
   Only-if part: 5 <= n ==> 2 ** n <= lcm_run n
      Let h = HALF n.
      Then n = 2 * h + 1                 by ODD_HALF
        so          4 <= 2 * h           by 5 - 1 = 4
        or          2 <= h               by arithmetic
       ==> 2 * 4 ** h <= h * 4 ** h      by LESS_MONO_MULT
       But 2 * 4 ** h
         = 2 * (2 ** 2) ** h             by arithmetic
         = 2 * 2 ** (2 * h)              by EXP_EXP_MULT
         = 2 ** SUC (2 * h)              by EXP
         = 2 ** n                        by ADD1, n = 2 * h + 1
      With h * 4 ** h <= lcm_run n       by lcm_run_lower_odd
        or     2 ** n <= lcm_run n       by LESS_EQ_TRANS
*)
val lcm_run_lower_odd_iff = store_thm(
  "lcm_run_lower_odd_iff",
  ``!n. ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < 5` by decide_tac >>
    `EVEN 0 /\ EVEN 2 /\ EVEN 4` by rw[] >>
    `n <> 0 /\ n <> 2 /\ n <> 4` by metis_tac[EVEN_ODD] >>
    `(n = 1) \/ (n = 3)` by decide_tac >-
    fs[] >>
    fs[lcm_run_small],
    qabbrev_tac `h = HALF n` >>
    `n = 2 * h + 1` by rw[ODD_HALF, Abbr`h`] >>
    `2 * 4 ** h <= h * 4 ** h` by rw[] >>
    `2 * 4 ** h = 2 * 2 ** (2 * h)` by rw[EXP_EXP_MULT] >>
    `_ = 2 ** n` by rw[GSYM EXP] >>
    `h * 4 ** h <= lcm_run n` by rw[lcm_run_lower_odd] >>
    decide_tac
  ]);

(* Theorem: EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n) *)
(* Proof:
   If part: 2 ** n <= lcm_run n ==> (n = 0) \/ 8 <= n
      By contradiction, suppose n <> 0 /\ n < 8.
      By EVEN n, n = 2 or n = 4 or n = 6.
         If n = 2, LHS = 2 ** 2 = 4              by arithmetic
                   RHS = lcm_run 2 = 2           by lcm_run_small
                   Hence false.
         If n = 4, LHS = 2 ** 4 = 16             by arithmetic
                   RHS = lcm_run 4 = 12          by lcm_run_small
                   Hence false.
         If n = 6, LHS = 2 ** 6 = 64             by arithmetic
                   RHS = lcm_run 6 = 60          by lcm_run_small
                   Hence false.
   Only-if part: (n = 0) \/ 8 <= n ==> 2 ** n <= lcm_run n
         If n = 0, LHS = 2 ** 0 = 1              by arithmetic
                   RHS = lcm_run 0 = 1           by lcm_run_0
                   Hence true.
         If n = 8, LHS = 2 ** 8 = 256            by arithmetic
                   RHS = lcm_run 8 = 840         by lcm_run_small
                   Hence true.
         Otherwise, 10 <= n, since ODD 9.
         Let h = HALF n, k = h - 1.
         Then n = 2 * h                          by EVEN_HALF
                = 2 * (k + 1)                    by k = h - 1
                = 2 * k + 2                      by arithmetic
          But lcm_run (2 * k + 1) <= lcm_run (2 * k + 2)  by lcm_run_monotone
          and k * 4 ** k <= lcm_run (2 * k + 1)           by lcm_run_lower_odd

          Now          5 <= h                    by 10 <= h
           so          4 <= k                    by k = h - 1
          ==> 4 * 4 ** k <= k * 4 ** k           by LESS_MONO_MULT

              4 * 4 ** k
            = (2 ** 2) * (2 ** 2) ** k           by arithmetic
            = (2 ** 2) * (2 ** (2 * k))          by EXP_EXP_MULT
            = 2 ** (2 * k + 2)                   by EXP_ADD
            = 2 ** n                             by n = 2 * k + 2

         Overall 2 ** n <= lcm_run n             by LESS_EQ_TRANS
*)
val lcm_run_lower_even_iff = store_thm(
  "lcm_run_lower_even_iff",
  ``!n. EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < 8` by decide_tac >>
    `ODD 1 /\ ODD 3 /\ ODD 5 /\ ODD 7` by rw[] >>
    `n <> 1 /\ n <> 3 /\ n <> 5 /\ n <> 7` by metis_tac[EVEN_ODD] >>
    `(n = 2) \/ (n = 4) \/ (n = 6)` by decide_tac >-
    fs[lcm_run_small] >-
    fs[lcm_run_small] >>
    fs[lcm_run_small],
    fs[lcm_run_0],
    Cases_on `n = 8` >-
    rw[lcm_run_small] >>
    `ODD 9` by rw[] >>
    `n <> 9` by metis_tac[EVEN_ODD] >>
    `10 <= n` by decide_tac >>
    qabbrev_tac `h = HALF n` >>
    `n = 2 * h` by rw[EVEN_HALF, Abbr`h`] >>
    qabbrev_tac `k = h - 1` >>
    `lcm_run (2 * k + 1) <= lcm_run (2 * k + 1 + 1)` by rw[lcm_run_monotone] >>
    `2 * k + 1 + 1 = n` by rw[Abbr`k`] >>
    `k * 4 ** k <= lcm_run (2 * k + 1)` by rw[lcm_run_lower_odd] >>
    `4 * 4 ** k <= k * 4 ** k` by rw[Abbr`k`] >>
    `4 * 4 ** k = 2 ** 2 * 2 ** (2 * k)` by rw[EXP_EXP_MULT] >>
    `_ = 2 ** (2 * k + 2)` by rw[GSYM EXP_ADD] >>
    `_ = 2 ** n` by rw[] >>
    metis_tac[LESS_EQ_TRANS]
  ]);

(* Theorem: 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n *)
(* Proof:
   If EVEN n,
      Then n <> 5, n <> 7, so 8 <= n    by arithmetic
      Thus true                         by lcm_run_lower_even_iff
   If ~EVEN n, then ODD n               by EVEN_ODD
      Then n <> 0, n <> 6, so 5 <= n    by arithmetic
      Thus true                         by lcm_run_lower_odd_iff
*)
val lcm_run_lower_better_iff = store_thm(
  "lcm_run_lower_better_iff",
  ``!n. 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n``,
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `ODD 5 /\ ODD 7` by rw[] >>
    `n <> 5 /\ n <> 7` by metis_tac[EVEN_ODD] >>
    metis_tac[lcm_run_lower_even_iff, DECIDE``8 <= n <=> (7 <= n /\ n <> 7)``],
    `EVEN 0 /\ EVEN 6` by rw[] >>
    `ODD n /\ n <> 0 /\ n <> 6` by metis_tac[EVEN_ODD] >>
    metis_tac[lcm_run_lower_odd_iff, DECIDE``5 <= n <=> (n = 5) \/ (n = 6) \/ (7 <= n)``]
  ]);

(* This is the ultimate goal! *)

(* ------------------------------------------------------------------------- *)
(* Nair's Trick - using consecutive LCM                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the consecutive LCM function *)
val lcm_upto_def = Define`
    (lcm_upto 0 = 1) /\
    (lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n))
`;

(* Extract theorems from definition *)
val lcm_upto_0 = save_thm("lcm_upto_0", lcm_upto_def |> CONJUNCT1);
(* val lcm_upto_0 = |- lcm_upto 0 = 1: thm *)

val lcm_upto_SUC = save_thm("lcm_upto_SUC", lcm_upto_def |> CONJUNCT2);
(* val lcm_upto_SUC = |- !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n): thm *)

(* Theorem: (lcm_upto 0 = 1) /\ (!n. lcm_upto (n+1) = lcm (n+1) (lcm_upto n)) *)
(* Proof: by lcm_upto_def *)
val lcm_upto_alt = store_thm(
  "lcm_upto_alt",
  ``(lcm_upto 0 = 1) /\ (!n. lcm_upto (n+1) = lcm (n+1) (lcm_upto n))``,
  metis_tac[lcm_upto_def, ADD1]);

(* Theorem: lcm_upto 1 = 1 *)
(* Proof:
     lcm_upto 1
   = lcm_upto (SUC 0)          by ONE
   = lcm (SUC 0) (lcm_upto 0)  by lcm_upto_SUC
   = lcm (SUC 0) 1             by lcm_upto_0
   = lcm 1 1                   by ONE
   = 1                         by LCM_REF
*)
val lcm_upto_1 = store_thm(
  "lcm_upto_1",
  ``lcm_upto 1 = 1``,
  metis_tac[lcm_upto_def, LCM_REF, ONE]);

(* Theorem: lcm_upto n for small n *)
(* Proof: by evaluation. *)
val lcm_upto_small = store_thm(
  "lcm_upto_small",
  ``(lcm_upto 2 = 2) /\ (lcm_upto 3 = 6) /\ (lcm_upto 4 = 12) /\
   (lcm_upto 5 = 60) /\ (lcm_upto 6 = 60) /\ (lcm_upto 7 = 420) /\
   (lcm_upto 8 = 840) /\ (lcm_upto 9 = 2520) /\ (lcm_upto 10 = 2520)``,
  EVAL_TAC);

(* Theorem: lcm_upto n = list_lcm [1 .. n] *)
(* Proof:
   By induction on n.
   Base: lcm_upto 0 = list_lcm [1 .. 0]
         lcm_upto 0
       = 1                     by lcm_upto_0
       = list_lcm []           by list_lcm_nil
       = list_lcm [1 .. 0]     by listRangeINC_EMPTY
   Step: lcm_upto n = list_lcm [1 .. n] ==> lcm_upto (SUC n) = list_lcm [1 .. SUC n]
         lcm_upto (SUC n)
       = lcm (SUC n) (lcm_upto n)            by lcm_upto_SUC
       = lcm (SUC n) (list_lcm [1 .. n])     by induction hypothesis
       = list_lcm (SNOC (SUC n) [1 .. n])    by list_lcm_snoc
       = list_lcm [1 .. (SUC n)]             by listRangeINC_SNOC, ADD1, 1 <= n + 1
*)
val lcm_upto_eq_list_lcm = store_thm(
  "lcm_upto_eq_list_lcm",
  ``!n. lcm_upto n = list_lcm [1 .. n]``,
  Induct >-
  rw[lcm_upto_0, list_lcm_nil, listRangeINC_EMPTY] >>
  rw[lcm_upto_SUC, list_lcm_snoc, listRangeINC_SNOC, ADD1]);

(* Theorem: 2 ** n <= lcm_upto (n + 1) *)
(* Proof:
     lcm_upto (n + 1)
   = list_lcm [1 .. (n + 1)]   by lcm_upto_eq_list_lcm
   >= 2 ** n                   by lcm_lower_bound
*)
val lcm_upto_lower = store_thm(
  "lcm_upto_lower",
  ``!n. 2 ** n <= lcm_upto (n + 1)``,
  rw[lcm_upto_eq_list_lcm, lcm_lower_bound]);

(* Theorem: 0 < lcm_upto (n + 1) *)
(* Proof:
     lcm_upto (n + 1)
   >= 2 ** n                   by lcm_upto_lower
    > 0                        by EXP_POS, 0 < 2
*)
val lcm_upto_pos = store_thm(
  "lcm_upto_pos",
  ``!n. 0 < lcm_upto (n + 1)``,
  metis_tac[lcm_upto_lower, EXP_POS, LESS_LESS_EQ_TRANS, DECIDE``0 < 2``]);

(* Theorem: (n + 1) divides lcm_upto (n + 1) /\ (lcm_upto n) divides lcm_upto (n + 1) *)
(* Proof:
   Note lcm_upto (n + 1) = lcm (n + 1) (lcm_upto n)   by lcm_upto_alt
     so (n + 1) divides lcm_upto (n + 1)
    and (lcm_upto n) divides lcm_upto (n + 1)         by LCM_DIVISORS
*)
val lcm_upto_divisors = store_thm(
  "lcm_upto_divisors",
  ``!n. (n + 1) divides lcm_upto (n + 1) /\ (lcm_upto n) divides lcm_upto (n + 1)``,
  rw[lcm_upto_alt, LCM_DIVISORS]);

(* Theorem: lcm_upto n <= lcm_upto (n + 1) *)
(* Proof:
   Note (lcm_upto n) divides lcm_upto (n + 1)   by lcm_upto_divisors
    and 0 < lcm_upto (n + 1)                  by lcm_upto_pos
     so lcm_upto n <= lcm_upto (n + 1)          by DIVIDES_LE
*)
val lcm_upto_monotone = store_thm(
  "lcm_upto_monotone",
  ``!n. lcm_upto n <= lcm_upto (n + 1)``,
  rw[lcm_upto_divisors, lcm_upto_pos, DIVIDES_LE]);

(* Theorem: k <= n ==> (leibniz n k) divides lcm_upto (n + 1) *)
(* Proof:
   Note (leibniz n k) divides list_lcm (leibniz_vertical n)   by leibniz_vertical_divisor
    ==> (leibniz n k) divides list_lcm [1 .. (n + 1)]         by notation
     or (leibniz n k) divides lcm_upto (n + 1)                by lcm_upto_eq_list_lcm
*)
val lcm_upto_leibniz_divisor = store_thm(
  "lcm_upto_leibniz_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides lcm_upto (n + 1)``,
  metis_tac[leibniz_vertical_divisor, lcm_upto_eq_list_lcm]);

(* Theorem: n * 4 ** n <= lcm_upto (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Let m = 2 * n.

   Claim: (m + 1) * binomial m n divides lcm_upto (m + 1)       [1]
   Proof: Note n <= m                                           by LESS_MONO_MULT, 1 <= 2
           ==> (leibniz m n) divides lcm_upto (m + 1)           by lcm_upto_leibniz_divisor, n <= m
            or (m + 1) * binomial m n divides lcm_upto (m + 1)  by leibniz_def

   Claim: n * binomial m n divides lcm_upto (m + 1)             [2]
   Proof: Note (lcm_upto m) divides lcm_upto (m + 1)            by lcm_upto_divisors
          Also 0 < m /\ n <= m - 1                              by 0 < n
           and m - 1 + 1 = m                                    by 0 < m
          Thus (leibniz (m - 1) n) divides lcm_upto m           by lcm_upto_leibniz_divisor, n <= m - 1
            or (leibniz (m - 1) n) divides lcm_upto (m + 1)     by DIVIDES_TRANS
           and leibniz (m - 1) n
             = (m - n) * binomial m n                           by leibniz_up_alt
             = n * binomial m n                                 by m - n = n

   Note coprime n (m + 1)                         by GCD_EUCLID, GCD_1, 1 < n
   Thus lcm (n * binomial m n) ((m + 1) * binomial m n)
      = n * (m + 1) * binomial m n                by LCM_COMMON_COPRIME
      = n * ((m + 1) * binomial m n)              by MULT_ASSOC
      = n * leibniz m n                           by leibniz_def
    ==> n * leibniz m n divides lcm_upto (m + 1)  by LCM_DIVIDES, [1], [2]
   Note 0 < lcm_upto (m + 1)                      by lcm_upto_pos
     or n * leibniz m n <= lcm_upto (m + 1)       by DIVIDES_LE, 0 < lcm_upto (m + 1)
    Now          4 ** n <= leibniz m n            by leibniz_middle_lower
     so      n * 4 ** n <= n * leibniz m n        by LESS_MONO_MULT, MULT_COMM
     or      n * 4 ** n <= lcm_upto (m + 1)       by LESS_EQ_TRANS
*)
val lcm_upto_lower_odd = store_thm(
  "lcm_upto_lower_odd",
  ``!n. n * 4 ** n <= lcm_upto (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = 2 * n` >>
  `(m + 1) * binomial m n divides lcm_upto (m + 1)` by
  (`n <= m` by rw[Abbr`m`] >>
  metis_tac[lcm_upto_leibniz_divisor, leibniz_def]) >>
  `n * binomial m n divides lcm_upto (m + 1)` by
    (`(lcm_upto m) divides lcm_upto (m + 1)` by rw[lcm_upto_divisors] >>
  `0 < m /\ n <= m - 1` by rw[Abbr`m`] >>
  `m - 1 + 1 = m` by decide_tac >>
  `(leibniz (m - 1) n) divides lcm_upto m` by metis_tac[lcm_upto_leibniz_divisor] >>
  `(leibniz (m - 1) n) divides lcm_upto (m + 1)` by metis_tac[DIVIDES_TRANS] >>
  `leibniz (m - 1) n = (m - n) * binomial m n` by rw[leibniz_up_alt] >>
  `_ = n * binomial m n` by rw[Abbr`m`] >>
  metis_tac[]) >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  `lcm (n * binomial m n) ((m + 1) * binomial m n) = n * (m + 1) * binomial m n` by rw[LCM_COMMON_COPRIME] >>
  `_ = n * leibniz m n` by rw[leibniz_def, MULT_ASSOC] >>
  `n * leibniz m n divides lcm_upto (m + 1)` by metis_tac[LCM_DIVIDES] >>
  `n * leibniz m n <= lcm_upto (m + 1)` by rw[DIVIDES_LE, lcm_upto_pos] >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  metis_tac[LESS_MONO_MULT, MULT_COMM, LESS_EQ_TRANS]);

(* Theorem: n * 4 ** n <= lcm_upto (2 * (n + 1)) *)
(* Proof:
     lcm_upto (2 * (n + 1))
   = lcm_upto (2 * n + 2)        by arithmetic
   >= lcm_upto (2 * n + 1)       by lcm_upto_monotone
   >= n * 4 ** n                 by lcm_upto_lower_odd
*)
val lcm_upto_lower_even = store_thm(
  "lcm_upto_lower_even",
  ``!n. n * 4 ** n <= lcm_upto (2 * (n + 1))``,
  rpt strip_tac >>
  `2 * (n + 1) = 2 * n + 1 + 1` by decide_tac >>
  metis_tac[lcm_upto_monotone, lcm_upto_lower_odd, LESS_EQ_TRANS]);

(* Theorem: 7 <= n ==> 2 ** n <= lcm_upto n *)
(* Proof:
   If ODD n, ?k. n = SUC (2 * k)       by ODD_EXISTS,
      When 5 <= 7 <= n = 2 * k + 1     by ADD1
           2 <= k                      by arithmetic
       and lcm_upto n
         = lcm_upto (2 * k + 1)        by notation
         >= k * 4 ** k                 by lcm_upto_lower_odd
         >= 2 * 4 ** k                 by k >= 2, LESS_MONO_MULT
          = 2 * 2 ** (2 * k)           by EXP_EXP_MULT
          = 2 ** SUC (2 * k)           by EXP
          = 2 ** n                     by n = SUC (2 * k)
   If EVEN n, ?m. n = 2 * m            by EVEN_EXISTS
      Note ODD 7 /\ ODD 9              by arithmetic
      If n = 8,
         LHS = 2 ** 8 = 256,
         RHS = lcm_upto 8 = 840        by lcm_upto_small
         Hence true.
      Otherwise, 10 <= n               by 7 <= n, n <> 7, n <> 8, n <> 9
      Since 0 < n, 0 < m               by MULT_EQ_0
         so ?k. m = SUC k              by num_CASES
       When 10 <= n = 2 * (k + 1)      by ADD1
             4 <= k                    by arithmetic
       and lcm_upto n
         = lcm_upto (2 * (k + 1))      by notation
         >= k * 4 ** k                 by lcm_upto_lower_even
         >= 4 * 4 ** k                 by k >= 4, LESS_MONO_MULT
          = 4 ** SUC k                 by EXP
          = 4 ** m                     by notation
          = 2 ** (2 * m)               by EXP_EXP_MULT
          = 2 ** n                     by n = 2 * m
*)
val lcm_upto_lower_better = store_thm(
  "lcm_upto_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_upto n``,
  rpt strip_tac >>
  Cases_on `ODD n` >| [
    `?k. n = SUC (2 * k)` by rw[GSYM ODD_EXISTS] >>
    `2 <= k` by decide_tac >>
    `2 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_upto n = lcm_upto (2 * k + 1)` by rw[ADD1] >>
    `2 ** n = 2 * 2 ** (2 * k)` by rw[EXP] >>
    `_ = 2 * 4 ** k` by rw[EXP_EXP_MULT] >>
    metis_tac[lcm_upto_lower_odd, LESS_EQ_TRANS],
    `ODD 7 /\ ODD 9` by rw[] >>
    `EVEN n /\ n <> 7 /\ n <> 9` by metis_tac[ODD_EVEN] >>
    `?m. n = 2 * m` by rw[GSYM EVEN_EXISTS] >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    Cases_on `n = 8` >-
    rw[lcm_upto_small] >>
    `4 <= k` by decide_tac >>
    `4 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_upto n = lcm_upto (2 * (k + 1))` by rw[ADD1] >>
    `2 ** n = 4 ** m` by rw[EXP_EXP_MULT] >>
    `_ = 4 * 4 ** k` by rw[EXP] >>
    metis_tac[lcm_upto_lower_even, LESS_EQ_TRANS]
  ]);

(* This is a very significant result. *)

(* ------------------------------------------------------------------------- *)
(* Simple LCM lower bounds -- rework                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: HALF (n + 1) <= lcm_run n *)
(* Proof:
   If n = 0,
      LHS = HALF 1 = 0                by arithmetic
      RHS = lcm_run 0 = 1             by lcm_run_0
      Hence true.
   If n <> 0, 0 < n.
      Let l = [1 .. n].
      Then l <> []                    by listRangeINC_NIL, n <> 0
        so EVERY_POSITIVE l           by listRangeINC_EVERY
        lcm_run n
      = list_lcm l                    by notation
      >= (SUM l) DIV (LENGTH l)       by list_lcm_nonempty_lower, l <> []
       = (SUM l) DIV n                by listRangeINC_LEN
       = (HALF (n * (n + 1))) DIV n   by sum_1_to_n_eqn
       = HALF ((n * (n + 1)) DIV n)   by DIV_DIV_DIV_MULT, 0 < 2, 0 < n
       = HALF (n + 1)                 by MULT_TO_DIV
*)
val lcm_run_lower_simple = store_thm(
  "lcm_run_lower_simple",
  ``!n. HALF (n + 1) <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  qabbrev_tac `l = [1 .. n]` >>
  `l <> []` by rw[listRangeINC_NIL, Abbr`l`] >>
  `EVERY_POSITIVE l` by rw[listRangeINC_EVERY, Abbr`l`] >>
  `(SUM l) DIV (LENGTH l) = (SUM l) DIV n` by rw[listRangeINC_LEN, Abbr`l`] >>
  `_ = (HALF (n * (n + 1))) DIV n` by rw[sum_1_to_n_eqn, Abbr`l`] >>
  `_ = HALF ((n * (n + 1)) DIV n)` by rw[DIV_DIV_DIV_MULT] >>
  `_ = HALF (n + 1)` by rw[MULT_TO_DIV] >>
  metis_tac[list_lcm_nonempty_lower]);

(* This is a simple result, good but not very useful. *)

(* Theorem: lcm_run n = list_lcm (leibniz_vertical (n - 1)) *)
(* Proof:
   If n = 0,
      Then n - 1 + 1 = 0 - 1 + 1 = 1
       but lcm_run 0 = 1 = lcm_run 1, hence true.
   If n <> 0,
      Then n - 1 + 1 = n, hence true trivially.
*)
val lcm_run_alt = store_thm(
  "lcm_run_alt",
  ``!n. lcm_run n = list_lcm (leibniz_vertical (n - 1))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0, lcm_run_1] >>
  rw[]);

(* Theorem: 2 ** (n - 1) <= lcm_run n *)
(* Proof:
   If n = 0,
      LHS = HALF 1 = 0                by arithmetic
      RHS = lcm_run 0 = 1             by lcm_run_0
      Hence true.
   If n <> 0, 0 < n, or 1 <= n.
      Let l = leibniz_horizontal (n - 1).
      Then LENGTH l = n               by leibniz_horizontal_len
        so l <> []                    by LENGTH_NIL, n <> 0
       and EVERY_POSITIVE l           by leibniz_horizontal_pos
        lcm_run n
      = list_lcm (leibniz_vertical (n - 1)) by lcm_run_alt
      = list_lcm l                    by leibniz_lcm_property
      >= (SUM l) DIV (LENGTH l)       by list_lcm_nonempty_lower, l <> []
       = 2 ** (n - 1)                 by leibniz_horizontal_average_eqn
*)
val lcm_run_lower_good = store_thm(
  "lcm_run_lower_good",
  ``!n. 2 ** (n - 1) <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n /\ 1 <= n /\ (n - 1 + 1 = n)` by decide_tac >>
  qabbrev_tac `l = leibniz_horizontal (n - 1)` >>
  `lcm_run n = list_lcm l` by metis_tac[leibniz_lcm_property] >>
  `LENGTH l = n` by metis_tac[leibniz_horizontal_len] >>
  `l <> []` by metis_tac[LENGTH_NIL] >>
  `EVERY_POSITIVE l` by rw[leibniz_horizontal_pos, Abbr`l`] >>
  metis_tac[list_lcm_nonempty_lower, leibniz_horizontal_average_eqn]);

(* ------------------------------------------------------------------------- *)
(* Upper Bound by Leibniz Triangle                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: leibniz n k = (n + 1 - k) * binomial (n + 1) k *)
(* Proof: by leibniz_up_alt:
leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
*)
val leibniz_eqn = store_thm(
  "leibniz_eqn",
  ``!n k. leibniz n k = (n + 1 - k) * binomial (n + 1) k``,
  rw[GSYM leibniz_up_alt]);

(* Theorem: leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1) *)
(* Proof: by leibniz_up_alt:
leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
*)
val leibniz_right_alt = store_thm(
  "leibniz_right_alt",
  ``!n k. leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1)``,
  metis_tac[leibniz_up_alt, DECIDE``0 < n + 1 /\ (n + 1 - 1 = n) /\ (n + 1 - (k + 1) = n - k)``]);

(* Leibniz Stack:
       \
            \
                \
                    \
                     (L k k) <-- boundary of Leibniz Triangle
                        |    \            |-- (m - k) = distance
                        |   k <= m <= n  <-- m
                        |         \           (n - k) = height, or max distance
                        |     binomial (n+1) (m+1) is at south-east of binomial n m
                        |              \
                        |                   \
   n-th row: ....... (L n k) .................

leibniz_binomial_identity
|- !m n k. k <= m /\ m <= n ==> (leibniz n k * binomial (n - k) (m - k) = leibniz m k * binomial (n + 1) (m + 1))
This says: (leibniz n k) at bottom is related to a stack entry (leibniz m k).
leibniz_divides_leibniz_factor
|- !m n k. k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
This is just a corollary of leibniz_binomial_identity, by divides_def.

leibniz_horizontal_member_divides
|- !m n x. n <= TWICE m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
           x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
This says: for the n-th row, q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
           is a common multiple of all members of the n-th row when n <= TWICE m + 1 /\ m <= n
That means, for the n-th row, pick any m-th row for HALF (n - 1) <= m <= n
Compute its list_lcm (leibniz_horizontal m), then multiply by binomial (n + 1) (m + 1) as q.
This value q is a common multiple of all members in n-th row.
The proof goes through all members of n-th row, i.e. (L n k) for k <= n.
To apply leibniz_binomial_identity, the condition is k <= m, not k <= n.
Since m has been picked (between HALF n and n), divide k into two parts: k <= m, m < k <= n.
For the first part, apply leibniz_binomial_identity.
For the second part, use symmetry L n (n - k) = L n k, then apply leibniz_binomial_identity.
With k <= m, m <= n, we apply leibniz_binomial_identity:
(1) Each member x = leibniz n k divides p = leibniz m k * binomial (n + 1) (m + 1), stack member with a factor.
(2) But leibniz m k is a member of (leibniz_horizontal m)
(3) Thus leibniz m k divides list_lcm (leibniz_horizontal m), the stack member divides its row list_lcm
    ==>  p divides q           by multiplying both by binomial (n + 1) (m + 1)
(4) Hence x divides q.
With the other half by symmetry, all members x divides q.
Corollary 1:
lcm_run_divides_property
|- !m n. n <= TWICE m /\ m <= n ==> lcm_run n divides binomial n m * lcm_run m
This follows by list_lcm_is_least_common_multiple and leibniz_lcm_property.
Corollary 2:
lcm_run_bound_recurrence
|- !m n. n <= TWICE m /\ m <= n ==> lcm_run n <= lcm_run m * binomial n m
Then lcm_run_upper_bound |- !n. lcm_run n <= 4 ** n  follows by complete induction on n.
*)

(* Theorem: k <= m /\ m <= n ==>
           ((leibniz n k) * (binomial (n - k) (m - k)) = (leibniz m k) * (binomial (n + 1) (m + 1))) *)
(* Proof:
     leibniz n k * (binomial (n - k) (m - k))
   = (n + 1) * (binomial n k) * (binomial (n - k) (m - k))     by leibniz_def
                    n!              (n - k)!
   = (n + 1) * ------------- * ------------------              binomial formula
                 k! (n - k)!    (m - k)! (n - m)!
                    n!                 1
   = (n + 1) * -------------- * ------------------             cancel (n - k)!
                 k! 1           (m - k)! (n - m)!
                    n!               (m + 1)!
   = (n + 1) * -------------- * ------------------             replace by (m + 1)!
                k! (m + 1)!     (m - k)! (n - m)!
                  (n + 1)!           m!
   = (m + 1) * -------------- * ------------------             merge and split factorials
                k! (m + 1)!     (m - k)! (n - m)!
                    m!             (n + 1)!
   = (m + 1) * -------------- * ------------------             binomial formula
                k! (m - k)!      (m + 1)! (n - m)!
   = leibniz m k * binomial (n + 1) (m + 1)                    by leibniz_def
*)
val leibniz_binomial_identity = store_thm(
  "leibniz_binomial_identity",
  ``!m n k. k <= m /\ m <= n ==>
           ((leibniz n k) * (binomial (n - k) (m - k)) = (leibniz m k) * (binomial (n + 1) (m + 1)))``,
  rw[leibniz_def] >>
  `m + 1 <= n + 1` by decide_tac >>
  `m - k <= n - k` by decide_tac >>
  `(n - k) - (m - k) = n - m` by decide_tac >>
  `(n + 1) - (m + 1) = n - m` by decide_tac >>
  `FACT m = binomial m k * (FACT (m - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n + 1) = binomial (n + 1) (m + 1) * (FACT (n - m) * FACT (m + 1))` by metis_tac[binomial_formula2] >>
  `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n - k) = binomial (n - k) (m - k) * (FACT (n - m) * FACT (m - k))` by metis_tac[binomial_formula2] >>
  `!n. FACT (n + 1) = (n + 1) * FACT n` by metis_tac[FACT, ADD1] >>
  `FACT (n + 1) = FACT (n - m) * (FACT k * (FACT (m - k) * ((m + 1) * (binomial m k) * (binomial (n + 1) (m + 1)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `FACT (n + 1) = FACT (n - m) * (FACT k * (FACT (m - k) * ((n + 1) * (binomial n k) * (binomial (n - k) (m - k)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[MULT_LEFT_CANCEL, FACT_LESS, NOT_ZERO_LT_ZERO]);

(* Theorem: k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1) *)
(* Proof:
   Note leibniz m k * binomial (n + 1) (m + 1)
      = leibniz n k * binomial (n - k) (m - k)                 by leibniz_binomial_identity
   Thus leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
                                                               by divides_def, MULT_COMM
*)
val leibniz_divides_leibniz_factor = store_thm(
  "leibniz_divides_leibniz_factor",
  ``!m n k. k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)``,
  metis_tac[leibniz_binomial_identity, divides_def, MULT_COMM]);

(* Theorem: n <= 2 * m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
            x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1) *)
(* Proof:
   Let q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1).
   Note MEM x (leibniz_horizontal n)
    ==> ?k. k <= n /\ (x = leibniz n k)          by leibniz_horizontal_member
   Here the picture is:
                HALF n ... m .... n
          0 ........ k .......... n
   We need k <= m to get x divides q, by applying leibniz_divides_leibniz_factor.
   For m < k <= n, we shall use symmetry to get x divides q.
   If k <= m,
      Let p = (leibniz m k) * binomial (n + 1) (m + 1).
      Then x divides p                           by leibniz_divides_leibniz_factor, k <= m, m <= n
       and MEM (leibniz m k) (leibniz_horizontal m)   by leibniz_horizontal_member, k <= m
       ==> (leibniz m k) divides list_lcm (leibniz_horizontal m)   by list_lcm_is_common_multiple
        so (leibniz m k) * binomial (n + 1) (m + 1)
           divides
           list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)   by DIVIDES_CANCEL, binomial_pos
        or p divides q                           by notation
      Thus x divides q                           by DIVIDES_TRANS
   If ~(k <= m), then m < k.
      Note x = leibniz n (n - k)                 by leibniz_sym, k <= n
       Now n <= m + m + 1                        by given n <= 2 * m + 1
        so n - k <= m + m + 1 - k                by arithmetic
       and m + m + 1 - k <= m                    by m < k, so m + 1 <= k
        or n - k <= m                            by LESS_EQ_TRANS
       Let j = n - k, p = (leibniz m j) * binomial (n + 1) (m + 1).
      Then x divides p                           by leibniz_divides_leibniz_factor, j <= m, m <= n
       and MEM (leibniz m j) (leibniz_horizontal m)   by leibniz_horizontal_member, j <= m
       ==> (leibniz m j) divides list_lcm (leibniz_horizontal m)   by list_lcm_is_common_multiple
        so (leibniz m j) * binomial (n + 1) (m + 1)
           divides
           list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)   by DIVIDES_CANCEL, binomial_pos
        or p divides q                           by notation
      Thus x divides q                           by DIVIDES_TRANS
*)
val leibniz_horizontal_member_divides = store_thm(
  "leibniz_horizontal_member_divides",
  ``!m n x. n <= 2 * m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
           x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)``,
  rpt strip_tac >>
  qabbrev_tac `q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)` >>
  `?k. k <= n /\ (x = leibniz n k)` by rw[GSYM leibniz_horizontal_member] >>
  Cases_on `k <= m` >| [
    qabbrev_tac `p = (leibniz m k) * binomial (n + 1) (m + 1)` >>
    `x divides p` by rw[leibniz_divides_leibniz_factor, Abbr`p`] >>
    `MEM (leibniz m k) (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_member] >>
    `(leibniz m k) divides list_lcm (leibniz_horizontal m)` by rw[list_lcm_is_common_multiple] >>
    `p divides q` by rw[GSYM DIVIDES_CANCEL, binomial_pos, Abbr`p`, Abbr`q`] >>
    metis_tac[DIVIDES_TRANS],
    `n - k <= m` by decide_tac >>
    qabbrev_tac `j = n - k` >>
    `x = leibniz n j` by rw[Once leibniz_sym, Abbr`j`] >>
    qabbrev_tac `p = (leibniz m j) * binomial (n + 1) (m + 1)` >>
    `x divides p` by rw[leibniz_divides_leibniz_factor, Abbr`p`] >>
    `MEM (leibniz m j) (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_member] >>
    `(leibniz m j) divides list_lcm (leibniz_horizontal m)` by rw[list_lcm_is_common_multiple] >>
    `p divides q` by rw[GSYM DIVIDES_CANCEL, binomial_pos, Abbr`p`, Abbr`q`] >>
    metis_tac[DIVIDES_TRANS]
  ]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) divides (lcm_run m) * binomial n m *)
(* Proof:
   If n = 0,
      Then lcm_run 0 = 1                         by lcm_run_0
      Hence true                                 by ONE_DIVIDES_ALL
   If n <> 0,
      Then 0 < n, and 0 < m                      by n <= 2 * m
      Thus m - 1 <= n - 1                        by m <= n
       and n - 1 <= 2 * m - 1                    by n <= 2 * m
                  = 2 * (m - 1) + 1
      Thus !x. MEM x (leibniz_horizontal (n - 1)) ==>
            x divides list_lcm (leibniz_horizontal (m - 1)) * binomial n m
                                                 by leibniz_horizontal_member_divides
       ==> list_lcm (leibniz_horizontal (n - 1)) divides
           list_lcm (leibniz_horizontal (m - 1)) * binomial n m
                                                 by list_lcm_is_least_common_multiple
       But lcm_run n = leibniz_horizontal (n - 1)          by leibniz_lcm_property
       and lcm_run m = leibniz_horizontal (m - 1)          by leibniz_lcm_property
           list_lcm (leibniz_horizontal h) divides q       by list_lcm_is_least_common_multiple
      Thus (lcm_run n) divides (lcm_run m) * binomial n m  by above
*)
val lcm_run_divides_property = store_thm(
  "lcm_run_divides_property",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) divides (lcm_run m) * binomial n m``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n` by decide_tac >>
  `0 < m` by decide_tac >>
  `m - 1 <= n - 1` by decide_tac >>
  `n - 1 <= 2 * (m - 1) + 1` by decide_tac >>
  `(n - 1 + 1 = n) /\ (m - 1 + 1 = m)` by decide_tac >>
  metis_tac[leibniz_horizontal_member_divides, list_lcm_is_least_common_multiple, leibniz_lcm_property]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) <= (lcm_run m) * binomial n m *)
(* Proof:
   Note 0 < lcm_run m                                    by lcm_run_pos
    and 0 < binomial n m                                 by binomial_pos
     so 0 < lcm_run m * binomial n m                     by MULT_EQ_0
    Now (lcm_run n) divides (lcm_run m) * binomial n m   by lcm_run_divides_property
   Thus (lcm_run n) <= (lcm_run m) * binomial n m        by DIVIDES_LE
*)
val lcm_run_bound_recurrence = store_thm(
  "lcm_run_bound_recurrence",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) <= (lcm_run m) * binomial n m``,
  rpt strip_tac >>
  `0 < lcm_run m * binomial n m` by metis_tac[lcm_run_pos, binomial_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw[lcm_run_divides_property, DIVIDES_LE]);

(* Theorem: lcm_run n <= 4 ** n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Base: n = 0.
         LHS = lcm_run 0 = 1               by lcm_run_0
         RHS = 4 ** 0 = 1                  by EXP
         Hence true.
      Step: n <> 0 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = lcm_run m * binomial n m.
         Then n = 2 * m                    by EVEN_HALF
           so m <= 2 * m = n               by arithmetic
          ==> lcm_run n <= c               by lcm_run_bound_recurrence, m <= n
          But m <> 0                       by n <> 0
           so m < n                        by arithmetic
          Now c = lcm_run m * binomial n m by notation
               <= 4 ** m * binomial n m    by induction hypothesis, m < n
               <= 4 ** m * 4 ** m          by binomial_middle_upper_bound
                = 4 ** (m + m)             by EXP_ADD
                = 4 ** n                   by TIMES2, n = 2 * m
         Hence lcm_run n <= 4 ** n.
   If ~EVEN n,
      Then ODD n                           by EVEN_ODD
      Base: n = 1.
         LHS = lcm_run 1 = 1               by lcm_run_1
         RHS = 4 ** 1 = 4                  by EXP
         Hence true.
      Step: n <> 1 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = lcm_run (m + 1) * binomial n (m + 1).
         Then n = 2 * m + 1                by ODD_HALF
          and 0 < m                        by n <> 1
          and m + 1 <= 2 * m + 1 = n       by arithmetic
          ==> (lcm_run n) <= c             by lcm_run_bound_recurrence, m + 1 <= n
          But m + 1 <> n                   by m <> 0
           so m + 1 < n                    by m + 1 <> n
          Now c = lcm_run (m + 1) * binomial n (m + 1)   by notation
               <= 4 ** (m + 1) * binomial n (m + 1)      by induction hypothesis, m + 1 < n
                = 4 ** (m + 1) * binomial n m            by binomial_sym, n - (m + 1) = m
               <= 4 ** (m + 1) * 4 ** m                  by binomial_middle_upper_bound
                = 4 ** m * 4 ** (m + 1)    by arithmetic
                = 4 ** (m + (m + 1))       by EXP_ADD
                = 4 ** (2 * m + 1)         by arithmetic
                = 4 ** n                   by n = 2 * m + 1
         Hence lcm_run n <= 4 ** n.
*)
val lcm_run_upper_bound = store_thm(
  "lcm_run_upper_bound",
  ``!n. lcm_run n <= 4 ** n``,
  completeInduct_on `n` >>
  Cases_on `EVEN n` >| [
    Cases_on `n = 0` >-
    rw[lcm_run_0] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    qabbrev_tac `c = lcm_run m * binomial n m` >>
    `lcm_run n <= c` by rw[lcm_run_bound_recurrence, Abbr`c`] >>
    `lcm_run m <= 4 ** m` by rw[] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** m = 4 ** n` by metis_tac[EXP_ADD, TIMES2] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    Cases_on `n = 1` >-
    rw[lcm_run_1] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    qabbrev_tac `c = lcm_run (m + 1) * binomial n (m + 1)` >>
    `lcm_run n <= c` by rw[lcm_run_bound_recurrence, Abbr`c`] >>
    `lcm_run (m + 1) <= 4 ** (m + 1)` by rw[] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** (m + 1) * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** (m + 1) * 4 ** m = 4 ** n` by metis_tac[MULT_COMM, EXP_ADD, ADD_ASSOC, TIMES2] >>
    decide_tac
  ]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Beta Triangle                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define beta triangle *)
(* Use temp_overload so that beta is invisibe outside:
val beta_def = Define`
    beta n k = k * (binomial n k)
`;
*)
val _ = temp_overload_on ("beta", ``\n k. k * (binomial n k)``); (* for temporary overloading *)
(* can use overload, but then hard to print and change the appearance of too many theorem? *)

(*

Pascal's Triangle (k <= n)
n = 0    1 = binomial 0 0
n = 1    1  1
n = 2    1  2  1
n = 3    1  3  3  1
n = 4    1  4  6  4  1
n = 5    1  5 10 10  5  1
n = 6    1  6 15 20 15  6  1

Beta Triangle (0 < k <= n)
n = 1       1                = 1 * (1)                = leibniz_horizontal 0
n = 2       2  2             = 2 * (1  1)             = leibniz_horizontal 1
n = 3       3  6  3          = 3 * (1  2  1)          = leibniz_horizontal 2
n = 4       4 12 12  4       = 4 * (1  3  3  1)       = leibniz_horizontal 3
n = 5       5 20 30 20  5    = 5 * (1  4  6  4  1)    = leibniz_horizontal 4
n = 6       6 30 60 60 30  6 = 6 * (1  5 10 10  5  1) = leibniz_horizontal 5

> EVAL ``let n = 10 in let k = 6 in (beta (n+1) (k+1) = leibniz n k)``; --> T
> EVAL ``let n = 10 in let k = 4 in (beta (n+1) (k+1) = leibniz n k)``; --> T
> EVAL ``let n = 10 in let k = 3 in (beta (n+1) (k+1) = leibniz n k)``; --> T

*)

(* Theorem: beta 0 n = 0 *)
(* Proof:
     beta 0 n
   = n * (binomial 0 n)              by notation
   = n * (if n = 0 then 1 else 0)    by binomial_0_n
   = 0
*)
val beta_0_n = store_thm(
  "beta_0_n",
  ``!n. beta 0 n = 0``,
  rw[binomial_0_n]);

(* Theorem: beta n 0 = 0 *)
(* Proof: by notation *)
val beta_n_0 = store_thm(
  "beta_n_0",
  ``!n. beta n 0 = 0``,
  rw[]);

(* Theorem: n < k ==> (beta n k = 0) *)
(* Proof: by notation, binomial_less_0 *)
val beta_less_0 = store_thm(
  "beta_less_0",
  ``!n k. n < k ==> (beta n k = 0)``,
  rw[binomial_less_0]);

(* Theorem: beta (n + 1) (k + 1) = leibniz n k *)
(* Proof:
   If k <= n, then k + 1 <= n + 1                by arithmetic
        beta (n + 1) (k + 1)
      = (k + 1) binomial (n + 1) (k + 1)         by notation
      = (k + 1) (n + 1)!  / (k + 1)! (n - k)!    by binomial_formula2
      = (n + 1) n! / k! (n - k)!                 by factorial composing and decomposing
      = (n + 1) * binomial n k                   by binomial_formula2
      = leibniz_horizontal n k                   by leibniz_def
   If ~(k <= n), then n < k /\ n + 1 < k + 1     by arithmetic
     Then beta (n + 1) (k + 1) = 0               by beta_less_0
      and leibniz n k = 0                        by leibniz_less_0
     Hence true.
*)
val beta_eqn = store_thm(
  "beta_eqn",
  ``!n k. beta (n + 1) (k + 1) = leibniz n k``,
  rpt strip_tac >>
  Cases_on `k <= n` >| [
    `(n + 1) - (k + 1) = n - k` by decide_tac >>
    `k + 1 <= n + 1` by decide_tac >>
    `FACT (n - k) * FACT k * beta (n + 1) (k + 1) = FACT (n - k) * FACT k * ((k + 1) * binomial (n + 1) (k + 1))` by rw[] >>
    `_ = FACT (n - k) * FACT (k + 1) * binomial (n + 1) (k + 1)` by metis_tac[FACT, ADD1, MULT_ASSOC, MULT_COMM] >>
    `_ = FACT (n + 1)` by metis_tac[binomial_formula2,  MULT_ASSOC, MULT_COMM] >>
    `_ = (n + 1) * FACT n` by metis_tac[FACT, ADD1] >>
    `_ = FACT (n - k) * FACT k * ((n + 1) * binomial n k)` by metis_tac[binomial_formula2, MULT_ASSOC, MULT_COMM] >>
    `_ = FACT (n - k) * FACT k * (leibniz n k)` by rw[leibniz_def] >>
    `FACT k <> 0 /\ FACT (n - k) <> 0` by metis_tac[FACT_LESS, NOT_ZERO_LT_ZERO] >>
    metis_tac[EQ_MULT_LCANCEL, MULT_ASSOC],
    rw[beta_less_0, leibniz_less_0]
  ]);

(* Theorem: 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1)) *)
(* Proof: by beta_eqn *)
val beta_alt = store_thm(
  "beta_alt",
  ``!n k. 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1))``,
  rw[GSYM beta_eqn]);

(* Theorem: 0 < k /\ k <= n ==> 0 < beta n k *)
(* Proof:
       0 < beta n k
   <=> beta n k <> 0                 by NOT_ZERO_LT_ZERO
   <=> k * (binomial n k) <> 0       by notation
   <=> k <> 0 /\ binomial n k <> 0   by MULT_EQ_0
   <=> k <> 0 /\ k <= n              by binomial_pos
   <=> 0 < k /\ k <= n               by NOT_ZERO_LT_ZERO
*)
val beta_pos = store_thm(
  "beta_pos",
  ``!n k. 0 < k /\ k <= n ==> 0 < beta n k``,
  metis_tac[MULT_EQ_0, binomial_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: (beta n k = 0) <=> (k = 0) \/ n < k *)
(* Proof:
       beta n k = 0
   <=> k * (binomial n k) = 0           by notation
   <=> (k = 0) \/ (binomial n k = 0)    by MULT_EQ_0
   <=> (k = 0) \/ (n < k)               by binomial_eq_0
*)
val beta_eq_0 = store_thm(
  "beta_eq_0",
  ``!n k. (beta n k = 0) <=> (k = 0) \/ n < k``,
  rw[binomial_eq_0]);

(*
binomial_sym  |- !n k. k <= n ==> (binomial n k = binomial n (n - k))
leibniz_sym   |- !n k. k <= n ==> (leibniz n k = leibniz n (n - k))
*)

(* Theorem: k <= n ==> (beta n k = beta n (n - k + 1)) *)
(* Proof:
   If k = 0,
      Then beta n 0 = 0                  by beta_n_0
       and beta n (n + 1) = 0            by beta_less_0
      Hence true.
   If k <> 0, then 0 < k
      Thus 0 < n                         by k <= n
         beta n k
      = leibniz (n - 1) (k - 1)          by beta_alt
      = leibniz (n - 1) (n - k)          by leibniz_sym
      = leibniz (n - 1) (n - k + 1 - 1)  by arithmetic
      = beta n (n - k + 1)               by beta_alt
*)
val beta_sym = store_thm(
  "beta_sym",
  ``!n k. k <= n ==> (beta n k = beta n (n - k + 1))``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[beta_n_0, beta_less_0] >>
  rw[beta_alt, Once leibniz_sym]);

(* ------------------------------------------------------------------------- *)
(* Beta Horizontal List                                                      *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``leibniz_horizontal 3``;    --> [4; 12; 12; 4]
> EVAL ``GENLIST (beta 4) 5``;      --> [0; 4; 12; 12; 4]
> EVAL ``TL (GENLIST (beta 4) 5)``; --> [4; 12; 12; 4]
*)

(* Use overloading for a row of beta n k, k = 1 to n. *)
(* val _ = overload_on("beta_horizontal", ``\n. TL (GENLIST (beta n) (n + 1))``); *)
(* use a direct GENLIST rather than tail of a GENLIST *)
val _ = temp_overload_on("beta_horizontal", ``\n. GENLIST (beta n o SUC) n``); (* for temporary overloading *)

(*
> EVAL ``leibniz_horizontal 5``; --> [6; 30; 60; 60; 30; 6]
> EVAL ``beta_horizontal 6``;    --> [6; 30; 60; 60; 30; 6]
*)

(* Theorem: beta_horizontal 0 = [] *)
(* Proof:
     beta_horizontal 0
   = GENLIST (beta 0 o SUC) 0    by notation
   = []                          by GENLIST
*)
val beta_horizontal_0 = store_thm(
  "beta_horizontal_0",
  ``beta_horizontal 0 = []``,
  rw[]);

(* Theorem: LENGTH (beta_horizontal n) = n *)
(* Proof:
     LENGTH (beta_horizontal n)
   = LENGTH (GENLIST (beta n o SUC) n)     by notation
   = n                                     by LENGTH_GENLIST
*)
val beta_horizontal_len = store_thm(
  "beta_horizontal_len",
  ``!n. LENGTH (beta_horizontal n) = n``,
  rw[]);

(* Theorem: beta_horizontal (n + 1) = leibniz_horizontal n *)
(* Proof:
   Note beta_horizontal (n + 1) = GENLIST ((beta (n + 1) o SUC)) (n + 1)   by notation
    and leibniz_horizontal n = GENLIST (leibniz n) (n + 1)          by notation
    Now (beta (n + 1)) o SUC) k
      = beta (n + 1) (k + 1)                              by ADD1
      = leibniz n k                                       by beta_eqn
   Thus beta_horizontal (n + 1) = leibniz_horizontal n    by GENLIST_FUN_EQ
*)
val beta_horizontal_eqn = store_thm(
  "beta_horizontal_eqn",
  ``!n. beta_horizontal (n + 1) = leibniz_horizontal n``,
  rw[GENLIST_FUN_EQ, beta_eqn, ADD1]);

(* Theorem: 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1)) *)
(* Proof: by beta_horizontal_eqn *)
val beta_horizontal_alt = store_thm(
  "beta_horizontal_alt",
  ``!n. 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1))``,
  metis_tac[beta_horizontal_eqn, DECIDE``0 < n ==> (n - 1 + 1 = n)``]);

(* Theorem: 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      ?m. m < n /\ (beta n k = beta n (SUC m))
   Since k <> 0, k = SUC m,
     and SUC m = k <= n ==> m < n     by arithmetic
   So take this m, and the result follows.
*)
val beta_horizontal_mem = store_thm(
  "beta_horizontal_mem",
  ``!n k. 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n)``,
  rpt strip_tac >>
  rw[MEM_GENLIST] >>
  `?m. k = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `m < n` by decide_tac >>
  metis_tac[]);

(* too weak:
binomial_horizontal_mem  |- !n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)
leibniz_horizontal_mem   |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
*)

(* Theorem: MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n /\ (beta n k = beta n (SUC m))) <=> 0 < k /\ k <= n
   If part: (?m. m < n /\ (beta n k = beta n (SUC m))) ==> 0 < k /\ k <= n
      By contradiction, suppose k = 0 \/ n < k
      Note SUC m <> 0 /\ ~(n < SUC m)     by m < n
      Thus beta n (SUC m) <> 0            by beta_eq_0
        or beta n k <> 0                  by beta n k = beta n (SUC m)
       ==> (k <> 0) /\ ~(n < k)           by beta_eq_0
      This contradicts k = 0 \/ n < k.
  Only-if part: 0 < k /\ k <= n ==> ?m. m < n /\ (beta n k = beta n (SUC m))
      Note k <> 0, so ?m. k = SUC m       by num_CASES
       and SUC m <= n <=> m < n           by LESS_EQ
        so Take this m, and the result follows.
*)
val beta_horizontal_mem_iff = store_thm(
  "beta_horizontal_mem_iff",
  ``!n k. MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n``,
  rw[MEM_GENLIST] >>
  rewrite_tac[EQ_IMP_THM] >>
  strip_tac >| [
    spose_not_then strip_assume_tac >>
    `SUC m <> 0 /\ ~(n < SUC m)` by decide_tac >>
    `(k <> 0) /\ ~(n < k)` by metis_tac[beta_eq_0] >>
    decide_tac,
    strip_tac >>
    `?m. k = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
    metis_tac[LESS_EQ]
  ]);

(* Theorem: MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n /\ (x = beta n (SUC m))) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)
   Since 0 < k /\ k <= n <=> ?m. (k = SUC m) /\ m < n  by num_CASES, LESS_EQ
   This is trivially true.
*)
val beta_horizontal_member = store_thm(
  "beta_horizontal_member",
  ``!n x. MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)``,
  rw[MEM_GENLIST] >>
  metis_tac[num_CASES, NOT_ZERO_LT_ZERO, SUC_NOT_ZERO, LESS_EQ]);

(* Theorem: k < n ==> (EL k (beta_horizontal n) = beta n (k + 1)) *)
(* Proof: by EL_GENLIST, ADD1 *)
val beta_horizontal_element = store_thm(
  "beta_horizontal_element",
  ``!n k. k < n ==> (EL k (beta_horizontal n) = beta n (k + 1))``,
  rw[EL_GENLIST, ADD1]);

(* Theorem: 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n)) *)
(* Proof:
   Note n <> 0
    ==> n = SUC k for some k          by num_CASES
     or n = k + 1                     by ADD1
     lcm_run n
   = lcm_run (k + 1)
   = list_lcm (leibniz_horizontal k)  by leibniz_lcm_property
   = list_lcm (beta_horizontal n)     by beta_horizontal_eqn
*)
val lcm_run_by_beta_horizontal = store_thm(
  "lcm_run_by_beta_horizontal",
  ``!n. 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n))``,
  metis_tac[leibniz_lcm_property, beta_horizontal_eqn, num_CASES, ADD1, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < k /\ k <= n ==> (beta n k) divides lcm_run n *)
(* Proof:
   Note 0 < n                                       by 0 < k /\ k <= n
    and MEM (beta n k) (beta_horizontal n)          by beta_horizontal_mem
   also lcm_run n = list_lcm (beta_horizontal n)    by lcm_run_by_beta_horizontal, 0 < n
   Thus (beta n k) divides lcm_run n                by list_lcm_is_common_multiple
*)
val lcm_run_beta_divisor = store_thm(
  "lcm_run_beta_divisor",
  ``!n k. 0 < k /\ k <= n ==> (beta n k) divides lcm_run n``,
  rw[beta_horizontal_mem, lcm_run_by_beta_horizontal, list_lcm_is_common_multiple]);

(* Theorem: k <= m /\ m <= n ==> (beta n k) divides (beta m k) * (binomial n m) *)
(* Proof:
   Note (binomial m k) * (binomial n m)
      = (binomial n k) * (binomial (n - k) (m - k))                  by binomial_product_identity
   Thus binomial n k divides binomial m k * binomial n m             by divides_def, MULT_COMM
    ==> k * binomial n k divides k * (binomial m k * binomial n m)   by DIVIDES_CANCEL_COMM
                              = (k * binomial m k) * binomial n m    by MULT_ASSOC
     or (beta n k) divides (beta m k) * (binomial n m)               by notation
*)
val beta_divides_beta_factor = store_thm(
  "beta_divides_beta_factor",
  ``!m n k. k <= m /\ m <= n ==> (beta n k) divides (beta m k) * (binomial n m)``,
  rw[] >>
  `binomial n k divides binomial m k * binomial n m` by metis_tac[binomial_product_identity, divides_def, MULT_COMM] >>
  metis_tac[DIVIDES_CANCEL_COMM, MULT_ASSOC]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) divides (binomial n m) * (lcm_run m) *)
(* Proof:
   If n = 0,
      Then lcm_run 0 = 1                         by lcm_run_0
      Hence true                                 by ONE_DIVIDES_ALL
   If n <> 0, then 0 < n.
   Let q = (binomial n m) * (lcm_run m)

   Claim: !x. MEM x (beta_horizontal n) ==> x divides q
   Proof: Note MEM x (beta_horizontal n)
           ==> ?k. 0 < k /\ k <= n /\ (x = beta n k)   by beta_horizontal_member
          Here the picture is:
                     HALF n ... m .... n
              0 ........ k ........... n
          We need k <= m to get x divides q.
          For m < k <= n, we shall use symmetry to get x divides q.
          If k <= m,
             Let p = (beta m k) * (binomial n m).
             Then x divides p                    by beta_divides_beta_factor, k <= m, m <= n
              and (beta m k) divides lcm_run m   by lcm_run_beta_divisor, 0 < k /\ k <= m
               so (beta m k) * (binomial n m)
                  divides
                  (lcm_run m) * (binomial n m)   by DIVIDES_CANCEL, binomial_pos
               or p divides q                    by MULT_COMM
             Thus x divides q                    by DIVIDES_TRANS
          If ~(k <= m), then m < k.
             Note x = beta n (n - k + 1)         by beta_sym, k <= n
              Now n <= m + m                     by given
               so n - k + 1 <= m + m + 1 - k     by arithmetic
              and m + m + 1 - k <= m             by m < k
              ==> n - k + 1 <= m                 by arithmetic
              Let h = n - k + 1, p = (beta m h) * (binomial n m).
             Then x divides p                    by beta_divides_beta_factor, h <= m, m <= n
              and (beta m h) divides lcm_run m   by lcm_run_beta_divisor, 0 < h /\ h <= m
               so (beta m h) * (binomial n m)
                  divides
                  (lcm_run m) * (binomial n m)   by DIVIDES_CANCEL, binomial_pos
               or p divides q                    by MULT_COMM
             Thus x divides q                    by DIVIDES_TRANS

   Therefore,
          (list_lcm (beta_horizontal n)) divides q      by list_lcm_is_least_common_multiple, Claim
       or                    (lcm_run n) divides q      by lcm_run_by_beta_horizontal, 0 < n
*)
val lcm_run_divides_property_alt = store_thm(
  "lcm_run_divides_property_alt",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) divides (binomial n m) * (lcm_run m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `q = (binomial n m) * (lcm_run m)` >>
  `!x. MEM x (beta_horizontal n) ==> x divides q` by
  (rpt strip_tac >>
  `?k. 0 < k /\ k <= n /\ (x = beta n k)` by rw[GSYM beta_horizontal_member] >>
  Cases_on `k <= m` >| [
    qabbrev_tac `p = (beta m k) * (binomial n m)` >>
    `x divides p` by rw[beta_divides_beta_factor, Abbr`p`] >>
    `(beta m k) divides lcm_run m` by rw[lcm_run_beta_divisor] >>
    `p divides q` by metis_tac[DIVIDES_CANCEL, MULT_COMM, binomial_pos] >>
    metis_tac[DIVIDES_TRANS],
    `x = beta n (n - k + 1)` by rw[Once beta_sym] >>
    `n - k + 1 <= m` by decide_tac >>
    qabbrev_tac `h = n - k + 1` >>
    qabbrev_tac `p = (beta m h) * (binomial n m)` >>
    `x divides p` by rw[beta_divides_beta_factor, Abbr`p`] >>
    `(beta m h) divides lcm_run m` by rw[lcm_run_beta_divisor, Abbr`h`] >>
    `p divides q` by metis_tac[DIVIDES_CANCEL, MULT_COMM, binomial_pos] >>
    metis_tac[DIVIDES_TRANS]
  ]) >>
  `(list_lcm (beta_horizontal n)) divides q` by metis_tac[list_lcm_is_least_common_multiple] >>
  metis_tac[lcm_run_by_beta_horizontal]);

(* This is the original lcm_run_divides_property to give lcm_run_upper_bound. *)

(* Theorem: lcm_run n <= 4 ** n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Base: n = 0.
         LHS = lcm_run 0 = 1               by lcm_run_0
         RHS = 4 ** 0 = 1                  by EXP
         Hence true.
      Step: n <> 0 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = binomial n m * lcm_run m.
         Then n = 2 * m                    by EVEN_HALF
           so m <= 2 * m = n               by arithmetic
         Note 0 < binomial n m             by binomial_pos, m <= n
          and 0 < lcm_run m                by lcm_run_pos
          ==> 0 < c                        by MULT_EQ_0
         Thus (lcm_run n) divides c        by lcm_run_divides_property, m <= n
           or lcm_run n
           <= c                            by DIVIDES_LE, 0 < c
            = (binomial n m) * lcm_run m   by notation
           <= (binomial n m) * 4 ** m      by induction hypothesis, m < n
           <= 4 ** m * 4 ** m              by binomial_middle_upper_bound
            = 4 ** (m + m)                 by EXP_ADD
            = 4 ** n                       by TIMES2, n = 2 * m
         Hence lcm_run n <= 4 ** n.
   If ~EVEN n,
      Then ODD n                           by EVEN_ODD
      Base: n = 1.
         LHS = lcm_run 1 = 1               by lcm_run_1
         RHS = 4 ** 1 = 4                  by EXP
         Hence true.
      Step: n <> 1 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = binomial n (m + 1) * lcm_run (m + 1).
         Then n = 2 * m + 1                by ODD_HALF
          and 0 < m                        by n <> 1
          and m + 1 <= 2 * m + 1 = n       by arithmetic
          But m + 1 <> n                   by m <> 0
           so m + 1 < n                    by m + 1 <> n
         Note 0 < binomial n (m + 1)       by binomial_pos, m + 1 <= n
          and 0 < lcm_run (m + 1)          by lcm_run_pos
          ==> 0 < c                        by MULT_EQ_0
         Thus (lcm_run n) divides c        by lcm_run_divides_property, 0 < m + 1, m + 1 <= n
           or lcm_run n
           <= c                            by DIVIDES_LE, 0 < c
            = (binomial n (m + 1)) * lcm_run (m + 1)   by notation
           <= (binomial n (m + 1)) * 4 ** (m + 1)      by induction hypothesis, m + 1 < n
            = (binomial n m) * 4 ** (m + 1)            by binomial_sym, n - (m + 1) = m
           <= 4 ** m * 4 ** (m + 1)        by binomial_middle_upper_bound
            = 4 ** (m + (m + 1))           by EXP_ADD
            = 4 ** (2 * m + 1)             by arithmetic
            = 4 ** n                       by n = 2 * m + 1
         Hence lcm_run n <= 4 ** n.
*)
Theorem lcm_run_upper_bound[allow_rebind]:
  !n. lcm_run n <= 4 ** n
Proof
  completeInduct_on `n` >>
  Cases_on `EVEN n` >| [
    Cases_on `n = 0` >-
    rw[lcm_run_0] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    qabbrev_tac `c = binomial n m * lcm_run m` >>
    `m <= n` by decide_tac >>
    `0 < c` by metis_tac[binomial_pos, lcm_run_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
    `lcm_run n <= c` by rw[lcm_run_divides_property, DIVIDES_LE, Abbr`c`] >>
    `lcm_run m <= 4 ** m` by rw[] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** m = 4 ** n` by metis_tac[EXP_ADD, TIMES2] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    Cases_on `n = 1` >-
    rw[lcm_run_1] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    `0 < m` by rw[] >>
    qabbrev_tac `c = binomial n (m + 1) * lcm_run (m + 1)` >>
    `m + 1 <= n` by decide_tac >>
    `0 < c` by metis_tac[binomial_pos, lcm_run_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
    `lcm_run n <= c` by rw[lcm_run_divides_property, DIVIDES_LE, Abbr`c`] >>
    `lcm_run (m + 1) <= 4 ** (m + 1)` by rw[] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** (m + 1)` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** (m + 1) = 4 ** n` by metis_tac[EXP_ADD, ADD_ASSOC, TIMES2] >>
    decide_tac
  ]
QED

(* This is the original proof of the upper bound. *)

(* ------------------------------------------------------------------------- *)
(* LCM Lower Bound using Maximum                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: POSITIVE l ==> MAX_LIST l <= list_lcm l *)
(* Proof:
   If l = [],
      Note MAX_LIST [] = 0          by MAX_LIST_NIL
       and list_lcm [] = 1          by list_lcm_nil
      Hence true.
   If l <> [],
      Let x = MAX_LIST l.
      Then MEM x l                  by MAX_LIST_MEM
       and x divides (list_lcm l)   by list_lcm_is_common_multiple
       Now 0 < list_lcm l           by list_lcm_pos, EVERY_MEM
        so x <= list_lcm l          by DIVIDES_LE, 0 < list_lcm l
*)
val list_lcm_ge_max = store_thm(
  "list_lcm_ge_max",
  ``!l. POSITIVE l ==> MAX_LIST l <= list_lcm l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[MAX_LIST_NIL, list_lcm_nil] >>
  `MEM (MAX_LIST l) l` by rw[MAX_LIST_MEM] >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  rw[list_lcm_is_common_multiple, DIVIDES_LE]);

(* Theorem: (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)] *)
(* Proof:
   Note !k. MEM k (binomial_horizontal n) ==> 0 < k by binomial_horizontal_pos_alt [1]

    list_lcm [1 .. (n + 1)]
  = list_lcm (leibniz_vertical n)                by notation
  = list_lcm (leibniz_horizontal n)              by leibniz_lcm_property
  = (n + 1) * list_lcm (binomial_horizontal n)   by leibniz_horizontal_lcm_alt
  >= (n + 1) * MAX_LIST (binomial_horizontal n)  by list_lcm_ge_max, [1], LE_MULT_LCANCEL
  = (n + 1) * binomial n (HALF n)                by binomial_horizontal_max
*)
val lcm_lower_bound_by_list_lcm = store_thm(
  "lcm_lower_bound_by_list_lcm",
  ``!n. (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)]``,
  rpt strip_tac >>
  `MAX_LIST (binomial_horizontal n) <= list_lcm (binomial_horizontal n)` by
  (irule list_lcm_ge_max >>
  metis_tac[binomial_horizontal_pos_alt]) >>
  `list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)` by rw[leibniz_lcm_property] >>
  `_ = (n + 1) * list_lcm (binomial_horizontal n)` by rw[leibniz_horizontal_lcm_alt] >>
  `n + 1 <> 0` by decide_tac >>
  metis_tac[LE_MULT_LCANCEL, binomial_horizontal_max]);

(* Theorem: FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s *)
(* Proof:
   If s = {},
      Note MAX_SET {} = 0          by MAX_SET_EMPTY
       and big_lcm {} = 1          by big_lcm_empty
      Hence true.
   If s <> {},
      Let x = MAX_SET s.
      Then x IN s                  by MAX_SET_IN_SET
       and x divides (big_lcm s)   by big_lcm_is_common_multiple
       Now 0 < big_lcm s           by big_lcm_positive
        so x <= big_lcm s          by DIVIDES_LE, 0 < big_lcm s
*)
val big_lcm_ge_max = store_thm(
  "big_lcm_ge_max",
  ``!s. FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s``,
  rpt strip_tac >>
  Cases_on `s = {}` >-
  rw[MAX_SET_EMPTY, big_lcm_empty] >>
  `(MAX_SET s) IN s` by rw[MAX_SET_IN_SET] >>
  `0 < big_lcm s` by rw[big_lcm_positive] >>
  rw[big_lcm_is_common_multiple, DIVIDES_LE]);

(* Theorem: (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1)) *)
(* Proof:
   Claim: MAX_SET (IMAGE (binomial n) (count (n + 1))) <= big_lcm (IMAGE (binomial n) count (n + 1))
   Proof: By big_lcm_ge_max, this is to show:
          (1) FINITE (IMAGE (binomial n) (count (n + 1)))
              This is true                                    by FINITE_COUNT, IMAGE_FINITE
          (2) !x. x IN IMAGE (binomial n) (count (n + 1)) ==> 0 < x
              This is true                                    by binomial_pos, IN_IMAGE, IN_COUNT

     big_lcm (natural (n + 1))
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))   by big_lcm_natural_eqn
   >= (n + 1) * MAX_SET (IMAGE (binomial n) (count (n + 1)))  by claim, LE_MULT_LCANCEL
   = (n + 1) * binomial n (HALF n)                            by binomial_row_max
*)
val lcm_lower_bound_by_big_lcm = store_thm(
  "lcm_lower_bound_by_big_lcm",
  ``!n. (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `MAX_SET (IMAGE (binomial n) (count (n + 1))) <=
       big_lcm (IMAGE (binomial n) (count (n + 1)))` by
  ((irule big_lcm_ge_max >> rpt conj_tac) >-
  metis_tac[binomial_pos, IN_IMAGE, IN_COUNT, DECIDE``x < n + 1 ==> x <= n``] >>
  rw[]
  ) >>
  metis_tac[big_lcm_natural_eqn, LE_MULT_LCANCEL, binomial_row_max, DECIDE``n + 1 <> 0``]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM function                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
            !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n] *)
(* Proof:
   Note ODD n ==> n <> 0                  by EVEN_0, EVEN_ODD
   If n = 1,
      Note 1 <= pi                        by 0 < pi
        so 2 <= 2 * pi                    by LE_MULT_LCANCEL, 2 <> 0
        or 1 < 2 * pi                     by arithmetic
      Thus 1 DIV (2 * pi) = 0             by ONE_DIV, 1 < 2 * pi
       and SQRT (1 DIV (2 * pi)) = 0      by ZERO_EXP, 0 ** h, h <> 0
       But list_lcm [1 .. 1] = 1          by list_lcm_sing
        so SQRT (1 DIV (2 * pi)) * 2 ** 1 <= list_lcm [1 .. 1]    by MULT
   If n <> 1,
      Then 0 < n - 1.
      Let m = n - 1, then n = m + 1       by arithmetic
      and n * binomial m (HALF m) <= list_lcm [1 .. n]   by lcm_lower_bound_by_list_lcm
      Now !a b c. (a DIV b) * c = (a * c) DIV b          by DIV_1, MULT_RIGHT_1, c = c DIV 1, b * 1 = b
      Note ODD n ==> EVEN m               by EVEN_ODD_SUC, ADD1
           n * binomial m (HALF m)
         = n * (2 ** n DIV SQRT (2 * pi * m))     by binomial_middle_by_stirling
         = (2 ** n DIV SQRT (2 * pi * m)) * n     by MULT_COMM
         = (2 ** n * n) DIV (SQRT (2 * pi * m))   by above
         = (n * 2 ** n) DIV (SQRT (2 * pi * m))   by MULT_COMM
         = (n DIV SQRT (2 * pi * m)) * 2 ** n     by above
         = (SQRT (n DIV (2 * pi)) * 2 ** n        by assumption, m = n - 1
      Hence SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n]
*)
val lcm_lower_bound_by_list_lcm_stirling = store_thm(
  "lcm_lower_bound_by_list_lcm_stirling",
  ``Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
   !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n]``,
  rpt strip_tac >>
  `!n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))` by prove_tac[binomial_middle_by_stirling] >>
  `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
  Cases_on `n = 1` >| [
    `1 <= pi` by decide_tac >>
    `1 < 2 * pi` by decide_tac >>
    `1 DIV (2 * pi) = 0` by rw[ONE_DIV] >>
    `SQRT (1 DIV (2 * pi)) * 2 ** 1 = 0` by rw[] >>
    rw[list_lcm_sing],
    `0 < n - 1 /\ (n = (n - 1) + 1)` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `n * binomial m (HALF m) <= list_lcm [1 .. n]` by metis_tac[lcm_lower_bound_by_list_lcm] >>
    `EVEN m` by metis_tac[EVEN_ODD_SUC, ADD1] >>
    `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
    `n * binomial m (HALF m) = n * (2 ** n DIV SQRT (2 * pi * m))` by rw[] >>
    `_ = (n DIV SQRT (2 * pi * m)) * 2 ** n` by metis_tac[MULT_COMM] >>
    metis_tac[]
  ]);

(* Theorem: big_lcm (natural n) <= big_lcm (natural (n + 1)) *)
(* Proof:
   Note FINITE (natural n)                    by natural_finite
    and 0 < big_lcm (natural n)               by big_lcm_positive, natural_element
       big_lcm (natural n)
    <= lcm (SUC n) (big_lcm (natural n))      by LCM_LE, 0 < SUC n, 0 < big_lcm (natural n)
     = big_lcm ((SUC n) INSERT (natural n))   by big_lcm_insert
     = big_lcm (natural (SUC n))              by natural_suc
     = big_lcm (natural (n + 1))              by ADD1
*)
val big_lcm_non_decreasing = store_thm(
  "big_lcm_non_decreasing",
  ``!n. big_lcm (natural n) <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `0 < big_lcm (natural n)` by rw[big_lcm_positive, natural_element] >>
  `big_lcm (natural (n + 1)) = big_lcm (natural (SUC n))` by rw[ADD1] >>
  `_ = big_lcm ((SUC n) INSERT (natural n))` by rw[natural_suc] >>
  `_ = lcm (SUC n) (big_lcm (natural n))` by rw[big_lcm_insert] >>
  rw[LCM_LE]);

(* Theorem: Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
            !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n) *)
(* Proof:
   Note ODD n ==> n <> 0                  by EVEN_0, EVEN_ODD
   If n = 1,
      Note 1 <= pi                        by 0 < pi
        so 2 <= 2 * pi                    by LE_MULT_LCANCEL, 2 <> 0
        or 1 < 2 * pi                     by arithmetic
      Thus 1 DIV (2 * pi) = 0             by ONE_DIV, 1 < 2 * pi
       and SQRT (1 DIV (2 * pi)) = 0      by ZERO_EXP, 0 ** h, h <> 0
       But big_lcm (natural 1) = 1        by list_lcm_sing, natural_1
        so SQRT (1 DIV (2 * pi)) * 2 ** 1 <= big_lcm (natural 1)    by MULT
   If n <> 1,
      Then 0 < n - 1.
      Let m = n - 1, then n = m + 1       by arithmetic
      and n * binomial m (HALF m) <= big_lcm (natural n)   by lcm_lower_bound_by_big_lcm
      Now !a b c. (a DIV b) * c = (a * c) DIV b            by DIV_1, MULT_RIGHT_1, c = c DIV 1, b * 1 = b
      Note ODD n ==> EVEN m               by EVEN_ODD_SUC, ADD1
           n * binomial m (HALF m)
         = n * (2 ** n DIV SQRT (2 * pi * m))     by binomial_middle_by_stirling
         = (2 ** n DIV SQRT (2 * pi * m)) * n     by MULT_COMM
         = (2 ** n * n) DIV (SQRT (2 * pi * m))   by above
         = (n * 2 ** n) DIV (SQRT (2 * pi * m))   by MULT_COMM
         = (n DIV SQRT (2 * pi * m)) * 2 ** n     by above
         = (SQRT (n DIV (2 * pi)) * 2 ** n        by assumption, m = n - 1
      Hence SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n)
*)
val lcm_lower_bound_by_big_lcm_stirling = store_thm(
  "lcm_lower_bound_by_big_lcm_stirling",
  ``Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
   !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n)``,
  rpt strip_tac >>
  `!n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))` by prove_tac[binomial_middle_by_stirling] >>
  `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
  Cases_on `n = 1` >| [
    `1 <= pi` by decide_tac >>
    `1 < 2 * pi` by decide_tac >>
    `1 DIV (2 * pi) = 0` by rw[ONE_DIV] >>
    `SQRT (1 DIV (2 * pi)) * 2 ** 1 = 0` by rw[] >>
    rw[big_lcm_sing],
    `0 < n - 1 /\ (n = (n - 1) + 1)` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `n * binomial m (HALF m) <= big_lcm (natural n)` by metis_tac[lcm_lower_bound_by_big_lcm] >>
    `EVEN m` by metis_tac[EVEN_ODD_SUC, ADD1] >>
    `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
    `n * binomial m (HALF m) = n * (2 ** n DIV SQRT (2 * pi * m))` by rw[] >>
    `_ = (n DIV SQRT (2 * pi * m)) * 2 ** n` by metis_tac[MULT_COMM] >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Extra Theorems (not used)                                                 *)
(* ------------------------------------------------------------------------- *)

(*
This is GCD_CANCEL_MULT by coprime p n, and coprime p n ==> coprime (p ** k) n by coprime_exp.
Note prime_not_divides_coprime.
*)

(* Theorem: prime p /\ m divides n /\ ~((p * m) divides n) ==> (gcd (p * m) n = m) *)
(* Proof:
   Note m divides n ==> ?q. n = q * m     by divides_def

   Claim: coprime p q
   Proof: By contradiction, suppose gcd p q <> 1.
          Since (gcd p q) divides p       by GCD_IS_GREATEST_COMMON_DIVISOR
             so gcd p q = p               by prime_def, gcd p q <> 1.
             or p divides q               by divides_iff_gcd_fix
          Now, m <> 0 because
               If m = 0, p * m = 0        by MULT_0
               Then m divides n and ~((p * m) divides n) are contradictory.
          Thus p * m divides q * m        by DIVIDES_MULTIPLE_IFF, MULT_COMM, p divides q, m <> 0
          But q * m = n, contradicting ~((p * m) divides n).

      gcd (p * m) n
    = gcd (p * m) (q * m)                 by n = q * m
    = m * gcd p q                         by GCD_COMMON_FACTOR, MULT_COMM
    = m * 1                               by coprime p q, from Claim
    = m
*)
val gcd_prime_product_property = store_thm(
  "gcd_prime_product_property",
  ``!p m n. prime p /\ m divides n /\ ~((p * m) divides n) ==> (gcd (p * m) n = m)``,
  rpt strip_tac >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `m <> 0` by metis_tac[MULT_0] >>
  `coprime p q` by
  (spose_not_then strip_assume_tac >>
  `(gcd p q) divides p` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  `gcd p q = p` by metis_tac[prime_def] >>
  `p divides q` by rw[divides_iff_gcd_fix] >>
  metis_tac[DIVIDES_MULTIPLE_IFF, MULT_COMM]) >>
  metis_tac[GCD_COMMON_FACTOR, MULT_COMM, MULT_RIGHT_1]);

(* Theorem: prime p /\ m divides n /\ ~((p * m) divides n) ==>(lcm (p * m) n = p * n) *)
(* Proof:
   Note m <> 0                             by MULT_0, m divides n /\ ~((p * m) divides n)
   and   m * lcm (p * m) n
       = gcd (p * m) n * lcm (p * m) n     by gcd_prime_product_property
       = (p * m) * n                       by GCD_LCM
       = (m * p) * n                       by MULT_COMM
       = m * (p * n)                       by MULT_ASSOC
   Thus   lcm (p * m) n = p * n            by MULT_LEFT_CANCEL
*)
val lcm_prime_product_property = store_thm(
  "lcm_prime_product_property",
  ``!p m n. prime p /\ m divides n /\ ~((p * m) divides n) ==>(lcm (p * m) n = p * n)``,
  rpt strip_tac >>
  `m <> 0` by metis_tac[MULT_0] >>
  `m * lcm (p * m) n = gcd (p * m) n * lcm (p * m) n` by rw[gcd_prime_product_property] >>
  `_ = (p * m) * n` by rw[GCD_LCM] >>
  `_ = m * (p * n)` by metis_tac[MULT_COMM, MULT_ASSOC] >>
  metis_tac[MULT_LEFT_CANCEL]);

(* Theorem: prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l) *)
(* Proof:
   By induction on l.
   Base: prime p /\ p divides list_lcm [] ==> p divides PROD_SET (set [])
      Note list_lcm [] = 1                  by list_lcm_nil
       and PROD_SET (set [])
         = PROD_SET {}                      by LIST_TO_SET
         = 1                                by PROD_SET_EMPTY
      Hence conclusion is alredy in predicate, thus true.
   Step: prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l) ==>
         prime p /\ p divides list_lcm (h::l) ==> p divides PROD_SET (set (h::l))
      Note PROD_SET (set (h::l))
         = PROD_SET (h INSERT set l)        by LIST_TO_SET
      This is to show: p divides PROD_SET (h INSERT set l)

      Let x = list_lcm l.
      Since p divides (lcm h x)             by given
         so p divides (gcd h x) * (lcm h x) by DIVIDES_MULTIPLE
         or p divides h * x                 by GCD_LCM
        ==> p divides h  or  p divides x    by P_EUCLIDES
      Case: p divides h.
      If h IN set l, or MEM h l,
         Then h divides x                                       by list_lcm_is_common_multiple
           so p divides x                                       by DIVIDES_TRANS
         Thus p divides PROD_SET (set l)                        by induction hypothesis
           or p divides PROD_SET (h INSERT set l)               by ABSORPTION
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)  by PROD_SET_INSERT
           or p divides PROD_SET (h INSERT set l)               by DIVIDES_MULTIPLE, MULT_COMM
      Case: p divides x.
      If h IN set l, or MEM h l,
         Then p divides PROD_SET (set l)                        by induction hypothesis
           or p divides PROD_SET (h INSERT set l)               by ABSORPTION
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)  by PROD_SET_INSERT
           or p divides PROD_SET (h INSERT set l)               by DIVIDES_MULTIPLE
*)
val list_lcm_prime_factor = store_thm(
  "list_lcm_prime_factor",
  ``!p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[] >>
  qabbrev_tac `x = list_lcm l` >>
  `(gcd h x) * (lcm h x) = h * x` by rw[GCD_LCM] >>
  `p divides (h * x)` by metis_tac[DIVIDES_MULTIPLE] >>
  `p divides h \/ p divides x` by rw[P_EUCLIDES] >| [
    Cases_on `h IN set l` >| [
      `h divides x` by rw[list_lcm_is_common_multiple, Abbr`x`] >>
      `p divides x` by metis_tac[DIVIDES_TRANS] >>
      fs[ABSORPTION],
      rw[PROD_SET_INSERT] >>
      metis_tac[DIVIDES_MULTIPLE, MULT_COMM]
    ],
    Cases_on `h IN set l` >-
    fs[ABSORPTION] >>
    rw[PROD_SET_INSERT] >>
    metis_tac[DIVIDES_MULTIPLE]
  ]);

(* Theorem: prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x *)
(* Proof:
   By induction on l.
   Base: prime p /\ p divides PROD_SET (set []) ==> ?x. MEM x [] /\ p divides x
          p divides PROD_SET (set [])
      ==> p divides PROD_SET {}            by LIST_TO_SET
      ==> p divides 1                      by PROD_SET_EMPTY
      ==> p = 1                            by DIVIDES_ONE
      This contradicts with 1 < p          by ONE_LT_PRIME
   Step: prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x ==>
         !h. prime p /\ p divides PROD_SET (set (h::l)) ==> ?x. MEM x (h::l) /\ p divides x
      Note PROD_SET (set (h::l))
         = PROD_SET (h INSERT set l)                              by LIST_TO_SET
      This is to show: ?x. ((x = h) \/ MEM x l) /\ p divides x    by MEM
      If h IN set l, or MEM h l,
         Then h INSERT set l = set l                              by ABSORPTION
         Thus ?x. MEM x l /\ p divides x                          by induction hypothesis
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)    by PROD_SET_INSERT
         Thus p divides h \/ p divides (PROD_SET (set l))         by P_EUCLIDES
         Case p divides h.
              Take x = h, the result is true.
         Case p divides PROD_SET (set l).
              Then ?x. MEM x l /\ p divides x                     by induction hypothesis
*)
val list_product_prime_factor = store_thm(
  "list_product_prime_factor",
  ``!p l. prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x``,
  strip_tac >>
  Induct >| [
    rpt strip_tac >>
    `PROD_SET (set []) = 1` by rw[PROD_SET_EMPTY] >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> 1` by decide_tac >>
    metis_tac[DIVIDES_ONE],
    rw[] >>
    Cases_on `h IN set l` >-
    metis_tac[ABSORPTION] >>
    fs[PROD_SET_INSERT] >>
    `p divides h \/ p divides (PROD_SET (set l))` by rw[P_EUCLIDES] >-
    metis_tac[] >>
    metis_tac[]
  ]);

(* Theorem: prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x *)
(* Proof: by list_lcm_prime_factor, list_product_prime_factor *)
val list_lcm_prime_factor_member = store_thm(
  "list_lcm_prime_factor_member",
  ``!p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x``,
  rw[list_lcm_prime_factor, list_product_prime_factor]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
