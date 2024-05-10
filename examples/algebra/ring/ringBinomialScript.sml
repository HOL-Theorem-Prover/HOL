(* ------------------------------------------------------------------------- *)
(* Binomial coefficients and expansion, for Ring                             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringBinomial";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory;

open ringTheory;
open groupTheory;
open monoidTheory;
open groupMapTheory ringMapTheory;

(* ------------------------------------------------------------------------- *)
(* Ring Binomial Documentation                                               *)
(* ------------------------------------------------------------------------- *)
(*
   Overloading:
   rlist    = ring_list r
   rsum     = ring_sum r
   rfun     = ring_fun r
*)
(* Definitions and Theorems (# are exported):

   List from elements in Ring:
#  ring_list_def         |- (!r. rlist [] <=> T) /\ !r h t. rlist (h::t) <=> h IN R /\ rlist t
   ring_list_nil         |- !r. rlist [] <=> T
   ring_list_cons        |- !r h t. rlist (h::t) <=> h IN R /\ rlist t
   ring_list_front_last  |- !s. rlist (FRONT s) /\ LAST s IN R ==> rlist s
   ring_list_SNOC        |- !x s. rlist (SNOC x s) <=> x IN R /\ rlist s

   Summation in Ring:
#  ring_sum_def      |- (!r. rsum [] = #0) /\ !r h t. rsum (h::t) = h + rsum t
   ring_sum_nil      |- !r. rsum [] = #0
   ring_sum_cons     |- !r h t. rsum (h::t) = h + rsum t
#  ring_sum_element  |- !r. Ring r ==> !s. rlist s ==> rsum s IN R
   ring_sum_sing     |- !r. Ring r ==> !x. x IN R ==> (rsum [x] = x)
   ring_sum_append   |- !r. Ring r ==> !s t. rlist s /\ rlist t ==> (rsum (s ++ t) = rsum s + rsum t)
   ring_sum_mult     |- !r. Ring r ==> !k s. k IN R /\ rlist s ==> (k * rsum s = rsum (MAP (\x. k * x) s))
   ring_sum_mult_ladd  |- !r. Ring r ==> !m n s. m IN R /\ n IN R /\ rlist s ==>
                          ((m + n) * rsum s = rsum (MAP (\x. m * x) s) + rsum (MAP (\x. n * x) s))
   ring_sum_SNOC     |- !r. Ring r ==> !k s. k IN R /\ rlist s ==> (rsum (SNOC k s) = rsum s + k)

   Function giving elements in Ring:
#  ring_fun_def     |- !r f. rfun f <=> !x. f x IN R
   ring_fun_add     |- !r. Ring r ==> !a b. rfun a /\ rfun b ==> rfun (\k. a k + b k)
   ring_fun_genlist |- !f. rfun f ==> !n. rlist (GENLIST f n)
   ring_fun_map     |- !f l. rfun f ==> rlist (MAP f l)
   ring_fun_from_ring_fun      |- !r. Ring r ==> !f. rfun f ==> !x. x IN R ==> rfun (\j. f j * x ** j)
   ring_fun_from_ring_fun_exp  |- !r. Ring r ==> !f. rfun f ==> !x. x IN R ==>
                                  !n. rfun (\j. (f j * x ** j) ** n)
   ring_list_gen_from_ring_fun |- !r. Ring r ==> !f. rfun f ==> !x. x IN R ==>
                                  !n. rlist (GENLIST (\j. f j * x ** j) n)
   ring_list_from_genlist_ring_fun   |- !r f. rfun f ==> !n g. rlist (GENLIST (f o g) n)
   ring_list_from_genlist            |- !r f. rfun f ==> !n. rlist (GENLIST f n)

   Ring Sum Involving GENLIST:
   ring_sum_fun_zero           |- !r. Ring r ==> !f. rfun f ==> !n. (!k. 0 < k /\ k < n ==>
                                  (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE n))) = #0)

   ring_sum_decompose_first |- !r f n. rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) n)
   ring_sum_decompose_last  |- !r. Ring r ==> !f n. rfun f ==> (rsum (GENLIST f (SUC n)) = rsum (GENLIST f n) + f n)
   ring_sum_decompose_first_last  |- !r. Ring r ==> !f n. rfun f /\ 0 < n ==>
                                    (rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) (PRE n)) + f n)
   ring_sum_genlist_add       |- !r. Ring r ==> !a b. rfun a /\ rfun b ==>
                              !n. rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)
   ring_sum_genlist_append    |- !r. Ring r ==> !a b. rfun a /\ rfun b ==>
                              !n. rsum (GENLIST a n ++ GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)
   ring_sum_genlist_sum     |- !r. Ring r ==> !f. rfun f ==>
                     !n m. rsum (GENLIST f (n + m)) = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n)
   ring_sum_genlist_const   |- !r. Ring r ==> !x. x IN R ==> !n. rsum (GENLIST (K x) n) = ##n * x

   Ring Binomial Theorem:
   ring_binomial_genlist_index_shift  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                            !n. GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n =
                                GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** SUC k) n
   ring_binomial_index_shift  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                              !n. (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) o SUC =
                                  (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** SUC k)
   ring_binomial_term_merge_x |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
     !n. (\k. x * k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k)
   ring_binomial_term_merge_y |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
     !n. (\k. y * k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (n - k) * y ** SUC k)
   ring_binomial_thm          |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
     !n. (x + y) ** n = rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))

   Ring with prime characteristic:
   ring_char_prime        |- !r. Ring r ==> (prime (char r) <=>
                             1 < char r /\ !k. 0 < k /\ k < char r ==> (##(binomial (char r) k) = #0))
   ring_freshman_thm      |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             ((x + y) ** char r = x ** char r + y ** char r)
   ring_freshman_all      |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             !n. (x + y) ** char r ** n = x ** char r ** n + y ** char r ** n
   ring_freshman_thm_sub  |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             ((x - y) ** char r = x ** char r - y ** char r)
   ring_freshman_all_sub  |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             !n. (x - y) ** char r ** n = x ** char r ** n - y ** char r ** n
   ring_fermat_thm        |- !r. Ring r /\ prime (char r) ==> !n. (##n) ** (char r) = (##n)
   ring_fermat_all        |- !r. Ring r /\ prime (char r) ==> !n k. ##n ** char r ** k = ##n
   ring_sum_freshman_thm  |- !r. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
                             !n. rsum (GENLIST (\j. f j * x ** j) n) ** char r =
                                 rsum (GENLIST (\j. (f j * x ** j) ** char r) n)
   ring_sum_freshman_all  |- !r. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
                             !n k. rsum (GENLIST (\j. f j * x ** j) n) ** char r ** k =
                                   rsum (GENLIST (\j. (f j * x ** j) ** char r ** k) n)
   ring_char_prime_endo   |- !r. Ring r /\ prime (char r) ==> RingEndo (\x. x ** char r) r
*)

(*
binomial_thm:
!n x y. (x + y)**n = rsum (GENLIST (\k. (binomial n k)* x**(n-k) * y**k) (SUC n))
*)

(* ------------------------------------------------------------------------- *)
(* List from elements in Ring                                                *)
(* ------------------------------------------------------------------------- *)

(* Ring element list. *)
val ring_list_def = Define`
  (ring_list (r:'a ring) [] <=> T) /\
  (ring_list (r:'a ring) ((h:'a)::(t:'a list)) <=> h IN R /\ (ring_list r t))
`;
val _ = overload_on ("rlist", ``ring_list r``);

(* export simple definition. *)
val _ = export_rewrites ["ring_list_def"];

(* Theorem: rlist [] <=> T *)
val ring_list_nil = save_thm("ring_list_nil", ring_list_def |> CONJUNCT1);
(* > val ring_list_nil = |- !r. rlist [] <=> T : thm *)

(* Theorem: rlist (h::t) <=> h IN R /\ rlist t *)
val ring_list_cons = save_thm("ring_list_cons", ring_list_def |> CONJUNCT2);
(* > val ring_list_cons = |- !r h t. rlist (h::t) <=> h IN R /\ rlist t : thm *)


(* Theorem: rlist (FRONT l) /\ LAST l IN R ==> rlist l *)
(* Proof: by induction on s.
   Base case: rlist (FRONT []) ==> LAST [] IN R ==> rlist []
     true since rlist []   by ring_list_nil.
   Step case: rlist (FRONT s) ==> LAST s IN R ==> rlist s ==>
              !h. rlist (FRONT (h::s)) ==> LAST (h::s) IN R ==> rlist (h::s)
     If s = [],
        FRONT (h::[]) = [], LAST (h::[]) = h,   by FRONT_CONS and LAST_CONS,
        hence rlist [] /\ h IN R, hence rlist (h::[])  by ring_list_cons.
     If s <> [], s = h'::t
        FRONT (h::s) = h::FRONT s, LAST (h::s) = LAST s, by FRONT_CONS and LAST_CONS,
        hence rlist (h::FRONT s) /\ LAST s IN R,
           or h IN R /\ rlist (FRONT s) /\ LAST s IN R   by ring_list_cons
           or h IN R /\ rlist s                          by induction hypothesis
           hence rlist (h::s)                            by ring_list_cons
*)
val ring_list_front_last = store_thm(
  "ring_list_front_last",
  ``!s. rlist (FRONT s) /\ LAST s IN R ==> rlist s``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  metis_tac[FRONT_CONS, LAST_CONS, ring_list_def, list_CASES]);

(* Theorem: !x s. rlist (SNOC x s) <=> x IN R /\ rlist s *)
(* Proof:
   By induction on s.
   Base case: rlist (SNOC x []) <=> x IN R /\ rlist []
          rlist (SNOC x [])
      <=> rlist [x]           by SNOC
      <=> x IN R /\ rlist []  by ring_list_cons
   Step case: rlist (SNOC x s) <=> x IN R /\ rlist s ==>
              !h. rlist (SNOC x (h::s)) <=> x IN R /\ rlist (h::s)
          rlist (SNOC x (h::s))
      <=> rlist (h::SONC x s)          by SNOC
      <=> h IN R /\ rlist (SNOC x s)   by ring_list_cons
      <=> h IN R /\ x IN R /\ rlist s  by induction hypothesis
      <=> x IN R /\ rlist (h::s)       by ring_list_cons
*)
val ring_list_SNOC = store_thm(
  "ring_list_SNOC",
  ``!x s. rlist (SNOC x s) <=> x IN R /\ rlist s``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Summation in Ring                                                         *)
(* ------------------------------------------------------------------------- *)

(* Summation in a Ring. *)
val ring_sum_def = Define`
  (ring_sum (r:'a ring) [] = #0) /\
  (ring_sum (r:'a ring) ((h:'a)::(t:'a list)) = h + (ring_sum r t))
`;
val _ = overload_on ("rsum", ``ring_sum r``);

(* export simple definition. *)
val _ = export_rewrites ["ring_sum_def"];

(* Theorem: rsum [] = #0 *)
val ring_sum_nil = save_thm("ring_sum_nil", ring_sum_def |> CONJUNCT1);
(* > val ring_sum_nil = |- !r. rsum [] = #0 : thm *)

(* Theorem: rsum (h::t)= h + rsum t *)
val ring_sum_cons = save_thm("ring_sum_cons", ring_sum_def |> CONJUNCT2);
(* > val ring_sum_cons = |- !r h t. rsum (h::t) = h + rsum t : thm *)

(* Theorem: rsum s IN R *)
(* Proof: by induction on s.
   Base case: rlist [] ==> rsum [] IN R
      true by ring_sum_nil, ring_zero_element.
   Step case: rlist s ==> rsum s IN R ==> !h. rlist (h::s) ==> rsum (h::s) IN R
      rlist (h::s) ==> h IN R /\ rlist s      by ring_list_cons
      since  ring_sum(h::s) = h + rsum s      by ring_sum_cons
      with h IN R and rlist s ==> rsum s IN R by induction hypothesis
      true by ring_add_element
*)
val ring_sum_element = store_thm(
  "ring_sum_element",
  ``!r:'a ring. Ring r ==> !s. rlist s ==> rsum s IN R``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

val _ = export_rewrites ["ring_sum_element"];

(* Theorem: rsum [x] = x *)
(* Proof:
     rsum [x]
   = x + rsum []    by ring_sum_cons
   = x + #0         by ring_sum_nil
   = x              by ring_add_rzero
*)
val ring_sum_sing = store_thm(
  "ring_sum_sing",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (rsum [x] = x)``,
  rw[]);

(* Theorem: rsum (s ++ t) = rsum s + rsum t *)
(* Proof: by induction on s
   Base case: rlist [] ==> (rsum ([] ++ t) = rsum [] + rsum t)
     rsum ([] ++ t)
   = rsum t                   by APPEND
   = #0 + rsum t              by ring_add_lzero
   = rsum [] + rsum t   by ring_sum_nil
   Step case: rlist s /\ rlist t ==> (rsum (s ++ t) = rsum s + rsum t) ==>
              rlist (h::s) ==> (rsum (h::s ++ t) = rsum (h::s) + rsum t)
     rsum (h::s ++ t)
   = rsum (h::(s ++ t))       by APPEND
   = h + rsum (s ++ t)        by ring_sum_cons, h IN R by ring_list_cons
   = h + (rsum s + rsum t)    by induction hypothesis
   = (h + rsum s) + rsum t    by ring_add_assoc
   = rsum (h::s) + rsum t     by ring_sum_cons
*)
val ring_sum_append = store_thm(
  "ring_sum_append",
  ``!r:'a ring. Ring r ==> !s t. rlist s /\ rlist t ==> (rsum (s ++ t) = rsum s + rsum t)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[ring_add_assoc]);

(* Theorem: constant multiplication: k * rsum s = rsum (MAP (\x. k*x) s))  *)
(* Proof: by induction on s
   Base case: k * rsum [] = rsum (MAP (\x. k * x) [])
   LHS = k * rsum []
       = k * #0          by ring_sum_nil
       = #0              by ring_mult_rzero
   RHS = rsum (MAP (\x. k * x) [])
       = rsum []         by MAP
       = #0              by ring_sum_nil
       = LHS
   Step case: rlist s ==> (k * rsum s = rsum (MAP (\x. k * x) s)) ==>
              !h. rlist (h::s) ==> (k * rsum (h::s) = rsum (MAP (\x. k * x) (h::s)))
   LHS = k * rsum (h::s)
       = k * (h + rsum s)     by ring_sum_cons
       = k * h + k * rsum s   by ring_mult_radd
       = k * h + rsum (MAP (\x. k * x) s)   by induction hypothesis
   RHS = rsum (MAP (\x. k * x) (h::s))
       = rsum ((\x. k * x) h :: MAP (\x. k * x) s)  by MAP
       = (\x. k * x) h + rsum (MAP (\x. k * x) s)   by ring_sum_cons
       = k * h + rsum (MAP (\x. k * x) s
       = LHS
*)
val ring_sum_mult = store_thm(
  "ring_sum_mult",
  ``!r:'a ring. Ring r ==> !k s. k IN R /\ rlist s ==> (k * rsum s = rsum (MAP (\x. k*x) s))``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: (m+n) * rsum s = rsum (MAP (\x. m*x) s) + rsum (MAP (\x. n*x) s)  *)
(* Proof:
    (m + n) * rsum s
  = m * rsum s + n * rsum s                          by ring_mult_ladd
  = rsum (MAP (\x. m*x) s) + rsum (MAP (\x. n*x) s)  by ring_sum_mult
*)
val ring_sum_mult_ladd = store_thm(
  "ring_sum_mult_ladd",
  ``!r:'a ring. Ring r ==> !m n s. m IN R /\ n IN R /\ rlist s ==>
       ((m + n) * rsum s = rsum (MAP (\x. m*x) s) + rsum (MAP (\x. n*x) s))``,
  rw[ring_sum_mult, ring_mult_ladd]);

(*
- EVAL ``GENLIST I 4``;
> val it = |- GENLIST I 4 = [0; 1; 2; 3] : thm
- EVAL ``GENLIST SUC 4``;
> val it = |- GENLIST SUC 4 = [1; 2; 3; 4] : thm
- EVAL ``GENLIST (\k. binomial 4 k) 5``;
> val it = |- GENLIST (\k. binomial 4 k) 5 = [1; 4; 6; 4; 1] : thm
- EVAL ``GENLIST (\k. binomial 5 k) 6``;
> val it = |- GENLIST (\k. binomial 5 k) 6 = [1; 5; 10; 10; 5; 1] : thm
- EVAL ``GENLIST (\k. binomial 10 k) 11``;
> val it = |- GENLIST (\k. binomial 10 k) 11 = [1; 10; 45; 120; 210; 252; 210; 120; 45; 10; 1] : thm
*)

(* Theorems on GENLIST:

- GENLIST;
> val it = |- (!f. GENLIST f 0 = []) /\
               !f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) : thm
- NULL_GENLIST;
> val it = |- !n f. NULL (GENLIST f n) <=> (n = 0) : thm
- GENLIST_CONS;
> val it = |- GENLIST f (SUC n) = f 0::GENLIST (f o SUC) n : thm
- EL_GENLIST;
> val it = |- !f n x. x < n ==> (EL x (GENLIST f n) = f x) : thm
- EXISTS_GENLIST;
> val it = |- !n. EXISTS P (GENLIST f n) <=> ?i. i < n /\ P (f i) : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
- GENLIST_APPEND;
> val it = |- !f a b. GENLIST f (a + b) = GENLIST f b ++ GENLIST (\t. f (t + b)) a : thm
- HD_GENLIST;
> val it = |- HD (GENLIST f (SUC n)) = f 0 : thm
- TL_GENLIST;
> val it = |- !f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n : thm
- HD_GENLIST_COR;
> val it = |- !n f. 0 < n ==> (HD (GENLIST f n) = f 0) : thm
- GENLIST_FUN_EQ;
> val it = |- !n f g. (GENLIST f n = GENLIST g n) <=> !x. x < n ==> (f x = g x) : thm

*)

(* Theorem: rsum (SNOC h s) = (rsum s) + h *)
(* Proof: by induction on s.
   Base case: (rsum (SNOC k []) = rsum [] + k)
      rsum (SNOC k [])
    = rsum [k]            by SNOC
    = k + #0              by ring_sum_cons, ring_sum_nil
    = k                   by ring_add_rzero
    = #0 + k              by ring_add_lzero
    = rsum [] + k         by ring_sum_nil
   Step case: rlist s ==> (rsum (SNOC k s) = rsum s + k) ==>
              !h. rlist (h::s) ==> (rsum (SNOC k (h::s)) = rsum (h::s) + k)
     rsum (SNOC k (h::s))
   = rsum (h::SNOC k s)   by SNOC
   = h + rsum (SNOC k s)  by ring_sum_cons
   = h + (rsum s + k)     by induction hypothesis
   = (h + rsum s) + k     by ring_add_assoc, ring_sum_element
   = rsum(h::s) + k       by ring_sum_cons
*)
val ring_sum_SNOC = store_thm(
  "ring_sum_SNOC",
  ``!r:'a ring. Ring r ==> !k s. k IN R /\ rlist s ==> (rsum (SNOC k s) = (rsum s) + k)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[ring_add_assoc]);

(* ------------------------------------------------------------------------- *)
(* Function giving elements in Ring                                          *)
(* ------------------------------------------------------------------------- *)

(* Ring element function. *)
val ring_fun_def = Define`
  ring_fun (r:'a ring) f <=> !x. f x IN R
`;
val _ = overload_on ("rfun", ``ring_fun r``);

(* export simple definition. *)
val _ = export_rewrites ["ring_fun_def"];

(* Theorem: rfun a /\ rfun b ==> rfun (\k. a k + b k) *)
(* Proof: by ring_add_element. *)
val ring_fun_add = store_thm(
  "ring_fun_add",
  ``!r:'a ring. Ring r ==> !a b. rfun a /\ rfun b ==> rfun (\k. a k + b k)``,
  rw[]);

(* Theorem: rfun f ==> rlist (GENLIST f n) *)
(* Proof: by induction on n.
   Base case: rlist (GENLIST f 0)
      Since GENLIST f 0 = []   by GENLIST
      hence true by ring_list_nil.
   Step case: rlist (GENLIST f n) ==> rlist (GENLIST f (SUC n))
*)
val ring_fun_genlist = store_thm(
  "ring_fun_genlist",
  ``!f. rfun f ==> !n. rlist (GENLIST f n)``,
  rw_tac std_ss[ring_fun_def] >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[ring_list_cons, GENLIST] >>
  `rlist (FRONT (SNOC (f n) (GENLIST f n)))` by rw_tac std_ss[FRONT_SNOC] >>
  `LAST (SNOC (f n) (GENLIST f n)) IN R` by rw_tac std_ss[LAST_SNOC] >>
  metis_tac[ring_list_front_last]);

(* Theorem: rfun f ==> rlist (MAP f l) *)
(* Proof: by induction.
   Base case: rlist (MAP f [])
     True by ring_list_nil, MAP: MAP f [] = []
   Step case: rlist l ==> rlist (MAP f l) ==> !h. rlist (h::l) ==> rlist (MAP f (h::l))
     True by ring_list_cons, MAP: MAP f (h::t) = f h::MAP f t
*)
val ring_fun_map = store_thm(
  "ring_fun_map",
  ``!f l. rfun f ==> rlist (MAP f l)``,
  rw_tac std_ss[ring_fun_def] >>
  Induct_on `l` >| [
    rw_tac std_ss[MAP, ring_list_nil],
    rw_tac std_ss[MAP, ring_list_cons]
  ]);

(* Theorem: rfun f ==> !x. x IN R ==> rfun (\j. f j * x ** j *)
(* Proof: by ring_fun_def, ring_exp_element, ring_mult_element *)
val ring_fun_from_ring_fun = store_thm(
  "ring_fun_from_ring_fun",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !x. x IN R ==> rfun (\j. f j * x ** j)``,
  rw[ring_fun_def]);

(* Theorem: rfun f ==> !x. x IN R ==> !n. rfun (\j. (f j * x ** j) ** n) *)
(* Proof: by ring_fun_def, ring_exp_element, ring_mult_element *)
val ring_fun_from_ring_fun_exp = store_thm(
  "ring_fun_from_ring_fun_exp",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !x. x IN R ==> !n. rfun (\j. (f j * x ** j) ** n)``,
  rw[ring_fun_def]);

(* Theorem: rfun f ==> !x. x IN R ==> !n. rlist (GENLIST (\j. f j * x ** j) n) *)
(* Proof:
   By induction on n.
   Base case: rlist (GENLIST (\j. f j * x ** j) 0)
      Since rlist (GENLIST (\j. f j * x ** j) 0) = rlist []    by GENLIST
        and rlist [] = T                                       by ring_list_nil
   Step case: rlist (GENLIST (\j. f j * x ** j) n) ==> rlist (GENLIST (\j. f j * x ** j) (SUC n))
        rlist (GENLIST (\j. f j * x ** j) (SUC n))
      = rlist (SNOC (f n * x ** n) (GENLIST (\j. f j * x ** j) n))    by GENLIST
      = (f n ** x ** n) IN R /\ rlist (GENLIST (\j. f j * x ** j) n)  by ring_list_SNOC
      = true /\ rlist (GENLIST (\j. f j * x ** j) n)                  by ring_fun_def, ring_exp_element
      = true /\ true                                                  by induction hypothesis
*)
val ring_list_gen_from_ring_fun = store_thm(
  "ring_list_gen_from_ring_fun",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !x. x IN R ==> !n. rlist (GENLIST (\j. f j * x ** j) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `!j. f j IN R` by metis_tac[ring_fun_def] >>
  rw_tac std_ss[GENLIST, ring_list_SNOC, ring_exp_element, ring_mult_element]);

(* Theorem: !f. rfun f ==> !n g. rlist (GENLIST (f o g) n) *)
(* Proof:
   By induction on n.
   Base: rlist (GENLIST (f o g) 0)
          rlist (GENLIST (f o g) 0)
      <=> rlist []                   by GENLIST_0
      <=> T                          by ring_list_nil
   Step: rlist (GENLIST (f o g) n) ==> rlist (GENLIST (f o g) (SUC n))
          rlist (GENLIST (f o g) (SUC n))
      <=> rlist (SNOC ((f o g) n) (GENLIST (f o g) n))   by GENLIST
      <=> (f o g) n IN R /\ rlist (GENLIST (f o g) n)    by ring_list_SNOC
      <=> (f o g) n IN R /\ T                            by induction hypothesis
      <=> f (g n) IN R                                   by o_THM
      <=> T                                              by ring_fun_def
*)
val ring_list_from_genlist_ring_fun = store_thm(
  "ring_list_from_genlist_ring_fun",
  ``!r:'a ring. !f. rfun f ==> !n g. rlist (GENLIST (f o g) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `rlist (GENLIST (f o g) (SUC n)) <=> f (g n) IN R` by rw_tac std_ss[GENLIST, ring_list_SNOC] >>
  metis_tac[ring_fun_def]);

(* Theorem: !f. rfun f ==> !n. rlist (GENLIST f n) *)
(* Proof:
   Since f = f o I      by I_o_ID
   The result follows from ring_list_from_genlist_ring_fun
*)
val ring_list_from_genlist = store_thm(
  "ring_list_from_genlist",
  ``!r:'a ring. !f. rfun f ==> !n. rlist (GENLIST f n)``,
  rpt strip_tac >>
  `f = f o I` by rw[] >>
  `rlist (GENLIST (f o I) n)` by rw[ring_list_from_genlist_ring_fun] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Ring Sum Involving GENLIST                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !f n k. (0 < k /\ k < n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE p))) = #0) *)
(* Proof: by induction on n
   Base case: (!k. 0 < k /\ k < 0 ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE 0))) = #0)
     rsum (MAP f (GENLIST SUC (PRE 0))
   = rsum (MAP f (GENLIST SUC 0))         by PRE 0 = 0
   = rsum (MAP f [])                      by GENLIST f 0 = [] in GENLIST
   = rsum []                              by MAP f [] = []    in MAP
   = #0                                   by ring_sum_nil
   Step case: (!k. 0 < k /\ k < n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE n))) = #0) ==>
              (!k. 0 < k /\ k < SUC n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE (SUC n)))) = #0)
   First, note that n < SUC n             by LESS_SUC
   hence !k. 0 < k /\ k < n ==> f k = #0  by LESS_TRANS
   If n = 0, true by similar reasoning in base case.
   If n <> 0, 0 < n, then n = SUC m for some m    by num_CASES
     rsum (MAP f (GENLIST SUC (PRE (SUC n))))
   = rsum (MAP f (GENLIST SUC n))
   = rsum (MAP f (GENLIST SUC (SUC (PRE n))))               by SUC_PRE
   = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [SUC (PRE n)]))  by GENLIST, SNOC_APPEND
   = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [n]))            by SUC_PRE
   = rsum (MAP f (GENLIST SUC (PRE n)) ++ MAP f [n])        by MAP_APPEND
   = rsum (MAP f (GENLIST SUC (PRE n))) + rsum (MAP f [n])  by ring_sum_append, ring_fun_map
   = #0 + rsum (MAP f [n])                                  by induction hypothesis
   = rsum (MAP f [n])                                       by ring_add_lzero, ring_sum_element, ring_fun_map
   = rsum ([f n])                                           by MAP
   = f n                                                    by ring_sum_sing, ring_fun_def
   = #0                                                     by n < SUC n
*)
val ring_sum_fun_zero = store_thm(
  "ring_sum_fun_zero",
  ``!r:'a ring. Ring r ==> !f. rfun f ==>
    !n. (!k. 0 < k /\ k < n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE n))) = #0)``,
  ntac 4 strip_tac >>
  Induct_on `n` >| [
    `GENLIST SUC 0 = []` by rw_tac std_ss[GENLIST] >>
    `MAP f [] = []` by rw_tac std_ss[MAP] >>
    rw_tac std_ss[ring_sum_nil],
    rw_tac std_ss[] >>
    `n < SUC n /\ !k. 0 < k /\ k < n ==> (f k = #0)` by metis_tac[LESS_SUC, LESS_TRANS] >>
    Cases_on `n = 0` >| [
      rw_tac std_ss[] >>
      `GENLIST SUC 0 = []` by rw_tac std_ss[GENLIST] >>
      `MAP f [] = []` by rw_tac std_ss[MAP] >>
      rw_tac std_ss[ring_sum_nil],
      `0 < n /\ ?m. n = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
      `rsum (MAP f (GENLIST SUC n)) = rsum (MAP f (GENLIST SUC (SUC (PRE n))))` by rw_tac std_ss[SUC_PRE] >>
      `_ = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [SUC (PRE n)]))` by rw_tac std_ss[GENLIST, SNOC_APPEND] >>
      `_ = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [n]))` by rw_tac std_ss[SUC_PRE] >>
      `_ = rsum (MAP f (GENLIST SUC (PRE n)) ++ MAP f [n])` by rw_tac std_ss[MAP_APPEND] >>
      `_ = rsum (MAP f (GENLIST SUC (PRE n))) + rsum (MAP f [n])` by rw_tac std_ss[ring_sum_append, ring_fun_map] >>
      `_ = #0 + rsum (MAP f [n])` by metis_tac[] >>
      `_ = rsum (MAP f [n])` by rw_tac std_ss[ring_add_lzero, ring_sum_element, ring_fun_map] >>
      `_ = rsum ([f n])` by rw_tac std_ss[MAP] >>
      `_ = f n` by metis_tac[ring_sum_sing, ring_fun_def] >>
      metis_tac[]
    ]
  ]);

(* Theorem: rsum (k=0..n) f(k) = f(0) + rsum (k=1..n) f(k)  *)
(* Proof:
     rsum (GENLIST f (SUC n))
   = rsum (f 0 :: GENLIST (f o SUC) n)   by GENLIST_CONS
   = f 0 + rsum (GENLIST (f o SUC) n)    by ring_sum_cons
*)
val ring_sum_decompose_first = store_thm(
  "ring_sum_decompose_first",
  ``!r:'a ring. !f n. rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) n)``,
  rw[GENLIST_CONS]);

(* Theorem: rsum (k=0..n) f(k) = rsum (k=0..(n-1)) f(k) + f n *)
(* Proof:
     rsum (GENLIST f (SUC n))
   = rsum (SNOC (f n) (GENLIST f n))   by GENLIST definition
   = rsum ((GENLIST f n) ++ [f n])     by SNOC_APPEND
   = rsum (GENLIST f n) + rsum [f n]   by ring_sum_append
   = rsum (GENLIST f n) + f n          by ring_sum_sing
*)
val ring_sum_decompose_last = store_thm(
  "ring_sum_decompose_last",
  ``!r:'a ring. Ring r ==> !f n. rfun f ==> (rsum (GENLIST f (SUC n)) = rsum (GENLIST f n) + f n)``,
  rpt strip_tac >>
  `rlist (GENLIST f n)` by rw_tac std_ss[ring_fun_genlist] >>
  `f n IN R /\ rlist [f n]` by metis_tac[ring_list_def, ring_fun_def] >>
  rw_tac std_ss[GENLIST, SNOC_APPEND, ring_sum_append, ring_sum_sing]);

(* Theorem: Ring r /\ rfun f /\ 0 < n ==> rsum (k=0..n) f(k) = f(0) + rsum (k=1..n-1) f(k) + f(n)  *)
(* Proof:
     rsum (GENLIST f (SUC n))
   = rsum (GENLIST f n) + f n                     by ring_sum_decompose_last
   = rsum (GENLIST f (SUC m)) + f n               by n = SUC m, since 0 < n
   = f 0 + rsum (GENLIST f o SUC m) + f n         by ring_sum_decompose_first
   = f 0 + rsum (GENLIST f o SUC (PRE n)) + f n   by PRE_SUC_EQ
*)
val ring_sum_decompose_first_last = store_thm(
  "ring_sum_decompose_first_last",
  ``!r:'a ring. Ring r ==> !f n. rfun f /\ 0 < n ==> (rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) (PRE n)) + f n)``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `rsum (GENLIST f (SUC n)) = rsum (GENLIST f n) + f n` by rw_tac std_ss[ring_sum_decompose_last] >>
  `_ = f 0 + rsum (GENLIST (f o SUC) m) + f n` by rw_tac std_ss[ring_sum_decompose_first] >>
  rw_tac std_ss[PRE_SUC_EQ]);

(* Theorem: rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n) *)
(* Proof: by induction on n.
   Base case: rsum (GENLIST a 0) + rsum (GENLIST b 0) = rsum (GENLIST (\k. a k + b k) 0)
      true by GENLIST f 0 = [], and rsum [] = #0, and #0 + #0 = #0 by ring_add_zero_zero.
   Step case: rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n) ==>
              rsum (GENLIST a (SUC n)) + rsum (GENLIST b (SUC n)) = rsum (GENLIST (\k. a k + b k) (SUC n))
   LHS = rsum (GENLIST a (SUC n)) + rsum (GENLIST b (SUC n))
       = (rsum (GENLIST a n) + a n) + (rsum (GENLIST b n) + b n)    by ring_sum_decompose_last
       = rsum (GENLIST a n) + (a n + (rsum (GENLIST b n) + b n))    by ring_add_assoc
       = rsum (GENLIST a n) + (a n + rsum (GENLIST b n) + b n)      by ring_add_assoc
       = rsum (GENLIST a n) + (rsum (GENLIST b n) + a n + b n)      by ring_add_comm
       = rsum (GENLIST a n) + (rsum (GENLIST b n) + (a n + b n))    by ring_add_assoc
       = rsum (GENLIST a n) + rsum (GENLIST b n) + (a n + b n)      by ring_add_assoc
       = rsum (GENLIST (\k. a k + b k) n) + (a n + b n)             by induction hypothesis
       = rsum (GENLIST (\k. a k + b k) (SUC n))                     by ring_sum_decompose_last
       = RHS
*)
val ring_sum_genlist_add = store_thm(
  "ring_sum_genlist_add",
  ``!r:'a ring. Ring r ==> !a b. rfun a /\ rfun b ==>
   !n. rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `rfun (\k. a k + b k)` by rw_tac std_ss[ring_fun_add] >>
  rw_tac std_ss[ring_sum_decompose_last] >>
  `rsum (GENLIST a n) IN R /\ rsum (GENLIST b n) IN R` by rw_tac std_ss[ring_sum_element, ring_fun_genlist] >>
  `a n IN R /\ b n IN R` by metis_tac[ring_fun_def] >>
  `rsum (GENLIST a n) + a n + (rsum (GENLIST b n) + b n)
   = rsum (GENLIST a n) + (a n + rsum (GENLIST b n) + b n)` by rw[ring_add_assoc] >>
  `_ = rsum (GENLIST a n) + (rsum (GENLIST b n) + a n + b n)` by rw_tac std_ss[ring_add_comm] >>
  `_ = rsum (GENLIST a n) + rsum (GENLIST b n) + (a n + b n)` by rw[ring_add_assoc] >>
  rw_tac std_ss[]);

(* Theorem: rsum (GENLIST a n ++ GENLIST b n) = rsum (GENLIST (\k. a k + b k) n) *)
(* Proof:
     rsum (GENLIST a n ++ GENLIST b n)
   = rsum (GENLIST a n) + rsum (GENLIST b n)   by ring_sum_append, due to ring_fun_genlist.
   = rsum (GENLIST (\k. a k + b k) n)          by ring_sum_genlist_add
*)
val ring_sum_genlist_append = store_thm(
  "ring_sum_genlist_append",
  ``!r:'a ring. Ring r ==> !a b. rfun a /\ rfun b ==>
    !n. rsum (GENLIST a n ++ GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)``,
  rw_tac std_ss[ring_sum_append, ring_sum_genlist_add, ring_fun_genlist]);

(* Theorem: Ring r ==> !f. rfun f  ==>
            !n m. rsum (GENLIST f (n + m)) = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n) *)
(* Proof:
   Note (\k. f (k + m)) = f o (\k. k + m)    by FUN_EQ_THM
   Hence rlist (GENLIST f m)                 by ring_list_from_genlist
     and rlist (GENLIST (\k. f (k + m)) n)   by ring_list_from_genlist_ring_fun
     rsum (GENLIST f (n + m))
   = rsum (GENLIST f m ++ GENLIST (\k. f (k + m)) n)         by GENLIST_APPEND
   = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n)   by ring_sum_append
*)
val ring_sum_genlist_sum = store_thm(
  "ring_sum_genlist_sum",
  ``!r:'a ring. Ring r ==> !f. rfun f  ==>
   !n m. rsum (GENLIST f (n + m)) = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n)``,
  rpt strip_tac >>
  `(\k. f (k + m)) = f o (\k. k + m)` by rw[FUN_EQ_THM] >>
  `rlist (GENLIST (\k. f (k + m)) n)` by rw[ring_list_from_genlist_ring_fun] >>
  `rlist (GENLIST f m)` by rw[ring_list_from_genlist] >>
  metis_tac[GENLIST_APPEND, ring_sum_append]);

(* Theorem: Ring r ==> !x. x IN R ==> !n. rsum (GENLIST (K x) n) = ##n * x *)
(* Proof:
   By induction on n.
   Base: rsum (GENLIST (K x) 0) = ##0 * x
         rsum (GENLIST (K x) 0)
       = rsum []               by GENLIST_0
       = #0                    by ring_sum_nil
       = ##0 * x               by ring_num_0, ring_mult_lzero
   Step: rsum (GENLIST (K x) n) = ##n * x ==>
         rsum (GENLIST (K x) (SUC n)) = ##(SUC n) * x
       Note rfun (K x)                     by ring_fun_def, K_THM, x IN R
         so rlist (GENLIST (K x) n)        by ring_list_from_genlist
         rsum (GENLIST (K x) (SUC n))
       = rsum (SNOC ((K x) n) (GENLIST (K x) n))   by GENLIST
       = rsum (SNOC x (GENLIST (K x) n))           by K_THM
       = rsum (GENLIST (K x) n) + x                by ring_sum_SNOC
       = ##n * x + x                               by induction hypothesis
       = ##n * x + #1 * x                          by ring_mult_lone
       = (##n + #1) * x                            by ring_mult_ladd
       = ##(SUC n) * x                             by ring_num_suc
*)
val ring_sum_genlist_const = store_thm(
  "ring_sum_genlist_const",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. rsum (GENLIST (K x) n) = ##n * x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `rfun (K x)` by rw[ring_fun_def] >>
  `rlist (GENLIST (K x) n)` by rw[ring_list_from_genlist] >>
  `rsum (GENLIST (K x) (SUC n)) = ##n * x + x` by rw[GENLIST, ring_sum_SNOC] >>
  rw[ring_mult_ladd, ring_num_suc]);

(* ------------------------------------------------------------------------- *)
(* Ring Binomial Theorem                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Binomial Index Shifting, for
     rsum (k=1..n) ##C(n,k) x^(n+1-k) y^k = rsum (k=0..n-1) ##C(n,k+1) x^(n-k) y^(k+1)  *)
(* Proof:
   Since
     rsum (k=1..n) C(n,k)x^(n+1-k)y^k
   = rsum (MAP (\k. (binomial n k)* x**(n+1-k) * y**k) (GENLIST SUC n))
   = rsum (GENLIST (\k. (binomial n k)* x**(n+1-k) * y**k) o SUC n)

     rsum (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
   = rsum (MAP (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) (GENLIST I n))
   = rsum (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) o I n)
   = rsum (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) n)

   This is equivalent to showing:
   (\k. (binomial n k)* x**(n-k+1) * y**k) o SUC = (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1))
*)

(* Theorem: Binomial index shift for GENLIST:
   (\k. (binomial n k)* x**(n-k+1) * y**k) o SUC = (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) *)
(* Proof:
   For any k < n,
     ((\k. (binomial n k)* x**(n-k+1) * y**k) o SUC) k
   = ##(binomial n (SUC k)) * x ** SUC (n - SUC k) * y ** SUC k
   = ##(binomial n (SUC k)) * x ** (n-k) * y ** SUC k    by SUC (n - SUC k) = n - k for k < n
   = ##(binomial n (k + 1)) * x ** (n-k) * y ** (k+1)    by definition of SUC
   = (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) k
*)
val ring_binomial_genlist_index_shift = store_thm(
  "ring_binomial_genlist_index_shift",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. GENLIST ((\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) o SUC) n =
       GENLIST (\k. ##(binomial n (SUC k)) * x**(n-k) * y**(SUC k)) n``,
  rw_tac std_ss[GENLIST_FUN_EQ] >>
  `SUC (n - SUC k) = n - k` by decide_tac >>
  rw_tac std_ss[]);

(* This is closely related to above, with (SUC n) replacing (n),
   but does not require k < n. *)
(* Proof: by equality of function. *)
val ring_binomial_index_shift = store_thm(
  "ring_binomial_index_shift",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (\k. ##(binomial (SUC n) k) * x**((SUC n) - k) * y**k) o SUC =
       (\k. ##(binomial (SUC n) (SUC k)) * x**(n-k) * y**(SUC k))``,
  rw[FUN_EQ_THM]);

(* Pattern for binomial expansion:

    (x+y)(x^3 + 3x^2y + 3xy^2 + y^3)
  = x(x^3) + 3x(x^2y) + 3x(xy^2) + x(y^3) +
               y(x^3) + 3y(x^2y) + 3y(xy^2) + y(y^3)
  = x^4 + (3+1)x^3y + (3+3)(x^2y^2) + (1+3)(xy^3) + y^4
    = x^4 + 4x^3y   + 6x^2y^2       + 4xy^3       + y^4

*)

(* Theorem: multiply x into a binomial term:
   (\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (SUC(n - k)) * y ** k)  *)
(* Proof: to prove:
     x * (##(binomial n k) * x ** (n - k) * y ** k) = ##(binomial n k) * x ** SUC (n - k) * y ** k
   LHS = x * (##(binomial n k) * x ** (n - k) * y ** k)
       = x * (##(binomial n k) * (x ** (n - k) * y ** k))   by ring_mult_assoc
       = (x * ##(binomial n k)) * (x ** (n - k) * y ** k)   by ring_mult_assoc
       = (##(binomial n k) * x) * (x ** (n - k) * y ** k)   by ring_mult_comm
       = ##(binomial n k) * (x * x ** (n - k) * y ** k)     by ring_mult_assoc
       = ##(binomial n k) * (x ** SUC (n - k) * y ** k)     by ring_exp_SUC
       = ##(binomial n k) * x ** SUC (n - k) * y ** k       by ring_mult_assoc
       = RHS
*)
val ring_binomial_term_merge_x = store_thm(
  "ring_binomial_term_merge_x",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (SUC(n - k)) * y ** k)``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `##(binomial n k) IN R /\ x ** (n - k) IN R /\ y ** k IN R /\ x ** SUC (n - k) IN R` by rw[] >>
  `x * (##(binomial n k) * x ** (n - k) * y ** k) = (x * ##(binomial n k)) * (x ** (n - k) * y ** k)` by rw[ring_mult_assoc] >>
  `_ = (##(binomial n k) * x) * (x ** (n - k) * y ** k)` by rw_tac std_ss[ring_mult_comm] >>
  rw[ring_mult_assoc]);

(* Theorem: multiply y into a binomial term:
   (\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k))  *)
(* Proof: to prove:
     y * (##(binomial n k) * x ** (n - k) * y ** k) = ##(binomial n k) * x ** (n - k) * y ** SUC k
   LHS = y * (##(binomial n k) * x ** (n - k) * y ** k)
       = y * (##(binomial n k) * (x ** (n - k) * y ** k))   by ring_mult_assoc
       = (y * ##(binomial n k)) * (x ** (n - k) * y ** k)   by ring_mult_assoc
       = (##(binomial n k) * y) * (x ** (n - k) * y ** k)   by ring_mult_comm
       = (##(binomial n k) * y) * (y ** k * x ** (n - k))   by ring_mult_comm
       = ##(binomial n k) * (y * y ** k * x ** (n - k))     by ring_mult_assoc
       = ##(binomial n k) * (y ** SUC k * x ** (n - k))     by ring_exp_SUC
       = ##(binomial n k) * (x ** (n - k) * y ** SUC k)     by ring_mult_comm
       = ##(binomial n k) * x ** (n - k) * y ** SUC k       by ring_mult_assoc
       = RHS
*)
val ring_binomial_term_merge_y = store_thm(
  "ring_binomial_term_merge_y",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `##(binomial n k) IN R /\ x ** (n - k) IN R /\ y ** k IN R /\ y ** SUC k IN R` by rw[] >>
  `y * (##(binomial n k) * x ** (n - k) * y ** k) =
    (y * ##(binomial n k)) * (x ** (n - k) * y ** k)` by rw[ring_mult_assoc] >>
  `_ = (##(binomial n k) * y) * (y ** k * x ** (n - k))` by rw_tac std_ss[ring_mult_comm] >>
  `_ = ##(binomial n k) * (y ** SUC k * x ** (n - k))` by rw[ring_mult_assoc] >>
  `_ = ##(binomial n k) * (x ** (n - k) * y ** SUC k)` by rw_tac std_ss[ring_mult_comm] >>
  rw[ring_mult_assoc]);


(* GOAL: *)

(* Theorem: [Binomial Theorem]  (x + y)^n = rsum (k=0..n) C(n,k)x^(n-k)y^k
   or (x + y)**n = rsum (GENLIST (\k. (binomial n k)* x**(n-k) * y**k) (SUC n)) *)
(* Proof: by induction on n.
   Base case: to prove (x + y)^0 = rsum (k=0..0) C(0,k)x^(0-k)y^k
   or  (x + y) ** 0 = rsum (GENLIST (\k. ##(binomial 0 k) * x ** (0 - k) * y ** k) (SUC 0))
   LHS = (x + y) ** 0 = #1        by ring_exp_0, ring_add_element
   RHS = rsum (GENLIST (\k. ##(binomial 0 k) * x ** (0 - k) * y ** k) (SUC 0))
       = rsum (GENLIST (\k. ##(binomial 0 k) * x ** (0 - k) * y ** k) 1)   by ONE
       = rsum (SNOC (##(binomial 0 0) * x ** 0 * y ** 0) [])               by GENLIST
       = rsum [##(binomial 0 0) * x ** 0 * y ** 0]                         by SNOC
       = rsum [##(binomial 0 0) * #1 * #1]                                 by ring_exp_0
       = rsum [##1 * #1 * #1]                                              by binomial_n_n
       = rsum [#1 * #1 * #1]                                               by ring_num_1
       = rsum [#1]                                                         by ring_mult_one_one
       = #1                                                                by ring_sum_sing, ring_one_element
       = LHS
   Step case: assume (x + y)^n = rsum (k=0..n) C(n,k)x^(n-k)y^k
    to prove: (x + y)^SUC n = rsum (k=0..(SUC n)) C(SUC n,k)x^((SUC n)-k)y^k
    or (x + y) ** n = rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) ==>
       (x + y) ** SUC n = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC (SUC n)))
   LHS = (x + y) ** SUC n
       = (x + y) * (x + y) ** n       by ring_exp_SUC
       = (x + y) * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))    by induction hypothesis
       = x * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) +
         y * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))          by ring_mult_ladd
       = rsum (MAP (\k. x*k) (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))) +
         rsum (MAP (\k. y*k) (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)))  by ring_sum_mult
       = rsum (GENLIST ((\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n)) +
         rsum (GENLIST ((\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n))    by MAP_GENLIST
       = rsum (GENLIST (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) (SUC n)) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))
                                                               by ring_binomial_term_merge_x, ring_binomial_term_merge_y
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))   by ring_sum_decompose_first
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )                      by ring_sum_decompose_last
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
         rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )             by ring_binomial_genlist_index_shift
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        (rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n)) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n               by ring_add_assoc, ring_add_element
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k) +
                            ##(binomial n k) * x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_sum_genlist_add
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) + ##(binomial n k)) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_mult_ladd, ring_mult_element
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * (x ** (n - k) * y ** (SUC k)) +
                            ##(binomial n k) * (x ** (n - k) * y ** (SUC k)))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by  ring_mult_assoc
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial n (SUC k) + binomial n k) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_num_add_mult, ring_mult_element
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by binomial_recurrence, ADD_COMM
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_mult_assoc
       = ##(binomial n 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        ##(binomial n n) * x ** 0 * y ** (SUC n)                              by function application
       = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)                  by binomial_n_0, binomial_n_n
       = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST ((\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)                  by ring_binomial_index_shift
       = (\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) 0 +
        rsum (GENLIST ((\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        (\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) (SUC n)    by function application
       = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)      by ring_sum_decompose_first
       = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC (SUC n))) by ring_sum_decompose_last
       = RHS
    Conventionally,
      (x + y)^SUC n
    = (x + y)(x + y)^n      by EXP
    = (x + y) rsum (k=0..n) C(n,k)x^(n-k)y^k   by induction hypothesis
    = x (rsum (k=0..n) C(n,k)x^(n-k)y^k) +
      y (rsum (k=0..n) C(n,k)x^(n-k)y^k)       by RIGHT_ADD_DISTRIB
    = rsum (k=0..n) C(n,k)x^(n+1-k)y^k +
      rsum (k=0..n) C(n,k)x^(n-k)y^(k+1)       by moving factor into ring_sum
    = C(n,0)x^(n+1) + rsum (k=1..n) C(n,k)x^(n+1-k)y^k +
                      rsum (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)  by breaking sum
    = C(n,0)x^(n+1) + rsum (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1) +
                      rsum (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)  by index shifting
    = C(n,0)x^(n+1) + rsum (k=0..n-1) [C(n,k+1) + C(n,k)] x^(n-k)y^(k+1) + C(n,n)y^(n+1)     by merging sums
    = C(n,0)x^(n+1) + rsum (k=0..n-1) C(n+1,k+1) x^(n-k)y^(k+1)          + C(n,n)y^(n+1)     by binomial recurrence
    = C(n,0)x^(n+1) + rsum (k=1..n) C(n+1,k) x^(n+1-k)y^k                + C(n,n)y^(n+1)     by index shifting again
    = C(n+1,0)x^(n+1) + rsum (k=1..n) C(n+1,k) x^(n+1-k)y^k              + C(n+1,n+1)y^(n+1) by binomial identities
    = rsum (k=0..(SUC n))C(SUC n,k) x^((SUC n)-k)y^k                                         by synthesis of sum
*)
val ring_binomial_thm = store_thm(
  "ring_binomial_thm",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (x + y)**n = rsum (GENLIST (\k. ##(binomial n k) * x**(n-k) * y**k) (SUC n))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[ring_sum_sing, binomial_n_n] >>
  rw_tac std_ss[ring_exp_SUC, ring_add_element] >>
  `!m n k h. ##(binomial m n) IN R /\ x ** h IN R /\ y ** k IN R` by rw[] >>
  `!h. (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) h IN R` by rw_tac std_ss[ring_mult_element] >>
  `!h. (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) h IN R` by rw_tac std_ss[ring_mult_element] >>
  `!m. rfun (\k. ##(binomial m k) * x ** (m - k) * y ** k)` by rw_tac std_ss[ring_fun_def, ring_mult_element] >>
  `!m n. rlist (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** k) n)` by rw_tac std_ss[ring_fun_genlist] >>
  `!m n. rsum (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** k) n) IN R` by rw_tac std_ss[ring_sum_element] >>
  `!m. rfun (\k. ##(binomial m k) * x ** (m - k) * y ** SUC k)` by rw_tac std_ss[ring_fun_def, ring_mult_element] >>
  `!m n. rlist (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** SUC k) n)` by rw_tac std_ss[ring_fun_genlist] >>
  `!m n. rsum (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** SUC k) n) IN R` by rw_tac std_ss[ring_sum_element] >>
  `!m. rfun (\k. ##(binomial m (SUC k)) * x ** (m - k) * y ** SUC k)` by rw_tac std_ss[ring_fun_def, ring_mult_element] >>
  `!m n. rlist (GENLIST (\k. ##(binomial m (SUC k)) * x ** (m - k) * y ** SUC k) n)` by rw_tac std_ss[ring_fun_genlist] >>
  `!m n. rsum (GENLIST (\k. ##(binomial m (SUC k)) * x ** (m - k) * y ** SUC k) n) IN R` by rw_tac std_ss[ring_sum_element] >>
  `(x + y) * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) =
    x * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) +
    y * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))` by rw_tac std_ss[ring_mult_ladd] >>
  `_ = rsum (GENLIST ((\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n)) +
        rsum (GENLIST ((\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n))`
    by rw_tac std_ss[ring_sum_mult, MAP_GENLIST] >>
  `_ = rsum (GENLIST (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) (SUC n)) +
        rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw_tac std_ss[ring_binomial_term_merge_x, ring_binomial_term_merge_y] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw_tac std_ss[ring_sum_decompose_first] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )`
    by rw_tac std_ss[ring_sum_decompose_last] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
         rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )`
    by rw_tac std_ss[ring_binomial_genlist_index_shift] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        (rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n)) +
       (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_add_assoc, ring_add_element] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k) +
                            ##(binomial n k) * x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_sum_genlist_add] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * (x ** (n - k) * y ** (SUC k)) +
                            ##(binomial n k) * (x ** (n - k) * y ** (SUC k)))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_mult_assoc] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial n (SUC k) + binomial n k) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_num_add_mult, ring_mult_element] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[binomial_recurrence, ADD_COMM] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_mult_assoc] >>
  `_ = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)`
        by rw_tac std_ss[binomial_n_0, binomial_n_n] >>
  `_ = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST ((\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)`
        by rw_tac std_ss[ring_binomial_index_shift] >>
  `_ = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)`
        by rw_tac std_ss[ring_sum_decompose_first] >>
  `_ = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC (SUC n)))`
        by rw_tac std_ss[ring_sum_decompose_last] >>
  rw_tac std_ss[]);

(* This is a major milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Ring with prime characteristic                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> prime (char r) <=> 1 < char r /\ ##(binomial (char r) k) = #0   for  0 < k < (char r) *)
(* Proof:
       prime (char r)
   <=> divides (char r) (binomial (char r) k) for 0 < k < (char r) by prime_iff_divides_binomials
   <=> ##(binomial (char r) k) = #0           for 0 < k < (char r) by ring_char_divides
*)
val ring_char_prime = store_thm(
  "ring_char_prime",
  ``!r:'a ring. Ring r ==>
   (prime (char r) <=> 1 < char r /\ !k. 0 < k /\ k < char r ==> (##(binomial (char r) k) = #0))``,
  rw_tac std_ss[prime_iff_divides_binomials, ring_char_divides]);

(* Theorem: [Freshman's Theorem]
            Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
            ((x + y) ** (char r) = x ** (char r) + y ** (char r)) *)
(* Proof:
   Let p = char r.
   prime p ==> 0 < p                                 by PRIME_POS
   Let f = (\k. ##(binomial p k) * x**(p-k) * y**k), then
   then rfun f /\ f 0 IN R /\ f p IN R               by ring_fun_def
   !k. 0 < k /\ k < p ==> (##(binomial p k) = #0)    by ring_char_prime
   !k. 0 < k /\ k < p ==> (f k = #0)                 by ring_mult_lzero, ring_num_element, ring_exp_element
     (x + y) ** p
   = rsum (GENLIST f) (SUC p))                       by ring_binomial_thm
   = f 0 + rsum (GENLIST (f o SUC) (PRE p)) + f p    by ring_sum_decompose_first_last
   = f 0 + rsum (MAP f (GENLIST SUC (PRE p))) + f p  by MAP_GENLIST
   = f 0 + #0 + f p                                  by ring_sum_fun_zero
   = f 0 + f p                                       by ring_add_rzero

   f 0 = ##(binomial p 0) * x**(p-0) * y**0
       =  #1 * x**p * #1                             by binomial_n_0, ring_exp_0, ring_num_1
       = x ** p                                      by ring_mult_lone, ring_mult_rone
   f p = ##(binomial p p) * x**(p-p) * y**p
       = #1 * #1 * y**p                              by binomial_n_n, ring_exp_0, ring_num_1
       = y ** p                                      by ring_exp_element, ring_mult_one_one
   The result follows.
*)
val ring_freshman_thm = store_thm(
  "ring_freshman_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
         ((x + y) ** (char r) = x ** (char r) + y ** (char r))``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `0 < p` by metis_tac[PRIME_POS] >>
  qabbrev_tac `f = (\k. ##(binomial p k) * x**(p-k) * y**k)` >>
  `rfun f /\ f 0 IN R /\ f p IN R` by rw[ring_fun_def, Abbr`f`] >>
  `!k. 0 < k /\ k < p ==> (##(binomial p k) = #0)` by metis_tac[ring_char_prime] >>
  `!k. 0 < k /\ k < p ==> (f k = #0)` by rw[Abbr`f`, Abbr`p`] >>
  `(x + y) ** p = rsum (GENLIST f (SUC p))` by rw_tac std_ss[ring_binomial_thm, Abbr(`p`), Abbr(`f`)] >>
  `(x + y) ** p = f 0 + rsum (GENLIST (f o SUC) (PRE p)) + f p` by metis_tac[ring_sum_decompose_first_last] >>
  `_ = f 0 + rsum (MAP f (GENLIST SUC (PRE p))) + f p` by rw_tac std_ss[MAP_GENLIST] >>
  `_ = f 0 + f p` by rw_tac std_ss[ring_sum_fun_zero, ring_add_rzero] >>
  `f 0 = #1 * x**p * #1` by rw_tac std_ss[Abbr`f`, binomial_n_0, ring_exp_0, ring_num_1] >>
  `f p = #1 * #1 * y**p` by rw_tac std_ss[Abbr`f`, binomial_n_n, ring_exp_0, ring_num_1] >>
  rw[]);

(* Note: a ** b ** c = a ** (b ** c) *)
(* Theorem: [Freshman's Theorem Generalized]
             Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
             !n. (x + y) ** (char r) ** n = x ** (char r) ** n + y ** (char r) ** n *)
(* Proof:
   Let p = char r.
   prime p ==> 0 < p                by PRIME_POS
   By induction on n.
   Base case: (x + y) ** p ** 0 = x ** p ** 0 + y ** p ** 0
   LHS = (x + y) ** p ** 0
       = (x + y) ** 1               by EXP
       = x + y                      by ring_exp_1
       = x ** 1 + y ** 1            by ring_exp_1
       = x ** p ** 0 + y ** p ** 0  by EXP
       = RHS
   Step case: (x + y) ** p ** n = x ** p ** n + y ** p ** n ==>
              (x + y) ** p ** SUC n = x ** p ** SUC n + y ** p ** SUC n
   LHS = (x + y) ** p ** SUC n
       = (x + y) ** (p * p ** n)                   by EXP
       = (x + y) ** (p ** n * p)                   by MULT_COMM
       = ((x + y) ** p ** n) ** p                  by ring_exp_mult
       = (x ** p ** n + y ** p ** n) ** p          by induction hypothesis
       = (x ** p ** n) ** p + (y ** p ** n) ** p   by ring_freshman_thm
       = x ** (p ** n * p) + y ** (p ** n * p)     by ring_exp_mult
       = x ** (p * p ** n) + y ** (p * p ** n)     by MULT_COMM
       = x ** p ** SUC n + y ** p ** SUC n         by EXP
       = RHS
*)
val ring_freshman_all = store_thm(
  "ring_freshman_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
   !n. (x + y) ** (char r) ** n = x ** (char r) ** n + y ** (char r) ** n``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  Induct_on `n` >-
  rw[EXP] >>
  `(x + y) ** p ** SUC n = (x + y) ** (p * p ** n)` by rw[EXP] >>
  `_ = (x + y) ** (p ** n * p)` by rw_tac std_ss[MULT_COMM] >>
  `_ = ((x + y) ** p ** n) ** p` by rw[ring_exp_mult] >>
  `_ = (x ** p ** n + y ** p ** n) ** p` by rw[] >>
  `_ = (x ** p ** n) ** p + (y ** p ** n) ** p` by rw[ring_freshman_thm, Abbr`p`] >>
  `_ = x ** (p ** n * p) + y ** (p ** n * p)` by rw[ring_exp_mult] >>
  `_ = x ** (p * p ** n) + y ** (p * p ** n)` by rw_tac std_ss[MULT_COMM] >>
  `_ = x ** p ** SUC n + y ** p ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
            ((x - y) ** char r = x ** char r - y ** char r) *)
(* Proof:
   Let m = char r.
     (x - y) ** m
   = (x + -y) ** m            by ring_sub_def
   = x ** m + (-y) ** m       by ring_freshman_thm
   If EVEN m,
      (-y) ** m = y ** m      by ring_neg_exp
      prime m ==> m = 2       by EVEN_PRIME
      y ** m = - (y ** m)     by ring_neg_char_2
      The result follows      by ring_sub_def
   If ~EVEN m,
      (-y) ** m = - (y ** m)  by ring_neg_exp
      The result follows      by ring_sub_def
*)
val ring_freshman_thm_sub = store_thm(
  "ring_freshman_thm_sub",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
               ((x - y) ** char r = x ** char r - y ** char r)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  rw[] >>
  `(x + -y) ** m = x ** m + (-y) ** m` by rw[ring_freshman_thm, Abbr`m`] >>
  Cases_on `EVEN m` >-
  rw[GSYM EVEN_PRIME, ring_neg_exp, ring_neg_char_2, Abbr`m`] >>
  rw[ring_neg_exp]);

(* Theorem: Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
            !n. (x - y) ** (char r) ** n = x ** (char r) ** n - y ** (char r) ** n *)
(* Proof:
   Let m = char r.
   prime m ==> 0 < m                by PRIME_POS
   By induction on n.
   Base case: (x - y) ** m ** 0 = x ** m ** 0 - y ** m ** 0
        (x - y) ** m ** 0
      = (x - y) ** 1               by EXP
      = x - y                      by ring_exp_1
      = x ** 1 - y ** 1            by ring_exp_1
      = x ** m ** 0 - y ** m ** 0  by EXP
   Step case: (x - y) ** m ** n = x ** m ** n - y ** m ** n ==>
              (x - y) ** m ** SUC n = x ** m ** SUC n - y ** m ** SUC n
        (x - y) ** m ** SUC n
      = (x - y) ** (m * m ** n)                   by EXP
      = (x - y) ** (m ** n * m)                   by MULT_COMM
      = ((x - y) ** m ** n) ** m                  by ring_exp_mult
      = (x ** m ** n - y ** m ** n) ** m          by induction hypothesis
      = (x ** m ** n) ** m - (y ** m ** n) ** m   by ring_freshman_thm_sub
      = x ** (m ** n * m) - y ** (m ** n * m)     by ring_exp_mult
      = x ** (m * m ** n) - y ** (m * m ** n)     by MULT_COMM
      = x ** m ** SUC n - y ** m ** SUC n         by EXP
*)
val ring_freshman_all_sub = store_thm(
  "ring_freshman_all_sub",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
   !n. (x - y) ** (char r) ** n = x ** (char r) ** n - y ** (char r) ** n``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >-
  rw[EXP] >>
  `(x - y) ** m ** SUC n = (x - y) ** (m * m ** n)` by rw[EXP] >>
  `_ = (x - y) ** (m ** n * m)` by rw_tac std_ss[MULT_COMM] >>
  `_ = ((x - y) ** m ** n) ** m` by rw[ring_exp_mult] >>
  `_ = (x ** m ** n - y ** m ** n) ** m` by rw[] >>
  `_ = (x ** m ** n) ** m - (y ** m ** n) ** m` by rw[ring_freshman_thm_sub, Abbr`m`] >>
  `_ = x ** (m ** n * m) - y ** (m ** n * m)` by rw[ring_exp_mult] >>
  `_ = x ** (m * m ** n) - y ** (m * m ** n)` by rw_tac std_ss[MULT_COMM] >>
  `_ = x ** m ** SUC n - y ** m ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: [Fermat's Little Theorem]
            Ring r /\ prime (char r) ==> !n. (##n) ** (char r) = (##n)  *)
(* Proof: by induction on n.
   Let p = char r, prime p ==> 0 < p   by PRIME_POS
   Base case: ##0 ** p = ##0
     ##0 ** p
   = #0 ** p              by ring_num_0
   = #0                   by ring_zero_exp, p <> 0
   = ##0                  by ring_num_0
   Step case: ##n ** p = ##n ==> ##(SUC n) ** p = ##(SUC n)
     ##(SUC n) ** p
   = (#1 + ##n) ** p      by ring_num_SUC
   = #1 ** p + ##n ** p   by ring_freshman_thm
   = #1 ** p + ##n        by induction hypothesis
   = #1 + ##n             by ring_one_exp
   = ##(SUC n)            by ring_num_SUC
*)
val ring_fermat_thm = store_thm(
  "ring_fermat_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !n. (##n) ** (char r) = (##n)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `p <> 0` by decide_tac >>
  Induct_on `n` >| [
    rw[ring_zero_exp],
    rw_tac std_ss[ring_num_SUC] >>
    `#1 IN R /\ ##n IN R` by rw[] >>
    metis_tac[ring_freshman_thm, ring_one_exp]
  ]);

(* Theorem: [Fermat's Little Theorem Generalized]
            Ring r /\ prime (char r) ==> !n k. (##n) ** (char r) ** k = (##n)  *)
(* Proof:
   Let p = char r. By induction on k.
   Base case: ##n ** p ** 0 = ##n
     ##n ** p ** 0
   = ##n ** 1               by EXP
   = ##n                    by ring_exp_1
   Step case: ##n ** p ** k = ##n ==> ##n ** p ** SUC k = ##n
     ##n ** p ** SUC k
   = ##n ** (p * p ** k)    by EXP
   = ##n ** (p ** k * p)    by MULT_COMM
   = (##n ** p ** k) ** p   by ring_exp_mult
   = ##n ** p               by induction hypothesis
   = ##n                    by ring_fermat_thm
*)
val ring_fermat_all = store_thm(
  "ring_fermat_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !n k. (##n) ** (char r) ** k = (##n)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  Induct_on `k` >-
  rw[EXP] >>
  `##n ** p ** SUC k = ##n ** (p * p ** k)` by rw[EXP] >>
  `_ = ##n ** (p ** k * p)` by rw_tac std_ss[MULT_COMM] >>
  rw[ring_exp_mult, ring_fermat_thm, Abbr`p`]);

(* Theorem: [Freshman Theorem for Ring Sum]
            Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
            !n. rsum (GENLIST (\j. f j * x ** j) n) ** char r =
                rsum (GENLIST (\j. (f j * x ** j) ** char r) n) *)
(* Proof:
   Let m = char r.
   By induction on n.
   Base case: rsum (GENLIST (\j. f j * x ** j) 0) ** m =
              rsum (GENLIST (\j. (f j * x ** j) ** m) 0)
      Note 0 < m                      by PRIME_POS
        rsum (GENLIST (\j. f j * x ** j) 0) ** m
      = rsum [] ** m                  by GENLIST
      = #0 ** m                       by ring_sum_nil
      = #0                            by ring_zero_exp, 0 < m.
      = rsum []                       by ring_sum_nil
      = rsum (GENLIST (\j. (f j * x ** j) ** m) 0)   by GENLIST
   Step case: rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m =
              rsum (GENLIST (\j. (f j * x ** j) ** m) (SUC n))
      Note rfun (\j. f j * x ** j)                   by ring_fun_from_ring_fun
       and rfun (\j. (f j * x ** j) ** m)            by ring_fun_from_ring_fun_exp
       and rsum (GENLIST (\j. f j * x ** j) n) IN R  by ring_sum_element, ring_list_gen_from_ring_fun
        rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m
      = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m       by ring_sum_decompose_last
      = (rsum (GENLIST (\j. f j * x ** j) n)) ** m + (f n * x ** n) ** m  by ring_freshman_thm
      = rsum (GENLIST (\j. (f j * x ** j) ** m) n) + (f n * x ** n) ** m  by induction hypothesis
      = rsum (GENLIST (\j. (f j * x ** j) ** m) (SUC n))                  by poly_sum_decompose_last
*)
val ring_sum_freshman_thm = store_thm(
  "ring_sum_freshman_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
   !n. rsum (GENLIST (\j. f j * x ** j) n) ** char r =
       rsum (GENLIST (\j. (f j * x ** j) ** char r) n)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >| [
    rw_tac std_ss[GENLIST, ring_sum_nil] >>
    `0 < m` by rw[PRIME_POS, Abbr`m`] >>
    `m <> 0` by decide_tac >>
    rw[ring_zero_exp],
    `rfun (\j. f j * x ** j)` by rw[ring_fun_from_ring_fun] >>
    `rfun (\j. (f j * x ** j) ** m)` by rw[ring_fun_from_ring_fun_exp] >>
    `rsum (GENLIST (\j. f j * x ** j) n) IN R` by rw[ring_sum_element, ring_list_gen_from_ring_fun] >>
    `!j. f j IN R` by metis_tac[ring_fun_def] >>
    `f n * x ** n IN R` by rw[] >>
    `rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m
    = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m` by rw[ring_sum_decompose_last] >>
    `_ = (rsum (GENLIST (\j. f j * x ** j) n)) ** m + (f n * x ** n) ** m` by rw[ring_freshman_thm, Abbr`m`] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m) n) + (f n * x ** n) ** m` by rw[] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m) (SUC n))` by rw[ring_sum_decompose_last] >>
    rw[]
  ]);

(* Theorem: Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
            !n k. rsum (GENLIST (\j. f j * x ** j) n) ** char r ** k =
                  rsum (GENLIST (\j. (f j * x ** j) ** char r ** k) n) *)
(* Proof:
   Let m = char r.
   By induction on n.
   Base case: rsum (GENLIST (\j. f j * x ** j) 0) ** m ** k =
              rsum (GENLIST (\j. (f j * x ** j) ** m ** k) 0)
      Note 0 < m                      by PRIME_POS
        so 0 < m ** k                 by EXP_NONZERO
        rsum (GENLIST (\j. f j * x ** j) 0) ** m ** k
      = rsum [] ** m ** k        by GENLIST
      = #0 ** m ** k             by ring_sum_nil
      = #0                       by ring_zero_exp, 0 < m ** k.
      = rsum []                  by ring_sum_nil
      = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) 0)   by GENLIST
   Step case: rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m ** k =
              rsum (GENLIST (\j. (f j * x ** j) ** m ** k) (SUC n))
      Note rfun (\j. f j * x ** j)                   by ring_fun_from_ring_fun
       and rfun (\j. (f j * x ** j) ** m ** k)       by ring_fun_from_ring_fun_exp
       and rsum (GENLIST (\j. f j * x ** j) n) IN R  by ring_sum_element, ring_list_gen_from_ring_fun
        rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m ** k
      = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m ** k            by ring_sum_decompose_last
      = (rsum (GENLIST (\j. f j * x ** j) n)) ** m ** k + (f n * x ** n) ** m ** k  by ring_freshman_all
      = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) n) + (f n * x ** n) ** m ** k  by induction hypothesis
      = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) (SUC n))                       by ring_sum_decompose_last
*)
val ring_sum_freshman_all = store_thm(
  "ring_sum_freshman_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
   !n k. rsum (GENLIST (\j. f j * x ** j) n) ** char r ** k =
         rsum (GENLIST (\j. (f j * x ** j) ** char r ** k) n)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >| [
    rw_tac std_ss[GENLIST, ring_sum_nil] >>
    `0 < m` by rw[PRIME_POS, Abbr`m`] >>
    `m <> 0` by decide_tac >>
    `m ** k <> 0` by rw[EXP_NONZERO] >>
    rw[ring_zero_exp],
    `rfun (\j. f j * x ** j)` by rw[ring_fun_from_ring_fun] >>
    `rfun (\j. (f j * x ** j) ** m ** k)` by rw[ring_fun_from_ring_fun_exp] >>
    `rsum (GENLIST (\j. f j * x ** j) n) IN R` by rw[ring_sum_element, ring_list_gen_from_ring_fun] >>
    `!j. f j IN R` by metis_tac[ring_fun_def] >>
    `f n * x ** n IN R` by rw[] >>
    `rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m ** k
    = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m ** k` by rw[ring_sum_decompose_last] >>
    `_ = (rsum (GENLIST (\j. f j * x ** j) n)) ** m ** k + (f n * x ** n) ** m ** k` by rw[ring_freshman_all, Abbr`m`] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) n) + (f n * x ** n) ** m ** k` by rw[] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) (SUC n))` by rw[ring_sum_decompose_last] >>
    rw[]
  ]);

(* Theorem: [Frobenius Theorem]
            For a Ring with prime p = char r, x IN R,
            the map x --> x^p  is a ring homomorphism to itself (endomorphism)
         or Ring r /\ prime (char r) ==> RingEndo (\x. x ** (char r)) r  *)
(* Proof:
   Let p = char r, and prime p.
   First, x IN R ==> x ** p IN R           by ring_exp_element.
   So we need to verify F(x) = x ** p is a ring homomorphism, meaning:
   (1) Ring r /\ prime p ==> GroupHomo (\x. x ** p) (ring_sum r) (ring_sum r)
       Expanding by GroupHomo_def, this is to show:
       Ring r /\ prime p /\ x IN R /\ x' IN R ==> (x + x') ** p = x ** p + x' ** p
       which is true by ring_freshman_thm.
   (2) Ring r ==> MonoidHomo (\x. x ** p) r.prod r.prod
       Expanding by MonoidHomo_def, this is to show:
       Ring r /\ prime p /\ x IN R /\ x' IN R ==> (x * x') ** p = x ** p * x' ** p
       which is true by ring_mult_exp.
*)
val ring_char_prime_endo = store_thm(
  "ring_char_prime_endo",
  ``!r:'a ring. Ring r /\ prime (char r) ==> RingEndo (\x. x ** (char r)) r``,
  rpt strip_tac >>
  rw[RingEndo_def, RingHomo_def] >| [
    rw[GroupHomo_def] >>
    metis_tac[ring_freshman_thm],
    rw[MonoidHomo_def, ring_mult_monoid]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
