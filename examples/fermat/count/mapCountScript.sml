(* ------------------------------------------------------------------------- *)
(* Counting of maps between finite sets.                                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "mapCount";

(* ------------------------------------------------------------------------- *)

open arithmeticTheory pred_setTheory gcdsetTheory numberTheory listTheory
     rich_listTheory listRangeTheory combinatoricsTheory;

val _ = temp_overload_on("over", ``\f s t. !x. x IN s ==> f x IN t``);

(* ------------------------------------------------------------------------- *)
(* Counting of maps between finite sets Documentation                        *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   FUN_ANY         = \(x :'a). (ARB :'b)
   fun_count m n   = fun_set (count m) (count n)
   inj_count m n   = inj_set (count m) (count n)
   bij_maps s      = bij_set s s
   bij_count n     = inj_count n n
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Function on a Set:
   on_def              |- !f s. f on s = (\x. if x IN s then f x else ARB)
   on_over             |- !f s t. over f s t <=> over (f on s) s t
   on_empty            |- !f. f on {} = FUN_ANY
   on_compose          |- !f g s. f o (g on s) on s = f o g on s
   on_inj              |- !f s t. INJ (f on s) s t <=> INJ f s t
   on_surj             |- !f s t. SURJ (f on s) s t <=> SURJ f s t
   on_bij              |- !f s t. BIJ (f on s) s t <=> BIJ f s t
   on_eq               |- !f1 f2 s. f1 on s = f2 on s <=> !x. x IN s ==> f1 x = f2 x
   on_element          |- !f s t x. x IN s /\ f x IN t ==> (f on s) x IN t
   on_on               |- !f s. (f on s) on s = f on s
   on_on_compose       |- !f1 f2 s. (!x. x IN s ==> f2 x IN s) ==>
                                    (f1 on s) o (f2 on s) on s = f1 o f2 on s
   on_on_compose_assoc |- !f1 f2 f3 s. (!x. x IN s ==> f3 x IN s) ==>
                                       (f1 o f2 on s) o f3 on s = f1 o (f2 o f3 on s) on s
   bij_on_bij          |- !f s t. BIJ f s t ==> BIJ (f on s) s t
   bij_on_compose_bij  |- !f g s t u. BIJ f s t /\ BIJ g t u ==> BIJ (g o f on s) s u
   bij_on_compose      |- !f1 f2 s. f2 PERMUTES s ==>
                                    (f1 on s) o (f2 on s) on s = f1 o f2 on s
   bij_on_compose_assoc|- !f1 f2 f3 s. f3 PERMUTES s ==>
                                       (f1 o f2 on s) o f3 on s = f1 o (f2 o f3 on s) on s
   bij_on_id           |- !s. I on s PERMUTES s
   inj_on_linv         |- !f s t. INJ f s t ==> LINV f s o f on s = I on s
   bij_on_linv         |- !f s. f PERMUTES s ==> LINV f s o f on s = I on s
   INJ_I_SUBSET        |- !s t. INJ I s t <=> s SUBSET t
   INJ_I_on_SUBSET     |- !s t. INJ (I on s) s t <=> s SUBSET t
   map_on_count        |- !f n. MAP f [0 ..< n] = MAP (f on count n) [0 ..< n]
   map_on_count_length |- !f ls. set ls = count (LENGTH ls) ==>
                                 MAP f ls = MAP (f on count (LENGTH ls)) ls

   Counting number of functions:
   fun_set_def         |- !s t. fun_set s t = {f on s | f | over f s t}
   fun_set_element     |- !x s t. x IN fun_set s t <=> ?f. x = f on s /\ over f s t
   fun_set_element_alt |- !f s t. f IN fun_set s t <=>
                                  (over f s t) /\ !x. x NOTIN s ==> f x = ARB
   fun_set_alt         |- !s t. fun_set s t = {f on s | f | IMAGE f s SUBSET t}
   fun_set_empty_domain|- !s. fun_set {} s = {FUN_ANY}
   fun_set_empty_range |- !s. s <> {} ==> fun_set s {} = {}
   fun_count_element   |- !x m n. x IN fun_count m n <=>
                              ?f. x = f on count m /\ !j. j < m ==> f j < n
   fun_count_inj       |- !m n. INJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
   fun_count_surj      |- !m n. SURJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
   fun_count_bij       |- !m n. BIJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
   fun_count_finite    |- !m n. FINITE (fun_count m n)
   fun_count_card      |- !m n. CARD (fun_count m n) = n ** m
   fun_set_bij_eq      |- !s t. FINITE s /\ FINITE t ==>
                                fun_set s t =b= fun_count (CARD s) (CARD t)
   fun_set_finite      |- !s t. FINITE s /\ FINITE t ==> FINITE (fun_set s t)
   fun_set_card        |- !s t. FINITE s /\ FINITE t ==>
                                CARD (fun_set s t) = CARD t ** CARD s

   Counting number of injections:
   inj_set_def         |- !s t. inj_set s t = {f on s | f | INJ f s t}
   inj_set_element     |- !x s t. x IN inj_set s t <=> ?f. x = f on s /\ INJ f s t
   inj_set_alt         |- !s t. inj_set s t = {f | f IN fun_set s t /\ INJ f s t}
   inj_set_element_alt |- !f s t. f IN inj_set s t <=> f IN fun_set s t /\ INJ f s t
   inj_set_subset      |- !s t. inj_set s t SUBSET fun_set s t
   inj_set_finite      |- !s t. FINITE s /\ FINITE t ==> FINITE (inj_set s t)
   inj_count_element   |- !f n m. f IN inj_count m n <=>
                                  f IN fun_count m n /\ INJ f (count m) (count n)
   inj_count_eq_empty  |- !m n. inj_count m n = {} <=> n < m
   inj_count_map_element
                       |- !f m n. f IN inj_count m n ==> MAP f [0 ..< m] IN list_count n m
   inj_count_map_inj   |- !m n. INJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m)
   inj_count_map_surj  |- !m n. SURJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m)
   inj_count_map_bij   |- !m n. BIJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m)
   inj_count_bij_eq_list_count
                       |- !m n. inj_count m n =b= list_count n m
   inj_count_finite    |- !m n. FINITE (inj_count m n)
   inj_count_card      |- !m n. CARD (inj_count m n) = n arrange m
   inj_set_bij_eq_inj_count
                       |- !s t. FINITE s /\ FINITE t ==>
                                inj_set s t =b= inj_count (CARD s) (CARD t)
   inj_set_eq_empty    |- !s t. FINITE s /\ FINITE t ==>
                                (inj_set s t = {} <=> CARD t < CARD s)
   inj_set_card        |- !s t. FINITE s /\ FINITE t ==>
                                CARD (inj_set s t) = CARD t arrange CARD s

   Counting number of bijections:
   bij_set_def         |- !s t. bij_set s t = {f on s | f | BIJ f s t}
   bij_set_element     |- !x s t. x IN bij_set s t <=> ?f. x = f on s /\ BIJ f s t
   bij_set_alt         |- !s t. bij_set s t = {f | f IN fun_set s t /\ BIJ f s t}
   bij_set_element_alt |- !f s t. f IN bij_set s t <=> f IN fun_set s t /\ BIJ f s t
   bij_set_subset      |- !s t. bij_set s t SUBSET inj_set s t
   bij_set_finite      |- !s t. FINITE s /\ FINITE t ==> FINITE (bij_set s t)
   bij_set_not_empty   |- !s t. FINITE s /\ FINITE t ==>
                                (bij_set s t <> {} <=> CARD s = CARD t)
   bij_maps_thm        |- !s. bij_maps s = {f on s | f | f PERMUTES s}
   bij_maps_element    |- !x s. x IN bij_maps s <=> ?f. x = f on s /\ f PERMUTES s
   bij_maps_alt        |- !s. bij_maps s = {f | f IN fun_set s s /\ f PERMUTES s}
   bij_maps_element_alt|- !f s. f IN bij_maps s <=> f IN fun_set s s /\ f PERMUTES s
   bij_maps_subset     |- !s. bij_maps s SUBSET inj_set s s
   bij_maps_finite     |- !s. FINITE s ==> FINITE (bij_maps s)
   bij_maps_not_empty  |- !s. FINITE s ==> bij_maps s <> {}
   bij_set_map_element |- !f g s t. BIJ f t s /\ g IN bij_set s t ==>
                                    f o g on s IN bij_maps s
   bij_set_map_inj     |- !f s t. BIJ f t s ==>
                                  INJ (\g. f o g on s) (bij_set s t) (bij_maps s)
   bij_set_map_surj    |- !f s t. BIJ f t s ==>
                                  SURJ (\g. f o g on s) (bij_set s t) (bij_maps s)
   bij_set_map_bij     |- !f s t. BIJ f t s ==>
                                  BIJ (\g. f o g on s) (bij_set s t) (bij_maps s)
   bij_set_bij_eq_maps |- !s t. FINITE s /\ FINITE t /\ CARD s = CARD t ==>
                                bij_set s t =b= bij_maps s
   bij_maps_eq_inj_set |- !s. FINITE s ==> bij_maps s = inj_set s s
   bij_maps_card       |- !s. FINITE s ==> CARD (bij_maps s) = perm (CARD s)
   bij_set_card        |- !s t. FINITE s /\ FINITE t ==>
                                CARD (bij_set s t) =
                                  if CARD s = CARD t then perm (CARD s) else 0

   A direct count of bijections:
   bij_count_element   |- !x n. x IN bij_count n <=>
                            ?f. x = f on count n /\ f PERMUTES count n
   bij_count_not_empty |- !n. bij_count n <> {}
   bij_count_map_bij   |- !n. BIJ (\f. MAP f [0 ..< n]) (bij_count n) (perm_count n)
   bij_count_bij_eq_perm_count
                       |- !n. bij_count n =b= perm_count n
   bij_count_finite    |- !n. FINITE (bij_count n)
   bij_count_card      |- !n. CARD (bij_count n) = perm n
   bij_maps_bij_count  |- !n. bij_maps (count n) = bij_count n
   bij_maps_bij_eq_bij_count
                       |- !s. FINITE s ==> bij_maps s =b= bij_count (CARD s)
   bij_maps_bij_eq_perm_count
                       |- !s. FINITE s ==> bij_maps s =b= perm_count (CARD s)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Function in HOL4:
In HOL4, a function has type ('a -> 'b), which is a lambda expression,
taking input of type 'a, giving output of type 'b. For a lambda expression,
the domain and range are universal sets.
In mathematics, a function f: X -> Y is a mapping between sets. While the
sets can be universal, in most cases we are interested in functions between
known sets, and the function value f(x) for x outside the domain X is not
interesting. Therefore a function in math corresponds to many HOL4 functions,
lambda expressions that gives the same values f(x) whenever x is within domain.

Therefore, to count math functions in HOL4, it is necessary to define:
lambda f restricted to a set: f on s = if x IN s then f x else ARB

Then we can define:
fun_set s t = the set of math functions with domain s and range t.

This is different from FUNSET P Q in pred_setTheory,
which are still lambda expressions, not math functions.
*)

(* ------------------------------------------------------------------------- *)
(* Function on a Set                                                         *)
(* ------------------------------------------------------------------------- *)

(* Function with domain on a set *)
(* val _ = overload_on("on", ``\(f:'a -> 'b) (s:'a -> bool) x. if x IN s then f x else ARB``); *)
Definition on_def:
    on (f:'a -> 'b) (s:'a -> bool) = (\x. if x IN s then f x else ARB)
End
(* make this an infix operator *)
val _ = set_fixity "on" (Infix(NONASSOC, 550)); (* higher than arithmetic op 500. *)

(* Theorem: over f s t <=> over (f on s) s t *)
(* Proof: by on_def. *)
Theorem on_over:
  !f s t. over f s t <=> over (f on s) s t
Proof
  simp[on_def]
QED

(* Overload the universal function. *)
val _ = overload_on("FUN_ANY", ``\(x :'a). (ARB :'b)``);

(*
> overload_info_for "FUN_ANY";
FUN_ANY parses to:
  \(x :'a). (ARB :'b)
*)

(* Theorem: f on {} = FUN_ANY *)
(* Proof: by on_def. *)
Theorem on_empty:
  !f. f on {} = FUN_ANY
Proof
  simp[on_def]
QED
(* val on_empty = |- !f. f on {} = (\x. bool$ARB): thm *)

(* Theorem: f o (g on s) on s = f o g on s *)
(* Proof: by on_def, FUN_EQ_THM. *)
Theorem on_compose:
  !f g s. f o (g on s) on s = f o g on s
Proof
  simp[on_def, FUN_EQ_THM]
QED

(* Theorem: INJ (f on s) s t <=> INJ f s t *)
(* Proof: by INJ_DEF, on_def. *)
Theorem on_inj:
  !f s t. INJ (f on s) s t <=> INJ f s t
Proof
  simp[INJ_DEF, on_def]
QED

(* Theorem: SURJ (f on s) s t <=> SURJ f s t *)
(* Proof: by SURJ_DEF, on_def. *)
Theorem on_surj:
  !f s t. SURJ (f on s) s t <=> SURJ f s t
Proof
  simp[SURJ_DEF, on_def] >>
  metis_tac[]
QED

(* Theorem: BIJ (f on s) s t <=> BIJ f s t *)
(* Proof:
       BIJ (f on s) s t
   <=> INJ (f on s) s t /\ SURJ (f on s) s t   by BIJ_DEF
   <=> INJ f s t /\ SURJ f s t                 by on_inj, on_surj
   <=> BIJ f s t                               by BIJ_DEF
*)
Theorem on_bij:
  !f s t. BIJ (f on s) s t <=> BIJ f s t
Proof
  simp[BIJ_DEF, on_inj, on_surj]
QED

(* Theorem: (f1 on s = f2 on s) <=> !x. x IN s ==> f1 x = f2 x *)
(* Proof: by on_def. *)
Theorem on_eq:
  !f1 f2 s. (f1 on s = f2 on s) <=> !x. x IN s ==> f1 x = f2 x
Proof
  rw[on_def, EQ_IMP_THM] >>
  metis_tac[]
QED

(* Theorem: x IN s /\ f x IN t ==> (f on s) x IN t *)
(* Proof: by on_def *)
Theorem on_element:
  !f s t x. x IN s /\ f x IN t ==> (f on s) x IN t
Proof
  rw_tac std_ss[on_def]
QED

(* Theorem: (f on s) on s = f on s *)
(* Proof: by on_def *)
Theorem on_on:
  !f s. (f on s) on s = f on s
Proof
  rw_tac std_ss[on_def]
QED

(* Theorem: over f2 s s ==> (f1 on s) o (f2 on s) on s = f1 o f2 on s *)
(* Proof: by on_def *)
Theorem on_on_compose:
  !f1 f2 s. over f2 s s ==> (f1 on s) o (f2 on s) on s = f1 o f2 on s
Proof
  rw[on_def, FUN_EQ_THM]
QED

(* Theorem: (!x. x IN s ==> f3 x IN s) ==>
            (f1 o f2 on s) o f3 on s = f1 o (f2 o f3 on s) on s *)
(* Proof: by on_def, FUN_EQ_THM *)
Theorem on_on_compose_assoc:
  !f1 f2 f3 s. over f3 s s ==>
               (f1 o f2 on s) o f3 on s = f1 o (f2 o f3 on s) on s
Proof
  rw[on_def, FUN_EQ_THM]
QED

(* Theorem: BIJ f s t ==> BIJ (f on s) s t *)
(* Proof: by on_bij. *)
Theorem bij_on_bij:
  !f s t. BIJ f s t ==> BIJ (f on s) s t
Proof
  simp[on_bij]
QED

(* Theorem: BIJ f s t /\ BIJ g t u ==> BIJ (g o f on s) s u *)
(* Proof: by BIJ_DEF, INJ_DEF, SURJ_DEF, on_def *)
Theorem bij_on_compose_bij:
  !f g t u. BIJ f s t /\ BIJ g t u ==> BIJ (g o f on s) s u
Proof
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, on_def] >>
  metis_tac[]
QED

(* Theorem: f2 PERMUTES s ==> (f1 on s) o (f2 on s) on s = f1 o f2 on s *)
(* Proof: by on_on_compose, BIJ_ELEMENT *)
Theorem bij_on_compose:
  !f1 f2 s. f2 PERMUTES s ==> (f1 on s) o (f2 on s) on s = f1 o f2 on s
Proof
  metis_tac[on_on_compose, BIJ_ELEMENT]
QED

(* Theorem: f3 PERMUTES s ==> (f1 o f2 on s) o f3 on s = f1 o (f2 o f3 on s) on s *)
(* Proof: by on_on_compose_assoc, BIJ_ELEMENT *)
Theorem bij_on_compose_assoc:
  !f1 f2 f3 s. f3 PERMUTES s ==>
               (f1 o f2 on s) o f3 on s = f1 o (f2 o f3 on s) on s
Proof
  metis_tac[on_on_compose_assoc, BIJ_ELEMENT]
QED

(* Theorem: I on s PERMUTES s *)
(* Proof:
   Note I PERMUTES s           by BIJ_I_SAME
     so I on s PERMUTES s      by on_bij
*)
Theorem bij_on_id:
  !s. I on s PERMUTES s
Proof
  simp[BIJ_I_SAME, on_bij]
QED

(* Theorem: INJ f s t ==> LINV f s o f on s = I on s *)
(* Proof: by on_def, LINV_DEF. *)
Theorem inj_on_linv:
  !f s t. INJ f s t ==> LINV f s o f on s = I on s
Proof
  rw[on_def, FUN_EQ_THM] >>
  metis_tac[LINV_DEF]
QED

(* Theorem: f PERMUTES s ==> LINV f s o f on s = I on s *)
(* Proof:
   Note INJ f s t              by BIJ_DEF
     so LINV f s (f x) = x     by inj_on_linv
*)
Theorem bij_on_linv:
  !f s. f PERMUTES s ==> LINV f s o f on s = I on s
Proof
  metis_tac[BIJ_DEF, inj_on_linv]
QED

(* Theorem: INJ I s t <=> s SUBSET t *)
(* Proof:
       INJ I s t
   <=> (!x. x IN s ==> x IN t) /\
        !x y. x IN s /\ y IN s ==> x = y ==> x = y   by INJ_DEF
   <=> (!x. x IN s ==> x IN t) /\ T
   <=> s SUBSET t                                    by SUBSET_DEF
*)
Theorem INJ_I_SUBSET:
  !s t. INJ I s t <=> s SUBSET t
Proof
  simp[INJ_DEF, SUBSET_DEF]
QED

(* Theorem: INJ (I on s) s t <=> s SUBSET t *)
(* Proof:
       INJ (I on s) s t
   <=> INJ (\x. if x IN s then x else ARB) s t       by on_def
   <=> (!x. x IN s ==> x IN t) /\
        !x y. x IN s /\ y IN s ==> x = y ==> x = y   by INJ_DEF
   <=> (!x. x IN s ==> x IN t) /\ T
   <=> s SUBSET t                                    by SUBSET_DEF
*)
Theorem INJ_I_on_SUBSET:
  !s t. INJ (I on s) s t <=> s SUBSET t
Proof
  simp[on_def, INJ_DEF, SUBSET_DEF]
QED

(* Theorem: MAP f [0 ..< n] = MAP (f on count n) [0 ..< n] *)
(* Proof:
   Note LENGTH [0 ..< n] = n                           by listRangeLHI_LEN
     so LENGTH (MAP f [0 ..< n]) = n                   by LENGTH_MAP
    and LENGTH (MAP (f on count n) [0 ..< n]) = n      by LENGTH_MAP
   By LIST_EQ, it remains to show:
      !x. x < n ==> EL x (MAP f [0 ..< n]) = EL x (MAP (f on count n) [0 ..< n])
   Note x IN (count n)                   by IN_COUNT, x < n
     EL x (MAP f [0 ..< n])
   = f (EL x [0 ..< n])                  by EL_MAP
   = f x                                 by listRangeLHI_EL
   = (f on count n) x                    by on_def, x IN (count n)
   = (f on count n) (EL x [0 ..< n])     by listRangeLHI_EL
   = EL x (MAP (f on count n) [0 ..< n]) by EL_MAP
*)
Theorem map_on_count:
  !f n. MAP f [0 ..< n] = MAP (f on count n) [0 ..< n]
Proof
  rpt strip_tac >>
  irule LIST_EQ >>
  rw[on_def, EL_MAP, listRangeLHI_EL]
QED

(* Theorem: set ls = count (LENGTH ls) ==> MAP f ls = MAP (f on count (LENGTH ls)) ls *)
(* Proof:
   Let n = LENGTH ls, g = f on count n.
   Note LENGTH (MAP f ls) = n            by LENGTH_MAP
    and LENGTH (MAP g ls) = n            by LENGTH_MAP
   By LIST_EQ, it remains to show:
      !x. x < n ==> EL x (MAP f ls) = EL x (MAP g ls)
   Note EL x ls IN (count n)             by set_list_eq_count, x < n
     EL x (MAP f ls)
   = f (EL x ls)                         by EL_MAP
   = (f on count n) (EL x ls)            by on_def, EL x ls IN (count n)
   = g (EL x ls)                         by notation
   = EL x (MAP g ls)                     by EL_MAP
*)
Theorem map_on_count_length:
  !f ls. set ls = count (LENGTH ls) ==> MAP f ls = MAP (f on count (LENGTH ls)) ls
Proof
  rpt strip_tac >>
  irule LIST_EQ >>
  rw[on_def, EL_MAP] >>
  metis_tac[set_list_eq_count]
QED

(* ------------------------------------------------------------------------- *)
(* Counting number of functions.                                             *)
(* ------------------------------------------------------------------------- *)

(* The strategy:
Define the set of functions restricted to domain:
   fun_set_def         |- !s t. fun_set s t = {f on s | f | over f s t}

and show:
   fun_set_empty_domain|- !s. fun_set {} s = {FUN_ANY}
   fun_set_empty_range |- !s. s <> {} ==> fun_set s {} = {}

Next, using (MAP f [0 ..< m]) every function from (count m) to (count n) is identified with a necklace. This gives:
fun_count_bij     |- !m n. BIJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
fun_count_card    |- !m n. CARD (fun_count m n) = n ** m

Then, identifying finite sets with counting sets, due to:
FINITE_BIJ_COUNT_CARD  |- !s. FINITE s ==> count (CARD s) =b= s, where s =b= t  means ?f. BIJ f s t.

we can prove:
fun_set_bij_eq         |- !s t. FINITE s /\ FINITE t ==> fun_set s t =b= fun_count (CARD s) (CARD t)
fun_set_card           |- !s t. FINITE s /\ FINITE t ==> CARD (fun_set s t) = CARD t ** CARD s

Therefore, such a fundamental result of combinatorics takes a lot of effort, and making use of necklaces!
*)

(* The set of functions restricted to the domain. *)
Definition fun_set_def[nocompute]:
    fun_set s t = {f on s | f | over f s t}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: x IN fun_set s t <=> ?f. x = f on s /\ over f s t *)
(* Proof: by fun_set_def. *)
Theorem fun_set_element:
  !x s t. x IN fun_set s t <=> ?f. x = f on s /\ over f s t
Proof
  simp[fun_set_def]
QED

(* Theorem: f IN fun_set s t <=> (over f s t) /\ (!x. x NOTIN s ==> f x = ARB) *)
(* Proof: by fun_set_def, on_def. *)
Theorem fun_set_element_alt:
  !f s t. f IN fun_set s t <=> (over f s t) /\ (!x. x NOTIN s ==> f x = ARB)
Proof
  rw[fun_set_def, on_def] >>
  metis_tac[]
QED

(* Theorem: fun_set s t = {f on s | f | (IMAGE f s) SUBSET t} *)
(* Proof:
     fun_set s t
   = {f on s | f | over f s t}                         by fun_set_def
   = {f on s | f | !y. y IN (IMAGE f s) ==> y IN t}    by IN_IMAGE
   = {f on s | f | (IMAGE f s) SUBSET t}               by SUBSET_DEF
*)
Theorem fun_set_alt:
  !s t. fun_set s t = {f on s | f | (IMAGE f s) SUBSET t}
Proof
  rw[fun_set_def, SUBSET_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: fun_set {} s = {FUN_ANY} *)
(* Proof: by fun_set_def, on_empty, EXTENSION. *)
Theorem fun_set_empty_domain:
  !s. fun_set {} s = {FUN_ANY}
Proof
  simp[fun_set_def, on_empty, EXTENSION]
QED
(*
Note: Thus fun_set {} {} = {FUN_ANY}.
This is why n ** 0 = 1, even 0 ** 0 = 1.
Compare this with:
EMPTY_FUNSET |- !s. FUNSET {} s = univ(:'a -> 'b)
*)

(* Theorem: s <> {} ==> fun_set s {} = EMPTY *)
(* Proof: by fun_set_def, on_empty, EXTENSION. *)
Theorem fun_set_empty_range:
  !s. s <> {} ==> fun_set s {} = EMPTY
Proof
  simp[fun_set_def, EXTENSION]
QED

(* Overload function set from (count m) to (count n). *)
val _ = overload_on("fun_count", ``\m n. fun_set (count m) (count n)``);

(* Theorem: x IN fun_count m n <=>
            ?f. x = f on count m /\ !j. j < m ==> f j < n *)
(* Proof:
       x IN fun_count m n
   <=> x IN fun_set (count m) (count n)                    by notation
   <=> ?f. x = f on count m /\ over f (count m) (count n)  by fun_set_element
   <=> ?f. x = f on count m /\ !j. j < m ==> f j < n       by IN_COUNT
*)
Theorem fun_count_element:
  !x m n. x IN fun_count m n <=>
      ?f. x = f on count m /\ !j. j < m ==> f j < n
Proof
  simp[fun_set_element]
QED

(* Idea: every function f in (fun_count m n) corresponds to a necklace. *)

(* Theorem: INJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n) *)
(* Proof:
   By INJ_DEF, fun_count_element, necklace_def, this is to show:
   (1) !j. j < m ==> f j < n ==> set (MAP (f on count m) [0 ..< m]) SUBSET count n
       Since f is restricted to (count m) for [0 ..< m],
       on count m can be discarded             by on_def
       By SUBSET_DEF, this is to show:
       MEM x (MAP f [0 ..< m]) ==> x < n
           MEM x (MAP f [0 ..< m])
       <=> ?y. x = f y /\ MEM y [0 ..< m]      by MEM_MAP
       <=> ?y. x = f y /\ y < m                by listRangeLHI_MEM
       <=> x < n                               by implication
       <=> x IN (count n)                      by IN_COUNT
   (2) MAP (f' on count m) [0 ..< m] = MAP (f on count m) [0 ..< m] ==>
       f' on (count m) = f on (count m)
       Since f is restricted to (count m) for [0 ..< m],
       on count m can be discarded             by on_def
           MAP f' [0 ..< m] = MAP f [0 ..< m]
       <=> GENLIST f' m = GENLIST f m          by listRangeLHI_MAP
       <=> !x. x < m ==> f' x = f x            by GENLIST_FUN_EQ
       <=> f' on (count m) = f on (count m)    by on_def, IN_COUNT
*)
Theorem fun_count_inj:
  !m n. INJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
Proof
  rw[INJ_DEF, fun_count_element, necklace_def] >| [
    rw[on_def, SUBSET_DEF, MEM_MAP] >>
    metis_tac[],
    fs[listRangeLHI_MAP] >>
    fs[on_def, GENLIST_FUN_EQ]
  ]
QED

(* Theorem: SURJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n) *)
(* Proof:
   By SURJ_DEF, fun_count_element, necklace_def, this is to show:
   (1) !j. j < m ==> f j < n ==> set (MAP (f on count m) [0 ..< m]) SUBSET count n
       Since f is restricted to (count m) for [0 ..< m],
       on count m can be discarded          by on_def
       By SUBSET_DEF, this is to show:
       MEM x (MAP f [0 ..< m]) ==> x < n
           MEM x (MAP f [0 ..< m])
       <=> ?y. x = f y /\ MEM y [0 ..< m]   by MEM_MAP
       <=> ?y. x = f y /\ y < m             by listRangeLHI_MEM
       <=> x < n                            by implication
       <=> x IN (count n)                   by IN_COUNT
   (2) set x SUBSET count n ==>
       ?f. (?f'. f = (f' on count m) /\ !x'. x' < m ==> f' x' < n) /\
       Since f is restricted to (count m) for [0 ..< m],
       on count m can be discarded          by on_def
           MAP f [0 ..< m] = x, where m = LENGTH x.
       Let f = (\j. if j < m then EL j x else ARB).
       Take this as f and f'.
       Then f = (f' on count m)             by FUN_EQ_THM
        and !x'. x' < m ==> f' x' = EL m x'
       thus MEM (f' x') x                   by MEM_EL
        and f' x' < n                       by set x SUBSET (count n)
       Note LENGTH [0 ..< m] = k            by listRangeLHI_LEN
        and MAP f [0 ..< m] = GENLIST f m   by listRangeLHI_MAP
       Thus MAP f [0 ..< m] = x             by LIST_EQ
*)
Theorem fun_count_surj:
  !m n. SURJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
Proof
  rw[SURJ_DEF, fun_count_element, necklace_def] >| [
    rw[on_def, SUBSET_DEF, MEM_MAP] >>
    metis_tac[],
    fs[SUBSET_DEF] >>
    qabbrev_tac `m = LENGTH x` >>
    qabbrev_tac `f = \j. if j < m then EL j x else ARB` >>
    qexists_tac `f` >>
    rpt strip_tac >| [
      qexists_tac `f` >>
      simp[on_def, FUN_EQ_THM, Abbr`f`] >>
      metis_tac[MEM_EL],
      irule LIST_EQ >>
      rw[listRangeLHI_LEN, listRangeLHI_MAP, Abbr`f`, Abbr`m`]
    ]
  ]
QED

(* May need to define:
num_fun_to_list   for fun_count_inj
num_list_to_fun   for fun_count_surj
*)

(* Theorem: BIJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n) *)
(* Proof:
   Let f = (\f. MAP f [0 ..< m]),
       s = fun_count m n,
       t = necklace m n.
   By BIJ_DEF, this is to show:
   (1) INJ f s t, true       by fun_count_inj
   (2) SURJ f s t, true      by fun_count_surj
*)
Theorem fun_count_bij:
  !m n. BIJ (\f. MAP f [0 ..< m]) (fun_count m n) (necklace m n)
Proof
  simp[BIJ_DEF, fun_count_inj, fun_count_surj]
QED

(* Theorem: FINITE (fun_count m n) *)
(* Proof:
   Let f = (\f. MAP f [0 ..< m]),
       s = fun_count m n,
       t = necklace m n.
   Note BIJ f s t              by fun_count_bij
    and FINITE t               by necklace_finite
     so FINITE s               by BIJ_FINITE_IFF
*)
Theorem fun_count_finite:
  !m n. FINITE (fun_count m n)
Proof
  metis_tac[fun_count_bij, necklace_finite, BIJ_FINITE_IFF]
QED

(* Theorem: CARD (fun_count m n) = n ** m *)
(* Proof:
   Let f = (\f. MAP f [0 ..< m]),
       s = fun_count m n,
       t = necklace m n.
   Note BIJ f s t              by fun_count_bij
    and FINITE s               by fun_count_finite
     so CARD s
      = CARD t                 by FINITE_BIJ_CARD
      = n ** m                 by necklace_card
*)
Theorem fun_count_card:
  !m n. CARD (fun_count m n) = n ** m
Proof
  metis_tac[fun_count_bij, fun_count_finite, FINITE_BIJ_CARD, necklace_card]
QED

(* Idea: fun_set s t is bijective equivalent to fun_set with counts on cardinality. *)

(* Theorem: FINITE s /\ FINITE t ==> fun_set s t =b= fun_count (CARD s) (CARD t) *)
(* Proof:
   Let m = CARD s, n = CARD t.
   The goal is: fun_set s t =b= fun_count m n
   By SCHROEDER_BERNSTEIN, this is to show:
   (1) ?f. INJ f (fun_set s t) (fun_count m n)
       Note ?ele. BIJ ele (count m) s          by FINITE_BIJ_COUNT_CARD
        and ?idx. BIJ idx t (count n)          by bij_eq_count
        Now !x. x < m ==> ele x IN s           by BIJ_ELEMENT, IN_COUNT
        and !y. y IN t ==> idx y < n           by BIJ_ELEMENT, IN_COUNT

       Let g = \f j. if j < m then idx (f (ele j)) else ARB.
       Take this g.
       By INJ_DEF, fun_set_def, this is to show:
       (1) ?h. g (f on s) = (h on count m) /\ !x. x < m ==> h x < n
           Let h = \j. idx (f (ele j)).
           Take this h.
           Then g (f on s) = (h on count m)    by on_def, FUN_EQ_THM
            and !x. x < m ==> h x < n          by definition and implication
       (2) g f on s = g (f' on s) ==> f on s = f' on s
           By on_def, FUN_EQ_THM, this is to show:
              !x. x IN s ==> f x = f' x
           Let x IN s.
           Then ?j. x = ele j /\ j < m         by BIJ_IS_SURJ, IN_COUNT
           Thus idx (f x) = idx (f' x)         by g f on s = g (f' on s)
             so       f x = f' x               by BIJ_IS_INJ, idx is injective

   (2) ?g. INJ g (fun_count m n) (fun_set s t)
       Note ?idx. BIJ idx s (count m)          by bij_eq_count
        and ?ele. BIJ ele (count n) t          by FINITE_BIJ_COUNT_CARD
        Now !x. x IN s ==> idx x < m           by BIJ_ELEMENT, IN_COUNT
        and !y. y < n ==> ele y IN t           by BIJ_ELEMENT, IN_COUNT

       Let g = \f x. if x IN s then ele (f (idx x)) else ARB.
       Take this g.
       By INJ_DEF, fun_set_def, this is to show:
       (1) ?h. g (f on count m) = (h on s) /\ !x. x IN s ==> h x IN t
           Let h = \x. ele (f (idx x)).
           Take this h.
           Then g (f on count m) = (h on s)    by on_def, FUN_EQ_THM
            and !x. x IN s ==> h x IN t        by definition and implication
       (2) g (f on count m) = g (f' on count m) ==> (f on count m) = (f' on count m)
           By on_def, FUN_EQ_THM, this is to show:
              !x. x < m ==> f x = f' x
           Let x < m, so x IN count m          by IN_COUNT
           Then ?y. y IN s /\ idx y = x        by BIJ_IS_SURJ, IN_COUNT
           Thus ele (f x) = ele (f' x)         by g (f on count m) = g (f' on count m)
             so       f x = f' x               by BIJ_IS_INJ, ele is injective
*)
Theorem fun_set_bij_eq:
  !s t. FINITE s /\ FINITE t ==> fun_set s t =b= fun_count (CARD s) (CARD t)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = CARD s` >>
  qabbrev_tac `n = CARD t` >>
  irule SCHROEDER_BERNSTEIN >>
  rpt strip_tac >| [
    `?ele. BIJ ele (count m) s` by rw[FINITE_BIJ_COUNT_CARD, Abbr`m`] >>
    `?idx. BIJ idx t (count n)` by rw[bij_eq_count, Abbr`n`] >>
    `!x. x < m ==> ele x IN s` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    `!y. y IN t ==> idx y < n` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    qabbrev_tac `g = \f j. if j < m then idx (f (ele j)) else ARB` >>
    qexists_tac `g` >>
    rw[INJ_DEF, fun_set_def] >| [
      qabbrev_tac `h = \j. idx (f (ele j))` >>
      qexists_tac `h` >>
      rw[on_def, FUN_EQ_THM, Abbr`g`, Abbr`h`],
      fs[on_def, FUN_EQ_THM] >>
      rpt strip_tac >>
      (Cases_on `x IN s` >> simp[]) >>
      fs[FUN_EQ_THM, Abbr`g`] >>
      `?j. x = ele j /\ j < m` by prove_tac[BIJ_IS_SURJ, IN_COUNT] >>
      metis_tac[BIJ_IS_INJ]
    ],
    `?idx. BIJ idx s (count m)` by rw[bij_eq_count, Abbr`m`] >>
    `?ele. BIJ ele (count n) t` by rw[FINITE_BIJ_COUNT_CARD, Abbr`n`] >>
    `!x. x IN s ==> idx x < m` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    `!y. y < n ==> ele y IN t` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    qabbrev_tac `g = \f x. if x IN s then ele (f (idx x)) else ARB` >>
    qexists_tac `g` >>
    rw[INJ_DEF, fun_set_def] >| [
      qabbrev_tac `h = \x. ele (f (idx x))` >>
      qexists_tac `h` >>
      rw[on_def, FUN_EQ_THM, Abbr`g`, Abbr`h`],
      fs[on_def, FUN_EQ_THM] >>
      rpt strip_tac >>
      (Cases_on `x < m` >> simp[]) >>
      fs[FUN_EQ_THM, Abbr`g`] >>
      `?y. y IN s /\ idx y = x` by prove_tac[BIJ_IS_SURJ, IN_COUNT] >>
      first_x_assum (qspec_then `y` strip_assume_tac) >>
      rfs[] >>
      metis_tac[BIJ_IS_INJ, IN_COUNT]
    ]
  ]
QED

(* Theorem: FINITE s /\ FINITE t ==>  FINITE (fun_set s t) *)
(* Proof:
   Let m = CARD s, n = CARD t.
       P = fun_count m n,
       Q = fun_set s t
   Note Q =b= P                    by fun_set_bij_eq
    and FINITE P                   by fun_count_finite
     so FINITE Q                   by BIJ_FINITE_IFF
*)
Theorem fun_set_finite:
  !s t. FINITE s /\ FINITE t ==>  FINITE (fun_set s t)
Proof
  metis_tac[fun_set_bij_eq, fun_count_finite, BIJ_FINITE_IFF]
QED

(* Theorem: FINITE s /\ FINITE t ==> CARD (fun_set s t) = (CARD t) ** (CARD s) *)
(* Proof:
   Let m = CARD s, n = CARD t.
       P = fun_count m n,
       Q = fun_set s t
   Note Q =b= P                    by fun_set_bij_eq
    and FINITE Q                   by fun_set_finite
     so CARD Q
      = CARD P                     by FINITE_BIJ_CARD
      = n ** m                     by fun_count_card
*)
Theorem fun_set_card:
  !s t. FINITE s /\ FINITE t ==> CARD (fun_set s t) = (CARD t) ** (CARD s)
Proof
  metis_tac[fun_set_bij_eq, fun_set_finite, FINITE_BIJ_CARD, fun_count_card]
QED

(* This is a key theorem for counting in combinatorics. *)

(* ------------------------------------------------------------------------- *)
(* Counting types of functions between finite sets.                          *)
(* ------------------------------------------------------------------------- *)

(* Note:

Counting Bijective, Injective, and Surjective Functions
https://blog.jpolak.org/?p=1773
posted by Jason Polak on Wednesday March 1, 2017

Bijective Functions
The number of bijective functions [n]→[n] is the familiar factorial: n! = 1 x 2 x ... x n.

Another name for a bijection [n]→[n] is a permutation. In fact, the set all permutations [n]→[n]
 form a group whose multiplication is function composition.

Injective Functions
What about injective functions [k]→[n] where 1 ≤ k ≤n ? In that case, the image in [n]
 consists of k elements, and the order in which they are chosen determines the function,
so the number of injective functions [k]→[n] is k!C(n,k) = P(n,k).

Surjective Functions
Calculating the number of surjective functions [n]→[k] where n ≥ k ≥1 is the most interesting.
Let's denote by S(n,k) this number. For example, S(n,n)=n! and S(n,1)=1.
A degenerate case is S(0,0)=1, though S(n,0)=0.
Another easy to calculate one is S(n,2) = 2^n – 2: this is because there are 2^n functions [n]→[2],
but two of them send everything to just one element. What about an explicit formula in general?

The most natural thing to do is perhaps come up with a recurrence relation.
So let's divide up the number of surjective functions into two classes:
the first is where if we restrict the function to [n−1], we still get a surjective function.
It's clear there are kS(n−1,k) of these. On the other hand, if after restricting to [n−1]
 the function is no longer surjective, then there are kS(n−1,k−1) of these,
because to make such a function you choose one element in [k] that has n mapping to it,
and then a surjective function [n−1] onto the remaining k−1 elements.
Thus, we have the recurrence relation: S(n,k) = kS(n−1,k) + kS(n−1,k−1).

What about an explicit formula that is not a recurrence relation?
To find one, we can use the generating function technique.
S(n,k) = SUM (from j = 1 to k) \frac{(-1)^{k-j}k! j^{n}}{j!(k - j)!}.

Some readers may recognize that this formula is very similar to the one
for the number of partitions of [n] into k nonempty subsets.
In fact it's k! times this number. That makes good combinatorial sense:
to make a surjective function, you first partition [n] into k nonempty subsets,
and then in one of k! ways, assign one of these subsets for each element in [k].

*)

(* ------------------------------------------------------------------------- *)
(* Counting number of injections.                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the set of injections from s to t. *)
Definition inj_set_def[nocompute]:
    inj_set s t = {f on s | f | INJ f s t}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: x IN inj_set s t <=> ?f. x = f on s /\ INJ f s t *)
(* Proof: by inj_set_def. *)
Theorem inj_set_element:
  !x s t. x IN inj_set s t <=> ?f. x = f on s /\ INJ f s t
Proof
  simp[inj_set_def]
QED

(* Theorem: inj_set s t = {f | f IN fun_set s t /\ INJ f s t} *)
(* Proof:
   By inj_set_def, EXTENSION, this is to show:
   If part: INJ f s t ==> f on s IN fun_set s t /\ INJ (f on s) s t
      Note f on s IN fun_set s t   by fun_set_def, over_inj
       and INJ (f on s) s t        by on_inj, INJ f s t
   Only-if part: x IN fun_set s t /\ INJ x s t ==> ?f. x = f on s /\ INJ f s t
      Note ?f. x = f on s          by fun_set_def
      Take this f, and INJ f s t   by on_inj, INJ x s t
*)
Theorem inj_set_alt:
  !s t. inj_set s t = {f | f IN fun_set s t /\ INJ f s t}
Proof
  rw[inj_set_def, EXTENSION, EQ_IMP_THM] >| [
    simp[fun_set_def] >>
    metis_tac[over_inj],
    simp[on_inj],
    fs[fun_set_def] >>
    metis_tac[on_inj]
  ]
QED

(* Theorem: f IN inj_set s t <=> f IN fun_set s t /\ INJ f s t *)
(* Proof: by inj_set_alt. *)
Theorem inj_set_element_alt:
  !f s t. f IN inj_set s t <=> f IN fun_set s t /\ INJ f s t
Proof
  simp[inj_set_alt]
QED

(* Theorem: inj_set s t SUBSET fun_set s t *)
(* Proof: by inj_set_alt, SUBSET_DEF. *)
Theorem inj_set_subset:
  !s t. inj_set s t SUBSET fun_set s t
Proof
  simp[inj_set_alt, SUBSET_DEF]
QED

(* Theorem: FINITE s /\ FINITE t ==> FINITE (inj_set s t) *)
(* Proof:
   Note inj_set s t SUBSET fun_set s t         by inj_set_subset
    and FINITE (fun_set s t)                   by fun_set_finite
     so FINITE (inj_set s t)                   by SUBSET_FINITE
*)
Theorem inj_set_finite:
  !s t. FINITE s /\ FINITE t ==> FINITE (inj_set s t)
Proof
  metis_tac[inj_set_subset, fun_set_finite, SUBSET_FINITE]
QED

(* Overload inj_set from (count m) to (count n). *)
val _ = overload_on("inj_count", ``\m n. inj_set (count m) (count n)``);

(* derive theorem *)
Theorem inj_count_element =
   inj_set_element |> ISPEC ``x:num -> num`` |> ISPEC ``count m``
                   |> ISPEC ``count n`` |> SIMP_RULE (srw_ss()) [fun_set_def]
                   |> GEN ``m:num`` |> GEN ``n:num`` |> GEN_ALL;
(* val inj_count_element =
   |- !x n m. x IN inj_count m n <=>
          ?f. x = f on count m /\ INJ f (count m) (count n): thm *)

(* Theorem: inj_count m n = {} <=> n < m *)
(* Proof:
   If part: inj_count m n = {} ==> n < m
      By contradiction, suppose m <= n.
      Then (count m) SUBSET (count n)          by COUNT_SUBSET, m <= n
      Let f = I on (count m).
      Then INJ I (count m) (count n)           by INJ_I_SUBSET
       and f IN fun_count m n                  by fun_set_def
        so f IN inj_count m n                  by inj_count_element
      This contradicts inj_count m n = {}      by MEMBER_NOT_EMPTY
   Only-if part: n < m ==> inj_count m n = {}
      By contradiction, suppose inj_count m n <> {}.
      Then ?f. f IN inj_count m n              by MEMBER_NOT_EMPTY
      Let s = count m, t = count n.
       so INJ f s t                            by inj_count_element
      But FINITE (count n)                     by FINITE_COUNT
      and CARD s = m, CARD t = n               by CARD_COUNT
      This contradicts the Pigeonhole principle with n < m.
*)
Theorem inj_count_eq_empty:
  !m n. inj_count m n = {} <=> n < m
Proof
  rw[inj_set_def, EXTENSION, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `count m SUBSET count n` by rw[COUNT_SUBSET] >>
    `INJ I (count m) (count n)` by rw[INJ_I_SUBSET] >>
    metis_tac[],
    `FINITE (count n)` by rw[] >>
    metis_tac[PHP, CARD_COUNT]
  ]
QED

(* Idea: every INJ in inj_count can be encoded as a list in list_count *)

(* Theorem: f IN inj_count m n ==> MAP f [0 ..< m] IN list_count n m *)
(* Proof:
   Note f IN fun_count m n /\ INJ f (count m) (count n)  by inj_set_alt
   By list_count_def, this is to show:
   (1) ALL_DISTINCT (MAP f [0 ..< m])
       Note ALL_DISTINCT [0 ..< m]             by listRangeLHI_ALL_DISTINCT
        and MEM x [0 ..< m] <=> x IN count m   by listRangeLHI_MEM, IN_COUNT
         so f x = f y ==> x = y                by INJ_DEF
       Thus ALL_DISTINCT (MAP f [0 ..< m])     by ALL_DISTINCT_MAP_INJ
   (2) set (MAP f [0 ..< m]) SUBSET count n
       Note set (MAP f [0 ..< m])
          = IMAGE f (set [0 ..< m])            by LIST_TO_SET_MAP
          = IMAGE f (count m)                  by listRangeLHI_SET
        and IMAGE f (count m) SUBSET (count n) by INJ_IMAGE_SUBSET
*)
Theorem inj_count_map_element:
  !f m n. f IN inj_count m n ==> MAP f [0 ..< m] IN list_count n m
Proof
  rw[inj_set_alt, list_count_def] >| [
    `ALL_DISTINCT [0 ..< m]` by rw[] >>
    `!x y. MEM x [0 ..< m] /\ MEM y [0 ..< m] /\ f x = f y ==> x = y` by fs[INJ_DEF] >>
    simp[ALL_DISTINCT_MAP_INJ],
    simp[LIST_TO_SET_MAP, listRangeLHI_SET, INJ_IMAGE_SUBSET]
  ]
QED

(* Theorem: INJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) f IN inj_count m n ==> MAP f [0 ..< m] IN list_count n m
       This is true                                    by inj_count_map_element
   (2) g IN inj_count m n /\ f IN inj_count m n /\
       MAP g [0 ..< m] = MAP f [0 ..< m] ==> g = f
       Note f and g are restricted to x IN (count m)   by inj_set_alt
         or f and g are restricted to x < m            by IN_COUNT
         so MEM x [0 ..< m]                            by listRangeLHI_MEM
        and g x = f x                                  by listRangeLHI_MAP, GENLIST_FUN_EQ
       Thus g = x                                      by FUN_EQ_THM
*)
Theorem inj_count_map_inj:
  !m n. INJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m)
Proof
  rw[INJ_DEF] >-
  simp[inj_count_map_element] >>
  rw[FUN_EQ_THM] >>
  fs[inj_set_alt] >>
  (Cases_on `x < m` >> fs[fun_set_def, on_def]) >>
  rfs[listRangeLHI_MAP, GENLIST_FUN_EQ]
QED

(* Theorem: SURJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) f IN inj_count m n ==> MAP f [0 ..< m] IN list_count n m
       This is true                            by inj_count_map_element
   (2) x IN list_count n m ==>
       ?f. f IN inj_count m n /\ MAP f [0 ..< m] = x
       Take (f on count m), where f = (\j. EL j x).
       By inj_set_alt, this is to show:
       (1) f on count m IN fun_count m n
           Note ALL_DISTINCT x /\
                set x SUBSET count n /\
                LENGTH x = m                   by list_count_element
           Thus !k. MEM k x ==> k < n          by SUBSET_DEF, IN_COUNT
             so !j. j < m ==> EL j j < n       by MEM_EL
             or !j. j < m ==> f j < n          by notation
             so f on count m IN fun_count m n  by fun_set_element, IN_COUNT
       (2) INJ (f on count m) (count m) (count n)
           By INJ_DEF, this is to show:
           (1) k < m ==> (f on count m) k < n
               Note set x SUBSET count n       by list_count_element
               Thus !k. MEM k x ==> k < n      by SUBSET_DEF, IN_COUNT
                 so !j. j < m ==> EL j j < n   by MEM_EL
                 or !j. j < m ==> f j < n      by notation
           (2) h < m /\ k < m /\ (f on count m) h = (f on count m) k ==> h = k
               Note EL h x = EL k x            by on_def, notation
                but ALL_DISTINCT x             by list_count_element
                 so h = k                      by ALL_DISTINCT_EL_IMP
       (3) MAP (f on count m) [0 ..< m] = x
           By LIST_EQ, this is to show:
           (1) !k. k < LENGTH (MAP (f on count m) [0 ..< m]) ==>
                   EL k (MAP (f on count m) [0 ..< m]) = EL k x)
                 LENGTH (MAP (f on count m) [0 ..< m])
               = LENGTH [0 ..< m]              by LENGTH_MAP
               = m                             by listRangeLHI_LEN
                 EL k (MAP (f on count m) [0 ..< m])
               = f (EL k [0 ..< m])            by EL_MAP, on_def
               = f k                           by listRangeLHI_EL
               = EL k x                        by notation
           (2) LENGTH (MAP (f on count m) [0 ..< m]) = LENGTH x
                 LENGTH (MAP (f on count m) [0 ..< m])
               = LENGTH [0 ..< m]              by LENGTH_MAP
               = m                             by listRangeLHI_LEN
               = LENGTH x                      by list_count_element
*)
Theorem inj_count_map_surj:
  !m n. SURJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m)
Proof
  rw[SURJ_DEF] >-
  simp[inj_count_map_element] >>
  qabbrev_tac `f = \j. EL j x` >>
  qexists_tac `f on (count m)` >>
  rw[inj_set_alt] >| [
    fs[list_count_def, SUBSET_DEF] >>
    simp[fun_set_def] >>
    qexists_tac `f` >>
    fs[EL_MEM, Abbr`f`],
    rw[INJ_DEF, on_def, Abbr`f`] >-
    fs[list_count_def, EL_MEM, SUBSET_DEF] >>
    rfs[list_count_def, SUBSET_DEF, ALL_DISTINCT_EL_IMP],
    irule LIST_EQ >>
    rw[listRangeLHI_MAP, on_def, Abbr`f`] >>
    fs[list_count_def]
  ]
QED

(* Theorem: BIJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m) *)
(* Proof:
   Let g = (\f. MAP f [0 ..< m]), s = inj_count m n, t = list_count n m.
   Note  INJ g s t             by inj_count_map_inj
    and SURJ g s t             by inj_count_map_surj
     so  BIJ g s t             by BIJ_DEF
*)
Theorem inj_count_map_bij:
  !m n. BIJ (\f. MAP f [0 ..< m]) (inj_count m n) (list_count n m)
Proof
  simp[BIJ_DEF, inj_count_map_inj, inj_count_map_surj]
QED

(* Theorem: inj_count m n =b= list_count n m *)
(* Proof:
   Let g = (\f. MAP f [0 ..< m]).
   Note BIJ g (inj_count m n) (list_count n m) by inj_count_map_bij
   Thus (inj_count m n) =b= (list_count n m)   by notation
*)
Theorem inj_count_bij_eq_list_count:
  !m n. inj_count m n =b= list_count n m
Proof
  metis_tac[inj_count_map_bij]
QED

(* Theorem: FINITE (inj_count m n) *)
(* Proof:
   Note inj_count m n =b= list_count n m       by inj_count_bij_eq_list_count
    and FINITE (list_count n m)                by list_count_finite
     so FINITE (inj_count m n)                 by bij_eq_finite
*)
Theorem inj_count_finite:
  !m n. FINITE (inj_count m n)
Proof
  metis_tac[inj_count_bij_eq_list_count, list_count_finite, bij_eq_finite]
QED

(* Theorem: CARD (inj_count m n) = n arrange m *)
(* Proof:
   Note inj_count m n =b= list_count n m       by inj_count_bij_eq_list_count
    and FINITE (list_count n m)                by list_count_finite
     CARD (inj_count m n)
   = CARD (list_count n m)                     by bij_eq_card
   = n arrange m                               by arrange_def
*)
Theorem inj_count_card:
  !m n. CARD (inj_count m n) = n arrange m
Proof
  metis_tac[inj_count_bij_eq_list_count, list_count_finite, bij_eq_card, arrange_def]
QED

(* This is a major result! *)

(* Theorem: FINITE s /\ FINITE t ==>
            inj_set s t =b= inj_count (CARD s) (CARD t) *)
(* Proof:
   Let m = CARD s, n = CARD t.
   By SCHROEDER_BERNSTEIN, this is to show:
   (1) ?f. INJ f (inj_set s t) (inj_count m n)
       Note ?ele. BIJ ele (count m) s              by FINITE_BIJ_COUNT_CARD
        and ?idx. BIJ idx t (count n)              by bij_eq_count
        Now !x. x < m ==> ele x IN s               by BIJ_ELEMENT, IN_COUNT
        and !y. y IN t ==> idx y < n               by BIJ_ELEMENT, IN_COUNT

       Let g = \f j. if j < m then idx (f (ele j)) else ARB.
       Take this g, to show: INJ g (inj_set s t) (inj_count m n)
       By INJ_DEF, this is to show:
       (1) x IN inj_set s t ==> g x IN inj_count m n
           By inj_set_def, fun_set_def, ?f. x = f on s, and this is to show:
           (1) ?h. g f on s = (h on count m) /\ !x. x < m ==> h x < n
               Let h = \j. idx (x (ele j)).
               Take this h.
               Then g f on s = (h on count m)      by on_def, FUN_EQ_THM
                and !x. x < m ==> h x < n          by definition and implication
           (2) INJ (f on s) s t ==> INJ (g f on s) (count m) (count n)
               By INJ_DEF, on_def, this is to show:
                  x < m /\ y < m /\ idx (f (ele x)) = idx (f (ele y)) ==> x = y
               Note f (ele x) = f (ele y)          by BIJ_IS_INJ for idx
                 so     ele x = ele y              by INJ_DEF, on_def for f on s
                 or         x = y                  by BIJ_IS_INJ for ele
       (2) x IN inj_set s t /\ y IN inj_set s t /\ g x = g y ==> x = y
           Note ?f1. x = (f1 on s) /\ INJ x s t    by inj_set_def, fun_set_def
            and ?f2. y = (f2 on s) /\ INJ y s t    by inj_set_def, fun_set_def
           For z IN s,
                ?k. k IN (count m) /\ z = ele k    by BIJ_DEF, SURJ_DEF for ele
                  g x = g y
            ==> g x k = g y k  for k < m           by FUN_EQ_THM, IN_COUNT
            ==> idx (x (ele k)) = idx (y (ele k))  by notation
            ==>       x (ele k) = y (ele k)        by BIJ_IS_INJ for idx
            ==>             x z = y z              by z = ele k, z IN s
            ==>               x = y                by FUN_EQ_THM

   (2) ?g. INJ g (inj_count m n) (inj_set s t)
       Note ?idx. BIJ idx s (count m)              by bij_eq_count
        and ?ele. BIJ ele (count n) t              by FINITE_BIJ_COUNT_CARD
        Now !x. x IN s ==> idx x < m               by BIJ_ELEMENT, IN_COUNT
        and !y. y < n ==> ele y IN t               by BIJ_ELEMENT, IN_COUNT
       Let g = \f x. if x IN s then ele (f (idx x)) else ARB.
       Take this g, to show: INJ g (inj_count m n) (inj_set s t)
       By INJ_DEF, this is to show:
       (1) x IN inj_count m n ==> g x IN inj_set s t
           By inj_set_alt, fun_set_def, ?f. x = f on count m, and this is to show:
           (1) ?h. g (f on count m) = (h on s) /\ !x. x IN s ==> h x IN t
               Let h = \z. ele (x (idx z)).
               Take this h.
               Then g (f on count m) = (h on s)    by on_def, FUN_EQ_THM
                and !x. x IN s ==> h x IN t        by definition and implication
           (2) INJ x (count m) (count n) ==> INJ (g (f on count m)) s t
               By INJ_DEF, on_def, this is to show:
                  x IN s /\ y IN s /\ ele (f (idx x)) = ele (f (idx y)) ==> x = y
               Note f (idx x) = f (idx y)          by BIJ_IS_INJ for ele
                 so     idx x = idx y              by INJ_DEF, on_def for f on s
                 or         x = y                  by BIJ_IS_INJ for idx
       (2) x IN inj_count m n /\ y IN inj_count m n /\ g x = g y ==> x = y
           Note ?f1. x = (f1 on count m) /\ INJ x (count m) (count n)
                                                   by inj_set_def, fun_set_def
            and ?f2. y = (f2 on count m) /\ INJ y (count m) (count n)
                                                   by inj_set_def, fun_set_def
           For k IN count m,
                ?z. z IN s /\ idx z = k            by BIJ_IS_SURJ for idx
                  g x = g y
            ==> g x z = g y z  for z IN s          by FUN_EQ_THM
            ==> ele (x (idx z)) = ele (y (idz z))  by notation
            ==>       x (idx z) = y (idz z)        by BIJ_IS_INJ for ele
            ==>             x k = y k              by idx z = k, z IN s
            ==>               x = y                by FUN_EQ_THM
*)
Theorem inj_set_bij_eq_inj_count:
  !s t. FINITE s /\ FINITE t ==>
        inj_set s t =b= inj_count (CARD s) (CARD t)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = CARD s` >>
  qabbrev_tac `n = CARD t` >>
  irule SCHROEDER_BERNSTEIN >>
  rpt strip_tac >| [
    `?ele. BIJ ele (count m) s` by rw[FINITE_BIJ_COUNT_CARD, Abbr`m`] >>
    `?idx. BIJ idx t (count n)` by rw[bij_eq_count, Abbr`n`] >>
    `!x. x < m ==> ele x IN s` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    `!y. y IN t ==> idx y < n` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    qabbrev_tac `g = \f j. if j < m then idx (f (ele j)) else ARB` >>
    qexists_tac `g` >>
    rw[INJ_DEF] >| [
      fs[inj_set_alt, fun_set_def] >>
      rpt strip_tac >| [
        qabbrev_tac `f = (\j. idx (x (ele j)))` >>
        qexists_tac `f` >>
        fs[on_def, Abbr`g`, Abbr`f`],
        rw[INJ_DEF, on_def, Abbr`g`] >>
        fs[INJ_DEF, on_def] >>
        metis_tac[BIJ_IS_INJ, IN_COUNT]
      ],
      fs[inj_set_alt, fun_set_def] >>
      rw[on_def, FUN_EQ_THM] >>
      (Cases_on `x IN s` >> simp[]) >>
      rfs[INJ_DEF, on_def, Abbr`g`] >>
      fs[FUN_EQ_THM] >>
      `?k. k IN (count m) /\ x = ele k` by metis_tac[BIJ_IS_SURJ] >>
      metis_tac[BIJ_IS_INJ, IN_COUNT]
    ],
    `?idx. BIJ idx s (count m)` by rw[bij_eq_count, Abbr`m`] >>
    `?ele. BIJ ele (count n) t` by rw[FINITE_BIJ_COUNT_CARD, Abbr`n`] >>
    `!x. x IN s ==> idx x < m` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    `!y. y < n ==> ele y IN t` by metis_tac[BIJ_ELEMENT, IN_COUNT] >>
    qabbrev_tac `g = \f x. if x IN s then ele (f (idx x)) else ARB` >>
    qexists_tac `g` >>
    rw[INJ_DEF] >| [
      fs[inj_set_alt, fun_set_def] >>
      rpt strip_tac >| [
        qabbrev_tac `f = (\z. ele (x (idx z)))` >>
        qexists_tac `f` >>
        fs[on_def, Abbr`g`, Abbr`f`],
        rw[INJ_DEF, on_def, Abbr`g`] >>
        fs[INJ_DEF, on_def] >>
        metis_tac[BIJ_IS_INJ, IN_COUNT]
      ],
      fs[inj_set_alt, fun_set_def] >>
      rw[on_def, FUN_EQ_THM, Abbr`g`] >>
      (Cases_on `x < m` >> simp[]) >>
      fs[on_def, FUN_EQ_THM] >>
      `?y. y IN s /\ idx y = x` by prove_tac[BIJ_IS_SURJ, IN_COUNT] >>
      metis_tac[BIJ_IS_INJ, IN_COUNT]
    ]
  ]
QED

(* Theorem: FINITE s /\ FINITE t ==> (inj_set s t = {} <=> CARD t < CARD s) *)
(* Proof:
   Let m = CARD s, n = CARD t.
   Note inj_set s t =b= inj_count m n    by inj_set_bij_eq_inj_count
       inj_set s t = {}
   <=> (inj_count m n) = {}              by bij_eq_empty
   <=> n < m                             by inj_count_eq_empty
*)
Theorem inj_set_eq_empty:
  !s t. FINITE s /\ FINITE t ==> (inj_set s t = {} <=> CARD t < CARD s)
Proof
  metis_tac[inj_set_bij_eq_inj_count, bij_eq_empty, inj_count_eq_empty]
QED

(* Theorem: FINITE s /\ FINITE t ==>
            CARD (inj_set s t) = (CARD t) arrange (CARD s) *)
(* Proof:
   Let m = CARD s, n = CARD t.
   Note inj_set s t =b= inj_count m n    by inj_set_bij_eq_inj_count
    and FINITE (inj_count m n)           by inj_count_finite
       CARD (inj_set s t)
     = CARD (inj_count m n)              by bij_eq_card
     = n arrange m                       by inj_count_card
*)
Theorem inj_set_card:
  !s t. FINITE s /\ FINITE t ==>
        CARD (inj_set s t) = (CARD t) arrange (CARD s)
Proof
  metis_tac[inj_set_bij_eq_inj_count, inj_count_finite, bij_eq_card, inj_count_card]
QED

(* ------------------------------------------------------------------------- *)
(* Counting number of bijections.                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the set of bijections from s to t. *)
Definition bij_set_def[nocompute]:
    bij_set s t = {f on s | f | BIJ f s t}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: x IN bij_set s t <=> ?f. x = f on s /\ BIJ f s t *)
(* Proof: by bij_set_def. *)
Theorem bij_set_element:
  !x s t. x IN bij_set s t <=> ?f. x = f on s /\ BIJ f s t
Proof
  simp[bij_set_def]
QED

(* Theorem: bij_set s t = {f | f IN fun_set s t /\ BIJ f s t} *)
(* Proof:
   By bij_set_def, EXTENSION, this is to show:
   (2) BIJ f s t ==> (f on s) IN fun_set s t /\ BIJ (f on s) s t
       Note (f on s) IN fun_set s t      by fun_set_def, over_bij
        and BIJ (f on s) s t             by on_bij, BIJ f s t

   (1) x IN fun_set s t /\ BIJ x s t ==> ?f. x = f on s /\ BIJ f s t
       Note ?f. x = f on s               by fun_set_def
       Take this f.
       Then BIJ f s t                    by on_bij, BIJ x s t
*)
Theorem bij_set_alt:
  !s t. bij_set s t = {f | f IN fun_set s t /\ BIJ f s t}
Proof
  rw[bij_set_def, EXTENSION, EQ_IMP_THM] >| [
    simp[fun_set_def] >>
    metis_tac[over_bij],
    simp[on_bij],
    fs[fun_set_def] >>
    metis_tac[on_bij]
  ]
QED

(* Theorem: f IN inj_set s t <=> f IN fun_set s t /\ BIJ f s t *)
(* Proof: by bij_set_def. *)
Theorem bij_set_element_alt:
  !f s t. f IN bij_set s t <=> f IN fun_set s t /\ BIJ f s t
Proof
  simp[bij_set_alt]
QED

(* Theorem: bij_set s t SUBSET inj_set s t *)
(* Proof:
       f IN bij_set s t
   <=> f IN fun_set s t /\ BIJ f s t     by bij_set_element_alt
   ==> f IN fun_set s t /\ INJ f s t     by BIJ_DEF
   <=> f IN inj_set s t                  by inj_set_element_alt
   Thus bij_set s t SUBSET inj_set s t   by SUBSET_DEF
*)
Theorem bij_set_subset:
  !s t. bij_set s t SUBSET inj_set s t
Proof
  simp[bij_set_alt, inj_set_alt, BIJ_DEF, SUBSET_DEF]
QED

(* Theorem: FINITE s /\ FINITE t ==> FINITE (bij_set s t) *)
(* Proof:
   Note bij_set s t SUBSET inj_set s t   by bij_set_subset
    and FINITE (inj_set s t)             by inj_set_finite
     so FINITE (bij_set s t)             by SUBSET_FINITE
*)
Theorem bij_set_finite:
  !s t. FINITE s /\ FINITE t ==> FINITE (bij_set s t)
Proof
  metis_tac[bij_set_subset, inj_set_finite, SUBSET_FINITE]
QED

(* Theorem: FINITE s /\ FINITE t ==>
            (bij_set s t <> {} <=> CARD s = CARD t) *)
(* Proof:
   If part: bij_set s t <> {} ==> CARD s = CARD t
      Note ?f. f IN bij_set s t    by MEMBER_NOT_EMPTY
       ==> BIJ f s t               by bij_set_element_alt
      Thus CARD s = CARD t         by bij_eq_card
   Only-if part: CARD s = CARD t ==> bij_set s t <> {}
      Note ?f. BIJ f s t           by bij_eq_card_eq
        so BIJ (f on s) s t        by on_bij
      Thus f on s IN bij_set s t   by bij_set_element_alt, fun_set_element, over_bij
        or bij_set s t <> {}       by MEMBER_NOT_EMPTY
*)
Theorem bij_set_not_empty:
  !s t. FINITE s /\ FINITE t ==>
        (bij_set s t <> {} <=> CARD s = CARD t)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[MEMBER_NOT_EMPTY, bij_set_element_alt, bij_eq_card] >>
  `?f. BIJ f s t` by rw[bij_eq_card_eq] >>
  `f on s IN bij_set s t` by
  (rw[bij_set_alt, fun_set_def] >-
  metis_tac[over_bij] >>
  metis_tac[on_bij]
  ) >>
  metis_tac[MEMBER_NOT_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* Permutation maps of a set.                                                *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of permutation maps. *)
val _ = overload_on("bij_maps", ``\s. bij_set s s``);

(* Theorem: bij_maps s = {f on s | f | f PERMUTES s} *)
(* Proof: by bij_set_def. *)
Theorem bij_maps_thm:
  !s. bij_maps s = {f on s | f | f PERMUTES s}
Proof
  simp[bij_set_def]
QED

(* Theorem: x IN bij_maps s <=> ?f. x = f on s /\ f PERMUTES s *)
(* Proof: by bij_set_element. *)
Theorem bij_maps_element:
  !x s. x IN bij_maps s <=> ?f. x = f on s /\ f PERMUTES s
Proof
  simp[bij_set_element]
QED

(* Theorem: bij_maps s = {f | f IN fun_set s s /\ f PERMUTES s} *)
(* Proof: by bij_set_alt. *)
Theorem bij_maps_alt:
  !s. bij_maps s = {f | f IN fun_set s s /\ f PERMUTES s}
Proof
  simp[bij_set_alt]
QED

(* Theorem: f IN bij_maps s <=> f IN fun_set s s /\ f PERMUTES s *)
(* Proof: by bij_set_element_alt. *)
Theorem bij_maps_element_alt:
  !f s. f IN bij_maps s <=> f IN fun_set s s /\ f PERMUTES s
Proof
  simp[bij_set_element_alt]
QED

(* Theorem: bij_maps s SUBSET inj_set s s *)
(* Proof: by bij_set_subset. *)
Theorem bij_maps_subset:
  !s. bij_maps s SUBSET inj_set s s
Proof
  simp[bij_set_subset]
QED

(* Theorem: FINITE s ==> FINITE (bij_maps s) *)
(* Proof: by bij_set_finite. *)
Theorem bij_maps_finite:
  !s. FINITE s ==> FINITE (bij_maps s)
Proof
  simp[bij_set_finite]
QED

(* Theorem: FINITE s ==> bij_maps s <> {} *)
(* Proof: by bij_set_not_empty. *)
Theorem bij_maps_not_empty:
  !s. FINITE s ==> bij_maps s <> {}
Proof
  simp[bij_set_not_empty]
QED

(* Theorem: BIJ f t s /\ g IN bij_set s t ==> (f o g) on s IN bij_maps s *)
(* Proof:
   Note BIJ g s t                  by bij_set_element_alt
   By bij_set_def, fun_set_def, this is to show:
      ?h. f o g on s = (h on s) /\ h PERMUTES s
   Take h = f o g.
   Then (f o g) PERMUTES s         by BIJ_COMPOSE
*)
Theorem bij_set_map_element:
  !f g s t. BIJ f t s /\ g IN bij_set s t ==> (f o g) on s IN bij_maps s
Proof
  rpt strip_tac >>
  `BIJ g s t` by fs[bij_set_element_alt] >>
  rw[bij_set_def, fun_set_def] >>
  qexists_tac `f o g` >>
  metis_tac[BIJ_COMPOSE]
QED

(* Theorem: BIJ f t s ==> INJ (\g. (f o g) on s) (bij_set s t) (bij_maps s) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) g IN bij_set s t ==> f o g on s IN bij_maps s
       This is true                            by bij_set_map_element
   (2) g IN bij_set s t /\ h IN bij_set s t /\
       f o g on s = (f o h on s) ==> g = h
       Note ?f1. g = (f1 on s) /\ BIJ g s t    by bij_set_element
        and ?f2. h = (f2 on s) /\ BIJ h s t    by bij_set_element
       As both g and h are restricted to s,
          g = h <=> f1 x = f2 x   for x IN s   by FUN_EQ_THM
       Now for x IN s,
          f o g on s x = (f o h on s) x        by FUN_EQ_THM
        or      f (f1 x) = f (f2 x)            by o_THM
        or          f1 x = f2 x                by BIJ_DEF, INJ_DEF for BIJ f t s
*)
Theorem bij_set_map_inj:
  !f s t. BIJ f t s ==> INJ (\g. (f o g) on s) (bij_set s t) (bij_maps s)
Proof
  rw[INJ_DEF] >-
  metis_tac[bij_set_map_element] >>
  fs[bij_set_element] >>
  rw[FUN_EQ_THM] >>
  simp[on_def] >>
  (Cases_on `x IN s` >> simp[]) >>
  fs[on_def, FUN_EQ_THM] >>
  `f (f' x) = f (f'' x)` by metis_tac[] >>
  prove_tac[BIJ_DEF, INJ_DEF]
QED

(* Theorem: BIJ f t s ==> SURJ (\g. (f o g) on s) (bij_set s t) (bij_maps s) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) g IN bij_set s t ==> f o g on s IN bij_maps s
       This is true                            by bij_set_map_element
   (2) x IN bij_maps s ==> ?g. g IN bij_set s t /\ f o g on s = x
       Note ?h. x = (h on s) /\ BIJ h s s      by bij_set_element
       Let g = (LINV f t) o h, and take (g on s).
       Then f o (g on s) on s
          = f o g on s                         by on_compose
          = (f o (LINV f t) o h) on s          by notation
          = h on s                             by BIJ_LINV_INV
          = x
        Now BIJ (LINV f t) s t                 by BIJ_LINV_BIJ
        and BIJ g s t                          by BIJ_COMPOSE
       Thus g IN bij_set s t                   by bij_set_element
*)
Theorem bij_set_map_surj:
  !f s t. BIJ f t s ==> SURJ (\g. (f o g) on s) (bij_set s t) (bij_maps s)
Proof
  rw[SURJ_DEF] >-
  metis_tac[bij_set_map_element] >>
  fs[bij_set_element] >>
  qabbrev_tac `g = (LINV f t) o f'` >>
  qexists_tac `g on s` >>
  rpt strip_tac >| [
    qexists_tac `g` >>
    rw[Abbr`g`] >>
    metis_tac[BIJ_LINV_BIJ, BIJ_COMPOSE],
    simp[on_compose] >>
    rw[on_def, FUN_EQ_THM] >>
    (Cases_on `x IN s` >> simp[]) >>
    simp[Abbr`g`] >>
    metis_tac[BIJ_LINV_INV, BIJ_ELEMENT]
  ]
QED

(* Theorem: BIJ f t s ==> BIJ (\g. (f o g) on s) (bij_set s t) (bij_maps s) *)
(* Proof:
   Let h = (\g. (f o g) on s).
   Note  INJ h (bij_set s t) (bij_maps s)     by bij_set_map_inj
    and SURJ h (bij_set s t) (bij_maps s)     by bij_set_map_surj
   Thus  BIJ h (bij_set s t) (bij_maps s)     by BIJ_DEF
*)
Theorem bij_set_map_bij:
  !f s t. BIJ f t s ==> BIJ (\g. (f o g) on s) (bij_set s t) (bij_maps s)
Proof
  simp[BIJ_DEF, bij_set_map_inj, bij_set_map_surj]
QED

(* Theorem: FINITE s /\ FINITE t /\ CARD s = CARD t ==>
            bij_set s t =b= bij_maps s *)
(* Proof:
   Note ?f. BIJ f t s                    by bij_eq_card_eq, CARD s = CARD t
     so BIJ (\g. (f o g) on s) (bij_set s t) (bij_maps s)
                                         by bij_set_map_bij
     or bij_set s t =b= bij_maps s       by notation
*)
Theorem bij_set_bij_eq_maps:
  !s t. FINITE s /\ FINITE t /\ CARD s = CARD t ==>
        bij_set s t =b= bij_maps s
Proof
  metis_tac[bij_eq_card_eq, bij_set_map_bij]
QED

(* Theorem: FINITE s ==> bij_maps s = inj_set s s *)
(* Proof:
   By SUBSET_ANTISYM, this is to show:
   (1) bij_maps s SUBSET inj_set s s
       Let f IN bij_maps s.
       Then f IN fun_set s t /\ BIJ f s s      by bij_set_element_alt
         so f IN fun_set s t /\ INJ f s s      by BIJ_DEF
         or f IN inj_set s s                   by inj_set_element_alt
       Thus bij_maps s SUBSET inj_set s s      by SUBSET_DEF
   (2) inj_set s s SUBSET bij_maps s
       Let f IN inj_set s s.
       Then f IN fun_set s t /\ INJ f s s      by inj_set_element_alt
         so f IN fun_set s t /\ BIJ f s s      by FINITE_INJ_IS_BIJ
         or f IN bij_maps s                    by bij_set_element_alt
       Thus inj_set s s SUBSET bij_maps s      by SUBSET_DEF
*)
Theorem bij_maps_eq_inj_set:
  !s. FINITE s ==> bij_maps s = inj_set s s
Proof
  rpt strip_tac >>
  irule SUBSET_ANTISYM >>
  rw[bij_set_alt, inj_set_alt, SUBSET_DEF] >-
  fs[BIJ_DEF] >>
  simp[FINITE_INJ_IS_BIJ]
QED

(* Theorem: FINITE s ==> CARD (bij_maps s) = perm (CARD s) *)
(* Proof:
   Let n = CARD s.
     CARD (bij_maps s)
   = CARD (inj_set s s)        by bij_maps_eq_inj_set
   = n arrange n               by inj_set_card
   = perm n                    by arrange_n_n
*)
Theorem bij_maps_card:
  !s. FINITE s ==> CARD (bij_maps s) = perm (CARD s)
Proof
  simp[bij_maps_eq_inj_set, inj_set_card, arrange_n_n]
QED

(* Theorem: FINITE s /\ FINITE t ==>
            CARD (bij_set s t) =
            if (CARD s = CARD t) then perm (CARD s) else 0 *)
(* Proof:
   If CARD s = CARD t,
      Note bij_set s t =b= bij_maps s
                                   by bij_set_bij_eq_maps
       and FINITE (bij_set s t)    by bij_set_finite
      CARD (bij_set s t)
    = CARD (bij_maps s)            by bij_eq_card
    = perm (CARD s)                by bij_maps_card
   If CARD s <> CARD t,
      CARD (bij_set s t)
    = CARD {}                      by bij_set_not_empty
    = 0                            by CARD_EMPTY
*)
Theorem bij_set_card:
  !s t. FINITE s /\ FINITE t ==>
        CARD (bij_set s t) =
          if (CARD s = CARD t) then perm (CARD s) else 0
Proof
  rw[] >| [
    `bij_set s t =b= bij_maps s` by rw[bij_set_bij_eq_maps] >>
    metis_tac[bij_set_finite, bij_eq_card, bij_maps_card],
    metis_tac[bij_set_not_empty, CARD_EMPTY]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* A direct count of bijections.                                             *)
(* ------------------------------------------------------------------------- *)

(* Overload inj_count of equal size. *)
Overload bij_count = “\n. inj_count n n”

(* A better theorem of bij_count_element. *)

(* Theorem: x IN bij_count n <=> ?f. x = f on count n /\ f PERMUTES (count n) *)
(* Proof:
       x IN bij_count n
   <=> ?f. x = f on count n /\ INJ f (count n) (count n)   by inj_count_element
   <=> ?f. x = f on count n /\ INJ f (count n) (count n) /\
                               SURJ f (count n) (count n)  by FINITE_INJ_IS_SURJ, FINITE_COUNT
   <=> ?f. x = f on count n /\ BIJ f (count n) (count n)   by BIJ_DEF
   <=> ?f. x = f on count n /\ f PERMUTES (count n)        by notation
*)
Theorem bij_count_element:
  !x n. x IN bij_count n <=> ?f. x = f on count n /\ f PERMUTES (count n)
Proof
  rpt strip_tac >>
  `!f n. f PERMUTES (count n) <=> INJ f (count n) (count n)` by
  (rw[BIJ_DEF, EQ_IMP_THM] >>
  simp[FINITE_INJ_IS_SURJ]) >>
  simp[inj_count_element]
QED

(* Theorem: bij_count n <> {} *)
(* Proof: by inj_count_eq_empty. *)
Theorem bij_count_not_empty:
  !n. bij_count n <> {}
Proof
  simp[inj_count_eq_empty]
QED

(* Derive theorems. *)
Theorem bij_count_map_bij =
   inj_count_map_bij |> ISPEC ``n:num`` |> ISPEC ``n:num``
                     |> SIMP_RULE std_ss [list_count_n_n] |> GEN_ALL;
(* val bij_count_map_bij =
|- !n. BIJ (\f. MAP f [0 ..< n]) (bij_count n) (perm_count n): thm *)

Theorem bij_count_bij_eq_perm_count =
   inj_count_bij_eq_list_count |> ISPEC ``n:num`` |> ISPEC ``n:num``
                               |> SIMP_RULE std_ss [list_count_n_n] |> GEN_ALL;
(* val bij_count_bij_eq_perm_count = |- !n. bij_count n =b= perm_count n: thm *)

Theorem bij_count_finite =
   inj_count_finite |> ISPEC ``n:num`` |> ISPEC ``n:num`` |> GEN_ALL;
(* val bij_count_finite = |- !n. FINITE (bij_count n): thm *)

Theorem bij_count_card =
   inj_count_card |> ISPEC ``n:num`` |> ISPEC ``n:num``
                  |> SIMP_RULE std_ss [arrange_n_n] |> GEN_ALL;
(* val bij_count_card = |- !n. CARD (bij_count n) = perm n: thm *)

Theorem bij_maps_bij_count =
   bij_maps_eq_inj_set |> ISPEC ``count n``
                       |> SIMP_RULE std_ss [FINITE_COUNT] |> GEN_ALL;
(* val bij_maps_bij_count = |- !n. bij_maps (count n) = bij_count n: thm *)

Theorem bij_maps_bij_eq_bij_count =
   inj_set_bij_eq_inj_count |> ISPEC ``s:'a -> bool`` |> ISPEC ``s:'a -> bool``
                            |> SIMP_RULE std_ss [GSYM bij_maps_eq_inj_set] |> GEN_ALL;
(* val bij_maps_bij_eq_bij_count =
|- !s. FINITE s ==> bij_maps s =b= bij_count (CARD s): thm *)

(* Theorem: FINITE s ==> bij_maps s =b= perm_count (CARD s) *)
(* Proof:
   Note bij_maps s =b= bij_count (CARD s)              by bij_maps_bij_eq_bij_count
    and bij_count (CARD s) =b= perm_count (CARD s)     by bij_count_bij_eq_perm_count
     so bij_maps s =b= perm_count (CARD s)             by bij_eq_trans
*)
Theorem bij_maps_bij_eq_perm_count:
  !s. FINITE s ==> bij_maps s =b= perm_count (CARD s)
Proof
  metis_tac[bij_maps_bij_eq_bij_count, bij_count_bij_eq_perm_count, bij_eq_trans]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
