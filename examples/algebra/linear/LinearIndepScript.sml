(* ------------------------------------------------------------------------- *)
(* Linear Independence                                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "LinearIndep";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory listTheory numberTheory combinatoricsTheory;

(* Get dependent theories local *)
(* val _ = load "SpanSpaceTheory"; *)
open VectorSpaceTheory SpanSpaceTheory;
open monoidTheory groupTheory fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Linear Independence Documentation                                         *)
(* ------------------------------------------------------------------------- *)
(* Overload:
*)
(* Definitions and Theorems (# are exported):

   Change of Basis:
   stick_rotate_length     |- !r n1 n. n1 IN sticks r n ==> !k. rotate k n1 IN sticks r n
   basis_rotate_once_basis |- !g b. basis g b ==> basis g (rotate 1 b)
   basis_rotate_basis      |- !g b. basis g b ==> !k. k < LENGTH b ==> basis g (rotate k b)
   vsum_stick_rotate_once  |- !r g op. VSpace r g op ==> !b. basis g b ==>
                              !n. n IN sticks r (LENGTH b) ==> (n |o| b = rotate 1 n |o| rotate 1 b)
   vsum_stick_rotate       |- !r g op. VSpace r g op ==> !b. basis g b ==>
                              !n. n IN sticks r (LENGTH b) ==>
                              !k. k < LENGTH b ==> (n |o| b = rotate k n |o| rotate k b)
   vspace_span_with_rotate |- !r g op. VSpace r g op ==> !b. basis g b ==>
                              !k. k < LENGTH b ==> (SpanSpace r g op (rotate k b) = SpanSpace r g op b)
   vspace_span_basis_shrink|- !r g op. VSpace r g op ==> !b. basis g b ==>
                              !n. n IN sticks r (LENGTH b) /\ (n |o| b = |0|) ==>
                              !k. k < LENGTH b /\ EL k n <> #0 ==>
                                  (SpanSpace r g op (DROP (SUC k) b ++ TAKE k b) = SpanSpace r g op b)

   Linear Independence:
   LinearIndepBasis_def   |- !r g op b. LinearIndepBasis r g op b <=> basis g b /\
                             !n. n IN sticks r (LENGTH b) ==>
                                 ((n |o| b = |0|) <=> !k. k < LENGTH b ==> (EL k n = #0))
   indep_basis_is_basis   |- !r g op b. LinearIndepBasis r g op b ==> basis g b
   indep_basis_property   |- !r g op b. LinearIndepBasis r g op b ==>
                             !n. n IN sticks r (LENGTH b) ==>
                                 ((n |o| b = |0|) <=> !k. k < LENGTH b ==> (EL k n = #0))

   vspace_indep_basis_inj       |- !r g op. VSpace r g op ==> !b. LinearIndepBasis r g op b ==>
                                            INJ (\n. n |o| b) (sticks r (LENGTH b)) V
   vspace_basis_indep_one_less  |- !r g op. VSpace r g op ==>
                                   !h t. LinearIndepBasis r g op (h::t) ==> LinearIndepBasis r g op t
   vspace_basis_dep_one_more    |- !r g op. VSpace r g op ==>
                                   !h t. ~LinearIndepBasis r g op t ==> ~LinearIndepBasis r g op (h::t)
*)

(* Overloads for convenience *)
val _ = temp_overload_on ("o", ``(op:'a -> 'b -> 'b)``);
val _ = temp_overload_on ("V", ``(g:'b group).carrier``);
val _ = temp_overload_on ("||", ``(g:'b group).op``);
val _ = temp_overload_on ("|0|", ``(g:'b group).id``);
val _ = set_fixity "||" (Infixl 500); (* same as + in arithmeticScript.sml *)

val _ = temp_overload_on ("+", ``stick_add r``);
val _ = temp_overload_on ("-", ``stick_neg r``);
val _ = temp_overload_on ("*", ``stick_cmult r``);
val _ = temp_overload_on ("-", ``stick_sub r``);

(* ------------------------------------------------------------------------- *)
(* Change of Basis                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note: rotate is defined in helperList.
> rotate_def;
val it = |- !n l. rotate n l = DROP n l ++ TAKE n l: thm

This is a simple form of a change of basis by permutation.
*)

(* Theorem: !n1. n1 IN sticks r n ==> !k. (rotate k nl) IN sticks r n *)
(* Proof:
   By sticks_def, rotate_same_length, rotate_same_set.
*)
val stick_rotate_length = store_thm(
  "stick_rotate_length",
  ``!r:'a field. !n1 n. n1 IN sticks r n ==> !k. (rotate k n1) IN sticks r n``,
  rw[sticks_def, rotate_same_length, rotate_same_set]);

(* Theorem: !b. basis g b ==> basis g (rotate 1 b) *)
(* Proof:
   If b = [],
       basis g (rotate 1 [])
     = basis g []              by rotate_nil
     = T                       by basis_nil
   If b = h::t, h IN V /\ basis g t                  by basis_cons
       rotate 1 (h::t)
     = DROP (SUC 0) (h::t) ++ TAKE (SUC 0) (h::t)    by ONE
     = DROP 0 t ++ h::TAKE 0 t                       by DROP_def, TAKE_def
     = b ++ [h]                                      by DROP_def, TAKE_def
     Since basis g b, !x. MEM x b <=> x IN V.        by basis_member
     With h IN V,    !x. MEM x (b ++ [h]) <=> x IN V.
     Hence basis g (b ++ [h])                        by basis_member
*)
val basis_rotate_once_basis = store_thm(
  "basis_rotate_once_basis",
  ``!(g:'b group) (b:'b list). basis g b ==> basis g (rotate 1 b)``,
  strip_tac >>
  Cases_on `b` >-
  rw[basis_nil, rotate_nil] >>
  rw[basis_cons, rotate_def] >>
  pop_assum mp_tac >>
  rw[basis_member] >>
  rw[]);

(* Theorem: basis g b ==> !k. k < LENGTH b ==> basis g (rotate k b) *)
(* Proof:
   By induction on k.
   Base case: 0 < LENGTH b ==> basis g (rotate 0 b)
      basis g (rotate 0 b) = basis g b    by rotate_0
      Hence true.
   Step case: SUC k < LENGTH b ==> basis g (rotate (SUC k) b)
      i.e. k < LENGTH b.
        basis g (rotate (SUC k) b)
      = basis g (rotate 1 (rotate k b))   by rotate_suc
      = T                                 by basis_rotate_once_basis
      due to basis g (rotate k b)         by induction hypothesis
*)
val basis_rotate_basis = store_thm(
  "basis_rotate_basis",
  ``!(g:'b group) (b:'b list). basis g b ==> !k. k < LENGTH b ==> basis g (rotate k b)``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[rotate_0] >>
  rw[] >>
  `k < LENGTH b` by decide_tac >>
  rw[rotate_suc, basis_rotate_once_basis]);

(* Theorem: basis g b ==> !n. n IN sticks r (LENGTH b) ==> n |o| b = (rotate 1 n) |o| (rotate 1 b) *)
(* Proof:
   If b = [], n IN sticks r 0 ==> n = []      by sticks_0, IN_SING.
   RHS = (rotate 1 []) |o| (rotate 1 [])
       = [] |o| []                            by rotate_nil
       = LHS
   If b = h::t, LENGTH (h::t) = SUC (LENGTH t)               by LENGTH
   ?k s. k IN R /\ s IN sticks r (LENGTH t) /\ (n = k::s)    by stick_cons
   After expanding by vsum_cons and rotate_def, SNOC, this is to show:
     k o h || (s |o| t) = (s ++ [k]) |o| (t ++ [h])
   RHS = (s ++ [k]) |o| (t ++ [h])
       = (SNOC k s) |o| (SNOC h t)            by SNOC_APPEND
       = k o h || (s |o| t)                   by vsum_stick_snoc
       = LHS
*)
val vsum_stick_rotate_once = store_thm(
  "vsum_stick_rotate_once",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN sticks r (LENGTH b) ==> (n |o| b = (rotate 1 n) |o| (rotate 1 b))``,
  rpt strip_tac >>
  Cases_on `b` >| [
    pop_assum mp_tac >>
    rw[] >>
    `n = []` by metis_tac[sticks_0, IN_SING] >>
    rw[rotate_nil],
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    rw[basis_cons, stick_cons] >>
    rw[vsum_cons, rotate_def] >>
    metis_tac[vsum_stick_snoc, SNOC_APPEND]
  ]);

(* Theorem: basis g b ==>
   !n. n IN sticks r (LENGTH b) ==> !k. k < LENGTH b ==> n |o| b = (rotate k n) |o| (rotate k b) *)
(* Proof:
   By induction on b.
   Base case: 0 < LENGTH b ==> (n |o| b = rotate 0 n |o| rotate 0 b)
     Since rotate 0 n = n and rotate 0 b = b   by rotate_0
     This is true.
   Step case: SUC k < LENGTH b ==> (n |o| b = rotate (SUC k) n |o| rotate (SUC k) b)
     Since SUC k < LENGTH b implies k < LENGTH b,
     and   LENGTH n = LENGTH b                 by stick_length
     and   basis g (rotate k b)                by basis_rotate_basis
     RHS = rotate (SUC k) n |o| rotate (SUC k) b
         = (rotate 1 (rotate k n)) |o| (rotate 1 (rotate k b))  by rotate_suc
         = (rotate k n) |o| (rotate k b)                        by vsum_stick_rotate_once
         = n |o| b                                              by induction hypothesis
         = LHS
*)
val vsum_stick_rotate = store_thm(
  "vsum_stick_rotate",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN sticks r (LENGTH b) ==> !k. k < LENGTH b ==> (n |o| b = (rotate k n) |o| (rotate k b))``,
  ntac 8 strip_tac >>
  Induct >-
  rw[rotate_0] >>
  rw[] >>
  `k < LENGTH b` by decide_tac >>
  `LENGTH n = LENGTH b` by metis_tac[stick_length] >>
  `basis g (rotate k b)` by rw[basis_rotate_basis] >>
  `(rotate k n) IN sticks r (LENGTH b)` by metis_tac[stick_rotate_length] >>
  `LENGTH (rotate k b) = LENGTH b` by rw[rotate_same_length] >>
  metis_tac[rotate_suc, vsum_stick_rotate_once]);

(* Theorem: !k. k < LENGTH b ==> SpanSpace r g op (rotate k b) = SpanSpace r g op b *)
(* Proof:
   Note that LENGTH (rotate k b) = LENGTH b                        by rotate_same_length
   Expanding by SpanSpace_def, using monoid_component_equality, this is to show:
   (1) n IN sticks r (LENGTH b) ==> ?n'. (n |o| rotate k b = n' |o| b) /\ n' IN sticks r (LENGTH b)
       Let n' = rotate (LENGTH b - k) n IN sticks r (LENGTH b)     by stick_rotate_length
       Then  n' |o| b
          = (rotate (LENGTH b - k) n) |o| b                        by n' = rotate (LENGTH b - k) n
          = (rotate k (rotate (LENGTH b - k) n)) |o| (rotate k b)  by vsum_stick_rotate
          = n |o| (rotate k b)                                     by rotate_rcancel
   (2) n IN sticks r (LENGTH b) ==> ?n'. (n |o| b = n' |o| rotate k b) /\ n' IN sticks r (LENGTH b)
       Let n' = rotate k n IN sticks r (LENGTH b)                  by stick_rotate_length
       Then n' |o| (rotate k b)
          = (rotate k n) |o| (rotate k b)                          by n' = rotate k n
          = n |o| b                                                by vsum_stick_rotate
*)
val vspace_span_with_rotate = store_thm(
  "vspace_span_with_rotate",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !k. k < LENGTH b ==> (SpanSpace r g op (rotate k b) = SpanSpace r g op b)``,
  rpt strip_tac >>
  rw[SpanSpace_def, monoid_component_equality, rotate_same_length, EXTENSION, EQ_IMP_THM] >-
  metis_tac[stick_rotate_length, stick_length, vsum_stick_rotate, rotate_rcancel] >>
  metis_tac[vsum_stick_rotate, stick_rotate_length]);

(* Theorem: Let n IN sticks r (LENGTH b) /\ (n |o| b = |0|)
            If n is nonzero at index k, the basis b at same index k, after deletion (from list),
            will span the same subspace.
    basis g b ==> !n. n IN sticks r (LENGTH b) /\ (n |o| b = |0|) ==>
    !k. k < LENGTH b /\ EL k n <> #0 ==>
    (SpanSpace r g op (DROP (SUC k) b ++ TAKE k b) = SpanSpace r g op b) *)
(* Proof:
   Let u = EL k b, a vector in the basis b.
   Let b' = DROP (SUC k) b ++ TAKE k b, a kind of mutated basis of b.
   Note rotate k b = u::b'             by rotate_shift_element
    and u IN V /\ basis g b'           by basis_rotate_basis, basis_cons
     SpanSpace r g op b
   = SpanSpace r g op (rotate k b)     by vspace_span_with_rotate
   = SpanSpace r g op (u::b')          by rotate_shift_element
   = SpanSpace r g op (b')             by vspace_span_with_member
     if u IN (SpanSpace r g op b').carrier, which is proved as:

   Let h = EL k n, the corresponding scalar in sticks n.
   To show: u IN (SpanSpace r g op b').carrier, i.e. u is spanned by basis b',
   Trick is to show: (h o u) IN (SpanSpace r g op b').carrier,
   Then u = |/h o (h o u) IN (SpanSpace r g op b').carrier  by vspace_span_cmult.

   Why does the trick works? Due to rotation:
   Let n' = (DROP (SUC k) n ++ TAKE k n), a kind of mutated n to match b'.
   Note k < LENGTH b means k < LENGTH n        by stick_length, n IN sticks r (LENGTH b)
   Then rotate k n = h::n'                     by rotate_shift_element
   Thus |0| = n |o| b                          by given
            = (rotate k n) |o| (rotate k b)    by vsum_stick_rotate
            = (h::n') |o| (u::b')              by rotations above
            = (h o u) || (n' |o| b')           by vsum_stick_cons
   Since Group (SpanSpace r g op b')           by vspace_span_group
   It is obvious that (n' |o| b') IN (SpanSpace r g op b').carrier (recall it is a span space),
   and it is almost simple to argue that its inverse should be in the same carrier.
   The actual path is still not so straight-forward.

   (1) Let's try to show: (n' |o| b') IN (SpanSpace r g op b').carrier
       This is true by vspace_span_property if: n' IN sticks r (LENGTH b')
       Note rotate k n IN sticks r (LENGTH b)           by stick_rotate_length
         or h :: n' IN sticks r (LENGTH b)              by rotate k n = h::n' above
         or         IN sticks r (LENGTH (rotate k b))   by rotate_same_length
         or         IN sticks r (LENGTH (u::b'))        by rotate k b = u::b' above
         or         IN sticks r (SUC (LENGTH b'))       by LENGTH
       Thus ?h1 n1. h1 IN R /\ n1 IN sticks r (LENGTH b')
        and (h :: n' = h1 :: n1)                        by stick_cons
         or (h1 = h) /\ (n1 = n')                       by list_11
       Hence n' IN sticks r (LENGTH b').
       and h IN R as bonus, although this can be deduced by stick_components_stick
   (2) Now to show: h o u IN (SpanSpace r g op b').carrier
       Let vv = n' |o| b'.
       Then vv IN (SpanSpace r g op b').carrier         by n' IN sticks r (LENGTH b'), above
       thus ?uu. uu IN (SpanSpace r g op s).carrier, and
                 (uu || vv = |0|)                       by vspace_span_negative
       Now  uu IN V /\ vv IN V                          by vspace_span_vector
       and  h o u IN V                                  by vspace_cmult_vector, h IN R, u IN V
       With Group g                                     by vspace_has_group
         so h o u = uu                                  by group_linv_unique, Group g
       Thus h o u IN (SpanSpace r g op b').carrier      by uu IN (SpanSpace r g op s).carrier
   (3) With Field r                                     by vspace_has_field
        and h IN R+                                     by field_nonzero_eq, given h <> #0
         so |/h IN R                                    by field_inv_element, h IN R+
       Now  |/h o (h o u)
          = ( |/h * h) o u                               by vspace_cmult_cmult
          = #1 o u                                      by field_mult_linv, h IN R+
          = u                                           by vspace_cmult_lone
       Hence u = |/h o (h o u) IN (SpanSpace r g op b').carrier  by vspace_span_cmult
*)
val vspace_span_basis_shrink = store_thm(
  "vspace_span_basis_shrink",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
    !n. n IN sticks r (LENGTH b) /\ (n |o| b = |0|) ==>
    !k. k < LENGTH b /\ EL k n <> #0 ==>
     (SpanSpace r g op ((DROP (SUC k) b) ++ (TAKE k b)) = SpanSpace r g op b)``,
  rpt strip_tac >>
  qabbrev_tac `u = EL k b` >>
  qabbrev_tac `h = EL k n` >>
  qabbrev_tac `b' = DROP (SUC k) b ++ TAKE k b` >>
  qabbrev_tac `n' = DROP (SUC k) n ++ TAKE k n` >>
  `rotate k b = u::b'` by rw[rotate_shift_element, Abbr`u`, Abbr`b'`] >>
  `rotate k n = h :: n'` by metis_tac[rotate_shift_element, stick_length] >>
  `u IN V /\ basis g b'` by metis_tac[basis_cons, basis_rotate_basis] >>
  `u IN (SpanSpace r g op b').carrier` by
  (`h IN R /\ h o u IN (SpanSpace r g op b').carrier` by
    (`rotate k n IN sticks r (SUC (LENGTH b'))` by metis_tac[stick_rotate_length, rotate_same_length, LENGTH] >>
  `h IN R /\ n' IN sticks r (LENGTH b')` by metis_tac[stick_cons, list_11] >>
  `(h o u) || (n' |o| b') = |0|` by metis_tac[vsum_stick_cons, vsum_stick_rotate] >>
  qabbrev_tac `vv = n' |o| b'` >>
  `vv IN (SpanSpace r g op b').carrier` by rw[vspace_span_property, Abbr`vv`] >>
  `?uu. uu IN (SpanSpace r g op b').carrier /\ (uu || vv = |0|)` by rw[vspace_span_negative] >>
  `uu IN V /\ vv IN V` by metis_tac[vspace_span_vector] >>
  `h o u IN V` by metis_tac[vspace_cmult_vector] >>
  `h o u = uu` by metis_tac[group_linv_unique, vspace_has_group] >>
  rw[]) >>
  `Field r` by metis_tac[vspace_has_field] >>
  `h IN R+ /\ |/h IN R` by rw[field_nonzero_eq] >>
  `|/h o (h o u) = ( |/h * h) o u` by metis_tac[vspace_cmult_cmult] >>
  `_ = #1 o u` by rw[] >>
  `_ = u` by metis_tac[vspace_cmult_lone] >>
  metis_tac[vspace_span_cmult]) >>
  metis_tac[vspace_span_with_rotate, rotate_shift_element, vspace_span_with_member]);

(*
If SpanSpace r g op b = SpanSpace r g op b', what is the condition on an additional vector h such that:
   SpanSpace r g op (h::b) = SpanSpace r g op (h::b') ?
If h is already spanned by b (or b'), (h::b) spans the same space.
If h is not spanned by b (or b'), (h::b) gives another dimension, same as (h::b').
*)

(* ------------------------------------------------------------------------- *)
(* Linear Independence.                                                      *)
(* ------------------------------------------------------------------------- *)

(* In general, vectors in basis b may or may not be linearly independent.
   However, if a vector has two sticks representations:
   e.g.    4 o (v) || 4 o (-v) = 3 o (v) || 3 o (-v)
   then    1 o (v) || 1 o (-v) = |0|
   i.e. there is another sticks of the same length giving a nonzero representation of zero vector.
*)

(* Better formulation: if vector zero has only zero-representation,
          then any vector has a unique representation. *)

(* Linearly Independent basis has only one representation of zero vector *)
val LinearIndepBasis_def = Define`
  LinearIndepBasis (r:'a field) (g:'b group) (op:'a -> 'b -> 'b) (b:'b list) <=>
    (basis g b) /\
    !n. n IN sticks r (LENGTH b) ==> ((n |o| b = |0|) <=> !k. k < LENGTH b ==> (EL k n = #0))
`;

(* Theorem: LinearIndepBasis r g op b ==> basis g b *)
(* Proof: by LinearIndepBasis_def *)
val indep_basis_is_basis = store_thm(
  "indep_basis_is_basis",
  ``!(r:'a field) (g:'b group) op b. LinearIndepBasis r g op b ==> basis g b``,
  rw[LinearIndepBasis_def]);

(* Theorem: LinearIndepBasis r g op b ==>
   !n. n IN sticks r (LENGTH b) ==> ((n |o| b = |0|) <=> !k. k < LENGTH b ==> (EL k n = #0)) *)
(* Proof: by LinearIndepBasis_def *)
val indep_basis_property = store_thm(
  "indep_basis_property",
  ``!(r:'a field) (g:'b group) op b. LinearIndepBasis r g op b ==>
   !n. n IN sticks r (LENGTH b) ==> ((n |o| b = |0|) <=> !k. k < LENGTH b ==> (EL k n = #0))``,
  rw[LinearIndepBasis_def]);

(* Theorem: LinearIndepBasis r g op b ==> INJ (\n. n |o| b) (sticks r (LENGTH b)) V *)
(* Proof:
   Note basis g b                                    by indep_basis_is_basis
   By INJ_DEF, this is to show:
   (1) n IN sticks r (LENGTH b) ==> n |o| b IN V
       True by vsum_basis_stick_vector.
   (2) n IN sticks r (LENGTH b) /\ n' IN sticks r (LENGTH b) /\ (n |o| b = n' |o| b) ==> n = n'
       Note (n |o| b) IN V /\ (n' |o| b) IN V        by vsum_basis_stick_vector
       Then (n - n') |o| b
          = (n |o| b) || g.inv (n' |o| b)            by vsum_stick_sub
          = |0|                                      by group_rinv, given n |o| b = n' |o| b
       As n - n' IN sticks r (LENGTH b)              by stick_sub_length
          !k. k < LENGTH b ==> (EL k (n - n') = #0)  by indep_basis_property
       Hence n = n'                                  by stick_eq_property.
*)
val vspace_indep_basis_inj = store_thm(
  "vspace_indep_basis_inj",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. LinearIndepBasis r g op b ==> INJ (\n. n |o| b) (sticks r (LENGTH b)) V``,
  rw[INJ_DEF, LinearIndepBasis_def] >-
  metis_tac[vsum_basis_stick_vector] >>
  `(n - n') |o| b = (n |o| b) || g.inv (n' |o| b)` by rw[vsum_stick_sub] >>
  `n |o| b IN V /\ n' |o| b IN V` by metis_tac[vspace_span_vector, vspace_span_property] >>
  `(n - n') |o| b = |0|` by metis_tac[group_rinv, vspace_has_group] >>
  `Field r` by metis_tac[vspace_has_field] >>
  `n - n' IN sticks r (LENGTH b)` by rw[stick_sub_length] >>
  metis_tac[stick_eq_property]);

(* Theorem: Reduce-by-1 of linear indepedent basis is still linear independent:
            LinearIndepBasis r g op (h::t) ==> LinearIndepBasis r g op t *)
(* Proof:
   By LinearIndepBasis_def, this is to show:
      !n. n IN sticks r (SUC (LENGTH t)) ==>
        ((n |o| (h::t) = |0|) <=> !k. k < SUC (LENGTH t) ==> (EL k n = #0))

   By contradiction, need to find m IN sticks r (SUC (LENGTH t))
      such that ((m |o| (h::t) = |0|) <=/=> !k. k < SUC (LENGTH t) ==> (EL k m = #0))

   Note VSpace r g op ==> Field r              by vspace_has_field
        VSpace r g op ==> Group g              by vspace_has_group
    Let m = #0 :: n, that is, appending #0 to the sticks n.
   Then m IN sticks r (SUC (LENGTH t))         by stick_cons, LENGTH
   Note (n |o| t) IN V                         by vsum_stick_basis_vector
   Also  m |o| (h::t)
       = (#0::n) |o| (h::t)
       = #0 o h || (n |o| t)                   by vsum_cons, MAP2
       = |0| || (n |o| t)                      by vspace_cmult_lzero
       = (n |o| t)                             by group_lid, (n |o| t) IN V

     Now !k . k < LENGTH t <=> SUC k < SUC (LENGTH t)  by LESS_MONO
     and !k. EL (SUC k) (#0::n) = EL k n               by EL_restricted
    also EL 0 (#0::n) = #0                             by EL, HD

   The assumed LinearIndepBasis r g op (h::t) gives:
   !n'. n' IN sticks r (SUC (LENGTH t)) ==>
        ((n' |o| (h::t) = |0|) <=> !k. k < SUC (LENGTH t) ==> (EL k n' = #0))

   To derive the contradiction, need to show:
   (1) (n |o| t = |0|) /\ k < (LENGTH t) /\ EL k n <> #0 ==> F
       Putting m as n', k as (SUC k) in the if implication,
          EL (SUC k) m = #0,
       or EL (SUC k) m = EL (SUC k) (#0::n) = EL k n = #0, contradicting EL k n <> #0.
   (2) (!k. k < (LENGTH t) ==> (EL k n = #0)) /\ (n |o| t <> |0|) ==> F
       Putting m as n', k as (SUC k) in the only-if implication, and consider cases on k,
          m |o| (h::t) = |0|
       or n |o| t = |0|.
*)
val vspace_basis_indep_one_less = store_thm(
  "vspace_basis_indep_one_less",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
     !h t. LinearIndepBasis r g op (h::t) ==> LinearIndepBasis r g op t``,
  rw[LinearIndepBasis_def, basis_cons] >>
  `Field r` by metis_tac[vspace_has_field] >>
  `Group g` by metis_tac[vspace_has_group] >>
  qabbrev_tac `m = #0 :: n` >>
  `m IN sticks r (SUC (LENGTH t))` by rw[stick_cons, Abbr`m`] >>
  `n |o| t IN V` by metis_tac[vsum_basis_stick_vector] >>
  `m |o| (h::t) = #0 o h || (n |o| t)` by rw[vsum_cons, Abbr`m`] >>
  `_ = |0| || (n |o| t)` by metis_tac[vspace_cmult_lzero] >>
  `_ = n |o| t` by rw[] >>
  `!k . k < LENGTH t <=> SUC k < SUC (LENGTH t)` by decide_tac >>
  `!k. EL (SUC k) (#0::n) = EL k n` by metis_tac[EL_restricted] >>
  `EL 0 (#0::n) = #0` by rw[Abbr`m`] >>
  rw_tac bool_ss[EQ_IMP_THM] >-
  metis_tac[] >>
  metis_tac[num_CASES]);

(* Theorem: Add-by-1 of a linear dependent basis is still linear dependent:
            ~LinearIndepBasis r g op t ==> ~LinearIndepBasis r g op (h::t) *)
(* Proof: by contrapositive of vspace_basis_indep_one_less. *)
val vspace_basis_dep_one_more = store_thm(
  "vspace_basis_dep_one_more",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
     !h t. ~LinearIndepBasis r g op t ==> ~LinearIndepBasis r g op (h::t)``,
  metis_tac[vspace_basis_indep_one_less]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
