(* ------------------------------------------------------------------------- *)
(* Involution Fix                                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "involuteFix";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
val _ = load("involuteTheory");
open helperFunctionTheory; (* for FUNPOW_2 *)
open helperSetTheory; (* for BIJ_ELEMENT *)
open helperNumTheory; (* for MOD_EQ *)
open helperTwosqTheory; (* for doublet_finite, doublet_card *)
open involuteTheory;

(* arithmeticTheory -- load by default *)
open arithmeticTheory pred_setTheory;


(* ------------------------------------------------------------------------- *)
(* Involution Fix Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   pair_by f     = \x y. (x fpair y) f
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Helper Theorems:

   Singles and Doubles of Involution:
   fpair_def     |- !x y f. pair_by f x y <=> y = x \/ y = f x
   fpair_refl    |- !f x. pair_by f x x
   fpair_sym     |- !f s x y. f involute s /\ x IN s /\
                              pair_by f x y ==> pair_by f y x
   fpair_trans   |- !f s x y z. f involute s /\ x IN s /\
                                pair_by f x y /\ pair_by f y z ==> pair_by f x z
   fpair_equiv   |- !f s. f involute s ==> (\x y. pair_by f x y) equiv_on s

   fixes_def     |- !f s. fixes f s = {x | x IN s /\ f x = x}
   pairs_def     |- !f s. pairs f s = {x | x IN s /\ f x <> x}
   fixes_element |- !f s x. x IN fixes f s <=> x IN s /\ f x = x
   pairs_element |- !f s x. x IN pairs f s <=> x IN s /\ f x <> x
   fixes_empty   |- !f. fixes f {} = {}
   pairs_empty   |- !f. pairs f {} = {}
   fixes_subset  |- !f s. fixes f s SUBSET s
   pairs_subset  |- !f s. pairs f s SUBSET s
   fixes_finite  |- !f s. FINITE s ==> FINITE (fixes f s)
   pairs_finite  |- !f s. FINITE s ==> FINITE (pairs f s)

   Equivalence classes of pair_by:
   equiv_class_fixes_iff   |- !f s x. f endo s ==>
                               (x IN fixes f s <=>
                                equiv_class (\x y. pair_by f x y) s x = {x})
   equiv_class_fixes       |- !f s x. x IN fixes f s ==>
                               equiv_class (\x y. pair_by f x y) s x = {x}
   equiv_class_pairs_iff   |- !f s x. f endo s ==>
                               (x IN pairs f s <=>
                                equiv_class (\x y. pair_by f x y) s x = {x; f x} /\ f x <> x)
   equiv_class_pairs       |- !f s x. x IN pairs f s /\ f x IN s ==>
                               equiv_class (\x y. pair_by f x y) s x = {x; f x}
   involute_pairs_element_pair
                           |- !f s x. f involute s /\ x IN pairs f s ==> f x IN pairs f s
   equiv_class_pairs_pairs |- !f s x. f involute s /\ x IN pairs f s ==>
                                      equiv_class (\x y. pair_by f x y) s (f x) =
                                      equiv_class (\x y. pair_by f x y) s x

   Show partitions:
   fixes_pairs_split     |- !f s. s =|= fixes f s # pairs f s
   fixes_pairs_union     |- !f s. s = fixes f s UNION pairs f s
   fixes_pairs_disjoint  |- !f s. DISJOINT (fixes f s) (pairs f s)

   equiv_fixes_def       |- !f s. equiv_fixes f s =
                            IMAGE (\x. equiv_class (\x y. pair_by f x y) s x) (fixes f s)
   equiv_pairs_def       |- !f s. equiv_pairs f s =
                            IMAGE (\x. equiv_class (\x y. pair_by f x y) s x) (pairs f s)
   equiv_fixes_element   |- !f s x. x IN equiv_fixes f s <=>
                            ?y. y IN fixes f s /\ (x = equiv_class (\x y. pair_by f x y) s y)
   equiv_pairs_element   |- !f s x. x IN equiv_pairs f s <=>
                            ?y. y IN pairs f s /\ (x = equiv_class (\x y. pair_by f x y) s y)
   equiv_fixes_pairs_disjoint
                         |- !f s. DISJOINT (equiv_fixes f s) (equiv_pairs f s)

   equiv_fixes_pairs_union  |- !f s. partition (\x y. pair_by f x y) s =
                                     equiv_fixes f s UNION equiv_pairs f s
   equiv_fixes_pairs_split  |- !f s. partition (\x y. pair_by f x y) s =|=
                                     equiv_fixes f s # equiv_pairs f s
   equiv_fixes_subset       |- !f s. equiv_fixes f s SUBSET partition (\x y. pair_by f x y) s
   equiv_pairs_subset       |- !f s. equiv_pairs f s SUBSET partition (\x y. pair_by f x y) s
   equiv_fixes_element_sing_iff
                            |- !f s t. f endo s ==>
                                (t IN equiv_fixes f s <=> ?x. x IN fixes f s /\ t = {x})
   equiv_fixes_element_sing |- !f s t. t IN equiv_fixes f s ==> ?x. x IN fixes f s /\ t = {x}
   equiv_fixes_element_card |- !f s t. t IN equiv_fixes f s ==> CARD t = 1
   equiv_pairs_element_doublet_iff
                            |- !f s t. f endo s ==>
                                (t IN equiv_pairs f s <=> ?x. x IN pairs f s /\ t = {x; f x})
   equiv_pairs_element_doublet
                            |- !f s t. f endo s /\ t IN equiv_pairs f s ==>
                               ?x. x IN pairs f s /\ t = {x; f x}
   equiv_pairs_element_card |- !f s t. f endo s /\ t IN equiv_pairs f s ==> CARD t = 2
   equiv_fixes_fixes_bij    |- !f s. f endo s ==> BIJ CHOICE (equiv_fixes f s) (fixes f s)
   equiv_fixes_card         |- !f s. FINITE s /\ f endo s ==>
                                     CARD (equiv_fixes f s) = CARD (fixes f s)
   equiv_fixes_finite   |- !f s. FINITE s ==> FINITE (equiv_fixes f s)
   equiv_pairs_finite   |- !f s. FINITE s ==> FINITE (equiv_pairs f s)

   equiv_fixes_pair_disjoint |- !f s. f involute s ==> PAIR_DISJOINT (equiv_fixes f s)
   equiv_pairs_pair_disjoint |- !f s. f involute s ==> PAIR_DISJOINT (equiv_pairs f s)
   equiv_pairs_bigunion_card_even
                             |- !f s. FINITE s /\ f involute s ==>
                                      EVEN (CARD (BIGUNION (equiv_pairs f s)))
   equiv_fixes_by_image |- !f s. f endo s ==> equiv_fixes f s = IMAGE (\x. {x}) (fixes f s)
   equiv_pairs_by_image |- !f s. f endo s ==> equiv_pairs f s = IMAGE (\x. {x; f x}) (pairs f s)
   equiv_fixes_bigunion |- !f s. f endo s ==> BIGUNION (equiv_fixes f s) = fixes f s
   equiv_fixes_pairs_bigunion_disjoint
                        |- !f s. f involute s ==>
                            DISJOINT (BIGUNION (equiv_fixes f s)) (BIGUNION (equiv_pairs f s))
   equiv_fixes_pairs_bigunion_union
                        |- !f s. f involute s ==>
                            s = BIGUNION (equiv_fixes f s) UNION BIGUNION (equiv_pairs f s)
   equiv_fixes_pairs_bigunion_split
                        |- !f s. f involute s ==>
                            s =|= BIGUNION (equiv_fixes f s) # BIGUNION (equiv_pairs f s)
   equiv_pairs_bigunion |- !f s. f involute s ==> (BIGUNION (equiv_pairs f s) = pairs f s)
   pairs_card_even      |- !f s. FINITE s /\ f involute s ==> EVEN (CARD (pairs f s))
   involute_set_fixes_both_even
                        |- !f s. FINITE s /\ f involute s ==>
                                 (EVEN (CARD s) <=> EVEN (CARD (fixes f s)))
   involute_set_fixes_both_odd
                        |- !f s. FINITE s /\ f involute s ==>
                                 (ODD (CARD s) <=> ODD (CARD (fixes f s)))

   Reformulate using mates:
   mates_def             |- !f s. mates f s = s DIFF fixes f s
   mates_element         |- !f s x. x IN mates f s <=> x IN s /\ f x <> x
   mates_subset          |- !f s. mates f s SUBSET s
   mates_finite          |- !f s. FINITE s ==> FINITE (mates f s)
   mates_fixes_union     |- !f s. s = mates f s UNION fixes f s
   mates_fixes_disjoint  |- !f s. DISJOINT (mates f s) (fixes f s)
   mates_fixes_card      |- !f s. FINITE s ==> CARD s = CARD (mates f s) + CARD (fixes f s)
   involute_mates        |- !f s. f involute s ==> f involute mates f s
   involute_mates_partner|- !f s x. f involute s /\ x IN mates f s ==> f x IN mates f s
   fpair_equiv_on_mates  |- !f s. f involute s ==> (\x y. pair_by f x y) equiv_on mates f s
   mates_partition_element_doublet
                         |- !f s t. f involute s ==>
                                    t IN partition (\x y. pair_by f x y) (mates f s) <=>
                                    ?x. x IN mates f s /\ t = {x; f x}
   mates_partition_element_card
                         |- !f s t. FINITE s /\ f involute s /\
                                    t IN partition (\x y. pair_by f x y) (mates f s) ==>
                                    CARD t = 2
   mates_card_even       |- !f s. FINITE s /\ f involute s ==> EVEN (CARD (mates f s))
   involute_set_fixes_both_even
                         |- !f s. FINITE s /\ f involute s ==>
                                  (EVEN (CARD s) <=> EVEN (CARD (fixes f s)))

   Two Involutions:
   involute_two_fixes_both_even
                        |- !f g s. FINITE s /\ f involute s /\ g involute s ==>
                                   (EVEN (CARD (fixes f s)) <=> EVEN (CARD (fixes g s)))
   involute_two_fixes_both_odd
                        |- !f g s. FINITE s /\ f involute s /\ g involute s ==>
                                   (ODD (CARD (fixes f s)) <=> ODD (CARD (fixes g s)))
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Singles and Doubles of Involution                                         *)
(* ------------------------------------------------------------------------- *)

(* Use this approach:

A finite set and the set of its fixed points under any involution have cardinalities of the same parity
https://math.stackexchange.com/questions/1373671/
answer by Brian M. Scott, July 2015.

*)

(*
if  fpair x y f <=> y = f x
this is too general:
* it cannot be shown to be reflexive
* it cannot be symmetric in general:  y = f x /\ x = f y ==> x = f (f x) only.
* it is almost transitive: y = f x /\ z = f y ==> z = f (f x)
* Thus to make this an equivalence relation, need to extend y = f x  to y = f^n x
for whatever n. That's the repeat of f, and the relation is: reachable.

Adding the possibility of equality in (fpair x y f) changes things:
* it is reflexive by default of equality.
* it is symmetric when f (f x) = x, that is, an involution.
* it is transitive when f (f x) = x, due to equality, that is, an involution.
*)

(* Define an equivalence relation *)
Definition fpair_def:
   fpair x y f <=> y = x \/ y = f x
End

(* make this infix *)
val _ = set_fixity "fpair" (Infix(NONASSOC, 450));

(* Theorem: (x fpair x) f *)
(* Proof: by fpair_def, x = x. *)
Theorem fpair_refl:
  !f x. (x fpair x) f
Proof
  rw[fpair_def]
QED

(* Theorem: f involute s /\ x IN s /\ (x fpair y) f ==> (y fpair x) f *)
(* Proof:
   If x = y, this is trivial.
   Assume x <> y,
   Then y = f x                 by fpair_def
    and f y = f (f x) = x       by f involute s, x IN s
   Thus (y fpair x) f           by fpair_def
*)
Theorem fpair_sym:
  !f s x y. f involute s /\ x IN s /\ (x fpair y) f ==> (y fpair x) f
Proof
  metis_tac[fpair_def]
QED

(* Theorem: f involute s /\ x IN s /\ (x fpair y) f /\ (y fpair z) f ==> (x fpair z) f *)
(* Proof:
   If x = y or y = z, this is trivial.
   Assume x <> y and y <> z.
   Then y = f x                 by fpair_def
    and z = f y                 by fpair_def
          = f (f x)             by above
          = x                   by f involute s, x IN s
   Thus (x fpair z) f           by fpair_def
*)
Theorem fpair_trans:
  !f s x y z. f involute s /\ x IN s /\
               (x fpair y) f /\ (y fpair z) f ==> (x fpair z) f
Proof
  (rw[fpair_def] >> metis_tac[])
QED

(* Overload the equivalence relation *)
val _ = overload_on("pair_by", ``\f x y. (x fpair y) f``);

(* Theorem: f involute s ==> (pair_by f) equiv_on s *)
(* Proof: by equiv_on_def, fpair_refl, fpair_sym, fpair_trans *)
Theorem fpair_equiv:
  !f s. f involute s ==> (pair_by f) equiv_on s
Proof
  rw[equiv_on_def] >-
  simp[fpair_refl] >-
  metis_tac[fpair_sym] >>
  metis_tac[fpair_trans]
QED

(* Define the fixed points and pairs of involution. *)
Definition fixes_def[nocompute]:
   fixes f s = {x | x IN s /\ f x = x}
End
(* use [nocompute] as this is not effective. *)

(* Define the pairs of involution. *)
Definition pairs_def[nocompute]:
   pairs f s = {x | x IN s /\ f x <> x}
End
(* use [nocompute] as this is not effective. *)

(* Theorem: x IN fixes f s <=> x IN s /\ f x = x *)
(* Proof: by fixes_def *)
Theorem fixes_element:
  !f s x. x IN fixes f s <=> x IN s /\ f x = x
Proof
  rw[fixes_def]
QED

(* Theorem: x IN pairs f s <=> x IN s /\ f x <> x *)
(* Proof: by pairs_def *)
Theorem pairs_element:
  !f s x. x IN pairs f s <=> x IN s /\ f x <> x
Proof
  rw[pairs_def]
QED

(* Theorem: fixes f {} = {} *)
(* Proof: by fixes_def. *)
Theorem fixes_empty:
  !f. fixes f {} = {}
Proof
  simp[fixes_def]
QED

(* Theorem: pairs f {} = {} *)
(* Proof: by pairs_def. *)
Theorem pairs_empty:
  !f. pairs f {} = {}
Proof
  simp[pairs_def]
QED

(* Theorem: fixes f s SUBSET s *)
(* Proof: by fixes_def *)
Theorem fixes_subset:
  !f s. fixes f s SUBSET s
Proof
  rw[fixes_def, SUBSET_DEF]
QED

(* Theorem: pairs f s SUBSET s *)
(* Proof: by pairs_def *)
Theorem pairs_subset:
  !f s. pairs f s SUBSET s
Proof
  rw[pairs_def, SUBSET_DEF]
QED

(* Theorem: FINITE s ==> FINITE (fixes f s) *)
(* Proof:
   Note (fixes f s) SUBSET s     by fixes_subset
   Thus FINITE (fixes f s)       by SUBSET_FINITE
*)
Theorem fixes_finite:
  !f s. FINITE s ==> FINITE (fixes f s)
Proof
  metis_tac[fixes_subset, SUBSET_FINITE]
QED

(* Theorem: FINITE s ==> FINITE (pairs f s) *)
(* Proof:
   Note (pairs f s) SUBSET s     by pairs_subset
   Thus FINITE (pairs f s)       by SUBSET_FINITE
*)
Theorem pairs_finite:
  !f s. FINITE s ==> FINITE (pairs f s)
Proof
  metis_tac[pairs_subset, SUBSET_FINITE]
QED

(* Equivalence classes of pair_by *)

(* Theorem: f endo s ==> (x IN fixes f s <=> equiv_class (pair_by f) s x = {x}) *)
(* Proof:
       y IN equiv_class (pair_by f) s x
   <=> y IN s /\ (pair_by f) x y          by equiv_class_element
   <=> y IN s /\ (x fpair y) f            by notation
   <=> y IN s /\ ((x = y) \/ (y = f x))   by fpair_def
   <=> y IN s /\ ((x = y) \/ (y = x))     by fixes_def
   <=> y IN s /\ (x = y)
   <=> y IN {x} /\ x IN s                 by fixes_def
   Thus equiv_class (pair_by f) s x = {x} by EXTENSION
*)
Theorem equiv_class_fixes_iff:
  !f s x. f endo s ==>
          (x IN fixes f s <=> equiv_class (pair_by f) s x = {x})
Proof
  rw[fixes_def, fpair_def, EXTENSION, EQ_IMP_THM]
QED

(* Theorem: x IN fixes f s ==> equiv_class (pair_by f) s x = {x} *)
(* Proof: simplifed form of equiv_class_fixes_iff. *)
Theorem equiv_class_fixes:
  !f s x. x IN fixes f s ==> equiv_class (pair_by f) s x = {x}
Proof
  rw[fixes_def, fpair_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: f endo s ==>
            (x IN pairs f s <=> equiv_class (pair_by f) s x = {x; f x} /\ f x <> x) *)
(* Proof:
       y IN equiv_class (pair_by f) s x
   <=> y IN s /\ (pair_by f) x y                by equiv_class_element
   <=> y IN s /\ (x fpair y) f                  by notation
   <=> y IN s /\ ((x = y) \/ (y = f x))         by fpair_def
   <=> y IN s /\ y IN {x; f x} /\ f x <> x      by pairs_def
   <=> y IN {x; f x} /\ x IN s /\ f x IN s      by pairs_def, f x IN s
   Thus equiv_class (pair_by f) s x = {x; f x}  by EXTENSION
*)
Theorem equiv_class_pairs_iff:
  !f s x. f endo s ==>
          (x IN pairs f s <=> equiv_class (pair_by f) s x = {x; f x} /\ f x <> x)
Proof
  rw[pairs_def, fpair_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: x IN pairs f s /\ f x IN s ==>
            equiv_class (pair_by f) s x = {x; f x} *)
(* Proof: simplifed form of equiv_class_pairs_iff. *)
Theorem equiv_class_pairs:
  !f s x. x IN pairs f s /\ f x IN s ==>
          equiv_class (pair_by f) s x = {x; f x}
Proof
  rw[pairs_def, fpair_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: x IN pairs f s /\ f x IN s ==> f x IN pairs f s *)
(* Proof:
   Note x IN pairs f s
    <=> x IN s /\ f x <> x             by pairs_def
        f x IN pairs f s
    <=> f x IN s /\ f (f x) <> f x     by pairs_def
    <=> T                              by f involute s
*)
Theorem involute_pairs_element_pair:
  !f s x. f involute s /\ x IN pairs f s ==> f x IN pairs f s
Proof
  rw[pairs_def]
QED

(* Theorem: f involute s /\ x IN pairs f s ==>
            equiv_class (pair_by f) s (f x) = equiv_class (pair_by f) s x *)
(* Proof:
   Note f involute s /\ x IN s ==>
        f x IN s /\ f (f x) = x       by notation
        equiv_class (pair_by f) s (f x)
      = {f x; f (f x)}                by equiv_class_pairs
      = {f x; x}                      by f involute s
      = equiv_class (pair_by f) s x   by equiv_class_pairs
*)
Theorem equiv_class_pairs_pairs:
  !f s x. f involute s /\ x IN pairs f s ==>
            equiv_class (pair_by f) s (f x) = equiv_class (pair_by f) s x
Proof
  rw[pairs_def, fpair_def, EXTENSION] >>
  metis_tac[]
QED

(* Show partitions! *)

(* Theorem: s =|= (fixes f s) # (pairs f s) *)
(* Proof: by fixes_def, pairs_def *)
Theorem fixes_pairs_split:
  !f s. s =|= (fixes f s) # (pairs f s)
Proof
  (rw[fixes_def, pairs_def, DISJOINT_DEF, EXTENSION] >> metis_tac[])
QED

(* Extract theorems *)
val fixes_pairs_union = save_thm("fixes_pairs_union",
    fixes_pairs_split |> SPEC_ALL |> CONJUNCT1 |> GEN ``s:'a -> bool`` |> GEN_ALL);
(* val fixes_pairs_union = |- !f s. s = fixes f s UNION pairs f s: thm *)

val fixes_pairs_disjoint = save_thm("fixes_pairs_disjoint",
    fixes_pairs_split |> SPEC_ALL |> CONJUNCT2 |> GEN ``s:'a -> bool`` |> GEN_ALL);
(* val fixes_pairs_disjoint = |- !f s. DISJOINT (fixes f s) (pairs f s): thm *)


(* Those equivalent classes of fixes *)
Definition equiv_fixes_def:
   equiv_fixes f s = IMAGE (equiv_class (pair_by f) s) (fixes f s)
End

(* Those equivalent classes of pairs *)
Definition equiv_pairs_def:
   equiv_pairs f s = IMAGE (equiv_class (pair_by f) s) (pairs f s)
End

(* Theorem: x IN equiv_fixes f s <=>
            ?y. y IN (fixes f s) /\ x = equiv_class (pair_by f) s y *)
(* Proof: by equiv_fixes_def *)
Theorem equiv_fixes_element:
  !f s x. x IN equiv_fixes f s <=>
          ?y. y IN (fixes f s) /\ x = equiv_class (pair_by f) s y
Proof
  rw[equiv_fixes_def] >>
  metis_tac[]
QED

(* Theorem: x IN equiv_pairs f s <=>
            ?y. y IN (pairs f s) /\ x = equiv_class (pair_by f) s y *)
(* Proof: by equiv_fixes_def *)
Theorem equiv_pairs_element:
  !f s x. x IN equiv_pairs f s <=>
          ?y. y IN (pairs f s) /\ x = equiv_class (pair_by f) s y
Proof
  rw[equiv_pairs_def] >>
  metis_tac[]
QED

(* Theorem: DISJOINT (equiv_fixes f s) (equiv_pairs f s) *)
(* Proof:
   Let R = (pair_by f).
   By contradiction, suppose there is an x such that:
       x IN (equiv_fixes f s) INTER (equiv_pairs f s)
   ==> x IN IMAGE (equiv_class R s) (fixes f s) /\
       x IN IMAGE (equiv_class R s) (pairs f s)           by equiv_fixes_def, equiv_pairs_def
   ==> ?y. (y = equiv_class R s x) /\ y IN fixes f s /\   by IN_IMAGE
       ?z. (z = equiv_class R s x) /\ z IN pairs f s      by IN_IMAGE
   ==> ?y. y IN fixes f s /\ y IN pairs f s
   This contradicts DISJOINT (fixes f s) (pairs f s)      by fixes_pairs_disjoint
*)
Theorem equiv_fixes_pairs_disjoint:
  !f s. DISJOINT (equiv_fixes f s) (equiv_pairs f s)
Proof
  rw[DISJOINT_DEF, equiv_fixes_def, equiv_pairs_def, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `x' IN x /\ x'' IN x /\ pair_by f x' x''` by metis_tac[fixes_element, pairs_element, fpair_refl] >>
  `x' = x''` by fs[fpair_def, fixes_def] >>
  metis_tac[fixes_pairs_disjoint, IN_DISJOINT]
QED

(* Theorem: partition (pair_by f) s = (equiv_fixes f s) UNION (equiv_pairs f s) *)
(* Proof:
   Let R = (pair_by f).
       x IN partition R s
   <=> ?t. t IN s /\ (x = equiv_class R s t)           by partition_def
   <=> ?t. (t IN (fixes f s) \/ t IN (pairs f s)) /\
           (x = equiv_class R s t)                     by fixes_pairs_union
   <=> (x IN equiv_fixes R s) \/                       by equiv_fixes_def
       (x IN equiv_pairs R s)                          by equiv_pairs_def
   <=> x IN (equiv_fixes f s) UNION (equiv_pairs f s)  by IN_UNION
*)
Theorem equiv_fixes_pairs_union:
  !f s. partition (pair_by f) s = (equiv_fixes f s) UNION (equiv_pairs f s)
Proof
  rpt strip_tac >>
  `!x. x IN equiv_fixes f s <=> ?t. (x = equiv_class (\x y. pair_by f x y) s t) /\t IN (fixes f s)` by rw[equiv_fixes_def] >>
  `!x. x IN equiv_pairs f s <=> ?t. (x = equiv_class (\x y. pair_by f x y) s t) /\t IN (pairs f s)` by rw[equiv_pairs_def] >>
  qabbrev_tac `R = \x y. pair_by f x y` >>
  rw_tac std_ss[EXTENSION] >>
  `x IN partition R s <=> ?t. t IN s /\ (x = equiv_class R s t)` by rw[partition_def] >>
  `_ = ?t. (t IN (fixes f s) \/ t IN (pairs f s)) /\ (x = equiv_class R s t)` by metis_tac[fixes_pairs_union, IN_UNION] >>
  metis_tac[IN_UNION]
QED

(* Theorem: partition (pair_by f) s =|= (equiv_fixes f s) # (equiv_pairs f s) *)
(* Proof: by equiv_fixes_pairs_union, equiv_fixes_pairs_disjoint *)
Theorem equiv_fixes_pairs_split:
  !f s. partition (pair_by f) s =|= (equiv_fixes f s) # (equiv_pairs f s)
Proof
  rw[equiv_fixes_pairs_union, equiv_fixes_pairs_disjoint]
QED

(* Theorem: equiv_fixes f s SUBSET partition (pair_by f) s *)
(* Proof: by equiv_fixes_pairs_union, SUBSET_UNION *)
Theorem equiv_fixes_subset:
  !f s. equiv_fixes f s SUBSET partition (pair_by f) s
Proof
  rw[equiv_fixes_pairs_union, SUBSET_UNION]
QED

(* Theorem: equiv_pairs f s SUBSET partition (pair_by f) s *)
(* Proof: by equiv_fixes_pairs_union, SUBSET_UNION *)
Theorem equiv_pairs_subset:
  !f s. equiv_pairs f s SUBSET partition (pair_by f) s
Proof
  rw[equiv_fixes_pairs_union, SUBSET_UNION]
QED

(* Theorem: f endo s ==>
            (t IN equiv_fixes f s <=> ?x. x IN fixes f s /\ t = {x}) *)
(* Proof:
       t IN equiv_fixes f s
   <=> ?x. x IN fixes f s /\ (t = equiv_class (pair_by f) s x)
                                           by equiv_fixes_element
   <=> ?x. x IN fixes f s /\ t = {x}       by equiv_class_fixes_iff
*)
Theorem equiv_fixes_element_sing_iff:
  !f s t. f endo s ==>
          (t IN equiv_fixes f s <=> ?x. x IN fixes f s /\ t = {x})
Proof
  metis_tac[equiv_fixes_element, equiv_class_fixes_iff]
QED

(* Theorem: t IN equiv_fixes f s ==> ?x. x IN fixes f s /\ t = {x} *)
(* Proof: simplified form of equiv_fixes_element_sing_iff. *)
Theorem equiv_fixes_element_sing:
  !f s t. t IN equiv_fixes f s ==> ?x. x IN fixes f s /\ t = {x}
Proof
  rpt strip_tac >>
  imp_res_tac equiv_fixes_element >>
  rw[equiv_class_fixes]
QED

(* Theorem: t IN equiv_fixes f s ==> CARD t = 1 *)
(* Proof: by equiv_fixes_element_sing, CARD_SING. *)
Theorem equiv_fixes_element_card:
  !f s t. t IN equiv_fixes f s ==> CARD t = 1
Proof
  metis_tac[equiv_fixes_element_sing, CARD_SING]
QED

(* Theorem: f endo s ==>
            (t IN equiv_pairs f s <=> ?x. x IN pairs f s /\ t = {x; f x}) *)
(* Proof:
        t IN equiv_pairs f s
    <=> ?x. x IN pairs f s /\ t = equiv_class (pair_by f) s x
                                           by equiv_pairs_element
    <=> ?x. x IN pairs f s /\ t = {x; f x}
                                           by equiv_class_pairs_iff
*)
Theorem equiv_pairs_element_doublet_iff:
  !f s t. f endo s ==>
          (t IN equiv_pairs f s <=> ?x. x IN pairs f s /\ t = {x; f x})
Proof
  metis_tac[equiv_pairs_element, pairs_element, equiv_class_pairs_iff]
QED

(* Theorem: f endo s /\ t IN equiv_pairs f s ==>
            ?x. x IN pairs f s /\ t = {x; f x} *)
(* Proof: simplified form of equiv_pairs_element_doublet_iff. *)
Theorem equiv_pairs_element_doublet:
  !f s t. f endo s /\ t IN equiv_pairs f s ==> ?x. x IN pairs f s /\ t = {x; f x}
Proof
  rpt strip_tac >>
  imp_res_tac equiv_pairs_element >>
  metis_tac[equiv_class_pairs, pairs_element]
QED

(* Theorem: f endo s /\ t IN equiv_pairs f s ==> CARD t = 2 *)
(* Proof:
   Note ?x. x IN pairs f s /\ (t = {x; f x}) by equiv_pairs_element_doublet
    now f x <> x                             by pairs_element
   thus CARD t = 2                           by CARD_DEF
*)
Theorem equiv_pairs_element_card:
  !f s t. f endo s /\ t IN equiv_pairs f s ==> CARD t = 2
Proof
  rpt strip_tac >>
  `?x. x IN pairs f s /\ t = {x; f x}` by rw[equiv_pairs_element_doublet] >>
  `f x <> x` by metis_tac[pairs_element] >>
  rw[]
QED

(* Theorem: f endo s ==> BIJ CHOICE (equiv_fixes f s) (fixes f s) *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) x IN equiv_fixes f s ==> CHOICE x IN fixes f s
       Note ?y. (x = {y}) /\ y IN fixes f s  by equiv_fixes_element_sing_iff
         so CHOICE x = y                     by CHOICE_SING
       thus true.
   (2) x IN equiv_fixes f s /\ y IN equiv_fixes f s /\ CHOICE x = CHOICE y ==> x = y
       Note ?u. x = {u}                      by equiv_fixes_element_sing_iff
        and ?v. y = {v}                      by equiv_fixes_element_sing_iff
         so CHOICE x = u                     by CHOICE_SING
        and CHOICE y = v                     by CHOICE_SING
       Thus u = v, and x = y                 by EXTENSION
   (3) same as (1).
   (4) x IN fixes f s ==> ?y. y IN equiv_fixes f s /\ (CHOICE y = x)
       Let y = {x}, then CHOICE y = x        by CHOICE_SING
       and y IN equiv_fixes f s              by equiv_fixes_element_sing_iff
*)
Theorem equiv_fixes_fixes_bij:
  !f s. f endo s ==> BIJ CHOICE (equiv_fixes f s) (fixes f s)
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[equiv_fixes_element_sing_iff, CHOICE_SING]
QED

(* Theorem: FINITE s /\ f endo s ==> CARD (equiv_fixes f s) = CARD (fixes f s) *)
(* Proof:
   Note (fixes f s) SUBSET s                       by fixes_subset
     so FINITE (fixes f s)                         by SUBSET_FINITE
    Now BIJ CHOICE (equiv_fixes f s) (fixes f s)   by equiv_fixes_fixes_bij
     so ?g. BIJ g (fixes f s) (equiv_fixes f s)    by BIJ_INV
    ==> CARD (equiv_fixes f s) = CARD (fixes f s)  by FINITE_BIJ_CARD
*)
Theorem equiv_fixes_card:
  !f s. FINITE s /\ f endo s ==> CARD (equiv_fixes f s) = CARD (fixes f s)
Proof
  rpt strip_tac >>
  `FINITE (fixes f s)` by metis_tac[fixes_subset, SUBSET_FINITE] >>
  `BIJ CHOICE (equiv_fixes f s) (fixes f s)` by rw[equiv_fixes_fixes_bij] >>
  metis_tac[FINITE_BIJ_CARD, BIJ_INV]
QED

(* Theorem: FINITE s ==> FINITE (equiv_fixes f s)  *)
(* Proof:
   Let g = equiv_class (pair_by f) s.
   Note equiv_fixes f s = IMAGE g (fixes f s)    by equiv_fixes_def
    now FINITE (fixes f s)                       by fixes_finite
     so FINITE (equiv_fixes f s)                 by IMAGE_FINITE
*)
Theorem equiv_fixes_finite:
  !f s. FINITE s ==> FINITE (equiv_fixes f s)
Proof
  rw[equiv_fixes_def, fixes_finite, IMAGE_FINITE]
QED

(* Theorem: FINITE s ==> FINITE (equiv_pairs f s)  *)
(* Proof:
   Let g = equiv_class (pair_by f) s.
   Note equiv_pairs f s = IMAGE g (pairs f s)    by equiv_pairs_def
    now FINITE (pairs f s)                       by pairs_finite
     so FINITE (equiv_pairs f s)                 by IMAGE_FINITE
*)
Theorem equiv_pairs_finite:
  !f s. FINITE s ==> FINITE (equiv_pairs f s)
Proof
  rw[equiv_pairs_def, pairs_finite, IMAGE_FINITE]
QED

(* Theorem: f involute s ==> PAIR_DISJOINT (equiv_fixes f s) *)
(* Proof:
   Let R = pair_by f.
   Note R equiv_on s                               by fpair_equiv
     so PAIR_DISJOINT (partition R s)              by partition_elements_disjoint
    But (equiv_fixes f s) SUBSET (partition R s)   by equiv_fixes_subset
     so PAIR_DISJOINT (equiv_fixes f s)            by pair_disjoint_subset
*)
Theorem equiv_fixes_pair_disjoint:
  !f s. f involute s ==> PAIR_DISJOINT (equiv_fixes f s)
Proof
  ntac 3 strip_tac >>
  qabbrev_tac `R = pair_by f` >>
  `R equiv_on s` by rw[fpair_equiv, Abbr`R`] >>
  `PAIR_DISJOINT (partition R s)` by metis_tac[partition_elements_disjoint] >>
  `(equiv_fixes f s) SUBSET (partition R s)` by rw[equiv_fixes_subset, Abbr`R`] >>
  prove_tac[pair_disjoint_subset]
QED

(* Theorem: f involute s ==> PAIR_DISJOINT (equiv_pairs f s) *)
(* Proof:
   Let R = pair_by f.
   Note R equiv_on s                               by fpair_equiv
     so PAIR_DISJOINT (partition R s)              by partition_elements_disjoint
    But (equiv_pairs f s) SUBSET (partition R s)   by equiv_pairs_subset
     so PAIR_DISJOINT (equiv_pairs f s)            by pair_disjoint_subset
*)
Theorem equiv_pairs_pair_disjoint:
  !f s. f involute s ==> PAIR_DISJOINT (equiv_pairs f s)
Proof
  ntac 3 strip_tac >>
  qabbrev_tac `R = pair_by f` >>
  `R equiv_on s` by rw[fpair_equiv, Abbr`R`] >>
  `PAIR_DISJOINT (partition R s)` by metis_tac[partition_elements_disjoint] >>
  `(equiv_pairs f s) SUBSET (partition R s)` by rw[equiv_pairs_subset, Abbr`R`] >>
  prove_tac[pair_disjoint_subset]
QED

(* Theorem: FINITE s /\ f involute s ==> EVEN (CARD (BIGUNION (equiv_pairs f s))) *)
(* Proof:
   Let c = equiv_pairs f s.
   Then FINITE c                     by equiv_pairs_finite
   Note !t. t IN c ==> ?x. x IN pairs f s /\ (t = {x; f x})
                                     by equiv_pairs_element_doublet
   also f x <> x                     by pairs_element
   Thus !t. t IN c ==> FINITE t /\ (CARD t = 2)
                                     by doublet_finite, doublet_card
   also PAIR_DISJOINT c              by equiv_pairs_pair_disjoint
       CARD (BIGUNION c)
     = 2 * CARD c                    by CARD_BIGUNION_SAME_SIZED_SETS
   Thus EVEN (CARD (BIGUNION c))     by EVEN_DOUBLE
*)
Theorem equiv_pairs_bigunion_card_even:
  !f s. FINITE s /\ f involute s ==> EVEN (CARD (BIGUNION (equiv_pairs f s)))
Proof
  rpt strip_tac >>
  qabbrev_tac `c = equiv_pairs f s` >>
  `FINITE c` by rw[equiv_pairs_finite, Abbr`c`] >>
  `!t. t IN c ==> ?x. (t = {x; f x}) /\ (f x <> x)` by metis_tac[equiv_pairs_element_doublet, pairs_element] >>
  `!t. t IN c ==> FINITE t /\ (CARD t = 2)` by metis_tac[doublet_finite, doublet_card] >>
  `PAIR_DISJOINT c` by metis_tac[equiv_pairs_pair_disjoint] >>
  `CARD (BIGUNION c) = CARD c * 2` by rw[CARD_BIGUNION_SAME_SIZED_SETS] >>
  `_ = 2 * CARD c` by simp[] >>
  rw[EVEN_DOUBLE]
QED

(* Theorem: f endo s ==> equiv_fixes f s = IMAGE (\x. {x}) (fixes f s) *)
(* Proof:
   Let g = \x. {x}.
       t IN equiv_fixes f s
   <=> ?x. x IN fixes f s /\ (t = {x})  by equiv_fixes_element_sing_iff
   <=> ?x. x IN fixes f x /\ (t = g x)  by notation
   <=> t IN IMAGE g (fixes f s)         by IN_IMAGE
*)
Theorem equiv_fixes_by_image:
  !f s. f endo s ==> equiv_fixes f s = IMAGE (\x. {x}) (fixes f s)
Proof
  rpt strip_tac >>
  qabbrev_tac `g = \x. {x}` >>
  `!x. g x = {x}` by rw[Abbr`g`] >>
  rw_tac bool_ss[EXTENSION] >>
  metis_tac[equiv_fixes_element_sing_iff, IN_IMAGE]
QED

(* Theorem: f endo s ==> equiv_pairs f s = IMAGE (\x. {x; f x}) (pairs f s) *)
(* Proof:
   Let g = \x. {x; f x}.
       t IN equiv_pairs f s
   <=> ?x. x IN pairs f s /\ (t = {x; f x})  by equiv_pairs_element_doublet_iff
   <=> ?x. x IN pairs f s /\ (t = g x)       by notation
   <=> t IN IMAGE g (pairs f s)              by IN_IMAGE
*)
Theorem equiv_pairs_by_image:
  !f s. f endo s ==> equiv_pairs f s = IMAGE (\x. {x; f x}) (pairs f s)
Proof
  rpt strip_tac >>
  qabbrev_tac `g = \x. {x; f x}` >>
  `!x. g x = {x; f x}` by rw[Abbr`g`] >>
  rw_tac bool_ss[EXTENSION] >>
  metis_tac[equiv_pairs_element_doublet_iff, IN_IMAGE]
QED

(* Theorem: f endo s ==> BIGUNION (equiv_fixes f s) = fixes f s *)
(* Proof:
       BIGUNION (equiv_fixes f s)
     = BIGUNION (IMAGE (\x. {x}) (fixes f s))  by equiv_fixes_by_image
     = fixes f s                               by BIGUNION_ELEMENTS_SING
*)
Theorem equiv_fixes_bigunion:
  !f s. f endo s ==> BIGUNION (equiv_fixes f s) = fixes f s
Proof
  rw[equiv_fixes_by_image, BIGUNION_ELEMENTS_SING]
QED

(* Theorem: f involute s ==>
            DISJOINT (BIGUNION (equiv_fixes f s)) (BIGUNION (equiv_pairs f s)) *)
(* Proof:
   By contradiction, this is to show that the following is impossible:
      x IN a /\ x IN b /\ a IN equiv_fixes f s /\ b IN equiv_pairs f s
   Note ?y. y IN fixes f s /\ (a = {y})        by equiv_fixes_element_sing
    and ?z. z IN pairs f s /\ (b = {z; f z})   by equiv_pairs_element_doublet
   also y IN s /\ f y = y                      by fixes_element
    and z IN s /\ f z <> z                     by pairs_element
    Now x IN a = {y} ==> x = y                 by IN_SING
    and x IN b = {z; f z} ==> x = z \/ x = f z by EXTENSION
   If x = z,
      then z = y, and f y <> y is a contradiction.
   If x = f z,
      then f z = y = f y = f x = f (f z) = z   by f involute s
       and f z = z is a contradiction.
*)
Theorem equiv_fixes_pairs_bigunion_disjoint:
  !f s. f involute s ==>
        DISJOINT (BIGUNION (equiv_fixes f s)) (BIGUNION (equiv_pairs f s))
Proof
  rw[DISJOINT_DEF, BIGUNION, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `?y. y IN fixes f s /\ (s' = {y})` by rw[equiv_fixes_element_sing] >>
  `?z. z IN pairs f s /\ (s'' = {z; f z})` by rw[equiv_pairs_element_doublet] >>
  `y IN s /\ (f y = y)` by metis_tac[fixes_element] >>
  `z IN s /\ (f z <> z)` by metis_tac[pairs_element] >>
  `x = y` by fs[] >>
  `(x = z) \/ (x = f z)` by fs[] >>
  metis_tac[]
QED

(* Note:
equiv_fixes_pairs_disjoint
|- !f s. DISJOINT (equiv_fixes f s) (equiv_pairs f s)

In general, DISJOINT s t cannot imply DISJOINT (BIGUNION s) (BIGUNION t):
s = { {a,b,x}, {d,e,f}}   BIGUNION s = {a,b,x,d,e,f}
t = { {A,B,C}, {x,E,F}}   BIGUNION t = {A,B,C,x,E,F}
*)

(* Theorem: f involute s ==>
            s = BIGUNION (equiv_fixes f s) UNION BIGUNION (equiv_pairs f s) *)
(* Proof:
   Let R = pair_by f,
       a = fixes f s, ea = equiv_fixes f s,
       b = pairs f s, eb = equiv_pairs f s.
   then BIGUNION (partition R s)
      = BIGUNION (ea UNION eb)                by equiv_fixes_pairs_union
      = (BIGUNION ea) UNION (BIGUNION eb)     by BIGUNION_UNION
    and DISJOINT (BIGUNION ea) (BIGUNION eb)  by equiv_fixes_pairs_bigunion_disjoint
    Now R equiv_on s                          by fpair_equiv
     so s = BIGUNION (partition R s)          by BIGUNION_partition
   Hence s == BIGUNION ea UNION BIGUNION eb.
*)
Theorem equiv_fixes_pairs_bigunion_union:
  !f s. f involute s ==>
        s = BIGUNION (equiv_fixes f s) UNION BIGUNION (equiv_pairs f s)
Proof
  rpt strip_tac >>
  qabbrev_tac `R = pair_by f` >>
  `R equiv_on s` by rw[fpair_equiv, Abbr`R`] >>
  `s = BIGUNION (partition R s)` by rw[BIGUNION_partition] >>
  `_ = BIGUNION ((equiv_fixes f s) UNION (equiv_pairs f s))` by rw[equiv_fixes_pairs_union, Abbr`R`] >>
  fs[BIGUNION_UNION]
QED

(* Theorem: f involute s ==>
            s =|= (BIGUNION (equiv_fixes f s)) # (BIGUNION (equiv_pairs f s)) *)
(* Proof: by equiv_fixes_pairs_bigunion_union, equiv_fixes_pairs_bigunion_disjoint *)
Theorem equiv_fixes_pairs_bigunion_split:
  !f s. f involute s ==>
        s =|= (BIGUNION (equiv_fixes f s)) # (BIGUNION (equiv_pairs f s))
Proof
  metis_tac[equiv_fixes_pairs_bigunion_union, equiv_fixes_pairs_bigunion_disjoint]
QED

(* Theorem: f involute s ==> BIGUNION (equiv_pairs f s) = pairs f s *)
(* Proof:
   Let a = fixes f s, u = BIGUNION (equiv_fixes f s),
       b = pairs f s, v = BIGUNION (equiv_pairs f s).
   Note s =|= u # v       by equiv_fixes_pairs_bigunion_split
    and s =|= a # b       by fixes_pairs_split
        v
      = s DIFF u          by SPLIT_EQ_DIFF
      = s DIFF a          by equiv_fixes_bigunion
      = b                 by SPLIT_EQ_DIFF
*)
Theorem equiv_pairs_bigunion:
  !f s. f involute s ==> BIGUNION (equiv_pairs f s) = pairs f s
Proof
  rpt strip_tac >>
  qabbrev_tac `a = fixes f s` >>
  qabbrev_tac `b = pairs f s` >>
  qabbrev_tac `u = BIGUNION (equiv_fixes f s)` >>
  qabbrev_tac `v = BIGUNION (equiv_pairs f s)` >>
  `s =|= u # v` by rw[equiv_fixes_pairs_bigunion_split, Abbr`u`, Abbr`v`] >>
  `s =|= a # b` by rw[fixes_pairs_split, Abbr`a`, Abbr`b`] >>
  metis_tac[SPLIT_EQ_DIFF, equiv_fixes_bigunion]
QED

(* This is an indirect proof. A direct proof is desirable. *)

(* Theorem: f involute s ==> BIGUNION (equiv_pairs f s) = pairs f s *)
(* Proof:
   Let b = pairs f s, eb = equiv_pairs f s.
   This is to show: BIGUNION eb = b.
   First, show BIGUNION eb SUBSET b.
      By SUBSET_DEF, this is to show:
         x IN t /\ t IN eb ==> x IN b.
      Note ?z. z IN b /\ t = {z; f z}     by equiv_pairs_element_doublet
      Thus x = z or z = f z.
      If x = z, then x IN b.
      If x = f z, then x IN b             by involute_pairs_element_pair
      Hence BIGUNION eb SUBSET b          by SUBSET_DEF
   Next, show b SUBSET BIGUNION eb.
      By SUBSET_DEF, this is to show:
      x IN b ==> ?s. x IN s /\ s IN eb
      Let s = {x; f x}.
      Note s IN eb                        by equiv_pairs_element_doublet_iff
       and x IN s                         by EXTENSION
      Hence b SUBSET (BIGUNION eb)        by SUBSET_DEF

   Therefore, BIGUNION eb = b             by SUBSET_ANTISYM
*)
Theorem equiv_pairs_bigunion[allow_rebind]:
  !f s. f involute s ==> BIGUNION (equiv_pairs f s) = pairs f s
Proof
  rpt strip_tac >>
  qabbrev_tac `b = pairs f s` >>
  qabbrev_tac `eb = equiv_pairs f s` >>
  irule SUBSET_ANTISYM >>
  rw[SUBSET_DEF] >| [
    `?z. z IN b /\ s' = {z; f z}` by rw[equiv_pairs_element_doublet, Abbr`b`, Abbr`eb`] >>
    `x = z \/ x = f z` by fs[] >-
    simp[] >>
    metis_tac[involute_pairs_element_pair],
    qexists_tac `{x; f x}` >>
    simp[] >>
    metis_tac[equiv_pairs_element_doublet_iff]
  ]
QED

(* Theorem: FINITE s /\ f involute s ==> EVEN (CARD (pairs f s)) *)
(* Proof:
   Note BIGUNION (equiv_pairs f s) = pairs f s    by equiv_pairs_bigunion
    and EVEN (CARD (BIGUNION (equiv_pairs f s)))  by equiv_pairs_bigunion_card_even
   Thus EVEN (CARD (pairs f s)).
*)
Theorem pairs_card_even:
  !f s. FINITE s /\ f involute s ==> EVEN (CARD (pairs f s))
Proof
  rw[GSYM equiv_pairs_bigunion, equiv_pairs_bigunion_card_even]
QED

(* Theorem: FINITE s /\ f involute s ==> (EVEN (CARD s) <=> EVEN (CARD (fixes f s))) *)
(* Proof:
   Note s =|= (fixes f s) # (pairs f s)               by fixes_pairs_split
     so CARD s = CARD (fixes f s) + CARD (pairs f s)  by SPLIT_CARD
    But EVEN (CARD (pairs f s))                       by pairs_card_even
   Thus EVEN (CARD s) <=> EVEN (CARD (fixes f s))     by EVEN_ADD
*)
Theorem involute_set_fixes_both_even:
  !f s. FINITE s /\ f involute s ==> (EVEN (CARD s) <=> EVEN (CARD (fixes f s)))
Proof
  rpt strip_tac >>
  `CARD s = CARD (fixes f s) + CARD (pairs f s)` by rw[fixes_pairs_split, SPLIT_CARD] >>
  `EVEN (CARD (pairs f s))` by rw[pairs_card_even] >>
  metis_tac[EVEN_ADD]
QED

(* Theorem: FINITE s /\ f involute s ==> (ODD (CARD s) <=> ODD (CARD (fixes f s))) *)
(* Proof: by involute_set_fixes_both_even, ODD_EVEN. *)
Theorem involute_set_fixes_both_odd:
  !f s. FINITE s /\ f involute s ==> (ODD (CARD s) <=> ODD (CARD (fixes f s)))
Proof
  rw[involute_set_fixes_both_even, ODD_EVEN]
QED

(* ------------------------------------------------------------------------- *)
(* Reformulate using mates                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define mates of involution *)
Definition mates_def:
   mates f s = s DIFF (fixes f s)
End

(* Theorem: x IN mates f s <=> x IN s /\ f x <> x *)
(* Proof: by mates_def, fixes_def, IN_DIFF *)
Theorem mates_element:
  !f s x. x IN mates f s <=> x IN s /\ f x <> x
Proof
  rw[mates_def, fixes_def] >>
  metis_tac[]
QED

(* Theorem: mates f s SUBSET s *)
(* Proof: by mates_element, SUBSET_DEF *)
Theorem mates_subset:
  !f s. mates f s SUBSET s
Proof
  simp[mates_element, SUBSET_DEF]
QED

(* Theorem: FINITE s ==> FINITE (mates f s) *)
(* Proof: by mates_subset, SUBSET_FINITE *)
Theorem mates_finite:
  !f s. FINITE s ==> FINITE (mates f s)
Proof
  metis_tac[mates_subset, SUBSET_FINITE]
QED

(* Theorem: s = (fixes f s) UNION (mates f s) *)
(* Proof:
   Note (mates f s) = s DIFF (fixes f s)   by mates_def
    and (fixes f s) SUBSET s               by fixes_subset
   Thus s = (fixes f s) UNION (mates f s)  by UNION_DIFF
*)
Theorem mates_fixes_union:
  !f s. s = (mates f s) UNION (fixes f s)
Proof
  simp[mates_def, fixes_subset, UNION_DIFF]
QED

(* Theorem: DISJOINT (mates f s) (fixes f s) *)
(* Proof: by mates_def, DISJOINT_DIFF *)
Theorem mates_fixes_disjoint:
  !f s. DISJOINT (mates f s) (fixes f s)
Proof
  simp[mates_def, DISJOINT_DIFF]
QED

(* Theorem: FINITE s ==> CARD s = CARD (mates f s) + CARD (fixes f s) *)
(* Proof:
   Let a = mates f s, b = fixes f s.
   Then s = a UNION b              by mates_fixes_union
    and DISJOINT a b               by mates_fixes_disjoint
    and FINITE a                   by fixes_finite
    and FINITE b                   by mates_finite
   Thus CARD s = CARD a + CARD b   by CARD_UNION_DISJOINT
*)
Theorem mates_fixes_card:
  !f s. FINITE s ==> CARD s = CARD (mates f s) + CARD (fixes f s)
Proof
  metis_tac[fixes_finite, mates_finite,
            mates_fixes_union, mates_fixes_disjoint, CARD_UNION_DISJOINT]
QED

(* Theorem: f involute s ==> f involute (mates f s) *)
(* Proof: by mates_element *)
Theorem involute_mates:
  !f s. f involute s ==> f involute (mates f s)
Proof
  simp[mates_element]
QED

(* Theorem: f involute s /\ x IN mates f s ==> f x IN mates f s *)
(* Proof: by mates_element *)
Theorem involute_mates_partner:
  !f s x. f involute s /\ x IN mates f s ==> f x IN mates f s
Proof
  simp[mates_element]
QED

(* Theorem: f involute s ==> (pair_by f) equiv_on (mates f s) *)
(* Proof:
   By equiv_on_def, this is to show:
   (1) x IN mates f s ==> pair_by f x x
       True by fpair_refl
   (2) x IN mates f s /\ y IN mates f s ==> pair_by f y x <=> pair_by f x y
       True by mates_element, fpair_sym
   (3) x IN mates f s /\ x' IN mates f s /\ y IN mates f s /\
       pair_by f x x' /\ pair_by f x' y ==> pair_by f x y
       True by mates_element, fpair_trans
*)
Theorem fpair_equiv_on_mates:
  !f s. f involute s ==> (pair_by f) equiv_on (mates f s)
Proof
  rw[equiv_on_def] >-
  simp[fpair_refl] >-
  metis_tac[mates_element, fpair_sym] >>
  metis_tac[mates_element, fpair_trans]
QED

(* Theorem: f involute s ==>
           (t IN partition (pair_by f) (mates f s) <=>
            ?x. x IN (mates f s) /\ t = {x; f x}) *)
(* Proof:
   By partition_def, this is to show:
          ?x. x IN mates f s /\ (t = {y | y IN mates f s /\ pair_by f x y})
      <=> ?x. x IN mates f s /\ (t = {x; f x})
     {y | y IN mates f s /\ pair_by f x y}
   = {y | y IN mates f s /\ (y = x \/ y = f x)}   by fpair_def
   = {x; f x}                                     by mates_element, f x <> x
*)
Theorem mates_partition_element_doublet:
  !f s t. f involute s ==>
          (t IN partition (pair_by f) (mates f s) <=>
           ?x. x IN (mates f s) /\ t = {x; f x})
Proof
  rw[partition_def, fpair_def, EXTENSION] >>
  metis_tac[mates_element]
QED

(* Theorem: FINITE s /\ f involute s /\
            t IN partition (pair_by f) (mates f s) ==> CARD t = 2 *)
(* Proof:
   Note ?x. x IN (mates f s) /\ (t = {x; f x})   by mates_partition_element_doublet
    and f x <> x                                 by mates_element
   thus CARD t = 2                               by CARD_DEF
*)
Theorem mates_partition_element_card:
  !f s t. FINITE s /\ f involute s /\
          t IN partition (pair_by f) (mates f s) ==> CARD t = 2
Proof
  rpt strip_tac >>
  `?x. x IN (mates f s) /\ (t = {x; f x})` by rw[GSYM mates_partition_element_doublet] >>
  fs[mates_element]
QED

(* Theorem: FINITE s /\ f involute s ==> EVEN (CARD (mates f s)) *)
(* Proof:
   Let R = pair_by f, t = mates f s.
   Note FINITE t          by mates_finite
    and R equiv_on t      by fpair_equiv_on_mates
    and !e. e IN (partition R t) ==> (CARD e = 2)
                          by mates_partition_element_card
   Thus CARD t = 2 * CARD (partition R t)
                          by equal_partition_card
     so EVEN (CARD t)     by EVEN_DOUBLE
*)
Theorem mates_card_even:
  !f s. FINITE s /\ f involute s ==> EVEN (CARD (mates f s))
Proof
  rpt strip_tac >>
  qabbrev_tac `t = mates f s` >>
  `!e. e IN partition (\x y. pair_by f x y) t ==> (CARD e = 2)` by metis_tac[mates_partition_element_card] >>
  qabbrev_tac `R = pair_by f` >>
  `FINITE t` by rw[mates_finite, Abbr`t`] >>
  `R equiv_on t` by rw[fpair_equiv_on_mates, Abbr`R`, Abbr`t`] >>
  `CARD t = 2 * CARD (partition R t)` by rw[equal_partition_card] >>
  fs[EVEN_DOUBLE]
QED

(* Theorem: FINITE s /\ f involute s ==> (EVEN (CARD s) <=> EVEN (CARD (fixes f s))) *)
(* Proof:
   Let a = CARD s, b = CARD (mates f s), c = CARD (fixes f s).
   Then a = b + c           by mates_fixes_card
    and EVEN b              by mates_card_even
   Thus EVEN a <=> EVEN c   by EVEN_ADD
*)
Theorem involute_set_fixes_both_even[allow_rebind]:
  !f s. FINITE s /\ f involute s ==> (EVEN (CARD s) <=> EVEN (CARD (fixes f s)))
Proof
  rpt strip_tac >>
  qabbrev_tac `a = CARD s` >>
  qabbrev_tac `b = CARD (mates f s)` >>
  qabbrev_tac `c = CARD (fixes f s)` >>
  `a = b + c` by rw[mates_fixes_card, Abbr`a`, Abbr`b`, Abbr`c`] >>
  `EVEN b` by rw[mates_card_even, Abbr`b`] >>
  metis_tac[EVEN_ADD]
QED

(* This proof is much better! *)

(* ------------------------------------------------------------------------- *)
(* Two Involutions                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ f involute s /\ g involute s ==>
            (EVEN (CARD (fixes f s)) <=> EVEN (CARD (fixes g s))) *)
(* Proof:
       EVEN (CARD (fixes f s)
   <=> EVEN (CARD s)                by involute_set_fixes_both_even
   <=> EVEN (CARD (fixes g s))      by involute_set_fixes_both_even
*)
Theorem involute_two_fixes_both_even:
  !f g s. FINITE s /\ f involute s /\ g involute s ==>
          (EVEN (CARD (fixes f s)) <=> EVEN (CARD (fixes g s)))
Proof
  metis_tac[involute_set_fixes_both_even]
QED

(* Theorem: FINITE s /\ f involute s /\ g involute s ==>
            (ODD (CARD (fixes f s)) <=> ODD (CARD (fixes g s))) *)
(* Proof: by involute_two_fixes_both_even, ODD_EVEN. *)
Theorem involute_two_fixes_both_odd:
  !f g s. FINITE s /\ f involute s /\ g involute s ==>
          (ODD (CARD (fixes f s)) <=> ODD (CARD (fixes g s)))
Proof
  rw[involute_two_fixes_both_even, ODD_EVEN]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
