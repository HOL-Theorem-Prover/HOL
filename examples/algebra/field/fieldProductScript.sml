(* ------------------------------------------------------------------------- *)
(* Product of a set of Field elements                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "fieldProduct";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dividesTheory numberTheory
     combinatoricsTheory;

open fieldTheory;
open ringTheory;
open groupTheory;
open monoidTheory;

(* val _ = load "groupProductTheory"; *)
open groupProductTheory;
open subgroupTheory;

(* ------------------------------------------------------------------------- *)
(* Product of a set of Field elements Documentation                          *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   FPROD s       = field_prod_set r s
*)
(* Definitions and Theorems (# are exported):

   Product of a set of Field elements:
   field_prod_set_def       |- !r s. FPROD s = GPROD_SET f* s
   field_prod_set_empty     |- !r. Field r ==> (FPROD {} = #1)
   field_prod_set_nonzero   |- !r. Field r ==> !s. FINITE s /\ s SUBSET R+ ==> FPROD s IN R+
   field_prod_set_element   |- !r. Field r ==> !s. FINITE s /\ s SUBSET R+ ==> FPROD s IN R
   field_prod_set_thm       |- !r. Field r ==> !s. FINITE s /\ s SUBSET R+ ==>
                               !x. x IN R+ ==> (FPROD (x INSERT s) = x * FPROD (s DELETE x))
   field_prod_set_insert    |- !r. Field r ==> !s. FINITE s /\ s SUBSET R+ ==>
                               !x. x IN R+ /\ x NOTIN s ==> (FPROD (x INSERT s) = x * FPROD s)
   field_prod_set_sing      |- !r. Field r ==> !x. x IN R+ ==> (FPROD {x} = x)
*)

(* ------------------------------------------------------------------------- *)
(* Product of a set of Field elements                                        *)
(* ------------------------------------------------------------------------- *)

(* Define Field Product of a set of Elements. *)
val field_prod_set_def = Define`
   field_prod_set (r:'a field) (s:'a -> bool) = GPROD_SET f* s
`;

(* overload for field_prod_set *)
val _ = overload_on ("FPROD", ``field_prod_set r``);

(* Theorem: Field r ==> (FPROD {} = #1) *)
(* Proof:
     FPROD {}
   = GPROD_SET f* {}     by field_prod_set_def
   = f*.id               by GPROD_SET_EMPTY
   = #1                  by field_nonzero_mult_property
*)
val field_prod_set_empty = store_thm(
  "field_prod_set_empty",
  ``!r:'a field. Field r ==> (FPROD {} = #1)``,
  rw[field_prod_set_def, GPROD_SET_EMPTY, field_nonzero_mult_property]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R+ ==> FPROD s IN R+ *)
(* Proof:
    Note Field r
     ==> AbelianGroup f*              by field_nonzero_mult_is_abelian_group
     ==> AbelianMonoid f*             by abelian_group_is_abelian_monoid
    Also F* = R+                      by field_mult_carrier
     Now FPROD s = GPROD_SET f* s     by field_prod_set_def
   Hence FPROD s IN F*                by GPROD_SET_PROPERTY
      or FPROD s IN R+                by above, field_mult_carrier
*)
val field_prod_set_nonzero = store_thm(
  "field_prod_set_nonzero",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R+ ==> FPROD s IN R+``,
  rw[field_prod_set_def] >>
  `AbelianGroup f*` by rw[field_nonzero_mult_is_abelian_group] >>
  `AbelianMonoid f*` by rw[abelian_group_is_abelian_monoid] >>
  `F* = R+` by rw[field_mult_carrier] >>
  metis_tac[GPROD_SET_PROPERTY]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R+ ==> FPROD s IN R *)
(* Proof: by field_prod_set_nonzero, field_nonzero_element *)
val field_prod_set_element = store_thm(
  "field_prod_set_element",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R+ ==> FPROD s IN R``,
  rw[field_prod_set_nonzero, field_nonzero_element]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R+ ==>
            !x. x IN R+ ==> (FPROD (x INSERT s) = x * FPROD (s DELETE x)) *)
(* Proof:
    Note Field r
     ==> AbelianGroup f*              by field_nonzero_mult_is_abelian_group
     ==> AbelianMonoid f*             by abelian_group_is_abelian_monoid
    Also F* = R+                      by field_mult_carrier
     Now FPROD (x INSERT s)
       = GPROD_SET f* (x INSERT s)             by field_prod_set_def
       = f*.op x (GPROD_SET f* (s DELETE x)))  by GPROD_SET_THM
       = x * (GPROD_SET f* (s DELETE x)))      by field_nonzero_mult_property
       = x * FPROD (s DELETE x)                by field_prod_set_def
*)
val field_prod_set_thm = store_thm(
  "field_prod_set_thm",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R+ ==>
   !x. x IN R+ ==> (FPROD (x INSERT s) = x * FPROD (s DELETE x))``,
  rw[field_prod_set_def] >>
  `AbelianGroup f*` by rw[field_nonzero_mult_is_abelian_group] >>
  `AbelianMonoid f*` by rw[abelian_group_is_abelian_monoid] >>
  `(F* = R+) /\ (f*.op = $* )` by rw[field_nonzero_mult_property] >>
  metis_tac[GPROD_SET_THM]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R+ ==>
            !x. x IN R+ /\ x NOTIN s ==> (FPROD (x INSERT s) = x * FPROD s) *)
(* Proof:
      FPROD (x INSERT s)
    = x * FPROD (s DELETE x)     by field_prod_set_thm
    = x * FPROD s                by DELETE_NON_ELEMENT
*)
val field_prod_set_insert = store_thm(
  "field_prod_set_insert",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R+ ==>
   !x. x IN R+ /\ x NOTIN s ==> (FPROD (x INSERT s) = x * FPROD s)``,
  rw[field_prod_set_thm, DELETE_NON_ELEMENT]);

(* Theorem: Field r ==> !x. x IN R+ ==> (FPROD {x} = x) *)
(* Proof:
   Since FINITE {}            by FINITE_EMPTY
     and {} SUBSET R+         by EMPTY_SUBSET
    Note x NOTIN {}           by MEMBER_NOT_EMPTY
     and x IN R               by field_nonzero_element

     FPROD {x}
   = FPROD (x INSERT {})      by notation
   = x * FPROD {}             by field_prod_set_insert
   = x * #1                   by field_prod_set_empty
   = x                        by field_mult_rone
*)
val field_prod_set_sing = store_thm(
  "field_prod_set_sing",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> (FPROD {x} = x)``,
  rw[field_prod_set_insert, field_prod_set_empty, field_nonzero_element]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
