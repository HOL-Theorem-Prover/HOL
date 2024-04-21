(* ------------------------------------------------------------------------- *)
(* Units in a Ring                                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringUnit";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory;

open ringTheory;
open groupTheory;
open monoidTheory;
open groupOrderTheory;

(* ------------------------------------------------------------------------- *)
(* Ring Units Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(*
   Overloading:
   r*       = Invertibles (r.prod)
   R*       = r*.carrier
   unit x   = x IN R*
   |/       = r*.inv
   x =~ y   = unit_eq r x y
*)
(* Definitions and Theorems (# are exported):

   Units in a Ring:
   ring_units_property       |- !r. Ring r ==> (r*.op = $* ) /\ (r*.id = #1)
   ring_units_has_one        |- !r. Ring r ==> #1 IN R*
   ring_units_has_zero       |- !r. Ring r ==> (#0 IN R* <=> (#1 = #0))
   ring_units_element        |- !r. Ring r ==> !x. x IN R* ==> x IN R

   Units in a Ring form a Group:
   ring_units_group          |- !r. Ring r ==> Group r*
   ring_units_abelain_group  |- !r. Ring r ==> AbelianGroup r*

   Ring Units:
#  ring_unit_one             |- !r. Ring r ==> unit #1
   ring_unit_zero            |- !r. Ring r ==> (unit #0 <=> (#1 = #0))
   ring_unit_nonzero         |- !r. Ring r /\ #1 <> #0 ==> !x. unit x ==> x <> #0
   ring_unit_has_inv         |- !r. Ring r ==> !x. unit x ==> unit ( |/ x)
   ring_unit_linv            |- !r. Ring r ==> !x. unit x ==> ( |/ x * x = #1)
   ring_unit_rinv            |- !r. Ring r ==> !x. unit x ==> (x * |/ x = #1)
#  ring_unit_element         |- !r. Ring r ==> !x. unit x ==> x IN R
   ring_unit_inv_element     |- !r. Ring r ==> !x. unit x ==> |/ x IN R
   ring_unit_inv_nonzero     |- !r. Ring r /\ #1 <> #0 ==> !x. unit x ==> |/ x <> #0
   ring_unit_mult_zero       |- !r. Ring r ==> !x y. unit x /\ y IN R ==> ((x * y = #0) <=> (y = #0))
   ring_unit_property        |- !r. Ring r ==> !u. unit u <=> u IN R /\ ?v. v IN R /\ (u * v = #1)
   ring_unit_neg             |- !r. Ring r ==> !x. unit x ==> unit (-x)
   ring_unit_mult_unit       |- !r. Ring r ==> !u v. unit u /\ unit v ==> unit (u * v)
   ring_unit_mult_eq_unit    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (unit (x * y) <=> unit x /\ unit y)
   ring_unit_rinv_unique     |- !r. Ring r ==> !u v. unit u /\ v IN R /\ (u * v = #1) ==> (v = |/ u)
   ring_unit_linv_unique     |- !r. Ring r ==> !u v. u IN R /\ unit v /\ (u * v = #1) ==> (u = |/ v)
   ring_unit_inv_inv         |- !r. Ring r ==> !u. unit u ==> (u = |/ ( |/ u))
   ring_unit_linv_inv        |- !r. Ring r ==> !u v. unit u /\ v IN R /\ ( |/ u * v = #1) ==> (u = v)
   ring_unit_rinv_inv        |- !r. Ring r ==> !u v. u IN R /\ unit v /\ (u * |/ v = #1) ==> (u = v)
#  ring_inv_one              |- !r. Ring r ==> ( |/ #1 = #1)

   Ring Unit Equivalence:
   unit_eq_def       |- !r x y. x =~ y <=> ?u. unit u /\ (x = u * y)
   unit_eq_refl      |- !r. Ring r ==> !x. x IN R ==> x =~ x
   unit_eq_sym       |- !r. Ring r ==> !x y. x IN R /\ y IN R /\ x =~ y ==> y =~ x
   unit_eq_trans     |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R /\ x =~ y /\ y =~ z ==> x =~ z
   ring_eq_unit_eq   |- !r. Ring r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y
*)

(* ------------------------------------------------------------------------- *)
(* Units in a Ring = Invertibles of (r.prod).                                *)
(* ------------------------------------------------------------------------- *)

(*
(* Define the Units of a Ring *)
val Units_def = Define`
  Units (r:'a ring) = Invertibles (r.prod)
`;
*)
val _ = overload_on ("r*", ``Invertibles (r.prod)``); (* instead of r_star *)
val _ = overload_on ("R*", ``r*.carrier``); (* instead of R_star *)

(* Theorem: r*.op = r.prod.op /\ r*.id = #1 *)
(* Proof: by ring_of_units, and Invertibles_def *)
val ring_units_property = store_thm(
  "ring_units_property",
  ``!r:'a ring. Ring r ==> (r*.op = r.prod.op) /\ (r*.id = #1)``,
  rw_tac std_ss[Invertibles_def]);

(* Theorem: #1 IN R* *)
(* Proof: by monoid_id_invertible. *)
val ring_units_has_one = store_thm(
  "ring_units_has_one",
  ``!r:'a ring. Ring r ==> #1 IN R*``,
  rw[ring_mult_monoid, Invertibles_def]);

(* Theorem: #0 IN R* ==> #1 = #0 *)
(* Proof:
   If part: #0 IN R* ==> #1 = #0
      This means ?x. x IN R* /\ x * #0 = #1 /\ #0 * x = #1   by monoid_invertibles_def
      Therefore #1 = #0 by ring_mult_lzero, ring_mult_rzero.
   Only-if part: #1 = #0 ==> #0 IN R*
      true ring_units_has_one.
*)
val ring_units_has_zero = store_thm(
  "ring_units_has_zero",
  ``!r:'a ring. Ring r ==> (#0 IN R* <=> (#1 = #0))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `Monoid r.prod /\ (r.prod.carrier = R)` by rw_tac std_ss[ring_mult_monoid] >>
    `R* = monoid_invertibles r.prod` by rw_tac std_ss[Invertibles_def] >>
    metis_tac[ring_mult_lzero, monoid_inv_from_invertibles],
    metis_tac[ring_units_has_one]
  ]);

(* Theorem: Ring r ==> x IN R* ==> x IN R *)
(* Proof:
       x IN R*
   ==> x IN (Invertibles (r.prod)).carrier
   ==> x IN monoid_invertibles r.prod         by Invertibles_def
   ==> x IN r.prod.carrier                    by monoid_invertibles
   ==> x IN R                                 by ring_carriers
*)
val ring_units_element = store_thm(
  "ring_units_element",
  ``!r:'a ring. Ring r ==> !x. x IN R* ==> x IN R``,
  rw[Invertibles_def, monoid_invertibles_def]);

(* ------------------------------------------------------------------------- *)
(* Units in a Ring form a Group.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> Group r* *)
(* Proof: by monoid_invertibles_is_group, ring_mult_monoid. *)
val ring_units_group = store_thm(
  "ring_units_group",
  ``!r:'a ring. Ring r ==> Group r*``,
  rw[monoid_invertibles_is_group, ring_mult_monoid]);

(* Theorem: Units of Ring is an Abelian Group. *)
(* Proof: by checking definition.
   (1) Ring r ==> Group r*
       by ring_units_group
   (2) x IN R* /\ y IN R* ==> r*op x y = r*.op y x
       x IN R /\ y IN R       by ring_units_element
       r*.op = r.prod.op      by ring_units_property
       Hence true             by ring_mult_monoid
*)
val ring_units_abelain_group = store_thm(
  "ring_units_abelain_group",
  ``!r:'a ring. Ring r ==> AbelianGroup r*``,
  rw[AbelianGroup_def, ring_units_group] >>
  rw[ring_units_element, ring_mult_monoid, ring_units_property]);

(* ------------------------------------------------------------------------- *)
(* Units in a Ring have inverses.                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Ring Units                                                                *)
(* ------------------------------------------------------------------------- *)

(* define unit by overloading *)
val _ = overload_on ("unit", ``\x. x IN R*``);

(* Theorem: #1 IN R* *)
(* Proof: by monoid_id_invertible. *)
val ring_unit_one = store_thm(
  "ring_unit_one",
  ``!r:'a ring. Ring r ==> unit #1``,
  rw[ring_mult_monoid, Invertibles_def]);

(* export simple result *)
val _ = export_rewrites ["ring_unit_one"];

(* Theorem: #0 IN R* ==> #1 = #0 *)
(* Proof:
   If part: #0 IN R* ==> #1 = #0
      This means ?x. x IN R* /\ x * #0 = #1 /\ #0 * x = #1   by monoid_invertibles_def
      Therefore #1 = #0 by ring_mult_lzero, ring_mult_rzero.
   Only-if part: #1 = #0 ==> #0 IN R*
      True by ring_unit_one.
*)
val ring_unit_zero = store_thm(
  "ring_unit_zero",
  ``!r:'a ring. Ring r ==> (unit #0 <=> (#1 = #0))``,
  rw[EQ_IMP_THM] >| [
    `Monoid r.prod /\ (r.prod.carrier = R)` by rw[ring_mult_monoid] >>
    `R* = monoid_invertibles r.prod` by rw[Invertibles_def] >>
    metis_tac[ring_mult_lzero, monoid_inv_from_invertibles],
    metis_tac[ring_unit_one]
  ]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. unit x ==> x <> #0 *)
(* Proof: by ring_unit_zero: |- !r. Ring r ==> (unit #0 <=> (#1 = #0)) *)
val ring_unit_nonzero = store_thm(
  "ring_unit_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !x. unit x ==> x <> #0``,
  metis_tac[ring_unit_zero]);

(*
group_inv_element |> SPEC ``r*``;
|- Group r* ==> !x. x IN R* ==> r*.inv x IN R*: thm
group_inv_element |> SPEC ``r*`` |> UNDISCH_ALL |> PROVE_HYP (ring_units_group |> SPEC_ALL |> UNDISCH_ALL);
group_inv_element |> SPEC ``r*`` |> UNDISCH_ALL |> PROVE_HYP (ring_units_group |> SPEC_ALL |> UNDISCH_ALL)
    |> DISCH_ALL |> GEN_ALL;
|- !r. Ring r ==> !x. x IN R* ==> r*.inv x IN R*: thm
*)

(* Lifting Group Inverse Theorem for Ring units
   from: !g: 'a group. Group g ==> E(g.inv)
     to: !r:'a ring.  Ring r ==> E(r*.inv)
    via: !r:'a ring.  Ring r ==> Group r*
*)
local
val rug = ring_units_group |> SPEC_ALL |> UNDISCH_ALL
val rupropery = ring_units_property |> SPEC_ALL |> UNDISCH_ALL
in
fun lift_group_inv_thm gsuffix rsuffix = let
  val thm = DB.fetch "group" ("group_" ^ gsuffix)
  val thm' = thm |> SPEC ``r*`` |> UNDISCH_ALL
in
  save_thm("ring_" ^ rsuffix,
           thm' |> PROVE_HYP rug
           |> REWRITE_RULE [rupropery]
           |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* overloading for inverse *)
val _ = overload_on ("|/", ``r*.inv``);

(* Theorem: x IN R* ==> |/ x IN R* *)
(* Proof: by group_inv_element, ring_units_group. *)
val ring_unit_has_inv = lift_group_inv_thm "inv_element" "unit_has_inv";
(* val ring_unit_has_inv = |- !r. Ring r ==> !x. unit x ==> unit ( |/ x) : thm *)

(* Theorem: x IN R* ==> |/ x * x = #1 *)
(* Proof: by group_linv, ring_units_group. *)
val ring_unit_linv = lift_group_inv_thm "linv" "unit_linv";
(* val ring_unit_linv = |- !r. Ring r ==> !x. unit x ==> ( |/ x * x = #1) : thm *)

(* Theorem: x IN R* ==> x * |/ x = #1 *)
(* Proof: by group_rinv, ring_units_group. *)
val ring_unit_rinv = lift_group_inv_thm "rinv" "unit_rinv";
(* val ring_unit_rinv = |- !r. Ring r ==> !x. unit x ==> (x * |/ x = #1) : thm *)

(* Theorem: x IN R* ==> x IN R *)
val ring_unit_element = save_thm("ring_unit_element", ring_units_element);
(* > val ring_unit_element = |- !r. Ring r ==> !x. unit x ==> x IN R : thm *)

(* export simple result *)
val _ = export_rewrites ["ring_unit_element"];

(* Theorem: x IN R* ==> |/ x IN R *)
(* Proof: by ring_unit_has_inv, ring_unit_element. *)
val ring_unit_inv_element = store_thm(
  "ring_unit_inv_element",
  ``!r:'a ring. Ring r ==> !x. unit x ==> |/ x IN R``,
  rw[ring_unit_has_inv]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. unit x ==> |/ x <> #0 *)
(* Proof:
   By contradiction, suppose |/ x = #0.
     #1 = x * |/x          by ring_unit_rinv
        = x * #0           by assumption
        = #0               by ring_mult_rzero
   This contradicts #1 <> #0.
*)
val ring_unit_inv_nonzero = store_thm(
  "ring_unit_inv_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !x. unit x ==> |/ x <> #0``,
  metis_tac[ring_unit_rinv, ring_mult_rzero, ring_unit_element]);

(* Theorem: x IN R*, y IN R, x * y = #0 <=> y = #0 *)
(* Proof:
                   x * y = #0
   <=>     |/x * (x * y) = |/x * #0 = #0    by ring_mult_rzero
   <=>     ( |/x * x) * y = #0              by ring_mult_assoc
   <=>            #1 * y = #0               by ring_unit_linv
   <=>                 y = #0               by ring_mult_lone
*)
val ring_unit_mult_zero = store_thm(
  "ring_unit_mult_zero",
  ``!r:'a ring. Ring r ==> !x y. unit x /\ y IN R ==> ((x * y = #0) <=> (y = #0))``,
  rpt strip_tac >>
  `x IN R` by rw[] >>
  rw[EQ_IMP_THM] >>
  `|/x IN R` by rw[ring_unit_inv_element] >>
  `y = #1 * y` by rw[] >>
  `_ = ( |/x * x) * y` by rw[ring_unit_linv] >>
  metis_tac[ring_mult_assoc, ring_mult_rzero]);

(* Theorem: Ring r ==> !u. unit u <=> ?v. u * v = #1 *)
(* Proof:
   If part: unit u ==> ?v. u * v = #1
     unit u ==> |/u IN R, and u * |/u = #1, so take v = |/u.
   Only-if part: ?v. u * v = #1 ==> unit u
     by definition of unit x = x IN R*
                             = x IN r*.carrier
                             = x IN (Invertibles (r.prod)).carrier
*)
val ring_unit_property = store_thm(
  "ring_unit_property",
  ``!r:'a ring. Ring r ==> !u. unit u <=> u IN R /\ (?v. v IN R /\ (u * v = #1))``,
  rw[EQ_IMP_THM] >-
  metis_tac[ring_unit_inv_element, ring_unit_rinv] >>
  `r.prod.carrier = R` by rw[ring_mult_monoid] >>
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, GSPECIFICATION] >>
  metis_tac[ring_mult_comm]);

(* Theorem: Ring r ==> !x. unit x ==> unit (-x) *)
(* Proof:
   Since unit x
     ==> x IN R /\ ?v. v IN R /\ x * v = #1    by ring_unit_property
   hence (-x) * (-v) = x * v                   by ring_mult_neg_neg
                     = #1                      by above
   Since -v IN R                               by ring_neg_element
   Hence unit (-x)                             by ring_unit_property
*)
val ring_unit_neg = store_thm(
  "ring_unit_neg",
  ``!r:'a ring. Ring r ==> !x. unit x ==> unit (-x)``,
  metis_tac[ring_unit_property, ring_mult_neg_neg, ring_neg_element]);

(* Theorem: Ring r ==> !u v. unit u /\ unit v ==> unit (u * v) *)
(* Proof:
   Let z = |/ v * |/ u
   Since |/ u IN R /\ |/ v IN R     by ring_unit_inv_element
      so z IN R                     by ring_mult_element
    also (u * v) * z
       = (u * v) * ( |/ v * |/ u)   by above
       = (u * v * |/ v) * |/u       by ring_mult_assoc
       = u * |/ u                   by ring_unit_rinv, ring_mult_rone
       = #1                         by ring_unit_rinv
   Hence unit (u * v)               by ring_unit_property
*)
val ring_unit_mult_unit = store_thm(
  "ring_unit_mult_unit",
  ``!r:'a ring. Ring r ==> !u v. unit u /\ unit v ==> unit (u * v)``,
  rpt strip_tac >>
  qabbrev_tac `z = |/ v * |/ u` >>
  `u IN R /\ v IN R` by rw[ring_unit_element] >>
  `|/ v IN R /\ |/ u IN R` by rw[ring_unit_inv_element] >>
  `z IN R` by rw[Abbr`z`] >>
  `(u * v) * z = (u * v) * ( |/ v * |/ u)` by rw[Abbr`z`] >>
  `_ = u * (v * ( |/ v * |/ u))` by rw[ring_mult_assoc] >>
  `_ = u * (v * |/ v * |/ u)` by rw[ring_mult_assoc] >>
  `_ = u * |/ u` by rw[ring_unit_rinv] >>
  `_ = #1` by rw[ring_unit_rinv] >>
  metis_tac[ring_unit_property, ring_mult_element]);

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==>
            (unit (x * y) <=> unit x /\ unit y) *)
(* Proof:
   If part: unit (x * y) ==> unit x /\ unit y
      Let z = x * y.
      Then z IN R /\
           ?u. u IN R /\ (z * u = #1)   by ring_unit_property
       ==> (x * y) * u = #1             by z = x * y
       ==> x * (y * u) = #1             by ring_mult_assoc
       Hence unit x                     by ring_unit_property, ring_mult_element
       Also (y * u) * x = #1            by ring_mult_comm
       ==>  y * (u * x) = #1            by ring_mult_assoc
       Hence unit y                     by ring_unit_property, ring_mult_element

   Only-if part: unit x /\ unit y ==> unit (x * y)
      This is true         by ring_unit_mult_unit
*)
val ring_unit_mult_eq_unit = store_thm(
  "ring_unit_mult_eq_unit",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
    (unit (x * y) <=> unit x /\ unit y)``,
  rpt strip_tac >>
  simp[EQ_IMP_THM] >>
  ntac 2 strip_tac >| [
    qabbrev_tac `z = x * y` >>
    `z IN R /\ ?u. u IN R /\ (z * u = #1)` by metis_tac[ring_unit_property] >>
    `x * (y * u) = #1` by rw[GSYM ring_mult_assoc, Abbr`z`] >>
    `y * (u * x) = #1` by rw[GSYM ring_mult_assoc, ring_mult_comm, Abbr`z`] >>
    metis_tac[ring_unit_property, ring_mult_element],
    rw[ring_unit_mult_unit]
  ]);

(* Theorem: Ring r ==> unit u /\ u * v = #1 ==> v = |/ u *)
(* Proof:
   unit u ==> |/ u in R             by ring_unit_inv_element
   so  |/ u * (u * v) = |/ u * #1
   or  ( |/ u * u) * v = |/ u * #1  by ring_mult_assoc
               #1 * v = |/ u * #1   by ring_unit_linv
                    v = |/ u        by ring_mult_lone, ring_mult_rone
*)
val ring_unit_rinv_unique = store_thm(
  "ring_unit_rinv_unique",
  ``!r:'a ring. Ring r ==> !u v. unit u /\ v IN R /\ (u * v = #1) ==> (v = |/ u)``,
  rpt strip_tac >>
  `u IN R /\ |/ u IN R` by rw[ring_unit_inv_element] >>
  `v = ( |/u * u) * v` by rw[ring_unit_linv] >>
  `_ = |/ u * (u * v)` by rw[ring_mult_assoc] >>
  `_ = |/ u` by rw[] >>
  rw[]);

(* Theorem: Ring r ==> unit v /\ u * v = #1 ==> u = |/ v *)
(* Proof: by ring_unit_rinv_unique and ring_mult_comm. *)
val ring_unit_linv_unique = store_thm(
  "ring_unit_linv_unique",
  ``!r:'a ring. Ring r ==> !u v. u IN R /\ unit v /\ (u * v = #1) ==> (u = |/ v)``,
  rw[ring_unit_rinv_unique, ring_mult_comm]);

(* Theorem: Ring r ==> unit u ==> |/ ( |/ u) = u *)
(* Proof: by ring_unit_rinv_unique, put v = |/ u. *)
val ring_unit_inv_inv = store_thm(
  "ring_unit_inv_inv",
  ``!r:'a ring. Ring r ==> !u. unit u ==> (u = |/ ( |/ u))``,
  rw[ring_unit_inv_element, ring_unit_has_inv, ring_unit_linv, ring_unit_rinv_unique]);

(* Theorem: Ring r ==> unit u /\ |/ u * v = #1 ==> u = v *)
(* Proof:
   unit u ==> |/ u in R           by ring_unit_inv_element
   so   u * ( |/ u * v) = u * #1
   or   (u * |/ u) * v = u * #1   by ring_mult_assoc
   or           #1 * v = u * #1   by ring_unit_rinv
   or                v = u        by ring_mult_lone, ring_mult_rone
*)
val ring_unit_linv_inv = store_thm(
  "ring_unit_linv_inv",
  ``!r:'a ring. Ring r ==> !u v. unit u /\ v IN R /\ ( |/ u * v = #1) ==> (u = v)``,
  rpt strip_tac >>
  `u IN R /\ |/ u IN R` by rw[ring_unit_inv_element] >>
  `u = (u * |/ u) * v` by rw[ring_mult_assoc] >>
  `_ = v` by rw[ring_unit_rinv] >>
  rw[]);

(* Theorem: Ring r ==> unit v /\ u * |/ v = #1 ==> u = v *)
(* Proof: by ring_unit_linv_inv and ring_mult_comm. *)
val ring_unit_rinv_inv = store_thm(
  "ring_unit_rinv_inv",
  ``!r:'a ring. Ring r ==> !u v. u IN R /\ unit v /\ (u * |/ v = #1) ==> (u = v)``,
  metis_tac[ring_unit_linv_inv, ring_mult_comm, ring_unit_inv_element]);

(* Theorem: Ring r ==> ( |/ #1 = #1) *)
(* Proof:
   Note Group r*                by ring_units_group
    and r*.id = #1              by ring_units_property
   Thus r*.inv r*.id = r*.id    by group_inv_id
     or        |/ #1 = #1       by notation
*)
val ring_inv_one = store_thm(
  "ring_inv_one",
  ``!r:'a ring. Ring r ==> ( |/ #1 = #1)``,
  rpt strip_tac >>
  `Group r*` by rw[ring_units_group] >>
  `r*.id = #1` by rw[ring_units_property] >>
  metis_tac[group_inv_id]);

(* export simple theorem *)
val _ = export_rewrites ["ring_inv_one"];

(* ------------------------------------------------------------------------- *)
(* Ring Unit Equivalence                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define unit equivalence for ring *)
Definition unit_eq_def:
   unit_eq (r:'a ring) (x:'a) (y:'a) = ?(u:'a). unit u /\ (x = u * y)
End
(* overload on unit equivalence *)
val _ = overload_on("=~", ``unit_eq r``);
val _ = set_fixity "=~" (Infix(NONASSOC, 450)); (* same as relation *)
(*
> unit_eq_def;
val it = |- !r x y. x =~ y <=> ?u. unit u /\ (x = u * y): thm
*)

(* Theorem: Ring r ==> !x. x IN R ==> x =~ x *)
(* Proof:
   Since unit #1      by ring_unit_one
     and x = #1 * x   by ring_mult_lone
   Hence x =~ x       by unit_eq_def
*)
Theorem unit_eq_refl:
  !r:'a ring. Ring r ==> !x. x IN R ==> x =~ x
Proof
  metis_tac[unit_eq_def, ring_unit_one, ring_mult_lone]
QED

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R /\ x =~ y ==> y =~ x *)
(* Proof:
   Since x =~ y
     ==> ?u. unit u /\ (x = u * y)    by unit_eq_def
     and unit ( |/ u)                 by ring_unit_has_inv
     and |/ u * u = #1                by ring_unit_linv
      so y = #1 * y                   by ring_mult_lone
           = ( |/ u * u) * y          by above
           = |/ u * (u * y)           by ring_mult_assoc, ring_unit_element
           = |/ u * x                 by above
   Hence y =~ x  by taking ( |/ u)    by unit_eq_def
*)
Theorem unit_eq_sym:
  !r:'a ring. Ring r ==> !x y. x IN R /\ y IN R /\ x =~ y ==> y =~ x
Proof
  rw[unit_eq_def] >>
  `unit ( |/ u)` by rw[ring_unit_has_inv] >>
  `|/ u * u = #1` by rw[ring_unit_linv] >>
  metis_tac[ring_mult_assoc, ring_unit_element, ring_mult_lone]
QED

(* Theorem: Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R /\ x =~ y /\ y =~ z ==> x =~ z *)
(* Proof:
   Since x =~ y
     ==> ?u. unit u /\ (x = u * y)    by unit_eq_def
     and y =~ z
     ==> ?v. unit v /\ (y = v * z)    by unit_eq_def
   Hence x = u * (v * z)              by above
           = (u * v) * z              by ring_mult_assoc, ring_unit_element
     and unit (u * v)                 by ring_unit_mult_unit
    Thus x =~ z                       by unit_eq_def
*)
Theorem unit_eq_trans:
  !r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R /\ x =~ y /\ y =~ z ==> x =~ z
Proof
  rw[unit_eq_def] >>
  qexists_tac `u * u'` >>
  rw[ring_unit_element, ring_unit_mult_unit, ring_mult_assoc]
QED

(* Theorem: Ring r ==> !x. x IN R /\ y IN R /\ (x = y) ==> x =~ y *)
(* Proof: by unit_eq_refl *)
Theorem ring_eq_unit_eq:
  !r:'a ring. Ring r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y
Proof
  rw[unit_eq_refl]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
