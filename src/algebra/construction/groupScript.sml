(* ------------------------------------------------------------------------- *)
(* Group library                                                             *)
(* ========================================================================= *)
(*  A group is an algebraic structure: a monoid with all its elements        *)
(*  invertible.                                                              *)
(* ------------------------------------------------------------------------- *)
(* Group Theory -- axioms to exponentiation.                                 *)
(* Group Maps                                                                *)
(* Group Theory -- Subgroups (Cosets, Lagrange's Theorem)                    *)
(* Group Theory -- Normal subgroup and Quotient Groups.                      *)
(* Group Theory -- Iterated Product.                                         *)
(* Finite Group Order                                                        *)
(* Finite Group Theory                                                       *)
(* Applying Group Theory: Group Instances                                    *)
(* Cyclic Group                                                              *)
(* Group Action, Orbits and Fixed points.                                    *)
(* Group Correspondence Theory                                               *)
(* Congruences from Number Theory                                            *)
(* ------------------------------------------------------------------------- *)
(* (Joseph) Hing-Lun Chan, The Australian National University, 2014-2019     *)
(* ------------------------------------------------------------------------- *)

(*
based on: examples/elliptic/groupScript.sml

The idea behind this script is discussed in (Secton 2.1.1. Groups):

Formalizing Elliptic Curve Cryptography in Higher Order Logic (Joe Hurd)
http://www.gilith.com/research/papers/elliptic.pdf

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "group";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory prim_recTheory arithmeticTheory dividesTheory gcdTheory
     gcdsetTheory listTheory;

open numberTheory combinatoricsTheory primeTheory;

open monoidTheory; (* for G*, monoid_invertibles_is_monoid *)

(* ------------------------------------------------------------------------- *)
(* Group Documentation                                                       *)
(* ------------------------------------------------------------------------- *)
(* Data type (same as monoid):
   The generic symbol for group data is g.
   g.carrier = Carrier set of group, overloaded as G.
   g.op      = Binary operation of group, overloaded as *.
   g.id      = Identity element of group, overloaded as #e.
   g.exp     = Iteration of g.op (added by monoid)
   g.inv     = Inverse of g.op   (added by monoid)
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   Group_def               |- !g. Group g <=> Monoid g /\ (G* = G)
   AbelianGroup_def        |- !g. AbelianGroup g <=> Group g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
   FiniteGroup_def         |- !g. FiniteGroup g <=> Group g /\ FINITE G
   FiniteAbelianGroup_def  |- !g. FiniteAbelianGroup g <=> AbelianGroup g /\ FINITE G

   Extract from definition:
   group_clauses           |- !g. Group g ==> Monoid g /\ (G* = G)
#  group_is_monoid         |- !g. Group g ==> Monoid g
#  group_all_invertible    |- !g. Group g ==> (G* = G)

   Simple theorems:
   monoid_invertibles_is_group   |- !g. Monoid g ==> Group (Invertibles g)
   finite_monoid_invertibles_is_finite_group
                                 |- !g. FiniteMonoid g ==> FiniteGroup (Invertibles g)
   FiniteAbelianGroup_def_alt    |- !g. FiniteAbelianGroup g <=>
                                        FiniteGroup g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
   finite_group_is_group         |- !g. FiniteGroup g ==> Group g
   finite_group_is_monoid        |- !g. FiniteGroup g ==> Monoid g
   finite_group_is_finite_monoid |- !g. FiniteGroup g ==> FiniteMonoid g
   abelian_group_is_abelian_monoid
                                 |- !g. AbelianGroup g ==> AbelianMonoid g
   finite_abelian_group_is_finite_abelian_monoid
                                 |- !g. FiniteAbelianGroup g ==> FiniteAbelianMonoid g

   Group theorems (lift or take from Monoid):
   group_id_element   |- !g. Group g ==> #e IN G
   group_op_element   |- !g. Group g ==> !x y. x IN G /\ y IN G ==> x * y IN G
   group_assoc        |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z))
   group_lid          |- !g. Group g ==> !x. x IN G ==> (#e * x = x)
   group_rid          |- !g. Group g ==> !x. x IN G ==> (x * #e = x)
   group_id           |- !g. Group g ==> !x. x IN G ==> (#e * x = x) /\ (x * #e = x)
   group_id_id        |- !g. Group g ==> (#e * #e = #e)
   group_exp_element  |- !g. Group g ==> !x. x IN G ==> !n. x ** n IN G
   group_exp_SUC      |- !g x n. x ** SUC n = x * x ** n
   group_exp_suc      |- !g. Group g ==> !x. x IN G ==> !n. x ** SUC n = x ** n * x
   group_exp_0        |- !g x. x ** 0 = #e
   group_exp_1        |- !g. Group g ==> !x. x IN G ==> (x ** 1 = x)
   group_id_exp       |- !g. Group g ==> !n. #e ** n = #e
   group_comm_exp     |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) ==> !n. x ** n * y = y * x ** n
   group_exp_comm     |- !g. Group g ==> !x. x IN G ==> !n. x ** n * x = x * x ** n
   group_comm_op_exp  |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n. (x * y) ** n = x ** n * y ** n
   group_exp_add      |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n + k) = x ** n * x ** k
   group_exp_mult     |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n * k) = (x ** n) ** k

   Group theorems (from Monoid invertibles).
#  group_inv_element  |- !g. Group g ==> !x. x IN G ==> |/ x IN G
#  group_linv         |- !g. Group g ==> !x. x IN G ==> ( |/ x * x = #e)
#  group_rinv         |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e)
   group_inv_thm      |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e) /\ ( |/ x * x = #e)
   group_carrier_nonempty  |- !g. Group g ==> G <> {}

   Group theorems (not from Monoid):
   group_lcancel     |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = x * z) <=> (y = z))
   group_rcancel     |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((y * x = z * x) <=> (y = z))

   Inverses with assocative law:
   group_linv_assoc  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (y = x * ( |/ x * y)) /\ (y = |/ x * (x * y))
   group_rinv_assoc  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (y = y * |/ x * x) /\ (y = y * x * |/ x)
   group_lsolve      |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) <=> (x = z * |/ y))
   group_rsolve      |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) <=> (y = |/ x * z))
   group_lid_unique  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) <=> (y = #e))
   group_rid_unique  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = x) <=> (y = #e))
   group_id_unique   |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) <=> (y = #e)) /\
                                                                   ((x * y = x) <=> (y = #e))
   group_linv_unique |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) <=> (x = |/ y))
   group_rinv_unique |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) <=> (y = |/ x))
#  group_inv_inv     |- !g. Group g ==> !x. x IN G ==> ( |/ ( |/ x) = x)
#  group_inv_eq      |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x = |/ y) <=> (x = y))
#  group_inv_eq_swap |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x = y) <=> (x = |/ y))
#  group_inv_id      |- !g. Group g ==> ( |/ #e = #e)
   group_inv_eq_id   |- !g. Group g ==> !x. x IN G ==> (( |/ x = #e) <=> (x = #e))
   group_inv_op      |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ( |/ (x * y) = |/ y * |/ x)
   group_pair_reduce |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * z * |/ (y * z) = x * |/ y)
   group_id_fix      |- !g. Group g ==> !x. x IN G ==> ((x * x = x) <=> (x = #e))
   group_op_linv_eq_id  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x * y = #e) <=> (x = y))
   group_op_rinv_eq_id  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ((x * |/ y = #e) <=> (x = y))
   group_op_linv_eqn    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (( |/ x * y = z) <=> (y = x * z))
   group_op_rinv_eqn    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * |/ y = z) <=> (x = z * y))
   Invertibles_inv      |- !g x. Monoid g /\ x IN G* ==> ((Invertibles g).inv x = |/ x)
   monoid_inv_id        |- !g. Monoid g ==> |/ #e = #e

   Group defintion without explicit mention of Monoid.
   group_def_alt        |- !g. Group g <=>
                            (!x y. x IN G /\ y IN G ==> x * y IN G) /\
                            (!x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z))) /\
                            #e IN G /\
                            (!x. x IN G ==> (#e * x = x)) /\ !x. x IN G ==> ?y. y IN G /\ (y * x = #e)
   group_def_by_inverse |- !g. Group g <=> Monoid g /\ !x. x IN G ==> ?y. y IN G /\ (y * x = #e)
   group_alt            |- !g. Group g <=>
                            (!x y::G. x * y IN G) /\ (!x y z::G. x * y * z = x * (y * z)) /\
                            #e IN G /\ (!x::G. #e * x = x) /\ !x::G. |/ x IN G /\ |/ x * x = #e

   Transformation of Group structure by modifying carrier (for field).
   including_def   |- !g z. including g z = <|carrier := G UNION {z}; op := $*; id := #e|>
   excluding_def   |- !g z. excluding g z = <|carrier := G DIFF {z}; op := $*; id := #e|>
   group_including_property
                   |- !g z. ((g including z).op = $* ) /\ ((g including z).id = #e) /\
                      !x. x IN (g including z).carrier ==> x IN G \/ (x = z)
   group_excluding_property
                   |- !g z. ((g excluding z).op = $* ) /\ ((g excluding z).id = #e) /\
                      !x. x IN (g excluding z).carrier ==> x IN G /\ x <> z
   group_including_excluding_property
                   |- !g z. ((g including z excluding z).op = $* ) /\
                            ((g including z excluding z).id = #e) /\
                            (z NOTIN G ==> ((g including z excluding z).carrier = G))
   group_including_excluding_group
                   |- !g z. z NOTIN G ==> (Group g <=> Group (g including z excluding z))
   group_including_excluding_abelian
                   |- !g z. z NOTIN G ==> (AbelianGroup g <=> AbelianGroup (g including z excluding z))
   group_including_excluding_eqn |- !g z.  g including z excluding z =
                   if z IN G then <|carrier := G DELETE z; op := $*; id := #e|> else g
#  group_excluding_op  |- !g z. (g excluding z).op = $*
   group_excluding_exp |- !g z x n. (g excluding z).exp x n = x ** n
   abelian_monoid_invertible_excluding
                       |- !g. AbelianMonoid g ==>
                          !z. z NOTIN G* ==> (monoid_invertibles (g excluding z) = G* )

   Group Exponentiation with Inverses:
   group_exp_inv   |- !g. Group g ==> !x. x IN G ==> !n. |/ (x ** n) = |/ x ** n
   group_inv_exp   |- !g. Group g ==> !x. x IN G ==> !n. |/ x ** n = |/ (x ** n)
   group_exp_eq    |- !g. Group g ==> !x. x IN G ==> !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n - m) = #e)
   group_exp_mult_comm |- !g. Group g ==> !x. x IN G ==> !m n. (x ** m) ** n = (x ** n) ** m
   group_comm_exp_exp  |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                                          !n m. x ** n * y ** m = y ** m * x ** n

*)

(* ------------------------------------------------------------------------- *)
(* Group Definition.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Set up group type as a record
   A Group has:
   . a carrier set (set = function 'a -> bool, since MEM is a boolean function)
   . an identity element
   . an inverse function (unary operation)
   . a product function called multiplication (binary operation)
*)

(* Monoid and Group share the same type: already defined in monoid.hol
val _ = Hol_datatype`
  group = <| carrier:'a -> bool;
                  id: 'a;
                 inv:'a -> 'a; -- by val _ = add_record_field ("inv", ``monoid_inv``);
                mult:'a -> 'a -> 'a
           |>`;
*)
val _ = type_abbrev ("group", Type `:'a monoid`);

(* Define Group by Monoid

   NOTE:
val _ = overload_on ("G", ``g.carrier``);
val _ = overload_on ("G*", ``monoid_invertibles g``);
 *)
val Group_def = Define`
  Group (g:'a group) <=>
    Monoid g /\ (G* = G)
`;

(* ------------------------------------------------------------------------- *)
(* More Group Defintions.                                                    *)
(* ------------------------------------------------------------------------- *)
(* Abelian Group: a Group with a commutative product: x * y = y * x. *)
val AbelianGroup_def = Define`
  AbelianGroup (g:'a group) <=>
    Group g /\ (!x y. x IN G /\ y IN G ==> (x * y = y * x))
`;

(* Finite Group: a Group with a finite carrier set. *)
val FiniteGroup_def = Define`
  FiniteGroup (g:'a group) <=>
    Group g /\ FINITE G
`;

(* Finite Abelian Group: a Group that is both Finite and Abelian. *)
val FiniteAbelianGroup_def = Define`
  FiniteAbelianGroup (g:'a group) <=>
    AbelianGroup g /\ FINITE G
`;

(* ------------------------------------------------------------------------- *)
(* Basic theorems from definition.                                           *)
(* ------------------------------------------------------------------------- *)

(* Group clauses from definition, internal use *)
val group_clauses = Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> GEN_ALL;
(* > val group_clauses = |- !g. Group g ==> Monoid g /\ (G* = G) *)

(* Theorem: A Group is a Monoid. *)
(* Proof: by definition. *)
val group_is_monoid = save_thm("group_is_monoid",
  Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val group_is_monoid = |- !g. Group g ==> Monoid g : thm *)

val _ = export_rewrites ["group_is_monoid"];

(* Theorem: Group Invertibles is the whole carrier set. *)
(* Proof: by definition. *)
val group_all_invertible = save_thm("group_all_invertible",
  Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val group_all_invertible = |- !g. Group g ==> (G* = G) : thm *)

val _ = export_rewrites ["group_all_invertible"];

(* ------------------------------------------------------------------------ *)
(* Simple Theorems                                                          *)
(* ------------------------------------------------------------------------ *)

(* Theorem: The Invertibles of a monoid form a group. *)
(* Proof: by checking definition. *)
val monoid_invertibles_is_group = store_thm(
  "monoid_invertibles_is_group",
  ``!g. Monoid g ==> Group (Invertibles g)``,
  rw[Group_def, monoid_invertibles_is_monoid] >>
  rw[Invertibles_def, monoid_invertibles_def, EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: FiniteMonoid g ==> FiniteGroup (Invertibles g) *)
(* Proof:
   Note Monoid g /\ FINITE G            by FiniteMonoid_def
   Let s = (Invertibles g).carrier).
   Then s SUBSET G                      by Invertibles_subset
    ==> FINITE s                        by SUBSET_FINITE
   Also Group (Invertibles g)           by monoid_invertibles_is_group
    ==> FiniteGroup (Invertibles g)     by FiniteGroup_def
*)
val finite_monoid_invertibles_is_finite_group = store_thm(
  "finite_monoid_invertibles_is_finite_group",
  ``!g:'a monoid. FiniteMonoid g ==> FiniteGroup (Invertibles g)``,
  metis_tac[monoid_invertibles_is_group, FiniteGroup_def, FiniteMonoid_def,
            Invertibles_subset, SUBSET_FINITE]);

(* Theorem: Finite Abelian Group = Finite Group /\ commutativity. *)
(* Proof: by definitions. *)
val FiniteAbelianGroup_def_alt = store_thm(
  "FiniteAbelianGroup_def_alt",
  ``!g:'a group. FiniteAbelianGroup g <=>
                FiniteGroup g /\ (!x y. x IN G /\ y IN G ==> (x * y = y * x))``,
  rw[FiniteAbelianGroup_def, FiniteGroup_def, AbelianGroup_def, EQ_IMP_THM]);

(* Theorem: FiniteGroup g ==> Group g *)
(* Proof: by FiniteGroup_def *)
val finite_group_is_group = store_thm(
  "finite_group_is_group",
  ``!g:'a group. FiniteGroup g ==> Group g``,
  rw[FiniteGroup_def]);

(* Theorem: FiniteGroup g ==> Monoid g *)
(* Proof: by finite_group_is_group, group_is_monoid *)
val finite_group_is_monoid = store_thm(
  "finite_group_is_monoid",
  ``!g:'a group. FiniteGroup g ==> Monoid g``,
  rw[FiniteGroup_def]);

(* Theorem: For FINITE Group is FINITE monoid. *)
(* Proof: by group_is_monoid. *)
val finite_group_is_finite_monoid = store_thm(
  "finite_group_is_finite_monoid",
  ``!g:'a group. FiniteGroup g ==> FiniteMonoid g``,
  rw[FiniteGroup_def, FiniteMonoid_def, group_is_monoid]);

(* Theorem: AbelianGroup g ==> AbelianMonoid g *)
(* Proof: by AbelianGroup_def, AbelianMonoid_def, group_is_monoid. *)
val abelian_group_is_abelian_monoid = store_thm(
  "abelian_group_is_abelian_monoid[simp]",
  ``!g. AbelianGroup g ==> AbelianMonoid g``,
  rw[AbelianGroup_def, AbelianMonoid_def]);

(* Theorem: FiniteAbelianGroup g ==> FiniteAbelianMonoid g *)
(* Proof: by FiniteAbelianGroup_def, FiniteAbelianMonoid_def, abelian_group_is_abelian_monoid. *)
val finite_abelian_group_is_finite_abelian_monoid = store_thm(
  "finite_abelian_group_is_finite_abelian_monoid",
  ``!g. FiniteAbelianGroup g ==> FiniteAbelianMonoid g``,
  rw_tac std_ss[FiniteAbelianGroup_def, FiniteAbelianMonoid_def, abelian_group_is_abelian_monoid]);

(* ------------------------------------------------------------------------- *)
(* Group theorems (from Monoid).                                             *)
(* ------------------------------------------------------------------------- *)

(* Do Theorem Lifting, but no need to export. *)

(* Manual Lifting:

- show_assums := true;
> val it = () : unit

- monoid_id_element;
> val it =  [] |- !g. Monoid g ==> #e IN G : thm
- monoid_id_element |> SPEC_ALL |> UNDISCH;
> val it =  [Monoid g] |- #e IN G : thm
- monoid_id_element |> SPEC_ALL |> UNDISCH |> PROVE_HYP (group_is_monoid |> SPEC_ALL |> UNDISCH);
> val it =  [Group g] |- #e IN G : thm
- monoid_id_element |> SPEC_ALL |> UNDISCH |> PROVE_HYP (group_is_monoid |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !g. Group g ==> #e IN G : thm

or
- group_is_monoid;
> val it =  [] |- !g. Group g ==> Monoid g : thm
- group_is_monoid |> SPEC_ALL |> UNDISCH;
> val it =  [Group g] |- Monoid g : thm
- group_is_monoid |> SPEC_ALL |> UNDISCH |> MP (monoid_id_element |> SPEC_ALL);
> val it =  [Group g] |- #e IN G : thm
- group_is_monoid |> SPEC_ALL |> UNDISCH |> MP (monoid_id_element |> SPEC_ALL) |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !g. Group g ==> #e IN G : thm

- show_assums := false;
> val it = () : unit
*)

(* Lifting Monoid theorem for Group.
   from: !g:'a monoid. Monoid g ==> ....
     to: !g:'a group.  Group g ==> ....
    via: !g:'a group.  Group g ==> Monoid g
*)
local
val gim = group_is_monoid |> SPEC_ALL |> UNDISCH
in
fun lift_monoid_thm suffix = let
   val mth = DB.fetch "monoid" ("monoid_" ^ suffix)
   val mth' = mth |> SPEC_ALL
in
   save_thm("group_" ^ suffix, gim |> MP mth' |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: Group identity is an element. *)
val group_id_element = lift_monoid_thm "id_element";
(* > val group_id_element = |- !g. Group g ==> #e IN G : thm *)

(* Theorem: [Group closure] Group product is an element. *)
val group_op_element = lift_monoid_thm "op_element";
(* > val group_op_element = |- !g. Group g ==> !x y. x IN G /\ y IN G ==> x * y IN G : thm *)

(* Theorem: [Group associativity] (x * y) * z = x * (y * z) *)
val group_assoc = lift_monoid_thm "assoc";
(* > val group_assoc = |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z)) : thm *)

(* Theorem: [Group left identity] #e * x = x *)
val group_lid = lift_monoid_thm "lid";
(* > val group_lid = |- !g. Group g ==> !x. x IN G ==> (#e * x = x) : thm *)

(* Theorem: [Group right identity] x * #e = x *)
val group_rid = lift_monoid_thm "rid";
(* > val group_rid = |- !g. Group g ==> !x. x IN G ==> (x * #e = x) : thm *)

(* Theorem: [Group identities] #e * x = x /\ x * #e = x *)
val group_id = lift_monoid_thm "id";
(* > val group_id = |- !g. Group g ==> !x. x IN G ==> (#e * x = x) /\ (x * #e = x) : thm *)

(* Theorem: #e * #e = #e *)
val group_id_id = lift_monoid_thm "id_id";
(* > val group_id_id = |- !g. Group g ==> (#e * #e = #e) : thm *)

(* Theorem: (x ** n) in G *)
val group_exp_element = lift_monoid_thm "exp_element";
(* > val group_exp_element = |- !g. Group g ==> !x. x IN G ==> !n. x ** n IN G : thm *)

(* Theorem: x ** SUC n = x * x ** n *)
val group_exp_SUC = save_thm("group_exp_SUC", monoid_exp_SUC);
(* > val group_exp_SUC = |- !g x. x ** SUC n = x * x ** n : thm *)

(* Theorem: x ** SUC n = x ** n * x *)
val group_exp_suc = lift_monoid_thm "exp_suc";
(* val group_exp_suc = |- !g. Group g ==> !x. x IN G ==> !n. x ** SUC n = x ** n * x : thm *)

(* Theorem: x ** 0 = #e *)
val group_exp_0 = save_thm("group_exp_0", monoid_exp_0);
(* > val group_exp_0 = |- !g x. x ** 0 = #e : thm *)

(* Theorem: x ** 1 = x *)
val group_exp_1 = lift_monoid_thm "exp_1";
(* > val group_exp_1 = |- !g. Group g ==> !x. x IN G ==> (x ** 1 = x) : thm *)

(* Theorem: (#e ** n) = #e  *)
val group_id_exp = lift_monoid_thm "id_exp";
(* > val group_id_exp = |- !g. Group g ==> !n. #e ** n = #e : thm *)

(* Theorem: For abelian group g,  (x ** n) * y = y * (x ** n) *)
val group_comm_exp = lift_monoid_thm "comm_exp";
(* > val group_comm_exp = |- !g. Group g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) ==> !n. x ** n * y = y * x ** n : thm *)

(* Theorem: (x ** n) * x = x * (x ** n) *)
val group_exp_comm = lift_monoid_thm "exp_comm";
(* > val group_exp_comm = |- !g. Group g ==> !x. x IN G ==> !n. x ** n * x = x * x ** n : thm *)

(* Theorem: For abelian group, (x * y) ** n = (x ** n) * (y ** n) *)
val group_comm_op_exp = lift_monoid_thm "comm_op_exp";
(* > val group_comm_op_exp = |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n. (x * y) ** n = x ** n * y ** n : thm *)

(* Theorem: x ** (m + n) = (x ** m) * (x ** n) *)
val group_exp_add = lift_monoid_thm "exp_add";
(* > val group_exp_add = |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n + k) = x ** n * x ** k : thm *)

(* Theorem: x ** (m * n) = (x ** m) ** n  *)
val group_exp_mult = lift_monoid_thm "exp_mult";
(* > val group_exp_mult = |- !g. Group g ==> !x. x IN G ==> !n k. x ** (n * k) = (x ** n) ** k : thm *)

(* ------------------------------------------------------------------------- *)
(* Group theorems (from Monoid invertibles).                                 *)
(* ------------------------------------------------------------------------- *)

(* val _ = overload_on("|/", ``monoid_inv g``); *)
(* val _ = overload_on("|/", ``reciprocal``); *)

(* Theorem: [Group inverse element] |/ x IN G *)
(* Proof: by Group_def and monoid_inv_def. *)
Theorem group_inv_element[simp]:
  !g:'a group. Group g ==> !x. x IN G ==> |/x IN G
Proof rw[monoid_inv_def]
QED

val gim = Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT1;
val ginv = Group_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2;

(* Theorem: [Group left inverse] |/ x * x = #e *)
(* Proof: by Group_def and monoid_inv_def. *)
Theorem group_linv[simp] =
  monoid_inv_def |> SPEC_ALL |> REWRITE_RULE [gim, ginv] |> SPEC_ALL |> UNDISCH_ALL
                 |> CONJUNCT2 |> CONJUNCT2 |> DISCH ``x IN G`` |> GEN ``x`` |> DISCH ``Group g`` |> GEN_ALL
(* > val group_linv = |- !g. Group g ==> !x. x IN G ==> ( |/ x * x = #e) : thm *)

(* Theorem: [Group right inverse] x * |/ x = #e *)
(* Proof: by Group_def and monoid_inv_def. *)
val group_rinv = save_thm("group_rinv",
  monoid_inv_def |> SPEC_ALL |> REWRITE_RULE [gim, ginv] |> SPEC_ALL |> UNDISCH_ALL
                 |> CONJUNCT2 |> CONJUNCT1 |> DISCH ``x IN G`` |> GEN ``x`` |> DISCH ``Group g`` |> GEN_ALL);
(* > val group_rinv = |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e) : thm *)

(* Maybe good to export ? *)
val _ = export_rewrites ["group_inv_element", "group_linv", "group_rinv"];

(* Theorem: [Group inverses] x * |/ x = #e /\ |/x * x = #e *)
val group_inv_thm = save_thm("group_inv_thm",
  monoid_inv_def |> SPEC_ALL |> REWRITE_RULE [gim, ginv] |> SPEC_ALL |> UNDISCH_ALL
                 |> CONJUNCT2 |> DISCH ``x IN G`` |> GEN ``x`` |> DISCH ``Group g`` |> GEN_ALL);
(* > val group_inv_thm = |- !g. Group g ==> !x. x IN G ==> (x * |/ x = #e) /\ ( |/ x * x = #e) : thm *)

(* Theorem: [Group carrier nonempty] G <> {} *)
val group_carrier_nonempty = lift_monoid_thm "carrier_nonempty";
(* > val group_carrier_nonempty = |- !g. Group g ==> G <> {} : thm *)

(* ------------------------------------------------------------------------- *)
(* Group Theorems (not from Monoid).                                         *)
(* ------------------------------------------------------------------------- *)

(* Just an exercise to show that right inverse can be deduced from left inverse for Group. *)

(* Theorem: [Group right inverse] x * |/ x = #e *)
(* Proof:
     x * |/ x
   = #e  * (x * |/ x)                   by left identity: #e * X = X, where X = (x * |/ x)
   = (#e * x) * |/ x                    by associativity
   = ( |/ ( |/ x) * |/ x) * x) * |/ x   by left inverse: #e = |/ Y * Y, where Y = |/ x
   = ( |/ ( |/ x) * ( |/ x * x)) * |/ x by associativity
   = ( |/ ( |/ x) * #e) * |/ x          by left inverse: |/ Y * Y = #e, where Y = |/ x
   = |/ ( |/ x) * (#e * |/ x)           by associativity
   = |/ ( |/ x) * ( |/ x)               by left identity: #e * Y = Y, where Y = |/ x
   = #e                                 by left inverse: |/ Y * Y = #e, where Y = |/ x
*)

(* Just an exercise to show that right identity can be deduced from left identity for Group. *)

(* Theorem: [Group right identity] x * #e = x *)
(* Proof:
     x * #e
   = x * ( |/ x * x)    by left inverse: |/ Y * Y = #e, where Y = x
   = (x * |/ x) * x     by associativity
   = #e * x             by right inverse: Y * |/ Y = #e, where Y = x
   = x                  by left identity: #e * Y = Y, where Y = x
*)

(* Theorem: [Left cancellation] x * y = x * z <=> y = z *)
(* Proof:
   (wrong proof: note the <=>)
               x * y = x * z
   <=> |/x * (x * y) = |/x * (x * z)    this asssume left-cancellation!
   <=> ( |/x * x) * y = ( |/x * x) * z  by group_assoc
   <=>        #e * y = #e * z           by group_linv
   <=>             y = z                by group_lid
   (correct proof: note the ==>)
   If part: x * y = x * z ==> y = z
               x * y = x * z
   ==> |/x * (x * y) = |/x * (x * z)    by group_inv_element
   ==> ( |/x * x) * y = ( |/x * x) * z  by group_assoc
   ==>        #e * y = #e * z           by group_linv
   ==>             y = z                by group_lid
   Only-if part: true by substitution.
*)
val group_lcancel = store_thm(
  "group_lcancel",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = x * z) = (y = z))``,
  rw[EQ_IMP_THM] >>
  `( |/x * x) * y = ( |/x * x) * z` by rw[group_assoc] >>
  metis_tac[group_linv, group_lid]);

(* Theorem: [Right cancellation] y * x = z * x <=> y = z *)
(* Proof:
   If part: y * x = z * x ==> y = z
       y * x = z * x
   ==> y * x * |/x = z * x * |/x      by group_inv_element
   ==> y * (x * |/x) = z * (x * |/x)  by group_assoc
   ==>         y * #e = z * #e        by group_rinv
   ==>              y = z             by group_rid
   Only-if part: true by substitution.
*)
val group_rcancel = store_thm(
  "group_rcancel",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((y * x = z * x) = (y = z))``,
  rw[EQ_IMP_THM] >>
  `y * (x * |/x) = z * (x * |/x)` by rw[GSYM group_assoc] >>
  metis_tac[group_rinv, group_rid]);

(* ------------------------------------------------------------------------- *)
(* Inverses with assocative law.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: y = x * ( |/ x * y) /\ y = |/x * (x * y) *)
(* Proof: by group_assoc and group_linv or group_rinv. *)
val group_linv_assoc = store_thm(
  "group_linv_assoc",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (y = x * ( |/ x * y)) /\ (y = |/x * (x * y))``,
  rw[GSYM group_assoc]);

(* Theorem: y = y * |/ x * x /\ y = y * x * |/x *)
(* Proof: by group_assoc and group_linv or group_rinv. *)
val group_rinv_assoc = store_thm(
  "group_rinv_assoc",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (y = y * |/ x * x) /\ (y = y * x * |/x)``,
  rw[group_assoc]);

(* Theorem: [Solve left unknown] x * y = z <=> x = z * |/y *)
(* Proof:
   If part: x * y = z ==> x = z * |/y
     z * |/y
   = (x * y) * |/y   by substituting z
   = x               by group_rinv_assoc
   Only-if part: x = z * |/y ==> x * y = z
     x * y
   = (z * |/y) * y   by substituting x
   = z               by group_rinv_assoc
*)
val group_lsolve = store_thm(
  "group_lsolve",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) = (x = z * |/y))``,
  rw[group_rinv_assoc, EQ_IMP_THM]);

(* Theorem: [Solve left unknown] x * y = z <=> x = z * |/y *)
(* Another proof:
   If part: x * y = z ==> x = z * |/y
     x * y = z
           = z * #e           by group_rid
           = z * ( |/y * y)   by group_linv
           = (z * |/y) * y    by group_assc
     hence x = z * |/y        by group_rcancel
   Only-if part: x = z * |/y ==> x * y = z
     x * y = (z * |/y) * y    by substituting x
           = z * ( |/y * y)   by group_assoc
           = z * #e           by group_linv
           = z                by group_rid
*)
(* still, the first proof is easier. *)

(* Theorem: [Solve right unknown] x * y = z <=> y = |/x * z *)
(* Proof:
   If part: x * y = z ==> y = |/x * z
      |/x * z
    = |/x * (x * y)    by substituting z
    = y                by group_linv_assoc
   Only-if part: y = |/x * z ==> x * y = z
      x * y
    = x ( |/x * z)     by substituting y
    = z                by group_linv_assoc
*)
val group_rsolve = store_thm(
  "group_rsolve",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y = z) = (y = |/x * z))``,
  rw[group_linv_assoc, EQ_IMP_THM]);

(* Theorem: [Left identity unique] y * x = x <=> y = #e *)
(* Proof:
       y * x = x
   <=> y = x * |/x   by group_lsolve
         = #e        by group_rinv
   Another proof:
       y * x = x = #e * x    by group_lid
           y = #e            by group_rcancel
*)
val group_lid_unique = store_thm(
  "group_lid_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) = (y = #e))``,
  rw[group_lsolve]);

(* Theorem: [Right identity unique] x * y = x <=> y = #e *)
(* Proof:
       x * y = x
   <=> y = |/x * x    by group_rsolve
         = #e         by group_linv
*)
val group_rid_unique = store_thm(
  "group_rid_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = x) = (y = #e))``,
  rw[group_rsolve]);

(* Theorem: Group identity is unique. *)
(* Proof: from group_ild_unique and group_rid_unique. *)
val group_id_unique = store_thm(
  "group_id_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((y * x = x) = (y = #e)) /\ ((x * y = x) = (y = #e))``,
  rw[group_lid_unique, group_rid_unique]);

(* Note: These are stronger claims than monoid_id_unique. *)

(* Theorem: [Left inverse unique] x * y = #e <=> x = |/y *)
(* Proof:
       x * y = #e
   <=> x = #e * |/y    by group_lsolve
         = |/ y        by group_lid
*)
val group_linv_unique = store_thm(
  "group_linv_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) = (x = |/y))``,
  rw[group_lsolve]);

(* Theorem: [Right inverse unique] x * y = #e <=> y = |/x *)
(* Proof:
       x * y = #e
   <=> y = |/x * #e    by group_rsolve
         = |/x         by group_rid
*)
val group_rinv_unique = store_thm(
  "group_rinv_unique",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * y = #e) = (y = |/x))``,
  rw[group_rsolve]);

(* Theorem: [Inverse of inverse] |/( |/ x) = x *)
(* Proof:
       x * |/x = #e      by group_rinv
   <=> x = |/x ( |/x)    by group_linv_unique
*)
val group_inv_inv = store_thm(
  "group_inv_inv",
  ``!g:'a group. Group g ==> !x. x IN G ==> ( |/( |/x) = x)``,
  metis_tac[group_rinv, group_linv_unique, group_inv_element]);

val _ = export_rewrites ["group_inv_inv"];

(* Theorem: [Inverse equal] |/x = |/y <=> x = y *)
(* Proof:
   Only-if part is trivial.
   For the if part: |/x = |/y ==> x = y
            |/x = |/y
   ==> |/( |/x) = |/( |/y)
   ==>        x = y         by group_inv_inv
*)
val group_inv_eq = store_thm(
  "group_inv_eq",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (( |/x = |/y) = (x = y))``,
  metis_tac[group_inv_inv]);

val _ = export_rewrites ["group_inv_eq"];

(* Theorem: [Inverse equality swap]: |/x = y <=> x = |/y *)
(* Proof:
            |/x = y
   <=> |/( |/x) = |/y
   <=>        x = |/y    by group_inv_inv
*)
val group_inv_eq_swap = store_thm(
  "group_inv_eq_swap",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (( |/x = y) = (x = |/y))``,
  metis_tac[group_inv_inv]);

val _ = export_rewrites ["group_inv_eq_swap"];

(* Theorem: [Inverse of identity] |/#e = #e *)
(* Proof:
       #e * #e = #e    by group_id_id
   <=>      #e = |/#e  by group_linv_unique
*)
val group_inv_id = store_thm(
  "group_inv_id",
  ``!g:'a group. Group g ==> ( |/ #e = #e)``,
  metis_tac[group_lid, group_linv_unique, group_id_element]);

val _ = export_rewrites ["group_inv_id"];

(* Theorem: [Inverse equal identity] |/x = #e <=> x = #e *)
(* Proof:
      |/x = #e = |/#e    by group_inv_id
   <=>  x = #e           by group_inv_eq
*)
val group_inv_eq_id = store_thm(
  "group_inv_eq_id",
  ``!g:'a group. Group g ==> !x. x IN G ==> (( |/x = #e) = (x = #e))``,
  rw[]);

(* Theorem: [Inverse of product] |/(x * y) = |/y * |/x *)
(* Proof:
   First show this product:
     (x * y) * ( |/y * |/x)
   = ((x * y) * |/y) * |/x     by group_assoc
   = (x * (y * |/y)) * |/x     by group_assoc
   = (x * #e) * |/x            by group_rinv
   = x * |/x                   by group_rid
   = #e                        by group_rinv
   Hence |/(x y) = |/y * |/x   by group_rinv_unique.
*)
val group_inv_op = store_thm(
  "group_inv_op",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ( |/(x * y) = |/y * |/x)``,
  rpt strip_tac >>
  `(x * y) * ( |/y * |/x) = x * (y * |/y) * |/x` by rw[group_assoc] >>
  `_ = #e` by rw_tac std_ss[group_rinv, group_rid] >>
  pop_assum mp_tac >>
  rw[group_rinv_unique]);

(* Theorem: [Pair Reduction] Group g ==> (x * z) * |/ (y * z) = x * |/ y *)
(* Proof:
     (x * z) * |/ (y * z)
   = (x * z) * ( |/ z * |/ y)   by group_inv_op
   = ((x * z) * |/ z) * |/ y    by group_assoc
   = (x * (z * |/ z)) * |/ y    by group_assoc
   = (x * #e) * |/ y            by group_rinv
   = x * |/ y                   by group_rid
*)
val group_pair_reduce = store_thm(
  "group_pair_reduce",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * z) * |/ (y * z) = x * |/ y)``,
  rpt strip_tac >>
  `!a. a IN G ==> |/ a IN G` by rw[] >>
  `(x * z) * |/ (y * z) = (x * z) * ( |/ z * |/ y)` by rw_tac std_ss[group_inv_op] >>
  `_ = (x * (z * |/ z)) * |/ y` by rw[group_assoc] >>
  `_ = (x * #e) * |/ y` by rw_tac std_ss[group_rinv] >>
  `_ = x * |/ y` by rw_tac std_ss[group_rid] >>
  metis_tac[]);

(* Theorem: The identity is a fixed point: x * x = x ==> x = #e. *)
(* Proof:
   For the if part:
       x * x = x
   ==> x * x = #e * x     by group_lid
   ==> x = #e             by group_rcancel
   For the only-if part:
       #e * #e = #e       by group_id_id
*)
val group_id_fix = store_thm(
  "group_id_fix",
  ``!g:'a group. Group g ==> !x. x IN G ==> ((x * x = x) = (x = #e))``,
  metis_tac[group_lid, group_rcancel, group_id_element]);

(* Theorem: Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x * y = #e) <=> (x = y)) *)
(* Proof:
   If part: |/ x * y = #e ==> x = y
   Note |/ x IN G                by group_inv_element
   Given  |/ x * y = #e
                 y = |/ ( |/ x)  by group_rinv_unique
                   = x           by group_inv_inv

   Only-if part: x = y ==> |/ x * y = #e
       True by group_linv.
*)
val group_op_linv_eq_id = store_thm(
  "group_op_linv_eq_id",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> (( |/ x * y = #e) <=> (x = y))``,
  rw[EQ_IMP_THM] >>
  metis_tac[group_inv_element, group_rinv_unique, group_inv_inv]);

(* Theorem: Group g ==> !x y. x IN G /\ y IN G ==> ((x * |/ y = #e) <=> (x = y)) *)
(* Proof:
   If part: x * |/ y = #e ==> x = y
   Note |/ x IN G                by group_inv_element
   Given  x * |/ y = #e
                 x = |/ ( |/ y)  by group_linv_unique
                   = y           by group_inv_inv

   Only-if part: x = y ==> x * |/ y = #e
       True by group_rinv.
*)
val group_op_rinv_eq_id = store_thm(
  "group_op_rinv_eq_id",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> ((x * |/ y = #e) <=> (x = y))``,
  rw[EQ_IMP_THM] >>
  metis_tac[group_inv_element, group_linv_unique, group_inv_inv]);

(* Theorem: Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (( |/ x * y = z) <=> (y = x * z)) *)
(* Proof:
   Note |/ x IN G                     by group_inv_element
                |/ x * y = z
   <=> x * (( |/ x) * y) = x * z      by group_lcancel
   <=>    (x * |/ x) * y = x * z      by group_assoc
   <=>            #e * y = x * z      by group_rinv
   <=>                 y = x * z      by group_lid
*)
val group_op_linv_eqn = store_thm(
  "group_op_linv_eqn",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (( |/ x * y = z) <=> (y = x * z))``,
  rpt strip_tac >>
  `|/ x IN G` by rw[] >>
  `( |/ x * y = z) <=> (x * ( |/ x * y) = x * z)` by rw[group_lcancel] >>
  `_ = ((x * |/ x) * y = x * z)` by rw[group_assoc] >>
  `_ = (y = x * z)` by rw[] >>
  rw[]);

(* Theorem: Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * |/ y = z) <=> (x = z * y)) *)
(* Proof:
   Note |/ y IN G                     by group_inv_element
                x * |/ y = z
   <=>    (x * |/ y) * y = z * y      by group_rcancel
   <=>   x * ( |/ y * y) = z * y      by group_assoc
   <=>           x * #e  = z * y      by group_linv
   <=>                 x = z * y      by group_rid
*)
val group_op_rinv_eqn = store_thm(
  "group_op_rinv_eqn",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * |/ y = z) <=> (x = z * y))``,
  rpt strip_tac >>
  `|/ y IN G` by rw[] >>
  `(x * |/ y = z) <=> ((x * |/ y) * y = z * y)` by rw[group_rcancel] >>
  `_ = (x * ( |/ y * y) = z * y)` by rw[group_assoc] >>
  `_ = (x = z * y)` by rw[] >>
  rw[]);

(* Theorem: Monoid g /\ x IN G* ==> ((Invertibles g).inv x = |/ x) *)
(* Proof:
   Note Group (Invertibles g)             by monoid_invertibles_is_group
    and (Invertibles g).op = g.op         by Invertibles_property
    and (Invertibles g).id = #e           by Invertibles_property
    and (Invertibles g).carrier = G*      by Invertibles_carrier
    Now ( |/ x) IN G*                     by monoid_inv_invertible
    and x * ( |/ x) = #e                  by monoid_inv_def
    ==> |/ x = (Invertibles g).inv x      by group_rinv_unique
*)
val Invertibles_inv = store_thm(
  "Invertibles_inv",
  ``!(g:'a monoid) x. Monoid g /\ x IN G* ==> ((Invertibles g).inv x = |/ x)``,
  rpt strip_tac >>
  `Group (Invertibles g)` by rw[monoid_invertibles_is_group] >>
  `(Invertibles g).carrier = G*` by rw[Invertibles_carrier] >>
  `( |/ x) IN G*` by rw[monoid_inv_invertible] >>
  `x * ( |/ x) = #e` by rw[monoid_inv_def] >>
  metis_tac[group_rinv_unique, Invertibles_property]);

(* Theorem: Monoid g ==> ( |/ #e = #e) *)
(* Proof:
   Note Group (Invertibles g)   by monoid_invertibles_is_group
    and #e IN G*                by monoid_id_invertible
   Thus |/ #e
      = (Invertibles g).inv #e                 by Invertibles_inv
      = (Invertibles g).inv (Invertibles g).id by Invertibles_property
      = (Invertibles g).id                     by group_inv_id
      = #e                                     by by Invertibles_property
*)
val monoid_inv_id = store_thm(
  "monoid_inv_id",
  ``!g:'a monoid. Monoid g ==> ( |/ #e = #e)``,
  rpt strip_tac >>
  `Group (Invertibles g)` by rw[monoid_invertibles_is_group] >>
  `(Invertibles g).id = #e` by rw[Invertibles_property] >>
  `#e IN G*` by rw[monoid_id_invertible] >>
  metis_tac[group_inv_id, Invertibles_inv]);

(* ------------------------------------------------------------------------- *)
(* Group Defintion without explicit mention of Monoid.                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Alternative Definition]
      Group g <=> #e IN G /\
               (!x y::(G). x * y IN G) /\
               (!x::(G). |/x IN G) /\
               (!x::(G). #e * x = x) /\
               (!x::(G). |/x * x = #e) /\
               (!x y z::(G). (x * y) * z = x * (y * z)) *)
(* Proof:
   Monoid needs the right identity:
     x * #e
   = (#e * x) * #e      by #e * x = x          left_identity
   = (x''x')x(x'x)      by #e = x' x = x'' x'  left_inverse
   = x''(x'x)(x'x)      by associativity
   = x''(x'x)           by #e * (x'x) = x'x    left_identity
   = (x''x')x           by associativity
   = #e * x             by #e = x''x'          left_inverse
   = x                  by #e * x = x          left_identity
   monoid_invertibles need right inverse:
     x * x'
   = (#e * x) * x'      by #e * x = x          left_identity
   = (x'' x')* x * x'   by #e = x''x'          left_inverse
   = x'' (x' x) x'      by associativity
   = x'' x'             by #e = x'x            left_inverse
   = #e                 by #e = x''x'          left_inverse
*)
val group_def_alt = store_thm(
  "group_def_alt",
  ``!g:'a group. Group g <=>
        (!x y. x IN G /\ y IN G ==> x * y IN G) /\
        (!x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y) * z = x * (y * z))) /\
         #e IN G /\
        (!x. x IN G ==> (#e * x = x)) /\
        (!x. x IN G ==> ?y. y IN G /\ (y * x = #e))``,
  rw[group_assoc, EQ_IMP_THM] >-
  metis_tac[group_linv, group_inv_element] >>
  rw_tac std_ss[Group_def, Monoid_def, monoid_invertibles_def, EXTENSION, EQ_IMP_THM, GSPECIFICATION] >| [
    `?y. y IN G /\ (y * x = #e)` by metis_tac[] >>
    `?z. z IN G /\ (z * y = #e)` by metis_tac[] >>
    `z * y * x = z * (y * x)` by rw_tac std_ss[],
    `?y. y IN G /\ (y * x = #e)` by metis_tac[] >>
    `?z. z IN G /\ (z * y = #e)` by metis_tac[] >>
    `z * y * x = z * (y * x)` by rw_tac std_ss[] >>
    `z * #e * y = z * (#e * y)` by rw_tac std_ss[]
  ] >> metis_tac[]);

(* Theorem: Group g <=> Monoid g /\ (!x. x IN G ==> ?y. y IN G /\ (y * x = #e)) *)
(* Proof:
   By Group_def and EXTENSION this is to show:
   (1) G* = G /\ x IN G ==> ?y. y IN G /\ (y * x = #e)
       Note x IN G ==> x IN G*          by G* = G
        ==> ?y. y IN G /\ (y * x = #e)  by monoid_invertibles_element
   (2) x IN G* ==> x IN G
       Note x IN G* ==> x IN G          by monoid_invertibles_element
   (3) (!x. x IN G ==> ?y. y IN G /\ (g.op y x = #e)) /\ x IN G ==> x IN G*
       Note ?y. y IN G /\ (y * x = #e)  by x IN G
         so ?z. z IN G /\ (z * y = #e)  by y IN G
            x
          = #e * x                      by monoid_lid
          = (z * y) * x                 by #e = z * y
          = z * (y * x)                 by monoid_assoc
          = z * #e                      by #e = y * x
          = z                           by monoid_rid
       Thus ?y. y * x = #e  /\ x * y = #e
         or x IN G*                     by monoid_invertibles_element
*)
val group_def_by_inverse = store_thm(
  "group_def_by_inverse",
  ``!g:'a group. Group g <=> Monoid g /\ (!x. x IN G ==> ?y. y IN G /\ (y * x = #e))``,
  rw_tac std_ss[Group_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[monoid_invertibles_element] >-
  metis_tac[monoid_invertibles_element] >>
  `?y. y IN G /\ (y * x = #e)` by rw[] >>
  `?z. z IN G /\ (z * y = #e)` by rw[] >>
  `z * y * x = z * (y * x)` by rw_tac std_ss[monoid_assoc] >>
  `x = z` by metis_tac[monoid_lid, monoid_rid] >>
  metis_tac[monoid_invertibles_element]);

(* Alternative concise definition of a group. *)

(* Theorem: Group g <=>
            (!x y::G. x * y IN G) /\
            (!x y z::G. x * y * z = x * (y * z)) /\
             #e IN G /\ (!x::G. #e * x = x) /\
             !x::G. |/ x IN G /\ |/ x * x = #e *)
(* Proof: by group_def_alt, group_inv_element. *)
Theorem group_alt:
  !(g:'a group). Group g <=>
          (!x y::G. x * y IN G) /\ (* closure *)
          (!x y z::G. x * y * z = x * (y * z)) /\ (* associativity *)
          #e IN G /\ (!x::G. #e * x = x) /\ (* identity *)
          !x::G. |/ x IN G /\ |/ x * x = #e
Proof
  rw[group_def_alt, group_inv_element, EQ_IMP_THM] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Transformation of Group structure by modifying carrier.                   *)
(* Useful for Field and Field Instances, include or exclude zero.            *)
(* ------------------------------------------------------------------------- *)

(* Include an element z (zero) for the carrier, usually putting group to monoid. *)
val including_def = zDefine`
   including (g:'a group) (z:'a) :'a monoid =
      <| carrier := G UNION {z};
              op := g.op;
              id := g.id
       |>
`;
val _ = set_fixity "including" (Infixl 600); (* like division / *)
(* > val including_def = |- !g z. including g z = <|carrier := G UNION {z}; op := $*; id := #e|> : thm *)

(* Exclude an element z (zero) from the carrier, usually putting monoid to group. *)
val excluding_def = zDefine`
   excluding (g:'a monoid) (z:'a) :'a group =
      <| carrier := G DIFF {z};
              op := g.op;
              id := g.id
       |>
`;
val _ = set_fixity "excluding" (Infixl 600); (* like division / *)
(* > val excluding_def = |- !g z. excluding g z = <|carrier := G DIFF {z}; op := $*; id := #e|> : thm *)
(*
- type_of ``g including z``;
> val it = ``:'a group`` : hol_type
- type_of ``g excluding z``;
> val it = ``:'a group`` : hol_type
*)

(* Theorem: (g including z).op = g.op /\ (g including z).id = g.id /\
            !x. x IN (g including z).carrier = x IN G \/ (x = z) *)
(* Proof: by IN_UNION, IN_SING. *)
val group_including_property = store_thm(
  "group_including_property",
  ``!g:'a group. !z:'a. ((g including z).op = g.op) /\
                        ((g including z).id = g.id) /\
                        (!x. x IN (g including z).carrier ==> x IN G \/ (x = z))``,
  rw[including_def]);

(* Theorem: (g excluding z).op = g.op /\ (g excluding z).id = g.id /\
            !x. x IN (g excluding z).carrier = x IN G /\ (x <> z) *)
(* Proof: by IN_DIFF, IN_SING. *)
val group_excluding_property = store_thm(
  "group_excluding_property",
  ``!g:'a group. !z:'a. ((g excluding z).op = g.op) /\
                        ((g excluding z).id = g.id) /\
                        (!x. x IN (g excluding z).carrier ==> x IN G /\ (x <> z))``,
  rw[excluding_def]);

(* Theorem: ((g including z) excluding z).op = g.op /\ ((g including z) excluding z).id = g.id /\
            If z NOTIN G, then ((g including z) excluding z).carrier = G. *)
(* Proof:
   If z NOTIN G,
   then G UNION {z} DIFF {z} = G    by IN_UNION, IN_DIFF, IN_SING.
*)
val group_including_excluding_property = store_thm(
  "group_including_excluding_property",
  ``!g:'a group. !z:'a. (((g including z) excluding z).op = g.op) /\
                        (((g including z) excluding z).id = g.id) /\
                        (z NOTIN G ==> (((g including z) excluding z).carrier = G))``,
  rw_tac std_ss[including_def, excluding_def] >>
  rw[EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: If z NOTIN G, then Group g = Group ((g including z) excluding z). *)
(* Proof: by group_including_excluding_property. *)
val group_including_excluding_group = store_thm(
  "group_including_excluding_group",
  ``!g:'a group. !z:'a. z NOTIN G ==> (Group g = Group ((g including z) excluding z))``,
  rw_tac std_ss[group_def_alt, group_including_excluding_property]);

(* Theorem: If z NOTIN G, then AbelianGroup g = AbelianGroup ((g including z) excluding z). *)
(* Proof: by group_including_excluding_property. *)
val group_including_excluding_abelian = store_thm(
  "group_including_excluding_abelian",
  ``!g:'a group. !z:'a. z NOTIN G ==> (AbelianGroup g = AbelianGroup ((g including z) excluding z))``,
  rw_tac std_ss[AbelianGroup_def, group_def_alt, group_including_excluding_property]);

(* Theorem: g including z excluding z explicit expression. *)
(* Proof: by definition. *)
val group_including_excluding_eqn = store_thm(
  "group_including_excluding_eqn",
  ``!g:'a group. !z:'a. g including z excluding z = if z IN G then <| carrier := G DELETE z; op := g.op; id := g.id |> else g``,
  rw[including_def, excluding_def] >| [
    rw[EXTENSION] >>
    metis_tac[],
    rw[monoid_component_equality] >>
    rw[EXTENSION] >>
    metis_tac[]
  ]);
(* better -- Michael's solution *)
Theorem group_including_excluding_eqn[allow_rebind]:
  !g:'a group. !z:'a. g including z excluding z =
                      if z IN G then <| carrier := G DELETE z;
                                        op := g.op;
                                        id := g.id |>
                      else g
Proof
  rw[including_def, excluding_def] >>
  rw[monoid_component_equality] >>
  rw[EXTENSION] >> metis_tac[]
QED

(* Theorem: (g excluding z).op = g.op *)
(* Proof: by definition. *)
val group_excluding_op = store_thm(
  "group_excluding_op",
  ``!g:'a group. !z:'a. (g excluding z).op = g.op``,
  rw_tac std_ss[excluding_def]);

val _ = export_rewrites ["group_excluding_op"];
val _ = computeLib.add_persistent_funs ["group_excluding_op"];

(* Theorem: (g excluding z).exp x n = x ** n *)
(* Proof:
   By induction on n.
   Base: (g excluding z).exp x 0 = x ** 0
           (g excluding z).exp x 0
         = (g excluding z).id            by group_exp_0
         = #e                            by group_excluding_property
         = x ** 0                        by group_exp_0
   Step: (g excluding z).exp x n = x ** n ==> (g excluding z).exp x (SUC n) = x ** SUC n
         (g excluding z).exp x (SUC n)
       = (g excluding z).op x (g excluding z).exp x n   by group_exp_SUC
       = (g excluding z).op x (x ** n)                  by induction hypothesis
       = x * (x ** n)                                   by group_excluding_property
       = x ** SUC n                                     by group_exp_SUC
*)
val group_excluding_exp = store_thm(
  "group_excluding_exp",
  ``!(g:'a group) z x n. (g excluding z).exp x n = x ** n``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[group_excluding_property]);

(* Theorem: AbelianMonoid g ==>
           !z. z NOTIN G* ==> (monoid_invertibles (g excluding z) = G* ) *)
(* Proof:
   By monoid_invertibles_def, excluding_def, EXTENSION, this is to show:
   (1) x IN G /\ y IN G /\ y * x = #e ==> ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)
       True by properties of AbelianMonoid g.
   (2) z NOTIN G* /\ x IN G /\ y IN G /\ x * y = #e /\ y * x = #e ==> x <> z
       Note x IN G*                   by monoid_invertibles_element
       But  z NOTIN G*, so x <> z.
   (3) x IN G /\ y IN G /\ x * y = #e /\ y * x = #e ==> ?y. (y IN G /\ y <> z) /\ (x * y = #e) /\ (y * x = #e)
       Take the same y, then y <> z   by monoid_invertibles_element
*)
val abelian_monoid_invertible_excluding = store_thm(
  "abelian_monoid_invertible_excluding",
  ``!g:'a monoid. AbelianMonoid g ==>
   !z. z NOTIN G* ==> (monoid_invertibles (g excluding z) = G* )``,
  rw_tac std_ss[AbelianMonoid_def] >>
  rw[monoid_invertibles_def, excluding_def, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  metis_tac[] >-
  metis_tac[monoid_invertibles_element] >>
  metis_tac[monoid_invertibles_element]);

(* ------------------------------------------------------------------------- *)
(* Group Exponentiation with Inverses.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Inverse of exponential:  |/(x ** n) = ( |/x) ** n *)
(* Proof:
   By induction on n.
   Base case: |/ (x ** 0) = |/ x ** 0
     |/ (x ** 0)
   = |/ #e            by group_exp_zero
   = #e               by group_inv_id
   = ( |/ #e) ** 0    by group_exp_zero
   Step case: |/ (x ** n) = |/ x ** n ==> |/ (x ** SUC n) = |/ x ** SUC n
     |/ (x ** SUC n)
   = |/ (x * (x ** n))        by group_exp_SUC
   = ( |/ (x ** n)) * ( |/x)  by group_inv_op
   = ( |/x) ** n * ( |/x)     by inductive hypothesis
   = ( |/x) * ( |/x) ** n     by group_exp_comm
   = ( |/x) ** SUC n          by group_exp_SUC
*)
val group_exp_inv = store_thm(
  "group_exp_inv",
  ``!g:'a group. Group g ==> !x. x IN G ==> !n. |/ (x ** n) = ( |/ x) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[group_exp_SUC, group_inv_op, group_exp_comm, group_inv_element, group_exp_element]);

(* Theorem: Exponential of Inverse:  ( |/x) ** n = |/(x ** n) *)
(* Proof: by group_exp_inv. *)
val group_inv_exp = store_thm(
  "group_inv_exp",
  ``!g:'a group. Group g ==> !x. x IN G ==> !n. ( |/ x) ** n = |/ (x ** n)``,
  rw[group_exp_inv]);

(* Theorem: For m < n, x ** m = x ** n ==> x ** (n-m) = #e *)
(* Proof:
     x ** (n-m) * x ** m
   = x ** ((n-m) + m)         by group_exp_add
   = x ** n                   by arithmetic, m < n
   = x ** m                   by given
   Hence x ** (n-m) = #e      by group_lid_unique
*)
val group_exp_eq = store_thm(
  "group_exp_eq",
  ``!g:'a group. Group g ==> !x. x IN G ==> !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n-m) = #e)``,
  rpt strip_tac >>
  `(n-m) + m = n` by decide_tac >>
  `x ** (n-m) * x ** m = x ** ((n-m) + m)` by rw_tac std_ss[group_exp_add] >>
  pop_assum mp_tac >>
  rw_tac std_ss[group_lid_unique, group_exp_element]);

(* Theorem: Group g /\ x IN G ==> (x ** m) ** n = (x ** n) ** m *)
(* Proof:
     (x ** m) ** n
   = x ** (m * n)    by group_exp_mult
   = x ** (n * m)    by MULT_COMM
   = (x ** n) ** m   by group_exp_mult
*)
val group_exp_mult_comm = store_thm(
  "group_exp_mult_comm",
  ``!g:'a group. Group g ==> !x. x IN G ==> !m n. (x ** m) ** n = (x ** n) ** m``,
  metis_tac[group_exp_mult, MULT_COMM]);

(* group_exp_mult is exported, never export a commutative version. *)

(* Theorem: Group /\ x IN G /\ y IN G /\ x * y = y * x ==> (x ** n) * (y ** m) = (y ** m) * (x ** n) *)
(* Proof:
   By inducton on  m.
   Base case: x ** n * y ** 0 = y ** 0 * x ** n
   LHS = x ** n * y ** 0
       = x ** n * #e         by group_exp_0
       = x ** n              by group_rid
       = #e * x ** n         by group_lid
       = y ** 0 * x ** n     by group_exp_0
       = RHS
   Step case: x ** n * y ** m = y ** m * x ** n ==> x ** n * y ** SUC m = y ** SUC m * x ** n
   LHS = x ** n * y ** SUC m
       = x ** n * (y * y ** m)    by group_exp_SUC
       = (x ** n * y) * y ** m    by group_assoc
       = (y * x ** n) * y ** m    by group_comm_exp (with single y)
       = y * (x ** n * y ** m)    by group_assoc
       = y * (y ** m * x ** n)    by induction hypothesis
       = (y * y ** m) * x ** n    by group_assoc
       = y ** SUC m  * x ** n     by group_exp_SUC
       = RHS
*)
val group_comm_exp_exp = store_thm(
  "group_comm_exp_exp",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n m. x ** n * y ** m = y ** m * x ** n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  `x ** n * y ** SUC m = x ** n * (y * y ** m)` by rw[] >>
  `_ = (x ** n * y) * y ** m` by rw[group_assoc] >>
  `_ = (y * x ** n) * y ** m` by metis_tac[group_comm_exp] >>
  `_ = y * (x ** n * y ** m)` by rw[group_assoc] >>
  `_ = y * (y ** m * x ** n)` by metis_tac[] >>
  rw[group_assoc]);

(* ------------------------------------------------------------------------- *)
(* Group Maps Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   homo_group g f   = homo_monoid g f
*)
(* Definitions and Theorems (# are exported):

   Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups:
   GroupHomo_def   |- !f g h. GroupHomo f g h <=> (!x. x IN G ==> f x IN h.carrier) /\
                                                   !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   GroupIso_def    |- !f g h. GroupIso f g h <=> GroupHomo f g h /\ BIJ f G h.carrier
   GroupEndo_def   |- !f g. GroupEndo f g <=> GroupHomo f g g
   GroupAuto_def   |- !f g. GroupAuto f g <=> GroupIso f g g
   subgroup_def    |- !h g. subgroup h g <=> GroupHomo I h g

   Group Homomorphisms:
   group_homo_id       |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id)
   group_homo_element  |- !f g h. GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier
   group_homo_inv      |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> (f ( |/ x) = h.inv (f x))
   group_homo_cong     |- !g h. Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
                                (GroupHomo f1 g h <=> GroupHomo f2 g h)
   group_homo_I_refl   |- !g. GroupHomo I g g
   group_homo_trans    |- !g h k f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
   group_homo_sym      |- !g h f. Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g
   group_homo_compose  |- !g h k f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
   group_homo_is_monoid_homo
                       |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h
   group_homo_monoid_homo
                       |- !f g h. GroupHomo f g h /\ f #e = h.id <=> MonoidHomo f g h
   group_homo_exp      |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
                          !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n

   Group Isomorphisms:
   group_iso_property  |- !f g h. GroupIso f g h <=>
                                  GroupHomo f g h /\ !y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)
   group_iso_id        |- !f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)
   group_iso_element   |- !f g h. GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier
   group_iso_I_refl    |- !g. GroupIso I g g
   group_iso_trans     |- !g h k f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k
   group_iso_sym       |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g
   group_iso_compose   |- !g h k f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k
   group_iso_is_monoid_iso
                       |- !g h f. Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h
   group_iso_monoid_iso|- !f g h. GroupIso f g h /\ f #e = h.id <=> MonoidIso f g h
   group_iso_exp       |- !g h f. Group g /\ Group h /\ GroupIso f g h ==>
                          !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n
   group_iso_order     |- !g h f. Group g /\ Group h /\ GroupIso f g h ==>
                          !x. x IN G ==> (order h (f x) = ord x)
   group_iso_linv_iso  |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g
   group_iso_bij       |- !g h f. GroupIso f g h ==> BIJ f G h.carrier
   group_iso_group     |- !g h f. Group g /\ GroupIso f g h /\ (f #e = h.id) ==> Group h
   group_iso_card_eq   |- !g h f. GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)

   Group Automorphisms:
   group_auto_id       |- !f g. Group g /\ GroupAuto f g ==> (f #e = #e)
   group_auto_element  |- !f g. GroupAuto f g ==> !x. x IN G ==> f x IN G
   group_auto_compose  |- !g f1 f2. GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g
   group_auto_is_monoid_auto
                       |- !g f. Group g /\ GroupAuto f g ==> MonoidAuto f g
   group_auto_exp      |- !g f. Group g /\ GroupAuto f g ==>
                          !x. x IN G ==> !n. f (x ** n) = f x ** n
   group_auto_order    |- !g f. Group g /\ GroupAuto f g ==>
                          !x. x IN G ==> (ord (f x) = ord x)
   group_auto_I        |- !g. GroupAuto I g
   group_auto_linv_auto|- !g f. Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g
   group_auto_bij      |- !g f. GroupAuto f g ==> f PERMUTES G

   Subgroups:
   subgroup_eqn             |- !g h. subgroup h g <=> H SUBSET G /\
                               !x y. x IN H /\ y IN H ==> (h.op x y = x * y)
   subgroup_subset          |- !g h. subgroup h g ==> H SUBSET G
   subgroup_homo_homo       |- !g h k f. subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k
   subgroup_reflexive       |- !g. subgroup g g
   subgroup_transitive      |- !g h k. subgroup g h /\ subgroup h k ==> subgroup g k
   subgroup_I_antisym       |- !g h. subgroup h g /\ subgroup g h ==> GroupIso I h g
   subgroup_carrier_antisym |- !g h. subgroup h g /\ G SUBSET H ==> GroupIso I h g
   subgroup_is_submonoid    |- !g h. Group g /\ Group h /\ subgroup h g ==> submonoid h g
   subgroup_order_eqn       |- !g h. Group g /\ Group h /\ subgroup h g ==>
                               !x. x IN H ==> (order h x = ord x)

   Homomorphic Image of a Group:
   homo_group_closure |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x y. x IN fG /\ y IN fG ==> x o y IN fG
   homo_group_assoc   |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o y o z)
   homo_group_id      |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> #i IN fG /\
                         !x. x IN fG ==> (#i o x = x) /\ (x o #i = x)
   homo_group_inv     |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x. x IN fG ==> ?z. z IN fG /\ (z o x = #i)
   homo_group_group   |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> Group (homo_group g f)
   homo_group_comm    |- !g f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
                         !x y. x IN fG /\ y IN fG ==> (x o y = y o x)
   homo_group_abelian_group  |- !g f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
                                      AbelianGroup (homo_group g f)
   homo_group_by_inj         |- !g f. Group g /\ INJ f G univ(:'b) ==> GroupHomo f g (homo_group g f)

   Injective Image of Group:
   group_inj_image_group           |- !g f. Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f)
   group_inj_image_abelian_group   |- !g f. AbelianGroup g /\ INJ f G univ(:'b) ==> AbelianGroup (monoid_inj_image g f)
   group_inj_image_excluding_group
                               |- !g f e. Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
                                          Group (monoid_inj_image g f excluding f e)
   group_inj_image_excluding_abelian_group
                               |- !g f e. AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
                                          AbelianGroup (monoid_inj_image g f excluding f e)
   group_inj_image_group_homo  |- !g f. INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups.  *)
(* ------------------------------------------------------------------------- *)

(* A function f from g to h is a homomorphism if group properties are preserved. *)
(* For group, no need to ensure that identity is preserved, see group_homo_id.   *)

val GroupHomo_def = Define`
  GroupHomo (f:'a -> 'b) (g:'a group) (h:'b group) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)))
    (* no requirement for: f #e = h.id *)
`;

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val GroupIso_def = Define`
  GroupIso f g h <=> GroupHomo f g h /\ BIJ f G h.carrier
`;

(* A group homomorphism from g to g is an endomorphism. *)
val GroupEndo_def = Define `GroupEndo f g <=> GroupHomo f g g`;

(* A group isomorphism from g to g is an automorphism. *)
val GroupAuto_def = Define `GroupAuto f g <=> GroupIso f g g`;

(* A subgroup h of g if identity is a homomorphism from h to g *)
val subgroup_def = Define `subgroup h g <=> GroupHomo I h g`;

(* ------------------------------------------------------------------------- *)
(* Group Homomorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> f #e = h.id *)
(* Proof:
   Since #e IN G                     by group_id_element,
   f (#e * #e) = h.op (f #e) (f #e)  by GroupHomo_def
   f #e = h.op (f #e) (f #e)         by group_id_id
   ==> f #e = h.id                   by group_id_fix
*)
val group_homo_id = store_thm(
  "group_homo_id",
  ``!f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id)``,
  rw_tac std_ss[GroupHomo_def] >>
  `#e IN G` by rw[] >>
  metis_tac[group_id_fix, group_id_id]);

(* Theorem: GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by GroupHomo_def *)
val group_homo_element = store_thm(
  "group_homo_element",
  ``!f g h. GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier``,
  rw_tac std_ss[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> f ( |/x) = h.inv (f x) *)
(* Proof:
   Since |/x IN G                      by group_inv_element
   f ( |/x * x) = h.op (f |/x) (f x)   by GroupHomo_def
   f (#e) = h.op (f |/x) (f x)         by group_linv
     h.id = h.op (f |/x) (f x)         by group_homo_id
   ==> f |/x = h.inv (f x)             by group_linv_unique
*)
val group_homo_inv = store_thm(
  "group_homo_inv",
  ``!f g h. Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> (f ( |/x) = h.inv (f x))``,
  rpt strip_tac >>
  `|/x IN G` by rw_tac std_ss[group_inv_element] >>
  `f x IN h.carrier /\ f ( |/x) IN h.carrier` by metis_tac[GroupHomo_def] >>
  `h.op (f ( |/x)) (f x) = f ( |/x * x)` by metis_tac[GroupHomo_def] >>
  metis_tac[group_linv_unique, group_homo_id, group_linv]);

(* Theorem: Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==> (GroupHomo f1 g h = GroupHomo f2 g h) *)
(* Proof: by GroupHomo_def, group_op_element *)
val group_homo_cong = store_thm(
  "group_homo_cong",
  ``!(g:'a group) (h:'b group) f1 f2. Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
          (GroupHomo f1 g h = GroupHomo f2 g h)``,
  rw_tac std_ss[GroupHomo_def, EQ_IMP_THM] >-
  metis_tac[group_op_element] >>
  metis_tac[group_op_element]);

(* Theorem: GroupHomo I g g *)
(* Proof: by GroupHomo_def. *)
val group_homo_I_refl = store_thm(
  "group_homo_I_refl",
  ``!g:'a group. GroupHomo I g g``,
  rw[GroupHomo_def]);

(* Theorem: GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo f2 o f1 g k *)
(* Proof: true by GroupHomo_def. *)
val group_homo_trans = store_thm(
  "group_homo_trans",
  ``!(g:'a group) (h:'b group) (k:'c group).
    !f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k``,
  rw[GroupHomo_def]);

(* Theorem: Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g *)
(* Proof:
   Note BIJ f G h.carrier
    ==> BIJ (LINV f G) h.carrier G     by BIJ_LINV_BIJ
   By GroupHomo_def, this is to show:
   (1) x IN h.carrier ==> LINV f G x IN G
       With BIJ (LINV f G) h.carrier G
        ==> INJ (LINV f G) h.carrier G           by BIJ_DEF
        ==> x IN h.carrier ==> LINV f G x IN G   by INJ_DEF
   (2) x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       With x IN h.carrier
        ==> ?x1. (x = f x1) /\ x1 IN G           by BIJ_DEF, SURJ_DEF
       With y IN h.carrier
        ==> ?y1. (y = f y1) /\ y1 IN G           by BIJ_DEF, SURJ_DEF
        and x1 * y1 IN G                         by group_op_element
            LINV f G (h.op x y)
          = LINV f G (f (x1 * y1))                  by GroupHomo_def
          = x1 * y1                                 by BIJ_LINV_THM, x1 * y1 IN G
          = (LINV f G (f x1)) * (LINV f G (f y1))   by BIJ_LINV_THM, x1 IN G, y1 IN G
          = (LINV f G x) * (LINV f G y)             by x = f x1, y = f y1.
*)
val group_homo_sym = store_thm(
  "group_homo_sym",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g``,
  rpt strip_tac >>
  `BIJ (LINV f G) h.carrier G` by rw[BIJ_LINV_BIJ] >>
  fs[GroupHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >>
  `?x1. (x = f x1) /\ x1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `?y1. (y = f y1) /\ y1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `g.op x1 y1 IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]);

Theorem group_homo_sym_any:
  Group g /\ GroupHomo f g h /\
  (!x. x IN h.carrier ==> i x IN g.carrier /\ f (i x) = x) /\
  (!x. x IN g.carrier ==> i (f x) = x)
  ==>
  GroupHomo i h g
Proof
  rpt strip_tac \\ fs[GroupHomo_def]
  \\ rpt strip_tac
  \\ `h.op x y = f (g.op (i x) (i y))` by metis_tac[]
  \\ pop_assum SUBST1_TAC
  \\ first_assum irule
  \\ PROVE_TAC[group_def_alt]
QED

(* Theorem: GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k *)
(* Proof: by GroupHomo_def *)
val group_homo_compose = store_thm(
  "group_homo_compose",
  ``!(g:'a group) (h:'b group) (k:'c group).
   !f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k``,
  rw_tac std_ss[GroupHomo_def]);
(* This is the same as group_homo_trans. *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h *)
(* Proof:
   By MonoidHomo_def, this is to show:
   (1) x IN G ==> f x IN h.carrier, true                           by GroupHomo_def
   (2) x IN G /\ y IN G ==> f (x * y) = h.op (f x) (f y), true     by GroupHomo_def
   (3) Group g /\ Group h /\ GroupHomo f g h ==> f #e = h.id, true by group_homo_id
*)
val group_homo_is_monoid_homo = store_thm(
  "group_homo_is_monoid_homo",
  ``!g:'a group h f. Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h``,
  rw[MonoidHomo_def] >-
  fs[GroupHomo_def] >-
  fs[GroupHomo_def] >>
  fs[group_homo_id]);

(* Theorem: (GroupHomo f g h /\ f #e = h.id) <=> MonoidHomo f g h *)
(* Proof: by MonoidHomo_def, GroupHomo_def. *)
Theorem group_homo_monoid_homo:
  !f g h. (GroupHomo f g h /\ f #e = h.id) <=> MonoidHomo f g h
Proof
  simp[MonoidHomo_def, GroupHomo_def] >>
  rw[EQ_IMP_THM]
QED

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidHomo f g h   by group_homo_is_monoid_homo
    The result follows     by monoid_homo_exp
*)
val group_homo_exp = store_thm(
  "group_homo_exp",
  ``!g:'a group h:'b group f. Group g /\ Group h /\ GroupHomo f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[group_is_monoid, group_homo_is_monoid_homo, monoid_homo_exp]);

(* ------------------------------------------------------------------------- *)
(* Group Isomorphisms                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GroupIso f g h <=> GroupIHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) BIJ f G H /\ y IN H ==> ?!x. x IN G /\ (f x = y)
       true by INJ_DEF and SURJ_DEF.
   (2) !y. y IN H /\ GroupHomo f g h ==> ?!x. x IN G /\ (f x = y) ==> BIJ f G H
       true by INJ_DEF and SURJ_DEF, and
       x IN G /\ GroupHomo f g h ==> f x IN H  by GroupHomo_def
*)
val group_iso_property = store_thm(
  "group_iso_property",
  ``!f g h. GroupIso f g h <=> GroupHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y))``,
  rw[GroupIso_def, EQ_IMP_THM] >-
  metis_tac[BIJ_THM] >>
  rw[BIJ_THM] >>
  metis_tac[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> f #e = h.id *)
(* Proof:
   Since Group g, Group h ==> Monoid g, Monoid h   by group_is_monoid
   and GroupIso = WeakIso, GroupHomo = WeakHomo,
   this follows by monoid_iso_id.
*)
val group_iso_id = store_thm(
  "group_iso_id",
  ``!f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)``,
  rw[monoid_weak_iso_id, group_is_monoid, GroupIso_def, GroupHomo_def, WeakIso_def, WeakHomo_def]);
(* However,
   this result is worse than (proved earlier):
- group_homo_id;
> val it = |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id) : thm
*)

(* Theorem: GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by GroupIso_def, group_homo_element *)
val group_iso_element = store_thm(
  "group_iso_element",
  ``!f g h. GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier``,
  metis_tac[GroupIso_def, group_homo_element]);

(* Theorem: GroupIso I g g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo I g g, true by group_homo_I_refl
   (2) BIJ I R R, true by BIJ_I_SAME
*)
val group_iso_I_refl = store_thm(
  "group_iso_I_refl",
  ``!g:'a group. GroupIso I g g``,
  rw[GroupIso_def, group_homo_I_refl, BIJ_I_SAME]);

(* Theorem: GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g
       True by group_homo_trans.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE.
*)
val group_iso_trans = store_thm(
  "group_iso_trans",
  ``!(g:'a group) (h:'b group) (k:'c group).
    !f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k``,
  rw[GroupIso_def] >-
  metis_tac[group_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Group g ==> !f. GroupIso f g h ==> GroupIso (LINV f G) h g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g
       True by group_homo_sym.
   (2) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val group_iso_sym = store_thm(
  "group_iso_sym",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g``,
  rw[GroupIso_def, group_homo_sym, BIJ_LINV_BIJ]);

(* Theorem: GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
       True by group_homo_compose.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE
*)
val group_iso_compose = store_thm(
  "group_iso_compose",
  ``!(g:'a group) (h:'b group) (k:'c group).
   !f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k``,
  rw_tac std_ss[GroupIso_def] >-
  metis_tac[group_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as group_iso_trans. *)

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h *)
(* Proof: by GroupIso_def, MonoidIso_def, group_homo_is_monoid_homo *)
val group_iso_is_monoid_iso = store_thm(
  "group_iso_is_monoid_iso",
  ``!(g:'a group) (h:'b group) f. Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h``,
  rw[GroupIso_def, MonoidIso_def] >>
  rw[group_homo_is_monoid_homo]);

(* Theorem: (GroupIso f g h /\ f #e = h.id) <=> MonoidIso f g h *)
(* Proof:
       MonioidIso f g h
   <=> MonoidHomo f g h /\ BIJ f G h.carrier                 by MonoidIso_def
   <=> GroupHomo f g h /\ f #e = h.id /\ BIJ f G h.carrier   by group_homo_monoid_homo
   <=> GroupIso f g h /\ f #e = h.id                         by GroupIso_def
*)
Theorem group_iso_monoid_iso:
  !f g h. (GroupIso f g h /\ f #e = h.id) <=> MonoidIso f g h
Proof
  simp[MonoidIso_def, GroupIso_def] >>
  metis_tac[group_homo_monoid_homo]
QED

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidIso f g h    by group_iso_is_monoid_iso
    The result follows     by monoid_iso_exp
*)
val group_iso_exp = store_thm(
  "group_iso_exp",
  ``!g:'a group h:'b group f. Group g /\ Group h /\ GroupIso f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[group_is_monoid, group_iso_is_monoid_iso, monoid_iso_exp]);

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                    by group_is_monoid
    and MonoidIso f h g                         by group_iso_is_monoid_iso
   Thus !x. x IN H ==> (order h (f x) = ord x)  by monoid_iso_order
*)
val group_iso_order = store_thm(
  "group_iso_order",
  ``!(g:'a group) (h:'b group) f. Group g /\ Group h /\ GroupIso f g h ==>
    !x. x IN G ==> (order h (f x) = ord x)``,
  rw[group_is_monoid, group_iso_is_monoid_iso, monoid_iso_order]);

(* Theorem: Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g *)
(* Proof:
   By GroupIso_def, GroupHomo_def, this is to show:
   (1) BIJ f G h.carrier /\ x IN h.carrier ==> LINV f G x IN G
       True by BIJ_LINV_ELEMENT
   (2) BIJ f G h.carrier /\ x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       Let x' = LINV f G x, y' = LINV f G y.
       Then x' IN G /\ y' IN G        by BIJ_LINV_ELEMENT
         so x' * y' IN G              by group_op_element
        ==> f (x' * y') = h.op (f x') (f y')    by GroupHomo_def
                        = h.op x y              by BIJ_LINV_THM
       Thus LINV f G (h.op x y)
          = LINV f G (f (x' * y'))    by above
          = x' * y'                   by BIJ_LINV_THM
   (3) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val group_iso_linv_iso = store_thm(
  "group_iso_linv_iso",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g``,
  rw_tac std_ss[GroupIso_def, GroupHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
 (qabbrev_tac `x' = LINV f G x` >>
  qabbrev_tac `y' = LINV f G y` >>
  metis_tac[BIJ_LINV_THM, BIJ_LINV_ELEMENT, group_op_element]) >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as group_iso_sym. *)

(* Theorem: GroupIso f g h ==> BIJ f G h.carrier *)
(* Proof: by GroupIso_def *)
val group_iso_bij = store_thm(
  "group_iso_bij",
  ``!(g:'a group) (h:'b group) f. GroupIso f g h ==> BIJ f G h.carrier``,
  rw_tac std_ss[GroupIso_def]);

(* Note: read the discussion in group_iso_id for the condition: f #e = h.id:
   group_iso_id  |- !f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)
*)
(* Theorem: Group g /\ GroupIso f g h /\ f #e = h.id ==> Group h  *)
(* Proof:
   This is to show:
   (1) x IN h.carrier /\ y IN h.carrier ==> h.op x y IN h.carrier
       Group g ==> Monoid g               by group_is_monoid
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
             ?y'. y' IN G /\ (f y' = y)   by group_iso_property
             h.op x y = f (x' * y')       by GroupHomo_def
       As                  x' * y' IN G   by group_op_element
       hence f (x' * y') IN h.carrier     by GroupHomo_def
   (2) x IN h.carrier /\ y IN h.carrier /\ z IN h.carrier ==> h.op (h.op x y) z = h.op x (h.op y z)
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
             ?y'. y' IN G /\ (f y' = y)   by group_iso_property
             ?z'. z' IN G /\ (f z' = z)   by group_iso_property
       as     x' * y' IN G                by group_op_element
       and f (x' * y') IN h.carrier       by GroupHomo_def
       ?!t. t IN G /\ f t = f (x' * y')   by group_iso_property
       i.e.  t = x' * y'                  by uniqueness
       hence h.op (h.op x y) z = f (x' * y' * z')
                                          by GroupHomo_def
       Similary,
       as     y' * z' IN G                by group_op_element
       and f (y' * z') IN h.carrier       by GroupHomo_def
       ?!s. s IN G /\ f s = f (y' * z')   by group_iso_property
       i.e.  s = y' * z'                  by uniqueness
       and   h.op x (h.op y z) = f (x' * (y' * z'))
                                          by GroupHomo_def
       hence true                         by group_assoc.
   (3) h.id IN h.carrier
       Since #e IN G                      by group_id_element
            (f #e) = h.id IN h.carrier    by GroupHomo_def
   (4) x IN h.carrier ==> h.op h.id x = x
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
       h.id IN h.carrier                  by group_id_element
       ?!e. e IN G /\ f e = h.id = f #e   by group_iso_property
       i.e. e = #e                        by uniqueness
       hence h.op h.id x = f (e * x')     by GroupHomo_def
                         = f (#e * x')
                         = f x'           by group_lid
                         = x
   (5) x IN h.carrier ==> ?y. y IN h.carrier /\ (h.op y x = h.id)
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
       so      |/ x' IN G                 by group_inv_element
       and  f ( |/ x') IN h.carrier       by GroupHomo_def
       Let y = f ( |/ x')
       then h.op y x = f ( |/ x' * x')    by GroupHomo_def
                     = f #e               by group_linv
                     = h.id
*)
val group_iso_group = store_thm(
  "group_iso_group",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h /\ (f #e = h.id) ==> Group h``,
  rw[group_iso_property] >>
  `(!x. x IN G ==> f x IN h.carrier) /\ !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))`
    by metis_tac[GroupHomo_def] >>
  rw[group_def_alt] >| [
    metis_tac[group_op_element],
    `?x'. x' IN G /\ (f x' = x)` by metis_tac[] >>
    `?y'. y' IN G /\ (f y' = y)` by metis_tac[] >>
    `?z'. z' IN G /\ (f z' = z)` by metis_tac[] >>
    `?t. t IN G /\ (t = x' * y')` by metis_tac[group_op_element] >>
    `h.op (h.op x y) z = f (x' * y' * z')` by metis_tac[] >>
    `?s. s IN G /\ (s = y' * z')` by metis_tac[group_op_element] >>
    `h.op x (h.op y z) = f (x' * (y' * z'))` by metis_tac[] >>
    `x' * y' * z' = x' * (y' * z')` by rw[group_assoc] >>
    metis_tac[],
    metis_tac[group_id_element, GroupHomo_def],
    metis_tac[group_lid, group_id_element],
    metis_tac[group_linv, group_inv_element]
  ]);

(* Theorem: GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier) *)
(* Proof: by GroupIso_def, FINITE_BIJ_CARD. *)
val group_iso_card_eq = store_thm(
  "group_iso_card_eq",
  ``!g:'a group h:'b group f. GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)``,
  metis_tac[GroupIso_def, FINITE_BIJ_CARD]);

(* ------------------------------------------------------------------------- *)
(* Group Automorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ GroupAuto f g ==> (f #e = #e) *)
(* Proof: by GroupAuto_def, group_iso_id *)
val group_auto_id = store_thm(
  "group_auto_id",
  ``!f g. Group g /\ GroupAuto f g ==> (f #e = #e)``,
  rw_tac std_ss[GroupAuto_def, group_iso_id]);

(* Theorem: GroupAuto f g ==> !x. x IN G ==> f x IN G *)
(* Proof: by GroupAuto_def, group_iso_element *)
val group_auto_element = store_thm(
  "group_auto_element",
  ``!f g. GroupAuto f g ==> !x. x IN G ==> f x IN G``,
  metis_tac[GroupAuto_def, group_iso_element]);

(* Theorem: GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g *)
(* Proof: by GroupAuto_def, group_iso_compose *)
val group_auto_compose = store_thm(
  "group_auto_compose",
  ``!(g:'a group). !f1 f2. GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g``,
  metis_tac[GroupAuto_def, group_iso_compose]);

(* Theorem: Group g /\ GroupAuto f g ==> MonoidAuto f g *)
(* Proof: by GroupAuto_def, MonoidAuto_def, group_iso_is_monoid_iso *)
val group_auto_is_monoid_auto = store_thm(
  "group_auto_is_monoid_auto",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==> MonoidAuto f g``,
  rw[GroupAuto_def, MonoidAuto_def] >>
  rw[group_iso_is_monoid_iso]);

(* Theorem: Group g /\ GroupAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidAuto f g     by group_auto_is_monoid_auto
    The result follows     by monoid_auto_exp
*)
val group_auto_exp = store_thm(
  "group_auto_exp",
  ``!g:'a group f. Group g /\ GroupAuto f g ==>
   !x. x IN G ==> !n. f (x ** n) = (f x) ** n``,
  rw[group_is_monoid, group_auto_is_monoid_auto, monoid_auto_exp]);

(* Theorem: Group g /\ GroupAuto f g ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                  by group_is_monoid
    and MonoidAuto f h                        by group_auto_is_monoid_auto
   Thus !x. x IN H ==> (ord (f x) = ord x)    by monoid_auto_order
*)
val group_auto_order = store_thm(
  "group_auto_order",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==>
    !x. x IN G ==> (ord (f x) = ord x)``,
  rw[group_is_monoid, group_auto_is_monoid_auto, monoid_auto_order]);

(* Theorem: GroupAuto I g *)
(* Proof:
       GroupAuto I g
   <=> GroupIso I g g                 by GroupAuto_def
   <=> GroupHomo I g g /\ BIJ f G G   by GroupIso_def
   <=> T /\ BIJ f G G                 by GroupHomo_def, I_THM
   <=> T /\ T                         by BIJ_I_SAME
*)
val group_auto_I = store_thm(
  "group_auto_I",
  ``!(g:'a group). GroupAuto I g``,
  rw_tac std_ss[GroupAuto_def, GroupIso_def, GroupHomo_def, BIJ_I_SAME]);

(* Theorem: Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g *)
(* Proof:
       GroupAuto I g
   ==> GroupIso I g g                by GroupAuto_def
   ==> GroupIso (LINV f G) g         by group_iso_linv_iso
   ==> GroupAuto (LINV f G) g        by GroupAuto_def
*)
val group_auto_linv_auto = store_thm(
  "group_auto_linv_auto",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g``,
  rw_tac std_ss[GroupAuto_def, group_iso_linv_iso]);

(* Theorem: GroupAuto f g ==> f PERMUTES G *)
(* Proof: by GroupAuto_def, GroupIso_def *)
val group_auto_bij = store_thm(
  "group_auto_bij",
  ``!g:'a group. !f. GroupAuto f g ==> f PERMUTES G``,
  rw_tac std_ss[GroupAuto_def, GroupIso_def]);

(* ------------------------------------------------------------------------- *)
(* Subgroups                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: subgroup h g <=> H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) *)
(* Proof:
       subgroup h g
   <=> GroupHomo I h g                                              by subgroup_def
   <=> (!x. x IN H ==> I x IN G) /\
       (!x y. x IN H /\ y IN H ==> (I (h.op x y) = (I x) * (I y)))  by GroupHomo_def
   <=> (!x. x IN H ==> x IN G) /\
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))              by I_THM
   <=> H SUBSET G
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))              by SUBSET_DEF
*)
val subgroup_eqn = store_thm(
  "subgroup_eqn",
  ``!(g:'a group) (h:'a group). subgroup h g <=>
     H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))``,
  rw_tac std_ss[subgroup_def, GroupHomo_def, SUBSET_DEF]);

(* Theorem: subgroup h g ==> H SUBSET G *)
(* Proof: by subgroup_eqn *)
val subgroup_subset = store_thm(
  "subgroup_subset",
  ``!(g:'a group) (h:'a group). subgroup h g ==> H SUBSET G``,
  rw_tac std_ss[subgroup_eqn]);

(* Theorem: subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k *)
(* Proof:
   Note H SUBSET G              by subgroup_subset
     or !x. x IN H ==> x IN G   by SUBSET_DEF
   By GroupHomo_def, this is to show:
   (1) x IN H ==> f x IN k.carrier
       True                     by GroupHomo_def, GroupHomo f g k
   (2) x IN H /\ y IN H /\ f (h.op x y) = k.op (f x) (f y)
       Note x IN H ==> x IN G   by above
        and y IN H ==> y IN G   by above
         f (h.op x y)
       = f (x * y)              by subgroup_eqn
       = k.op (f x) (f y)       by GroupHomo_def
*)
val subgroup_homo_homo = store_thm(
  "subgroup_homo_homo",
  ``!(g:'a group) (h:'a group) (k:'b group) f. subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k``,
  rw_tac std_ss[subgroup_def, GroupHomo_def]);

(* Theorem: subgroup g g *)
(* Proof:
   By subgroup_def, this is to show:
   GroupHomo I g g, true by group_homo_I_refl.
*)
val subgroup_reflexive = store_thm(
  "subgroup_reflexive",
  ``!g:'a group. subgroup g g``,
  rw[subgroup_def, group_homo_I_refl]);

(* Theorem: subgroup g h /\ subgroup h k ==> subgroup g k *)
(* Proof:
   By subgroup_def, this is to show:
   GroupHomo I g h /\ GroupHomo I h k ==> GroupHomo I g k
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by group_homo_trans
*)
val subgroup_transitive = store_thm(
  "subgroup_transitive",
  ``!(g h k):'a group. subgroup g h /\ subgroup h k ==> subgroup g k``,
  prove_tac[subgroup_def, combinTheory.I_o_ID, group_homo_trans]);

(* Theorem: subgroup h g /\ subgroup g h ==> GroupIso I h g *)
(* Proof:
   By subgroup_def, GroupIso_def, this is to show:
      GroupHomo I h g /\ GroupHomo I g h ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by subgroup_subset, subgroup h g
   (2) x IN G ==> x IN H, true    by subgroup_subset, subgroup g h
*)
val subgroup_I_antisym = store_thm(
  "subgroup_I_antisym",
  ``!(g:'a monoid) h. subgroup h g /\ subgroup g h ==> GroupIso I h g``,
  rw_tac std_ss[subgroup_def, GroupIso_def] >>
  fs[GroupHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subgroup h g /\ G SUBSET H ==> GroupIso I h g *)
(* Proof:
   By subgroup_def, GroupIso_def, this is to show:
      GroupHomo I h g /\ G SUBSET H ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by subgroup_subset, subgroup h g
   (2) x IN G ==> x IN H, true    by G SUBSET H, given
*)
val subgroup_carrier_antisym = store_thm(
  "subgroup_carrier_antisym",
  ``!(g:'a group) h. subgroup h g /\ G SUBSET H ==> GroupIso I h g``,
  rpt (stripDup[subgroup_def]) >>
  rw_tac std_ss[GroupIso_def] >>
  `H SUBSET G` by rw[subgroup_subset] >>
  fs[GroupHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: Group g /\ Group h /\ subgroup h g ==> submonoid h g *)
(* Proof:
   By subgroup_def, submonoid_def, this is to show:
      Group g /\ Group h /\ GroupHomo I h g ==> MonoidHomo I h g
   This is true by group_homo_is_monoid_homo
*)
Theorem subgroup_is_submonoid0:
  !g:'a group h. Group g /\ Group h /\ subgroup h g ==> submonoid h g
Proof
  rw[subgroup_def, submonoid_def] >>
  rw[group_homo_is_monoid_homo]
QED

(* Theorem: Group g /\ Group h /\ subgroup h g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                  by group_is_monoid
    and submonoid h g                         by subgroup_is_submonoid0
   Thus !x. x IN H ==> (order h x = ord x)    by submonoid_order_eqn
*)
val subgroup_order_eqn = store_thm(
  "subgroup_order_eqn",
  ``!g:'a group h. Group g /\ Group h /\ subgroup h g ==>
   !x. x IN H ==> (order h x = ord x)``,
  rw[group_is_monoid, subgroup_is_submonoid0, submonoid_order_eqn]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of a Group.                                             *)
(* ------------------------------------------------------------------------- *)

(* For those same as monoids, use overloading  *)
val _ = overload_on ("homo_group", ``homo_monoid``);

(* Theorem: [Closure] Group g /\ GroupHomo f g (homo_group g f) ==> x IN fG /\ y IN fG ==> x o y IN fG *)
(* Proof:
   x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))  by homo_monoid_property
   Since   CHOICE (preimage f G x) IN G    by preimage_choice_property
           CHOICE (preimage f G y) IN G    by preimage_choice_property
   hence   CHOICE (preimage f G x) * CHOICE (preimage f G y) IN G      by group_op_element
   so    f (CHOICE (preimage f G x) * CHOICE (preimage f G y)) IN fG   by GroupHomo_def
*)
val homo_group_closure = store_thm(
  "homo_group_closure",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
     !x y. x IN fG /\ y IN fG ==> x o y IN fG``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_def, image_op_def] >>
  rw_tac std_ss[preimage_choice_property, group_op_element]);

(* Theorem: [Associative] Group g /\ GroupHomo f g (homo_group g f) ==>
            x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = x o (y o z) *)
(* Proof:
   By GroupHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
           CHOICE (preimage f G y) IN G /\ y = f (CHOICE (preimage f G y))   by preimage_choice_property
           CHOICE (preimage f G z) IN G /\ z = f (CHOICE (preimage f G z))   by preimage_choice_property
     (x o y) o z
   = (f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y))) o f (CHOICE (preimage f G z))   by expanding x, y, z
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)) o f (CHOICE (preimage f G z))         by homo_monoid_property
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y) * CHOICE (preimage f G z))             by homo_monoid_property
   = f (CHOICE (preimage f G x) * (CHOICE (preimage f G y) * CHOICE (preimage f G z)))           by group_assoc
   = f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y) * CHOICE (preimage f G z))         by homo_monoid_property
   = f (CHOICE (preimage f G x)) o (f (CHOICE (preimage f G y)) o f (CHOICE (preimage f G z)))   by homo_monoid_property
   = x o (y o z)                                                                                 by contracting x, y, z
*)
val homo_group_assoc = store_thm(
  "homo_group_assoc",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
   !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[GroupHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==>
     (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw_tac std_ss[homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G y) IN G /\ (f (CHOICE (preimage f G y)) = y)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) IN G` by rw[] >>
  `CHOICE (preimage f G y) * CHOICE (preimage f G z) IN G` by rw[] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) * CHOICE (preimage f G z) =
   CHOICE (preimage f G x) * (CHOICE (preimage f G y) * CHOICE (preimage f G z))` by rw[group_assoc] >>
  metis_tac[]);

(* Theorem: [Identity] Group g /\ GroupHomo f g (homo_group g f) ==> #i IN fG /\ #i o x = x /\ x o #i = x. *)
(* Proof:
   By homo_monoid_property, #i = f #e, and #i IN fG.
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   hence  #i o x
        = (f #e) o  f (preimage f G x)
        = f (#e * preimage f G x)       by homo_group_property
        = f (preimage f G x)            by group_lid
        = x
   similarly for x o #i = x             by group_rid
*)
val homo_group_id = store_thm(
  "homo_group_id",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
      #i IN fG /\ (!x. x IN fG ==> (#i o x = x) /\ (x o #i = x))``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >| [
    rw[],
    metis_tac[group_lid, group_id_element, preimage_choice_property],
    metis_tac[group_rid, group_id_element, preimage_choice_property]
  ]);

(* Theorem: [Inverse] Group g /\ GroupHomo f g (homo_monoid g f) ==> x IN fG ==> ?z. z IN fG /\ z o x = #i. *)
(* Proof:
   x IN fG ==> CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   Choose z = f ( |/ (preimage f G x)),
   then   z IN fG since |/ CHOICE (preimage f G x) IN G,
   and    z o x = f ( |/ (CHOICE (preimage f G x))) o f (CHOICE (preimage f G x))
                = f ( |/ (CHOICE (preimage f G x)) * CHOICE (preimage f G x))    by homo_monoid_property
                = f #e                                                           by group_lid
                = #i                                                             by homo_monoid_id
*)
val homo_group_inv = store_thm(
  "homo_group_inv",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_monoid g f) ==>
     !x. x IN fG ==> ?z. z IN fG /\ (z o x = #i)``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `|/ (CHOICE (preimage f G x)) IN G /\ ( |/ (CHOICE (preimage f G x)) * CHOICE (preimage f G x) = #e)` by rw[] >>
  qexists_tac `f ( |/ (CHOICE (preimage f G x)))` >>
  metis_tac[]);

(* Theorem: [Commutative] AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
            x IN fG /\ y IN fG ==> (x o y = y o x) *)
(* Proof:
   Note AbelianGroup g ==> Group g and
        !x y. x IN G /\ y IN G ==> (x * y = y * x)          by AbelianGroup_def
   By GroupHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
           CHOICE (preimage f G y) IN G /\ y = f (CHOICE (preimage f G y))   by preimage_choice_property
     x o y
   = f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y))   by expanding x, y
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))       by homo_monoid_property
   = f (CHOICE (preimage f G y) * CHOICE (preimage f G x))       by AbelianGroup_def, above
   = f (CHOICE (preimage f G y)) o f (CHOICE (preimage f G x))   by homo_monoid_property
   = y o x                                                       by contracting x, y
*)
val homo_group_comm = store_thm(
  "homo_group_comm",
  ``!(g:'a group) (f:'a -> 'b). AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
   !x y. x IN fG /\ y IN fG ==> (x o y = y o x)``,
  rw_tac std_ss[AbelianGroup_def, GroupHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G y) IN G /\ (f (CHOICE (preimage f G y)) = y)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) = CHOICE (preimage f G y) * CHOICE (preimage f G x)` by rw[] >>
  metis_tac[]);

(* Theorem: Homomorphic image of a group is a group.
            Group g /\ GroupHomo f g (homo_monoid g f) ==> Group (homo_monoid g f) *)
(* Proof:
   This is to show each of these:
   (1) x IN fG /\ y IN fG ==> x o y IN fG    true by homo_group_closure
   (2) x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = (x o y) o z    true by homo_group_assoc
   (3) #i IN fG, true by homo_group_id
   (4) x IN fG ==> #i o x = x, true by homo_group_id
   (5) x IN fG ==> ?y. y IN fG /\ (y o x = #i), true by homo_group_inv
*)
val homo_group_group = store_thm(
  "homo_group_group",
  ``!(g:'a group) f. Group g /\ GroupHomo f g (homo_monoid g f) ==> Group (homo_monoid g f)``,
  rpt strip_tac >>
  rw[group_def_alt] >| [
    rw[homo_group_closure],
    rw[homo_group_assoc],
    rw[homo_group_id],
    rw[homo_group_id],
    rw[homo_group_inv]
  ]);

(* Theorem: Homomorphic image of an Abelian group is an Abelian group.
            AbelianGroup g /\ GroupHomo f g (homo_group g f) ==> AbelianGroup (homo_monoid g f) *)
(* Proof:
   Note AbelianGroup g ==> Group g                  by AbelianGroup_def
   By AbelianGroup_def, this is to show:
   (1) Group (homo_group g f), true                 by homo_group_group, Group g
   (2) x IN fG /\ y IN fG ==> x o y = y o x, true   by homo_group_comm, AbelianGroup g
*)
val homo_group_abelian_group = store_thm(
  "homo_group_abelian_group",
  ``!(g:'a group) f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==> AbelianGroup (homo_monoid g f)``,
  metis_tac[homo_group_group, AbelianGroup_def, homo_group_comm]);

(* Theorem: Group g /\ INJ f G UNIV ==> GroupHomo f g (homo_group g f) *)
(* Proof:
   By GroupHomo_def, homo_monoid_property, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true                 by IN_IMAGE
   (2) x IN G /\ y IN G ==> f (x * y) = f x o f y, true  by homo_monoid_op_inj
*)
val homo_group_by_inj = store_thm(
  "homo_group_by_inj",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ INJ f G UNIV ==> GroupHomo f g (homo_group g f)``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >-
  rw[] >>
  rw[homo_monoid_op_inj]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Group.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Group g, and an injective function f,
   then the image (f G) is a Group, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Define a group injective image for an injective f, with LINV f G. *)
(* Since a group is a monoid, group injective image = monoid injective image *)

(* Theorem: Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f) *)
(* Proof:
   By Group_def, this is to show:
   (1) Group g ==> Monoid (monoid_inj_image g f)
       Group g ==> Monoid g                            by group_is_monoid
               ==> Monoid (monoid_inj_image g f)       by monoid_inj_image_monoid
   (2) monoid_invertibles (monoid_inj_image g f) = (monoid_inj_image g f).carrier
       By monoid_invertibles_def, monoid_inj_image_def, this is to show:
       z IN G ==> ?y. (?x. (y = f x) /\ x IN G) /\
                  (f (t (f z) * t y) = f #e) /\ (f (t y * t (f z)) = f #e)
                                                       where t = LINV f G
      Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)   by INJ_IMAGE_BIJ_ALT
        so !x. x IN G ==> t (f x) = x
       and !x. x IN (IMAGE f G) ==> f (t x) = x        by BIJ_LINV_THM
      Also z IN G ==> |/ z IN G                        by group_inv_element
       Put x = |/ z, and y = f x
      Then  f (t (f z) * t y)
          = f (t (f z) * t (f ( |/ z)))                by y = f ( |/ z)
          = f (z * |/ z)                               by !y. t (f y) = y
          = f #e                                       by group_inv_thm
        and f (t y * t (f z))
          = f (t (f ( |/ z)) * t (f z))                by y = f ( |/ z)
          = f ( |/ z * z)                              by !y. t (f y) = y
          = f #e                                       by group_inv_thm
*)
Theorem group_inj_image_group:
  !(g:'a group) (f:'a -> 'b). Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f)
Proof
  rpt strip_tac >>
  rw_tac std_ss[Group_def] >-
  rw[monoid_inj_image_monoid] >>
  rw[monoid_invertibles_def, monoid_inj_image_def, EXTENSION, EQ_IMP_THM] >>
  `g.inv x' IN G` by rw[] >>
  qexists_tac `f (g.inv x')` >>
  `BIJ f G (IMAGE f G)` by rw[INJ_IMAGE_BIJ_ALT] >>
  imp_res_tac BIJ_LINV_THM >>
  metis_tac[group_inv_thm]
QED

(* Theorem: AbelianGroup g /\ INJ f G univ(:'b) ==> AbelianGroup (monoid_inj_image g f) *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group g ==> Group (monoid_inj_image g f)
       True by group_inj_image_group.
   (2) (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       By monoid_inj_image_def, this is to show:
       x' IN G /\ x'' IN G /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
       ==> f (t (f x') * t (f x'')) = f (t (f x'') * t (f x'))  where t = LINV f G
       Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)  by INJ_IMAGE_BIJ_ALT
         so !x. x IN G ==> t (f x) = x
        and !x. x IN (IMAGE f G) ==> f (t x) = x       by BIJ_LINV_THM
         f (t (f x') * t (f x''))
       = f (x' * x'')                                  by !y. t (f y) = y
       = f (x'' * x')                                  by commutativity condition
       = f (t (f x'') * t (f x'))                      by !y. t (f y) = y
*)
Theorem group_inj_image_abelian_group:
  !(g:'a group) (f:'a -> 'b). AbelianGroup g /\ INJ f G univ(:'b) ==>
       AbelianGroup (monoid_inj_image g f)
Proof
  rw[AbelianGroup_def] >-
  rw[group_inj_image_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[monoid_inj_image_def] >>
  metis_tac[INJ_IMAGE_BIJ_ALT, BIJ_LINV_THM]
QED

(* Theorem: Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G
            ==> Group (monoid_inj_image g f excluding f e) *)
(* Proof:
   Let h = g excluding e.
   Then H = h.carrier = G DIFF {e}             by excluding_def
    and h.op = g.op /\ h.id = g.id             by excluding_def
    and IMAGE f H = IMAGE f G DIFF {f e}       by IMAGE_DIFF
    and H SUBSET G                             by DIFF_SUBSET
   Let t = LINV f G.
   Then !x. x IN H ==> t (f x) = x             by LINV_SUBSET

   By group_def_alt, monoid_inj_image_def, excluding_def, this is to show:
   (1) x IN IMAGE f H /\ y IN IMAGE f H ==> f (t x * t y) IN IMAGE f H
       Note ?a. (x = f a) /\ a IN H            by IN_IMAGE
            ?b. (y = f b) /\ b IN H            by IN_IMAGE
       Hence  f (t x * t y)
            = f (t (f a) * t (f b))            by x = f a, y = f b
            = f (a * b)                        by !y. t (f y) = y
       Since a * b IN H                        by group_op_element
       hence f (a * b) IN IMAGE f H            by IN_IMAGE
   (2) x IN IMAGE f H /\ y IN IMAGE f H /\ z IN IMAGE f H ==> f (t x * t y * t z) = f (t x * (t y * t z))
       Note ?a. (x = f a) /\ a IN G            by IN_IMAGE
            ?b. (y = f b) /\ b IN G            by IN_IMAGE
            ?c. (z = f c) /\ c IN G            by IN_IMAGE
       Hence  (t x * t y) * t z
            = (t (f a) * t (f b)) * t (f c)    by x = f a, y = f b, z = f c
            = (a * b) * c                      by !y. t (f y) = y
            = a * (b * c)                      by group_assoc
            = t (f a) * (t (f b) * t (f c))    by !y. t (f y) = y
            = t x * (t y * t z)                by x = f a, y = f b, z = f c
       or   f ((t x * t y) * t z) = f (t x * (t y * t z))
   (3) f #e IN IMAGE f H
       Since #e IN H                           by group_id_element
       f #e IN IMAGE f H                       by IN_IMAGE
   (4) x IN IMAGE f H ==> f (t (f #e) * t x) = x
       Note #e IN H                            by group_id_element
        and ?a. (x = f a) /\ a IN H            by IN_IMAGE
       Hence f (t (f #e) * t x)
           = f (#e * t x)                      by !y. t (f y) = y
           = f (#e * t (f a))                  by x = f a
           = f (#e * a)                        by !y. t (f y) = y
           = f a                               by group_id
           = x                                 by x = f a
   (5) x IN IMAGE f H ==> ?y. y IN IMAGE f H /\ f (t y * t x) = f #e
       Note ?a. (x = f a) /\ a IN H            by IN_IMAGE
        and b = (h.inv a) IN H                 by group_inv_element
       Let y = f b.
       Then y IN IMAGE f H                     by IN_IMAGE
        and f (t y * t x)
          = f (t y * t (f a))                  by x = f a
          = f (t (f b)) * t (f a))             by y = f b
          = f (b * a)                          by !y. t (f y) = y
          = f #e                               by group_linv
*)
Theorem group_inj_image_excluding_group:
  !(g:'a group) (f:'a -> 'b) e.
      Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
      Group (monoid_inj_image g f excluding f e)
Proof
  rpt strip_tac >>
  qabbrev_tac `h = g excluding e` >>
  `h.carrier = G DIFF {e} /\ h.op = g.op /\ h.id = g.id` by rw[excluding_def, Abbr`h`] >>
  qabbrev_tac `Q = IMAGE f G DIFF {f e}` >>
  `H SUBSET G` by fs[] >>
  imp_res_tac LINV_SUBSET >>
  rw_tac std_ss[group_def_alt, monoid_inj_image_def, excluding_def] >| [
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_op_element, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    `?a. (x = f a) /\ a IN H` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN H` by rw[GSYM IN_IMAGE] >>
    `?c. (z = f c) /\ c IN H` by rw[GSYM IN_IMAGE] >>
    metis_tac[group_assoc, group_op_element],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_id_element, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_id_element, group_id, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    `?a. (x = f a) /\ a IN H` by rw[GSYM IN_IMAGE] >>
    `h.inv a IN H` by rw[group_inv_element] >>
    `f (h.inv a) IN Q` by rw[] >>
    metis_tac[group_linv]
  ]
QED

(* Theorem: AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
            AbelianGroup (monoid_inj_image g f excluding f e) *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Group (monoid_inj_image g f excluding f e)
       True by group_inj_image_excluding_group.
   (2) x IN IMAGE f H /\ y IN IMAGE f H ==> (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       where H = G DIFF {e}
       Note H SUBSET G                                     by DIFF_SUBSET
         so !x. x IN H ==> LINV f G (f x) = x              by LINV_SUBSET
        and (monoid_inj_image g f excluding f e).carrier
          = (IMAGE f G) DIFF {f e}                         by monoid_inj_image_def, excluding_def
          = IMAGE f (G DIFF {e})                           by IMAGE_DIFF
          = IMAGE f H                                      by notation
       By monoid_inj_image_def, excluding_def, this is to show:
          f (t x * t y) = f (t y * t x)                    where t = LINV f G
       Note ?a. x = f a /\ a IN H                          by IN_IMAGE
            ?b. y = f b /\ b IN H                          by IN_IMAGE
         f (t x * t y)
       = f (t (f a) * t (f b))                             by x = f a, y = f b
       = f (a * b)                                         by !y. t (f y) = y
       = f (b * a)                                         by commutativity condition
       = f (t (f b) * t (f a))                             by !y. t (f y) = y
       = f (t y * t x)                                     by y = f b, x = f a
*)
Theorem group_inj_image_excluding_abelian_group:
  !(g:'a group) (f:'a -> 'b) e.
      AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
      AbelianGroup (monoid_inj_image g f excluding f e)
Proof
  rw[AbelianGroup_def] >-
  rw[group_inj_image_excluding_group] >>
  qabbrev_tac `h = g excluding e` >>
  `h.carrier = G DIFF {e} /\ h.op = g.op /\ h.id = g.id` by rw[excluding_def, Abbr`h`] >>
  `H SUBSET G` by fs[] >>
  imp_res_tac LINV_SUBSET >>
  `(monoid_inj_image g f excluding f e).carrier = IMAGE f G DIFF {f e}` by rw[monoid_inj_image_def, excluding_def] >>
  `_ = IMAGE f H` by rw[IMAGE_DIFF] >>
  simp[monoid_inj_image_def, excluding_def] >>
  metis_tac[IN_IMAGE]
QED

(* Theorem: INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f) *)
(* Proof:
   Let s = IMAGE f G.
   Then BIJ f G s                              by INJ_IMAGE_BIJ_ALT
     so INJ f G s                              by BIJ_DEF

   By GroupHomo_def, monoid_inj_image_def, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x * y) = f (LINV f R (f x) * LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem group_inj_image_group_homo:
  !(g:'a group) f. INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f)
Proof
  rw[GroupHomo_def, monoid_inj_image_def] >>
  qabbrev_tac `s = IMAGE f G` >>
  `BIJ f G s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f G s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* ------------------------------------------------------------------------- *)
(* Subgroup Documentation                                                    *)
(* ------------------------------------------------------------------------- *)
(* Data type group:
   The generic symbol for group data is g.
   g.carrier = Carrier set of group, overloaded as G.
   g.op      = Binary operation of group, overloaded as *.
   g.id      = Identity element of group, overloaded as #e.
   g.exp     = Iteration of g.op (added by monoid)
   g.inv     = Inverse of g.op   (added by monoid)

   The generic symbol for a subgroup is h, denoted by h <= g.
   h.carrier = Carrier set of subgroup, overloaded as H.
   h.op      = Binary operation of subgroup, same as g.op = *.
   h.id      = Identity element of subgroup, same as g.id = #e.

   Overloading (# is temporary):
   h <= g       = Subgroup h g
   a * H        = coset g a H
   H * a        = right_coset g H a
#  K            = k.carrier
#  x o y        = h.op x y
   sgbINTER g   = subgroup_big_intersect g
*)
(* Definitions and Theorems (# are exported):

   Subgroup of a Group:
   Subgroup_def       |- !h g.  h <= g <=> Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )
   subgroup_property  |- !g h. h <= g ==> Group h /\ Group g /\ H SUBSET G /\
                        !x y. x IN H /\ y IN H ==> (h.op x y = x * y)
#  subgroup_element   |- !g h. h <= g ==> !z. z IN H ==> z IN G
   subgroup_homomorphism   |- !g h. h <= g ==> Group h /\ Group g /\ subgroup h g
   subgroup_carrier_subset |- !g h. h <= g ==> H SUBSET G
   subgroup_op        |- !g h. h <= g ==> (h.op = $* )
   subgroup_id        |- !g h. h <= g ==> (h.id = #e)
   subgroup_inv       |- !g h. h <= g ==> !x. x IN H ==> (h.inv x = |/ x)
   subgroup_has_groups|- !g h. h <= g ==> Group g /\ Group h
   subgroup_is_group  |- !g h. h <= g ==> Group h
   subgroup_is_submonoid   |- !g h. h <= g ==> h << g
   subgroup_exp       |- !g h. h <= g ==> !x. x IN H ==> !n. h.exp x n = x ** n
   subgroup_alt       |- !g. Group g ==> !h. h <= g <=> H <> {} /\ H SUBSET G /\
                            (h.op = $* ) /\ (h.id = #e) /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_thm       |- !g h. h <= g <=>
                               Group g /\ (h.op = $* ) /\ (h.id = #e) /\ H <> {} /\ H SUBSET G /\
                         !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_order     |- !g h. h <= g ==> !x. x IN H ==> (order h x = ord x)

   Subgroup Theorems:
   subgroup_refl      |- !g. Group g ==> g <= g
   subgroup_antisym   |- !g h. h <= g /\ g <= h ==> (h = g)
   subgroup_trans     |- !g h t. h <= t /\ t <= g ==> h <= g

   finite_subgroup_carrier_finite  |- !g. FiniteGroup g ==> !h. h <= g ==> FINITE H
   finite_subgroup_finite_group    |- !g. FiniteGroup g ==> !h. h <= g ==> FiniteGroup h
   abelian_subgroup_abelian        |- !g h. AbelianGroup g /\ h <= g ==> AbelianGroup h

   subgroup_groups            |- !g h. h <= g ==> Group h /\ Group g
   subgroup_property_all      |- !g h. h <= g ==>
                                       Group g /\ Group h /\ H <> {} /\ H SUBSET G /\
                                       (h.op = $* ) /\ (h.id = #e) /\
                                       (!x. x IN H ==> (h.inv x = |/ x)) /\
                                        !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_inv_closure       |- !g h. h <= g ==> !x y. x IN H /\ y IN H ==> x * |/ y IN H
   subgroup_carrier_nonempty  |- !g h. h <= g ==> H <> {}
   subgroup_eq_carrier        |- !g h. h <= g /\ (H = G) ==> (h = g)
   subgroup_eq                |- !g h1 h2. h1 <= g /\ h2 <= g ==> ((h1 = h2) <=> (h1.carrier = h2.carrier))

   Cosets, especially cosets of a subgroup:
   coset_def         |- !g X a. a * X = IMAGE (\z. a * z) X
   left_coset_def    |- !g X a. left_coset g X a = a * X
   right_coset_def   |- !g X a. X * a = IMAGE (\z. z * a) X
   coset_alt         |- !g a X. a * X = {a * z | z IN X}
   left_coset_alt    |- !g X a. left_coset g X a = {a * z | z IN X}
   right_coset_alt   |- !g X a. X * a = {z * a | z IN X}
   coset_property    |- !g a. Group g /\ a IN G ==> !X. X SUBSET G ==> a * X SUBSET G
   coset_empty       |- !g a. Group g /\ a IN G ==> (a * {} = {})
   coset_element     |- !g X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y)
   in_coset          |- !g X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y)
   group_coset_eq_itself      |- !g a. Group g /\ a IN G ==> (a * G = G)
   group_coset_is_permutation |- !g a. Group g /\ a IN G ==> (a * G = G)
   subgroup_coset_subset    |- !g h a x. h <= g /\ a IN G /\ x IN a * H ==> x IN G
   element_coset_property   |- !g X a. a IN G ==> !x. x IN X ==> a * x IN a * X
   subgroup_coset_nonempty  |- !h g. h <= g ==> !x. x IN G ==> x IN x * H
   subgroup_coset_eq        |- !g h. h <= g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> |/ y * x IN H)
   subgroup_to_coset_bij    |- !g h. h <= g ==> !a. a IN G ==> BIJ (\x. a * x) H (a * H)
   subgroup_coset_card      |- !g h. h <= g /\ FINITE H ==> !a. a IN G ==> (CARD (a * H) = CARD H)

   Lagrange's Theorem by Subgroups and Cosets:
   inCoset_def               |- !g h a b. inCoset g h a b <=> b IN a * H
   inCoset_refl              |- !g h. h <= g ==> !a. a IN G ==> inCoset g h a a
   inCoset_sym               |- !g h. h <= g ==> !a b. a IN G /\ b IN G /\
                                      inCoset g h a b ==> inCoset g h b a
   inCoset_trans             |- !g h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\
                                      inCoset g h a b /\ inCoset g h b c ==> inCoset g h a c
   inCoset_equiv_on_carrier  |- !g h. h <= g ==> inCoset g h equiv_on G
   CosetPartition_def        |- !g h. CosetPartition g h = partition (inCoset g h) G
   carrier_card_by_coset_partition  |- !g h.  h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (CosetPartition g h))
   coset_partition_element   |- !g h. h <= g ==> (!e. e IN CosetPartition g h <=> ?a. a IN G /\ (e = a * H))
   coset_partition_element_card |- !g h. h <= g /\ FINITE G ==> !e. e IN CosetPartition g h ==> (CARD e = CARD H)
   Lagrange_identity         |- !g h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (CosetPartition g h))
   coset_partition_card      |- !g h. h <= g /\ FINITE G ==> (CARD (CosetPartition g h) = CARD G DIV CARD H)
   Lagrange_thm              |- !g h. h <= g /\ FINITE G ==> (CARD H) divides (CARD G)

   Alternate proof without using inCoset:
   subgroup_coset_sym        |- !g h. h <= g ==> !a b. a IN G /\ b IN G /\ b IN a * H ==> a IN b * H
   subgroup_coset_trans      |- !g h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\
                                                    b IN a * H /\ c IN b * H ==> c IN a * H
   subgroup_incoset_equiv  |- !g h. h <= g ==> left_coset g H equiv_on G
   carrier_card_by_subgroup_coset_partition |- !g h. h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (partition (left_coset g H) G))
   subgroup_coset_partition_element |- !g h. h <= g ==> (!e. e IN partition (left_coset g H) G <=> ?a. a IN G /\ (e = a * H))
   subgroup_coset_card_partition_element |- !g h. h <= g /\ FINITE G ==> !e. e IN partition (left_coset g H) G ==> (CARD e = CARD H)
   Lagrange_identity_alt   |- !g h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (partition (left_coset g H) G))

   Useful Coset theorems:
   subgroup_coset_in_partition     |- !g h. h <= g ==>
                                      !x. x IN IMAGE (left_coset g H) G <=> x IN CosetPartition g h
   coset_partition_eq_coset_image  |- !g h. h <= g ==> (CosetPartition g h = IMAGE (left_coset g H) G)
   coset_id_eq_subgroup            |- !g h. h <= g ==> (#e * H = H)

   Conjugate of sets and subgroups:
   conjugate_def                   |- !g a s. conjugate g a s = {a * z * |/ a | z IN s}
   conjugate_subgroup_def          |- !h g a. conjugate_subgroup h g a =
                                              <|carrier := conjugate g a H; id := #e; op := $* |>
   conjugate_subgroup_group        |- !g h. h <= g ==> !a. a IN G ==> Group (conjugate_subgroup h g a)
   conjugate_subgroup_subgroup     |- !g h. h <= g ==> !a::(G). conjugate_subgroup h g a <= g
   subgroup_conjugate_subgroup_bij |- !g h. h <= g ==> !a. a IN G ==>
                                            BIJ (\z. a * z * |/ a) H (conjugate_subgroup h g a).carrier

   Subgroup Intersection:
   subgroup_intersect_has_inv   |- !g h k. h <= g /\ k <= g ==> !x. x IN H INTER K ==> |/ x IN H INTER K
   subgroup_intersect_group     |- !g h k. h <= g /\ k <= g ==> Group (h mINTER k)
   subgroup_intersect_inv       |- !g h k. h <= g /\ k <= g ==>
                                           !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)
   subgroup_intersect_property  |- !g h k. h <= g /\ k <= g ==>
                                           ((h mINTER k).carrier = H INTER K) /\
                                           (!x y. x IN H INTER K /\ y IN H INTER K ==>
                                            ((h mINTER k).op x y = x * y)) /\ ((h mINTER k).id = #e) /\
                                            !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)
   subgroup_intersect_subgroup  |- !g h k. h <= g /\ k <= g ==> (h mINTER k) <= g

   Subgroup Big Intersection:
   subgroup_big_intersect_def   |- !g. sgbINTER g =
                                       <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g}); op := $*; id := #e|>
   subgroup_big_intersect_property  |- !g. ((sgbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g})) /\
                                           (!x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==>
                                           ((sgbINTER g).op x y = x * y)) /\ ((sgbINTER g).id = #e)
   subgroup_big_intersect_element    |- !g x. x IN (sgbINTER g).carrier <=> !h. h <= g ==> x IN H
   subgroup_big_intersect_op_element |- !g x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==>
                                               (sgbINTER g).op x y IN (sgbINTER g).carrier
   subgroup_big_intersect_has_id     |- !g. (sgbINTER g).id IN (sgbINTER g).carrier
   subgroup_big_intersect_has_inv    |- !g x. x IN (sgbINTER g).carrier ==> |/ x IN (sgbINTER g).carrier
   subgroup_big_intersect_subset     |- !g. Group g ==> (sgbINTER g).carrier SUBSET G
   subgroup_big_intersect_group      |- !g. Group g ==> Group (sgbINTER g)
   subgroup_big_intersect_subgroup   |- !g. Group g ==> sgbINTER g <= g

   Subset Group:
   subset_group_def        |- !g s. subset_group g s = <|carrier := s; op := $*; id := #e|>
   subset_group_property   |- !g s. ((subset_group g s).carrier = s) /\
                                    ((subset_group g s).op = $* ) /\
                                    ((subset_group g s).id = #e)
   subset_group_exp        |- !g s x. x IN s ==> !n. (subset_group g s).exp x n = x ** n
   subset_group_order      |- !g s x. x IN s ==> (order (subset_group g s) x = ord x)
   subset_group_submonoid  |- !g s. Monoid g /\ #e IN s /\ s SUBSET G /\
                                    (!x y. x IN s /\ y IN s ==> x * y IN s) ==>
                                    subset_group g s << g
   subset_group_subgroup   |- !g s. Group g /\ s <> {} /\ s SUBSET G /\
                                    (!x y. x IN s /\ y IN s ==> x * |/ y IN s) ==>
                                    subset_group g s <= g
*)
(* ------------------------------------------------------------------------- *)
(* Subgroup of a Group.                                                      *)
(* ------------------------------------------------------------------------- *)

(* A Subgroup is a subset of a group that's a group itself, keeping op, id, inv. *)
val Subgroup_def = Define `
  Subgroup (h:'a group) (g:'a group) <=>
    Group h /\ Group g /\
    H SUBSET G /\ (h.op = g.op)
`;

(* Overload Subgroup *)
val _ = overload_on ("<=", ``Subgroup``);
(* already an infix symbol *)

(* Note: The requirement $o = $* is stronger than the following:
val _ = overload_on ("<<", ``\(h g):'a group. Group g /\ Group h /\ subgroup h g``);
Since subgroup h g is based on GroupHomo I g h, which only gives
!x y. x IN H /\ y IN H ==> (h.op x y = x * y))

This is not enough to satisfy monoid_component_equality,
hence cannot prove: h << g /\ g << h ==> h = g
*)

(*
val subgroup_property = save_thm(
  "subgroup_property",
  Subgroup_def
      |> SPEC_ALL
      |> REWRITE_RULE [ASSUME ``h:'a group <= g``]
      |> CONJUNCTS
      |> (fn thl => List.take(thl, 2) @ List.drop(thl, 3))
      |> LIST_CONJ
      |> DISCH_ALL
      |> Q.GEN `h` |> Q.GEN `g`);
val subgroup_property = |- !g h. h <= g ==> Group h /\ Group g /\ (h.op = $* )
*)

(* Theorem: properties of subgroup *)
(* Proof: Assume h <= g, then derive all consequences of definition *)
val subgroup_property = store_thm(
  "subgroup_property",
  ``!(g:'a group) h. h <= g ==> Group h /\ Group g /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))``,
  rw_tac std_ss[Subgroup_def]);

(* Theorem: elements in subgroup are also in group. *)
(* Proof: since subgroup carrier is a subset of group carrier. *)
val subgroup_element = store_thm(
  "subgroup_element",
  ``!(g:'a group) (h:'a group). h <= g ==> !z. z IN H ==> z IN G``,
  rw_tac std_ss[Subgroup_def, SUBSET_DEF]);

(* Theorem: A subgroup h of g implies identity is a homomorphism from h to g.
        or  h <= g ==> Group h /\ Group g /\ GroupHomo I h g  *)
(* Proof: check definitions. *)
val subgroup_homomorphism = store_thm(
  "subgroup_homomorphism",
  ``!(g:'a group) h. h <= g ==> Group h /\ Group g /\ subgroup h g``,
  rw_tac std_ss[Subgroup_def, subgroup_def, GroupHomo_def, SUBSET_DEF]);

(* original:
g `!(g:'a group) h. h <= g = Group h /\ Group g /\ subgroup h g`;
e (rw_tac std_ss[Subgroup_def, subgroup_def, GroupHomo_def, SUBSET_DEF, EQ_IMP_THM]);

The only-if part (<==) cannot be proved:
Note Subgroup_def uses h.op = g.op,
but subgroup_def uses homomorphism I, and so cannot show this for any x y.
*)

(* Theorem: h <= g ==> H SUBSET G *)
(* Proof: by Subgroup_def *)
val subgroup_carrier_subset = store_thm(
  "subgroup_carrier_subset",
  ``!(g:'a group) h. h <= g ==> H SUBSET G``,
  rw[Subgroup_def]);

(* Theorem: h <= g ==> (h.op = $* ) *)
(* Proof: by Subgroup_def *)
val subgroup_op = store_thm(
  "subgroup_op",
  ``!(g:'a group) h. h <= g ==> (h.op = g.op)``,
  rw[Subgroup_def]);

(* Theorem: h <= g ==> h.id = #e *)
(* Proof:
   Since h.id IN H    by group_id_element
     h.id * h.id
   = h.op h.id h.id   by Subgroup_def
   = h.id             by group_id_id
   But h.id IN G      by SUBSET_DEF
   hence h.id = #e    by group_id_fix
   or
   by group_homo_id and subgroup_homomorphism.
*)
val subgroup_id = store_thm(
  "subgroup_id",
  ``!g h. h <= g ==> (h.id = #e)``,
  rpt strip_tac >>
  `!x. I x = x` by rw[] >>
  metis_tac[group_homo_id, subgroup_homomorphism, subgroup_def]);

(* Theorem: h <= g ==> h.inv x = |/x *)
(* Proof: by group_homo_inv and subgroup_homomorphism. *)
val subgroup_inv = store_thm(
  "subgroup_inv",
  ``!g h. h <= g ==> !x. x IN H ==> (h.inv x = |/ x)``,
  rpt strip_tac >>
  `!x. I x = x` by rw[] >>
  metis_tac[group_homo_inv, subgroup_homomorphism, subgroup_def]);

(* Theorem: h <= g ==> Group g /\ Group h *)
(* Proof: by Subgroup_def *)
val subgroup_has_groups = store_thm(
  "subgroup_has_groups",
  ``!g:'a group h. h <= g ==> Group g /\ Group h``,
  metis_tac[Subgroup_def]);

(* Theorem: h <= g ==> Group h *)
(* Proof: by Subgroup_def *)
val subgroup_is_group = store_thm(
  "subgroup_is_group",
  ``!g:'a group h. h <= g ==> Group h``,
  metis_tac[Subgroup_def]);

(* Theorem: h <= g ==> h << g *)
(* Proof:
   Since h <= g ==> Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )  by Subgroup_def
   To satisfy Submonoid_def, need to show:
   (1) Group h ==> Monoid h, true by group_is_monoid
   (2) Group g ==> Monoid g, true by group_is_monoid
   (3) h <= g ==> h.id = #e, true by subgroup_id
*)
Theorem subgroup_is_submonoid:
  !(g:'a group) h. h <= g ==> h << g
Proof
  rpt strip_tac >>
  `Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )` by metis_tac[Subgroup_def] >>
  rw_tac std_ss[Submonoid_def] >| [
    rw[],
    rw[],
    rw[subgroup_id]
  ]
QED

(* Theorem: h <= g ==> !x. x IN H ==> !n. h.exp x n = x ** n *)
(* Proof: by subgroup_is_submonoid, submonoid_exp *)
val subgroup_exp = store_thm(
  "subgroup_exp",
  ``!(g:'a group) h. h <= g ==> !x. x IN H ==> !n. h.exp x n = x ** n``,
  rw_tac std_ss[subgroup_is_submonoid, submonoid_exp]);

(* Theorem: h <= g <=> H <> {} /\ H SUBSET G /\ h.op = g.op /\ h.id = #e /\ !x y IN H, x * |/ y IN H *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group h ==> H <> {}
       True by group_id_element.
   (2) h <= g ==> h.id = #e
       True by subgroup_id.
   (3) Group h /\ x IN H /\ y IN H ==> x * |/ y IN H
       Since y IN H ==> |/ y IN H     by group_inv_element, subgroup_inv
       Hence x * |/ y IN H            by group_op_element
   (4) H SUBSET G /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H ==> Group h
       Put y = x, x * |/ x = #e   IN H                  by group_rinv
       Put x = #e, y IN H ==> #e * |/ y = |/ y IN H     by group_lid
       x * y = x * |/ ( |/ y) IN H                      by group_inv_inv
       Verify by group_def_alt.
*)
val subgroup_alt = store_thm(
  "subgroup_alt",
  ``!g:'a group. Group g ==>
      !h. h <= g <=> (H <> {} /\ H SUBSET G /\ (h.op = g.op) /\ (h.id = #e) /\
                      !x y. x IN H /\ y IN H ==> x * |/ y IN H)``,
  rw[Subgroup_def, EQ_IMP_THM] >-
  metis_tac[group_id_element, MEMBER_NOT_EMPTY] >-
  rw[subgroup_id, Subgroup_def] >-
  metis_tac[group_inv_element, group_op_element, subgroup_inv, Subgroup_def] >>
  `?x. x IN H` by rw[MEMBER_NOT_EMPTY] >>
  `!x. x IN H ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `#e IN H` by metis_tac[group_rinv] >>
  `!y. y IN H ==> |/ y IN H` by metis_tac[group_lid, group_inv_element] >>
  `!x y. x IN H /\ y IN H ==> x * y IN H` by metis_tac[group_inv_inv] >>
  rw[group_def_alt] >-
  rw[group_assoc] >>
  metis_tac[group_linv]);

(* Theorem: h <= g <=>
       (Group g /\  (h.op = g.op) /\ (h.id = #e) /\
        H <> {} /\ H SUBSET G /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H) *)
(* Proof: by Subgroup_def, subgroup_alt *)
val subgroup_thm = store_thm(
  "subgroup_thm",
  ``!g:'a group h. h <= g <=>
       (Group g /\  (h.op = g.op) /\ (h.id = #e) /\
        H <> {} /\ H SUBSET G /\ !x y. x IN H /\ y IN H ==> x * |/ y IN H)``,
  metis_tac[subgroup_alt, Subgroup_def]);

(* Theorem: h <= g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note Group g /\ Group h /\ subgroup h g    by subgroup_homomorphism, h <= g
   Thus !x. x IN H ==> (order h x = ord x)    by subgroup_order_eqn
*)
val subgroup_order = store_thm(
  "subgroup_order",
  ``!g:'a group h. h <= g ==> !x. x IN H ==> (order h x = ord x)``,
  metis_tac[subgroup_homomorphism, subgroup_order_eqn]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Theorems                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: g <= g *)
(* Proof: by definition, this is to show:
   G SUBSET G, true by SUBSET_REFL.
*)
val subgroup_refl = store_thm(
  "subgroup_refl",
  ``!g:'a group. Group g ==> g <= g``,
  rw[Subgroup_def]);

(* Theorem: h <= g /\ g <= h ==> (h = g) *)
(* Proof:
   By monoid_component_equality, this is to show:
   (1) h <= g /\ g <= h ==> H = G
       By Subgroup_def, H SUBSET G /\ G SUBSET H,
       hence true by SUBSET_ANTISYM.
   (2) h <= g /\ g <= h ==> h.op = $*
       True by Subgroup_def.
   (3) h <= g /\ g <= h ==> h.id = #e
*)
val subgroup_antisym = store_thm(
  "subgroup_antisym",
  ``!(g:'a group) (h:'a group). h <= g /\ g <= h ==> (h = g)``,
  metis_tac[monoid_component_equality, Subgroup_def, SUBSET_ANTISYM, subgroup_id]);

(* Theorem: h <= t /\ t <= g ==> h <= g *)
(* Proof: by definition, this is to show:
   H SUBSET t.carrier /\ t.carrier SUBSET G ==> H SUBSET G
   True by SUBSET_TRANS.
*)
val subgroup_trans = store_thm(
  "subgroup_trans",
  ``!(g:'a group) (h:'a group) (t:'a group). h <= t /\ t <= g ==> h <= g``,
  rw[Subgroup_def] >>
  metis_tac[SUBSET_TRANS]);

(* Theorem: FiniteGroup g ==> !h. h <= g ==> FINITE H *)
(* Proof:
   Since FiniteGroup g
     ==> Group g /\ FINITE G               by FiniteGroup_def
     and h <= g ==> Group h /\ H SUBSET G  by Subgroup_def
   Hence FINITE H                          by SUBSET_FINITE
*)
val finite_subgroup_carrier_finite = store_thm(
  "finite_subgroup_carrier_finite",
  ``!g:'a group. FiniteGroup g ==> !h. h <= g ==> FINITE H``,
  metis_tac[FiniteGroup_def, Subgroup_def, SUBSET_FINITE]);

(* Theorem: FiniteGroup g ==> !h. h <= g ==> FiniteGroup h *)
(* Proof:
   Since FiniteGroup g
     ==> Group g /\ FINITE G               by FiniteGroup_def
     and h <= g ==> Group h /\ H SUBSET G  by Subgroup_def
   Hence FINITE H                          by SUBSET_FINITE
    thus FiniteGroup h                     by FiniteGroup_def
*)
val finite_subgroup_finite_group = store_thm(
  "finite_subgroup_finite_group",
  ``!g:'a group. FiniteGroup g ==> !h. h <= g ==> FiniteGroup h``,
  metis_tac[FiniteGroup_def, Subgroup_def, SUBSET_FINITE]);

(* Theorem: AbelianGroup g /\ h <= g ==> AbelianGroup h *)
(* Proof:
   Note AbelianGroup g
    <=> Group g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)  by AbelianGroup_def
   Also h <= g
    <=> Group h /\ Group g /\ H SUBSET G /\ (h.op = $* )       by Subgroup_def
   With Group h              by above
    and !x y. x IN H /\ y IN H
    ==> x IN G /\ y IN G              by SUBSET_DEF
    ==> x * y = y * x                 by above, commutativity
    ==> h.op x y = h.op y x           by above, h.op = $*
   Thus AbelianGroup h                by AbelianGroup_def
*)
val abelian_subgroup_abelian = store_thm(
  "abelian_subgroup_abelian",
  ``!(g:'a group) h. AbelianGroup g /\ h <= g ==> AbelianGroup h``,
  rw_tac std_ss[AbelianGroup_def, Subgroup_def, SUBSET_DEF]);

(* Theorem: h <= g ==> Group h /\ Group g *)
(* Proof: by subgroup_property *)
val subgroup_groups = store_thm(
  "subgroup_groups",
  ``!(g:'a group) h. h <= g ==> Group h /\ Group g``,
  metis_tac[subgroup_property]);

(* Theorem: h <= g ==> Group g /\ Group h /\ H <> {} /\ H SUBSET G /\ (h.op = $* ) /\ (h.id = #e) /\
                       (!x. x IN H ==> (h.inv x = |/ x)) /\
                       (!x y. x IN H /\ y IN H ==> x * ( |/ y) IN H) *)
(* Proof: by subgroup_property, subgroup_alt, subgroup_inv *)
val subgroup_property_all = store_thm(
  "subgroup_property_all",
  ``!(g:'a group) h. h <= g ==> Group g /\ Group h /\
    H <> {} /\ H SUBSET G /\ (h.op = g.op ) /\ (h.id = #e) /\
    (!x. x IN H ==> (h.inv x = |/ x)) /\
    (!x y. x IN H /\ y IN H ==> x * ( |/ y) IN H)``,
  metis_tac[subgroup_property, subgroup_inv, subgroup_alt]);

(* Theorem: h <= g ==> !x y. x IN H /\ y IN H ==> x * |/ y IN H *)
(* Proof: by subgroup_property_all *)
val subgroup_inv_closure = store_thm(
  "subgroup_inv_closure",
  ``!(g:'a group) h. h <= g ==> !x y. x IN H /\ y IN H ==> x * ( |/ y) IN H``,
  rw[subgroup_property_all]);

(* Theorem: h <= g ==> H <> {} *)
(* Proof: by subgroup_property_all, or
     h <= g ==> Group h     by Subgroup_def
            ==> H <> {}     by group_carrier_nonempty
*)
val subgroup_carrier_nonempty = store_thm(
  "subgroup_carrier_nonempty",
  ``!(g:'a group) h. h <= g ==> H <> {}``,
  rw[Subgroup_def, group_carrier_nonempty]);

(* Theorem: h <= g /\ (H = G) ==> (h = g) *)
(* Proof:
   By subgroup_antisym, this is to show:
   Note Group h /\ Group g         by subgroup_groups
   Note (1) G <> {}, true          by group_carrier_nonempty
        (2) $* = h.op, true        by subgroup_alt
        (3) #e = h.id, true        by subgroup_alt
        (4) x IN G /\ y IN G ==> h.op x (h.inv y) IN G,
            This is true           by subgroup_alt, subgroup_inv, group_op_element
   Thus g <= h.
   With given h <= g, h = g        by subgroup_antisym
*)
val subgroup_eq_carrier = store_thm(
  "subgroup_eq_carrier",
  ``!(g:'a group) h. h <= g /\ (H = G) ==> (h = g)``,
  rpt strip_tac >>
  (irule subgroup_antisym >> rpt conj_tac) >| [
    `Group h /\ Group g` by metis_tac[subgroup_groups] >>
    rw[subgroup_alt] >-
    rw[group_carrier_nonempty] >-
    metis_tac[subgroup_alt] >-
    metis_tac[subgroup_alt] >>
    metis_tac[subgroup_alt, subgroup_inv, group_op_element],
    rw[]
  ]);

(* Theorem: h1 <= g /\ h2 <= g ==> ((h1 = h2) <=> (h1.carrier = h2.carrier)) *)
(* Proof:
   Note h1 <= g ==> h1.op = g.op /\ h1.id = #e    by subgroup_op, subgroup_id
    and h2 <= g ==> h2.op = g.op /\ h2.id = #e    by subgroup_op, subgroup_id
   Thus (h1 = h2) <=> (h1.carrier = h2.carrier)   by monoid_component_equality
*)
val subgroup_eq = store_thm(
  "subgroup_eq",
  ``!g:'a group. !h1 h2. h1 <= g /\ h2 <= g ==> ((h1 = h2) <=> (h1.carrier = h2.carrier))``,
  metis_tac[subgroup_op, subgroup_id, monoid_component_equality]);

(* ------------------------------------------------------------------------- *)
(* Cosets, especially cosets of a subgroup.                                  *)
(* ------------------------------------------------------------------------- *)

(* Define (left) coset of subgroup with an element a. *)
val coset_def = Define `
  coset (g:'a group) a X = IMAGE (\z. a * z) X
`;

(* val _ = export_rewrites ["coset_def"]; *)

(* Define left coset of subgroup with an element a. *)
val left_coset_def = Define `
  left_coset (g:'a group) X a = coset g a X
`;

(* Define right coset of subgroup with an element a. *)
val right_coset_def = Define `
  right_coset (g:'a group) X a = IMAGE (\z. z * a) X
`;

(* set overloading after all above defintions. *)
val _ = overload_on ("*", ``coset g``);
val _ = overload_on ("*", ``right_coset g``);

(* Derive theorems. *)
val coset_alt = save_thm("coset_alt",
    coset_def |> SIMP_RULE bool_ss [IMAGE_DEF]);
(* val coset_alt = |- !g a X. a * X = {a * z | z IN X}: thm *)

val left_coset_alt = save_thm("left_coset_alt",
    left_coset_def |> REWRITE_RULE [coset_alt]);
(* val left_coset_alt = |- !g X a. left_coset g X a = {a * z | z IN X}: thm *)

val right_coset_alt = save_thm("right_coset_alt",
    right_coset_def |> SIMP_RULE bool_ss [IMAGE_DEF]);
(* val right_coset_alt = |- !g X a. X * a = {z * a | z IN X}: thm *)

(* Theorem: a * X SUBSET G *)
(* Proof: by definition. *)
val coset_property = store_thm(
  "coset_property",
  ``!(g:'a group) a. Group g /\ a IN G ==> !X. X SUBSET G ==> a * X SUBSET G``,
  rw[coset_def, SUBSET_DEF] >>
  metis_tac[group_op_element]);

(* Theorem: a * {} = {} *)
(* Proof: by definition. *)
val coset_empty = store_thm(
  "coset_empty",
  ``!(g:'a group) a. Group g /\ a IN G ==> (a * {} = {})``,
  rw[coset_def]);

(* Theorem: For x IN a * X <=> ?y IN X /\ x = a * y *)
(* Proof: by coset_def, x is IN IMAGE.
   Essentially this is to prove:
     z IN X <=> ?y. y IN X /\ (a * z = a * y)
   Take y = z.
*)
val coset_element = store_thm(
  "coset_element",
  ``!(g:'a group) X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y)``,
  rw[coset_def] >>
  metis_tac[]);

(* Theorem alias *)
val in_coset = save_thm("in_coset", coset_element);
(*
val in_coset = |- !g X a. a IN G ==> !x. x IN a * X <=> ?y. y IN X /\ (x = a * y): thm
*)

(* Theorem: Group g, a IN G ==> a * G = G *)
(* Proof:
   By closure property of g.op.
   This is to prove:
   (1) a * z IN G, true by group_op_element.
   (2) ?z. (x = a * z) /\ z IN G, true by z = |/a * x, from group_rsolve.
*)
val group_coset_eq_itself = store_thm(
  "group_coset_eq_itself",
  ``!(g:'a group) a. Group g /\ a IN G ==> (a * G = G)``,
  rw[coset_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >>
  qexists_tac `|/a * x` >>
  rw[group_linv_assoc]);

(* Theorem: [Cosets of a group are permutations]
            (a * G) = G *)
(* Proof:
   Essentially this is to prove:
   (1) a IN G /\ x IN G ==> a*x IN G, true by group_op_element
   (2) a IN G /\ x IN G ==> ?z. (x = a * z) /\ z IN G, true by group_rsolve
*)
val group_coset_is_permutation = store_thm(
  "group_coset_is_permutation",
  ``!(g:'a group) a. Group g /\ a IN G ==> (a * G = G)``,
  rw[coset_def, EXTENSION, EQ_IMP_THM] >| [
    rw_tac std_ss[group_op_element] >>
    rw[],
    `|/ a * x IN G` by rw[] >>
    metis_tac[group_rsolve]
  ]);

(* Theorem: Group g, h <= g, a IN G /\ x IN a * H ==> x IN G *)
(* Proof:
   Coset contains all  x = a*z  where a IN G and z IN H, so x IN G by group_op_element.
*)
val subgroup_coset_subset = store_thm(
  "subgroup_coset_subset",
  ``!(g:'a group) (h:'a group) a x. h <= g /\ a IN G /\ x IN a * H ==> x IN G``,
  rw_tac std_ss[coset_def, Subgroup_def, SUBSET_DEF, IMAGE_DEF, GSPECIFICATION] >>
  rw_tac std_ss[group_op_element]);

(* Theorem: For all x IN H, a * x IN a * H. *)
(* Proof: by coset definition
   or to prove: ?z. (a * x = a * z) /\ z IN H. Take z = x.
*)
val element_coset_property = store_thm(
  "element_coset_property",
  ``!(g:'a group) X a. a IN G ==> !x. x IN X ==> a * x IN a * X``,
  rw[coset_def]);

(* Theorem: For h <= g, x IN x * H *)
(* Proof:
   Since #e IN H   by subgroup_id
   and x * #e = x  by group_rid
   Essentially this is to prove:
   (1) ?z. (x = x * z) /\ z IN H, true by z = #e.
*)
val subgroup_coset_nonempty = store_thm(
  "subgroup_coset_nonempty",
  ``!(g:'a group) h. h <= g ==> !x. x IN G ==> x IN x * H``,
  rw[coset_def] >>
  metis_tac[subgroup_id, group_rid, group_id_element, Subgroup_def]);

(* eliminate "group" from default simpset *)
(* val groupSS = diminish_srw_ss ["group"]; *)
(* val mySS = diminish_srw_ss ["subgroup"]; *)

(* Theorem: For h <= g, y IN x * H ==> ?z IN H /\ x = y * z *)
(* Proof:
   This is to prove:
   x * z IN G /\ z IN H ==> ?z'. z' IN H /\ (x = x * z * z')
   Just take z' = |/z.
*)
val subgroup_coset_relate = prove(
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G /\ y IN x * H ==> ?z. z IN H /\ (x = y * z)``,
  rw[coset_def] >>
  metis_tac[subgroup_inv, group_rinv_assoc, subgroup_element, group_inv_element, Subgroup_def]);

(* Theorem: For h <= g, |/y * x in H ==> x * H = y * H. *)
(* Proof:
   Essentially this is to prove:
   (1) |/ y * x IN H /\ z IN H ==> ?z'. (x * z = y * z') /\ z' IN H
       Solving, z' = |/y * (x * z) = ( |/y * x) * z, in H by group_op_element.
   (2) |/ y * x IN H /\ z IN H ==> ?z'. (y * z = x * z') /\ z' IN H
       Solving, z' = |/x * (y * z) = ( |/x * y) * z, and |/( |/y * x) = |/x * y IN H.
*)
val subgroup_coset_eq1 = prove(
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G /\ ( |/y * x) IN H ==> (x * H = y * H)``,
  rpt strip_tac >>
  `Group h /\ Group g /\ !x y. x IN H /\ y IN H ==> (h.op x y = x * y)` by metis_tac[Subgroup_def] >>
  rw[coset_def, EXTENSION, EQ_IMP_THM] >| [
    `z IN G` by metis_tac[subgroup_element] >>
    `y * ( |/y * x * z) = x * z` by rw[group_assoc, group_linv_assoc] >>
    metis_tac[group_op_element],
    `z IN G` by metis_tac[subgroup_element] >>
    `x * ( |/x * y * z) = y * z` by rw[group_assoc, group_linv_assoc] >>
    `|/( |/y * x) = |/x * y` by rw[group_inv_op] >>
    metis_tac[subgroup_inv, group_inv_element, group_op_element]
  ]);

(* Theorem: For h <= g, x * H = y * H ==> |/y * x in H. *)
(* Proof:   Since y IN y * H, always, by subgroup_coset_nonempty.
   we have y IN x * H, since the cosets are equal.
   hence ?z IN H /\  x = y * z  by subgroup_coset_relate.
   Solving, z = |/y * x, and z IN H.
*)
val subgroup_coset_eq2 = prove(
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G /\ (x * H = y * H) ==> ( |/y * x) IN H``,
  rpt strip_tac >>
  `y IN x * H` by rw_tac std_ss[subgroup_coset_nonempty] >>
  `?z. z IN H /\ (x = y * z)` by rw_tac std_ss[subgroup_coset_relate] >>
  metis_tac[group_rsolve, Subgroup_def, subgroup_element]);

(* Theorem: For h <= g, x * H = y * H iff |/y * x in H *)
(* Proof:
   By subgroup_coset_eq1 and subgroup_coset_eq2.
*)
val subgroup_coset_eq = store_thm(
  "subgroup_coset_eq",
  ``!(g:'a group) h. h <= g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> |/y * x IN H)``,
  metis_tac[subgroup_coset_eq1, subgroup_coset_eq2]);

(* Theorem: There is a bijection between subgroup and its cosets. *)
(* Proof:
   Essentially this is to prove:
   (1) x IN H ==> a * x IN a * H
       True by element_coset_property.
   (2) x IN H /\ x' IN H /\ a * x = a * x' ==> x = x'
       True by group_lcancel.
   (3) same as (1)
   (4) x IN a * H ==> ?x'. x' IN H /\ (a * x' = x)
       True by coset_element.
*)
val subgroup_to_coset_bij = store_thm(
  "subgroup_to_coset_bij",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> BIJ (\x. a * x) H (a * H)``,
  rw_tac std_ss[BIJ_DEF, SURJ_DEF, INJ_DEF, element_coset_property] >| [
    metis_tac[group_lcancel, subgroup_element, Subgroup_def],
    metis_tac[coset_element]
  ]);

(* Theorem: All cosets of subgroup are of the same size as the subgroup *)
(* Proof:
   Due to BIJ (\x. a*x) H (a * H), and sets are FINITE.
*)
(* Note: An infinite group can have a finite subgroup, e.g. the units of complex multiplication. *)
val subgroup_coset_card = store_thm(
  "subgroup_coset_card",
  ``!(g:'a group) h. h <= g /\ FINITE H  ==> !a. a IN G ==> (CARD (a * H) = CARD H)``,
  rpt strip_tac >>
  `BIJ (\x. a * x) H (a * H)` by rw_tac std_ss[subgroup_to_coset_bij] >>
  `FINITE (a * H)` by rw[coset_def] >>
  metis_tac[FINITE_BIJ_CARD_EQ]);

(* ------------------------------------------------------------------------- *)
(* Lagrange's Theorem by Subgroups and Cosets                                *)
(* ------------------------------------------------------------------------- *)

(* From subgroup_coset_card:
   `!g h a. Group g /\ h <= g /\ a IN G /\ FINITE H ==> (CARD (a * H) = CARD (H))`

   This can be used directly to prove Lagrange's Theorem for subgroup.
*)

(* Theorem: (Lagrange Theorem) For FINITE Group g, size of subgroup divides size of group. *)
(* Proof:
   For the action g.op h G

     CARD G
   = SIGMA CARD (TargetPartition g.op h G)  by CARD_TARGET_BY_PARTITION
   = (CARD H) * CARD (TargetPartition g.op h G)
           by SIGMA_CARD_CONSTANT, and (CARD e = CARD H) from CARD_subgroup_partition

   Hence (CARD H) divides (CARD G).
*)

(* Define b ~ a  when  b IN (a * H) *)
val inCoset_def = Define `
  inCoset (g:'a group) (h:'a group) a b <=> b IN (a * H)
`;

(* Theorem: inCoset is Reflexive:
            h <= g /\ a IN G ==> inCoset g h a a *)
(* Proof:
   Follows from subgroup_coset_nonempty.
*)
val inCoset_refl = store_thm(
  "inCoset_refl",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> inCoset g h a a``,
  rw_tac std_ss[inCoset_def, subgroup_coset_nonempty]);

(* Theorem: inCoset is Symmetric:
            h <= g /\ a IN G /\ b IN G ==> (inCoset g h a b ==> inCoset g h b a) *)
(* Proof:
       inCoset g h a b
   ==> b IN (a * H)          by definition
   ==> ?z in H. b = a * z    by coset_element
   ==> |/z in H              by h <= g, group_inv_element
   ==> b * ( |/z) = (a * z) * ( |/z)
                  = a        by group_rinv_assoc
   The result follows        by element_coset_property:
   !x. x IN H ==> b * x IN b * H  -- take x = |/z.
*)
val inCoset_sym = store_thm(
  "inCoset_sym",
  ``!(g:'a group) h. h <= g ==> !a b. a IN G /\ b IN G /\ inCoset g h a b ==> inCoset g h b a``,
  rw_tac std_ss[inCoset_def] >>
  `Group h/\ Group g /\ !x. x IN H ==> x IN G` by metis_tac[Subgroup_def, subgroup_element] >>
  `?z. z IN H /\ (b = a * z)` by rw_tac std_ss[GSYM coset_element] >>
  `|/z IN H` by metis_tac[subgroup_inv, group_inv_element] >>
  metis_tac[element_coset_property, group_rinv_assoc]);

(* Theorem: inCoset is Transitive:
            h <= g /\ a IN G /\ b IN G /\ c IN G
            ==> (inCoset g h a b /\ inCoset g h b c ==> inCoset g h a c) *)
(* Proof:
       inCoset g h a b
   ==> b IN (a * H)          by definition
   ==> ?y in H. b = a * y    by coset_element

       inCoset g h b c
   ==> c IN (b * H)          by definition
   ==> ?z in H. c = b * z    by coset_element

   Hence  c = b * z
            = (a * y)* z
            = a * (y * z)    by group_assoc
   Since y * z in H          by group_op_element
   Hence  c IN (a * H), the result follows from element_coset_property.
*)
val inCoset_trans = store_thm(
  "inCoset_trans",
  ``!(g:'a group) h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\ inCoset g h a b /\ inCoset g h b c ==> inCoset g h a c``,
  rw_tac std_ss[inCoset_def] >>
  `Group h /\ Group g /\ !x. x IN H ==> x IN G` by metis_tac[Subgroup_def, subgroup_element] >>
  `?y. y IN H /\ (b = a * y) /\ ?z. z IN H /\ (c = b * z)` by rw_tac std_ss[GSYM coset_element] >>
  `c = a * (y * z)` by rw[group_assoc] >>
  metis_tac[element_coset_property, group_op_element, subgroup_property]);

(* Theorem: inCoset is an equivalence relation.
            Group g /\ h <= g ==> (inCoset g h) is an equivalent relation on G. *)
(* Proof:
   By inCoset_refl, inCoset_sym, and inCoset_trans.
*)
val inCoset_equiv_on_carrier = store_thm(
  "inCoset_equiv_on_carrier",
  ``!(g:'a group) h. h <= g ==> inCoset g h equiv_on G``,
  rw_tac std_ss[equiv_on_def] >>
  metis_tac[inCoset_refl, inCoset_sym, inCoset_trans]);

(* Define coset partitions of G by inCoset g h. *)
val CosetPartition_def = Define `
  CosetPartition g h = partition (inCoset g h) G
`;

(* Theorem: For FINITE Group g, h <= g ==>
            CARD G = SUM of CARD partitions in (CosetPartition g h) *)
(* Proof:
   Apply partition_CARD
    |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
*)
val carrier_card_by_coset_partition = store_thm(
  "carrier_card_by_coset_partition",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (CosetPartition g h))``,
  rw_tac std_ss[CosetPartition_def, inCoset_equiv_on_carrier, partition_CARD]);

(* Theorem: Elements in CosetPartition are cosets of some a In G *)
(* Proof:
   By definition, this is to show:
   h <= g /\ x IN G ==> ?a. a IN G /\ ({y | y IN G /\ y IN x * H} = a * H)
   Let a = x, then need to show: {y | y IN G /\ y IN x * H} = x * H
   Since y IN x * H ==> ?z. z IN H /\ (y = x * z)
   so need to show: x IN G /\ z IN G ==> y IN G, which is true by group_op_element.
*)
val coset_partition_element = store_thm(
  "coset_partition_element",
  ``!(g:'a group) h. h <= g ==> (!e. e IN CosetPartition g h <=> ?a. a IN G /\ (e = a * H))``,
  rpt strip_tac >>
  `!x z. x IN G /\ z IN H ==> x * z IN G` by metis_tac[group_op_element, Subgroup_def, subgroup_element] >>
  rw[CosetPartition_def, inCoset_def, partition_def, EQ_IMP_THM,
     coset_def, EXTENSION] >>
  metis_tac[]);

(* Theorem: For FINITE group, CARD element in CosetPartiton = CARD subgroup. *)
(* Proof:
   By coset_partition_element and subgroup_coset_card
*)
val coset_partition_element_card = store_thm(
  "coset_partition_element_card",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> !e. e IN CosetPartition g h ==> (CARD e = CARD H)``,
  metis_tac[coset_partition_element, subgroup_coset_card, Subgroup_def, SUBSET_FINITE]);

(* Theorem: (Lagrange Identity)
            For FINITE Group g and subgroup h,
            (size of group) = (size of subgroup) * (size of coset partition). *)
(* Proof:
   Since
   !e. e IN CosetPartition g h ==> (CARD e = CARD H)  by coset_partition_element_card

   CARD G
   = SIGMA CARD (CosetPartition g h)     by carrier_card_by_coset_partition
   = CARD H * CARD (CosetPartition g h)  by SIGMA_CARD_CONSTANT
*)
val Lagrange_identity = store_thm(
  "Lagrange_identity",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (CosetPartition g h))``,
  rpt strip_tac >>
  `FINITE (CosetPartition g h)` by metis_tac[CosetPartition_def, inCoset_equiv_on_carrier, FINITE_partition] >>
  metis_tac[carrier_card_by_coset_partition, SIGMA_CARD_CONSTANT, coset_partition_element_card]);

(* Theorem: (Coset Partition size)
            For FINITE Group g, size of coset partition = (size of group) div (size of subgroup). *)
(* Proof:
   By Lagrange_identity and MULT_DIV.
*)
val coset_partition_card = store_thm(
  "coset_partition_card",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD (CosetPartition g h) = CARD G DIV CARD H)``,
  rpt strip_tac >>
  `Group h /\ FINITE H` by metis_tac[Subgroup_def, SUBSET_FINITE] >>
  `0 < CARD H` by metis_tac[group_id_element, MEMBER_NOT_EMPTY, CARD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[Lagrange_identity, MULT_DIV, MULT_SYM]);

(* Theorem: (Lagrange Theorem)
            For FINITE Group g, size of subgroup divides size of group. *)
(* Proof:
   By Lagrange_identity and divides_def.
*)
val Lagrange_thm = store_thm(
  "Lagrange_thm",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD H) divides (CARD G)``,
  metis_tac[Lagrange_identity, MULT_SYM, dividesTheory.divides_def]);

(* ------------------------------------------------------------------------- *)
(* Alternate proof without using inCoset.                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Subgroup Coset membership is Symmetric:
            Group g /\ h <= g /\ a IN G /\ b IN G
            ==> b IN a * H ==> a IN b * H
   Proof:
       b IN (a * H)
   ==> ?z in H. b = a * z    by coset_element
   ==> |/z in H              by h <= g, group_inv_element
   ==> b * ( |/z) = (a * z) * ( |/z) = a
                             by group_rinv_assoc
   The result follows by element_coset_property:
   !x. x IN H ==> b * x IN b * H  -- take x = |/z.
*)
val subgroup_coset_sym = store_thm(
  "subgroup_coset_sym",
  ``!(g:'a group) h. h <= g ==> !a b. a IN G /\ b IN G /\ b IN (a * H) ==> a IN (b * H)``,
  rpt strip_tac >>
  `?z. z IN H /\ (b = a * z)` by rw_tac std_ss[GSYM coset_element] >>
  `Group g /\ Group h` by metis_tac[Subgroup_def] >>
  `|/ z IN H` by metis_tac[subgroup_inv, group_inv_element] >>
  `z IN G /\ |/ z IN G` by metis_tac[subgroup_element] >>
  `b * |/ z = a` by rw_tac std_ss[group_rinv_assoc] >>
  metis_tac[element_coset_property]);

(* Theorem: Subgroup Coset membership is Transitive:
            Group g /\ h <= g /\ a IN G /\ b IN G /\ c IN G
            ==> b IN (a * H) /\ c IN (b * H) ==> c IN (a * H)
   Proof:
       b IN (a * H)          by definition
   ==> ?y in H. b = a * y    by coset_element
       c IN (b * H)          by definition
   ==> ?z in H. c = b * z    by coset_element

   Hence  c = b * z
            = (a * y)* z
            = a * (y * z)    by group_assoc
   Since y * z in H          by group_op_element
   Hence  c IN (a * H), the result follows from element_coset_property.
*)
val subgroup_coset_trans = store_thm(
  "subgroup_coset_trans",
  ``!(g:'a group) h. h <= g ==> !a b c. a IN G /\ b IN G /\ c IN G /\ b IN (a * H) /\ c IN (b * H) ==> c IN (a * H)``,
  rpt strip_tac >>
  `?y. y IN H /\ (b = a * y) /\ ?z. z IN H /\ (c = b * z)` by rw_tac std_ss[GSYM coset_element] >>
  `Group g /\ Group h /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))` by metis_tac[subgroup_property] >>
  `y IN G /\ z IN G` by metis_tac[subgroup_element] >>
  `c = a * (y * z)` by rw_tac std_ss[group_assoc] >>
  `y * z IN H` by metis_tac[group_op_element] >>
  rw_tac std_ss[element_coset_property]);

(* Theorem: inCoset is an equivalence relation.
            h <= g ==> (inCoset g h) is an equivalent relation on G. *)
(* Proof:
   By subgroup_coset_nonempty, subgroup_coset_sym, and subgroup_coset_trans.
*)
val subgroup_incoset_equiv = store_thm(
  "subgroup_incoset_equiv",
  ``!(g:'a group) h. h <= g ==> (left_coset g H) equiv_on G``,
  rw_tac std_ss[left_coset_def, equiv_on_def] >| [
    metis_tac[subgroup_coset_nonempty, SPECIFICATION],
    metis_tac[subgroup_coset_sym, SPECIFICATION],
    metis_tac[subgroup_coset_trans, SPECIFICATION]
  ]);

(* Theorem: For FINITE Group g, h <= g ==>
            CARD G = SUM of CARD partitions by (left_coset g H) *)
(* Proof:
   Apply partition_CARD
    |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
*)
val carrier_card_by_subgroup_coset_partition = store_thm(
  "carrier_card_by_subgroup_coset_partition",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = SIGMA CARD (partition (left_coset g H) G))``,
  rw_tac std_ss[subgroup_incoset_equiv, partition_CARD]);

(* Theorem: Elements in coset partition are cosets of some a In G *)
(* Proof:
   If-part: h <= g /\ e IN partition (left_coset g H) G ==> ?a. a IN G /\ (e = a * H)
      Since there is x such that x IN G /\ e = {y | y IN G /\ x * H y}  by partition_def
      Let a = x, need to show x * H = {y | y IN G /\ x * H y}
      This is true by SPECIFICATION.
   Only-if part: case: h <= g /\ a IN G ==> a * H IN partition (left_coset g H) G
      This is to show: ?x. x IN G /\ (a * H = {y | y IN G /\ x * H y})
      Let x = a, need to show a * H = {y | y IN G /\ a * H y}
      This is true by SPECIFICATION.
*)
val subgroup_coset_partition_element = store_thm(
  "subgroup_coset_partition_element",
  ``!(g:'a group) h. h <= g ==> (!e. e IN (partition (left_coset g H) G) <=> ?a. a IN G /\ (e = a * H))``,
  rpt strip_tac >>
  `!x z. x IN G /\ z IN H ==> x * z IN G` by metis_tac[Subgroup_def, SUBSET_DEF, group_op_element] >>
  rw[partition_def, EQ_IMP_THM, left_coset_def, coset_def, EXTENSION] >>
  metis_tac[]);

(* Theorem: For FINITE group, CARD element in subgroup coset partiton = CARD subgroup. *)
(* Proof:
   By subgroup_coset_partition_element and subgroup_coset_card
*)
val subgroup_coset_card_partition_element = store_thm(
  "subgroup_coset_card_partition_element",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> !e. e IN (partition (left_coset g H) G) ==> (CARD e = CARD H)``,
  rpt strip_tac >>
  `?a. a IN G /\ (e = a * H)` by rw_tac std_ss[GSYM subgroup_coset_partition_element] >>
  `FINITE H` by metis_tac[Subgroup_def, SUBSET_FINITE] >>
  metis_tac[subgroup_coset_card]);

(* Theorem: (Lagrange Identity)
            For FINITE Group g and subgroup h,
            (size of group) = (size of subgroup) * (size of coset partition). *)
(* Proof:
   Since
   !e. e IN coset partition g h ==> (CARD e = CARD H)  by subgroup_coset_card_partition_element

   CARD G
   = SIGMA CARD (CosetPartition g h)   by carrier_card_by_subgroup_coset_partition
   = CARD H * CARD (CosetPartition g h)  by SIGMA_CARD_CONSTANT
*)
val Lagrange_identity_alt = store_thm(
  "Lagrange_identity_alt",
  ``!(g:'a group) h. h <= g /\ FINITE G ==> (CARD G = CARD H * CARD (partition (left_coset g H) G))``,
  metis_tac[carrier_card_by_subgroup_coset_partition, subgroup_coset_card_partition_element,
             SIGMA_CARD_CONSTANT, FINITE_partition]);

(* ------------------------------------------------------------------------- *)
(* Useful Coset theorems.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: h <= g /\ x IN IMAGE (left_coset g H) G <=> x IN CosetPartition g h *)
(* Proof:
       x IN IMAGE (left_coset g H) G
   <=> ?y. y IN G /\ y = (left_coset g H) x   by IN_IMAGE
   <=> ?y. y IN G /\ y = x * H                by left_coset_def
   <=> x IN CosetPartition g h                   by coset_partition_element
*)
val subgroup_coset_in_partition = store_thm(
  "subgroup_coset_in_partition",
  ``!g h:'a group. h <= g ==> !x. x IN IMAGE (left_coset g H) G <=> x IN CosetPartition g h``,
  rw_tac std_ss[IN_IMAGE, left_coset_def, coset_partition_element] >>
  metis_tac[]);

(* Theorem: CosetPartition g h = IMAGE (left_coset g H) G *)
(* Proof:
      !e. e IN CosetPartition g h
   <=> ?a. a IN G /\ (e = a * H)      by coset_partition_element
   <=> e IN IMAGE (left_coset g H) G  by IN_IMAGE
*)
val coset_partition_eq_coset_image = store_thm(
  "coset_partition_eq_coset_image",
  ``!(g:'a group) h. h <= g ==> (CosetPartition g h = IMAGE (left_coset g H) G)``,
  rw[Once EXTENSION] >>
  metis_tac[left_coset_def, coset_partition_element]);

(* Theorem: #e * H = H *)
(* Proof:
     #e * H
   = IMAGE (\z. #e * z) H   by coset_def
   = IMAGE (\z. z) H        by group_lid, subgroup_id
   = H                      by IMAGE_ID
*)
Theorem coset_id_eq_subgroup:
  !(g:'a group) h. h <= g ==> (#e * H = H)
Proof
  rw[coset_def, EXTENSION] >>
  metis_tac[subgroup_property, subgroup_id, group_lid, group_id_element]
QED

(* Michael's proof *)
Theorem IMAGE_ID_lemma[local]:
  (!x. x IN s ==> (f x = x)) ==> (IMAGE f s = s)
Proof rw[EXTENSION] >> metis_tac[]
QED

Theorem coset_id_eq_subgroup[allow_rebind]:
  !(g:'a group) h. h <= g ==> (#e * H = H)
Proof
  srw_tac[SatisfySimps.SATISFY_ss]
         [subgroup_property, subgroup_element, IMAGE_ID_lemma, coset_def]
QED

(* Rework of proof from outline:
   For the in-line IMAGE_ID', universally qualify all parameters :
   !f s. (!x. x IN s ==> (f x = x)) ==> (IMAGE f s = s)
*)
Theorem coset_id_eq_subgroup[allow_rebind]:
  !(g:'a group) h. h <= g ==> (#e * H = H)
Proof
  rpt strip_tac >>
  ‘!f s. (!x. x IN s ==> (f x = x)) ==> (IMAGE f s = s)’
    by (rw[EXTENSION] >> metis_tac[]) >>
  ‘!x. x IN H ==> ((\z. #e * z) x = x)’
    by metis_tac[subgroup_property, subgroup_element, group_lid] >>
  full_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss)[coset_def]
QED

(* ------------------------------------------------------------------------- *)
(* Conjugate of sets and subgroups                                           *)
(* ------------------------------------------------------------------------- *)

(* Conjugate of a set s by a group element a in G is the set {a * z * |/a | z in s}. *)
val conjugate_def = Define `
  conjugate (g:'a group) (a: 'a) (s: 'a -> bool) = { a * z * |/a | z IN s}
`;

(* Conjugate of subgroup h <= g by a in G is the set {a * z * |/a | z in H}. *)
val conjugate_subgroup_def = Define `
  conjugate_subgroup (h:'a group) (g:'a group) a : 'a group =
      <| carrier := conjugate g a H;
              id := #e;
              op := g.op
       |>
`;
(* > val conjugate_subgroup_def =
  |- !h g a. conjugate_subgroup h g a = <|carrier := conjugate g a H; id := #e; op := $* |> : thm
*)

(*
- type_of ``conjugate_subgroup h g a``;
> val it = ``:'a group`` : hol_type
*)

(* Theorem: Group g, h <= g, a in G ==> Group (conjugate_subgroup h g a) *)
(* Proof:
   Closure: (a * z * |/a) * (a * z' * |/ a)
          = a * z * ( |/ a * a) * z' * |/ a
          = a * (z * z') * |/ a, and z * z' IN H.
   Associativity: inherits from group associativity
   Identity: #e in (conjugate_subgroup h g a) since #e IN H and a * #e * |/ a = #e.
   Inverse: |/ (a * z * |/a)
          = |/( |/a) * ( |/ z) * |/a
          = a * ( |/z) * |/a, and |/z IN H.
*)
val conjugate_subgroup_group = store_thm(
  "conjugate_subgroup_group",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> Group (conjugate_subgroup h g a)``,
  rpt strip_tac >>
  `Group h /\ Group g /\ !z. z IN H ==> z IN G` by metis_tac[Subgroup_def, subgroup_element] >>
  `#e IN H` by metis_tac[subgroup_id, group_id_element] >>
  `|/a IN G` by rw_tac std_ss[group_inv_element] >>
  `!p q. p IN G /\ q IN G ==> (a * p * |/ a * (a * q * |/ a) = a * (p * q) * |/a)` by
  (rpt strip_tac >>
  `a * p IN G /\ q * |/a IN G` by rw_tac std_ss[group_op_element] >>
  `a * p * |/ a * (a * q * |/ a) = a * p * ( |/ a * a * (q * |/ a))` by rw_tac std_ss[group_assoc, group_op_element] >>
  `_ = a * p * (q * |/a)` by rw_tac std_ss[group_linv, group_lid] >>
  rw_tac std_ss[group_assoc, group_op_element]) >>
  rw_tac std_ss[conjugate_subgroup_def, conjugate_def, group_def_alt, RES_FORALL_THM, RES_EXISTS_THM, GSPECIFICATION] >| [
    `z * z' IN H` by metis_tac[group_op_element, subgroup_property] >>
    metis_tac[],
    `!x y. x IN H /\ y IN H ==> (h.op x y = x * y)` by metis_tac[group_op_element, subgroup_property] >>
    `a * z' * |/ a * (a * z'' * |/ a) * (a * z''' * |/ a) = a * (z' * z'') * |/ a * (a * z''' * |/ a)` by rw_tac std_ss[] >>
    `_ = a * ((z' * z'') * z''') * |/ a` by rw_tac std_ss[group_op_element] >>
    `_ = a * (z' * (z'' * z''')) * |/ a` by rw_tac std_ss[group_assoc] >>
    `_ = a * z' * |/ a * (a * (z'' * z''') * |/a)` by rw_tac std_ss[group_op_element] >>
    rw_tac std_ss[],
    metis_tac[group_rid, group_rinv],
    rw_tac std_ss[group_lid, group_op_element],
    `|/z IN H` by metis_tac[subgroup_inv, group_inv_element] >>
    metis_tac[group_linv, group_rid, group_rinv]
  ]);

(* Theorem: Group g, h <= g, a in G ==> (conjugate_subgroup h g a) <= g *)
(* Proof:
   By conjugate_subgroup_group, and (conjugate_subgroup h g a).carrier SUBSET G.
*)
val conjugate_subgroup_subgroup = store_thm(
  "conjugate_subgroup_subgroup",
  ``!(g:'a group) h. h <= g ==> !a::G. (conjugate_subgroup h g a) <= g``,
  rw_tac std_ss[RES_FORALL_THM] >>
  `Group (conjugate_subgroup h g a)` by rw_tac std_ss[conjugate_subgroup_group] >>
  `Group g` by metis_tac[Subgroup_def] >>
  rw_tac std_ss[conjugate_subgroup_def, conjugate_def, Subgroup_def, SUBSET_DEF, GSPECIFICATION] >>
  metis_tac[group_inv_element, group_op_element, subgroup_element]);

(* Theorem: [Bijection between subgroup and its conjugate]
            Group g, h <= g, a in G ==>
            BIJ (\z. a * z * |/ a) H (conjugate_subgroup h g a).carrier *)
(* Proof:
   Essentially this is to prove:
   (1) z IN H ==> ?z'. (a * z * |/ a = a * z' * |/ a) /\ z' IN H
       True by taking z' = z.
   (2) z IN H /\ z' IN H /\ a * z * |/ a = a * z' * |/ a ==> z = z'
       True by group left/right cancellations.
   (3) z IN H ==> ?z'. (a * z * |/ a = a * z' * |/ a) /\ z' IN H
       True by taking z' = z.
   (4) z IN H ==> ?z'. z' IN H /\ (a * z' * |/ a = a * z * |/ a)
       True by taking z' = z.
*)
val subgroup_conjugate_subgroup_bij = store_thm(
  "subgroup_conjugate_subgroup_bij",
  ``!(g:'a group) h. h <= g ==> !a. a IN G ==> BIJ (\z. a * z * |/ a) H (conjugate_subgroup h g a).carrier``,
  rw_tac std_ss[conjugate_subgroup_def, conjugate_def, BIJ_DEF, INJ_DEF, SURJ_DEF, GSPECIFICATION] >| [
    metis_tac[],
    `Group g /\ z IN G /\ z' IN G` by metis_tac[subgroup_property, subgroup_element] >>
    `|/a IN G /\ a * z IN G /\ a * z' IN G` by rw_tac std_ss[group_inv_element, group_op_element] >>
    metis_tac[group_lcancel, group_rcancel],
    metis_tac[],
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Intersection                                                     *)
(* ------------------------------------------------------------------------- *)

(* Use K to denote k.carrier *)
val _ = temp_overload_on ("K", ``(k:'a group).carrier``);
(* Use o to denote h.op *)
val _ = temp_overload_on ("o", ``(h:'a group).op``);
(* Use #i to denote h.id *)
val _ = temp_overload_on ("#i", ``(h:'a monoid).id``);

(* Theorem: h <= g /\ k <= g ==> !x. x IN H INTER K ==> |/ x IN H INTER K *)
(* Proof:
   Since h <= g ==> Group h /\ Group g /\ h << g    by subgroup_homomorphism, subgroup_is_submonoid
     and k <= g ==> Group k /\ Group g /\ k << g    by subgroup_homomorphism, subgroup_is_submonoid
   x IN H INTER K ==> x IN H and x IN K             by IN_INTER
   Since x IN H, by h <= g, h.inv x = |/ x          by subgroup_inv
    also x IN K, by k <= g, k.inv x = |/ x          by subgroup_inv
    Therefore |/ x IN H INTER K                     by IN_INTER, group_inv_element
*)
val subgroup_intersect_has_inv = store_thm(
  "subgroup_intersect_has_inv",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> !x. x IN H INTER K ==> |/ x IN H INTER K``,
  rpt strip_tac >>
  `h << g /\ k << g` by rw[subgroup_is_submonoid] >>
  `x IN H /\ x IN K` by metis_tac[IN_INTER] >>
  `(h.inv x = |/ x) /\ (k.inv x = |/ x)` by rw[subgroup_inv] >>
  `Group h /\ Group k` by metis_tac[subgroup_homomorphism] >>
  metis_tac[IN_INTER, group_inv_element]);

(* Theorem: h <= g /\ k <= g ==> Group (h mINTER k) *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid (h mINTER k)
       Since h <= g ==> h << g     by subgroup_is_submonoid
         and k <= g ==> k << g     by subgroup_is_submonoid
       Hence Monoid (h mINTER k)   by submonoid_intersect_monoid
   (2) monoid_invertibles (h mINTER k) = (h mINTER k).carrier
       By monoid_invertibles_def, this is to show:
       ?y. y IN (h mINTER k).carrier /\
        ((h mINTER k).op x y = (h mINTER k).id) /\ ((h mINTER k).op y x = (h mINTER k).id)
       Since h <= g ==> h << g     by subgroup_is_submonoid
         and k <= g ==> k << g     by subgroup_is_submonoid
       By submonoid_intersect_property, this is to show:
       ?y. y IN H INTER K /\ (x * y = #e) /\ (y * x = #e)
       Let y = |/ x.
       Then |/ x IN H INTER K            by subgroup_intersect_has_inv
       Since h <= g ==> Group g          by subgroup_homomorphism
         and x IN H and x IN K           by IN_INTER
             ==> x IN G                  by subgroup_element
       Hence x * y = #e and y * x = #e   by group_id
*)
val subgroup_intersect_group = store_thm(
  "subgroup_intersect_group",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> Group (h mINTER k)``,
  rpt strip_tac >>
  `h << g /\ k << g` by rw[subgroup_is_submonoid] >>
  `Group h /\ Group k /\ Group g` by metis_tac[subgroup_homomorphism] >>
  rw[Group_def] >| [
    metis_tac[submonoid_intersect_monoid],
    rw[monoid_invertibles_def, EXTENSION, EQ_IMP_THM] >>
    pop_assum mp_tac >>
    `x IN H INTER K ==> ?y. y IN H INTER K /\ (x * y = #e) /\ (y * x = #e)` suffices_by metis_tac[submonoid_intersect_property] >>
    rpt strip_tac >>
    `|/ x IN H INTER K` by metis_tac[subgroup_intersect_has_inv] >>
    qexists_tac `|/ x` >>
    `x IN G` by metis_tac[IN_INTER, subgroup_element] >>
    rw[]
  ]);

(* Theorem: h <= g /\ k <= g ==> !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x) *)
(* Proof:
   Since h <= g ==> Group h /\ Group g     by subgroup_homomorphism
     and h <= g ==> h << g                 by subgroup_is_submonoid
     and k <= g ==> k << g                 by subgroup_is_submonoid
   Hence by submonoid_intersect_property,
        (h mINTER k).carrier = H INTER K
        !x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)
        (h mINTER k).id = #e
   Now, h <= g /\ k <= g ==> Group (h mINTER k)   by subgroup_intersect_group
   and  |/ x IN H INTER K                         by subgroup_intersect_has_inv
   also x IN G /\ |/ x IN G                       by IN_INTER, subgroup_element
   Therefore (h mINTER k).op ( |/ x) x = (h mINTER k).id     by group_linv
   Hence (h mINTER k).inv x = |/ x                by group_linv_unique
*)
val subgroup_intersect_inv = store_thm(
  "subgroup_intersect_inv",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> !x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)``,
  rpt strip_tac >>
  `Group g /\ Group h` by metis_tac[subgroup_homomorphism] >>
  `h << g /\ k << g` by rw[subgroup_is_submonoid] >>
  `(h mINTER k).carrier = H INTER K` by metis_tac[submonoid_intersect_property] >>
  `!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)` by metis_tac[submonoid_intersect_property] >>
  `(h mINTER k).id = #e` by metis_tac[submonoid_intersect_property] >>
  `Group (h mINTER k)` by metis_tac[subgroup_intersect_group] >>
  `|/ x IN H INTER K` by rw[subgroup_intersect_has_inv] >>
  `x IN G /\ |/ x IN G` by metis_tac[IN_INTER, subgroup_element] >>
  metis_tac[group_linv, group_linv_unique]);

(* Theorem: properties of subgroup_intersect:
   h <= g /\ k <= g ==>
     ((h mINTER k).carrier = H INTER K) /\
     (!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)) /\
     ((h mINTER k).id = #e) /\
     (!x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x)) *)
(* Proof: by subgroup_is_submonoid, submonoid_intersect_property, subgroup_intersect_inv. *)
val subgroup_intersect_property = store_thm(
  "subgroup_intersect_property",
  ``!(g:'a group) h k. h <= g /\ k <= g ==>
     ((h mINTER k).carrier = H INTER K) /\
     (!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)) /\
     ((h mINTER k).id = #e) /\
     (!x. x IN H INTER K ==> ((h mINTER k).inv x = |/ x))``,
  metis_tac[subgroup_is_submonoid, submonoid_intersect_property, subgroup_intersect_inv]);

(* Theorem: h <= g /\ k <= g ==> (h mINTER k) <= g *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (h mINTER k), true by subgroup_intersect_group.
   (2) Group g, true by subgroup_homomorphism.
   (3) (h mINTER k).carrier SUBSET G
       Since (h mINTER k).carrier = H INTER K   by subgroup_intersect_property
         and (H INTER K) SUBSET H               by INTER_SUBSET
         and h <= g ==> H SUBSET G              by Subgroup_def
       Hence (h mINTER k).carrier SUBSET G      by SUBSET_TRANS
   (4) (h mINTER k).op = $*
       By monoid_intersect_def, this is to show: $o = $*
       which is true by Subgroup_def.
*)
val subgroup_intersect_subgroup = store_thm(
  "subgroup_intersect_subgroup",
  ``!(g:'a group) h k. h <= g /\ k <= g ==> (h mINTER k) <= g``,
  rpt strip_tac >>
  rw[Subgroup_def] >| [
    metis_tac[subgroup_intersect_group],
    metis_tac[subgroup_homomorphism],
    `(h mINTER k).carrier = H INTER K` by metis_tac[subgroup_intersect_property] >>
    `(H INTER K) SUBSET H` by rw[INTER_SUBSET] >>
    `H SUBSET G` by metis_tac[Subgroup_def] >>
    metis_tac[SUBSET_TRANS],
    rw[monoid_intersect_def] >>
    metis_tac[Subgroup_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Big Intersection                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define intersection of subgroups of a group *)
val subgroup_big_intersect_def = Define `
   subgroup_big_intersect (g:'a group) =
      <| carrier := BIGINTER (IMAGE (\h. H) {h | h <= g});
              op := $*; (* g.op *)
              id := #e  (* g.id *)
       |>
`;

val _ = overload_on ("sgbINTER", ``subgroup_big_intersect``);
(*
> subgroup_big_intersect_def;
val it = |- !g. sgbINTER g =
     <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g}); op := $*; id := #e|>: thm
*)

(* Theorem: ((sgbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g})) /\
   (!x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> ((sgbINTER g).op x y = x * y)) /\
   ((sgbINTER g).id = #e) *)
(* Proof: by subgroup_big_intersect_def. *)
val subgroup_big_intersect_property = store_thm(
  "subgroup_big_intersect_property",
  ``!g:'a group. ((sgbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g})) /\
   (!x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> ((sgbINTER g).op x y = x * y)) /\
   ((sgbINTER g).id = #e)``,
  rw[subgroup_big_intersect_def]);

(* Theorem: x IN (sgbINTER g).carrier <=> (!h. h <= g ==> x IN H) *)
(* Proof:
       x IN (sgbINTER g).carrier
   <=> x IN BIGINTER (IMAGE (\h. H) {h | h <= g})          by subgroup_big_intersect_def
   <=> !P. P IN (IMAGE (\h. H) {h | h <= g}) ==> x IN P    by IN_BIGINTER
   <=> !P. ?h. (P = H) /\ h IN {h | h <= g}) ==> x IN P    by IN_IMAGE
   <=> !P. ?h. (P = H) /\ h <= g) ==> x IN P               by GSPECIFICATION
   <=> !h. h <= g ==> x IN H
*)
val subgroup_big_intersect_element = store_thm(
  "subgroup_big_intersect_element",
  ``!g:'a group. !x. x IN (sgbINTER g).carrier <=> (!h. h <= g ==> x IN H)``,
  rw[subgroup_big_intersect_def] >>
  metis_tac[]);

(* Theorem: x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> (sgbINTER g).op x y IN (sgbINTER g).carrier *)
(* Proof:
   Since x IN (sgbINTER g).carrier, !h. h <= g ==> x IN H   by subgroup_big_intersect_element
    also y IN (sgbINTER g).carrier, !h. h <= g ==> y IN H   by subgroup_big_intersect_element
     Now !h. h <= g ==> x o y IN H                          by Subgroup_def, group_op_element
                    ==> x * y IN H                          by subgroup_property
     Now, (sgbINTER g).op x y = x * y                       by subgroup_big_intersect_property
     Hence (sgbINTER g).op x y IN (sgbINTER g).carrier      by subgroup_big_intersect_element
*)
val subgroup_big_intersect_op_element = store_thm(
  "subgroup_big_intersect_op_element",
  ``!g:'a group. !x y. x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==>
                     (sgbINTER g).op x y IN (sgbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h <= g ==> x IN H /\ y IN H` by metis_tac[subgroup_big_intersect_element] >>
  `!h. h <= g ==> x * y IN H` by metis_tac[Subgroup_def, group_op_element, subgroup_property] >>
  `(sgbINTER g).op x y = x * y` by rw[subgroup_big_intersect_property] >>
  metis_tac[subgroup_big_intersect_element]);

(* Theorem: (sgbINTER g).id IN (sgbINTER g).carrier *)
(* Proof:
   !h. h <= g ==> #i = #e                               by subgroup_id
   !h. h <= g ==> #i IN H                               by Subgroup_def, group_id_element
   Now (smbINTER g).id = #e                             by subgroup_big_intersect_property
   Hence !h. h <= g ==> (sgbINTER g).id IN H            by above
      or (sgbINTER g).id IN (sgbINTER g).carrier        by subgroup_big_intersect_element
*)
val subgroup_big_intersect_has_id = store_thm(
  "subgroup_big_intersect_has_id",
  ``!g:'a group. (sgbINTER g).id IN (sgbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h <= g ==> (#i = #e)` by rw[subgroup_id] >>
  `!h. h <= g ==> #i IN H` by rw[Subgroup_def] >>
  `(sgbINTER g).id = #e` by metis_tac[subgroup_big_intersect_property] >>
  metis_tac[subgroup_big_intersect_element]);

(* Theorem: !x. x IN (sgbINTER g).carrier ==> |/ x IN (sgbINTER g).carrier *)
(* Proof:
   Since x IN (sgbINTER g).carrier,
         !h. h <= g ==> x IN H             by subgroup_big_intersect_element
    also !h. h <= g ==> (h.inv x = |/ x)   by subgroup_inv, x IN H.
     Now !h. h <= g ==> Group h            by Subgroup_def
      so !h. h <= g ==> |/ x IN H          by group_inv_element
   Hence |/ x IN (sgbINTER g).carrier      by subgroup_big_intersect_element
*)
val subgroup_big_intersect_has_inv = store_thm(
  "subgroup_big_intersect_has_inv",
  ``!g:'a group. !x. x IN (sgbINTER g).carrier ==> |/ x IN (sgbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h <= g ==> x IN H` by metis_tac[subgroup_big_intersect_element] >>
  `!h. h <= g ==> (h.inv x = |/ x)` by rw[subgroup_inv] >>
  `!h. h <= g ==> Group h` by rw[Subgroup_def] >>
  `!h. h <= g ==> |/ x IN H` by metis_tac[group_inv_element] >>
  metis_tac[subgroup_big_intersect_element]);

(* Theorem: Group g ==> (sgbINTER g).carrier SUBSET G *)
(* Proof:
   By subgroup_big_intersect_def, this is to show:
   Group g ==> BIGINTER (IMAGE (\h. H) {h | h <= g}) SUBSET G
   Let P = IMAGE (\h. H) {h | h <= g}.
   Since g <= g                    by subgroup_refl
      so G IN P                    by IN_IMAGE, definition of P.
    Thus P <> {}                   by MEMBER_NOT_EMPTY.
     Now h <= g ==> H SUBSET G     by Subgroup_def
   Hence P SUBSET G                by BIGINTER_SUBSET
*)
val subgroup_big_intersect_subset = store_thm(
  "subgroup_big_intersect_subset",
  ``!g:'a group. Group g ==> (sgbINTER g).carrier SUBSET G``,
  rw[subgroup_big_intersect_def] >>
  qabbrev_tac `P = IMAGE (\h. H) {h | h <= g}` >>
  (`!x. x IN P <=> ?h. (H = x) /\ h <= g` by (rw[Abbr`P`] >> metis_tac[])) >>
  `g <= g` by rw[subgroup_refl] >>
  `P <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `!h:'a group. h <= g ==> H SUBSET G` by rw[Subgroup_def] >>
  metis_tac[BIGINTER_SUBSET]);

(* Theorem: Group g ==> Group (smbINTER g) *)
(* Proof:
   Group g ==> (sgbINTER g).carrier SUBSET G                by subgroup_big_intersect_subset
   By Monoid_def, this is to show:
   (1) x IN (sgbINTER g).carrier /\ y IN (sgbINTER g).carrier ==> (sgbINTER g).op x y IN (sgbINTER g).carrier
       True by subgroup_big_intersect_op_element.
   (2) (sgbINTER g).op ((sgbINTER g).op x y) z = (sgbINTER g).op x ((sgbINTER g).op y z)
       Since (sgbINTER g).op x y IN (sgbINTER g).carrier    by subgroup_big_intersect_op_element
         and (sgbINTER g).op y z IN (sgbINTER g).carrier    by subgroup_big_intersect_op_element
       So this is to show: (x * y) * z = x * (y * z)        by subgroup_big_intersect_property
       Since x IN G, y IN G and z IN G                      by SUBSET_DEF
       This follows by group_assoc.
   (3) (sgbINTER g).id IN (sgbINTER g).carrier
       This is true by subgroup_big_intersect_has_id.
   (4) x IN (sgbINTER g).carrier ==> (sgbINTER g).op (sgbINTER g).id x = x
       Since (sgbINTER g).id IN (sgbINTER g).carrier   by subgroup_big_intersect_op_element
         and (sgbINTER g).id = #e                      by subgroup_big_intersect_property
        also x IN G                                    by SUBSET_DEF
         (sgbINTER g).op (sgbINTER g).id x
       = #e * x                                        by subgroup_big_intersect_property
       = x                                             by group_id
   (5) x IN (sgbINTER g).carrier ==>
       ?y. y IN (sgbINTER g).carrier /\ ((sgbINTER g).op y x = (sgbINTER g).id)
       Since |/ x IN (sgbINTER g).carrier              by subgroup_big_intersect_has_inv
         and (sgbINTER g).id IN (sgbINTER g).carrier   by subgroup_big_intersect_op_element
         and (sgbINTER g).id = #e                      by subgroup_big_intersect_property
        also x IN G                                    by SUBSET_DEF
        Let y = |/ x, then y IN (sgbINTER g).carrier,
         (sgbINTER g).op y x
       = |/ x * x                                      by subgroup_big_intersect_property
       = #e                                            by group_linv
*)
val subgroup_big_intersect_group = store_thm(
  "subgroup_big_intersect_group",
  ``!g:'a group. Group g ==> Group (sgbINTER g)``,
  rpt strip_tac >>
  `(sgbINTER g).carrier SUBSET G` by rw[subgroup_big_intersect_subset] >>
  rw_tac std_ss[group_def_alt] >| [
    metis_tac[subgroup_big_intersect_op_element],
    `(sgbINTER g).op x y IN (sgbINTER g).carrier` by metis_tac[subgroup_big_intersect_op_element] >>
    `(sgbINTER g).op y z IN (sgbINTER g).carrier` by metis_tac[subgroup_big_intersect_op_element] >>
    `(x * y) * z = x * (y * z)` suffices_by rw[subgroup_big_intersect_property] >>
    `x IN G /\ y IN G /\ z IN G` by metis_tac[SUBSET_DEF] >>
    rw[group_assoc],
    metis_tac[subgroup_big_intersect_has_id],
    `(sgbINTER g).id = #e` by rw[subgroup_big_intersect_property] >>
    `(sgbINTER g).id IN (sgbINTER g).carrier` by metis_tac[subgroup_big_intersect_has_id] >>
    `#e * x = x` suffices_by rw[subgroup_big_intersect_property] >>
    `x IN G` by metis_tac[SUBSET_DEF] >>
    rw[],
    `|/ x IN (sgbINTER g).carrier` by rw[subgroup_big_intersect_has_inv] >>
    `(sgbINTER g).id = #e` by rw[subgroup_big_intersect_property] >>
    `(sgbINTER g).id IN (sgbINTER g).carrier` by rw[subgroup_big_intersect_has_id] >>
    qexists_tac `|/ x` >>
    `|/ x * x = #e` suffices_by rw[subgroup_big_intersect_property] >>
    `x IN G` by metis_tac[SUBSET_DEF] >>
    rw[]
  ]);

(* Theorem: Group g ==> (sgbINTER g) <= g *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (sgbINTER g)
       True by subgroup_big_intersect_group.
   (2) (sgbINTER g).carrier SUBSET G
       True by subgroup_big_intersect_subset.
   (3) (sgbINTER g).op = $*
       True by subgroup_big_intersect_def
*)
val subgroup_big_intersect_subgroup = store_thm(
  "subgroup_big_intersect_subgroup",
  ``!g:'a group. Group g ==> (sgbINTER g) <= g``,
  rw_tac std_ss[Subgroup_def] >| [
    rw[subgroup_big_intersect_group],
    rw[subgroup_big_intersect_subset],
    rw[subgroup_big_intersect_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subset Group (to be subgroup)                                             *)
(* ------------------------------------------------------------------------- *)

(* Define the subset group: takes a subset and gives a group candidate *)
val subset_group_def = Define`
    subset_group (g:'a group) (s:'a -> bool) =
    <| carrier := s;
            op := g.op;
            id := g.id
     |>
`;
(* val subset_group_def = |- !g s. subset_group g s = <|carrier := s; op := $*; id := #e|>: thm *)

(* Theorem: properties of subset_group *)
(* Proof: by subset_group_def *)
val subset_group_property = store_thm(
  "subset_group_property",
  ``!(g:'a group) s.
     ((subset_group g s).carrier = s) /\
     ((subset_group g s).op = g.op) /\
     ((subset_group g s).id = #e)``,
  rw_tac std_ss[subset_group_def]);

(* Theorem: x IN s ==> !n. (subset_group g s).exp x n = x ** n *)
(* Proof:
   By induction on n.
   Base: (subset_group g s).exp x 0 = x ** 0
          (subset_group g s).exp x 0
        = (subset_group g s).id        by group_exp_0
        = #0                           by subset_group_property
        = x ** 0                       by group_exp_0
   Step: x IN s /\ (subset_group g s).exp x n = x ** n ==>
         (subset_group g s).exp x (SUC n) = x ** SUC n
          (subset_group g s).exp x (SUC n)
        = (subset_group g s).op x ((subset_group g s).exp x n)   by group_exp_SUC
        = x * ((subset_group g s).exp x n)                       by subset_group_property
        = x * (x ** n)                 by induction hypothesis
        = x ** SUC n                   by group_exp_SUC
*)
val subset_group_exp = store_thm(
  "subset_group_exp",
  ``!(g:'a group) s. !x. x IN s ==> !n. (subset_group g s).exp x n = x ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[subset_group_property] >>
  rw[subset_group_property]);

(* Theorem: x IN s ==> (order (subset_group g s) x = order g x) *)
(* Proof:
   Note (subset_group g s).exp x k = x ** k      by subset_group_exp
    and (subset_group g s).id = #e               by subset_group_property
   Thus order (subset_group g s) x = order g x   by order_def, period_def
*)
val subset_group_order = store_thm(
  "subset_group_order",
  ``!(g:'a group) s. !x. x IN s ==> (order (subset_group g s) x = order g x)``,
  rw[order_def, period_def, subset_group_property, subset_group_exp]);

(* Theorem: Monoid g /\ #e IN s /\ (s SUBSET G) /\
           (!x y. x IN s /\ y IN s ==> x * y IN s)  ==> (subset_group g s) << g *)
(* Proof:
   Let h = subset_group g s
   Then H = s          by subset_group_property
   Thus h << g         by subset_group_property, submonoid_alt
*)
val subset_group_submonoid = store_thm(
  "subset_group_submonoid",
  ``!(g:'a monoid) s. Monoid g /\ #e IN s /\ (s SUBSET G) /\
           (!x y. x IN s /\ y IN s ==> x * y IN s)  ==> (subset_group g s) << g``,
  rw[submonoid_alt, subset_group_property]);

(* Theorem: Group g /\ s <> {} /\ (s SUBSET G) /\
            (!x y. x IN s /\ y IN s ==> x * ( |/ y) IN s) ==> (subset_group g s) <= g *)
(* Proof:
   Let h = subset_group g s
   Then H = s          by subset_group_property
   Thus h <= g         by subset_group_property, subgroup_alt
*)
val subset_group_subgroup = store_thm(
  "subset_group_subgroup",
  ``!(g:'a group) s. Group g /\ s <> {} /\ (s SUBSET G) /\
   (!x y. x IN s /\ y IN s ==> x * |/ y IN s) ==> (subset_group g s) <= g``,
  rw[subgroup_alt, subset_group_property]);

(* ------------------------------------------------------------------------- *)
(* Quotient Group Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   x / y    = group_div g x y
   h << g   = normal_subgroup h g
   h == g   = group_equiv g h
   x o y    = coset_op g h x y
   g / h    = quotient_group g h
*)
(* Definitions and Theorems (# are exported):

   Group element division:
#  group_div_def      |- !g x y. x / y = x * |/ y
#  group_div_element  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> x / y IN G
#  group_div_cancel   |- !g. Group g ==> !x. x IN G ==> (x / x = #e)
   group_div_pair     |- !g. Group g ==> !x1 y1 x2 y2. x1 IN G /\ y1 IN G /\ x2 IN G /\ y2 IN G ==>
                         (x1 * y1 / (x2 * y2) = x1 * (y1 / y2) / x1 * (x1 / x2))
   group_div_lsame    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (z * x / (z * y) = z * (x / y) / z)
   group_div_rsame    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * z / (y * z) = x / y)

   Normal Subgroup:
   normal_subgroup_def       |- !h g. h << g <=> h <= g /\ !a z. a IN G /\ z IN H ==> a * z / a IN H
   normal_subgroup_subgroup  |- !h g. h << g ==> h <= g
   normal_subgroup_property  |- !h g. h << g ==> !a z. a IN G /\ z IN H ==> a * z / a IN H
   normal_subgroup_groups    |- !g h. h << g ==> h <= g /\ Group h /\ Group g
   normal_subgroup_refl      |- !g. Group g ==> g << g
   normal_subgroup_antisym   |- !g h. h << g /\ g << h ==> (h = g)
   normal_subgroup_alt       |- !g h. h << g <=> h <= g /\ !a. a IN G ==> (a * H = H * a)
   normal_subgroup_coset_eq  |- !g h. h << g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> x / y IN H)

   Equivalence induced by Normal Subgroup:
   group_equiv_def               |- !g h x y. x == y <=> x / y IN H
   group_normal_equiv_reflexive  |- !g h. h << g ==> !z. z IN G ==> z == z
   group_normal_equiv_symmetric  |- !g h. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> y == x)
   group_normal_equiv_transitive |- !g h. h << g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> x == y /\ y == z ==> x == z
   group_normal_equiv            |- !g h. h << g ==> $== equiv_on G
   group_normal_equiv_property   |- !h g. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> x IN y * H)

   Binary operation for cosets:
   cogen_def       |- !g h e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G /\ (e = cogen g h e * H)
   cogen_element   |- !h g e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G
   coset_cogen_property   |- !h g e. h <= g /\ e IN CosetPartition g h ==> (e = cogen g h e * H)
   coset_op_def           |- !g h x y. x o y = cogen g h x * cogen g h y * H
   cogen_of_subgroup      |- !g h. h <= g ==> (cogen g h H * H = H
   cogen_coset_element    |- !g h. h <= g ==> !x. x IN G ==> cogen g h (x * H) IN G
   normal_cogen_property  |- !g h. h << g ==> !x. x IN G ==> x / cogen g h (x * H) IN H
   normal_coset_property1 |- !g h. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * b * H = a * b * H)
   normal_coset_property2 |- !g h. h << g ==> !a b. a IN G /\ b IN G ==> (a * cogen g h (b * H) * H = a * b * H)
   normal_coset_property  |- !g h. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * cogen g h (b * H) * H = a * b * H)

   Quotient Group:
   quotient_group_def  |- !g h. g / h = <|carrier := CosetPartition g h; op := $o; id := H|>
   quotient_group_closure    |- !g h. h <= g ==>
      !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h
   quotient_group_assoc     |- !g h. h << g ==>
      !x y z. x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h ==> ((x o y) o z = x o y o z)
   quotient_group_id        |- !g h. h << g ==> H IN CosetPartition g h /\ !x. x IN CosetPartition g h ==> (H o x = x)
   quotient_group_inv       |- !g h. h << g ==> !x. x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H)
   quotient_group_group     |- !g h. h << g ==> Group (g / h)

   Group Homomorphism by left_coset via normal subgroup:
   normal_subgroup_coset_homo  |- !g h. h << g ==> GroupHomo (left_coset g H) g (g / h)
   normal_coset_op_property    |- !g h. h << g ==> !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==>
         (x o y = CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y) * H)
   coset_homo_group_iso_quotient_group |- !g h. h << g ==> GroupIso I (homo_group g (left_coset g H)) (g / h)

   Kernel Group of Group Homomorphism:
   kernel_def             |- !f g h. kernel f g h = preimage f G h.id
   kernel_group_def       |- !f g h. kernel_group f g h = <|carrier := kernel f g h; id := #e; op := $* |>
#  kernel_property        |- !g h f x. x IN kernel f g h <=> x IN G /\ (f x = h.id)
   kernel_element         |- !g h f x. x IN kernel f g h <=> x IN G /\ (f x = h.id)
   kernel_group_group     |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> Group (kernel_group f g h)
   kernel_group_subgroup  |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> kernel_group f g h <= g
   kernel_group_normal    |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> kernel_group f g h << g
   kernel_quotient_group  |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> Group (g / kernel_group f g h)

   Homomorphic Image and Kernel:
   homo_image_def            |- !f g h. homo_image f g h = <|carrier := IMAGE f G; op := h.op; id := h.id|>
   homo_image_monoid         |- !g h f. Monoid g /\ Monoid h /\ MonoidHomo f g h ==> Monoid (homo_image f g h)
   homo_image_group          |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> Group (homo_image f g h)
   homo_image_subgroup       |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> homo_image f g h <= h
   group_homo_image_surj_property  |- !g h f. Group g /\ Group h /\
                                              SURJ f G h.carrier ==> GroupIso I h (homo_image f g h)
   monoid_homo_homo_image_monoid   |- !g h f. Monoid g /\ MonoidHomo f g h ==> Monoid (homo_image f g h)
   group_homo_homo_image_group     |- !g h f. Group g /\ MonoidHomo f g h ==> Group (homo_image f g h)

   First Isomorphic Theorem for Group:
   homo_image_homo_quotient_kernel    |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      GroupHomo (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h)
   homo_image_to_quotient_kernel_bij  |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      BIJ (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h).carrier (g / kernel_group f g h).carrier
   homo_image_iso_quotient_kernel     |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      GroupIso (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h)
   group_first_isomorphism_thm        |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      kernel_group f g h << g /\ homo_image f g h <= h /\
      GroupIso (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h) /\
      (SURJ f G h.carrier ==> GroupIso I h (homo_image f g h))
*)

(* ------------------------------------------------------------------------- *)
(* Group element division.                                                   *)
(* ------------------------------------------------------------------------- *)
(* Define group division *)
val group_div_def = Define `
  group_div (g:'a group) (x:'a) (y:'a)  = x * |/ y
`;

(* set overloading *)
val _ = overload_on ("/", ``group_div g``);
val _ = set_fixity "/" (Infixl 600); (* same as "*" in arithmeticScript.sml *)

(* export simple defintion *)
val _ = export_rewrites ["group_div_def"];

(* Theorem: x / y IN G *)
(* Proof:
   x / y = x * |/y  by group_div_def
   and |/y IN G     by group_inv_element
   hence true       by group_op_element
*)
val group_div_element = store_thm(
  "group_div_element",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> x / y IN G``,
  rw[group_div_def]);

val _ = export_rewrites ["group_div_element"];

(* Theorem: x / x = #e *)
(* Proof:
   x / x = x * |/x   by group_div_def
         = #e        by group_rinv
*)
val group_div_cancel = store_thm(
  "group_div_cancel",
  ``!g:'a group. Group g ==> !x. x IN G ==> (x / x = #e)``,
  rw[group_div_def]);

val _ = export_rewrites ["group_div_cancel"];

(* Theorem: (x1 * y1) / (x2 * y2) = x1 * (y1 / y2) / x1 * (x1 / x2) *)
(* Proof:
     (x1 * y1) / (x2 * y2)
   = (x1 * y1) * |/ (x2 * y2)                    by group_div_def
   = (x1 * y1) * ( |/ y2 * |/ x2)                by group_inv_op
   = x1 * (y1 * ( |/ y2 * |/ x2))                by group_assoc
   = x1 * (y1 * |/ y2 * |/ x2)                   by group_assoc
   = x1 * (y1 * |/ y2 * ( |/ x1 * x1 * |/ x2))   by group_linv, group_lid
   = x1 * (y1 * |/ y2 * ( |/ x1 * (x1 * |/ x2))) by group_assoc
   = x1 * (y1 / y2) * |/ x1 * (x1 / x2)          by group_assoc
   = x1 * (y1 / y2) / x1 * (x1 / x2)             by group_div_def
*)
val group_div_pair = store_thm(
  "group_div_pair",
  ``!g:'a group. Group g ==> !x1 y1 x2 y2. x1 IN G /\ y1 IN G /\ x2 IN G /\ y2 IN G ==>
    ((x1 * y1) / (x2 * y2) = (x1 * (y1 / y2) / x1) * (x1 / x2))``,
  rw_tac std_ss[group_div_def] >>
  `|/ x1 IN G /\ |/ y1 IN G /\ |/ x2 IN G /\ |/ y2 IN G` by rw[group_assoc] >>
  `(x1 * y1) * |/ (x2 * y2) = x1 * y1 * ( |/ y2 * |/ x2)` by rw[group_inv_op] >>
  `_ = x1 * (y1 * |/ y2 * |/ x2)` by rw[group_assoc] >>
  `_ = x1 * (y1 * |/ y2 * ( |/ x1 * x1 * |/ x2))` by rw_tac std_ss[group_linv, group_lid] >>
  `_ = (x1 * (y1 * |/ y2) * |/ x1) * (x1 * |/ x2)` by rw[group_assoc] >>
  rw_tac std_ss[]);

(* Theorem: (z * x) / (z * y) = z * (x / y) / z  *)
(* Proof:
     (z * x) / (z * y)
   = z * (x / y) / z * (z / z)    by group_div_pair
   = z * (x / y) / z * #e         by group_div_cancel
   = z * (x / y) / z              by group_rid
*)
val group_div_lsame = store_thm(
  "group_div_lsame",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((z * x) / (z * y) = z * (x / y) / z)``,
  rw[group_assoc, group_div_pair]);

(* Theorem: (x * z) / (y * z) = x / y  *)
(* Proof:
     (x * z) / (y * z)
   = x * (z / z) / x * (x / y)   by group_div_pair
   = x * #e / x * (x / y)        by group_div_cancel
   = x / x * (x / y)             by group_rid
   = #e * (x / y)                by group_div_cancel
   = x / y                       by group_lid
*)
val group_div_rsame = store_thm(
  "group_div_rsame",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * z) / (y * z) = x / y)``,
  rw[group_assoc, group_div_pair]);

(* ------------------------------------------------------------------------- *)
(* Normal Subgroup                                                           *)
(* ------------------------------------------------------------------------- *)

(* A Normal Subgroup: for all x IN H, for all a IN G, a * x / a IN H
   i.e. A subgroup, H, of a group, G, is called a normal subgroup if it is invariant under conjugation. *)
val normal_subgroup_def = Define `
  normal_subgroup (h:'a group) (g:'a group) <=>
    h <= g /\ (!a z. a IN G /\ z IN H ==> a * z / a IN H)
`;

(* set overloading *)
val _ = overload_on ("<<", ``normal_subgroup``);
val _ = set_fixity "<<" (Infixl 650); (* higher than * or / *)

(* Theorem: Normal subgroup is a subgroup. *)
val normal_subgroup_subgroup = save_thm("normal_subgroup_subgroup",
    normal_subgroup_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val normal_subgroup_subgroup = |- !h g. h << g ==> h <= g : thm *)

(* Theorem: Normal subgroup is invariant under conjugation. *)
val normal_subgroup_property = save_thm("normal_subgroup_property",
    normal_subgroup_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val normal_subgroup_property = |- !h g. h << g ==> !a z. a IN G /\ z IN H ==> a * z / a IN H : thm *)

(* Theorem: h << g ==> h <= g /\ Group h /\ Group g *)
(* Proof: by normal_subgroup_def and subgroup_property. *)
val normal_subgroup_groups = store_thm(
  "normal_subgroup_groups",
  ``!g h:'a group. h << g ==> h <= g /\ Group h /\ Group g``,
  metis_tac[normal_subgroup_def, subgroup_property]);

(* Theorem: g << g *)
(* Proof: by definition, this is to show:
   g <= g,
   True by subgroup_refl
*)
val normal_subgroup_refl = store_thm(
  "normal_subgroup_refl",
  ``!g:'a group. Group g ==> g << g``,
  rw[normal_subgroup_def, subgroup_refl]);

(* Theorem: h << g /\ g << h ==> h = g *)
(* Proof: by definition, this is to show:
   h <= g /\ g <= h ==> h = g,
   True by subgroup_antisym.
*)
val normal_subgroup_antisym = store_thm(
  "normal_subgroup_antisym",
  ``!(g:'a group) (h:'a group). h << g /\ g << h ==> (h = g)``,
  rw[normal_subgroup_def, subgroup_antisym]);

(* Note: Subgroup normality is not transitive:
see: http://groupprops.subwiki.org/wiki/Normality_is_not_transitive

D4 = <a, x | a^4 = x^2 = e, x a x = |/a >
Let H1 = <x>, H2 = <a^2 x>, K = <x, a^2>
Then H1 << K, H2 << K, K << D4, but neither H1 << D4 nor H2 << D4.

i.e. <s> << <r^2, s> << <r, s>=D4, but <s> is not normal in D4.

or
In S4 and its following subgroup A={(12)(34)} and B={(12)(34),(13)(42),(23)(41),e}
Try to show A is normal in B and B is normal in S4 but A is not normal in G.

*)

(* Property of Normal Subgroup: a subgroup with left coset = right coset. *)
(* Theorem: h << g <=> h <= g /\ aH = Ha  for all a in G. *)
(* Proof:
   If-part:
     h << g ==> !a. a IN G ==> (IMAGE (\z. z * a) H = IMAGE (\z. a * z) H)
   This essentially boils down to 2 cases:
   case 1. h <= g /\ a IN G /\ z IN H ==> ?z'. (z * a = a * z') /\ z' IN H
      By group property, z' = |/a * z * a, need to show that z' IN H
      This is because, a IN G ==> |/a IN G,
      hence |/a * z * |/( |/ a) IN H    by by conjugate property
         or |/a * z * a        IN H    by group_inv_inv
   case 2. h <= g /\ a IN G /\ z IN H ==> ?z'. (a * z = z' * a) /\ z' IN H
      By group property, z' = a * z / a, need to show z' IN H
      This is because a IN G, hence true by conjugate property.
   Only-if part:
      h <= g /\ !a. a IN G ==> (IMAGE (\z. z * a) H = IMAGE (\z. a * z) H) ==> a * z * |/ a IN H
      Since a * z IN right image, there is z' such that z' * a = a * z and z' IN H
      i.e. z' = a * z * |/a IN H,
              = a * z / a   IN H.
*)
val normal_subgroup_alt = store_thm(
  "normal_subgroup_alt",
  ``!g h:'a group. h << g <=> h <= g /\ (!a. a IN G ==> (a * H = H * a))``,
  rw_tac std_ss[normal_subgroup_def, coset_def, right_coset_def, EQ_IMP_THM] >| [
    rw[EXTENSION] >>
    `Group h /\ Group g` by metis_tac[subgroup_property] >>
    `|/a IN G` by rw[] >>
    rw_tac std_ss[EQ_IMP_THM] >| [
      qexists_tac `a * z / a` >>
      `z IN G` by metis_tac[subgroup_element] >>
      rw[group_rinv_assoc],
      qexists_tac `|/a * z * a` >>
      `z IN G` by metis_tac[subgroup_element] >>
      rw[group_assoc, group_linv_assoc] >>
      `|/ a * (z * a) = |/a * z * a` by rw[group_assoc] >>
      metis_tac[group_inv_inv, group_div_def]
    ],
    full_simp_tac std_ss [IMAGE_DEF, EXTENSION, GSPECIFICATION] >>
    `?z'. (a * z = z' * a) /\ z' IN H` by metis_tac[] >>
    metis_tac[group_rinv_assoc, group_div_def, Subgroup_def, SUBSET_DEF]
  ]);

(* Theorem: x * H = y * H ==> x / y IN H  if  H is a normal subgroup *)
(* Proof:
   By subgroup_coset_eq, |/y * x IN H
   i.e. y * ( |/y * x) * |/ y    IN H  by normal_subgroup_property
     or x * |/ y                 IN H  by group_assoc, group_rinv, group_lid
     or x / y                    IN H  by group_div_def
*)
val normal_subgroup_coset_eq = store_thm(
  "normal_subgroup_coset_eq",
  ``!g h:'a group. h << g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> x / y IN H)``,
  rw_tac std_ss[normal_subgroup_def, group_div_def] >>
  `|/y * x IN H <=> x * |/ y IN H` suffices_by rw_tac std_ss[subgroup_coset_eq] >>
  `Group h /\ Group g` by metis_tac[subgroup_property] >>
  `y * ( |/y * x) * |/ y = y * |/y * x * |/ y` by rw[group_assoc] >>
  `_ = x * |/ y` by rw_tac std_ss[group_rinv, group_lid] >>
  `|/ x * (x * |/ y) * x = |/ x * x * |/ y * x` by rw[group_assoc] >>
  `_ = |/ y * x` by rw_tac std_ss[group_linv, group_lid, group_inv_element] >>
  metis_tac[group_inv_element, group_inv_inv]);

(* ------------------------------------------------------------------------- *)
(* Equivalence induced by Normal Subgroup                                    *)
(* ------------------------------------------------------------------------- *)

(* Two group elements x y are equivalent if  x / y = x * |/y in normal subgroup. *)

(* Define group element equivalence by normal subgroup. *)
val group_equiv_def = Define `
  group_equiv (g:'a group) (h:'a group) x y  <=> x / y IN H
`;

(* set overloading *)
val _ = overload_on ("==", ``group_equiv g h``);
val _ = set_fixity "==" (Infix(NONASSOC, 450));

(* Theorem: [== is reflexive] h << g ==> z == z   for z IN G. *)
(* Proof:
   z == z  iff z / z         IN H  by group_equiv_def
           iff z * |/z = #e  IN H  by group_div_def, group_rinv
   which is true since h <= g, and Group h.
   or: since h << g, h.id = #e     by subgroup_id
   hence   z * |/z = z * #e * |/z  IN H   by normal_subgroup_property.
*)
val group_normal_equiv_reflexive = store_thm(
  "group_normal_equiv_reflexive",
  ``!g h:'a group. h << g ==> !z. z IN G ==> z == z``,
  rw_tac std_ss[normal_subgroup_def, group_equiv_def, group_div_def] >>
  metis_tac[group_id_element, subgroup_id, group_rid, Subgroup_def]);

(* Theorem: [== is symmetric] h << g ==> x == y <=> y == x   for x, y IN G. *)
(* Proof:
   x == y  iff x / y         IN H    by group_equiv_def
           iff x * |/ y      IN H    by group_div_def
           iff |/ (x * |/ y) IN H    by group_inv_element
           iff y * |/ x      IN H    by group_inv_op, group_inv_inv
           if  y / x         IN H    by group_div_def
           iff y == x                by group_equiv_def
*)
val group_normal_equiv_symmetric = store_thm(
  "group_normal_equiv_symmetric",
  ``!g h:'a group. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> y == x)``,
  rw_tac std_ss[normal_subgroup_def, group_equiv_def, group_div_def] >>
  `Group h /\ Group g` by metis_tac[Subgroup_def] >>
  `|/ ( x * |/ y) = y * |/ x` by rw[group_inv_inv, group_inv_op] >>
  `|/ ( y * |/ x) = x * |/ y` by rw[group_inv_inv, group_inv_op] >>
  metis_tac[group_inv_element, subgroup_inv]);

(* Theorem: [== is transitive] h << g ==> x == y /\ y == z ==> x == z   for x, y, z IN G. *)
(* Proof:
   x == y  iff x * |/ y  IN H        by group_equiv_def, group_div_def
   y == z  iff y * |/ z  IN H        by by group_equiv_def, group_div_def
   Together,
      (x * |/ y) * (y * |/ z) IN H   by group_op_element
   or  x * |/ z               IN H   by group_assoc, group_linv
   i..e. x == z                      by by group_equiv_def, group_div_def
*)
val group_normal_equiv_transitive = store_thm(
  "group_normal_equiv_transitive",
  ``!g h:'a group. h << g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x == y /\ y == z ==> x == z)``,
  rw_tac std_ss[normal_subgroup_def, group_equiv_def, group_div_def] >>
  `Group h /\ Group g` by metis_tac[Subgroup_def] >>
  `(x * |/ y) * (y * |/ z) = (x * |/ y) * y * |/ z` by rw[group_assoc] >>
  `_ = x * |/ z` by rw_tac std_ss[group_linv, group_rid, group_assoc, group_inv_element] >>
  metis_tac[group_op_element, subgroup_property]);

(* Theorem: [== is an equivalence relation] h << g ==> $== equiv_on G. *)
(* Proof: by group_normal_equiv_reflexive, group_normal_equiv_symmetric, group_normal_equiv_transitive. *)
val group_normal_equiv = store_thm(
  "group_normal_equiv",
  ``!g h:'a group. h << g ==> $== equiv_on G``,
  rw_tac std_ss[equiv_on_def] >| [
    rw_tac std_ss[group_normal_equiv_reflexive],
    rw_tac std_ss[group_normal_equiv_symmetric],
    metis_tac[group_normal_equiv_transitive]
  ]);

(* ------------------------------------------------------------------------- *)
(* Normal Equivalence Classes are Cosets of Normal Subgroup.                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: for x, y in G, x == y  iff x IN y * H, the coset of y with normal subgroup. *)
(* Proof:
   x == y  iff   x / y IN H                 by group_equiv_def
           iff   x * |/ y  IN H             by group_div_def
           iff   x * |/ y = z,  where z IN H
           iff   x = z * y
           iff   x IN IMAGE (\z. z * y) H   by IMAGE definition
           iff   x IN IMAGE (\z. y * z) H   by normal_subgroup_alt
           iff   x IN yH                    by coset definition
*)
val group_normal_equiv_property = store_thm(
  "group_normal_equiv_property",
  ``!h g:'a group. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> x IN y * H)``,
  rw_tac std_ss[group_equiv_def] >>
  `x / y IN H <=> x IN H * y` suffices_by metis_tac[normal_subgroup_alt] >>
  rw_tac std_ss[group_div_def, right_coset_def, IN_IMAGE] >>
  `x * |/ y IN H <=> ?z. z IN H /\ (z = x * |/ y)` by rw_tac std_ss[] >>
  metis_tac[group_lsolve, normal_subgroup_subgroup, Subgroup_def, SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* The map to set of costes and the induced binary operation.                *)
(* Aim: coset g H is a homomorphism: G -> Group of {a * H | a IN G}    *)
(* ------------------------------------------------------------------------- *)

(* from subgroupTheory:

- inCoset_def;
> val it = |- !g h a b. inCoset g h a b <=> b IN a * H : thm

- inCoset_equiv_on_carrier;
> val it = |- !g h. h <= g ==> inCoset g h equiv_on G : thm

- CosetPartition_def;
> val it = |- !g h. CosetPartition g h = partition (inCoset g h) G : thm

- coset_partition_element;
> val it = |- !g h. h <= g ==> !e. e IN CosetPartition g h ==> ?a. a IN G /\ (e = a * H) : thm

- GroupHomo_def;
> val it = |- !f g h. GroupHomo f g h <=> (!x. x IN G ==> f x IN H) /\
                                          !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)) : thm
- type_of ``a * H``;
> val it = ``:'a -> bool`` : hol_type

*)

(* Existence of coset generator: e IN CosetPartition g h ==> ?a. a IN G /\ (e = a * H) *)
val lemma = prove(
  ``!g h e. ?a. h <= g /\ e IN CosetPartition g h ==> a IN G /\ (e = a * H)``,
  metis_tac[coset_partition_element]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define coset generator *)
val cogen_def = new_specification(
    "cogen_def",
    ["cogen"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val cogen_def = |- !g h e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G /\ (e = (cogen g h e) * H) : thm *)

(* Theorem: h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G *)
val cogen_element = save_thm("cogen_element",
    cogen_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val cogen_element = |- !h g e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G : thm *)

(* Theorem: h <= g /\ e IN CosetPartition g h ==> (cogen g h e) * H = e *)
val coset_cogen_property = save_thm("coset_cogen_property",
    cogen_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val coset_cogen_property = |- !h g e. h <= g /\ e IN CosetPartition g h ==> (e = (cogen g h e) * H) : thm *)

(* Define coset multiplication *)
val coset_op_def = Define `
  coset_op (g:'a group) (h:'a group) (x:'a -> bool) (y:'a -> bool) = ((cogen g h x) * (cogen g h y)) * H
`;

(* set overloading *)
val _ = overload_on ("o", ``coset_op g h``);

(* Theorem: h <= g ==> cogen g h H * H = H *)
(* Proof:
   Since H = #e * H          by coset_id_eq_subgroup
   H IN CosetPartition g h   by coset_partition_element
   hence cogen g h H * H = H by cogen_def
*)
val cogen_of_subgroup = store_thm(
  "cogen_of_subgroup",
  ``!g h:'a group. h <= g ==> (cogen g h H * H = H)``,
  rpt strip_tac >>
  `#e * H = H` by rw_tac std_ss[coset_id_eq_subgroup] >>
  `Group g` by metis_tac[Subgroup_def] >>
  `H IN CosetPartition g h` by metis_tac[coset_partition_element, group_id_element] >>
  rw_tac std_ss[cogen_def]);

(* Theorem: h <= g ==> !x. x IN G ==> cogen g h (x * H) IN G *)
(* Proof:
   Since x * H  IN CosetPartition g h   by coset_partition_element
   cogen g h (x * H) IN G               by cogen_def
*)
val cogen_coset_element = store_thm(
  "cogen_coset_element",
  ``!g h:'a group. h <= g ==> !x. x IN G ==> cogen g h (x * H) IN G``,
  metis_tac[cogen_def, coset_partition_element]);

(* Theorem: x / cogen g h (x * H) IN H if H is a normal subgroup. *)
(* Proof:
   Since x * H IN CosetPartition g h  by coset_partition_element
         cogen g h (x * H) IN G /\
         ((cogen g h (x * H)) * H = x * H)  by cogen_def
   hence x / cogen g h (x * H) IN H   by normal_subgroup_coset_eq
*)
val normal_cogen_property = store_thm(
  "normal_cogen_property",
  ``!g h:'a group. h << g ==> !x. x IN G ==> x / cogen g h (x * H) IN H``,
  rpt strip_tac >>
  `h <= g` by rw_tac std_ss[normal_subgroup_subgroup] >>
  `x * H IN CosetPartition g h` by metis_tac[coset_partition_element] >>
  `cogen g h (x * H) IN G /\ ((cogen g h (x * H)) * H = x * H)` by rw_tac std_ss[cogen_def] >>
  metis_tac[normal_subgroup_coset_eq]);

(* Theorem: h << g ==> cogen g h (a * H) * b * H = a * b * H  *)
(* Proof:
   By normal_subgroup_coset_eq, and reversing the equality,
   this is to show: (a * b) / (cogen g h (a * H) * b) IN H
   but  (a * b) / (cogen g h (a * H) * b) = a / cogen g h (a * H)  by group_div_rsame
   and  a / cogen g h (a * H) IN H    by normal_cogen_property.
*)
val normal_coset_property1 = store_thm(
  "normal_coset_property1",
  ``!g h:'a group. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * b * H = a * b * H)``,
  rpt strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  `cogen g h (a * H) IN G` by rw_tac std_ss[cogen_coset_element] >>
  `a / cogen g h (a * H) IN H` by rw_tac std_ss[normal_cogen_property] >>
  `(a * b) / (cogen g h (a * H) * b) = a / cogen g h (a * H)` by rw_tac std_ss[group_div_rsame] >>
  metis_tac[normal_subgroup_coset_eq, group_op_element]);

(* Theorem: h << g ==> a * cogen g h (b * H) * H = a * b * H  *)
(* Proof:
   By normal_subgroup_coset_eq, and reversing the equality,
   this is to show: (a * b) / (a * cogen g h (b * H)) IN H
   but (a * b) / (a * cogen g h (b * H)) = a * (b / cogen g h (b * H)) / a  by group_div_lsame
   and  b / cogen g h (b * H) IN H          by normal_cogen_property
   hence a * b / cogen g h (b * H) / a IN H by normal_subgroup_property
*)
val normal_coset_property2 = store_thm(
  "normal_coset_property2",
  ``!g h:'a group. h << g ==> !a b. a IN G /\ b IN G ==> (a * cogen g h (b * H) * H = a * b * H)``,
  rpt strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  `cogen g h (b * H) IN G` by rw_tac std_ss[cogen_coset_element] >>
  `b / cogen g h (b * H) IN H` by rw_tac std_ss[normal_cogen_property] >>
  `a * b / (a * cogen g h (b * H)) = a * (b / cogen g h (b * H)) / a` by rw_tac std_ss[group_div_lsame] >>
  `a * b / (a * cogen g h (b * H)) IN H` by rw_tac std_ss[normal_subgroup_property] >>
  metis_tac[normal_subgroup_coset_eq, group_op_element]);

(* Theorem: h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * cogen g h (b * H) * H = a * b * H) *)
(* Proof:
   h << g ==> h <= g                  by normal_subgroup_subgroup
   a IN G ==> cogen g h (a * H) IN G  by cogen_coset_element, h <= g
   b IN G ==> cogen g h (b * H) IN G  by cogen_coset_element, h <= g
     cogen g h (a * H) * cogen g h (b * H) * H
   = a * cogen g h (b * H) * H        by normal_coset_property1, h << g
   = a * b * H                        by normal_coset_property2, h << g
*)
val normal_coset_property = store_thm(
  "normal_coset_property",
  ``!g h:'a group. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * cogen g h (b * H) * H = a * b * H)``,
  rw_tac std_ss[normal_subgroup_subgroup, cogen_coset_element, normal_coset_property1, normal_coset_property2]);

(* ------------------------------------------------------------------------- *)
(* Quotient Group                                                            *)
(* ------------------------------------------------------------------------- *)
(* Define the quotient group, the group divided by a normal subgroup. *)
val quotient_group_def = Define`
  quotient_group (g:'a group) (h:'a group) =
    <| carrier := (CosetPartition g h);
            op := coset_op g h;
            id := H
     |>
`;

(* set overloading *)
val _ = overload_on ("/", ``quotient_group``);
val _ = set_fixity "/" (Infixl 600); (* same as "*" in arithmeticScript.sml *)

(*
- type_of ``(g:'a group) / (h:'a group)``;
> val it = ``:('a -> bool) group`` : hol_type
- type_of ``coset g H``;
> val it = ``:'a -> 'a -> bool`` : hol_type
*)

(* Theorem: [Quotient Group Closure]
   h << g ==> x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h *)
(* Proof:
   x o y = cogen g h x * cogen g h y * H    by coset_op_def
   Since cogen g h x IN G    by cogen_def
     and cogen g h y IN G    by cogen_def
   hence cogen g h x * cogen g h y IN G   by group_op_element
      or (cogen g h x * cogen g h y IN G) * H IN CosetPartition g h   by coset_partition_element.

*)
val quotient_group_closure = store_thm(
  "quotient_group_closure",
  ``!g h:'a group. h <= g ==> !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h``,
  rw_tac std_ss[coset_op_def] >>
  `cogen g h x IN G /\ cogen g h y IN G` by rw_tac std_ss[cogen_def] >>
  metis_tac[group_op_element, coset_partition_element, Subgroup_def]);

(* Theorem: [Quotient Group Associativity]
   h << g ==> x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h ==> (x o y) o z = x o (y o z)  *)
(* Proof:
   By coset_op_def,
     (x o y) o z
   = cogen g h (cogen g h x * cogen g h y * H) * cogen g h z * H     by coset_op_def
   = ((cogen g h x * cogen g h y) * cogen g h z) * H                 by normal_coset_property1
   = (cogen g h x * (cogen g h y * cogen g h z)) * H                 by group_assoc
   = cogen g h x * cogen g h (cogen g h y * cogen g h z * H) * H     by normal_coset_property2
   = x o (y o z)                                                     by coset_op_def

   Since cogen g h x IN G    by cogen_def
     and cogen g h y IN G    by cogen_def
     and cogen g h z IN G    by cogen_def
   Let t = cogen g h x * cogen g h y  IN G
       t * H   IN CosetPartition g h
       cogen g h (t * H)  IN G /\ (cogen g h (t * H)) * H = t * H
   For h << g, this implies t / cogen g h (t * H)  IN H   by normal_cogen_property

*)
val quotient_group_assoc = store_thm(
  "quotient_group_assoc",
  ``!g h:'a group. h << g ==> !x y z. x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h
      ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[coset_op_def] >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  rw[group_assoc, normal_coset_property1, normal_coset_property2, cogen_coset_element, cogen_def]);

(* Theorem: [Quotient Group Identity]
   h << g ==> H IN CosetPartition g h /\ !x. x INCosetPartition g h ==> H o x = x *)
(* Proof:
   Since  #e * H = H                by coset_id_eq_subgroup
   hence  H IN CosetPartition g h   by coset_partition_element, group_id_element
   Since  cogen g h x IN G and x = cogen g h x * H     by cogen_def
   By normal_coset_property1,
       cogen g h (#e * H) * cogen g h x * H = #e * cogen g h x * H
   or  cogen g h H * cogen g h x * H = cogen g h x * H   by group_lid
   Hence
       H o x = cogen g h H * cogen g h x * H    by coset_op_def
             = cogen g h x * H                  by above
             = x
*)
val quotient_group_id = store_thm(
  "quotient_group_id",
  ``!g h:'a group. h << g ==> H IN CosetPartition g h /\ !x. x IN CosetPartition g h ==> (H o x = x)``,
  ntac 3 strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_def, Subgroup_def] >>
  `#e * H = H` by rw_tac std_ss[coset_id_eq_subgroup] >>
  `#e IN G` by rw_tac std_ss[group_id_element] >>
  rw_tac std_ss[coset_op_def] >| [
    metis_tac[coset_partition_element],
    `cogen g h x IN G /\ (cogen g h x * H = x)` by rw_tac std_ss[cogen_def] >>
    `cogen g h (#e * H) * cogen g h x * H = #e * cogen g h x * H` by rw_tac std_ss[normal_coset_property1] >>
    metis_tac[group_lid]
  ]);

(* Theorem: [Quotient Group Inverse]
   h << g ==> x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H) *)
(* Proof:
   Since x IN CosetPartition g h,
       cogen g h x IN G /\ (cogen g h x * H = x)                     by cogen_def
   and |/ (cogen g h x) IN G /\ |/ (cogen g h x) * cogen g h x = #e  by group_inv_element, group_linv
   hence  |/ (cogen g h x) * H IN CosetPartition g h                 by coset_partition_element
   Let y = |/ (cogen g h x) * H, then
   y o x = cogen g h ( |/ (cogen g h x) * H) * cogen g h x * H
         = |/ (cogen g h x) * H o cogen g h x * H                    by normal_coset_property1
         = ( |/ (cogen g h x) * cogen g h x) * H                     by coset_op_def
         = #e * H = H                                                by coset_id_eq_subgroup
*)
val quotient_group_inv = store_thm(
  "quotient_group_inv",
  ``!g h:'a group. h << g ==> !x. x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H)``,
  rpt strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  `cogen g h x IN G /\ (cogen g h x * H = x)` by rw_tac std_ss[cogen_def] >>
  `|/ (cogen g h x) IN G /\ ( |/ (cogen g h x) * cogen g h x = #e)` by rw[] >>
  `|/ (cogen g h x) * H IN CosetPartition g h` by metis_tac[coset_partition_element] >>
  metis_tac[coset_op_def, normal_coset_property1, coset_id_eq_subgroup]);

(* Theorem: quotient_group is a group for normal subgroup
   i.e. h << g ==> Group (quotient_group g h)               *)
(* Proof:
   This is to prove:
   (1) x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h
       true by quotient_group_closure.
   (2) x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h ==> (x o y) o z = x o y o z
       true by quotient_group_assoc.
   (3) H IN CosetPartition g h
       true by quotient_group_id.
   (4) x IN CosetPartition g h ==> H o x = x
       true by quotient_group_id.
   (5) x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H)
       true by quotient_group_inv.
*)
val quotient_group_group = store_thm(
  "quotient_group_group",
  ``!g h:'a group. h << g ==> Group (quotient_group g h)``,
  rpt strip_tac >>
  `h <= g /\ Group h /\ Group g` by metis_tac[normal_subgroup_groups] >>
  rw_tac std_ss[group_def_alt, quotient_group_def] >| [
    rw_tac std_ss[quotient_group_closure],
    rw_tac std_ss[quotient_group_assoc],
    rw_tac std_ss[quotient_group_id],
    rw_tac std_ss[quotient_group_id],
    rw_tac std_ss[quotient_group_inv]
  ]);

(* ------------------------------------------------------------------------- *)
(* Group Homomorphism by left_coset via normal subgroup.                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: A normal subgroup induces a natural homomorphism to its quotient group, i.e.
            h << g ==> GroupHomo (left_coset g H) g (g / h) *)
(* Proof:
   After expanding by quotient_group_def, this is to show 2 things:
   (1) h << g /\ x IN G ==> x * H IN CosetPartition g h
       This is true by coset_partition_element, and normal_subgroup_subgroup.
   (2) h << g /\ x IN G /\ y IN G ==> (x * y) * H = x * H o y * H
       This is to show:
       (x * y) * H = (cogen g h (x * H) * cogen g h (y * H)) * H
       Since x * H IN CosetPartition g h    by coset_partition_element
             y * H IN CosetPartition g h    by coset_partition_element
       hence cogen g h (x * H) IN G         by cogen_def
             cogen g h (y * H) IN G         by cogen_def
       By normal_subgroup_coset_eq, this is to show:
             (x * y) / (cogen g h (x * H) * cogen g h (y * H)) IN H
       But  (x * y) / (cogen g h (x * H) * cogen g h (y * H))
          = x * (y / cogen g h (y * H)) / x * (x / cogen g h (x * H)  by group_div_pair

       Since      x / cogen g h (x * H) IN H    by normal_cogen_property
       and    z = y / cogen g h (y * H) IN H    by normal_cogen_property
       so     x * z * / x  IN H  since z IN H   by normal_subgroup_property
       hence their product is IN H              by group_op_element
*)
val normal_subgroup_coset_homo = store_thm(
  "normal_subgroup_coset_homo",
  ``!g h:'a group. h << g ==> GroupHomo (left_coset g H) g (g / h)``,
  rw_tac std_ss[GroupHomo_def, quotient_group_def, left_coset_def] >-
  metis_tac[coset_partition_element, normal_subgroup_subgroup] >>
  rw_tac std_ss[coset_op_def] >>
  `h <= g /\ !a z. a IN G /\ z IN H ==> a * z / a IN H` by metis_tac[normal_subgroup_def] >>
  `Group h /\ Group g /\ !x y. x IN H /\ y IN H ==> (h.op x y = x * y)` by metis_tac[subgroup_property] >>
  `x * H IN CosetPartition g h /\ y * H IN CosetPartition g h` by metis_tac[coset_partition_element] >>
  `cogen g h (x * H) IN G /\ cogen g h (y * H) IN G` by rw_tac std_ss[cogen_def] >>
  `(x * y) / (cogen g h (x * H) * cogen g h (y * H)) IN H`
     suffices_by rw_tac std_ss[normal_subgroup_coset_eq, group_op_element] >>
  rw_tac std_ss[group_div_pair] >>
  `x / cogen g h (x * H) IN H /\ y / cogen g h (y * H) IN H` by rw_tac std_ss[normal_cogen_property] >>
  `x * (y / cogen g h (y * H)) / x IN H` by rw_tac std_ss[normal_subgroup_property] >>
  metis_tac[group_op_element]);

(* Theorem: x o y = (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) * H *)
(* Proof:
   This is to show:
   cogen g h x * cogen g h y * H = CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y) * H
   By normal_subgroup_coset_eq, need to show:
      (cogen g h x * cogen g h y) / (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) IN H
   i.e.  (cogen g h x) * ((cogen g h y) / CHOICE (preimage (left_coset g H) G y)) / (cogen g h x) *
         ((cogen g h x) / CHOICE (preimage (left_coset g H) G x))   IN H    by group_div_pair
   Since  x = (cogen g h x) * H                by cogen_def
          x = (CHOICE (preimage (left_coset g H) G x)) * H   by preimage_choice_property
          (cogen g h x) / (CHOICE (preimage (left_coset g H) G x)) IN H    by normal_subgroup_coset_eq
   Similarly,
          y = (cogen g h y) * H                by cogen_def
          y = (CHOICE (preimage (left_coset g H) G y)) * H   by preimage_def
          (cogen g h y) / (CHOICE (preimage (left_coset g H) G y)) IN H    by normal_subgroup_coset_eq
   Hence (cogen g h x) * ((cogen g h y) / (CHOICE (preimage (left_coset g H) G y))) / (cogen g h x)   by normal_subgroup_property
   and the whole product is thus in H                by group_op_element, as h <= g ==> Group h.
*)
val normal_coset_op_property = store_thm(
  "normal_coset_op_property",
  ``!g h:'a group. h << g ==> !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==>
     (x o y = (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) * H)``,
  rw_tac std_ss[coset_op_def] >>
  `h <= g /\ Group g /\ !a z. a IN G /\ z IN H ==> a * z / a IN H` by metis_tac[normal_subgroup_def, subgroup_property] >>
  `cogen g h x IN G /\ ((cogen g h x) * H = x)` by rw_tac std_ss[cogen_def] >>
  `cogen g h y IN G /\ ((cogen g h y) * H = y)` by rw_tac std_ss[cogen_def] >>
  `x IN IMAGE (left_coset g H) G` by metis_tac[coset_partition_element, left_coset_def, IN_IMAGE] >>
  `y IN IMAGE (left_coset g H) G` by metis_tac[coset_partition_element, left_coset_def, IN_IMAGE] >>
  `CHOICE (preimage (left_coset g H) G x) IN G /\ (x = (CHOICE (preimage (left_coset g H) G x)) * H)` by metis_tac[preimage_choice_property, left_coset_def] >>
  `CHOICE (preimage (left_coset g H) G y) IN G /\ (y = (CHOICE (preimage (left_coset g H) G y)) * H)` by metis_tac[preimage_choice_property, left_coset_def] >>
  `(cogen g h x) / CHOICE (preimage (left_coset g H) G x) IN H` by metis_tac[normal_subgroup_coset_eq] >>
  `(cogen g h y) / CHOICE (preimage (left_coset g H) G y) IN H` by metis_tac[normal_subgroup_coset_eq] >>
  `(cogen g h x * cogen g h y) / (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) IN H` suffices_by rw_tac std_ss[normal_subgroup_coset_eq, group_op_element] >>
  rw_tac std_ss[group_div_pair] >>
  prove_tac[group_op_element, subgroup_property]);
(* This theorem does not help to prove identity below, but helps to prove isomorphism. *)

(* Theorem: h << g ==> GroupIso I (homo_group g (left_coset g H)) (g / h)  *)
(* Proof:
   This is to show:
   (1) h << g ==> GroupHomo I (homo_group g (left_coset g H)) (g / h)
       This is to show:
       (1.1) x IN IMAGE (left_coset g H) G ==> x IN CosetPartition g h
             true by subgroup_coset_in_partition.
       (1.2) x IN IMAGE (left_coset g H) G /\ y IN IMAGE (left_coset g H) G ==> image_op g (left_coset g H) x y = x o y
             Since x IN CosetPartition g h    by subgroup_coset_in_partition
                   y IN CosetPartition g h    by subgroup_coset_in_partition
             hence true by normal_coset_op_property, image_op_def, left_coset_def.
   (2) h << g ==> BIJ I (homo_group g (left_coset g H)).carrier (g / h).carrier
       This is to show: BIJ I (IMAGE (left_coset g H) G) (CosetPartition g h)
       Since h <= g  by normal_subgroup_def
       this is true by BIJ and subgroup_coset_in_partition.
*)
val coset_homo_group_iso_quotient_group = store_thm(
  "coset_homo_group_iso_quotient_group",
  ``!g h:'a group. h << g ==> GroupIso I (homo_group g (left_coset g H)) (g / h)``,
  rw_tac std_ss[GroupIso_def] >| [
    `h <= g` by metis_tac[normal_subgroup_def] >>
    rw_tac std_ss[GroupHomo_def, homo_monoid_def, quotient_group_def] >| [
      rw_tac std_ss[GSYM subgroup_coset_in_partition],
      `x IN CosetPartition g h` by rw_tac std_ss[GSYM subgroup_coset_in_partition] >>
      `y IN CosetPartition g h` by rw_tac std_ss[GSYM subgroup_coset_in_partition] >>
      rw_tac std_ss[image_op_def, left_coset_def, normal_coset_op_property]
    ],
    `h <= g` by metis_tac[normal_subgroup_def] >>
    rw_tac std_ss[homo_monoid_def, quotient_group_def] >>
    rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, subgroup_coset_in_partition]
  ]);

(* ------------------------------------------------------------------------- *)
(* Kernel Group of Group Homomorphism.                                       *)
(* ------------------------------------------------------------------------- *)

(* Define kernel of a mapping: the preimage of identity. *)
val kernel_def = Define`
  kernel f (g:'a group) (h:'b group) = preimage f G h.id
`;

(* Convert kernel to a group structure *)
val kernel_group_def = Define`
  kernel_group f (g:'a group) (h:'b group) =
    <| carrier := kernel f g h;
            id := g.id;
            op := g.op
     |>`;

(* Theorem: !x. x IN kernel f g h <=> x IN G /\ f x = h.id *)
(* Proof: by definition. *)
val kernel_property = store_thm(
  "kernel_property",
  ``!(g:'a group) (h:'b group). !f x. x IN kernel f g h <=> x IN G /\ (f x = h.id)``,
  simp_tac std_ss [kernel_def, preimage_def] >>
  rw[]);

(* export trivial truth. *)
val _ = export_rewrites ["kernel_property"];

(* Theorem alias *)
val kernel_element = save_thm("kernel_element", kernel_property);
(*
val kernel_element = |- !g h f x. x IN kernel f g h <=> x IN G /\ (f x = h.id): thm
*)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> Group (kernel_group f g h) *)
(* Proof:
   This is to show:
   (1) x IN kernel f g h /\ y IN kernel f g h ==> x * y IN kernel f g h
   By kernel property, x IN G and y IN G.
   f (x * y) = (f x) o (f y)      by GroupHomo_def
             = h.id o h.id        by kernel_property
             = h.id               by group_id_id
   Since x * y IN G               by group_op_element
   Hence x * y IN kernel f g h    by preimage_of_image
   (2) x IN kernel f g h /\ y IN kernel f g h /\ z IN kernel f g h ==> x * y * z = x * (y * z)
   By kernel_property, x IN G, y IN G and z IN G,
   Hence x * y * z = x * (y * z)  by group_assoc
   (3) #e IN kernel f g h
   Since #e IN G                  by group_id_element
   and f #e = h.id                by group_homo_id
   Hence #e IN kernel f g h       by preimage_of_image
   (4) x IN kernel f g h ==> #e * x = x
   By kernel property, x IN G.
   Hence #e * x = x               by group_lid
   (5) x IN kernel f g h ==> ?y. y IN kernel f g h /\ (y * x = #e)
   By kernel property, x IN G.
   Also, |/ x IN G                by group_inv_element
   Let y = |/ x, then y * x = #e  by group_linv
   Now f ( |/ x) = h.inv (f x))   by group_homo_inv
                = h.inv (h.id)    by kernel_property
                = h.id            by group_inv_id
   Hence |/ x IN kernel f g h     by preimage_of_image
*)
val kernel_group_group = store_thm(
  "kernel_group_group",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> Group (kernel_group f g h)``,
  rw_tac std_ss[GroupHomo_def] >>
  rw_tac std_ss[group_def_alt, kernel_group_def] >| [
    `x IN G /\ y IN G` by metis_tac[kernel_property] >>
    `x * y IN G` by rw[] >>
    `f (x * y) = h.id` by metis_tac[kernel_property, group_id_id] >>
    metis_tac[kernel_def, preimage_of_image],
    `x IN G /\ y IN G /\ z IN G` by metis_tac[kernel_property] >>
    rw[group_assoc],
    `#e IN G` by rw[] >>
    `f #e = h.id` by rw_tac std_ss[group_homo_id, GroupHomo_def] >>
    metis_tac[kernel_def, preimage_of_image],
    `x IN G` by metis_tac[kernel_property] >>
    rw[],
    `x IN G` by metis_tac[kernel_property] >>
    qexists_tac `|/ x` >>
    rw[] >>
    `|/x IN G` by rw[] >>
    `f ( |/ x) = h.inv (f x)` by rw_tac std_ss[group_homo_inv, GroupHomo_def] >>
    `_ = h.inv h.id` by metis_tac[kernel_property] >>
    `_ = h.id` by rw[] >>
    metis_tac[kernel_def, preimage_of_image]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) <= g *)
(* Proof: by Subgroup_def.
   (1) Group (kernel_group f g h)
   True by kernel_group_group.
   (2) (kernel_group f g h).carrier SUBSET G
   True by kernel_group_def, kernel_def, preimage_subset.
   (3) x IN (kernel_group f g h).carrier /\ y IN (kernel_group f g h).carrier ==> (kernel_group f g h).op x y = x * y
   True by kernel_group_def.
*)
val kernel_group_subgroup = store_thm(
  "kernel_group_subgroup",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) <= g``,
  rw_tac std_ss[Subgroup_def] >| [
    rw_tac std_ss[kernel_group_group],
    rw[kernel_group_def, kernel_def, preimage_subset],
    full_simp_tac (srw_ss()) [kernel_group_def]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) << g *)
(* Proof: by normal_subgroup_def.
   With kernel_group_subgroup, it needs to show further:
   a IN G /\ z IN kernel f g h ==> a * z * |/ a IN kernel f g h
   By kernel_property, z IN G /\ f z = h.id
   Hence a * z * |/ a IN G              by group_op_element, group_inv_element.
     f (a * z * |/ a)
   = h.op (f (a * z)) f ( |/ a)         by GroupHomo_def
   = h.op (h.op (f a) (f z)) f ( |/ a)  by GroupHomo_def
   = h.op (h.op (f a) h.id) (h.inv f a) by group_homo_inv
   = h.op (f a) (h.inv f a)             by group_rid
   = h.id                               by group_rinv
   Hence a * z * |/ a IN kernel f g h   by preimage_of_image
*)
val kernel_group_normal = store_thm(
  "kernel_group_normal",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) << g``,
  rw_tac std_ss[normal_subgroup_def, kernel_group_subgroup, kernel_group_def] >>
  `z IN G /\ (f z = h.id)` by metis_tac[kernel_property] >>
  `|/ a IN G /\ a * z IN G /\ a * z * |/ a IN G` by rw[] >>
  `f (a * z * |/ a) = h.id` by metis_tac[group_rid, group_rinv, group_homo_inv, GroupHomo_def] >>
  metis_tac[kernel_property, group_div_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> Group (g / (kernel_group f g h)) *)
(* Proof:
   By kernel_group_normal, kernel_group f g h << g.
   By quotient_group_group, Group (g / (kernel_group f g h))
*)
val kernel_quotient_group = store_thm(
  "kernel_quotient_group",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> Group (g / kernel_group f g h)``,
  rw[kernel_group_normal, quotient_group_group]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image and Kernel.                                             *)
(* ------------------------------------------------------------------------- *)

(* Proved in groupTheory,
- group_homo_group;
> val it = |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> Group (homo_group g f) : thm
- homo_monoid_def;
> val it = |- !g f. homo_group g f = <|carrier := IMAGE f G; op := image_op g f; id := f #e|> : thm
*)

(* Define the homomorphic image of a group via homomorphism. *)
val homo_image_def = Define`
  homo_image f (g:'a group) (h:'b group) =
    <| carrier := IMAGE f G;
            op := h.op;
            id := h.id
     |>
`;

(* Theorem: Monoid g /\ Monoid h /\ MonoidHomo f g h ==> Monoid (homo_image f g h) *)
(* Proof: by definition.
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> h.op x y IN IMAGE f G
   By IN_IMAGE, there are a IN G with f a = x, and b IN G with f b = y.
   Then h.op x y = h.op (f a) (f b) = f (a * b)                        by GroupHomo_def
   Since a * b IN G  by group_op_element, hence f (a * b) IN IMAGE f G by IN_IMAGE.
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> h.op (h.op x y) z = h.op x (h.op y z)
   By IN_IMAGE, there are a IN G with f a = x, b IN G with f b = y, and c IN G with f c = z.
   Hence x, y, z IN h.carrier      by MonoidHomo_def, thus true by monoid_assoc.
   (3) h.id IN IMAGE f G
   Since #e IN G               by monoid_id_element
   and f #e = h.id             by MonoidHomo_def
   Hence h.id IN IMAGE f G     by IN_IMAGE
   (4) h.op h.id x = x
   By IN_IMAGE, there are a IN G with f a = x.
   Hence x IN h.carrier        by MonoidHomo_def
   Hence h.op h.id x = x       by monoid_lid
   (5) h.op x h.id = x
   By IN_IMAGE, there are a IN G with f a = x.
   Hence x IN h.carrier        by MonoidHomo_def
   Hence h.op x h.id = x      by monoid_rid
*)
val homo_image_monoid = store_thm(
  "homo_image_monoid",
  ``!(g:'a monoid) (h:'b monoid). !f. Monoid g /\ Monoid h /\ MonoidHomo f g h ==> Monoid (homo_image f g h)``,
  rw_tac std_ss[MonoidHomo_def] >>
  `!x. x IN IMAGE f G ==> ?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  rw_tac std_ss[homo_image_def, Monoid_def] >| [
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `?b. b IN G /\ (f b = y)` by rw_tac std_ss[] >>
    `a * b IN G` by rw[] >>
    `h.op x y = f (a * b)` by rw_tac std_ss[] >>
    metis_tac[IN_IMAGE],
    `x IN h.carrier` by metis_tac[] >>
    `y IN h.carrier` by metis_tac[] >>
    `z IN h.carrier` by metis_tac[] >>
    rw[monoid_assoc],
    metis_tac[monoid_id_element, IN_IMAGE],
    `x IN h.carrier` by metis_tac[] >>
    rw[],
    `x IN h.carrier` by metis_tac[] >>
    rw[]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> Group (homo_image f g h) *)
(* Proof: by definition.
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> h.op x y IN IMAGE f G
   By IN_IMAGE, there are a IN G with f a = x, and b IN G with f b = y.
   Then h.op x y = h.op (f a) (f b) = f (a * b)   by GroupHomo_def
   Since a * b IN G  by group_op_element, hence f (a * b) IN IMAGE f G by IN_IMAGE.
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> h.op (h.op x y) z = h.op x (h.op y z)
   By IN_IMAGE, there are a IN G with f a = x, b IN G with f b = y, and c IN G with f c = z.
   Hence x, y, z IN h.carrier  by GroupHomo_def, thus true by group_assoc.
   (3) h.id IN IMAGE f G
   Since #e IN G               by group_id_element
   and f #e = h.id             by group_homo_id
   Hence h.id IN IMAGE f G     by IN_IMAGE
   (4) h.op h.id x = x
   By IN_IMAGE, there are a IN G with f a = x.
   Hence x IN h.carrier        by GroupHomo_def
   Hence h.op h.id x = x       by group_lid

   Since GroupHomo f g h /\           by given
         f #e = h.id                  by group_homo_id
     ==> MonoidHomo h g h             by GroupHomo_def, MonoidHomo_def
   Hence Monoid (homo_image f g h)    by homo_image_monoid
   With Group_def and other definitions, this is to show:
         x IN IMAGE f G ==> ?y. y IN IMAGE f G /\ (h.op y x = h.id)
   By IN_IMAGE, there is a IN G with f a = x.
   Hence |/ a IN G                    by group_inv_element
   Let y = f ( |/ a), y IN IMAGE f G  by IN_IMAGE
   h.op y x = h.op (f ( |/ a)) (f a)
            = f ( |/a * a)            by GroupHomo_def
            = f #e                    by group_linv
            = h.id                    by group_homo_id
   h.op x y = h.op (f a) (f ( |/ a))
            = f (a * |/a )            by GroupHomo_def
            = f #e                    by group_rinv
            = h.id                    by group_homo_id
*)
val homo_image_group = store_thm(
  "homo_image_group",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> Group (homo_image f g h)``,
  rpt strip_tac >>
  `f #e = h.id` by rw_tac std_ss[group_homo_id] >>
  `MonoidHomo f g h` by prove_tac[GroupHomo_def, MonoidHomo_def] >>
  `Monoid (homo_image f g h)` by rw[homo_image_monoid] >>
  rw_tac std_ss[Group_def, monoid_invertibles_def, homo_image_def, GSPECIFICATION, EXTENSION, EQ_IMP_THM] >>
  `?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  `|/ a IN G` by rw[] >>
  `( |/ a * a = #e) /\ (a * |/ a = #e)` by rw[] >>
  `f ( |/ a) IN IMAGE f G` by metis_tac[GroupHomo_def, IN_IMAGE] >>
  metis_tac[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> (homo_image f g h) <= h *)
(* Proof: by Subgroup_def.
   (1) Group (homo_image f g h)
   True by homo_image_group.
   (2) (homo_image f g h).carrier SUBSET h.carrier
   (homo_image f g h).carrier = IMAGE f G    by homo_image_def
   For all x IN IMAGE f G, ?a. a IN G /\ (f a = x)   by IN_IMAGE
   Hence x IN h.carrier by GroupHomo_def, hence true by SUBSET_DEF.
   (3) x IN (homo_image f g h).carrier /\ y IN (homo_image f g h).carrier ==> (homo_image f g h).op x y = h.op x y
   True by homo_image_def.
*)
val homo_image_subgroup = store_thm(
  "homo_image_subgroup",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> (homo_image f g h) <= h``,
  rw_tac std_ss[Subgroup_def] >| [
    rw_tac std_ss[homo_image_group],
    rw[homo_image_def, SUBSET_DEF] >>
    metis_tac[GroupHomo_def],
    rw_tac std_ss[homo_image_def]
  ]);

(* Theorem: Group g /\ Group h /\ SURJ f G h.carrier ==> GroupIso I h (homo_image f g h) *)
(* Proof:
   After expanding by GroupIso_def, GroupHomo_def, and homo_image_def, this is to show:
   (1) x IN h.carrier ==> x IN IMAGE f G
       Note x IN h.carrier ==> ?z. z IN G /\ f z = x    by SURJ_DEF
        and z IN G ==> f z = x IN IMAGE f G             by IN_IMAGE
   (2) x IN IMAGE f G ==> x IN h.carrier
       Note x IN IMAGE f G ==> ?z. z IN G /\ f z = x    by IN_IMAGE
        and z IN G ==> f z = x IN h.carrier             by SURJ_DEF
*)
val group_homo_image_surj_property = store_thm(
  "group_homo_image_surj_property",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\
     SURJ f G h.carrier ==> GroupIso I h (homo_image f g h)``,
  rw_tac std_ss[BIJ_DEF, SURJ_DEF, INJ_DEF, GroupIso_def, GroupHomo_def, homo_image_def] >>
  metis_tac[IN_IMAGE]);

(* Theorem: Monoid g /\ MonoidHomo f g h ==> Monoid (homo_image f g h) *)
(* Proof:
   Note MonoidHomo f g h
    ==> !x. x IN G ==> f x IN h.carrier                             by MonoidHomo_def
    and !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))   by MonoidHomo_def
    and f #e = h.id                                                 by MonoidHomo_def
   Also !x. x IN IMAGE f G ==> ?a. a IN G /\ (f a = x)              by IN_IMAGE

   Expand by homo_image_def, Monoid_def, this is to show:
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> h.op x y IN IMAGE f G
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
        and ?b. b IN G /\ (f b = y)             by y IN IMAGE f G
       also a * b IN G                          by monoid_op_element
        Now h.op x y = f (a * b)                by above
         so h.op x y IN IMAGE f G               by IN_IMAGE
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> h.op (h.op x y) z = h.op x (h.op y z)
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
        and ?b. b IN G /\ (f b = y)             by y IN IMAGE f G
        and ?c. c IN G /\ (f c = z)             by z IN IMAGE f G
        Now h.op (h.op x y) z = f ((a * b) * c) by a * b IN G, and above
        and h.op x (h.op y z) = f (a * (b * c)) by b * c IN G, and above
      Since a * b * c = a * (b * c)             by monoid_assoc
       thus h.op (h.op x y) z = h.op x (h.op y z)
   (3) h.id IN IMAGE f G
       Note h.id = f #e                         by above
        Now #e IN G                             by monoid_id_element
         so h.id IN IMAGE f G                   by IN_IMAGE
   (4) x IN IMAGE f G ==> h.op h.id x = x
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
            h.op h.id x
          = f (#e * a)                          by monoid_id_element, and above
          = f a                                 by monoid_lid
          = x
   (5) x IN IMAGE f G ==> h.op x h.id = x
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
            h.op x h.id
          = f (a * #e)                          by monoid_id_element, and above
          = f a                                 by monoid_rid
          = x
*)
val monoid_homo_homo_image_monoid = store_thm(
  "monoid_homo_homo_image_monoid",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidHomo f g h ==> Monoid (homo_image f g h)``,
  rw_tac std_ss[MonoidHomo_def] >>
  `!x. x IN IMAGE f G ==> ?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  rw_tac std_ss[homo_image_def, Monoid_def] >| [
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `?b. b IN G /\ (f b = y)` by rw_tac std_ss[] >>
    `a * b IN G` by rw[] >>
    `h.op x y = f (a * b)` by rw_tac std_ss[] >>
    metis_tac[IN_IMAGE],
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `?b. b IN G /\ (f b = y)` by rw_tac std_ss[] >>
    `?c. c IN G /\ (f c = z)` by rw_tac std_ss[] >>
    `h.op x y = f (a * b)` by rw_tac std_ss[] >>
    `h.op y z = f (b * c)` by rw_tac std_ss[] >>
    `a * b IN G /\ b * c IN G` by rw[] >>
    `h.op (h.op x y) z = f ((a * b) * c)` by metis_tac[] >>
    `h.op x (h.op y z) = f (a * (b * c))` by metis_tac[] >>
    `a * b * c = a * (b * c)` by rw[monoid_assoc] >>
    metis_tac[],
    metis_tac[monoid_id_element, IN_IMAGE],
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `h.op h.id x = f (#e * a)` by rw_tac std_ss[monoid_id_element] >>
    metis_tac[monoid_lid],
    `x IN h.carrier` by metis_tac[] >>
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `h.op x h.id = f (a * #e)` by rw_tac std_ss[monoid_id_element] >>
    metis_tac[monoid_rid]
  ]);

(*
GroupHomo_def is weaker than MonoidHomo_def.
May need to define  GroupHomo = MonoidHomo, making f #e = h.id mandatory.
Better keep GroupHomo, just use MonoidHomo if necessary.
*)

(* Theorem: Group g /\ MonoidHomo f g h ==> Group (homo_image f g h) *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid (homo_image f g h), true   by monoid_homo_homo_image_monoid
   (2) monoid_invertibles (homo_image f g h) = (homo_image f g h).carrier
       By monoid_invertibles_def, homo_image_def, this is to show:
       x IN IMAGE f G ==> ?y. y IN IMAGE f G /\ (h.op x y = h.id) /\ (h.op y x = h.id)

       Note ?a. a IN G /\ (f a = x)      by x IN IMAGE f G
      Hence |/ a IN G                    by group_inv_element
        Let y = f ( |/ a).
       Then y IN IMAGE f G               by IN_IMAGE
            h.op y x
          = h.op (f ( |/ a)) (f a)
          = f ( |/a * a)                 by MonoidHomo_def
          = f #e                         by group_linv
          = h.id                         by MonoidHomo_def
            h.op x y
          = h.op (f a) (f ( |/ a))
          = f (a * |/a )                 by MonoidHomo_def
          = f #e                         by group_rinv
          = h.id                         by MonoidHomo_def
*)
val group_homo_homo_image_group = store_thm(
  "group_homo_homo_image_group",
  ``!(g:'a group) (h:'b group) f. Group g /\ MonoidHomo f g h ==> Group (homo_image f g h)``,
  rpt strip_tac >>
  `Monoid (homo_image f g h)` by rw[monoid_homo_homo_image_monoid] >>
  rw_tac std_ss[Group_def, monoid_invertibles_def, homo_image_def, GSPECIFICATION, EXTENSION, EQ_IMP_THM] >>
  `?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  `|/ a IN G` by rw[] >>
  `( |/ a * a = #e) /\ (a * |/ a = #e)` by rw[] >>
  `f ( |/ a) IN IMAGE f G` by metis_tac[IN_IMAGE] >>
  metis_tac[MonoidHomo_def]);

(* ------------------------------------------------------------------------- *)
(* First Isomorphic Theorem for Group.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==>
            GroupHomo (\z. (CHOICE (preimage f G z)) * (kernel f g h) ) (homo_image f g h) (g / (kernel_group f g h)) *)
(* Proof: by GroupHomo_def, homo_image_def and quotient_group_def.
   This is to show:
   (1) !z. z IN IMAGE f G ==> CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h)
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   Since (kernel_group f g h) <= g  by kernel_group_subgroup
   Hence CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h) by coset_partition_element
   and
   (2) !z. z IN IMAGE f G /\ z' IN IMAGE f G ==>
   CHOICE (preimage f G (h.op z z')) * kernel f g h =
   coset_op g (kernel_group f g h) (CHOICE (preimage f G z) * kernel f g h) (CHOICE (preimage f G z') * kernel f g h)
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   After expanding by coset_op_def, this is to show:
   CHOICE (preimage f G (h.op z z')) * kernel f g h =
   cogen g (kernel_group f g h) (CHOICE (preimage f G z) * kernel f g h) *
   cogen g (kernel_group f g h) (CHOICE (preimage f G z') * kernel f g h) * kernel f g h
   Now, (kernel_group f g h) << g    by kernel_group_normal
   Let x = CHOICE (preimage f G z
       x' = CHOICE (preimage f G z'
       y = CHOICE (preimage f G (h.op z z'))
       k = kernel_group f g h
       s = kernel f g h
   This is to show: y * s = cogen g k (x * s) * cogen g k (x' * s) * s
   This can be done via normal_coset_property, but first:
   x IN G /\ x' IN G /\ (f x = z) /\ (f x' = z')   by preimage_choice_property
   x * s IN CosetPartition g k    by coset_partition_element
   x' * s IN CosetPartition g k   by coset_partition_element
   Hence
   cogen g k (x * s) * cogen g k (x' * s) * s = x * x' * s  by normal_coset_property
   It remains to show: y * s = x * x' * s
   i.e. to show: y / (x * x') IN s   since k << g  if we know y IN G and x * x' IN G
   But h.op z z' = f (x * x')    by GroupHomo_def
   Hence x * x' IN G /\ f (x * x') IN IMAGE f G   by group_op_element, IN_IMAGE
   and f y = h.op z z' = f (x * x') by preimage_choice_property
   Hence we just need to show: y / (x * x') IN s  where s = kernel f g h
   An element is in kernel if it maps to h.id, so compute:
     f (y / (x * x'))
   = f (y * |/ (x * x'))          by group_div_def
   = h.op (f y) f ( |/ (x * x'))   by GroupHomo_def
   = h.op (f y) h.inv f (x * x')  by group_homo_inv
   = h.op (f y) h.inv (f y)       by above
   = h.id                         by group_rinv
*)
val homo_image_homo_quotient_kernel = store_thm(
  "homo_image_homo_quotient_kernel",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
            GroupHomo (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                     (homo_image f g h) (g / (kernel_group f g h))``,
  rw_tac std_ss[homo_image_def, quotient_group_def] >>
  `(kernel_group f g h).carrier = kernel f g h` by rw_tac std_ss[kernel_group_def] >>
  rw_tac std_ss[GroupHomo_def] >| [
    metis_tac[preimage_choice_property, kernel_group_subgroup, coset_partition_element],
    rw_tac std_ss[coset_op_def] >>
    `(kernel_group f g h) << g /\ (kernel_group f g h) <= g` by rw_tac std_ss[kernel_group_normal, normal_subgroup_subgroup] >>
    qabbrev_tac `x = CHOICE (preimage f G z)` >>
    qabbrev_tac `x' = CHOICE (preimage f G z')` >>
    qabbrev_tac `y = CHOICE (preimage f G (h.op z z'))` >>
    qabbrev_tac `k = kernel_group f g h` >>
    qabbrev_tac `s = kernel f g h` >>
    `x IN G /\ x' IN G /\ (f x = z) /\ (f x' = z')` by rw_tac std_ss[preimage_choice_property, Abbr`x`, Abbr`x'`] >>
    `x * s IN CosetPartition g k /\ x' * s IN CosetPartition g k` by metis_tac[coset_partition_element] >>
    `cogen g k (x * s) * cogen g k (x' * s) * s = x * x' * s` by rw_tac std_ss[normal_coset_property] >>
    full_simp_tac std_ss [] >>
    `h.op z z' = f (x * x')` by metis_tac[GroupHomo_def] >>
    `x * x' IN G /\ f (x * x') IN IMAGE f G` by rw[] >>
    `y IN G /\ (f y = h.op z z')` by metis_tac[preimage_choice_property] >>
    `y / (x * x') IN s` suffices_by rw_tac std_ss[normal_subgroup_coset_eq] >>
    `|/ (x * x') IN G` by rw[] >>
    `f y IN h.carrier` by metis_tac[GroupHomo_def] >>
    `f (y / (x * x')) = f (y * |/ (x * x'))` by rw_tac std_ss[group_div_def] >>
    `_ = h.op (f y) (f ( |/ (x * x')))` by metis_tac[GroupHomo_def] >>
    `_ = h.op (f y) (h.inv (h.op z z'))` by metis_tac[group_homo_inv] >>
    `_ = h.id` by metis_tac[group_rinv] >>
    metis_tac[kernel_property, group_div_element]
  ]);

(* Theorem:  BIJ (\z. CHOICE (preimage f G z) * kernel f g h)
             (homo_image f g h).carrier (g / kernel_group f g h).carrier *)
(* Proof:
   This is to prove:
   (1) z IN IMAGE f G ==> CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h)
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   Since (kernel_group f g h) <= g  by kernel_group_subgroup
   Hence CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h) by coset_partition_element
   (2) z IN IMAGE f G /\ z' IN IMAGE f G /\ CHOICE (preimage f G z) * kernel f g h = CHOICE (preimage f G z') * kernel f g h ==> z = z'
   Let x = CHOICE (preimage f G z)
       x' = CHOICE (preimage f G z'), then
   z IN IMAGE f G ==> x IN G /\ f x = z  by preimage_choice_property
   z' IN IMAGE f G ==> x' IN G /\ f x' = z'  by preimage_choice_property
   x IN G ==> z = f x IN H, x' IN G ==> z' = f x' IN H   by GroupHomo_def
   Given  x * kernel f g h = x' * kernel f g h
   Since (kernel_group f g h) << g      by kernel_group_normal
   this gives  x / x' IN kernel f g h   by normal_subgroup_coset_eq
   Hence    f (x / x') = h.id           by kernel_property
   i.e. h.id = f (x / x')
             = f (x * |/ x')            by group_div_def
             = h.op (f x) (f ( |/ x'))   by GroupHomo_def
             = h.op (f x) h.inv (f x')  by group_homo_inv
             = h.op z h.inv z'          by above
   Hence z = z'  by group_linv_unique, group_inv_inv
   (3) same as (1).
   (4) x IN CosetPartition g (kernel_group f g h) ==> ?z. z IN IMAGE f G /\ (CHOICE (preimage f G z) * kernel f g h = x)
   Note (kernel_group f g h) << g          by kernel_group_normal
   and (kernel_group f g h) <= g           by normal_subgroup_subgroup
   Since x IN CosetPartition g (kernel_group f g h),
   ?a. a IN G /\ (x = a * kernel f g h)    by coset_partition_element
   Let z = f a, then z IN IMAGE f G    by IN_IMAGE,
   and CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)  by preimage_choice_property
   Thus, this is to prove:
   CHOICE (preimage f G z) * kernel f g h = x = a * kernel f g h
   Since kernel f g h << g, this is true if  CHOICE (preimage f G z) / a IN kernel f g h
   or need to show: f (CHOICE (preimage f G z) / a) = h.id  by normal_subgroup_coset_eq
   By computation,
     f (CHOICE (preimage f G z) / a)
   = f (CHOICE (preimage f G z) * |/ a)             by group_div_def
   = h.op (f (CHOICE (preimage f G z)) (f ( |/ a))   by GroupHomo_def
   = h.op z (h.inv z)                               by group_homo_inv
   = h.id                                           by group_linv
*)
val homo_image_to_quotient_kernel_bij = store_thm(
  "homo_image_to_quotient_kernel_bij",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
            BIJ (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                     (homo_image f g h).carrier (g / (kernel_group f g h)).carrier``,
  rw_tac std_ss[homo_image_def, quotient_group_def] >>
  `(kernel_group f g h).carrier = kernel f g h` by rw_tac std_ss[kernel_group_def] >>
  rw_tac std_ss[BIJ_DEF, SURJ_DEF, INJ_DEF] >| [
    metis_tac[preimage_choice_property, kernel_group_subgroup, coset_partition_element],
    `CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)` by rw_tac std_ss[preimage_choice_property] >>
    `CHOICE (preimage f G z') IN G /\ (f (CHOICE (preimage f G z')) = z')` by rw_tac std_ss[preimage_choice_property] >>
    `(kernel_group f g h) << g` by rw_tac std_ss[kernel_group_normal] >>
    qabbrev_tac `x = CHOICE (preimage f G z)` >>
    qabbrev_tac `x' = CHOICE (preimage f G z')` >>
    qabbrev_tac `k = kernel_group f g h` >>
    qabbrev_tac `s = kernel f g h` >>
    `|/ x' IN G` by rw[] >>
    `f ( |/ x') = h.inv z'` by rw_tac std_ss[group_homo_inv] >>
    `z IN h.carrier /\ z' IN h.carrier /\ h.inv z' IN h.carrier` by metis_tac[GroupHomo_def] >>
    `x / x' IN s` by metis_tac[normal_subgroup_coset_eq] >>
    `h.id = f (x / x')` by metis_tac[kernel_property] >>
    `_ = f (x * |/ x')` by rw_tac std_ss[group_div_def] >>
    `_ = h.op (f x) (h.inv (f x'))` by metis_tac[GroupHomo_def] >>
    metis_tac[group_linv_unique, group_inv_inv],
    metis_tac[preimage_choice_property, kernel_group_subgroup, coset_partition_element],
    `(kernel_group f g h) << g /\ (kernel_group f g h) <= g` by rw_tac std_ss[kernel_group_normal, normal_subgroup_subgroup] >>
    `?a. a IN G /\ (x = a * kernel f g h)` by metis_tac[coset_partition_element] >>
    qexists_tac `f a` >>
    rw[] >>
    qabbrev_tac `z = f a` >>
    qabbrev_tac `x = CHOICE (preimage f G z)` >>
    qabbrev_tac `k = kernel_group f g h` >>
    qabbrev_tac `s = kernel f g h` >>
    `x IN G /\ (f x = z) /\ z IN h.carrier` by metis_tac[preimage_choice_property, IN_IMAGE, GroupHomo_def] >>
    `x / a IN s` suffices_by metis_tac[normal_subgroup_coset_eq] >>
    `|/a IN G` by rw[] >>
    `f (x * |/ a) = h.op (f x) (f ( |/ a))` by metis_tac[GroupHomo_def] >>
    `_ = h.op z (h.inv z)` by metis_tac[group_homo_inv] >>
    `_ = h.id` by metis_tac[group_rinv] >>
    metis_tac[kernel_property, group_div_def, group_div_element]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==>
            GroupIso (\z. (CHOICE (preimage f G z)) * (kernel f g h) ) (homo_image f g h) (g / (kernel_group f g h)) *)
(* Proof: by GroupIso_def.
   (1) GroupHomo (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h)
   True by homo_image_homo_quotient_kernel.
   (2) BIJ (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h).carrier (g / kernel_group f g h).carrier
   True by homo_image_to_quotient_kernel_bij.
*)
val homo_image_iso_quotient_kernel = store_thm(
  "homo_image_iso_quotient_kernel",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
            GroupIso (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                     (homo_image f g h) (g / (kernel_group f g h))``,
  rw[GroupIso_def, homo_image_homo_quotient_kernel, homo_image_to_quotient_kernel_bij]);

(* Theorem [First Isomorphism Theorem for Groups]
   Let G and H be groups, and let f: G -> H be a homomorphism. Then:
   (a) The kernel of f is a normal subgroup of G,
   (b) The image of f is a subgroup of H, and
   (c) The image of f is isomorphic to the quotient group G / ker(f).
   In particular, (d) if f is surjective then H is isomorphic to G / ker(f).
*)
(* Proof:
   (a) by kernel_group_normal
   (b) by homo_image_subgroup
   (c) by homo_image_iso_quotient_kernel
   (d) by group_homo_image_surj_property
*)
val group_first_isomorphism_thm = store_thm(
  "group_first_isomorphism_thm",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
      (kernel_group f g h) << g /\
      (homo_image f g h) <= h /\
      GroupIso (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                    (homo_image f g h) (g / (kernel_group f g h)) /\
      (SURJ f G h.carrier ==> GroupIso I h (homo_image f g h))``,
  rw[kernel_group_normal, homo_image_subgroup, homo_image_iso_quotient_kernel, group_homo_image_surj_property]);

(* ------------------------------------------------------------------------- *)
(* Iterated Product Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   FUN_COMM op f  = !x y z. op (f x) (op (f y) z) = op (f y) (op (f x) z)
#  GPI f s        = GROUP_IMAGE g f s
#  gfun f         = group_fun g f
*)
(* Definitions and Theorems (# are exported):

   Fermat's Little Theorem of Abelian Groups:
   GPROD_SET_IMAGE            |- !g a. Group g /\ a IN G ==> (GPROD_SET g (a * G) = GPROD_SET g G)
   GPROD_SET_REDUCTION_INSERT |- !g s. FiniteAbelianGroup g /\ s SUBSET G ==>
                                 !a x::(G). x NOTIN s ==>
                          (a * x * GPROD_SET g (a * (G DIFF (x INSERT s))) = GPROD_SET g (a * (G DIFF s)))
   GPROD_SET_REDUCTION        |- !g s. FiniteAbelianGroup g /\ s SUBSET G ==>
                       !a::(G). a ** CARD s * GPROD_SET g s * GPROD_SET g (a * (G DIFF s)) = GPROD_SET g G

   Group Factorial:
   GFACT_def              |- !g. GFACT g = GPROD_SET g G
   GFACT_element          |- !g. FiniteAbelianMonoid g ==> GFACT g IN G
   GFACT_identity         |- !g a. FiniteAbelianGroup g /\ a IN G ==> (GFACT g = a ** CARD G * GFACT g)
   finite_abelian_Fermat  |- !g a. FiniteAbelianGroup g /\ a IN G ==> (a ** CARD G = #e)

   Group Iterated Product over a function:
   OP_IMAGE_DEF    |- !op id f s. OP_IMAGE op id f s = ITSET (\e acc. op (f e) acc) s id
   OP_IMAGE_EMPTY  |- !op id f. OP_IMAGE op id f {} = id
   OP_IMAGE_SING   |- !op id f x. OP_IMAGE op id f {x} = op (f x) id
   OP_IMAGE_THM    |- !op id f. (OP_IMAGE op id f {} = id) /\
                                (FUN_COMM op f ==> !s. FINITE s ==>
                      !e. OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e)))

   GROUP_IMAGE_DEF          |- !g f s. GPI f s = ITSET (\e acc. f e * acc) s #e
   group_image_as_op_image  |- !g. GPI = OP_IMAGE $* #e
   sum_image_as_op_image    |- SIGMA = OP_IMAGE (\x y. x + y) 0
   prod_image_as_op_image   |- PI = OP_IMAGE (\x y. x * y) 1
   GITSET_AS_ITSET          |- !g. (\s b. GITSET g s b) = ITSET (\e acc. e * acc)
   GPROD_SET_AS_GROUP_IMAGE |- !g. GPROD_SET g = GPI I
   group_image_empty        |- !g f. GPI f {} = #e
   group_fun_def            |- !g f. gfun f <=> !x. x IN G ==> f x IN G
   group_image_sing         |- !g. Monoid g ==> !f. gfun f ==> !x. x IN G ==> (GPI f {x} = f x)

*)


(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem of Abelian Groups.                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For Group g, a IN G ==> GPROD_SET g a * G = GPROD_SET g G *)
(* Proof:
   This is trivial by group_coset_eq_itself.
*)
val GPROD_SET_IMAGE = store_thm(
  "GPROD_SET_IMAGE",
  ``!g a. Group g /\ a IN G ==> (GPROD_SET g (a * G) = GPROD_SET g G)``,
  rw[group_coset_eq_itself]);

(* ------------------------------------------------------------------------- *)
(* An Invariant Property when reducing GPROD_SET g (IMAGE (\z. a*z) G):
     GPROD_SET g (IMAGE (\z. a*z) G)
   = (a*z) * GPROD_SET g ((IMAGE (\z. a*z) G) DELETE (a*z))
   = a * (GPROD_SET g (z INSERT {})) * GPROD_SET g (IMAGE (\z. a*z) (G DELETE z))
   = a * <building up a GPROD_SET> * <reducing down a GPROD_SET>
   = a*a * <building one more> * <reducing one more>
   = a*a*a * <building one more> * <reducing one more>
   = a**(CARD G) * GPROD_SET g G * GPROD_SET g {}
   = a**(CARD G) * GPROD_SET g G * #e
   = a**(CARD G) * GPROD_SET g G
*)
(* ------------------------------------------------------------------------- *)

(* Theorem: [INSERT for GPROD_SET_REDUCTION]
            (a*x)* GPROD_SET g (coset g (G DIFF (x INSERT t)))
            = GPROD_SET g (coset g (G DIFF t)) *)
(* Proof:
   Essentially this is to prove:
   a * x * GPROD_SET g {a * z | z | z IN G /\ z <> x /\ z NOTIN s} =
           GPROD_SET g {a * z | z | z IN G /\ z NOTIN s}
   Let q = {a * z | z | z IN G /\ z <> x /\ z NOTIN s}
       p = {a * z | z | z IN G /\ z NOTIN s}
   Since p = (a*x) INSERT q   by EXTENSION,
     and (a*x) NOTIN q        by group_lcancel, a NOTIN s.
     and (a*x) IN G           by group_op_element
   RHS = GPROD_SET g p
       = GPROD_SET g ((a*x) INSERT q)            by p = (a*x) INSERT q
       = (a*x) * GPROD_SET g (q DELETE (a*x))    by GPROD_SET_THM
       = (a*x) * GPROD_SET g q                   by DELETE_NON_ELEMENT, (a*x) NOTIN q.
       = LHS
*)
val GPROD_SET_REDUCTION_INSERT = store_thm(
  "GPROD_SET_REDUCTION_INSERT",
  ``!g s. FiniteAbelianGroup g /\ s SUBSET G ==>
   !a x::(G). x NOTIN s ==>
   (a * x * GPROD_SET g (a * (G DIFF (x INSERT s))) = GPROD_SET g (a * (G DIFF s)))``,
  rw[coset_def, IMAGE_DEF, EXTENSION, RES_FORALL_THM] >>
  qabbrev_tac `p = {a * z | z | z IN G /\ z NOTIN s}` >>
  qabbrev_tac `q = {a * z | z | z IN G /\ z <> x /\ z NOTIN s}` >>
  (`p = (a * x) INSERT q` by (rw[EXTENSION, EQ_IMP_THM, Abbr`p`, Abbr`q`] >> metis_tac[])) >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def] >>
  `!z. z IN G /\ (a * z = a * x) <=> (z = x)` by metis_tac[group_lcancel] >>
  (`(a * x) NOTIN q` by (rw[Abbr`q`] >> metis_tac[])) >>
  (`q SUBSET G` by (rw[EXTENSION, SUBSET_DEF, Abbr`q`] >> rw[])) >>
  `a * x IN G` by rw[] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  `FINITE q` by metis_tac[SUBSET_FINITE] >>
  metis_tac[GPROD_SET_THM, DELETE_NON_ELEMENT]);

(* Theorem: (a ** n) * <building n-steps GPROD_SET> * <reducing n-steps GPROD_SET> = GPROD_SET g G *)
(* Proof:
   By complete induction on CARD s.
   Case s = {},
     LHS = a ** (CARD s) * (GPROD_SET g s) * GPROD_SET g (a * (G DIFF s))
         = a ** 0 * (GPROD_SET g {}) * GPROD_SET g (a * (G DIFF {}))        by CARD_EMPTY
         = #e * #e * GPROD_SET g (a * G)      by group_exp_0, DIFF_EMPTY, GPROD_SET_EMPTY.
         = GPROD_SET g (a * G)                by group_lid
         = GPROD_SET g G                      by GPROD_SET_IMAGE
         = RHS
   Case s <> {},
     Let x = CHOICE s, t = REST s, so s = x INSERT t, x NOTIN t.
     LHS = a ** (CARD s) * (GPROD_SET g s) * GPROD_SET g (a * (G DIFF s))
         = a ** SUC(CARD t) *
           (GPROD_SET g (x INSERT t)) *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by CARD s = SUC(CARD t), s = x INSERT t.
         = a ** SUC(CARD t) *
           (x * GPROD_SET g (t DELETE x)) *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by GPROD_SET_THM
         = a ** SUC(CARD t) *
           (x * GPROD_SET g t) *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by DELETE_NON_ELEMENT, x NOTIN t.
         = a*a ** (CARD t) *
           x * GPROD_SET g t *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by group_exp_SUC
         = a ** (CARD t) *
           GPROD_SET g t *
           (a * x) * GPROD_SET g (a * (G DIFF (x INSERT t)))  by Abelian group commuting
         = a ** (CARD t) *
           GPROD_SET g t *
           GPROD_SET g (a * (G DIFF t))   by GPROD_SET_REDUCTION_INSERT
         = RHS                            by induction
*)
val GPROD_SET_REDUCTION = store_thm(
  "GPROD_SET_REDUCTION",
  ``!g s. FiniteAbelianGroup g /\ s SUBSET G ==>
   !a::(G). a ** (CARD s) * (GPROD_SET g s) * GPROD_SET g (a * (G DIFF s)) = GPROD_SET g G``,
  completeInduct_on `CARD s` >>
  pop_assum (assume_tac o SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw[RES_FORALL_THM] >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  Cases_on `s = {}` >| [
    rw[GPROD_SET_EMPTY] >>
    `GPROD_SET g G IN G` by rw[GPROD_SET_PROPERTY] >>
    rw[GPROD_SET_IMAGE],
    `?x t. (x = CHOICE s) /\ (t = REST s) /\ (s = x INSERT t)` by rw[CHOICE_INSERT_REST] >>
    `x IN G` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
    `t SUBSET G /\ FINITE t` by metis_tac[REST_SUBSET, SUBSET_TRANS, SUBSET_FINITE] >>
    `x NOTIN t` by metis_tac[CHOICE_NOT_IN_REST] >>
    `(CARD s = SUC(CARD t)) /\ CARD t < CARD s` by rw[CARD_INSERT] >>
    `GPROD_SET g t IN G` by rw[GPROD_SET_PROPERTY] >>
    `GPROD_SET g (a * (G DIFF (x INSERT t))) IN G` by metis_tac[coset_property, DIFF_SUBSET, SUBSET_FINITE, GPROD_SET_PROPERTY] >>
    qabbrev_tac `t' = a * (G DIFF (x INSERT t))` >>
    `a ** CARD s * GPROD_SET g s * GPROD_SET g (a * (G DIFF s)) =
    a ** SUC(CARD t) * GPROD_SET g (x INSERT t) * GPROD_SET g t'` by rw[Abbr`t'`] >>
    `_ = a ** SUC(CARD t) * (x * GPROD_SET g (t DELETE x)) * GPROD_SET g t'` by rw[GPROD_SET_THM] >>
    `_ = a ** SUC(CARD t) * (x * GPROD_SET g t) * GPROD_SET g t'` by metis_tac[DELETE_NON_ELEMENT] >>
    `_ = (a * a ** (CARD t)) * (x * GPROD_SET g t) * GPROD_SET g t'` by rw[group_exp_SUC] >>
    `_ = (a ** (CARD t) * a) * (x * GPROD_SET g t) * GPROD_SET g t'` by metis_tac[AbelianGroup_def, group_exp_element] >>
    `_ = a ** (CARD t) * (a * (x * GPROD_SET g t)) * GPROD_SET g t'` by rw[group_assoc] >>
    `_ = a ** (CARD t) * ((a * x) * GPROD_SET g t) * GPROD_SET g t'` by rw[group_assoc] >>
    `_ = a ** (CARD t) * (GPROD_SET g t * (a * x)) * GPROD_SET g t'` by metis_tac[AbelianGroup_def, group_op_element] >>
    `_ = (a ** (CARD t) * GPROD_SET g t) * (a * x) * GPROD_SET g t'` by rw[group_assoc] >>
    `_ = a ** (CARD t) * GPROD_SET g t * ((a * x) * GPROD_SET g t')` by rw[group_assoc] >>
    `_ = a ** (CARD t) * GPROD_SET g t * GPROD_SET g (a * (G DIFF t))` by metis_tac[GPROD_SET_REDUCTION_INSERT] >>
    rw[]
  ]);

(* Define Group Factorial *)
val GFACT_def = Define`
  GFACT g = GPROD_SET g G
`;

(* Theorem: GFACT g is an element in Group g. *)
(* Proof:
   Since G SUBSET G     by SUBSET_REFL
   This is true by GPROD_SET_PROPERTY:
   !g s. FiniteAbelianMonoid g /\ s SUBSET G ==> GPROD_SET g s IN G : thm
*)
val GFACT_element = store_thm(
  "GFACT_element",
  ``!g. FiniteAbelianMonoid g ==> GFACT g IN G``,
  rw_tac std_ss[FiniteAbelianMonoid_def, GFACT_def, GPROD_SET_PROPERTY, SUBSET_REFL]);

(* Theorem: For FiniteAbelian Group g, a IN G ==> GFACT g = a ** (CARD g) * GFACT g *)
(* Proof:
   Since G SUBSET G  by SUBSET_REFL,
   and G DIFF G = {},
   Put s = G in GPROD_SET_REDUCTION:
       a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * (G DIFF G)) = GPROD_SET g G
   ==> a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * {}) = GPROD_SET g G
   ==> a ** (CARD G) * GPROD_SET g G * GPROD_SET g {} = GPROD_SET g G  by coset_empty.
   ==> a ** (CARD G) * GPROD_SET g G * #e = GPROD_SET g G              by GPROD_SET_EMPTY.
   ==> a ** (CARD G) * GPROD_SET g G = GPROD_SET g G                   by group_assoc and group_rid
*)
val GFACT_identity = store_thm(
  "GFACT_identity",
  ``!(g:'a group) a. FiniteAbelianGroup g /\ a IN G ==> (GFACT g = a ** (CARD G) * GFACT g)``,
  rw[GFACT_def] >>
  `G SUBSET G` by rw[] >>
  `G DIFF G = {}` by rw[] >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  `GPROD_SET g G IN G` by rw[GPROD_SET_PROPERTY] >>
  `GPROD_SET g G = a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * (G DIFF G))` by rw[GPROD_SET_REDUCTION] >>
  `_ = a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * {})` by rw[] >>
  `_ = a ** (CARD G) * GPROD_SET g G * GPROD_SET g {}` by rw[coset_empty] >>
  `_ = a ** (CARD G) * GPROD_SET g G * #e` by metis_tac[GPROD_SET_EMPTY] >>
  `_ = a ** (CARD G) * GPROD_SET g G` by rw[] >>
  rw[]);

(* Theorem: For FiniteAbelian Group g, a IN G ==> a ** (CARD g) = #e *)
(* Proof:
   Since  a ** (CARD G) * GFACT g = GFACT g    by GFACT_identity
   Hence  a ** (CARD G) = #e                   by group_lid_unique
*)
val finite_abelian_Fermat = store_thm(
  "finite_abelian_Fermat",
  ``!(g:'a group) a. FiniteAbelianGroup g /\ a IN G ==> (a ** (CARD G) = #e)``,
  rpt strip_tac >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  `GFACT g IN G` by rw[GFACT_element] >>
  `a ** (CARD G) * GFACT g = GFACT g` by rw[GFACT_identity] >>
  metis_tac[group_exp_element, group_lid_unique]);


(* ------------------------------------------------------------------------- *)
(* Group Iterated Product over a function.                                   *)
(* ------------------------------------------------------------------------- *)

(*
> show_types := true; ITSET_def; show_types := false;
val it = |- !(s :'a -> bool) (f :'a -> 'b -> 'b) (b :'b).
    ITSET f s b = if FINITE s then if s = ({} :'a -> bool) then b
                                   else ITSET f (REST s) (f (CHOICE s) b)
                  else (ARB :'b): thm

> show_types := true; SUM_IMAGE_DEF; show_types := false;
val it = |- !(f :'a -> num) (s :'a -> bool).
    SIGMA f s = ITSET (\(e :'a) (acc :num). f e + acc) s (0 :num): thm

> ITSET_def |> ISPEC ``s:'b -> bool`` |> ISPEC ``(f:'b -> 'a)`` |> ISPEC ``b:'a``;
val it = |- GITSET g s b = if FINITE s then if s = {} then b else GITSET g (REST s) (CHOICE s * b)
                           else ARB: thm
*)

(* A general iterator for operation (op:'a -> 'a -> 'a) and (id:'a) *)
val OP_IMAGE_DEF = Define `
    OP_IMAGE (op:'a -> 'a -> 'a) (id:'a) (f:'b -> 'a) (s:'b -> bool) = ITSET (\e acc. op (f e) acc) s id
`;

(* Theorem: OP_IMAGE op id f {} = id *)
(* Proof:
     OP_IMAGE op id f {}
   = ITSET (\e acc. op (f e) acc) {} id    by OP_IMAGE_DEF
   = id                                    by ITSET_EMPTY
*)
val OP_IMAGE_EMPTY = store_thm(
  "OP_IMAGE_EMPTY",
  ``!op id f. OP_IMAGE op id f {} = id``,
  rw[OP_IMAGE_DEF, ITSET_EMPTY]);

(* Theorem: OP_IMAGE op id f {x} = op (f x) id *)
(* Proof:
     OP_IMAGE op id f {x}
   = ITSET (\e acc. op (f e) acc) {x} id    by OP_IMAGE_DEF
   = (\e acc. op (f e) acc) x id            by ITSET_SING
   = op (f x) id                            by application
*)
val OP_IMAGE_SING = store_thm(
  "OP_IMAGE_SING",
  ``!op id f x. OP_IMAGE op id f {x} = op (f x) id``,
  rw[OP_IMAGE_DEF, ITSET_SING]);

(*
Now the hard part: show (\e acc. op (f e) acc) is an accumulative function for ITSET.

val SUM_IMAGE_THM = store_thm(
  "SUM_IMAGE_THM",
  ``!f. (SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (SUM_IMAGE f (e INSERT s) =
                f e + SUM_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC THENL [
    SIMP_TAC (srw_ss()) [ITSET_THM, SUM_IMAGE_DEF],
    SIMP_TAC (srw_ss()) [SUM_IMAGE_DEF] THEN
    Q.ABBREV_TAC `g = \e acc. f e + acc` THEN
    Q_TAC SUFF_TAC `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)` THEN1
       SRW_TAC [][Abbr`g`] THEN
    MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
    SRW_TAC [ARITH_ss][Abbr`g`]
  ]);

val PROD_IMAGE_THM = store_thm(
  "PROD_IMAGE_THM",
  ``!f. (PROD_IMAGE f {} = 1) /\
        (!e s. FINITE s ==>
          (PROD_IMAGE f (e INSERT s) = f e * PROD_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC THEN1
    SIMP_TAC (srw_ss()) [ITSET_THM, PROD_IMAGE_DEF] THEN
  SIMP_TAC (srw_ss()) [PROD_IMAGE_DEF] THEN
  Q.ABBREV_TAC `g = \e acc. f e * acc` THEN
  Q_TAC SUFF_TAC `ITSET g (e INSERT s) 1 =
                  g e (ITSET g (s DELETE e) 1)` THEN1 SRW_TAC [][Abbr`g`] THEN
  MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
  SRW_TAC [ARITH_ss][Abbr`g`]);

*)

(* Overload a communtative operation *)
val _ = overload_on("FUN_COMM", ``\op f. !x y z. op (f x) (op (f y) z) = op (f y) (op (f x) z)``);

(* Theorem: (OP_IMAGE op id f {} = id)  /\
            (FUN_COMM op f ==> !s. FINITE s ==>
             !e. OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e))) *)
(* Proof:
   First goal: P_IMAGE op id f {} = id
      True by OP_IMAGE_EMPTY.
   Second goal: OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e)))
      Let g = \e acc. op (f e) acc,
      Then by OP_IMAGE_DEF, the goal is:
      to show: ITSET g (e INSERT s) id = op (f e) (ITSET g (s DELETE e) id)
      or show: ITSET g (e INSERT s) id = g e (ITSET g (s DELETE e) id)
      Given FUN_COMM op f, the is true by COMMUTING_ITSET_RECURSES.
*)
val OP_IMAGE_THM = store_thm(
  "OP_IMAGE_THM",
  ``!op id f. (OP_IMAGE op id f {} = id)  /\
   (FUN_COMM op f ==> !s. FINITE s ==>
    !e. OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e)))``,
  rpt strip_tac >-
  rw[OP_IMAGE_EMPTY] >>
  rw[OP_IMAGE_DEF] >>
  qabbrev_tac `g = \e acc. op (f e) acc` >>
  rw[] >>
  rw[COMMUTING_ITSET_RECURSES, Abbr`g`]);

(* A better iterator for group operation over (f:'b -> 'a) *)
val GROUP_IMAGE_DEF = Define `
    GROUP_IMAGE (g:'a group) (f:'b -> 'a) (s:'b -> bool) = ITSET (\e acc. (f e) * acc) s #e
`;

(* overload GROUP_IMAGE *)
val _ = temp_overload_on("GPI", ``GROUP_IMAGE g``);

(*
> GROUP_IMAGE_DEF;
val it = |- !g f s. GPI f s = ITSET (\e acc. f e * acc) s #e: thm
*)

(* Theorem: GPI = OP_IMAGE (g.op) (g.id) *)
(* Proof: by GROUP_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM *)
val group_image_as_op_image = store_thm(
  "group_image_as_op_image",
  ``!g:'a group. GPI = OP_IMAGE (g.op) (g.id)``,
  rw[GROUP_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM]);

(* Theorem: SUM_IMAGE = OP_IMAGE (\(x y):num. x + y) 0 *)
(* Proof: by SUM_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM *)
val sum_image_as_op_image = store_thm(
  "sum_image_as_op_image",
  ``SIGMA = OP_IMAGE (\(x y):num. x + y) 0``,
  rw[SUM_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM]);

(* Theorem: PROD_IMAGE = OP_IMAGE (\(x y):num. x * y) 1 *)
(* Proof: by PROD_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM *)
val prod_image_as_op_image = store_thm(
  "prod_image_as_op_image",
  ``PI = OP_IMAGE (\(x y):num. x * y) 1``,
  rw[PROD_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM]);

(*
val _ = clear_overloads_on("GITSET");
val _ = clear_overloads_on("GPI");
val _ = overload_on("GITSET", ``\g s b. ITSET g.op s b``);
val _ = overload_on("GPI", ``GROUP_IMAGE g``);
*)

(* val _ = overload_on("GITSET", ``\g s b. ITSET g.op s b``); *)

(* Theorem: GITSET g = ITSET (\e acc. g.op e acc) *)
(* Proof:
   Note g.op = (\e acc. e * acc)   by FUN_EQ_THM

     GITSET g s b
   = ITSET g.op s b                by notation
   = ITSET (\e acc. e * acc) s b   by ITSET_CONG

   Hence GITSET g = ITSET (\e acc. g.op e acc)  by FUN_EQ_THM
*)
val GITSET_AS_ITSET = store_thm(
  "GITSET_AS_ITSET",
  ``!g:'a group. GITSET g = ITSET (\e acc. g.op e acc)``,
  rw[FUN_EQ_THM] >>
  `g.op = (\e acc. e * acc)` by rw[FUN_EQ_THM] >>
  `ITSET g.op = ITSET (\e acc. e * acc)` by rw[ITSET_CONG] >>
  rw[]);

(*
> ITSET_def |> ISPEC ``s:'b -> bool`` |> ISPEC ``(g:'a group).op`` |> ISPEC ``b:'a``;
val it = |- GITSET g s b = if FINITE s then if s = {} then b else GITSET g (REST s) (CHOICE s * b)
                           else ARB: thm
*)

(* Theorem: GPROD_SET g = GPI I *)
(* Proof:
   Note g.op = (\e acc. e * acc)    by FUN_EQ_THM

     GPROD_SET g x
   = GITSET g x #e                  by GPROD_SET_def
   = ITSET g.op x #e                by notation
   = ITSET (\e acc. e * acc) x #e   by above
   = GPI I x                        by GROUP_IMAGE_DEF
   Hence GPROD_SET g = GPI I        by FUN_EQ_THM
*)
val GPROD_SET_AS_GROUP_IMAGE = store_thm(
  "GPROD_SET_AS_GROUP_IMAGE",
  ``!g:'a group. GPROD_SET g = GPI I``,
  rw[FUN_EQ_THM] >>
  `g.op = (\e acc. e * acc)` by rw[FUN_EQ_THM] >>
  `ITSET g.op = ITSET (\e acc. e * acc)` by rw[ITSET_CONG] >>
  `GPROD_SET g x = GITSET g x #e` by rw[GPROD_SET_def] >>
  `_ = ITSET (\e acc. e * acc) x #e` by rw[] >>
  `_ = GPI I x` by rw[GROUP_IMAGE_DEF] >>
  rw[]);

(* Theorem: GPI f {} = #e *)
(* Proof
     GPI f {}
   = GROUP_IMAGE g f {}               by notation
   = ITSET (\e acc. f e * acc) {} #e  by GROUP_IMAGE_DEF
   = #e                               by ITSET_EMPTY
*)
val group_image_empty = store_thm(
  "group_image_empty",
  ``!g:'a group. !f. GPI f {} = #e``,
  rw[GROUP_IMAGE_DEF, ITSET_EMPTY]);

(* Define a group function *)
val group_fun_def = Define `
    group_fun (g:'a group) f = !x. x IN G ==> f x IN G
`;

(* overload on group function *)
val _ = temp_overload_on("gfun", ``group_fun g``);

(* Theorem: Monoid g ==> !f. gfun f ==> !x. x IN G ==> (GPI f {x} = f x) *)
(* Proof:
   Note x IN G ==> f x IN G            by group_fun_def
     GPI f {x}
   = GROUP_IMAGE g f {x}               by notation
   = ITSET (\e acc. f e * acc) {x} #e  by GROUP_IMAGE_DEF
   = f x * #e                          by ITSET_SING
   = f x                               by monoid_rid
*)
val group_image_sing = store_thm(
  "group_image_sing",
  ``!g:'a group. Monoid g ==> !f. gfun f ==> !x. x IN G ==> (GPI f {x} = f x)``,
  rw[GROUP_IMAGE_DEF, group_fun_def, ITSET_SING]);

(* ------------------------------------------------------------------------- *)
(* Finite Group Order Documentation                                          *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   gen a     = Generated g a
   Gen a     = (Generated g a).carrier
   uroots n  = roots_of_unity g n
   gen_set s = Generated_subset g s
*)
(* Definitions and Theorems (# are exported):

   Finite Group:
   finite_group_card_pos  |- !g. FiniteGroup g ==> 0 < CARD G
   finite_group_exp_not_distinct
                          |- !g. FiniteGroup g ==> !x. x IN G ==> ?h k. (x ** h = x ** k) /\ h <> k
   finite_group_exp_period_exists
                          |- !g. FiniteGroup g ==> !x. x IN G ==> ?k. 0 < k /\ (x ** k = #e)

   Finite Group Order:
   group_order_nonzero    |- !g. FiniteGroup g ==> !x. x IN G ==> ord x <> 0
   group_order_pos        |- !g. FiniteGroup g ==> !x. x IN G ==> 0 < ord x
   group_order_property   |- !g. FiniteGroup g ==> !x. x IN G ==> 0 < ord x /\ (x ** ord x = #e)
   group_order_inv        |- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> ( |/ x = x ** (ord x - 1))
   group_exp_mod          |- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)

   Characterization of Group Order:
   group_order_thm        |- !g n. 0 < n ==>
                             !x. (ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e
   group_order_unique     |- !g. Group g ==> !x. x IN G ==>
                             !m n. m < ord x /\ n < ord x ==> (x ** m = x ** n) ==> (m = n)
   group_exp_equal        |- !g x. Group g /\ x IN G ==>
                             !n m. n < ord x /\ m < ord x /\ (x ** n = x ** m) ==> (n = m)
   finite_group_order     |- !g. FiniteGroup g ==> !x. x IN G ==>
                             !n. (ord x = n) ==>
                                 0 < n /\ (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e
   finite_group_primitive_property
                          |- !g. FiniteGroup g ==> !z. z IN G /\ (ord z = CARD G) ==>
                                                   !x. x IN G ==> ?n. x = z ** n

   Lifting Theorems from Monoid Order:
#  group_order_id         |- !g. Group g ==> (ord #e = 1)
   group_order_eq_1       |- !g. Group g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e))
   group_order_condition  |- !g. Group g ==> !x. x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m
   group_order_power_eq_0 |- !g. Group g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0)
   group_order_power      |- !g. Group g ==> !x. x IN G ==> !k. ord (x ** k) * gcd (ord x) k = ord x
   group_order_power_eqn  |- !g. Group g ==> !x k. x IN G /\ 0 < k ==> (ord (x ** k) = ord x DIV gcd k (ord x))
   group_order_power_coprime
                          |- !g. Group g ==> !x. x IN G ==>
                                             !n. coprime n (ord x) ==> (ord (x ** n) = ord x)
   group_order_cofactor   |- !g. Group g ==> !x n. x IN G /\ 0 < ord x /\ n divides ord x ==>
                                                   (ord (x ** (ord x DIV n)) = n)
   group_order_divisor    |- !g. Group g ==>!x m. x IN G /\ 0 < ord x /\ m divides ord x ==>
                                            ?y. y IN G /\ (ord y = m)
   group_order_common     |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                                 ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   group_order_common_coprime
                          |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) /\
                                 coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)
   group_orders_eq_1      |- !g. Group g ==> (orders g 1 = {#e})
   group_order_divides_exp     |- !g x. Group g /\ x IN G ==> !n. (x ** n = #e) <=> ord x divides n
   group_exp_mod_order         |- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)
   group_order_divides_maximal |- !g. FiniteAbelianGroup g ==>  !x. x IN G ==> (ord x) divides (maximal_order g)
   abelian_group_order_common  |- !g. AbelianGroup g ==> !x y. x IN G /\ y IN G ==>
                                      ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   abelian_group_order_common_coprime
                               |- !g. AbelianGroup g ==> !x y. x IN G /\ y IN G /\
                                      coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)

   Order of Inverse:
   group_inv_order           |- !g x. Group g /\ x IN G ==> (ord ( |/ x) = ord x)
   monoid_inv_order_property |- !g. FiniteMonoid g ==> !x. x IN G* ==> 0 < ord x /\ (x ** ord x = #e)
   monoid_inv_order          |- !g x. Monoid g /\ x IN G* ==> (ord ( |/ x) = ord x)

   The generated subgroup by a group element:
   Generated_def          |- !g a. gen a = <|carrier := {x | ?k. x = a ** k}; op := $*; id := #e|>
   generated_element      |- !g a x. x IN Gen a <=> ?n. x = a ** n
   generated_property     |- !g a. ((gen a).op = $* ) /\ ((gen a).id = #e)
   generated_carrier      |- !g a. a IN G ==> (Gen a = IMAGE ($** a) univ(:num))
   generated_gen_element  |- !g. Group g ==> !x. x IN G ==> x IN (Gen x)
   generated_carrier_has_id    |- !g a. #e IN Gen a
   generated_id_carrier   |- !g. Group g ==> (Gen #e = {#e})
   generated_id_subgroup  |- !g. Group g ==> gen #e <= g
   generated_group        |- !g a. FiniteGroup g /\ a IN G ==> Group (gen a)
   generated_subset       |- !g a. Group g /\ a IN G ==> Gen a SUBSET G
   generated_subgroup     |- !g a. FiniteGroup g /\ a IN G ==> gen a <= g
   generated_group_finite |- !g a. FiniteGroup g /\ a IN G ==> FINITE (Gen a)
   generated_finite_group |- !g a. FiniteGroup g /\ a IN G ==> FiniteGroup (gen a)
   generated_exp          |- !g a z. a IN G /\ z IN Gen a ==> !n. (gen a).exp z n = z ** n
   group_order_to_generated_bij
                          |- !g a. Group g /\ a IN G /\ 0 < ord a ==>
                                   BIJ (\n. a ** n) (count (ord a)) (Gen a)
   generated_group_card   |- !g a. Group g /\ a IN G /\ 0 < ord a ==> (CARD (Gen a) = ord a)
   generated_carrier_as_image  |- !g. Group g ==> !a. a IN G /\ 0 < ord a ==>
                                       (Gen a = IMAGE (\j. a ** j) (count (ord a)))

   Group Order and Divisibility:
   group_order_divides    |- !g. FiniteGroup g ==> !x. x IN G ==> (ord x) divides (CARD G)
   finite_group_Fermat    |- !g a. FiniteGroup g /\ a IN G ==> (a ** CARD G = #e)
   generated_Fermat       |- !g a. FiniteGroup g /\ a IN G ==>
                             !x. x IN (Gen a) ==> (x ** CARD (Gen a) = #e)
   group_exp_eq_condition |- !g x. Group g /\ x IN G /\ 0 < ord x ==>
                             !n m. (x ** n = x ** m) <=> (n MOD ord x = m MOD ord x)
   group_order_power_eq_order  |- !g x. Group g /\ x IN G /\ 0 < ord x ==>
                                  !k. (ord (x ** k) = ord x) <=> coprime k (ord x)
   group_order_exp_cofactor    |- !g x n. Group g /\ x IN G /\ 0 < ord x /\ n divides ord x ==>
                                          (ord (x ** (ord x DIV n)) = n)

   Roots of Unity form a Subgroup:
   roots_of_unity_def     |- !g n. uroots n =
                                   <|carrier := {x | x IN G /\ (x ** n = #e)}; op := $*; id := #e|>
   roots_of_unity_element |- !g n x. x IN (uroots n).carrier <=> x IN G /\ (x ** n = #e)
   roots_of_unity_subset  |- !g n. (uroots n).carrier SUBSET G
   roots_of_unity_0       |- !g. (uroots 0).carrier = G
   group_uroots_has_id    |- !g. Group g ==> !n. #e IN (uroots n).carrier
   group_uroots_subgroup  |- !g. AbelianGroup g ==> !n. uroots n <= g
   group_uroots_group     |- !g. AbelianGroup g ==> !n. Group (uroots n)

   Subgroup generated by a subset of a Group:
   Generated_subset_def      |- !g s. gen_set s =
                                    <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H});
                                      op := $*; id := #e|>
   Generated_subset_property |- !g s.
        ((gen_set s).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H})) /\
        ((gen_set s).op = $* ) /\ ((gen_set s).id = #e)
   Generated_subset_has_set  |- !g s. s SUBSET (gen_set s).carrier
   Generated_subset_subset   |- !g s. Group g /\ s SUBSET G ==> (gen_set s).carrier SUBSET G
   Generated_subset_group    |- !g s. Group g /\ SUBSET G ==> Group (gen_set s)
   Generated_subset_subgroup |- !g s. Group g /\ s SUBSET G ==> gen_set s <= g
   Generated_subset_exp      |- !g s. (gen_set s).exp = $**
   Generated_subset_gen      |- !g a. FiniteGroup g /\ a IN G ==> (gen_set (Gen a) = gen a)
*)

(* ------------------------------------------------------------------------- *)
(* Finite Group.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteGroup g ==> 0 < CARD G *)
(* Proof:
   Since FiniteGroup g
     ==> Group g /\ FINITE G      by FiniteGroup_def
      so G <> {}                  by group_carrier_nonempty
    thus CARD G <> 0              by CARD_EQ_0, FINITE G
      or 0 < CARD G               by NOT_ZERO_LT_ZERO
*)
val finite_group_card_pos = store_thm(
  "finite_group_card_pos",
  ``!g:'a group. FiniteGroup g ==> 0 < CARD G``,
  metis_tac[FiniteGroup_def, group_carrier_nonempty, CARD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: For FINITE Group g and x IN G, x ** n cannot be all distinct. *)
(* Proof: by finite_monoid_exp_not_distinct. *)
val finite_group_exp_not_distinct = store_thm(
  "finite_group_exp_not_distinct",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> ?h k. (x ** h = x ** k) /\ h <> k``,
  rw[finite_monoid_exp_not_distinct, finite_group_is_finite_monoid]);

(* Theorem: For FINITE Group g and x IN G, there is k > 0 such that x ** k = #e. *)
(* Proof:
   Since G is FINITE,
   ?m n. m <> n and x ** m = x ** n      by finite_group_exp_not_distinct
   Assume m < n, then x ** (n-m) = #e    by group_exp_eq
   The case m > n is symmetric.

   Note: Probably can be improved to bound k <= CARD G.
*)
val finite_group_exp_period_exists = store_thm(
  "finite_group_exp_period_exists",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> ?k. 0 < k /\ (x ** k = #e)``,
  rpt strip_tac >>
  `?m n. m <> n /\ (x ** m = x ** n)` by metis_tac[finite_group_exp_not_distinct] >>
  Cases_on `m < n` >| [
    `0 < n-m` by decide_tac,
    `n < m /\ 0 < m-n` by decide_tac
  ] >> metis_tac[group_exp_eq, FiniteGroup_def]);

(* ------------------------------------------------------------------------- *)
(* Finite Group Order                                                        *)
(* ------------------------------------------------------------------------- *)

(* Note:

(Z, $+ ) and (Z, $* ) are examples of infinite group with non-identity elements of order 0.
(Power set of an infinite set, symmetric difference) is an example of an infinite group with non-identity elements of order 2.

Although FiniteGroup g implies 0 < ord x
group_order_nonzero |- !g. FiniteGroup g ==> !x. x IN G ==> 0 < ord x
even infinite groups can have 0 < ord x.

Thus if the theorem only needs 0 < ord x, there is no need for FiniteGroup g.
*)

(* Theorem: FiniteGroup g ==> !x. x IN G ==> ord x <> 0 *)
(* Proof:
   By contradiction. Suppose ord x = 0.
   Then !n. 0 < n ==> x ** n <> #e    by order_eq_0
    But ?k. 0 < k /\ (x ** k = #e)    by finite_group_exp_period_exists
   Hence a contradiction.
*)
val group_order_nonzero = store_thm(
  "group_order_nonzero",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> ord x <> 0``,
  spose_not_then strip_assume_tac >>
  `ord x = 0` by decide_tac >>
  metis_tac[order_eq_0, finite_group_exp_period_exists]);

(* Theorem: FiniteGroup g ==> !x. x IN G ==> 0 < ord x *)
(* Proof: by group_order_nonzero *)
val group_order_pos = store_thm(
  "group_order_pos",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> 0 < ord x``,
  metis_tac[group_order_nonzero, NOT_ZERO_LT_ZERO]);

(* Theorem: The finite group element order m satisfies: 0 < m and x ** m = #e. *)
(* Proof: by group_order_pos, order_property. *)
val group_order_property = store_thm(
  "group_order_property",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> 0 < ord x /\ (x ** ord x = #e)``,
  rw[group_order_pos, order_property]);

(* Theorem: For Group g, if 0 < m, |/ x = x ** (m-1) where m = ord x *)
(* Proof:
   Let y = x ** ((ord x) - 1).
   x * y = x ** (SUC (ord x - 1))   by group_exp_SUC
         = x ** ord x               by 0 < ord x
         = #e                       by order_property
   Thus |/ x = y                    by group_rinv_unique
*)
val group_order_inv = store_thm(
  "group_order_inv",
  ``!g:'a group. Group g ==> !x. x IN G /\ 0 < ord x ==> ( |/x = x ** ((ord x)-1))``,
  rpt strip_tac >>
  qabbrev_tac `y = x ** ((ord x) - 1)` >>
  `y IN G` by rw[Abbr`y`] >>
  `SUC ((ord x) - 1) = ord x` by decide_tac >>
  `x * y = x ** (ord x)` by metis_tac[group_exp_SUC] >>
  metis_tac[group_rinv_unique, order_property]);

(* Theorem: For Group g, if 0 < m, x ** n = x ** (n mod m), where m = ord x *)
(* Proof:
   Let m = ord x.
     x ** n
   = x ** (m * q + r)            by division: n = q * m + r
   = x ** (m * q) * (x ** r)     by group_exp_add
   = ((x ** m) ** q) * (x ** r)  by group_exp_mult
   = (#e ** q) * (x ** r)        by order_property
   = #e * (x ** r)               by group_id_exp
   = x ** r                      by group_lid
*)
val group_exp_mod = store_thm(
  "group_exp_mod",
  ``!g:'a group. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)``,
  rpt strip_tac >>
  qabbrev_tac `m = ord x` >>
  `x ** m = #e` by rw[order_property, Abbr`m`] >>
  `n = (n DIV m) * m + (n MOD m)` by rw[DIVISION] >>
  `_ = m * (n DIV m) + (n MOD m)` by decide_tac >>
  metis_tac[group_exp_add, group_exp_mult, group_id_exp, group_lid, group_exp_element]);

(* ------------------------------------------------------------------------- *)
(* Characterization of Group Order                                           *)
(* ------------------------------------------------------------------------- *)

(* A characterization of group order without reference to period. *)

(* Theorem: If 0 < n, ord x = n iff x ** n = #e with 0 < n, and !m < n, x ** m <> #e. *)
(* Proof: true by order_thm. *)
val group_order_thm = store_thm(
  "group_order_thm",
  ``!g:'a group. !n. 0 < n ==>
   !x. (ord x = n) <=> (x ** n = #e) /\ (!m. 0 < m /\ m < n ==> (x ** m) <> #e)``,
  rw[order_thm]);

(* Theorem: For Group g, m, n < (ord x), x ** m = x ** n ==> m = n *)
(* Proof:
   Otherwise x ** (m-n) = #e by group_exp_eq,
   contradicting minimal nature of element order.
*)
val group_order_unique = store_thm(
  "group_order_unique",
  ``!g:'a group. Group g ==> !x. x IN G ==>
   !m n. m < ord x /\ n < ord x /\ (x ** m = x ** n) ==> (m = n)``,
  spose_not_then strip_assume_tac >>
  Cases_on `m < n` >| [
    `0 < n-m /\ n-m < ord x` by decide_tac,
    `n < m /\ 0 < m-n /\ m-n < ord x` by decide_tac
  ] >>
  metis_tac[group_exp_eq, order_minimal]);

(* Theorem: Group g /\ x IN G ==> !n m. n < ord x /\ m < ord x /\ (x ** n = x ** m) ==> (n = m) *)
(* Proof: by group_order_unique *)
val group_exp_equal = store_thm(
  "group_exp_equal",
  ``!(g:'a group) x. Group g /\ x IN G ==>
   !n m. n < ord x /\ m < ord x /\ (x ** n = x ** m) ==> (n = m)``,
  metis_tac[group_order_unique]);

(* Theorem: [property of finite group order]
   For x IN G, if (ord x = n), 0 < n /\ (x ** n = #e) /\ (!m. 0 < m /\ m < n ==> (x ** m) <> #e
*)
(* Proof:
   ord x = n ==> 0 < n /\ x ** n = #e                  by group_order_property
   ord x = n ==> !m. 0 < m /\ m < n ==> x ** m <> #e   by order_minimal
*)
val finite_group_order = store_thm(
  "finite_group_order",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==>
      !n. (ord x = n) ==> (0 < n /\ (x ** n = #e) /\ (!m. 0 < m /\ m < n ==> (x ** m) <> #e))``,
  metis_tac[group_order_property, order_minimal]);

(* Theorem: FiniteGroup g /\ !z. z IN G /\ (ord z = CARD G) ==>
            !x. x IN G ==> ?n. n < CARD G /\ (x = z ** n) *)
(* Proof:
   By order g z = CARD G, all powers of z are distinct.
   By FiniteGroup g, all powers of z = permutation of element.
   Hence each element is some power of z.
   Or,
   Let f = \n. z ** n
   Then INJ f (count (CARD G)) G         by INJ_DEF, group_order_unique
   Now  FINITE (count (CARD G))          by FINITE_COUNT
        CARD (count (CARD G)) = CARD G   by CARD_COUNT
    so  SURJ f (count (CARD G)) G        by FINITE_INJ_AS_SURJ, FINITE G
   i.e. IMAGE f (count (CARD G)) = G     by IMAGE_SURJ
   Hence ?n. n < CARD G /\ x = z ** n    by IN_IMAGE, IN_COUNT
*)
val finite_group_primitive_property = store_thm(
  "finite_group_primitive_property",
  ``!g:'a group. FiniteGroup g ==> !z. z IN G /\ (ord z = CARD G) ==>
   (!x. x IN G ==> ?n. n < CARD G /\ (x = z ** n))``,
  rpt (stripDup[FiniteGroup_def]) >>
  qabbrev_tac `f = \n. z ** n` >>
  `INJ f (count (CARD G)) G` by
  (rw[INJ_DEF, Abbr`f`] >>
  metis_tac[group_order_unique]) >>
  `FINITE (count (CARD G))` by rw[] >>
  `CARD (count (CARD G)) = CARD G` by rw[] >>
  `SURJ f (count (CARD G)) G` by rw[FINITE_INJ_AS_SURJ] >>
  `IMAGE f (count (CARD G)) = G` by rw[GSYM IMAGE_SURJ] >>
  metis_tac[IN_IMAGE, IN_COUNT]);

(* ------------------------------------------------------------------------- *)
(* Lifting Theorems from Monoid Order                                        *)
(* ------------------------------------------------------------------------- *)

(* Lifting Monoid Order theorem for Group Order.
   from: !g:'a monoid. Monoid g ==> ....
     to: !g:'a group.  Group g ==> ....
    via: !g:'a group.  Group g ==> Monoid g
*)
local
val gim = group_is_monoid |> SPEC_ALL |> UNDISCH
in
fun lift_monoid_order_thm suffix = let
   val mth = DB.fetch "monoid" ("monoid_order_" ^ suffix)
   val mth' = mth |> SPEC_ALL
in
   save_thm("group_order_" ^ suffix, gim |> MP mth' |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: ord #e = 1 *)
val group_order_id = lift_monoid_order_thm "id";
(* > val group_order_id = |- !g. Group g ==> (ord #e = 1): thm *)

(* export simple result *)
val _ = export_rewrites ["group_order_id"];

(* Theorem: x IN G ==> ord x = 1 <=> x = #e *)
val group_order_eq_1 = lift_monoid_order_thm "eq_1";
(* > val group_order_eq_1 = |- !g. Group g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e)): thm *)

(* Theorem: x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m *)
val group_order_condition = lift_monoid_order_thm "condition";
(* > val group_order_condition = |- !g. Group g ==> !x. x IN G ==> !m. (x ** m = #e) <=> ord x divides m: thm *)

(* Theorem: x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0) *)
val group_order_power_eq_0 = lift_monoid_order_thm "power_eq_0";
(* > val group_order_power_eq_0 = |- !g. Group g ==>
     !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0): thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_power = lift_monoid_order_thm "power";
(* > val group_order_power = |- !g. Group g ==> !x. x IN G ==> !k. ord (x ** k) * gcd (ord x) k = ord x: thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_power_eqn = lift_monoid_order_thm "power_eqn";
(* > val group_order_power_eqn = |- !g. Group g ==> !x k. x IN G /\ 0 < k ==> (ord (x ** k) = ord x DIV (gcd k (ord x))): thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_power_coprime = lift_monoid_order_thm "power_coprime";
(* > val group_order_power_coprime =
   |- !g. Group g ==> !x. x IN G ==> !n. coprime n (ord x) ==> (ord (x ** n) = ord x): thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_cofactor = lift_monoid_order_thm "cofactor";
(* > val group_order_cofactor = |- !g. Group g ==> !x n. x IN G /\ 0 < ord x /\ n divides ord x ==>
        (ord (x ** (ord x DIV n)) = n): thm *)

(* Theorem: If x IN G with ord x = n, and m divides n, then G contains an element of order m. *)
val group_order_divisor = lift_monoid_order_thm "divisor";
(* > val group_order_divisor = |- !g. Group g ==>
     !x m. x IN G /\ 0 < ord x /\ m divides ord x ==> ?y. y IN G /\ (ord y = m): thm *)

(* Theorem: If x * y = y * x, and n = ord x, m = ord y,
            then there exists z IN G such that ord z = (lcm n m) / (gcd n m) *)
val group_order_common = lift_monoid_order_thm "common";
(* > val group_order_common = |- !g. Group g ==>
         !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
         ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y)): thm *)
(* Note:
   This is interesting, but this z has a 'smaller' order: (lcm n m) / (gcd n m).

   The theorem that is desired is:
   Theorem: If x * y = y * x, and n = ord x, m = ord y, then there exists z IN G such that ord z = (lcm n m)

   But this needs another method.
   However, a restricted form of this theorem is still useful.
*)

(* Theorem: If x * y = y * x, and n = ord x, m = ord y, and gcd n m = 1,
            then there exists z IN G with ord z = (lcm n m) *)
val group_order_common_coprime = lift_monoid_order_thm "common_coprime";
(* > val group_order_common_coprime = |- !g. Group g ==>
         !x y. x IN G /\ y IN G /\ (x * y = y * x) /\ coprime (ord x) (ord y) ==>
         ?z. z IN G /\ (ord z = ord x * ord y): thm *)

(* Theorem: Group g ==> (orders g 1 = {#e}) *)
(* Proof: by group_is_monoid, orders_eq_1 *)
val group_orders_eq_1 = store_thm(
  "group_orders_eq_1",
  ``!g:'a group. Group g ==> (orders g 1 = {#e})``,
  rw[group_is_monoid, orders_eq_1]);

(* Theorem: Group g /\ x IN G ==> !n. (x ** n = #e) <=> (ord x) divides n *)
(* Proof: by group_order_condition *)
val group_order_divides_exp = store_thm(
  "group_order_divides_exp",
  ``!(g:'a group) x. Group g /\ x IN G ==> !n. (x ** n = #e) <=> (ord x) divides n``,
  rw[group_order_condition]);

(* Another proof of subgroup_order in subgroupTheory. *)

(* Theorem: h <= g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   h <= g means Group g /\ Group h /\ H SUBSET G   by Subgroup_def
   Let x IN H, then x IN G                         by SUBSET_DEF
   x ** (order h x) = #e /\ x ** (ord x) = #e      by order_property
   Therefore
   (ord x) (order h x) divides           by group_order_condition, 1st one
   (order h x) divides (ord x)           by group_order_condition, 2nd one
   Hence order h x = ord x               by DIVIDES_ANTISYM
*)
(* keep subgroupTheory.subgroup_order *)
val subgroup_order = prove(
  ``!g h:'a group. h <= g ==> !x. x IN H ==> (order h x = ord x)``,
  rpt strip_tac >>
  `Group g /\ Group h /\ H SUBSET G /\ (h.op = g.op) /\ (h.id = #e)` by metis_tac[Subgroup_def, subgroup_id] >>
  `!x. x IN H ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `!x. x IN H ==> !n. h.exp x n = x ** n` by metis_tac[subgroup_exp] >>
  metis_tac[order_property, group_order_condition, DIVIDES_ANTISYM]);

(* Theorem: Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x)) *)
(* Proof: by monoid_exp_mod_order, group_is_monoid *)
val group_exp_mod_order = store_thm(
  "group_exp_mod_order",
  ``!g:'a group. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x))``,
  metis_tac[monoid_exp_mod_order, group_is_monoid]);

(* Theorem: In a Finite Abelian Group, every order divides the maximal order.
            FiniteAbelianGroup g ==> !x. x IN G ==> ord x divides maximal_order g *)
(* Proof:
   Since 0 < ord x     by group_order_pos
   The result is true  by monoid_order_divides_maximal
*)
val group_order_divides_maximal = store_thm(
  "group_order_divides_maximal",
  ``!g:'a group. FiniteAbelianGroup g ==> !x. x IN G ==> (ord x) divides (maximal_order g)``,
  metis_tac[monoid_order_divides_maximal, group_order_pos, finite_group_is_finite_monoid,
             FiniteAbelianGroup_def_alt, FiniteAbelianMonoid_def_alt]);

(* Theorem: AbelianGroup g ==> !x y. x IN G /\ y IN G ==>
            ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y)) *)
(* Proof: by AbelianGroup_def, group_order_common *)
val abelian_group_order_common = store_thm(
  "abelian_group_order_common",
  ``!g:'a group. AbelianGroup g ==> !x y. x IN G /\ y IN G ==>
   ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))``,
  rw[AbelianGroup_def, group_order_common]);

(* Theorem: AbelianGroup g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
            ?z. z IN G /\ (ord z = ord x * ord y) *)
(* Proof: by AbelianGroup_def, group_order_common_coprime *)
val abelian_group_order_common_coprime = store_thm(
  "abelian_group_order_common_coprime",
  ``!g:'a group. AbelianGroup g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
   ?z. z IN G /\ (ord z = ord x * ord y)``,
  rw[AbelianGroup_def, group_order_common_coprime]);

(* ------------------------------------------------------------------------- *)
(* Order of Inverse                                                          *)
(* ------------------------------------------------------------------------- *)

(*
group_order_inv
|- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> ( |/ x = x ** (ord x - 1))
*)

(* Theorem: Group g /\ x IN G ==> (ord ( |/ x) = ord x) *)
(* Proof:
   Let n = ord x.
   If n = 0,
      Let m = ord ( |/ x).
      By contradiction, suppose m <> 0.
      Then #e = ( |/ x) ** m               by order_property
              = |/ (x ** m)                by group_inv_exp
      Thus x ** m = |/ #e                  by group_inv_inv
                  = #e                     by group_inv_id
      This contradicts ord x = n = 0       by order_eq_0, 0 < m

   Otherwise n <> 0, or 0 < n              by NOT_ZERO_LT_ZERO
     ord ( |/ x)
   = ord ( |/ x) * 1                       by MULT_RIGHT_1
   = ord ( |/ x) * gcd n (n - 1)           by coprime_PRE, 0 < n
   = ord (x ** (n - 1)) * gcd n (n - 1)    by group_order_inv
   = n                                     by group_order_power
*)
val group_inv_order = store_thm(
  "group_inv_order",
  ``!(g:'a group) x. Group g /\ x IN G ==> (ord ( |/ x) = ord x)``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  Cases_on `n = 0` >| [
    simp[] >>
    spose_not_then strip_assume_tac >>
    qabbrev_tac `m = ord ( |/ x)` >>
    `#e = ( |/ x) ** m` by rw[order_property, Abbr`m`] >>
    `_ = |/ (x ** m)` by rw[group_inv_exp] >>
    `x ** m = #e` by metis_tac[group_inv_inv, group_inv_id, group_exp_element] >>
    `0 < m` by decide_tac >>
    metis_tac[order_eq_0],
    `0 < n` by decide_tac >>
    metis_tac[MULT_RIGHT_1, coprime_PRE, group_order_inv, group_order_power]
  ]);

(*
> group_order_property |> ISPEC ``Invertibles g``;
val it = |- FiniteGroup (Invertibles g) ==> !x. x IN (Invertibles g).carrier ==>
     0 < order (Invertibles g) x /\
     ((Invertibles g).exp x (order (Invertibles g) x) = (Invertibles g).id): thm
*)

(* Theorem: FiniteMonoid g ==> !x. x IN G* ==> 0 < ord x /\ (x ** ord x = #e) *)
(* Proof:
   Note FiniteGroup (Invertibles g)        by finite_monoid_invertibles_is_finite_group
    and (Invertibles g).carrier = G*       by Invertibles_carrier
    ==> 0 < order (Invertibles g) x  /\
        (Invertibles g).exp x (order (Invertibles g) x) =
         (Invertibles g).id                by group_order_property
    But order (Invertibles g) x = ord x    by Invertibles_order
    and (Invertibles g).id = #e            by Invertibles_property
    and (Invertibles g).exp = $**          by Invertibles_property
    ==> 0 < ord x /\ x ** ord x = #e       by above
*)
val monoid_inv_order_property = store_thm(
  "monoid_inv_order_property",
  ``!g:'a monoid. FiniteMonoid g ==> !x. x IN G* ==> 0 < ord x /\ (x ** ord x = #e)``,
  ntac 4 strip_tac >>
  `FiniteGroup (Invertibles g)` by rw[finite_monoid_invertibles_is_finite_group] >>
  metis_tac[group_order_property, Invertibles_order, Invertibles_property]);

(*
This proof is quite complicated:
* The invertibles of monoid form a group.
* For a finite group, finite_group_Fermat |- !g a. FiniteGroup g /\ a IN G ==> (a ** CARD G = #e)
* Thus   a ** (CARD G - 1) = |/ a
*    ord ( |/ a) = ord (a ** (CARD G - 1)) * gcd (ord a) (CARD G - 1) = ord a
* because (ord a) divides (CARD G), gcd (ord a) (CARD G - 1) = 1, and ord ( |/ a) = ord a.
*)

(*
> group_inv_order |> ISPEC ``Invertibles g``;
val it = |- FiniteGroup (Invertibles g) ==> !x. x IN (Invertibles g).carrier ==>
     (order (Invertibles g) ((Invertibles g).inv x) = order (Invertibles g) x): thm
*)

(* Theorem: Monoid g /\ x IN G* ==> (ord ( |/ x) = ord x) *)
(* Proof:
   Note Group (Invertibles g)                  by monoid_invertibles_is_group
    and (Invertibles g).carrier = G*           by Invertibles_carrier
    ==> order (Invertibles g) ((Invertibles g).inv x)
      = order (Invertibles g) x                by group_inv_order
    But !x. order (Invertibles g) x = ord x    by Invertibles_order
    and (Invertibles g).inv x = |/ x           by Invertibles_inv
    ==> ord ( |/ x) = ord x                    by above
*)
val monoid_inv_order = store_thm(
  "monoid_inv_order",
  ``!(g:'a monoid) x. Monoid g /\ x IN G* ==> (ord ( |/ x) = ord x)``,
  rpt strip_tac >>
  `Group (Invertibles g)` by rw[monoid_invertibles_is_group] >>
  `(Invertibles g).carrier = G*` by rw[Invertibles_carrier] >>
  `(Invertibles g).inv x = |/ x` by metis_tac[Invertibles_inv] >>
  metis_tac[group_inv_order, Invertibles_order]);

(* ------------------------------------------------------------------------- *)
(* Application of Finite Group element order:                                *)
(* The generated subgroup by a group element.                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The Subgroup <a> of any element a of Group g.                             *)
(* ------------------------------------------------------------------------- *)

(* Define the generator group, the exponential group of an element a of group g *)
val Generated_def = Define`
  Generated g a : 'a group =
    <| carrier := {x | ?k. x = a ** k };
            op := g.op;
            id := g.id
     |>
`;
(*
- type_of ``Generated g a``;
> val it = ``:'a group`` : hol_type
*)


(* overload on generated group and its carrier *)
val _ = overload_on("gen", ``Generated g``);
val _ = overload_on("Gen", ``\a. (Generated g a).carrier``);

(* Theorem: x IN Gen a <=> ?n. x = a ** n *)
(* Proof: by Generated_def *)
val generated_element = store_thm(
  "generated_element",
  ``!g:'a group. !a x. x IN Gen a <=> ?n. x = a ** n``,
  rw[Generated_def]);

(* Theorem: ((gen a).op = g.op) /\ ((gen a).id = #e) *)
(* Proof: by Generated_def. *)
val generated_property = store_thm(
  "generated_property",
  ``!(g:'a group) a. ((gen a).op = g.op) /\ ((gen a).id = #e)``,
  rw[Generated_def]);

(* Theorem: !a. a IN G ==> (Gen a = IMAGE (g.exp a) univ(:num)) *)
(* Proof: by Generated_def, EXTENSION *)
val generated_carrier = store_thm(
  "generated_carrier",
  ``!(g:'a group) a. a IN G ==> (Gen a = IMAGE (g.exp a) univ(:num))``,
  rw[Generated_def, EXTENSION]);

(* Theorem: Group g ==> !x. x IN G ==> x IN (Gen x) *)
(* Proof: by Generated_def, group_exp_1 *)
val generated_gen_element = store_thm(
  "generated_gen_element",
  ``!g:'a group. Group g ==> !x. x IN G ==> x IN (Gen x)``,
  rw[Generated_def] >>
  metis_tac[group_exp_1]);

(* Theorem: #e IN (Gen a) *)
(* Proof:
   Note a ** 0 = #e    by group_exp_0
    ==> #e IN (Gen a)  by generated_element
*)
val generated_carrier_has_id = store_thm(
  "generated_carrier_has_id",
  ``!g:'a group. !a. #e IN (Gen a)``,
  metis_tac[generated_element, group_exp_0]);

(* Theorem: Group g ==> (Gen #e = {#e}) *)
(* Proof:
     Gen #e
   = {x | ?k. x = #e ** k}     by Generated_def
   = {x | x = #e}              by group_id_exp, Group g
   = {#e}                      by EXTENSION
*)
val generated_id_carrier = store_thm(
  "generated_id_carrier",
  ``!g:'a group. Group g ==> (Gen #e = {#e})``,
  rw[Generated_def, EXTENSION]);

(* Theorem: Group g ==> gen #e <= g *)
(* Proof:
   Note Gen #e = {#e}            by generated_id_carrier, Group g
   By subgroup_alt, this is to show:
   (1) Gen #e <> {}, true        by NOT_SING_EMPTY
   (2) (Gen #e) SUBSET G, true   by group_id_element, SUBSET_DEF
   (3) (gen #e).op = $*, true    by generated_property
   (4) (gen #e).id = #e, true    by generated_property
   (5) x IN (Gen #e) /\ y IN (Gen #e) ==> x * |/ y IN (Gen #e)
       Note x = #e /\ y = #e     by IN_SING
         so x * |/ y = #e        by group_inv_id, group_id_id
         or x * |/ y IN (Gen #e) by IN_SING
*)
val generated_id_subgroup = store_thm(
  "generated_id_subgroup",
  ``!g:'a group. Group g ==> gen #e <= g``,
  rw[generated_id_carrier, subgroup_alt, generated_property]);

(* Note for the next theorem:
   FINITE is required to have the order m, giving the inverse.
   INFINITE would require two generators: a and |/ a.
   For example, (Z, $+) is a group, but (gen 1 = naturals) is not a group.
   Also (gen 2 = multples of 2) is not a group, but (gen 2 -2) is a group.
   Indeed, Z = gen 1 -1, but our generated_def has only one generator.

   Can define |/a = a ** -1, but that would require exponents to be :int, not :num
*)

(* Theorem: For a FINITE group g, the generated group of a in G is a group *)
(* Proof:
   This is to show:
   (1) ?k''. a ** k * a ** k' = a ** k''   by group_exp_add
   (2) a ** k * a ** k' * a ** k'' = a ** k * (a ** k' * a ** k'')  by group_assoc
   (3) ?k. #e = a ** k                     by group_exp_0, a ** 0 = #e.
   (4) #e * a ** k = a ** k                by group_lid
   (5) ?y. (?k'. y = a ** k') /\ (y * a ** k = #e)
       There is m = ord a with the property 0 < m
                                           by group_order_pos
          |/ (a ** k)
        = ( |/a) ** k                      by group_exp_inv
        = (a ** (m-1)) ** k                by group_order_inv
        = a ** ((m-1) * k)                 by group_exp_mult
        Pick k' = (m-1) * k, and y = a ** k' = |/ (a ** k).
*)
val generated_group = store_thm(
  "generated_group",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> Group (gen a)``,
  rpt (stripDup[FiniteGroup_def]) >>
  rw_tac std_ss[group_def_alt, Generated_def, RES_FORALL_THM, GSPECIFICATION] >-
  metis_tac[group_exp_add] >-
  rw_tac std_ss[group_assoc, group_exp_element] >-
  metis_tac[group_exp_0] >-
  rw_tac std_ss[group_lid, group_exp_element] >>
  `0 < ord a` by rw[group_order_pos] >>
  metis_tac[group_order_inv, group_exp_inv, group_exp_mult, group_linv, group_exp_element]);

(* Theorem: Group g /\ a IN G ==> (Gen a) SUBSET G *)
(* Proof:
   x IN (Gen a) ==> ?n. x = a ** n          by Generated_def
   a IN G ==> a ** n IN G                   by group_exp_element
   Hence (Gen a) SUBSET G                   by SUBSET_DEF
*)
val generated_subset = store_thm(
  "generated_subset",
  ``!(g:'a group) a. Group g /\ a IN G ==> (Gen a) SUBSET G``,
  rw[Generated_def, SUBSET_DEF] >>
  rw[]);

(* Theorem: The generated group <a> for a IN G is subgroup of G. *)
(* Proof:
   Essentially this is to prove:
   (1) Group (gen a)              true by generated_group.
   (2) (Gen a) SUBSET G           true by generated_subset
   (3) gen a).op x y = x * y      true by Generated_def.
*)
val generated_subgroup = store_thm(
  "generated_subgroup",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> Subgroup (gen a) g``,
  rpt (stripDup[FiniteGroup_def]) >>
  rw_tac std_ss[Subgroup_def, SUBSET_DEF, GSPECIFICATION] >-
  rw_tac std_ss[generated_group] >-
  metis_tac[generated_subset, SUBSET_DEF] >>
  rw_tac std_ss[Generated_def]);

(* Theorem: FiniteGroup g /\ a IN G ==> FINITE (Gen a) *)
(* Proof:
   FiniteGroup g ==> Group g /\ FINITE G  by FiniteGroup_def
   Group g ==> (Gen a) SUBSET G           by generated_subset
   Hence FINITE (Gen a)                   by SUBSET_FINITE
*)
val generated_group_finite = store_thm(
  "generated_group_finite",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> FINITE (Gen a)``,
  metis_tac[FiniteGroup_def, generated_subset, SUBSET_FINITE]);

(* Theorem: FiniteGroup g /\ a IN G ==> FiniteGroup (gen a) *)
(* Proof:
   FiniteGroup g ==> FINITE (Gen a)   by generated_group_finite
   FiniteGroup g ==> Group (gen a)    by generated_group
   and FiniteGroup (gen a)            by FiniteGroup_def
*)
val generated_finite_group = store_thm(
  "generated_finite_group",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> FiniteGroup (gen a)``,
  rw[FiniteGroup_def, generated_group, generated_group_finite]);

(* Theorem: a IN G /\ z IN (Gen a) ==> !n. (gen a).exp z n = z ** n *)
(* Proof:
     (gen a).exp z n
   = FUNPOW ((gen a).op z) n (gen a).id    by monoid_exp_def
   = FUNPOW (g.op z) n (g.id)              by Generated_def
   = g.exp z n                             by monoid_exp_def
   = z ** n                                by notation
*)
val generated_exp = store_thm(
  "generated_exp",
  ``!g:'a group. !a z. a IN G /\ z IN (Gen a) ==> !n. (gen a).exp z n = z ** n``,
  rw[Generated_def, monoid_exp_def]);

(* Theorem: There is a bijection from (count m) to (gen a), where m = ord x and 0 < m *)
(* Proof:
   The map (\n. a ** n) from (count m) to (gen a) is bijective:
   (1) surjective because x in (gen a) means ?k. x = a ** k = a ** (k mod m), so take n = k mod m.
       This is group_exp_mod.
   (2) injective because a ** m = a ** n ==> m = n,
       otherwise a ** (m-n) = #e, contradicting minimal nature of m.
       This is group_order_unique.

   Essentially this is to prove:
   (1) a IN G /\ n < ord a ==> ?k. a ** n = a ** k,             just take k = n.
   (2) n < ord a /\ n' < ord a /\ a ** n = a ** n' ==> n = n',  true by group_order_unique
   (3) same as (1)
   (4) a IN G ==> ?n. n < ord a /\ (a ** n = a ** k),           true by group_exp_mod, n = k mod order.
*)
val group_order_to_generated_bij = store_thm(
  "group_order_to_generated_bij",
  ``!(g:'a group) a. Group g /\ a IN G /\ 0 < ord a ==> BIJ (\n. a ** n) (count (ord a)) (Gen a)``,
  rpt strip_tac >>
  rw[BIJ_DEF, SURJ_DEF, INJ_DEF, Generated_def] >-
  metis_tac[] >-
  metis_tac[group_order_unique] >-
  metis_tac[] >>
  metis_tac[group_exp_mod, MOD_LESS]);

(* Theorem: The order of the generated_subgroup is the order of its element *)
(* Proof:
   Note BIJ (\n. a**n) (count (ord a)) (Gen a)  by group_order_to_generated_bij
    and FINITE (count (ord a))                  by FINITE_COUNT
    and CARD (count (ord a)) = ord a            by CARD_COUNT
   Thus CARD (Gen a) = ord a                    by FINITE_BIJ
*)
val generated_group_card = store_thm(
  "generated_group_card",
  ``!(g:'a group) a. Group g /\ a IN G /\ 0 < ord a ==> (CARD (Gen a) = ord a)``,
  metis_tac[group_order_to_generated_bij, FINITE_BIJ, FINITE_COUNT, CARD_COUNT]);

(* Theorem: Group g ==> !a. a IN G /\ 0 < ord a ==> (Gen a = IMAGE (\j. a ** j) (count (ord a))) *)
(* Proof:
   By generated_carrier, IN_IMAGE and IN_COUNT, this is to show:
   (1) a IN G /\ 0 < ord a ==> ?j. (a ** x' = a ** j) /\ j < ord a
       Take j = x' MOD (ord a).
       Then j < ord a                by MOD_LESS
        and a ** x' = a ** j         by group_exp_mod
   (2) ?x'. a ** j = a ** x'
       Take x' = j.
*)
val generated_carrier_as_image = store_thm(
  "generated_carrier_as_image",
  ``!g:'a group. Group g ==> !a. a IN G /\ 0 < ord a ==>
               (Gen a = IMAGE (\j. a ** j) (count (ord a)))``,
  rw[generated_carrier, EXTENSION, EQ_IMP_THM] >-
  metis_tac[group_exp_mod, MOD_LESS] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Group Order and Divisibility                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For FiniteGroup g g, if x IN G, (ord x) divides (CARD G) *)
(* Proof:
   By applying Lagrange theorem to the generated subgroup of the element x:
   Note gen x <= g              by generated_subgroup
   Thus CARD (Gen x)) (CARD G)  by Lagrange_thm
    Now 0 < ord x               by group_order_pos
    and CARD (Gen x)) = ord x   by generated_group_card
   The result follows.
*)
val group_order_divides = store_thm(
  "group_order_divides",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> (ord x) divides (CARD G)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `gen x <= g` by rw[generated_subgroup] >>
  `(CARD (Gen x)) divides (CARD G)` by rw[Lagrange_thm] >>
  metis_tac[generated_group_card, group_order_pos]);

(* Theorem: For FiniteGroup g, a IN G ==> a ** (CARD g) = #e *)
(* Proof:
   Note (ord a) divides (CARD G)     by group_order_divides
     or ?k. CARD G = (ord a) * k     by divides_def, MULT_COMM

     a ** (CARD G)
   = a ** ((ord a) * k)         by above
   = (a ** (ord a)) ** k        by group_exp_mult
   = (#e) ** k                  by order_property
   = #e                         by group_id_exp
*)
val finite_group_Fermat = store_thm(
  "finite_group_Fermat",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> (a ** (CARD G) = #e)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(ord a) divides (CARD G)` by rw[group_order_divides] >>
  `?k. CARD G = (ord a) * k` by rw[GSYM divides_def] >>
  metis_tac[group_exp_mult, group_id_exp, order_property]);

(* Theorem: x IN (Gen a) ==> (x ** (CARD (Gen a)) = #e) *)
(* Proof:
   Given FiniteGroup g /\ a IN G
      so FiniteGroup (gen a)             by generated_finite_group
     ==> (gen a).exp x (CARD (Gen a)) = (gen a).id
                                         by finite_group_Fermat
     Now (gen a).id = #e                 by generated_property
     and !n. (gen a).exp x n = x ** n    by generated_exp
   The result follows.
*)
val generated_Fermat = store_thm(
  "generated_Fermat",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==>
   !x. x IN (Gen a) ==> (x ** (CARD (Gen a)) = #e)``,
  rpt strip_tac >>
  `FiniteGroup (gen a)` by rw[generated_finite_group] >>
  `(gen a).id = #e` by rw[generated_property] >>
  `!n. (gen a).exp x n = x ** n` by rw[generated_exp] >>
  metis_tac[finite_group_Fermat]);

(* Theorem: Group g /\ x IN G /\ 0 < ord x ==>
           !n m. (x ** n = x ** m) <=> (n MOD (ord x) = m MOD (ord x)) *)
(* Proof:
   Note x ** n = x ** (n MOD (ord x))    by group_exp_mod
    and x ** m = x ** (m MOD (ord x))    by group_exp_mod
   If part: x ** n = x ** m ==> n MOD ord x = m MOD ord x
      Since n MOD ord x < ord x          by MOD_LESS
        and m MOD ord x < ord x          by MOD_LESS
        ==> n MOD ord x = m MOD ord x    by group_exp_equal
   Only-if part: trivially true.
*)
val group_exp_eq_condition = store_thm(
  "group_exp_eq_condition",
  ``!(g:'a group) x. Group g /\ x IN G /\ 0 < ord x ==>
     !n m. (x ** n = x ** m) <=> (n MOD (ord x) = m MOD (ord x))``,
  metis_tac[group_exp_mod, group_exp_equal, MOD_LESS]);

(* ------------------------------------------------------------------------- *)
(* Finite Group Order                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ x IN G /\ 0 < ord x ==>
            !k. (ord (x ** k) = ord x) <=> coprime k (ord x) *)
(* Proof:
   If part: ord (x ** k) = ord x ==> coprime k (ord x)
       Note ord (x ** k) * gcd k (ord x) = ord x       by group_order_power, GCD_SYM
         or      (ord x) * gcd k (ord x) = ord x       by ord (x ** k) = ord x
         or      (ord x) * gcd k (ord x) = ord x * 1   by MULT_RIGHT_1
        Therefore gcd k (ord x) = 1                    by MULT_RIGHT_ID
               or coprime k (ord x)                    by notation
   Only-if part: coprime k (ord x) ==> ord (x ** k) = ord x
       Note ord (x ** k) * gcd k (ord x) = ord x       by group_order_power, GCD_SYM
        but coprime k (ord x) means gcd k (ord x) = 1  by notation
      Hence ord (x ** k) = ord x                       by MULT_RIGHT_1
*)
val group_order_power_eq_order = store_thm(
  "group_order_power_eq_order",
  ``!(g:'a group) x. Group g /\ x IN G /\ 0 < ord x ==>
   !k. (ord (x ** k) = ord x) <=> coprime k (ord x)``,
  rpt strip_tac >>
  `ord (x ** k) * gcd k (ord x) = ord x` by metis_tac[group_order_power, GCD_SYM] >>
  rw[EQ_IMP_THM] >-
  metis_tac[MULT_RIGHT_ID] >>
  fs[]);

(* Theorem: Group g /\ x IN G /\ 0 < ord x /\ n divides (ord x) ==>
            (ord (x ** ((ord x) DIV n)) = n) *)
(* Proof:
   Let m = ord x, k = m DIV n.
   Note n divides m ==> 0 < n        by ZERO_DIVIDES, m <> 0
    and n divides m ==> m = k * n    by DIVIDES_EQN, 0 < n
   thus k <> 0                       by MULT_0, m <> 0
    Now ord (x ** k) * gcd m k = m   by group_order_power
    but m = n * k                    by MULT_COMM
     so gcd m k = k                  by GCD_MULTIPLE_ALT
  Hence ord (x ** k) = n             by EQ_MULT_RCANCEL
*)
val group_order_exp_cofactor = store_thm(
  "group_order_exp_cofactor",
  ``!(g:'a group) x n. Group g /\ x IN G /\ 0 < ord x /\ n divides (ord x) ==>
        (ord (x ** ((ord x) DIV n)) = n)``,
  rpt strip_tac >>
  qabbrev_tac `m = ord x` >>
  qabbrev_tac `k = m DIV n` >>
  `ord (x ** k) * gcd m k = m` by rw[group_order_power, Abbr`m`] >>
  `m <> 0` by decide_tac >>
  `n <> 0` by metis_tac[ZERO_DIVIDES] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `_ = n * k` by rw[MULT_COMM] >>
  `k <> 0` by metis_tac[MULT_0] >>
  metis_tac[GCD_MULTIPLE_ALT, EQ_MULT_RCANCEL]);

(* ------------------------------------------------------------------------- *)
(* Roots of Unity form a Subgroup                                            *)
(* ------------------------------------------------------------------------- *)

(* Define n-th roots of unity *)
val roots_of_unity_def = Define`
  roots_of_unity (g:'a group) (n:num):'a group =
     <| carrier := {x | x IN G /\ (x ** n = #e)};
             op := g.op;
             id := #e
      |>
`;
(* Overload root of unity *)
val _ = overload_on ("uroots", ``roots_of_unity g``);

(*
> roots_of_unity_def;
val it = |- !g n. uroots n = <|carrier := {x | x IN G /\ (x ** n = #e)}; op := $*; id := #e|>: thm
*)

(* Theorem: x IN (uroots n).carrier <=> x IN G /\ (x ** n = #e) *)
(* Proof: by roots_of_unity_def *)
val roots_of_unity_element = store_thm(
  "roots_of_unity_element",
  ``!g:'a group. !n x. x IN (uroots n).carrier <=> x IN G /\ (x ** n = #e)``,
  rw[roots_of_unity_def]);

(* Theorem: (uroots n).carrier SUBSET G *)
(* Proof: by roots_of_unity_element, SUBSET_DEF. *)
val roots_of_unity_subset = store_thm(
  "roots_of_unity_subset",
  ``!g:'a group. !n. (uroots n).carrier SUBSET G``,
  rw[roots_of_unity_element, SUBSET_DEF]);

(* Theorem: (uroots 0).carrier = G *)
(* Proof:
   (uroots 0).carrier = {x | x IN G /\ (x ** 0 = #e)}   by roots_of_unity_def
   Since   x ** 0 = #e                                  by group_exp_0
   (uroots 0).carrier = {x | x IN G /\ T} = G           by EXTENSION
*)
val roots_of_unity_0 = store_thm(
  "roots_of_unity_0",
  ``!g:'a group. (uroots 0).carrier = G``,
  rw[roots_of_unity_def]);

(* Theorem: #e IN (uroots n).carrier *)
(* Proof: by group_id_exp. *)
val group_uroots_has_id = store_thm(
  "group_uroots_has_id",
  ``!g:'a group. Group g ==> !n. #e IN (uroots n).carrier``,
  rw[roots_of_unity_def]);

(* Theorem: AbelianGroup g ==> uroots n <= g *)
(* Proof:
   By subgroup_alt, roots_of_unity_def, this is to show:
   (1) ?x. x IN G /\ (x ** n = #e)
       Since #e IN G   by group_id_element
       This is true    by group_id_exp
   (2) x ** n = #e /\ y ** n = #e ==> (x * |/ y) ** n = #e
         (x * |/ y) ** n
       = (x ** n) * ( |/ y) ** n   by group_comm_op_exp
       = (x ** n) * |/ (y ** n)    by group_inv_exp
       = #e * |/ #e                by x, y IN uroots n
       = #e * #e                   by group_inv_exp
       = #e                        by group_id_id
*)
val group_uroots_subgroup = store_thm(
  "group_uroots_subgroup",
  ``!g:'a group. AbelianGroup g ==> !n. uroots n <= g``,
  rw[AbelianGroup_def] >>
  rw[subgroup_alt, roots_of_unity_def, EXTENSION, SUBSET_DEF] >-
  metis_tac[group_id_element, group_id_exp] >>
  rw[group_inv_exp, group_inv_id, group_comm_op_exp]);

(* Theorem: AbelianGroup g ==> !n. Group (uroots n) *)
(* Proof: by group_uroots_subgroup, Subgroup_def *)
Theorem group_uroots_group:
  !g:'a group. AbelianGroup g ==> !n. Group (uroots n)
Proof
  metis_tac[group_uroots_subgroup, Subgroup_def]
QED

(* Is this true: Group g ==> !n. Group (uroots n) *)
(* No? *)

(* Theorem: AbelianGroup g ==> !n. Group (uroots n) *)
(* Proof:
   By roots_of_unity_def, group_def_alt, this is to show:
   (1) x ** n = #e /\ y ** n = #e ==> (x * y) ** n = #e,  true by group_comm_op_exp
   (2) z * (x * y) = x * (y * z)
         z * (x * y)
       = (z * x) * y            by group_assoc
       = (x * z) * y            by commutativity condition
       = x * (z * y)            by group_assoc
       = x * (y * z)            by commutativity condition
   (3) x ** n = #e ==> ?y. (y IN G /\ (y ** n = #e)) /\ (y * x = #e)
       Let m = ord x.
       Then m divides n         by group_order_divides_exp
       Note ord ( |/ x) = m     by group_inv_order
       Thus ( |/ x) ** n = #e   by group_order_divides_exp
       Take y = |/ x, then true by group_linv
*)
Theorem group_uroots_group[allow_rebind]:
  !g:'a group. AbelianGroup g ==> !n. Group (uroots n)
Proof
  rw[AbelianGroup_def] >>
  rw[roots_of_unity_def, group_def_alt]
  >- rw[group_comm_op_exp]
  >- metis_tac[group_assoc] >>
  metis_tac[group_order_divides_exp, group_inv_order, group_linv,
            group_inv_element]
QED

(* ------------------------------------------------------------------------- *)
(* Subgroup generated by a subset of a Group.                                *)
(* ------------------------------------------------------------------------- *)

(* Define the group generated by a subset of the group carrier *)
val Generated_subset_def = Define`
    Generated_subset (g:'a group) (s:'a -> bool) =
        <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H}); op := g.op; id := #e|>
`;
(* Note: this is the minimal subgroup containing the subset. *)
(* Similar to subgroup_big_intersect_def in subgroup theory. *)
val _ = overload_on("gen_set", ``Generated_subset (g:'a group)``);

(* Theorem: ((gen_set s).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H})) /\
            ((gen_set s).op = g.op) /\ ((gen_set s).id = #e) *)
(* Proof: by Generated_subset_def *)
val Generated_subset_property = store_thm(
  "Generated_subset_property",
  ``!(g:'a group) s. ((gen_set s).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H})) /\
                    ((gen_set s).op = g.op) /\ ((gen_set s).id = #e)``,
  rw[Generated_subset_def]);

(* Theorem: s SUBSET (gen_set s).carrier *)
(* Proof: by Generated_subset_def, SUBSET_DEF *)
val Generated_subset_has_set = store_thm(
  "Generated_subset_has_set",
  ``!(g:'a group) s. s SUBSET (gen_set s).carrier``,
  rw[Generated_subset_def, SUBSET_DEF] >>
  simp[]);

(* Theorem: Group g /\ s SUBSET G ==> (gen_set s).carrier SUBSET G *)
(* Proof:
   By Generated_subset_def, this is to show:
      BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H}) SUBSET G
   By BIGINTER_SUBSET, this is to show:
      ?t. t IN IMAGE (\h. H) {h | h <= g /\ s SUBSET H} /\ t SUBSET G
   By IN_IMAGE, this is,
      ?t. (?h. t = H /\ h <= g /\ s SUBSET H) /\ t SUBSET G
   or ?h. h <= g /\ s SUBSET H     by subgroup_carrier_subset
   Take h = g,
   Then g <= g                     by subgroup_refl
    and s SUBSET G                 by given
*)
Theorem Generated_subset_subset:
  !(g:'a group) s. Group g /\ s SUBSET G ==> (gen_set s).carrier SUBSET G
Proof
  rw[Generated_subset_def] >>
  irule BIGINTER_SUBSET >>
  csimp[subgroup_carrier_subset, PULL_EXISTS] >>
  metis_tac[subgroup_refl]
QED

(* Theorem: Group g /\ s SUBSET G ==> Group (gen_set s) *)
(* Proof:
   Let t = {h | h <= g /\ s SUBSET H}.
   By group_def_alt, Generated_subset_def, this is to show:
   (1) h IN t ==> x * y IN H
       Note h <= g                by definition of t
       Thus x IN H /\ y IN H      by implication
        ==> h.op x y IN H         by subgroup_property, group_op_element
         or x * y IN H            by subgroup_property
   (2) x * y * z = x * (y * z)
       Note g <= g                       by subgroup_refl
         so g IN t                       by definition of t
       Thus x IN G /\ y IN G /\ z IN G   by implication
       The result follows                by group_assoc
   (3) h IN t ==> #e IN H
       Note h <= g                by definition of t
        ==> h.id IN H             by subgroup_property, group_id_element
         or #e IN H               by subgroup_id
   (4) #e * x = x
       Note g <= g                by subgroup_refl
         so g IN t                by definition of t
       Thus x IN G                by implication
       The result follows         by group_id
   (5) ?y. (!P. (?h. (P = H) /\ h IN {h | h <= g /\ s SUBSET H}) ==> y IN P) /\ (y * x = #e)
       Note g <= g                by subgroup_refl
         so g IN t                by definition of t
       Thus x IN G                by implication
        ==> |/ x IN G             by group_inv_element
        and ( |/ x) * x = #e      by group_linv
       Let y = |/ x.
       Need to show: h IN t ==> y IN H.
       But h IN t ==> h <= g      by definition of t
       Thus x IN H                by implication
         so h.inv x IN H          by subgroup_property, group_inv_element
         or |/ x = y IN H         by subgroup_inv
*)
val Generated_subset_group = store_thm(
  "Generated_subset_group",
  ``!(g:'a group) s. Group g /\ s SUBSET G ==> Group (gen_set s)``,
  rpt strip_tac >>
  rw_tac std_ss[group_def_alt, Generated_subset_def, IN_BIGINTER, IN_IMAGE] >| [
    `h <= g` by fs[] >>
    `x IN H /\ y IN H` by metis_tac[] >>
    metis_tac[subgroup_property, group_op_element],
    `g <= g` by rw[subgroup_refl] >>
    `g IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN G /\ y IN G /\ z IN G` by metis_tac[] >>
    rw[group_assoc],
    `h <= g` by fs[] >>
    metis_tac[subgroup_property, subgroup_id, group_id_element],
    `g <= g` by rw[subgroup_refl] >>
    `g IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN G` by metis_tac[] >>
    rw[],
    `g <= g` by rw[subgroup_refl] >>
    `g IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN G` by metis_tac[] >>
    `|/ x IN G` by rw[] >>
    `( |/ x) * x = #e` by rw[] >>
    qexists_tac `|/ x` >>
    rw[] >>
    `h IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN H` by metis_tac[] >>
    metis_tac[subgroup_property, subgroup_inv, group_inv_element]
  ]);

(* Theorem: Group g /\ s SUBSET G ==> (gen_set s) <= g *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (gen_set s), true              by Generated_subset_group
   (2) (gen_set s).carrier SUBSET G, true   by Generated_subset_subset
   (3) (gen_set s).op = $*, true            by Generated_subset_property
*)
val Generated_subset_subgroup = store_thm(
  "Generated_subset_subgroup",
  ``!(g:'a group) s. Group g /\ s SUBSET G ==> (gen_set s) <= g``,
  rw[Subgroup_def] >-
  rw[Generated_subset_group] >-
  rw[Generated_subset_subset] >>
  rw[Generated_subset_property]);

(* Theorem: Group g /\ s SUBSET G ==> (gen_set s) <= g *)
(* Proof: by Generated_subset_def, monoid_exp_def, FUN_EQ_THM *)
val Generated_subset_exp = store_thm(
  "Generated_subset_exp",
  ``!(g:'a group) s. (gen_set s).exp = g.exp``,
  rw[Generated_subset_def, monoid_exp_def, FUN_EQ_THM]);

(* Theorem: FiniteGroup g /\ a IN G ==> (gen_set (Gen a) = gen a) *)
(* Proof:
   By Generated_def, Generated_subset_def, SUBSET_DEF, EXTENSION,
   this is to show:
   (1) a IN G /\
       !P. (?h. (!x. (x IN P ==> x IN H) /\ (x IN H ==> x IN P)) /\
                h <= g /\ !x. (?k. x = a ** k) ==> x IN H) ==> x IN P
       ==> ?k. x = a ** k
       Take P = Gen a, and h = gen a.
       Note h <= g             by generated_subgroup
        and ?k. x = a ** k     by generated_element
       Take this k, the result follows.
   (2) a IN G /\ !x. (?k. x = a ** k) ==> x IN H /\
                 !x'. (x' IN P ==> x' IN H) /\ (x' IN H ==> x' IN P)
       ==> a ** k IN P
       Let x = a ** k.
       Note x IN H       by the first implication,
       Thus x IN P       by the second implication.
*)
val Generated_subset_gen = store_thm(
  "Generated_subset_gen",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> (gen_set (Gen a) = gen a)``,
  rpt (stripDup[FiniteGroup_def]) >>
  rw[Generated_def, Generated_subset_def, SUBSET_DEF, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    last_x_assum (qspecl_then [`Gen a`] strip_assume_tac) >>
    `gen a <= g` by rw[generated_subgroup] >>
    metis_tac[generated_element],
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Finite Group Theory Documentation                                         *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   s1 o s2             = subset_cross (g:'a group) s1 s2
   h1 o h2             = subgroup_cross (g:'a group) h1 h2
   left z              = subset_cross_left g s1 s2 z
   right z             = subset_cross_right g s1 s2 z
   independent g a b   = (Gen a) INTER (Gen b) = {#e}
   sgbcross B          = subgroup_big_cross (g:'a group) B
   ssbcross B          = subset_big_cross (g:'a group) B
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Cross Product of Subset and Subgroup:
   make_group_def         |- !g s. make_group g s = <|carrier := s; op := $*; id := #e|>
   make_group_property    |- !g s. ((make_group g s).carrier = s) /\
                                   ((make_group g s).op = $* ) /\
                                   ((make_group g s).id = #e)

   subset_cross_def          |- !g s1 s2. s1 o s2 = {x * y | x IN s1 /\ y IN s2}
   subset_cross_element      |- !g s1 s2 x y. x IN s1 /\ y IN s2 ==> x * y IN s1 o s2
   subset_cross_element_iff  |- !g s1 s2 z. z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)
   subset_cross_alt          |- !g s1 s2. s1 o s2 = IMAGE (\(x,y). x * y) (s1 CROSS s2)

   subgroup_cross_def        |- !g h1 h2. h1 o h2 = make_group g (h1.carrier o h2.carrier)
   subgroup_cross_property   |- !g h1 h2. ((h1 o h2).carrier = h1.carrier o h2.carrier) /\
                                          ((h1 o h2).op = $* ) /\ ((h1 o h2).id = #e)
   subgroup_test_by_cross    |- !g. Group g ==> !h. h <= g <=>
                                    H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE |/ H = H)

   Subset Cross Properties:
   subset_cross_assoc      |- !g. Group g ==>
                              !s1 s2 s3. s1 SUBSET G /\ s2 SUBSET G /\ s3 SUBSET G ==>
                                         ((s1 o s2) o s3 = s1 o s2 o s3)
   subset_cross_self       |- !g h. h <= g ==> (H o H = H)
   subset_cross_comm       |- !g. AbelianGroup g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2 = s2 o s1)
   subset_cross_subset     |- !g. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> s1 o s2 SUBSET G
   subset_cross_inv        |- !g. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==>
                                              (IMAGE |/ (s1 o s2) = IMAGE |/ s2 o IMAGE |/ s1)
   subset_cross_finite     |- !g s1 s2. FINITE s1 /\ FINITE s2 ==> FINITE (s1 o s2)

   Subgroup Cross Properties:
   subgroup_cross_assoc    |- !g h1 h2 h3. h1 <= g /\ h2 <= g /\ h3 <= g ==> ((h1 o h2) o h3 = h1 o h2 o h3)
   subgroup_cross_self     |- !g h. h <= g ==> (h o h = h)
   subgroup_cross_comm     |- !g. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2 = h2 o h1)
   subgroup_cross_subgroup |- !g h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> h1 o h2 <= g
   subgroup_cross_group    |- !g h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> Group (h1 o h2)
   abelian_subgroup_cross_subgroup   |- !g. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> h1 o h2 <= g
   subgroup_cross_finite   |- !g h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) /\ FiniteGroup h1 /\
                              FiniteGroup h2 ==> FiniteGroup (h1 o h2)
   abelian_subgroup_cross_finite     |- !g. AbelianGroup g ==>
                                        !h1 h2. h1 <= g /\ h2 <= g /\ FiniteGroup h1 /\ FiniteGroup h2 ==>
                                        FiniteGroup (h1 o h2)

   Subgroup Cross Cardinality:
   subset_cross_left_right_def         |- !g s1 s2 z. z IN s1 o s2 ==>
                                          left z IN s1 /\ right z IN s2 /\ (z = left z * right z)
   subset_cross_to_preimage_cross_bij  |- !g h1 h2. h1 <= g /\ h2 <= g ==>
                                          (let s1 = h1.carrier in let s2 = h2.carrier in
                                           let f (x,y) = x * y in
                                          !z. z IN s1 o s2 ==>
                                              BIJ (\d. (left z * d,|/ d * right z)) (s1 INTER s2)
                                                                    (preimage f (s1 CROSS s2) z))
   subset_cross_partition_property     |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                             (let s1 = h1.carrier in let s2 = h2.carrier in
                                              let f (x,y) = x * y in
                                          !t. t IN partition (feq f) (s1 CROSS s2) ==>
                                              (CARD t = CARD (s1 INTER s2)))
   subset_cross_element_preimage_card  |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                          (let s1 = h1.carrier in let s2 = h2.carrier in
                                           let f (x,y) = x * y in
                                          !z. z IN s1 o s2 ==>
                                          (CARD (preimage f (s1 CROSS s2) z) = CARD (s1 INTER s2)))
   subset_cross_preimage_inj   |- !g s1 s2. INJ (preimage (\(x,y). x * y) (s1 CROSS s2)) (s1 o s2)
                                                                            univ(:'a # 'a -> bool)
   subgroup_cross_card_eqn     |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                  (let s1 = h1.carrier in let s2 = h2.carrier in
                                   CARD (h1 o h2).carrier * CARD (s1 INTER s2) = CARD s1 * CARD s2)
   subgroup_cross_card         |- !g h1 h2. h1 <= g /\ h2 <= g /\ FINITE G ==>
                                  (let s1 = h1.carrier in let s2 = h2.carrier in
                                   CARD (h1 o h2).carrier = CARD s1 * CARD s2 DIV CARD (s1 INTER s2))

   Finite Group Generators:
   independent_sym                 |- !g a b. independent g a b <=> independent g b a
   independent_generated_eq        |- !g. Group g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                                                      ((gen a = gen b) <=> (a = b))
   independent_generator_2_card    |- !g. FiniteGroup g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                                          (CARD (gen a o gen b).carrier = ord a * ord b)

   all_subgroups_def          |- !g. all_subgroups g = {h | h <= g}
   all_subgroups_element      |- !g h. h IN all_subgroups g <=> h <= g
   all_subgroups_subset       |- !g. Group g ==> IMAGE (\h. H) (all_subgroups g) SUBSET POW G
   all_subgroups_has_gen_id   |- !g. Group g ==> gen #e IN all_subgroups g
   all_subgroups_finite       |- !g. FiniteGroup g ==> FINITE (all_subgroups g)
   generated_image_subset_all_subgroups    |- !g. FiniteGroup g ==>
                                              !s. s SUBSET G ==> IMAGE gen s SUBSET all_subgroups g
   generated_image_subset_power_set       |- !g. Group g ==> !s. s SUBSET G ==> IMAGE (\a. Gen a) s SUBSET POW G

   subset_cross_closure_comm_assoc_fun    |- !g. AbelianGroup g ==> closure_comm_assoc_fun $o (POW G)
   subgroup_cross_closure_comm_assoc_fun  |- !g. AbelianGroup g ==> closure_comm_assoc_fun $o (all_subgroups g)

   Big Cross of Subsets:
   subset_big_cross_def         |- !g B. ssbcross B = ITSET $o B {#e}
   subset_big_cross_empty       |- !g. ssbcross {} = {#e}
   subset_big_cross_thm         |- !g. FiniteAbelianGroup g ==> !B. B SUBSET POW G ==>
                                   !s. s SUBSET G ==> (ssbcross (s INSERT B) = s o ssbcross (B DELETE s))
   subset_big_cross_insert      |- !g. FiniteAbelianGroup g ==> !B. B SUBSET POW G ==>
                                   !s. s SUBSET G /\ s NOTIN B ==> (ssbcross (s INSERT B) = s o ssbcross B)

   Big Cross of Subgroups:
   subgroup_big_cross_def       |- !g B. sgbcross B = ITSET $o B (gen #e)
   subgroup_big_cross_empty     |- !g. sgbcross {} = gen #e
   subgroup_big_cross_thm       |- !g. FiniteAbelianGroup g ==> !B. B SUBSET all_subgroups g ==>
                                   !h. h IN all_subgroups g ==> (sgbcross (h INSERT B) = h o sgbcross (B DELETE h))
   subgroup_big_cross_insert    |- !g. FiniteAbelianGroup g ==> !B. B SUBSET all_subgroups g ==>
                                   !h. h IN all_subgroups g /\ h NOTIN B ==> (sgbcross (h INSERT B) = h o sgbcross B)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Cross Product of Subset and Subgroup                                      *)
(* ------------------------------------------------------------------------- *)

(* Given a Group g, and a subset s, make a group by inheriting op and id. *)
val make_group_def = Define`
    make_group (g:'a group) (s:'a -> bool) =
       <| carrier := s;
               op := g.op;
               id := g.id
        |>
`;

(* Theorem: Properties of make_group g s *)
(* Proof: by make_group_def *)
val make_group_property = store_thm(
  "make_group_property",
  ``!(g:'a group) s. ((make_group g s).carrier = s) /\
                    ((make_group g s).op = g.op) /\
                    ((make_group g s).id = g.id)``,
  rw[make_group_def]);

(* Given two subsets, define their cross-product, or direct product *)
val subset_cross_def = Define`
    subset_cross (g:'a group) (s1:'a -> bool) (s2:'a -> bool) =
       {x * y | x IN s1 /\ y IN s2}
`;

(* Overload subset cross product *)
val _ = overload_on("o", ``subset_cross (g:'a group)``);
(*
> subset_cross_def;
val it = |- !g s1 s2. s1 o s2 = {x * y | x IN s1 /\ y IN s2}: thm
*)

(* Theorem: x IN s1 /\ y IN s2 ==> x * y IN s1 o s2 *)
(* Proof: by subset_cross_def *)
val subset_cross_element = store_thm(
  "subset_cross_element",
  ``!g:'a group. !s1 s2. !x y. x IN s1 /\ y IN s2 ==> x * y IN s1 o s2``,
  rw[subset_cross_def] >>
  metis_tac[]);

(* Theorem: z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y) *)
(* Proof:
   By subset_cross_def, this ius to show:
      (?x y. (z = x * y) /\ x IN s1 /\ y IN s2) <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)
   The candidates are just the x, y themselves.
*)
val subset_cross_element_iff = store_thm(
  "subset_cross_element_iff",
  ``!g:'a group. !s1 s2 z. z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)``,
  rw[subset_cross_def] >>
  metis_tac[]);

(* Theorem: s1 o s2 = IMAGE (\(x, y). x * y) (s1 CROSS s2) *)
(* Proof:
   By subset_cross_def, EXTENSION, this is to show:
   (1) x IN s1 /\ y IN s2 ==> ?x'. (x * y = (\(x,y). x * y) x') /\ FST x' IN s1 /\ SND x' IN s2
       Take x' = (x, y), this is true by function application.
   (2) FST x' IN s1 /\ SND x' IN s2 ==> ?x y. ((\(x,y). x * y) x' = x * y) /\ x IN s1 /\ y IN s2
       Let x = FST x', y = SND x', this is true y UNCURRY.
*)
val subset_cross_alt = store_thm(
  "subset_cross_alt",
  ``!(g:'a group) s1 s2. s1 o s2 = IMAGE (\(x, y). x * y) (s1 CROSS s2)``,
  rw[subset_cross_def, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `(x', y)` >>
    simp[],
    qexists_tac `FST x'` >>
    qexists_tac `SND x'` >>
    simp[pairTheory.UNCURRY]
  ]);

(* Given two subgroups, define their cross-product, or direct product *)
val subgroup_cross_def = Define`
    subgroup_cross (g:'a group) (h1:'a group) (h2:'a group) =
       make_group g (h1.carrier o h2.carrier)
`;

(* Overload subgroup cross product *)
val _ = overload_on("o", ``subgroup_cross (g:'a group)``);
(*
> subgroup_cross_def;
val it = |- !g h1 h2. h1 o h2 = make_group g (h1.carrier o h2.carrier): thm
*)

(* Theorem: ((h1 o h2).carrier = h1.carrier o h2.carrier) /\ ((h1 o h2).op = g.op) /\ ((h1 o h2).id = #e) *)
(* Proof: by subgroup_cross_def, make_group_def *)
val subgroup_cross_property = store_thm(
  "subgroup_cross_property",
  ``!(g h1 h2):'a group. ((h1 o h2).carrier = h1.carrier o h2.carrier) /\
                        ((h1 o h2).op = g.op) /\ ((h1 o h2).id = #e)``,
  rw[subgroup_cross_def, make_group_def]);

(* The following is a reformulation of:
subgroup_alt
|- !g. Group g ==> !h. h <= g <=>
                   H <> {} /\ H SUBSET G /\ (h.op = $* ) /\ (h.id = #e) /\
                   !x y. x IN H /\ y IN H ==> x * |/ y IN H: thm
*)

(* Theorem: Group g ==>
            !h. h <= g <=> H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H) *)
(* Proof:
   If part: h <= g ==> H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H)
      This is to show:
      (1) h <= g ==> H <> {}, true          by subgroup_carrier_nonempty
      (2) h <= g ==> H SUBSET G, true       by subgroup_carrier_subset
      (3) h <= g ==> h o h = h
          Note (h o h).op = $* = h.op       by subgroup_cross_property, Subgroup_def
           and (h o h).id = #e = h.id       by subgroup_cross_property, subgroup_id
          Need only to show: H o H = H      by monoid_component_equality
          By EXTENSION, this is to show:
          (3.1) x IN H /\ y IN H ==> x * y IN H
                Note x * y = h.op x y       by subgroup_property
                 and h.op x y IN H          by group_op_element
          (3.2) z IN H ==> ?x y. z = x * y /\ x IN H /\ y IN H
                Note h.id IN H              by group_id_element
                Take x = h.id, y = z
                Then x * y
                   = h.op (h.id) z          by subgroup_property
                   = z                      by group_id
      (4) h <= g ==> IMAGE ( |/) H = H
          By IN_IMAGE, EXTENSION, this is to show:
          (4.1) x IN H ==> |/ x IN H
                Note |/ x = h.inv x         by subgroup_inv
                 and (h.inv x) IN H         by group_inv_element
          (4.2) z IN H ==> ?x. (z = |/ x) /\ x IN H
                Take x = h.inv z
                Then x = h.inv z IN H       by group_inv_element
                     |/ x
                   = |/ (h.inv z)           by above
                   = h.inv (h.inv z)        by subgroup_inv
                   = z                      by group_inv_inv

   Only-if part: H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H) ==> h <= g
      By subgroup_alt, this is to show:
      (1) h o h = h ==> h.op = $*
            h.op
          = (h o h).op                      by monoid_component_equality
          = $*                              by subgroup_cross_property
      (2) h o h = h ==> h.id = #e
            h.id
          = (h o h).id                      by monoid_component_equality
          = #e                              by subgroup_cross_property
      (3) h o h = h /\ IMAGE |/ H = H /\ x IN H /\ y IN H ==> x * |/ y IN H
          Note |/ y IN IMAGE |/ H           by IN_IMAGE
            or |/ y IN H                    by H = IMAGE |/ H
            so x * |/ y IN H o H            by subset_cross_element
            or x * |/ y IN H                by subgroup_cross_property
*)
val subgroup_test_by_cross = store_thm(
  "subgroup_test_by_cross",
  ``!g:'a group. Group g ==>
   !h. h <= g <=> H <> {} /\ H SUBSET G /\ (h o h = h) /\ (IMAGE ( |/) H = H)``,
  rw[EQ_IMP_THM] >-
  metis_tac[subgroup_carrier_nonempty] >-
  rw[subgroup_carrier_subset] >-
 (pop_assum mp_tac >>
  stripDup[Subgroup_def] >>
  `h.id = #e` by rw[subgroup_id] >>
  rw[subgroup_cross_property, subset_cross_def, monoid_component_equality, EXTENSION, EQ_IMP_THM] >-
  metis_tac[subgroup_property, group_op_element] >>
  metis_tac[subgroup_property, group_id_element, group_id]) >-
 (pop_assum mp_tac >>
  stripDup[Subgroup_def] >>
  `h.id = #e` by rw[subgroup_id] >>
  rw[EXTENSION, EQ_IMP_THM] >-
  metis_tac[subgroup_inv, group_inv_element] >>
  metis_tac[subgroup_inv, group_inv_element, group_inv_inv]) >>
  rw[subgroup_alt] >-
  fs[subgroup_cross_property, monoid_component_equality] >-
  fs[subgroup_cross_property, monoid_component_equality] >>
  prove_tac[subgroup_cross_property, subset_cross_element, IN_IMAGE]);

(* ------------------------------------------------------------------------- *)
(* Subset Cross Properties                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g ==> !s1 s2 s3. s1 SUBSET G /\ s2 SUBSET G /\ s3 SUBSET G ==>
                        ((s1 o s2) o s3 = s1 o (s2 o s3)) *)
(* Proof:
   By subset_cross_def, EXTENSION this is to show:
   (?x' y. (x = x' * y) /\ (?x'' y. (x' = x'' * y) /\ x'' IN s1 /\ y IN s2) /\ y IN s3) <=>
    ?x' y. (x = x' * y) /\ x' IN s1 /\ ?x y'. (y = x * y') /\ x IN s2 /\ y' IN s3
   By SUBSET_DEF, the candidates are readily chosen, with equations valid by group_assoc.
*)
val subset_cross_assoc = store_thm(
  "subset_cross_assoc",
  ``!g:'a group. Group g ==> !s1 s2 s3. s1 SUBSET G /\ s2 SUBSET G /\ s3 SUBSET G ==>
       ((s1 o s2) o s3 = s1 o (s2 o s3))``,
  rw[subset_cross_def, EXTENSION] >>
  prove_tac[group_assoc, SUBSET_DEF]);

(* Theorem: h <= g ==> (h o h = h) *)
(* Proof:
   Note Group g /\ Group h         by subgroup_property
   By subset_cross_element_iff, EXTENSION, this is to show:
   (1) h <= g /\ x IN H /\ y IN H ==> x * y IN H
       Note x * y = h.op x y       by subgroup_op
        and h.op x y IN H          by group_op_element
   (2) z IN H ==> ?x y. x IN H /\ y IN H /\ (z = x * y)
       Let x = h.id, y = z.
       Then x IN H                 by group_id_element
       and x * y = h.op x y        by subgroup_op
                 = y               by group_id
                 = z               by above
*)
val subset_cross_self = store_thm(
  "subset_cross_self",
  ``!(g h):'a group. h <= g ==> (H o H = H)``,
  rpt strip_tac >>
  `Group g /\ Group h` by metis_tac[subgroup_property] >>
  rw[subset_cross_element_iff, EXTENSION, EQ_IMP_THM] >-
  metis_tac[subgroup_op, group_op_element] >>
  metis_tac[subgroup_id, subgroup_op, group_id_element, group_id]);

(* Theorem: AbelianGroup g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2 = s2 o s1) *)
(* Proof:
   Note Group g                     by AbelianGroup_def
    and !x y. x IN G /\ y IN G
        ==> (x * y = y * x)         by AbelianGroup_def
    s1 o s2
  = {x * y | x IN s1 /\ y IN s2}    by subset_cross_def
  = {y * x | y IN s2 /\ x IN s1}    by above, SUBSET_DEF
  = s2 o s1                         by subset_cross_def
*)
val subset_cross_comm = store_thm(
  "subset_cross_comm",
  ``!g:'a group. AbelianGroup g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2 = s2 o s1)``,
  rw[AbelianGroup_def] >>
  rw[subset_cross_def, EXTENSION] >>
  metis_tac[SUBSET_DEF]);

(* Theorem: Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2) SUBSET G *)
(* Proof:
   By subset_cross_def, SUBSET_DEF, this is to show:
       x IN s1 /\ y IN s2 ==> x * y IN G
   But x IN s1 ==> x IN G       by SUBSET_DEF, s1 SUBSET G
   and y IN s2 ==> y IN G       by SUBSET_DEF, s2 SUBSET G
   ==> x * y IN G               by group_op_element
*)
val subset_cross_subset = store_thm(
  "subset_cross_subset",
  ``!g:'a group. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==> (s1 o s2) SUBSET G``,
  rw[subset_cross_def, SUBSET_DEF, pairTheory.EXISTS_PROD] >>
  rw[]);

(* Theorem: Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==>
            (IMAGE ( |/) (s1 o s2) = (IMAGE ( |/) s2) o (IMAGE ( |/) s1)) *)
(* Proof:
   By subset_cross_def, SUBSET_DEF, this is to show:
      (?x'. (x = |/ x') /\ ?x y. (x' = x * y) /\ x IN s1 /\ y IN s2) <=>
      ?x' y. (x = x' * y) /\ (?x''. (x' = |/ x'') /\ x'' IN s2) /\ ?x. (y = |/ x) /\ x IN s1
   Both directions are satisfied by group_inv_op:
      |- !g. Group g ==> !x y. x IN G /\ y IN G ==> ( |/ (x * y) = |/ y * |/ x)
*)
val subset_cross_inv = store_thm(
  "subset_cross_inv",
  ``!g:'a group. Group g ==> !s1 s2. s1 SUBSET G /\ s2 SUBSET G ==>
         (IMAGE ( |/) (s1 o s2) = (IMAGE ( |/) s2) o (IMAGE ( |/) s1))``,
  rw[subset_cross_def, SUBSET_DEF, pairTheory.EXISTS_PROD, EXTENSION] >>
  metis_tac[group_inv_op]);

(* Theorem: FINITE s1 /\ FINITE s2 ==> FINITE (s1 o s2) *)
(* Proof:
   Note s1 o s2 = IMAGE (\(x,y). x * y) (s1 CROSS s2)    by subset_cross_alt
    and FINITE (s1 CROSS s2)                             by FINITE_CROSS
   Thus FINITE (s1 o s2)                                 by IMAGE_FINITE
*)
val subset_cross_finite = store_thm(
  "subset_cross_finite",
  ``!g:'a group. !s1 s2. FINITE s1 /\ FINITE s2 ==> FINITE (s1 o s2)``,
  rw[subset_cross_alt]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Cross Properties                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: h1 <= g /\ h2 <= g /\ h3 <= g ==> ((h1 o h2) o h3 = h1 o (h2 o h3)) *)
(* Proof:
   Note Group g              by subgroup_property
    and h1.carrier SUBSET G  by subgroup_carrier_subset, h1 <= g
    and h2.carrier SUBSET G  by subgroup_carrier_subset, h2 <= g
    and h3.carrier SUBSET G  by subgroup_carrier_subset, h3 <= g
   By subgroup_cross_property, monoid_component_equality, this is to show:
      (h1.carrier o h2.carrier) o h3.carrier = h1.carrier o (h2.carrier o h3.carrier)
   This is true by subset_cross_assoc.
*)
val subgroup_cross_assoc = store_thm(
  "subgroup_cross_assoc",
  ``!g:'a group. !h1 h2 h3. h1 <= g /\ h2 <= g /\ h3 <= g ==>
       ((h1 o h2) o h3 = h1 o (h2 o h3))``,
  rpt strip_tac >>
  `Group g` by metis_tac[subgroup_property] >>
  rw[subgroup_cross_property, monoid_component_equality, subgroup_carrier_subset, subset_cross_assoc]);

(* Theorem: h <= g ==> (h o h = h) *)
(* Proof:
   By subgroup_cross_property, monoid_component_equality, this is to show:
   (1) h <= g ==>  H o H = H, true    by subset_cross_self
   (2) h <= g ==> $* = h.op, true     by subgroup_op
   (3) h <= g ==> #e = h.id, true     by subgroup_id
*)
val subgroup_cross_self = store_thm(
  "subgroup_cross_self",
  ``!(g h):'a group. h <= g ==> (h o h = h)``,
  rw[subgroup_cross_property, monoid_component_equality] >-
  rw[subset_cross_self] >-
  rw[subgroup_op] >>
  rw[subgroup_id]);

(* Theorem: AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2 = h2 o h1) *)
(* Proof:
   Note Group g             by AbelianGroup_def
   Let s1 = h1.carrier, s2 = h2.carrier.
   By subgroup_cross_property, monoid_component_equality,
   this is to show: s1 o s2 = s2 o s1
   But s1 SUBSET G          by subgroup_carrier_subset
   and s2 SUBSET G          by subgroup_carrier_subset
   so s1 o s2 = s2 o s1     by subset_cross_comm
*)
val subgroup_cross_comm = store_thm(
  "subgroup_cross_comm",
  ``!g:'a group. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2 = h2 o h1)``,
  rw[AbelianGroup_def, subgroup_cross_property,
     monoid_component_equality, subset_cross_comm, subgroup_carrier_subset]);

(* Theorem: h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> (h1 o h2) <= g *)
(* Proof:
   Note Group g                   by subgroup_property
    and Group h1 /\ Group h2      by subgroup_property
   By subgroup_test_by_cross, this is to show:
   (1) h1 <= g /\ h2 <= g ==> (h1 o h2).carrier <> {}
       Note h1.id IN h1.carrier                        by group_id_element
        and h2.id IN h2.carrier                        by group_id_element
       Thus h1.id * h2.id IN (h1.carrier o h2.carrier) by subset_cross_element
         or h1.id * h2.id IN (h1 o h2).carrier         by subgroup_cross_property
         or (h1 o h2).carrier <> {}                    by MEMBER_NOT_EMPTY
   (2) h1 <= g /\ h2 <= g ==> (h1 o h2).carrier SUBSET G
       Let z IN (h1 o h2).carrier
       Then ?x y. x IN h1.carrier /\ y IN h2.carrier
       giving z = x * y                                by subgroup_cross_property, subset_cross_element_iff
       But x IN G                                      by subgroup_carrier_subset, SUBSET_DEF, h1 <= g
       and y IN G                                      by subgroup_carrier_subset, SUBSET_DEF, h2 <= g
       ==> x * y IN G or z IN G                        by group_op_element
       Thus (h1 o h2).carrier SUBSET G                 by SUBSET_DEF
   (3) h1 <= g /\ h2 <= g ==> (h1 o h2) o (h1 o h2) = h1 o h2
       Let H = h1.carrier, K = h2.carrier.
       Note ((h1 o h2) o (h1 o h2)).op = (h1 o h2).op             by subgroup_cross_property
        and ((h1 o h2) o (h1 o h2)).id = (h1 o h2).id             by subgroup_cross_property
       Thus by monoid_component_equality, this is
            to show:
            ((h1 o h2) o (h1 o h2)).carrier = (h1 o h2).carrier   by subgroup_cross_property
         or to show: (H o K) o (H o K) = H o K                    by subgroup_cross_property
       Note H SUBSET G /\ K SUBSET G      by subgroup_carrier_subset
        and H o K = K o H                 by subgroup_cross_property, monoid_component_equality, h1 o h2 = h2 o h1
       Also (H o K) SUBSET G              by subset_cross_subset, H SUBSET G, K SUBSET G

            (H o K) o (H o K)
          = ((H o K) o H) o K             by subset_cross_assoc, (H o K) SUBSET G
          = (H o (K o H)) o K             by subset_cross_assoc
          = (H o (H o K)) o K             by above
          = ((H o H) o K) o K             by subset_cross_assoc
          = (H o K) o K                   by subset_cross_self, h1 <= g
          = H o (K o K)                   by subset_cross_assoc
          = H o K                         by subset_cross_self, h2 <= g
   (4) h1 <= g /\ h2 <= g ==> IMAGE |/ (h1 o h2).carrier = (h1 o h2).carrier
       Let H = h1.carrier, K = h2.carrier.
       Note H SUBSET G /\ K SUBSET G      by subgroup_carrier_subset
        and h1 <= g ==> IMAGE |/ H = H    by subgroup_test_by_cross
        and h2 <= g ==> IMAGE |/ K = K    by subgroup_test_by_cross

         IMAGE |/ (h1 o h2).carrier
       = IMAGE |/ (H o K)                 by subgroup_cross_property
       = (IMAGE |/ K) o (IMAGE |/ H)      by subset_cross_inv
       = K o H                            by above
       = H o K                            by subgroup_cross_property, monoid_component_equality, h1 o h2 = h2 o h1
       = (h1 o h2).carrier                by subgroup_cross_property
*)
val subgroup_cross_subgroup = store_thm(
  "subgroup_cross_subgroup",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> (h1 o h2) <= g``,
  rpt strip_tac >>
  `Group g /\ Group h1 /\ Group h2` by metis_tac[subgroup_property] >>
  rw[subgroup_test_by_cross] >-
  metis_tac[group_id_element, subgroup_cross_property, subset_cross_element, MEMBER_NOT_EMPTY] >-
 (rw[SUBSET_DEF] >>
  `?y z. y IN h1.carrier /\ z IN h2.carrier /\ (x = y * z)` by metis_tac[subgroup_cross_property, subset_cross_element_iff] >>
  `y IN G /\ z IN G` by metis_tac[subgroup_carrier_subset, SUBSET_DEF] >>
  rw[]) >-
 (qabbrev_tac `h = h1.carrier` >>
  qabbrev_tac `k = h2.carrier` >>
  `(h o k) o (h o k) = h o k` suffices_by rw[monoid_component_equality, subgroup_cross_property] >>
  `h SUBSET G /\ k SUBSET G` by rw[subgroup_carrier_subset, Abbr`h`, Abbr`k`] >>
  `h o k = k o h` by fs[subgroup_cross_property, monoid_component_equality, Abbr`h`, Abbr`k`] >>
  `(h o k) SUBSET G` by rw[subset_cross_subset] >>
  `(h o k) o (h o k) = ((h o k) o h) o k` by rw[subset_cross_assoc] >>
  `_ = (h o (k o h)) o k` by rw[GSYM subset_cross_assoc] >>
  `_ = (h o (h o k)) o k` by metis_tac[] >>
  `_ = ((h o h) o k) o k` by rw[subset_cross_assoc] >>
  `_ = (h o k) o k` by metis_tac[subset_cross_self] >>
  `_ = h o (k o k)` by rw[subset_cross_assoc] >>
  `_ = h o k` by metis_tac[subset_cross_self] >>
  rw[]) >>
  qabbrev_tac `h = h1.carrier` >>
  qabbrev_tac `k = h2.carrier` >>
  `h SUBSET G /\ k SUBSET G` by rw[subgroup_carrier_subset, Abbr`h`, Abbr`k`] >>
  `IMAGE |/ (h1 o h2).carrier = IMAGE |/ (h o k)` by rw[subgroup_cross_property, Abbr`h`, Abbr`k`] >>
  `_ = (IMAGE |/ k) o (IMAGE |/ h)` by rw[subset_cross_inv] >>
  `_ = k o h` by metis_tac[subgroup_test_by_cross] >>
  `_ = h o k` by metis_tac[subgroup_cross_property, monoid_component_equality] >>
  `_ = (h1 o h2).carrier` by rw[subgroup_cross_property, Abbr`h`, Abbr`k`] >>
  rw[]);

(* This is a milestone theorem for me! *)
(* This is just Lemma X.1 in Appendix of "Finite Group Theory" by Irving Martin Isaacs. *)

(* Theorem: h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> Group (h1 o h2) *)
(* Proof: by subgroup_cross_subgroup, subgroup_property *)
val subgroup_cross_group = store_thm(
  "subgroup_cross_group",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) ==> Group (h1 o h2)``,
  metis_tac[subgroup_cross_subgroup, subgroup_property]);

(* Theorem: AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2) <= g *)
(* Proof: by subgroup_cross_comm, subgroup_cross_subgroup *)
val abelian_subgroup_cross_subgroup = store_thm(
  "abelian_subgroup_cross_subgroup",
  ``!g:'a group. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g ==> (h1 o h2) <= g``,
  rw[subgroup_cross_comm, subgroup_cross_subgroup]);

(* Theorem: h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) /\
            FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2) *)
(* Proof:
   Note Group (h1 o h2)                           by subgroup_cross_group
    and FiniteGroup h1 ==> FINITE (h1.carrier)    by FiniteGroup_def
    and FiniteGroup h2 ==> FINITE (h2.carrier)    by FiniteGroup_def
    ==> FINITE (h1.carrier o h2.carrier)          by subset_cross_finite
     or FINITE (h1 o h2).carrier                  by subgroup_cross_property
*)
val subgroup_cross_finite = store_thm(
  "subgroup_cross_finite",
  ``!g:'a group. !h1 h2. h1 <= g /\ h2 <= g /\ (h1 o h2 = h2 o h1) /\
                FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2)``,
  metis_tac[FiniteGroup_def, subgroup_cross_group, subset_cross_finite, subgroup_cross_property]);

(* Theorem: AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g /\
            FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2) *)
(* Proof: by subgroup_cross_finite, subgroup_cross_comm. *)
val abelian_subgroup_cross_finite = store_thm(
  "abelian_subgroup_cross_finite",
  ``!g:'a group. AbelianGroup g ==> !h1 h2. h1 <= g /\ h2 <= g /\
                FiniteGroup h1 /\ FiniteGroup h2 ==> FiniteGroup (h1 o h2)``,
  rw[subgroup_cross_finite, subgroup_cross_comm]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Cross Cardinality                                                *)
(* ------------------------------------------------------------------------- *)

(* Split element of (s1 o s2) into a left-right pair *)

(*
subset_cross_element_iff
|- !g s1 s2 z. z IN s1 o s2 <=> ?x y. x IN s1 /\ y IN s2 /\ (z = x * y)
*)
val lemma = prove(
  ``!g:'a group. !(s1 s2):'a -> bool. !z. ?x y. z IN (s1 o s2) ==> x IN s1 /\ y IN s2 /\ (z = x * y)``,
  metis_tac[subset_cross_element_iff]);

(* 2. Apply Skolemization *)
val subset_cross_left_right_def = new_specification(
   "subset_cross_left_right_def",
  ["subset_cross_left", "subset_cross_right"],
  SIMP_RULE bool_ss [SKOLEM_THM] lemma);

(* overload subset_cross_left and subset_cross_right *)
val _ = overload_on("left", ``subset_cross_left (g:'a group) (s1:'a -> bool) (s2:'a -> bool)``);
val _ = overload_on("right", ``subset_cross_right (g:'a group) (s1:'a -> bool) (s2:'a -> bool)``);

(*
> subset_cross_left_right_def;
val it = |- !g s1 s2 z. z IN s1 o s2 ==> left z IN s1 /\ right z IN s2 /\ (z = left z * right z): thm
*)

(* Picture of BIJECTION:
(s1 INTER s2) <-> (preimage f s z)
    #e        <-> (left z, right z)
    d         <-> ((left z) * d, ( |/ d) * (right z)))
*)

(* Theorem: h1 <= g /\ h2 <= g ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
            !z. z IN (s1 o s2) ==>
            BIJ (\d. ((left z) * d, ( |/ d) * (right z))) (s1 INTER s2) (preimage f (s1 CROSS s2) z) *)
(* Proof:
   Let s = s1 CROSS s2.
   Note Group g /\ Group h1 /\ Group h2     by subgroup_property
    and s1 SUBSET G /\ s2 SUBSET G          by subgroup_carrier_subset
    and left z IN s1 /\ right z IN s2       by subset_cross_left_right_def
    and !x. x IN s1 ==> x IN G              by SUBSET_DEF, s1 SUBSET G
    and !x. x IN s2 ==> x IN G              by SUBSET_DEF, s2 SUBSET G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) d IN s1 /\ d IN s2 ==> (left z * d,|/ d * mright z) IN preimage f s z
       By in_preimage, IN_CROSS, this is to show:
       (1.1) left z * d IN s1
             Note (left z) * d
                = h.op (left z) d           by subgroup_op
             and  h.op (left z) d IN s1     by group_op_element, Group h1
       (1.2) |/ d * right z IN s2
             With         d IN s2           by given
              ==> (h.inv d) IN s2           by group_inv_element, Group h2
               or      |/ d IN s2           by subgroup_inv, h2 <= g
             Note |/ d * (right z)
                = h.op ( |/ d) (right z)                  by subgroup_op
             and  h.op ( |/ d) (right z) IN s2            by group_op_element, Group h2
       (1.3) left z * d * ( |/ d * right z) = z
             Note |/ d IN G                               by group_inv_element
                  (left z * d) * ( |/ d * right z)
                = ((left z * d) * |/ d) * right z         by group_assoc
                = (left z * (d * |/ d)) * right z         by group_assoc
                = left z * #e * right z                   by group_rinv
                = left z * right z                        by group_rid
                = z                                       by subset_cross_left_right_def
   (2) d IN s1, s2 /\ d' IN s1, s2 /\ left z * d = left z * d' ==> d = d'
       Note left z IN G /\ d IN G /\ d' IN G              by elements in s1 or s2
       Thus left z * d = left z * d' ==> d = d'           by group_lcancel
   (3) d IN s1 /\ d IN s2 ==> (left z * d,|/ d * mright z) IN preimage f s z, same as (1).
   (4) x IN preimage f s z ==> ?d. (d IN s1 /\ d IN s2) /\ ((left z * d,|/ d * right z) = x)
       The idea is:
       To get:  x = (FST x, SND x) = (left z * d, |/ d * right z)
       Use this to solve for d: d = |/ (left z) * FST x

       Note (left z) * (right z) = z      by subset_cross_left_right_def
        and x IN s /\ (f x = z)           by in_preimage
       Let x1 = FST x, x2 = SND x.
       Then x = (x1, x2)                  by PAIR
        and f x = x1 * x2 = z             by function application
        and x1 IN s1 /\ x2 IN s2          by IN_CROSS

       To produce an intersection element,
       Note z = (left z) * (right z) = x1 * x2
        ==>     left z = z * ( |/ (right z))            by group_lsolve
         or     left z = x1 * (x2 * ( |/ (right z)))    by group_assoc, z = x1 * x2
        ==> ( |/ x1) * (left z) = x2 * ( |/ (right z))  by group_rsolve, group_op_element, [1]
       Thus the common element is both IN s1 and IN s2.

       Let d = ( |/ (left z)) * x1, the inverse of common element
       To compute |/ d,
       Note |/ (left z) IN s1             by subgroup_inv, group_inv_element, h1 <= g
        and |/ (right z) IN s2            by subgroup_inv, group_inv_element, h2 <= g
            |/ d
          = |/ (( |/ (left z)) * x1)      by above
          = |/ x1 * (left z)              by group_inv_op, group_inv_inv
          = x2 * ( |/ (right z))          by above identity [1]

       Note d IN s1                       by subgroup_op, group_op_element, d = ( |/ (left z)) * x1
        and |/ d IN s2                    by subgroup_op, group_op_element, |/ d = x2 * ( |/ (right z))
        ==> |/ ( |/ d) = d IN s2          by subgroup_inv, group_inv_element, group_inv_inv

            (left z) * d
          = (left z) * ( |/ (left z)) * x1   by group_assoc
          = x1                               by group_rinv, group_lid
            ( |/ d) * right z
          = x2 * ( |/ (right z) * right z)   by group_assoc
          = x2                               by group_linv, group_rid
       Take this d, and the result follows.
*)
val subset_cross_to_preimage_cross_bij = store_thm(
  "subset_cross_to_preimage_cross_bij",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
   !z. z IN (s1 o s2) ==>
       BIJ (\d. ((left z) * d, ( |/ d) * (right z))) (s1 INTER s2) (preimage f (s1 CROSS s2) z)``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `Group g /\ Group h1 /\ Group h2` by metis_tac[subgroup_property] >>
  `s1 SUBSET G /\ s2 SUBSET G` by rw[subgroup_carrier_subset, Abbr`s1`, Abbr`s2`] >>
  `left z IN s1 /\ right z IN s2` by metis_tac[subset_cross_left_right_def] >>
  `!x. x IN s1 ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `!x. x IN s2 ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `!d. d IN s1 /\ d IN s2 ==> (left z * d, |/ d * right z) IN preimage f s z` by
  (rw[in_preimage, IN_CROSS, Abbr`s`, Abbr`f`] >-
  metis_tac[group_op_element, subgroup_op] >-
  metis_tac[group_inv_element, group_op_element, subgroup_inv, subgroup_op] >>
  `(left z * d) * ( |/ d * right z) = ((left z * d) * |/ d) * right z` by rw[group_assoc] >>
  `_ = (left z * (d * |/ d)) * right z` by rw[GSYM group_assoc] >>
  `_ = z` by rw[subset_cross_left_right_def] >>
  rw[]
  ) >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  metis_tac[group_lcancel] >>
  `(left z) * (right z) = z` by rw[subset_cross_left_right_def, Abbr`s`, Abbr`f`] >>
  `x IN s /\ (f x = z)` by metis_tac[in_preimage] >>
  qabbrev_tac `x1 = FST x` >>
  qabbrev_tac `x2 = SND x` >>
  `x = (x1, x2)` by rw[pairTheory.PAIR, Abbr`x1`, Abbr`x2`] >>
  `x1 * x2 = z` by rw[Abbr`f`] >>
  `x1 IN s1 /\ x2 IN s2` by metis_tac[IN_CROSS] >>
  `z IN G /\ |/ (left z) IN G /\ |/ (right z) IN G` by rw[] >>
  `left z = z * ( |/ (right z))` by rw[GSYM group_lsolve] >>
  `_ = x1 * (x2 * ( |/ (right z)))` by rw[GSYM group_assoc] >>
  `( |/ x1) * (left z) = x2 * ( |/ (right z))` by metis_tac[group_rsolve, group_op_element] >>
  qabbrev_tac `d = ( |/ (left z)) * x1` >>
  `|/ (left z) IN s1` by metis_tac[subgroup_inv, group_inv_element] >>
  `|/ (right z) IN s2` by metis_tac[subgroup_inv, group_inv_element] >>
  `|/ d = |/ x1 * (left z)` by rw[group_inv_op, group_inv_inv, Abbr`d`] >>
  `_ = x2 * ( |/ (right z))` by rw[] >>
  `d IN s1` by metis_tac[subgroup_op, group_op_element] >>
  `|/ d IN s2` by metis_tac[subgroup_op, group_op_element] >>
  `d IN s2` by metis_tac[subgroup_inv, group_inv_element, group_inv_inv] >>
  `(left z) * d = x1` by rw[GSYM group_assoc, Abbr`d`] >>
  `( |/ d) * right z = x2` by rw[group_assoc] >>
  metis_tac[]);

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
            !t. t IN partition (feq f) (s1 CROSS s2) ==> (CARD t = CARD (s1 INTER s2)) *)
(* Proof:
   Let s = s1 CROSS s2.
   Note partition (feq f) s
      = IMAGE ((preimage f s) o f) s       by feq_partition
      = IMAGE (preimage f s) (IMAGE f s)   by IMAGE_COMPOSE
      = IMAGE (preimage f s) (s1 o s2)     by subset_cross_alt
   With t IN partition (feq f) s           by given
    ==> ?z. z IN (IMAGE f s) /\
            (preimage f s z = t)           by IN_IMAGE
    ==> ?m. BIJ m (s1 INTER s2) t          by subset_cross_to_preimage_cross_bij
   Note s1 SUBSET G /\ s2 SUBSET G         by subgroup_carrier_subset
     so FINITE s1 /\ FINITE s2             by SUBSET_FINITE, FINITE G
    ==> FINITE (s1 INTER s2)               by FINITE_INTER
   Thus CARD t = CARD (s1 INTER s2)        by FINITE_BIJ
*)
val subset_cross_partition_property = store_thm(
  "subset_cross_partition_property",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
   !t. t IN partition (feq f) (s1 CROSS s2) ==> (CARD t = CARD (s1 INTER s2))``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `partition (feq f) s = IMAGE (preimage f s) (IMAGE f s)` by rw[feq_partition, IMAGE_COMPOSE] >>
  `_ = IMAGE (preimage f s) (s1 o s2)` by rw[subset_cross_alt, Abbr`s`] >>
  `?z. z IN (s1 o s2) /\ (preimage f s z = t)` by metis_tac[IN_IMAGE] >>
  `?m. BIJ m (s1 INTER s2) t` by metis_tac[subset_cross_to_preimage_cross_bij] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[subgroup_carrier_subset, SUBSET_FINITE] >>
  `FINITE (s1 INTER s2)` by rw[] >>
  metis_tac[FINITE_BIJ]);

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
            !z. z IN (s1 o s2) ==> (CARD (preimage f (s1 CROSS s2) z) = CARD (s1 INTER s2)) *)
(* Proof:
   Let s = s1 CROSS s2.
   Then ?m. BIJ m (s1 INTER s2) (preimage f s z)     by subset_cross_to_preimage_cross_bij
   Note s1 SUBSET G /\ s2 SUBSET G                   by subgroup_carrier_subset
     so FINITE s1 /\ FINITE s2                       by SUBSET_FINITE, FINITE G
    ==> FINITE (s1 INTER s2)                         by FINITE_INTER
   Thus CARD (preimage f s z) = CARD (s1 INTER s2)   by FINITE_BIJ
*)
val subset_cross_element_preimage_card = store_thm(
  "subset_cross_element_preimage_card",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in let (f = (\(x, y). x * y)) in
   !z. z IN (s1 o s2) ==> (CARD (preimage f (s1 CROSS s2) z) = CARD (s1 INTER s2))``,
  metis_tac[subset_cross_to_preimage_cross_bij, subgroup_carrier_subset,
             SUBSET_FINITE, FINITE_INTER, FINITE_BIJ]);

(* Theorem: INJ (preimage (\(x, y). x * y) (s1 CROSS s2)) (s1 o s2) univ(:('a # 'a -> bool)) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN s1 o s2 ==> preimage (\(x,y). x * y) (s1 CROSS s2) x IN univ(:'a reln)
       Since type_of ``preimage (\(x,y). x * y) (s1 CROSS s2) x`` is :'a reln,
       This is true by IN_UNIV
   (2) x IN s1 o s2 /\ y IN s1 o s2 /\
       preimage (\(x,y). x * y) (s1 CROSS s2) x = preimage (\(x,y). x * y) (s1 CROSS s2) y ==> x = y
       Expand by preimage_def, pairTheory.FORALL_PROD, EXTENSION, this is to show:
       !p_1 p_2. (p_1 IN s1 /\ p_2 IN s2) /\ (p_1 * p_2 = x) <=>
                 (p_1 IN s1 /\ p_2 IN s2) /\ (p_1 * p_2 = y) ==> x = y
       Note ?x1 x2. x1 IN s1 /\ x2 IN s2 /\ (x = x1 * x2)   by subset_cross_element_iff
        ==> y = x1 * x2                                     by implication
         or x = y
*)
val subset_cross_preimage_inj = store_thm(
  "subset_cross_preimage_inj",
  ``!g:'a group. !(s1 s2):'a -> bool.
     INJ (preimage (\(x, y). x * y) (s1 CROSS s2)) (s1 o s2) univ(:('a # 'a -> bool))``,
  rw[INJ_DEF] >>
  fs[preimage_def, pairTheory.FORALL_PROD, EXTENSION] >>
  metis_tac[subset_cross_element_iff]);

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in
                (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2)) *)
(* Proof:
   Let s = s1 CROSS s2, f = f = (\(x, y). x * y).
   Note s1 SUBSET G /\ s2 SUBSET G         by subgroup_carrier_subset
     so FINITE s1 /\ FINITE s2             by SUBSET_FINITE, FINITE G
     so FINITE s                           by FINITE_CROSS
    ==> FINITE (partition (feq f) s)       by FINITE_partition

   Claim: CARD (partition (feq f) s) = CARD (s1 o s2)
   Proof:   partition (feq f) s
          = IMAGE (preimage f s o f) s                         by feq_partition
          = IMAGE (preimage f s) (IMAGE f s)                   by IMAGE_COMPOSE
          = IMAGE (preimage f s) (s1 o s2)                     by subset_cross_alt
          Note INJ (preimage f s) (s1 o s2) univ(:('a reln))   by subset_cross_preimage_inj
           and FINITE (s1 o s2)                                by subset_cross_finite
           ==> CARD (partition (feq f) s) = CARD (s1 o s2)     by INJ_CARD_IMAGE

   Note !t. t IN partition (feq f) s ==>
            (CARD t = CARD (s1 INTER s2))  by subset_cross_partition_property

      CARD s1 * CARD s2
    = CARD (s1 CROSS s2)                               by CARD_CROSS
    = CARD s                                           by notation
    = SIGMA CARD (partition (feq f) s)                 by finite_card_by_feq_partition
    = CARD (s1 INTER s2) * CARD (partition (feq f) s)  by SIGMA_CARD_CONSTANT
    = CARD (s1 INTER s2) * CARD (s1 o s2)              by Claim
    = CARD (s1 o s2) * CARD (s1 INTER s2)              by MULT_COMM
    = CARD (h1 o h2).carrier * CARD (s1 INTER s2)      by subgroup_cross_property
*)
val subgroup_cross_card_eqn = store_thm(
  "subgroup_cross_card_eqn",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in
    (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2))``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `s1 SUBSET G /\ s2 SUBSET G` by rw[subgroup_carrier_subset, Abbr`s1`, Abbr`s2`] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[SUBSET_FINITE] >>
  `FINITE s` by rw[Abbr`s`] >>
  qabbrev_tac `f = (\(x:'a, y:'a). x * y)` >>
  `CARD (partition (feq f) s) = CARD (s1 o s2)` by
  (`partition (feq f) s = IMAGE (preimage f s) (IMAGE f s)` by rw[feq_partition, IMAGE_COMPOSE] >>
  `_ = IMAGE (preimage f s) (s1 o s2)` by rw[subset_cross_alt, Abbr`s`] >>
  metis_tac[subset_cross_finite, subset_cross_preimage_inj, INJ_CARD_IMAGE]) >>
  `FINITE (partition (feq f) s)` by rw[FINITE_partition] >>
  `CARD s1 * CARD s2 = CARD (s1 CROSS s2)` by rw[CARD_CROSS] >>
  `_ = SIGMA CARD (partition (feq f) s)` by rw[finite_card_by_feq_partition, Abbr`s`] >>
  `_ = CARD (s1 INTER s2) * CARD (s1 o s2)` by metis_tac[SIGMA_CARD_CONSTANT, subset_cross_partition_property] >>
  rw[subgroup_cross_property, Abbr`s1`, Abbr`s2`]);

(* Another proof of the same theorem *)

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in
            (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2)) *)
(* Proof:
   Let s = s1 CROSS s2.
   Then s1 SUBSET G /\ s2 SUBSET G     by subgroup_carrier_subset
    ==> FINITE s1 /\ FINITE s2         by SUBSET_FINITE, FINITE G
   Thus FINITE s                       by FINITE_CROSS
    and FINITE (s1 o s2)               by subset_cross_finite

   Let f = (\(x:'a, y:'a). x * y),
   Note !z. z IN (s1 o s2) ==>
        ((CARD o t) z = CARD (s1 INTER s2))            by subset_cross_element_preimage_card, [1]

      CARD s1 * CARD s2
    = CARD s                                           by CARD_CROSS
    = SIGMA CARD (IMAGE (preimage f s o f) s)          by finite_card_by_image_preimage, FINITE s
    = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))    by IMAGE_COMPOSE
    = SIGMA CARD (IMAGE (preimage f s) (s1 o s2))      by subset_cross_alt
    = SIGMA (CARD o preimage f s) (s1 o s2)            by SUM_IMAGE_INJ_o, subset_cross_preimage_inj, FINITE (s1 o s2)
    = SIGMA (\z. CARD (s1 INTER s2)) (s1 o s2)         by SUM_IMAGE_CONG, [1]
    = CARD (s1 INTER s2) * CARD (s1 o s2)              by SIGMA_CONSTANT
    = CARD (s1 o s2) * CARD (s1 INTER s2)              by MULT_COMM
    = CARD (h1 o h2).carrier * CARD (s1 INTER s2)      by subgroup_cross_property
*)
Theorem subgroup_cross_card_eqn[allow_rebind]:
  !(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in
    (CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `s = s1 CROSS s2` >>
  `FINITE s1 /\ FINITE s2` by metis_tac[subgroup_carrier_subset, SUBSET_FINITE] >>
  `FINITE s` by rw[Abbr`s`] >>
  `FINITE (s1 o s2)` by rw[subset_cross_finite] >>
  qabbrev_tac `f = (\(x:'a, y:'a). x * y)` >>
  qabbrev_tac `t = preimage f s` >>
  (`!z. z IN (s1 o s2) ==> ((CARD o t) z = CARD (s1 INTER s2))` by (rw[] >> metis_tac[subset_cross_element_preimage_card])) >>
  `CARD s1 * CARD s2 = CARD s` by rw[CARD_CROSS, Abbr`s`] >>
  `_ = SIGMA CARD (IMAGE (t o f) s)` by rw[finite_card_by_image_preimage, Abbr`t`] >>
  `_ = SIGMA CARD (IMAGE t (IMAGE f s))` by rw[IMAGE_COMPOSE] >>
  `_ = SIGMA CARD (IMAGE t (s1 o s2))` by rw[subset_cross_alt] >>
  `_ = SIGMA (CARD o t) (s1 o s2)` by metis_tac[SUM_IMAGE_INJ_o, subset_cross_preimage_inj] >>
  `_ = SIGMA (\z. CARD (s1 INTER s2)) (s1 o s2)` by rw[SUM_IMAGE_CONG] >>
  `_ = CARD (s1 INTER s2) * CARD (s1 o s2)` by rw[SIGMA_CONSTANT] >>
  rw[subgroup_cross_property]
QED

(* Theorem: h1 <= g /\ h2 <= g /\ FINITE G ==>
            let (s1 = h1.carrier) in let (s2 = h2.carrier) in
                (CARD (h1 o h2).carrier = ((CARD s1) * (CARD s2)) DIV (CARD (s1 INTER s2))) *)
(* Proof:
   Note Group h1 /\ Group h2        by subgroup_property
    and s1 SUBSET G /\ s2 SUBSET G  by subgroup_carrier_subset
    ==> FINITE s1 /\ FINITE s2      by SUBSET_FINITE
   Note #e IN s1 /\ #e IN s2        by subgroup_id, group_id_element
   Thus #e IN s1 INTER s2           by IN_INTER
    and FINITE (s1 INTER s2)        by FINITE_INTER
    ==> s1 INTER s2 <> {}           by MEMBER_NOT_EMPTY
     or CARD (s1 INTER s2) <> 0     by CARD_EQ_0
     or 0 < CARD (s1 INTER s2)      by NOT_ZERO_LT_ZERO
     By subgroup_cross_card_eqn,
        CARD (h1 o h2).carrier * CARD (s1 INTER s2) = (CARD s1) * (CARD s2)
    Thus the result follows         by DIV_SOLVE, 0 < CARD (s1 INTER s2)
*)
val subgroup_cross_card = store_thm(
  "subgroup_cross_card",
  ``!(g h1 h2):'a group. h1 <= g /\ h2 <= g /\ FINITE G ==>
   let (s1 = h1.carrier) in let (s2 = h2.carrier) in
       (CARD (h1 o h2).carrier = ((CARD s1) * (CARD s2)) DIV (CARD (s1 INTER s2)))``,
  rw_tac std_ss[] >>
  `Group h1 /\ Group h2` by metis_tac[subgroup_property] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[subgroup_carrier_subset, SUBSET_FINITE] >>
  `#e IN s1 /\ #e IN s2` by metis_tac[subgroup_id, group_id_element] >>
  `#e IN s1 INTER s2` by rw[] >>
  `FINITE (s1 INTER s2)` by rw[] >>
  `CARD (s1 INTER s2) <> 0` by metis_tac[CARD_EQ_0, MEMBER_NOT_EMPTY] >>
  metis_tac[subgroup_cross_card_eqn, DIV_SOLVE, NOT_ZERO_LT_ZERO]);

(* Another milestone theorem for me! *)
(* This is just Lemma X.2 in Appendix of "Finite Group Theory" by Irving Martin Isaacs. *)

(* ------------------------------------------------------------------------- *)
(* Finite Group Generators                                                   *)
(* ------------------------------------------------------------------------- *)

(*
I thought that, given a IN G /\ b IN G, if a <> b, then (Gen a) INTER (Gen b) = {#e}.
However, a proof of this turns out to be elusive.
This comes down to showing:   a ** n = b ** m  is impossible for n < ord a, m < ord b.
But even for the case n = m, a = b is hard to conclude.
Eventually I realize that, (gen (a * a)) is a subgroup of (gen a), and a * a <> a!.
This gives (Gen (a * a)) SUBSET (Gen a), so (Gen (a * a)) INTER (Gen a) = (Gen (a * a)) <> {#e}.
Thus (Gen a) INTER (Gen b) = {#e} is a condition in elements a, b, called these independence.
*)

(* Overload the notion of independent group elements *)
val _ = overload_on("independent",
        ``\(g:'a group) a b. (Gen a) INTER (Gen b) = {#e}``);

(* Theorem: independent g a b = independent g b a *)
(* Proof:
       independent g a b
   <=> (Gen a) INTER (Gen b) = {#e}     by notation
   <=> (Gen b) INTER (Gen a) = {#e}     by INTER_COMM
   <=> independent g b a                by notation
*)
val independent_sym = store_thm(
  "independent_sym",
  ``!g:'a group. !a b. independent g a b = independent g b a``,
  rw[INTER_COMM]);

(* Theorem: Group g ==>
            !a b. a IN G /\ b IN G /\ independent g a b ==> ((gen a = gen b) <=> (a = b)) *)
(* Proof:
   If part: gen a = gen b ==> a = b
      Note Gen a = Gen b                  by Generated_def, monoid_component_equality
       and a IN (Gen a) /\ b IN (Gen b)   by generated_gen_element, Group g
      Note (Gen a) INTER (Gen b) = {#e}   by notation
       ==> a IN {#e} /\ b IN {#e}         by IN_INTER
        or a = #e /\ b = #e               by IN_SING
      Thus a = b.

   Only-if part: a = b ==> gen a = gen b, true trivially.
*)
val independent_generated_eq = store_thm(
  "independent_generated_eq",
  ``!g:'a group. Group g ==>
   !a b. a IN G /\ b IN G /\ independent g a b ==> ((gen a = gen b) <=> (a = b))``,
  rw[EQ_IMP_THM] >>
  `Gen a = Gen b` by rw[Generated_def, monoid_component_equality] >>
  metis_tac[generated_gen_element, IN_INTER, IN_SING]);

(* Theorem: FiniteGroup g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                (CARD ((gen a) o (gen b)).carrier = (ord a) * (ord b)) *)
(* Proof:
   Note (gen a) <= g /\ (gen b) <= g     by generated_subgroup
    and CARD (Gen a) = ord a             by generated_group_card, group_order_pos
    and CARD (Gen b) = ord b             by generated_group_card, group_order_pos
    Now (Gen a) INTER (Gen b) = {#e}     by independent a b
    and CARD {#e} = 1                    by CARD_SING

        CARD ((gen a) o (gen b)).carrier
      = ((CARD (Gen a)) * (CARD (Gen b))) DIV (CARD ((Gen a) INTER (Gen b)))   by subgroup_cross_card
      = ((ord a) * (ord b)) DIV 1        by above
      = (ord a) * (ord b)                by DIV_1
*)
val independent_generator_2_card = store_thm(
  "independent_generator_2_card",
  ``!g:'a group. FiniteGroup g ==> !a b. a IN G /\ b IN G /\ independent g a b ==>
                (CARD ((gen a) o (gen b)).carrier = (ord a) * (ord b))``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(gen a) <= g /\ (gen b) <= g` by rw[generated_subgroup] >>
  `CARD {#e} = 1` by rw[] >>
  metis_tac[subgroup_cross_card, generated_group_card, group_order_pos, DIV_1]);

(* Define the set of all subgroups of a group. *)
val all_subgroups_def = Define`
    all_subgroups (g:'a group) = {h | h <= g}
`;

(* Theorem: h IN all_subgroups g <=> h <= g *)
(* Proof: by all_subgroups_def *)
val all_subgroups_element = store_thm(
  "all_subgroups_element",
  ``!g:'a group. !h. h IN all_subgroups g <=> h <= g``,
  rw[all_subgroups_def]);

(* Theorem: Group g ==> (IMAGE (\h:'a group. H) (all_subgroups g)) SUBSET (POW G) *)
(* Proof:
   Let s IN IMAGE (\h:'a group. H) (all_subgroups g)
   Then ?h. h IN (all_subgroups g) /\ (H = s)   by IN_IMAGE
     or ?h. h <= g  /\ (H = s)                  by all_subgroups_element
     or ?h. h <= g  /\ (H = s) /\ (H SUBSET G)  by subgroup_carrier_subset
     or s IN (POW G)                            by IN_POW
   The result follows                           by SUBSET_DEF
*)
val all_subgroups_subset = store_thm(
  "all_subgroups_subset",
  ``!g:'a group. Group g ==> (IMAGE (\h:'a group. H) (all_subgroups g)) SUBSET (POW G)``,
  rw[all_subgroups_element, SUBSET_DEF, IN_POW] >>
  metis_tac[subgroup_carrier_subset, SUBSET_DEF]);

(* Theorem: Group g ==> (gen #e) IN (all_subgroups g) *)
(* Proof:
   Note #e IN G                        by group_id_element, Group g
    and (gen #e) <= g                  by generated_id_subgroup, Group g
    ==> (gen #e) IN (all_subgroups g)  by all_subgroups_element
*)
val all_subgroups_has_gen_id = store_thm(
  "all_subgroups_has_gen_id",
  ``!g:'a group. Group g ==> (gen #e) IN (all_subgroups g)``,
  rw[generated_id_subgroup, all_subgroups_element]);

(* Theorem: FiniteGroup g ==> FINITE (all_subgroups g) *)
(* Proof:
   Note Group g /\ FINITE G      by FiniteGroup_def
   Let f = \h:'a group. H, s = all_subgroups g
   Then (IMAGE f s) SUBSET (POW G)     by all_subgroups_subset, Group g
    and FINITE (POW G)                 by FINITE_POW, FINITE G
    ==> FINITE (IMAGE f s)             by SUBSET_FINITE
   Claim: INJ f s (IMAGE f s)
   Proof: By INJ_DEF, this is to show:
          !h1 h2. h1 IN s /\ h2 IN s /\ (h1.carrier = h2.carrier) ==> h1 = h2.
          or      h1 <= g /\ h2 <= g /\ (h1.carrier = h2.carrier) ==> h1 = h2   by all_subgroups_element
          This is true                 by subgroup_eq

   With INJ f s (IMAGE f s)            by Claim
    and FINITE (IMAGE f s)             by above
    ==> FINITE s                       by FINITE_INJ
*)
val all_subgroups_finite = store_thm(
  "all_subgroups_finite",
  ``!g:'a group. FiniteGroup g ==> FINITE (all_subgroups g)``,
  rw[FiniteGroup_def] >>
  qabbrev_tac `f = \h:'a group. H` >>
  qabbrev_tac `s = all_subgroups g` >>
  `(IMAGE f s) SUBSET (POW G)` by rw[all_subgroups_subset, Abbr`f`, Abbr`s`] >>
  `FINITE (POW G)` by rw[FINITE_POW] >>
  `FINITE (IMAGE f s)` by metis_tac[SUBSET_FINITE] >>
  (`INJ f s (IMAGE f s)` by (rw[INJ_DEF, all_subgroups_element, Abbr`f`, Abbr`s`] >> metis_tac[subgroup_eq])) >>
  metis_tac[FINITE_INJ]);

(* Theorem: FiniteGroup g ==> !s. s SUBSET G ==> (IMAGE gen s) SUBSET all_subgroups g *)
(* Proof:
   Let h IN (IMAGE gen s)
   Then ?x. x IN s /\ (h = gen x)   by IN_IMAGE
     or ?x. x IN G /\ (h = gen x)   by SUBSET_DEF, s SUBSET G
     or h <= g                      by generated_subgroup, FiniteGroup g
   Thus h IN all_subgroups g        by all_subgroups_element
   The result follows               by SUBSET_DEF
*)
val generated_image_subset_all_subgroups = store_thm(
  "generated_image_subset_all_subgroups",
  ``!g:'a group. FiniteGroup g ==> !s. s SUBSET G ==> (IMAGE gen s) SUBSET all_subgroups g``,
  metis_tac[generated_subgroup, SUBSET_DEF, all_subgroups_element, IN_IMAGE]);

(* Theorem: Group g ==> !s. s SUBSET G ==> (IMAGE Gen s) SUBSET (POW G) *)
(* Proof:
   Let z IN (IMAGE Gen s)
   Then ?x. x IN s /\ (z = Gen x)   by IN_IMAGE
     or ?x. x IN G /\ (z = Gen x)   by SUBSET_DEF, s SUBSET G
     or z SUBSET G                  by generated_subset, FiniteGroup g
   Thus z IN POW G                  by IN_POW
   The result follows               by SUBSET_DEF
*)
val generated_image_subset_power_set = store_thm(
  "generated_image_subset_power_set",
  ``!g:'a group. Group g ==> !s. s SUBSET G ==> (IMAGE Gen s) SUBSET (POW G)``,
  rw[IN_POW, SUBSET_DEF] >>
  metis_tac[generated_subset, SUBSET_DEF]);

(* Theorem: AbelianGroup g ==> closure_comm_assoc_fun (subset_cross g) (POW G) *)
(* Proof:
   Note Group g              by AbelianGroup_def
   By closure_comm_assoc_fun_def, IN_POW, this is to show:
   (1) x SUBSET G /\ y SUBSET G ==> x o y SUBSET G
       This is true          by subset_cross_subset, Group g
   (2) x SUBSET G /\ y SUBSET G /\ z SUBSET G ==> x o (y o z) = y o (x o z)
         x o (y o z)
       = (x o y) o z         by subset_cross_assoc, Group g
       = (y o x) o z         by subset_cross_comm, AbelianGroup g
       = y o (x o z)         by subset_cross_assoc, Group g
*)
val subset_cross_closure_comm_assoc_fun = store_thm(
  "subset_cross_closure_comm_assoc_fun",
  ``!g:'a group. AbelianGroup g ==> closure_comm_assoc_fun (subset_cross g) (POW G)``,
  rpt strip_tac >>
  `Group g` by metis_tac[AbelianGroup_def] >>
  rw[closure_comm_assoc_fun_def, IN_POW] >-
  rw[subset_cross_subset] >>
  `x o (y o z) = (x o y) o z` by rw[subset_cross_assoc] >>
  `_ = (y o x) o z` by rw[subset_cross_comm] >>
  rw[subset_cross_assoc]);

(* Theorem: AbelianGroup g ==> closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g) *)
(* Proof:
   Note Group g              by AbelianGroup_def
   By closure_comm_assoc_fun_def, all_subgroups_element, this is to show:
   (1) x <= g /\ y <= g ==> x o y <= g
       This is true          by abelian_subgroup_cross_subgroup, AbelianGroup g
   (2) x <= g /\ y <= g /\ z <= g ==> x o (y o z) = y o (x o z)
         x o (y o z)
       = (x o y) o z         by subgroup_cross_assoc
       = (y o x) o z         by subgroup_cross_comm, AbelianGroup g
       = y o (x o z)         by subgroup_cross_assoc
*)
val subgroup_cross_closure_comm_assoc_fun = store_thm(
  "subgroup_cross_closure_comm_assoc_fun",
  ``!g:'a group. AbelianGroup g ==> closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g)``,
  rpt strip_tac >>
  `Group g` by metis_tac[AbelianGroup_def] >>
  rw[closure_comm_assoc_fun_def, all_subgroups_element] >-
  rw[abelian_subgroup_cross_subgroup] >>
  `x o (y o z) = (x o y) o z` by rw[subgroup_cross_assoc] >>
  `_ = (y o x) o z` by rw[subgroup_cross_comm] >>
  rw[subgroup_cross_assoc]);

(* ------------------------------------------------------------------------- *)
(* Big Cross of Subsets.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define big cross product of subsets. *)
val subset_big_cross_def = Define`
    subset_big_cross (g:'a group) (B:('a -> bool) -> bool) = ITSET (subset_cross g) B {#e}
`;
(* overload big cross product of subsets. *)
val _ = overload_on("ssbcross", ``subset_big_cross (g:'a group)``);

(*
> subset_big_cross_def;
val it = |- !g B. ssbcross B = ITSET $o B {#e}: thm
*)

(* Theorem: ssbcross {} = {#e} *)
(* Proof:
     ssbcross {}
   = ITSET $o {} {#e}    by subset_big_cross_def
   = {#e}                by ITSET_EMPTY
*)
val subset_big_cross_empty = store_thm(
  "subset_big_cross_empty",
  ``!g:'a group. ssbcross {} = {#e}``,
  rw[subset_big_cross_def, ITSET_EMPTY]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
            !s. s SUBSET G ==> (ssbcross (s INSERT B) = s o ssbcross (B DELETE s)) *)
(* Proof:
   Note AbelianGroup g /\ FINITE G      by FiniteAbelianGroup_def
    ==> Group g                         by AbelianGroup_def
   Note closure_comm_assoc_fun (subset_cross g) (POW G)
                                        by subset_cross_closure_comm_assoc_fun
    Now FINITE (POW G)                  by FINITE_POW
     so FINITE B                        by SUBSET_FINITE
   Also {#e} SUBSET G                   by group_id_element, SUBSET_DEF
     so {#e} IN (POW G)                 by IN_POW
    and s IN (POW G)                    by IN_POW, s SUBSET G

     (ssbcross (s INSERT B)
   = ITSET $o (s INSERT B) {#e}         by subset_big_cross_def
   = s o ITSET $o (B DELETE s) {#e}     by SUBSET_COMMUTING_ITSET_RECURSES
   = s o ssbcross (B DELETE s))         by subset_big_cross_def
*)
val subset_big_cross_thm = store_thm(
  "subset_big_cross_thm",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
   !s. s SUBSET G ==> (ssbcross (s INSERT B) = s o ssbcross (B DELETE s))``,
  rw[FiniteAbelianGroup_def] >>
  `Group g` by metis_tac[AbelianGroup_def] >>
  `closure_comm_assoc_fun (subset_cross g) (POW G)` by rw[subset_cross_closure_comm_assoc_fun] >>
  `FINITE B` by metis_tac[FINITE_POW, SUBSET_FINITE] >>
  `s IN (POW G)` by rw[IN_POW] >>
  `{#e} IN (POW G)` by rw[IN_POW] >>
  metis_tac[subset_big_cross_def, SUBSET_COMMUTING_ITSET_RECURSES]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
            !s. s SUBSET G /\ s NOTIN B ==> (ssbcross (s INSERT B) = s o ssbcross B) *)
(* Proof: by subset_big_cross_thm, DELETE_NON_ELEMENT *)
val subset_big_cross_insert = store_thm(
  "subset_big_cross_insert",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (POW G) ==>
   !s. s SUBSET G /\ s NOTIN B ==> (ssbcross (s INSERT B) = s o ssbcross B)``,
  rw[subset_big_cross_thm, DELETE_NON_ELEMENT]);

(* ------------------------------------------------------------------------- *)
(* Big Cross of Subgroups.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define big cross product of subgroups. *)
val subgroup_big_cross_def = Define`
    subgroup_big_cross (g:'a group) (B:('a group) -> bool) = ITSET (subgroup_cross g) B (gen #e)
`;
(* overload big cross product of subgroups. *)
val _ = overload_on("sgbcross", ``subgroup_big_cross (g:'a group)``);

(*
> subgroup_big_cross_def;
val it = |- !g B. sgbcross B = ITSET $o B (gen #e): thm
*)

(* Theorem: sgbcross {} = gen #e *)
(* Proof:
     sgbcross {}
   = ITSET $o {} (gen #e)    by subgroup_big_cross_def
   = gen #e                  by ITSET_EMPTY
*)
val subgroup_big_cross_empty = store_thm(
  "subgroup_big_cross_empty",
  ``!g:'a group. sgbcross {} = gen #e``,
  rw[subgroup_big_cross_def, ITSET_EMPTY]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
            !h. h IN (all_subgroups g) ==> (sgbcross (h INSERT B) = h o sgbcross (B DELETE h)) *)
(* Proof:
   Note AbelianGroup g /\ FINITE G      by FiniteAbelianGroup_def
    ==> Group g                         by AbelianGroup_def
    and FiniteGroup g                   by FiniteGroup_def
   Note closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g)
                                        by subgroup_cross_closure_comm_assoc_fun
    Now FINITE (all_subgroups g)        by all_subgroups_finite
     so FINITE B                        by SUBSET_FINITE
    and (gen #e) IN (all_subgroups g)   by all_subgroups_has_gen_id

     (sgbcross (h INSERT B)
   = ITSET $o (h INSERT B) (gen #e)     by subgroup_big_cross_def
   = h o ITSET $o (B DELETE h) (gen #e) by SUBSET_COMMUTING_ITSET_RECURSES
   = h o sgbcross (B DELETE h))         by subgroup_big_cross_def
*)
val subgroup_big_cross_thm = store_thm(
  "subgroup_big_cross_thm",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
   !h. h IN (all_subgroups g) ==> (sgbcross (h INSERT B) = h o sgbcross (B DELETE h))``,
  rw[FiniteAbelianGroup_def] >>
  `Group g /\ FiniteGroup g` by metis_tac[AbelianGroup_def, FiniteGroup_def] >>
  `closure_comm_assoc_fun (subgroup_cross g) (all_subgroups g)`
     by rw[subgroup_cross_closure_comm_assoc_fun] >>
  `FINITE B` by metis_tac[all_subgroups_finite, SUBSET_FINITE] >>
  `(gen #e) IN (all_subgroups g)` by rw[all_subgroups_has_gen_id] >>
  metis_tac[subgroup_big_cross_def, SUBSET_COMMUTING_ITSET_RECURSES]);

(* Theorem: FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
            !h. h IN (all_subgroups g) /\ h NOTIN B ==> (sgbcross (h INSERT B) = h o sgbcross B) *)
(* Proof: by subgroup_big_cross_thm, DELETE_NON_ELEMENT *)
val subgroup_big_cross_insert = store_thm(
  "subgroup_big_cross_insert",
  ``!g:'a group. FiniteAbelianGroup g ==> !B. B SUBSET (all_subgroups g) ==>
   !h. h IN (all_subgroups g) /\ h NOTIN B ==> (sgbcross (h INSERT B) = h o sgbcross B)``,
  rw[subgroup_big_cross_thm, DELETE_NON_ELEMENT]);

(*

Group Instances
===============
The important ones:

 Zn -- Addition Modulo n, n > 0.
Z*p -- Multiplication Modulo p, p a prime.
E*n -- Multiplication Modulo n, of order phi(n).

*)
(* ------------------------------------------------------------------------- *)
(* Group Instances Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Group Data type:
   The generic symbol for group data is g.
   g.carrier = Carrier set of group
   g.op      = Binary operation of group
   g.id      = Identity element of group
   g.inv     = Inverse operation of group (as monoid_inv g)
*)
(* Overloading (# are temporary):
   Z n       = Zadd n
   Z* n      = Zstar n
*)
(* Definitions and Theorems (# are exported, ! are in computeLib):

   The Group Zn = Addition Modulo n (n > 0):
   Zadd_def      |- !n. Z n = <|carrier := count n; id := 0; op := (\i j. (i + j) MOD n)|>
   Zadd_element  |- !n x. x IN (Z n).carrier <=> x < n
   Zadd_property |- !n. (!x. x IN (Z n).carrier <=> x < n) /\ ((Z n).id = 0) /\
                      (!x y. (Z n).op x y = (x + y) MOD n) /\
                      FINITE (Z n).carrier /\ (CARD (Z n).carrier = n)
   Zadd_carrier  |- !n. (Z n).carrier = count n
   Zadd_carrier_alt  |- !n. (Z n).carrier = {i | i < n}
   Zadd_id       |- !n. (Z n).id = 0
   Zadd_finite   |- !n. FINITE (Z n).carrier
   Zadd_card     |- !n. CARD (Z n).carrier = n
   Zadd_group    |- !n. 0 < n ==> Group (Z n)
   Zadd_finite_group          |- !n. 0 < n ==> FiniteGroup (Z n)
   Zadd_finite_abelian_group  |- !n. 0 < n ==> FiniteAbelianGroup (Z n)
   Zadd_exp      |- !n. 0 < n ==> !x m. (Z n).exp x m = (x * m) MOD n
#! Zadd_eval     |- !n. ((Z n).carrier = count n) /\ (!x y. (Z n).op x y = (x + y) MOD n) /\ ((Z n).id = 0)
#  Zadd_inv      |- !n. 0 < n ==> !x. x < n ==> ((Z n).inv x = (n - x) MOD n)
!  Zadd_inv_compute |- !n x. (Z n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((Z n).inv x) bad_element

   The Group Z*p = Multiplication Modulo p (prime p):
   Zstar_def       |- !p. Z* p = <|carrier := residue p; id := 1; op := (\i j. (i * j) MOD p)|>
   Zstar_element   |- !p x. x IN (Z* p).carrier <=> 0 < x /\ x < p
   Zstar_property  |- !p. ((Z* p).carrier = residue p) /\ ((Z* p).id = 1) /\
                          (!x y. (Z* p).op x y = (x * y) MOD p) /\
                          FINITE (Z* p).carrier /\ (0 < p ==> (CARD (Z* p).carrier = p - 1))
   Zstar_carrier   |- !p. (Z* p).carrier = residue p
   Zstar_carrier_alt |- !p. (Z* p).carrier = {i | i <> 0 /\ i < p}
   Zstar_id        |- !p. (Z* p).id = 1
   Zstar_finite    |- !p. FINITE (Z* p).carrier
   Zstar_card      |- !p. 0 < p ==> (CARD (Z* p).carrier = p - 1)
   Zstar_group     |- !p. prime p ==> Group (Z* p)
   Zstar_finite_group         |- !p. prime p ==> FiniteGroup (Z* p)
   Zstar_finite_abelian_group |- !p. prime p ==> FiniteAbelianGroup (Z* p)
   Zstar_exp       |- !p a. prime p /\ a IN (Z* p).carrier ==> !n. (Z* p).exp a n = a ** n MOD p
!  Zstar_eval      |- !p. ((Z* p).carrier = residue p) /\
                          (!x y. (Z* p).op x y = (x * y) MOD p) /\ ((Z* p).id = 1)
!  Zstar_inv       |- !p. prime p ==> !x. 0 < x /\ x < p ==>
                     ((Z* p).inv x = (Z* p).exp x (order (Z* p) x - 1))
   Zstar_inv_compute |- !p x. (Z* p).inv x = if prime p /\ 0 < x /\ x < p
                                            then (Z* p).exp x (order (Z* p) x - 1)
                                            else FAIL ((Z* p).inv x) bad_element

   Euler's generalization of Modulo Multiplicative Group (any modulo n):
   Estar_def       |- !n. Estar n = <|carrier := Euler n; id := 1; op := (\i j. (i * j) MOD n)|>
   Estar_alt       |- !n. Estar n =
                            <|carrier := {i | 0 < i /\ i < n /\ coprime n i}; id := 1;
                                   op := (\i j. (i * j) MOD n)|>
!  Estar_eval      |- !n. (Estar n).carrier = Euler n /\
                          (!x y. (Estar n).op x y = (x * y) MOD n) /\ ((Estar n).id = 1)
   Estar_element   |- !n x. x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x
   Estar_property  |- !n. ((Estar n).carrier = Euler n) /\ ((Estar n).id = 1) /\
                          (!x y. (Estar n).op x y = (x * y) MOD n) /\
                          FINITE (Estar n).carrier /\ (CARD (Estar n).carrier = totient n)
   Estar_carrier   |- !n. (Estar n).carrier = Euler n
   Estar_carrier_alt |- !n. (Estar n).carrier = {i | 0 < i /\ i < n /\ coprime n i}
   Estar_id        |- !n. (Estar n).id = 1
   Estar_finite    |- !n. FINITE (Estar n).carrier
   Estar_card      |- !n. CARD (Estar n).carrier = totient n
   Estar_card_alt  |- !n. 1 < n ==> (CARD (Estar n).carrier = phi n)
   Estar_group         |- !n. 1 < n ==> Group (Estar n)
   Estar_finite_group  |- !n. 1 < n ==> FiniteGroup (Estar n)
   Estar_finite_abelian_group |- !n. 1 < n ==> FiniteAbelianGroup (Estar n)
   Estar_exp       |- !n a. 1 < n /\ a IN (Estar n).carrier ==> !k. (Estar n).exp a k = a ** k MOD n

   Euler-Fermat Theorem:
   Euler_Fermat_eqn     |- !n a. 1 < n /\ a < n /\ coprime n a ==> (a ** totient n MOD n = 1)
   Euler_Fermat_thm     |- !n a. 1 < n /\ coprime n a ==> (a ** totient n MOD n = 1)
   Euler_Fermat_alt     |- !n a. 1 < n /\ coprime a n ==> a ** totient n MOD n = 1
   Fermat_little_thm    |- !p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)
   Fermat_little_eqn    |- !p a. prime p ==> a ** p MOD p = a MOD p
   Estar_inv            |- !n a. 1 < n /\ a < n /\ coprime n a ==>
                                 (Estar n).inv a = a ** (totient n - 1) MOD n
!  Estar_inv_compute    |- !n a. (Estar n).inv a =
                                 if 1 < n /\ a < n /\ coprime n a
                                 then a ** (totient n - 1) MOD n
                                 else FAIL ((Estar n).inv a) bad_element

   The Trivial Group:
   trivial_group_def |- !e. trivial_group e = <|carrier := {e}; id := e; op := (\x y. e)|>
   trivial_group_carrier
                     |- !e. (trivial_group e).carrier = {e}
   trivial_group_id  |- !e. (trivial_group e).id = e
   trivial_group     |- !e. FiniteAbelianGroup (trivial_group e)

   The Function Cyclic Group:
   fn_cyclic_group_def  |- !e f. fn_cyclic_group e f =
         <|carrier := {x | ?n. FUNPOW f n e = x};
                id := e;
                op := (\x y. @z. !xi yi. (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==> (FUNPOW f (xi + yi) e = z))|>
   fn_cyclic_group_alt  |- !e f n. (?k. k <> 0 /\ (FUNPOW f k e = e)) /\
      (n = LEAST k. k <> 0 /\ (FUNPOW f k e = e)) ==>
         ((fn_cyclic_group e f).carrier = {FUNPOW f k e | k < n}) /\
         ((fn_cyclic_group e f).id = e) /\
         !i j. (fn_cyclic_group e f).op (FUNPOW f i e) (FUNPOW f j e) = FUNPOW f ((i + j) MOD n) e
   fn_cyclic_group_carrier              |- !e f. (fn_cyclic_group e f).carrier = { x | ?n. FUNPOW f n e = x }
   fn_cyclic_group_id                   |- !e f. (fn_cyclic_group e f).id = e
   fn_cyclic_group_group                |- !e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> Group (fn_cyclic_group e f)
   fn_cyclic_group_finite_abelian_group |- !e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteAbelianGroup (fn_cyclic_group e f)
   fn_cyclic_group_finite_group         |- !e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteGroup (fn_cyclic_group e f)

   The Group of Addition Modulo n:
   add_mod_def      |- !n. add_mod n = <|carrier := {i | i < n}; id := 0; op := (\i j. (i + j) MOD n)|>
   add_mod_element  |- !n x. x IN (add_mod n).carrier <=> x < n
   add_mod_property |- !n. (!x. x IN (add_mod n).carrier <=> x < n) /\
                           ((add_mod n).id = 0) /\
                           (!x y. (add_mod n).op x y = (x + y) MOD n) /\
                           FINITE (add_mod n).carrier /\ (CARD (add_mod n).carrier = n)
   add_mod_carrier  |- !n. (add_mod n).carrier = { i | i < n }
   add_mod_carrier_alt    |- !n. (add_mod n).carrier = count n
   add_mod_id       |- !n. (add_mod n).id = 0
   add_mod_finite   |- !n. FINITE (add_mod n).carrier
   add_mod_card     |- !n. CARD (add_mod n).carrier = n
   add_mod_group    |- !n. 0 < n ==> Group (add_mod n)
   add_mod_abelian_group  |- !n. 0 < n ==> AbelianGroup (add_mod n)
   add_mod_finite_group   |- !n. 0 < n ==> FiniteGroup (add_mod n)
   add_mod_finite_abelian_group |- !n. 0 < n ==> FiniteAbelianGroup (add_mod n)
   add_mod_exp            |- !n. 0 < n ==> !x m. (add_mod n).exp x m = (x * m) MOD n
#! add_mod_eval     |- !n. ((add_mod n).carrier = {i | i < n}) /\
                           (!x y. (add_mod n).op x y = (x + y) MOD n) /\ ((add_mod n).id = 0)
#  add_mod_inv      |- !n. 0 < n ==> !x. x < n ==> ((add_mod n).inv x = (n - x) MOD n)
!  add_mod_inv_compute |- !n x. (add_mod n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((add_mod n).inv x) bad_element

   The Group of Multiplication Modulo prime p:
   mult_mod_def     |- !p. mult_mod p = <|carrier := {i | i <> 0 /\ i < p}; id := 1; op := (\i j. (i * j) MOD p)|>
   mult_mod_element      |- !p x. x IN (mult_mod p).carrier <=> x <> 0 /\ x < p
   mult_mod_element_alt  |- !p x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p
   mult_mod_property     |- !p. (!x. x IN (mult_mod p).carrier ==> x <> 0) /\
                                (!x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p) /\
                                ((mult_mod p).id = 1) /\
                                (!x y. (mult_mod p).op x y = (x * y) MOD p) /\
                                FINITE (mult_mod p).carrier /\ (0 < p ==> (CARD (mult_mod p).carrier = p - 1))
   mult_mod_carrier |- !p. (mult_mod p).carrier = { i | i <> 0 /\ i < p }
   mult_mod_carrier_alt    |- !p. (mult_mod p).carrier = residue p
   mult_mod_id      |- !p. (mult_mod p).id = 1
   mult_mod_finite  |- !p. FINITE (mult_mod p).carrier
   mult_mod_card    |- !p. 0 < p ==> (CARD (mult_mod p).carrier = p - 1)
   mult_mod_group   |- !p. prime p ==> Group (mult_mod p)
   mult_mod_abelian_group  |- !p. prime p ==> AbelianGroup (mult_mod p)
   mult_mod_finite_group   |- !p. prime p ==> FiniteGroup (mult_mod p)
   mult_mod_finite_abelian_group  |- !p. prime p ==> FiniteAbelianGroup (mult_mod p)
   mult_mod_exp     |- !p a. prime p /\ a IN (mult_mod p).carrier ==> !n. (mult_mod p).exp a n = a ** n MOD p
#! mult_mod_eval    |- !p. ((mult_mod p).carrier = {i | i <> 0 /\ i < p}) /\
                           (!x y. (mult_mod p).op x y = (x * y) MOD p) /\ ((mult_mod p).id = 1)
#  mult_mod_inv     |- !p. prime p ==> !x. 0 < x /\ x < p ==>
                           ((mult_mod p).inv x = (mult_mod p).exp x (order (mult_mod p) x - 1))
!  mult_mod_inv_compute |- !p x. (mult_mod p).inv x = if prime p /\ 0 < x /\ x < p
                                                 then (mult_mod p).exp x (order (mult_mod p) x - 1)
                                                 else FAIL ((mult_mod p).inv x) bad_element

   ElGamal encryption and decryption -- purely group-theoretic:
   ElGamal_encrypt_def  |- !g y h m k. ElGamal_encrypt g y h m k = (y ** k,h ** k * m)
   ElGamal_decrypt_def  |- !g x a b. ElGamal_decrypt g x (a,b) = |/ (a ** x) * b
   ElGamal_correctness  |- !g. Group g ==> !(y::G) (h::G) (m::G) k x. (h = y ** x) ==>
                               (ElGamal_decrypt g x (ElGamal_encrypt g y h m k) = m)
*)
(* ------------------------------------------------------------------------- *)
(* The Group Zn = Addition Modulo n, for n > 0.                              *)
(* ------------------------------------------------------------------------- *)

(* Define (Zadd n) = Addition Modulo n Group *)
val Zadd_def = zDefine`
  Zadd n : num group =
    <| carrier := count n;
            id := 0;
       (*  inv := (\i. (n - i) MOD n);  -- so that inv 0 = 0 *)
            op := (\i j. (i + j) MOD n)
     |>
`;
(* Use of zDefine to avoid incorporating into computeLib, by default. *)
(* This is the same as add_mod below, using {i | i < n} as carrier. *)

(* Overload Zadd n *)
val _ = temp_overload_on("Z", ``Zadd``);

(*
- type_of ``Z n``;
> val it = ``:num group`` : hol_type
> EVAL ``(Z 7).op 5 6``;
val it = |- (Z 7).op 5 6 = (Z 7).op 5 6: thm

Here, we are putting a finer control on evaluation.
If we had use Define instead of zDefine, this would work.
However, because (Zadd n).inv is an add-on field, that would not work.
We define Zadd_eval and Zadd_inv below, and put them into computeLib.
*)

(* Theorem: Evaluation of Zadd for each record field. *)
(* Proof: by Zadd_def. *)
val Zadd_eval = store_thm(
  "Zadd_eval",
  ``!n. ((Z n).carrier = count n) /\
       (!x y. (Z n).op x y = (x + y) MOD n) /\
       ((Z n).id = 0)``,
  rw_tac std_ss[Zadd_def]);
(* This is later exported to computeLib, with Zadd_inv_compute. *)

(* Theorem: x IN (Z n).carrier <=> x < n *)
(* Proof: by definition, IN_COUNT. *)
val Zadd_element = store_thm(
  "Zadd_element",
  ``!n x. x IN (Z n).carrier <=> x < n``,
  rw[Zadd_def]); (* by IN_COUNT *)

(* Theorem: properties of Zn. *)
(* Proof: by definition. *)
val Zadd_property = store_thm(
  "Zadd_property",
  ``!n. (!x. x IN (Z n).carrier <=> x < n) /\
       ((Z n).id = 0) /\
       (!x y. (Z n).op x y = (x + y) MOD n) /\
       FINITE (Z n).carrier /\
       (CARD (Z n).carrier = n)``,
  rw_tac std_ss[Zadd_def, IN_COUNT, FINITE_COUNT, CARD_COUNT]);

(* Theorem: (Z n).carrier = count n *)
(* Proof: by Zadd_def. *)
Theorem Zadd_carrier:
  !n. (Z n).carrier = count n
Proof
  simp[Zadd_def]
QED

(* Theorem: (Z n).carrier = {i | i < n} *)
(* Proof: by Zadd_carrier. *)
Theorem Zadd_carrier_alt:
  !n. (Z n).carrier = {i | i < n}
Proof
  simp[Zadd_carrier, EXTENSION]
QED

(* Theorem: (Z n).id = 0 *)
(* Proof: by Zadd_def. *)
Theorem Zadd_id:
  !n. (Z n).id = 0
Proof
  simp[Zadd_def]
QED

(* Theorem: FINITE (Z n).carrier *)
(* Proof: by Zadd_property *)
val Zadd_finite = store_thm(
  "Zadd_finite",
  ``!n. FINITE (Z n).carrier``,
  rw[Zadd_property]);

(* Theorem: CARD (Z n).carrier = n *)
(* Proof: by Zadd_property *)
val Zadd_card = store_thm(
  "Zadd_card",
  ``!n. CARD (Z n).carrier = n``,
  rw[Zadd_property]);

(* Theorem: Zn is a group if n > 0. *)
(* Proof: by definitions:
   Associativity: ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n
      true by MOD_ADD_ASSOC.
   Inverse: ?y. y < n /\ ((y + x) MOD n = 0)
      If x = 0, let y = 0, true by ZERO_MOD.
      If x <> 0, let y = n - x, true by DIVMOD_ID.
*)
val Zadd_group = store_thm(
  "Zadd_group",
  ``!n. 0 < n ==> Group (Z n)``,
  rw_tac std_ss[group_def_alt, Zadd_property] >| [
    rw_tac std_ss[MOD_ADD_ASSOC],
    Cases_on `x = 0` >| [
      metis_tac[ZERO_MOD, ADD],
      `n - x < n /\ ((n - x) + x = n)` by decide_tac >>
      metis_tac[DIVMOD_ID]
    ]
  ]);

(* Theorem: Zn is a FiniteGroup if n > 0. *)
(* Proof: by Zadd_group and FINITE_Zadd_carrier. *)
val Zadd_finite_group = store_thm(
  "Zadd_finite_group",
  ``!n. 0 < n ==> FiniteGroup (Z n)``,
  rw_tac std_ss[FiniteGroup_def, Zadd_group, Zadd_property]);

(* Theorem: Zn is a finite Abelian group if n > 0. *)
(* Proof: by Zadd_finite_group and arithmetic. *)
val Zadd_finite_abelian_group = store_thm(
  "Zadd_finite_abelian_group",
  ``!n. 0 < n ==> FiniteAbelianGroup (Z n)``,
  rw_tac std_ss[FiniteAbelianGroup_def, AbelianGroup_def, Zadd_property] >-
  rw_tac std_ss[Zadd_group] >>
  rw_tac arith_ss [Zadd_def]);

(* Theorem: 0 < n ==> !x m. (Z n).exp x m = (x * m) MOD n *)
(* Proof:
   Note Group (Z n)        by Zadd_group
   By induction on m.
   Base case: (Z n).exp x 0 = (x * 0) MOD n
        (Z n).exp x 0
      = (Z n).id           by group_exp_0
      = 0                  by Zadd_property
      = (x * 0) MOD n      by MULT
   Step case: (Z n).exp x m = (x * m) MOD n ==>
              (Z n).exp x (SUC m) = (x * SUC m) MOD n
        (Z n).exp x (SUC m)
      = (Z n).op m (Z n).exp x m       by group_exp_SUC
      = (m + (Z n).exp x m) MOD n      by Zadd_property
      = (m + (x * m) MOD n) MOD n      by induction hypothesis
      = (m + x * m) MOD n              by MOD_PLUS, MOD_MOD
      = (x * SUC m) MOD n              by MULT_SUC
*)
val Zadd_exp = store_thm(
  "Zadd_exp",
  ``!n. 0 < n ==> !x m. (Z n).exp x m = (x * m) MOD n``,
  rpt strip_tac >>
  `Group (Z n)` by rw[Zadd_group] >>
  Induct_on `m` >-
  rw[group_exp_0, Zadd_property] >>
  rw_tac std_ss[group_exp_SUC, Zadd_property] >>
  metis_tac[MOD_PLUS, MOD_MOD, MULT_SUC]);

(* Theorem: (Z n).inv x = (n - x) MOD n *)
(* Proof: by MOD_ADD_INV and group_linv_unique. *)
val Zadd_inv = store_thm(
  "Zadd_inv",
  ``!n x. 0 < n /\ x < n ==> ((Z n).inv x = (n - x) MOD n)``,
  rpt strip_tac >>
  `x IN (Z n).carrier /\ (n - x) MOD n IN (Z n).carrier` by rw_tac std_ss[Zadd_property] >>
  `((n - x) MOD n + x) MOD n = 0` by rw_tac std_ss[MOD_ADD_INV] >>
  metis_tac[Zadd_group, group_linv_unique, Zadd_property]);

(* Due to zDefine before, now export the Define to computeLib. *)

(* export simple result *)
val _ = export_rewrites ["Zadd_eval", "Zadd_inv"];
(*
- SIMP_CONV (srw_ss()) [] ``(Z 5).op 3 4``;
> val it = |- (Z 5).op 3 4 = 2 : thm
- SIMP_CONV (srw_ss()) [] ``(Z 5).inv 3``;
> val it = |- (Z 5).inv 3 = 2 : thm
*)

(* Now put these to computeLib *)
val _ = computeLib.add_persistent_funs ["Zadd_eval"];
(*
- EVAL ``(Z 5).op 3 4``;
> val it = |- (Z 5).op 3 4 = 2 : thm
- EVAL ``(Z 5).op 6 8``;
> val it = |- (Z 5).op 6 8 = 4 : thm
*)
(* val _ = computeLib.add_persistent_funs ["Zadd_inv"]; -- cannot put a non-function. *)

(* Theorem: As function, (Z n).inv x = (n - x) MOD n *)
(* Proof: by Zadd_inv. *)
val Zadd_inv_compute = store_thm(
  "Zadd_inv_compute",
  ``!n x. (Z n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((Z n).inv x) bad_element``,
  rw_tac std_ss[Zadd_inv, combinTheory.FAIL_DEF]);

val _ = computeLib.add_persistent_funs ["Zadd_inv_compute"];
val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0);

(*
- EVAL ``(Z 5).inv 2``;
> val it = |- (Z 5).inv 2 = 3 : thm
- EVAL ``(Z 5).inv 3``;
> val it = |- (Z 5).inv 3 = 2 : thm
- EVAL ``(Z 5).inv 6``;
> val it = |- (Z 5).inv 6 = FAIL ((Z 5).inv 6) bad_element : thm
*)


(* ------------------------------------------------------------------------- *)
(* The Group Z*p = Multiplication Modulo p, for prime p.                     *)
(* ------------------------------------------------------------------------- *)

(* Define Multiplicative Modulo p Group *)
val Zstar_def = zDefine`
  Zstar p : num group =
   <| carrier := residue p;
           id := 1;
       (* inv := MOD_MULT_INV p; *)
           op := (\i j. (i * j) MOD p)
    |>`;
(* Use of zDefine to avoid incorporating into computeLib, by default. *)
(* This is the same as mult_mod below, using { i | i <> 0 /\ i < p } as carrier. *)

(* Overload Zstar n *)
val _ = temp_overload_on("Z*", ``Zstar``);

(*
- type_of ``Z* p``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: Evaluation of Zstar for each record field. *)
(* Proof: by Zstar_def. *)
val Zstar_eval = store_thm(
  "Zstar_eval",
  ``!p. ((Z* p).carrier = residue p) /\
       (!x y. (Z* p).op x y = (x * y) MOD p) /\
       ((Z* p).id = 1)``,
  rw_tac std_ss[Zstar_def]);
(* This is put to computeLib later, together with Zstar_inv_compute. *)

(* Theorem: x IN (Z* p).carrier ==> 0 < x /\ x < p *)
(* Proof: by definition. *)
val Zstar_element = store_thm(
  "Zstar_element",
  ``!p x. x IN (Z* p).carrier <=> 0 < x /\ x < p``,
  rw[Zstar_def, residue_def]);

(* Theorem: properties of Z* p. *)
(* Proof: by definition. *)
val Zstar_property = store_thm(
  "Zstar_property",
  ``!p. ((Z* p).carrier = residue p) /\
       ((Z* p).id = 1) /\
       (!x y. (Z* p).op x y = (x * y) MOD p) /\
       FINITE (Z* p).carrier /\
       (0 < p ==> (CARD (Z* p).carrier = p - 1))``,
  rw[Zstar_def, residue_finite, residue_card]);

(* Theorem: (Z* p).carrier = residue p *)
(* Proof: by Zstar_def. *)
Theorem Zstar_carrier:
  !p. (Z* p).carrier = residue p
Proof
  simp[Zstar_def]
QED

(* Theorem: (Z* p).carrier = {i | 0 < i /\ i < p} *)
(* Proof: by Zstar_carrier, residue_def. *)
Theorem Zstar_carrier_alt:
  !p. (Z* p).carrier = {i | 0 < i /\ i < p}
Proof
  simp[Zstar_carrier, residue_def, EXTENSION]
QED

(* Theorem: (Z* p).id = 1 *)
(* Proof: by Zstar_def. *)
Theorem Zstar_id:
  !p. (Z* p).id = 1
Proof
  simp[Zstar_def]
QED

(* Theorem: FINITE (Z* p).carrier *)
(* Proof: by Zstar_property *)
val Zstar_finite = store_thm(
  "Zstar_finite",
  ``!p. FINITE (Z* p).carrier``,
  rw[Zstar_property]);

(* Theorem: 0 < p ==> (CARD (Z* p).carrier = p - 1) *)
(* Proof: by Zstar_property *)
val Zstar_card = store_thm(
  "Zstar_card",
  ``!p. 0 < p ==> (CARD (Z* p).carrier = p - 1)``,
  rw[Zstar_property]);

(* Theorem: Z* p is a Group for prime p. *)
(* Proof: check definitions.
   Closure: 0 < (x * y) MOD p < p
      true by EUCLID_LEMMA and MOD_LESS.
   Associativity: ((x * y) MOD p * z) MOD p = (x * (y * z) MOD p) MOD p
      true by MOD_MULT_ASSOC.
   Inverse: ?y. (0 < y /\ y < p) /\ ((y * x) MOD p = 1)
      true by MOD_MULT_INV_DEF.
*)
val Zstar_group = store_thm(
  "Zstar_group",
  ``!p. prime p ==> Group (Z* p)``,
  rw_tac std_ss[group_def_alt, Zstar_property, residue_def, GSPECIFICATION, ONE_LT_PRIME] >| [
    `x MOD p <> 0 /\ y MOD p <> 0` by rw_tac arith_ss[] >>
    `(x * y) MOD p <> 0` by metis_tac[EUCLID_LEMMA] >>
    decide_tac,
    rw_tac arith_ss[],
    rw_tac std_ss[PRIME_POS, MOD_MULT_ASSOC],
    metis_tac[MOD_MULT_INV_DEF]
  ]);

(* Theorem: If p is prime, Z*p is a Finite Group. *)
(* Proof: by Zstar_group, FINITE (Z* p).carrier *)
val Zstar_finite_group = store_thm(
  "Zstar_finite_group",
  ``!p. prime p ==> FiniteGroup (Z* p)``,
  rw[FiniteGroup_def, Zstar_group, Zstar_property]);

(* Theorem: If p is prime, Z*p is a Finite Abelian Group. *)
(* Proof:
   Verify all finite Abelian group axioms for Z*p.
*)
val Zstar_finite_abelian_group = store_thm(
  "Zstar_finite_abelian_group",
  ``!p. prime p ==> FiniteAbelianGroup (Z* p)``,
  rw_tac std_ss[FiniteAbelianGroup_def, AbelianGroup_def, Zstar_property, residue_def, GSPECIFICATION] >-
  rw_tac std_ss[Zstar_group] >>
  rw_tac arith_ss[]);

(* Theorem: (Z* p).exp a n = a ** n MOD p *)
(* Proof:
   By induction on n.
   Base case: (Z* p).exp a 0 = a ** 0 MOD p
      (Z* p).exp a 0
    = (Z* p).id                   by group_exp_0
    = 1                           by Zstar_def
    = 1 MOD 1                     by DIVMOD_ID, 0 < 1
    = a ** 0 MOD p                by EXP
   Step case:  (Z* p).exp a n = a ** n MOD p ==> (Z* p).exp a (SUC n) = a ** SUC n MOD p
      (Z* p).exp a (SUC n)
    = a * ((Z* p).exp a n)     by group_exp_SUC
    = a * ((a ** n) MOD p)        by inductive hypothesis
    = (a MOD p) * ((a**n) MOD p)  by a < p, MOD_LESS
    = (a*(a**n)) MOD p            by MOD_TIMES2
    = (a**(SUC n) MOD p           by EXP
*)
val Zstar_exp = store_thm(
  "Zstar_exp",
  ``!p a. prime p /\ a IN (Z* p).carrier ==> !n. (Z* p).exp a n = (a ** n) MOD p``,
  rw[Zstar_def, monoid_exp_def, residue_def] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  Induct_on `n` >-
  rw_tac std_ss[FUNPOW_0, EXP, ONE_MOD] >>
  rw_tac std_ss[FUNPOW_SUC, EXP] >>
  `a MOD p = a` by rw_tac arith_ss[] >>
  metis_tac[MOD_TIMES2]);

(*
- group_order_property |> ISPEC ``(Z* p)``;
> val it = |- FiniteGroup (Z* p) ==> !x. x IN (Z* p).carrier ==>
         0 < order (Z* p) x /\  ((Z* p).exp x (order (Z* p) x) = (Z* p).id) : thm
- EVAL ``order (Z* 5) 1``;
> val it = |- order (Z* 5) 1 = 1 : thm
- EVAL ``order (Z* 5) 2``;
> val it = |- order (Z* 5) 2 = 4 : thm
- EVAL ``order (Z* 5) 3``;
> val it = |- order (Z* 5) 3 = 4 : thm
- EVAL ``order (Z* 5) 4``;
> val it = |- order (Z* 5) 4 = 2 : thm
*)

(* Theorem: (Z* p).inv x = x ** (order (Z* p) x - 1) *)
(* Proof: by group_order_property and group_rinv_unique. *)
val Zstar_inv = store_thm(
  "Zstar_inv",
  ``!p. prime p ==> !x. 0 < x /\ x < p ==> ((Z* p).inv x = (Z* p).exp x (order (Z* p) x - 1))``,
  rpt strip_tac >>
  `x IN residue p` by rw_tac std_ss[residue_def, GSPECIFICATION] >>
  `x IN (Z* p).carrier /\ ((Z* p).id = 1)` by rw_tac std_ss[Zstar_property] >>
  `Group (Z* p)` by rw_tac std_ss[Zstar_group] >>
  `FiniteGroup (Z* p)` by rw_tac std_ss[FiniteGroup_def, Zstar_property] >>
  `0 < order (Z* p) x /\ ((Z* p).exp x (order (Z* p) x) = 1)` by rw_tac std_ss[group_order_property] >>
  `SUC ((order (Z* p) x) - 1) = order (Z* p) x` by rw_tac arith_ss[] >>
  metis_tac[group_rinv_unique, group_exp_SUC, group_exp_element]);

(* val _ = computeLib.add_persistent_funs ["Zstar_inv"]; -- cannot put a non-function. *)

(* Theorem: As function, (Z* p).inv x = x ** (order (Z* p) x - 1) *)
(* Proof: by Zstar_inv. *)
val Zstar_inv_compute = store_thm(
  "Zstar_inv_compute",
  ``!p x. (Z* p).inv x = if prime p /\ 0 < x /\ x < p then (Z* p).exp x (order (Z* p) x - 1)
                           else FAIL ((Z* p).inv x) bad_element``,
  rw_tac std_ss[Zstar_inv, combinTheory.FAIL_DEF]);

(* Now put thse input computeLib for EVAL *)
val _ = computeLib.add_persistent_funs ["Zstar_eval"];
val _ = computeLib.add_persistent_funs ["Zstar_inv_compute"];
val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0);

(*
- EVAL ``(Z* 5).op 3 2``;
> val it = |- (Z* 5).op 3 2 = 1 : thm
- EVAL ``(Z* 5).id``;
> val it = |- (Z* 5).id = 1 : thm
- EVAL ``(Z* 5).inv 2``;
> val it = |- (Z* 5).inv 2 = if prime 5 then 3 else FAIL ((Z* 5).inv 2) bad_element : thm
- EVAL ``prime 5``;
> val it = |- prime 5 <=> prime 5 : thm
*)

(* Export these for SIMP_CONV *)
val _ = export_rewrites ["Zstar_eval", "Zstar_inv"];

(*
- SIMP_CONV (srw_ss()) [] ``(Z* 5).op 3 2``;
> val it = |- (Z* 5).op 3 2 = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(Z* 5).id``;
> val it = |- (Z* 5).id = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(Z* 5).inv 2``;
! Uncaught exception:
! UNCHANGED
*)

(* ------------------------------------------------------------------------- *)
(* Euler's generalization of Modulo Multiplicative Group for any modulo n.   *)
(* ------------------------------------------------------------------------- *)

(* Define Multiplicative Modulo n Group *)
val Estar_def = zDefine`
  Estar n : num group =
   <| carrier := Euler n;
           id := 1;
      (*  inv := GCD_MOD_MULT_INV n; *)
           op := (\i j. (i * j) MOD n)
    |>`;

(*
- type_of ``Estar n``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: Estar n =
       <|carrier := {i | 0 < i /\ i < n /\ coprime n i} ; id := 1; op := (\i j. (i * j) MOD n)|>*)
(* Proof: by Estar_def, Euler_def *)
val Estar_alt = store_thm(
  "Estar_alt",
  ``!n. Estar n =
       <|carrier := {i | 0 < i /\ i < n /\ coprime n i} ; id := 1; op := (\i j. (i * j) MOD n)|>``,
  rw[Estar_def, Euler_def]);

(* Theorem: Evaluation of Zstar for each record field. *)
(* Proof: by Etar_def. *)
val Estar_eval = store_thm(
  "Estar_eval[compute]",
  ``!n. ((Estar n).carrier = Euler n) /\
       (!x y. (Estar n).op x y = (x * y) MOD n) /\
       ((Estar n).id = 1)``,
  rw_tac std_ss[Estar_def]);
(* This is put to computeLib, later also Estar_inv_compute. *)

(* Theorem: x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x *)
(* Proof: by Estar_def, Euler_def *)
val Estar_element = store_thm(
  "Estar_element",
  ``!n x. x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x``,
  rw[Estar_def, Euler_def]);

(* Theorem: properties of (Estar n). *)
(* Proof: by definition. *)
val Estar_property = store_thm(
  "Estar_property",
  ``!n. ((Estar n).carrier = Euler n) /\
       ((Estar n).id = 1) /\
       (!x y. (Estar n).op x y = (x * y) MOD n) /\
       FINITE (Estar n).carrier /\
       (CARD (Estar n).carrier = totient n)``,
  rw_tac std_ss[Estar_def, totient_def] >>
  rw_tac std_ss[Euler_def] >>
  `{i | 0 < i /\ i < n /\ coprime n i} SUBSET count n` by rw[SUBSET_DEF] >>
  metis_tac[FINITE_COUNT, SUBSET_FINITE]);

(* Theorem: (Estar n).carrier = Euler n *)
(* Proof: by Estar_def. *)
Theorem Estar_carrier:
  !n. (Estar n).carrier = Euler n
Proof
  simp[Estar_def]
QED

(* Theorem: (Estar n).carrier = {i | 0 < i /\ i < n /\ coprime n i } *)
(* Proof: by Estar_carrier, Euler_def. *)
Theorem Estar_carrier_alt:
  !n. (Estar n).carrier = {i | 0 < i /\ i < n /\ coprime n i }
Proof
  simp[Estar_carrier, Euler_def, EXTENSION]
QED

(* Theorem: (Estar n).id = 1 *)
(* Proof: by Estar_def. *)
Theorem Estar_id:
  !n. (Estar n).id = 1
Proof
  simp[Estar_def]
QED

(* Theorem: FINITE (Estar n).carrier *)
(* Proof: by Estar_property *)
val Estar_finite = store_thm(
  "Estar_finite",
  ``!n. FINITE (Estar n).carrier``,
  rw[Estar_property]);

(* Theorem: CARD (Estar n).carrier = totient n *)
(* Proof: by Estar_property *)
val Estar_card = store_thm(
  "Estar_card",
  ``!n. CARD (Estar n).carrier = totient n``,
  rw[Estar_property]);

(* Theorem: CARD (Estar n).carrier = totient n *)
(* Proof: by Estar_card, phi_eq_totient *)
val Estar_card_alt = store_thm(
  "Estar_card_alt",
  ``!n. 1 < n ==> (CARD (Estar n).carrier = phi n)``,
  rw[Estar_card, phi_eq_totient]);

(* Theorem: Estar is a Group *)
(* Proof: check definitions.
   Closure: 1 < n /\ coprime n x /\ coprime n y ==> 0 < (x * y) MOD n < n
      true by MOD_NONZERO_WHEN_GCD_ONE, PRODUCT_WITH_GCD_ONE, MOD_LESS.
   Closure: 1 < n /\ coprime n x /\ coprime n y ==> coprime n ((x * y) MOD n
      true by MOD_WITH_GCD_ONE, PRODUCT_WITH_GCD_ONE.
   Associativity: ((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n
      true by MOD_MULT_ASSOC.
   Inverse: 1 < n /\ coprime n x ==> ?y. (0 < y /\ y < n /\ coprime n y) /\ ((y * x) MOD n = 1)
      true by GEN_MULT_INV_DEF.
*)
val Estar_group = store_thm(
  "Estar_group",
  ``!n. 1 < n ==> Group (Estar n)``,
  rw_tac std_ss[group_def_alt, Estar_property, Euler_def, GSPECIFICATION, GCD_1] >-
  rw_tac std_ss[MOD_NONZERO_WHEN_GCD_ONE, PRODUCT_WITH_GCD_ONE] >-
  rw_tac arith_ss[] >-
  rw_tac std_ss[MOD_WITH_GCD_ONE, PRODUCT_WITH_GCD_ONE, ONE_LT_POS] >-
  rw_tac std_ss[MOD_MULT_ASSOC, ONE_LT_POS] >>
  metis_tac[GEN_MULT_INV_DEF]);

(* Theorem: Estar is a Finite Group *)
(* Proof: by Estar_group, FINITE (Estar n).carrier. *)
val Estar_finite_group = store_thm(
  "Estar_finite_group",
  ``!n. 1 < n ==> FiniteGroup (Estar n)``,
  rw[FiniteGroup_def, Estar_group, Estar_property]);

(* Theorem: Estar is a Finite Abelian Group *)
(* Proof: by checking definitions. *)
val Estar_finite_abelian_group = store_thm(
  "Estar_finite_abelian_group",
  ``!n. 1 < n ==> FiniteAbelianGroup (Estar n)``,
  rw_tac arith_ss [FiniteAbelianGroup_def, AbelianGroup_def, Estar_group, Estar_property]);

(* Theorem: (Estar n).exp a k = a ** k MOD n *)
(* Proof:
   By induction on k.
   Base case: (Estar n).exp a 0 = a ** 0 MOD n
     (Estar n).exp a 0
   = (Estar n).id                   by group_exp_0
   = 1                              by Estar_def
   = 1 MOD n                        by ONE_MOD
   = a ** 0 MOD n                   by EXP
   Step case: (Estar n).exp a k = a ** k MOD n ==> (Estar n).exp a (SUC k) = a ** SUC k MOD n
     (Estar n).exp a (SUC k)
   = a * (group_exp (Estar n) a k)  by group_exp_SUC
   = a * ((a ** k) MOD n)           by inductive hypothesis
   = (a MOD n) * ((a ** k) MOD n)   by a < n, MOD_LESS
   = (a * (a ** k)) MOD n           by MOD_TIMES2
   = (a ** (SUC k) MOD n            by EXP
*)
val Estar_exp = store_thm(
  "Estar_exp",
  ``!n a. 1 < n /\ a IN (Estar n).carrier ==> !k. (Estar n).exp a k = (a ** k) MOD n``,
  rpt strip_tac >>
  `Group (Estar n)` by rw_tac std_ss[Estar_group] >>
  `0 < n` by decide_tac >>
  Induct_on `k` >| [
    rw_tac std_ss[group_exp_0, EXP, Estar_def],
    rw_tac std_ss[group_exp_SUC, EXP, Estar_def] >>
    `!x. x IN (Estar n).carrier ==> (x MOD n = x)` by rw[Estar_def, Euler_def, residue_def] >>
    metis_tac[MOD_TIMES2]
  ]);

(* ------------------------------------------------------------------------- *)
(* Euler-Fermat Theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For all a in Estar n, a ** (totient n) MOD n = 1 *)
(* Proof:
   Since FiniteAbelianGroup (Estar n)        by Estar_finite_abelian_group, 1 < n
     and a IN (Estar n).carrier              by Estar_property, Euler_element
     and (Estar n).id = 1                    by Estar_property
     and CARD (Estar n).carrier = totient n  by Estar_property
     and !k. (Estar n).exp k = a ** k MOD n  by Estar_exp
   Hence a ** (totient n) MOD n = 1          by finite_abelian_Fermat
*)
val Euler_Fermat_eqn = store_thm(
  "Euler_Fermat_eqn",
  ``!n a. 1 < n /\ a < n /\ coprime n a ==> (a ** (totient n) MOD n = 1)``,
  rpt strip_tac >>
  `0 < a` by metis_tac[GCD_0, NOT_ZERO, LESS_NOT_EQ] >>
  metis_tac[Estar_finite_abelian_group, Euler_element, Estar_property, finite_abelian_Fermat, Estar_exp]);

(* Theorem: 1 < n /\ coprime n a ==> (a ** (totient n) MOD n = 1) *)
(* Proof:
   Let b = a MOD n.
   Then b < n            by MOD_LESS, 0 < n
    and coprime n b      by coprime_mod, 0 < n
        a ** totient n MOD n
      = b ** totient n MOD n   by MOD_EXP
      = 1                      by Euler_Fermat_eqn
*)
val Euler_Fermat_thm = store_thm(
  "Euler_Fermat_thm",
  ``!n a. 1 < n /\ coprime n a ==> (a ** (totient n) MOD n = 1)``,
  rpt strip_tac >>
  qabbrev_tac `b = a MOD n` >>
  `b < n` by rw[Abbr`b`] >>
  `coprime n b` by rw[coprime_mod, Abbr`b`] >>
  `a ** totient n MOD n = b ** totient n MOD n` by rw[MOD_EXP, Abbr`b`] >>
  metis_tac[Euler_Fermat_eqn]);

(* Theorem: 1 < n /\ coprime a n ==> (a ** (totient n) MOD n = 1) *)
(* Proof: by Euler_Fermat_thm, GCD_SYM *)
val Euler_Fermat_alt = store_thm(
  "Euler_Fermat_alt",
  ``!n a. 1 < n /\ coprime a n ==> (a ** (totient n) MOD n = 1)``,
  rw[Euler_Fermat_thm, GCD_SYM]);

(* Theorem: For prime p, 0 < a < p ==> a ** (p - 1) MOD p = 1 *)
(* Proof
   Using Z* p:
   Given prime p, 0 < p                      by PRIME_POS
     ==> FiniteAbelianGroup (Z* p)           by Zstar_finite_abelian_group
     and 0 < a < p ==> a IN (Z* p).carrier   by Zstar_def, residue_def
     and CARD (Z* p).carrier = (p - 1)       by Zstar_property
     and !n. (Z* p).exp a n = a ** n MOD p   by Zstar_exp
   Hence a ** (p - 1) MOD p = 1              by finite_abelian_Fermat

   Using Euler_Fermat_thm:
   For prime p,  1 < p                   by ONE_LT_PRIME
       and  gcd p a = 1                  by prime_coprime_all_lt
   Hence  (a ** (totient p) MOD p = 1)   by Euler_Fermat_eqn, 1 < p
   or      a ** (p-1) MOD p = 1          by Euler_card_prime
*)
val Fermat_little_thm = store_thm(
  "Fermat_little_thm",
  ``!p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)``,
  rw[ONE_LT_PRIME, prime_coprime_all_lt, Euler_Fermat_eqn, GSYM Euler_card_prime]);

(* Theorem: prime p ==> (a ** p MOD p = a MOD p) *)
(* Proof:
   Note 0 < p             by PRIME_POS
     so p = SUC (p - 1)   by arithmetic
   Let b = a MOD p.
   Then b ** p MOD p = a ** p MOD p    by MOD_EXP, 0 < p
   Thus the goal is: b ** p MOD p = b.
   If b = 0,
        0 ** p MOD p
      = 0 MOD p                        by ZERO_EXP
      = 0                              by ZERO_MOD
   If b <> 0,
      Then 0 < b /\ b < p              by MOD_LESS, 0 < p
        b ** p MOD p
      = (b ** (SUC (p - 1))) MOD p     by above
      = (b * b ** (p - 1)) MOD p       by EXP
      = ((b MOD p) * (b ** (p - 1) MOD p)) MOD p
                                       by MOD_TIMES2
      = ((b MOD p) * 1) MOD p          by Fermat_little_thm
      = b MOD p MOD p                  by MULT_RIGHT_1
      = b MOD p                        by MOD_MOD
      = a MOD p                        by MOD_MOD
      = b                              by notation
*)
val Fermat_little_eqn = store_thm(
  "Fermat_little_eqn",
  ``!p a. prime p ==> (a ** p MOD p = a MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `b = a MOD p` >>
  `b < p` by rw[Abbr`b`] >>
  `b ** p MOD p = b` suffices_by rw[MOD_EXP, Abbr`b`] >>
  Cases_on `b = 0` >-
  metis_tac[ZERO_EXP, ZERO_MOD, NOT_ZERO_LT_ZERO] >>
  `0 < b` by decide_tac >>
  `b ** (p - 1) MOD p = 1` by rw[Fermat_little_thm] >>
  `p = SUC (p - 1)` by decide_tac >>
  metis_tac[EXP, MOD_TIMES2, MOD_MOD, MULT_RIGHT_1]);

(* Theorem: 1 < n /\ a < n /\ coprime n a ==>
           ((Estar n).inv a = a ** ((totient n) - 1) MOD n) *)
(* Proof:
   Note Group (Estar n)            by Estar_group, 1 < n
    and 0 < a                      by GCD_0, n <> 1
    and a IN (Estar n).carrier     by Estar_element
   Let b = a ** ((totient n) - 1) MOD n.
   The goal becomes: (Estar n).inv a = b.

   Note b = (Estar n).exp a ((totient n) - 1)      by Estar_exp
   Thus b IN (Estar n).carrier                     by group_exp_element
        (Estar n).op a b
      = (a * a ** ((totient n) - 1) MOD n) MOD n   by Estar_property
      = (a * a ** (totient n - 1)) MOD n           by LESS_MOD, MOD_TIMES2, 0 < n
      = (a ** SUC (totient n - 1)) MOD n           by EXP
      = (a ** totient n) MOD n                     by 0 < totient n from Euler_card_bounds
      = 1                                          by Euler_Fermat_eqn
      = (Estar n).id                               by Estar_property
   Therefore b = (Estar n).inv a                   by group_rinv_unique
*)
val Estar_inv = store_thm(
  "Estar_inv",
  ``!n a. 1 < n /\ a < n /\ coprime n a ==>
      ((Estar n).inv a = a ** ((totient n) - 1) MOD n)``,
  rpt strip_tac >>
  `Group (Estar n)` by rw_tac std_ss[Estar_group] >>
  `0 < a` by metis_tac[GCD_0, NOT_ZERO, LESS_NOT_EQ] >>
  `a IN (Estar n).carrier` by rw_tac std_ss[Estar_element] >>
  qabbrev_tac `b = a ** ((totient n) - 1) MOD n` >>
  `b = (Estar n).exp a ((totient n) - 1)` by rw[Estar_exp, Abbr`b`] >>
  `b IN (Estar n).carrier` by rw[] >>
  `(Estar n).op a b = (Estar n).id` by
  (`(Estar n).id = 1` by rw[Estar_property] >>
  `(Estar n).op a b = (a * a ** ((totient n) - 1) MOD n) MOD n` by rw[Estar_property, Abbr`b`] >>
  `_ = (a * a ** (totient n - 1)) MOD n` by metis_tac[LESS_MOD, MOD_TIMES2, ONE_LT_POS] >>
  `_ = (a ** SUC (totient n - 1)) MOD n` by rw[EXP] >>
  `0 < totient n` by rw[Euler_card_bounds] >>
  `SUC (totient n - 1) = totient n` by decide_tac >>
  rw[Euler_Fermat_eqn]) >>
  metis_tac[group_rinv_unique]);

(* Theorem: As function, (Estar n).inv a = a ** (totient n - 1) MOD n) *)
(* Proof: by Estar_inv. *)
val Estar_inv_compute = store_thm(
  "Estar_inv_compute[compute]",
  ``!n a. (Estar n).inv a = if 1 < n /\ a < n /\ coprime n a
                           then a ** ((totient n) - 1) MOD n
                           else FAIL ((Estar n).inv a) bad_element``,
  rw_tac std_ss[Estar_inv, combinTheory.FAIL_DEF]);
(* put in computeLib for Estar inverse computation *)

(*
> EVAL ``(Estar 10).inv 3``;
val it = |- (Estar 10).inv 3 = 7: thm
*)

(* ------------------------------------------------------------------------- *)
(* The following is a rework from Hol/examples/elliptic/groupScript.sml      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The Trivial Group.                                                        *)
(* ------------------------------------------------------------------------- *)

(* The trivial group: {#e} *)
val trivial_group_def = zDefine`
  trivial_group e : 'a group =
   <| carrier := {e};
           id := e;
       (* inv := (\x. e);  *)
           op := (\x y. e)
    |>`;

(*
- type_of ``trivial_group e``;
> val it = ``:'a group`` : hol_type
*)

(* Theorem: (trivial_group e).carrier = {e} *)
(* Proof: by trivial_group_def. *)
Theorem trivial_group_carrier:
  !e. (trivial_group e).carrier = {e}
Proof
  simp[trivial_group_def]
QED

(* Theorem: (trivial_group e).id = e *)
(* Proof: by trivial_group_def. *)
Theorem trivial_group_id:
  !e. (trivial_group e).id = e
Proof
  simp[trivial_group_def]
QED

(* Theorem: {#e} is indeed a group *)
(* Proof: check by definition. *)
val trivial_group = store_thm(
  "trivial_group",
  ``!e. FiniteAbelianGroup (trivial_group e)``,
  rw_tac std_ss[trivial_group_def, FiniteAbelianGroup_def, FiniteGroup_def, AbelianGroup_def, group_def_alt, IN_SING, FINITE_SING, GSPECIFICATION]);

(* ------------------------------------------------------------------------- *)
(* The Function Cyclic Group.                                                *)
(* ------------------------------------------------------------------------- *)

(* Cyclic group of f and e
   = all FUNPOW f by a generator e
   = {e, f e, f f e, f f f e, ... }
*)

val fn_cyclic_group_def = zDefine`
    fn_cyclic_group e f : 'a group =
   <| carrier := { x | ?n. FUNPOW f n e = x };
           id := e; (* Note: next comment must be in one line *)
      (*  inv := (\x. @y. ?yi. (FUNPOW f yi e = y) /\ (!xi. (FUNPOW f xi e = x) ==> (FUNPOW f (xi + yi) e = e)));  *)
           op := (\x y. @z. !xi yi.
                   (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==>
                   (FUNPOW f (xi + yi) e = z))
    |>`;

(*
- type_of ``fn_cyclic_group e f``;
> val it = ``:'a group`` : hol_type
*)

(* Original:

val fn_cyclic_group_def = Define
  `fn_cyclic_group e f : 'a group =
   <| carrier := { x | ?n. FUNPOW f n e = x };
      id := e;
      inv := (\x. @y. ?yi. !xi.
                (FUNPOW f yi e = y) /\
                ((FUNPOW f xi e = x) ==> (FUNPOW f (xi + yi) e = e)));
      mult := (\x y. @z. !xi yi.
                (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==>
                (FUNPOW f (xi + yi) e = z)) |>`;

*)

(* Theorem: alternative characterization of cyclic group:
   If there exists a period k: k <> 0 /\ FUNPOW f k e = e
   Let order n = LEAST such k, then:
   (1) (fn_cyclic_group e f).carrier = { FUNPOW f k e | k < n }
   (2) (fn_cyclic_group e f).id = e)
   (3) !i. (fn_cyclic_group e f).inv (FUNPOW f i e) = FUNPOW f ((n - i MOD n) MOD n) e
   (4) !i j. (fn_cyclic_group e f).op (FUNPOW f i e) (FUNPOW f j e) = FUNPOW f ((i + j) MOD n) e
*)
(* Proof:
   Expand by fn_cyclic_group_def, this is to show:
   (1) 0 < h /\ FUNPOW f h e = e ==> ?k. (FUNPOW f n e = FUNPOW f k e) /\ k < h
       Since (n MOD h) < h                         by MOD_LESS
         and FUNPOW f n e = FUNPOW f (n MOD h) e   by FUNPOW_MOD, 0 < h
       So take k = n MOD h will satisfy the requirements.
   (2) ?n. FUNPOW f n e = FUNPOW f k e
       Just take n = k.
   (3) (@z. !xi yi. (FUNPOW f xi e = FUNPOW f i e) /\ (FUNPOW f yi e = FUNPOW f j e) ==>
                    (FUNPOW f (xi + yi) e = z)) = FUNPOW f ((i + j) MOD h) e
       This comes down to show:
       (1) ?z. !xi yi. (FUNPOW f xi e = FUNPOW f i e) /\ (FUNPOW f yi e = FUNPOW f j e) ==>
                       (FUNPOW f (xi + yi) e = z)
           Let z = FUNPOW f (i + j) e,
           the goal simplifies to: FUNPOW f (xi + yi) e = FUNPOW f (i + j) e
             FUNPOW f (xi + yi) e
           = FUNPOW f xi (FUNPOW f yi e)     by FUNPOW_ADD
           = FUNPOW f xi (FUNPOW f j e)      by given
           = FUNPOW f (xi + j) e             by FUNPOW_ADD
           = FUNPOW f (j + xi) e             by ADD_COMM
           = FUNPOW f j (FUNPOW f xi e)      by FUNPOW_ADD
           = FUNPOW f j (FUNPOW f i e)       by given
           = FUNPOW f (j + i) e              by FUNPOW_ADD
           = FUNPOW f (i + j) e              by ADD_COMM
       (2) z = FUNPOW f ((i + j) MOD h) e
           That is, FUNPOW f (i + j) e = FUNPOW f ((i + j) MOD h) e
           which is true by FUNPOW_MOD
*)
val fn_cyclic_group_alt = store_thm(
  "fn_cyclic_group_alt",
  ``!e f n.
     (?k. k <> 0 /\ (FUNPOW f k e = e)) /\
     (n = LEAST k. k <> 0 /\ (FUNPOW f k e = e)) ==>
     ((fn_cyclic_group e f).carrier = { FUNPOW f k e | k < n }) /\
     ((fn_cyclic_group e f).id = e) /\
  (* (!i. (fn_cyclic_group e f).inv (FUNPOW f i e) = FUNPOW f ((n - i MOD n) MOD n) e) /\ *)
     (!i j. (fn_cyclic_group e f).op (FUNPOW f i e) (FUNPOW f j e) = FUNPOW f ((i + j) MOD n) e)``,
  rpt gen_tac >>
  simp_tac std_ss [whileTheory.LEAST_EXISTS] >>
  Q.SPEC_TAC (`LEAST k. k <> 0 /\ (FUNPOW f k e = e)`,`h`) >>
  gen_tac >>
  strip_tac >>
  `0 < h` by decide_tac >>
  rw[fn_cyclic_group_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[FUNPOW_MOD, MOD_LESS] >-
  metis_tac[] >>
  normalForms.SELECT_TAC >>
  match_mp_tac (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``) >>
  conj_tac >| [
    qexists_tac `FUNPOW f (i + j) e` >>
    rw[] >>
    metis_tac[FUNPOW_ADD, ADD_COMM],
    rw[] >>
    metis_tac[FUNPOW_MOD]
  ]);

(* Theorem: (fn_cyclic_group e f).carrier = { x | ?n. FUNPOW f n e = x } *)
(* Proof: by fn_cyclic_group_def. *)
Theorem fn_cyclic_group_carrier:
  !e f. (fn_cyclic_group e f).carrier = { x | ?n. FUNPOW f n e = x }
Proof
  simp[fn_cyclic_group_def]
QED

(* Theorem: (fn_cyclic_group e f).id = e *)
(* Proof: by fn_cyclic_group_def. *)
Theorem fn_cyclic_group_id:
  !e f. (fn_cyclic_group e f).id = e
Proof
  simp[fn_cyclic_group_def]
QED

(* Theorem: Group (fn_cyclic_group e f) *)
(* Proof:
   By fn_cyclic_group_alt and group_def_alt.
   This comes down to 2 goals:
   (1) ?n. n <> 0 /\ (FUNPOW f n e = e) ==>
       (?k. k <> 0 /\ (FUNPOW f k e = e)) /\ ((LEAST n. n <> 0 /\ (FUNPOW f n e = e)) =
       LEAST k. k <> 0 /\ (FUNPOW f k e = e))
       This is trivially true.
   (2) Group (fn_cyclic_group e f)
       By group_def_alt, this is to show:
       (1) ?k''. (FUNPOW f ((k + k') MOD h) e = FUNPOW f k'' e) /\ k'' < h
           Let k'' = (k + k') MOD h, this is true by MOD_LESS
       (2) FUNPOW f (((k + k') MOD h + k'') MOD h) e = FUNPOW f ((k + (k' + k'') MOD h) MOD h) e
             ((k + k') MOD h + k'') MOD h
           = ((k + k') MOD h + k'' MOD h) MOD h   by LESS_MOD
           = (k + k' + k'') MOD h                 by MOD_PLUS
           = (k + (k' + k'')) MOD h               by ADD_ASSOC
           = (k MOD h + (k' + k'') MOD h) MOD h   by MOD_PLUS
           = (k + (k' + k'') MOD h) MOD h         by LESS_MOD
       (3) ?k. (e = FUNPOW f k e) /\ k < h
           Take k = 0, then FUNPOW f 0 e = e      by FUNPOW_0
       (4) (fn_cyclic_group e f).op e (FUNPOW f k e) = FUNPOW f k e
           With FUNPOW f 0 e = e                  by FUNPOW_0
            and the given, this is to show:
            FUNPOW f ((0 + k) MOD h) e = FUNPOW f k e
            But (0 + k) MOD h = k MOD h = k       by LESS_MOD
       (5) ?y. (?k. (y = FUNPOW f k e) /\ k < h) /\ ((fn_cyclic_group e f).op y (FUNPOW f k e) = e)
           Let y = FUNPOW f ((h - k) MOD h) e. This is to show:
           (1) ?k'. (FUNPOW f ((h - k) MOD h) e = FUNPOW f k' e) /\ k' < h
               Take k' = (h - k) MOD h < h        by MOD_LESS
           (2) FUNPOW f (((h - k) MOD h + k) MOD h) e = e
                 ((h - k) MOD h + k) MOD h
               = ((h - k) MOD h + (k MOD h)) MOD h   by LESS_MOD
               = (h - k + k) MOD h                   by MOD_PLUS
               = h MOD h                             by arithmetic
               = 0                                   by DIVMOD_ID
               Thus true since FUNPOW f 0 e = e      by FUNPOW_0
*)
val fn_cyclic_group_group = store_thm(
  "fn_cyclic_group_group",
  ``!e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> Group (fn_cyclic_group e f)``,
  rpt gen_tac >>
  disch_then assume_tac >>
  mp_tac (Q.SPECL [`e`,`f`,`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`] fn_cyclic_group_alt) >>
  match_mp_tac (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``) >>
  conj_tac >-
  rw[] >>
  pop_assum mp_tac >>
  simp_tac std_ss [whileTheory.LEAST_EXISTS] >>
  qspec_tac (`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`,`h`) >>
  gen_tac >>
  rpt strip_tac >>
  `0 < h` by decide_tac >>
  rw[group_def_alt] >| [
    rw_tac std_ss[] >>
    qexists_tac `(k + k') MOD h` >>
    metis_tac[MOD_LESS],
    rw_tac std_ss[] >>
    metis_tac[ADD_ASSOC, MOD_PLUS, LESS_MOD],
    metis_tac[FUNPOW_0],
    metis_tac[FUNPOW_0, ADD_CLAUSES, LESS_MOD],
    qexists_tac `FUNPOW f ((h - k) MOD h) e` >>
    rw_tac std_ss[] >-
    metis_tac[MOD_LESS] >>
    metis_tac[LESS_MOD, MOD_PLUS, SUB_ADD, LESS_IMP_LESS_OR_EQ, DIVMOD_ID, FUNPOW_0]
  ]);

(* Theorem: FiniteAbelianGroup (fn_cyclic_group e f) *)
(* Proof:
   Use fn_cyclic_group_alt due to assumption: (?n. n <> 0 /\ (FUNPOW f n e = e))
   By fn_cyclic_group_alt, this comes down to 2 goals:
   (1) ?n. n <> 0 /\ (FUNPOW f n e = e) ==>
       (?k. k <> 0 /\ (FUNPOW f k e = e)) /\ ((LEAST n. n <> 0 /\ (FUNPOW f n e = e)) =
       LEAST k. k <> 0 /\ (FUNPOW f k e = e))
       This is trivially true.
   (2) expand by FiniteAbelianGroup_def, AbelianGroup_def, the goals are:
       (1) Group (fn_cyclic_group e f), true by fn_cyclic_group_group.
       (2) FUNPOW f ((k + k') MOD h) e = FUNPOW f ((k' + k) MOD h) e, true by ADD_COMM
       (3) FINITE {FUNPOW f k e | k < h}, true by FINITE_COUNT_IMAGE
*)
val fn_cyclic_group_finite_abelian_group = store_thm(
  "fn_cyclic_group_finite_abelian_group",
  ``!e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteAbelianGroup (fn_cyclic_group e f)``,
  rpt gen_tac >>
  (disch_then assume_tac) >>
  mp_tac (Q.SPECL [`e`,`f`,`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`] fn_cyclic_group_alt) >>
  match_mp_tac (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``) >>
  conj_tac >| [
    rw[],
    pop_assum mp_tac >>
    simp_tac std_ss [whileTheory.LEAST_EXISTS] >>
    Q.SPEC_TAC (`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`,`h`) >>
    gen_tac >>
    strip_tac >>
    `0 < h` by decide_tac >>
    strip_tac >>
    rw[FiniteAbelianGroup_def, AbelianGroup_def] >| [
      metis_tac[fn_cyclic_group_group],
      rw_tac std_ss[ADD_COMM],
      rw_tac std_ss[FINITE_COUNT_IMAGE]
    ]
  ]);

(* Theorem: FiniteGroup (fn_cyclic_group e f) *)
(* Proof: by fn_cyclic_group_finite_abelian_group. *)
val fn_cyclic_group_finite_group = store_thm(
  "fn_cyclic_group_finite_group",
  ``!e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteGroup (fn_cyclic_group e f)``,
  metis_tac[fn_cyclic_group_finite_abelian_group, FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def]);

(* ------------------------------------------------------------------------- *)
(* The Group of Addition Modulo n.                                           *)
(* ------------------------------------------------------------------------- *)

(* Additive Modulo Group *)
val add_mod_def = zDefine`
  add_mod n : num group =
   <| carrier := { i | i < n };
           id := 0;
       (* inv := (\i. (n - i) MOD n); *)
           op := (\i j. (i + j) MOD n)
    |>
`;
(* This group, with modulus n, is taken as the additive group in ZN ring later. *)
(* Evaluation is given later in add_mod_eval and add_mod_inv. *)

(*
- type_of ``add_mod n``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: add_mod evaluation. *)
(* Proof: by add_mod_def. *)
val add_mod_eval = store_thm(
  "add_mod_eval",
  ``!n. ((add_mod n).carrier = {i | i < n}) /\
       (!x y. (add_mod n).op x y = (x + y) MOD n) /\
       ((add_mod n).id = 0)``,
  rw_tac std_ss[add_mod_def]);

(* Now put these to computeLib *)
val _ = computeLib.add_persistent_funs ["add_mod_eval"];
(*
- EVAL ``(add_mod 5).id``;
> val it = |- (add_mod 5).id = 0 : thm
- EVAL ``(add_mod 5).op 3 4``;
> val it = |- (add_mod 5).op 3 4 = 2 : thm
- EVAL ``(add_mod 5).op 6 8``;
> val it = |- (add_mod 5).op 6 8 = 4 : thm
*)
(* Later put add_mod_inv_compute in computeLib. *)

(* Theorem: x IN (add_mod n).carrier <=> x < n *)
(* Proof: by add_mod_def *)
val add_mod_element = store_thm(
  "add_mod_element",
  ``!n x. x IN (add_mod n).carrier <=> x < n``,
  rw[add_mod_def]);

(* Theorem: properties of (add_mod n) *)
(* Proof: by definition. *)
val add_mod_property = store_thm(
  "add_mod_property",
  ``!n. (!x. x IN (add_mod n).carrier <=> x < n) /\
       ((add_mod n).id = 0) /\
       (!x y. (add_mod n).op x y = (x + y) MOD n) /\
       FINITE (add_mod n).carrier /\
       (CARD (add_mod n).carrier = n)``,
  rw_tac std_ss[add_mod_def, GSYM count_def, FINITE_COUNT, CARD_COUNT, IN_COUNT]);

(* Theorem: (add_mod n).carrier = { i | i < n } *)
(* Proof: by add_mod_def. *)
Theorem add_mod_carrier:
  !n. (add_mod n).carrier = { i | i < n }
Proof
  simp[add_mod_def]
QED

(* Theorem: (add_mod n).carrier = count n *)
(* Proof: by add_mod_def. *)
Theorem add_mod_carrier_alt:
  !n. (add_mod n).carrier = count n
Proof
  simp[add_mod_def, EXTENSION]
QED

(* Theorem: (add_mod n).id = 0 *)
(* Proof: by add_mod_def. *)
Theorem add_mod_id:
  !n. (add_mod n).id = 0
Proof
  simp[add_mod_def]
QED

(* Theorem: FINITE (add_mod n).carrier *)
(* Proof: by add_mod_property *)
val add_mod_finite = store_thm(
  "add_mod_finite",
  ``!n. FINITE (add_mod n).carrier``,
  rw[add_mod_property]);

(* Theorem: CARD (add_mod n).carrier = n *)
(* Proof: by add_mod_property *)
val add_mod_card = store_thm(
  "add_mod_card",
  ``!n. CARD (add_mod n).carrier = n``,
  rw[add_mod_property]);

(* Theorem: Additive Modulo Group is a group. *)
(* Proof: check group definitions.
   For associativity,
   to show: x < n /\ y < n /\ z < n ==> ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n
   LHS = ((x + y) MOD n + z) MOD n
       = ((x + y) MOD n + z MOD n) MOD n    by LESS_MOD
       = (x + y + z) MOD n                  by MOD_PLUS
       = (x + (y + z)) MOD n                by ADD_ASSOC
       = (x MOD n + (y + z) MOD n) MOD n    by MOD_PLUS
       = (x + (y + z) MOD n) MOD n          by LESS_MOD
       = RHS
   For additive inverse,
   to show: x < n ==> ?y. y < n /\ ((y + x) MOD n = 0)
   If x = 0, take y = 0.        (0 + 0) MOD n = 0 MOD n = 0  by ZERO_MOD
   If x <> 0, take y = n-x. (n - x + x) MOD n = n MOD n = 0  by DIVMOD_ID
*)
val add_mod_group = store_thm(
  "add_mod_group",
  ``!n. 0 < n ==> Group (add_mod n)``,
  rw_tac std_ss[group_def_alt, add_mod_property] >| [
    metis_tac[LESS_MOD, MOD_PLUS, ADD_ASSOC],
    Cases_on `x = 0` >| [
      metis_tac[ZERO_MOD, ADD],
      metis_tac[DIVMOD_ID, DECIDE ``x <> 0 /\ x < n ==> n - x < n /\ (n - x + x = n)``]
    ]
  ]);

(* Theorem: Additive Modulo Group is an Abelian group. *)
(* Proof: by add_mod_group and ADD_COMM. *)
val add_mod_abelian_group = store_thm(
  "add_mod_abelian_group",
  ``!n. 0 < n ==> AbelianGroup (add_mod n)``,
  rw_tac std_ss[AbelianGroup_def, add_mod_group, add_mod_property, ADD_COMM]);

(* Theorem: Additive Modulo Group is a Finite Group. *)
(* Proof: by add_mod_group and add_mod_property. *)
val add_mod_finite_group = store_thm(
  "add_mod_finite_group",
  ``!n. 0 < n ==> FiniteGroup (add_mod n)``,
  rw_tac std_ss[FiniteGroup_def, add_mod_group, add_mod_property]);

(* Theorem: Additive Modulo Group is a Finite Abelian Group. *)
(* Proof: by add_mod_abelian_group and add_mod_property. *)
val add_mod_finite_abelian_group = store_thm(
  "add_mod_finite_abelian_group",
  ``!n. 0 < n ==> FiniteAbelianGroup (add_mod n)``,
  rw_tac std_ss[FiniteAbelianGroup_def, add_mod_abelian_group, add_mod_property]);

(* Theorem: 0 < n ==> !x m. (add_mod n).exp x m = (x * m) MOD n *)
(* Proof:
   By induction on m:
   Base case: (add_mod n).exp x 0 = (x * 0) MOD n
         (add_mod n).exp x 0
       = (add_mod n).id            by group_exp_0
       = 0                         by add_mod_property
       = 0 MOD n                   by ZERO_MOD, 0 < n
       = (x * 0) MOD n             by MULT_0
   Step case: (add_mod n).exp x m = (x * m) MOD n ==>
              (add_mod n).exp x (SUC m) = (x * SUC m) MOD n
         (add_mod n).exp x (SUC m)
       = (add_mod n).op x ((add_mod n).exp x m)   by group_exp_SUC
       = (add_mod n).op x ((x * m) MOD n)         by induction hypothesis
       = (x + ((x * m) MOD n)) MOD n              by add_mod_property
       = (x + x * m) MOD n                        by MOD_PLUS, MOD_MOD
       = (x * SUC m) MOD n                        by MULT_SUC
*)
val add_mod_exp = store_thm(
  "add_mod_exp",
  ``!n. 0 < n ==> !x m. (add_mod n).exp x m = (x * m) MOD n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[add_mod_property] >>
  rw_tac std_ss[group_exp_SUC, add_mod_property] >>
  metis_tac[MOD_PLUS, MOD_MOD, MULT_SUC]);

(* Theorem: (add_mod n).inv x = (n - x) MOD n *)
(* Proof: by MOD_ADD_INV and group_linv_unique. *)
val add_mod_inv = store_thm(
  "add_mod_inv",
  ``!n x. 0 < n /\ x < n ==> ((add_mod n).inv x = (n - x) MOD n)``,
  rpt strip_tac >>
  `x IN (add_mod n).carrier /\ (n - x) MOD n IN (add_mod n).carrier` by rw_tac std_ss[add_mod_property] >>
  `((n - x) MOD n + x) MOD n = 0` by rw_tac std_ss[MOD_ADD_INV] >>
  metis_tac[add_mod_group, group_linv_unique, add_mod_property]);

(* Theorem: (add_mod n).inv x = (n - x) MOD n as function *)
(* Proof: by add_mod_inv. *)
val add_mod_inv_compute = store_thm(
  "add_mod_inv_compute",
  ``!n x. (add_mod n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((add_mod n).inv x) bad_element``,
  rw_tac std_ss[add_mod_inv, combinTheory.FAIL_DEF]);

(* val _ = computeLib.add_persistent_funs ["add_mod_inv"]; -- cannot put a non-function. *)

(* Function can be put to computeLib *)
val _ = computeLib.add_persistent_funs ["add_mod_inv_compute"];
(* val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0); *)

(*
- EVAL ``(add_mod 5).inv 3``;
> val it = |- (add_mod 5).inv 3 = 2 : thm
- EVAL ``(add_mod 5).inv 7``;
> val it = |- (add_mod 5).inv 7 = FAIL ((add_mod 5).inv 7) bad_element : thm
*)

val _ = export_rewrites ["add_mod_eval", "add_mod_inv"];
(*
- SIMP_CONV (srw_ss()) [] ``(add_mod 5).op 3 4``;
> val it = |- (add_mod 5).op 3 4 = 2 : thm
- SIMP_CONV (srw_ss()) [] ``(add_mod 5).id``;
> val it = |- (add_mod 5).id = 0 : thm
- SIMP_CONV (srw_ss()) [] ``(add_mod 5).inv 2``;
> val it = |- (add_mod 5).inv 2 = 3 : thm
*)

(* ------------------------------------------------------------------------- *)
(* The Group of Multiplication Modulo prime p.                               *)
(* ------------------------------------------------------------------------- *)

(* Multiplicative Modulo Group *)
(* This version relies on fermat_little from pure Number Theory! *)
(*
val mult_mod_def = zDefine
  `mult_mod p =
   <| carrier := { i | i <> 0 /\ i < p };
           id := 1;
          inv := (\i. i ** (p - 2) MOD p);
         mult := (\i j. (i * j) MOD p)
    |>`;
*)

(* This version relies on MOD_MULT_INV, using LINEAR_GCD. *)
val mult_mod_def = zDefine`
  mult_mod p : num group =
   <| carrier := { i | i <> 0 /\ i < p };
           id := 1;
       (* inv := (\i. MOD_MULT_INV p i); *)
           op := (\i j. (i * j) MOD p)
    |>
`;
(* This group, with prime modulus, is not used in ZN ring later. *)
(* Evaluation is given later in mult_mod_eval and mult_mod_inv. *)

(*
- type_of ``mult_mod p``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: x IN (mult_mod p).carrier <=> x <> 0 /\ x < p *)
(* Proof: by mult_mod_def *)
val mult_mod_element = store_thm(
  "mult_mod_element",
  ``!p x. x IN (mult_mod p).carrier <=> x <> 0 /\ x < p``,
  rw[mult_mod_def]);

(* Theorem: x IN (mult_mod p).carrier <=> 0 < x /\ x < p *)
(* Proof: by mult_mod_def *)
val mult_mod_element_alt = store_thm(
  "mult_mod_element_alt",
  ``!p x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p``,
  rw[mult_mod_def]);

(* Theorem: properties of (mult_mod p) *)
(* Proof: by definition. *)
val mult_mod_property = store_thm(
  "mult_mod_property",
  ``!p. (!x. x IN (mult_mod p).carrier ==> x <> 0) /\
       (!x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p) /\
       ((mult_mod p).id = 1) /\
       (!x y. (mult_mod p).op x y = (x * y) MOD p) /\
       FINITE (mult_mod p).carrier /\
       (0 < p ==> (CARD (mult_mod p).carrier = p - 1))``,
  rw_tac std_ss[mult_mod_def, GSPECIFICATION, NOT_ZERO_LT_ZERO] >-
  metis_tac[residue_def, residue_finite] >>
  metis_tac[residue_def, residue_card]);

(* Theorem: (mult_mod p).carrier = { i | i <> 0 /\ i < p } *)
(* Proof: by mult_mod_def. *)
Theorem mult_mod_carrier:
  !p. (mult_mod p).carrier = { i | i <> 0 /\ i < p }
Proof
  simp[mult_mod_def]
QED

(* Theorem: (mult_mod p).carrier = residue p *)
(* Proof: by mult_mod_def, residue_def. *)
Theorem mult_mod_carrier_alt:
  !p. (mult_mod p).carrier = residue p
Proof
  simp[mult_mod_def, residue_def, EXTENSION]
QED

(* Theorem: (mult_mod p).id = 1 *)
(* Proof: by mult_mod_def. *)
Theorem mult_mod_id:
  !p. (mult_mod p).id = 1
Proof
  simp[mult_mod_def]
QED

(* Theorem: FINITE (mult_mod p).carrier *)
(* Proof: by mult_mod_property *)
val mult_mod_finite = store_thm(
  "mult_mod_finite",
  ``!p. FINITE (mult_mod p).carrier``,
  rw[mult_mod_property]);

(* Theorem: 0 < p ==> (CARD (mult_mod p).carrier = p - 1) *)
(* Proof: by mult_mod_property *)
val mult_mod_card = store_thm(
  "mult_mod_card",
  ``!p. 0 < p ==> (CARD (mult_mod p).carrier = p - 1)``,
  rw[mult_mod_property]);

(* Theorem: Multiplicative Modulo Group is a group for prime p. *)
(* Proof: check group definitions.
   (1) Closure: prime p /\ x <> 0 /\ x < p /\ y <> 0 /\ y < p ==> (x * y) MOD p <> 0
       By contradiction. Suppose (x * y) MOD p = 0
       Then  x MOD p = 0  or y MOD p = 0   by EUCLID_LEMMA
       i.e         x = 0  or       y = 0   by LESS_MOD
       contradicting x <> 0 and y <> 0.
   (2) Associativity: x < p /\ y < p /\ z < p ==> ((x * y) MOD p * z) MOD p = (x * (y * z) MOD p) MOD p
       True by MOD_MULT_ASSOC, or
       LHS = ((x * y) MOD p * z) MOD p
           = ((x * y) MOD p * z MOD p) MOD p         by MOD_LESS
           = (x * y * z) MOD p                       by MOD_TIMES2
           = (x * (y * z)) MOD p                     by MULT_ASSOC
           = (x MOD p * (y * z) MOD p) MOD p         by MOD_TIMES2
           = (x * (y * z) MOD p) MOD p               by MOD_LESS
           = RHS
   (3) Identity: prime p ==> 1 < p
       True by ONE_LT_PRIME.
   (4) Multiplicative inverse: prime p /\ x <> 0 /\ x < p ==> ?y. (y <> 0 /\ y < p) /\ ((y * x) MOD p = 1)
       True by MOD_MULT_INV_DEF.
*)
val mult_mod_group = store_thm(
  "mult_mod_group",
  ``!p. prime p ==> Group (mult_mod p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  rw_tac std_ss[group_def_alt, mult_mod_property] >| [
    metis_tac[EUCLID_LEMMA, LESS_MOD, NOT_ZERO_LT_ZERO],
    rw_tac std_ss[MOD_MULT_ASSOC],
    rw_tac std_ss[ONE_LT_PRIME],
    metis_tac[MOD_MULT_INV_DEF, NOT_ZERO_LT_ZERO]
  ]);

(* Theorem: Multiplicative Modulo Group is an Abelian group for prime p. *)
(* Proof: by mult_mod_group and MULT_COMM. *)
val mult_mod_abelian_group = store_thm(
  "mult_mod_abelian_group",
  ``!p. prime p ==> AbelianGroup (mult_mod p)``,
  rw_tac std_ss[AbelianGroup_def, mult_mod_group, mult_mod_property, MULT_COMM, PRIME_POS]);

(* Theorem: Multiplicative Modulo Group is a Finite Abelian Group for prime p. *)
(* Proof: by mult_mod_group and mult_mod_property. *)
val mult_mod_finite_group = store_thm(
  "mult_mod_finite_group",
  ``!p. prime p ==> FiniteGroup (mult_mod p)``,
  rw_tac std_ss[FiniteGroup_def, mult_mod_group, mult_mod_property]);

(* Theorem: Multiplicative Modulo Group is a Finite Abelian Group for prime p. *)
(* Proof: by mult_mod_abelian_group and mult_mod_property. *)
val mult_mod_finite_abelian_group = store_thm(
  "mult_mod_finite_abelian_group",
  ``!p. prime p ==> FiniteAbelianGroup (mult_mod p)``,
  rw_tac std_ss[FiniteAbelianGroup_def, mult_mod_abelian_group, mult_mod_property]);

(* Theorem: (mult_mod p).exp a n = a ** n MOD p *)
(* Proof:
   By induction on n.
   Base case: (mult_mod p).exp a 0 = a ** 0 MOD p
      (mult_mod p).exp a 0
    = (mult_mod p).id                by group_exp_0
    = 1                              by mult_mod_def
    = 1 MOD 1                        by DIVMOD_ID, 0 < 1
    = a ** 0 MOD p                   by EXP
   Step case:  (mult_mod p).exp a n = a ** n MOD p ==> (mult_mod p).exp a (SUC n) = a ** SUC n MOD p
      (mult_mod p).exp a (SUC n)
    = a * ((mult_mod p).exp a n)     by group_exp_SUC
    = a * ((a ** n) MOD p)           by inductive hypothesis
    = (a MOD p) * ((a ** n) MOD p)   by a < p, MOD_LESS
    = (a * (a ** n)) MOD p           by MOD_TIMES2
    = (a ** (SUC n) MOD p            by EXP
*)
val mult_mod_exp = store_thm(
  "mult_mod_exp",
  ``!p a. prime p /\ a IN (mult_mod p).carrier ==> !n. (mult_mod p).exp a n = (a ** n) MOD p``,
  rw[mult_mod_def, monoid_exp_def, residue_def] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  Induct_on `n` >-
  rw_tac std_ss[FUNPOW_0, EXP, ONE_MOD] >>
  rw_tac std_ss[FUNPOW_SUC, EXP] >>
  `a MOD p = a` by rw_tac arith_ss[] >>
  metis_tac[MOD_TIMES2]);

(* Theorem: due to zDefine before, now export the Define to computeLib. *)
(* Proof: by mult_mod_def. *)
val mult_mod_eval = store_thm(
  "mult_mod_eval",
  ``!p. ((mult_mod p).carrier = { i | i <> 0 /\ i < p }) /\
       (!x y. (mult_mod p).op x y = (x * y) MOD p) /\
       ((mult_mod p).id = 1)``,
  rw_tac std_ss[mult_mod_def]);

(*
- group_order_property |> ISPEC ``(mult_mod p)``;
> val it = |- FiniteGroup (mult_mod p) ==> !x. x IN (mult_mod p).carrier ==>
         0 < order (mult_mod p) x /\ ((mult_mod p).exp x (order (mult_mod p) x) = (mult_mod p).id) : thm
- EVAL ``order (mult_mod 5) 1``;
> val it = |- order (mult_mod 5) 1 = 1 : thm
- EVAL ``order (mult_mod 5) 2``;
> val it = |- order (mult_mod 5) 2 = 4 : thm
- EVAL ``order (mult_mod 5) 3``;
> val it = |- order (mult_mod 5) 3 = 4 : thm
- EVAL ``order (mult_mod 5) 4``;
> val it = |- order (mult_mod 5) 4 = 2 : thm
*)

(* Theorem: (mult_mod p).inv x = x ** (order (mult_mod p) x - 1) *)
(* Proof: by group_order_property and group_rinv_unique. *)
val mult_mod_inv = store_thm(
  "mult_mod_inv",
  ``!p. prime p ==> !x. 0 < x /\ x < p ==> ((mult_mod p).inv x = (mult_mod p).exp x (order (mult_mod p) x - 1))``,
  rpt strip_tac >>
  `x IN (mult_mod p).carrier /\ ((mult_mod p).id = 1)` by rw_tac std_ss[mult_mod_property] >>
  `Group (mult_mod p)` by rw_tac std_ss[mult_mod_group] >>
  `FiniteGroup (mult_mod p)` by rw_tac std_ss[FiniteGroup_def, mult_mod_property] >>
  `0 < order (mult_mod p) x /\ ((mult_mod p).exp x (order (mult_mod p) x) = 1)` by rw_tac std_ss[group_order_property] >>
  `SUC ((order (mult_mod p) x) - 1) = order (mult_mod p) x` by rw_tac arith_ss[] >>
  metis_tac[group_rinv_unique, group_exp_SUC, group_exp_element]);

(* val _ = computeLib.add_persistent_funs ["mult_mod_inv"]; -- cannot put a non-function. *)

(* Theorem: As function, (mult_mod p).inv x = x ** (order (mult_mod p) x - 1) *)
(* Proof: by mult_mod_inv. *)
val mult_mod_inv_compute = store_thm(
  "mult_mod_inv_compute",
  ``!p x. (mult_mod p).inv x = if prime p /\ 0 < x /\ x < p
                            then (mult_mod p).exp x (order (mult_mod p) x - 1)
                            else FAIL ((mult_mod p).inv x) bad_element``,
  rw_tac std_ss[mult_mod_inv, combinTheory.FAIL_DEF]);

(* Now put thse input computeLib for EVAL *)
val _ = computeLib.add_persistent_funs ["mult_mod_eval"];
val _ = computeLib.add_persistent_funs ["mult_mod_inv_compute"];
(* val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0); *)

(*
- EVAL ``(mult_mod 5).id``;
> val it = |- (mult_mod 5).id = 1 : thm
- EVAL ``(mult_mod 5).op 3 2``;
> val it = |- (mult_mod 5).op 3 2 = 1 : thm
- EVAL ``(mult_mod 5).inv 2``;
> val it = |- (mult_mod 5).inv 2 = if prime 5 then 3 else FAIL ((mult_mod 5).inv 2) bad_element : thm
- EVAL ``prime 5``;
> val it = |- prime 5 <=> prime 5 : thm

- val _ = computeLib.add_persistent_funs ["PRIME_5"];
- EVAL ``prime 5``;
> val it = |- prime 5 <=> T : thm
- EVAL ``(Z* 5).inv 2``;
> val it = |- (mult_mod 5).inv 2 = 3 : thm
*)

(* Export these for SIMP_CONV *)
val _ = export_rewrites ["mult_mod_eval", "mult_mod_inv"];

(*
- SIMP_CONV (srw_ss()) [] ``(mult_mod 5).id``;
> val it = |- (mult_mod 5).id = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(mult_mod 5).op 3 2``;
> val it = |- (mult_mod 5).op 3 2 = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(mult_mod 5).inv 2``;
! Uncaught exception:
! UNCHANGED
*)

(* ========================================================================= *)
(* Cryptography based on groups                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* ElGamal encryption and decryption -- purely group-theoretic.              *)
(* ------------------------------------------------------------------------- *)

(* Define encryption and decryption of ElGamal scheme. *)
val ElGamal_encrypt_def = Define`
  ElGamal_encrypt (g:'a group) (y:'a) (h:'a) (m:'a) (k:num) = (y ** k, (h ** k) * m)
`;

val ElGamal_decrypt_def = Define`
  ElGamal_decrypt (g:'a group) (x:num) (a:'a, b:'a) = ( |/ (a ** x)) * b
`;

(* Theorem: ElGamal decypt can undo ElGamal encrypt. *)
(* Proof:
   This is to show
   ElGamal_decrypt g x (ElGamal_encrypt g y h m k)  = m
   or:     |/ ((y ** k) ** x) * ((y ** x) ** k * m) = m

   |/ ((y ** k) ** x) * ((y ** x) ** k * m)
 = |/ (y ** (k*x)) * (y ** (x*k) * m)      by group_exp_mult
 = ( |/ y) ** (k*x) * (y ** (x*k) * m)     by group_exp_inv
 = ( |/ y) ** (k*x) * (y ** (k*x) * m)     by MULT_COMM (the x*k is not g.op, in exp)
 = (( |/ y) ** (k*x) * y ** (k*x)) * m     by group_assoc
 = ( |/y * y) ** (k*x) * m                 by group_mult_exp
 = #e ** (k*x) * m                         by group_linv, group_rinv
 = #e * m                                  by group_id_exp
 = m                                       by group_lid
*)
val ElGamal_correctness = store_thm(
  "ElGamal_correctness",
  ``!g:'a group. Group g ==> !y h m::G. !k x. (h = y ** x) ==> (ElGamal_decrypt g x (ElGamal_encrypt g y h m k) = m)``,
  rw_tac std_ss[ElGamal_encrypt_def, ElGamal_decrypt_def, RES_FORALL_THM] >>
  `|/ ((y ** k) ** x) * ((y ** x) ** k * m) = |/ (y ** (k*x)) * (y ** (x*k) * m)` by rw_tac std_ss[group_exp_mult] >>
  `_ = ( |/ y)**(k*x) * (y**(x*k) * m)` by rw_tac std_ss[group_exp_inv] >>
  `_ = ( |/ y)**(k*x) * (y**(k*x) * m)` by rw_tac std_ss[MULT_COMM] >>
  `_ = (( |/ y)**(k*x) * y**(k*x)) * m` by rw_tac std_ss[group_assoc, group_inv_element, group_exp_element] >>
  `_ = ( |/y * y)**(k*x) * m` by rw_tac std_ss[group_linv, group_rinv, group_comm_op_exp, group_inv_element] >>
  rw_tac std_ss[group_linv, group_id_exp, group_lid]);

(* ------------------------------------------------------------------------- *)
(* A Group from Sets.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define symmetric difference for two sets. *)
val symdiff_def = Define`symdiff s1 s2 = (s1 UNION s2) DIFF (s1 INTER s2)`;

(* The Group of set symmetric difference *)
val symdiff_set_def = Define`
  symdiff_set = <| carrier := UNIV;
                       id := EMPTY;
                       op := symdiff |>
`;

(*
> EVAL ``symdiff_set.id``;
val it = |- symdiff_set.id = {}: thm
> EVAL ``symdiff_set.op {1;2;3;4} {1;4;5;6}``;
val it = |- symdiff_set.op {1; 2; 3; 4} {1; 4; 5; 6} = {2; 3; 5; 6}: thm
*)


(* Theorem: symdiff_set is a Group. *)
(* Proof: check definitions. *)
val symdiff_set_group = store_thm(
  "symdiff_set_group",
  ``Group symdiff_set``,
  rw[group_def_alt, symdiff_set_def] >| [
    rw[EXTENSION, symdiff_def] >> metis_tac[],
    rw[EXTENSION, symdiff_def],
    qexists_tac `x` >> rw[EXTENSION, symdiff_def]
  ]);

val _ = export_rewrites ["symdiff_set_group"];

(* Theorem: symdiff_set is an abelian Group. *)
(* Proof: check definitions. *)
val symdiff_set_abelian_group = store_thm(
  "symdiff_set_abelian_group",
  ``AbelianGroup symdiff_set``,
  rw[AbelianGroup_def, symdiff_set_def] >>
  rw[symdiff_def, EXTENSION] >>
  metis_tac[]);

val _ = export_rewrites ["symdiff_set_abelian_group"];

(* ------------------------------------------------------------------------- *)
(* Cyclic Group Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
*)
(* Definitions and Theorems (# are exported):

   Helper Theroems:

   Cyclic Group has a generator:
   cyclic_def              |- !g. cyclic g <=> Group g /\ ?z. z IN G /\ !x. x IN G ==> ?n. x = z ** n
   cyclic_gen_def          |- !g. cyclic g ==> cyclic_gen g IN G /\
                                           !x. x IN G ==> ?n. x = cyclic_gen g ** n
#  cyclic_group            |- !g. cyclic g ==> Group g
   cyclic_element          |- !g. cyclic g ==> !x. x IN G ==> ?n. x = cyclic_gen g ** n
   cyclic_gen_element      |- !g. cyclic g ==> cyclic_gen g IN G
   cyclic_generated_group  |- !g. FiniteGroup g ==> !x. x IN G ==> cyclic (gen x)
   cyclic_gen_order        |- !g. cyclic g /\ FINITE G ==> (ord (cyclic_gen g) = CARD G)
   cyclic_gen_power_order  |- !g. cyclic g /\ FINITE G ==> !n. 0 < n /\ (CARD G MOD n = 0) ==>
                                              (ord (cyclic_gen g ** (CARD G DIV n)) = n)

   cyclic_generated_by_gen         |- !g. cyclic g /\ FINITE G ==> (g = gen (cyclic_gen g))
   cyclic_element_by_gen           |- !g. cyclic g /\ FINITE G ==>
                                      !x. x IN G ==> ?n. n < CARD G /\ (x = cyclic_gen g ** n)
   cyclic_element_in_generated     |- !g. cyclic g /\ FINITE G ==>
                                      !x. x IN G ==> x IN (Gen (cyclic_gen g ** (CARD G DIV ord x)))
   cyclic_finite_has_order_divisor |- !g. cyclic g /\ FINITE G ==>
                                      !n. n divides CARD G ==> ?x. x IN G /\ (ord x = n)

   Cyclic Group Properties:
   cyclic_finite_alt           |- !g. FiniteGroup g ==> (cyclic g <=> ?z. z IN G /\ (ord z = CARD G))
   cyclic_group_comm           |- !g. cyclic g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x)
   cyclic_group_abelian        |- !g. cyclic g ==> AbelianGroup g

   Cyclic Subgroups:
   cyclic_subgroup_cyclic      |- !g h. cyclic g /\ h <= g ==> cyclic h
   cyclic_subgroup_condition   |- !g. cyclic g /\ FINITE G ==>
                                  !n. (?h. h <= g /\ (CARD H = n)) <=> n divides CARD G

   Cyclic Group Examples:
   cyclic_uroots_has_primitive |- !g. FINITE G /\ cyclic g ==>
                                  !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)
   cyclic_uroots_cyclic        |- !g. cyclic g ==> !n. cyclic (uroots n)
   add_mod_order_1             |- !n. 1 < n ==> (order (add_mod n) 1 = n)
   add_mod_cylic               |- !n. 0 < n ==> cyclic (add_mod n)

   Cyclic Generators:
   cyclic_generators_def       |- !g. cyclic_generators g = {z | z IN G /\ (ord z = CARD G)}
   cyclic_generators_element   |- !g z. z IN cyclic_generators g <=> z IN G /\ (ord z = CARD G)
   cyclic_generators_subset    |- !g. cyclic_generators g SUBSET G
   cyclic_generators_finite    |- !g. FINITE G ==> FINITE (cyclic_generators g)
   cyclic_generators_nonempty  |- !g. cyclic g /\ FINITE G ==> cyclic_generators g <> {}
   cyclic_generators_coprimes_bij |- !g. cyclic g /\ FINITE G ==>
                          BIJ (\j. cyclic_gen g ** j) (coprimes (CARD G)) (cyclic_generators g)
   cyclic_generators_card      |- !g. cyclic g /\ FINITE G ==> (CARD (cyclic_generators g) = phi (CARD G))
   cyclic_generators_gen_cofactor_eq_orders  |- !g. cyclic g /\ FINITE G ==> !n. n divides CARD G ==>
                          (cyclic_generators (Generated g (cyclic_gen g ** (CARD G DIV n))) = orders g n)
   cyclic_orders_card          |- !g. cyclic g /\ FINITE G ==>
                                  !n. CARD (orders g n) = if n divides CARD G then phi n else 0

   Partition by order equality:
   eq_order_def            |- !g x y. eq_order g x y <=> (ord x = ord y)
   eq_order_equiv          |- !g. eq_order g equiv_on G
   cyclic_orders_nonempty  |- !g. cyclic g /\ FINITE G ==> !n. n divides CARD G ==> orders g n <> {}
   cyclic_eq_order_partition         |- !g. cyclic g /\ FINITE G ==>
                                        (partition (eq_order g) G = {orders g n | n | n divides CARD G})
   cyclic_eq_order_partition_alt     |- !g. cyclic g /\ FINITE G ==>
                                        (partition (eq_order g) G = {orders g n | n | n IN divisors (CARD G)})
   cyclic_eq_order_partition_by_card |- !g. cyclic g /\ FINITE G ==>
                                        (IMAGE CARD (partition (eq_order g) G) = IMAGE phi (divisors (CARD G)))

   eq_order_is_feq_order           |- !g. eq_order g = feq ord
   orders_is_feq_class_order       |- !g. orders g = feq_class ord G
   cyclic_image_ord_is_divisors    |- !g. cyclic g /\ FINITE G ==> (IMAGE ord G = divisors (CARD G))
   cyclic_orders_partition         |- !g. cyclic g /\ FINITE G ==>
                                          (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G)))

   Finite Cyclic Group Existence:
   finite_cyclic_group_existence   |- !n. 0 < n ==> ?g. cyclic g /\ (CARD g.carrier = n)

   Cyclic Group index relative to a generator:
   cyclic_index_exists             |- !g x. cyclic g /\ x IN G ==>
                                      ?n. (x = cyclic_gen g ** n) /\ (FINITE G ==> n < CARD G)
   cyclic_index_def                |- !g x. cyclic g /\ x IN G ==>
                                      (x = cyclic_gen g ** cyclic_index g x) /\
                                      (FINITE G ==> cyclic_index g x < CARD G)
   finite_cyclic_index_property    |- !g. cyclic g /\ FINITE G ==>
                                      !n. n < CARD G ==> (cyclic_index g (cyclic_gen g ** n) = n)
   finite_cyclic_index_unique      |- !g x. cyclic g /\ FINITE G /\ x IN G ==>
                                      !n. n < CARD G ==> ((x = cyclic_gen g ** n) <=> (n = cyclic_index g x))
   finite_cyclic_index_add         |- !g x y. cyclic g /\ FINITE G /\ x IN G /\ y IN G ==>
                                      (cyclic_index g (x * y) =
                                         (cyclic_index g x + cyclic_index g y) MOD CARD G)

   Finite Cyclic Group Uniqueness:
   finite_cyclic_group_homo          |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2
   finite_cyclic_group_bij           |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier
   finite_cyclic_group_iso           |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupIso (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2
   finite_cyclic_group_uniqueness    |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      ?f. GroupIso f g1 g2
   finite_cyclic_group_add_mod_homo  |- !g. cyclic g /\ FINITE G ==>
      GroupHomo (\n. cyclic_gen g ** n) (add_mod (CARD G)) g
   finite_cyclic_group_add_mod_bij   |- !g. cyclic g /\ FINITE G ==>
      BIJ (\n. cyclic_gen g ** n) (add_mod (CARD G)).carrier G
   finite_cyclic_group_add_mod_iso   |- !g. cyclic g /\ FINITE G ==>
      GroupIso (\n. cyclic_gen g ** n) (add_mod (CARD G)) g

   Isomorphism between Cyclic Groups:
   cyclic_iso_gen     |- !g h f. cyclic g /\ cyclic h /\ FINITE G /\ GroupIso f g h ==>
                                 f (cyclic_gen g) IN cyclic_generators h
*)

(* ------------------------------------------------------------------------- *)
(* Cyclic Group has a generator.                                             *)
(* ------------------------------------------------------------------------- *)

(* Define Cyclic Group *)
val cyclic_def = Define`
  cyclic (g:'a group) <=> Group g /\ ?z. z IN G /\ (!x. x IN G ==> ?n. x = z ** n)
`;

(* Apply Skolemization *)
val lemma = prove(
  ``!(g:'a group). ?z. cyclic g ==> z IN G /\ !x. x IN G ==> ?n. x = z ** n``,
  metis_tac[cyclic_def]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define cyclic generator *)
(*
- SIMP_RULE bool_ss [SKOLEM_THM] lemma;
> val it = |- ?f. !g. cyclic g ==> f g IN G /\ !x. x IN G ==> ?n. x = f g ** n: thm
*)
val cyclic_gen_def = new_specification(
    "cyclic_gen_def",
    ["cyclic_gen"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
> val cyclic_gen_def = |-
  !g. cyclic g ==> cyclic_gen g IN G /\ !x. x IN G ==> ?n. x = cyclic_gen g ** n: thm
*)

(* Theorem: cyclic g ==> Group g *)
(* Proof: by cyclic_def *)
val cyclic_group = store_thm(
  "cyclic_group",
  ``!g:'a group. cyclic g ==> Group g``,
  rw[cyclic_def]);

(* export simple result *)
val _ = export_rewrites ["cyclic_group"];

(* Theorem: cyclic g ==> !x. x IN G ==> ?n. x = (cyclic_gen g) ** n *)
(* Proof: by cyclic_gen_def. *)
val cyclic_element = store_thm(
  "cyclic_element",
  ``!g:'a group. cyclic g ==> (!x. x IN G ==> ?n. x = (cyclic_gen g) ** n)``,
  rw[cyclic_gen_def]);

(* Theorem cyclic g ==> (cyclic_gen g) IN G *)
(* Proof: by cyclic_gen_def. *)
val cyclic_gen_element = store_thm(
  "cyclic_gen_element",
  ``!g:'a group. cyclic g ==> (cyclic_gen g) IN G``,
  rw[cyclic_gen_def]);

(* Theorem: FiniteGroup g ==> !x. x IN G ==> cyclic (gen x) *)
(* Proof:
   By cyclic_def, this is to show:
   (1) x IN G ==> Group (gen x)
       True by generated_group.
   (2) ?z. z IN (Gen x) /\ !x'. x' IN (Gen x) ==> ?n. x' = (gen x).exp z n
       x IN (Gen x)   by generated_gen_element
       Let z = x, the assertion is true by generated_element
*)
val cyclic_generated_group = store_thm(
  "cyclic_generated_group",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> cyclic (gen x)``,
  rpt strip_tac >>
  `Group g /\ FINITE G` by metis_tac[FiniteGroup_def] >>
  rw[cyclic_def] >-
  rw[generated_group] >>
  `x IN (Gen x)` by rw[generated_gen_element] >>
  metis_tac[generated_subgroup, generated_element, subgroup_exp, subgroup_element]);

(* Theorem: cyclic g /\ FINITE G ==> ord (cyclic_gen g) = CARD G *)
(* Proof:
   Let z = cyclic_gen g.
   !x. x IN G ==> ?n. x = z ** n     by cyclic_element
              ==> x IN (Gen z)       by generated_element
   Hence G SUBSET (Gen z)            by SUBSET_DEF
   But (gen z) <= g                  by generated_subgroup
   So  (Gen z) SUBSET G              by Subgroup_def
   Hence (Gen z) = G                 by SUBSET_ANTISYM
   or ord z = CARD (Gen z)           by generated_group_card, group_order_pos
            = CARD G                 by above
*)
val cyclic_gen_order = store_thm(
  "cyclic_gen_order",
  ``!g:'a group. cyclic g /\ FINITE G ==> (ord (cyclic_gen g) = CARD G)``,
  rpt strip_tac >>
  `Group g /\ cyclic_gen g IN G /\ !x. x IN G ==> ?n. x = cyclic_gen g ** n` by rw[cyclic_gen_def] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  `G SUBSET (Gen (cyclic_gen g))` by rw[generated_element, SUBSET_DEF] >>
  `(Gen (cyclic_gen g)) SUBSET G` by metis_tac[generated_subgroup, Subgroup_def] >>
  metis_tac[generated_group_card, group_order_pos, SUBSET_ANTISYM]);

(* Theorem: cyclic g /\ FINITE G ==>
           !n. 0 < n /\ ((CARD G) MOD n = 0) ==> (ord (cyclic_gen g ** (CARD G DIV n)) = n) *)
(* Proof:
   First, Group g                           by cyclic_group
   Therefore  FiniteGroup g                 by FiniteGroup_def
   Let t = (cyclic_gen g) ** m, where m = (CARD G) DIV n.
   Since (cyclic_gen g) IN G                by cyclic_gen_element
      so t IN G                             by group_exp_element
   Since ord (cyclic_gen g) = CARD G        by cyclic_gen_order
      so ord t * gcd (CARD G) m = CARD G    by group_order_power

     But CARD G
       = m * n + ((CARD G) MOD n)           by DIVISION
       = m * n                              since (CARD G) MOD n = 0
       = n * m                              by MULT_COMM
      so gcd (CARD G) m = m                 by GCD_MULTIPLE_ALT

     But CARD G <> 0                        by group_carrier_nonempty, CARD_EQ_0
      so m = (CARD G) DIV n <> 0            by GCD_EQ_0
   Therefore  ord t * m = n * m
          or  ord t = n                     by MULT_RIGHT_CANCEL
*)
val cyclic_gen_power_order = store_thm(
  "cyclic_gen_power_order",
  ``!g:'a group. cyclic g /\ FINITE G ==>
   !n. 0 < n /\ ((CARD G) MOD n = 0) ==> (ord (cyclic_gen g ** (CARD G DIV n)) = n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  qabbrev_tac `m = (CARD G) DIV n` >>
  qabbrev_tac `t = (cyclic_gen g) ** m` >>
  `(cyclic_gen g) IN G` by rw[cyclic_gen_element] >>
  `t IN G` by rw[Abbr`t`] >>
  `ord (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  `ord t * gcd (CARD G) m = CARD G` by metis_tac[group_order_power] >>
  `CARD G = m * n + ((CARD G) MOD n)` by rw[DIVISION, Abbr`m`] >>
  `_ = n * m` by rw[MULT_COMM] >>
  `gcd (CARD G) m = m` by metis_tac[GCD_MULTIPLE_ALT] >>
  `m <> 0` by metis_tac[group_carrier_nonempty, CARD_EQ_0, GCD_EQ_0] >>
  metis_tac[MULT_RIGHT_CANCEL]);

(* Theorem: cyclic g ==> (g = (gen (cyclic_gen g))) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
   Let z = cyclic_gen g.
   Then z IN G                    by cyclic_gen_element
    and (Gen z) SUBSET G          by generated_subset
   Now, show: G SUBSET (Gen z)
     or show: x IN G ==> x IN (Gen z)   by SUBSET_DEF
       Since cyclic g and x IN G,
             ?j. x = z ** j       by cyclic_gen_def
       hence x IN x IN (Gen z)    by generated_element

   Thus (Gen z) SUBSET G
    and G SUBSET (Gen z)
    ==> G = Gen z                 by SUBSET_ANTISYM
   also (gen z).op = $*
    and (gen z).id = #e           by generated_property
   Therefore g = (gen z)          by monoid_component_equality
*)
val cyclic_generated_by_gen = store_thm(
  "cyclic_generated_by_gen",
  ``!g:'a group. cyclic g ==> (g = (gen (cyclic_gen g)))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `(Gen z) SUBSET G` by rw[generated_subset] >>
  `G SUBSET (Gen z)` by metis_tac[SUBSET_DEF, cyclic_gen_def, generated_element] >>
  `G = Gen z` by rw[SUBSET_ANTISYM] >>
  metis_tac[monoid_component_equality, generated_property]);

(* Theorem: cyclic g /\ FINITE G ==> !x. x IN G ==>
            ?n. n < CARD G /\ (x = (cyclic_gen g) ** n) *)
(* Proof:
   Since cyclic g ==> Group g    by cyclic_group
      so FiniteGroup g           by FiniteGroup_def
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                   by cyclic_gen_element
    and 0 < m                    by finite_group_card_pos
   also ord z = m                by cyclic_gen_order
    Now ?k. x = z ** k           by cyclic_element
   Since k MOD m < m             by MOD_LESS
     and z ** k = z (k MOD m)    by group_exp_mod, 0 < m
   Just take n = k MOD m.
*)
val cyclic_element_by_gen = store_thm(
  "cyclic_element_by_gen",
  ``!g:'a group. cyclic g /\ FINITE G ==> !x. x IN G ==>
     ?n. n < CARD G /\ (x = (cyclic_gen g) ** n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `?k. x = z ** k` by rw[cyclic_element, Abbr`z`] >>
  qexists_tac `k MOD m` >>
  metis_tac[group_exp_mod, MOD_LESS]);

(* Theorem: cyclic g /\ FINITE G ==> !x. x IN G ==>
            x IN (Gen ((cyclic_gen g) ** ((CARD G) DIV (ord x)))) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
    and 0 < m                     by finite_group_card_pos
   Let n = ord x, k = m DIV n, y = z ** k.
   To show: x IN (Gen y)
   Note n divides m               by group_order_divides
   Since x IN G,
         ?t. x = z ** t           by cyclic_element
     But x ** n = #e              by order_property
      or (z ** t) ** n = #e       by x = z ** t
      or  z ** (t * n) = #e       by group_exp_mult
    Thus m divides (t * n)        by group_order_divides_exp, m = ord z
      so k divides t              by dividend_divides_divisor_multiple, n divides m
   Hence ?s. t = s * k            by divides_def
     and x = z ** t
           = z ** (s * k)         by t = s * k
           = z ** (k * s)         by MULT_COMM
           = (z ** k) ** s        by group_exp_mult
           = y ** s               by y = z ** k
   Therefore x IN (Gen y)         by generated_element
*)
val cyclic_element_in_generated = store_thm(
  "cyclic_element_in_generated",
  ``!g:'a group. cyclic g /\ FINITE G ==> !x. x IN G ==>
        x IN (Gen ((cyclic_gen g) ** ((CARD G) DIV (ord x))))``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `m = CARD G` >>
  qabbrev_tac `z = cyclic_gen g` >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `z IN G /\ (ord z = m)` by rw[GSYM cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `k = m DIV n` >>
  qabbrev_tac `y = z ** k` >>
  `n divides m` by rw[group_order_divides, Abbr`n`, Abbr`m`] >>
  `?t. x = z ** t` by rw[cyclic_element, Abbr`z`] >>
  `x ** n = #e` by rw[order_property, Abbr`n`] >>
  `z ** (t * n) = #e` by rw[group_exp_mult] >>
  `m divides (t * n)` by rw[GSYM group_order_divides_exp] >>
  `k divides t` by rw[GSYM dividend_divides_divisor_multiple, Abbr`k`] >>
  `?s. t = s * k` by rw[GSYM divides_def] >>
  `x = y ** s` by metis_tac[group_exp_mult, MULT_COMM] >>
  metis_tac[generated_element]);

(* Theorem: cyclic g /\ FINITE G ==> !n. n divides CARD G ==> ?x. x IN G /\ (ord x = n) *)
(* Proof:
   Note cyclic g ==> Group g                    by cyclic_group
    and Group g /\ FINITE G ==> FiniteGroup g   by FiniteGroup_def
      Let z = cyclic_gen g, m = CARD G.
      Note 0 < m                                by finite_group_card_pos
      Then z IN G                               by cyclic_gen_element
       and ord z = m                            by cyclic_gen_order
      Let x = z ** (m DIV n),
      Then x IN G                               by group_exp_element
       and ord x = n                            by group_order_exp_cofactor, 0 < m
*)
val cyclic_finite_has_order_divisor = store_thm(
  "cyclic_finite_has_order_divisor",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. n divides CARD G ==> ?x. x IN G /\ (ord x = n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  qabbrev_tac `x = z ** (m DIV n)` >>
  metis_tac[group_order_exp_cofactor, group_exp_element]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Group Properties                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteGroup g ==> cyclic g <=> ?z. z IN G /\ (ord z = CARD G) *)
(* Proof:
   If part: cyclic g ==> ?z. z IN G /\ (ord z = CARD G)
     Let z = cyclic_gen g.
     cyclic g ==> z IN G                          by cyclic_gen_element
     cyclic g /\ FINITE G ==>  (ord z = CARD G)   by cyclic_gen_order
   Only-if part: ?z. z IN G /\ (ord z = CARD G) ==> cyclic g
     Note 0 < CARD G                      by finite_group_card_pos
     (Gen z) SUBSET G                     by generated_subset
     CARD (Gen z) = ord z                 by generated_group_card
     (Gen z) = G                          by SUBSET_EQ_CARD
     Thus !x. x IN G ==> ?n. x = z ** n   by generated_element
*)
val cyclic_finite_alt = store_thm(
  "cyclic_finite_alt",
  ``!g:'a group. FiniteGroup g ==> (cyclic g <=> (?z. z IN G /\ (ord z = CARD G)))``,
  rpt strip_tac >>
  `Group g /\ FINITE G` by metis_tac[FiniteGroup_def] >>
  rw[EQ_IMP_THM] >-
  metis_tac[cyclic_gen_element, cyclic_gen_order] >>
  rw[cyclic_def] >>
  qexists_tac `z` >>
  rw[] >>
  `(Gen z) SUBSET G` by metis_tac[generated_subset] >>
  `CARD (Gen z) = ord z` by rw[generated_group_card, finite_group_card_pos] >>
  `Gen z = G` by metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE] >>
  metis_tac[generated_element]);

(* Theorem: cyclic g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) *)
(* Proof:
   Let z = cyclic_gen g.
   x IN G ==> ?n. x = z ** n     by cyclic_element
   y IN G ==> ?m. y = z ** m     by cyclic_element
     x * y
   = (z ** n) * (z ** m)
   = z ** (n + m)                by group_exp_add
   = z ** (m + n)                by ADD_COMM
   = (z ** m) * (z ** n)         by group_exp_add
   = y * x
*)
val cyclic_group_comm = store_thm(
  "cyclic_group_comm",
  ``!g:'a group. cyclic g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x)``,
  metis_tac[cyclic_group, cyclic_gen_def, cyclic_element, group_exp_add, ADD_COMM]);;

(* Theorem: cyclic g ==> AbelianGroup g *)
(* Proof: by cyclic_group_comm, cyclic_group, AbelianGroup_def *)
val cyclic_group_abelian = store_thm(
  "cyclic_group_abelian",
  ``!g:'a group. cyclic g ==> AbelianGroup g``,
  rw[cyclic_group_comm, AbelianGroup_def]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Subgroups                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cyclic g /\ h <= g ==> cyclic h *)
(* Proof:
   Let z = cyclic_gen g.
   h <= g <=> Group h /\ Group g /\ H SUBSET G     by Subgroup_def
   Hence H <> {}                                   by group_carrier_nonempty
   and #e IN H                                     by group_id_element, subgroup_id
   If H = {#e},
      !x. x IN H ==> x = #e, #e ** 1 = #e          by group_exp_1, IN_SING
      Hence cyclic h                               by cyclic_def
   If H <> {#e}, there is an x IN H and x <> #e    by ONE_ELEMENT_SING
   !x. x IN H ==> x IN G                           by SUBSET_DEF
              ==> ?n. x = z ** n                   by cyclic_element
   Let m = MIN_SET {n | 0 < n /\ z ** n IN H}
   Let s = z ** m, s IN H                          by group_exp_element
   Then for any x IN H, ?n. x = z ** n             by above
   Now n = q * m + r                               by DIVISION
   x = z ** n
     = z ** (q * m + r)
     = z ** q * m  * z ** r                        by group_comm_op_exp
     = (z ** m) ** q * z ** r                      by group_exp_mult, MULT_COMM
     = s ** q * z ** r
   Hence z ** r = |/ (s ** q) * x                  by group_rsolve
   or z ** r IN H                                  by group_op_element, group_exp_element
   But 0 <= r < m, and m is minimum.
   Hence r = 0, or z ** r = #e                     by group_exp_0
   Therefore for any x IN H, ?q. x = s ** q.
   Result follows by cyclic_def.
*)
val cyclic_subgroup_cyclic = store_thm(
  "cyclic_subgroup_cyclic",
  ``!g h:'a group. cyclic g /\ h <= g ==> cyclic h``,
  rpt strip_tac >>
  `Group g /\ (cyclic_gen g) IN G` by rw[cyclic_gen_def] >>
  `Group h /\ (h.op = g.op) /\ !x. x IN H ==> x IN G` by metis_tac[Subgroup_def, SUBSET_DEF] >>
  qabbrev_tac `z = cyclic_gen g` >>
  `H <> {}` by rw[group_carrier_nonempty] >>
  `#e IN H` by metis_tac[subgroup_id, group_id_element] >>
  `!x. x IN H ==> ?n. x = z ** n` by rw[cyclic_element, Abbr`z`] >>
  `!x. x IN H ==> !n. h.exp x n = x ** n` by rw[subgroup_exp] >>
  `!x. x IN H ==> (h.inv x = |/ x)` by rw[subgroup_inv] >>
  rw[cyclic_def] >>
  Cases_on `H = {#e}` >-
  rw[] >>
  `?x. x IN H /\ x <> #e` by metis_tac[ONE_ELEMENT_SING] >>
  `?n. x = z ** n` by rw[] >>
  `n <> 0` by metis_tac[group_exp_0] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `s = {n | 0 < n /\ z ** n IN H}` >>
  `n IN s` by rw[Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `MIN_SET s IN s /\ !n. n IN s ==> MIN_SET s <= n` by metis_tac[MIN_SET_LEM] >>
  qabbrev_tac `m = MIN_SET s` >>
  `!n. n IN s <=> 0 < n /\ z ** n IN H` by rw[Abbr`s`] >>
  `0 < m /\ z ** m IN H` by metis_tac[] >>
  qexists_tac `z ** m` >>
  rw[] >>
  `?n'. x' = z ** n'` by rw[] >>
  `?q r. ?r q. (n' = q * m + r) /\ r < m` by rw[DA] >>
  `x' = z ** (q * m + r)` by rw[] >>
  `_ = z ** (q * m) * z ** r` by rw[group_exp_add] >>
  `_ = z ** (m * q) * z ** r` by metis_tac[MULT_COMM] >>
  `_ = (z ** m) ** q * z ** r` by metis_tac[group_exp_mult] >>
  `(z ** m) ** q IN H` by metis_tac[group_exp_element] >>
  Cases_on `r = 0` >-
  metis_tac[group_exp_0, group_rid] >>
  `0 < r` by decide_tac >>
  `|/ ((z ** m) ** q) IN H` by metis_tac[group_inv_element] >>
  `z ** r IN H` by metis_tac[group_rsolve, group_exp_element, group_op_element] >>
  `m <= r` by metis_tac[] >>
  `~(r < m)` by decide_tac);

(* Theorem: cyclic g /\ FINITE G ==> !n. (?h. h <= g /\ (CARD H = n)) <=> (n divides (CARD G)) *)
(* Proof:
   If part: h <= g ==> CARD H divides CARD G
      True by Lagrange_thm.
   Only-if part: n divides CARD G ==> ?h. h <= g /\ (CARD H = n)
      Let z = cyclic_gen g, m = CARD G.
      Then z IN G          by cyclic_gen_element
       and (ord z = m)     by cyclic_gen_order
      Since n divides m,
            ?k. m = k * n  by divides_def
       Thus k divides m    by divides_def, MULT_COMM
        and gcd k m = k    by divides_iff_gcd_fix
       Note Group g        by cyclic_group
        and FiniteGroup g  by FiniteGroup_def, FINITE G.
       Let x = z ** k,
       Then x IN G                    by group_exp_element
        and n * k
          = m                         by MULT_COMM, m = k * n
          = ord (z ** k) * gcd m k    by group_order_power
          = ord x * gcd k m           by GCD_SYM
          = ord x * k                 by above
       Since 0 < m, m <> 0            by finite_group_card_pos
          so k <> 0 and n <> 0        by MULT_EQ_0
        thus ord x = n                by EQ_MULT_RCANCEL, k <> 0
        Take h = gen x,
        then h <= g                   by generated_subgroup
         and CARD (Gen x)
           = ord x = n                by generated_group_card
*)
val cyclic_subgroup_condition = store_thm(
  "cyclic_subgroup_condition",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. (?h. h <= g /\ (CARD H = n)) <=> (n divides (CARD G))``,
  rw[EQ_IMP_THM] >-
  rw[Lagrange_thm] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `?k. m = k * n` by rw[GSYM divides_def] >>
  `k divides m` by metis_tac[divides_def, MULT_COMM] >>
  `gcd k m = k` by rw[GSYM divides_iff_gcd_fix] >>
  qabbrev_tac `x = z ** k` >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  `ord x * k = n * k` by metis_tac[group_order_power, GCD_SYM, MULT_COMM] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `m <> 0` by decide_tac >>
  `k <> 0 /\ n <> 0` by metis_tac[MULT_EQ_0] >>
  `ord x = n` by metis_tac[EQ_MULT_RCANCEL] >>
  `x IN G` by rw[Abbr`x`] >>
  qexists_tac `gen x` >>
  metis_tac[generated_subgroup, generated_group_card, NOT_ZERO_LT_ZERO]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Group Examples                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE G /\ cyclic g ==>
            !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)  *)
(* Proof:
       cyclic g
   ==> AbelianGroup g       by cyclic_group_abelian
   ==> (uroots n) <= g      by group_uroots_subgroup
   ==> cyclic (uroots n)    by cyclic_subgroup_cyclic
   ==> (cyclic_gen (uroots n)) IN (uroots n).carrier
                            by cyclic_gen_element
   ==> ord (cyclic_gen (uroots n)) = CARD (uroots n)
                            by cyclic_gen_order, subgroup_order
*)
val cyclic_uroots_has_primitive = store_thm(
  "cyclic_uroots_has_primitive",
  ``!g:'a group. FINITE G /\ cyclic g ==>
     !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `AbelianGroup g` by rw[cyclic_group_abelian] >>
  `(uroots n) <= g` by rw[group_uroots_subgroup] >>
  `cyclic (uroots n)` by metis_tac[cyclic_subgroup_cyclic] >>
  `(cyclic_gen (uroots n)) IN (uroots n).carrier` by rw[cyclic_gen_element] >>
  metis_tac[cyclic_gen_order, subgroup_order, Subgroup_def, SUBSET_FINITE]);

(* This cyclic_uroots_has_primitive, originally for the next one, is not used. *)

(* Theorem: cyclic g ==> cyclic (uroots n) *)
(* Proof:
   Note AbelianGroup g           by cyclic_group_abelian
    and (uroots n) <= g          by group_uroots_subgroup
   Thus cyclic (uroots n)        by cyclic_subgroup_cyclic
*)
val cyclic_uroots_cyclic = store_thm(
  "cyclic_uroots_cyclic",
  ``!g:'a group. cyclic g ==> !n. cyclic (uroots n)``,
  rpt strip_tac >>
  `AbelianGroup g` by rw[cyclic_group_abelian] >>
  `(uroots n) <= g` by rw[group_uroots_subgroup] >>
  metis_tac[cyclic_subgroup_cyclic]);

(* Theorem: 1 < n ==> (order (add_mod n) 1 = n) *)
(* Proof:
   Since 1 IN (add_mod n).carrier             by add_mod_element, 1 < n
     and !m. (add_mod n).exp 1 m = m MOD n    by add_mod_exp, 0 < n
   Therefore,
         (add_mod n).exp 1 n = n MOD n = 0    by DIVMOD_ID, 0 < n
     and !m. 0 < m /\ m < n,
         (add_mod n).exp 1 m = m <> 0         by NOT_ZERO_LT_ZERO, 0 < n
     Now (add_mod n).id = 0                   by add_mod_property
      so order (add_mod n) 1 = n              by group_order_thm
*)
val add_mod_order_1 = store_thm(
  "add_mod_order_1",
  ``!n. 1 < n ==> (order (add_mod n) 1 = n)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `!m. (add_mod n).exp 1 m = m MOD n` by rw[add_mod_exp] >>
  `1 IN (add_mod n).carrier` by rw[add_mod_element] >>
  `(add_mod n).exp 1 n = 0` by rw[] >>
  `!m. 0 < m /\ m < n ==> (add_mod n).exp 1 m <> 0` by rw[NOT_ZERO_LT_ZERO] >>
  metis_tac[group_order_thm, add_mod_property]);

(* Theorem: 0 < n ==> cyclic (add_mod n) *)
(* Proof:
   Note Group (add_mod n)                  by add_mod_group
    and FiniteGroup (add_mod n)            by add_mod_finite_group
    and (add_mod n).id = 0                 by add_mod_property
    and CARD (add_mod n).carrier = n       by add_mod_property
   If n = 1,
      Since order (add_mod 1) 0 = 1        by group_order_id
        and 0 IN (add_mod 1).carrier       by group_id_element
        and CARD (add_mod 1).carrier = 1   by above
       Thus cyclic (add_mod 1)             by cyclic_finite_alt
   If n <> 1, 1 < n.
      Since 1 IN (add_mod n).carrier       by add_mod_element, 1 < n
        and order (add_mod n) 1 = n        by add_mod_order_1, 1 < n
       Thus cyclic (add_mod n)             by cyclic_finite_alt
*)
val add_mod_cylic = store_thm(
  "add_mod_cylic",
  ``!n. 0 < n ==> cyclic (add_mod n)``,
  rpt strip_tac >>
  `Group (add_mod n)` by rw[add_mod_group] >>
  `FiniteGroup (add_mod n)` by rw[add_mod_finite_group] >>
  `((add_mod n).id = 0) /\ (CARD (add_mod n).carrier = n)` by rw[add_mod_property] >>
  Cases_on `n = 1` >-
  metis_tac[cyclic_finite_alt, group_order_id, group_id_element] >>
  `1 < n` by decide_tac >>
  metis_tac[cyclic_finite_alt, add_mod_order_1, add_mod_element]);

(* ------------------------------------------------------------------------- *)
(* Order of elements in a Cyclic Group                                       *)
(* ------------------------------------------------------------------------- *)

(*
From FiniteField theory, knowing that F* is cyclic, we can prove stronger results:
(1) Let G be cyclic with |G| = n, so it has a generator z with (order z = n).
(2) All elements in G are known: 1, g, g^2, ...., g^(n-1).
(3) Thus all their orders are known: n/gcd(0,n), n/gcd(1,n), n/gcd(2,n), ..., n/gcd(n-1,n).
(4) Counting, CARD (order_eq k) = phi k.
(5) As a result, n = SUM (phi k), over k | n.
*)

(* ------------------------------------------------------------------------- *)
(* Cyclic Generators                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define the set of generators for cyclic group *)
val cyclic_generators_def = Define `
    cyclic_generators (g:'a group) = {z | z IN G /\ (ord z = CARD G)}
`;

(* Theorem: z IN cyclic_generators g <=> z IN G /\ (ord z = CARD G) *)
(* Proof: by cyclic_generators_def *)
val cyclic_generators_element = store_thm(
  "cyclic_generators_element",
  ``!g:'a group. !z. z IN cyclic_generators g <=> z IN G /\ (ord z = CARD G)``,
  rw[cyclic_generators_def]);

(* Theorem: (cyclic_generators g) SUBSET G *)
(* Proof: by cyclic_generators_def, SUBSET_DEF *)
val cyclic_generators_subset = store_thm(
  "cyclic_generators_subset",
  ``!g:'a group. (cyclic_generators g) SUBSET G``,
  rw[cyclic_generators_def, SUBSET_DEF]);

(* Theorem: FINITE G ==> FINITE (cyclic_generators g) *)
(* Proof: by cyclic_generators_subset, SUBSET_FINITE *)
val cyclic_generators_finite = store_thm(
  "cyclic_generators_finite",
  ``!g:'a group. FINITE G ==> FINITE (cyclic_generators g)``,
  metis_tac[cyclic_generators_subset, SUBSET_FINITE]);

(* Theorem: cyclic g /\ FINITE G ==> (cyclic_generators g) <> {} *)
(* Proof:
   Let z = cyclic_gen g, m = CARD G.
    Then z IN G                        by cyclic_gen_element
     and ord z = m                     by cyclic_gen_order, FINITE G
   Hence z IN cyclic_generators g      by cyclic_generators_element
      or (cyclic_generators g) <> {}   by MEMBER_NOT_EMPTY
*)
val cyclic_generators_nonempty = store_thm(
  "cyclic_generators_nonempty",
  ``!g:'a group. cyclic g /\ FINITE G ==> (cyclic_generators g) <> {}``,
  metis_tac[cyclic_generators_element, cyclic_gen_element, cyclic_gen_order, MEMBER_NOT_EMPTY]);

(* Theorem: cyclic g /\ FINITE G ==>
            BIJ (\j. (cyclic_gen g) ** j) (coprimes (CARD G)) (cyclic_generators g) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
    and 0 < m                     by finite_group_card_pos
   Expanding by BIJ_DEF, INJ_DEF, and SURJ_DEF, this is to show:
   (1) z IN G /\ (ord z = m) /\ j IN coprimes m ==> z ** j IN cyclic_generators g
       Since z ** j IN G                    by group_exp_element
         and coprime j m                    by coprimes_element
          so ord (z ** j) = m               by group_order_power_eq_order
       Hence z ** j IN cyclic_generators g  by cyclic_generators_element
   (2) z IN G /\ (ord z = m) /\ j IN coprimes m /\ j' IN coprimes m /\ z ** j = z ** j' ==> j = j'
       If m = 1,
          then coprimes 1 = {1}                  by coprimes_1
          hence j = 1 = j'                       by IN_SING
       If m <> 1, 1 < m.
          then j IN coprimes m ==> j < m         by coprimes_element_less
           and j' IN coprimes m ==> j' < m       by coprimes_element_less
          Therefore j = j'                       by group_exp_equal
   (3) same as (1)
   (4) z IN G /\ (ord z = m) /\ x IN cyclic_generators g ==> ?j. j IN coprimes m /\ (z ** j = x)
       Since x IN cyclic_generators g
         ==> x IN G /\ (ord x = m)               by cyclic_generators_element
        Also ?k. k < m /\ (x = z ** k)           by cyclic_element_by_gen
        If m = 1,
           then ord x = 1 ==> x = #e             by group_order_eq_1
           then ord z = 1 ==> z = #e             by group_order_eq_1
           Take j = 1,
           and 1 IN (coprimes 1)                 by coprimes_1, IN_SING
           with z ** 1 = x                       by group_exp_1
        If m <> 1,
           then x <> #e                          by group_order_eq_1
           thus k <> 0                           by group_exp_0
             so 0 < k, and k < m ==> k <= m      by LESS_IMP_LESS_OR_EQ
           Also ord (z ** k) = m ==> coprime k m by group_order_power_eq_order
           Take j = k, and j IN coprimes m       by coprimes_element
*)
val cyclic_generators_coprimes_bij = store_thm(
  "cyclic_generators_coprimes_bij",
  ``!g:'a group. cyclic g /\ FINITE G ==>
      BIJ (\j. (cyclic_gen g) ** j) (coprimes (CARD G)) (cyclic_generators g)``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    qabbrev_tac `m = ord z` >>
    `coprime j m` by metis_tac[coprimes_element] >>
    `z ** j IN G` by rw[] >>
    `ord (z ** j) = m` by metis_tac[group_order_power_eq_order] >>
    metis_tac[cyclic_generators_element],
    qabbrev_tac `m = ord z` >>
    Cases_on `m = 1` >-
    metis_tac[coprimes_1, IN_SING] >>
    `1 < m` by decide_tac >>
    metis_tac[coprimes_element_less, group_exp_equal],
    qabbrev_tac `m = ord z` >>
    `coprime j m` by metis_tac[coprimes_element] >>
    `z ** j IN G` by rw[] >>
    `ord (z ** j) = m` by metis_tac[group_order_power_eq_order] >>
    metis_tac[cyclic_generators_element],
    qabbrev_tac `m = ord z` >>
    `x IN G /\ (ord x = m)` by metis_tac[cyclic_generators_element] >>
    `?k. k < m /\ (x = z ** k)` by metis_tac[cyclic_element_by_gen] >>
    Cases_on `m = 1` >-
    metis_tac[group_order_eq_1, coprimes_1, IN_SING, group_exp_1] >>
    `x <> #e` by metis_tac[group_order_eq_1] >>
    `k <> 0` by metis_tac[group_exp_0] >>
    `0 < k /\ k <= m` by decide_tac >>
    metis_tac[group_order_power_eq_order, coprimes_element]
  ]);

(* Theorem: cyclic g /\ FINITE G ==> (CARD (cyclic_generators g) = phi (CARD G)) *)
(* Proof:
   Let z = cyclic_gen g, m = CARD G.
    Then z IN G                        by cyclic_gen_element
     and ord z = m                     by cyclic_gen_order
     Now BIJ (\j. z ** j) (coprimes m) (cyclic_generators g)   by cyclic_generators_coprimes_bij
   Since FINITE (coprimes m)           by coprimes_finite
     and FINITE (cyclic_generators g)  by cyclic_generators_finite
   Hence CARD (cyclic_generators g)
       = CARD (coprimes m)             by FINITE_BIJ_CARD_EQ
       = phi m                         by phi_def
*)
val cyclic_generators_card = store_thm(
  "cyclic_generators_card",
  ``!g:'a group. cyclic g /\ FINITE G ==> (CARD (cyclic_generators g) = phi (CARD G))``,
  rpt strip_tac >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `BIJ (\j. z ** j) (coprimes m) (cyclic_generators g)` by rw[cyclic_generators_coprimes_bij, Abbr`z`, Abbr`m`] >>
  `FINITE (coprimes m)` by rw[coprimes_finite] >>
  `FINITE (cyclic_generators g)` by rw[cyclic_generators_finite] >>
  metis_tac[phi_def, FINITE_BIJ_CARD_EQ]);

(*
Goolge: order of elements in a cyclic group.

Pattern of orders of elements in a cyclic group
http://math.stackexchange.com/questions/158281/pattern-of-orders-of-elements-in-a-cyclic-group

The number of elements of order d, where d is a divisor of n, is 'v(d).

Let G be a cyclic group of order n, and let a in G be a generator. Let d be a divisor of n.

Certainly, a^{n/d} is an element of G of order d (in other words, <a^{n/d}> is a subgroup of G of order d).
If a^{t} in G is an element of order d, then (a^{t})^{d} = e, hence n | td, and thus (n/d) | t.
This shows that a^{t} in <a^{n/d}>, and thus <a^{t}> = <a^{n/d}> (since they are both subgroups of order d).
Thus, there is exactly one subgroup, let's call it H_{d}, of G of order d, for each divisor d of n,
and all of these subgroups are themselves cyclic.

Any cyclic group of order d has phi(d) generators, i.e. there are phi(d) elements of order d in H_{d},
and hence there are phi(d) elements of order d in G. Here, phi is Euler's phi function.

This can be checked to make sense via the identity: n = SUM phi(d), over d | n.
*)

(* Theorem: cyclic g /\ FINITE G ==> !n. n divides (CARD G) ==>
            (cyclic_generators (Generated g ((cyclic_gen g) ** ((CARD G) DIV n))) = orders g n) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
    and 0 < m                     by finite_group_card_pos

   Let k = m DIV n, y = z ** k, h = Generated g y.
   Then y IN G                    by group_exp_element
    and h <= g                    by generated_subgroup, y IN G

   Expanding by cyclic_generators_def, orders_def, this is to show:
   (1) h <= g /\ x IN H ==> x IN G
       True by Subgroup_def, SUBSET_DEF.
   (2) h <= g /\ order h x = CARD H ==> ord x = n
       Note ord x = CARD H      by subgroup_order
                  = ord y       by generated_group_card, group_order_pos
                  = n           by group_order_exp_cofactor
   (3) h <= g /\ x IN G /\ (ord x) divides m ==> x IN H
       True by cyclic_element_in_generated.
   (4) h <= g /\ x IN G ==> order h x = CARD H
       Note x IN H              by cyclic_element_in_generated
        and (ord x) divides m   by group_order_divides
            order h x
          = ord x               by subgroup_order, x IN H
          = ord (z ** k)        by group_order_exp_cofactor, (ord x) divides m = ord z
          = ord y               by y = z ** k
          = CARD H              by generated_group_card, group_order_pos
*)
val cyclic_generators_gen_cofactor_eq_orders = store_thm(
  "cyclic_generators_gen_cofactor_eq_orders",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. n divides (CARD G) ==>
   (cyclic_generators (Generated g ((cyclic_gen g) ** ((CARD G) DIV n))) = orders g n)``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `m = CARD G` >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  qabbrev_tac `k = m DIV n` >>
  qabbrev_tac `y = z ** k` >>
  qabbrev_tac `h = Generated g y` >>
  `y IN G` by rw[Abbr`y`, Abbr`z`] >>
  `h <= g` by rw[generated_subgroup, Abbr`h`] >>
  rw[cyclic_generators_def, orders_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[Subgroup_def, SUBSET_DEF] >-
  metis_tac[subgroup_order, generated_group_card, group_order_exp_cofactor, group_order_pos] >-
  metis_tac[cyclic_element_in_generated] >>
  qabbrev_tac `m = ord z` >>
  qabbrev_tac `n = ord x` >>
  `x IN H` by metis_tac[cyclic_element_in_generated] >>
  `order h x = n` by rw[subgroup_order, Abbr`n`] >>
  `ord y = n` by rw[group_order_exp_cofactor, Abbr`m`, Abbr`y`, Abbr`k`] >>
  `CARD H = ord y` by rw[generated_group_card, group_order_pos, Abbr`h`] >>
  decide_tac);

(* Theorem: cyclic g /\ FINITE G ==>
            !n. CARD (orders g n) = if (n divides CARD G) then phi n else 0 *)
(* Proof:
   Let m = CARD G.
   Note 0 < m                     by finite_group_card_pos
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
   If n divides m, to show: CARD (orders g n) = phi n
      Let k = m DIV n, y = z ** k, h = Generated g y.
      Then y IN G                 by group_exp_element
       and ord y = n              by group_order_exp_cofactor
      also h <= g                 by generated_subgroup
       and CARD H = n             by generated_group_card, group_order_pos
      Also cyclic h               by cyclic_subgroup_cyclic
       and FINITE H               by finite_subgroup_carrier_finite
      Hence CARD (orders g n)
          = CARD (cyclic_generators h)  by cyclic_generators_gen_cofactor_eq_orders
          = phi n                       by cyclic_generators_card, FINITE H

   If ~(n divides m), to show: CARD (orders g n) = 0
      By contradiction, suppose CARD (orders g n) <> 0.
      Since FINITE (orders g n)       by orders_finite
         so orders g n <> {}          by CARD_EQ_0
       Thus ?x. x IN orders g n       by MEMBER_NOT_EMPTY
         or x IN G /\ (ord x = n)     by orders_element
        Now (ord x) divides m         by group_order_divides
        which contradicts ~(n divides m).
*)
val cyclic_orders_card = store_thm(
  "cyclic_orders_card",
  ``!g:'a group. cyclic g /\ FINITE G ==>
   !n. CARD (orders g n) = if (n divides CARD G) then phi n else 0``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  Cases_on `n divides m` >| [
    simp[] >>
    qabbrev_tac `k = m DIV n` >>
    qabbrev_tac `y = z ** k` >>
    qabbrev_tac `h = Generated g y` >>
    `y IN G` by rw[Abbr`y`] >>
    `ord y = n` by metis_tac[group_order_exp_cofactor] >>
    `h <= g` by rw[generated_subgroup, Abbr`h`] >>
    `CARD H = n` by rw[generated_group_card, group_order_pos, Abbr`h`] >>
    `cyclic h` by metis_tac[cyclic_subgroup_cyclic] >>
    `FINITE H` by metis_tac[finite_subgroup_carrier_finite] >>
    metis_tac[cyclic_generators_gen_cofactor_eq_orders, cyclic_generators_card],
    simp[] >>
    spose_not_then strip_assume_tac >>
    `FINITE (orders g n)` by rw[orders_finite] >>
    `orders g n <> {}` by rw[GSYM CARD_EQ_0] >>
    metis_tac[MEMBER_NOT_EMPTY, orders_element, group_order_divides]
  ]);

(* ------------------------------------------------------------------------- *)
(* Partition by order equality                                               *)
(* ------------------------------------------------------------------------- *)

(* Define a relation: eq_order *)
val eq_order_def = Define `
    eq_order (g:'a group) x y <=> (ord x = ord y)
`;

(* Theorem: (eq_order g) equiv_on G *)
(* Proof: by eq_order_def, equiv_on_def *)
val eq_order_equiv = store_thm(
  "eq_order_equiv",
  ``!g:'a group. (eq_order g) equiv_on G``,
  rw[eq_order_def, equiv_on_def]);

(* Theorem: cyclic g /\ FINITE G ==> !n. n divides CARD G ==> orders g n <> {} *)
(* Proof:
   Let z = cyclic_gen g, m = CARD G.
   Note 0 < m               by finite_group_card_pos
   Then z IN G              by cyclic_gen_element
    and ord z = m           by cyclic_gen_order
   Let x = z ** (m DIV n)
   Then x IN G              by group_exp_element
    and ord x = n           by group_order_exp_cofactor
     so x IN (orders g n)   by orders_element
   Thus orders g n <> {}    by MEMBER_NOT_EMPTY
*)
val cyclic_orders_nonempty = store_thm(
  "cyclic_orders_nonempty",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. n divides CARD G ==> orders g n <> {}``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  qabbrev_tac `x = z ** (m DIV n)` >>
  `x IN G` by rw[Abbr`x`] >>
  `ord x = n` by metis_tac[group_order_exp_cofactor] >>
  metis_tac[orders_element, MEMBER_NOT_EMPTY]);

(* Theorem: cyclic g /\ FINITE G ==>
            (partition (eq_order g) G = {orders g n | n | n divides (CARD G)}) *)
(* Proof:
   Expanding by partition_def, eq_order_def, orders_def, this is to show:
   (1) x' IN G /\ ... ==> ?n. ... (ord x' = n) ... /\ n divides CARD G
       Let n = ord x',
       Result is true since n divides CARD G   by group_order_divides
   (2) n divides CARD G /\ ... (ord x'' = n) ... ==> ?x'. x' IN G /\ ... (ord x' = ord x'') ...
       Since n divides CARD G
         ==> (orders g n) <> {}            by cyclic_orders_nonempty
         ==> ?z. z IN G /\ (ord z = n)     by orders_element, , MEMBER_NOT_EMPTY
       Let x' = z, then the result follows.
*)
val cyclic_eq_order_partition = store_thm(
  "cyclic_eq_order_partition",
  ``!g:'a group. cyclic g /\ FINITE G ==>
     (partition (eq_order g) G = {orders g n | n | n divides (CARD G)})``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  rw[partition_def, eq_order_def, orders_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[group_order_divides] >>
  metis_tac[orders_element, cyclic_orders_nonempty, MEMBER_NOT_EMPTY]);

(* Theorem: cyclic g /\ FINITE G ==>
            (partition (eq_order g) G = {orders g n | n | n IN divisors (CARD G)}) *)
(* Proof:
   Note Group g            by cyclic_group
     so FiniteGroup g      by FiniteGroup_def
    ==> 0 < CARD G         by finite_group_card_pos, FiniteGroup g
        partition (eq_order g) G
      = {orders g n | n | n divides (CARD G)}      by cyclic_eq_order_partition
      = {orders g n | n | n IN divisors (CARD G)}  by divisors_element_alt, 0 < CARD G
*)
val cyclic_eq_order_partition_alt = store_thm(
  "cyclic_eq_order_partition_alt",
  ``!g:'a group. cyclic g /\ FINITE G ==>
                (partition (eq_order g) G = {orders g n | n | n IN divisors (CARD G)})``,
  rpt strip_tac >>
  `0 < CARD G` by metis_tac[finite_group_card_pos, cyclic_group, FiniteGroup_def] >>
  rw[cyclic_eq_order_partition, divisors_element_alt]);

(* We have shown: in a finite cyclic group G,
   For each divisor d | |G|, there are phi(d) elements of order d.
   Since each element must have some order in a finite group,
   the sum of phi(d) over all divisors d will count all elements in the group,
   that is,  n = SUM phi(d), over d | n.
*)

(* Theorem: cyclic g /\ FINITE G ==>
            (IMAGE CARD (partition (eq_order g) g.carrier) = IMAGE phi (divisors (CARD G))) *)
(* Proof:
   Since cyclic g ==> Group g       by cyclic_group
      so FiniteGroup g              by FiniteGroup_def
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                      by cyclic_gen_element
    and ord z = m                   by cyclic_gen_order
    and 0 < m                       by finite_group_card_pos

   Apply partition_def, eq_order_def, to show:
   (1) ?x''. (CARD s = phi x'') /\ x'' IN divisors m
       Note s = orders g n         by orders_def
       Let n = ord x'', y = z ** (m DIV n).
       Then n divides m             by group_order_divides
        and y IN G                  by group_exp_element
        and ord y = n               by group_order_exp_cofactor
       Since 0 < m, n IN divisors m by divisors_element_alt
       hence CARD s = phi n         by cyclic_orders_card
       So take x'' = n.
   (2) x' IN divisors m ==> ?x''. (phi x' = CARD x'') /\ ?x. x IN orders g x'
       Let n = x', y = z ** (m DIV n).
       Since n IN divisors m,
         ==> n <= m /\ n divides m  by divisors_element
         Let s = orders g n,
        Then CARD s = phi n         by cyclic_orders_card
         and y IN G                 by group_exp_element
         and ord y = n              by group_order_exp_cofactor
          so y IN orders g n        by orders_element
       So take x'' = y.
*)
val cyclic_eq_order_partition_by_card = store_thm(
  "cyclic_eq_order_partition_by_card",
  ``!g:'a group. cyclic g /\ FINITE G ==>
      (IMAGE CARD (partition (eq_order g) g.carrier) = IMAGE phi (divisors (CARD G)))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `m = CARD G` >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  rw[partition_def, eq_order_def, EXTENSION, EQ_IMP_THM] >| [
    qabbrev_tac `m = ord z` >>
    qabbrev_tac `n = ord x''` >>
    (`x' = orders g n` by (rw[orders_def, EXTENSION] >> metis_tac[])) >>
    qabbrev_tac `y = z ** (m DIV n)` >>
    `n divides m` by metis_tac[group_order_divides] >>
    `y IN G` by rw[Abbr`y`] >>
    `ord y = n` by rw[group_order_exp_cofactor, Abbr`y`, Abbr`m`] >>
    metis_tac[cyclic_orders_card, divisors_element_alt],
    qabbrev_tac `m = ord z` >>
    qabbrev_tac `n = x'` >>
    qabbrev_tac `y = z ** (m DIV n)` >>
    `n <= m /\ n divides m` by metis_tac[divisors_element] >>
    `y IN G` by rw[Abbr`y`] >>
    `ord y = n` by rw[group_order_exp_cofactor, Abbr`y`, Abbr`m`] >>
    metis_tac[cyclic_orders_card, orders_element]
  ]);

(* Theorem: eq_order g = feq ord *)
(* Proof:
       eq_order g x y
   <=> ord x = ord y   by eq_order_def
   <=> feq ord x y     by feq_def
   Hence true by FUN_EQ_THM.
*)
val eq_order_is_feq_order = store_thm(
  "eq_order_is_feq_order",
  ``!g:'a group. eq_order g = feq ord``,
  rw[eq_order_def, FUN_EQ_THM, fequiv_def]);

(* Theorem: orders g = feq_class ord G *)
(* Proof:
     orders g n
   = {x | x IN G /\ (ord x = n)}   by orders_def
   = feq_class ord G n             by feq_class_def
   Hence true by FUN_EQ_THM.
*)
Theorem orders_is_feq_class_order:
  !g:'a group. orders g = feq_class ord G
Proof
  rw[orders_def, in_preimage, EXTENSION, Once FUN_EQ_THM]
QED

(* Theorem: cyclic g /\ FINITE G ==> (IMAGE ord G = divisors (CARD G)) *)
(* Proof:
   Note cyclic g ==> Group g                    by cyclic_group
    and Group g /\ FINITE G ==> FiniteGroup g   by FiniteGroup_def
   If part: x IN G ==> ord x <= CARD G /\ (ord x) divides (CARD G)
      Since FiniteGroup g ==> 0 < CARD G        by finite_group_card_pos
       also ==> (ord x) divides (CARD G)        by group_order_divides
      Hence ord x IN divisors (CARD G)          by divisors_element_alt, 0 < CARD G
   Only-if part: n <= CARD G /\ n divides CARD G ==> ?x. x IN G /\ (ord x = n)
      True by cyclic_finite_has_order_divisor.
*)
Theorem cyclic_image_ord_is_divisors:
  !g:'a group. cyclic g /\ FINITE G ==> (IMAGE ord G = divisors (CARD G))
Proof
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  `0 < CARD G` by simp[finite_group_card_pos] >>
  rw[EXTENSION, divisors_element_alt, EQ_IMP_THM] >-
  rw[group_order_divides] >>
  metis_tac[cyclic_finite_has_order_divisor]
QED

(* Theorem: cyclic g /\ FINITE G ==> (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G))) *)
(* Proof:
   Since cyclic g /\ FINITE G
     ==> FiniteGroup g              by FiniteGroup_def, cyclic_group
      so 0 < CARD G                 by finite_group_card_pos
    Then partition (eq_order g) G
       = {orders g n | n | n divides CARD G}  by cyclic_eq_order_partition
       = IMAGE (orders g) (divisors (CARD G)) by divisors_element_alt, 0 < CARD G
*)
Theorem cyclic_orders_partition:
  !g:'a group. cyclic g /\ FINITE G ==>
       (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G)))
Proof
  rpt strip_tac >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def, cyclic_group] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `partition (eq_order g) G = {orders g n | n | n divides CARD G}` by rw[cyclic_eq_order_partition] >>
  rw[divisors_element_alt, EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(* Finite Cyclic Group Existence.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> ?g:num group. cyclic g /\ (CARD g.carrier = n)  *)
(* Proof:
   Let g = add_mod n.
   Then cyclic (add_mod n)        by add_mod_cylic
    and CARD g.carrier = n        by add_mod_card
*)
val finite_cyclic_group_existence = store_thm(
  "finite_cyclic_group_existence",
  ``!n. 0 < n ==> ?g:num group. cyclic g /\ (CARD g.carrier = n)``,
  rpt strip_tac >>
  qexists_tac `add_mod n` >>
  rpt strip_tac >-
  rw[add_mod_cylic] >>
  rw[add_mod_card]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Group index relative to a generator.                               *)
(* ------------------------------------------------------------------------- *)

(* Extract cyclic index w.r.t a generator *)

(* Theorem: cyclic g /\ x IN G ==> ?n. (x = (cyclic_gen g) ** n) /\ (FINITE G ==> n < CARD G) *)
(* Proof:
   Note Group g                          by cyclic_def
    and cyclic_gen g IN G /\
        ?k. x = (cyclic_gen g) ** k      by cyclic_gen_def
   If FINITE G,
      Then FiniteGroup g                 by FiniteGroup_def
        so 0 < CARD G                    by finite_group_card_pos
       and ord (cyclic_gen g) = CARD G   by cyclic_gen_order
      Take n = k MOD (CARD G).
      Then (cyclic_gen g) ** n
         = (cyclic_gen g) ** k           by group_exp_mod, 0 < CARD G
         = x                             by above
       and n < CARD G                    by MOD_LESS, 0 < CARD G
   If INFINITE G,
      Take n = k, the result follows.
*)
val cyclic_index_exists = store_thm(
  "cyclic_index_exists",
  ``!(g:'a group) x. cyclic g /\ x IN G ==> ?n. (x = (cyclic_gen g) ** n) /\ (FINITE G ==> n < CARD G)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `cyclic_gen g IN G /\ ?n. x = (cyclic_gen g) ** n` by rw[cyclic_gen_def] >>
  Cases_on `FINITE G` >| [
    rw[] >>
    `FiniteGroup g` by rw[FiniteGroup_def] >>
    `0 < CARD G` by rw[finite_group_card_pos] >>
    `ord (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
    qexists_tac `n MOD (CARD G)` >>
    rw[Once group_exp_mod],
    metis_tac[]
  ]);

(* Apply Skolemization *)
val lemma = prove(
  ``!(g:'a group) x. ?n. cyclic g /\ x IN G ==> (x = (cyclic_gen g) ** n) /\ (FINITE G ==> n < CARD G)``,
  metis_tac[cyclic_index_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define cyclic generator *)
(*
- SIMP_RULE (bool_ss) [SKOLEM_THM] lemma;
> val it =
   |- ?f. !g x. cyclic g /\ x IN G ==> x = cyclic_gen g ** f g x /\ (FINITE G ==> f g x < CARD G): thm
*)
val cyclic_index_def = new_specification(
    "cyclic_index_def",
    ["cyclic_index"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
val cyclic_index_def =
   |- !g x. cyclic g /\ x IN G ==> x = cyclic_gen g ** cyclic_index g x /\
            (FINITE G ==> cyclic_index g x < CARD G): thm
*)

(* Theorem: cyclic g /\ FINITE G ==>
            !n. n < CARD G ==> (cyclic_index g (cyclic_gen g ** n) = n) *)
(* Proof:
   Note Group g                           by cyclic_group
    ==> FiniteGroup g                     by FiniteGroup_def
    Let x = (cyclic_gen g) ** n.
   Note cyclic_gen g IN G                 by cyclic_gen_def
   Then x IN G                            by group_exp_element
   Thus (x = (cyclic_gen g) ** (cyclic_index g x)) /\
        cyclic_index g x < CARD G         by cyclic_index_def
    Now ord (cyclic_gen g) = CARD G       by cyclic_gen_order
    and 0 < CARD G                        by finite_group_card_pos
   Thus n = cyclic_index g x              by group_exp_equal
*)
val finite_cyclic_index_property = store_thm(
  "finite_cyclic_index_property",
  ``!g:'a group. cyclic g /\ FINITE G ==>
   !n. n < CARD G ==> (cyclic_index g ((cyclic_gen g) ** n) = n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  qabbrev_tac `x = (cyclic_gen g) ** n` >>
  `cyclic_gen g IN G` by rw[cyclic_gen_def] >>
  `x IN G` by rw[Abbr`x`] >>
  `(x = (cyclic_gen g) ** (cyclic_index g x)) /\ cyclic_index g x < CARD G` by fs[cyclic_index_def] >>
  `ord (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  metis_tac[group_exp_equal, finite_group_card_pos]);

(* Theorem: cyclic g /\ FINITE G /\ x IN G ==>
            !n. n < CARD G ==> ((x = (cyclic_gen g) ** n) <=> (n = cyclic_index g x)) *)
(* Proof:
   If part: (x = (cyclic_gen g) ** n) ==> (n = cyclic_index g x)
      This is true by finite_cyclic_index_property.
   Only-if part: (n = cyclic_index g x) ==> (x = (cyclic_gen g) ** n)
      This is true by cyclic_index_def
*)
val finite_cyclic_index_unique = store_thm(
  "finite_cyclic_index_unique",
  ``!g:'a group x. cyclic g /\ FINITE G /\ x IN G ==>
   !n. n < CARD G ==> ((x = (cyclic_gen g) ** n) <=> (n = cyclic_index g x))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  rw[cyclic_index_def, EQ_IMP_THM] >>
  rw[finite_cyclic_index_property]);

(* Theorem: cyclic g /\ FINITE G /\ x IN G /\ y IN G ==>
            (cyclic_index g (x * y) = ((cyclic_index g x) + (cyclic_index g y)) MOD (CARD G)) *)
(* Proof:
   Note Group g                 by cyclic_group
     so FiniteGroup g           by FiniteGroup_def
    and x * y IN G              by group_op_element
   Let z = cyclic_gen g.
   Then z IN G                  by cyclic_gen_def
    and ord z = CARD G          by cyclic_gen_order
   Note 0 < CARD G              by finite_group_card_pos
   Let h = cyclic_index g x, k = cyclic_index g y.
       z ** ((h + k) MOD CARD G)
     = z ** (h + k)             by group_exp_mod
     = (z ** h) * (z ** k)      by group_exp_add
     = x * y                    by cyclic_index_def
   Note (h + k) MOD (CARD G) < CARD G                   by MOD_LESS
   Thus (h + k) MOD (CARD G) = cyclic_index g (x * y)   by finite_cyclic_index_unique
*)
val finite_cyclic_index_add = store_thm(
  "finite_cyclic_index_add",
  ``!g:'a group x y. cyclic g /\ FINITE G /\ x IN G /\ y IN G ==>
    (cyclic_index g (x * y) = ((cyclic_index g x) + (cyclic_index g y)) MOD (CARD G))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  `x * y IN G` by rw[] >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G` by rw[cyclic_gen_def, Abbr`z`] >>
  `ord z = CARD G` by rw[cyclic_gen_order, Abbr`z`] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  qabbrev_tac `h = cyclic_index g x` >>
  qabbrev_tac `k = cyclic_index g y` >>
  `z ** ((h + k) MOD CARD G) = z ** (h + k)` by metis_tac[group_exp_mod] >>
  `_ = (z ** h) * (z ** k)` by rw[] >>
  `_ = x * y` by metis_tac[cyclic_index_def] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `(h + k) MOD (CARD G) < CARD G` by rw[] >>
  metis_tac[finite_cyclic_index_unique]);

(* ------------------------------------------------------------------------- *)
(* Finite Cyclic Group Uniqueness.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2 *)
(* Proof:
   Note Group g2                                     by cyclic_group
    and FiniteGroup g2                               by FiniteGroup_def
   Note cyclic_gen g2 IN g2.carrier                  by cyclic_gen_def
    and order g2 (cyclic_gen g2) = CARD g2.carrier   by cyclic_gen_order

   By GroupHomo_def, this is to show:
   (1) x IN g1.carrier ==> g2.exp (cyclic_gen g2) (cyclic_index g1 x) IN g2.carrier
       This is true           by group_exp_element
   (2) x IN g1.carrier /\ x' IN g1.carrier ==>
         g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.op x x')) =
         g2.op (g2.exp (cyclic_gen g2) (cyclic_index g1 x)) (g2.exp (cyclic_gen g2) (cyclic_index g1 x'))

         g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.op x x'))
       = g2.exp (cyclic_gen g2) (((cyclic_index g1 x) +
                                  (cyclic_index g1 x')) MOD (CARD g1.carrier)) by finite_cyclic_index_add
       = g2.exp (cyclic_gen g2) ((cyclic_index g1 x) + (cyclic_index g1 x'))   by group_exp_mod, group_order_pos
       = g2.op (g2.exp (cyclic_gen g2) (cyclic_index g1 x))
               (g2.exp (cyclic_gen g2) (cyclic_index g1 x'))                   by group_exp_add
*)
val finite_cyclic_group_homo = store_thm(
  "finite_cyclic_group_homo",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2``,
  rpt strip_tac >>
  `Group g2 /\ FiniteGroup g2` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g2 IN g2.carrier` by rw[cyclic_gen_def] >>
  `order g2 (cyclic_gen g2) = CARD g2.carrier` by rw[cyclic_gen_order] >>
  rw[GroupHomo_def] >>
  `g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.op x x')) =
    g2.exp (cyclic_gen g2) (((cyclic_index g1 x) + (cyclic_index g1 x')) MOD (CARD g1.carrier))` by rw[finite_cyclic_index_add] >>
  `_ = g2.exp (cyclic_gen g2) ((cyclic_index g1 x) + (cyclic_index g1 x'))` by metis_tac[group_exp_mod, group_order_pos] >>
  rw[group_exp_add]);

(* Theorem: cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier *)
(* Proof:
   Note Group g2                                     by cyclic_group
    and FiniteGroup g2                               by FiniteGroup_def
   Note cyclic_gen g2 IN g2.carrier                  by cyclic_gen_def
    and order g2 (cyclic_gen g2) = CARD g2.carrier   by cyclic_gen_order

   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN g1.carrier ==> g2.exp (cyclic_gen g2) (cyclic_index g1 x) IN g2.carrier
       This is true           by group_exp_element
   (2) x IN g1.carrier /\ x' IN g1.carrier /\
       g2.exp (cyclic_gen g2) (cyclic_index g1 x) = g2.exp (cyclic_gen g2) (cyclic_index g1 x') ==> x = x'
       Note cyclic_index g1 x < CARD g2.carrier           by cyclic_index_def
        and cyclic_index g1 x' < CARD g2.carrier          by cyclic_index_def
       Thus cyclic_index g1 x = cyclic_index g1 x'        by group_exp_equal, group_order_ps
            x
          = g1.exp (cyclic_gen g1) (cyclic_index g1 x)    by finite_cyclic_index_unique
          = g1.exp (cyclic_gen g1) (cyclic_index g1 x')   by above
          = x'                                            by finite_cyclic_index_unique
   (3) x IN g2.carrier ==> ?x'. x' IN g1.carrier /\ g2.exp (cyclic_gen g2) (cyclic_index g1 x') = x
       Note Group g1                                      by cyclic_group
        and FiniteGroup g1                                by FiniteGroup_def
       Note cyclic_gen g1 IN g2.carrier                   by cyclic_gen_def
        and order g1 (cyclic_gen g1) = CARD g1.carrier    by cyclic_gen_order
        and cyclic_index g2 x < CARD g2.carrier           by cyclic_index_def

        Let x' = g1.exp (cyclic_gen g1) (cyclic_index g2 x).
       Then g1.exp (cyclic_gen g1) (cyclic_index g2 x) IN g1.carrier    by group_exp_element
        and g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.exp (cyclic_gen g1) (cyclic_index g2 x)))
           = g2.exp (cyclic_gen g2) (cyclic_index g2 x)    by finite_cyclic_index_property
           = x                                             by cyclic_index_def
*)
val finite_cyclic_group_bij = store_thm(
  "finite_cyclic_group_bij",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier``,
  rpt strip_tac >>
  `Group g2 /\ FiniteGroup g2` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g2 IN g2.carrier` by rw[cyclic_gen_def] >>
  `order g2 (cyclic_gen g2) = CARD g2.carrier` by rw[cyclic_gen_order] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    `cyclic_index g1 x < CARD g2.carrier /\ cyclic_index g1 x' < CARD g2.carrier` by metis_tac[cyclic_index_def] >>
    `cyclic_index g1 x = cyclic_index g1 x'` by metis_tac[group_exp_equal, group_order_pos] >>
    metis_tac[finite_cyclic_index_unique],
    `Group g1 /\ FiniteGroup g1` by rw[FiniteGroup_def, cyclic_group] >>
    `cyclic_gen g1 IN g1.carrier` by rw[cyclic_gen_def] >>
    `order g1 (cyclic_gen g1) = CARD g1.carrier` by rw[cyclic_gen_order] >>
    qexists_tac `g1.exp (cyclic_gen g1) (cyclic_index g2 x)` >>
    rw[] >>
    `cyclic_index g2 x < CARD g2.carrier` by rw[cyclic_index_def] >>
    `cyclic_index g1 (g1.exp (cyclic_gen g1) (cyclic_index g2 x)) = cyclic_index g2 x` by fs[finite_cyclic_index_property] >>
    rw[cyclic_index_def]
  ]);

(* Theorem: cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupIso (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2 *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2
       This is true by finite_cyclic_group_homo
   (2) BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier
       This is true by finite_cyclic_group_bij
*)
val finite_cyclic_group_iso = store_thm(
  "finite_cyclic_group_iso",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupIso (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2``,
  rw[GroupIso_def] >-
  rw[finite_cyclic_group_homo] >>
  rw[finite_cyclic_group_bij]);

(* Theorem: cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
            (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2 *)
(* Proof:
   Let f = \x. g2.exp (cyclic_gen g2) (cyclic_index g1 x).
   The result follows by finite_cyclic_group_iso
*)
val finite_cyclic_group_uniqueness = store_thm(
  "finite_cyclic_group_uniqueness",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
        (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2``,
  metis_tac[finite_cyclic_group_iso]);

(* This completes the classification of finite cyclic groups. *)

(* Another proof of uniqueness *)

(* Theorem: cyclic g /\ FINITE G ==> GroupHomo (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g *)
(* Proof:
   Note Group g                             by cyclic_group
    and FiniteGroup g                       by FiniteGroup_def
    and cyclic_gen g IN G                   by cyclic_gen_def
    and order g (cyclic_gen g) = CARD G     by cyclic_gen_order
   By GroupHomo_def, this is to show:
   (1) (cyclic_gen g) ** n IN G, true       by group_exp_element
   (2) n < CARD G /\ n' < CARD G ==>
       cyclic_gen g ** ((n + n') MOD CARD G) = cyclic_gen g ** n * cyclic_gen g ** n'
       Note cyclic_gen g ** ((n + n') MOD CARD G)
          = cyclic_gen g ** (n + n')                 by group_exp_mod, 0 < CARD G
          = cyclic_gen g ** n * cyclic_gen g ** n'   by group_exp_add
*)
val finite_cyclic_group_add_mod_homo = store_thm(
  "finite_cyclic_group_add_mod_homo",
  ``!g:'a group. cyclic g /\ FINITE G ==> GroupHomo (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g``,
  rpt strip_tac >>
  `Group g /\ FiniteGroup g` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g IN G` by rw[cyclic_gen_def] >>
  `order g (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  rw[GroupHomo_def] >>
  `0 < CARD G` by decide_tac >>
  `cyclic_gen g ** ((n + n') MOD CARD G) = cyclic_gen g ** (n + n')` by metis_tac[group_exp_mod] >>
  rw[]);

(* Theorem: cyclic g /\ FINITE G ==> BIJ (\n. (cyclic_gen g) ** n) (add_mod (CARD G)).carrier G *)
(* Proof:
   Note Group g                             by cyclic_group
    and FiniteGroup g                       by FiniteGroup_def
    and cyclic_gen g IN G                   by cyclic_gen_def
    and order g (cyclic_gen g) = CARD G     by cyclic_gen_order
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) (cyclic_gen g) ** n IN G, true       by group_exp_element
   (2) n < CARD G /\ n' < CARD G /\ cyclic_gen g ** n = cyclic_gen g ** n' ==> n = n'
       This is true                         by finite_cyclic_index_property
   (3) x IN G ==> ?n. n < CARD G /\ (cyclic_gen g ** n = x)
       This is true                         by cyclic_index_def
*)
val finite_cyclic_group_add_mod_bij = store_thm(
  "finite_cyclic_group_add_mod_bij",
  ``!g:'a group. cyclic g /\ FINITE G ==> BIJ (\n. (cyclic_gen g) ** n) (add_mod (CARD G)).carrier G``,
  rpt strip_tac >>
  `Group g /\ FiniteGroup g` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g IN G` by rw[cyclic_gen_def] >>
  `order g (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  metis_tac[finite_cyclic_index_property] >>
  metis_tac[cyclic_index_def]);

(* Theorem: cyclic g /\ FINITE G ==> GroupIso (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo (\n. cyclic_gen g ** n) (add_mod (CARD G)) g
       This is true by finite_cyclic_group_add_mod_homo
   (2) BIJ (\n. cyclic_gen g ** n) (add_mod (CARD G)).carrier G
       This is true by finite_cyclic_group_add_mod_bij
*)
val finite_cyclic_group_add_mod_iso = store_thm(
  "finite_cyclic_group_add_mod_iso",
  ``!g:'a group. cyclic g /\ FINITE G ==> GroupIso (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g``,
  rw_tac std_ss[GroupIso_def] >-
  rw[finite_cyclic_group_add_mod_homo] >>
  rw[finite_cyclic_group_add_mod_bij]);

(* Theorem: cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
            (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2 *)
(* Proof:
   Note Group g1                             by cyclic_group
     so FiniteGroup g1                       by FiniteGroup_def
    ==> 0 < CARD g1.carrier                  by finite_group_card_pos
   Thus Group (add_mod (CARD g1.carrier))    by add_mod_group, 0 < CARD g1.carrier
   Let f1 = (\n. g1.exp (cyclic_gen g1) n),
       f2 = (\n. g2.exp (cyclic_gen g2) n).
    Now GroupIso f1 (add_mod (CARD g1.carrier)) g1    by finite_cyclic_group_add_mod_iso
    and GroupIso f2 (add_mod (CARD g2.carrier)) g2    by finite_cyclic_group_add_mod_iso
   Thus GroupIso (LINV f1 (add_mod (CARD g1.carrier)).carrier) g1 (add_mod (CARD g1.carrier))
                                                      by group_iso_sym
     or ?f. GroupIso f g1 g2                          by group_iso_trans
*)
Theorem finite_cyclic_group_uniqueness[allow_rebind]:
  !g1:'a group g2:'b group.
    cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
    (CARD g1.carrier = CARD g2.carrier) ==>
    ?f. GroupIso f g1 g2
Proof
  rpt strip_tac >>
  ‘Group g1 /\ FiniteGroup g1’ by rw[cyclic_group, FiniteGroup_def] >>
  ‘0 < CARD g1.carrier’ by rw[finite_group_card_pos] >>
  ‘Group (add_mod (CARD g1.carrier))’ by rw[add_mod_group] >>
  ‘GroupIso (\n. g1.exp (cyclic_gen g1) n) (add_mod (CARD g1.carrier)) g1’ by rw[finite_cyclic_group_add_mod_iso] >>
  ‘GroupIso (\n. g2.exp (cyclic_gen g2) n) (add_mod (CARD g2.carrier)) g2’ by rw[finite_cyclic_group_add_mod_iso] >>
  metis_tac[group_iso_sym, group_iso_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Isomorphism between Cyclic Groups                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cyclic g /\ cyclic h /\ FINITE G /\
            GroupIso f g h ==> f (cyclic_gen g) IN (cyclic_generators h) *)
(* Proof:
   Note Group g /\ Group h          by cyclic_group
    and cyclic_gen g IN G           by cyclic_gen_element
   By cyclic_generators_element, this is to show:
   (1) f (cyclic_gen g) IN h.carrier, true by group_iso_element
   (2) order h (f (cyclic_gen g)) = CARD h.carrier
        order h (f (cyclic_gen g))
      = ord (cyclic_gen g)          by group_iso_order
      = CARD G                      by cyclic_gen_order, FINITE G
      = CARD h.carrier              by group_iso_card_eq
*)
val cyclic_iso_gen = store_thm(
  "cyclic_iso_gen",
  ``!(g:'a group) (h:'b group) f. cyclic g /\ cyclic h /\ FINITE G /\
        GroupIso f g h ==> f (cyclic_gen g) IN (cyclic_generators h)``,
  rpt strip_tac >>
  `Group g /\ Group h` by rw[] >>
  `cyclic_gen g IN G` by rw[cyclic_gen_element] >>
  rw[cyclic_generators_element] >-
  metis_tac[group_iso_element] >>
  `order h (f (cyclic_gen g)) = ord (cyclic_gen g)` by rw[group_iso_order] >>
  `_ = CARD G` by rw[cyclic_gen_order] >>
  metis_tac[group_iso_card_eq]);

(*===========================================================================*)

(*

Group action
============
. action f is a map from Group g to target set X, satisfying some conditions.
. The action induces an equivalence relation "reach" on target set X.
. The equivalent classes of "reach" on A are called orbits.
. Due to this partition, CARD X = SIGMA CARD orbits.
. As equivalent classes are non-empty, minimum CARD orbit = 1.
. These singleton orbits have a 1-1 correspondence with a special set on A:
  the fixed_points. The main result is:
  CARD X = CARD fixed_points + SIGMA (CARD non-singleton orbits).

  When group action is applied to necklaces, Z[n] enters into the picture.
  The cyclic Z[n] of modular addition is the group for necklaces of n beads.

Rework
======
. name target set Xs X, with points x, y, use a, b as group elements.
. keep x, y as group elements, a, b as set A elements.
. orbit is defined as image, with one less parameter.
. orbits is named, replacing TargetPartition.

*)

(*===========================================================================*)

(* ------------------------------------------------------------------------- *)
(* Group Action Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (g act X) f    = action f g X
   (x ~~ y) f g   = reach f g x y
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Group action:
   action_def       |- !f g X. (g act X) f <=> !x. x IN X ==>
                               (!a. a IN G ==> f a x IN X) /\ f #e x = x /\
                                !a b. a IN G /\ b IN G ==> f a (f b x) = f (a * b) x
   action_closure   |- !f g X. (g act X) f ==> !a x. a IN G /\ x IN X ==> f a x IN X
   action_compose   |- !f g X. (g act X) f ==>
                       !a b x. a IN G /\ b IN G /\ x IN X ==> f a (f b x) = f (a * b) x
   action_id        |- !f g X. (g act X) f ==> !x. x IN X ==> f #e x = x
   action_reverse   |- !f g X. Group g /\ (g act X) f ==>
                       !a x y. a IN G /\ x IN X /\ y IN X /\ f a x = y ==> f ( |/ a) y = x
   action_trans     |- !f g X. (g act X) f ==> !a b x y z. a IN G /\ b IN G /\
                       x IN X /\ y IN X /\ z IN X /\ f a x = y /\ f b y = z ==> f (b * a) x = z

   Group action induces an equivalence relation:
   reach_def    |- !f g x y. (x ~~ y) f g <=> ?a. a IN G /\ f a x = b
   reach_refl   |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> (x ~~ x) f g
   reach_sym    |- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ (x ~~ y) f g ==> (y ~~ x) f g
   reach_trans  |- !f g X x y z. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ z IN X /\
                                 (x ~~ y) f g /\ (y ~~ z) f g ==> (x ~~ z) f g
   reach_equiv  xx|- !f g X. Group g /\ (g act X) f ==> reach f g equiv_on X

   Orbits as equivalence classes of Group action:
   orbit_def           |- !f g x. orbit f g x = IMAGE (\a. f a x) G
   orbit_alt           |- !f g x. orbit f g x = {f a x | a IN G}
   orbit_element       |- !f g x y. y IN orbit f g x <=> (x ~~ y) f g
   orbit_has_action_element
                       |- !f g x a. a IN G ==> f a x IN orbit f g x
   orbit_has_self      |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x
   orbit_subset_target |- !f g X x. (g act X) f /\ x IN X ==> orbit f g x SUBSET X
   orbit_element_in_target
                       |- !f g X x y. (g act X) f /\ x IN X /\ y IN orbit f g x ==> y IN X
   orbit_finite        |- !f g X. FINITE G ==> FINITE (orbit f g x)
   orbit_finite_by_target
                       |- !f g X x. (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x)
   orbit_eq_equiv_class|- !f g X x. (g act X) f /\ x IN X ==>
                                    orbit f g x = equiv_class (reach f g) X x
   orbit_eq_orbit      |- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X ==>
                                     (orbit f g x = orbit f g y <=> (x ~~ y) f g)

   Partition by Group action:
   orbits_def          |- !f g X. orbits f g X = IMAGE (orbit f g) X
   orbits_alt          |- !f g X. orbits f g X = {orbit f g x | x IN X}
   orbits_element      |- !f g X e. e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x
   orbits_eq_partition |- !f g X. (g act X) f ==> orbits f g X = partition (reach f g) X
   orbits_finite       |- !f g X. FINITE X ==> FINITE (orbits f g X)
   orbits_element_finite   |- !f g X. (g act X) f /\ FINITE X ==> EVERY_FINITE (orbits f g X)
   orbits_element_nonempty |- !f g X. Group g /\ (g act X) f ==> !e. e IN orbits f g X ==> e <> {}
   orbits_element_subset   |- !f g X e. (g act X) f /\ e IN orbits f g X ==> e SUBSET X
   orbits_element_element  |- !f g X e x. (g act X) f /\ e IN orbits f g X /\ x IN e ==> x IN X
   orbit_is_orbits_element |- !f g X x. x IN X ==> orbit f g x IN orbits f g X
   orbits_element_is_orbit |- !f g X e x. Group g /\ (g act X) f /\ e IN orbits f g X /\ x IN e ==>
                                          e = orbit f g x

   Target size and orbit size:
   action_to_orbit_surj        |- !f g X x. (g act X) f /\ x IN X ==> SURJ (\a. f a x) G (orbit f g x)
   orbit_finite_inj_card_eq    |- !f g X x. (g act X) f /\ x IN X /\ FINITE X /\
                                            INJ (\a. f a x) G (orbit f g x) ==>
                                            CARD (orbit f g x) = CARD G
   target_card_by_partition    |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                          CARD X = SIGMA CARD (orbits f g X)
   orbits_equal_size_partition_equal_size
                               |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> CARD (orbit f g x) = n) ==>
                                            !e. e IN orbits f g X ==> CARD e = n
   orbits_equal_size_property  |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> CARD (orbit f g x) = n) ==>
                                            n divides CARD X
   orbits_size_factor_partition_factor
                               |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> n divides CARD (orbit f g x)) ==>
                                            !e. e IN orbits f g X ==> n divides CARD e
   orbits_size_factor_property |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\
                                           (!x. x IN X ==> n divides CARD (orbit f g x)) ==>
                                            n divides CARD X

   Stabilizer as invariant:
   stabilizer_def        |- !f g x. stabilizer f g x = {a | a IN G /\ f a x = x}
   stabilizer_element    |- !f g x a. a IN stabilizer f g x <=> a IN G /\ f a x = x
   stabilizer_subset     |- !f g x. stabilizer f g x SUBSET G
   stabilizer_has_id     |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> #e IN stabilizer f g x
   stabilizer_nonempty   |- !f g X x. Group g /\ (g act X) f /\ x IN X ==> stabilizer f g x <> {}
   stabilizer_as_image   |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                      stabilizer f g x = IMAGE (\x. if f a x = x then a else #e) G

   Stabilizer subgroup:
   StabilizerGroup_def            |- !f g x. StabilizerGroup f g x =
                                             <|carrier := stabilizer f g x; op := $*; id := #e|>
   stabilizer_group_property      |- !f g X. ((StabilizerGroup f g x).carrier = stabilizer f g x) /\
                                             ((StabilizerGroup f g x).op = $* ) /\
                                             ((StabilizerGroup f g x).id = #e)
   stabilizer_group_carrier       |- !f g X. (StabilizerGroup f g x).carrier = stabilizer f g x
   stabilizer_group_id            |- !f g X. (StabilizerGroup f g x).id = #e
   stabilizer_group_group         |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                               Group (StabilizerGroup f g x)
   stabilizer_group_subgroup      |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                               StabilizerGroup f g x <= g
   stabilizer_group_finite_group  |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
                                               FiniteGroup (StabilizerGroup f g x)
   stabilizer_group_card_divides  |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
                                               CARD (stabilizer f g x) divides CARD G

   Orbit-Stabilizer Theorem:
   orbit_stabilizer_map_good |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !a b. a IN G /\ b IN G /\ f a x = f b x ==>
                                      (a * stabilizer f g x = b * stabilizer f g x)
   orbit_stabilizer_map_inj  |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !a b. a IN G /\ b IN G /\ (a * stabilizer f g x = b * stabilizer f g x) ==>
                                      f a x = f b x
   action_match_condition    |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !a b. a IN G /\ b IN G ==> (f a x = f b x <=> |/ x * y IN stabilizer f g x)
   action_match_condition_alt|- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                !x y::G. f a x = f b x <=> |/ x * y IN stabilizer f g x
   stabilizer_conjugate      |- !f g X x a. Group g /\ (g act X) f /\ x IN X /\ a IN G ==>
                                            (conjugate g a (stabilizer f g x) = stabilizer f g (f a x))
   act_by_def                |- !f g x y. (x ~~ y) f g ==> act_by f g x y IN G /\ f (act_by f g x y) x = y
   action_reachable_coset    |- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
                                (act_by f g x y * stabilizer f g x = {a | a IN G /\ f a x = y})
   action_reachable_coset_alt|- !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
                                !a. a IN G /\ f a x = y ==> a * stabilizer f g x = {b | b IN G /\ f b x = y}
   orbit_stabilizer_cosets_bij     |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                      BIJ (\y. act_by f g x y * stabilizer f g x)
                                          (orbit f g x)
                                          {a * stabilizer f g x | a | a IN G}
   orbit_stabilizer_cosets_bij_alt |- !f g X x. Group g /\ (g act X) f /\ x IN X ==>
                                      BIJ (\y. act_by f g x y * stabilizer f g x)
                                          (orbit f g x)
                                          (CosetPartition g (StabilizerGroup f g x))
   orbit_stabilizer_thm      |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                                          (CARD G = CARD (orbit f g x) * CARD (stabilizer f g x))
   orbit_card_divides_target_card
                             |- !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                                          CARD (orbit f g x) divides CARD G

   Fixed Points of action:
   fixed_points_def          |- !f g X. fixed_points f g X = {x | x IN X /\ !a. a IN G ==> f a x = x}
   fixed_points_element      |- !f g X x. x IN fixed_points f g X <=>
                                          x IN X /\ !a. a IN G ==> f a x = x
   fixed_points_subset       |- !f g X. fixed_points f g X SUBSET X
   fixed_points_finite       |- !f g X. FINITE X ==> FINITE (fixed_points f g X)
   fixed_points_element_element
                             |- !f g X x. x IN fixed_points f g X ==> x IN X
   fixed_points_orbit_sing   |- !f g X. Group g /\ (g act X) f ==>
                                !x. x IN fixed_points f g X <=> <=> x IN X /\ orbit f g x = {x}
   orbit_sing_fixed_points   |- !f g X. (g act X) f ==>
                                !x. x IN X /\ orbit f g x = {x} ==> x IN fixed_points f g X
   fixed_points_orbit_iff_sing
                             |- !f g X. Group g /\ (g act X) f ==>
                                !x. x IN X ==> (x IN fixed_points f g X <=> SING (orbit f g x))
   non_fixed_points_orbit_not_sing
                             |- !f g X. Group g /\ (g act X) f ==>
                                !x. x IN X DIFF fixed_points f g X <=> x IN X /\ ~SING (orbit f g x)
   non_fixed_points_card     |- !f g X. FINITE X ==>
                                CARD (X DIFF fixed_points f g X) = CARD X - CARD (fixed_points f g X)

   Target Partition by orbits:
   sing_orbits_def                  |- !f g X. sing_orbits f g X = {e | e IN orbits f g X /\ SING e}
   multi_orbits_def                 |- !f g X. multi_orbits f g X = {e | e IN orbits f g X /\ ~SING e}
   sing_orbits_element              |- !f g X e. e IN sing_orbits f g X <=> e IN orbits f g X /\ SING e
   sing_orbits_subset               |- !f g X. sing_orbits f g X SUBSET orbits f g X
   sing_orbits_finite               |- !f g X. FINITE X ==> FINITE (sing_orbits f g X)
   sing_orbits_element_subset       |- !f g X e. (g act X) f /\ e IN sing_orbits f g X ==> e SUBSET X
   sing_orbits_element_finite       |- !f g X e. e IN sing_orbits f g X ==> FINITE e
   sing_orbits_element_card         |- !f g X e. e IN sing_orbits f g X ==> CARD e = 1
   sing_orbits_element_choice       |- !f g X. Group g /\ (g act X) f ==>
                                       !e. e IN sing_orbits f g X ==> CHOICE e IN fixed_points f g X
   multi_orbits_element             |- !f g X e. e IN multi_orbits f g X <=> e IN orbits f g X /\ ~SING e
   multi_orbits_subset              |- !f g X. multi_orbits f g X SUBSET orbits f g X
   multi_orbits_finite              |- !f g X. FINITE X ==> FINITE (multi_orbits f g X)
   multi_orbits_element_subset      |- !f g X e. (g act X) f /\ e IN multi_orbits f g X ==> e SUBSET X
   multi_orbits_element_finite      |- !f g X e. (g act X) f /\ FINITE X /\ e IN multi_orbits f g X ==> FINITE e
   target_orbits_disjoint           |- !f g X. DISJOINT (sing_orbits f g X) (multi_orbits f g X)
   target_orbits_union              |- !f g X. orbits f g X = sing_orbits f g X UNION multi_orbits f g X
   target_card_by_orbit_types       |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                       (CARD X = CARD (sing_orbits f g X) + SIGMA CARD (multi_orbits f g X))
   sing_orbits_to_fixed_points_inj  |- !f g X. Group g /\ (g act X) f ==>
                                               INJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_to_fixed_points_surj |- !f g X. Group g /\ (g act X) f ==>
                                               SURJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g
   sing_orbits_to_fixed_points_bij  |- !f g X. Group g /\ (g act X) f ==>
                                               BIJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
   sing_orbits_card_eqn             |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                               (CARD (sing_orbits f g X) = CARD (fixed_points f g X))
   target_card_by_fixed_points      |- !f g X. Group g /\ (g act X) f /\ FINITE X ==>
                                              (CARD X = CARD (fixed_points f g X) +
                                                        SIGMA CARD (multi_orbits f g X))
   target_card_and_fixed_points_congruence
                                    |- !f g X n. Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
                                                (!e. e IN multi_orbits f g X ==> CARD e = n) ==>
                                                 CARD X MOD n = CARD (fixed_points f g X) MOD n
*)

(* ------------------------------------------------------------------------- *)
(* Group action                                                              *)
(* ------------------------------------------------------------------------- *)

(* An action from group g to a set X is a map f: G x X -> X such that
   (0)   [is a map] f (a IN G)(x IN X) in X
   (1)  [id action] f (e in G)(x IN X) = x
   (2) [composable] f (a IN G)(f (b in G)(x IN X)) =
                    f (g.op (a IN G)(b in G))(x IN X)
*)
Definition action_def:
    action f (g:'a group) (X:'b -> bool) =
       !x. x IN X ==> (!a. a IN G ==> f a x IN X) /\
                      f #e x = x /\
                      (!a b. a IN G /\ b IN G ==> f a (f b x) = f (a * b) x)
End

(* Overload on action *)
val _ = overload_on("act", ``\(g:'a group) (X:'b -> bool) f. action f g X``);
val _ = set_fixity "act" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> action_def;
val it = |- !(f :'a -> 'b -> 'b) (g :'a group) (X :'b -> bool).
     (g act X) f <=> !(x :'b). x IN X ==>
       (!(a :'a). a IN G ==> f a x IN X) /\ f #e x = x /\
       !(a :'a) (b :'a). a IN G /\ b IN G ==> (f a (f b x) = f ((a * b) :'a) x): thm
> action_def |> ISPEC ``$o``;
val it = |- !g' X. (g' act A) $o <=>
            !x. x IN X ==>
              (!a. a IN g'.carrier ==> a o x IN X) /\ g'.id o x = x /\
               !a b. a IN g'.carrier /\ b IN g'.carrier ==> a o b o x = g'.op a b o x: thm
*)

(* ------------------------------------------------------------------------- *)
(* Action Properties                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Closure]
            (g act X) f ==> !a x. a IN G /\ x IN X ==> f a x IN X *)
(* Proof: by action_def. *)
Theorem action_closure:
  !f g X. (g act X) f ==> !a x. a IN G /\ x IN X ==> f a x IN X
Proof
  rw[action_def]
QED

(* Theorem: [Compose]
            (g act X) f ==> !a b x. a IN G /\ b IN G /\ x IN X ==> f a (f b x) = f (a * b) x *)
(* Proof: by action_def. *)
Theorem action_compose:
  !f g X. (g act X) f ==> !a b x. a IN G /\ b IN G /\ x IN X ==> f a (f b x) = f (a * b) x
Proof
  rw[action_def]
QED

(* Theorem: [Identity]
            (g act X) f ==> !x. x IN X ==> f #e x = x *)
(* Proof: by action_def. *)
Theorem action_id:
  !f g X. (g act X) f ==> !x. x IN X ==> f #e x = x
Proof
  rw[action_def]
QED
(* This is essentially reach_refl *)

(* Theorem: Group g /\ (g act X) f ==>
            !a x y. a IN G /\ x IN X /\ y IN X /\ f a x = y ==> f ( |/ a) y = x *)
(* Proof:
   Note |/ a IN G        by group_inv_element
     f ( |/ a) y
   = f ( |/ a) (f a x)   by y = f a x
   = f ( |/ a * a) x     by action_compose
   = f #e x              by group_linv
   = x                   by action_id
*)
Theorem action_reverse:
  !f g X. Group g /\ (g act X) f ==>
          !a x y. a IN G /\ x IN X /\ y IN X /\ f a x = y ==> f ( |/ a) y = x
Proof
  rw[action_def]
QED
(* This is essentially reach_sym *)

(* Theorem: (g act X) f ==> !a b x y z. a IN G /\ b IN G /\
            x IN X /\ y IN X /\ z IN X /\ f a x = y /\ f b y = z ==> f (b * a) x = z *)
(* Proof:
     f (b * a) x
   = f b (f a x)     by action_compose
   = f b y           by y = f a x
   = z               by z = f b y
*)
Theorem action_trans:
  !f g X. (g act X) f ==> !a b x y z. a IN G /\ b IN G /\
          x IN X /\ y IN X /\ z IN X /\ f a x = y /\ f b y = z ==> f (b * a) x = z
Proof
  rw[action_def]
QED
(* This is essentially reach_trans *)

(* ------------------------------------------------------------------------- *)
(* Group action induces an equivalence relation.                             *)
(* ------------------------------------------------------------------------- *)

(* Define reach to relate two action points a and y IN X *)
val reach_def = zDefine`
    reach f (g:'a group) (x:'b) (y:'b) = ?a. a IN G /\ f a x = y
`;
(* Note: use zDefine as this is not effective. *)

(* Overload reach relation *)
val _ = temp_overload_on("~~", ``\(x:'b) (y:'b) f (g:'a group). reach f g x y``);
(* Make reach an infix. *)
val _ = set_fixity "~~" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> reach_def;
val it = |- !f g x y. (x ~~ y) f g <=> ?a. a IN G /\ f a x = y
*)

(* Theorem: [Reach is Reflexive]
            Group g /\ (g act X) f /\ x IN X ==> (x ~~ x) f g  *)
(* Proof:
   Note f #e x = x         by action_id
    and #e in G            by group_id_element
   Thus (x ~~ x) f g       by reach_def, take x = #e.
*)
Theorem reach_refl:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> (x ~~ x) f g
Proof
  metis_tac[reach_def, action_id, group_id_element]
QED

(* Theorem: [Reach is Symmetric]
            Group g /\ (g act X) f /\ x IN X /\ y IN X /\ (x ~~ y) f g ==> (y ~~ x) f g *)
(* Proof:
   Note ?a. a IN G /\ f a x = y     by reach_def, (x ~~ y) f g
    ==> f ( |/ a) y = x             by action_reverse
    and |/ a IN G                   by group_inv_element
   Thus (y ~~ x) f g                by reach_def
*)
Theorem reach_sym:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ (x ~~ y) f g ==> (y ~~ x) f g
Proof
  metis_tac[reach_def, action_reverse, group_inv_element]
QED

(* Theorem: [Reach is Transitive]
            Group g /\ (g act X) f /\ x IN X /\ y IN X /\ z IN X /\
            (x ~~ y) f g /\ (y ~~ z) f g ==> (x ~~ z) f g *)
(* Proof:
   Note ?a. a IN G /\ f a x = y       by reach_def, (x ~~ y) f g
    and ?b. b IN G /\ f b y = z       by reach_def, (y ~~ z) f g
   Thus f (b * a) x = z               by action_trans
    and b * a IN G                    by group_op_element
    ==> (x ~~ z) f g                  by reach_def
*)
Theorem reach_trans:
  !f g X x y z. Group g /\ (g act X) f /\ x IN X /\ y IN X /\ z IN X /\
                (x ~~ y) f g /\ (y ~~ z) f g ==> (x ~~ z) f g
Proof
  rw[reach_def] >>
  metis_tac[action_trans, group_op_element]
QED

(* Theorem: Reach is an equivalence relation on target set X.
            Group g /\ (g act X) f ==> (reach f g) equiv_on X *)
(* Proof:
   By Reach being Reflexive, Symmetric and Transitive.
*)
Theorem reach_equiv:
  !f g X. Group g /\ (g act X) f ==> (reach f g) equiv_on X
Proof
  rw_tac std_ss[equiv_on_def] >-
  metis_tac[reach_refl] >-
  metis_tac[reach_sym] >>
  metis_tac[reach_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Orbits as equivalence classes.                                            *)
(* ------------------------------------------------------------------------- *)

(* Orbit of action for a: those that can be reached by taking a IN G. *)
Definition orbit_def:
   orbit (f:'a -> 'b -> 'b) (g:'a group) (x:'b) = IMAGE (\a. f a x) G
End
(* Note: define as IMAGE for evaluation when f and g are concrete. *)
(*
> orbit_def |> ISPEC ``$o``;
val it = |- !g' x. orbit $o g' x = IMAGE (\a. a o x) g'.carrier: thm
*)

(* Theorem: orbit f g x = {f a x | a IN G} *)
(* Proof: by orbit_def, EXTENSION. *)
Theorem orbit_alt:
  !f g x. orbit f g x = {f a x | a IN G}
Proof
  simp[orbit_def, EXTENSION]
QED

(* Theorem: y IN orbit f g x <=> (x ~~ y) f g *)
(* Proof:
       y IN orbit f g x
   <=> ?a. a IN G /\ (y = f a x)   by orbit_def, IN_IMAGE
   <=> (x ~~ y) f g                by reach_def
*)
Theorem orbit_element:
  !f g x y. y IN orbit f g x <=> (x ~~ y) f g
Proof
  simp[orbit_def, reach_def] >>
  metis_tac[]
QED

(* Theorem: a IN G ==> f a x IN (orbit f g x) *)
(* Proof: by orbit_def *)
Theorem orbit_has_action_element:
  !f g x a. a IN G ==> f a x IN (orbit f g x)
Proof
  simp[orbit_def] >>
  metis_tac[]
QED

(* Theorem: Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x *)
(* Proof:
   Let b = orbit f g x.
   Note #e IN G            by group_id_element
     so #e o x IN b        by orbit_has_action_element
    and #e o x = x         by action_id, x IN X
   thus x IN b             by above
*)
Theorem orbit_has_self:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x
Proof
  metis_tac[orbit_has_action_element, group_id_element, action_id]
QED

(* Theorem: orbits are subsets of the target set.
            (g act X) f /\ x IN X ==> (orbit f g x) SUBSET X *)
(* Proof: orbit_def, SUBSET_DEF, action_closure. *)
Theorem orbit_subset_target:
  !f g X x. (g act X) f /\ x IN X ==> (orbit f g x) SUBSET X
Proof
  rw[orbit_def, SUBSET_DEF] >>
  metis_tac[action_closure]
QED

(* Theorem: orbits elements are in the target set.
            (g act X) f /\ x IN X /\ y IN (orbit f g x) ==> y IN X *)
(* Proof: orbit_subset_target, SUBSET_DEF. *)
Theorem orbit_element_in_target:
  !f g X x y. (g act X) f /\ x IN X /\ y IN (orbit f g x) ==> y IN X
Proof
  metis_tac[orbit_subset_target, SUBSET_DEF]
QED

(* Theorem: FINITE G ==> FINITE (orbit f g x) *)
(* Proof: by orbit_def, IMAGE_FINITE. *)
Theorem orbit_finite:
  !f (g:'a group) x. FINITE G ==> FINITE (orbit f g x)
Proof
  simp[orbit_def]
QED

(* Theorem: (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x) *)
(* Proof: by orbit_subset_target, SUBSET_FINITE. *)
Theorem orbit_finite_by_target:
  !f g X x. (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x)
Proof
  metis_tac[orbit_subset_target, SUBSET_FINITE]
QED

(* Theorem: (g act X) f /\ x IN X ==> orbit f g x = equiv_class (reach f g) X x *)
(* Proof: by orbit_def, reach_def, action_closure. *)
Theorem orbit_eq_equiv_class:
  !f g X x. (g act X) f /\ x IN X ==> orbit f g x = equiv_class (reach f g) X x
Proof
  simp[orbit_def, reach_def, EXTENSION] >>
  metis_tac[action_closure]
QED

(* Theorem: Group g /\ (g act X) f /\ x IN X /\ y IN X ==>
            (orbit f g x = orbit f g y <=> (x ~~ y) f g) *)
(* Proof: by orbit_eq_equiv_class, reach_equiv, equiv_class_eq. *)
Theorem orbit_eq_orbit:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN X ==>
              (orbit f g x = orbit f g y <=> (x ~~ y) f g)
Proof
  metis_tac[orbit_eq_equiv_class, reach_equiv, equiv_class_eq]
QED

(* ------------------------------------------------------------------------- *)
(* Partition by Group action.                                                *)
(* ------------------------------------------------------------------------- *)

(* The collection of orbits of target points. *)
Definition orbits_def:
   orbits f (g:'a group) X = IMAGE (orbit f g) X
End
(* Note: define as IMAGE for evaluation when f and g are concrete. *)
(*
> orbits_def |> ISPEC ``$o``;
val it = |- !g' X. orbits $o g' X = IMAGE (orbit $o g') X: thm
*)

(* Theorem: orbits f g X = {orbit f g x | x | x IN X} *)
(* Proof: by orbits_def, EXTENSION. *)
Theorem orbits_alt:
  !f g X. orbits f g X = {orbit f g x | x | x IN X}
Proof
  simp[orbits_def, EXTENSION]
QED

(* Theorem: e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x *)
(* Proof: by orbits_def, IN_IMAGE. *)
Theorem orbits_element:
  !f g X e. e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x
Proof
  simp[orbits_def] >>
  metis_tac[]
QED

(* Theorem: (g act X) f ==> orbits f g X = partition (reach f g) X *)
(* Proof:
   By EXTENSION,
       e IN orbits f g X
   <=> ?x. x IN X /\ e = orbit f g x     by orbits_element
   <=> ?x. x IN X /\ e = equiv_class (reach f g) X x
                                         by orbit_eq_equiv_class, (g act X) f
   <=> e IN partition (reach f g) X)     by partition_element
*)
Theorem orbits_eq_partition:
  !f g X. (g act X) f ==> orbits f g X = partition (reach f g) X
Proof
  rw[EXTENSION] >>
  metis_tac[orbits_element, orbit_eq_equiv_class, partition_element]
QED

(* Theorem: orbits = target partition is FINITE.
            FINITE X ==> FINITE (orbits f g X) *)
(* Proof: by orbits_def, IMAGE_FINITE *)
Theorem orbits_finite:
  !f g X. FINITE X ==> FINITE (orbits f g X)
Proof
  simp[orbits_def]
QED

(* Theorem: For e IN (orbits f g X), FINITE X ==> FINITE e
            (g act X) f /\ FINITE X ==> EVERY_FINITE (orbits f g X) *)
(* Proof: by orbits_eq_partition, FINITE_partition. *)
Theorem orbits_element_finite:
  !f g X. (g act X) f /\ FINITE X ==> EVERY_FINITE (orbits f g X)
Proof
  metis_tac[orbits_eq_partition, FINITE_partition]
QED
(*
orbit_finite_by_target;
|- !f g X x. (g act X) f /\ x IN X /\ FINITE X ==> FINITE (orbit f g x): thm
*)

(* Theorem: For e IN (orbits f g X), e <> EMPTY
            Group g /\ (g act X) f ==> !e. e IN orbits f g X ==> e <> EMPTY *)
(* Proof: by orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition. *)
Theorem orbits_element_nonempty:
  !f g X. Group g /\ (g act X) f ==> !e. e IN orbits f g X ==> e <> EMPTY
Proof
  simp[orbits_eq_partition, reach_equiv, EMPTY_NOT_IN_partition]
QED
(*
orbit_has_self;
|- !f g X x. Group g /\ (g act X) f /\ x IN X ==> x IN orbit f g x: thm
*)

(* Theorem: orbits elements are subset of target.
            (g act X) f /\ e IN orbits f g X ==> e SUBSET X *)
(* Proof: by orbits_eq_partition, partition_SUBSET. *)
Theorem orbits_element_subset:
  !f g X e. (g act X) f /\ e IN orbits f g X ==> e SUBSET X
Proof
  metis_tac[orbits_eq_partition, partition_SUBSET]
QED
(*
orbit_subset_target;
|- !f g X x. (g act X) f /\ x IN X ==> orbit f g x SUBSET X: thm
*)

(* Theorem: Elements in element of orbits are also in target.
            (g act X) f /\ e IN orbits f g X /\ x IN e ==> x IN X *)
(* Proof: by orbits_element_subset, SUBSET_DEF *)
Theorem orbits_element_element:
  !f g X e x. (g act X) f /\ e IN orbits f g X /\ x IN e ==> x IN X
Proof
  metis_tac[orbits_element_subset, SUBSET_DEF]
QED
(*
orbit_element_in_target;
|- !f g X x y. (g act X) f /\ x IN X /\ y IN orbit f g x ==> y IN X: thm
*)

(* Theorem: x IN X ==> (orbit f g x) IN (orbits f g X) *)
(* Proof: by orbits_def, IN_IMAGE. *)
Theorem orbit_is_orbits_element:
  !f g X x. x IN X ==> (orbit f g x) IN (orbits f g X)
Proof
  simp[orbits_def]
QED

(* Theorem: Elements of orbits are orbits of its own element.
            Group g /\ (g act X) f /\ e IN orbits f g X /\ x IN e ==> e = orbit f g x *)
(* Proof:
   By orbits_def, this is to show:
   x IN X /\ y IN orbit f g x ==> orbit f g x = orbit f g y

   Note y IN X                       by orbit_element_in_target
    and (x ~~ y) f g                 by orbit_element
    ==> orbit f g x = orbit f g y    by orbit_eq_orbit
*)
Theorem orbits_element_is_orbit:
  !f g X e x. Group g /\ (g act X) f /\ e IN orbits f g X /\
              x IN e ==> e = orbit f g x
Proof
  rw[orbits_def] >>
  metis_tac[orbit_element_in_target, orbit_element, orbit_eq_orbit]
QED
(*
orbits_element;
|- !f g X e. e IN orbits f g X <=> ?x. x IN X /\ e = orbit f g x: thm
*)

(* ------------------------------------------------------------------------- *)
(* Target size and orbit size.                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For action f g X, all a in G are reachable, belong to some orbit,
            (g act X) f /\ x IN X ==> SURJ (\a. f a x) G (orbit f g x). *)
(* Proof:
   This should follow from the fact that reach induces a partition, and
   the partition elements are orbits (orbit_is_orbits_element).

   By action_def, orbit_def, SURJ_DEF, this is to show:
   (1) x IN X /\ a IN G ==> ?b. f a x = f b x /\ b IN G
       True by taking b = a.
   (2) x IN X /\ a IN G ==> ?b. b IN G /\ f b x = f a x
       True by taking b = a.
*)
Theorem action_to_orbit_surj:
  !f g X x. (g act X) f /\ x IN X ==> SURJ (\a. f a x) G (orbit f g x)
Proof
  rw[action_def, orbit_def, SURJ_DEF] >> metis_tac[]
QED

(* Theorem: If (\a. f a x) is INJ into orbit for action,
            then orbit is same size as the group.
            (g act X) f /\ FINITE X /\ x IN X /\
            INJ (\a. f a x) G (orbit f g x) ==> CARD (orbit f g x) = CARD G *)
(* Proof:
   Note SURJ (\a. f a x) G (orbit f g x)     by action_to_orbit_surj
   With INJ (\a. f a x) G (orbit f g x)      by given
    ==> BIJ (\a. f a x) G (orbit f g x)      by BIJ_DEF
    Now (orbit f g x) SUBSET X               by orbit_subset_target
     so FINITE (orbit f g x)                 by SUBSET_FINITE, FINITE X
    ==> FINITE G                             by FINITE_INJ
   Thus CARD (orbit f g x) = CARD G          by FINITE_BIJ_CARD_EQ
*)
Theorem orbit_finite_inj_card_eq:
  !f g X x. (g act X) f /\ x IN X /\ FINITE X /\
            INJ (\a. f a x) G (orbit f g x) ==> CARD (orbit f g x) = CARD G
Proof
  metis_tac[action_to_orbit_surj, BIJ_DEF,
            orbit_subset_target, SUBSET_FINITE, FINITE_INJ, FINITE_BIJ_CARD_EQ]
QED

(* Theorem: For FINITE X, CARD X = SUM of CARD partitions in (orbits f g X).
            Group g /\ (g act X) f /\ FINITE X ==>
            CARD X = SIGMA CARD (orbits f g X) *)
(* Proof:
   With orbits_eq_partition, reach_equiv, apply
   partition_CARD
   |- !R s. R equiv_on s /\ FINITE s ==> CARD s = SIGMA CARD (partition R s)
*)
Theorem target_card_by_partition:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD X = SIGMA CARD (orbits f g X)
Proof
  metis_tac[orbits_eq_partition, reach_equiv, partition_CARD]
QED

(* Theorem: If for all x IN X, CARD (orbit f g x) = n,
            then (orbits f g X) has pieces with equal size of n.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> CARD (orbit f g x) = n) ==>
            (!e. e IN orbits f g X ==> CARD e = n) *)
(* Proof:
   Note !x. x IN e ==> (e = orbit f g x)     by orbits_element_is_orbit
   Thus ?y. y IN e                           by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But y IN X                               by orbits_element_element
     so CARD e = n                           by given implication.
*)
Theorem orbits_equal_size_partition_equal_size:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> CARD (orbit f g x) = n) ==>
            (!e. e IN orbits f g X ==> CARD e = n)
Proof
  metis_tac[orbits_element_is_orbit, orbits_element_nonempty,
            MEMBER_NOT_EMPTY, orbits_element_element]
QED

(* Theorem: If for all x IN X, CARD (orbit f g x) = n, then n divides CARD X.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> CARD (orbit f g x) = n) ==> n divides (CARD X) *)
(* Proof:
   Let R = reach f g.
   Note !e. e IN orbits f g X ==> CARD e = n by orbits_equal_size_partition_equal_size
    and R equiv_on X                  by reach_equiv
    and orbits f g X = partition R X  by orbits_eq_partition
   Thus n divides CARD X
      = n * CARD (partition R X)      by equal_partition_card
      = CARD (partition R X) * n      by MULT_SYM
     so n divides (CARD X)            by divides_def
   The last part is simplified by:

equal_partition_factor;
|- !R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> CARD e = n) ==>
          n divides CARD s
*)
Theorem orbits_equal_size_property:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> (CARD (orbit f g x) = n)) ==> n divides (CARD X)
Proof
  rpt strip_tac >>
  imp_res_tac orbits_equal_size_partition_equal_size >>
  metis_tac[orbits_eq_partition, reach_equiv, equal_partition_factor]
QED

(* Theorem: If for all x IN X, n divides CARD (orbit f g x),
            then n divides size of elements in orbits f g X.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==>
            (!e. e IN orbits f g X ==> n divides (CARD e)) *)
(* Proof:
   Note !x. x IN e ==> (e = orbit f g x) by orbits_element_is_orbit
   Thus ?y. y IN e                       by orbits_element_nonempty, MEMBER_NOT_EMPTY
    But y IN X                           by orbits_element_element
     so n divides (CARD e)               by given implication.
*)
Theorem orbits_size_factor_partition_factor:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==>
            (!e. e IN orbits f g X ==> n divides (CARD e))
Proof
  metis_tac[orbits_element_is_orbit, orbits_element_nonempty,
            MEMBER_NOT_EMPTY, orbits_element_element]
QED

(* Theorem: If for all x IN X, n divides (orbit f g x), then n divides CARD X.
            Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==> n divides (CARD X) *)
(* Proof:
   Note !e. e IN orbits f g X ==> n divides (CARD e)
                                   by orbits_size_factor_partition_factor
    and reach f g equiv_on X       by reach_equiv
   Thus n divides (CARD X)         by orbits_eq_partition, factor_partition_card
*)
Theorem orbits_size_factor_property:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\
            (!x. x IN X ==> n divides (CARD (orbit f g x))) ==> n divides (CARD X)
Proof
  metis_tac[orbits_size_factor_partition_factor,
            orbits_eq_partition, reach_equiv, factor_partition_card]
QED

(* ------------------------------------------------------------------------- *)
(* Stabilizer as invariant.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stabilizer of action: for x IN X, the group elements that fixes x. *)
val stabilizer_def = zDefine`
    stabilizer f (g:'a group) (x:'b) = {a | a IN G /\ f a x = x }
`;
(* Note: use zDefine as this is not effective for computation. *)
(*
> stabilizer_def |> ISPEC ``$o``;
val it = |- !g' x. stabilizer $o g' x = {a | a IN G'.carrier /\ a o x = x}: thm
*)

(* Theorem: a IN stabilizer f g x ==> a IN G /\ f a x = x *)
(* Proof: by stabilizer_def *)
Theorem stabilizer_element:
  !f g x a. a IN stabilizer f g x <=> a IN G /\ f a x = x
Proof
  simp[stabilizer_def]
QED

(* Theorem: The (stabilizer f g x) is a subset of G. *)
(* Proof: by stabilizer_element, SUBSET_DEF *)
Theorem stabilizer_subset:
  !f g x. (stabilizer f g x) SUBSET G
Proof
  simp[stabilizer_element, SUBSET_DEF]
QED

(* Theorem: (stabilizer f g x) has #e.
            Group g /\ (g act X) f /\ x IN X ==> #e IN stabilizer f g x *)
(* Proof:
   Note #e IN G                   by group_id_element
    and f #e x = x                by action_id
     so #e IN stabilizer f g x    by stabilizer_element
*)
Theorem stabilizer_has_id:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> #e IN stabilizer f g x
Proof
  metis_tac[stabilizer_element, action_id, group_id_element]
QED
(* This means (stabilizer f g x) is non-empty *)

(* Theorem: (stabilizer f g x) is nonempty.
            Group g /\ (g act X) f /\ x IN X ==> stabilizer f g x <> EMPTY *)
(* Proof: by stabilizer_has_id, MEMBER_NOT_EMPTY. *)
Theorem stabilizer_nonempty:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> stabilizer f g x <> EMPTY
Proof
  metis_tac[stabilizer_has_id, MEMBER_NOT_EMPTY]
QED

(* Theorem: Group g /\ (g act X) f /\ x IN X ==>
            stabilizer f g x = IMAGE (\a. if f a x = x then a else #e) G *)
(* Proof:
   By stabilizer_def, EXTENSION, this is to show:
   (1) a IN G /\ f a x = x ==> ?b. a = (if f b x = x then b else #e) /\ b IN G
       This is true by taking b = a.
   (2) a IN G ==> (if f a x = x then a else #e) IN G, true   by group_id_element
   (3) f (if f a x = x then a else #e) x = x, true           by action_id
*)
Theorem stabilizer_as_image:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            stabilizer f g x = IMAGE (\a. if f a x = x then a else #e) G
Proof
  (rw[stabilizer_def, EXTENSION] >> metis_tac[group_id_element, action_id])
QED

(* ------------------------------------------------------------------------- *)
(* Application:                                                              *)
(* Stabilizer subgroup.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the stabilizer group, the restriction of group G to stabilizer. *)
Definition StabilizerGroup_def:
    StabilizerGroup f (g:'a group) (x:'b) =
      <| carrier := stabilizer f g x;
              op := g.op;
              id := #e
       |>
End

(* Theorem: StabilizerGroup properties. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_property:
  !f g x. (StabilizerGroup f g x).carrier = stabilizer f g x /\
          (StabilizerGroup f g x).op = g.op /\
          (StabilizerGroup f g x).id = #e
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: StabilizerGroup carrier. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_carrier:
  !f g x. (StabilizerGroup f g x).carrier = stabilizer f g x
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: StabilizerGroup identity. *)
(* Proof: by StabilizerGroup_def. *)
Theorem stabilizer_group_id:
  !f g x. (StabilizerGroup f g x).id = g.id
Proof
  simp[StabilizerGroup_def]
QED

(* Theorem: If g is a Group, f g X is an action, StabilizerGroup f g x is a Group.
            Group g /\ (g act X) f /\ x IN X ==> Group (StabilizerGroup f g x) *)
(* Proof:
   By group_def_alt, StabilizerGroup_def, stabilizer_def, action_def, this is to show:
   (1) a IN G /\ b IN G /\ f a x = x /\ f b x = x ==> f (a * b) x = x
         f (a * b) x
       = f a (f b x)         by action_compose
       = f a x               by f b x = x
       = a                   by f a x = x
   (2) a IN G /\ f a x = x ==> ?b. b IN G /\ f b x = x /\ b * a = #e
       Let b = |/ a.
       Then b * a = #e       by group_linv
         f ( |/x) a
       = f ( |/x) (f a x)    by f a x = x
       = f ( |/x * x) a      by action_def
       = f (#e) a            by group_linv
       = a                   by action_def
*)
Theorem stabilizer_group_group:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> Group (StabilizerGroup f g x)
Proof
  rw_tac std_ss[group_def_alt, StabilizerGroup_def, stabilizer_def,
                action_def, GSPECIFICATION] >> prove_tac[]
QED

(* Theorem: If g is Group, f g X is an action, then StabilizerGroup f g x is a subgroup of g.
            Group g /\ (g act X) f /\ x IN X ==> (StabilizerGroup f g x) <= g *)
(* Proof:
   By Subgroup_def, stabilizer_group_property, this is to show:
   (1) x IN X ==> Group (StabilizerGroup f g x), true by stabilizer_group_group
   (2) stabilizer f g x SUBSET G, true                by stabilizer_subset
*)
Theorem stabilizer_group_subgroup:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==> (StabilizerGroup f g x) <= g
Proof
  metis_tac[Subgroup_def, stabilizer_group_property, stabilizer_group_group, stabilizer_subset]
QED

(* Theorem: If g is FINITE Group, StabilizerGroup f g x is a FINITE Group.
            FiniteGroup g /\ (g act X) f /\ x IN X ==> FiniteGroup (StabilizerGroup f g x) *)
(* Proof:
   By FiniteGroup_def, stabilizer_group_property, this is to show:
   (1) x IN X ==> Group (StabilizerGroup f g x), true          by stabilizer_group_group
   (2) FINITE G /\ x IN X ==> FINITE (stabilizer f g x), true  by stabilizer_SUBSET, SUBSET_FINITE
*)
Theorem stabilizer_group_finite_group:
  !f g X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
            FiniteGroup (StabilizerGroup f g x)
Proof
  rw_tac std_ss[FiniteGroup_def, stabilizer_group_property] >-
  metis_tac[stabilizer_group_group] >>
  metis_tac[stabilizer_subset, SUBSET_FINITE]
QED

(* Theorem: If g is FINITE Group, CARD (stabilizer f g x) divides CARD G.
            FiniteGroup g /\ (g act X) f /\ x IN X ==>
            CARD (stabilizer f g x) divides (CARD G) *)
(* Proof:
   By Lagrange's Theorem, and (StabilizerGroup f g x) is a subgroup of g.

   Note (StabilizerGroup f g x) <= g                         by stabilizer_group_subgroup
    and (StabilizerGroup f g x).carrier = stabilizer f g x   by stabilizer_group_property
    but (stabilizer f g x) SUBSET G                          by stabilizer_subset
  Thus CARD (stabilizer f g x) divides (CARD G)              by Lagrange_thm
*)
Theorem stabilizer_group_card_divides:
  !f (g:'a group) X x. FiniteGroup g /\ (g act X) f /\ x IN X ==>
                       CARD (stabilizer f g x) divides (CARD G)
Proof
  rpt (stripDup[FiniteGroup_def]) >>
  `(StabilizerGroup f g x) <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  metis_tac[stabilizer_subset, Lagrange_thm]
QED

(* ------------------------------------------------------------------------- *)
(* Orbit-Stabilizer Theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The map from orbit to coset of stabilizer is well-defined.
            Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\ f a x = f b x ==>
                  a * (stabilizer f g x) = b * (stabilizer f g x) *)
(* Proof:
   Note StabilizerGroup f g x <= g         by stabilizer_group_subgroup
    and (StabilizerGroup f g x).carrier
      = stabilizer f g x                   by stabilizer_group_property
   By subgroup_coset_eq, this is to show:
      ( |/b * a) IN (stabilizer f g x)

   Note ( |/b * a) IN G        by group_inv_element, group_op_element
        f ( |/b * a) x
      = f ( |/b) (f a x)       by action_compose
      = f ( |/b) (f b x)       by given
      = f ( |/b * b) x         by action_compose
      = f #e x                 by group_linv
      = x                      by action_id
   Hence  ( |/b * a) IN (stabilizer f g x)
                               by stabilizer_element
*)
Theorem orbit_stabilizer_map_good:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\ f a x = f b x ==>
                  a * (stabilizer f g x) = b * (stabilizer f g x)
Proof
  rpt strip_tac >>
  `StabilizerGroup f g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  fs[action_def] >>
  `( |/b * a) IN (stabilizer f g x)` suffices_by metis_tac[subgroup_coset_eq] >>
  `f ( |/b * a) x = f ( |/b) (f a x)` by rw[action_compose] >>
  `_ = f ( |/b) (f b x)` by asm_rewrite_tac[] >>
  `_ = f ( |/b * b) x` by rw[] >>
  `_ = f #e x` by rw[] >>
  `_ = x` by rw[] >>
  rw[stabilizer_element]
QED

(* Theorem: The map from orbit to coset of stabilizer is injective.
            Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\
                  a * (stabilizer f g x) = b * (stabilizer f g x) ==> f a x = f b x *)
(* Proof:
   Note a * (stabilizer f g x) = b * (stabilizer f g x)
    ==> ( |/b * a) IN (stabilizer f g x)   by subgroup_coset_eq
    ==> f ( |/b * a) x = x                 by stabilizer_element
       f a x
     = f (#e * x) a            by group_lid
     = f ((b * |/ b) * a) x    by group_rinv
     = f (b * ( |/b * a)) x    by group_assoc
     = f b (f ( |/b * a) x)    by action_compose
     = f b x                   by above, x = f ( |/b * a) x
*)
Theorem orbit_stabilizer_map_inj:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G /\
                  a * (stabilizer f g x) = b * (stabilizer f g x) ==>
                  f a x = f b x
Proof
  rpt strip_tac >>
  `StabilizerGroup f g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  `( |/b * a) IN (stabilizer f g x)` by metis_tac[subgroup_coset_eq] >>
  `f ( |/b * a) x = x` by fs[stabilizer_element] >>
  `|/b * a IN G` by rw[] >>
  `f a x = f (#e * a) x` by rw[] >>
  `_ = f ((b * |/ b) * a) x` by rw_tac std_ss[group_rinv] >>
  `_ = f (b * ( |/ b * a)) x` by rw[group_assoc] >>
  `_ = f b (f ( |/ b * a) x)` by metis_tac[action_compose] >>
  metis_tac[]
QED

(* Theorem: For action f g X /\ x IN X,
            if x, y IN G, f a x = f b x <=> 1/a * b IN (stabilizer f g x).
            Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G ==>
                 (f a x = f b x <=> ( |/ a * b) IN (stabilizer f g x))  *)
(* Proof:
   If part: f a x = f b x ==> ( |/ a * b) IN (stabilizer f g x)
      Let y = f b x, so f a x = y.
      then y IN X                   by action_closure
       and f ( |/ a) y = x          by action_reverse [1]
      Note |/ a IN G                by group_inv_element
       and |/ a * b IN G            by group_op_element
           f ( |/ a * b) x
         = f ( |/ a) (f b x)        by action_compose
         = x                        by [1] above
      Thus ( |/ a * b) IN (stabilizer f g x)
                                    by stabilizer_element
   Only-if part: ( |/ a * b) IN (stabilizer f g x) ==> f a x = f b x
      Note ( |/ a * b) IN G /\
           f ( |/ a * b) x = x      by stabilizer_element
           f a x
         = f a (f ( |/a * b) x)     by above
         = f (a * ( |/ a * b)) x    by action_compose
         = f ((a * |/ a) * b) x     by group_assoc, group_inv_element
         = f (#e * b) x             by group_rinv
         = f b x                    by group_lid
*)
Theorem action_match_condition:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b. a IN G /\ b IN G ==>
                  (f a x = f b x <=> ( |/ a * b) IN (stabilizer f g x))
Proof
  rw[EQ_IMP_THM] >| [
    `|/ a IN G /\ |/ a * b IN G` by rw[] >>
    `f ( |/ a * b) x = f ( |/ a) (f b x)` by metis_tac[action_compose] >>
    `_ = x` by metis_tac[action_closure, action_reverse] >>
    rw[stabilizer_element],
    `( |/ a * b) IN G /\ f ( |/ a * b) x = x` by metis_tac[stabilizer_element] >>
    `f a x = f a (f ( |/a * b) x)` by rw[] >>
    `_ = f (a * ( |/ a * b)) x` by metis_tac[action_compose] >>
    `_ = f ((a * |/ a) * b) x` by rw[group_assoc] >>
    rw[]
  ]
QED

(* Alternative form of the same theorem. *)
Theorem action_match_condition_alt:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            !a b::G. f a x = f b x <=> ( |/ a * b) IN (stabilizer f g x)
Proof
  metis_tac[action_match_condition]
QED

(* Theorem: stabilizers of points in same orbit:
            a * (stabilizer f g x) * 1/a = stabilizer f g (f a x).
            Group g /\ (g act X) f /\ x IN X /\ a IN G ==>
            conjugate g a (stabilizer f g x) = stabilizer f g (f a x) *)
(* Proof:
   In Section 1.12 of Volume I of [Jacobson] N.Jacobson, Basic Algebra, 1980.
   [Artin] E. Artin, Galois Theory 1942.

   By conjugate_def, stabilizer_def, this is to show:
   (1) z IN G /\ f z x = x ==> a * z * |/ a IN G
       Note |/ a   IN G                  by group_inv_element
       Thus a * z * |/ a IN G            by group_op_element
   (2) z IN G /\ f z x = x ==> f (a * z * |/ a) (f a x) = f a x
       Note a * z * |/ a IN G            by group_inv_element
         f (a * z * |/ a) (f a x)
       = f (a * z * |/ a * a) x          by action_compose
       = f ((a * z) * ( |/ a * a)) x     by group_assoc
       = f ((a * z) * #e) x              by group_linv
       = f (a * z) x                     by group_rid
       = f a (f z x)                     by action_compose
       = f a x                           by x = f z x
   (3) b IN G /\ f b (f a x) = f a x ==> ?z. b = a * z * |/ a /\ z IN G /\ f z x = x
       Let z = |/ a * b * a.
       Note |/ a IN G                    by group_inv_element
         so z IN G                       by group_op_element
         a * z * |/ a
       = a * ( |/ a * b * a) * |/ a      by notation
       = (a * ( |/ a)) * b * a * |/ a    by group_assoc
       = (a * ( |/ a)) * (b * a * |/ a)  by group_assoc
       = (a * |/ a) * b * (a * |/ a)     by group_assoc
       = #e * b * #e                     by group_rinv
       = b                               by group_lid, group_rid
         f z x
       = f ( |/ a * b * a) x             by notation
       = f ( |/ a * (b * a)) x           by group_assoc
       = f ( |/ a) (f (b * a) x)         by action_compose
       = f ( |/ a) (f b (f a x))         by action_compose
       = f ( |/ a) (f a x)               by given f b (f a x) = f a x
       = f ( |/ a * a) x                 by action_compose
       = f #e x                          by group_linv
       = x                               by action_id
*)
Theorem stabilizer_conjugate:
  !f g X x a. Group g /\ (g act X) f /\ x IN X /\ a IN G ==>
              conjugate g a (stabilizer f g x) = stabilizer f g (f a x)
Proof
  rw[conjugate_def, stabilizer_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >-
 (`a * z * |/ a IN G` by rw[] >>
  `f (a * z * |/ a) (f a x) = f (a * z * |/ a * a) x` by metis_tac[action_compose] >>
  `_ = f ((a * z) * ( |/ a * a)) x` by rw[group_assoc] >>
  `_ = f (a * z) x` by rw[] >>
  metis_tac[action_compose]) >>
  qexists_tac `|/a * x' * a` >>
  rw[] >| [
    `a * ( |/ a * x' * a) * |/ a = (a * |/ a) * x' * (a * |/ a)` by rw[group_assoc] >>
    rw[],
    `|/ a IN G /\ x' * a IN G` by rw[] >>
    `f ( |/ a * x' * a) x = f ( |/ a * (x' * a)) x` by rw[group_assoc] >>
    metis_tac[action_compose, group_linv, action_id]
  ]
QED

(* This is a major result. *)

(* Extract the existence element of reach *)
(* - reach_def;
> val it = |- !f g x y. (x ~~ y) f g <=> ?a. a IN G /\ f a x = y:  thm
*)

(* Existence of act_by: the x in reach f g X b, such that a IN G /\ f a x = b. *)
val lemma = prove(
  ``!f (g:'a group) (x:'b) (y:'b). ?a. reach f g x y ==> a IN G /\ f a x = y``,
  metis_tac[reach_def]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val act_by_def = new_specification(
    "act_by_def",
    ["act_by"],
    lemma |> SIMP_RULE bool_ss [SKOLEM_THM]
          |> CONV_RULE (RENAME_VARS_CONV ["t"] (* to allow rename of f' back to f *)
             THENC BINDER_CONV (RENAME_VARS_CONV ["f", "g", "x", "y"])));
(*
val act_by_def = |- !f g x y.
          (x ~~ y) f g ==> act_by f g x y IN G /\ f (act_by f g x y) x = y: thm
*)

(* Theorem: The reachable set from a to b is the coset act_by b of (stabilizer a).
            Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
            (act_by f g x y) * (stabilizer f g x) = {a | a IN G /\ f a x = y} *)
(* Proof:
   By orbit_element, coset_def, this is to show:
   (1) z IN stabilizer f g x ==> act_by f g x y * z IN G
       Note act_by f g x y IN G          by act_by_def
        and z IN G                       by stabilizer_element
         so act_by f g x y * z IN G      by group_op_element
   (2) z IN stabilizer f g x ==> f (act_by f g x y * z) x = y
       Note act_by f g x y IN G          by act_by_def
        and z IN G                       by stabilizer_element
         f (act_by f g x y * z) x
       = f (act_by f g x y) (f z x)      by action_compose
       = f (act_by f g x y) x            by stabilizer_element
       = y                               by act_by_def
   (3) (x ~~ f a x) f g /\ a IN G ==> ?z. a = act_by f g x (f a x) * z /\ z IN stabilizer f g x
       Let b = act_by f g x (f a x)
       Then b IN G /\ (f b x = f a x)       by act_by_def
        and |/ b * a IN (stabilizer f g x)  by action_match_condition
        Let z = |/ b * a, to show: a = b * z.
           b * z
         = b * ( |/ b * a)        by notation
         = (b * |/ b) * a         by group_assoc
         = #e * a                 by group_rinv
         = a                      by group_lid
*)
Theorem action_reachable_coset:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
              (act_by f g x y) * (stabilizer f g x) = {a | a IN G /\ f a x = y}
Proof
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[act_by_def, stabilizer_element, group_op_element] >-
  metis_tac[act_by_def, action_compose, stabilizer_element] >>
  qabbrev_tac `b = act_by f g x (f x' x)` >>
  `b IN G /\ (f b x = f x' x)` by rw[act_by_def, Abbr`b`] >>
  `|/ b * x' IN (stabilizer f g x)` by metis_tac[action_match_condition] >>
  qexists_tac `|/ b * x'` >>
  `b * ( |/ b * x') = (b * |/ b) * x'` by rw[group_assoc] >>
  `_ = x'` by rw[] >>
  rw[]
QED

(* Another formulation of the same result. *)

(* Theorem: The reachable set from x to y is the coset act_by y of (stabilizer x).
            Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
            !a. a IN G /\ f a x = y ==>
                a * (stabilizer f g x) = {b | b IN G /\ f b x = y} *)
(* Proof:
   By orbit_element, coset_def, this is to show:
   (1) z IN stabilizer f g x ==> a * z IN G
       Note z IN G            by stabilizer_element
         so a * z IN G        by group_op_element
   (2) z IN stabilizer f g x ==> f (a * z) x = f a x
       Note f z x = x         by stabilizer_element
         f (a * z) x
       = f a (f z x)          by action_compose
       = f a x                by above
   (3) b IN G /\ f a x = f b a ==> ?z. b = a * z /\ z IN stabilizer f g x
       Let z = |/ a * b.
         a * z
       = a * ( |/ a * b)      by notation
       = (a * |/ a) * b       by group_assoc
       = #e * b               by group_rinv
       = b                    by group_lid
       Hence z IN stabilizer f g x,
                              by action_match_condition, f a x = f b x
*)
Theorem action_reachable_coset_alt:
  !f g X x y. Group g /\ (g act X) f /\ x IN X /\ y IN orbit f g x ==>
              !a. a IN G /\ f a x = y ==>
                  a * (stabilizer f g x) = {b | b IN G /\ f b x = y}
Proof
  rw[orbit_element, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[stabilizer_element, group_op_element] >-
  metis_tac[stabilizer_element, action_compose] >>
  qexists_tac `|/ a * x'` >>
  rpt strip_tac >-
  rw[GSYM group_assoc] >>
  metis_tac[action_match_condition]
QED

(* Theorem: Elements of (orbit a) and cosets of (stabilizer a) are one-to-one.
            Group g /\ (g act X) f /\ x IN X ==>
            BIJ (\y. (act_by f g x y) * (stabilizer f g x))
                (orbit f g x)
                {a * (stabilizer f g x) | a IN G} *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) y IN orbit f g x ==> ?a. (act_by f g x y * stabilizer f g x = a * stabilizer f g x) /\ a IN G
       Take a = act_by f g x y.
       Note (x ~~ y) f g         by orbit_element, y IN orbit f g x
       Thus a IN G               by act_by_def
   (2) y IN orbit f g x /\ z IN orbit f g x /\
       act_by f g x y * stabilizer f g x = act_by f g x z * stabilizer f g x ==> y = z
       Note (x ~~ y) f g /\ (x ~~ z) f g                 by orbit_element
        and act_by f g x y IN G /\ act_by f g x z IN G   by act_by_def
       Thus y
          = f (act_by f g x y) x        by act_by_def
          = f (act_by f g x z) x        by orbit_stabilizer_map_inj
          = z                           by act_by_def
   (3) same as (1)
   (4) a IN G ==> ?y. y IN orbit f g x /\ (act_by f g x y * stabilizer f g x = a * stabilizer f g x)
       Take y = f a x.
       Then (x ~~ y) f g                by reach_def
        and y IN X                      by action_closure
         so y IN orbit f g x            by orbit_element
       Let b = act_by f g x y.
       Then f a x = y = f b x           by act_by_def
        ==> a * stabilizer f g x = b * stabilizer f g x
                                        by orbit_stabilizer_map_good
*)
Theorem orbit_stabilizer_cosets_bij:
  !f g X x. Group g /\ (g act X) f /\ x IN X ==>
            BIJ (\y. (act_by f g x y) * (stabilizer f g x))
                (orbit f g x)
                {a * (stabilizer f g x) | a IN G}
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
  metis_tac[orbit_element, act_by_def] >-
  metis_tac[orbit_stabilizer_map_inj, orbit_element, act_by_def] >-
  metis_tac[orbit_element, act_by_def] >>
  qexists_tac `f a x` >>
  rpt strip_tac >-
  metis_tac[orbit_element, reach_def, action_closure] >>
  `(x ~~ (f a x)) f g` by metis_tac[reach_def] >>
  metis_tac[orbit_stabilizer_map_good, act_by_def]
QED

(* The above version is not using CosetPartition. *)

(* Theorem: Elements of (orbit x) and cosets of (stabilizer x) are one-to-one.
            Group g /\ (g act X) f /\ x IN X ==>
            BIJ (\y. (act_by f g x y) * (stabilizer f g x))
                (orbit f g x)
                (CosetPartition g (StabilizerGroup f g x) *)
(* Proof:
   By CosetPartition_def, partition_def, inCoset_def,
      StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) y IN orbit f g x ==>
          ?a. a IN G /\ (act_by f g x y * stabilizer f g x = {b | b IN G /\ b IN a * stabilizer f g x})
       Let c = act_by f g x y, and put a = c.
       Note (x ~~ y) f g        by orbit_element
        and c IN G              by act_by_def,
       By coset_def, EXTENSION, this is to show:
          (?z. a = c * z /\ z IN stabilizer f g x) <=>
          a IN G /\ ?z. a = c * z /\ z IN stabilizer f g x
       Need to show: c * z IN G.
       Now z IN G               by stabilizer_element
       Thus c * z IN G          by group_op_element
   (2) y IN orbit f g x /\ z IN orbit f g x /\
         act_by f g x y * stabilizer f g x = act_by f g x z * stabilizer f g x ==> y = z
       Note (x ~~ y) f g /\ (x ~~ z) f g                  by orbit_element
        and act_by f g x y IN G /\ act_by f g x z IN G    by act_by_def
        ==> f (act_by f g x y) x = f (act_by f g x z) x   by orbit_stabilizer_map_inj
         so y = z                                         by act_by_def
   (3) same as (1)
   (4) a IN G /\ s = {y | y IN G /\ y IN a * stabilizer f g x} ==>
         ?y. y IN orbit f g x /\ (act_by f g x y * stabilizer f g x = s)
       Let y = f a x.
       Note (x ~~ y) f g             by reach_def
        and act_by f g x y IN G /\ (f (act_by f g x y) x = f a x)  by act_by_def
        ==> act_by f g x y * (stabilizer f g x)
          = a * (stabilizer f g x)   by orbit_stabilizer_map_good
      By EXTENSION, this is to show:
         !b. b IN a * stabilizer f g x ==> b IN G
      Note b IN IMAGE (\z. a * z) (stabilizer f g x)     by coset_def
      Thus ?z. z IN (stabilizer f g x) /\ (b = a * z)    by IN_IMAGE
       Now z IN G                                        by stabilizer_element
      Thus b = a * z IN G                                by group_op_element
*)
Theorem orbit_stabilizer_cosets_bij_alt:
  !f g X x.
     Group g /\ (g act X) f /\ x IN X ==>
     BIJ (\y. (act_by f g x y) * (stabilizer f g x))
         (orbit f g x)
         (CosetPartition g (StabilizerGroup f g x))
Proof
  simp_tac (srw_ss()) [CosetPartition_def, partition_def, inCoset_def,
                       StabilizerGroup_def, BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt strip_tac >| [
    qabbrev_tac `z = act_by f g x y` >>
    qexists_tac `z` >>
    `(x ~~ y) f g` by metis_tac[orbit_element] >>
    `z IN G` by rw[act_by_def, Abbr`z`] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    metis_tac[orbit_element, orbit_stabilizer_map_inj, act_by_def],
    qabbrev_tac `z = act_by f g x y` >>
    qexists_tac `z` >>
    `(x ~~ y) f g` by metis_tac[orbit_element] >>
    `z IN G` by rw[act_by_def, Abbr`z`] >>
    rw[coset_def, IMAGE_DEF, EXTENSION] >>
    metis_tac[stabilizer_element, group_op_element],
    rename [‘x'' IN G’, ‘_ IN a * stabilizer f g x’] >>
    qexists_tac `f a x` >>
    rpt strip_tac >- metis_tac[orbit_element, action_closure, reach_def] >>
    qabbrev_tac `y = f a x` >>
    `(x ~~ y) f g` by metis_tac[reach_def] >>
    `act_by f g x y IN G /\ (f (act_by f g x y) x = f a x)` by rw[act_by_def] >>
    `act_by f g x y * (stabilizer f g x) = a * (stabilizer f g x)`
      by metis_tac[orbit_stabilizer_map_good] >>
    asm_simp_tac (srw_ss()) [EXTENSION, EQ_IMP_THM] >>
    metis_tac[coset_def, IN_IMAGE, stabilizer_element, group_op_element]
  ]
QED

(* Theorem: [Orbit-Stabilizer Theorem]
            FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
            CARD G = CARD (orbit f g x) * CARD (stabilizer f g x) *)
(* Proof:
   Let h = StabilizerGroup f g x
   Then h <= g                          by stabilizer_group_subgroup
    and H = stabilizer f g x            by stabilizer_group_property
   Note CosetPartition g h = partition (inCoset g h) G  by CosetPartition_def
     so FINITE (CosetPartition g h)     by FINITE_partition
   Note FINITE_partition = IMAGE (\a. f a x) G  by orbit_def
     so FINITE (orbit f g x)            by IMAGE_FINITE

     CARD G
   = CARD H * CARD (CosetPartition g h)            by Lagrange_identity, h <= g
   = CARD (stabilizer f g x) * CARD (orbit f g x)  by orbit_stabilizer_cosets_bij_alt, FINITE_BIJ_CARD_EQ
   = CARD (orbit f g x) * CARD (stabilizer f g x)  by MULT_COMM
*)
Theorem orbit_stabilizer_thm:
  !f (g:'a group) X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                       CARD G = CARD (orbit f g x) * CARD (stabilizer f g x)
Proof
  rpt (stripDup[FiniteGroup_def]) >>
  `StabilizerGroup f g x <= g` by metis_tac[stabilizer_group_subgroup] >>
  `(StabilizerGroup f g x).carrier = stabilizer f g x` by rw[stabilizer_group_property] >>
  `FINITE (CosetPartition g (StabilizerGroup f g x))` by metis_tac[CosetPartition_def, FINITE_partition] >>
  `FINITE (orbit f g x)` by rw[orbit_def] >>
  `CARD G = CARD (stabilizer f g x) * CARD (CosetPartition g (StabilizerGroup f g x))` by metis_tac[Lagrange_identity] >>
  `_ = CARD (stabilizer f g x) * CARD (orbit f g x)` by metis_tac[orbit_stabilizer_cosets_bij_alt, FINITE_BIJ_CARD_EQ] >>
  rw[]
QED

(* This is a major milestone! *)

(* Theorem: FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
            CARD (orbit f g x) divides CARD G *)
(* Proof:
   Let b = orbit f g x,
       c = stabilizer f g x.
   Note CARD G = CARD b * CARD c         by orbit_stabilizer_thm
   Thus (CARD b) divides (CARD G)        by divides_def
*)
Theorem orbit_card_divides_target_card:
  !f (g:'a group) X x. FiniteGroup g /\ (g act X) f /\ x IN X /\ FINITE X ==>
                       CARD (orbit f g x) divides CARD G
Proof
  prove_tac[orbit_stabilizer_thm, divides_def, MULT_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Fixed Points of action.                                                   *)
(* ------------------------------------------------------------------------- *)

(*
Fixed Points have singleton orbits -- although it is not defined in this way,
this property is the theorem fixed_points_orbit_sing.

This important property of fixed points gives this simple trick:
to count how many singleton orbits, just count the set (fixed_points f g X).

Since orbits are equivalent classes, they cannot be empty, hence singleton
orbits are the simplest type. For equivalent classes:

CARD Target = SUM CARD (orbits)
            = SUM CARD (singleton orbits) + SUM CARD (non-singleton orbits)
            = CARD (fixed_points) + SUM CARD (non-singleton orbits)
*)

(* Fixed points of action: those points fixed by all group elements. *)
val fixed_points_def = zDefine`
   fixed_points f (g:'a group) (X:'b -> bool) =
      {x | x IN X /\ !a. a IN G ==> f a x = x }
`;
(* Note: use zDefine as this is not effective for computation. *)
(*
> fixed_points_def |> ISPEC ``$o``;
|- !g' X. fixed_points $o g' X = {x | x IN X /\ !a. a IN G'.carrier ==> a o x = x}: thm
*)

(* Theorem: Fixed point elements:
            x IN (fixed_points f g X) <=> x IN X /\ !a. a IN G ==> f a x = x *)
(* Proof: by fixed_points_def. *)
Theorem fixed_points_element:
  !f g X x. x IN (fixed_points f g X) <=> x IN X /\ !a. a IN G ==> f a x = x
Proof
  simp[fixed_points_def]
QED

(* Theorem: Fixed points are subsets of target set.
            (fixed_points f g X) SUBSET X *)
(* Proof: by fixed_points_def, SUBSET_DEF. *)
Theorem fixed_points_subset:
  !f g X. (fixed_points f g X) SUBSET X
Proof
  simp[fixed_points_def, SUBSET_DEF]
QED

(* Theorem: Fixed points are finite.
            FINITE X ==> FINITE (fixed_points f g X) *)
(* Proof: by fixed_points_subset, SUBSET_FINITE. *)
Theorem fixed_points_finite:
  !f g X. FINITE X ==> FINITE (fixed_points f g X)
Proof
  metis_tac[fixed_points_subset, SUBSET_FINITE]
QED

(* Theorem: x IN fixed_points f g X ==> x IN X *)
(* Proof: by fixed_points_def *)
Theorem fixed_points_element_element:
  !f g X x. x IN fixed_points f g X ==> x IN X
Proof
  simp[fixed_points_def]
QED

(* Fixed Points have singleton orbits, or those with stabilizer = whole group. *)

(* Theorem: Group g /\ (g act X) f ==>
            !x. x IN fixed_points f g X <=> x IN X /\ orbit f g x = {x} *)
(* Proof:
   By fixed_points_def, orbit_def, EXTENSION, this is to show:
   (1) a IN G /\ (!a. a IN G ==> f a x = x) ==> f a x = x
       This is true                by the included implication
   (2) (!a. a IN G ==> f a x = x) ==> ?a. a IN G /\ x = f a x
       Take a = #e,
       Then a IN G                 by group_id_element
        and f a x = x              by implication
   (3) (g act X) f /\ a IN G ==> f a x = x
       This is true                by action_closure
*)
Theorem fixed_points_orbit_sing:
  !f g X. Group g /\ (g act X) f ==>
          !x. x IN fixed_points f g X <=>
             x IN X /\ orbit f g x = {x}
Proof
  rw[fixed_points_def, orbit_def, EXTENSION, EQ_IMP_THM] >-
  rw_tac std_ss[] >-
  metis_tac[group_id_element] >>
  metis_tac[action_closure]
QED

(* Theorem: For action f g X, x IN X, (orbit f g x = {x}) ==> x IN fixed_points f g X *)
(* Proof:
   By fixed_points_def, orbit_def, EXTENSION, this is to prove:
   (g act X) f /\ x IN X /\ a IN G /\
     !x. x IN X /\ (?b. b IN G /\ (f b x = x) <=> a = b) ==> f a x = x
   This is true by action_closure.
*)
Theorem orbit_sing_fixed_points:
  !f g X. (g act X) f ==>
          !x. x IN X /\ orbit f g x = {x} ==> x IN fixed_points f g X
Proof
  rw[fixed_points_def, orbit_def, EXTENSION] >>
  metis_tac[action_closure]
QED
(* This is weaker than the previous theorem. *)

(* Theorem: Group g /\ (g act X) f ==>
           !x. x IN fixed_points f g X <=> SING (orbit f g x)) *)
(* Proof:
   By SING_DEF, this is to show:
   If part: x IN fixed_points f g X ==> ?z. (orbit f g x) = {a}
      Take z = x, then true              by fixed_points_orbit_sing
   Only-if part: (orbit f g x) = {x} ==> x IN fixed_points f g X
      Note a IN (orbit f g x)            by orbit_has_self
      Thus x = a                         by IN_SING
        so x IN fixed_points f g X       by fixed_points_orbit_sing
*)
Theorem fixed_points_orbit_iff_sing:
  !f g X. Group g /\ (g act X) f ==>
          !x. x IN X ==> (x IN fixed_points f g X <=> SING (orbit f g x))
Proof
  metis_tac[fixed_points_orbit_sing, orbit_has_self, SING_DEF, IN_SING]
QED

(* Theorem: Group g /\ (g act X) f ==>
            !x. x IN (X DIFF fixed_points f g X) <=>
                x IN X /\ ~ SING (orbit f g x))  *)
(* Proof:
       x IN (X DIFF fixed_points f g X)
   <=> x IN X /\ x NOTIN (fixed_points f g X)  by IN_DIFF
   <=> x IN X /\ ~ SING (orbit f g x))         by fixed_points_orbit_iff_sing
*)
Theorem non_fixed_points_orbit_not_sing:
  !f g X. Group g /\ (g act X) f ==>
          !x. x IN (X DIFF fixed_points f g X) <=>
              x IN X /\ ~ SING (orbit f g x)
Proof
  metis_tac[IN_DIFF, fixed_points_orbit_iff_sing]
QED

(* Theorem: FINITE X ==> CARD (X DIFF fixed_points f g X) =
                         CARD X - CARD (fixed_points f g X) *)
(* Proof:
   Let fp = fixed_points f g X.
   Note fp SUBSET X                by fixed_points_subset
   Thus X INTER fp = fp            by SUBSET_INTER_ABSORPTION
     CARD (X DIFF bp)
   = CARD X - CARD (X INTER fp)    by CARD_DIFF
   = CARD X - CARD fp              by SUBSET_INTER_ABSORPTION
*)
Theorem non_fixed_points_card:
  !f g X. FINITE X ==>
          CARD (X DIFF fixed_points f g X) =
          CARD X - CARD (fixed_points f g X)
Proof
  metis_tac[CARD_DIFF, fixed_points_subset,
            SUBSET_INTER_ABSORPTION, SUBSET_FINITE, INTER_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Partition of Target into single orbits and non-single orbits.             *)
(* ------------------------------------------------------------------------- *)

(* Define singleton and non-singleton orbits *)
val sing_orbits_def = zDefine`
    sing_orbits f (g:'a group) (X:'b -> bool) = { e | e IN (orbits f g X) /\ SING e }
`;
val multi_orbits_def = zDefine`
    multi_orbits f (g:'a group) (X:'b -> bool) = { e | e IN (orbits f g X) /\ ~ SING e }
`;
(* Note: use zDefine as this is not effective for computation. *)

(* Theorem: e IN sing_orbits f g X <=> e IN (orbits f g X) /\ SING e *)
(* Proof: by sing_orbits_def *)
Theorem sing_orbits_element:
  !f g X e. e IN sing_orbits f g X <=> e IN (orbits f g X) /\ SING e
Proof
  simp[sing_orbits_def]
QED

(* Theorem: (sing_orbits f g X) SUBSET (orbits f g X) *)
(* Proof: by sing_orbits_element, SUBSET_DEF *)
Theorem sing_orbits_subset:
  !f g X. (sing_orbits f g X) SUBSET (orbits f g X)
Proof
  simp[sing_orbits_element, SUBSET_DEF]
QED

(* Theorem: FINITE X ==> FINITE (sing_orbits f g X) *)
(* Proof: by sing_orbits_subset, orbits_finite, SUBSET_FINITE *)
Theorem sing_orbits_finite:
  !f g X. FINITE X ==> FINITE (sing_orbits f g X)
Proof
  metis_tac[sing_orbits_subset, orbits_finite, SUBSET_FINITE]
QED

(* Theorem: For (g act X) f, elements of (sing_orbits f g X) are subsets of X.
            (g act X) f /\ e IN (sing_orbits f g X) ==> e SUBSET X *)
(* Proof: by sing_orbits_element, orbits_element_subset *)
Theorem sing_orbits_element_subset:
  !f g X e. (g act X) f /\ e IN (sing_orbits f g X) ==> e SUBSET X
Proof
  metis_tac[sing_orbits_element, orbits_element_subset]
QED

(* Theorem: e IN (sing_orbits f g X) ==> FINITE e *)
(* Proof: by sing_orbits_element, SING_FINITE *)
Theorem sing_orbits_element_finite:
  !f g X e. e IN (sing_orbits f g X) ==> FINITE e
Proof
  simp[sing_orbits_element, SING_FINITE]
QED

(* Theorem: e IN (sing_orbits f g X) ==> CARD e = 1 *)
(* Proof: by sing_orbits_element, SING_DEF, CARD_SING *)
Theorem sing_orbits_element_card:
  !f g X e. e IN (sing_orbits f g X) ==> CARD e = 1
Proof
  metis_tac[sing_orbits_element, SING_DEF, CARD_SING]
QED

(* Theorem: Group g /\ (g act X) f ==>
            !e. e IN (sing_orbits f g X) ==> CHOICE e IN fixed_points f g X *)
(* Proof:
   Note e IN orbits f g X /\ SING e  by sing_orbits_element
   Thus ?x. e = {x}                  by SING_DEF
    ==> x IN e /\ (CHOICE e = x)     by IN_SING, CHOICE_SING
     so e = orbit f g x              by orbits_element_is_orbit, x IN e
    and x IN X                       by orbits_element_element
    ==> x IN fixed_points f g X      by orbit_sing_fixed_points
*)
Theorem sing_orbits_element_choice:
  !f g X. Group g /\ (g act X) f ==>
          !e. e IN (sing_orbits f g X) ==> CHOICE e IN fixed_points f g X
Proof
  rw[sing_orbits_element] >>
  `?x. e = {x}` by rw[GSYM SING_DEF] >>
  `x IN e /\ CHOICE e = x` by rw[] >>
  `e = orbit f g x` by metis_tac[orbits_element_is_orbit] >>
  metis_tac[orbit_sing_fixed_points, orbits_element_element]
QED

(* Theorem: e IN multi_orbits f g X <=> e IN (orbits f g X) /\ ~SING e *)
(* Proof: by multi_orbits_def *)
Theorem multi_orbits_element:
  !f g X e. e IN multi_orbits f g X <=> e IN (orbits f g X) /\ ~SING e
Proof
  simp[multi_orbits_def]
QED

(* Theorem: (multi_orbits f g X) SUBSET (orbits f g X) *)
(* Proof: by multi_orbits_element, SUBSET_DEF *)
Theorem multi_orbits_subset:
  !f g X. (multi_orbits f g X) SUBSET (orbits f g X)
Proof
  simp[multi_orbits_element, SUBSET_DEF]
QED

(* Theorem: FINITE X ==> FINITE (multi_orbits f g X) *)
(* Proof: by multi_orbits_subset, orbits_finite, SUBSET_FINITE *)
Theorem multi_orbits_finite:
  !f g X. FINITE X ==> FINITE (multi_orbits f g X)
Proof
  metis_tac[multi_orbits_subset, orbits_finite, SUBSET_FINITE]
QED

(* Theorem: For (g act X) f, elements of (multi_orbits f g X) are subsets of X.
            (g act X) f /\ e IN (multi_orbits f g X) ==> e SUBSET X *)
(* Proof: by multi_orbits_element, orbits_element_subset *)
Theorem multi_orbits_element_subset:
  !f g X e. (g act X) f /\ e IN (multi_orbits f g X) ==> e SUBSET X
Proof
  metis_tac[multi_orbits_element, orbits_element_subset]
QED

(* Theorem: (g act X) f /\ e IN (multi_orbits f g X) ==> FINITE e *)
(* Proof: by multi_orbits_element, orbits_element_finite *)
Theorem multi_orbits_element_finite:
  !f g X e. (g act X) f /\ FINITE X /\ e IN (multi_orbits f g X) ==> FINITE e
Proof
  metis_tac[multi_orbits_element, orbits_element_finite]
QED

(* Theorem: sing_orbits and multi_orbits are disjoint.
            DISJOINT (sing_orbits f g X) (multi_orbits f g X) *)
(* Proof: by sing_orbits_def, multi_orbits_def, DISJOINT_DEF. *)
Theorem target_orbits_disjoint:
  !f g X. DISJOINT (sing_orbits f g X) (multi_orbits f g X)
Proof
  rw[sing_orbits_def, multi_orbits_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: orbits = sing_orbits + multi_orbits.
            orbits f g X = (sing_orbits f g X) UNION (multi_orbits f g X) *)
(* Proof: by sing_orbits_def, multi_orbits_def. *)
Theorem target_orbits_union:
  !f g X. orbits f g X = (sing_orbits f g X) UNION (multi_orbits f g X)
Proof
  rw[sing_orbits_def, multi_orbits_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: For (g act X) f, CARD X = CARD sing_orbits + SIGMA CARD multi_orbits.
            Group g /\ (g act X) f /\ FINITE X ==>
            (CARD X = CARD (sing_orbits f g X) + SIGMA CARD (multi_orbits f g X)) *)
(* Proof:
   Let s = sing_orbits f g X, t = multi_orbits f g X.
   Note FINITE s                   by sing_orbits_finite
    and FINITE t                   by multi_orbits_finite
   also s INTER t = {}             by target_orbits_disjoint, DISJOINT_DEF

     CARD X
   = SIGMA CARD (orbits f g X)     by target_card_by_partition
   = SIGMA CARD (s UNION t)        by target_orbits_union
   = SIGMA CARD s + SIGMA CARD t   by SUM_IMAGE_UNION, SUM_IMAGE_EMPTY
   = 1 * CARD s + SIGMA CARD t     by sing_orbits_element_card, SIGMA_CARD_CONSTANT
   = CARD s + SIGMA CARD t         by MULT_LEFT_1
*)
Theorem target_card_by_orbit_types:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD X = CARD (sing_orbits f g X) + SIGMA CARD (multi_orbits f g X)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = sing_orbits f g X` >>
  qabbrev_tac `t = multi_orbits f g X` >>
  `FINITE s` by rw[sing_orbits_finite, Abbr`s`] >>
  `FINITE t` by rw[multi_orbits_finite, Abbr`t`] >>
  `s INTER t = {}` by rw[target_orbits_disjoint, GSYM DISJOINT_DEF, Abbr`s`, Abbr`t`] >>
  `CARD X = SIGMA CARD (orbits f g X)` by rw_tac std_ss[target_card_by_partition] >>
  `_ = SIGMA CARD (s UNION t)` by rw_tac std_ss[target_orbits_union] >>
  `_ = SIGMA CARD s + SIGMA CARD t` by rw[SUM_IMAGE_UNION, SUM_IMAGE_EMPTY] >>
  `_ = 1 * CARD s + SIGMA CARD t` by metis_tac[sing_orbits_element_card, SIGMA_CARD_CONSTANT] >>
  rw[]
QED

(* Theorem: The map: e IN (sing_orbits f g X) --> x IN (fixed_points f g X)
               where e = {x} is injective.
            Group g /\ (g act X) f ==>
            INJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) e IN sing_orbits f g X ==> CHOICE e IN fixed_points f g X
       This is true                    by sing_orbits_element_choice
   (2) e IN sing_orbits f g X /\ e' IN sing_orbits f g X /\ CHOICE e = CHOICE e' ==> e = e'
       Note SING e /\ SING e'          by sing_orbits_element
       Thus this is true               by SING_DEF, CHOICE_SING.
*)
Theorem sing_orbits_to_fixed_points_inj:
  !f g X. Group g /\ (g act X) f ==>
          INJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
Proof
  rw[INJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  metis_tac[sing_orbits_element, SING_DEF, CHOICE_SING]
QED

(* Theorem: The map: e IN (sing_orbits f g X) --> x IN (fixed_points f g X)
               where e = {x} is surjective.
            Group g /\ (g act X) f ==>
            SURJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) e IN sing_orbits f g X ==> CHOICE e IN fixed_points f g X
       This is true                      by sing_orbits_element_choice
   (2) x IN fixed_points f g X ==> ?e. e IN sing_orbits f g X /\ (CHOICE e = x)
       Note x IN X                       by fixed_points_element
        and orbit f g x = {x}            by fixed_points_orbit_sing
       Take e = {x},
       Then CHOICE e = x                 by CHOICE_SING
        and SING e                       by SING_DEF
        and e IN orbits f g X            by orbit_is_orbits_element
        ==> e IN sing_orbits f g X       by sing_orbits_element
*)
Theorem sing_orbits_to_fixed_points_surj:
  !f g X. Group g /\ (g act X) f ==>
          SURJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
Proof
  rw[SURJ_DEF] >-
  rw[sing_orbits_element_choice] >>
  `x IN X` by metis_tac[fixed_points_element] >>
  `orbit f g x = {x}` by metis_tac[fixed_points_orbit_sing] >>
  qexists_tac `{x}` >>
  simp[sing_orbits_element] >>
  metis_tac[orbit_is_orbits_element]
QED

(* Theorem: The map: e IN (sing_orbits f g X) --> x IN (fixed_points f g X)
               where e = {x} is bijective.
            Group g /\ (g act X) f ==>
            BIJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X) *)
(* Proof:
   By sing_orbits_to_fixed_points_inj,
      sing_orbits_to_fixed_points_surj, BIJ_DEF.
   True since the map is shown to be both injective and surjective.
*)
Theorem sing_orbits_to_fixed_points_bij:
  !f g X. Group g /\ (g act X) f ==>
          BIJ (\e. CHOICE e) (sing_orbits f g X) (fixed_points f g X)
Proof
  simp[BIJ_DEF, sing_orbits_to_fixed_points_surj,
                sing_orbits_to_fixed_points_inj]
QED

(* Theorem: For (g act X) f, sing_orbits is the same size as fixed_points f g X,
            Group g /\ (g act X) f /\ FINITE X ==>
            CARD (sing_orbits f g X) = CARD (fixed_points f g X) *)
(* Proof:
   Let s = sing_orbits f g X, t = fixed_points f g X.
   Note s SUBSET (orbits f g X)    by sing_orbits_subset
    and t SUBSET X                 by fixed_points_subset
   Also FINITE s                   by orbits_finite, SUBSET_FINITE
    and FINITE t                   by SUBSET_FINITE
   With BIJ (\e. CHOICE e) s t     by sing_orbits_to_fixed_points_bij
    ==> CARD s = CARD t            by FINITE_BIJ_CARD_EQ
*)
Theorem sing_orbits_card_eqn:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD (sing_orbits f g X) = CARD (fixed_points f g X)
Proof
  rpt strip_tac >>
  `(sing_orbits f g X) SUBSET (orbits f g X)` by rw[sing_orbits_subset] >>
  `(fixed_points f g X) SUBSET X` by rw[fixed_points_subset] >>
  metis_tac[sing_orbits_to_fixed_points_bij, FINITE_BIJ_CARD_EQ, SUBSET_FINITE, orbits_finite]
QED

(* Theorem: For (g act X) f, CARD X = CARD fixed_points + SIGMA CARD multi_orbits.
            Group g /\ (g act X) f /\ FINITE X ==>
            CARD X = CARD (fixed_points f g X) + SIGMA CARD (multi_orbits f g X) *)
(* Proof:
   Let s = sing_orbits f g X, t = multi_orbits f g X.
     CARD X
   = CARD s + SIGMA CARD t                       by target_card_by_orbit_types
   = CARD (fixed_points f g X) + SIGMA CARD t    by sing_orbits_card_eqn
*)
Theorem target_card_by_fixed_points:
  !f g X. Group g /\ (g act X) f /\ FINITE X ==>
          CARD X = CARD (fixed_points f g X) + SIGMA CARD (multi_orbits f g X)
Proof
  metis_tac[target_card_by_orbit_types, sing_orbits_card_eqn]
QED

(* Theorem:  Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
             (!e. e IN multi_orbits f g X ==> (CARD e = n)) ==>
             (CARD X MOD n = CARD (fixed_points f g X) MOD n) *)
(* Proof:
   Let s = fixed_points f g X,
       t = multi_orbits f g X.
   Note FINITE t                         by multi_orbits_finite
       (CARD X) MOD n
     = (CARD s + SIGMA CARD t) MOD n     by target_card_by_fixed_points
     = (CARD s + n * CARD t) MOD n       by SIGMA_CARD_CONSTANT, FINITE t
     = (CARD t * n + CARD s) MOD n       by ADD_COMM, MULT_COMM
     = (CARD s) MOD n                    by MOD_TIMES
*)
Theorem target_card_and_fixed_points_congruence:
  !f g X n. Group g /\ (g act X) f /\ FINITE X /\ 0 < n /\
            (!e. e IN multi_orbits f g X ==> (CARD e = n)) ==>
            CARD X MOD n = CARD (fixed_points f g X) MOD n
Proof
  rpt strip_tac >>
  imp_res_tac target_card_by_fixed_points >>
  `_ = CARD (fixed_points f g X) + n * CARD (multi_orbits f g X)`
     by rw[multi_orbits_finite, SIGMA_CARD_CONSTANT] >>
  fs[]
QED

(* This is a very useful theorem! *)

(* ------------------------------------------------------------------------- *)
(* Group Correspondence Documentation                                        *)
(* ------------------------------------------------------------------------- *)
(* Notes:

   Author: Yiming Xu
   Editor: Joseph Chan
   Date: March 2018
   Summary: This makes use of the HOL4 Group and Subgroup Libraries
            to formalise the Correspondence Theorem of Group Theory.
   Reference: page 62 in Algebra (2nd Edition) by Michael Artin, ISBN: 0132413779.
*)
(* Overload:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   SURJ_IMAGE_PREIMAGE     |- !f a b. s SUBSET b /\ SURJ f a b ==> IMAGE f (PREIMAGE f s INTER a) = s
   count_formula           |- !g h. FiniteGroup g /\ h << g ==> CARD G = CARD H * CARD (g / h).carrier
   iso_group_same_card     |- !g h. FINITE G /\ GroupIso f g h ==> CARD G = CARD h.carrier
   Subgroup_subgroup       |- !g h. h <= g ==> subgroup h g
   Subgroup_homo_homo      |- !g h k f. h <= g /\ GroupHomo f g k ==> GroupHomo f h k

   Lemma 1:
   image_subgroup_subgroup |- !f g1 g2 h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g1 ==>
                                          homo_image f h g2 <= g2
   Lemma 2:
   preimage_group_def          |- !f g1 g2 h. preimage_group f g1 g2 h =
                                              <|carrier := PREIMAGE f h INTER g1.carrier;
                                                     op := g1.op;
                                                     id := g1.id|>
   preimage_group_property     |- !f g1 g2 h x. x IN PREIMAGE f h INTER g1.carrier ==>
                                                x IN g1.carrier /\ f x IN h
   preimage_group_group        |- !f g1 g2 h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
                                              Group (preimage_group f g1 g2 h.carrier)
   preimage_subgroup_subgroup  |- !f g1 g2 h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
                                              preimage_group f g1 g2 h.carrier <= g1

   Lemma 3:
   preimage_subgroup_kernel    |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
                                               kernel f g1 g2 SUBSET PREIMAGE f h2.carrier INTER g1.carrier

   Lemma 4:
   normal_preimage_normal      |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
                                               h2 << g2 ==> preimage_group f g1 g2 h2.carrier << g1
   normal_surj_normal          |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
                                               SURJ f g1.carrier g2.carrier ==>
                                               preimage_group f g1 g2 h2.carrier << g1 ==> h2 << g2
   normal_iff_preimage_normal  |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
                                               SURJ f g1.carrier g2.carrier ==>
                                               (h2 << g2 <=> preimage_group f g1 g2 h2.carrier << g1)

   Lemma 5:
   image_preimage_group    |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\
                                          SURJ f g1.carrier g2.carrier ==>
                                          IMAGE f (PREIMAGE f h.carrier INTER g1.carrier) = h.carrier
   subset_preimage_image   |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 ==>
                                          H SUBSET PREIMAGE f (IMAGE f H) INTER g1.carrier
   preimage_image_subset   |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 /\
                                          SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET H ==>
                                          PREIMAGE f (IMAGE f H) INTER g1.carrier SUBSET H
   bij_corres              |- !f g1 g2 h1 h2. Group g1 /\ Group g2 /\ h1 <= g1 /\ h2 <= g2 /\
                                              GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\
                                              kernel f g1 g2 SUBSET h1.carrier ==>
                               IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
                               PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier

   Lemma 6:
   homo_count_formula      |- !f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
                               CARD (preimage_group f g1 g2 h.carrier).carrier =
                                 CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier *
                                 CARD (preimage_group f g1 g2 h.carrier /
                                       kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier
   image_iso_preimage_quotient     |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
      GroupIso (\z. coset (preimage_group f g1 g2 h.carrier)
              (CHOICE (preimage f (preimage_group f g1 g2 h.carrier).carrier z))
              (kernel f (preimage_group f g1 g2 h.carrier) g2))
        (homo_image f (preimage_group f g1 g2 h.carrier) g2)
        (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2)
   finite_homo_image       |- !f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
                              FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier
   image_preimage_quotient_same_card   |- !f g1 g2 h.
      FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
      CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
      CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier
   homo_restrict_same_kernel    |- !f g1 g2 h. H SUBSET g1.carrier /\ GroupHomo f g1 g2 /\
                                               kernel f g1 g2 SUBSET H ==> kernel f g1 g2 = kernel f h g2
   preimage_cardinality    |- !f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\
                                          SURJ f g1.carrier g2.carrier ==>
      CARD (preimage_group f g1 g2 h.carrier).carrier = CARD h.carrier * CARD (kernel f g1 g2)

   Correspondence Theorem:
   corres_thm    |- !f g1 g2 h1 h2. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\
                                    SURJ f g1.carrier g2.carrier /\ h1 <= g1 /\
                                    kernel f g1 g2 SUBSET h1.carrier /\ h2 <= g2 ==>
                     homo_image f h1 g2 <= g2 /\
                     preimage_group f g1 g2 h2.carrier <= g1 /\
                     kernel f g1 g2 SUBSET PREIMAGE f h2.carrier INTER g1.carrier /\
                     (h2 << g2 <=> preimage_group f g1 g2 h2.carrier << g1) /\
                     IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
                     PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier /\
                     (FiniteGroup g1 ==>
                         CARD (preimage_group f g1 g2 h2.carrier).carrier =
                         CARD h2.carrier * CARD (kernel f g1 g2))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* set tight equality *)
val _ = ParseExtras.tight_equality();

(* Firstly we prove a useful fact for set-theoric function to be used later. *)

(* lemma 0 (SURJ_IMAGE_PREIMAGE):
   Let f be a surjective function from set a to set b, let s be a subset of b, then f(f^{-1}(s) = s. *)
(* Theorem: s SUBSET b /\ SURJ f a b ==> (IMAGE f (PREIMAGE f s INTER a) = s) *)
(* Proof:
          f(f^{-1}(s)) = s
     <=>  x IN f(f^{-1}(s)) iff x IN s                                       definition of equality of sets
     <=>  ?y. y IN f^{-1}(s) /\ f(y) = x iff x IN s                          definition of image
     <=>  ?y. f(y) IN s /\ f(y) = x iff x IN s                               definition of preimage
     <=>  ?y. x IN s /\ f(y) = x iff x IN s                                  substitute ``f(y)`` by ``x``
     <=>  x IN s /\ !y. f(y) = x iff x IN s                                  FOL
     <=>  x IN s /\ T iff x IN s                                             definition of surjectiveness
     <=>  x IN s iff x IN s                                                  FOL
     <=>  T                                                                  FOL
*)

Theorem SURJ_IMAGE_PREIMAGE:
  !f a b. s SUBSET b /\  SURJ f a b ==> (IMAGE f(PREIMAGE f s INTER a) = s)
Proof
  rpt strip_tac >> simp[EXTENSION, PREIMAGE_def] >> strip_tac >> fs[SURJ_DEF] >>
  eq_tac >> rpt strip_tac >> metis_tac[SUBSET_DEF]
QED

(* Add some facts about cardinal arithmetic of groups. *)

(* count_formula:
   Let g be a group and h be a normal subgroup of g. Then CARD g = CARD h * CARD g / h. *)
(* Theorem: FiniteGroup g /\ h << g ==> CARD G = CARD H * CARD ((g / h).carrier) *)
(* Proof:
   Note h <= g                   by normal_subgroup_def
    and FINITE G                 by FiniteGroup_def
        CARD G
      = CARD H * CARD (CosetPartition g h)    by Lagrange_identity
      = CARD H * CARD ((g / h).carrier)       by quotient_group_def
*)
val count_formula = store_thm(
  "count_formula",
  ``!g:'a group h. FiniteGroup g /\ h << g ==> CARD G = CARD H * CARD ((g / h).carrier)``,
  rpt strip_tac >>
  `(g / h).carrier = CosetPartition g h` by simp[quotient_group_def] >>
  fs[FiniteGroup_def, normal_subgroup_def] >>
  rw[Lagrange_identity]);

(* iso_group_same_card: If two groups g and h are isomorphic, then CARD g = CARD h. *)
(* Theorem:  FINITE G /\ GroupIso f g h ==> CARD G = CARD h.carrier *)
(* Proof:
   Note BIJ f G h.carrier          by group_iso_bij
   Thus CARD G = CARD h.carrier    by FINITE_BIJ_CARD, FINITE G
*)
val iso_group_same_card = store_thm(
  "iso_group_same_card",
  ``!f g:'a group h. FINITE G /\ GroupIso f g h ==> CARD G = CARD h.carrier``,
  rpt strip_tac >>
  `BIJ f G h.carrier` by fs[group_iso_bij] >>
  metis_tac[FINITE_BIJ_CARD]);

(* lemma 1' (Subgroup_subgroup):
   The definition "Subgroup_def" implies the definition "subgroup_def" *)
(* Theorem: h <= g ==> subgroup h g *)
(* Proof: by subgroup_homomorphism *)
val Subgroup_subgroup = store_thm(
  "Subgroup_subgroup",
  ``!g:'a group h. h <= g ==> subgroup h g``,
  rw[subgroup_homomorphism]);

(* Theorem: h <= g /\ GroupHomo f g k ==> GroupHomo f h k *)
(* Proof:
   Note subgroup h g          by Subgroup_subgroup
   Thus GroupHomo f h k       by subgroup_homo_homo
*)
val Subgroup_homo_homo = store_thm(
  "Subgroup_homo_homo",
  ``!g:'a group h k f. h <= g /\ GroupHomo f g k ==> GroupHomo f h k``,
  rpt strip_tac >>
  `subgroup h g` by metis_tac[Subgroup_subgroup] >>
  metis_tac[subgroup_homo_homo]);

(* ------------------------------------------------------------------------- *)
(* Lemma 1                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 1 (image_subgroup_subgroup) :
   For a group homomorphism f from a group g1 to a group g2,
   the image of any subgroup h of g1 under f is a subgroup of g2. *)
(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g1 ==> homo_image f h g2 <= g2 *)
(* Proof:
   Note subgroup h g1             by Subgroup_subgroup, h <= g1
    ==> GroupHomo f h g2          by subgroup_homo_homo
    and Group h                   by subgroup_groups
   Thus homo_image f h g2 <= g2   by homo_image_subgroup
*)
val image_subgroup_subgroup = store_thm(
  "image_subgroup_subgroup",
  ``!g1:'a group g2 h f. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g1 ==> homo_image f h g2 <= g2``,
  rpt strip_tac >>
  `subgroup h g1` by fs[Subgroup_subgroup] >>
  `GroupHomo f h g2` by metis_tac[subgroup_homo_homo] >>
  `Group h` by metis_tac[subgroup_groups] >>
  metis_tac[homo_image_subgroup]);

(* This is Lemma 1 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 2                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 2 (preimage_subgroup_subgroup):
   For a group homomorphism f from a group g1 to a group g2,
       the preimage of any subgroup of g2 under f is a subgroup of g1. *)

(* ------------------------------------------------------------------------- *)
(* Preimage Group of Group Homomorphism.                                     *)
(* ------------------------------------------------------------------------- *)
val preimage_group_def = Define `
    preimage_group (f:'a -> 'b) (g1:'a group) (g2:'b group) (h:'b -> bool) =
    <| carrier := PREIMAGE f h INTER g1.carrier;
            op := g1.op;
            id := g1.id
     |>
`;
(* This is subset_group g1 (PREIMAGE f h INTER g1.carrier) *)


(* Theorem: x IN (PREIMAGE f h) INTER g1.carrier ==> x IN g1.carrier /\ f x IN h *)
(* Proof: by definitions. *)
val preimage_group_property = store_thm(
    "preimage_group_property",
    ``!(f:'a -> 'b) (g1:'a group) (g2:'b group) (h:'b -> bool) x.
       x IN (PREIMAGE f h) INTER g1.carrier ==> x IN g1.carrier /\ f x IN h``,
    rpt strip_tac >> fs[INTER_DEF, PREIMAGE_def]);

(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
            Group (preimage_group f g1 g2 h.carrier) *)
(* Proof:
   By group_def_alt and other definitions, this is to show:
   (1) f (g1.op x y) IN h.carrier
         f (g1.op x y)
       = g2.op (f x) (f y)      by GroupHomo_def
       = h.op (f x) (f y)       by Subgroup_def
       which is IN h.carrier    by Subgroup_def, Group h
   (2) g1.op (g1.op x y) z = g1.op x (g1.op y z)
       This is true             by group_assoc
   (3) f g1.id IN h.carrier
         f g1.id
       = g2.id                  by group_homo_id
       = h.id                   by subgroup_id
       which is IN h.carrier    by group_id_element, Group h
   (4) ?y. (f y IN h.carrier /\ y IN g1.carrier) /\ g1.op y x = g1.id
       Let y = g1.inv x.
       Then f y = g2.inv (f x)  by group_homo_inv
                = h.inv (f x)   by subgroup_inv
                IN h.carrier    by group_inv_element
        and   y IN g1.carrier   by group_inv_element
        and g1.op y x = g1.id   by group_inv_thm
*)
val preimage_group_group = store_thm(
    "preimage_group_group",
 ``!f g1:'a group g2:'b group h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==> Group (preimage_group f g1 g2 h.carrier)``,
    rpt strip_tac >> rw_tac std_ss[group_def_alt] >> fs[preimage_group_def, preimage_group_property] >>
    fs[PREIMAGE_def]
    >- (fs[GroupHomo_def] >>
       ` g2.op (f x) (f y) = h.op (f x) (f y)` by fs[Subgroup_def] >>
       `Group h` by fs[Subgroup_def] >>
       `h.op (f x) (f y) IN h.carrier` by fs[group_def_alt] >> rw[])

    >- fs[group_def_alt]
    >- (`f g1.id = g2.id` by metis_tac[group_homo_id] >>
        `h.id = g2.id` by fs[subgroup_id] >> fs[Subgroup_def] >> fs[group_def_alt])
    >- (qexists_tac `g1.inv x` >> rpt strip_tac
        >-
      ( `f (g1.inv x) = g2.inv (f x)` by fs[group_homo_inv] >>
       `g2.inv (f x) = h.inv (f x)` by fs[subgroup_inv] >>
       `Group h` by fs[Subgroup_def] >> fs[group_inv_element])
        >- (`Group h` by fs[Subgroup_def] >>
           `h.inv (f x) IN h.carrier` by fs[group_inv_element] >> rw[])
        >- fs[group_inv_thm]));

(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
            preimage_group f g1 g2 h.carrier <= g1 *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (preimage_group f g1 g2 h.carrier), true        by preimage_group_group
   (2) (preimage_group f g1 g2 h.carrier).carrier
        SUBSET g1.carrier, true                              by preimage_group_def
   (3) (preimage_group f g1 g2 h.carrier).op = g1.op, true   by preimage_group_def
*)
Theorem preimage_subgroup_subgroup:
  !f g1:'a group g2:'b group h.
    Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
    preimage_group f g1 g2 h.carrier <= g1
Proof
  rpt strip_tac >> simp[Subgroup_def] >> rpt strip_tac
  >- metis_tac[preimage_group_group] >>
  rw[preimage_group_def]
QED

(* This is Lemma 2 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 3                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 3 (preimage_subgroup_kernel):
   For a group homomorphism f from a group g to a group 'g,
   the preimage of any subgroup 'h of 'g under f contains the kernel of f. *)

(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
             (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier*)
(* Proof:
        k SUBSET f^{-1}('h)
    <=> !x. x IN k ==> x IN f^{-1}('h)                                 by definition of set inclusion
    <=> !x. x IN g /\ f(x) = #e ==> x IN g /\ f(x) IN 'h               by definition of kernel, preimage
    <=> !x. x IN g /\ f(x) = #e ==> x IN g /\ #e IN 'h                 substitute ``f(x)`` by ``#e``
    <=> T                                                              by definition of subgroup
*)
val preimage_subgroup_kernel = store_thm(
    "preimage_subgroup_kernel",
    ``!f g1:'a group g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
             (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier``,
    rpt strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >> rw[PREIMAGE_def] >>
    `h2.id = g2.id` by metis_tac[subgroup_id] >> `Group h2` by metis_tac[Subgroup_def] >>
    `h2.id IN h2.carrier` by metis_tac[group_id_element] >> metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Lemma 4                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 4 (normal_iff_preimage_normal):
   For a group homomorphism f from a group g to a group 'g, if 'h is a subgroup of 'g,
   then 'h is a normal subgroup of 'g iff PREIM f 'h is a normal subgroup of g. *)
(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
            (h2 << g2 ==> (preimage_group f g1 g2 h2.carrier) << g1) *)
(* Proof:
       'h is a normal subgroup of 'g ==> f^{-1}('h) is a normal subgroup of g.
   <=> (!'x 'y. 'x IN 'g /\ 'y IN 'h ==> 'x * 'y * 'x^{-1} IN 'h)
       ==> (!x y. x IN g /\ y IN f^{-1}('h) ==> x * y * x^{-1} IN f^{-1}('h)) by definition of normal subgroup
   <=> (!'x 'y. 'x IN 'g /\ 'y IN 'h ==> 'x * 'y * 'x^{-1} IN 'h)
       ==> (!x y. x IN g /\ f(y) IN 'h ==> f(x * y * x^{-1}) IN 'h            by definition of preimage
   <=> (!'x 'y. 'x IN 'g /\ 'y IN 'h ==> 'x * 'y * 'x^{-1} IN 'h)
       ==> (!x y. x IN g /\ f(y) IN 'h ==> f(x) * f(y) * (f(x))^{-1} IN 'h    by definition of homomorphism
                                                                                 f(x^{-1}) = (f(x))^{-1}
   <=> T                                                                      by FOL

       f^{-1}('h) is a normal subgroup of g ==> 'h is a normal subgroup of 'g.
   <=> (!a b. a IN g /\ b IN f^{-1}('h) ==> a * b * a^{-1} IN f^{-1}('h))
        ==> (!x y. x IN 'g /\ y IN 'h ==> x * y * x^{-1} IN 'h)               by definition of normal subgroup
   <=> (!a b. a IN g /\ f(b) IN 'h ==> f(a) * f(b) * (f(a))^{-1} IN 'h)
        ==> (!x y. x IN 'g /\ y IN 'h ==> x * y * x^{-1} IN 'h)               by definition of preimage
   Now !x y. ?x' y'. x' IN g /\ y' IN g /\ f(x') = x /\ f(y') = y             by definition of surjectiveness
   <=> (!a b. a IN g /\ f(b) IN 'h ==> f(a) * f(b) * (f(a))^{-1} IN 'h)
        ==> (!f(x') f(y'). f(x') IN 'g /\ f(y') IN 'h ==> f(x') * f(y') * (f(x))^{-1} IN 'h)
                             by substitute ``x`` by ``f(x')`` and substitute ``y`` by ``f(y')``
   <=> T                                                                      by condition satisfied
*)
val normal_preimage_normal = store_thm(
    "normal_preimage_normal",
    ``!f:'a -> 'b g1:'a group g2:'b group h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
    (h2 << g2 ==> (preimage_group f g1 g2 h2.carrier) << g1)``,
    rpt strip_tac >>
    fs[normal_subgroup_def] >> rpt strip_tac >>
    simp[preimage_subgroup_subgroup] >>
    fs[preimage_group_def] >> fs[PREIMAGE_def] >>
    `f (g1.op (g1.op a z) (g1.inv a)) = g2.op (g2.op (f a) (f z)) (f (g1.inv a))` by fs[GroupHomo_def] >>
    `f (g1.inv a) = g2.inv (f a)` by fs[group_homo_inv] >>
    `f (g1.op (g1.op a z) (g1.inv a)) = g2.op (g2.op (f a) (f z)) (g2.inv (f a))` by rw[] >>
    `(f a) IN g2.carrier` by metis_tac[group_homo_element] >>
    metis_tac[]);

(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            ((preimage_group f g1 g2 h2.carrier) << g1 ==> (h2 << g2)) *)
(* Proof:
   By normal_subgroup_def and preimage_group_def, this is to show:
      a IN g2.carrier /\ z IN h2.carrier ==>
           g2.op (g2.op a z) (g2.inv a) IN h2.carrier
   Let a1 = CHOICE (preimage f g1.carrier a),
   and z1 = CHOICE (preimage f g1.carrier a),
   Then f a1 = a /\ f z1 = z          by preimage_choice_property.
    and f (g1.op (g1.op a1 z1) (g1.inv a1))
      = g2.op (g2.op a z) (g2.inv a)  by GroupHomo_def, group_homo_inv
   Thus g2.op (g2.op a z) (g2.inv a) IN h2.carrier    by GroupHomo_def
*)
val normal_surj_normal = store_thm(
    "normal_surj_normal",
    ``!f:'a -> 'b g1:'a group g2:'b group h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==> ((preimage_group f g1 g2 h2.carrier) << g1 ==> (h2 << g2))``,
    rpt strip_tac >> fs[normal_subgroup_def] >> rpt strip_tac >> fs[preimage_group_def] >> fs[PREIMAGE_def] >>
    `IMAGE f g1.carrier = g2.carrier` by fs[IMAGE_SURJ] >>
    `h2.carrier SUBSET g2.carrier` by fs[Subgroup_def] >>
    `a IN IMAGE f g1.carrier` by metis_tac[] >>
    `z IN IMAGE f g1.carrier` by metis_tac[SUBSET_DEF] >>
    `CHOICE (preimage f g1.carrier a) IN g1.carrier /\ f (CHOICE (preimage f g1.carrier a)) = a` by metis_tac[preimage_choice_property] >>
    `CHOICE (preimage f g1.carrier z) IN g1.carrier /\ f (CHOICE (preimage f g1.carrier z)) = z` by metis_tac[preimage_choice_property] >>
    `f (CHOICE (preimage f g1.carrier z)) IN h2.carrier` by metis_tac[] >>
    `f (g1.op (g1.op (CHOICE (preimage f g1.carrier a)) (CHOICE (preimage f g1.carrier z))) (g1.inv (CHOICE (preimage f g1.carrier a)))) IN h2.carrier` by metis_tac[] >>
    `(f (g1.inv (CHOICE (preimage f g1.carrier a)))) = (g2.inv (f (CHOICE (preimage f g1.carrier a))))` by fs[group_homo_inv] >>
    `f (g1.op (g1.op (CHOICE (preimage f g1.carrier a)) (CHOICE (preimage f g1.carrier z))) (g1.inv (CHOICE (preimage f g1.carrier a)))) = g2.op (g2.op (f (CHOICE (preimage f g1.carrier a))) (f (CHOICE (preimage f g1.carrier z)))) (f (g1.inv (CHOICE (preimage f g1.carrier a))))` by fs[GroupHomo_def] >>
    `_ = g2.op (g2.op (f (CHOICE (preimage f g1.carrier a))) (f (CHOICE (preimage f g1.carrier z)))) (g2.inv (f (CHOICE (preimage f g1.carrier a))))` by rw[] >>
    `_ = g2.op (g2.op a z) (g2.inv a)` by rw[] >> metis_tac[]);


(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1) *)
(* Proof:
   If part: h2 << g2 ==> preimage_group f g1 g2 h2.carrier << g1
      This is true                    by normal_preimage_normal
   Only-if part: preimage_group f g1 g2 h2.carrier << g1 ==> h2 << g2
      This is true                    by normal_surj_normal
*)
val normal_iff_preimage_normal = store_thm(
    "normal_iff_preimage_normal",
    ``!f:'a -> 'b g1:'a group g2:'b group h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
    (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1)``,
    rpt strip_tac >> eq_tac >- metis_tac[normal_preimage_normal] >> metis_tac[normal_surj_normal]);

(* This is Lemma 4 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 5                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 5 (bij_corres):
    Let g, 'g are groups and f is a surjective group homomorphism from g to 'g.
    Let h be a subgroup of g contains the kernel of f, and let 'h be any subgroup of 'g,
    then f (PREIM f 'h) = 'h and PREIM f (f h) = h. *)
(* Proof:
   only need to prove f^{-1}(f(h)) is a subset of h,
   the other three follows from IMAGE_PREIMAGE, PREIMAGE_IMAGE, SURJ_IMAGE_PREIMAGE respectively.

          f^{-1}(f(h)) SUBSET h
      <=> !x. x IN f^{-1}(f(h)) ==> x IN h                               by definition of set inclusion
      <=> !x. f(x) IN f(h) ==> x IN h                                    by definition of preimage
      <=> !x. f(x) IN 'g /\ ?x'. x' IN h /\ f(x') = f(x) ==> x IN h      by definition of image
     Note f(x'^{-1} * x) = f(x'^{-1}) * f(x)                             by definition of homomorphism
                         = f(x')^{-1} * f(x)                             by (previous thm)
                   = f(x)^{-1} * f(x)                                    substitute ``f(x')`` by ``f(x)``
                   = #e                                                  by definition of inverse
      so x'^{-1} * x IN k                                                by definition of kernel
      so x'^{-1} * x IN h                                                by definition of subset
      so ?y. y IN h /\ x'^{-1} * x = y                                   by definition of element
      so ?y. y IN h /\ x = x' * y                                        by left cancellation
      so x IN h                                                          by closure of group
*)


(* Theorem: Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            IMAGE f (PREIMAGE f h.carrier INTER g1.carrier) = h.carrier *)
(* Proof: by SURJ_IMAGE_PREIMAGE *)
val image_preimage_group = store_thm(
  "image_preimage_group",
  ``!f g1:'a group g2 h.
      Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
        IMAGE f (PREIMAGE f h.carrier INTER g1.carrier) = h.carrier``,
  rpt strip_tac >>
  `h.carrier SUBSET g2.carrier` by metis_tac[Subgroup_def] >>
  metis_tac[SURJ_IMAGE_PREIMAGE]);

(* Theorem: Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 ==>
            h.carrier SUBSET PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier *)
(* Proof: by PREIMAGE_IMAGE *)
val subset_preimage_image = store_thm(
    "subset_preimage_image",
    ``!f g1:'a group g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 ==> h.carrier SUBSET PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier``,
    rpt strip_tac >> `h.carrier SUBSET g1.carrier` by metis_tac[Subgroup_def] >> fs[PREIMAGE_IMAGE]);

(* Theorem: Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 /\
            SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h.carrier ==>
            PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier SUBSET h.carrier *)
(* Proof:
   By SUBSET_DEF, PREIMAGE_def, this is to show:
      (!x. x IN g1.carrier /\ f x = g2.id ==> x IN H) /\ h <= g1 /\
      x' IN H /\ x IN g1.carrier /\ f x = f x' ==> x IN H

   Let y = g1.op x (g1.inv x').
   Note x' IN g1.carrier                 by subgroup_element
   Thus (g1.inv x') in g1.carrier        by group_inv_element
     or y IN g1.carrier                  by group_op_element
        f y
      = f (g1.op x (g1.inv x'))
      = g2.op (f x) f (g1.inv x')        by GroupHomo_def
      = g2.op (f x') f (g1.inv x')       by given, f x = f x'
      = f (g1.op x' (g1.inv x'))         by GroupHomo_def
      = f (g1.id)                        by group_rinv
      = g2.id                            by group_homo_id
   Thus y IN H                           by implication
    ==> h.op y x' IN H                   by group_op_element, h <= g1
    But h.op y x'
      = g1.op y x'                       by subgroup_op
      = g1.op (g1.op x (g1.inv x')) x'   by definition of y
      = g1.op x (g1.op (g1.inv x') x')   by group_assoc
      = g1.op x g1.id                    by group_linv
      = x                                by group_rid
     or x IN H
*)
val preimage_image_subset = store_thm(
    "preimage_image_subset",
    ``!f g1:'a group g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h.carrier ==> PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier SUBSET h.carrier``,
    rpt strip_tac >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[PREIMAGE_def] >>
    `H SUBSET g1.carrier` by fs[Subgroup_def] >>
    `x' IN g1.carrier` by fs[SUBSET_DEF] >>
    `g1.op x (g1.inv x') IN g1.carrier` by fs[group_def_alt] >>
    `(f x) IN g2.carrier` by fs[GroupHomo_def] >>
    `(f x') IN g2.carrier` by fs[GroupHomo_def] >>
    `g2.inv (f x') = f (g1.inv x')` by rw_tac std_ss[group_homo_inv] >>
    `g2.op (f x) (g2.inv (f x)) = g2.id` by fs[group_div_cancel] >>
    `g2.op (f x) (g2.inv (f x')) = g2.id` by metis_tac[] >>
    `g2.op (f x) (g2.inv (f x')) = g2.op (f x) (f (g1.inv x'))` by metis_tac[] >>
    `_ = f (g1.op x (g1.inv x'))` by fs[GroupHomo_def] >>
    `g1.inv x' IN g1.carrier` by fs[group_inv_element] >>
    `g1.op x (g1.inv x') IN g1.carrier` by fs[group_def_alt] >>
    `f (g1.op x (g1.inv x')) = g2.id` by metis_tac[] >>
    `g1.op x (g1.inv x') IN H` by metis_tac[] >>
    `Group h` by metis_tac[Subgroup_def] >>
    `g1.inv x' = h.inv x'` by metis_tac[subgroup_inv] >>
    `g1.op x (g1.inv x') = h.op x (g1.inv x')` by metis_tac[Subgroup_def] >>
    `_ = h.op x (h.inv x')` by metis_tac[] >>
    `h.op (h.op x (h.inv x')) x' IN H` by metis_tac[group_def_alt] >>
    `h.op (h.op x (h.inv x')) x' = g1.op (g1.op x (h.inv x')) x'` by fs[Subgroup_def] >>
    `_ = g1.op (g1.op x (g1.inv x')) x'` by metis_tac[subgroup_inv] >>
    `_ = g1.op x (g1.op (g1.inv x') x')` by metis_tac[group_assoc] >>
    `g1.op (g1.inv x') x' = g1.id` by metis_tac[group_linv] >>
    `h.op (h.op x (h.inv x')) x' = g1.op x g1.id` by metis_tac[] >>
    `g1.op x g1.id = x` by metis_tac[group_id] >> metis_tac[]);

(* Theorem: Group g1 /\ Group g2 /\ h1 <= g1 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
            SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h1.carrier ==>
            IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
            PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier *)
(* Proof:
   This is to show:
   (1) IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier
       This is true                       by image_preimage_group
   (2) PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier
       By SUBSET_ANTISYM, need to show:
       (1) PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier SUBSET h1.carrier
           This is true                   by preimage_image_subset
       (2) h1.carrier SUBSET PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier
           This is true                   by subset_preimage_image
*)
Theorem bij_corres:
  !f g1:'a group g2 h1 h2.
    Group g1 /\ Group g2 /\ h1 <= g1 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
    SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h1.carrier ==>
    IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
    PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier
Proof
  rpt strip_tac
  >- metis_tac[image_preimage_group] >>
  irule SUBSET_ANTISYM >> rpt conj_tac
  >- metis_tac[preimage_image_subset] >>
  metis_tac[subset_preimage_image]
QED

(* This is Lemma 5 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 6                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 6 (preimage_cardinality):
   If g, 'g are groups and f is a group homomorphism from g to 'g and 'h is a subgroup of 'g,
   then the cardinality of the preimage of 'h is
    the cardinality of 'h times the cardinality of the kernel of f. *)
(* Proof:
   Note f restrict to f^{-1}('h) is a group homomorphism
        from the group f^{-1}('h) to the group 'h. by previous thm
        (maybe we need to give another name to the restricted f, all in f'.)
   so k is also the kernel of f'.
   by the first isomorphism thm, Iso 'h f^{-1}('h) / k
   by iso_group_same_card, CARD 'h = CARD f^{-1}('h) / k
   by counting_formula, CARD f^{-1}('h) = CARD f^{-1}('h) / k * CARD k
   substitute CARD f^{-1}('h) by CARD 'h, the result follows.
*)

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
            CARD (preimage_group f g1 g2 h.carrier).carrier =
              (CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier) *
               CARD (preimage_group f g1 g2 h.carrier /
                     kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier *)
(* Proof:
   Let t = preimage_group f g1 g2 h.carrier, k = kernel_group f t g2.
   Note Group g1             by finite_group_is_group
    and t <= g1              by preimage_subgroup_subgroup
    ==> GroupHomo f t g2     by Subgroup_homo_homo
   Also Group t              by preimage_group_group
   Thus k << t               by kernel_group_normal
    and FiniteGroup t        by finite_subgroup_finite_group
   Thus CARD t.carrier = (CARD k.carrier) * CARD (t / k).carrier
                             by count_formula
*)
val homo_count_formula = store_thm(
    "homo_count_formula",
    ``!f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==> CARD (preimage_group f g1 g2 h.carrier).carrier = (CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier) * CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier``,
    rpt strip_tac >>
    `Group g1` by metis_tac[finite_group_is_group] >>
    `preimage_group f g1 g2 h.carrier <= g1` by metis_tac[preimage_subgroup_subgroup] >>
    `GroupHomo f (preimage_group f g1 g2 h.carrier) g2` by metis_tac[Subgroup_homo_homo] >>
    `Group (preimage_group f g1 g2 h.carrier)` by metis_tac[preimage_group_group] >>
    `kernel_group f (preimage_group f g1 g2 h.carrier) g2 << (preimage_group f g1 g2 h.carrier)` by metis_tac[kernel_group_normal] >>
    `FiniteGroup (preimage_group f g1 g2 h.carrier)` by metis_tac[finite_subgroup_finite_group] >>
    metis_tac[count_formula]);

(* Theorem: Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
            GroupIso (\z. coset (preimage_group f g1 g2 h.carrier)
                          (CHOICE (preimage f (preimage_group f g1 g2 h.carrier).carrier z))
                          (kernel f (preimage_group f g1 g2 h.carrier) g2))
               (homo_image f (preimage_group f g1 g2 h.carrier) g2)
               (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2) *)
(* Proof:
   Note Group (preimage_group f g1 g2 h.carrier)             by preimage_group_group
    and (preimage_group f g1 g2 h.carrier) <= g1             by preimage_subgroup_subgroup
   also GroupHomo f (preimage_group f g1 g2 h.carrier) g2    by Subgroup_homo_homo
   The result follows                                        by group_first_isomorphism_thm
*)
val image_iso_preimage_quotient = store_thm(
    "image_iso_preimage_quotient",
    ``!f g1:'a group g2 h. Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    GroupIso
         (λz.
             coset (preimage_group f g1 g2 h.carrier)
               (CHOICE
                  (preimage f (preimage_group f g1 g2 h.carrier).carrier
                     z))
               (kernel f (preimage_group f g1 g2 h.carrier) g2))
         (homo_image f (preimage_group f g1 g2 h.carrier) g2)
         (preimage_group f g1 g2 h.carrier /
          kernel_group f (preimage_group f g1 g2 h.carrier) g2)``,
    rpt strip_tac >>
    `Group (preimage_group f g1 g2 h.carrier)` by metis_tac[preimage_group_group] >>
    `(preimage_group f g1 g2 h.carrier) <= g1` by metis_tac[preimage_subgroup_subgroup] >>
    `GroupHomo f (preimage_group f g1 g2 h.carrier) g2` by metis_tac[Subgroup_homo_homo] >>
    imp_res_tac group_first_isomorphism_thm);

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
            FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier *)
(* Proof:
   Note FINITE g1.carrier                                  by FiniteGroup_def
   Thus FINITE (PREIMAGE f h.carrier INTER g1.carrier)     by FINITE_INTER
      = FINITE (preimage_group f g1 g2 h.carrier).carrier  by preimage_group_def
    ==> FINITE (IMAGE f (preimage_group f g1 g2 h.carrier).carrier)          by IMAGE_FINITE
      = FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier  by homo_image_def
*)
Theorem finite_homo_image:
  !f g1:'a group g2 h.
    FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier
Proof
  rpt strip_tac >>
  fs[homo_image_def] >>
  irule IMAGE_FINITE >>
  fs[preimage_group_def] >>
  irule FINITE_INTER >>
  metis_tac[FiniteGroup_def]
QED

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
    CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier *)
(* Proof:
   Let map = \z. coset (preimage_group f g1 g2 h.carrier)
                 (CHOICE (preimage f (preimage_group f g1 g2 h.carrier).carrier z))
                 (kernel f (preimage_group f g1 g2 h.carrier) g2)
       t1 = homo_image f (preimage_group f g1 g2 h.carrier) g2
       t2 = preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2
   Then GroupIso map t1 t2                   by image_iso_preimage_quotient
   Note FINITE t1.carrier                    by finite_homo_image, FiniteGroup g1
   Thus CARD t1.carrier = CARD t2.carrier    by iso_group_same_card
*)
Theorem image_preimage_quotient_same_card:
  !f g1:'a group g2 h.
    FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
    CARD
      (preimage_group f g1 g2 h.carrier /
       kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier
Proof
  rpt strip_tac >>
  `Group g1` by metis_tac[finite_group_is_group] >>
  imp_res_tac image_iso_preimage_quotient >>
  `FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier` by metis_tac[finite_homo_image] >>
  metis_tac[iso_group_same_card]
QED

(* Theorem: H SUBSET g1.carrier /\
            GroupHomo f g1 g2 /\ (kernel f g1 g2) SUBSET H ==> kernel f g1 g2 = kernel f h g2 *)
(* Proof:
   By kernel_def, preimage_def, this is to show:
      {x | x IN g1.carrier /\ f x = g2.id} SUBSET H ==>
      {x | x IN g1.carrier /\ f x = g2.id} = {x | x IN H /\ f x = g2.id}
   Since each is the other's SUBSET, they are equal by SET_EQ_SUBSET.
*)
val homo_restrict_same_kernel = store_thm(
  "homo_restrict_same_kernel",
  ``!f g1:'a group g2 h:'a group. H SUBSET g1.carrier /\
          GroupHomo f g1 g2 /\ (kernel f g1 g2) SUBSET H ==> kernel f g1 g2 = kernel f h g2``,
  rpt strip_tac >>
  fs[kernel_def] >>
  fs[preimage_def] >>
  fs[SET_EQ_SUBSET] >>
  rpt strip_tac >-
  fs[SUBSET_DEF] >>
  fs[SUBSET_DEF]);

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\
            GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            CARD ((preimage_group f g1 g2 h.carrier).carrier) = CARD h.carrier * CARD (kernel f g1 g2) *)
(* Proof:
   Let t1 = preimage_group f g1 g2 h.carrier,
       t2 = kernel_group f t1 g2.
   Note Group g1                  by finite_group_is_group
        CARD t1.carrier
      = CARD t2.carrier * CARD ((t1 / t2).carrier)   by homo_count_formula

   Let k = kernel f g1 g2.
   Then k SUBSET (PREIMAGE f h.carrier INTER g1.carrier)    by preimage_subgroup_kernel
    and k SUBSET t1.carrier                             by preimage_group_def
    and t1.carrier SUBSET g1.carrier                    by preimage_group_def
   Note t2.carrier
      = (kernel_group f t1).carrier                     by notation
      = kernel f t1 g2                                  by kernel_group_def
      = kernel f g1 g2 = k                              by homo_restrict_same_kernel
        CARD t1.carrier
      = CARD k * CARD ((t1 / t2.carrier))               by above
      = CARD k * CARD (homo_image f t1).carrier         by image_preimage_quotient_same_card
      = CARD k * CARD (IMAGE f t1.carrier)              by homo_image_def
      = CARD k * CARD (IMAGE f (PREIMAGE f h.carrier INTER g1.carrier)) by preimage_group_def
      = CARD k * CARD h.carrier                         by image_preimage_group
      = CARD h.carrier * CARD k                         by MULT_COMM
*)
val preimage_cardinality = store_thm(
    "preimage_cardinality",
    ``!f g1:'a group g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==> CARD ((preimage_group f g1 g2 h.carrier).carrier) = CARD h.carrier * CARD (kernel f g1 g2)``,
    rpt strip_tac >>
    `Group g1` by fs[finite_group_is_group] >>
    `CARD (preimage_group f g1 g2 h.carrier).carrier = (CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier) * CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier` by metis_tac[homo_count_formula] >>
    `(kernel f g1 g2) SUBSET (PREIMAGE f h.carrier INTER g1.carrier)` by metis_tac[preimage_subgroup_kernel] >>
    `(kernel f g1 g2) SUBSET (preimage_group f g1 g2 h.carrier).carrier` by fs[preimage_group_def] >>
    `(preimage_group f g1 g2 h.carrier).carrier SUBSET g1.carrier` by fs[preimage_group_def] >>
    `kernel f (preimage_group f g1 g2 h.carrier) g2 = kernel f g1 g2` by fs[homo_restrict_same_kernel] >>
    `(kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier = kernel f (preimage_group f g1 g2 h.carrier) g2` by fs[kernel_group_def] >>
    ` _ = kernel f g1 g2` by rw[] >>
    ` CARD (preimage_group f g1 g2 h.carrier).carrier =
      CARD (kernel f g1 g2) *
      CARD (preimage_group f g1 g2 h.carrier /
            kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier` by rw[] >>
    `CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
     CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier` by fs[image_preimage_quotient_same_card] >>
    `CARD (preimage_group f g1 g2 h.carrier).carrier =
       CARD (kernel f g1 g2) * CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier` by rw[] >>
    `(homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier = IMAGE f (preimage_group f g1 g2 h.carrier).carrier` by fs[homo_image_def] >>
    `_ = IMAGE f (PREIMAGE f h.carrier INTER g1.carrier)` by fs[preimage_group_def] >>
    `_ = h.carrier` by metis_tac[image_preimage_group] >>
    `CARD (preimage_group f g1 g2 h.carrier).carrier =
     CARD (kernel f g1 g2) * CARD h.carrier` by fs[] >>
    `CARD (kernel f g1 g2) * CARD h.carrier = CARD h.carrier * CARD (kernel f g1 g2)` by metis_tac[MULT_COMM] >>
    metis_tac[]);

(* This is Lemma 6 *)

(* ------------------------------------------------------------------------- *)
(* Correspondence Theorem                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem:
   Let f be a surjective group homomorphism from group g to group 'g with kernel k.
   There is a bijective correspondence between subgroups of 'g and subgroups of g that contains k.
   The correspondence is defined as follows:
   a subgroup h of g that contains k |-> its image f h in 'g,
   a subgroup 'h of 'g |-> its inverse image f^{-1} 'h in g.
   If h and 'h are corresponding subgroups, then h is normal in g iff 'h is normal in 'g.
   If h and 'h are corresponding subgroups, then | h | = | 'h | | k |.
*)

(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\
            h1 <= g1 /\ (kernel f g1 g2) SUBSET h1.carrier /\ h2 <= g2 ==>
            homo_image f h1 g2 <= g2 /\
            preimage_group f g1 g2 h2.carrier <= g1 /\
            (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier /\
            (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1) /\
            IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
            PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier /\
            (FiniteGroup g1 ==>
              CARD (preimage_group f g1 g2 h2.carrier).carrier = CARD h2.carrier * CARD (kernel f g1 g2)) *)
(* Proof:
   Directly by lemma 1, 2, 3 and 4.
   Specifically, to show:
   (1) homo_image f h1 g2 <= g2, true                 by image_subgroup_subgroup
   (2) preimage_group f g1 g2 h2.carrier <= g1, true  by preimage_subgroup_subgroup
   (3) kernel f g1 g2 SUBSET PREIMAGE f h2.carrier INTER g1.carrier
       This is true                                   by preimage_subgroup_kernel
   (4) h2 << g2 <=> preimage_group f g1 g2 h2.carrier << g1
       This is true                                   by normal_iff_preimage_normal
   (5) IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier
       This is true                                   by bij_corres
   (6) PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier
       This is true                                   by bij_corres
   (7) CARD (preimage_group f g1 g2 h2.carrier).carrier =
       CARD h2.carrier * CARD (kernel f g1 g2)
       This is true                                   by preimage_cardinality
*)
val corres_thm = store_thm(
   "corres_thm",
   ``!f g1:'a group g2:'b group h1 h2.
   Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\
   h1 <= g1 /\ (kernel f g1 g2) SUBSET h1.carrier /\ h2 <= g2 ==>
   homo_image f h1 g2 <= g2 /\
   preimage_group f g1 g2 h2.carrier <= g1 /\
   (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier /\
   (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1) /\
   IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
   PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier /\
   (FiniteGroup g1 ==> CARD (preimage_group f g1 g2 h2.carrier).carrier =
                       CARD h2.carrier * CARD (kernel f g1 g2))``,
   rpt strip_tac >-
   metis_tac[image_subgroup_subgroup] >- metis_tac[preimage_subgroup_subgroup] >-
   metis_tac[preimage_subgroup_kernel] >- metis_tac[normal_iff_preimage_normal] >-
   metis_tac[bij_corres] >- metis_tac[bij_corres] >- metis_tac[preimage_cardinality]);

(* ------------------------------------------------------------------------- *)
(* Congruences Documentation                                                 *)
(* ------------------------------------------------------------------------- *)

(* Purpose:
   subgroupTheory has finite_abelian_Fermat
   groupInstancesTheory has Z_star and mult_mod
   For Z_star p, show that MOD_MUL_INV can be evaluted by Fermat's Little Theorem.
   For mult_mod p, show that MOD_MULT_INV can be evaluted by Fermat's Little Theorem.
*)

(* Definitions and Theorems (# are exported):

   Fermat's Little Theorem:
   fermat_little      |- !p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)
   fermat_little_alt  |- !p a. prime p ==> (a ** (p - 1) MOD p = if a MOD p = 0 then 0 else 1)
   fermat_little_thm  |- !p. prime p ==> !a. a ** p MOD p = a MOD p
   fermat_roots       |- !p. prime p ==> !x y z. (x ** p + y ** p = z ** p) ==> ((x + y) MOD p = z MOD p)

   Multiplicative Inverse by Fermat's Little Theorem:
   Zstar_inverse          |- !p. prime p ==> !a. 0 < a /\ a < p ==> ((Zstar p).inv a = a ** (p - 2) MOD p)
   Zstar_inverse_compute  |- !p a. (Zstar p).inv a =
                             if prime p /\ 0 < a /\ a < p then a ** (p - 2) MOD p else (Zstar p).inv a
   PRIME_2    |- prime 2
   PRIME_3    |- prime 3
   PRIME_5    |- prime 5
   PRIME_7    |- prime 7
   mult_mod_inverse          |- !p. prime p ==>
                                !a. 0 < a /\ a < p ==> ((mult_mod p).inv a = a ** (p - 2) MOD p)
   mult_mod_inverse_compute  |- !p a. (mult_mod p).inv a =
                                if prime p /\ 0 < a /\ a < p then a ** (p - 2) MOD p else (mult_mod p).inv a
*)

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem (by Zp finite abelian group)                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For prime p, 0 < a < p,  a**(p-1) = 1 (mod p) *)
(* Proof:
   Since 0 < a < p, a IN (Zstar p).carrier,
   and (Zstar p) is a FiniteAbelian Group, by Zstar_finite_abelian_group
   and CARD (Zstar p).carrier = (p-1)      by Zstar_property.
   this follows by finite_abelian_Fermat and Zstar_exp, which relates group_exp to EXP.

> finite_abelian_Fermat |> ISPEC ``(Zstar p)``;
val it = |- !a. FiniteAbelianGroup (Zstar p) /\ a IN (Zstar p).carrier ==>
                ((Zstar p).exp a (CARD (Zstar p).carrier) = (Zstar p).id): thm
*)
val fermat_little = store_thm(
  "fermat_little",
  ``!p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)``,
  rpt strip_tac >>
  `FiniteAbelianGroup (Zstar p)` by rw_tac std_ss[Zstar_finite_abelian_group] >>
  `a IN (Zstar p).carrier /\ ((Zstar p).id = 1)` by rw[Zstar_def, residue_def] >>
  `CARD (Zstar p).carrier = p - 1` by rw_tac std_ss[PRIME_POS, Zstar_property] >>
  metis_tac[finite_abelian_Fermat, Zstar_exp]);

(* Theorem: Fermat's Little Theorem for all a: (a**(p-1) MOD p = if (a MOD p = 0) then 0 else 1  when p is prime. *)
(* Proof: by cases of a, and restricted Fermat's Little Theorem. *)
val fermat_little_alt = store_thm(
  "fermat_little_alt",
  ``!p a. prime p ==> (a**(p-1) MOD p = if (a MOD p = 0) then 0 else 1)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  `a ** (p-1) MOD p = (a MOD p) ** (p-1) MOD p` by metis_tac[EXP_MOD] >>
  rw_tac std_ss[] >| [
    `0 < (p - 1)` by decide_tac >>
    `?k. (p - 1) = SUC k` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
    rw[EXP],
    `0 < a MOD p` by decide_tac >>
    `a MOD p < p` by rw[MOD_LESS] >>
    metis_tac[fermat_little]
  ]);

(* Theorem: For prime p, a**p = a (mod p) *)
(* Proof: by fermat_little. *)
val fermat_little_thm = store_thm(
  "fermat_little_thm",
  ``!p. prime p ==> !a. a ** p MOD p = a MOD p``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `a ** p MOD p = (a MOD p) ** p MOD p` by rw_tac std_ss[MOD_EXP] >>
  Cases_on `a MOD p = 0` >-
  metis_tac[ZERO_MOD, ZERO_EXP, NOT_ZERO_LT_ZERO] >>
  `0 < a MOD p` by decide_tac >>
  `a MOD p < p` by rw_tac std_ss[MOD_LESS] >>
  `p = SUC (p-1)` by decide_tac >>
  `(a MOD p) ** p MOD p = ((a MOD p) * (a MOD p) ** (p-1)) MOD p` by metis_tac[EXP] >>
  `_ = ((a MOD p) * (a MOD p) ** (p-1) MOD p) MOD p` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = ((a MOD p) * 1) MOD p` by rw_tac std_ss[fermat_little] >>
  `_ = a MOD p` by rw_tac std_ss[MULT_RIGHT_1, MOD_MOD] >>
  rw_tac std_ss[]);

(* Theorem: For prime p > 2, x ** p + y ** p = z ** p ==> x + y = z (mod p) *)
(* Proof:
        x ** p + y ** p = z ** p
   ==>  x ** p + y ** p = z ** p   mod p
   ==>       x +      y = z        mod p   by Fermat's Little Theorem.
*)
val fermat_roots = store_thm(
  "fermat_roots",
  ``!p. prime p ==> !x y z. (x ** p + y ** p = z ** p) ==> ((x + y) MOD p = z MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `z ** p MOD p = (x ** p + y ** p) MOD p` by rw_tac std_ss[] >>
  `_ = (x ** p MOD p + y ** p MOD p) MOD p` by metis_tac[MOD_PLUS] >>
  `_ = (x MOD p + y MOD p) MOD p` by rw_tac std_ss[fermat_little_thm] >>
  `_ = (x + y) MOD p` by rw_tac std_ss[MOD_PLUS] >>
  metis_tac[fermat_little_thm]);

(* ------------------------------------------------------------------------- *)
(* Multiplicative Inverse by Fermat's Little Theorem                         *)
(* ------------------------------------------------------------------------- *)

(* There is already:
- Zstar_inv;
> val it = |- !p. prime p ==> !x. 0 < x /\ x < p ==> ((Zstar p).inv x = (Zstar p).exp x (order (Zstar p) x - 1)) : thm
*)

(* Theorem: For prime p, (Zstar p).inv a = a**(p-2) MOD p *)
(* Proof:
   a * (a ** (p-2) MOD p = a**(p-1) MOD p = 1   by  fermat_little.
   Hence (a ** (p-2) MOD p) is the multiplicative inverse by group_rinv_unique.
*)
val Zstar_inverse = store_thm(
  "Zstar_inverse",
  ``!p. prime p ==> !a. 0 < a /\ a < p ==> ((Zstar p).inv a = (a**(p-2)) MOD p)``,
  rpt strip_tac >>
  `a IN (Zstar p).carrier` by rw_tac std_ss[Zstar_element] >>
  `Group (Zstar p)` by rw_tac std_ss[Zstar_group] >>
  `(Zstar p).id = 1` by rw_tac std_ss[Zstar_property] >>
  `(Zstar p).exp a (p-2) = a**(p-2) MOD p` by rw_tac std_ss[Zstar_exp] >>
  `0 < p` by decide_tac >>
  `SUC (p-2) = p - 1` by decide_tac >>
  `(Zstar p).op a (a**(p-2) MOD p) = (a * (a**(p-2) MOD p)) MOD p` by rw_tac std_ss[Zstar_property] >>
  `_ = ((a MOD p) * (a**(p-2) MOD p)) MOD p` by rw_tac std_ss[LESS_MOD] >>
  `_ = (a * a**(p-2)) MOD p` by rw_tac std_ss[MOD_TIMES2] >>
  `_ = a ** (p-1) MOD p` by metis_tac[EXP] >>
  `_ = 1` by rw_tac std_ss[fermat_little] >>
  metis_tac[group_rinv_unique, group_exp_element]);

(* Theorem: As function, for prime p, (Zstar p).inv a = a**(p-2) MOD p *)
(* Proof: by Zstar_inverse. *)
val Zstar_inverse_compute = store_thm(
  "Zstar_inverse_compute",
  ``!p a. (Zstar p).inv a =
          if (prime p /\ 0 < a /\ a < p) then (a**(p-2) MOD p) else ((Zstar p).inv a)``,
  rw_tac std_ss[Zstar_inverse]);

(* Theorem: 2 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_2 = store_thm(
  "PRIME_2",
  ``prime 2``,
  rw_tac std_ss  [prime_def] >>
  `0 < 2` by decide_tac >>
  `0 < b /\ b <= 2` by metis_tac[DIVIDES_LE, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  rw_tac arith_ss []);

(* Theorem: 3 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_3 = store_thm(
  "PRIME_3",
  ``prime 3``,
  rw_tac std_ss[prime_def] >>
  `b <= 3` by rw_tac std_ss[DIVIDES_LE] >>
  `(b=0) \/ (b=1) \/ (b=2) \/ (b=3)` by decide_tac >-
  fs[] >-
  fs[] >-
  full_simp_tac arith_ss [divides_def] >>
  metis_tac[]);

(* Theorem: 5 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_5 = store_thm(
  "PRIME_5",
  ``prime 5``,
  rw_tac std_ss[prime_def] >>
  `0 < 5` by decide_tac >>
  `0 < b /\ b <= 5` by metis_tac[DIVIDES_LE, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `(b = 1) \/ (b = 2) \/ (b = 3) \/ (b = 4) \/ (b = 5)` by decide_tac >-
  rw_tac std_ss[] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >>
  rw_tac std_ss[]);

(* Theorem: 7 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_7 = store_thm(
  "PRIME_7",
  ``prime 7``,
  rw_tac std_ss[prime_def] >>
  `0 < 7` by decide_tac >>
  `0 < b /\ b <= 7` by metis_tac[DIVIDES_LE, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `(b = 1) \/ (b = 2) \/ (b = 3) \/ (b = 4) \/ (b = 5) \/ (b = 6) \/ (b = 7)` by decide_tac >-
  rw_tac std_ss[] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >>
  rw_tac std_ss[]);

(* These computation uses Zstar_inv_compute of groupInstances.

- val _ = computeLib.add_persistent_funs ["PRIME_5"];
- EVAL ``prime 5``;
> val it = |- prime 5 <=> T : thm
- EVAL ``(Zstar 5).inv 2``;
> val it = |- (Zstar 5).inv 2 = 3 : thm
- EVAL ``(Zstar 5).id``;
> val it = |- (Zstar 5).id = 1 : thm
- EVAL ``(Zstar 5).op 2 3``;
> val it = |- (Zstar 5).op 2 3 = 1 : thm
- EVAL ``(Zstar 5).inv 2``;
> val it = |- (Zstar 5).inv 2 = 3 : thm
- EVAL ``(Zstar 5).inv 3``;
> val it = |- (Zstar 5).inv 3 = 2 : thm
*)


(*
val th = mk_thm([], ``MOD_MULT_INV 7 x = (x ** 5) MOD 7``);
val _ = save_thm("th", th);
val _ = computeLib.add_persistent_funs ["th"];

val _ = computeLib.add_persistent_funs [("Zstar5_inv", Zstar5_inv)];
EVAL ``(Zstar 5).op 2 3``;
> val it = |- (Zstar 5).op 2 3 = 1 : thm
EVAL ``(Zstar 5).inv 2``;
> val it = |- (Zstar 5).inv 2 = MOD_MUL_INV 5 2 : thm  (before)
> val it = |- (Zstar 5).inv 2 = 3 : thm
*)


(* There is already this in groupInstancesTheory:

- mult_mod_inv;
> val it = |- !p. prime p ==> !x. 0 < x /\ x < p ==> ((mult_mod p).inv x = (mult_mod p).exp x (order (mult_mod p) x - 1)) : thm
*)

(* Theorem: For prime p, (mult_mod p).inv a = a**(p-2) MOD p *)
(* Proof:
   a * (a ** (p-2) MOD p = a**(p-1) MOD p = 1   by  fermat_little.
   Hence (a ** (p-2) MOD p) is the multiplicative inverse by group_rinv_unique.
*)
val mult_mod_inverse = store_thm(
  "mult_mod_inverse",
  ``!p. prime p ==> !a. 0 < a /\ a < p ==> ((mult_mod p).inv a = (a**(p-2)) MOD p)``,
  rpt strip_tac >>
  `a IN (mult_mod p).carrier` by rw_tac std_ss[mult_mod_property] >>
  `Group (mult_mod p)` by rw_tac std_ss[mult_mod_group] >>
  `(mult_mod p).exp a (p-2) = (a**(p-2) MOD p)` by rw_tac std_ss[mult_mod_exp] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  `SUC (p-2) = p - 1` by decide_tac >>
  `(mult_mod p).exp a (p-2) IN (mult_mod p).carrier` by rw_tac std_ss[group_exp_element] >>
  `(mult_mod p).op a (a**(p-2) MOD p) = (a * (a**(p-2) MOD p)) MOD p` by rw_tac std_ss[mult_mod_property] >>
  `_ = (a * a**(p-2)) MOD p` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = a ** (p-1) MOD p` by metis_tac[EXP] >>
  `_ = 1` by rw_tac std_ss[fermat_little] >>
  metis_tac[group_rinv_unique, mult_mod_property]);

(* Theorem: As function, for prime p, (mult_mod p).inv a = a**(p-2) MOD p *)
(* Proof: by mult_mod_inverse. *)
val mult_mod_inverse_compute = store_thm(
  "mult_mod_inverse_compute",
  ``!p a. (mult_mod p).inv a =
          if (prime p /\ 0 < a /\ a < p) then (a**(p-2) MOD p) else (mult_mod p).inv a``,
  rw_tac std_ss[mult_mod_inverse]);

(* These computation uses mult_mod_inv_compute of groupInstances.

- val _ = computeLib.add_persistent_funs ["PRIME_7"];
- EVAL ``prime 7``;
> val it = |- prime 7 <=> T : thm
- EVAL ``(mult_mod 7).id``;
> val it = |- (mult_mod 7).id = 1 : thm
- EVAL ``(mult_mod 7).op 5 3``;
> val it = |- (mult_mod 7).op 5 3 = 1 : thm
- EVAL ``(mult_mod 7).inv 5``;
> val it = |- (mult_mod 7).inv 5 = 3 : thm
- EVAL ``(mult_mod 7).inv 3``;
> val it = |- (mult_mod 7).inv 3 = 5 : thm
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
