(* ------------------------------------------------------------------------- *)
(* Group Theory -- axioms to exponentiation.                                 *)
(* ------------------------------------------------------------------------- *)

(*

Group Theory
============
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
open pred_setTheory arithmeticTheory;

(* Get dependent theories local *)
(* val _ = load "monoidOrderTheory"; *)
open monoidTheory monoidOrderTheory; (* for G*, monoid_invertibles_is_monoid *)

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory;


(* ------------------------------------------------------------------------- *)
(* Group Documentation                                                      *)
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

(* Define Group by Monoid *)
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
(* Below is too much effort for a simple theorem. *)


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

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
