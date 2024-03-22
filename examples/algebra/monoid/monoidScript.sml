(* ------------------------------------------------------------------------- *)
(* Monoid                                                                    *)
(* ------------------------------------------------------------------------- *)

(*

Monoid Theory
=============
A monoid is a semi-group with an identity.
The units of a monoid form a group.
A finite, cancellative monoid is also a group.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoid";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory;

(* Get dependent theories in lib *)
(* val _ = load "helperNumTheory"; *)
(* val _ = load "helperSetTheory"; *)
open helperNumTheory helperSetTheory;


(* ------------------------------------------------------------------------- *)
(* Monoid Documentation                                                      *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   The generic symbol for monoid data is g.
   g.carrier = Carrier set of monoid, overloaded as G.
   g.op      = Binary operation of monoid, overloaded as *.
   g.id      = Identity element of monoid, overloaded as #e.

   Overloading:
   *              = g.op
   #e             = g.id
   **             = g.exp
   G              = g.carrier
   GITSET g s b   = ITSET g.op s b
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   Monoid_def                |- !g. Monoid g <=>
                                (!x y. x IN G /\ y IN G ==> x * y IN G) /\
                                (!x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y) * z = x * (y * z))) /\
                                #e IN G /\ (!x. x IN G ==> (#e * x = x) /\ (x * #e = x))
   AbelianMonoid_def         |- !g. AbelianMonoid g <=> Monoid g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
#  FiniteMonoid_def          |- !g. FiniteMonoid g <=> Monoid g /\ FINITE G
#  FiniteAbelianMonoid_def   |- !g. FiniteAbelianMonoid g <=> AbelianMonoid g /\ FINITE G

   Extract from definition:
#  monoid_id_element   |- !g. Monoid g ==> #e IN G
#  monoid_op_element   |- !g. Monoid g ==> !x y. x IN G /\ y IN G ==> x * y IN G
   monoid_assoc        |- !g. Monoid g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z))
   monoid_id           |- !g. Monoid g ==> !x. x IN G ==> (#e * x = x) /\ (x * #e = x)
#  monoid_lid          |- !g. Monoid g ==> !x. x IN G ==> (#e * x = x)
#  monoid_rid          |- !g. Monoid g ==> !x. x IN G ==> (x * #e = x)
#  monoid_id_id        |- !g. Monoid g ==> (#e * #e = #e)

   Simple theorems:
   FiniteAbelianMonoid_def_alt  |- !g. FiniteAbelianMonoid g <=> FiniteMonoid g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
   monoid_carrier_nonempty      |- !g. Monoid g ==> G <> {}
   monoid_lid_unique   |- !g. Monoid g ==> !e. e IN G ==> (!x. x IN G ==> (e * x = x)) ==> (e = #e)
   monoid_rid_unique   |- !g. Monoid g ==> !e. e IN G ==> (!x. x IN G ==> (x * e = x)) ==> (e = #e)
   monoid_id_unique    |- !g. Monoid g ==> !e. e IN G ==> ((!x. x IN G ==> (x * e = x) /\ (e * x = x)) <=> (e = #e))

   Iteration of the binary operation gives exponentiation:
   monoid_exp_def      |- !g x n. x ** n = FUNPOW ($* x) n #e
#  monoid_exp_0        |- !g x. x ** 0 = #e
#  monoid_exp_SUC      |- !g x n. x ** SUC n = x * x ** n
#  monoid_exp_element  |- !g. Monoid g ==> !x. x IN G ==> !n. x ** n IN G
#  monoid_exp_1        |- !g. Monoid g ==> !x. x IN G ==> (x ** 1 = x)
#  monoid_id_exp       |- !g. Monoid g ==> !n. #e ** n = #e

   Monoid commutative elements:
   monoid_comm_exp      |- !g. Monoid g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) ==> !n. x ** n * y = y * x ** n
   monoid_exp_comm      |- !g. Monoid g ==> !x. x IN G ==> !n. x ** n * x = x * x ** n
#  monoid_exp_suc       |- !g. Monoid g ==> !x. x IN G ==> !n. x ** SUC n = x ** n * x
   monoid_comm_op_exp   |- !g. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                          !n. (x * y) ** n = x ** n * y ** n
   monoid_comm_exp_exp  |- !g. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                           !n m. x ** n * y ** m = y ** m * x ** n
#  monoid_exp_add       |- !g. Monoid g ==> !x. x IN G ==> !n k. x ** (n + k) = x ** n * x ** k
#  monoid_exp_mult      |- !g. Monoid g ==> !x. x IN G ==> !n k. x ** (n * k) = (x ** n) ** k
   monoid_exp_mult_comm |- !g. Monoid g ==> !x. x IN G ==> !m n. (x ** m) ** n = (x ** n) ** m


   Finite Monoid:
   finite_monoid_exp_not_distinct  |- !g. FiniteMonoid g ==> !x. x IN G ==>
                                          ?h k. (x ** h = x ** k) /\ h <> k

   Abelian Monoid ITSET Theorems:
   GITSET_THM      |- !s g b. FINITE s ==> (GITSET g s b = if s = {} then b
                                                           else GITSET g (REST s) (CHOICE s * b))
   GITSET_EMPTY    |- !g b. GITSET g {} b = b
   GITSET_INSERT   |- !x. FINITE s ==>
                      !x g b. (GITSET g (x INSERT s) b = GITSET g (REST (x INSERT s)) (CHOICE (x INSERT s) * b))
   GITSET_PROPERTY |- !g s. FINITE s /\ s <> {} ==> !b. GITSET g s b = GITSET g (REST s) (CHOICE s * b)

   abelian_monoid_op_closure_comm_assoc_fun   |- !g. AbelianMonoid g ==> closure_comm_assoc_fun $* G
   COMMUTING_GITSET_INSERT      |- !g s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
                                   !b x::G. GITSET g (x INSERT s) b = GITSET g (s DELETE x) (x * b)
   COMMUTING_GITSET_REDUCTION   |- !g s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
                                   !b x::G. GITSET g s (x * b) = x * GITSET g s b
   COMMUTING_GITSET_RECURSES    |- !g s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
                                   !b x::G. GITSET g (x INSERT s) b = x * GITSET g (s DELETE x) b:

   Abelian Monoid PROD_SET:
   GPROD_SET_def      |- !g s. GPROD_SET g s = GITSET g s #e
   GPROD_SET_THM      |- !g s. (GPROD_SET g {} = #e) /\
                               (AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
                                !x::(G). GPROD_SET g (x INSERT s) = x * GPROD_SET g (s DELETE x))
   GPROD_SET_EMPTY    |- !g s. GPROD_SET g {} = #e
   GPROD_SET_SING     |- !g. Monoid g ==> !x. x IN G ==> (GPROD_SET g {x} = x)
   GPROD_SET_PROPERTY |- !g s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==> GPROD_SET g s IN G

*)

(* ------------------------------------------------------------------------- *)
(* Monoid Definition.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Monoid and Group share the same type *)

(* Set up monoid type as a record
   A Monoid has:
   . a carrier set (set = function 'a -> bool, since MEM is a boolean function)
   . a binary operation (2-nary function) called multiplication
   . an identity element for the binary operation
*)
val _ = Hol_datatype`
  monoid = <| carrier: 'a -> bool;
                   op: 'a -> 'a -> 'a;
                   id: 'a
            |>`;
(* If the field  inv: 'a -> 'a; is included,
   there will be an implicit monoid_inv accessor generated.
   Later, when monoid_inv_def defines another monoid_inv,
   the monoid_accessors will ALL be invalidated!
   So, do not include the field inv here,
   but use add_record_field ("inv", ``monoid_inv``)
   to achieve the same effect.
*)

(* Using symbols m for monoid and g for group
   will give excessive overloading for Monoid and Group,
   so the generic symbol for both is taken as g. *)
(* set overloading  *)
val _ = overload_on ("*", ``g.op``);
val _ = overload_on ("#e", ``g.id``);
val _ = overload_on ("G", ``g.carrier``);

(* Monoid Definition:
   A Monoid is a set with elements of type 'a monoid, such that
   . Closure: x * y is in the carrier set
   . Associativity: (x * y) * z = x * (y * z))
   . Existence of identity: #e is in the carrier set
   . Property of identity: #e * x = x * #e = x
*)
(* Define Monoid by predicate *)
val Monoid_def = Define`
  Monoid (g:'a monoid) <=>
    (!x y. x IN G /\ y IN G ==> x * y IN G) /\
    (!x y z. x IN G /\ y IN G /\ z IN G ==> ((x * y) * z = x * (y * z))) /\
    #e IN G /\ (!x. x IN G ==> (#e * x = x) /\ (x * #e = x))
`;
(* export basic definition -- but too many and's. *)
(* val _ = export_rewrites ["Monoid_def"]; *)

(* ------------------------------------------------------------------------- *)
(* More Monoid Defintions.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Abelian Monoid = a Monoid that is commutative: x * y = y * x. *)
val AbelianMonoid_def = Define`
  AbelianMonoid (g:'a monoid) <=>
    Monoid g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
`;
(* export simple definition -- but this one has commutativity, so don't. *)
(* val _ = export_rewrites ["AbelianMonoid_def"]; *)

(* Finite Monoid = a Monoid with a finite carrier set. *)
val FiniteMonoid_def = Define`
  FiniteMonoid (g:'a monoid) <=>
    Monoid g /\ FINITE G
`;
(* export simple definition. *)
val _ = export_rewrites ["FiniteMonoid_def"];

(* Finite Abelian Monoid = a Monoid that is both Finite and Abelian. *)
val FiniteAbelianMonoid_def = Define`
  FiniteAbelianMonoid (g:'a monoid) <=>
    AbelianMonoid g /\ FINITE G
`;
(* export simple definition. *)
val _ = export_rewrites ["FiniteAbelianMonoid_def"];

(* ------------------------------------------------------------------------- *)
(* Basic theorems from definition.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Finite Abelian Monoid = Finite Monoid /\ commutativity. *)
(* Proof: by definitions. *)
val FiniteAbelianMonoid_def_alt = store_thm(
  "FiniteAbelianMonoid_def_alt",
  ``!g:'a monoid. FiniteAbelianMonoid g <=>
       FiniteMonoid g /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)``,
  rw[AbelianMonoid_def, EQ_IMP_THM]);

(* Monoid clauses from definition, in implicative form, no for-all, internal use only. *)
val monoid_clauses = Monoid_def |> SPEC_ALL |> #1 o EQ_IMP_RULE;
(* > val monoid_clauses =
    |- Monoid g ==>
       (!x y. x IN G /\ y IN G ==> x * y IN G) /\
       (!x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z))) /\
       #e IN G /\ !x. x IN G ==> (#e * x = x) /\ (x * #e = x) : thm *)

(* Extract theorems from Monoid clauses. *)
(* No need to export as definition is already exported. *)

(* Theorem: [Closure] x * y in carrier. *)
val monoid_op_element = save_thm("monoid_op_element",
  monoid_clauses |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val monoid_op_element = |- !g. Monoid g ==> !x y. x IN G /\ y IN G ==> x * y IN G : thm*)

(* Theorem: [Associativity] (x * y) * z = x * (y * z) *)
val monoid_assoc = save_thm("monoid_assoc",
  monoid_clauses |> UNDISCH_ALL |> CONJUNCT2|> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val monoid_assoc = |- !g. Monoid g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * y * z = x * (y * z)) : thm *)

(* Theorem: [Identity exists] #e in carrier. *)
val monoid_id_element = save_thm("monoid_id_element",
  monoid_clauses |> UNDISCH_ALL |> CONJUNCT2|> CONJUNCT2 |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val monoid_id_element = |- !g. Monoid g ==> #e IN G : thm *)

(* Theorem: [Identity property] #e * x = x  and x * #e = x *)
val monoid_id = save_thm("monoid_id",
  monoid_clauses |> UNDISCH_ALL |> CONJUNCT2|> CONJUNCT2 |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val monoid_id = |- !g. Monoid g ==> !x. x IN G ==> (#e * x = x) /\ (x * #e = x) : thm *)

(* Theorem: [Left identity] #e * x = x *)
(* Proof: from monoid_id. *)
val monoid_lid = save_thm("monoid_lid",
  monoid_id |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1
            |> DISCH ``x IN G`` |> GEN_ALL |> DISCH_ALL |> GEN_ALL);
(* > val monoid_lid = |- !g. Monoid g ==> !x. x IN G ==> (#e * x = x) : thm *)

(* Theorem: [Right identity] x * #e = x *)
(* Proof: from monoid_id. *)
val monoid_rid = save_thm("monoid_rid",
  monoid_id |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
            |> DISCH ``x IN G`` |> GEN_ALL |> DISCH_ALL |> GEN_ALL);
(* > val monoid_rid = |- !g. Monoid g ==> !x. x IN G ==> (x * #e = x) : thm *)

(* export simple statements (no complicated and's) *)
val _ = export_rewrites ["monoid_op_element"];
(* val _ = export_rewrites ["monoid_assoc"]; -- no associativity *)
val _ = export_rewrites ["monoid_id_element"];
val _ = export_rewrites ["monoid_lid"];
val _ = export_rewrites ["monoid_rid"];

(* Theorem: #e * #e = #e *)
(* Proof:
   by monoid_lid and monoid_id_element.
*)
val monoid_id_id = store_thm(
  "monoid_id_id",
  ``!g:'a monoid. Monoid g ==> (#e * #e = #e)``,
  rw[]);

val _ = export_rewrites ["monoid_id_id"];

(* ------------------------------------------------------------------------- *)
(* Theorems in basic Monoid Theory.                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Monoid carrier nonempty] G <> {} *)
(* Proof: by monoid_id_element. *)
val monoid_carrier_nonempty = store_thm(
  "monoid_carrier_nonempty",
  ``!g:'a monoid. Monoid g ==> G <> {}``,
  metis_tac[monoid_id_element, MEMBER_NOT_EMPTY]);

(* Theorem: [Left Identity unique] !x. (e * x = x) ==> e = #e *)
(* Proof:
   Put x = #e,
   then e * #e = #e  by given
   but  e * #e = e   by monoid_rid
   hence e = #e.
*)
val monoid_lid_unique = store_thm(
  "monoid_lid_unique",
  ``!g:'a monoid. Monoid g ==> !e. e IN G ==> ((!x. x IN G ==> (e * x = x)) ==> (e = #e))``,
  metis_tac[monoid_id_element, monoid_rid]);

(* Theorem: [Right Identity unique] !x. (x * e = x) ==> e = #e *)
(* Proof:
   Put x = #e,
   then #e * e = #e  by given
   but  #e * e = e   by monoid_lid
   hence e = #e.
*)
val monoid_rid_unique = store_thm(
  "monoid_rid_unique",
  ``!g:'a monoid. Monoid g ==> !e. e IN G ==> ((!x. x IN G ==> (x * e = x)) ==> (e = #e))``,
  metis_tac[monoid_id_element, monoid_lid]);

(* Theorem: [Identity unique] !x. (x * e = x)  and  (e * x = x) <=> e = #e *)
(* Proof:
   If e, #e are two identities,
   For e, put x = #e, #e*e = #e and e*#e = #e
   For #e, put x = e, e*#e = e  and #e*e = e
   Therefore e = #e.
*)
val monoid_id_unique = store_thm(
  "monoid_id_unique",
  ``!g:'a monoid. Monoid g ==> !e. e IN G ==> ((!x. x IN G ==> (x * e = x) /\ (e * x = x)) <=> (e = #e))``,
  metis_tac[monoid_id_element, monoid_id]);


(* ------------------------------------------------------------------------- *)
(* Application of basic Monoid Theory:                                       *)
(* Exponentiation - the FUNPOW version of Monoid operation.                  *)
(* ------------------------------------------------------------------------- *)

(* Define exponents of a monoid element:
   For x in Monoid g,   x ** 0 = #e
                        x ** (SUC n) = x * (x ** n)
*)
(*
val monoid_exp_def = Define`
  (monoid_exp m x 0 = g.id) /\
  (monoid_exp m x (SUC n) = x * (monoid_exp m x n))
`;
*)
val monoid_exp_def = Define `monoid_exp (g:'a monoid) (x:'a) n = FUNPOW (g.op x) n #e`;
(* val _ = export_rewrites ["monoid_exp_def"]; *)
(*
- monoid_exp_def;
> val it = |- !g x n. x ** n = FUNPOW ($* x) n #e : thm
*)

(* export simple properties later *)
(* val _ = export_rewrites ["monoid_exp_def"]; *)

(* Convert exp function to exp field, i.e. g.exp is defined to be monoid_exp. *)
val _ = add_record_field ("exp", ``monoid_exp``);
(*
- type_of ``g.exp``;
> val it = ``:'a -> num -> 'a`` : hol_type
*)
(* overloading  *)
(* val _ = clear_overloads_on "**"; *)
(* val _ = overload_on ("**", ``monoid_exp g``); -- not this *)
val _ = overload_on ("**", ``g.exp``);

(* Theorem: x ** 0 = #e *)
(* Proof: by definition and FUNPOW_0. *)
val monoid_exp_0 = store_thm(
  "monoid_exp_0",
  ``!g:'a monoid. !x:'a. x ** 0 = #e``,
  rw[monoid_exp_def]);

val _ = export_rewrites ["monoid_exp_0"];

(* Theorem: x ** (SUC n) = x * (x ** n) *)
(* Proof: by definition and FUNPOW_SUC. *)
val monoid_exp_SUC = store_thm(
  "monoid_exp_SUC",
  ``!g:'a monoid. !x:'a. !n. x ** (SUC n) = x * (x ** n)``,
  rw[monoid_exp_def, FUNPOW_SUC]);

(* should this be exported? Only FUNPOW_0 is exported. *)
val _ = export_rewrites ["monoid_exp_SUC"];

(* Theorem: (x ** n) in G *)
(* Proof: by induction on n.
   Base case: x ** 0 IN G
     x ** 0 = #e     by monoid_exp_0
              in G   by monoid_id_element.
   Step case: x ** n IN G ==> x ** SUC n IN G
     x ** SUC n
   = x * (x ** n)    by monoid_exp_SUC
     in G            by monoid_op_element and induction hypothesis
*)
val monoid_exp_element = store_thm(
  "monoid_exp_element",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !n. (x ** n) IN G``,
  rpt strip_tac>>
  Induct_on `n` >>
  rw[]);

val _ = export_rewrites ["monoid_exp_element"];

(* Theorem: x ** 1 = x *)
(* Proof:
     x ** 1
   = x ** SUC 0     by ONE
   = x * x ** 0     by monoid_exp_SUC
   = x * #e         by monoid_exp_0
   = x              by monoid_rid
*)
val monoid_exp_1 = store_thm(
  "monoid_exp_1",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> (x ** 1 = x)``,
  rewrite_tac[ONE] >>
  rw[]);

val _ = export_rewrites ["monoid_exp_1"];

(* Theorem: (#e ** n) = #e  *)
(* Proof: by induction on n.
   Base case: #e ** 0 = #e
      true by monoid_exp_0.
   Step case: #e ** n = #e ==> #e ** SUC n = #e
        #e ** SUC n
      = #e * #e ** n    by monoid_exp_SUC, monoid_id_element
      = #e ** n         by monoid_lid, monoid_exp_element
      hence true by induction hypothesis.
*)
val monoid_id_exp = store_thm(
  "monoid_id_exp",
  ``!g:'a monoid. Monoid g ==> !n. #e ** n = #e``,
  rpt strip_tac>>
  Induct_on `n` >>
  rw[]);

val _ = export_rewrites ["monoid_id_exp"];

(* Theorem: For Abelian Monoid g,  (x ** n) * y = y * (x ** n) *)
(* Proof:
   Since x ** n IN G     by monoid_exp_element
   True by abelian property: !z y. z IN G /\ y IN G ==> z * y = y * z
*)
(* This is trivial for AbelianMonoid, since every element commutes.
   However, what is needed is just for those elements that commute. *)

(* Theorem: x * y = y * x ==> (x ** n) * y = y * (x ** n) *)
(* Proof:
   By induction on n.
   Base case: x ** 0 * y = y * x ** 0
     (x ** 0) * y
   = #e * y            by monoid_exp_0
   = y * #e            by monoid_id
   = y * (x ** 0)      by monoid_exp_0
   Step case: x ** n * y = y * x ** n ==> x ** SUC n * y = y * x ** SUC n
     x ** (SUC n) * y
   = (x * x ** n) * y    by monoid_exp_SUC
   = x * ((x ** n) * y)  by monoid_assoc
   = x * (y * (x ** n))  by induction hypothesis
   = (x * y) * (x ** n)  by monoid_assoc
   = (y * x) * (x ** n)  by abelian property
   = y * (x * (x ** n))  by monoid_assoc
   = y * x ** (SUC n)    by monoid_exp_SUC
*)
val monoid_comm_exp = store_thm(
  "monoid_comm_exp",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) ==> !n. (x ** n) * y = y * (x ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[monoid_exp_SUC, monoid_assoc, monoid_exp_element]);

(* do not export commutativity check *)
(* val _ = export_rewrites ["monoid_comm_exp"]; *)

(* Theorem: (x ** n) * x = x * (x ** n) *)
(* Proof:
   Since x * x = x * x, this is true by monoid_comm_exp.
*)
val monoid_exp_comm = store_thm(
  "monoid_exp_comm",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !n. (x ** n) * x = x * (x ** n)``,
  rw[monoid_comm_exp]);

(* no export of commutativity *)
(* val _ = export_rewrites ["monoid_exp_comm"]; *)

(* Theorem: x ** (SUC n) = (x ** n) * x *)
(* Proof: by monoid_exp_SUC and monoid_exp_comm. *)
val monoid_exp_suc = store_thm(
  "monoid_exp_suc",
  ``!g:'a monoid. Monoid g ==> !x:'a. x IN G ==> !n. x ** (SUC n) = (x ** n) * x``,
  rw[monoid_exp_comm]);

(* no export of commutativity *)
(* val _ = export_rewrites ["monoid_exp_suc"]; *)

(* Theorem: x * y = y * x ==> (x * y) ** n = (x ** n) * (y ** n) *)
(* Proof:
   By induction on n.
   Base case: (x * y) ** 0 = x ** 0 * y ** 0
     (x * y) ** 0
   = #e                     by monoid_exp_0
   = #e * #e                by monoid_id_id
   = (x ** 0) * (y ** 0)    by monoid_exp_0
   Step case: (x * y) ** n = (x ** n) * (y ** n) ==>  (x * y) ** SUC n = x ** SUC n * y ** SUC n
     (x * y) ** (SUC n)
   = (x * y) * ((x * y) ** n)         by monoid_exp_SUC
   = (x * y) * ((x ** n) * (y ** n))  by induction hypothesis
   = x * (y * ((x ** n) * (y ** n)))  by monoid_assoc
   = x * ((y * (x ** n)) * (y ** n))  by monoid_assoc
   = x * (((x ** n) * y) * (y ** n))  by monoid_comm_exp
   = x * ((x ** n) * (y * (y ** n)))  by monoid_assoc
   = (x * (x ** n)) * (y * (y ** n))  by monoid_assoc
*)
val monoid_comm_op_exp = store_thm(
  "monoid_comm_op_exp",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==> !n. (x * y) ** n = (x ** n) * (y ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `(x * y) ** SUC n = x * ((y * (x ** n)) * (y ** n))` by rw[monoid_assoc] >>
  `_ = x * (((x ** n) * y) * (y ** n))` by metis_tac[monoid_comm_exp] >>
  rw[monoid_assoc]);

(* do not export commutativity check *)
(* val _ = export_rewrites ["monoid_comm_op_exp"]; *)

(* Theorem: x IN G /\ y IN G /\ x * y = y * x ==> (x ** n) * (y ** m) = (y ** m) * (x ** n) *)
(* Proof:
   By inducton on m.
   Base case: x ** n * y ** 0 = y ** 0 * x ** n
   LHS = x ** n * y ** 0
       = x ** n * #e         by monoid_exp_0
       = x ** n              by monoid_rid
       = #e * x ** n         by monoid_lid
       = y ** 0 * x ** n     by monoid_exp_0
       = RHS
   Step case: x ** n * y ** m = y ** m * x ** n ==> x ** n * y ** SUC m = y ** SUC m * x ** n
   LHS = x ** n * y ** SUC m
       = x ** n * (y * y ** m)    by monoid_exp_SUC
       = (x ** n * y) * y ** m    by monoid_assoc
       = (y * x ** n) * y ** m    by monoid_comm_exp (with single y)
       = y * (x ** n * y ** m)    by monoid_assoc
       = y * (y ** m * x ** n)    by induction hypothesis
       = (y * y ** m) * x ** n    by monoid_assoc
       = y ** SUC m  * x ** n     by monoid_exp_SUC
       = RHS
*)
val monoid_comm_exp_exp = store_thm(
  "monoid_comm_exp_exp",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
   !n m. x ** n * y ** m = y ** m * x ** n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  `x ** n * y ** SUC m = x ** n * (y * y ** m)` by rw[] >>
  `_ = (x ** n * y) * y ** m` by rw[monoid_assoc] >>
  `_ = (y * x ** n) * y ** m` by metis_tac[monoid_comm_exp] >>
  `_ = y * (x ** n * y ** m)` by rw[monoid_assoc] >>
  `_ = y * (y ** m * x ** n)` by metis_tac[] >>
  rw[monoid_assoc]);

(* Theorem: x ** (n + k) = (x ** n) * (x ** k) *)
(* Proof:
   By induction on n.
   Base case: x ** (0 + k) = x ** 0 * x ** k
     x ** (0 + k)
   = x ** k               by arithmetic
   = #e * (x ** k)        by monoid_lid
   = (x ** 0) * (x ** k)  by monoid_exp_0
   Step case: x ** (n + k) = x ** n * x ** k ==> x ** (SUC n + k) = x ** SUC n * x ** k
     x ** (SUC n + k)
   = x ** (SUC (n + k))         by arithmetic
   = x * (x ** (n + k))         by monoid_exp_SUC
   = x * ((x ** n) * (x ** k))  by induction hypothesis
   = (x * (x ** n)) * (x ** k)  by monoid_assoc
   = (x ** SUC n) * (x ** k)    by monoid_exp_def
*)
val monoid_exp_add = store_thm(
  "monoid_exp_add",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !n k. x ** (n + k) = (x ** n) * (x ** k)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[monoid_exp_SUC, monoid_assoc, monoid_exp_element, DECIDE ``SUC n + k = SUC (n+k)``]);

(* export simple result *)
val _ = export_rewrites ["monoid_exp_add"];

(* Theorem: x ** (n * k) = (x ** n) ** k  *)
(* Proof:
   By induction on n.
   Base case: x ** (0 * k) = (x ** 0) ** k
     x ** (0 * k)
   = x ** 0               by arithmetic
   = #e                   by monoid_exp_0
   = (#e) ** n            by monoid_id_exp
   = (x ** 0) ** n        by monoid_exp_0
   Step case: x ** (n * k) = (x ** n) ** k ==> x ** (SUC n * k) = (x ** SUC n) ** k
     x ** (SUC n * k)
   = x ** (n * k + k)             by arithmetic
   = (x ** (n * k)) * (x ** k)    by monoid_exp_add
   = ((x ** n) ** k) * (x ** k)   by induction hypothesis
   = ((x ** n) * x) ** k          by monoid_comm_op_exp and monoid_exp_comm
   = (x * (x ** n)) ** k          by monoid_exp_comm
   = (x ** SUC n) ** k            by monoid_exp_def
*)
val monoid_exp_mult = store_thm(
  "monoid_exp_mult",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !n k. x ** (n * k) = (x ** n) ** k``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `SUC n * k = n * k + k` by metis_tac[MULT] >>
  `x ** (SUC n * k) = ((x ** n) * x) ** k` by rw_tac std_ss[monoid_comm_op_exp, monoid_exp_comm, monoid_exp_element, monoid_exp_add] >>
  rw[monoid_exp_comm]);

(* export simple result *)
val _ = export_rewrites ["monoid_exp_mult"];

(* Theorem: x IN G ==> (x ** m) ** n = (x ** n) ** m *)
(* Proof:
     (x ** m) ** n
   = x ** (m * n)    by monoid_exp_mult
   = x ** (n * m)    by MULT_COMM
   = (x ** n) ** m   by monoid_exp_mult
*)
val monoid_exp_mult_comm = store_thm(
  "monoid_exp_mult_comm",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !m n. (x ** m) ** n = (x ** n) ** m``,
  metis_tac[monoid_exp_mult, MULT_COMM]);


(* ------------------------------------------------------------------------- *)
(* Finite Monoid.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For FINITE Monoid g and x IN G, x ** k cannot be all distinct. *)
(* Proof:
   By contradiction. Assume !k h. x ** k = x ** h ==> k = h, then
   Since G is FINITE, let c = CARD G.
   The map (count (SUC c)) -> G such that n -> x ** n is:
   (1) a map since each x ** n IN G
   (2) injective since all x ** n are distinct
   But c < SUC c = CARD (count (SUC c)), and this contradicts the Pigeon-hole Principle.
*)
val finite_monoid_exp_not_distinct = store_thm(
  "finite_monoid_exp_not_distinct",
  ``!g:'a monoid. FiniteMonoid g ==> !x. x IN G ==> ?h k. (x ** h = x ** k) /\ (h <> k)``,
  rw[FiniteMonoid_def] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `c = CARD G` >>
  `INJ (\n. x ** n) (count (SUC c)) G` by rw[INJ_DEF] >>
  `c < SUC c` by decide_tac >>
  metis_tac[CARD_COUNT, PHP]);
(*
This theorem implies that, if x ** k are all distinct for a Monoid g,
then its carrier G must be INFINITE.
Otherwise, this is not immediately useful for a Monoid, as the op has no inverse.
However, it is useful for a Group, where the op has inverse,
hence reduce this to x ** (h-k) = #e, if h > k.
Also, it is useful for an Integral Domain, where the prod.op still has no inverse,
but being a Ring, it has subtraction and distribution, giving  x ** k * (x ** (h-k) - #1) = #0
from which the no-zero-divisor property of Integral Domain gives x ** (h-k) = #1.
*)

(* ------------------------------------------------------------------------- *)
(* Abelian Monoid ITSET Theorems                                             *)
(* ------------------------------------------------------------------------- *)

(* Define ITSET for Monoid -- fold of g.op, especially for Abelian Monoid (by lifting) *)
val _ = overload_on("GITSET", ``\(g:'a monoid) s b. ITSET g.op s b``);

(*
> ITSET_def |> ISPEC ``s:'b -> bool`` |> ISPEC ``(g:'a monoid).op`` |> ISPEC ``b:'a``;
val it = |- GITSET g s b = if FINITE s then if s = {} then b else GITSET g (REST s) (CHOICE s * b)
                           else ARB: thm
*)

fun gINST th = th |> SPEC_ALL |> INST_TYPE [beta |-> alpha]
                  |> Q.INST [`f` |-> `g.op`] |> GEN_ALL;
(* val gINST = fn: thm -> thm *)

val GITSET_THM = save_thm("GITSET_THM", gINST ITSET_THM);
(* > val GITSET_THM =
  |- !s g b. FINITE s ==> (GITSET g s b = if s = {} then b else GITSET g (REST s) (CHOICE s * b)) : thm
*)

(* Theorem: GITSET {} b = b *)
val GITSET_EMPTY = save_thm("GITSET_EMPTY", gINST ITSET_EMPTY);
(* > val GITSET_EMPTY = |- !g b. GITSET g {} b = b : thm *)

(* Theorem: GITSET g (x INSERT s) b = GITSET g (REST (x INSERT s)) ((CHOICE (x INSERT s)) * b) *)
(* Proof:
   By GITSET_THM, since x INSERT s is non-empty.
*)
val GITSET_INSERT = save_thm(
  "GITSET_INSERT",
  gINST (ITSET_INSERT |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL);
(* > val GITSET_INSERT =
  |- !s. FINITE s ==> !x g b. (GITSET g (x INSERT s) b = GITSET g (REST (x INSERT s)) (CHOICE (x INSERT s) * b)) : thm
*)

(* Theorem: [simplified GITSET_INSERT]
            FINITE s /\ s <> {} ==> GITSET g s b = GITSET g (REST s) ((CHOICE s) * b) *)
(* Proof:
   Replace (x INSERT s) in GITSET_INSERT by s,
   GITSET g s b = GITSET g (REST s) ((CHOICE s) * b)
   Since CHOICE s IN s             by CHOICE_DEF
     so (CHOICE s) INSERT s = s    by ABSORPTION
   and the result follows.
*)
val GITSET_PROPERTY = store_thm(
  "GITSET_PROPERTY",
  ``!g s. FINITE s /\ s <> {} ==> !b. GITSET g s b = GITSET g (REST s) ((CHOICE s) * b)``,
  metis_tac[CHOICE_DEF, ABSORPTION, GITSET_INSERT]);

(* Theorem: AbelianMonoid g ==> closure_comm_assoc_fun g.op G *)
(* Proof:
   Note Monoid g /\ !x y::(G). x * y = y * x   by AbelianMonoid_def
    and !x y z::(G). x * y * z = y * x * z     by monoid_assoc, above gives commutativity
   Thus closure_comm_assoc_fun g.op G          by closure_comm_assoc_fun_def
*)
val abelian_monoid_op_closure_comm_assoc_fun = store_thm(
  "abelian_monoid_op_closure_comm_assoc_fun",
  ``!g:'a monoid. AbelianMonoid g ==> closure_comm_assoc_fun g.op G``,
  rw[AbelianMonoid_def, closure_comm_assoc_fun_def] >>
  metis_tac[monoid_assoc]);

(* Theorem: AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
            !b x::(G). GITSET g (x INSERT s) b = GITSET g (s DELETE x) (x * b) *)
(* Proof:
   Note closure_comm_assoc_fun g.op G          by abelian_monoid_op_closure_comm_assoc_fun
   The result follows                          by SUBSET_COMMUTING_ITSET_INSERT
*)
val COMMUTING_GITSET_INSERT = store_thm(
  "COMMUTING_GITSET_INSERT",
  ``!(g:'a monoid) s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
   !b x::(G). GITSET g (x INSERT s) b = GITSET g (s DELETE x) (x * b)``,
  metis_tac[abelian_monoid_op_closure_comm_assoc_fun, SUBSET_COMMUTING_ITSET_INSERT]);

(* Theorem: AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
            !b x::(G). GITSET g s (x * b) = x * (GITSET g s b) *)
(* Proof:
   Note closure_comm_assoc_fun g.op G          by abelian_monoid_op_closure_comm_assoc_fun
   The result follows                          by SUBSET_COMMUTING_ITSET_REDUCTION
*)
val COMMUTING_GITSET_REDUCTION = store_thm(
  "COMMUTING_GITSET_REDUCTION",
  ``!(g:'a monoid) s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
   !b x::(G). GITSET g s (x * b) = x * (GITSET g s b)``,
  metis_tac[abelian_monoid_op_closure_comm_assoc_fun, SUBSET_COMMUTING_ITSET_REDUCTION]);

(* Theorem: AbelianMonoid g ==> GITSET g (x INSERT s) b = x * (GITSET g (s DELETE x) b) *)
(* Proof:
   Note closure_comm_assoc_fun g.op G          by abelian_monoid_op_closure_comm_assoc_fun
   The result follows                          by SUBSET_COMMUTING_ITSET_RECURSES
*)
val COMMUTING_GITSET_RECURSES = store_thm(
  "COMMUTING_GITSET_RECURSES",
  ``!(g:'a monoid) s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
   !b x::(G). GITSET g (x INSERT s) b = x * (GITSET g (s DELETE x) b)``,
  metis_tac[abelian_monoid_op_closure_comm_assoc_fun, SUBSET_COMMUTING_ITSET_RECURSES]);

(* ------------------------------------------------------------------------- *)
(* Abelian Monoid PROD_SET                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define GPROD_SET via GITSET *)
val GPROD_SET_def = Define `GPROD_SET g s = GITSET g s #e`;

(* Theorem: property of GPROD_SET *)
(* Proof:
   This is to prove:
   (1) GITSET g {} #e = #e
       True by GITSET_EMPTY, and monoid_id_element.
   (2) GITSET g (x INSERT s) #e = x * GITSET g (s DELETE x) #e
       True by COMMUTING_GITSET_RECURSES, and monoid_id_element.
*)
val GPROD_SET_THM = store_thm(
  "GPROD_SET_THM",
  ``!g s. (GPROD_SET g {} = #e) /\
   (AbelianMonoid g /\ FINITE s /\ s SUBSET G ==>
      (!x::(G). GPROD_SET g (x INSERT s) = x * GPROD_SET g (s DELETE x)))``,
  rw[GPROD_SET_def, RES_FORALL_THM, GITSET_EMPTY] >>
  `Monoid g` by metis_tac[AbelianMonoid_def] >>
  metis_tac[COMMUTING_GITSET_RECURSES, monoid_id_element]);

(* Theorem: GPROD_SET g {} = #e *)
(* Proof:
     GPROD_SET g {}
   = GITSET g {} #e  by GPROD_SET_def
   = #e              by GITSET_EMPTY
   or directly       by GPROD_SET_THM
*)
val GPROD_SET_EMPTY = store_thm(
  "GPROD_SET_EMPTY",
  ``!g s. GPROD_SET g {} = #e``,
  rw[GPROD_SET_def, GITSET_EMPTY]);

(* Theorem: Monoid g ==> !x. x IN G ==> (GPROD_SET g {x} = x) *)
(* Proof:
      GPROD_SET g {x}
    = GITSET g {x} #e           by GPROD_SET_def
    = x * #e                    by ITSET_SING
    = x                         by monoid_rid
*)
val GPROD_SET_SING = store_thm(
  "GPROD_SET_SING",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> (GPROD_SET g {x} = x)``,
  rw[GPROD_SET_def, ITSET_SING]);

(*
> ITSET_SING |> SPEC_ALL |> INST_TYPE[beta |-> alpha] |> Q.INST[`f` |-> `g.op`] |> GEN_ALL;
val it = |- !x g b. GITSET g {x} b = x * b: thm
> ITSET_SING |> SPEC_ALL |> INST_TYPE[beta |-> alpha] |> Q.INST[`f` |-> `g.op`] |> Q.INST[`b` |-> `#e`] |> REWRITE_RULE[GSYM GPROD_SET_def];
val it = |- GPROD_SET g {x} = x * #e: thm
*)

(* Theorem: GPROD_SET g s IN G *)
(* Proof:
   By complete induction on CARD s.
   Case s = {},
       Then GPROD_SET g {} = #e         by GPROD_SET_EMPTY
       and #e IN G                      by monoid_id_element
   Case s <> {},
       Let x = CHOICE s, t = REST s, s = x INSERT t, x NOTIN t.
         GPROD_SET g s
       = GPROD_SET g (x INSERT t)       by s = x INSERT t
       = x * GPROD_SET g (t DELETE x)   by GPROD_SET_THM
       = x * GPROD_SET g t              by DELETE_NON_ELEMENT, x NOTIN t
       Hence GPROD_SET g s IN G         by induction, and monoid_op_element.
*)
val GPROD_SET_PROPERTY = store_thm(
  "GPROD_SET_PROPERTY",
  ``!(g:'a monoid) s. AbelianMonoid g /\ FINITE s /\ s SUBSET G ==> GPROD_SET g s IN G``,
  completeInduct_on `CARD s` >>
  pop_assum (assume_tac o SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rpt strip_tac >>
  `Monoid g` by metis_tac[AbelianMonoid_def] >>
  Cases_on `s = {}` >-
  rw[GPROD_SET_EMPTY] >>
  `?x t. (x = CHOICE s) /\ (t = REST s) /\ (s = x INSERT t)` by rw[CHOICE_INSERT_REST] >>
  `x IN G` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
  `t SUBSET G /\ FINITE t` by metis_tac[REST_SUBSET, SUBSET_TRANS, SUBSET_FINITE] >>
  `x NOTIN t` by metis_tac[CHOICE_NOT_IN_REST] >>
  `CARD t < CARD s` by rw[] >>
  metis_tac[GPROD_SET_THM, DELETE_NON_ELEMENT, monoid_op_element]);

(* ----------------------------------------------------------------------
    monoid extension

    lifting a monoid so that its carrier is the whole of the type but the
    op is the same on the old carrier set.
   ---------------------------------------------------------------------- *)

Definition extend_def:
  extend m = <| carrier := UNIV; id := m.id;
                op := λx y. if x ∈ m.carrier then
                              if y ∈ m.carrier then m.op x y else y
                            else x |>
End

Theorem extend_is_monoid[simp]:
  ∀m. Monoid m ⇒ Monoid (extend m)
Proof
  simp[extend_def, EQ_IMP_THM, Monoid_def] >> rw[] >> rw[] >>
  gvs[]
QED

Theorem extend_carrier[simp]:
  (extend m).carrier = UNIV
Proof
  simp[extend_def]
QED

Theorem extend_id[simp]:
  (extend m).id = m.id
Proof
  simp[extend_def]
QED

Theorem extend_op:
  x ∈ m.carrier ∧ y ∈ m.carrier ⇒ (extend m).op x y = m.op x y
Proof
  simp[extend_def]
QED



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
