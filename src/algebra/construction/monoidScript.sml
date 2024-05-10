(* ------------------------------------------------------------------------- *)
(* Monoid Theory                                                             *)
(* ========================================================================= *)
(* A monoid is a semi-group with an identity.                                *)
(* The units of a monoid form a group.                                       *)
(* A finite, cancellative monoid is also a group.                            *)
(* ------------------------------------------------------------------------- *)
(* Monoid                                                                    *)
(* Monoid Order and Invertibles                                              *)
(* Monoid Maps                                                               *)
(* Submonoid                                                                 *)
(* Applying Monoid Theory: Monoid Instances                                  *)
(* Theory about folding a monoid (or group) operation over a bag of elements *)
(* ------------------------------------------------------------------------- *)
(* (Joseph) Hing-Lun Chan, The Australian National University, 2014-2019     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoid";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory logrootTheory
     listTheory rich_listTheory bagTheory gcdsetTheory dep_rewrite;

open numberTheory combinatoricsTheory primeTheory;

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
                op := λx y. if x IN m.carrier then
                              if y IN m.carrier then m.op x y else y
                            else x |>
End

Theorem extend_is_monoid[simp]:
  !m. Monoid m ==> Monoid (extend m)
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
  x IN m.carrier /\ y IN m.carrier ==> (extend m).op x y = m.op x y
Proof
  simp[extend_def]
QED

(*

Monoid Order
============
This is an investigation of the equation x ** n = #e.
Given x IN G, x ** 0 = #e   by monoid_exp_0
But for those having non-trivial n with x ** n = #e,
the least value of n is called the order for the element x.
This is an important property for the element x,
especiallly later for Finite Group.

Monoid Invertibles
==================
In a monoid M, not all elements are invertible.
But for those elements that are invertible,
they have interesting properties.
Indeed, being invertible, an operation .inv or |/
can be defined through Skolemization, and later,
the Monoid Invertibles will be shown to be a Group.

*)

(* ------------------------------------------------------------------------- *)
(* Monoid Order and Invertibles Documentation                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   ord x             = order g x
   maximal_order g   = MAX_SET (IMAGE ord G)
   G*                = monoid_invertibles g
   reciprocal x      = monoid_inv g x
   |/                = reciprocal
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   period_def      |- !g x k. period g x k <=> 0 < k /\ (x ** k = #e)
   order_def       |- !g x. ord x = case OLEAST k. period g x k of NONE => 0 | SOME k => k
   order_alt       |- !g x. ord x = case OLEAST k. 0 < k /\ x ** k = #e of NONE => 0 | SOME k => k
   order_property  |- !g x. x ** ord x = #e
   order_period    |- !g x. 0 < ord x ==> period g x (ord x)
   order_minimal   |- !g x n. 0 < n /\ n < ord x ==> x ** n <> #e
   order_eq_0      |- !g x. (ord x = 0) <=> !n. 0 < n ==> x ** n <> #e
   order_thm       |- !g x n. 0 < n ==>
                      ((ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e)

#  monoid_order_id         |- !g. Monoid g ==> (ord #e = 1)
   monoid_order_eq_1       |- !g. Monoid g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e))
   monoid_order_condition  |- !g. Monoid g ==> !x. x IN G ==> !m. (x ** m = #e) <=> ord x divides m
   monoid_order_divides_exp|- !g. Monoid g ==> !x n. x IN G ==> ((x ** n = #e) <=> ord x divides n)
   monoid_order_power_eq_0 |- !g. Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0)
   monoid_order_power      |- !g. Monoid g ==> !x. x IN G ==> !k. ord (x ** k) * gcd (ord x) k = ord x
   monoid_order_power_eqn  |- !g. Monoid g ==> !x k. x IN G /\ 0 < k ==> (ord (x ** k) = ord x DIV gcd k (ord x))
   monoid_order_power_coprime   |- !g. Monoid g ==> !x. x IN G ==>
                                   !n. coprime n (ord x) ==> (ord (x ** n) = ord x)
   monoid_order_cofactor   |- !g. Monoid g ==> !x n. x IN G /\ 0 < ord x /\ n divides (ord x) ==>
                                                     (ord (x ** (ord x DIV n)) = n)
   monoid_order_divisor    |- !g. Monoid g ==> !x m. x IN G /\ 0 < ord x /\ m divides (ord x) ==>
                                               ?y. y IN G /\ (ord y = m)
   monoid_order_common     |- !g. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                                       ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   monoid_order_common_coprime  |- !g. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) /\
                                       coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)
   monoid_exp_mod_order         |- !g. Monoid g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)
   abelian_monoid_order_common  |- !g. AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
                                       ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   abelian_monoid_order_common_coprime
                                |- !g. AbelianMonoid g ==> !x y. x IN G /\ y IN G /\
                                       coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)
   abelian_monoid_order_lcm     |- !g. AbelianMonoid g ==>
                                   !x y. x IN G /\ y IN G ==> ?z. z IN G /\ (ord z = lcm (ord x) (ord y))

   Orders of elements:
   orders_def      |- !g n. orders g n = {x | x IN G /\ (ord x = n)}
   orders_element  |- !g x n. x IN orders g n <=> x IN G /\ (ord x = n)
   orders_subset   |- !g n. orders g n SUBSET G
   orders_finite   |- !g. FINITE G ==> !n. FINITE (orders g n)
   orders_eq_1     |- !g. Monoid g ==> (orders g 1 = {#e})

   Maximal Order:
   maximal_order_alt            |- !g. maximal_order g = MAX_SET {ord z | z | z IN G}
   monoid_order_divides_maximal |- !g. FiniteAbelianMonoid g ==>
                                   !x. x IN G /\ 0 < ord x ==> ord x divides maximal_order g

   Monoid Invertibles:
   monoid_invertibles_def       |- !g. G* = {x | x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)}
   monoid_invertibles_element   |- !g x. x IN G* <=> x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)
   monoid_order_nonzero         |- !g x. Monoid g /\ x IN G /\ 0 < ord x ==> x IN G*

   Invertibles_def              |- !g. Invertibles g = <|carrier := G*; op := $*; id := #e|>
   Invertibles_property         |- !g. ((Invertibles g).carrier = G* ) /\
                                       ((Invertibles g).op = $* ) /\
                                       ((Invertibles g).id = #e) /\
                                       ((Invertibles g).exp = $** )
   Invertibles_carrier          |- !g. (Invertibles g).carrier = G*
   Invertibles_subset           |- !g. (Invertibles g).carrier SUBSET G
   Invertibles_order            |- !g x. order (Invertibles g) x = ord x

   Monoid Inverse as an operation:
   monoid_inv_def               |- !g x. Monoid g /\ x IN G* ==> |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)
   monoid_inv_def_alt           |- !g. Monoid g ==> !x. x IN G* <=>
                                                        x IN G /\ |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)
   monoid_inv_element           |- !g. Monoid g ==> !x. x IN G* ==> x IN G
#  monoid_id_invertible         |- !g. Monoid g ==> #e IN G*
#  monoid_inv_op_invertible     |- !g. Monoid g ==> !x y. x IN G* /\ y IN G* ==> x * y IN G*
#  monoid_inv_invertible        |- !g. Monoid g ==> !x. x IN G* ==> |/ x IN G*
   monoid_invertibles_is_monoid |- !g. Monoid g ==> Monoid (Invertibles g)

*)

(* ------------------------------------------------------------------------- *)
(* Monoid Order Definition.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define order = optional LEAST period for an element x in Group g *)
val period_def = zDefine`
  period (g:'a monoid) (x:'a) k <=> 0 < k /\ (x ** k = #e)
`;
val order_def = zDefine`
  order (g:'a monoid) (x:'a) = case OLEAST k. period g x k of
                                 NONE => 0
                               | SOME k => k
`;
(* use zDefine here since these are not computationally effective. *)

(* Expand order_def with period_def. *)
val order_alt = save_thm(
  "order_alt", REWRITE_RULE [period_def] order_def);
(* val order_alt =
   |- !g x. order g x =
            case OLEAST k. 0 < k /\ x ** k = #e of NONE => 0 | SOME k => k: thm *)

(* overloading on Monoid Order *)
val _ = overload_on ("ord", ``order g``);

(* Theorem: (x ** (ord x) = #e *)
(* Proof: by definition, and x ** 0 = #e by monoid_exp_0. *)
val order_property = store_thm(
  "order_property",
  ``!g:'a monoid. !x:'a. (x ** (ord x) = #e)``,
  ntac 2 strip_tac >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[]);

(* Theorem: 0 < (ord x) ==> period g x (ord x) *)
(* Proof: by order_property, period_def. *)
val order_period = store_thm(
  "order_period",
  ``!g:'a monoid x:'a. 0 < (ord x) ==> period g x (ord x)``,
  rw[order_property, period_def]);

(* Theorem: !n. 0 < n /\ n < (ord x) ==> x ** n <> #e *)
(* Proof: by definition of OLEAST. *)
Theorem order_minimal:
  !g:'a monoid x:'a. !n. 0 < n /\ n < ord x ==> x ** n <> #e
Proof
  ntac 3 strip_tac >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  metis_tac[DECIDE “~(0 < 0)”]
QED

(* Theorem: (ord x = 0) <=> !n. 0 < n ==> x ** n <> #e *)
(* Proof:
   Expand by order_def, period_def, this is to show:
   (1) 0 < n /\ (!n. ~(0 < n) \/ x ** n <> #e) ==> x ** n <> #e
       True by assertion.
   (2) 0 < n /\ x ** n = #e /\ (!m. m < 0 ==> ~(0 < m) \/ x ** m <> #e) ==> (n = 0) <=> !n. 0 < n ==> x ** n <> #e
       True by assertion.
*)
Theorem order_eq_0:
  !g:'a monoid x. ord x = 0 <=> !n. 0 < n ==> x ** n <> #e
Proof
  ntac 2 strip_tac >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  metis_tac[DECIDE “~(0 < 0)”]
QED

val std_ss = std_ss -* ["NOT_LT_ZERO_EQ_ZERO"]

(* Theorem: 0 < n ==> ((ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e) *)
(* Proof:
   If part: (ord x = n) ==> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e
      This is to show:
      (1) (ord x = n) ==> (x ** n = #e), true by order_property
      (2) (ord x = n) ==> !m. 0 < m /\ m < n ==> x ** m <> #e, true by order_minimal
   Only-if part: (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e ==> (ord x = n)
      Expanding by order_def, period_def, this is to show:
      (1) 0 < n /\ x ** n = #e /\ !n'. ~(0 < n') \/ x ** n' <> #e ==> 0 = n
          Putting n' = n, the assumption is contradictory.
      (2) 0 < n /\ 0 < n' /\ x ** n = #e /\ x ** n' = #e /\ ... ==> n' = n
          The assumptions implies ~(n' < n), and ~(n < n'), hence n' = n.
*)
val order_thm = store_thm(
  "order_thm",
  ``!g:'a monoid x:'a. !n. 0 < n ==>
    ((ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e)``,
  rw[EQ_IMP_THM] >-
  rw[order_property] >-
  rw[order_minimal] >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >-
  metis_tac[] >>
  `~(n' < n)` by metis_tac[] >>
  `~(n < n')` by metis_tac[] >>
  decide_tac);

(* Theorem: Monoid g ==> (ord #e = 1) *)
(* Proof:
   Since #e IN G        by monoid_id_element
   and   #e ** 1 = #e   by monoid_exp_1
   Obviously, 0 < 1 and there is no m such that 0 < m < 1
   hence true by order_thm
*)
val monoid_order_id = store_thm(
  "monoid_order_id",
  ``!g:'a monoid. Monoid g ==> (ord #e = 1)``,
  rw[order_thm, DECIDE``!m . ~(0 < m /\ m < 1)``]);

(* export simple result *)
val _ = export_rewrites ["monoid_order_id"];

(* Theorem: Monoid g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e)) *)
(* Proof:
   If part: ord x = 1 ==> x = #e
      Since x ** (ord x) = #e      by order_property
        ==> x ** 1 = #e            by given
        ==> x = #e                 by monoid_exp_1
   Only-if part: x = #e ==> ord x = 1
      i.e. to show ord #e = 1.
      True by monoid_order_id.
*)
val monoid_order_eq_1 = store_thm(
  "monoid_order_eq_1",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e))``,
  rw[EQ_IMP_THM] >>
  `#e = x ** (ord x)` by rw[order_property] >>
  rw[]);

(* Theorem: Monoid g ==> !x. x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m *)
(* Proof:
   (ord x) is a period, and so divides all periods.
   Let n = ord x.
   If part: x^m = #e ==> n divides m
      If n = 0, m = 0   by order_eq_0
         Hence true     by ZERO_DIVIDES
      If n <> 0,
      By division algorithm, m = q * n + t   for some q, t and t < n.
      #e = x^m
         = x^(q * n + t)
         = (x^n)^q * x^t
         = #e * x^t
     Thus x^t = #e, but t < n.
     If 0 < t, this contradicts order_minimal.
     Hence t = 0, or n divides m.
   Only-if part: n divides m ==> x^m = #e
     By divides_def, ?k. m = k * n
     x^m = x^(k * n) = (x^n)^k = #e^k = #e.
*)
val monoid_order_condition = store_thm(
  "monoid_order_condition",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  rw[EQ_IMP_THM] >| [
    Cases_on `n = 0` >| [
      `~(0 < m)` by metis_tac[order_eq_0] >>
      `m = 0` by decide_tac >>
      rw[ZERO_DIVIDES],
      `x ** n = #e` by rw[order_property, Abbr`n`] >>
      `0 < n` by decide_tac >>
      `?q t. (m = q * n + t) /\ t < n` by metis_tac[DIVISION] >>
      `x ** m = x ** (n * q + t)` by metis_tac[MULT_COMM] >>
      `_ = (x ** (n * q)) * (x ** t)` by rw[] >>
      `_ = ((x ** n) ** q) * (x ** t)` by rw[] >>
      `_ = x ** t` by rw[] >>
      `~(0 < t)` by metis_tac[order_minimal] >>
      `t = 0` by decide_tac >>
      `m = q * n` by rw[] >>
      metis_tac[divides_def]
    ],
    `x ** n = #e` by rw[order_property, Abbr`n`] >>
    `?k. m = k * n` by rw[GSYM divides_def] >>
    `x ** m = x ** (n * k)` by metis_tac[MULT_COMM] >>
    `_ = (x ** n) ** k` by rw[] >>
    rw[]
  ]);

(* Theorem: Monoid g ==> !x n. x IN G ==> (x ** n = #e <=> ord x divides n) *)
(* Proof: by monoid_order_condition *)
val monoid_order_divides_exp = store_thm(
  "monoid_order_divides_exp",
  ``!g:'a monoid. Monoid g ==> !x n. x IN G ==> ((x ** n = #e) <=> ord x divides n)``,
  rw[monoid_order_condition]);

(* Theorem: Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0) *)
(* Proof:
   By order_eq_0, this is to show:
   (1) !n. 0 < n ==> (x ** k) ** n <> #e ==> 0 < k
       By contradiction. Assume k = 0.
       Then x ** k = #e         by monoid_exp_0
        and #e ** n = #e        by monoid_id_exp
       This contradicts the implication: (x ** k) ** n <> #e.
   (2) 0 < n /\ !n. 0 < n ==> (x ** k) ** n <> #e ==> x ** n <> #e
       By contradiction. Assume x ** n = #e.
       Now, (x ** k) ** n
           = x ** (k * n)        by monoid_exp_mult
           = x ** (n * k)        by MULT_COMM
           = (x ** n) * k        by monoid_exp_mult
           = #e ** k             by x ** n = #e
           = #e                  by monoid_id_exp
       This contradicts the implication: (x ** k) ** n <> #e.
   (3) 0 < n /\ !n. 0 < n ==> x ** n <> #e ==> (x ** k) ** n <> #e
       By contradiction. Assume (x ** k) ** n = #e.
       0 < k /\ 0 < n ==> 0 < k * n       by arithmetic
       But (x ** n) ** k = x ** (n * k)   by monoid_exp_mult
       This contradicts the implication: (x ** k) ** n <> #e.
*)
val monoid_order_power_eq_0 = store_thm(
  "monoid_order_power_eq_0",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0)``,
  rw[order_eq_0, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `k = 0` by decide_tac >>
    `x ** k = #e` by rw[monoid_exp_0] >>
    metis_tac[monoid_id_exp, DECIDE``0 < 1``],
    metis_tac[monoid_exp_mult, MULT_COMM, monoid_id_exp],
    `0 < k * n` by rw[LESS_MULT2] >>
    metis_tac[monoid_exp_mult]
  ]);

(* Theorem: ord (x ** k) = ord x / gcd(ord x, k)
            Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) * (gcd (ord x) k) = ord x) *)
(* Proof:
   Let n = ord x, m = ord (x^k), d = gcd(n,k).
   This is to show: m = n / d.
   If k = 0,
      m = ord (x^0) = ord #e = 1   by monoid_order_id
      d = gcd(n,0) = n             by GCD_0R
      henc true.
   If k <> 0,
   First, show ord (x^k) = m divides n/d.
     If n = 0, m = 0               by monoid_order_power_eq_0
     so ord (x^k) = m | (n/d)      by ZERO_DIVIDES
     If n <> 0,
     (x^k)^(n/d) = x^(k * n/d) = x^(n * k/d) = (x^n)^(k/d) = #e,
     so ord (x^k) = m | (n/d)      by monoid_order_condition.
   Second, show (n/d) divides m = ord (x^k), or equivalently: n divides d * m
     x^(k * m) = (x^k)^m = #e = x^n,
     so ord x = n | k * m          by monoid_order_condition
     Since d = gcd(k,n), there are integers a and b such that
       ka + nb = d                 by LINEAR_GCD
     Multiply by m: k * m * a + n * m * b = d * m.
     But since n | k * m, it follows that n | d*m,
     i.e. (n/d) | m                by DIVIDES_CANCEL.
   By DIVIDES_ANTISYM, ord (x^k) = m = n/d.
*)
val monoid_order_power = store_thm(
  "monoid_order_power",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) * (gcd (ord x) k) = ord x)``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `m = ord (x ** k)` >>
  qabbrev_tac `d = gcd n k` >>
  Cases_on `k = 0` >| [
    `d = n` by metis_tac[GCD_0R] >>
    rw[Abbr`m`],
    Cases_on `n = 0` >| [
      `0 < k` by decide_tac >>
      `m = 0` by rw[monoid_order_power_eq_0, Abbr`n`, Abbr`m`] >>
      rw[],
      `x ** n = #e` by rw[order_property, Abbr`n`] >>
      `0 < n /\ 0 < k` by decide_tac >>
      `?p q. (n = p * d) /\ (k = q * d)` by metis_tac[FACTOR_OUT_GCD] >>
      `k * p = n * q` by rw_tac arith_ss[] >>
      `(x ** k) ** p = x ** (k * p)` by rw[] >>
      `_ = x ** (n * q)` by metis_tac[] >>
      `_ = (x ** n) ** q` by rw[] >>
      `_ = #e` by rw[] >>
      `m divides p` by rw[GSYM monoid_order_condition, Abbr`m`] >>
      `x ** (m * k) = x ** (k * m)` by metis_tac[MULT_COMM] >>
      `_ = (x ** k) ** m` by rw[] >>
      `_ = #e` by rw[order_property, Abbr`m`] >>
      `n divides (m * k)` by rw[GSYM monoid_order_condition, Abbr`n`, Abbr`m`] >>
      `?u v. u * k = v * n + d` by rw[LINEAR_GCD, Abbr`d`] >>
      `m * k * u = m * (u * k)` by rw_tac arith_ss[] >>
      `_ = m * (v * n) + m * d` by metis_tac[LEFT_ADD_DISTRIB] >>
      `_ = m * v * n + m * d` by rw_tac arith_ss[] >>
      `n divides (m * k * u)` by metis_tac[DIVIDES_MULT] >>
      `n divides (m * v * n)` by metis_tac[divides_def] >>
      `n divides (m * d)` by metis_tac[DIVIDES_ADD_2] >>
      `d <> 0` by metis_tac[MULT_EQ_0] >>
      `0 < d` by decide_tac >>
      `p divides m` by metis_tac[DIVIDES_CANCEL] >>
      metis_tac[DIVIDES_ANTISYM]
    ]
  ]);

(* Theorem: Monoid g ==>
   !x k. x IN G /\ 0 < k ==> (ord (x ** k) = (ord x) DIV (gcd k (ord x))) *)
(* Proof:
   Note ord (x ** k) * gcd k (ord x) = ord x         by monoid_order_power, GCD_SYM
    and 0 < gcd k (ord x)                            by GCD_EQ_0, 0 < k
    ==> ord (x ** k) = (ord x) DIV (gcd k (ord x))   by MULT_EQ_DIV
*)
val monoid_order_power_eqn = store_thm(
  "monoid_order_power_eqn",
  ``!g:'a monoid. Monoid g ==>
   !x k. x IN G /\ 0 < k ==> (ord (x ** k) = (ord x) DIV (gcd k (ord x)))``,
  rpt strip_tac >>
  `ord (x ** k) * gcd k (ord x) = ord x` by metis_tac[monoid_order_power, GCD_SYM] >>
  `0 < gcd k (ord x)` by metis_tac[GCD_EQ_0, NOT_ZERO] >>
  fs[MULT_EQ_DIV]);

(* Theorem: Monoid g ==> !x. x IN G ==> !n. coprime n (ord x) ==> (ord (x ** n) = ord x) *)
(* Proof:
     ord x
   = ord (x ** n) * gcd (ord x) n   by monoid_order_power
   = ord (x ** n) * 1               by coprime_sym
   = ord (x ** n)                   by MULT_RIGHT_1
*)
val monoid_order_power_coprime = store_thm(
  "monoid_order_power_coprime",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !n. coprime n (ord x) ==> (ord (x ** n) = ord x)``,
  metis_tac[monoid_order_power, coprime_sym, MULT_RIGHT_1]);

(* Theorem: Monoid g ==>
            !x n. x IN G /\ 0 < ord x /\ n divides ord x ==> (ord (x ** (ord x DIV n)) = n) *)
(* Proof:
   Let m = ord x, k = m DIV n.
   Since 0 < m, n <> 0, or 0 < n         by ZERO_DIVIDES
   Since n divides m, m = k * n          by DIVIDES_EQN
   Hence k divides m                     by divisors_def, MULT_COMM
     and k <> 0                          by MULT, m <> 0
     and gcd k m = k                     by divides_iff_gcd_fix
     Now ord (x ** k) * k
       = m                               by monoid_order_power
       = k * n                           by above
       = n * k                           by MULT_COMM
   Hence ord (x ** k) = n                by MULT_RIGHT_CANCEL, k <> 0
*)
val monoid_order_cofactor = store_thm(
  "monoid_order_cofactor",
  ``!g: 'a monoid. Monoid g ==>
     !x n. x IN G /\ 0 < ord x /\ n divides ord x ==> (ord (x ** (ord x DIV n)) = n)``,
  rpt strip_tac >>
  qabbrev_tac `m = ord x` >>
  qabbrev_tac `k = m DIV n` >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `k divides m` by metis_tac[divides_def, MULT_COMM] >>
  `k <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  `gcd k m = k` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[monoid_order_power, GCD_SYM, MULT_COMM, MULT_RIGHT_CANCEL]);

(* Theorem: If x IN G with ord x = n > 0, and m divides n, then G contains an element of order m. *)
(* Proof:
   m divides n ==> n = k * m  for some k, by divides_def.
   Then x^k has order m:
   (x^k)^m = x^(k * m) = x^n = #e
   and for any h < m,
   if (x^k)^h = x^(k * h) = #e means x has order k * h < k * m = n,
   which is a contradiction with order_minimal.
*)
val monoid_order_divisor = store_thm(
  "monoid_order_divisor",
  ``!g:'a monoid. Monoid g ==>
   !x m. x IN G /\ 0 < ord x /\ m divides (ord x) ==> ?y. y IN G /\ (ord y = m)``,
  rpt strip_tac >>
  `ord x <> 0` by decide_tac >>
  `m <> 0` by metis_tac[ZERO_DIVIDES] >>
  `0 < m` by decide_tac >>
  `?k. ord x = k * m` by rw[GSYM divides_def] >>
  qexists_tac `x ** k` >>
  rw[] >>
  `x ** (ord x) = #e` by rw[order_property] >>
  `(x ** k) ** m = #e` by metis_tac[monoid_exp_mult] >>
  `(!h. 0 < h /\ h < m ==> (x ** k) ** h <> #e)` suffices_by metis_tac[order_thm] >>
  rpt strip_tac >>
  `h <> 0` by decide_tac >>
  `k <> 0 /\ k * h <> 0` by metis_tac[MULT, MULT_EQ_0] >>
  `0 < k /\ 0 < k * h` by decide_tac >>
  `k * h < k * m` by metis_tac[LT_MULT_LCANCEL] >>
  `(x ** k) ** h = x ** (k * h)` by rw[] >>
  metis_tac[order_minimal]);

(* Theorem: If x * y = y * x, and n = ord x, m = ord y,
            then there exists z IN G such that ord z = (lcm n m) / (gcd n m) *)
(* Proof:
   Let n = ord x, m = ord y, d = gcd(n, m).
   This is to show: ?z. z IN G /\ (ord z * d = n * m)
   If n = 0, take z = x, by LCM_0.
   If m = 0, take z = y, by LCM_0.
   If n <> 0 and m <> 0,
   First, get a pair with coprime orders.
   ?p q. (n = p * d) /\ (m = q * d) /\ coprime p q   by FACTOR_OUT_GCD
   Let u = x^d, v = y^d
   then ord u = ord (x^d) = ord x / gcd(n, d) = n/d = p   by monoid_order_power
    and ord v = ord (y^d) = ord y / gcd(m, d) = m/d = q   by monoid_order_power
   Now gcd(p,q) = 1, and there exists integers a and b such that
     a * p + b * q = 1             by LINEAR_GCD
   Let w = u^b * v^a
   Then w^p = (u^b * v^a)^p
            = (u^b)^p * (v^a)^p    by monoid_comm_op_exp
            = (u^p)^b * (v^a)^p    by monoid_exp_mult_comm
            = #e^b * v^(a * p)     by p = ord u
            = v^(a * p)            by monoid_id_exp
            = v^(1 - b * q)        by LINEAR_GCD condition
            = v^1 * |/ v^(b * q)   by variant of monoid_exp_add
            = v * 1/ (v^q)^b       by monoid_exp_mult_comm
            = v * 1/ #e^b          by q = ord v
            = v
   Hence ord (w^p) = ord v = q,
   Let c = ord w, c <> 0 since p * q <> 0   by GCD_0L
   then q = ord (w^p) = c / gcd(c,p)        by monoid_order_power
   i.e. q * gcd(c,p) = c, or q divides c
   Similarly, w^q = u, and p * gcd(c,q) = c, or p divides c.
   Since coprime p q, p * q divides c, an order of element w IN G.
   Hence there is some z in G such that ord z = p * q  by monoid_order_divisor.
   i.e.  ord z = lcm p q = lcm (n/d) (m/d) = (lcm n m) / d.
*)
val monoid_order_common = store_thm(
  "monoid_order_common",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
     ?z. z IN G /\ ((ord z) * gcd (ord x) (ord y) = lcm (ord x) (ord y))``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `m = ord y` >>
  qabbrev_tac `d = gcd n m` >>
  Cases_on `n = 0` >-
  metis_tac[LCM_0, MULT_EQ_0] >>
  Cases_on `m = 0` >-
  metis_tac[LCM_0, MULT_EQ_0] >>
  `x ** n = #e` by rw[order_property, Abbr`n`] >>
  `y ** m = #e` by rw[order_property, Abbr`m`] >>
  `d <> 0` by rw[GCD_EQ_0, Abbr`d`] >>
  `?p q. (n = p * d) /\ (m = q * d) /\ coprime p q` by rw[FACTOR_OUT_GCD, Abbr`d`] >>
  qabbrev_tac `u = x ** d` >>
  qabbrev_tac `v = y ** d` >>
  `u IN G /\ v IN G` by rw[Abbr`u`, Abbr`v`] >>
  `(gcd n d = d) /\ (gcd m d = d)` by rw[GCD_GCD, GCD_SYM, Abbr`d`] >>
  `ord u = p` by metis_tac[monoid_order_power, MULT_RIGHT_CANCEL] >>
  `ord v = q` by metis_tac[monoid_order_power, MULT_RIGHT_CANCEL] >>
  `p <> 0 /\ q <> 0` by metis_tac[MULT_EQ_0] >>
  `?a b. a * q = b * p + 1` by metis_tac[LINEAR_GCD] >>
  `?h k. h * p = k * q + 1` by metis_tac[LINEAR_GCD, GCD_SYM] >>
  qabbrev_tac `ua = u ** a` >>
  qabbrev_tac `vh = v ** h` >>
  qabbrev_tac `w = ua * vh` >>
  `ua IN G /\ vh IN G /\ w IN G` by rw[Abbr`ua`, Abbr`vh`, Abbr`w`] >>
  `ua * vh = (x ** d) ** a * (y ** d) ** h` by rw[] >>
  `_ = x ** (d * a) * y ** (d * h)` by rw_tac std_ss[GSYM monoid_exp_mult] >>
  `_ = y ** (d * h) * x ** (d * a)` by metis_tac[monoid_comm_exp_exp] >>
  `_ = vh * ua` by rw[] >>
  `w ** p = (ua * vh) ** p` by rw[] >>
  `_ = ua ** p * vh ** p` by metis_tac[monoid_comm_op_exp] >>
  `_ = (u ** p) ** a * (v ** h) ** p` by rw[monoid_exp_mult_comm] >>
  `_ = #e ** a * v ** (h * p)` by rw[order_property] >>
  `_ = v ** (h * p)` by rw[] >>
  `_ = v ** (k * q + 1)` by rw_tac std_ss[] >>
  `_ = v ** (k * q) * v` by rw[] >>
  `_ = v ** (q * k) * v` by rw_tac std_ss[MULT_COMM] >>
  `_ = (v ** q) ** k * v` by rw[] >>
  `_ = #e ** k * v` by rw[order_property] >>
  `_ = v` by rw[] >>
  `w ** q = (ua * vh) ** q` by rw[] >>
  `_ = ua ** q * vh ** q` by metis_tac[monoid_comm_op_exp] >>
  `_ = (u ** a) ** q * (v ** q) ** h` by rw[monoid_exp_mult_comm] >>
  `_ = u ** (a * q) * #e ** h` by rw[order_property] >>
  `_ = u ** (a * q)` by rw[] >>
  `_ = u ** (b * p + 1)` by rw_tac std_ss[] >>
  `_ = u ** (b * p) * u` by rw[] >>
  `_ = u ** (p * b) * u` by rw_tac std_ss[MULT_COMM] >>
  `_ = (u ** p) ** b * u` by rw[] >>
  `_ = #e ** b * u` by rw[order_property] >>
  `_ = u` by rw[] >>
  qabbrev_tac `c = ord w` >>
  `q * gcd c p = c` by rw[monoid_order_power, Abbr`c`] >>
  `p * gcd c q = c` by metis_tac[monoid_order_power] >>
  `p divides c /\ q divides c` by metis_tac[divides_def, MULT_COMM] >>
  `lcm p q = p * q` by rw[LCM_COPRIME] >>
  `(p * q) divides c` by metis_tac[LCM_IS_LEAST_COMMON_MULTIPLE] >>
  `p * q <> 0` by rw[MULT_EQ_0] >>
  `c <> 0` by metis_tac[GCD_0L] >>
  `0 < c` by decide_tac >>
  `?z. z IN G /\ (ord z = p * q)` by metis_tac[monoid_order_divisor] >>
  `ord z * d = d * (p * q)` by rw_tac arith_ss[] >>
  `_ = lcm (d * p) (d * q)` by rw[LCM_COMMON_FACTOR] >>
  `_ = lcm n m` by metis_tac[MULT_COMM] >>
  metis_tac[]);

(* This is a milestone. *)

(* Theorem: If x * y = y * x, and n = ord x, m = ord y, and gcd n m = 1,
            then there exists z IN G with ord z = (lcm n m) *)
(* Proof:
   By monoid_order_common and gcd n m = 1.
*)
val monoid_order_common_coprime = store_thm(
  "monoid_order_common_coprime",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) /\ coprime (ord x) (ord y) ==>
     ?z. z IN G /\ (ord z = (ord x) * (ord y))``,
  metis_tac[monoid_order_common, GCD_LCM, MULT_RIGHT_1, MULT_LEFT_1]);
(* This version can be proved directly using previous technique, then derive the general case:
   Let ord x = n, ord y = m.
   Let d = gcd(n,m)  p = n/d, q = m/d, gcd(p,q) = 1.
   By p | n = ord x, there is u with ord u = p     by monoid_order_divisor
   By q | m = ord y, there is v with ord v = q     by monoid_order_divisor
   By gcd(ord u, ord v) = gcd(p,q) = 1,
   there is z with ord z = lcm(p,q) = p * q = n/d * m/d = lcm(n,m)/gcd(n,m).
*)

(* Theorem: Monoid g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x)) *)
(* Proof:
   Let z = ord x, 0 < z                         by given
   Note n = (n DIV z) * z + (n MOD z)           by DIVISION, 0 < z.
      x ** n
    = x ** ((n DIV z) * z + (n MOD z))          by above
    = x ** ((n DIV z) * z) * x ** (n MOD z)     by monoid_exp_add
    = x ** (z * (n DIV z)) * x ** (n MOD z)     by MULT_COMM
    = (x ** z) ** (n DIV z) * x ** (n MOD z)    by monoid_exp_mult
    = #e ** (n DIV 2) * x ** (n MOD z)          by order_property
    = #e * x ** (n MOD z)                       by monoid_id_exp
    = x ** (n MOD z)                            by monoid_lid
*)
val monoid_exp_mod_order = store_thm(
  "monoid_exp_mod_order",
  ``!g:'a monoid. Monoid g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x))``,
  rpt strip_tac >>
  qabbrev_tac `z = ord x` >>
  `x ** n = x ** ((n DIV z) * z + (n MOD z))` by metis_tac[DIVISION] >>
  `_ = x ** ((n DIV z) * z) * x ** (n MOD z)` by rw[monoid_exp_add] >>
  `_ = x ** (z * (n DIV z)) * x ** (n MOD z)` by metis_tac[MULT_COMM] >>
  rw[monoid_exp_mult, order_property, Abbr`z`]);

(* Theorem: AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
            ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y)) *)
(* Proof: by AbelianMonoid_def, monoid_order_common *)
val abelian_monoid_order_common = store_thm(
  "abelian_monoid_order_common",
  ``!g:'a monoid. AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
   ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))``,
  rw[AbelianMonoid_def, monoid_order_common]);

(* Theorem: AbelianMonoid g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
            ?z. z IN G /\ (ord z = ord x * ord y) *)
(* Proof: by AbelianMonoid_def, monoid_order_common_coprime *)
val abelian_monoid_order_common_coprime = store_thm(
  "abelian_monoid_order_common_coprime",
  ``!g:'a monoid. AbelianMonoid g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
   ?z. z IN G /\ (ord z = ord x * ord y)``,
  rw[AbelianMonoid_def, monoid_order_common_coprime]);

(* Theorem: AbelianMonoid g ==>
            !x y. x IN G /\ y IN G ==> ?z. z IN G /\ (ord z = lcm (ord x) (ord y)) *)
(* Proof:
   If ord x = 0,
      Then lcm 0 (ord y) = 0 = ord x     by LCM_0
      Thus take z = x.
   If ord y = 0
      lcm (ord x) 0 = 0 = ord y          by LCM_0
      Thus take z = y.
   Otherwise, 0 < ord x /\ 0 < ord y.
      Let m = ord x, n = ord y.
      Note ?a b p q. (lcm m n = p * q) /\ coprime p q /\
                     (m = a * p) /\ (n = b * q)   by lcm_gcd_park_decompose
      Thus p divides m /\ q divides n             by divides_def
       ==> ?u. u IN G /\ (ord u = p)              by monoid_order_divisor, p divides m
       and ?v. v IN G /\ (ord v = q)              by monoid_order_divisor, q divides n
       ==> ?z. z IN G /\ (ord z = p * q)          by monoid_order_common_coprime, coprime p q
        or     z IN G /\ (ord z = lcm m n)        by above
*)
val abelian_monoid_order_lcm = store_thm(
  "abelian_monoid_order_lcm",
  ``!g:'a monoid. AbelianMonoid g ==>
   !x y. x IN G /\ y IN G ==> ?z. z IN G /\ (ord z = lcm (ord x) (ord y))``,
  rw[AbelianMonoid_def] >>
  qabbrev_tac `m = ord x` >>
  qabbrev_tac `n = ord y` >>
  Cases_on `(m = 0) \/ (n = 0)` >-
  metis_tac[LCM_0] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `?a b p q. (lcm m n = p * q) /\ coprime p q /\ (m = a * p) /\ (n = b * q)` by metis_tac[lcm_gcd_park_decompose] >>
  `p divides m /\ q divides n` by metis_tac[divides_def] >>
  `?u. u IN G /\ (ord u = p)` by metis_tac[monoid_order_divisor] >>
  `?v. v IN G /\ (ord v = q)` by metis_tac[monoid_order_divisor] >>
  `?z. z IN G /\ (ord z = p * q)` by rw[monoid_order_common_coprime] >>
  metis_tac[]);

(* This is much better than:
abelian_monoid_order_common
|- !g. AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
       ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
*)

(* ------------------------------------------------------------------------- *)
(* Orders of elements                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define the set of elements with a given order *)
val orders_def = Define `
   orders (g:'a monoid) n = {x | x IN G /\ (ord x = n)}
`;

(* Theorem: !x n. x IN orders g n <=> x IN G /\ (ord x = n) *)
(* Proof: by orders_def *)
val orders_element = store_thm(
  "orders_element",
  ``!g:'a monoid. !x n. x IN orders g n <=> x IN G /\ (ord x = n)``,
  rw[orders_def]);

(* Theorem: !n. (orders g n) SUBSET G *)
(* Proof: by orders_def, SUBSET_DEF *)
val orders_subset = store_thm(
  "orders_subset",
  ``!g:'a monoid. !n. (orders g n) SUBSET G``,
  rw[orders_def, SUBSET_DEF]);

(* Theorem: FINITE G ==> !n. FINITE (orders g n) *)
(* Proof: by orders_subset, SUBSET_FINITE *)
val orders_finite = store_thm(
  "orders_finite",
  ``!g:'a monoid. FINITE G ==> !n. FINITE (orders g n)``,
  metis_tac[orders_subset, SUBSET_FINITE]);

(* Theorem: Monoid g ==> (orders g 1 = {#e}) *)
(* Proof:
     orders g 1
   = {x | x IN G /\ (ord x = 1)}    by orders_def
   = {x | x IN G /\ (x = #e)}       by monoid_order_eq_1
   = {#e}                           by monoid_id_elelment
*)
val orders_eq_1 = store_thm(
  "orders_eq_1",
  ``!g:'a monoid. Monoid g ==> (orders g 1 = {#e})``,
  rw[orders_def, EXTENSION, EQ_IMP_THM, GSYM monoid_order_eq_1]);

(* ------------------------------------------------------------------------- *)
(* Maximal Order                                                             *)
(* ------------------------------------------------------------------------- *)

(* Overload maximal_order of a group *)
val _ = overload_on("maximal_order", ``\g:'a monoid. MAX_SET (IMAGE ord G)``);

(* Theorem: maximal_order g = MAX_SET {ord z | z | z IN G} *)
(* Proof: by IN_IMAGE *)
val maximal_order_alt = store_thm(
  "maximal_order_alt",
  ``!g:'a monoid. maximal_order g = MAX_SET {ord z | z | z IN G}``,
  rpt strip_tac >>
  `IMAGE ord G = {ord z | z | z IN G}` by rw[EXTENSION] >>
  rw[]);

(* Theorem: In an Abelian Monoid, every nonzero order divides the maximal order.
            FiniteAbelianMonoid g ==> !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g) *)
(* Proof:
   Let m = maximal_order g = MAX_SET {ord x | x IN G}
   Choose z IN G so that ord z = m.
   Pick x IN G so that ord x = n. Question: will n divide m ?

   We have: ord x = n, ord z = m  bigger.
   Let d = gcd(n,m), a = n/d, b = m/d.
   Since a | n = ord x, there is ord xa = a
   Since b | m = ord y, there is ord xb = b
   and gcd(a,b) = 1     by FACTOR_OUT_GCD

   If gcd(a,m) <> 1, let prime p divides gcd(a,m)   by PRIME_FACTOR

   Since gcd(a,m) | a  and gcd(a,m) divides m,
   prime p | a, p | m = b * d, a product.
   When prime p divides (b * d), p | b or p | d     by P_EUCLIDES
   But gcd(a,b)=1, they don't share any common factor, so p | a ==> p not divide b.
   If p not divide b, so p | d.
   But d | n, d | m, so p | n and p | m.

   Let  p^i | n  for some max i,   mi = MAX_SET {i | p^i divides n}, p^mi | n ==> n = nq * p^mi
   and  p^j | m  for some max j,   mj = MAX_SET {j | p^j divides m), p^mj | m ==> m = mq * p^mj
   If i <= j,
      ppppp | n     ppppppp | m
   d should picks up all i of the p's, leaving a = n/d with no p, p cannot divide a.
   But p | a, so i > j, but this will derive a contradiction:
      pppppp | n    pppp   | m
   d picks up j of the p's
   Let u = p^i (all prime p in n), v = m/p^j (no prime p)
   u | n, so there is ord x = u = p^i                 u = p^mi
   v | m, so there is ord x = v = m/p^j               v = m/p^mj
   gcd(u,v)=1, since u is pure prime p, v has no prime p (possible gcd = 1, p, p^2, etc.)
   So there is ord z = u * v = p^i * m /p^j = m * p^(i-j) .... > m, a contradiction!

   This case is impossible for the max order suitation.

   So gcd(a,m) = 1, there is ord z = a * m = n * m /d
   But  n * m /d <= m,  since m is maximal
   i.e.        n <= d
   But d | n,  d <= n,
   Hence       n = d = gcd(m,n), apply divides_iff_gcd_fix: n divides m.
*)
val monoid_order_divides_maximal = store_thm(
  "monoid_order_divides_maximal",
  ``!g:'a monoid. FiniteAbelianMonoid g ==>
   !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g)``,
  rw[FiniteAbelianMonoid_def, AbelianMonoid_def] >>
  qabbrev_tac `s = IMAGE ord G` >>
  qabbrev_tac `m = MAX_SET s` >>
  qabbrev_tac `n = ord x` >>
  `#e IN G /\ (ord #e = 1)` by rw[] >>
  `s <> {}` by metis_tac[IN_IMAGE, MEMBER_NOT_EMPTY] >>
  `FINITE s` by metis_tac[IMAGE_FINITE] >>
  `m IN s /\ !y. y IN s ==> y <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `?z. z IN G /\ (ord z = m)` by metis_tac[IN_IMAGE] >>
  `!z. 0 < z <=> z <> 0` by decide_tac >>
  `1 <= m` by metis_tac[in_max_set, IN_IMAGE] >>
  `0 < m` by decide_tac >>
  `?a b. (n = a * gcd n m) /\ (m = b * gcd n m) /\ coprime a b` by metis_tac[FACTOR_OUT_GCD] >>
  qabbrev_tac `d = gcd n m` >>
  `a divides n /\ b divides m` by metis_tac[divides_def, MULT_COMM] >>
  `?xa. xa IN G /\ (ord xa = a)` by metis_tac[monoid_order_divisor] >>
  `?xb. xb IN G /\ (ord xb = b)` by metis_tac[monoid_order_divisor] >>
  Cases_on `coprime a m` >| [
    `?xc. xc IN G /\ (ord xc = a * m)` by metis_tac[monoid_order_common_coprime] >>
    `a * m <= m` by metis_tac[IN_IMAGE] >>
    `n * m = d * (a * m)` by rw_tac arith_ss[] >>
    `n <= d` by metis_tac[LE_MULT_LCANCEL, LE_MULT_RCANCEL] >>
    `d <= n` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0, DIVIDES_LE] >>
    `n = d` by decide_tac >>
    metis_tac [divides_iff_gcd_fix],
    qabbrev_tac `q = gcd a m` >>
    `?p. prime p /\ p divides q` by rw[PRIME_FACTOR] >>
    `0 < a` by metis_tac[MULT] >>
    `q divides a /\ q divides m` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0] >>
    `p divides a /\ p divides m` by metis_tac[DIVIDES_TRANS] >>
    `p divides b \/ p divides d` by metis_tac[P_EUCLIDES] >| [
      `p divides 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, MULT] >>
      metis_tac[DIVIDES_ONE, NOT_PRIME_1],
      `d divides n` by metis_tac[divides_def] >>
      `p divides n` by metis_tac[DIVIDES_TRANS] >>
      `?i. 0 < i /\ (p ** i) divides n /\ !k. coprime (p ** k) (n DIV p ** i)` by rw[FACTOR_OUT_PRIME] >>
      `?j. 0 < j /\ (p ** j) divides m /\ !k. coprime (p ** k) (m DIV p ** j)` by rw[FACTOR_OUT_PRIME] >>
      Cases_on `i > j` >| [
        qabbrev_tac `u = p ** i` >>
        qabbrev_tac `v = m DIV p ** j` >>
        `0 < p` by metis_tac[PRIME_POS] >>
        `v divides m` by metis_tac[DIVIDES_COFACTOR, EXP_EQ_0] >>
        `?xu. xu IN G /\ (ord xu = u)` by metis_tac[monoid_order_divisor] >>
        `?xv. xv IN G /\ (ord xv = v)` by metis_tac[monoid_order_divisor] >>
        `coprime u v` by rw[Abbr`u`] >>
        `?xz. xz IN G /\ (ord xz = u * v)` by rw[monoid_order_common_coprime] >>
        `m = (p ** j) * v` by metis_tac[DIVIDES_FACTORS, EXP_EQ_0] >>
        `p ** (i - j) * m = p ** (i - j) * (p ** j) * v` by rw_tac arith_ss[] >>
        `j <= i` by decide_tac >>
        `p ** (i - j) * (p ** j) = p ** (i - j + j)` by rw[EXP_ADD] >>
        `_ = p ** i` by rw[SUB_ADD] >>
        `p ** (i - j) * m = u * v` by rw_tac std_ss[Abbr`u`] >>
        `0 < i - j` by decide_tac >>
        `1 < p ** (i - j)` by rw[ONE_LT_EXP, ONE_LT_PRIME] >>
        `m < p ** (i - j) * m` by rw[LT_MULT_RCANCEL] >>
        `m < u * v` by metis_tac[] >>
        `u * v > m` by decide_tac >>
        `u * v <= m` by metis_tac[IN_IMAGE] >>
        metis_tac[NOT_GREATER],
        `i <= j` by decide_tac >>
        `0 < p` by metis_tac[PRIME_POS] >>
        `p ** i <> 0 /\ p ** j <> 0` by metis_tac[EXP_EQ_0] >>
        `n = (p ** i) * (n DIV p ** i)` by metis_tac[DIVIDES_FACTORS] >>
        `m = (p ** j) * (m DIV p ** j)` by metis_tac[DIVIDES_FACTORS] >>
        `p ** (j - i) * (p ** i) = p ** (j - i + i)` by rw[EXP_ADD] >>
        `_ = p ** j` by rw[SUB_ADD] >>
        `m = p ** (j - i) * (p ** i) * (m DIV p ** j)` by rw_tac std_ss[] >>
        `_ = (p ** i) * (p ** (j - i) * (m DIV p ** j))` by rw_tac arith_ss[] >>
        qabbrev_tac `u = p ** i` >>
        qabbrev_tac `v = n DIV u` >>
        `u divides m` by metis_tac[divides_def, MULT_COMM] >>
        `u divides d` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
        `?c. d = c * u` by metis_tac[divides_def] >>
        `n = (a * c) * u` by rw_tac arith_ss[] >>
        `v = c * a` by metis_tac[MULT_RIGHT_CANCEL, MULT_COMM] >>
        `a divides v` by metis_tac[divides_def] >>
        `p divides v` by metis_tac[DIVIDES_TRANS] >>
        `p divides u` by metis_tac[DIVIDES_EXP_BASE, DIVIDES_REFL] >>
        `d <> 0` by metis_tac[MULT_0] >>
        `c <> 0` by metis_tac[MULT] >>
        `v <> 0` by metis_tac[MULT_EQ_0] >>
        `p divides (gcd v u)` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
        `coprime u v` by metis_tac[] >>
        metis_tac[GCD_SYM, DIVIDES_ONE, NOT_PRIME_1]
      ]
    ]
  ]);

(* This is a milestone theorem. *)

(* Another proof based on the following:

The Multiplicative Group of a Finite Field (Ryan Vinroot)
http://www.math.wm.edu/~vinroot/430S13MultFiniteField.pdf

*)

(* Theorem: FiniteAbelianMonoid g ==>
            !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g) *)
(* Proof:
   Note AbelianMonoid g /\ FINITE G         by FiniteAbelianMonoid_def
   Let ord z = m = maximal_order g, attained by some z IN G.
   Let ord x = n, and n <= m since m is maximal_order, so 0 < m.
   Then x IN G /\ z IN G
    ==> ?y. y IN G /\ ord y = lcm n m       by abelian_monoid_order_lcm
   Note lcm n m <= m                        by m is maximal_order
    but       m <= lcm n m                  by LCM_LE, lcm is a common multiple
    ==> lcm n m = m                         by EQ_LESS_EQ
     or n divides m                         by divides_iff_lcm_fix
*)
Theorem monoid_order_divides_maximal[allow_rebind]:
  !g:'a monoid.
    FiniteAbelianMonoid g ==>
    !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g)
Proof
  rw[FiniteAbelianMonoid_def] >>
  ‘Monoid g’ by metis_tac[AbelianMonoid_def] >>
  qabbrev_tac ‘s = IMAGE ord G’ >>
  qabbrev_tac ‘m = MAX_SET s’ >>
  qabbrev_tac ‘n = ord x’ >>
  ‘#e IN G /\ (ord #e = 1)’ by rw[] >>
  ‘s <> {}’ by metis_tac[IN_IMAGE, MEMBER_NOT_EMPTY] >>
  ‘FINITE s’ by rw[Abbr‘s’] >>
  ‘m IN s /\ !y. y IN s ==> y <= m’ by rw[MAX_SET_DEF, Abbr‘m’] >>
  ‘?z. z IN G /\ (ord z = m)’ by metis_tac[IN_IMAGE] >>
  ‘?y. y IN G /\ (ord y = lcm n m)’ by metis_tac[abelian_monoid_order_lcm] >>
  ‘n IN s /\ ord y IN s’ by rw[Abbr‘s’, Abbr‘n’] >>
  ‘n <= m /\ lcm n m <= m’ by metis_tac[] >>
  ‘0 < m’ by decide_tac >>
  ‘m <= lcm n m’ by rw[LCM_LE] >>
  rw[divides_iff_lcm_fix]
QED

(* ------------------------------------------------------------------------- *)
(* Monoid Invertibles                                                        *)
(* ------------------------------------------------------------------------- *)

(* The Invertibles are those with inverses. *)
val monoid_invertibles_def = Define`
    monoid_invertibles (g:'a monoid) =
    { x | x IN G /\ (?y. y IN G /\ (x * y = #e) /\ (y * x = #e)) }
`;
val _ = overload_on ("G*", ``monoid_invertibles g``);

(* Theorem: x IN G* <=> x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e) *)
(* Proof: by monoid_invertibles_def. *)
val monoid_invertibles_element = store_thm(
  "monoid_invertibles_element",
  ``!g:'a monoid x. x IN G* <=> x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)``,
  rw[monoid_invertibles_def]);

(* Theorem: Monoid g /\ x IN G /\ 0 < ord x ==> x IN G*  *)
(* Proof:
   By monoid_invertibles_def, this is to show:
      ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)
   Since x ** (ord x) = #e           by order_property
     and ord x = SUC n               by ord x <> 0
    Now, x ** SUC n = x * x ** n     by monoid_exp_SUC
         x ** SUC n = x ** n * x     by monoid_exp_suc
     and x ** n IN G                 by monoid_exp_element
    Hence taking y = x ** n will satisfy the requirements.
*)
val monoid_order_nonzero = store_thm(
  "monoid_order_nonzero",
  ``!g:'a monoid x. Monoid g /\ x IN G  /\ 0 < ord x ==> x IN G*``,
  rw[monoid_invertibles_def] >>
  `x ** (ord x) = #e` by rw[order_property] >>
  `ord x <> 0` by decide_tac >>
  metis_tac[num_CASES, monoid_exp_SUC, monoid_exp_suc, monoid_exp_element]);

(* The Invertibles of a monoid, will be a Group. *)
val Invertibles_def = Define`
  Invertibles (g:'a monoid) : 'a monoid =
    <| carrier := G*;
            op := g.op;
            id := g.id
     |>
`;
(*
- type_of ``Invertibles g``;
> val it = ``:'a moniod`` : hol_type
*)

(* Theorem: properties of Invertibles *)
(* Proof: by Invertibles_def. *)
val Invertibles_property = store_thm(
  "Invertibles_property",
  ``!g:'a monoid. ((Invertibles g).carrier = G*) /\
                 ((Invertibles g).op = g.op) /\
                 ((Invertibles g).id = #e) /\
                 ((Invertibles g).exp = g.exp)``,
  rw[Invertibles_def, monoid_exp_def, FUN_EQ_THM]);

(* Theorem: (Invertibles g).carrier = monoid_invertibles g *)
(* Proof: by Invertibles_def. *)
val Invertibles_carrier = store_thm(
  "Invertibles_carrier",
  ``!g:'a monoid. (Invertibles g).carrier = monoid_invertibles g``,
  rw[Invertibles_def]);

(* Theorem: (Invertibles g).carrier SUBSET G *)
(* Proof:
    (Invertibles g).carrier
   = G*                         by Invertibles_def
   = {x | x IN G /\ ... }       by monoid_invertibles_def
   SUBSET G                     by SUBSET_DEF
*)
val Invertibles_subset = store_thm(
  "Invertibles_subset",
  ``!g:'a monoid. (Invertibles g).carrier SUBSET G``,
  rw[Invertibles_def, monoid_invertibles_def, SUBSET_DEF]);

(* Theorem: order (Invertibles g) x = order g x *)
(* Proof: order_def, period_def, Invertibles_property *)
val Invertibles_order = store_thm(
  "Invertibles_order",
  ``!g:'a monoid. !x. order (Invertibles g) x = order g x``,
  rw[order_def, period_def, Invertibles_property]);

(* ------------------------------------------------------------------------- *)
(* Monoid Inverse as an operation                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN G* means inverse of x exists. *)
(* Proof: by definition of G*. *)
val monoid_inv_from_invertibles = store_thm(
  "monoid_inv_from_invertibles",
  ``!g:'a monoid. Monoid g ==> !x. x IN G* ==> ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)``,
  rw[monoid_invertibles_def]);

(* Convert this into the form: !g x. ?y. ..... for SKOLEM_THM *)
val lemma = prove(
  ``!(g:'a monoid) x. ?y. Monoid g /\ x IN G* ==> y IN G /\ (x * y = #e) /\ (y * x = #e)``,
  metis_tac[monoid_inv_from_invertibles]);

(* Convert this into the form: !g x. ?y. ..... for SKOLEM_THM

   NOTE: added ‘(Monoid g /\ x NOTIN G* ==> y = ARB)’ to make it a total function.
val lemma = prove(
   “!(g:'a monoid) x.
        ?y. (Monoid g /\ x IN G* ==> y IN G /\ (x * y = #e) /\ (y * x = #e)) /\
            (Monoid g /\ x NOTIN G* ==> y = ARB)”,
    rpt GEN_TAC
 >> MP_TAC (Q.SPEC ‘g’ monoid_inv_from_invertibles)
 >> Cases_on ‘Monoid g’ >> rw []
 >> Cases_on ‘x IN G*’ >> rw []);
 *)

(* Use Skolemization to generate the monoid_inv_from_invertibles function *)
val monoid_inv_def = new_specification(
   "monoid_inv_def", ["monoid_inv"], (* name of function *)
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* |- !g x. Monoid g /\ x IN G* ==>
            monoid_inv g x IN G /\ (x * monoid_inv g x = #e) /\
                                   (monoid_inv g x * x = #e) *)
(*
- type_of ``monoid_inv g``;
> val it = ``:'a -> 'a`` : hol_type
*)

(* Convert inv function to inv field, i.e. m.inv is defined to be monoid_inv. *)
val _ = add_record_field ("inv", ``monoid_inv``);
(*
- type_of ``g.inv``;
> val it = ``:'a -> 'a`` : hol_type
*)
(* val _ = overload_on ("|/", ``g.inv``); *) (* for non-unicode input *)

(* for unicode dispaly *)
val _ = add_rule{fixity = Suffix 2100,
                 term_name = "reciprocal",
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = OnlyIfNecessary,
                 pp_elements = [TOK (UnicodeChars.sup_minus ^ UnicodeChars.sup_1)]};
val _ = overload_on("reciprocal", ``monoid_inv g``);
val _ = overload_on ("|/", ``reciprocal``); (* for non-unicode input *)

(* This means: reciprocal will have the display $^{-1}$, and here reciprocal is
   short-name for monoid_inv g *)

(* - monoid_inv_def;
> val it = |- !g x. Monoid g /\ x IN G* ==> |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e) : thm
*)

(* Theorem: x IN G* <=> x IN G /\ |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e) *)
(* Proof: by definition. *)
val monoid_inv_def_alt = store_thm(
  "monoid_inv_def_alt",
  ``!g:'a monoid. Monoid g ==> (!x. x IN G* <=> x IN G /\ |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e))``,
  rw[monoid_invertibles_def, monoid_inv_def, EQ_IMP_THM] >>
  metis_tac[]);

(* In preparation for: The invertibles of a monoid form a group. *)

(* Theorem: x IN G* ==> x IN G *)
(* Proof: by definition of G*. *)
val monoid_inv_element = store_thm(
  "monoid_inv_element",
  ``!g:'a monoid. Monoid g ==> !x. x IN G* ==> x IN G``,
  rw[monoid_invertibles_def]);

(* This export will cause rewrites of RHS = x IN G to become proving LHS = x IN G*, which is not useful. *)
(* val _ = export_rewrites ["monoid_inv_element"]; *)

(* Theorem: #e IN G* *)
(* Proof: by monoid_id and definition. *)
val monoid_id_invertible = store_thm(
  "monoid_id_invertible",
  ``!g:'a monoid. Monoid g ==> #e IN G*``,
  rw[monoid_invertibles_def] >>
  qexists_tac `#e` >>
  rw[]);

val _ = export_rewrites ["monoid_id_invertible"];

(* This is a direct proof, next one is shorter. *)

(* Theorem: [Closure for Invertibles] x, y IN G* ==> x * y IN G* *)
(* Proof: inverse of (x * y) = (inverse of y) * (inverse of x)
   Note x IN G* ==>
        |/x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)   by monoid_inv_def
        y IN G* ==>
        |/y IN G /\ (y * |/ y = #e) /\ ( |/ y * y = #e)   by monoid_inv_def
    Now x * y IN G and | /y * | / x IN G       by monoid_op_element
    and (x * y) * ( |/ y * |/ x) = #e          by monoid_assoc, monoid_lid
    also ( |/ y * |/ x) * (x * y) = #e         by monoid_assoc, monoid_lid
    Thus x * y IN G*, with ( |/ y * |/ x) as its inverse.
*)
val monoid_inv_op_invertible = store_thm(
  "monoid_inv_op_invertible",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G* /\ y IN G* ==> x * y IN G*``,
  rpt strip_tac>>
  `x IN G /\ y IN G` by rw_tac std_ss[monoid_inv_element] >>
  `|/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)` by rw_tac std_ss[monoid_inv_def] >>
  `|/ y IN G /\ (y * |/ y = #e) /\ ( |/ y * y = #e)` by rw_tac std_ss[monoid_inv_def] >>
  `x * y IN G /\ |/ y * |/ x IN G` by rw_tac std_ss[monoid_op_element] >>
  `(x * y) * ( |/ y * |/ x) = x * ((y * |/ y) * |/ x)` by rw_tac std_ss[monoid_assoc, monoid_op_element] >>
  `( |/ y * |/ x) * (x * y) = |/ y * (( |/ x * x) * y)` by rw_tac std_ss[monoid_assoc, monoid_op_element] >>
  rw_tac std_ss[monoid_invertibles_def, GSPECIFICATION] >>
  metis_tac[monoid_lid]);

(* Better proof of the same theorem. *)

(* Theorem: [Closure for Invertibles] x, y IN G* ==> x * y IN G* *)
(* Proof: inverse of (x * y) = (inverse of y) * (inverse of x)  *)
Theorem monoid_inv_op_invertible[allow_rebind,simp]:
  !g:'a monoid. Monoid g ==> !x y. x IN G* /\ y IN G* ==> x * y IN G*
Proof
  rw[monoid_invertibles_def] >>
  qexists_tac `y'' * y'` >>
  rw_tac std_ss[monoid_op_element] >| [
    `x * y * (y'' * y') = x * ((y * y'') * y')` by rw[monoid_assoc],
    `y'' * y' * (x * y) = y'' * ((y' * x) * y)` by rw[monoid_assoc]
  ] >> rw_tac std_ss[monoid_lid]
QED

(* Theorem: x IN G* ==> |/ x IN G* *)
(* Proof: by monoid_inv_def. *)
val monoid_inv_invertible = store_thm(
  "monoid_inv_invertible",
  ``!g:'a monoid. Monoid g ==> !x. x IN G* ==> |/ x IN G*``,
  rpt strip_tac >>
  rw[monoid_invertibles_def] >-
  rw[monoid_inv_def] >>
  metis_tac[monoid_inv_def, monoid_inv_element]);

val _ = export_rewrites ["monoid_inv_invertible"];

(* Theorem: The Invertibles of a monoid form a monoid. *)
(* Proof: by checking definition. *)
val monoid_invertibles_is_monoid = store_thm(
  "monoid_invertibles_is_monoid",
  ``!g. Monoid g ==> Monoid (Invertibles g)``,
  rpt strip_tac >>
  `!x. x IN G* ==> x IN G` by rw[monoid_inv_element] >>
  rw[Invertibles_def] >>
  rewrite_tac[Monoid_def] >>
  rw[monoid_assoc]);

(* ------------------------------------------------------------------------- *)
(* Monoid Maps Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   H      = h.carrier
   o      = binary operation of homo_monoid: (homo_monoid g f).op
   #i     = identity of homo_monoid: (homo_monoid g f).id
   fG     = carrier of homo_monoid: (homo_monoid g f).carrier
*)
(* Definitions and Theorems (# are exported):

   Homomorphism, isomorphism, endomorphism, automorphism and submonoid:
   MonoidHomo_def   |- !f g h. MonoidHomo f g h <=>
                               (!x. x IN G ==> f x IN h.carrier) /\ (f #e = h.id) /\
                               !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   MonoidIso_def    |- !f g h. MonoidIso f g h <=> MonoidHomo f g h /\ BIJ f G h.carrier
   MonoidEndo_def   |- !f g. MonoidEndo f g <=> MonoidHomo f g g
   MonoidAuto_def   |- !f g. MonoidAuto f g <=> MonoidIso f g g
   submonoid_def    |- !h g. submonoid h g <=> MonoidHomo I h g

   Monoid Homomorphisms:
   monoid_homo_id       |- !f g h. MonoidHomo f g h ==> (f #e = h.id)
   monoid_homo_element  |- !f g h. MonoidHomo f g h ==> !x. x IN G ==> f x IN h.carrier
   monoid_homo_cong     |- !g h f1 f2. Monoid g /\ Monoid h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
                                       (MonoidHomo f1 g h <=> MonoidHomo f2 g h)
   monoid_homo_I_refl   |- !g. MonoidHomo I g g
   monoid_homo_trans    |- !g h k f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
   monoid_homo_sym      |- !g h f. Monoid g /\ MonoidHomo f g h /\ BIJ f G h.carrier ==> MonoidHomo (LINV f G) h g
   monoid_homo_compose  |- !g h k f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
   monoid_homo_exp      |- !g h f. Monoid g /\ MonoidHomo f g h ==>
                           !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n

   Monoid Isomorphisms:
   monoid_iso_property  |- !f g h. MonoidIso f g h <=>
                                   MonoidHomo f g h /\ !y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)
   monoid_iso_id        |- !f g h. MonoidIso f g h ==> (f #e = h.id)
   monoid_iso_element   |- !f g h. MonoidIso f g h ==> !x. x IN G ==> f x IN h.carrier
   monoid_iso_monoid    |- !g h f. Monoid g /\ MonoidIso f g h ==> Monoid h
   monoid_iso_I_refl    |- !g. MonoidIso I g g
   monoid_iso_trans     |- !g h k f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k
   monoid_iso_sym       |- !g h f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g
   monoid_iso_compose   |- !g h k f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k
   monoid_iso_exp       |- !g h f. Monoid g /\ MonoidIso f g h ==>
                           !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n
   monoid_iso_linv_iso  |- !g h f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g
   monoid_iso_bij       |- !g h f. MonoidIso f g h ==> BIJ f G h.carrier
   monoid_iso_eq_id     |- !g h f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
                           !x. x IN G ==> ((f x = h.id) <=> (x = #e))
   monoid_iso_order     |- !g h f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
                           !x. x IN G ==> (order h (f x) = ord x)
   monoid_iso_card_eq   |- !g h f. MonoidIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)

   Monoid Automorphisms:
   monoid_auto_id       |- !f g. MonoidAuto f g ==> (f #e = #e)
   monoid_auto_element  |- !f g. MonoidAuto f g ==> !x. x IN G ==> f x IN G
   monoid_auto_compose  |- !g f1 f2. MonoidAuto f1 g /\ MonoidAuto f2 g ==> MonoidAuto (f1 o f2) g
   monoid_auto_exp      |- !g f. Monoid g /\ MonoidAuto f g ==>
                           !x. x IN G ==> !n. f (x ** n) = f x ** n
   monoid_auto_I        |- !g. MonoidAuto I g
   monoid_auto_linv_auto|- !g f. Monoid g /\ MonoidAuto f g ==> MonoidAuto (LINV f G) g
   monoid_auto_bij      |- !g f. MonoidAuto f g ==> f PERMUTES G
   monoid_auto_order    |- !g f. Monoid g /\ MonoidAuto f g ==>
                           !x. x IN G ==> (ord (f x) = ord x)

   Submonoids:
   submonoid_eqn               |- !g h. submonoid h g <=> H SUBSET G /\
                                        (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\ (h.id = #e)
   submonoid_subset            |- !g h. submonoid h g ==> H SUBSET G
   submonoid_homo_homo         |- !g h k f. submonoid h g /\ MonoidHomo f g k ==> MonoidHomo f h k
   submonoid_refl              |- !g. submonoid g g
   submonoid_trans             |- !g h k. submonoid g h /\ submonoid h k ==> submonoid g k
   submonoid_I_antisym         |- !g h. submonoid h g /\ submonoid g h ==> MonoidIso I h g
   submonoid_carrier_antisym   |- !g h. submonoid h g /\ G SUBSET H ==> MonoidIso I h g
   submonoid_order_eqn         |- !g h. Monoid g /\ Monoid h /\ submonoid h g ==>
                                  !x. x IN H ==> (order h x = ord x)

   Homomorphic Image of Monoid:
   image_op_def         |- !g f x y. image_op g f x y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))
   image_op_inj         |- !g f. INJ f G univ(:'b) ==>
                           !x y. x IN G /\ y IN G ==> (image_op g f (f x) (f y) = f (x * y))
   homo_monoid_def      |- !g f. homo_monoid g f = <|carrier := IMAGE f G; op := image_op g f; id := f #e|>
   homo_monoid_property |- !g f. (fG = IMAGE f G) /\
                                 (!x y. x IN fG /\ y IN fG ==>
                                       (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))) /\
                                 (#i = f #e)
   homo_monoid_element  |- !g f x. x IN G ==> f x IN fG
   homo_monoid_id       |- !g f. f #e = #i
   homo_monoid_op_inj   |- !g f. INJ f G univ(:'b) ==> !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   homo_monoid_I        |- !g. MonoidIso I (homo_group g I) g

   homo_monoid_closure         |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                  !x y. x IN fG /\ y IN fG ==> x o y IN fG
   homo_monoid_assoc           |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                  !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o y o z)
   homo_monoid_id_property     |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> #i IN fG /\
                                  !x. x IN fG ==> (#i o x = x) /\ (x o #i = x)
   homo_monoid_comm            |- !g f. AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                  !x y. x IN fG /\ y IN fG ==> (x o y = y o x)
   homo_monoid_monoid          |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> Monoid (homo_monoid g f)
   homo_monoid_abelian_monoid  |- !g f. AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                        AbelianMonoid (homo_monoid g f)
   homo_monoid_by_inj          |- !g f. Monoid g /\ INJ f G univ(:'b) ==> MonoidHomo f g (homo_monoid g f)

   Weaker form of Homomorphic of Monoid and image of identity:
   WeakHomo_def        |- !f g h. WeakHomo f g h <=>
                           (!x. x IN G ==> f x IN h.carrier) /\
                            !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   WeakIso_def         |- !f g h. WeakIso f g h <=> WeakHomo f g h /\ BIJ f G h.carrier
   monoid_weak_iso_id  |- !f g h. Monoid g /\ Monoid h /\ WeakIso f g h ==> (f #e = h.id)

   Injective Image of Monoid:
   monoid_inj_image_def             |- !g f. monoid_inj_image g f =
                                             <|carrier := IMAGE f G;
                                                    op := (let t = LINV f G in \x y. f (t x * t y));
                                                    id := f #e
                                              |>
   monoid_inj_image_monoid          |- !g f. Monoid g /\ INJ f G univ(:'b) ==> Monoid (monoid_inj_image g f)
   monoid_inj_image_abelian_monoid  |- !g f. AbelianMonoid g /\ INJ f G univ(:'b) ==> AbelianMonoid (monoid_inj_image g f)
   monoid_inj_image_monoid_homo     |- !g f. INJ f G univ(:'b) ==> MonoidHomo f g (monoid_inj_image g f)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphism, isomorphism, endomorphism, automorphism and submonoid.      *)
(* ------------------------------------------------------------------------- *)

(* val _ = overload_on ("H", ``h.carrier``);

- type_of ``H``;
> val it = ``:'a -> bool`` : hol_type

then MonoidIso f g h = MonoidHomo f g h /\ BIJ f G H
will make MonoidIso apply only for f: 'a -> 'a.

will need val _ = overload_on ("H", ``(h:'b monoid).carrier``);
*)

(* A function f from g to h is a homomorphism if monoid properties are preserved. *)
(* For monoids, need to ensure that identity is preserved, too. See: monoid_weak_iso_id. *)
val MonoidHomo_def = Define`
  MonoidHomo (f:'a -> 'b) (g:'a monoid) (h:'b monoid) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))) /\
    (f #e = h.id)
`;
(*
If MonoidHomo_def uses the condition: !x y. f (x * y) = h.op (f x) (f y)
this will mean a corresponding change in GroupHomo_def, but then
in quotientGroup <<normal_subgroup_coset_homo>> will give a goal:
h <= g ==> x * y * H = (x * H) o (y * H) with no qualification on x, y!
*)

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val MonoidIso_def = Define`
  MonoidIso f g h <=> MonoidHomo f g h /\ BIJ f G h.carrier
`;

(* A monoid homomorphism from g to g is an endomorphism. *)
val MonoidEndo_def = Define `MonoidEndo f g <=> MonoidHomo f g g`;

(* A monoid isomorphism from g to g is an automorphism. *)
val MonoidAuto_def = Define `MonoidAuto f g <=> MonoidIso f g g`;

(* A submonoid h of g if identity is a homomorphism from h to g *)
val submonoid_def = Define `submonoid h g <=> MonoidHomo I h g`;

(* ------------------------------------------------------------------------- *)
(* Monoid Homomorphisms                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MonoidHomo f g h ==> (f #e = h.id) *)
(* Proof: by MonoidHomo_def. *)
val monoid_homo_id = store_thm(
  "monoid_homo_id",
  ``!f g h. MonoidHomo f g h ==> (f #e = h.id)``,
  rw[MonoidHomo_def]);

(* Theorem: MonoidHomo f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by MonoidHomo_def *)
val monoid_homo_element = store_thm(
  "monoid_homo_element",
  ``!f g h. MonoidHomo f g h ==> !x. x IN G ==> f x IN h.carrier``,
  rw_tac std_ss[MonoidHomo_def]);

(* Theorem: Monoid g /\ Monoid h /\ (!x. x IN G ==> (f1 x = f2 x)) ==> (MonoidHomo f1 g h = MonoidHomo f2 g h) *)
(* Proof: by MonoidHomo_def, monoid_op_element, monoid_id_element *)
val monoid_homo_cong = store_thm(
  "monoid_homo_cong",
  ``!g h f1 f2. Monoid g /\ Monoid h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
               (MonoidHomo f1 g h = MonoidHomo f2 g h)``,
  rw_tac std_ss[MonoidHomo_def, EQ_IMP_THM] >-
  metis_tac[monoid_op_element] >-
  metis_tac[monoid_id_element] >-
  metis_tac[monoid_op_element] >>
  metis_tac[monoid_id_element]);

(* Theorem: MonoidHomo I g g *)
(* Proof: by MonoidHomo_def. *)
val monoid_homo_I_refl = store_thm(
  "monoid_homo_I_refl",
  ``!g:'a monoid. MonoidHomo I g g``,
  rw[MonoidHomo_def]);

(* Theorem: MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo f2 o f1 g k *)
(* Proof: true by MonoidHomo_def. *)
val monoid_homo_trans = store_thm(
  "monoid_homo_trans",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
    !f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k``,
  rw[MonoidHomo_def]);

(* Theorem: Monoid g /\ MonoidHomo f g h /\ BIJ f G h.carrier ==> MonoidHomo (LINV f G) h g *)
(* Proof:
   Note BIJ f G h.carrier
    ==> BIJ (LINV f G) h.carrier G     by BIJ_LINV_BIJ
   By MonoidHomo_def, this is to show:
   (1) x IN h.carrier ==> LINV f G x IN G
       With BIJ (LINV f G) h.carrier G
        ==> INJ (LINV f G) h.carrier G           by BIJ_DEF
        ==> x IN h.carrier ==> LINV f G x IN G   by INJ_DEF
   (2) x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       With x IN h.carrier
        ==> ?x1. (x = f x1) /\ x1 IN G           by BIJ_DEF, SURJ_DEF
       With y IN h.carrier
        ==> ?y1. (y = f y1) /\ y1 IN G           by BIJ_DEF, SURJ_DEF
        and x1 * y1 IN G                         by monoid_op_element
            LINV f G (h.op x y)
          = LINV f G (f (x1 * y1))                  by MonoidHomo_def
          = x1 * y1                                 by BIJ_LINV_THM, x1 * y1 IN G
          = (LINV f G (f x1)) * (LINV f G (f y1))   by BIJ_LINV_THM, x1 IN G, y1 IN G
          = (LINV f G x) * (LINV f G y)             by x = f x1, y = f y1.
   (3) LINV f G h.id = #e
       Since #e IN G                   by monoid_id_element
         LINV f G h.id
       = LINV f G (f #e)               by MonoidHomo_def
       = #e                            by BIJ_LINV_THM
*)
val monoid_homo_sym = store_thm(
  "monoid_homo_sym",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidHomo f g h /\ BIJ f G h.carrier ==>
        MonoidHomo (LINV f G) h g``,
  rpt strip_tac >>
  `BIJ (LINV f G) h.carrier G` by rw[BIJ_LINV_BIJ] >>
  fs[MonoidHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >-
 (`?x1. (x = f x1) /\ x1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `?y1. (y = f y1) /\ y1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `g.op x1 y1 IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]) >>
  `#e IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]);

Theorem monoid_homo_sym_any:
  Monoid g /\ MonoidHomo f g h /\
  (!x. x IN h.carrier ==> i x IN g.carrier /\ f (i x) = x) /\
  (!x. x IN g.carrier ==> i (f x) = x)
  ==>
  MonoidHomo i h g
Proof
  rpt strip_tac >> fs[MonoidHomo_def]
  \\ metis_tac[Monoid_def]
QED

(* Theorem: MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k *)
(* Proof: by MonoidHomo_def *)
val monoid_homo_compose = store_thm(
  "monoid_homo_compose",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
   !f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k``,
  rw_tac std_ss[MonoidHomo_def]);
(* This is the same as monoid_homo_trans *)

(* Theorem: Monoid g /\ MonoidHomo f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   By induction on n.
   Base: f (x ** 0) = h.exp (f x) 0
         f (x ** 0)
       = f #e                by monoid_exp_0
       = h.id                by monoid_homo_id
       = h.exp (f x) 0       by monoid_exp_0
   Step: f (x ** SUC n) = h.exp (f x) (SUC n)
       Note x ** n IN G               by monoid_exp_element
         f (x ** SUC n)
       = f (x * x ** n)               by monoid_exp_SUC
       = h.op (f x) (f (x ** n))      by MonoidHomo_def
       = h.op (f x) (h.exp (f x) n)   by induction hypothesis
       = h.exp (f x) (SUC n)          by monoid_exp_SUC
*)
val monoid_homo_exp = store_thm(
  "monoid_homo_exp",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidHomo f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[monoid_exp_0, monoid_homo_id] >>
  fs[monoid_exp_SUC, MonoidHomo_def]);

(* ------------------------------------------------------------------------- *)
(* Monoid Isomorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MonoidIso f g h <=> MonoidHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) BIJ f G H /\ y IN H ==> ?!x. x IN G /\ (f x = y)
       true by INJ_DEF and SURJ_DEF.
   (2) !y. y IN H /\ MonoidHomo f g h ==> ?!x. x IN G /\ (f x = y) ==> BIJ f G H
       true by INJ_DEF and SURJ_DEF, and
       x IN G /\ GroupHomo f g h ==> f x IN H  by MonoidHomo_def
*)
val monoid_iso_property = store_thm(
  "monoid_iso_property",
  ``!f g h. MonoidIso f g h <=> MonoidHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y))``,
  rw_tac std_ss[MonoidIso_def, EQ_IMP_THM] >-
  metis_tac[BIJ_THM] >>
  rw[BIJ_THM] >>
  metis_tac[MonoidHomo_def]);

(* Note: all these proofs so far do not require the condition: f #e = h.id in MonoidHomo_def,
   but evetually it should, as this is included in definitions of all resources. *)

(* Theorem: MonoidIso f g h ==> (f #e = h.id) *)
(* Proof: by MonoidIso_def, monoid_homo_id. *)
val monoid_iso_id = store_thm(
  "monoid_iso_id",
  ``!f g h. MonoidIso f g h ==> (f #e = h.id)``,
  rw_tac std_ss[MonoidIso_def, monoid_homo_id]);

(* Theorem: MonoidIso f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by MonoidIso_def, monoid_homo_element *)
val monoid_iso_element = store_thm(
  "monoid_iso_element",
  ``!f g h. MonoidIso f g h ==> !x. x IN G ==> f x IN h.carrier``,
  metis_tac[MonoidIso_def, monoid_homo_element]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> Monoid h  *)
(* Proof:
   This is to show:
   (1) x IN h.carrier /\ y IN h.carrier ==> h.op x y IN h.carrier
       Since ?x'. x' IN G /\ (f x' = x)   by monoid_iso_property
             ?y'. y' IN G /\ (f y' = y)   by monoid_iso_property
             h.op x y = f (x' * y')       by MonoidHomo_def
       As                  x' * y' IN G   by monoid_op_element
       hence f (x' * y') IN h.carrier     by MonoidHomo_def
   (2) x IN h.carrier /\ y IN h.carrier /\ z IN h.carrier ==> h.op (h.op x y) z = h.op x (h.op y z)
       Since ?x'. x' IN G /\ (f x' = x)   by monoid_iso_property
             ?y'. y' IN G /\ (f y' = y)   by monoid_iso_property
             ?z'. z' IN G /\ (f z' = z)   by monoid_iso_property
       as     x' * y' IN G                by monoid_op_element
       and f (x' * y') IN h.carrier       by MonoidHomo_def
       ?!t. t IN G /\ f t = f (x' * y')   by monoid_iso_property
       i.e.  t = x' * y'                  by uniqueness
       hence h.op (h.op x y) z = f (x' * y' * z')     by MonoidHomo_def
       Similary,
       as     y' * z' IN G                by monoid_op_element
       and f (y' * z') IN h.carrier       by MonoidHomo_def
       ?!s. s IN G /\ f s = f (y' * z')   by monoid_iso_property
       i.e.  s = y' * z'                  by uniqueness
       and   h.op x (h.op y z) = f (x' * (y' * z'))   by MonoidHomo_def
       hence true by monoid_assoc.
   (3) h.id IN h.carrier
       Since #e IN G                     by monoid_id_element
            (f #e) = h.id IN h.carrier   by MonoidHomo_def
   (4) x IN h.carrier ==> h.op h.id x = x
       Since ?x'. x' IN G /\ (f x' = x)  by monoid_iso_property
       h.id IN h.carrier                 by monoid_id_element
       ?!e. e IN G /\ f e = h.id = f #e  by monoid_iso_property
       i.e. e = #e                       by uniqueness
       hence h.op h.id x = f (e * x')    by MonoidHomo_def
                         = f (#e * x')
                         = f x'          by monoid_lid
                         = x
   (5) x IN h.carrier ==> h.op x h.id = x
       Since ?x'. x' IN G /\ (f x' = x)  by monoid_iso_property
       h.id IN h.carrier                 by monoid_id_element
       ?!e. e IN G /\ f e = h.id = f #e  by monoid_iso_property
       i.e. e = #e                       by uniqueness
       hence h.op x h.id = f (x' * e)    by MonoidHomo_def
                         = f (x' * #e)
                         = f x'          by monoid_rid
                         = x
*)
val monoid_iso_monoid = store_thm(
  "monoid_iso_monoid",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==> Monoid h``,
  rw[monoid_iso_property] >>
  `(!x. x IN G ==> f x IN h.carrier) /\
     (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))) /\
     (f #e = h.id)` by metis_tac[MonoidHomo_def] >>
  rw_tac std_ss[Monoid_def] >-
  metis_tac[monoid_op_element] >-
 (`?x'. x' IN G /\ (f x' = x)` by metis_tac[] >>
  `?y'. y' IN G /\ (f y' = y)` by metis_tac[] >>
  `?z'. z' IN G /\ (f z' = z)` by metis_tac[] >>
  `?t. t IN G /\ (t = x' * y')` by metis_tac[monoid_op_element] >>
  `h.op (h.op x y) z = f (x' * y' * z')` by metis_tac[] >>
  `?s. s IN G /\ (s = y' * z')` by metis_tac[monoid_op_element] >>
  `h.op x (h.op y z) = f (x' * (y' * z'))` by metis_tac[] >>
  `x' * y' * z' = x' * (y' * z')` by rw[monoid_assoc] >>
  metis_tac[]) >-
  metis_tac[monoid_id_element, MonoidHomo_def] >-
  metis_tac[monoid_lid, monoid_id_element] >>
  metis_tac[monoid_rid, monoid_id_element]);

(* Theorem: MonoidIso I g g *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo I g g, true by monoid_homo_I_refl
   (2) BIJ I R R, true by BIJ_I_SAME
*)
val monoid_iso_I_refl = store_thm(
  "monoid_iso_I_refl",
  ``!g:'a monoid. MonoidIso I g g``,
  rw[MonoidIso_def, monoid_homo_I_refl, BIJ_I_SAME]);

(* Theorem: MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
       True by monoid_homo_trans.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE.
*)
val monoid_iso_trans = store_thm(
  "monoid_iso_trans",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
    !f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k``,
  rw[MonoidIso_def] >-
  metis_tac[monoid_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo f g h /\ BIJ f G h.carrier ==> MonoidHomo (LINV f G) h g
       True by monoid_homo_sym.
   (2) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val monoid_iso_sym = store_thm(
  "monoid_iso_sym",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g``,
  rw[MonoidIso_def, monoid_homo_sym, BIJ_LINV_BIJ]);

(* Theorem: MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
       True by monoid_homo_compose.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE
*)
val monoid_iso_compose = store_thm(
  "monoid_iso_compose",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
   !f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k``,
  rw_tac std_ss[MonoidIso_def] >-
  metis_tac[monoid_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as monoid_iso_trans. *)

(* Theorem: Monoid g /\ MonoidIso f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof: by MonoidIso_def, monoid_homo_exp *)
val monoid_iso_exp = store_thm(
  "monoid_iso_exp",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[MonoidIso_def, monoid_homo_exp]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g *)
(* Proof:
   By MonoidIso_def, MonoidHomo_def, this is to show:
   (1) BIJ f G h.carrier /\ x IN h.carrier ==> LINV f G x IN G
       True by BIJ_LINV_ELEMENT
   (2) BIJ f G h.carrier /\ x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       Let x' = LINV f G x, y' = LINV f G y.
       Then x' IN G /\ y' IN G        by BIJ_LINV_ELEMENT
         so x' * y' IN G              by monoid_op_element
        ==> f (x' * y') = h.op (f x') (f y')    by MonoidHomo_def
                        = h.op x y              by BIJ_LINV_THM
       Thus LINV f G (h.op x y)
          = LINV f G (f (x' * y'))    by above
          = x' * y'                   by BIJ_LINV_THM
   (3) BIJ f G h.carrier ==> LINV f G h.id = #e
       Note #e IN G                   by monoid_id_element
        and f #e = h.id               by MonoidHomo_def
        ==> LINV f G h.id = #e        by BIJ_LINV_THM
   (4) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val monoid_iso_linv_iso = store_thm(
  "monoid_iso_linv_iso",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g``,
  rw_tac std_ss[MonoidIso_def, MonoidHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
 (qabbrev_tac `x' = LINV f G x` >>
  qabbrev_tac `y' = LINV f G y` >>
  metis_tac[BIJ_LINV_THM, BIJ_LINV_ELEMENT, monoid_op_element]) >-
  metis_tac[BIJ_LINV_THM, monoid_id_element] >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as monoid_iso_sym, just a direct proof. *)

(* Theorem: MonoidIso f g h ==> BIJ f G h.carrier *)
(* Proof: by MonoidIso_def *)
val monoid_iso_bij = store_thm(
  "monoid_iso_bij",
  ``!(g:'a monoid) (h:'b monoid) f. MonoidIso f g h ==> BIJ f G h.carrier``,
  rw_tac std_ss[MonoidIso_def]);

(* Theorem: Monoid g /\ Monoid h /\ MonoidIso f g h ==>
            !x. x IN G ==> ((f x = h.id) <=> (x = #e)) *)
(* Proof:
   Note MonoidHomo f g h /\ BIJ f G h.carrier   by MonoidIso_def
   If part: x IN G /\ f x = h.id ==> x = #e
      By monoid_id_unique, this is to show:
      (1) !y. y IN G ==> y * x = y
          Let z = y * x.
          Then z IN G               by monoid_op_element
          f z = h.op (f y) (f x)    by MonoidHomo_def
              = h.op (f y) h.id     by f x = h.id
              = f y                 by monoid_homo_element, monoid_id
          Thus z = y                by BIJ_DEF, INJ_DEF
      (2) !y. y IN G ==> x * y = y
          Let z = x * y.
          Then z IN G               by monoid_op_element
          f z = h.op (f x) (f y)    by MonoidHomo_def
              = h.op h.id (f y)     by f x = h.id
              = f y                 by monoid_homo_element, monoid_id
          Thus z = y                by BIJ_DEF, INJ_DEF

   Only-if part: f #e = h.id, true  by monoid_homo_id
*)
val monoid_iso_eq_id = store_thm(
  "monoid_iso_eq_id",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
   !x. x IN G ==> ((f x = h.id) <=> (x = #e))``,
  rw[MonoidIso_def] >>
  rw[EQ_IMP_THM] >| [
    rw[GSYM monoid_id_unique] >| [
      qabbrev_tac `z = x' * x` >>
      `z IN G` by rw[Abbr`z`] >>
      `f z = h.op (f x') (f x)` by fs[MonoidHomo_def, Abbr`z`] >>
      `_ = f x'` by metis_tac[monoid_homo_element, monoid_id] >>
      metis_tac[BIJ_DEF, INJ_DEF],
      qabbrev_tac `z = x * x'` >>
      `z IN G` by rw[Abbr`z`] >>
      `f z = h.op (f x) (f x')` by fs[MonoidHomo_def, Abbr`z`] >>
      `_ = f x'` by metis_tac[monoid_homo_element, monoid_id] >>
      metis_tac[BIJ_DEF, INJ_DEF]
    ],
    rw[monoid_homo_id]
  ]);

(* Theorem: Monoid g /\ Monoid h /\ MonoidIso f g h ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Let n = ord x, y = f x.
   If n = 0, to show: order h y = 0.
      By contradiction, suppose order h y <> 0.
      Let m = order h y.
      Note h.id = h.exp y m          by order_property
                = f (x ** m)         by monoid_iso_exp
      Thus x ** m = #e               by monoid_iso_eq_id, monoid_exp_element
       But x ** m <> #e              by order_eq_0, ord x = 0
      This is a contradiction.

   If n <> 0, to show: order h y = n.
      Note ord x = n
       ==> (x ** n = #e) /\
           !m. 0 < m /\ m < n ==> x ** m <> #e    by order_thm, 0 < n
      Note h.exp y n = f (x ** n)    by monoid_iso_exp
                     = f #e          by x ** n = #e
                     = h.id          by monoid_iso_id, [1]
      Claim: !m. 0 < m /\ m < n ==> h.exp y m <> h.id
      Proof: By contradiction, suppose h.exp y m = h.id.
             Then f (x ** m) = h.exp y m    by monoid_iso_exp
                             = h.id         by above
               or     x ** m = #e           by monoid_iso_eq_id, monoid_exp_element
             But !m. 0 < m /\ m < n ==> x ** m <> #e   by above
             This is a contradiction.

      Thus by [1] and claim, order h y = n  by order_thm
*)
val monoid_iso_order = store_thm(
  "monoid_iso_order",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
   !x. x IN G ==> (order h (f x) = ord x)``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `y = f x` >>
  Cases_on `n = 0` >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `m = order h y` >>
    `0 < m` by decide_tac >>
    `h.exp y m = h.id` by metis_tac[order_property] >>
    `f (x ** m) = h.id` by metis_tac[monoid_iso_exp] >>
    `x ** m = #e` by metis_tac[monoid_iso_eq_id, monoid_exp_element] >>
    metis_tac[order_eq_0],
    `0 < n` by decide_tac >>
    `(x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e` by metis_tac[order_thm] >>
    `h.exp y n = h.id` by metis_tac[monoid_iso_exp, monoid_iso_id] >>
    `!m. 0 < m /\ m < n ==> h.exp y m <> h.id` by
  (spose_not_then strip_assume_tac >>
    `f (x ** m) = h.id` by metis_tac[monoid_iso_exp] >>
    `x ** m = #e` by metis_tac[monoid_iso_eq_id, monoid_exp_element] >>
    metis_tac[]) >>
    metis_tac[order_thm]
  ]);

(* Theorem: MonoidIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier) *)
(* Proof: by MonoidIso_def, FINITE_BIJ_CARD. *)
val monoid_iso_card_eq = store_thm(
  "monoid_iso_card_eq",
  ``!g:'a monoid h:'b monoid f. MonoidIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)``,
  metis_tac[MonoidIso_def, FINITE_BIJ_CARD]);

(* ------------------------------------------------------------------------- *)
(* Monoid Automorphisms                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MonoidAuto f g ==> (f #e = #e) *)
(* Proof: by MonoidAuto_def, monoid_iso_id. *)
val monoid_auto_id = store_thm(
  "monoid_auto_id",
  ``!f g. MonoidAuto f g ==> (f #e = #e)``,
  rw_tac std_ss[MonoidAuto_def, monoid_iso_id]);

(* Theorem: MonoidAuto f g ==> !x. x IN G ==> f x IN G *)
(* Proof: by MonoidAuto_def, monoid_iso_element *)
val monoid_auto_element = store_thm(
  "monoid_auto_element",
  ``!f g. MonoidAuto f g ==> !x. x IN G ==> f x IN G``,
  metis_tac[MonoidAuto_def, monoid_iso_element]);

(* Theorem: MonoidAuto f1 g /\ MonoidAuto f2 g ==> MonoidAuto (f1 o f2) g *)
(* Proof: by MonoidAuto_def, monoid_iso_compose *)
val monoid_auto_compose = store_thm(
  "monoid_auto_compose",
  ``!(g:'a monoid). !f1 f2. MonoidAuto f1 g /\ MonoidAuto f2 g ==> MonoidAuto (f1 o f2) g``,
  metis_tac[MonoidAuto_def, monoid_iso_compose]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n *)
(* Proof: by MonoidAuto_def, monoid_iso_exp *)
val monoid_auto_exp = store_thm(
  "monoid_auto_exp",
  ``!f g. Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n``,
  rw[MonoidAuto_def, monoid_iso_exp]);

(* Theorem: MonoidAuto I g *)
(* Proof:
       MonoidAuto I g
   <=> MonoidIso I g g                by MonoidAuto_def
   <=> MonoidHomo I g g /\ BIJ f G G  by MonoidIso_def
   <=> T /\ BIJ f G G                 by MonoidHomo_def, I_THM
   <=> T /\ T                         by BIJ_I_SAME
*)
val monoid_auto_I = store_thm(
  "monoid_auto_I",
  ``!(g:'a monoid). MonoidAuto I g``,
  rw_tac std_ss[MonoidAuto_def, MonoidIso_def, MonoidHomo_def, BIJ_I_SAME]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> MonoidAuto (LINV f G) g *)
(* Proof:
       MonoidAuto I g
   ==> MonoidIso I g g                by MonoidAuto_def
   ==> MonoidIso (LINV f G) g         by monoid_iso_linv_iso
   ==> MonoidAuto (LINV f G) g        by MonoidAuto_def
*)
val monoid_auto_linv_auto = store_thm(
  "monoid_auto_linv_auto",
  ``!(g:'a monoid) f. Monoid g /\ MonoidAuto f g ==> MonoidAuto (LINV f G) g``,
  rw_tac std_ss[MonoidAuto_def, monoid_iso_linv_iso]);

(* Theorem: MonoidAuto f g ==> f PERMUTES G *)
(* Proof: by MonoidAuto_def, MonoidIso_def *)
val monoid_auto_bij = store_thm(
  "monoid_auto_bij",
  ``!g:'a monoid. !f. MonoidAuto f g ==> f PERMUTES G``,
  rw_tac std_ss[MonoidAuto_def, MonoidIso_def]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> (ord (f x) = ord x) *)
(* Proof: by MonoidAuto_def, monoid_iso_order. *)
val monoid_auto_order = store_thm(
  "monoid_auto_order",
  ``!(g:'a monoid) f. Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> (ord (f x) = ord x)``,
  rw[MonoidAuto_def, monoid_iso_order]);

(* ------------------------------------------------------------------------- *)
(* Submonoids.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Use H to denote h.carrier *)
val _ = overload_on ("H", ``(h:'a monoid).carrier``);

(* Theorem: submonoid h g ==> H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\ (h.id = #e) *)
(* Proof:
       submonoid h g
   <=> MonoidHomo I h g           by submonoid_def
   <=> (!x. x IN H ==> I x IN G) /\
       (!x y. x IN H /\ y IN H ==> (I (h.op x y) = (I x) * (I y))) /\
       (h.id = I #e)              by MonoidHomo_def
   <=> (!x. x IN H ==> x IN G) /\
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\
       (h.id = #e)                by I_THM
   <=> H SUBSET G
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\
       (h.id = #e)                by SUBSET_DEF
*)
val submonoid_eqn = store_thm(
  "submonoid_eqn",
  ``!(g:'a monoid) (h:'a monoid). submonoid h g <=>
     H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\ (h.id = #e)``,
  rw_tac std_ss[submonoid_def, MonoidHomo_def, SUBSET_DEF]);

(* Theorem: submonoid h g ==> H SUBSET G *)
(* Proof: by submonoid_eqn *)
val submonoid_subset = store_thm(
  "submonoid_subset",
  ``!(g:'a monoid) (h:'a monoid). submonoid h g ==> H SUBSET G``,
  rw_tac std_ss[submonoid_eqn]);

(* Theorem: submonoid h g /\ MonoidHomo f g k ==> MonoidHomo f h k *)
(* Proof:
   Note H SUBSET G              by submonoid_subset
     or !x. x IN H ==> x IN G   by SUBSET_DEF
   By MonoidHomo_def, this is to show:
   (1) x IN H ==> f x IN k.carrier
       True                     by MonoidHomo_def, MonoidHomo f g k
   (2) x IN H /\ y IN H /\ f (h.op x y) = k.op (f x) (f y)
       Note x IN H ==> x IN G   by above
        and y IN H ==> y IN G   by above
         f (h.op x y)
       = f (x * y)              by submonoid_eqn
       = k.op (f x) (f y)       by MonoidHomo_def
   (3) f h.id = k.id
         f (h.id)
       = f #e                   by submonoid_eqn
       = k.id                   by MonoidHomo_def
*)
val submonoid_homo_homo = store_thm(
  "submonoid_homo_homo",
  ``!(g:'a monoid) (h:'a monoid) (k:'b monoid) f. submonoid h g /\ MonoidHomo f g k ==> MonoidHomo f h k``,
  rw_tac std_ss[submonoid_def, MonoidHomo_def]);

(* Theorem: submonoid g g *)
(* Proof:
   By submonoid_def, this is to show:
   MonoidHomo I g g, true by monoid_homo_I_refl.
*)
val submonoid_refl = store_thm(
  "submonoid_refl",
  ``!g:'a monoid. submonoid g g``,
  rw[submonoid_def, monoid_homo_I_refl]);

(* Theorem: submonoid g h /\ submonoid h k ==> submonoid g k *)
(* Proof:
   By submonoid_def, this is to show:
   MonoidHomo I g h /\ MonoidHomo I h k ==> MonoidHomo I g k
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by monoid_homo_trans
*)
val submonoid_trans = store_thm(
  "submonoid_trans",
  ``!(g h k):'a monoid. submonoid g h /\ submonoid h k ==> submonoid g k``,
  prove_tac[submonoid_def, combinTheory.I_o_ID, monoid_homo_trans]);

(* Theorem: submonoid h g /\ submonoid g h ==> MonoidIso I h g *)
(* Proof:
   By submonoid_def, MonoidIso_def, this is to show:
      MonoidHomo I h g /\ MonoidHomo I g h ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by submonoid_subset, submonoid h g
   (2) x IN G ==> x IN H, true    by submonoid_subset, submonoid g h
*)
val submonoid_I_antisym = store_thm(
  "submonoid_I_antisym",
  ``!(g:'a monoid) h. submonoid h g /\ submonoid g h ==> MonoidIso I h g``,
  rw_tac std_ss[submonoid_def, MonoidIso_def] >>
  fs[MonoidHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: submonoid h g /\ G SUBSET H ==> MonoidIso I h g *)
(* Proof:
   By submonoid_def, MonoidIso_def, this is to show:
      MonoidHomo I h g /\ G SUBSET H ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by submonoid_subset, submonoid h g
   (2) x IN G ==> x IN H, true    by G SUBSET H, given
*)
val submonoid_carrier_antisym = store_thm(
  "submonoid_carrier_antisym",
  ``!(g:'a monoid) h. submonoid h g /\ G SUBSET H ==> MonoidIso I h g``,
  rpt (stripDup[submonoid_def]) >>
  rw_tac std_ss[MonoidIso_def] >>
  `H SUBSET G` by rw[submonoid_subset] >>
  fs[MonoidHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: Monoid g /\ Monoid h /\ submonoid h g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note MonoidHomo I h g          by submonoid_def
   If ord x = 0, to show: order h x = 0.
      By contradiction, suppose order h x <> 0.
      Let n = order h x.
      Then 0 < n                  by n <> 0
       and h.exp x n = h.id       by order_property
        or    x ** n = #e         by monoid_homo_exp, monoid_homo_id, I_THM
       But    x ** n <> #e        by order_eq_0, ord x = 0
      This is a contradiction.
   If ord x <> 0, to show: order h x = ord x.
      Note 0 < ord x              by ord x <> 0
      By order_thm, this is to show:
      (1) h.exp x (ord x) = h.id
            h.exp x (ord x)
          = I (h.exp x (ord x))   by I_THM
          = (I x) ** ord x        by monoid_homo_exp
          = x ** ord x            by I_THM
          = #e                    by order_property
          = I (h.id)              by monoid_homo_id
          = h.id                  by I_THM
      (2) 0 < m /\ m < ord x ==> h.exp x m <> h.id
          By contradiction, suppose h.exp x m = h.id
            h.exp x m
          = I (h.exp x m)         by I_THM
          = (I x) ** m            by monoid_homo_exp
          = x ** m                by I_THM
            h.id = I (h.id)       by I_THM
                 = #e             by monoid_homo_id
         Thus x ** m = #e         by h.exp x m = h.id
          But x ** m <> #e        by order_thm
          This is a contradiction.
*)
val submonoid_order_eqn = store_thm(
  "submonoid_order_eqn",
  ``!(g:'a monoid) h. Monoid g /\ Monoid h /\ submonoid h g ==>
   !x. x IN H ==> (order h x = ord x)``,
  rw[submonoid_def] >>
  `!x. I x = x` by rw[] >>
  Cases_on `ord x = 0` >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `n = order h x` >>
    `0 < n` by decide_tac >>
    `h.exp x n = h.id` by rw[order_property, Abbr`n`] >>
    `x ** n = #e` by metis_tac[monoid_homo_exp, monoid_homo_id] >>
    metis_tac[order_eq_0],
    `0 < ord x` by decide_tac >>
    rw[order_thm] >-
    metis_tac[monoid_homo_exp, order_property, monoid_homo_id] >>
    spose_not_then strip_assume_tac >>
    `x ** m = #e` by metis_tac[monoid_homo_exp, monoid_homo_id] >>
    metis_tac[order_thm]
  ]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of Monoid.                                              *)
(* ------------------------------------------------------------------------- *)

(* Define an operation on images *)
val image_op_def = Define`
   image_op (g:'a monoid) (f:'a -> 'b) x y =  f (CHOICE (preimage f G x) * CHOICE (preimage f G y))
`;

(* Theorem: INJ f G univ(:'b) ==> !x y. x IN G /\ y IN G ==> (image_op g f (f x) (f y) = f (x * y)) *)
(* Proof:
   Note x = CHOICE (preimage f G (f x))    by preimage_inj_choice
    and y = CHOICE (preimage f G (f y))    by preimage_inj_choice
     image_op g f (f x) (f y)
   = f (CHOICE (preimage f G (f x)) * CHOICE (preimage f G (f y))   by image_op_def
   = f (x * y)                             by above
*)
val image_op_inj = store_thm(
  "image_op_inj",
  ``!g:'a monoid f. INJ f G univ(:'b) ==>
    !x y. x IN G /\ y IN G ==> (image_op g f (f x) (f y) = f (g.op x y))``,
  rw[image_op_def, preimage_inj_choice]);

(* Define the homomorphic image of a monoid. *)
val homo_monoid_def = Define`
  homo_monoid (g:'a monoid) (f:'a -> 'b) =
    <| carrier := IMAGE f G;
            op := image_op g f;
            id := f #e
     |>
`;

(* set overloading *)
val _ = overload_on ("o", ``(homo_monoid (g:'a monoid) (f:'a -> 'b)).op``);
val _ = overload_on ("#i", ``(homo_monoid (g:'a monoid) (f:'a -> 'b)).id``);
val _ = overload_on ("fG", ``(homo_monoid (g:'a monoid) (f:'a -> 'b)).carrier``);

(* Theorem: Properties of homo_monoid. *)
(* Proof: by homo_monoid_def and image_op_def. *)
val homo_monoid_property = store_thm(
  "homo_monoid_property",
  ``!(g:'a monoid) (f:'a -> 'b). (fG = IMAGE f G) /\
      (!x y. x IN fG /\ y IN fG  ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))) /\
      (#i = f #e)``,
  rw[homo_monoid_def, image_op_def]);

(* Theorem: !x. x IN G ==> f x IN fG *)
(* Proof: by homo_monoid_def, IN_IMAGE *)
val homo_monoid_element = store_thm(
  "homo_monoid_element",
  ``!(g:'a monoid) (f:'a -> 'b). !x. x IN G ==> f x IN fG``,
  rw[homo_monoid_def]);

(* Theorem: f #e = #i *)
(* Proof: by homo_monoid_def *)
val homo_monoid_id = store_thm(
  "homo_monoid_id",
  ``!(g:'a monoid) (f:'a -> 'b). f #e = #i``,
  rw[homo_monoid_def]);

(* Theorem: INJ f G univ(:'b) ==>
            !x y. x IN G /\ y IN G  ==> (f (x * y) = (f x) o (f y)) *)
(* Proof:
   Note x = CHOICE (preimage f G (f x))    by preimage_inj_choice
    and y = CHOICE (preimage f G (f y))    by preimage_inj_choice
     f (x * y)
   = f (CHOICE (preimage f G (f x)) * CHOICE (preimage f G (f y))   by above
   = (f x) o (f y)                         by homo_monoid_property
*)
val homo_monoid_op_inj = store_thm(
  "homo_monoid_op_inj",
  ``!(g:'a monoid) (f:'a -> 'b). INJ f G univ(:'b) ==>
   !x y. x IN G /\ y IN G  ==> (f (x * y) = (f x) o (f y))``,
  rw[homo_monoid_property, preimage_inj_choice]);

(* Theorem: MonoidIso I (homo_monoid g I) g *)
(* Proof:
   Note IMAGE I G = G         by IMAGE_I
    and INJ I G univ(:'a)     by INJ_I
    and !x. I x = x           by I_THM
   By MonoidIso_def, this is to show:
   (1) MonoidHomo I (homo_monoid g I) g
       By MonoidHomo_def, homo_monoid_def, this is to show:
          x IN G /\ y IN G ==> image_op g I x y = x * y
       This is true           by image_op_inj
   (2) BIJ I (homo_group g I).carrier G
         (homo_group g I).carrier
       = IMAGE I G            by homo_monoid_property
       = G                    by above, IMAGE_I
       This is true           by BIJ_I_SAME
*)
val homo_monoid_I = store_thm(
  "homo_monoid_I",
  ``!g:'a monoid. MonoidIso I (homo_monoid g I) g``,
  rpt strip_tac >>
  `IMAGE I G = G` by rw[] >>
  `INJ I G univ(:'a)` by rw[INJ_I] >>
  `!x. I x = x` by rw[] >>
  rw_tac std_ss[MonoidIso_def] >| [
    rw_tac std_ss[MonoidHomo_def, homo_monoid_def] >>
    metis_tac[image_op_inj],
    rw[homo_monoid_property, BIJ_I_SAME]
  ]);

(* Theorem: [Closure] Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> x IN fG /\ y IN fG ==> x o y IN fG *)
(* Proof:
   Let a = CHOICE (preimage f G x),
       b = CHOICE (preimage f G y).
   Then a IN G /\ x = f a      by preimage_choice_property
        b IN G /\ y = f b      by preimage_choice_property
        x o y
      = (f a) o (f b)
      = f (a * b)              by homo_monoid_property
   Note a * b IN G             by monoid_op_element
   so   f (a * b) IN fG        by homo_monoid_element
*)
val homo_monoid_closure = store_thm(
  "homo_monoid_closure",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
     !x y. x IN fG /\ y IN fG ==> x o y IN fG``,
  rw_tac std_ss[homo_monoid_property] >>
  rw[preimage_choice_property]);

(* Theorem: [Associative] Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
            x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = x o (y o z) *)
(* Proof:
   By MonoidHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Let a = CHOICE (preimage f G x),
       b = CHOICE (preimage f G y),
       c = CHOICE (preimage f G z).
   Then a IN G /\ x = f a      by preimage_choice_property
        b IN G /\ y = f b      by preimage_choice_property
        c IN G /\ z = f c      by preimage_choice_property
     (x o y) o z
   = ((f a) o (f b)) o (f c)   by expanding x, y, z
   = f (a * b) o (f c)         by homo_monoid_property
   = f (a * b * c)             by homo_monoid_property
   = f (a * (b * c))           by monoid_assoc
   = (f a) o f (b * c)         by homo_monoid_property
   = (f a) o ((f b) o (f c))   by homo_monoid_property
   = x o (y o z)               by contracting x, y, z
*)
val homo_monoid_assoc = store_thm(
  "homo_monoid_assoc",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
   !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[MonoidHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  qabbrev_tac `a = CHOICE (preimage f G x)` >>
  qabbrev_tac `b = CHOICE (preimage f G y)` >>
  qabbrev_tac `c = CHOICE (preimage f G z)` >>
  `a IN G /\ (f a = x)` by metis_tac[preimage_choice_property] >>
  `b IN G /\ (f b = y)` by metis_tac[preimage_choice_property] >>
  `c IN G /\ (f c = z)` by metis_tac[preimage_choice_property] >>
  `a * b IN G /\ b * c IN G ` by rw[] >>
  `a * b * c = a * (b * c)` by rw[monoid_assoc] >>
  metis_tac[]);

(* Theorem: [Identity] Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> #i IN fG /\ #i o x = x /\ x o #i = x. *)
(* Proof:
   By homo_monoid_property, #i = f #e, and #i IN fG.
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   hence  #i o x
        = (f #e) o f (preimage f G x)
        = f (#e * preimage f G x)       by homo_monoid_property
        = f (preimage f G x)            by monoid_lid
        = x
   similarly for x o #i = x             by monoid_rid
*)
val homo_monoid_id_property = store_thm(
  "homo_monoid_id_property",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
      #i IN fG /\ (!x. x IN fG ==> (#i o x = x) /\ (x o #i = x))``,
  rw[MonoidHomo_def, homo_monoid_property] >-
  metis_tac[monoid_lid, monoid_id_element, preimage_choice_property] >>
  metis_tac[monoid_rid, monoid_id_element, preimage_choice_property]);

(* Theorem: [Commutative] AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
            x IN fG /\ y IN fG ==> (x o y = y o x) *)
(* Proof:
   Note AbelianMonoid g ==> Monoid g and
        !x y. x IN G /\ y IN G ==> (x * y = y * x)          by AbelianMonoid_def
   By MonoidHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Let a = CHOICE (preimage f G x),
       b = CHOICE (preimage f G y).
   Then a IN G /\ x = f a     by preimage_choice_property
        b IN G /\ y = f b     by preimage_choice_property
     x o y
   = (f a) o (f b)            by expanding x, y
   = f (a * b)                by homo_monoid_property
   = f (b * a)                by AbelianMonoid_def, above
   = (f b) o (f a)            by homo_monoid_property
   = y o x                    by contracting x, y
*)
val homo_monoid_comm = store_thm(
  "homo_monoid_comm",
  ``!(g:'a monoid) (f:'a -> 'b). AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
   !x y. x IN fG /\ y IN fG ==> (x o y = y o x)``,
  rw_tac std_ss[AbelianMonoid_def, MonoidHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  qabbrev_tac `a = CHOICE (preimage f G x)` >>
  qabbrev_tac `b = CHOICE (preimage f G y)` >>
  `a IN G /\ (f a = x)` by metis_tac[preimage_choice_property] >>
  `b IN G /\ (f b = y)` by metis_tac[preimage_choice_property] >>
  `a * b = b * a` by rw[] >>
  metis_tac[]);

(* Theorem: Homomorphic image of a monoid is a monoid.
            Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> Monoid (homo_monoid g f) *)
(* Proof:
   This is to show each of these:
   (1) x IN fG /\ y IN fG ==> x o y IN fG    true by homo_monoid_closure
   (2) x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = (x o y) o z    true by homo_monoid_assoc
   (3) #i IN fG, true by homo_monoid_id_property
   (4) x IN fG ==> #i o x = x, true by homo_monoid_id_property
   (5) x IN fG ==> x o #i = x, true by homo_monoid_id_property
*)
val homo_monoid_monoid = store_thm(
  "homo_monoid_monoid",
  ``!(g:'a monoid) f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> Monoid (homo_monoid g f)``,
  rpt strip_tac >>
  rw_tac std_ss[Monoid_def] >| [
    rw[homo_monoid_closure],
    rw[homo_monoid_assoc],
    rw[homo_monoid_id_property],
    rw[homo_monoid_id_property],
    rw[homo_monoid_id_property]
  ]);

(* Theorem: Homomorphic image of an Abelian monoid is an Abelian monoid.
            AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==> AbelianMonoid (homo_monoid g f) *)
(* Proof:
   Note AbelianMonoid g ==> Monoid g               by AbelianMonoid_def
   By AbelianMonoid_def, this is to show:
   (1) Monoid (homo_monoid g f), true               by homo_monoid_monoid, Monoid g
   (2) x IN fG /\ y IN fG ==> x o y = y o x, true   by homo_monoid_comm, AbelianMonoid g
*)
val homo_monoid_abelian_monoid = store_thm(
  "homo_monoid_abelian_monoid",
  ``!(g:'a monoid) f. AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==> AbelianMonoid (homo_monoid g f)``,
  metis_tac[homo_monoid_monoid, AbelianMonoid_def, homo_monoid_comm]);

(* Theorem: Monoid g /\ INJ f G UNIV ==> MonoidHomo f g (homo_monoid g f) *)
(* Proof:
   By MonoidHomo_def, homo_monoid_property, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true                 by IN_IMAGE
   (2) x IN G /\ y IN G ==> f (x * y) = f x o f y, true  by homo_monoid_op_inj
*)
val homo_monoid_by_inj = store_thm(
  "homo_monoid_by_inj",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ INJ f G UNIV ==> MonoidHomo f g (homo_monoid g f)``,
  rw_tac std_ss[MonoidHomo_def, homo_monoid_property] >-
  rw[] >>
  rw[homo_monoid_op_inj]);

(* ------------------------------------------------------------------------- *)
(* Weaker form of Homomorphic of Monoid and image of identity.               *)
(* ------------------------------------------------------------------------- *)

(* Let us take out the image of identity requirement *)
val WeakHomo_def = Define`
  WeakHomo (f:'a -> 'b) (g:'a monoid) (h:'b monoid) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)))
    (* no requirement for: f #e = h.id *)
`;

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val WeakIso_def = Define`
  WeakIso f g h <=> WeakHomo f g h /\ BIJ f G h.carrier
`;

(* Then the best we can prove about monoid identities is the following:
            Monoid g /\ Monoid h /\ WeakIso f g h ==> f #e = h.id
   which is NOT:
            Monoid g /\ Monoid h /\ WeakHomo f g h ==> f #e = h.id
*)

(* Theorem: Monoid g /\ Monoid h /\ WeakIso f g h ==> f #e = h.id *)
(* Proof:
   By monoid_id_unique:
   |- !g. Monoid g ==> !e. e IN G ==> ((!x. x IN G ==> (x * e = x) /\ (e * x = x)) <=> (e = #e)) : thm
   Hence this is to show: !x. x IN h.carrier ==> (h.op x (f #e) = x) /\ (h.op (f #e) x = x)
   Note that WeakIso f g h = WeakHomo f g h /\ BIJ f G h.carrier.
   (1) x IN h.carrier /\ f #e IN h.carrier ==> h.op x (f #e) = x
       Since  x = f y     for some y IN G, by BIJ_THM
       h.op x (f #e) = h.op (f y) (f #e)
                     = f (y * #e)     by WeakHomo_def
                     = f y = x        by monoid_rid
   (2) x IN h.carrier /\ f #e IN h.carrier ==> h.op (f #e) x = x
       Similar to above,
       h.op (f #e) x = h.op (f #e) (f y) = f (#e * y) = f y = x  by monoid_lid.
*)
val monoid_weak_iso_id = store_thm(
  "monoid_weak_iso_id",
  ``!f g h. Monoid g /\ Monoid h /\ WeakIso f g h ==> (f #e = h.id)``,
  rw_tac std_ss[WeakIso_def] >>
  `#e IN G /\ f #e IN h.carrier` by metis_tac[WeakHomo_def, monoid_id_element] >>
  `!x. x IN h.carrier ==> (h.op x (f #e) = x) /\ (h.op (f #e) x = x)` suffices_by rw_tac std_ss[monoid_id_unique] >>
  rpt strip_tac>| [
    `?y. y IN G /\ (f y = x)` by metis_tac[BIJ_THM] >>
    metis_tac[WeakHomo_def, monoid_rid],
    `?y. y IN G /\ (f y = x)` by metis_tac[BIJ_THM] >>
    metis_tac[WeakHomo_def, monoid_lid]
  ]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Monoid.                                                *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Monoid g, and an injective function f,
   then the image (f G) is a Monoid, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Define a monoid injective image for an injective f, with LINV f G. *)
Definition monoid_inj_image_def:
   monoid_inj_image (g:'a monoid) (f:'a -> 'b) =
     <|carrier := IMAGE f G;
            op := let t = LINV f G in (\x y. f (t x * t y));
            id := f #e
      |>
End

(* Theorem: Monoid g /\ INJ f G univ(:'b) ==> Monoid (monoid_inj_image g f) *)
(* Proof:
   Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)      by INJ_IMAGE_BIJ_ALT
     so !x. x IN G ==> t (f x) = x                     where t = LINV f G
    and !x. x IN (IMAGE f G) ==> f (t x) = x           by BIJ_LINV_THM
   By Monoid_def, monoid_inj_image_def, this is to show:
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> f (t x * t y) IN IMAGE f G
       Note ?a. (x = f a) /\ a IN G                    by IN_IMAGE
            ?b. (y = f b) /\ b IN G                    by IN_IMAGE
       Hence  f (t x * t y)
            = f (t (f a) * t (f b))                    by x = f a, y = f b
            = f (a * b)                                by !y. t (f y) = y
       Since a * b IN G                                by monoid_op_element
       f (a * b) IN IMAGE f G                          by IN_IMAGE
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> f (t (f (t x * t y)) * t z) = f (t x * t (f (t y * t z)))
       Note ?a. (x = f a) /\ a IN G                    by IN_IMAGE
            ?b. (y = f b) /\ b IN G                    by IN_IMAGE
            ?c. (z = f c) /\ c IN G                    by IN_IMAGE
       LHS = f (t (f (t x * t y)) * t z))
           = f (t (f (t (f a) * t (f b))) * t (f c))   by x = f a, y = f b, z = f c
           = f (t (f (a * b)) * c)                     by !y. t (f y) = y
           = f ((a * b) * c)                           by !y. t (f y) = y, monoid_op_element
       RHS = f (t x * t (f (t y * t z)))
           = f (t (f a) * t (f (t (f b) * t (f c))))   by x = f a, y = f b, z = f c
           = f (a * t (f (b * c)))                     by !y. t (f y) = y
           = f (a * (b * c))                           by !y. t (f y) = y
           = LHS                                       by monoid_assoc
   (3) f #e IN IMAGE f G
       Since #e IN G                                   by monoid_id_element
          so f #e IN IMAGE f G                         by IN_IMAGE
   (4) x IN IMAGE f G ==> f (t (f #e) * t x) = x
       Note ?a. (x = f a) /\ a IN G                    by IN_IMAGE
        and #e IN G                                    by monoid_id_element
       Hence f (t (f #e) * t x)
           = f (#e * t x)                              by !y. t (f y) = y
           = f (#e * t (f a))                          by x = f a
           = f (#e * a)                                by !y. t (f y) = y
           = f a                                       by monoid_id
           = x                                         by x = f a
   (5) x IN IMAGE f G ==> f (t x * t (f #e)) = x
       Note ?a. (x = f a) /\ a IN G                    by IN_IMAGE
       and #e IN G                                     by monoid_id_element
       Hence f (t x * t (f #e))
           = f (t x * #e)                              by !y. t (f y) = y
           = f (t (f a) * #e)                          by x = f a
           = f (a * #e)                                by !y. t (f y) = y
           = f a                                       by monoid_id
           = x                                         by x = f a
*)
Theorem monoid_inj_image_monoid:
  !(g:'a monoid) (f:'a -> 'b). Monoid g /\ INJ f G univ(:'b) ==> Monoid (monoid_inj_image g f)
Proof
  rpt strip_tac >>
  `BIJ f G (IMAGE f G)` by rw[INJ_IMAGE_BIJ_ALT] >>
  `(!x. x IN G ==> (LINV f G (f x) = x)) /\ (!x. x IN (IMAGE f G) ==> (f (LINV f G x) = x))` by metis_tac[BIJ_LINV_THM] >>
  rw_tac std_ss[Monoid_def, monoid_inj_image_def] >| [
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN G` by rw[GSYM IN_IMAGE] >>
    rw[],
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN G` by rw[GSYM IN_IMAGE] >>
    `?c. (z = f c) /\ c IN G` by rw[GSYM IN_IMAGE] >>
    rw[monoid_assoc],
    rw[],
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    rw[],
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    rw[]
  ]
QED

(* Theorem: AbelianMonoid g /\ INJ f G univ(:'b) ==> AbelianMonoid (monoid_inj_image g f) *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Monoid g ==> Monoid (monoid_inj_image g f)
       True by monoid_inj_image_monoid.
   (2) x IN G /\ y IN G ==> (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       By monoid_inj_image_def, this is to show:
          f (t (f x) * t (f y)) = f (t (f y) * t (f x))    where t = LINV f G
       Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)      by INJ_IMAGE_BIJ_ALT
         so !x. x IN G ==> t (f x) = x
        and !x. x IN (IMAGE f G) ==> f (t x) = x           by BIJ_LINV_THM
         f (t (f x) * t (f y))
       = f (x * y)                                         by !y. t (f y) = y
       = f (y * x)                                         by commutativity condition
       = f (t (f y) * t (f x))                             by !y. t (f y) = y
*)
Theorem monoid_inj_image_abelian_monoid:
  !(g:'a monoid) (f:'a -> 'b). AbelianMonoid g /\ INJ f G univ(:'b) ==>
       AbelianMonoid (monoid_inj_image g f)
Proof
  rw[AbelianMonoid_def] >-
  rw[monoid_inj_image_monoid] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[monoid_inj_image_def] >>
  metis_tac[INJ_IMAGE_BIJ_ALT, BIJ_LINV_THM]
QED

(* Theorem: INJ f G univ(:'b) ==> MonoidHomo f g (monoid_inj_image g f) *)
(* Proof:
   Let s = IMAGE f G.
   Then BIJ f G s                              by INJ_IMAGE_BIJ_ALT
     so INJ f G s                              by BIJ_DEF

   By MonoidHomo_def, monoid_inj_image_def, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x * y) = f (LINV f R (f x) * LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem monoid_inj_image_monoid_homo:
  !(g:'a monoid) f. INJ f G univ(:'b) ==> MonoidHomo f g (monoid_inj_image g f)
Proof
  rw[MonoidHomo_def, monoid_inj_image_def] >>
  qabbrev_tac `s = IMAGE f G` >>
  `BIJ f G s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f G s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* ------------------------------------------------------------------------- *)
(* Submonoid Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# are temporary):
#  K          = k.carrier
#  x o y      = h.op x y
#  #i         = h.id
   h << g     = Submonoid h g
   h mINTER k = monoid_intersect h k
   smbINTER g = submonoid_big_intersect g
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Submonoid of a Monoid:
   Submonoid_def            |- !h g. h << g <=>
                                     Monoid h /\ Monoid g /\ H SUBSET G /\ ($o = $* ) /\ (#i = #e)
   submonoid_property       |- !g h. h << g ==>
                                     Monoid h /\ Monoid g /\ H SUBSET G /\
                                     (!x y. x IN H /\ y IN H ==> (x o y = x * y)) /\ (#i = #e)
   submonoid_carrier_subset |- !g h. h << g ==> H SUBSET G
#  submonoid_element        |- !g h. h << g ==> !x. x IN H ==> x IN G
#  submonoid_id             |- !g h. h << g ==> (#i = #e)
   submonoid_exp            |- !g h. h << g ==> !x. x IN H ==> !n. h.exp x n = x ** n
   submonoid_homomorphism   |- !g h. h << g ==> Monoid h /\ Monoid g /\ submonoid h g
   submonoid_order          |- !g h. h << g ==> !x. x IN H ==> (order h x = ord x)
   submonoid_alt            |- !g. Monoid g ==> !h. h << g <=> H SUBSET G /\
                                   (!x y. x IN H /\ y IN H ==> h.op x y IN H) /\
                                   h.id IN H /\ (h.op = $* ) /\ (h.id = #e)

   Submonoid Theorems:
   submonoid_reflexive      |- !g. Monoid g ==> g << g
   submonoid_antisymmetric  |- !g h. h << g /\ g << h ==> (h = g)
   submonoid_transitive     |- !g h k. k << h /\ h << g ==> k << g
   submonoid_monoid         |- !g h. h << g ==> Monoid h

   Submonoid Intersection:
   monoid_intersect_def          |- !g h. g mINTER h = <|carrier := G INTER H; op := $*; id := #e|>
   monoid_intersect_property     |- !g h. ((g mINTER h).carrier = G INTER H) /\
                                          ((g mINTER h).op = $* ) /\ ((g mINTER h).id = #e)
   monoid_intersect_element      |- !g h x. x IN (g mINTER h).carrier ==> x IN G /\ x IN H
   monoid_intersect_id           |- !g h. (g mINTER h).id = #e

   submonoid_intersect_property  |- !g h k. h << g /\ k << g ==>
                                    ((h mINTER k).carrier = H INTER K) /\
                                    (!x y. x IN H INTER K /\ y IN H INTER K ==>
                                          ((h mINTER k).op x y = x * y)) /\ ((h mINTER k).id = #e)
   submonoid_intersect_monoid    |- !g h k. h << g /\ k << g ==> Monoid (h mINTER k)
   submonoid_intersect_submonoid |- !g h k. h << g /\ k << g ==> (h mINTER k) << g

   Submonoid Big Intersection:
   submonoid_big_intersect_def      |- !g. smbINTER g =
                  <|carrier := BIGINTER (IMAGE (\h. H) {h | h << g}); op := $*; id := #e|>
   submonoid_big_intersect_property |- !g.
         ((smbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h << g})) /\
         (!x y. x IN (smbINTER g).carrier /\ y IN (smbINTER g).carrier ==> ((smbINTER g).op x y = x * y)) /\
         ((smbINTER g).id = #e)
   submonoid_big_intersect_element   |- !g x. x IN (smbINTER g).carrier <=> !h. h << g ==> x IN H
   submonoid_big_intersect_op_element   |- !g x y. x IN (smbINTER g).carrier /\
                                                   y IN (smbINTER g).carrier ==>
                                                   (smbINTER g).op x y IN (smbINTER g).carrier
   submonoid_big_intersect_has_id    |- !g. (smbINTER g).id IN (smbINTER g).carrier
   submonoid_big_intersect_subset    |- !g. Monoid g ==> (smbINTER g).carrier SUBSET G
   submonoid_big_intersect_monoid    |- !g. Monoid g ==> Monoid (smbINTER g)
   submonoid_big_intersect_submonoid |- !g. Monoid g ==> smbINTER g << g
*)

(* ------------------------------------------------------------------------- *)
(* Submonoid of a Monoid                                                     *)
(* ------------------------------------------------------------------------- *)

(* Use K to denote k.carrier *)
val _ = temp_overload_on ("K", ``(k:'a monoid).carrier``);

(* Use o to denote h.op *)
val _ = temp_overload_on ("o", ``(h:'a monoid).op``);

(* Use #i to denote h.id *)
val _ = temp_overload_on ("#i", ``(h:'a monoid).id``);

(* A Submonoid is a subset of a monoid that's a monoid itself, keeping op, id. *)
val Submonoid_def = Define`
  Submonoid (h:'a monoid) (g:'a monoid) <=>
    Monoid h /\ Monoid g /\
    H SUBSET G /\ ($o = $* ) /\ (#i = #e)
`;

(* Overload Submonoid *)
val _ = overload_on ("<<", ``Submonoid``);
val _ = set_fixity "<<" (Infix(NONASSOC, 450)); (* same as relation *)

(* Note: The requirement $o = $* is stronger than the following:
val _ = overload_on ("<<", ``\(h g):'a monoid. Monoid g /\ Monoid h /\ submonoid h g``);
Since submonoid h g is based on MonoidHomo I g h, which only gives
!x y. x IN H /\ y IN H ==> (h.op x y = x * y))

This is not enough to satisfy monoid_component_equality,
hence cannot prove: h << g /\ g << h ==> h = g
*)

(*
val submonoid_property = save_thm(
  "submonoid_property",
  Submonoid_def
      |> SPEC_ALL
      |> REWRITE_RULE [ASSUME ``h:'a monoid << g``]
      |> CONJUNCTS
      |> (fn thl => List.take(thl, 2) @ List.drop(thl, 3))
      |> LIST_CONJ
      |> DISCH_ALL
      |> Q.GEN `h` |> Q.GEN `g`);
val submonoid_property = |- !g h. h << g ==> Monoid h /\ Monoid g /\ ($o = $* )  /\ (#i = #e)
*)

(* Theorem: properties of submonoid *)
(* Proof: Assume h << g, then derive all consequences of definition. *)
val submonoid_property = store_thm(
  "submonoid_property",
  ``!(g:'a monoid) h. h << g ==> Monoid h /\ Monoid g /\ H SUBSET G /\
      (!x y. x IN H /\ y IN H ==> (x o y = x * y)) /\ (#i = #e)``,
  rw_tac std_ss[Submonoid_def]);

(* Theorem: h << g ==> H SUBSET G *)
(* Proof: by Submonoid_def *)
val submonoid_carrier_subset = store_thm(
  "submonoid_carrier_subset",
  ``!(g:'a monoid) h. Submonoid h g ==> H SUBSET G``,
  rw[Submonoid_def]);

(* Theorem: elements in submonoid are also in monoid. *)
(* Proof: Since h << g ==> H SUBSET G by Submonoid_def. *)
val submonoid_element = store_thm(
  "submonoid_element",
  ``!(g:'a monoid) h. h << g ==> !x. x IN H ==> x IN G``,
  rw_tac std_ss[Submonoid_def, SUBSET_DEF]);

(* export simple result *)
val _ = export_rewrites ["submonoid_element"];

(* Theorem: h << g ==> (h.op = $* ) *)
(* Proof: by Subgroup_def *)
val submonoid_op = store_thm(
  "submonoid_op",
  ``!(g:'a monoid) h. h << g ==> (h.op = g.op)``,
  rw[Submonoid_def]);

(* Theorem: h << g ==> #i = #e *)
(* Proof: by Submonoid_def. *)
val submonoid_id = store_thm(
  "submonoid_id",
  ``!(g:'a monoid) h. h << g ==> (#i = #e)``,
  rw_tac std_ss[Submonoid_def]);

(* export simple results *)
val _ = export_rewrites["submonoid_id"];

(* Theorem: h << g ==> !x. x IN H ==> !n. h.exp x n = x ** n *)
(* Proof: by induction on n.
   Base: h.exp x 0 = x ** 0
      LHS = h.exp x 0
          = h.id            by monoid_exp_0
          = #e              by submonoid_id
          = x ** 0          by monoid_exp_0
          = RHS
   Step: h.exp x n = x ** n ==> h.exp x (SUC n) = x ** SUC n
     LHS = h.exp x (SUC n)
         = h.op x (h.exp x n)    by monoid_exp_SUC
         = x * (h.exp x n)       by submonoid_property
         = x * x ** n            by induction hypothesis
         = x ** SUC n            by monoid_exp_SUC
         = RHS
*)
val submonoid_exp = store_thm(
  "submonoid_exp",
  ``!(g:'a monoid) h. h << g ==> !x. x IN H ==> !n. h.exp x n = x ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `h.exp x (SUC n) = h.op x (h.exp x n)` by rw_tac std_ss[monoid_exp_SUC] >>
  `_ = x * (h.exp x n)` by metis_tac[submonoid_property, monoid_exp_element] >>
  `_ = x * (x ** n)` by rw[] >>
  `_ = x ** (SUC n)` by rw_tac std_ss[monoid_exp_SUC] >>
  rw[]);

(* Theorem: A submonoid h of g implies identity is a homomorphism from h to g.
        or  h << g ==> Monoid h /\ Monoid g /\ submonoid h g  *)
(* Proof:
   h << g ==> Monoid h /\ Monoid g                  by Submonoid_def
   together with
       H SUBSET G /\ ($o = $* ) /\ (#i = #e)        by Submonoid_def
   ==> !x. x IN H ==> x IN G /\
       !x y. x IN H /\ y IN H ==> (x o y = x * y) /\
       #i = #e                                      by SUBSET_DEF
   ==> MonoidHomo I h g                             by MonoidHomo_def, f = I.
   ==> submonoid h g                                by submonoid_def
*)
val submonoid_homomorphism = store_thm(
  "submonoid_homomorphism",
  ``!(g:'a monoid) h. h << g ==> Monoid h /\ Monoid g /\ submonoid h g``,
  rw_tac std_ss[Submonoid_def, submonoid_def, MonoidHomo_def, SUBSET_DEF]);

(* original:
g `!(g:'a monoid) h. h << g = Monoid h /\ Monoid g /\ submonoid h g`;
e (rw_tac std_ss[Submonoid_def, submonoid_def, MonoidHomo_def, SUBSET_DEF, EQ_IMP_THM]);

The only-if part (<==) cannot be proved:
Note Submonoid_def uses h.op = g.op,
but submonoid_def uses homomorphism I, and so cannot show this for any x y.
*)

(* Theorem: h << g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h /\ submonoid h g   by submonoid_homomorphism, h << g
   Thus !x. x IN H ==> (order h x = ord x)      by submonoid_order_eqn
*)
val submonoid_order = store_thm(
  "submonoid_order",
  ``!(g:'a monoid) h. h << g ==> !x. x IN H ==> (order h x = ord x)``,
  metis_tac[submonoid_homomorphism, submonoid_order_eqn]);

(* Theorem: Monoid g ==> !h. Submonoid h g <=>
            H SUBSET G /\ (!x y. x IN H /\ y IN H ==> h.op x y IN H) /\ (h.id IN H) /\ (h.op = $* ) /\ (h.id = #e) *)
(* Proof:
   By Submonoid_def, EQ_IMP_THM, this is to show:
   (1) x IN H /\ y IN H ==> x * y IN H, true    by monoid_op_element
   (2) #e IN H, true                            by monoid_id_element
   (3) Monoid h
       By Monoid_def, this is to show:
       (1) x IN H /\ y IN H /\ z IN H
           ==> x * y * z = x * (y * z), true    by monoid_assoc, SUBSET_DEF
       (2) x IN H ==> #e * x = x, true          by monoid_lid, SUBSET_DEF
       (3) x IN H ==> x * #e = x, true          by monoid_rid, SUBSET_DEF
*)
val submonoid_alt = store_thm(
  "submonoid_alt",
  ``!g:'a monoid. Monoid g ==> !h. Submonoid h g <=>
    H SUBSET G /\ (* subset *)
    (!x y. x IN H /\ y IN H ==> h.op x y IN H) /\ (* closure *)
    (h.id IN H) /\ (* has identity *)
    (h.op = g.op ) /\ (h.id = #e)``,
  rw_tac std_ss[Submonoid_def, EQ_IMP_THM] >-
  metis_tac[monoid_op_element] >-
  metis_tac[monoid_id_element] >>
  rw_tac std_ss[Monoid_def] >-
  fs[monoid_assoc, SUBSET_DEF] >-
  fs[monoid_lid, SUBSET_DEF] >>
  fs[monoid_rid, SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Submonoid Theorems                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Monoid g ==> g << g *)
(* Proof: by Submonoid_def, SUBSET_REFL *)
val submonoid_reflexive = store_thm(
  "submonoid_reflexive",
  ``!g:'a monoid. Monoid g ==> g << g``,
  rw_tac std_ss[Submonoid_def, SUBSET_REFL]);

val monoid_component_equality = DB.fetch "-" "monoid_component_equality";

(* Theorem: h << g /\ g << h ==> (h = g) *)
(* Proof:
   Since h << g ==> Monoid h /\ Monoid g /\ H SUBSET G /\ ($o = $* ) /\ (#i = #e)   by Submonoid_def
     and g << h ==> Monoid g /\ Monoid h /\ G SUBSET H /\ ($* = $o) /\ (#e = #i)    by Submonoid_def
   Now, H SUBSET G /\ G SUBSET H ==> H = G       by SUBSET_ANTISYM
   Hence h = g                                   by monoid_component_equality
*)
val submonoid_antisymmetric = store_thm(
  "submonoid_antisymmetric",
  ``!g h:'a monoid. h << g /\ g << h ==> (h = g)``,
  rw_tac std_ss[Submonoid_def] >>
  full_simp_tac bool_ss[monoid_component_equality, SUBSET_ANTISYM]);

(* Theorem: k << h /\ h << g ==> k << g *)
(* Proof: by Submonoid_def and SUBSET_TRANS *)
val submonoid_transitive = store_thm(
  "submonoid_transitive",
  ``!g h k:'a monoid. k << h /\ h << g ==> k << g``,
  rw_tac std_ss[Submonoid_def] >>
  metis_tac[SUBSET_TRANS]);

(* Theorem: h << g ==> Monoid h *)
(* Proof: by Submonoid_def. *)
val submonoid_monoid = store_thm(
  "submonoid_monoid",
  ``!g h:'a monoid. h << g ==> Monoid h``,
  rw[Submonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Submonoid Intersection                                                    *)
(* ------------------------------------------------------------------------- *)

(* Define intersection of monoids *)
val monoid_intersect_def = Define`
   monoid_intersect (g:'a monoid) (h:'a monoid) =
      <| carrier := G INTER H;
              op := $*; (* g.op *)
              id := #e  (* g.id *)
       |>
`;

val _ = overload_on ("mINTER", ``monoid_intersect``);
val _ = set_fixity "mINTER" (Infix(NONASSOC, 450)); (* same as relation *)
(*
> monoid_intersect_def;
val it = |- !g h. g mINTER h = <|carrier := G INTER H; op := $*; id := #e|>: thm
*)

(* Theorem: ((g mINTER h).carrier = G INTER H) /\
            ((g mINTER h).op = $* ) /\ ((g mINTER h).id = #e) *)
(* Proof: by monoid_intersect_def *)
val monoid_intersect_property = store_thm(
  "monoid_intersect_property",
  ``!g h:'a monoid. ((g mINTER h).carrier = G INTER H) /\
                   ((g mINTER h).op = $* ) /\ ((g mINTER h).id = #e)``,
  rw[monoid_intersect_def]);

(* Theorem: !x. x IN (g mINTER h).carrier ==> x IN G /\ x IN H *)
(* Proof:
         x IN (g mINTER h).carrier
     ==> x IN G INTER H                     by monoid_intersect_def
     ==> x IN G and x IN H                  by IN_INTER
*)
val monoid_intersect_element = store_thm(
  "monoid_intersect_element",
  ``!g h:'a monoid. !x. x IN (g mINTER h).carrier ==> x IN G /\ x IN H``,
  rw[monoid_intersect_def, IN_INTER]);

(* Theorem: (g mINTER h).id = #e *)
(* Proof: by monoid_intersect_def. *)
val monoid_intersect_id = store_thm(
  "monoid_intersect_id",
  ``!g h:'a monoid. (g mINTER h).id = #e``,
  rw[monoid_intersect_def]);

(* Theorem: h << g /\ k << g ==>
    ((h mINTER k).carrier = H INTER K) /\
    (!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)) /\
    ((h mINTER k).id = #e) *)
(* Proof:
   (h mINTER k).carrier = H INTER K          by monoid_intersect_def
   Hence x IN (h mINTER k).carrier ==> x IN H /\ x IN K   by IN_INTER
     and y IN (h mINTER k).carrier ==> y IN H /\ y IN K   by IN_INTER
      so (h mINTER k).op x y = x o y         by monoid_intersect_def
                             = x * y         by submonoid_property
     and (h mINTER k).id = #i                by monoid_intersect_def
                         = #e                by submonoid_property
*)
val submonoid_intersect_property = store_thm(
  "submonoid_intersect_property",
  ``!g h k:'a monoid. h << g /\ k << g ==>
    ((h mINTER k).carrier = H INTER K) /\
    (!x y. x IN H INTER K /\ y IN H INTER K ==> ((h mINTER k).op x y = x * y)) /\
    ((h mINTER k).id = #e)``,
  rw[monoid_intersect_def, submonoid_property]);

(* Theorem: h << g /\ k << g ==> Monoid (h mINTER k) *)
(* Proof:
   By definitions, this is to show:
   (1) x IN H INTER K /\ y IN H INTER K ==> x o y IN H INTER K
       x IN H INTER K ==> x IN H /\ x IN K      by IN_INTER
       y IN H INTER K ==> y IN H /\ y IN K      by IN_INTER
       x IN H /\ y IN H ==> x o y IN H          by monoid_op_element
       x IN K /\ y IN K ==> k.op x y IN K       by monoid_op_element
       x o y = x * y                            by submonoid_property
       k.op x y = x * y                         by submonoid_property
       Hence x o y IN H INTER K                 by IN_INTER
   (2) x IN H INTER K /\ y IN H INTER K /\ z IN H INTER K ==> (x o y) o z = x o y o z
       x IN H INTER K ==> x IN H                by IN_INTER
       y IN H INTER K ==> y IN H                by IN_INTER
       z IN H INTER K ==> z IN H                by IN_INTER
       x IN H /\ y IN H ==> x o y IN H          by monoid_op_element
       y IN H /\ z IN H ==> y o z IN H          by monoid_op_element
       x, y, z IN H ==> x, y, z IN G            by submonoid_element
       LHS = (x o y) o z
           = (x o y) * z                        by submonoid_property
           = (x * y) * z                        by submonoid_property
           = x * (y * z)                        by monoid_assoc
           = x * (y o z)                        by submonoid_property
           = x o (y o z) = RHS                  by submonoid_property
   (3) #i IN H INTER K
       #i IN H and #i = #e                      by monoid_id_element, submonoid_id
       k.id IN K and k.id = #e                  by monoid_id_element, submonoid_id
       Hence #e = #i IN H INTER K               by IN_INTER
   (4) x IN H INTER K ==> #i o x = x
       x IN H INTER K ==> x IN H                by IN_INTER
                      ==> x IN G                by submonoid_element
       #i IN H and #i = #e                      by monoid_id_element, submonoid_id
         #i o x
       = #i * x                                 by submonoid_property
       = #e * x                                 by submonoid_id
       = x                                      by monoid_id
   (5) x IN H INTER K ==> x o #i = x
       x IN H INTER K ==> x IN H                by IN_INTER
                      ==> x IN G                by submonoid_element
       #i IN H and #i = #e                      by monoid_id_element, submonoid_id
         x o #i
       = x * #i                                 by submonoid_property
       = x * #e                                 by submonoid_id
       = x                                      by monoid_id
*)
val submonoid_intersect_monoid = store_thm(
  "submonoid_intersect_monoid",
  ``!g h k:'a monoid. h << g /\ k << g ==> Monoid (h mINTER k)``,
  rpt strip_tac >>
  `Monoid h /\ Monoid k /\ Monoid g` by metis_tac[submonoid_property] >>
  rw_tac std_ss[Monoid_def, monoid_intersect_def] >| [
    `x IN H /\ x IN K /\ y IN H /\ y IN K` by metis_tac[IN_INTER] >>
    `x o y IN H /\ (x o y = x * y)` by metis_tac[submonoid_property, monoid_op_element] >>
    `k.op x y IN K /\ (k.op x y = x * y)` by metis_tac[submonoid_property, monoid_op_element] >>
    metis_tac[IN_INTER],
    `x IN H /\ y IN H /\ z IN H` by metis_tac[IN_INTER] >>
    `x IN G /\ y IN G /\ z IN G` by metis_tac[submonoid_element] >>
    `x o y IN H /\ y o z IN H` by metis_tac[monoid_op_element] >>
    `(x o y) o z = (x * y) * z` by metis_tac[submonoid_property] >>
    `x o (y o z) = x * (y * z)` by metis_tac[submonoid_property] >>
    rw[monoid_assoc],
    metis_tac[IN_INTER, submonoid_id, monoid_id_element],
    metis_tac[submonoid_property, monoid_id, submonoid_element, IN_INTER, monoid_id_element],
    metis_tac[submonoid_property, monoid_id, submonoid_element, IN_INTER, monoid_id_element]
  ]);

(* Theorem: h << g /\ k << g ==> (h mINTER k) << g *)
(* Proof:
   By Submonoid_def, this is to show:
   (1) Monoid (h mINTER k), true by submonoid_intersect_monoid
   (2) (h mINTER k).carrier SUBSET G
       Since (h mINTER k).carrier = H INTER K    by submonoid_intersect_property
         and (H INTER K) SUBSET H                by INTER_SUBSET
         and h << g ==> H SUBSET G               by submonoid_property
       Hence (h mINTER k).carrier SUBSET G       by SUBSET_TRANS
   (3) (h mINTER k).op = $*
       (h mINTER k).op = $o                      by monoid_intersect_def
                       = $*                      by Submonoid_def
   (4) (h mINTER k).id = #e
       (h mINTER k).id = #i                      by monoid_intersect_def
                       = #e                      by Submonoid_def
*)
val submonoid_intersect_submonoid = store_thm(
  "submonoid_intersect_submonoid",
  ``!g h k:'a monoid. h << g /\ k << g ==> (h mINTER k) << g``,
  rpt strip_tac >>
  `Monoid h /\ Monoid k /\ Monoid g` by metis_tac[submonoid_property] >>
  rw[Submonoid_def] >| [
    metis_tac[submonoid_intersect_monoid],
    `(h mINTER k).carrier = H INTER K` by metis_tac[submonoid_intersect_property] >>
    `H SUBSET G` by rw[submonoid_property] >>
    metis_tac[INTER_SUBSET, SUBSET_TRANS],
    `(h mINTER k).op = $o` by rw[monoid_intersect_def] >>
    metis_tac[Submonoid_def],
    `(h mINTER k).id = #i` by rw[monoid_intersect_def] >>
    metis_tac[Submonoid_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Submonoid Big Intersection                                                *)
(* ------------------------------------------------------------------------- *)

(* Define intersection of submonoids of a monoid *)
val submonoid_big_intersect_def = Define`
   submonoid_big_intersect (g:'a monoid) =
      <| carrier := BIGINTER (IMAGE (\h. H) {h | h << g});
              op := $*; (* g.op *)
              id := #e  (* g.id *)
       |>
`;

val _ = overload_on ("smbINTER", ``submonoid_big_intersect``);
(*
> submonoid_big_intersect_def;
val it = |- !g. smbINTER g =
     <|carrier := BIGINTER (IMAGE (\h. H) {h | h << g}); op := $*; id := #e|>: thm
*)

(* Theorem: ((smbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h << g})) /\
   (!x y. x IN (smbINTER g).carrier /\ y IN (smbINTER g).carrier ==> ((smbINTER g).op x y = x * y)) /\
   ((smbINTER g).id = #e) *)
(* Proof: by submonoid_big_intersect_def. *)
val submonoid_big_intersect_property = store_thm(
  "submonoid_big_intersect_property",
  ``!g:'a monoid. ((smbINTER g).carrier = BIGINTER (IMAGE (\h. H) {h | h << g})) /\
   (!x y. x IN (smbINTER g).carrier /\ y IN (smbINTER g).carrier ==> ((smbINTER g).op x y = x * y)) /\
   ((smbINTER g).id = #e)``,
  rw[submonoid_big_intersect_def]);

(* Theorem: x IN (smbINTER g).carrier <=> (!h. h << g ==> x IN H) *)
(* Proof:
       x IN (smbINTER g).carrier
   <=> x IN BIGINTER (IMAGE (\h. H) {h | h << g})          by submonoid_big_intersect_def
   <=> !P. P IN (IMAGE (\h. H) {h | h << g}) ==> x IN P    by IN_BIGINTER
   <=> !P. ?h. (P = H) /\ h IN {h | h << g}) ==> x IN P    by IN_IMAGE
   <=> !P. ?h. (P = H) /\ h << g) ==> x IN P               by GSPECIFICATION
   <=> !h. h << g ==> x IN H
*)
val submonoid_big_intersect_element = store_thm(
  "submonoid_big_intersect_element",
  ``!g:'a monoid. !x. x IN (smbINTER g).carrier <=> (!h. h << g ==> x IN H)``,
  rw[submonoid_big_intersect_def] >>
  metis_tac[]);

(* Theorem: x IN (smbINTER g).carrier /\ y IN (smbINTER g).carrier ==> (smbINTER g).op x y IN (smbINTER g).carrier *)
(* Proof:
   Since x IN (smbINTER g).carrier, !h. h << g ==> x IN H   by submonoid_big_intersect_element
    also y IN (smbINTER g).carrier, !h. h << g ==> y IN H   by submonoid_big_intersect_element
     Now !h. h << g ==> x o y IN H                          by Submonoid_def, monoid_op_element
                    ==> x * y IN H                          by submonoid_property
     Now, (smbINTER g).op x y = x * y                       by submonoid_big_intersect_property
     Hence (smbINTER g).op x y IN (smbINTER g).carrier      by submonoid_big_intersect_element
*)
val submonoid_big_intersect_op_element = store_thm(
  "submonoid_big_intersect_op_element",
  ``!g:'a monoid. !x y. x IN (smbINTER g).carrier /\ y IN (smbINTER g).carrier ==>
                     (smbINTER g).op x y IN (smbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h << g ==> x IN H /\ y IN H` by metis_tac[submonoid_big_intersect_element] >>
  `!h. h << g ==> x * y IN H` by metis_tac[Submonoid_def, monoid_op_element, submonoid_property] >>
  `(smbINTER g).op x y = x * y` by rw[submonoid_big_intersect_property] >>
  metis_tac[submonoid_big_intersect_element]);

(* Theorem: (smbINTER g).id IN (smbINTER g).carrier *)
(* Proof:
   !h. h << g ==> #i = #e                             by submonoid_id
   !h. h << g ==> #i IN H                             by Submonoid_def, monoid_id_element
   Now (smbINTER g).id = #e                           by submonoid_big_intersect_property
   Hence !h. h << g ==> (smbINTER g).id IN H          by above
    or (smbINTER g).id IN (smbINTER g).carrier        by submonoid_big_intersect_element
*)
val submonoid_big_intersect_has_id = store_thm(
  "submonoid_big_intersect_has_id",
  ``!g:'a monoid. (smbINTER g).id IN (smbINTER g).carrier``,
  rpt strip_tac >>
  `!h. h << g ==> (#i = #e)` by rw[submonoid_id] >>
  `!h. h << g ==> #i IN H` by rw[Submonoid_def] >>
  `(smbINTER g).id = #e` by metis_tac[submonoid_big_intersect_property] >>
  metis_tac[submonoid_big_intersect_element]);

(* Theorem: Monoid g ==> (smbINTER g).carrier SUBSET G *)
(* Proof:
   By submonoid_big_intersect_def, this is to show:
   Monoid g ==> BIGINTER (IMAGE (\h. H) {h | h << g}) SUBSET G
   Let P = IMAGE (\h. H) {h | h << g}.
   Since g << g                    by submonoid_reflexive
      so G IN P                    by IN_IMAGE, definition of P.
    Thus P <> {}                   by MEMBER_NOT_EMPTY.
     Now h << g ==> H SUBSET G     by submonoid_property
   Hence P SUBSET G                by BIGINTER_SUBSET
*)
val submonoid_big_intersect_subset = store_thm(
  "submonoid_big_intersect_subset",
  ``!g:'a monoid. Monoid g ==> (smbINTER g).carrier SUBSET G``,
  rw[submonoid_big_intersect_def] >>
  qabbrev_tac `P = IMAGE (\h. H) {h | h << g}` >>
  (`!x. x IN P <=> ?h. (H = x) /\ h << g` by (rw[Abbr`P`] >> metis_tac[])) >>
  `g << g` by rw[submonoid_reflexive] >>
  `P <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `!h:'a monoid. h << g ==> H SUBSET G` by rw[submonoid_property] >>
  metis_tac[BIGINTER_SUBSET]);

(* Theorem: Monoid g ==> Monoid (smbINTER g) *)
(* Proof:
   Monoid g ==> (smbINTER g).carrier SUBSET G               by submonoid_big_intersect_subset
   By Monoid_def, this is to show:
   (1) x IN (smbINTER g).carrier /\ y IN (smbINTER g).carrier ==> (smbINTER g).op x y IN (smbINTER g).carrier
       True by submonoid_big_intersect_op_element.
   (2) (smbINTER g).op ((smbINTER g).op x y) z = (smbINTER g).op x ((smbINTER g).op y z)
       Since (smbINTER g).op x y IN (smbINTER g).carrier    by submonoid_big_intersect_op_element
         and (smbINTER g).op y z IN (smbINTER g).carrier    by submonoid_big_intersect_op_element
       So this is to show: (x * y) * z = x * (y * z)        by submonoid_big_intersect_property
       Since x IN G, y IN G and z IN G                      by SUBSET_DEF
       This follows by monoid_assoc.
   (3) (smbINTER g).id IN (smbINTER g).carrier
       This is true by submonoid_big_intersect_has_id.
   (4) x IN (smbINTER g).carrier ==> (smbINTER g).op (smbINTER g).id x = x
       Since (smbINTER g).id IN (smbINTER g).carrier   by submonoid_big_intersect_op_element
         and (smbINTER g).id = #e                      by submonoid_big_intersect_property
        also x IN G                                    by SUBSET_DEF
         (smbINTER g).op (smbINTER g).id x
       = #e * x                                        by submonoid_big_intersect_property
       = x                                             by monoid_id
   (5) x IN (smbINTER g).carrier ==> (smbINTER g).op x (smbINTER g).id = x
       Since (smbINTER g).id IN (smbINTER g).carrier   by submonoid_big_intersect_op_element
         and (smbINTER g).id = #e                      by submonoid_big_intersect_property
        also x IN G                                    by SUBSET_DEF
         (smbINTER g).op x (smbINTER g).id
       = x * #e                                        by submonoid_big_intersect_property
       = x                                             by monoid_id
*)
val submonoid_big_intersect_monoid = store_thm(
  "submonoid_big_intersect_monoid",
  ``!g:'a monoid. Monoid g ==> Monoid (smbINTER g)``,
  rpt strip_tac >>
  `(smbINTER g).carrier SUBSET G` by rw[submonoid_big_intersect_subset] >>
  rw_tac std_ss[Monoid_def] >| [
    metis_tac[submonoid_big_intersect_op_element],
    `(smbINTER g).op x y IN (smbINTER g).carrier` by metis_tac[submonoid_big_intersect_op_element] >>
    `(smbINTER g).op y z IN (smbINTER g).carrier` by metis_tac[submonoid_big_intersect_op_element] >>
    `(x * y) * z = x * (y * z)` suffices_by rw[submonoid_big_intersect_property] >>
    `x IN G /\ y IN G /\ z IN G` by metis_tac[SUBSET_DEF] >>
    rw[monoid_assoc],
    metis_tac[submonoid_big_intersect_has_id],
    `(smbINTER g).id = #e` by rw[submonoid_big_intersect_property] >>
    `(smbINTER g).id IN (smbINTER g).carrier` by metis_tac[submonoid_big_intersect_has_id] >>
    `#e * x = x` suffices_by rw[submonoid_big_intersect_property] >>
    `x IN G` by metis_tac[SUBSET_DEF] >>
    rw[],
    `(smbINTER g).id = #e` by rw[submonoid_big_intersect_property] >>
    `(smbINTER g).id IN (smbINTER g).carrier` by metis_tac[submonoid_big_intersect_has_id] >>
    `x * #e = x` suffices_by rw[submonoid_big_intersect_property] >>
    `x IN G` by metis_tac[SUBSET_DEF] >>
    rw[]
  ]);

(* Theorem: Monoid g ==> (smbINTER g) << g *)
(* Proof:
   By Submonoid_def, this is to show:
   (1) Monoid (smbINTER g)
       True by submonoid_big_intersect_monoid.
   (2) (smbINTER g).carrier SUBSET G
       True by submonoid_big_intersect_subset.
   (3) (smbINTER g).op = $*
       True by submonoid_big_intersect_def
   (4) (smbINTER g).id = #e
       True by submonoid_big_intersect_def
*)
val submonoid_big_intersect_submonoid = store_thm(
  "submonoid_big_intersect_submonoid",
  ``!g:'a monoid. Monoid g ==> (smbINTER g) << g``,
  rw_tac std_ss[Submonoid_def] >| [
    rw[submonoid_big_intersect_monoid],
    rw[submonoid_big_intersect_subset],
    rw[submonoid_big_intersect_def],
    rw[submonoid_big_intersect_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Monoid Instances Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Monoid Data type:
   The generic symbol for monoid data is g.
   g.carrier = Carrier set of monoid
   g.op      = Binary operation of monoid
   g.id      = Identity element of monoid
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   The trivial monoid:
   trivial_monoid_def |- !e. trivial_monoid e = <|carrier := {e}; id := e; op := (\x y. e)|>
   trivial_monoid     |- !e. FiniteAbelianMonoid (trivial_monoid e)

   The monoid of addition modulo n:
   plus_mod_def                     |- !n. plus_mod n =
                                           <|carrier := count n;
                                                  id := 0;
                                                  op := (\i j. (i + j) MOD n)|>
   plus_mod_property                |- !n. ((plus_mod n).carrier = count n) /\
                                           ((plus_mod n).op = (\i j. (i + j) MOD n)) /\
                                           ((plus_mod n).id = 0) /\
                                           (!x. x IN (plus_mod n).carrier ==> x < n) /\
                                           FINITE (plus_mod n).carrier /\
                                           (CARD (plus_mod n).carrier = n)
   plus_mod_exp                     |- !n. 0 < n ==> !x k. (plus_mod n).exp x k = (k * x) MOD n
   plus_mod_monoid                  |- !n. 0 < n ==> Monoid (plus_mod n)
   plus_mod_abelian_monoid          |- !n. 0 < n ==> AbelianMonoid (plus_mod n)
   plus_mod_finite                  |- !n. FINITE (plus_mod n).carrier
   plus_mod_finite_monoid           |- !n. 0 < n ==> FiniteMonoid (plus_mod n)
   plus_mod_finite_abelian_monoid   |- !n. 0 < n ==> FiniteAbelianMonoid (plus_mod n)

   The monoid of multiplication modulo n:
   times_mod_def                    |- !n. times_mod n =
                                           <|carrier := count n;
                                                  id := if n = 1 then 0 else 1;
                                                  op := (\i j. (i * j) MOD n)|>
!  times_mod_eval                   |- !n. ((times_mod n).carrier = count n) /\
                                           (!x y. (times_mod n).op x y = (x * y) MOD n) /\
                                           ((times_mod n).id = if n = 1 then 0 else 1)
   times_mod_property               |- !n. ((times_mod n).carrier = count n) /\
                                           ((times_mod n).op = (\i j. (i * j) MOD n)) /\
                                           ((times_mod n).id = if n = 1 then 0 else 1) /\
                                           (!x. x IN (times_mod n).carrier ==> x < n) /\
                                           FINITE (times_mod n).carrier /\
                                           (CARD (times_mod n).carrier = n)
   times_mod_exp                    |- !n. 0 < n ==> !x k. (times_mod n).exp x k = (x MOD n) ** k MOD n
   times_mod_monoid                 |- !n. 0 < n ==> Monoid (times_mod n)
   times_mod_abelian_monoid         |- !n. 0 < n ==> AbelianMonoid (times_mod n)
   times_mod_finite                 |- !n. FINITE (times_mod n).carrier
   times_mod_finite_monoid          |- !n. 0 < n ==> FiniteMonoid (times_mod n)
   times_mod_finite_abelian_monoid  |- !n. 0 < n ==> FiniteAbelianMonoid (times_mod n)

   The Monoid of List concatenation:
   lists_def     |- lists = <|carrier := univ(:'a list); id := []; op := $++ |>
   lists_monoid  |- Monoid lists

   The Monoids from Set:
   set_inter_def             |- set_inter = <|carrier := univ(:'a -> bool); id := univ(:'a); op := $INTER|>
   set_inter_monoid          |- Monoid set_inter
   set_inter_abelian_monoid  |- AbelianMonoid set_inter
   set_union_def             |- set_union = <|carrier := univ(:'a -> bool); id := {}; op := $UNION|>
   set_union_monoid          |- Monoid set_union
   set_union_abelian_monoid  |- AbelianMonoid set_union

   Addition of numbers form a Monoid:
   addition_monoid_def       |- addition_monoid = <|carrier := univ(:num); op := $+; id := 0|>
   addition_monoid_property  |- (addition_monoid.carrier = univ(:num)) /\
                                  (addition_monoid.op = $+) /\ (addition_monoid.id = 0)
   addition_monoid_abelian_monoid  |- AbelianMonoid addition_monoid
   addition_monoid_monoid          |- Monoid addition_monoid

   Multiplication of numbers form a Monoid:
   multiplication_monoid_def       |- multiplication_monoid = <|carrier := univ(:num); op := $*; id := 1|>
   multiplication_monoid_property  |- (multiplication_monoid.carrier = univ(:num)) /\
                                      (multiplication_monoid.op = $* ) /\ (multiplication_monoid.id = 1)
   multiplication_monoid_abelian_monoid   |- AbelianMonoid multiplication_monoid
   multiplication_monoid_monoid           |- Monoid multiplication_monoid

   Powers of a fixed base form a Monoid:
   power_monoid_def            |- !b. power_monoid b =
                                      <|carrier := {b ** j | j IN univ(:num)}; op := $*; id := 1|>
   power_monoid_property       |- !b. ((power_monoid b).carrier = {b ** j | j IN univ(:num)}) /\
                                      ((power_monoid b).op = $* ) /\ ((power_monoid b).id = 1)
   power_monoid_abelian_monoid |- !b. AbelianMonoid (power_monoid b)
   power_monoid_monoid         |- !b. Monoid (power_monoid b)

   Logarithm is an isomorphism:
   power_to_addition_homo  |- !b. 1 < b ==> MonoidHomo (LOG b) (power_monoid b) addition_monoid
   power_to_addition_iso   |- !b. 1 < b ==> MonoidIso (LOG b) (power_monoid b) addition_monoid


*)
(* ------------------------------------------------------------------------- *)
(* The trivial monoid.                                                       *)
(* ------------------------------------------------------------------------- *)

(* The trivial monoid: {#e} *)
val trivial_monoid_def = Define`
  trivial_monoid e :'a monoid =
   <| carrier := {e};
           id := e;
           op := (\x y. e)
    |>
`;

(*
- type_of ``trivial_monoid e``;
> val it = ``:'a monoid`` : hol_type
> EVAL ``(trivial_monoid T).id``;
val it = |- (trivial_monoid T).id <=> T: thm
> EVAL ``(trivial_monoid 8).id``;
val it = |- (trivial_monoid 8).id = 8: thm
*)

(* Theorem: {e} is indeed a monoid *)
(* Proof: check by definition. *)
val trivial_monoid = store_thm(
  "trivial_monoid",
  ``!e. FiniteAbelianMonoid (trivial_monoid e)``,
  rw_tac std_ss[FiniteAbelianMonoid_def, AbelianMonoid_def, Monoid_def, trivial_monoid_def, IN_SING, FINITE_SING]);

(* ------------------------------------------------------------------------- *)
(* The monoid of addition modulo n.                                          *)
(* ------------------------------------------------------------------------- *)

(* Additive Modulo Monoid *)
val plus_mod_def = Define`
  plus_mod n :num monoid =
   <| carrier := count n;
           id := 0;
           op := (\i j. (i + j) MOD n)
    |>
`;
(* This monoid should be upgraded to add_mod, the additive group of ZN ring later. *)

(*
- type_of ``plus_mod n``;
> val it = ``:num monoid`` : hol_type
> EVAL ``(plus_mod 7).op 5 6``;
val it = |- (plus_mod 7).op 5 6 = 4: thm
*)

(* Theorem: properties of (plus_mod n) *)
(* Proof: by plus_mod_def. *)
val plus_mod_property = store_thm(
  "plus_mod_property",
  ``!n. ((plus_mod n).carrier = count n) /\
       ((plus_mod n).op = (\i j. (i + j) MOD n)) /\
       ((plus_mod n).id = 0) /\
       (!x. x IN (plus_mod n).carrier ==> x < n) /\
       (FINITE (plus_mod n).carrier) /\
       (CARD (plus_mod n).carrier = n)``,
  rw[plus_mod_def]);

(* Theorem: 0 < n ==> !x k. (plus_mod n).exp x k = (k * x) MOD n *)
(* Proof:
   Expanding by definitions, this is to show:
   FUNPOW (\j. (x + j) MOD n) k 0 = (k * x) MOD n
   Applyy induction on k.
   Base case: FUNPOW (\j. (x + j) MOD n) 0 0 = (0 * x) MOD n
   LHS = FUNPOW (\j. (x + j) MOD n) 0 0
       = 0                                by FUNPOW_0
       = 0 MOD n                          by ZERO_MOD, 0 < n
       = (0 * x) MOD n                    by MULT
       = RHS
   Step case: FUNPOW (\j. (x + j) MOD n) (SUC k) 0 = (SUC k * x) MOD n
   LHS = FUNPOW (\j. (x + j) MOD n) (SUC k) 0
       = (x + FUNPOW (\j. (x + j) MOD n) k 0) MOD n    by FUNPOW_SUC
       = (x + (k * x) MOD n) MOD n                     by induction hypothesis
       = (x MOD n + (k * x) MOD n) MOD n               by MOD_PLUS, MOD_MOD
       = (x + k * x) MOD n                             by MOD_PLUS, MOD_MOD
       = (k * x + x) MOD n                by ADD_COMM
       = ((SUC k) * x) MOD n              by MULT
       = RHS
*)
val plus_mod_exp = store_thm(
  "plus_mod_exp",
  ``!n. 0 < n ==> !x k. (plus_mod n).exp x k = (k * x) MOD n``,
  rw_tac std_ss[plus_mod_def, monoid_exp_def] >>
  Induct_on `k` >-
  rw[] >>
  rw_tac std_ss[FUNPOW_SUC] >>
  metis_tac[MULT, ADD_COMM, MOD_PLUS, MOD_MOD]);

(* Theorem: Additive Modulo n is a monoid. *)
(* Proof: check group definitions, use MOD_ADD_ASSOC.
*)
val plus_mod_monoid = store_thm(
  "plus_mod_monoid",
  ``!n. 0 < n ==> Monoid (plus_mod n)``,
  rw_tac std_ss[plus_mod_def, Monoid_def, count_def, GSPECIFICATION, MOD_ADD_ASSOC]);

(* Theorem: Additive Modulo n is an Abelian monoid. *)
(* Proof: by plus_mod_monoid and ADD_COMM. *)
val plus_mod_abelian_monoid = store_thm(
  "plus_mod_abelian_monoid",
  ``!n. 0 < n ==> AbelianMonoid (plus_mod n)``,
  rw[plus_mod_monoid, plus_mod_def, AbelianMonoid_def, ADD_COMM]);

(* Theorem: Additive Modulo n carrier is FINITE. *)
(* Proof: by FINITE_COUNT. *)
val plus_mod_finite = store_thm(
  "plus_mod_finite",
  ``!n. FINITE (plus_mod n).carrier``,
  rw[plus_mod_def]);

(* Theorem: Additive Modulo n is a FINITE monoid. *)
(* Proof: by plus_mod_monoid and plus_mod_finite. *)
val plus_mod_finite_monoid = store_thm(
  "plus_mod_finite_monoid",
  ``!n. 0 < n ==> FiniteMonoid (plus_mod n)``,
  rw[FiniteMonoid_def, plus_mod_monoid, plus_mod_finite]);

(* Theorem: Additive Modulo n is a FINITE Abelian monoid. *)
(* Proof: by plus_mod_abelian_monoid and plus_mod_finite. *)
val plus_mod_finite_abelian_monoid = store_thm(
  "plus_mod_finite_abelian_monoid",
  ``!n. 0 < n ==> FiniteAbelianMonoid (plus_mod n)``,
  rw[FiniteAbelianMonoid_def, plus_mod_abelian_monoid, plus_mod_finite]);

(* ------------------------------------------------------------------------- *)
(* The monoid of multiplication modulo n.                                    *)
(* ------------------------------------------------------------------------- *)

(* Multiplicative Modulo Monoid *)
val times_mod_def = zDefine`
  times_mod n :num monoid =
   <| carrier := count n;
           id := if n = 1 then 0 else 1;
           op := (\i j. (i * j) MOD n)
    |>
`;
(* This monoid is taken as the multiplicative monoid of ZN ring later. *)
(* Use of zDefine to avoid incorporating into computeLib, by default. *)
(* Evaluation is given later in times_mod_eval. *)

(*
- type_of ``times_mod n``;
> val it = ``:num monoid`` : hol_type
> EVAL ``(times_mod 7).op 5 6``;
val it = |- (times_mod 7).op 5 6 = 2: thm
*)

(* Theorem: times_mod evaluation. *)
(* Proof: by times_mod_def. *)
val times_mod_eval = store_thm(
  "times_mod_eval[compute]",
  ``!n. ((times_mod n).carrier = count n) /\
       (!x y. (times_mod n).op x y = (x * y) MOD n) /\
       ((times_mod n).id = if n = 1 then 0 else 1)``,
  rw_tac std_ss[times_mod_def]);

(* Theorem: properties of (times_mod n) *)
(* Proof: by times_mod_def. *)
val times_mod_property = store_thm(
  "times_mod_property",
  ``!n. ((times_mod n).carrier = count n) /\
       ((times_mod n).op = (\i j. (i * j) MOD n)) /\
       ((times_mod n).id = if n = 1 then 0 else 1) /\
       (!x. x IN (times_mod n).carrier ==> x < n) /\
       (FINITE (times_mod n).carrier) /\
       (CARD (times_mod n).carrier = n)``,
  rw[times_mod_def]);

(* Theorem: 0 < n ==> !x k. (times_mod n).exp x k = ((x MOD n) ** k) MOD n *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) n = 1 ==> FUNPOW (\j. (x * j) MOD n) k 0 = (x MOD n) ** k MOD n
       or to show: FUNPOW (\j. 0) k 0 = 0       by MOD_1
       Note (\j. 0) = K 0                       by FUN_EQ_THM
        and FUNPOW (K 0) k 0 = 0                by FUNPOW_K
   (2) n <> 1 ==> FUNPOW (\j. (x * j) MOD n) k 1 = (x MOD n) ** k MOD n
       Note 1 < n                               by 0 < n /\ n <> 1
       By induction on k.
       Base: FUNPOW (\j. (x * j) MOD n) 0 1 = (x MOD n) ** 0 MOD n
             FUNPOW (\j. (x * j) MOD n) 0 1
           = 1                                  by FUNPOW_0
           = 1 MOD n                            by ONE_MOD, 1 < n
           = ((x MOD n) ** 0) MOD n             by EXP
       Step: FUNPOW (\j. (x * j) MOD n) (SUC k) 1 = (x MOD n) ** SUC k MOD n
             FUNPOW (\j. (x * j) MOD n) (SUC k) 1
           = (x * FUNPOW (\j. (x * j) MOD n) k 1) MOD n    by FUNPOW_SUC
           = (x * (x MOD n) ** k MOD n) MOD n              by induction hypothesis
           = ((x MOD n) * (x MOD n) ** k MOD n) MOD n      by MOD_TIMES2, MOD_MOD, 0 < n
           = ((x MOD n) * (x MOD n) ** k) MOD n            by MOD_TIMES2, MOD_MOD, 0 < n
           = ((x MOD n) ** SUC k) MOD n                    by EXP
*)
val times_mod_exp = store_thm(
  "times_mod_exp",
  ``!n. 0 < n ==> !x k. (times_mod n).exp x k = ((x MOD n) ** k) MOD n``,
  rw_tac std_ss[times_mod_def, monoid_exp_def] >| [
    `(\j. 0) = K 0` by rw[FUN_EQ_THM] >>
    metis_tac[FUNPOW_K],
    `1 < n` by decide_tac >>
    Induct_on `k` >-
    rw[EXP, ONE_MOD] >>
    `FUNPOW (\j. (x * j) MOD n) (SUC k) 1 = (x * FUNPOW (\j. (x * j) MOD n) k 1) MOD n` by rw_tac std_ss[FUNPOW_SUC] >>
    metis_tac[EXP, MOD_TIMES2, MOD_MOD]
  ]);

(* Theorem: For n > 0, Multiplication Modulo n is a monoid. *)
(* Proof: check monoid definitions, use MOD_MULT_ASSOC. *)
Theorem times_mod_monoid:
  !n. 0 < n ==> Monoid (times_mod n)
Proof
  rw_tac std_ss[Monoid_def, times_mod_def, count_def, GSPECIFICATION] >| [
    rw[MOD_MULT_ASSOC],
    decide_tac
  ]
QED

(* Theorem: For n > 0, Multiplication Modulo n is an Abelian monoid. *)
(* Proof: by times_mod_monoid and MULT_COMM. *)
val times_mod_abelian_monoid = store_thm(
  "times_mod_abelian_monoid",
  ``!n. 0 < n ==> AbelianMonoid (times_mod n)``,
  rw[AbelianMonoid_def, times_mod_monoid, times_mod_def, MULT_COMM]);

(* Theorem: Multiplication Modulo n carrier is FINITE. *)
(* Proof: by FINITE_COUNT. *)
val times_mod_finite = store_thm(
  "times_mod_finite",
  ``!n. FINITE (times_mod n).carrier``,
  rw[times_mod_def]);

(* Theorem: For n > 0, Multiplication Modulo n is a FINITE monoid. *)
(* Proof: by times_mod_monoid and times_mod_finite. *)
val times_mod_finite_monoid = store_thm(
  "times_mod_finite_monoid",
  ``!n. 0 < n ==> FiniteMonoid (times_mod n)``,
  rw[times_mod_monoid, times_mod_finite, FiniteMonoid_def]);

(* Theorem: For n > 0, Multiplication Modulo n is a FINITE Abelian monoid. *)
(* Proof: by times_mod_abelian_monoid and times_mod_finite. *)
val times_mod_finite_abelian_monoid = store_thm(
  "times_mod_finite_abelian_monoid",
  ``!n. 0 < n ==> FiniteAbelianMonoid (times_mod n)``,
  rw[times_mod_abelian_monoid, times_mod_finite, FiniteAbelianMonoid_def, AbelianMonoid_def]);

(*

- EVAL ``(plus_mod 5).op 3 4``;
> val it = |- (plus_mod 5).op 3 4 = 2 : thm
- EVAL ``(plus_mod 5).id``;
> val it = |- (plus_mod 5).id = 0 : thm
- EVAL ``(times_mod 5).op 2 3``;
> val it = |- (times_mod 5).op 2 3 = 1 : thm
- EVAL ``(times_mod 5).op 5 3``;
> val it = |- (times_mod 5).id = 1 : thm
*)

(* ------------------------------------------------------------------------- *)
(* The Monoid of List concatenation.                                         *)
(* ------------------------------------------------------------------------- *)

val lists_def = Define`
  lists :'a list monoid =
   <| carrier := UNIV;
           id := [];
           op := list$APPEND
    |>
`;

(*
> EVAL ``lists.op [1;2;3] [4;5]``;
val it = |- lists.op [1; 2; 3] [4; 5] = [1; 2; 3; 4; 5]: thm
*)

(* Theorem: Lists form a Monoid *)
(* Proof: check definition. *)
val lists_monoid = store_thm(
  "lists_monoid",
  ``Monoid lists``,
  rw_tac std_ss[Monoid_def, lists_def, IN_UNIV, GSPECIFICATION, APPEND, APPEND_NIL, APPEND_ASSOC]);

(* after a long while ...

val lists_monoid = store_thm(
  "lists_monoid",
  ``Monoid lists``,
  rw[Monoid_def, lists_def]);
*)

(* ------------------------------------------------------------------------- *)
(* The Monoids from Set.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The Monoid of set intersection *)
val set_inter_def = Define`
  set_inter = <| carrier := UNIV;
                      id := UNIV;
                      op := (INTER) |>
`;

(*
> EVAL ``set_inter.op {1;4;5;6} {5;6;8;9}``;
val it = |- set_inter.op {1; 4; 5; 6} {5; 6; 8; 9} = {5; 6}: thm
*)

(* Theorem: set_inter is a Monoid. *)
(* Proof: check definitions. *)
val set_inter_monoid = store_thm(
  "set_inter_monoid",
  ``Monoid set_inter``,
  rw[Monoid_def, set_inter_def, INTER_ASSOC]);

val _ = export_rewrites ["set_inter_monoid"];

(* Theorem: set_inter is an abelian Monoid. *)
(* Proof: check definitions. *)
val set_inter_abelian_monoid = store_thm(
  "set_inter_abelian_monoid",
  ``AbelianMonoid set_inter``,
  rw[AbelianMonoid_def, set_inter_def, INTER_COMM]);

val _ = export_rewrites ["set_inter_abelian_monoid"];

(* The Monoid of set union *)
val set_union_def = Define`
  set_union = <| carrier := UNIV;
                      id := EMPTY;
                      op := (UNION) |>
`;

(*
> EVAL ``set_union.op {1;4;5;6} {5;6;8;9}``;
val it = |- set_union.op {1; 4; 5; 6} {5; 6; 8; 9} = {1; 4; 5; 6; 8; 9}: thm
*)

(* Theorem: set_union is a Monoid. *)
(* Proof: check definitions. *)
val set_union_monoid = store_thm(
  "set_union_monoid",
  ``Monoid set_union``,
  rw[Monoid_def, set_union_def, UNION_ASSOC]);

val _ = export_rewrites ["set_union_monoid"];

(* Theorem: set_union is an abelian Monoid. *)
(* Proof: check definitions. *)
val set_union_abelian_monoid = store_thm(
  "set_union_abelian_monoid",
  ``AbelianMonoid set_union``,
  rw[AbelianMonoid_def, set_union_def, UNION_COMM]);

val _ = export_rewrites ["set_union_abelian_monoid"];

(* ------------------------------------------------------------------------- *)
(* Addition of numbers form a Monoid                                         *)
(* ------------------------------------------------------------------------- *)

(* Define the number addition monoid *)
val addition_monoid_def = Define`
    addition_monoid =
       <| carrier := univ(:num);
          op := $+;
          id := 0;
        |>
`;

(*
> EVAL ``addition_monoid.op 5 6``;
val it = |- addition_monoid.op 5 6 = 11: thm
*)

(* Theorem: properties of addition_monoid *)
(* Proof: by addition_monoid_def *)
val addition_monoid_property = store_thm(
  "addition_monoid_property",
  ``(addition_monoid.carrier = univ(:num)) /\
   (addition_monoid.op = $+ ) /\
   (addition_monoid.id = 0)``,
  rw[addition_monoid_def]);

(* Theorem: AbelianMonoid (addition_monoid) *)
(* Proof:
   By AbelianMonoid_def, Monoid_def, addition_monoid_def, this is to show:
   (1) ?z. z = x + y. Take z = x + y.
   (2) x + y + z = x + (y + z), true    by ADD_ASSOC
   (3) x + 0 = x /\ 0 + x = x, true     by ADD, ADD_0
   (4) x + y = y + x, true              by ADD_COMM
*)
val addition_monoid_abelian_monoid = store_thm(
  "addition_monoid_abelian_monoid",
  ``AbelianMonoid (addition_monoid)``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, addition_monoid_def, GSPECIFICATION, IN_UNIV] >>
  simp[]);

(* Theorem: Monoid (addition_monoid) *)
(* Proof: by addition_monoid_abelian_monoid, AbelianMonoid_def *)
val addition_monoid_monoid = store_thm(
  "addition_monoid_monoid",
  ``Monoid (addition_monoid)``,
  metis_tac[addition_monoid_abelian_monoid, AbelianMonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Multiplication of numbers form a Monoid                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the number multiplication monoid *)
val multiplication_monoid_def = Define`
    multiplication_monoid =
       <| carrier := univ(:num);
          op := $*;
          id := 1;
        |>
`;

(*
> EVAL ``multiplication_monoid.op 5 6``;
val it = |- multiplication_monoid.op 5 6 = 30: thm
*)

(* Theorem: properties of multiplication_monoid *)
(* Proof: by multiplication_monoid_def *)
val multiplication_monoid_property = store_thm(
  "multiplication_monoid_property",
  ``(multiplication_monoid.carrier = univ(:num)) /\
   (multiplication_monoid.op = $* ) /\
   (multiplication_monoid.id = 1)``,
  rw[multiplication_monoid_def]);

(* Theorem: AbelianMonoid (multiplication_monoid) *)
(* Proof:
   By AbelianMonoid_def, Monoid_def, multiplication_monoid_def, this is to show:
   (1) ?z. z = x * y. Take z = x * y.
   (2) x * y * z = x * (y * z), true    by MULT_ASSOC
   (3) x * 1 = x /\ 1 * x = x, true     by MULT, MULT_1
   (4) x * y = y * x, true              by MULT_COMM
*)
val multiplication_monoid_abelian_monoid = store_thm(
  "multiplication_monoid_abelian_monoid",
  ``AbelianMonoid (multiplication_monoid)``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, multiplication_monoid_def, GSPECIFICATION, IN_UNIV] >-
  simp[] >>
  simp[]);

(* Theorem: Monoid (multiplication_monoid) *)
(* Proof: by multiplication_monoid_abelian_monoid, AbelianMonoid_def *)
val multiplication_monoid_monoid = store_thm(
  "multiplication_monoid_monoid",
  ``Monoid (multiplication_monoid)``,
  metis_tac[multiplication_monoid_abelian_monoid, AbelianMonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Powers of a fixed base form a Monoid                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the power monoid *)
val power_monoid_def = Define`
    power_monoid (b:num) =
       <| carrier := {b ** j | j IN univ(:num)};
          op := $*;
          id := 1;
        |>
`;

(*
> EVAL ``(power_monoid 2).op (2 ** 3) (2 ** 4)``;
val it = |- (power_monoid 2).op (2 ** 3) (2 ** 4) = 128: thm
*)

(* Theorem: properties of power monoid *)
(* Proof: by power_monoid_def *)
val power_monoid_property = store_thm(
  "power_monoid_property",
  ``!b. ((power_monoid b).carrier = {b ** j | j IN univ(:num)}) /\
       ((power_monoid b).op = $* ) /\
       ((power_monoid b).id = 1)``,
  rw[power_monoid_def]);


(* Theorem: AbelianMonoid (power_monoid b) *)
(* Proof:
   By AbelianMonoid_def, Monoid_def, power_monoid_def, this is to show:
   (1) ?j''. b ** j * b ** j' = b ** j''
       Take j'' = j + j', true         by EXP_ADD
   (2) b ** j * b ** j' * b ** j'' = b ** j * (b ** j' * b ** j'')
       True                            by EXP_ADD, ADD_ASSOC
   (3) ?j. b ** j = 1
       or ?j. (b = 1) \/ (j = 0), true by j = 0.
   (4) b ** j * b ** j' = b ** j' * b ** j
       True                            by EXP_ADD, ADD_COMM
*)
val power_monoid_abelian_monoid = store_thm(
  "power_monoid_abelian_monoid",
  ``!b. AbelianMonoid (power_monoid b)``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, power_monoid_def, GSPECIFICATION, IN_UNIV] >-
  metis_tac[EXP_ADD] >-
  rw[EXP_ADD] >-
  metis_tac[] >>
  rw[EXP_ADD]);

(* Theorem: Monoid (power_monoid b) *)
(* Proof: by power_monoid_abelian_monoid, AbelianMonoid_def *)
val power_monoid_monoid = store_thm(
  "power_monoid_monoid",
  ``!b. Monoid (power_monoid b)``,
  metis_tac[power_monoid_abelian_monoid, AbelianMonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Logarithm is an isomorphism from Power Monoid to Addition Monoid          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b ==> MonoidHomo (LOG b) (power_monoid b) (addition_monoid) *)
(* Proof:
   By MonoidHomo_def, power_monoid_def, addition_monoid_def, this is to show:
   (1) LOG b (b ** j * b ** j') = LOG b (b ** j) + LOG b (b ** j')
         LOG b (b ** j * b ** j')
       = LOG b (b ** (j + j'))              by EXP_ADD
       = j + j'                             by LOG_EXACT_EXP
       = LOG b (b ** j) + LOG b (b ** j')   by LOG_EXACT_EXP
   (2) LOG b 1 = 0, true                    by LOG_1
*)
val power_to_addition_homo = store_thm(
  "power_to_addition_homo",
  ``!b. 1 < b ==> MonoidHomo (LOG b) (power_monoid b) (addition_monoid)``,
  rw[MonoidHomo_def, power_monoid_def, addition_monoid_def] >-
  rw[LOG_EXACT_EXP, GSYM EXP_ADD] >>
  rw[LOG_1]);

(* Theorem: 1 < b ==> MonoidIso (LOG b) (power_monoid b) (addition_monoid) *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo (LOG b) (power_monoid b) addition_monoid
       This is true               by power_to_addition_homo
   (2) BIJ (LOG b) (power_monoid b).carrier addition_monoid.carrier
       By BIJ_DEF, this is to show:
       (1) INJ (LOG b) {b ** j | j IN univ(:num)} univ(:num)
           By INJ_DEF, this is to show:
               LOG b (b ** j) = LOG b (b ** j') ==> b ** j = b ** j'
               LOG b (b ** j) = LOG b (b ** j')
           ==>             j  = j'                by LOG_EXACT_EXP
           ==>         b ** j = b ** j'
       (2) SURJ (LOG b) {b ** j | j IN univ(:num)} univ(:num)
           By SURJ_DEF, this is to show:
              ?y. (?j. y = b ** j) /\ (LOG b y = x)
           Let j = x, y = b ** x, then true       by LOG_EXACT_EXP
*)
val power_to_addition_iso = store_thm(
  "power_to_addition_iso",
  ``!b. 1 < b ==> MonoidIso (LOG b) (power_monoid b) (addition_monoid)``,
  rw[MonoidIso_def] >-
  rw[power_to_addition_homo] >>
  rw_tac std_ss[BIJ_DEF, power_monoid_def, addition_monoid_def] >| [
    rw[INJ_DEF] >>
    rfs[LOG_EXACT_EXP],
    rw[SURJ_DEF] >>
    metis_tac[LOG_EXACT_EXP]
  ]);

(* ------------------------------------------------------------------------- *)
(* Theory about folding a monoid (or group) operation over a bag of elements *)
(* ------------------------------------------------------------------------- *)

Overload GITBAG = ``\(g:'a monoid) s b. ITBAG g.op s b``;

Theorem GITBAG_THM =
  ITBAG_THM |> CONV_RULE SWAP_FORALL_CONV
  |> INST_TYPE [beta |-> alpha] |> Q.SPEC`(g:'a monoid).op`
  |> GEN_ALL

Theorem GITBAG_EMPTY[simp]:
  !g a. GITBAG g {||} a = a
Proof
  rw[ITBAG_EMPTY]
QED

Theorem GITBAG_INSERT:
  !b. FINITE_BAG b ==>
    !g x a. GITBAG g (BAG_INSERT x b) a =
              GITBAG g (BAG_REST (BAG_INSERT x b))
                (g.op (BAG_CHOICE (BAG_INSERT x b)) a)
Proof
  rw[ITBAG_INSERT]
QED

Theorem SUBSET_COMMUTING_ITBAG_INSERT:
  !f b t.
    SET_OF_BAG b SUBSET t /\ closure_comm_assoc_fun f t /\ FINITE_BAG b ==>
          !x a::t. ITBAG f (BAG_INSERT x b) a = ITBAG f b (f x a)
Proof
  simp[RES_FORALL_THM]
  \\ rpt gen_tac \\ strip_tac
  \\ completeInduct_on `BAG_CARD b`
  \\ rw[]
  \\ simp[ITBAG_INSERT, BAG_REST_DEF, EL_BAG]
  \\ qmatch_goalsub_abbrev_tac`{|c|}`
  \\ `BAG_IN c (BAG_INSERT x b)` by PROVE_TAC[BAG_CHOICE_DEF, BAG_INSERT_NOT_EMPTY]
  \\ fs[BAG_IN_BAG_INSERT]
  \\ `?b0. b = BAG_INSERT c b0` by PROVE_TAC [BAG_IN_BAG_DELETE, BAG_DELETE]
  \\ `BAG_DIFF (BAG_INSERT x b) {| c |} = BAG_INSERT x b0`
  by SRW_TAC [][BAG_INSERT_commutes]
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum(qspec_then`BAG_CARD b0`mp_tac)
  \\ `FINITE_BAG b0` by FULL_SIMP_TAC (srw_ss()) []
  \\ impl_keep_tac >- SRW_TAC [numSimps.ARITH_ss][BAG_CARD_THM]
  \\ disch_then(qspec_then`b0`mp_tac)
  \\ impl_tac >- simp[]
  \\ impl_tac >- fs[SUBSET_DEF]
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ first_assum(qspec_then`x`mp_tac)
  \\ first_x_assum(qspec_then`c`mp_tac)
  \\ impl_keep_tac >- fs[SUBSET_DEF]
  \\ disch_then(qspec_then`f x a`mp_tac)
  \\ impl_keep_tac >- metis_tac[closure_comm_assoc_fun_def]
  \\ strip_tac
  \\ impl_tac >- simp[]
  \\ disch_then(qspec_then`f c a`mp_tac)
  \\ impl_keep_tac >- metis_tac[closure_comm_assoc_fun_def]
  \\ disch_then SUBST1_TAC
  \\ simp[]
  \\ metis_tac[closure_comm_assoc_fun_def]
QED

Theorem COMMUTING_GITBAG_INSERT:
  !g b. AbelianMonoid g /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET G ==>
  !x a::(G). GITBAG g (BAG_INSERT x b) a = GITBAG g b (g.op x a)
Proof
  rpt strip_tac
  \\ irule SUBSET_COMMUTING_ITBAG_INSERT
  \\ metis_tac[abelian_monoid_op_closure_comm_assoc_fun]
QED

Theorem GITBAG_INSERT_THM =
  SIMP_RULE(srw_ss())[RES_FORALL_THM, PULL_FORALL, AND_IMP_INTRO]
  COMMUTING_GITBAG_INSERT

Theorem GITBAG_UNION:
  !g. AbelianMonoid g ==>
  !b1. FINITE_BAG b1 ==> !b2. FINITE_BAG b2 /\ SET_OF_BAG b1 SUBSET G
                                            /\ SET_OF_BAG b2 SUBSET G ==>
  !a. a IN G ==> GITBAG g (BAG_UNION b1 b2) a = GITBAG g b2 (GITBAG g b1 a)
Proof
  gen_tac \\ strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  \\ simp[BAG_UNION_INSERT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ gs[SUBSET_DEF]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_tac >- metis_tac[]
  \\ first_x_assum irule
  \\ simp[]
  \\ fs[AbelianMonoid_def]
QED

Theorem GITBAG_in_carrier:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==> !a. SET_OF_BAG b SUBSET G /\ a IN G ==> GITBAG g b a IN G
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ rpt strip_tac
  \\ drule COMMUTING_GITBAG_INSERT
  \\ disch_then (qspec_then`b`mp_tac)
  \\ fs[SUBSET_DEF]
  \\ simp[RES_FORALL_THM, PULL_FORALL]
  \\ strip_tac
  \\ last_x_assum irule
  \\ metis_tac[monoid_op_element, AbelianMonoid_def]
QED

Overload GBAG = ``\(g:'a monoid) b. GITBAG g b g.id``;

Theorem GBAG_in_carrier:
  !g b. AbelianMonoid g /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET G ==> GBAG g b IN G
Proof
  rw[]
  \\ irule GITBAG_in_carrier
  \\ metis_tac[AbelianMonoid_def, monoid_id_element]
QED

Theorem GITBAG_GBAG:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==> !a. a IN g.carrier /\ SET_OF_BAG b SUBSET g.carrier ==>
      GITBAG g b a = g.op a (GITBAG g b g.id)
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[] >- fs[AbelianMonoid_def]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac >- fs[SUBSET_DEF, AbelianMonoid_def]
  \\ irule EQ_TRANS
  \\ qexists_tac`g.op (g.op e a) (GBAG g b)`
  \\ conj_tac >- (
    first_x_assum irule
    \\ metis_tac[AbelianMonoid_def, monoid_op_element] )
  \\ first_x_assum(qspec_then`e`mp_tac)
  \\ simp[]
  \\ `g.op e (#e) = e` by metis_tac[AbelianMonoid_def, monoid_id]
  \\ pop_assum SUBST1_TAC
  \\ disch_then SUBST1_TAC
  \\ fs[AbelianMonoid_def]
  \\ irule monoid_assoc
  \\ simp[]
  \\ irule GBAG_in_carrier
  \\ simp[AbelianMonoid_def]
QED

Theorem GBAG_UNION:
  AbelianMonoid g /\ FINITE_BAG b1 /\ FINITE_BAG b2 /\
  SET_OF_BAG b1 SUBSET g.carrier /\ SET_OF_BAG b2 SUBSET g.carrier ==>
  GBAG g (BAG_UNION b1 b2) = g.op (GBAG g b1) (GBAG g b2)
Proof
  rpt strip_tac
  \\ DEP_REWRITE_TAC[GITBAG_UNION]
  \\ simp[]
  \\ conj_tac >- fs[AbelianMonoid_def]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ irule GBAG_in_carrier
  \\ simp[]
QED

Theorem GITBAG_BAG_IMAGE_op:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==>
  !p q a. IMAGE p (SET_OF_BAG b) SUBSET g.carrier /\
          IMAGE q (SET_OF_BAG b) SUBSET g.carrier /\ a IN g.carrier ==>
  GITBAG g (BAG_IMAGE (\x. g.op (p x) (q x)) b) a =
  g.op (GITBAG g (BAG_IMAGE p b) a) (GBAG g (BAG_IMAGE q b))
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[] >- fs[AbelianMonoid_def]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ conj_asm1_tac
  >- (
    gs[SUBSET_DEF, PULL_EXISTS]
    \\ gs[AbelianMonoid_def] )
  \\ qmatch_goalsub_abbrev_tac`GITBAG g bb aa`
  \\ first_assum(qspecl_then[`p`,`q`,`aa`]mp_tac)
  \\ impl_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS, Abbr`aa`]
    \\ fs[AbelianMonoid_def] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[Abbr`aa`]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ conj_asm1_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[AbelianMonoid_def] )
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ conj_asm1_tac >- fs[AbelianMonoid_def]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG |> SIMP_RULE(srw_ss())[PULL_FORALL,AND_IMP_INTRO]
                          |> Q.SPECL[`g`,`b`,`g.op x y`]]
  \\ simp[]
  \\ fs[AbelianMonoid_def]
  \\ qmatch_goalsub_abbrev_tac`_ * _ * gp * ( _ * gq)`
  \\ `gp IN g.carrier /\ gq IN g.carrier`
  by (
    unabbrev_all_tac
    \\ conj_tac \\ irule GBAG_in_carrier
    \\ fs[AbelianMonoid_def] )
  \\ drule monoid_assoc
  \\ strip_tac \\ gs[]
QED

Theorem IMP_GBAG_EQ_ID:
  AbelianMonoid g ==>
  !b. BAG_EVERY ((=) g.id) b ==> GBAG g b = g.id
Proof
  rw[]
  \\ `FINITE_BAG b`
  by (
    Cases_on`b = {||}` \\ simp[]
    \\ once_rewrite_tac[GSYM unibag_FINITE]
    \\ rewrite_tac[FINITE_BAG_OF_SET]
    \\ `SET_OF_BAG b = {g.id}`
    by (
      rw[SET_OF_BAG, FUN_EQ_THM]
      \\ fs[BAG_EVERY]
      \\ rw[EQ_IMP_THM]
      \\ Cases_on`b` \\ rw[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[])
  \\ qpat_x_assum`BAG_EVERY _ _` mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[] \\ gs[]
  \\ drule COMMUTING_GITBAG_INSERT
  \\ disch_then drule
  \\ impl_keep_tac
  >- (
    fs[SUBSET_DEF, BAG_EVERY]
    \\ fs[AbelianMonoid_def]
    \\ metis_tac[monoid_id_element] )
  \\ simp[RES_FORALL_THM, PULL_FORALL, AND_IMP_INTRO]
  \\ disch_then(qspecl_then[`#e`,`#e`]mp_tac)
  \\ simp[]
  \\ metis_tac[monoid_id_element, monoid_id_id, AbelianMonoid_def]
QED

Theorem GITBAG_CONG:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==> !b' a a'. FINITE_BAG b' /\
        a IN g.carrier /\ SET_OF_BAG b SUBSET g.carrier /\ SET_OF_BAG b' SUBSET g.carrier
        /\ (!x. BAG_IN x (BAG_UNION b b') /\ x <> g.id ==> b x = b' x)
  ==>
  GITBAG g b a = GITBAG g b' a
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT \\ rw[]
  >- (
    fs[BAG_IN, BAG_INN, EMPTY_BAG]
    \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
    \\ simp[]
    \\ irule EQ_TRANS
    \\ qexists_tac`g.op a g.id`
    \\ conj_tac >- fs[AbelianMonoid_def]
    \\ AP_TERM_TAC
    \\ irule EQ_SYM
    \\ irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, BAG_IN, BAG_INN]
    \\ metis_tac[])
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ fs[SET_OF_BAG_INSERT]
  \\ Cases_on`e = g.id`
  >- (
    fs[AbelianMonoid_def]
    \\ first_x_assum irule
    \\ simp[]
    \\ fs[BAG_INSERT]
    \\ metis_tac[] )
  \\ `BAG_IN e b'`
  by (
    simp[BAG_IN, BAG_INN]
    \\ fs[BAG_INSERT]
    \\ first_x_assum(qspec_then`e`mp_tac)
    \\ simp[] )
  \\ drule BAG_DECOMPOSE
  \\ disch_then(qx_choose_then`b2`strip_assume_tac)
  \\ pop_assum SUBST_ALL_TAC
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[] \\ fs[SET_OF_BAG_INSERT]
  \\ first_x_assum irule \\ simp[]
  \\ fs[BAG_INSERT, AbelianMonoid_def]
  \\ qx_gen_tac`x`
  \\ disch_then assume_tac
  \\ first_x_assum(qspec_then`x`mp_tac)
  \\ impl_tac >- metis_tac[]
  \\ IF_CASES_TAC \\ simp[]
QED

Theorem GITBAG_same_op:
  g1.op = g2.op ==>
  !b. FINITE_BAG b ==>
  !a. GITBAG g1 b a = GITBAG g2 b a
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[GITBAG_THM]
QED

Theorem GBAG_IMAGE_PARTITION:
  AbelianMonoid g /\ FINITE s ==>
  !b. FINITE_BAG b ==>
    IMAGE f (SET_OF_BAG b) SUBSET G /\
    (!x. BAG_IN x b ==> ?P. P IN s /\ P x) /\
    (!x P1 P2. BAG_IN x b /\ P1 IN s /\ P2 IN s /\ P1 x /\ P2 x ==> P1 = P2)
  ==>
    GBAG g (BAG_IMAGE (λP. GBAG g (BAG_IMAGE f (BAG_FILTER P b))) (BAG_OF_SET s)) =
    GBAG g (BAG_IMAGE f b)
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ conj_tac
  >- (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY]
    \\ rw[]
    \\ imp_res_tac BAG_IN_BAG_IMAGE_IMP
    \\ fs[] )
  \\ rpt strip_tac
  \\ fs[SET_OF_BAG_INSERT]
  \\ `?P. P IN s /\ P e` by metis_tac[]
  \\ `?s0. s = P INSERT s0 /\ P NOTIN s0` by metis_tac[DECOMPOSITION]
  \\ BasicProvers.VAR_EQ_TAC
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_INSERT]
  \\ qpat_x_assum`_ ==> _`mp_tac
  \\ impl_tac >- metis_tac[]
  \\ strip_tac
  \\ conj_tac >- metis_tac[FINITE_INSERT, FINITE_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE ff (BAG_OF_SET s0)`
  \\ `BAG_IMAGE ff (BAG_OF_SET s0) =
      BAG_IMAGE (\P. GBAG g (BAG_IMAGE f (BAG_FILTER P b))) (BAG_OF_SET s0)`
  by (
    irule BAG_IMAGE_CONG
    \\ simp[Abbr`ff`]
    \\ rw[]
    \\ metis_tac[IN_INSERT] )
  \\ simp[Abbr`ff`]
  \\ pop_assum kall_tac
  \\ rpt(first_x_assum(qspec_then`ARB`kall_tac))
  \\ pop_assum mp_tac
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ fs[AbelianMonoid_def]
  \\ conj_asm1_tac >- fs[SUBSET_DEF, PULL_EXISTS]
  \\ conj_asm1_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ irule GITBAG_in_carrier
    \\ fs[SUBSET_DEF, PULL_EXISTS, AbelianMonoid_def] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[AbelianMonoid_def]
    \\ irule GITBAG_in_carrier
    \\ simp[AbelianMonoid_def] )
  \\ simp[]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG] \\ simp[] \\ strip_tac
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG] \\ simp[]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG] \\ simp[]
  \\ DEP_REWRITE_TAC[monoid_assoc]
  \\ simp[]
  \\ conj_tac >- ( irule GBAG_in_carrier \\ simp[] )
  \\ irule EQ_SYM
  \\ irule GITBAG_GBAG
  \\ simp[]
QED

Theorem GBAG_PARTITION:
  AbelianMonoid g /\ FINITE s /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET G /\
    (!x. BAG_IN x b ==> ?P. P IN s /\ P x) /\
    (!x P1 P2. BAG_IN x b /\ P1 IN s /\ P2 IN s /\ P1 x /\ P2 x ==> P1 = P2)
  ==>
    GBAG g (BAG_IMAGE (λP. GBAG g (BAG_FILTER P b)) (BAG_OF_SET s)) = GBAG g b
Proof
  strip_tac
  \\ `!P. FINITE_BAG (BAG_FILTER P b)` by metis_tac[FINITE_BAG_FILTER]
  \\ `GBAG g b = GBAG g (BAG_IMAGE I b)` by metis_tac[BAG_IMAGE_FINITE_I]
  \\ pop_assum SUBST1_TAC
  \\ `(λP. GBAG g (BAG_FILTER P b)) = λP. GBAG g (BAG_IMAGE I (BAG_FILTER P b))`
  by simp[FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_IMAGE_PARTITION
  \\ simp[]
  \\ metis_tac[]
QED

Theorem GBAG_IMAGE_FILTER:
  AbelianMonoid g ==>
  !b. FINITE_BAG b ==> IMAGE f (SET_OF_BAG b INTER P) SUBSET g.carrier ==>
  GBAG g (BAG_IMAGE f (BAG_FILTER P b)) =
  GBAG g (BAG_IMAGE (\x. if P x then f x else g.id) b)
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ conj_asm1_tac
  >- (
    rw[]
    \\ fs[AbelianMonoid_def]
    \\ metis_tac[IN_DEF] )
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ fs[AbelianMonoid_def]
  \\ qmatch_goalsub_abbrev_tac`_ * gg`
  \\ `gg IN g.carrier`
  by (
    simp[Abbr`gg`]
    \\ irule GBAG_in_carrier
    \\ simp[AbelianMonoid_def, SUBSET_DEF, PULL_EXISTS] )
  \\ IF_CASES_TAC \\ gs[]
  \\ simp[Abbr`gg`]
  \\ irule EQ_SYM
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[PULL_EXISTS, SUBSET_DEF, AbelianMonoid_def]
  \\ conj_tac >- metis_tac[]
  \\ qpat_x_assum`_ = _`(assume_tac o SYM) \\ simp[]
  \\ irule GITBAG_GBAG
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[AbelianMonoid_def]
QED

Theorem GBAG_INSERT:
  AbelianMonoid g /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET g.carrier /\ x IN g.carrier ==>
  GBAG g (BAG_INSERT x b) = g.op x (GBAG g b)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ `Monoid g` by fs[AbelianMonoid_def] \\ simp[]
  \\ irule GITBAG_GBAG
  \\ simp[]
QED

Theorem MonoidHomo_GBAG:
  AbelianMonoid g /\ AbelianMonoid h /\
  MonoidHomo f g h /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET g.carrier ==>
  f (GBAG g b) = GBAG h (BAG_IMAGE f b)
Proof
  strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ fs[MonoidHomo_def]
  \\ rpt strip_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ `GBAG g b IN g.carrier` suffices_by metis_tac[]
  \\ irule GBAG_in_carrier
  \\ simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem IMP_GBAG_EQ_EXP:
  AbelianMonoid g /\ x IN g.carrier /\ SET_OF_BAG b SUBSET {x} ==>
  GBAG g b = g.exp x (b x)
Proof
  Induct_on`b x` \\ rw[]
  >- (
    Cases_on`b = {||}` \\ simp[]
    \\ fs[SUBSET_DEF]
    \\ Cases_on`b` \\ fs[BAG_INSERT] )
  \\ `b = BAG_INSERT x (b - {|x|})`
  by (
    simp[BAG_EXTENSION]
    \\ simp[BAG_INN, BAG_INSERT, EMPTY_BAG, BAG_DIFF]
    \\ rw[] )
  \\ qmatch_asmsub_abbrev_tac`BAG_INSERT x b0`
  \\ fs[]
  \\ `b0 x = v` by fs[BAG_INSERT]
  \\ first_x_assum(qspecl_then[`b0`,`x`]mp_tac)
  \\ simp[]
  \\ impl_tac >- fs[SUBSET_DEF]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ simp[BAG_INSERT]
  \\ rewrite_tac[GSYM arithmeticTheory.ADD1]
  \\ simp[]
  \\ DEP_REWRITE_TAC[GSYM FINITE_SET_OF_BAG]
  \\ `SET_OF_BAG b0 SUBSET {x}` by fs[SUBSET_DEF]
  \\ `FINITE {x}` by simp[]
  \\ reverse conj_tac >- fs[SUBSET_DEF]
  \\ metis_tac[SUBSET_FINITE]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
