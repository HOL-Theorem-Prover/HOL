(* ------------------------------------------------------------------------- *)
(* Submonoid                                                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "submonoid";

(* ------------------------------------------------------------------------- *)


(* val _ = load "lcsymtacs"; *)
open lcsymtacs;

(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "monoidMapTheory"; *)
open monoidTheory monoidMapTheory;

open pred_setTheory;
open helperSetTheory;


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
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

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
       Since x IN G, y IN G and z IN G                      by IN_SUBSET
       This follows by monoid_assoc.
   (3) (smbINTER g).id IN (smbINTER g).carrier
       This is true by submonoid_big_intersect_has_id.
   (4) x IN (smbINTER g).carrier ==> (smbINTER g).op (smbINTER g).id x = x
       Since (smbINTER g).id IN (smbINTER g).carrier   by submonoid_big_intersect_op_element
         and (smbINTER g).id = #e                      by submonoid_big_intersect_property
        also x IN G                                    by IN_SUBSET
         (smbINTER g).op (smbINTER g).id x
       = #e * x                                        by submonoid_big_intersect_property
       = x                                             by monoid_id
   (5) x IN (smbINTER g).carrier ==> (smbINTER g).op x (smbINTER g).id = x
       Since (smbINTER g).id IN (smbINTER g).carrier   by submonoid_big_intersect_op_element
         and (smbINTER g).id = #e                      by submonoid_big_intersect_property
        also x IN G                                    by IN_SUBSET
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
    `x IN G /\ y IN G /\ z IN G` by metis_tac[IN_SUBSET] >>
    rw[monoid_assoc],
    metis_tac[submonoid_big_intersect_has_id],
    `(smbINTER g).id = #e` by rw[submonoid_big_intersect_property] >>
    `(smbINTER g).id IN (smbINTER g).carrier` by metis_tac[submonoid_big_intersect_has_id] >>
    `#e * x = x` suffices_by rw[submonoid_big_intersect_property] >>
    `x IN G` by metis_tac[IN_SUBSET] >>
    rw[],
    `(smbINTER g).id = #e` by rw[submonoid_big_intersect_property] >>
    `(smbINTER g).id IN (smbINTER g).carrier` by metis_tac[submonoid_big_intersect_has_id] >>
    `x * #e = x` suffices_by rw[submonoid_big_intersect_property] >>
    `x IN G` by metis_tac[IN_SUBSET] >>
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

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
