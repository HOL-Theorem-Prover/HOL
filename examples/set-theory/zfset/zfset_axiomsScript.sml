(*****************************************************************************)
(* ZF-like axiomatic formalization of set theory in HOL following a mixture  *)
(* of Johnstone's book "Notes on logic and set theory" and Paulson's report  *)
(* "Set Theory as a Computational Logic: I. From Foundations to Functions"   *)
(* (Computer Laboratory Technical Report CL TR 271).                         *)
(*                                                                           *)
(* Probably equivalent (according to Thomas Forster) to ordinary             *)
(* (i.e. first order) ZF plus the existence of some large cardinals.         *)
(*                                                                           *)
(* Ported to HOL4 in 2007 from some ancient (1994) HOL88 files.              *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE FOR COMPILATION                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
******************************************************************************)
(*
quietdec := true;
map load [];
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)


(*****************************************************************************)
(* Create zfset_axiomsTheory                                                 *)
(*****************************************************************************)
val _ = new_theory "zfset_axioms";
val _ = ParseExtras.temp_loose_equality()
(*****************************************************************************)
(* The Universe ``:zfset``.                                                  *)
(*****************************************************************************)
val _ = new_type("zfset",0);

(*****************************************************************************)
(* The membership relation.                                                  *)
(*****************************************************************************)
val _ = set_fixity "In" (Infix(NONASSOC, 550));
val _ = new_constant("In", ``:zfset->zfset->bool``);

(*****************************************************************************)
(* The axioms                                                                *)
(*****************************************************************************)

(*****************************************************************************)
(* Axiom of extensionality.                                                  *)
(*****************************************************************************)
val Extension_ax =
 new_axiom("Extension_ax", ``!s t. (s = t) = (!x. x In s = x In t)``);

(*****************************************************************************)
(* Axiom of empty set.                                                       *)
(*****************************************************************************)
val EmptySet_ax =
 new_axiom("EmptySet_ax", ``?s. !x. ~(x In s)``);

(*****************************************************************************)
(* Definition of the empty set: |- !x. ~x In Empty                           *)
(*****************************************************************************)
val Empty_def =
 new_specification("Empty_def", ["Empty"], EmptySet_ax);

val EmptyEq =
 store_thm
  ("EmptyEq",
   ``!s. (!x. ~(x In s)) = (s = Empty)``,
   PROVE_TAC [Empty_def,Extension_ax]);

val NotEmpty =
 store_thm
  ("NotEmpty",
   ``!s. (?x. x In s) = ~(s = Empty)``,
   PROVE_TAC [Empty_def,Extension_ax]);

(*****************************************************************************)
(* Axiom of union.                                                           *)
(*****************************************************************************)
val Union_ax =
 new_axiom("Union_ax", ``!s. ?t. !x. x In t = ?u. x In u /\ u In s``);

(*****************************************************************************)
(* Big union:                                                                *)
(*                                                                           *)
(* UU = |- !x t. t In (UU x) = (?z. t In z /\ z In x)                        *)
(*****************************************************************************)
val UU_def =
 new_specification("UU_def", ["UU"] , CONV_RULE SKOLEM_CONV Union_ax);

(*****************************************************************************)
(* Definition of set inclusion.                                              *)
(*****************************************************************************)
val _ = set_fixity "Subset" (Infix(NONASSOC, 540));
val Subset_def =
 Define `s Subset t = !x. x In s ==> x In t`;

(*****************************************************************************)
(* Axiom of power-sets.                                                      *)
(*****************************************************************************)
val PowerSet_ax =
 new_axiom("PowerSet_ax", ``!s. ?t. !x. x In t = x Subset s``);

(*****************************************************************************)
(* Definition of the power set constructor                                   *)
(*                                                                           *)
(*    |- !s x. x In (Pow s) = (!y. y In x ==> y In s)                        *)
(*****************************************************************************)
val Pow_def =
 new_specification
  ("Pow_def",
   ["Pow"] ,
   prove
    (``?f. !s x. x In f s = !y. y In x ==> y In s``,
     REWRITE_TAC[CONV_RULE SKOLEM_CONV PowerSet_ax,GSYM Subset_def]));

val PowEmpty =
 store_thm
  ("PowEmpty",
   ``!x. x In Pow Empty = (x = Empty)``,
   PROVE_TAC[Pow_def,EmptyEq]);

val PowEmptyEq =
 store_thm
  ("PowEmptyEq",
   ``!s. (!x. x In s ==> (x = Empty)) /\ ~(s = Empty) = (s = Pow Empty)``,
   METIS_TAC[Pow_def,NotEmpty,Extension_ax]);

val EmptyPowEmpty =
 store_thm
  ("EmptyPowEmpty",
   ``~(Empty = Pow Empty) /\ ~(Pow Empty = Empty)``,
   METIS_TAC[Pow_def,NotEmpty,Extension_ax]);

val PowPowEmpty =
 store_thm
 ("PowPowEmpty",
  ``!x. x In Pow(Pow Empty) = (x = Empty) \/ (x = Pow Empty)``,
  METIS_TAC[Pow_def,EmptyEq,PowEmptyEq]);

(*****************************************************************************)
(* Axiom of replacement.                                                     *)
(*****************************************************************************)
val Replacement_ax =
 new_axiom
   ("Replacement_ax",
    ``!f s. ?t. !y. y In t = ?x. x In s /\ (y = f x)``);

(*****************************************************************************)
(* Image = |- !f t y. y In (Image f t) = (?x. x In t /\ (y = f x))           *)
(*****************************************************************************)
val Image_def =
 new_specification
  ("Image_def",
   ["Image"],
   (CONV_RULE SKOLEM_CONV Replacement_ax));

(*****************************************************************************)
(* Definition of singleton set: |- !x y. y In (Singleton x) = (y = x)        *)
(*****************************************************************************)
val Singleton_def =
 new_specification
  ("Singleton_def",
   ["Singleton"],
   (CONV_RULE
     SKOLEM_CONV
     (prove
       (``!s. ?t. !x. x In t = (x = s)``,
        GEN_TAC
         THEN EXISTS_TAC ``Image(\x. s)(Pow Empty)``
         THEN RW_TAC std_ss [Image_def,PowEmpty]))));

(*****************************************************************************)
(* Axiom of separation.                                                      *)
(*****************************************************************************)
val Separation_ax = store_thm("Separation_ax",
  ``!p s. ?t. !x. x In t = x In s /\ p x``,
NTAC 2 GEN_TAC THEN
EXISTS_TAC ``if (!x. x In s ==> ~(p x)) then Empty
             else Image (\x. if p x then x else (@x. x In s /\ p x)) s`` THEN
SRW_TAC [][Empty_def,Image_def] THEN
METIS_TAC []);

(*****************************************************************************)
(* Definition of Spec s p = set of x in s satisfying predicate p.            *)
(*****************************************************************************)
val Spec_def =
 new_specification
  ("Spec_def",
   ["Spec"],
   (prove
    (``?f. !s p. !x. x In (f s p) = x In s /\ p x``,
     METIS_TAC[CONV_RULE SKOLEM_CONV (SPEC_ALL Separation_ax)])));

(*****************************************************************************)
(* Definition of set intersection.                                           *)
(*                                                                           *)
(* Intersect = |- !s t x. x In (s Intersect t) = x In s /\ x In t            *)
(*                                                                           *)
(*****************************************************************************)
val _ = set_fixity "Intersect" (Infix(RIGHT, 300));
val Intersect_def =
 new_specification
  ("Intersect_def",
   ["Intersect"],
   (prove
     (``?f. !s t x. x In f s t = x In s /\ x In t``,
      EXISTS_TAC ``\s t. Spec s (\x. x In t)``
       THEN RW_TAC std_ss [Spec_def])));

(*****************************************************************************)
(* Axiom of foundation.                                                      *)
(*****************************************************************************)
val Foundation_ax =
 new_axiom
  ("Foundation_ax",
   ``!s. ~(s = Empty) ==> ?x. x In s /\ (x Intersect s = Empty)``);

(*****************************************************************************)
(* Pairing.                                                                  *)
(*****************************************************************************)
val Pairing =
 store_thm
  ("Pairing",
   ``!x y. ?u. x In u /\ y In u``,
   REPEAT GEN_TAC
    THEN EXISTS_TAC
          ``Image
            (\a. if (a = Empty)     then x else
                 if (a = Pow Empty) then y else ARB)
            (Pow(Pow Empty))``
   THEN RW_TAC std_ss [Image_def,PowPowEmpty]
   THEN PROVE_TAC[EmptyPowEmpty]);

(*****************************************************************************)
(* PairingFun_def = |- !x y. x In (PairingFun x y) /\ y In (PairingFun x y)  *)
(*****************************************************************************)
val PairingFun_def =
 new_specification
  ("PairingFun_def",
   ["PairingFun"] ,
   (CONV_RULE SKOLEM_CONV Pairing));

val Upair_def =
 Define `Upair x y = Spec (PairingFun x y) (\z. (z = x) \/ (z = y))`;

val InUpair =
 store_thm
  ("InUpair",
   ``!x y z. z In (Upair x y) = (z = x) \/ (z = y)``,
   RW_TAC std_ss [Upair_def,Spec_def]
    THEN PROVE_TAC[PairingFun_def]);

(*****************************************************************************)
(* Infixed binary union of sets.                                             *)
(*****************************************************************************)
val _ = set_fixity "U" (Infix(RIGHT, 350));
val U_def =
 new_specification
  ("U_def",
   ["U"],
   (prove
    (``?f. !s t x. x In (f s t) = (x In s) \/ (x In t)``,
     EXISTS_TAC ``\s t. UU(Upair s t)``
      THEN PROVE_TAC[UU_def,InUpair])));

(*****************************************************************************)
(* Successor of a set.                                                       *)
(*****************************************************************************)
val Suc_def =
 Define
  `Suc x = x U (Singleton x)`;

(*****************************************************************************)
(* Axiom of Infinity.                                                        *)
(*****************************************************************************)
val Infinity_ax =
 new_axiom("Infinity_ax", ``?s. Empty In s /\ !x. x In s ==> Suc x In s``);

val InfiniteSet_def =
 new_specification("InfiniteSet_def",["InfiniteSet"],Infinity_ax);

(*****************************************************************************)
(* End of the ZF axioms.                                                     *)
(*****************************************************************************)

val _ = export_theory();
