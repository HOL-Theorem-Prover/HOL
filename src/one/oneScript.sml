(* ===================================================================== *)
(* FILE          : oneScript.sml                                         *)
(* DESCRIPTION   : Creates the theory `one.th` containing the logical    *)
(*                 definition of the type :one, the type with only one   *)
(*                 value.  The type :one is defined and the following    *)
(*                 `axiomatization` is proven from the definition of the *)
(*                 type:                                                 *)
(*                                                                       *)
(*                     one_axiom: |- !f g. f = (g:'a->one)               *)
(*                                                                       *)
(*                 an alternative axiom is also proved:                  *)
(*                                                                       *)
(*                     one_Axiom: |- !e:'a. ?!fn. fn one = e             *)
(*                                                                       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.03.03                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure oneScript =
struct

open Lib HolKernel Parse boolLib;

type thm = Thm.thm;
infix THEN THENL;

val _ = new_theory "one";

(* ---------------------------------------------------------------------*)
(* Introduce the new type.						*)
(* The type :one will be represented by the subset {T} of :bool.	*)
(* The predicate defining this subset will be `\b.b`.  We must first 	*)
(* prove the (trivial) theorem: ?b.(\b.b)b.				*)
(*----------------------------------------------------------------------*)

val EXISTS_ONE_REP =
   prove(--`?b:bool. (\b.b) b`--,
         EXISTS_TAC (--`T`--) THEN
         CONV_TAC BETA_CONV THEN
         ACCEPT_TAC TRUTH);

(* Use the type definition mechanism to introduce the new type.		*)
(* The theorem returned is:   |- ?rep. TYPE_DEFINITION (\b.b) rep	*)

val one_TY_DEF = REWRITE_RULE [boolTheory.TYPE_DEFINITION_THM]
       (new_type_definition("one", EXISTS_ONE_REP));

(* ---------------------------------------------------------------------*)
(* The proof of the `axiom` for type :one follows.			*)
(* ---------------------------------------------------------------------*)

val one_axiom = store_thm("one_axiom",
  Term`!f g:'a -> one. f = g`,
    CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
    REPEAT GEN_TAC THEN
    STRIP_ASSUME_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) one_TY_DEF) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EQ_TAC THEN DISCH_THEN (K ALL_TAC) THEN
    POP_ASSUM (CONV_TAC o REWR_CONV) THENL
    [EXISTS_TAC (Term`g (x:'a):one`), EXISTS_TAC (Term`f (x:'a):one`)]
    THEN REFL_TAC);

(*---------------------------------------------------------------------------
    Define the constant `one` of type one....
 ---------------------------------------------------------------------------*)

val one_DEF = new_definition ("one_DEF", Term`one = @x:one.T`);

(*---------------------------------------------------------------------------
  The following theorem shows that there is only one value of type :one
 ---------------------------------------------------------------------------*)

val one = store_thm("one",
 Term`!v:one. v = one`,
 GEN_TAC THEN
 ACCEPT_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
   (AP_THM
     (SPECL [Term`\x:'a.(v:one)`,
             Term`\x:'a.one`] one_axiom) (Term`x:'a`))));

(*---------------------------------------------------------------------------
    Prove also the following theorem:
 ---------------------------------------------------------------------------*)

val one_Axiom = store_thm("one_Axiom",
    --`!e:'a. ?!fn. fn one = e`--,
    STRIP_TAC THEN
    CONV_TAC EXISTS_UNIQUE_CONV THEN
    STRIP_TAC THENL
    [EXISTS_TAC (--`\(x:one).(e:'a)`--) THEN
     BETA_TAC THEN REFL_TAC,
     REPEAT STRIP_TAC THEN
     CONV_TAC FUN_EQ_CONV THEN
     ONCE_REWRITE_TAC [one] THEN
     ASM_REWRITE_TAC[]]);

val _ = export_theory();

end;
