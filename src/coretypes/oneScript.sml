(* ===================================================================== *)
(* FILE          : oneScript.sml                                         *)
(* DESCRIPTION   : Creates the theory "one" containing the logical       *)
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


open Lib HolKernel Parse boolLib BasicProvers

local open satTheory in end

val _ = new_theory "one";

local open OpenTheoryMap in
val ns = ["Data","Unit"]
val _ = OpenTheory_tyop_name{tyop={Thy="one",Tyop="one"},name=(ns,"unit")}
val _ = OpenTheory_const_name{const={Thy="one",Name="one"},name=(ns,"()")}
val _ = OpenTheory_const_name{const={Thy="one",Name="one_CASE"},name=(ns,"case")}
end

(* ---------------------------------------------------------------------*)
(* Introduce the new type.                                              *)
(* The type :one will be represented by the subset {T} of :bool.        *)
(* The predicate defining this subset will be `\b.b`.  We must first    *)
(* prove the (trivial) theorem: ?b.(\b.b)b.                             *)
(*----------------------------------------------------------------------*)

val EXISTS_ONE_REP = prove
(“?b:bool. (\b.b) b”,
 EXISTS_TAC “T” THEN CONV_TAC BETA_CONV THEN ACCEPT_TAC TRUTH);

(*---------------------------------------------------------------------------*)
(* Use the type definition mechanism to introduce the new type.              *)
(* The theorem returned is:   |- ?rep. TYPE_DEFINITION (\b.b) rep            *)
(*---------------------------------------------------------------------------*)

val one_TY_DEF =
 REWRITE_RULE [boolTheory.TYPE_DEFINITION_THM]
    (new_type_definition("one", EXISTS_ONE_REP));

(* ---------------------------------------------------------------------*)
(* The proof of the `axiom` for type :one follows.                      *)
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
    Define the constant `one` of type one.
 ---------------------------------------------------------------------------*)

val one_DEF = new_definition ("one_DEF", Term`one = @x:one.T`);

(*---------------------------------------------------------------------------
  The following theorem shows that there is only one value of type :one
 ---------------------------------------------------------------------------*)

val one = store_thm("one[simp]",
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
    “!e:'a. ?!fn. fn one = e”,
    STRIP_TAC THEN
    CONV_TAC EXISTS_UNIQUE_CONV THEN
    STRIP_TAC THENL
    [EXISTS_TAC “\(x:one).(e:'a)” THEN
     BETA_TAC THEN REFL_TAC,
     REPEAT STRIP_TAC THEN
     CONV_TAC FUN_EQ_CONV THEN
     ONCE_REWRITE_TAC [one] THEN
     ASM_REWRITE_TAC[]]);

val one_prim_rec = store_thm
 ("one_prim_rec",
  Term`!e:'a. ?fn. fn one = e`,
  ACCEPT_TAC
    (GEN_ALL (CONJUNCT1 (SPEC_ALL
      (CONV_RULE (DEPTH_CONV EXISTS_UNIQUE_CONV) one_Axiom)))));

(* ----------------------------------------------------------------------
    Set up the one value to print as (), by analogy with SML's unit
   ---------------------------------------------------------------------- *)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT,0)),
                  fixity = Closefix,
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "(", TOK ")"],
                  term_name = "one"};

(*---------------------------------------------------------------------------
     Doing the above does not affect the pretty-printer because the
     printer works under the assumption that the only things with
     pretty-printer rules are applications ("comb"s).  In order to get
     ``one`` to print as ``()``, we overload it to that string.  This is
     solely for its effect on the printing ("outward") direction; the
     concrete syntax is such that Absyn parsing will never generate the
     string "()" for later stages of the parsing process to see, and it
     wouldn't matter if it did.
 ---------------------------------------------------------------------------*)

val _ = overload_on ("()", ``one``);
val _ = type_abbrev_pp("unit",``:one``);

val one_induction = Q.store_thm
("one_induction",
 `!P:one->bool. P one ==> !x. P x`,
 REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [one] THEN ASM_REWRITE_TAC[]);

val FORALL_ONE = store_thm(
  "FORALL_ONE[simp]",
  ``(!x:unit. P x) <=> P ()``,
  simpLib.SIMP_TAC boolSimps.bool_ss [EQ_IMP_THM, one_induction]);

(* This (and the next) was in examples/lambda/basics/termSceipt.sml, etc. *)
Theorem FORALL_ONE_FN :
    (!uf : one -> 'a. P uf) = !a. P (\u. a)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (Q.SPEC_THEN `uf ()` MP_TAC) THEN
  Q_TAC SUFF_TAC `(\y. uf()) = uf` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, one]
QED

Theorem EXISTS_ONE_FN :
    (?f : 'a -> one -> 'b. P f) = (?f : 'a -> 'b. P (\x u. f x))
Proof
  SRW_TAC [][EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `\a. f a ()` THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `(\x u. f x ()) = f` THEN1 SRW_TAC [][] THEN
    SRW_TAC [][FUN_EQ_THM, one],
    Q.EXISTS_TAC `\a u. f a` THEN SRW_TAC [][]
  ]
QED

(*---------------------------------------------------------------------------
    Define the case constant
 ---------------------------------------------------------------------------*)

val one_case_def = new_definition (
  "one_case_def",
  Term`one_CASE (u:unit) (x:'a) = x`);

val one_case_thm = Q.store_thm
 ("one_case_thm",
  `!x:'a. one_CASE () x = x`,
  ONCE_REWRITE_TAC [GSYM one] THEN REWRITE_TAC [one_case_def]);


val _ = TypeBase.export (
      TypeBasePure.gen_datatype_info {
        ax=one_prim_rec, ind=one_induction,
        case_defs = [one_case_thm]
      }
    )

val _ = computeLib.add_persistent_funs ["one_case_def"]



val _ = export_theory();
