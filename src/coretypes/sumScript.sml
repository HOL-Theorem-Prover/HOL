(* ===================================================================== *)
(* FILE          : sumScript.sml                                         *)
(* DESCRIPTION   : Creates a theory containing the logical definition of *)
(*                 the sum type operator.  The sum type is defined and   *)
(*                 the following `axiomatization` is proven from the     *)
(*                 definition of the type:                               *)
(*                                                                       *)
(*                   |- !f g. ?!h. (h o INL = f) /\ (h o INR = g)        *)
(*                                                                       *)
(*                 Using this axiom, the following standard theorems are *)
(*                 proven.                                               *)
(*                                                                       *)
(*                  |- ISL (INL a)                 |- ISR (INR b)        *)
(*                  |- ~ISL (INR b)                |- ~ISR (INL a)       *)
(*                  |- OUTL (INL a) = a            |- OUTR (INR b) = b   *)
(*                  |- ISL(x) ==> INL (OUTL x)=x                         *)
(*                  |- ISR(x) ==> INR (OUTR x)=x                         *)
(*                  |- !x. ISL x \/ ISR x                                *)
(*                                                                       *)
(*                 Also defines an infix SUM such that f SUM g denotes   *)
(*                 the unique function asserted to exist by the axiom.   *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* REVISED       : 87.03.14                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


open HolKernel Parse boolLib BasicProvers;
open quotientLib boolSimps simpLib

(* done to keep Holmake happy - satTheory is an ancestor of BasicProvers *)
local open satTheory in end

local open DefnBase in end
val _ = new_theory "sum";

fun simp ths = simpLib.asm_simp_tac (srw_ss()) ths (* don't eta reduce *)

val o_DEF = combinTheory.o_DEF
and o_THM = combinTheory.o_THM;

(* ---------------------------------------------------------------------*)
(* Introduce the new type.                                              *)
(*                                                                      *)
(* The sum of types `:'a` and `:'b` will be represented by a certain    *)
(* subset of type `:bool->'a->'b->bool`.  A left injection of value     *)
(* `p:'a` will be represented by:  `\b x y. x=p /\ b`. A right injection*)
(* of value `q:'b` will be represented by:  `\b x y. x=q /\ ~b`.        *)
(* The predicate IS_SUM_REP is true of just those objects of the type   *)
(* `:bool->'a->'b->bool` which are representations of some injection.   *)
(* ---------------------------------------------------------------------*)


val IS_SUM_REP =
    new_definition
     ("IS_SUM_REP",
      “IS_SUM_REP (f:bool->'a->'b->bool) =
         ?v1 v2.  (f = \b x y.(x=v1) /\ b) \/
                  (f = \b x y.(y=v2) /\ ~b)”);

(* Prove that there exists some object in the representing type that    *)
(* lies in the subset of legal representations.                         *)

val EXISTS_SUM_REP =
    TAC_PROOF(([], “?f:bool -> 'a -> 'b -> bool. IS_SUM_REP f”),
              EXISTS_TAC “\b x (y:'b). (x = @(x:'a).T) /\ b” THEN
              PURE_ONCE_REWRITE_TAC [IS_SUM_REP] THEN
              EXISTS_TAC “@(x:'a).T” THEN
              REWRITE_TAC []);

(* ---------------------------------------------------------------------*)
(* Use the type definition mechanism to introduce the new type.         *)
(* The theorem returned is:  |- ?rep. TYPE_DEFINITION IS_SUM_REP rep    *)
(* ---------------------------------------------------------------------*)

val sum_TY_DEF = new_type_definition ("sum", EXISTS_SUM_REP);
val _ = add_infix_type {Prec = 60, ParseName = SOME "+", Name = "sum",
                        Assoc = HOLgrammars.RIGHT}


(*---------------------------------------------------------------------------*)
(* Define a representation function, REP_sum, from the type ('a,'b)sum to    *)
(* the representing type bool->'a->'b->bool, and the inverse abstraction     *)
(* function ABS_sum, and prove some trivial lemmas about them.               *)
(*---------------------------------------------------------------------------*)

val sum_ISO_DEF = define_new_type_bijections
                  {name = "sum_ISO_DEF",
                   ABS = "ABS_sum",
                   REP = "REP_sum",
                   tyax = sum_TY_DEF};


val R_A    = GEN_ALL (SYM (SPEC_ALL (CONJUNCT2 sum_ISO_DEF)))
and R_11   = SYM(SPEC_ALL (prove_rep_fn_one_one sum_ISO_DEF))
and A_ONTO = REWRITE_RULE [IS_SUM_REP] (prove_abs_fn_onto sum_ISO_DEF);

(* --------------------------------------------------------------------- *)
(* The definitions of the constants INL and INR follow:                 *)
(* --------------------------------------------------------------------- *)

(* Define the injection function INL:'a->('a,'b)sum                     *)
val INL_DEF = new_definition("INL_DEF[notuserdef]",
   “!e.(INL:'a->(('a,'b)sum)) e = ABS_sum(\b x (y:'b). (x = e) /\ b)”);

(* Define the injection function INR:'b->( 'a,'b )sum                   *)
val INR_DEF = new_definition("INR_DEF[notuserdef]",
   “!e.(INR:'b->(('a,'b)sum)) e = ABS_sum(\b (x:'a) y. (y = e) /\ ~b)”);

(* --------------------------------------------------------------------- *)
(* The proof of the `axiom` for sum types follows.                      *)
(* --------------------------------------------------------------------- *)

val SIMP = REWRITE_RULE [];
fun REWRITE1_TAC th = REWRITE_TAC [th];

(* Prove that REP_sum(INL v) gives the representation of INL v.         *)
val REP_INL = TAC_PROOF(([],
   “REP_sum (INL v) = \b x (y:'b). ((x:'a) = v) /\ b”),
   PURE_REWRITE_TAC [INL_DEF,R_A,IS_SUM_REP] THEN
   EXISTS_TAC “v:'a” THEN
   REWRITE_TAC[]);


(* Prove that REP_sum(INR v) gives the representation of INR v.         *)
val REP_INR = TAC_PROOF(([],
   “REP_sum (INR v) = \b (x:'a) y. ((y:'b) = v) /\ ~b”),
   PURE_REWRITE_TAC [INR_DEF,R_A,IS_SUM_REP] THEN
   MAP_EVERY EXISTS_TAC [“v:'a”,“v:'b”] THEN
   DISJ2_TAC THEN
   REFL_TAC);

(* Prove that INL is one-to-one                                         *)
val INL_11 = store_thm(
  "INL_11",
  ``(INL x = ((INL y):('a,'b)sum)) = (x = y)``,
   EQ_TAC THENL
   [PURE_REWRITE_TAC [R_11,REP_INL] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (ACCEPT_TAC o SIMP o SPECL [“T”,“x:'a”,“y:'b”]),
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

(* Prove that INR is one-to-one                                         *)
val INR_11 = store_thm(
  "INR_11",
  ``(INR x = (INR y:('a,'b)sum)) = (x = y)``,
   EQ_TAC THENL
   [PURE_REWRITE_TAC [R_11,REP_INR] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (ACCEPT_TAC o SYM o SIMP o SPECL[“F”,“x:'a”,“y:'b”]),
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val INR_INL_11 = save_thm("INR_INL_11",
                          CONJ (GEN_ALL INL_11) (GEN_ALL INR_11));
val _ = export_rewrites ["INR_INL_11"]

(* Prove that left injections and right injections are not equal.       *)
val INR_neq_INL = store_thm("INR_neq_INL",
   “!v1 v2. ~(INR v2 :('a,'b)sum = INL v1)”,
   PURE_REWRITE_TAC [R_11,REP_INL,REP_INR] THEN
   REPEAT GEN_TAC THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (CONTR_TAC o SIMP o SPECL [“T”,“v1:'a”,“v2:'b”]));

(*----------------------------------------------------------------------*)
(* The abstract `axiomatization` of the sum type consists of the single *)
(* theorem given below:                                                 *)
(*                                                                      *)
(* sum_axiom    |- !f g. ?!h. (h o INL = f) /\ (h o INR = g)            *)
(*                                                                      *)
(* The definitions of the usual operators ISL, OUTL, etc. follow from   *)
(* this axiom.                                                          *)
(*----------------------------------------------------------------------*)

val sum_axiom = store_thm("sum_axiom",
    “!(f:'a->'c).
       !(g:'b->'c).
       ?!h. ((h o INL) = f) /\ ((h o INR) = g)”,
PURE_REWRITE_TAC [boolTheory.EXISTS_UNIQUE_DEF,o_DEF] THEN
CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC FUN_EQ_CONV)) THEN
REPEAT (FILTER_STRIP_TAC “x:('a,'b)sum->'c”) THENL
[EXISTS_TAC (“\(x:('a,'b)sum). if (?v1. x = INL v1)
                                 then f(@v1.x = INL v1)
                                 else g(@v2.x = INR v2):'c”) THEN
 simpLib.SIMP_TAC boolSimps.bool_ss [
   INL_11,INR_11,INR_neq_INL,SELECT_REFL_2
 ],
 REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
 (REWRITE1_TAC o (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)))) THEN
 REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (SPEC “s:('a,'b)sum” A_ONTO) THEN
 ASM_REWRITE_TAC (map (SYM o SPEC_ALL) [INL_DEF,INR_DEF])]);


(* ---------------------------------------------------------------------*)
(* We also prove a version of sum_axiom which is in a form suitable for *)
(* use with the recursive type definition tools.                        *)
(* ---------------------------------------------------------------------*)

val sum_Axiom0 = prove(
   “!f:'a->'c.
      !g:'b->'c.
      ?!h. (!x. h(INL x) = f x) /\
           (!y. h(INR y) = g y)”,
   let val cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom
       val rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv)
   in
   MATCH_ACCEPT_TAC rew
   end);

val sum_INDUCT = save_thm("sum_INDUCT",
                          Prim_rec.prove_induction_thm sum_Axiom0);

Theorem sum_Axiom:
  !(f:'a -> 'c) (g:'b -> 'c).
          ?h. (!x. h (INL x) = f x) /\ (!y. h (INR y) = g y)
Proof
  REPEAT GEN_TAC THEN
  STRIP_ASSUME_TAC
    ((SPECL [Term`f:'a -> 'c`, Term`g:'b -> 'c`] o
         Ho_Rewrite.REWRITE_RULE [EXISTS_UNIQUE_THM]) sum_Axiom0) THEN
  EXISTS_TAC (Term`h:'a + 'b -> 'c`) THEN
  ASM_REWRITE_TAC []
QED

val [sum_case_def] = Prim_rec.define_case_constant sum_Axiom
val _ = export_rewrites ["sum_case_def"]
val _ = overload_on("case", ``sum_CASE``)


val _ = TypeBase.export $ TypeBasePure.gen_datatype_info
    {ax=sum_Axiom, case_defs=[sum_case_def], ind=sum_INDUCT}

Theorem FORALL_SUM:
  (!s. P s) <=> (!x. P (INL x)) /\ (!y. P (INR y))
Proof
  EQ_TAC THENL [DISCH_TAC THEN ASM_REWRITE_TAC [],
                MATCH_ACCEPT_TAC sum_INDUCT]
QED

open simpLib

(* !P. (?s. P s) <=> (?x. P (INL x)) \/ (?y. P (INR y)) *)
val EXISTS_SUM = save_thm(
  "EXISTS_SUM",
  FORALL_SUM |> Q.INST [`P` |-> `\x. ~P x`] |> AP_TERM ``$~``
             |> CONV_RULE (BINOP_CONV (SIMP_CONV bool_ss []))
             |> Q.GEN `P`)


val sum_CASES = save_thm("sum_CASES",
                         hd (Prim_rec.prove_cases_thm sum_INDUCT));

val sum_distinct = store_thm("sum_distinct",
  Term`!x:'a y:'b. ~(INL x = INR y)`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC ((BETA_RULE o REWRITE_RULE [EXISTS_UNIQUE_DEF] o
                     Q.ISPECL [`\x:'a. T`, `\y:'b. F`]) sum_Axiom) THEN
  FIRST_X_ASSUM (MP_TAC o AP_TERM (Term`h:'a + 'b -> bool`)) THEN
  ASM_REWRITE_TAC []);
val _ = export_rewrites ["sum_distinct"]

val sum_distinct_rev = save_thm("sum_distinct1", GSYM sum_distinct);

(* ---------------------------------------------------------------------*)
(* The definitions of ISL, ISR, OUTL, OUTR follow.                      *)
(* ---------------------------------------------------------------------*)

val ISL = new_recursive_definition {
  def = “ISL (INL x) = T /\ ISL (INR y) = F”,
  name = "ISL[simp,compute]",
  rec_axiom = sum_Axiom
};

val ISR = new_recursive_definition {
  def = “ISR(INR x) = T /\ ISR(INL y) = F”, name = "ISR[simp,compute]",
  rec_axiom = sum_Axiom
};

val OUTL = new_recursive_definition {
  def = “OUTL (INL x) = x”, name = "OUTL[simp,compute]",
  rec_axiom = sum_Axiom
};

val OUTR = new_recursive_definition {
  def = “OUTR(INR x:'a+'b) = x”, name = "OUTR[simp,compute]",
  rec_axiom = sum_Axiom
};

val _ = TypeBase.general_update “:'a + 'b”
                (TypeBasePure.put_recognizers [ISL, ISR] o
                 TypeBasePure.put_destructors [OUTL, OUTR] o
                 TypeBasePure.put_lift (
                     mk_var("sumSyntax.lift_sum",
                            “:'type -> ('a -> 'term) ->
                              ('b -> 'term) -> ('a,'b)sum -> 'term”)
                  ))

(* ---------------------------------------------------------------------*)
(* Prove the following standard theorems about the sum type.            *)
(*                                                                      *)
(*                |- ISL(s) ==> INL (OUTL s)=s                          *)
(*                |- ISR(s) ==> INR (OUTR s)=s                          *)
(*                |- !s. ISL s \/ ISR s                                 *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)
(* First, get the existence and uniqueness parts of sum_axiom.          *)
(*                                                                      *)
(* sum_EXISTS:                                                          *)
(*   |- !f g. ?h. (!x. h(INL x) = f x) /\ (!x. h(INR x) = g x)          *)
(*                                                                      *)
(* sum_UNIQUE:                                                          *)
(*   |- !f g x y.                                                       *)
(*       ((!x. x(INL x) = f x) /\ (!x. x(INR x) = g x)) /\              *)
(*       ((!x. y(INL x) = f x) /\ (!x. y(INR x) = g x)) ==>             *)
(*       (!s. x s = y s)                                                *)
(* ---------------------------------------------------------------------*)

(* GEN_ALL gives problems, so changed to be more precise. kls.          *)
val [sum_EXISTS,sum_UNIQUE] =
   let val cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom
       val rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv)
       val [a,b] = CONJUNCTS (CONV_RULE EXISTS_UNIQUE_CONV rew)
   in
   map (GENL  [“f :'a -> 'c”, “g :'b -> 'c”])
       [ a, BETA_RULE (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) b) ]
   end;

(* Prove that: !x. ISL(x) \/ ISR(x)                                     *)
val ISL_OR_ISR = store_thm("ISL_OR_ISR",
    “!x:('a,'b)sum. ISL(x) \/ ISR(x)”,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC “x:('a,'b)sum” sum_CASES) THEN
    ASM_REWRITE_TAC [ISL,ISR]);

(* Prove that: |- !x. ISL(x) ==> INL (OUTL x) = x                       *)
val INL = store_thm("INL",
    “!x:('a,'b)sum. ISL(x) ==> (INL (OUTL x) = x)”,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC “x:('a,'b)sum” sum_CASES) THEN
    ASM_REWRITE_TAC [ISL,OUTL]);
val _ = export_rewrites ["INL"]

(* Prove that: |- !x. ISR(x) ==> INR (OUTR x) = x                       *)
val INR = store_thm("INR",
    “!x:('a,'b)sum. ISR(x) ==> (INR (OUTR x) = x)”,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC “x:('a,'b)sum” sum_CASES) THEN
    ASM_REWRITE_TAC [ISR,OUTR]);
val _ = export_rewrites ["INR"]

val sum_case_cong = save_thm("sum_case_cong",
                             Prim_rec.case_cong_thm sum_CASES sum_case_def);


(* ----------------------------------------------------------------------
    SUM_MAP
   ---------------------------------------------------------------------- *)

val SUM_MAP_def = Prim_rec.new_recursive_definition{
  name = "SUM_MAP_def[simp,compute]",
  def = ``(SUM_MAP f g (INL (a:'a)) = INL (f a:'c)) /\
          (SUM_MAP f g (INR (b:'b)) = INR (g b:'d))``,
  rec_axiom = sum_Axiom};
val _ = temp_set_mapped_fixity{tok = "++", term_name = "SUM_MAP",
                               fixity = Infixl 480}

val SUM_MAP = store_thm (
  "SUM_MAP",
  ``!f g (z:'a + 'b).
         (f ++ g) z = if ISL z then INL (f (OUTL z))
                      else INR (g (OUTR z)) :'c + 'd``,
  SIMP_TAC (srw_ss()) [FORALL_SUM]);

val SUM_MAP_CASE = store_thm (
  "SUM_MAP_CASE",
  ``!f g (z:'a + 'b).
         (f ++ g) z = sum_CASE z (INL o f) (INR o g) :'c + 'd``,
  SIMP_TAC (srw_ss()) [FORALL_SUM]);

Theorem SUM_MAP_I[simp,quotient_simp]:
  (I ++ I) = (I : 'a + 'b -> 'a + 'b)
Proof
  simp[FORALL_SUM, FUN_EQ_THM]
QED

Theorem SUM_MAP_o:
  (f ++ g) o (h ++ k) = (f o h) ++ (g o k)
Proof
  SIMP_TAC (srw_ss()) [FORALL_SUM, FUN_EQ_THM]
QED

val cond_sum_expand = store_thm("cond_sum_expand",
``(!x y z. ((if P then INR x else INL y) = INR z) = (P /\ (z = x))) /\
  (!x y z. ((if P then INR x else INL y) = INL z) = (~P /\ (z = y))) /\
  (!x y z. ((if P then INL x else INR y) = INL z) = (P /\ (z = x))) /\
  (!x y z. ((if P then INL x else INR y) = INR z) = (~P /\ (z = y)))``,
Cases_on `P` THEN FULL_SIMP_TAC(srw_ss())[] THEN SRW_TAC[][EQ_IMP_THM])
val _ = export_rewrites["cond_sum_expand"]

val NOT_ISL_ISR = store_thm("NOT_ISL_ISR",
  ``!x. ~ISL x = ISR x``,
  GEN_TAC THEN Q.SPEC_THEN `x` STRUCT_CASES_TAC sum_CASES THEN SRW_TAC[][])
val _ = export_rewrites["NOT_ISL_ISR"]

val NOT_ISR_ISL = store_thm("NOT_ISR_ISL",
  ``!x. ~ISR x = ISL x``,
  GEN_TAC THEN Q.SPEC_THEN `x` STRUCT_CASES_TAC sum_CASES THEN SRW_TAC[][])
val _ = export_rewrites["NOT_ISR_ISL"]

(* ----------------------------------------------------------------------
    SUM_ALL
   ---------------------------------------------------------------------- *)

val SUM_ALL_def = Prim_rec.new_recursive_definition {
  def = ``(SUM_ALL (P:'a -> bool) (Q:'b -> bool) (INL x) <=> P x) /\
          (SUM_ALL (P:'a -> bool) (Q:'b -> bool) (INR y) <=> Q y)``,
  name = "SUM_ALL_def",
  rec_axiom = sum_Axiom}
val _ = export_rewrites ["SUM_ALL_def"]

val SUM_ALL_MONO = store_thm(
  "SUM_ALL_MONO",
  ``(!x:'a. P x ==> P' x) /\ (!y:'b. Q y ==> Q' y) ==>
    SUM_ALL P Q s ==> SUM_ALL P' Q' s``,
  Q.SPEC_THEN `s` STRUCT_CASES_TAC sum_CASES THEN
  REWRITE_TAC [SUM_ALL_def] THEN REPEAT STRIP_TAC THEN RES_TAC);
val _ = IndDefLib.export_mono "SUM_ALL_MONO"

val SUM_ALL_CONG = store_thm(
  "SUM_ALL_CONG[defncong]",
  ``!(s:'a + 'b) s' P P' Q Q'.
       (s = s') /\ (!a. (s' = INL a) ==> (P a <=> P' a)) /\
       (!b. (s' = INR b) ==> (Q b <=> Q' b)) ==>
       (SUM_ALL P Q s <=> SUM_ALL P' Q' s')``,
  SIMP_TAC (srw_ss()) [FORALL_SUM]);

(* ----------------------------------------------------------------------
    SUM_FIN, sums built from particular sets
   ---------------------------------------------------------------------- *)

val SUM_FIN_def = new_definition(
  "SUM_FIN_def",
  “SUM_FIN A B = \ab. sum_CASE ab (\a. a IN A) (\b. b IN B)”);

Theorem IN_SUM_FIN_THM[simp]:
  (INL a IN SUM_FIN A B <=> a IN A) /\
  (INR b IN SUM_FIN A B <=> b IN B)
Proof
  SIMP_TAC (srw_ss()) [SUM_FIN_def, IN_DEF]
QED

(* ----------------------------------------------------------------------
    SUM_REL, the sum "relator"
   ---------------------------------------------------------------------- *)

val SUM_REL_def = Prim_rec.new_recursive_definition {
  def = “(SUM_REL R1 R2 (INL x:'a + 'b) ab <=> ISL ab /\ R1 x (OUTL ab)) /\
         (SUM_REL R1 R2 (INR y) ab <=> ISR ab /\ R2 y (OUTR ab))”,
  name = "SUM_REL_def",
  rec_axiom = sum_Axiom};

val _ = set_fixity "+++" (Infixl 480)
Overload "+++" = “SUM_REL”

Theorem SUM_REL_THM[simp,compute]:
  (SUM_REL R1 R2 (INL x :'a + 'b) (INL a) <=> R1 x a) /\
  (SUM_REL R1 R2 (INL x) (INR b) <=> F) /\
  (SUM_REL R1 R2 (INR y) (INL a) <=> F) /\
  (SUM_REL R1 R2 (INR y) (INR b) <=> R2 y b)
Proof
  SIMP_TAC (srw_ss()) [SUM_REL_def]
QED

Theorem SUM_REL_EQ[simp,quotient_simp]:
  SUM_REL $= $= = ($= : 'a + 'b -> 'a + 'b -> bool)
Proof
  REWRITE_TAC [FUN_EQ_THM] >> SIMP_TAC (srw_ss()) [FORALL_SUM]
QED

Theorem SUM_REL_REFL:
  (!x:'a. R1 x x) /\ (!a:'b. R2 a a) ==>
  !xy. SUM_REL R1 R2 xy xy
Proof
  SIMP_TAC (srw_ss()) [FORALL_SUM]
QED

Theorem SUM_REL_SYM:
  (!x y:'a. R1 x y <=> R1 y x) /\ (!a b:'b. R2 a b <=> R2 b a) ==>
  !xy ab. SUM_REL R1 R2 xy ab <=> SUM_REL R1 R2 ab xy
Proof
  SIMP_TAC (srw_ss()) [FORALL_SUM]
QED

Theorem SUM_REL_TRANS:
  (!x y z:'a. R1 x y /\ R1 y z ==> R1 x z) /\
  (!a b c:'b. R2 a b /\ R2 b c ==> R2 a c) ==>
  !xy ab uv. SUM_REL R1 R2 xy ab /\ SUM_REL R1 R2 ab uv ==>
             SUM_REL R1 R2 xy uv
Proof
  SIMP_TAC (srw_ss()) [FORALL_SUM]
QED

(* ----------------------------------------------------------------------
    SUM_SET
   ---------------------------------------------------------------------- *)

val SUM_SET_def = Prim_rec.new_recursive_definition {
  def = “SUM_SET f1 f2 (INL a : 'a + 'b) = f1 a : ('c -> bool) /\
         SUM_SET f1 f2 (INR b) = f2 b”,
  name = "SUM_SET_def", rec_axiom = sum_Axiom};

Overload setL = “SUM_SET ($= : 'a -> 'a -> bool) (K (\x. F) : 'b -> 'a -> bool)”
Overload setR = “SUM_SET (K (\x. F) : 'a -> 'b -> bool) ($= : 'b -> 'b -> bool)”

Theorem SUM_SETLR_THM[simp]:
  (a1 IN setL (INL a2 : 'a + 'b) <=> a1 = a2) /\
  (a IN setL  (INR b  : 'a + 'b) <=> F) /\
  (b IN setR  (INL a  : 'a + 'b) <=> F) /\
  (b1 IN setR (INR b2 : 'a + 'b) <=> b1 = b2)
Proof
  SIMP_TAC (srw_ss()) [SUM_SET_def, IN_DEF, EQ_IMP_THM]
QED

(* used later for sigma *)
val _ = remove_ovl_mapping "SUM_SET" {Name = "SUM_SET", Thy = "sum"}

Theorem SUM_MAP_CONG:
  (!a:'a. a IN setL ab ==> f1 a = f2 a :'c) /\
  (!b:'b. b IN setR ab ==> g1 b = g2 b :'d) ==>
  SUM_MAP f1 g1 ab = SUM_MAP f2 g2 ab
Proof
  Q.ID_SPEC_TAC ‘ab’ >> SIMP_TAC (srw_ss()) [FORALL_SUM]
QED

Theorem SUM_ALL_SET:
  SUM_ALL P Q ab <=> (!a. a IN setL ab ==> P a) /\ (!b. b IN setR ab ==> Q b)
Proof
  Q.ID_SPEC_TAC ‘ab’ >> SIMP_TAC (srw_ss()) [FORALL_SUM]
QED

Theorem SUM_MAP_SET[simp]:
  (c IN setL (SUM_MAP f g ab) <=> ?a:'a. c:'c = f a /\ a IN setL ab) /\
  (d IN setR (SUM_MAP f g ab) <=> ?b:'b. d:'d = g b /\ b IN setR ab)
Proof
  Q.ID_SPEC_TAC ‘ab’ >> SIMP_TAC (srw_ss()) [FORALL_SUM]
QED


val _ = computeLib.add_persistent_funs ["sum_case_def", "INL_11", "INR_11",
                                        "sum_distinct", "sum_distinct1",
                                        "SUM_ALL_def"]

local open OpenTheoryMap
val ns = ["Data","Sum"]
fun add x y = OpenTheory_const_name{const={Thy="sum",Name=x},name=(ns,y)} in
val _ = OpenTheory_tyop_name{tyop={Thy="sum",Tyop="sum"},name=(ns,"+")}
val _ = add "INR" "right"
val _ = add "INL" "left"
val _ = add "OUTR" "destRight"
val _ = add "OUTL" "destLeft"
end


val datatype_sum = store_thm(
  "datatype_sum",
  ``DATATYPE (sum (INL:'a -> 'a + 'b) (INR:'b -> 'a + 'b))``,
  REWRITE_TAC[DATATYPE_TAG_THM]);

(* ----------------------------------------------------------------------
    Theorems to support the quotient package
   ---------------------------------------------------------------------- *)

Theorem SUM_EQUIV[quotient_equiv]:
  !(R1:'a -> 'a -> bool) (R2:'b -> 'b -> bool).
    EQUIV R1 ==> EQUIV R2 ==> EQUIV (R1 +++ R2)
Proof
  simp[EQUIV_def, EQUIV_REFL_SYM_TRANS, FORALL_SUM] >> PROVE_TAC[]
QED

Theorem SUM_QUOTIENT[quotient]:
  !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         QUOTIENT (R1 +++ R2) (abs1 ++ abs2) (rep1 ++ rep2)
Proof
  REPEAT STRIP_TAC
  THEN REWRITE_TAC[QUOTIENT_def]
  THEN REPEAT CONJ_TAC
    THENL
      [ rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >> simp[FORALL_SUM],

        rpt (dxrule_then assume_tac QUOTIENT_REP_REFL) >> simp[FORALL_SUM],

        simp[FORALL_SUM] >>
        rpt (dxrule_then (fn th => simp[Once th, SimpLHS]) QUOTIENT_REL)
      ]
QED

(* sum theory: INL, INR, ISL, ISR, ++ *)
fun prs_tac ths =
  rpt (rpt gen_tac >> disch_tac) >>
  rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp(FORALL_SUM::ths)

Theorem INL_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a. INL a = (abs1 ++ abs2) (INL (rep1 a))
Proof prs_tac[]
QED

Theorem INL_RSP[quotient_rsp]:
   !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2.
          R1 a1 a2 ==>
          (R1 +++ R2) (INL a1) (INL a2)
Proof
  simp[]
QED

Theorem INR_PRS[quotient_prs]:
   !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !b. INR b = (abs1 ++ abs2) (INR (rep2 b))
Proof prs_tac[]
QED

Theorem INR_RSP[quotient_rsp]:
  !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !b1 b2.
          R2 b1 b2 ==>
          (R1 +++ R2) (INR b1) (INR b2)
Proof
  simp[]
QED

Theorem ISL_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a. ISL a = ISL ((rep1 ++ rep2) a)
Proof prs_tac[]
QED

Theorem ISL_RSP[quotient_rsp]:
   !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2.
          (R1 +++ R2) a1 a2 ==>
          (ISL a1 = ISL a2)
Proof
  simp[FORALL_SUM]
QED

Theorem ISR_PRS[quotient_prs]:
    !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a. ISR a = ISR ((rep1 ++ rep2) a)
Proof prs_tac[]
QED

Theorem ISR_RSP[quotient_rsp]:
    !R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2.
          (R1 +++ R2) a1 a2 ==>
          (ISR a1 = ISR a2)
Proof
   simp[FORALL_SUM]
QED

(* OUTL and OUTR are not completely defined, so do not lift. *)

Theorem SUM_MAP_PRS[quotient_prs]:
   !R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f g. (f ++ g) =
               ((rep1 ++ rep3) --> (abs2 ++ abs4))
                   (((abs1 --> rep2) f) ++ ((abs3 --> rep4) g))
Proof prs_tac[FUN_MAP_THM, FUN_EQ_THM]
QED

Theorem SUM_MAP_RSP[quotient_rsp]:
    !R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f1 f2 g1 g2.
          (R1 ===> R2) f1 f2 /\ (R3 ===> R4) g1 g2 ==>
          ((R1 +++ R3) ===> (R2 +++ R4)) (f1 ++ g1) (f2 ++ g2)
Proof
  simp[FUN_REL, FORALL_SUM]
QED

val _ = temp_remove_termtok {term_name = "SUM_MAP", tok = "++"}

val _ = export_theory();
