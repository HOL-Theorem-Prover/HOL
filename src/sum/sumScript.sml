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


structure sumScript =
struct

open HolKernel Parse boolLib BasicProvers;

(* done to keep Holmake happy - satTheory is an ancestor of BasicProvers *)
local open satTheory in end

val _ = new_theory "sum";

val o_DEF = combinTheory.o_DEF
and o_THM = combinTheory.o_THM;

(* ---------------------------------------------------------------------*)
(* Introduce the new type.						*)
(*                                                                      *)
(* The sum of types `:'a` and `:'b` will be represented by a certain	*)
(* subset of type `:bool->'a->'b->bool`.  A left injection of value     *)
(* `p:'a` will be represented by:  `\b x y. x=p /\ b`. A right injection*)
(* of value `q:'b` will be represented by:  `\b x y. x=q /\ ~b`.        *)
(* The predicate IS_SUM_REP is true of just those objects of the type	*)
(* `:bool->'a->'b->bool` which are representations of some injection.	*)
(* ---------------------------------------------------------------------*)


val IS_SUM_REP =
    new_definition
     ("IS_SUM_REP",
      --`IS_SUM_REP (f:bool->'a->'b->bool) =
         ?v1 v2.  (f = \b x y.(x=v1) /\ b) \/
                  (f = \b x y.(y=v2) /\ ~b)`--);

(* Prove that there exists some object in the representing type that 	*)
(* lies in the subset of legal representations.				*)

val EXISTS_SUM_REP =
    TAC_PROOF(([], --`?f:bool -> 'a -> 'b -> bool. IS_SUM_REP f`--),
	      EXISTS_TAC (--`\b x (y:'b). (x = @(x:'a).T) /\ b`--) THEN
	      PURE_ONCE_REWRITE_TAC [IS_SUM_REP] THEN
	      EXISTS_TAC (--`@(x:'a).T`--) THEN
	      REWRITE_TAC []);

(* ---------------------------------------------------------------------*)
(* Use the type definition mechanism to introduce the new type.		*)
(* The theorem returned is:  |- ?rep. TYPE_DEFINITION IS_SUM_REP rep 	*)
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
(* The definitions of the constants INL and INR follow:			*)
(* --------------------------------------------------------------------- *)

(* Define the injection function INL:'a->('a,'b)sum			*)
val INL_DEF = new_definition("INL_DEF",
   --`!e.(INL:'a->(('a,'b)sum)) e = ABS_sum(\b x (y:'b). (x = e) /\ b)`--);

(* Define the injection function INR:'b->( 'a,'b )sum			*)
val INR_DEF = new_definition("INR_DEF",
   --`!e.(INR:'b->(('a,'b)sum)) e = ABS_sum(\b (x:'a) y. (y = e) /\ ~b)`--);

(* --------------------------------------------------------------------- *)
(* The proof of the `axiom` for sum types follows.			*)
(* --------------------------------------------------------------------- *)

val SIMP = REWRITE_RULE [];
fun REWRITE1_TAC th = REWRITE_TAC [th];

(* Prove that REP_sum(INL v) gives the representation of INL v.		*)
val REP_INL = TAC_PROOF(([],
   --`REP_sum (INL v) = \b x (y:'b). ((x:'a) = v) /\ b`--),
   PURE_REWRITE_TAC [INL_DEF,R_A,IS_SUM_REP] THEN
   EXISTS_TAC (--`v:'a`--) THEN
   REWRITE_TAC[]);


(* Prove that REP_sum(INR v) gives the representation of INR v.		*)
val REP_INR = TAC_PROOF(([],
   --`REP_sum (INR v) = \b (x:'a) y. ((y:'b) = v) /\ ~b`--),
   PURE_REWRITE_TAC [INR_DEF,R_A,IS_SUM_REP] THEN
   MAP_EVERY EXISTS_TAC [--`v:'a`--,--`v:'b`--] THEN
   DISJ2_TAC THEN
   REFL_TAC);

(* Prove that INL is one-to-one						*)
val INL_11 = store_thm(
  "INL_11",
  ``(INL x = ((INL y):('a,'b)sum)) = (x = y)``,
   EQ_TAC THENL
   [PURE_REWRITE_TAC [R_11,REP_INL] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (ACCEPT_TAC o SIMP o SPECL [--`T`--,--`x:'a`--,--`y:'b`--]),
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

(* Prove that INR is one-to-one						*)
val INR_11 = store_thm(
  "INR_11",
  ``(INR x = (INR y:('a,'b)sum)) = (x = y)``,
   EQ_TAC THENL
   [PURE_REWRITE_TAC [R_11,REP_INR] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (ACCEPT_TAC o SYM o SIMP o SPECL[--`F`--,--`x:'a`--,--`y:'b`--]),
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val INR_INL_11 = save_thm("INR_INL_11",
                          CONJ (GEN_ALL INL_11) (GEN_ALL INR_11));
val _ = export_rewrites ["INR_INL_11"]

(* Prove that left injections and right injections are not equal.	*)
val INR_neq_INL = store_thm("INR_neq_INL",
   --`!v1 v2. ~(INR v2 :('a,'b)sum = INL v1)`--,
   PURE_REWRITE_TAC [R_11,REP_INL,REP_INR] THEN
   REPEAT GEN_TAC THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (CONTR_TAC o SIMP o SPECL [--`T`--,--`v1:'a`--,--`v2:'b`--]));

(*----------------------------------------------------------------------*)
(* The abstract `axiomatization` of the sum type consists of the single	*)
(* theorem given below:							*)
(*									*)
(* sum_axiom    |- !f g. ?!h. (h o INL = f) /\ (h o INR = g)		*)
(*									*)
(* The definitions of the usual operators ISL, OUTL, etc. follow from 	*)
(* this axiom.								*)
(*----------------------------------------------------------------------*)

val sum_axiom = store_thm("sum_axiom",
    --`!(f:'a->'c).
       !(g:'b->'c).
       ?!h. ((h o INL) = f) /\ ((h o INR) = g)`--,
PURE_REWRITE_TAC [boolTheory.EXISTS_UNIQUE_DEF,o_DEF] THEN
CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC FUN_EQ_CONV)) THEN
REPEAT (FILTER_STRIP_TAC (--`x:('a,'b)sum->'c`--)) THENL
[EXISTS_TAC (--`\(x:('a,'b)sum). if (?v1. x = INL v1)
                                 then f(@v1.x = INL v1)
                                 else g(@v2.x = INR v2):'c`--) THEN
 simpLib.SIMP_TAC boolSimps.bool_ss [
   INL_11,INR_11,INR_neq_INL,SELECT_REFL_2
 ],
 REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
 (REWRITE1_TAC o (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)))) THEN
 REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (SPEC (--`s:('a,'b)sum`--) A_ONTO) THEN
 ASM_REWRITE_TAC (map (SYM o SPEC_ALL) [INL_DEF,INR_DEF])]);


(* ---------------------------------------------------------------------*)
(* We also prove a version of sum_axiom which is in a form suitable for *)
(* use with the recursive type definition tools.			*)
(* ---------------------------------------------------------------------*)

val sum_Axiom0 = prove(
   --`!f:'a->'c.
      !g:'b->'c.
      ?!h. (!x. h(INL x) = f x) /\
           (!y. h(INR y) = g y)`--,
   let val cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom
       val rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv)
   in
   MATCH_ACCEPT_TAC rew
   end);

val sum_INDUCT = save_thm("sum_INDUCT",
                          Prim_rec.prove_induction_thm sum_Axiom0);

val FORALL_SUM = Q.store_thm
 ("FORALL_SUM",
  `(!s. P s) = (!x. P (INL x)) /\ (!y. P (INR y))`,
  EQ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC [],
    MATCH_ACCEPT_TAC sum_INDUCT]);

open simpLib

(* !P. (?s. P s) <=> (?x. P (INL x)) \/ (?y. P (INR y)) *)
val EXISTS_SUM = save_thm(
  "EXISTS_SUM",
  FORALL_SUM |> Q.INST [`P` |-> `\x. ~P x`] |> AP_TERM ``$~``
             |> CONV_RULE (BINOP_CONV (SIMP_CONV bool_ss []))
             |> Q.GEN `P`)

val sum_Axiom = store_thm(
  "sum_Axiom",
  Term`!(f:'a -> 'c) (g:'b -> 'c).
          ?h. (!x. h (INL x) = f x) /\ (!y. h (INR y) = g y)`,
  REPEAT GEN_TAC THEN
  STRIP_ASSUME_TAC
    ((SPECL [Term`f:'a -> 'c`, Term`g:'b -> 'c`] o
         Ho_Rewrite.REWRITE_RULE [EXISTS_UNIQUE_THM]) sum_Axiom0) THEN
  EXISTS_TAC (Term`h:'a + 'b -> 'c`) THEN
  ASM_REWRITE_TAC []);

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
(* The definitions of ISL, ISR, OUTL, OUTR follow.			*)
(* ---------------------------------------------------------------------*)


(* Derive the defining property for ISL.				*)
val ISL_DEF = TAC_PROOF(
  ([], --`?ISL. (!x:'a. ISL(INL x)) /\ (!y:'b. ~ISL(INR y))`--),
  let val inst = INST_TYPE [Type.gamma |-> Type.bool] sum_axiom
      val spec = SPECL [--`\x:'a.T`--, --`\y:'b.F`--] inst
      val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
      val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth
  in
      STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] conv) THEN
      EXISTS_TAC (--`h:'a+'b->bool`--) THEN ASM_REWRITE_TAC []
  end);

(* Then define ISL with a constant specification.			*)
val ISL = new_specification("ISL",["ISL"], ISL_DEF);
val _ = export_rewrites ["ISL"]

(* Derive the defining property for ISR.				*)
val ISR_DEF = TAC_PROOF(
  ([], --`?ISR. (!x:'b. ISR(INR x)) /\ (!y:'a. ~ISR(INL y))`--),
  let val inst = INST_TYPE [Type.gamma |-> Type.bool] sum_axiom
      val spec = SPECL [--`\x:'a.F`--,  --`\y:'b.T`--] inst
      val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
      val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth
  in
      STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] conv) THEN
      EXISTS_TAC (--`h:'a+'b->bool`--) THEN ASM_REWRITE_TAC []
  end);

(* Then define ISR with a constant specification.			*)
val ISR = new_specification("ISR",["ISR"], ISR_DEF);
val _ = export_rewrites ["ISR"]

(* Derive the defining property of OUTL.				*)
val OUTL_DEF = TAC_PROOF(([],
--`?OUTL. !x. OUTL(INL x:('a,'b)sum) = x`--),
   let val inst = INST_TYPE [Type.gamma |-> Type.alpha] sum_axiom
       val spec = SPECL [--`\x:'a.x`--, --`\y:'b.@x:'a.F`--] inst
       val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
       val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth
   in
   STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] (BETA_RULE conv)) THEN
   EXISTS_TAC (--`h:'a+'b->'a`--) THEN ASM_REWRITE_TAC []
   end);

(* Then define OUTL with a constant specification.			*)
val OUTL = new_specification("OUTL",["OUTL"], OUTL_DEF)
val _ = export_rewrites ["OUTL"]

(* Derive the defining property of OUTR.				*)
val OUTR_DEF = TAC_PROOF(
  ([], --`?OUTR. !x. OUTR(INR x:'a+'b) = x`--),
   let val inst = INST_TYPE [Type.gamma |-> Type.beta] sum_axiom
       val spec = SPECL [--`\x:'a.@y:'b.F`--,  --`\y:'b.y`--] inst
       val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
       val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth
   in
   STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] (BETA_RULE conv)) THEN
   EXISTS_TAC (--`h:'a+'b->'b`--) THEN ASM_REWRITE_TAC []
   end);

(* Then define OUTR with a constant specification.			*)
val OUTR = new_specification("OUTR", ["OUTR"], OUTR_DEF);
val _ = export_rewrites ["OUTR"]



(* ---------------------------------------------------------------------*)
(* Prove the following standard theorems about the sum type.		*)
(*									*)
(*	  	  |- ISL(s) ==> INL (OUTL s)=s				*)
(*		  |- ISR(s) ==> INR (OUTR s)=s				*)
(*	  	  |- !s. ISL s \/ ISR s					*)
(*		  							*)
(* ---------------------------------------------------------------------*)
(* First, get the existence and uniqueness parts of sum_axiom.		*)
(*									*)
(* sum_EXISTS: 								*)
(*   |- !f g. ?h. (!x. h(INL x) = f x) /\ (!x. h(INR x) = g x) 		*)
(*									*)
(* sum_UNIQUE: 								*)
(*   |- !f g x y.							*)
(*       ((!x. x(INL x) = f x) /\ (!x. x(INR x) = g x)) /\		*)
(*       ((!x. y(INL x) = f x) /\ (!x. y(INR x) = g x)) ==>		*)
(*       (!s. x s = y s)						*)
(* ---------------------------------------------------------------------*)

(* GEN_ALL gives problems, so changed to be more precise. kls.          *)
val [sum_EXISTS,sum_UNIQUE] =
   let val cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom
       val rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv)
       val [a,b] = CONJUNCTS (CONV_RULE EXISTS_UNIQUE_CONV rew)
   in
   map (GENL  [--`f :'a -> 'c`--, --`g :'b -> 'c`--])
       [ a, BETA_RULE (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) b) ]
   end;

(* Prove that: !x. ISL(x) \/ ISR(x)					*)
val ISL_OR_ISR = store_thm("ISL_OR_ISR",
    --`!x:('a,'b)sum. ISL(x) \/ ISR(x)`--,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`x:('a,'b)sum`--) sum_CASES) THEN
    ASM_REWRITE_TAC [ISL,ISR]);

(* Prove that: |- !x. ISL(x) ==> INL (OUTL x) = x			*)
val INL = store_thm("INL",
    --`!x:('a,'b)sum. ISL(x) ==> (INL (OUTL x) = x)`--,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`x:('a,'b)sum`--) sum_CASES) THEN
    ASM_REWRITE_TAC [ISL,OUTL]);
val _ = export_rewrites ["INL"]

(* Prove that: |- !x. ISR(x) ==> INR (OUTR x) = x			*)
val INR = store_thm("INR",
    --`!x:('a,'b)sum. ISR(x) ==> (INR (OUTR x) = x)`--,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`x:('a,'b)sum`--) sum_CASES) THEN
    ASM_REWRITE_TAC [ISR,OUTR]);
val _ = export_rewrites ["INR"]

val [sum_case_def] = Prim_rec.define_case_constant sum_Axiom
val _ = export_rewrites ["sum_case_def"]

val sum_case_cong = save_thm("sum_case_cong",
                             Prim_rec.case_cong_thm sum_CASES sum_case_def);


(* ----------------------------------------------------------------------
    SUM_MAP
   ---------------------------------------------------------------------- *)

val SUM_MAP_def = Prim_rec.new_recursive_definition{
  name = "SUM_MAP_def",
  def = ``(($++ f g) (INL (a:'a)) = INL ((f a):'c)) /\
          (($++ f g) (INR (b:'b)) = INR ((g b):'d))``,
  rec_axiom = sum_Axiom};
val _ = set_fixity "++" (Infixl 480)
val _ = export_rewrites ["SUM_MAP_def"]

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

val SUM_MAP_I = store_thm (
  "SUM_MAP_I",
  ``(I ++ I) = (I : 'a + 'b -> 'a + 'b)``,
  SIMP_TAC (srw_ss()) [FORALL_SUM, FUN_EQ_THM]);

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

val _ = computeLib.add_persistent_funs ["sum_case_def", "INL_11", "INR_11",
                                        "sum_distinct", "sum_distinct1",
                                        "OUTL", "OUTR", "ISL", "ISR"]

local open OpenTheoryMap
val ns = ["Data","Sum"]
fun add x y = OpenTheory_const_name{const={Thy="sum",Name=x},name=(ns,y)} in
val _ = OpenTheory_tyop_name{tyop={Thy="sum",Tyop="sum"},name=(ns,"+")}
val _ = add "INR" "right"
val _ = add "INL" "left"
val _ = add "OUTR" "destRight"
val _ = add "OUTL" "destLeft"
end

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME(fn ppstrm =>
   let val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
   in
      S "val _ = TypeBase.write";                           NL();
      S "  [TypeBasePure.mk_datatype_info";                 NL();
      S "     {ax=TypeBasePure.ORIG sum_Axiom,";            NL();
      S "      case_def=sum_case_def,";                     NL();
      S "      case_cong=sum_case_cong,";                   NL();
      S "      induction=TypeBasePure.ORIG sum_INDUCT,";    NL();
      S "      nchotomy=sum_CASES,";                        NL();
      S "      size=NONE,";                                 NL();
      S "      encode=NONE,";                               NL();
      S "      fields=[],";                                 NL();
      S "      accessors=[],";                              NL();
      S "      updates=[],";                                NL();
      S "      recognizers=[ISL,ISR],";                     NL();
      S "      destructors=[OUTL,OUTR],";                   NL();
      S "      lift=SOME(mk_var(\"sumSyntax.lift_sum\",Parse.Type`:'type -> ('a -> 'term) -> ('b -> 'term) -> ('a,'b)sum -> 'term`)),";
      S "      one_one=SOME INR_INL_11,";                   NL();
      S "      distinct=SOME sum_distinct}];";              NL()
   end)};

val _ = TypeBase.write
  [TypeBasePure.mk_datatype_info
     {ax=TypeBasePure.ORIG sum_Axiom,
      case_def=sum_case_def,
      case_cong=sum_case_cong,
      induction=TypeBasePure.ORIG sum_INDUCT,
      nchotomy=sum_CASES,
      size=NONE,
      encode=NONE,
      fields=[], accessors=[], updates=[],
      recognizers = [ISL,ISR],
      destructors = [OUTL,OUTR],
      lift=SOME(mk_var("sumSyntax.lift_sum",
                       Parse.Type`:'type -> ('a -> 'term) ->
                                            ('b -> 'term) -> ('a,'b)sum -> 'term`)),
      one_one=SOME INR_INL_11,
      distinct=SOME sum_distinct}];

val _ = export_theory();

end
