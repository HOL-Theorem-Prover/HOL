(* ===================================================================== *)
(* FILE          : mk_.sml                                               *)
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

open HolKernel Parse basicHol90Lib;
infix THEN THENL ORELSEC THENC |->;

type thm = Thm.thm;

val _ = new_theory "sum";

val o_DEF = combinTheory.o_DEF
and o_THM = combinTheory.o_THM;


(* ---------------------------------------------------------------------*)
(* Introduce the new type.						*)
(* ---------------------------------------------------------------------*)

(* The sum of types `:'a` and `:'b` will be represented by a certain	*)
(* subset of type `:bool->'a->'b->bool`.  A left injection of value     *)
(* `p:'a` will be represented by:  `\b x y. x=p /\ b`. A right injection*)
(* of value `q:'b` will be represented by:  `\b x y. x=q /\ ~b`.        *)
(* The predicate IS_SUM_REP is true of just those objects of the type	*)
(* `:bool->'a->'b->bool` which are representations of some injection.	*)
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

val sum_TY_DEF = new_type_definition
    {name = "sum", 
     pred = --`IS_SUM_REP:(bool -> 'a -> 'b -> bool) -> bool`--,
     inhab_thm = EXISTS_SUM_REP};

(* Define a representation function, REP_sum, from the type ( 'a,'b )sum to *)
(* the representing type bool->'a->'b->bool, and the inverse abstraction    *)
(* function ABS_sum, and prove some trivial lemmas about them.              *)
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
val INL_11 = TAC_PROOF(([], 
   --`(INL x = ((INL y):('a,'b)sum)) = (x = y)`--),
   EQ_TAC THENL
   [PURE_REWRITE_TAC [R_11,REP_INL] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (ACCEPT_TAC o SIMP o SPECL [--`T`--,--`x:'a`--,--`y:'b`--]),
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

(* Prove that INR is one-to-one						*)
val INR_11 = TAC_PROOF(([],
   --`(INR x = (INR y:('a,'b)sum)) = (x = y)`--),
   EQ_TAC THENL
   [PURE_REWRITE_TAC [R_11,REP_INR] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (ACCEPT_TAC o SYM o SIMP o SPECL[--`F`--,--`x:'a`--,--`y:'b`--]),
   DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val INR_INL_11 = save_thm("INR_INL_11",
CONJ (GEN_ALL INL_11) (GEN_ALL INR_11));

(* Prove that left injections and right injections are not equal.	*)
val INR_neq_INL = store_thm("INR_neq_INL",
   --`!v1 v2. ~(INR v2 :('a,'b)sum = INL v1)`--,
   PURE_REWRITE_TAC [R_11,REP_INL,REP_INR] THEN
   REPEAT GEN_TAC THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   DISCH_THEN (CONTR_TAC o SIMP o SPECL [--`T`--,--`v1:'a`--,--`v2:'b`--]));

(* Prove a little lemma about epsilon-terms.				*)
val EPS_lemma = TAC_PROOF(([],
   --`(@x:'a. y=x) = y`--),
   CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN 
   EXISTS_TAC (--`y:'a`--) THEN 
   REFL_TAC);

(* The abstract `axiomatization` of the sum type consists of the single	*)
(* theorem given below:							*)
(*									*)
(* sum_axiom    |- !f g. ?!h. (h o INL = f) /\ (h o INR = g)		*)
(*									*)
(* The definitions of the usual operators ISL, OUTL, etc. follow from 	*)
(* this axiom.								*)
val sum_axiom = store_thm("sum_axiom",
    --`!(f:'a->'c).
       !(g:'b->'c). 
       ?!h. ((h o INL) = f) /\ ((h o INR) = g)`--,
PURE_REWRITE_TAC [boolTheory.EXISTS_UNIQUE_DEF,o_DEF] THEN
CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC FUN_EQ_CONV)) THEN
REPEAT (FILTER_STRIP_TAC (--`x:('a,'b)sum->'c`--)) THENL
[EXISTS_TAC (--`\(x:('a,'b)sum).((?v1. x = INL v1) => 
                                f(@v1.x = INL v1) | 
				g(@v2.x = INR v2)):'c`--) THEN
 PURE_REWRITE_TAC [boolTheory.EXISTS_DEF] THEN
 CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
 REWRITE_TAC [INL_11,INR_11,INR_neq_INL,EPS_lemma],
 REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC 
 (REWRITE1_TAC o (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)))) THEN
 REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (SPEC (--`s:('a,'b)sum`--) A_ONTO) THEN
 ASM_REWRITE_TAC (map (SYM o SPEC_ALL) [INL_DEF,INR_DEF])]);


(* ---------------------------------------------------------------------*)
(* We also prove a version of sum_axiom which is in a form suitable for *)
(* use with the recursive type definition tools.			*)
(* ---------------------------------------------------------------------*)

val sum_Axiom = store_thm("sum_Axiom", 
   --`!f:'a->'c. 
      !g:'b->'c.
      ?!h. (!x. h(INL x) = f x) /\
           (!y. h(INR y) = g y)`--,
   let val cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom 
       val rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv) 
   in
   MATCH_ACCEPT_TAC rew
   end);


(* ---------------------------------------------------------------------*)
(* The definitions of ISL, ISR, OUTL, OUTR follow.			*)
(* ---------------------------------------------------------------------*)


(* Derive the defining property for ISL.				*)
val ISL_DEF = TAC_PROOF(([], 
--`?ISL. (!x:'a. ISL(INL x)) /\ (!y:'b. ~ISL(INR y))`--),
   let val inst = INST_TYPE [{redex = ==`:'c`==, residue = ==`:bool`==}]
                            sum_axiom
       val spec = SPECL [--`\x:'a.T`--, --`\y:'b.F`--] inst
       val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
       val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth 
   in
   STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] conv) THEN
   EXISTS_TAC (--`h:'a+'b->bool`--) THEN ASM_REWRITE_TAC []
   end);

(* Then define ISL with a constant specification.			*)
val ISL = new_specification
           {name = "ISL",
            consts = [{fixity = Prefix,const_name="ISL"}],
            sat_thm = ISL_DEF};

(* Derive the defining property for ISR.				*)
val ISR_DEF = TAC_PROOF(([], 
--`?ISR. (!x:'b. ISR(INR x)) /\ (!y:'a. ~ISR(INL y))`--),
   let val inst = INST_TYPE [{redex = ==`:'c`==, residue = ==`:bool`==}]
                            sum_axiom
       val spec = SPECL [--`\x:'a.F`--,  --`\y:'b.T`--] inst
       val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
       val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth 
   in
   STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] conv) THEN
   EXISTS_TAC (--`h:'a+'b->bool`--) THEN ASM_REWRITE_TAC []
   end);

(* Then define ISR with a constant specification.			*)
val ISR = new_specification
          {name = "ISR",
           consts = [{fixity=Prefix,const_name="ISR"}],
           sat_thm = ISR_DEF};

(* Derive the defining property of OUTL.				*)
val OUTL_DEF = TAC_PROOF(([], 
--`?OUTL. !x. OUTL(INL x:('a,'b)sum) = x`--),
   let val inst = INST_TYPE [==`:'c`== |-> ==`:'a`==] sum_axiom
       val spec = SPECL [--`\x:'a.x`--, --`\y:'b.@x:'a.F`--] inst
       val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
       val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth
   in
   STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] (BETA_RULE conv)) THEN
   EXISTS_TAC (--`h:'a+'b->'a`--) THEN ASM_REWRITE_TAC []
   end);

(* Then define OUTL with a constant specification.			*)
val OUTL = new_specification
            {name = "OUTL",
             consts = [{fixity = Prefix,const_name = "OUTL"}],
             sat_thm = OUTL_DEF};

(* Derive the defining property of OUTR.				*)
val OUTR_DEF = TAC_PROOF(([],
--`?OUTR. !x. OUTR(INR x:'a+'b) = x`--),
   let val inst = INST_TYPE [{redex = ==`:'c`==, residue = ==`:'b`==}]
                            sum_axiom
       val spec = SPECL [--`\x:'a.@y:'b.F`--,  --`\y:'b.y`--] inst
       val exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec)
       val conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth 
   in
   STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] (BETA_RULE conv)) THEN
   EXISTS_TAC (--`h:'a+'b->'b`--) THEN ASM_REWRITE_TAC []
   end);

(* Then define OUTR with a constant specification.			*)
val OUTR = new_specification
            {name = "OUTR",
             consts = [{fixity = Prefix,const_name = "OUTR"}],
             sat_thm = OUTR_DEF};



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

(* GEN_ALL gives problems, so changed to be more precise. kls.          *)
val [sum_EXISTS,sum_UNIQUE] = 
   let val cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom
       val rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv)
       val [a,b] = CONJUNCTS (CONV_RULE EXISTS_UNIQUE_CONV rew)
   in
   map (GENL  [--`f :'a -> 'c`--, --`g :'b -> 'c`--])
       [ a, BETA_RULE (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) b) ]
   end;

(* Prove the following key lemma by contradiction.			*)

val sum_lemma = 
   let val lemma = TAC_PROOF (([],
       --`~~!(v:'a+'b). (?x. v = INL x) \/ (?x. v = INR x)`--),
       CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
       PURE_REWRITE_TAC [DE_MORGAN_THM] THEN
       DISCH_THEN (STRIP_ASSUME_TAC o 
                   (CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV))) THEN
       MP_TAC (SPECL [--`\x:'a.T`--, --`\x:'b.F`--,
	              --`\v':('a,'b)sum. ((v = v') => T | ISL v')`--,
		      --`ISL:('a,'b)sum->bool`--] 
		       (INST_TYPE [{redex = ==`:'c`==, residue = ==`:bool`==}]
                                  sum_UNIQUE)) THEN
        MP_TAC (SPECL [--`\x:'a.T`--,  --`\x:'b.F`--,
		       --`\v':('a,'b)sum. ((v = v') => F | ISL v')`--,
		       --`ISL:('a,'b)sum->bool`--] 
		       (INST_TYPE [Type`:'c` |-> Type.bool] sum_UNIQUE)) THEN
        CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC [ISR,ISL] THEN
        DISCH_THEN (fn th => PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL th)]) THEN
        DISCH_THEN (MP_TAC o SPEC (--`v :'a + 'b`--)) THEN
        REWRITE_TAC[])
   in
   REWRITE_RULE [] lemma
   end;

(* Prove that: !x. ISL(x) \/ ISR(x)					*)
val ISL_OR_ISR = store_thm("ISL_OR_ISR",
    --`!x:('a,'b)sum. ISL(x) \/ ISR(x)`--,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`x:('a,'b)sum`--) sum_lemma) THEN
    ASM_REWRITE_TAC [ISL,ISR]);

(* Prove that: |- !x. ISL(x) ==> INL (OUTL x) = x			*)
val INL = store_thm("INL",
    --`!x:('a,'b)sum. ISL(x) ==> (INL (OUTL x) = x)`--,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`x:('a,'b)sum`--) sum_lemma) THEN
    ASM_REWRITE_TAC [ISL,OUTL]);

(* Prove that: |- !x. ISR(x) ==> INR (OUTR x) = x			*)
val INR = store_thm("INR",
    --`!x:('a,'b)sum. ISR(x) ==> (INR (OUTR x) = x)`--,
    STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`x:('a,'b)sum`--) sum_lemma) THEN
    ASM_REWRITE_TAC [ISR,OUTR]);

val _ = export_theory();

end;
