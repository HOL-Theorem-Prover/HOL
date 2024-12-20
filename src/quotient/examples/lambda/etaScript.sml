open HolKernel Parse boolLib;

val _ = new_theory "eta";


(* In interactive sessions, do:

app load ["pairTheory",
          "listTheory", "listLib", "numTheory", "numLib",
          "pred_setTheory", "pred_setLib",
          "MutualIndThen", "bossLib", "relationTheory",
          "ind_rel", "dep_rewrite", "quotient",
          "more_listTheory", "more_setTheory", "variableTheory",
          "termTheory", "alphaTheory", "liftTheory",
          "barendregt", "reductionTheory", "betaTheory"
         ];

*)

open prim_recTheory pairTheory listTheory rich_listTheory;
open combinTheory;
open listLib;
open pred_setTheory pred_setLib;
open numTheory;
open numLib;
open arithmeticTheory;
open bossLib;
open relationTheory;
open Mutual;
open ind_rel;
open dep_rewrite;
open quotient;
open more_listTheory;
open more_setTheory;
open variableTheory;
open termTheory;
open alphaTheory;
open liftTheory;
open barendregt;
open reductionTheory;
open betaTheory;


open tactics;


val term = ty_antiq ( ==`:'a term`== );
val subs = ty_antiq ( ==`:(var # 'a term) list`== );
val term_rel = ty_antiq ( ==`:'a term -> 'a term -> bool`== );


(* Reflexive closure of a relation. *)
(* copied from relationScript.sml: *)

val RC_INDUCT_TAC =
 let val rc_thm = RC_INDUCT
     fun tac (asl,w) =
      let open Rsyntax
          val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
          val (RC,Ru'v') = strip_comb ant
          val R = hd Ru'v'
          val u'v' = tl Ru'v'
          val u' = hd u'v'
          val v' = hd (tl u'v')
          (*val (RC,[R,u',v']) = strip_comb ant*)
          (*val {Name = "RC",...} = dest_const RC*)
          val _ = if #Name(dest_const RC) = "RC" then true else raise Match
          val _ = assert (aconv u) u'
          val _ = assert (aconv v) v'
          val P = list_mk_abs([u,v], conseq)
          val rc_thm' = BETA_RULE(ISPEC P (ISPEC R rc_thm))
      in MATCH_MP_TAC rc_thm' (asl,w)
      end
      handle _ => raise mk_HOL_ERR "<top-level>" "RC_INDUCT_TAC"
        "Unanticipated term structure"
 in tac
 end;

(* Also see RC_REFLEXIVE, RC_SUBSET, RC_INDUCT, RC_CASES. *)


(* Define the transitive closure of a relation.                          *)
(* Wait, it's already done: see file src/relation/relationScript.sml.    *)
(* This defines TC in the logic as TC R is the transitive closure of R,  *)
(* and "transitive R" as the property that R is transitite on 'a.        *)
(* There are also a bunch of theorems in structure TCScript, as well as  *)
(* induction tactics, cases theorems, etc.  It's theory "TC".            *)

(* copied: *)

val TC_INDUCT_TAC =
 let val tc_thm = TC_INDUCT
     fun tac (asl,w) =
      let open Rsyntax
          val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
          val (TC,Ru'v') = strip_comb ant
          val R = hd Ru'v'
          val u'v' = tl Ru'v'
          val u' = hd u'v'
          val v' = hd (tl u'v')
          (*val (TC,[R,u',v']) = strip_comb ant*)
          (*val {Name = "TC",...} = dest_const TC*)
          val _ = if #Name(dest_const TC) = "TC" then true else raise Match
          val _ = assert (aconv u) u'
          val _ = assert (aconv v) v'
          val P = list_mk_abs([u,v], conseq)
          val tc_thm' = BETA_RULE(ISPEC P (ISPEC R tc_thm))
      in MATCH_MP_TAC tc_thm' (asl,w)
      end
      handle _ => raise mk_HOL_ERR "<top-level>" "TC_INDUCT_TAC"
                     "Unanticipated term structure"
 in tac
 end;

val TC_TRANS = REWRITE_RULE[transitive_def] TC_TRANSITIVE;
(* Also see TC_SUBSET, TC_CASES1, TC_CASES2, TC_RC_RED1_IS_RED, TC_MONOTONIC *)



(* --------------------------------------------------------------------- *)
(* Definition of the relation of eta reduction.                          *)
(* This is simple, but we define it by rule induction.                   *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* (ETA_R t1 t2) means that the term t1 reduces entirely to the term t2  *)
(* in exactly one eta-reduction step, as defined in Barendregt,          *)
(* Section 3.3.1, page 63.   Note that this is true ONLY on t1 of        *)
(* the form (Lam x (App t (Var x))).                                     *)
(* --------------------------------------------------------------------- *)


val ETA_R =
“ETA_R : ^term_rel”;

val ETA_R_patterns = [“^ETA_R t1 t2”];

val ETA_R_rules_tm =
“                    (~(x IN FV t)
       (* -------------------------------------------- *) ==>
              (^ETA_R (Lam x (App t (Var x))) t))
”;

val (ETA_R_rules_sat,ETA_R_ind_thm) =
    define_inductive_relations ETA_R_patterns ETA_R_rules_tm;

val ETA_R_inv_thms = prove_inversion_theorems
    ETA_R_rules_sat ETA_R_ind_thm;

val ETA_R_strong_ind = prove_strong_induction
    ETA_R_rules_sat ETA_R_ind_thm;

val _ = save_thm ("ETA_R_rules_sat", ETA_R_rules_sat);
val _ = save_thm ("ETA_R_ind_thm", ETA_R_ind_thm);
val _ = save_thm ("ETA_R_inv_thms", LIST_CONJ ETA_R_inv_thms);
val _ = save_thm ("ETA_R_strong_ind", ETA_R_strong_ind);




(* --------------------------------------------------------------------- *)
(* We claim that ETA_R is a binary relation on the lambda calculus       *)
(* language which is                                                     *)
(*  1) a notion of reduction on the sigma calculus, in the sense of      *)
(*     Berendregt, Definition 3.1.2, pg 51 (trivial, since a relation)   *)
(*  2) deterministic                                                     *)
(* --------------------------------------------------------------------- *)


(* ETA_R is a deterministic relation. *)

val ETA_R_deterministic = store_thm
   ("ETA_R_deterministic",
    “!t:^term u1 u2.
         ETA_R t u1 /\ ETA_R t u2 ==> (u1 = u2)”,
    REWRITE_TAC ETA_R_inv_thms
    THEN REPEAT STRIP_TAC
    THEN UNDISCH_TAC ``(t:^term) = Lam x' (App u2 (Var x'))``
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[Lam_one_one]
    THEN REWRITE_TAC[SUB_term]
    THEN REWRITE_TAC[SUB]
    THEN REWRITE_TAC[term_one_one]
    THEN REWRITE_TAC[GSYM Lam_one_one]
    THEN STRIP_TAC
    THEN IMP_RES_TAC SUB_RENAME_TERM
    THEN POP_ASSUM (MP_TAC o SPEC “Var x:^term”)
    THEN IMP_RES_THEN REWRITE_THM subst_EMPTY
   );

(* Note that ETA_R is not reflexive, symmetric, or transitive. *)

(* ETA_R is monotonically decreasing with respect to free variables. *)

val ETA_FV = store_thm
   ("ETA_FV",
    “!t1:^term t2. ETA_R t1 t2 ==>
                           (FV t2 SUBSET FV t1)”,
    rule_induct ETA_R_strong_ind
    THEN REWRITE_TAC[FV_term]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUBSET_DEF]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC IN_NOT_IN
    THEN REWRITE_TAC[IN_UNION,IN_DIFF]
    THEN ASM_REWRITE_TAC[IN]
   );



(* --------------------------------------------------------------- *)
(* If substituting one variable for another across a term does not *)
(* change the term, then either the variables were the same, or    *)
(* the substitution never happened because the target variable did *)
(* not appear free in the term.                                    *)
(* --------------------------------------------------------------- *)

val SUBST_IS_SAME = store_thm
   ("SUBST_IS_SAME",
    “!t:^term x y. ((t <[ [x,Var y]) = t) ==>
                      ((x = y) \/ ~(x IN FV t))”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL (* 4 subgoals *)
      [ REWRITE_TAC[SUB_term,term_one_one,FV_term,IN],

        REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THENL
          [ REWRITE_TAC[term_one_one]
            THEN DISCH_TAC
            THEN ASM_REWRITE_TAC[],

            REWRITE_TAC[FV_term,IN]
            THEN FIRST_ASSUM (REWRITE_THM o GSYM)
          ],

        REWRITE_TAC[SUB_term,term_one_one,FV_term,IN_UNION]
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[term_one_one,FV_term,IN_DIFF,IN]
        THEN REWRITE_TAC[GSYM (ASSUME “~((z:var) = x')”)]
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


(* -------------------------------------------------------------------- *)
(* The following is remarkably simple, given that Lam x u = Lam x' u'   *)
(* for many choices of x', u'.                                          *)
(* -------------------------------------------------------------------- *)

Theorem ETA_R_equals :
   (!x t:^term. ETA_R (Var x) t = F) /\
   (!t u t':^term. ETA_R (App t u) t' = F) /\
   (!x u t:^term. ETA_R (Lam x u) t <=> ~(x IN FV t) /\ (u = App t (Var x)))
Proof
    REWRITE_TAC ETA_R_inv_thms
    THEN REWRITE_TAC[term_distinct,term_one_one]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ IMP_RES_TAC Lam_one_one
        THEN POP_ASSUM (REWRITE_ALL_THM o SYM)
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[SUB_term]
        THEN IMP_RES_THEN REWRITE_THM subst_EMPTY
        THEN REWRITE_TAC[SUB_term,SUB]
        THEN REWRITE_TAC[term_one_one]
        THEN DISCH_TAC
        THEN IMP_RES_TAC SUBST_IS_SAME
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “x:var”
        THEN ASM_REWRITE_TAC[]
      ]
QED


(* --------------------------------------------------------------------- *)
(* Now we claim that using the results of theory "reduction", that       *)
(* 1) RED1 ETA_R, RED ETA_R, and REQ ETA_R are compatible,               *)
(* 2) RED ETA_R is a reduction relation,                                 *)
(* 3) REQ ETA_R is an equality relation,                                 *)
(* 4) various theorems and relations hold (see the theory "reduction")   *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Now we begin to prove the Church-Rosser theorem for ETA_R.            *)
(* --------------------------------------------------------------------- *)


(* Barendregt Proposition 3.3.3, ETA_R is substitutive. *)

val ETA_R_SUBSTITUTIVE = store_thm
   ("ETA_R_SUBSTITUTIVE",
    “SUBSTITUTIVE (ETA_R:^term_rel)”,
    REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT GEN_TAC
    THEN DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE ETA_R_inv_thms)
    THEN ASM_REWRITE_TAC[]
    THEN DEFINE_NEW_VAR “(Nx:^term) = App N (Var x')”
    THEN FIRST_ASSUM (REWRITE_THM o SYM)
    THEN SIMPLE_SUBST_TAC
    THEN REWRITE_TAC[ETA_R_equals]
    THEN REWRITE_TAC[FV_term_subst]
    THEN DEP_REWRITE_TAC[NOT_IN_FV_subst]
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC Lam_one_one
    THEN POP_TAC
    THEN POP_ASSUM (REWRITE_THM o GSYM)
    THEN ASM_REWRITE_TAC[SUB_term,SUB]
    THEN REWRITE_TAC[term_one_one]
    THEN IMP_RES_THEN REWRITE_THM subst_EMPTY
   );

(* --------------------------------------------------------------- *)
(* Much of the following development could be moved to the theory  *)
(* "reduction", as it is general for all notions of reduction.     *)
(* --------------------------------------------------------------- *)

(* ----------------------------------------------------- *)
(* We define what it means for two relations to commute. *)
(* ----------------------------------------------------- *)

val COMMUTE =
    new_infixl_definition
    ("COMMUTE",
     “$COMMUTE R1 R2  =
         (!a b c:'a. R1 a b /\ R2 a c ==> (?d. R2 b d /\ R1 c d))”,
     250);

(* Define the infix substitution operator, <[, with higher precedence *)
(* than the substitution-creation operator //, but lower than CONS:   *)

val _ = add_infix("<=>",250,LEFT);

(* Now overload the operator <=> to refer to COMMUTE:  *)

val _ = overload_on("<=>",
        “$COMMUTE:('a->'a->bool)->('a->'a->bool)->bool”)
handle e => (Raise e);


(* Now R |= <> iff R <=> R. *)

val DIAMOND_COMMUTES_SELF = store_thm
   ("DIAMOND_COMMUTES_SELF",
    “!R:'a->'a->bool. DIAMOND R = (R <=> R)”,
    REWRITE_TAC[DIAMOND,COMMUTE]
   );


(* ------------------------------------- *)
(* We define the union of two relations. *)
(* ------------------------------------- *)

val UNION_R =
    new_infixl_definition
    ("UNION_R",
     “$UNION_R R1 R2  =
         (\(a:'a) (b:'b). R1 a b \/ R2 a b)”,
     500);

val IN_UNION_R = store_thm
   ("IN_UNION_R",
    “!(R1:'a->'b->bool) R2 x y. (R1 UNION_R R2) x y <=> R1 x y \/ R2 x y”,
    REWRITE_TAC[UNION_R]
    THEN BETA_TAC
    THEN REWRITE_TAC[]
   );


(* --------------------------------------------------------- *)
(* We prove the Hindley-Rosen Lemma on the Diamond property. *)
(* --------------------------------------------------------- *)

val DIAMOND_TC_UNION1 = TAC_PROOF(([],
    “!R1 R2 (a:'a) b. TC (R1 UNION_R R2) a b ==>
          (DIAMOND R1 /\ DIAMOND R2 /\ (R1 <=> R2) ==>
           (!c. (R1 UNION_R R2) a c ==>
               (?d. (R1 UNION_R R2) b d /\ TC (R1 UNION_R R2) c d)))”),
    GEN_TAC
    THEN GEN_TAC
    THEN TC_INDUCT_TAC
    THEN CONJ_TAC
    THENL
      [ REWRITE_TAC[IN_UNION_R]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_ALL_TAC[DIAMOND,COMMUTE]
        THEN RES_TAC
        THEN EXISTS_TAC “d':'a”
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC TC_SUBSET
        THEN REWRITE_TAC[IN_UNION_R]
        THEN ASM_REWRITE_TAC[],

        REPEAT GEN_TAC
        THEN STRIP_TAC
        THEN DISCH_THEN REWRITE_ALL_THM
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC “d':'a”
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC TC_TRANS
     ]
   );

val DIAMOND_TC_UNION2 = TAC_PROOF(([],
    “!R1 R2 (a:'a) b. TC (R1 UNION_R R2) a b ==>
          (DIAMOND R1 /\ DIAMOND R2 /\ (R1 <=> R2) ==>
           (!c. TC (R1 UNION_R R2) a c ==>
               (?d. TC (R1 UNION_R R2) b d /\ TC (R1 UNION_R R2) c d)))”),
    GEN_TAC
    THEN GEN_TAC
    THEN TC_INDUCT_TAC
    THEN CONJ_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN IMP_RES_TAC DIAMOND_TC_UNION1
        THEN EXISTS_TAC “d:'a”
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC TC_SUBSET,

        REPEAT GEN_TAC
        THEN STRIP_TAC
        THEN DISCH_THEN REWRITE_ALL_THM
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC “d':'a”
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC TC_TRANS
     ]
   );

(* -------------------------------------------- *)
(* Hindley-Rosen Lemma on the Diamond property. *)
(* Barendregt Proposition 3.3.5(i) (page 64):   *)
(* -------------------------------------------- *)

val DIAMOND_TC_UNION = store_thm
   ("DIAMOND_TC_UNION",
    “!(R1:'a->'a->bool) R2.
          DIAMOND R1 /\ DIAMOND R2 /\ (R1 <=> R2) ==>
          DIAMOND (TC (R1 UNION_R R2))”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[DIAMOND]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC DIAMOND_TC_UNION2
    THEN EXISTS_TAC ``d'':'a``
    THEN ASM_REWRITE_TAC[]
   );


val RED1_COMPAT = REWRITE_RULE[compatible] RED1_compatible;


(* -------------------------------------------------------------- *)
(* We now prove that the reduction based on a notion which is the *)
(* union of two notions of reduction, is itself a union of the    *)
(* reductions of the two notions.                                 *)
(* -------------------------------------------------------------- *)

val RED1_UNION1 = TAC_PROOF(([],
    “!R1 R2 R t1:^term t2.
             RED1 R t1 t2 ==>
                  (R = R1 UNION_R R2) ==>
                      (RED1 R1 UNION_R RED1 R2) t1 t2”),
    GEN_TAC THEN GEN_TAC
    THEN rule_induct RED1_ind_thm
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN REWRITE_ALL_TAC[IN_UNION_R]
    THEN POP_ASSUM STRIP_ASSUME_TAC
    THEN IMP_RES_TAC RED1_rules_sat
    THEN ASM_REWRITE_TAC[]
   );

val RED1_UNION2 = TAC_PROOF(([],
    “!R2 R1 t1:^term t2. RED1 R1 t1 t2 ==>
                            RED1 (R1 UNION_R R2) t1 t2”),
    GEN_TAC
    THEN rule_induct RED1_ind_thm
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ DEP_REWRITE_TAC[RED1_rules_sat]
        THEN ASM_REWRITE_TAC[IN_UNION_R],

        IMP_RES_TAC RED1_rules_sat
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC RED1_rules_sat
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC RED1_rules_sat
        THEN ASM_REWRITE_TAC[]
      ]
   );

val RED1_UNION3 = TAC_PROOF(([],
    “!R1 R2 t1:^term t2. RED1 R2 t1 t2 ==>
                            RED1 (R1 UNION_R R2) t1 t2”),
    GEN_TAC
    THEN rule_induct RED1_ind_thm
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ DEP_REWRITE_TAC[RED1_rules_sat]
        THEN ASM_REWRITE_TAC[IN_UNION_R],

        IMP_RES_TAC RED1_rules_sat
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC RED1_rules_sat
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC RED1_rules_sat
        THEN ASM_REWRITE_TAC[]
      ]
   );

val RED1_UNION = store_thm
   ("RED1_UNION",
    “!R1:^term_rel R2. RED1 (R1 UNION_R R2) = (RED1 R1 UNION_R RED1 R2)”,
    CONV_TAC (TOP_DEPTH_CONV FUN_EQ_CONV)
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ MATCH_MP_TAC (IMP2AND RED1_UNION1)
        THEN EXISTS_TAC “(R1:^term_rel) UNION_R R2”
        THEN ASM_REWRITE_TAC[],

        POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNION_R])
        THENL
          [ MATCH_MP_TAC RED1_UNION2,
            MATCH_MP_TAC RED1_UNION3
          ]
        THEN FIRST_ASSUM ACCEPT_TAC
      ]
   );

(* --------------------------------------------------------------------- *)
(* The above was for one-step reduction, RED1.  We now prove the         *)
(* corresponding property for the reflexive, transitive closure, RED.    *)
(* --------------------------------------------------------------------- *)

val RED_UNION1 = TAC_PROOF(([],
    “!R1 R2 R t1:^term t2. RED R t1 t2 ==>
                  (R = R1 UNION_R R2) ==>
                      TC (RED R1 UNION_R RED R2) t1 t2”),
    GEN_TAC THEN GEN_TAC
    THEN rule_induct RED_ind_thm
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THEN POP_ASSUM REWRITE_ALL_THM
    THENL
      [ MATCH_MP_TAC TC_SUBSET
        THEN REWRITE_ALL_TAC[RED1_UNION]
        THEN REWRITE_ALL_TAC[IN_UNION_R]
        THEN POP_ASSUM STRIP_ASSUME_TAC
        THEN IMP_RES_TAC RED_rules_sat
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC TC_SUBSET
        THEN REWRITE_TAC[IN_UNION_R]
        THEN REWRITE_TAC[RED_rules_sat],

        IMP_RES_TAC TC_TRANS
      ]
   );

val RED_UNION2 = TAC_PROOF(([],
    “!R2 R1 t1:^term t2. RED R1 t1 t2 ==>
                      RED (R1 UNION_R R2) t1 t2”),
    GEN_TAC
    THEN rule_induct RED_ind_thm
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ DEP_REWRITE_TAC[RED_rules_sat]
        THEN REWRITE_TAC[RED1_UNION]
        THEN ASM_REWRITE_TAC[IN_UNION_R],

        REWRITE_TAC[RED_rules_sat],

        IMP_RES_TAC RED_rules_sat
      ]
   );

val RED_UNION3 = TAC_PROOF(([],
    “!R1 R2 t1:^term t2. RED R2 t1 t2 ==>
                            RED (R1 UNION_R R2) t1 t2”),
    GEN_TAC
    THEN rule_induct RED_ind_thm
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ DEP_REWRITE_TAC[RED_rules_sat]
        THEN REWRITE_TAC[RED1_UNION]
        THEN ASM_REWRITE_TAC[IN_UNION_R],

        REWRITE_TAC[RED_rules_sat],

        IMP_RES_TAC RED_rules_sat
      ]
   );

val RED_UNION4 = TAC_PROOF(([],
    “!R1 R2 t1:^term t2. TC (RED R1 UNION_R RED R2) t1 t2 ==>
                            RED (R1 UNION_R R2) t1 t2”),
    GEN_TAC
    THEN GEN_TAC
    THEN TC_INDUCT_TAC
    THEN CONJ_TAC
    THENL
      [ REWRITE_TAC[IN_UNION_R]
        THEN REPEAT STRIP_TAC
        THENL
          [ MATCH_MP_TAC RED_UNION2,
            MATCH_MP_TAC RED_UNION3
          ]
        THEN FIRST_ASSUM ACCEPT_TAC,

        REPEAT STRIP_TAC
        THEN IMP_RES_TAC RED_rules_sat
     ]
   );

(* Remark of Barendregt at bottom of page 64. *)

val RED_UNION = store_thm
   ("RED_UNION",
    “!R1:^term_rel R2. RED (R1 UNION_R R2) = TC (RED R1 UNION_R RED R2)”,
    CONV_TAC (TOP_DEPTH_CONV FUN_EQ_CONV)
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC RED_UNION1
        THEN POP_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        IMP_RES_TAC RED_UNION4
      ]
   );


(* Barendregt Proposition 3.3.5(ii) (page 64): *)

val COMMUTE_CHURCH_ROSSER = store_thm
   ("COMMUTE_CHURCH_ROSSER",
    “!R1:^term_rel R2.
          CHURCH_ROSSER R1 /\ CHURCH_ROSSER R2 /\
          (RED R1 <=> RED R2) ==>
          CHURCH_ROSSER (R1 UNION_R R2)”,
    REWRITE_TAC[CHURCH_ROSSER]
    THEN REWRITE_TAC[RED_UNION]
    THEN REWRITE_TAC[DIAMOND_TC_UNION]
   );


(* -------------------------------------------------------------- *)
(* We now prove Barendregt's Lemma 3.3.6, as a way to prove that  *)
(* the reflexive, transitive closures of two relations commute.   *)
(* -------------------------------------------------------------- *)

val COMMUTE_TC_RC1 = TAC_PROOF(([],
    “!R2 a b.
          RC R2 a b ==>
          !R1.
          (!a b c:'a. R1 a b /\ R2 a c ==>
                      ?d. TC (RC R2) b d /\ RC R1 c d) ==>
          (!c. R1 a c ==>
                   ?d. RC R1 b d /\ TC (RC R2) c d)”),
    GEN_TAC
    THEN RC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ RES_TAC
        THEN EXISTS_TAC “d:'a”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``c:'a``
        THEN DEP_REWRITE_TAC[TC_SUBSET]
        THEN REWRITE_TAC[RC_REFLEXIVE]
        THEN MATCH_MP_TAC RC_SUBSET
        THEN ASM_REWRITE_TAC[]
      ]
   );

val COMMUTE_TC_RC2 = TAC_PROOF(([],
    “!R1 a b.
          RC R1 a b ==>
          !R2.
          (!a b c:'a. R1 a b /\ R2 a c ==>
                      ?d. TC (RC R2) b d /\ RC R1 c d) ==>
          (!c. RC R2 a c ==>
                   ?d. TC (RC R2) b d /\ RC R1 c d)”),
    GEN_TAC
    THEN RC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC COMMUTE_TC_RC1
        THEN EXISTS_TAC “d:'a”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``c:'a``
        THEN DEP_REWRITE_TAC[TC_SUBSET]
        THEN ASM_REWRITE_TAC[RC_REFLEXIVE]
      ]
   );

val COMMUTE_TC_RC3 = TAC_PROOF(([],
    “!R2 a b.
          TC (RC R2) a b ==>
          !R1.
          (!a b c:'a. R1 a b /\ R2 a c ==>
                      ?d. TC (RC R2) b d /\ RC R1 c d) ==>
          (!c. RC R1 a c ==>
                   ?d. RC R1 b d /\ TC (RC R2) c d)”),
    GEN_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC COMMUTE_TC_RC2
        THEN EXISTS_TAC “d:'a”
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC ``d':'a``
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC TC_TRANS
      ]
   );

val COMMUTE_TC_RC4 = TAC_PROOF(([],
    “!R1 a b.
          TC (RC R1) a b ==>
          !R2.
          (!a b c:'a. R1 a b /\ R2 a c ==>
                      ?d. TC (RC R2) b d /\ RC R1 c d) ==>
          (!c. TC (RC R2) a c ==>
                   ?d. TC (RC R2) b d /\ TC (RC R1) c d)”),
    GEN_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC COMMUTE_TC_RC3
        THEN EXISTS_TAC “d:'a”
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC TC_SUBSET
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC ``d':'a``
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC TC_TRANS
      ]
   );

(* Barendregt Lemma 3.3.6, page 65. *)

val COMMUTE_TC_RC = store_thm
   ("COMMUTE_TC_RC",
    “!R1 R2.
          (!a b c:'a. R1 a b /\ R2 a c ==>
                   ?d. TC (RC R2) b d /\ RC R1 c d) ==>
          (TC (RC R1) <=> TC (RC R2))”,
    REWRITE_TAC[COMMUTE]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC COMMUTE_TC_RC4
    THEN EXISTS_TAC “d:'a”
    THEN ASM_REWRITE_TAC[]
   );


val RED1_ETA_FV  = MATCH_MP RED1_FV ETA_FV;
val RED1_BETA_FV = MATCH_MP RED1_FV BETA_FV;


val RED1_ETA_RENAME = store_thm
   ("RED1_ETA_RENAME",
    “!t1:^term t2 t1' x y.
          RED1 ETA_R t1 t2 /\ (Lam x t1 = Lam y t1') ==>
          (Lam x t2 = Lam y (t2 <[ [x, Var y]))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_ETA_FV
    THEN IMP_RES_TAC LAMBDA_RENAME
   );


val [RED1_R, RED1_App1, RED1_App2, RED1_Lam] = CONJUNCTS RED1_rules_sat;

val RED1_ETA_SUBSTITUTIVE = REWRITE_RULE[SUBSTITUTIVE]
                            (MATCH_MP RED1_SUBSTITUTIVE ETA_R_SUBSTITUTIVE);

(* This is necessary for when we change a bound variable: *)

val RED1_ETA_CHANGE_VAR = store_thm
   ("RED1_ETA_CHANGE_VAR",
    “!t1:^term t2 x y t1'.
           RED1 ETA_R t1 t2 /\ (Lam x t1 = Lam y t1')  ==>
           RED1 ETA_R t1' (t2 <[ [x, Var y])”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
    THEN MATCH_MP_TAC RED1_ETA_SUBSTITUTIVE
    THEN ASM_REWRITE_TAC[]
   );


val RED1_ETA_cases = store_thm
   ("RED1_ETA_cases",
    “(!a t2:^term.
          RED1 ETA_R (Con a) t2 ==> F) /\
        (!x t2:^term.
          RED1 ETA_R (Var x) t2 ==> F) /\
        (!t u t2:^term.
          RED1 ETA_R (App t u) t2 ==>
          ((?t'. RED1 ETA_R t t' /\ (t2 = App t' u)) \/
           (?u'. RED1 ETA_R u u' /\ (t2 = App t u')))) /\
        (!x t t2:^term.
          RED1 ETA_R (Lam x t) t2 ==>
           ((~(x IN FV t2) /\ (t = App t2 (Var x)))) \/
            (?t'. RED1 ETA_R t t' /\ (t2 = Lam x t')))”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[term_distinct,term_one_one] o
            ONCE_REWRITE_RULE[RED1_inv_thms])
    THENL (* 7 subgoals *)
      [ UNDISCH_LAST_TAC
        THEN REWRITE_TAC ETA_R_inv_thms
        THEN REWRITE_TAC[term_distinct],

        UNDISCH_LAST_TAC
        THEN REWRITE_TAC ETA_R_inv_thms
        THEN REWRITE_TAC[term_distinct],

        UNDISCH_LAST_TAC
        THEN REWRITE_TAC ETA_R_inv_thms
        THEN REWRITE_TAC[term_distinct],

        DISJ1_TAC
        THEN EXISTS_TAC “t2':^term”
        THEN ASM_REWRITE_TAC[],

        DISJ2_TAC
        THEN EXISTS_TAC “u2:^term”
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC ETA_R_equals
        THEN ASM_REWRITE_TAC[],

        DISJ2_TAC
        THEN EXISTS_TAC “(t2':^term) <[ [x', Var x]”
        THEN ASSUM_LIST (ASSUME_TAC o SYM o hd o rev)
        THEN IMP_RES_THEN IMP_RES_TAC RED1_ETA_RENAME
        THEN IMP_RES_TAC RED1_ETA_CHANGE_VAR
        THEN ASM_REWRITE_TAC[]
      ]
   );

val [RED1_ETA_Con_case, RED1_ETA_Var_case,
     RED1_ETA_App_case, RED1_ETA_Lam_case]
    = CONJUNCTS RED1_ETA_cases;

val RED1_ETA_App_Var_case = store_thm
   ("RED1_ETA_App_Var_case",
    “!t x t2:^term.
          RED1 ETA_R (App t (Var x)) t2 ==>
          (?t'. RED1 ETA_R t t' /\ (t2 = App t' (Var x)))”,
    REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[term_distinct,term_one_one] o
            ONCE_REWRITE_RULE[RED1_inv_thms])
    THENL (* 3 subgoals *)
      [ UNDISCH_LAST_TAC
        THEN REWRITE_TAC[ETA_R_equals],

        EXISTS_TAC “t2':^term”
        THEN ASM_REWRITE_TAC[],

        UNDISCH_LAST_TAC
        THEN POP_TAC
        THEN POP_ASSUM (REWRITE_THM o SYM)
        THEN DISCH_TAC
        THEN IMP_RES_TAC RED1_ETA_Var_case
      ]
   );


val RC_RED1_COMPAT    = REWRITE_RULE[compatible] RC_RED1_compatible;
val TC_RC_RED1_COMPAT = REWRITE_RULE[compatible] TC_RC_RED1_compatible;


(* RC -->eta satisfies the diamond property. *)

(* Barendregt Lemma 3.3.7, page 65. *)

val DIAMOND_RED1_ETA_LEMMA = store_thm
   ("DIAMOND_RED1_ETA_LEMMA",
    “!R (M:^term) M1. RED1 R M M1 ==>
          !M2. RED1 ETA_R M M2 /\ (R = ETA_R) ==>
              ?M3. RC (RED1 ETA_R) M1 M3 /\ RC (RED1 ETA_R) M2 M3”,
    rule_induct RED1_strong_ind
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THEN POP_ASSUM REWRITE_ALL_THM
    THENL
      [ (* Case 1: M --> M1 is \x.Px --> P, and M=t1, M1 = P = t2. *)
        IMP_RES_TAC (hd ETA_R_inv_thms)
        THEN UNDISCH_LAST_TAC
        THEN POP_ASSUM REWRITE_ALL_THM
        THEN IMP_RES_TAC RED1_ETA_Lam_case
        THENL
          [ (* Case 1.1: M2 = t2 (= M1). *)
            POP_ASSUM (REWRITE_ALL_THM o REWRITE_RULE[term_one_one])
            THEN STRIP_TAC
            THEN EXISTS_TAC ``M2:^term``
            THEN REWRITE_TAC[RC_REFLEXIVE],

            (* Case 1.2: M2 = \x.t' = \x.P'x and P --> P'. *)
            IMP_RES_TAC RED1_ETA_App_Var_case  (* t'' = P'. *)
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN DISCH_TAC
            THEN EXISTS_TAC ``t'':^term``  (* Take M3 = P'. *)
            THEN DEP_REWRITE_TAC[RC_SUBSET]
            THEN ASM_REWRITE_TAC[]
            THEN MATCH_MP_TAC RED1_R
            THEN MATCH_MP_TAC ETA_R_rules_sat
            THEN IMP_RES_THEN MATCH_MP_TAC NOT_IN_SUBSET
            THEN IMP_RES_TAC RED1_ETA_FV
          ],

        (* Case 3: M --> M1 is PZ --> P'Z and is conseq of P --> P'. *)
        (*         P = t1, Z = u, P' = t2.  *)
        IMP_RES_TAC RED1_ETA_App_case
        THENL
          [ (* Case 3.1: P --> P'', M2 = P''Z.  P'' = t'. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN RES_TAC
            (* By ind. hyp, ?P'''. P' -->= P''' /\ P'' -->= P'''.
                            P''' appears as M3. *)
            THEN EXISTS_TAC ``App M3 u:^term``  (* Take M3 = P'''Z. *)
            THEN IMP_RES_THEN REWRITE_THM RC_RED1_COMPAT,

            (* Case 3.2: Z --> Z', M2 = P'Z'.  Z' = u'. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``App t2 u':^term``  (* Take M3 = P'Z'. *)
            THEN DEP_REWRITE_TAC[RC_SUBSET]
            THEN IMP_RES_THEN REWRITE_THM RED1_COMPAT
          ],

        (* Case 2: M --> M1 is ZP --> ZP' and is conseq of P --> P'. *)
        (*         Z = t, P = u1, P' = u2.  *)
        IMP_RES_TAC RED1_ETA_App_case
        THENL
          [ (* Case 2.1: Z --> Z', M2 = Z'P'.  Z' = t'. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``App t' u2:^term``  (* Take M3 = Z'P'. *)
            THEN DEP_REWRITE_TAC[RC_SUBSET]
            THEN IMP_RES_THEN REWRITE_THM RED1_COMPAT,

            (* Case 2.2: P --> P'', M2 = ZP''.  P'' = u'. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN RES_TAC
            (* By ind. hyp, ?P'''. P' -->= P''' /\ P'' -->= P'''.
                            P''' appears as M3. *)
            THEN EXISTS_TAC ``App t M3:^term``  (* Take M3 = ZP'''. *)
            THEN IMP_RES_THEN REWRITE_THM RC_RED1_COMPAT
          ],

        (* Case 4: M --> M1 is \x.P --> \x.P' and is conseq of P --> P'. *)
        (*         P = t1, P' = t2.  *)
        IMP_RES_TAC RED1_ETA_Lam_case
        THENL
          [ (* Case 4.2: P = P0 x, P0=M2, and so M --> M2 is \x.P0 x --> P0. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN IMP_RES_TAC RED1_ETA_App_Var_case  (* t' = P0'. *)
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``t':^term``  (* Take M3 = P0'. *)
            THEN DEP_REWRITE_TAC[RC_SUBSET]
            THEN ASM_REWRITE_TAC[]
            THEN MATCH_MP_TAC RED1_R
            THEN MATCH_MP_TAC ETA_R_rules_sat
            THEN IMP_RES_THEN MATCH_MP_TAC NOT_IN_SUBSET
            THEN MATCH_MP_TAC RED1_ETA_FV
            THEN ASM_REWRITE_TAC[],

            (* Case 4.1: M2 = \x.P'' with P --> P''.  P'' = t'. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN RES_TAC
            (* By ind. hyp, ?P'''. P' -->= P''' /\ P'' -->= P'''.
                            P''' appears as M3. *)
            THEN EXISTS_TAC ``Lam x M3:^term``  (* Take M3 = \x.P'''. *)
            THEN IMP_RES_THEN REWRITE_THM RC_RED1_COMPAT
          ]
      ]
   );

val DIAMOND_RED1_ETA_LEMMA1 =
    REWRITE_RULE[] (SPEC ``ETA_R:^term_rel`` DIAMOND_RED1_ETA_LEMMA);

val DIAMOND_RC_RED1_ETA1 = TAC_PROOF(([],
    “!(M:^term) M1.
          RC (RED1 ETA_R) M M1 ==>
          !M2. RED1 ETA_R M M2 ==>
          ?M3. RC (RED1 ETA_R) M1 M3 /\ RC (RED1 ETA_R) M2 M3”),
    RC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC DIAMOND_RED1_ETA_LEMMA1
        THEN EXISTS_TAC “M3':^term”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``M2:^term``
        THEN REWRITE_TAC[RC_REFLEXIVE]
        THEN MATCH_MP_TAC RC_SUBSET
        THEN ASM_REWRITE_TAC[]
      ]
   );

val DIAMOND_RC_RED1_ETA2 = TAC_PROOF(([],
    “!(M:^term) M1.
          RC (RED1 ETA_R) M M1 ==>
          !M2. RC (RED1 ETA_R) M M2 ==>
          ?M3. RC (RED1 ETA_R) M1 M3 /\ RC (RED1 ETA_R) M2 M3”),
    RC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC DIAMOND_RC_RED1_ETA1
        THEN EXISTS_TAC “M3:^term”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``M2:^term``
        THEN ASM_REWRITE_TAC[RC_REFLEXIVE]
      ]
   );

val DIAMOND_RC_RED1_ETA_LEMMA = store_thm
   ("DIAMOND_RC_RED1_ETA_LEMMA",
    “!(M:^term) M1 M2.
          RC (RED1 ETA_R) M M1 /\ RC (RED1 ETA_R) M M2 ==>
          ?M3. RC (RED1 ETA_R) M1 M3 /\ RC (RED1 ETA_R) M2 M3”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC DIAMOND_RC_RED1_ETA2
    THEN EXISTS_TAC “M3':^term”
    THEN ASM_REWRITE_TAC[]
   );

val DIAMOND_RC_RED1_ETA = store_thm
   ("DIAMOND_RC_RED1_ETA",
    “DIAMOND (RC (RED1 (ETA_R:^term_rel)))”,
    REWRITE_TAC[DIAMOND]
    THEN REWRITE_TAC[DIAMOND_RC_RED1_ETA_LEMMA]
   );



val ETA_R_CHURCH_ROSSER = store_thm
   ("ETA_R_CHURCH_ROSSER",
    “CHURCH_ROSSER (ETA_R:^term_rel)”,
    REWRITE_TAC[CHURCH_ROSSER]
    THEN REWRITE_TAC[GSYM TC_RC_RED1_IS_RED]
    THEN MATCH_MP_TAC TC_DIAMOND
    THEN REWRITE_TAC[DIAMOND_RC_RED1_ETA]
   );



val [RED_RED1, RED_REFL, RED_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) RED_rules_sat);


val RED1_BETA_Var_case = store_thm
   ("RED1_BETA_Var_case",
    “!x t2:^term.
          RED1 BETA_R (Var x) t2 ==> F”,
    REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[term_distinct,term_one_one] o
            ONCE_REWRITE_RULE[RED1_inv_thms])
    THEN UNDISCH_ALL_TAC
    THEN REWRITE_TAC[BETA_R_inv_thms]
    THEN REWRITE_TAC[term_distinct]
   );


val RED1_BETA_App_case = store_thm
   ("RED1_BETA_App_case",
    “!(t:^term) u t2.
          RED1 BETA_R (App t u) t2 ==>
          ((?t'. RED1 BETA_R t t' /\ (t2 = App t' u)) \/
           (?u'. RED1 BETA_R u u' /\ (t2 = App t u')) \/
           (?x t'. (t = Lam x t') /\ (t2 = t' <[ [x,u])))”,
    REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[term_distinct,term_one_one] o
            ONCE_REWRITE_RULE[RED1_inv_thms])
    THENL (* 3 subgoals *)
      [ DISJ2_TAC
        THEN DISJ2_TAC
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[BETA_R_inv_thms]
        THEN REWRITE_TAC[term_one_one]
        THEN STRIP_TAC
        THEN EXISTS_TAC ``x:var``
        THEN EXISTS_TAC ``u':^term``
        THEN ASM_REWRITE_TAC[],

        DISJ1_TAC
        THEN EXISTS_TAC ``t2':^term``
        THEN ASM_REWRITE_TAC[],

        DISJ2_TAC
        THEN DISJ1_TAC
        THEN EXISTS_TAC ``u2:^term``
        THEN ASM_REWRITE_TAC[]
      ]
   );


val TC_RC_RED1_SUBSTITUTION_REMARK =
    REWRITE_RULE[GSYM TC_RC_RED1_IS_RED] BARENDREGT_SUBSTITUTION_REMARK;


val RED1_BETA_COMMUTES_RED1_ETA_LEMMA1 = store_thm
   ("RED1_BETA_COMMUTES_RED1_ETA_LEMMA1",
    “!R (M:^term) M1.
         RED1 R M M1 ==> !M2. BETA_R M M2 /\ (R = ETA_R) ==>
         ?M3. RC (RED1 BETA_R) M1 M3 /\ TC (RC (RED1 ETA_R)) M2 M3”,
    rule_induct RED1_height_strong_ind
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THEN POP_ASSUM REWRITE_ALL_THM
    THENL
      [ (* Case 1: ETA M M1, BETA M M2, impossible. *)
        UNDISCH_ALL_TAC
        THEN REWRITE_TAC (BETA_R_inv_thms :: ETA_R_inv_thms)
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[term_distinct],

        (* Case 2: t1 -->e t2, BETA (t1 u) M2. *)
        IMP_RES_TAC BETA_R_inv_thms
        THEN POP_ASSUM REWRITE_ALL_THM
        THEN POP_ASSUM (REWRITE_ALL_THM o REWRITE_RULE[term_one_one])
        THEN IMP_RES_TAC RED1_ETA_Lam_case
        THENL
          [ (* Case 2.1: u' = t2 x, x not in FV t2. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``App t2 t:^term``  (* Take M3 = P0 Q, = t2 t. *)
            THEN REWRITE_TAC[SUB_term,SUB]
            THEN IMP_RES_THEN REWRITE_THM subst_EMPTY
            THEN DEP_REWRITE_TAC[TC_SUBSET]
            THEN REWRITE_TAC[RC_REFLEXIVE],

            (* Case 2.2: \x.u' -->e \x.t', u' -->e t', BETA ((\x.u') t) M2. *)
            POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``(t':^term) <[ [x,t]``  (* Take M3 = P'[x:=Q]. *)
            THEN DEP_REWRITE_TAC[TC_SUBSET,RC_SUBSET]
            THEN IMP_RES_THEN REWRITE_THM
                    (REWRITE_RULE[SUBSTITUTIVE] RED1_ETA_SUBSTITUTIVE)
            THEN MATCH_MP_TAC RED1_R
            THEN REWRITE_TAC[BETA_R_rules_sat]
          ],

        (* Case 3: t' -->e u2, BETA (t u1) M2. *)
        IMP_RES_TAC BETA_R_inv_thms
        THEN POP_ASSUM REWRITE_ALL_THM
        THEN POP_ASSUM (REWRITE_ALL_THM o REWRITE_RULE[term_one_one])
        THEN EXISTS_TAC ``(u:^term) <[ [x,u2]``  (* Take M3 = P[x:=Q']. *)
        THEN DEP_REWRITE_TAC[TC_RC_RED1_SUBSTITUTION_REMARK]
        THEN DEP_REWRITE_TAC[TC_SUBSET,RC_SUBSET]
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC RED1_R
        THEN REWRITE_TAC[BETA_R_rules_sat],

        (* Case 4: t1 -->e u2, BETA (t u1) M2. *)
        IMP_RES_TAC BETA_R_inv_thms
        THEN POP_ASSUM REWRITE_ALL_THM
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[term_distinct]
      ]
   );



val RED1_BETA_COMMUTES_RED1_ETA_LEMMA2 = store_thm
   ("RED1_BETA_COMMUTES_RED1_ETA_LEMMA2",
    “!R (M:^term) M1.
         RED1 R M M1 ==> !M2. RED1 ETA_R M M2 /\ (R = BETA_R) ==>
         ?M3. TC (RC (RED1 ETA_R)) M1 M3 /\ RC (RED1 BETA_R) M2 M3”,
    rule_induct RED1_height_strong_ind
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THEN POP_ASSUM REWRITE_ALL_THM
    THENL
      [ (* Case 1: *)
        IMP_RES_TAC RED1_BETA_COMMUTES_RED1_ETA_LEMMA1
        THEN POP_TAC
        THEN REWRITE_ALL_TAC[]
        THEN POP_ASSUM STRIP_ASSUME_TAC
        THEN EXISTS_TAC ``M3:^term``
        THEN ASM_REWRITE_TAC[],

        (* Case 2:  *)
        IMP_RES_TAC RED1_ETA_App_case
        THENL
          [ POP_ASSUM REWRITE_ALL_THM
            THEN RES_TAC
            THEN EXISTS_TAC ``App M3 u:^term``
            THEN IMP_RES_THEN REWRITE_THM TC_RC_RED1_COMPAT
            THEN IMP_RES_THEN REWRITE_THM RC_RED1_COMPAT,

            POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``App t2 u':^term``
            THEN DEP_REWRITE_TAC[TC_SUBSET,RC_SUBSET]
            THEN IMP_RES_THEN REWRITE_THM RED1_COMPAT
          ],

        (* Case 3:  *)
        IMP_RES_TAC RED1_ETA_App_case
        THENL
          [ POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC ``App t' u2:^term``
            THEN DEP_REWRITE_TAC[TC_SUBSET,RC_SUBSET]
            THEN IMP_RES_THEN REWRITE_THM RED1_COMPAT,

            POP_ASSUM REWRITE_ALL_THM
            THEN RES_TAC
            THEN EXISTS_TAC ``App t M3:^term``
            THEN IMP_RES_THEN REWRITE_THM TC_RC_RED1_COMPAT
            THEN IMP_RES_THEN REWRITE_THM RC_RED1_COMPAT
          ],

        (* Case 4:  *)
        IMP_RES_TAC RED1_ETA_Lam_case
        THENL
          [ POP_ASSUM REWRITE_ALL_THM
            THEN IMP_RES_TAC RED1_BETA_App_case
            THENL (* 3 subgoals *)
              [ (* Case 4.1: *)
                POP_ASSUM REWRITE_ALL_THM
                THEN EXISTS_TAC ``t':^term``
                THEN DEP_REWRITE_TAC[TC_SUBSET,RC_SUBSET]
                THEN ASM_REWRITE_TAC[]
                THEN MATCH_MP_TAC RED1_R
                THEN MATCH_MP_TAC ETA_R_rules_sat
                THEN IMP_RES_THEN MATCH_MP_TAC NOT_IN_SUBSET
                THEN IMP_RES_TAC RED1_BETA_FV,

                (* Case 4.2: *)
                POP_ASSUM REWRITE_ALL_THM
                THEN IMP_RES_TAC RED1_BETA_Var_case,

                (* Case 4.3: *)
                POP_ASSUM REWRITE_ALL_THM
                THEN POP_ASSUM REWRITE_ALL_THM
                THEN EXISTS_TAC ``Lam x' t':^term``
                THEN REWRITE_TAC[RC_REFLEXIVE]
                THEN DEP_REWRITE_TAC[
                        ONCE_REWRITE_RULE[EQ_SYM_EQ] LAMBDA_CHANGE_BOUND_VAR]
                THEN ASM_REWRITE_TAC[GSYM FV_term]
                THEN MATCH_MP_TAC TC_SUBSET
                THEN REWRITE_TAC[RC_REFLEXIVE]
              ],

            POP_ASSUM REWRITE_ALL_THM
            THEN RES_THEN (STRIP_ASSUME_TAC o REWRITE_RULE[])
            THEN POP_ASSUM IMP_RES_TAC
            THEN EXISTS_TAC ``Lam x M3:^term``
            THEN IMP_RES_THEN REWRITE_THM TC_RC_RED1_COMPAT
            THEN IMP_RES_THEN REWRITE_THM RC_RED1_COMPAT
          ]
      ]
   );


val RED_BETA_COMMUTES_RED_ETA = store_thm
   ("RED_BETA_COMMUTES_RED_ETA",
    “RED (BETA_R:^term_rel) <=> RED ETA_R”,
    REWRITE_TAC[GSYM TC_RC_RED1_IS_RED]
    THEN MATCH_MP_TAC COMMUTE_TC_RC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_BETA_COMMUTES_RED1_ETA_LEMMA2
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REFL_TAC
   );


(* ====================================== *)
(* Beta-eta reduction is Church-Rosser.   *)
(* Barendregt Theorem 3.3.9(i), page 66.  *)
(* ====================================== *)

val BETA_ETA_R_CHURCH_ROSSER = store_thm
   ("BETA_ETA_R_CHURCH_ROSSER",
    “CHURCH_ROSSER ((BETA_R:^term_rel) UNION_R ETA_R)”,
    MATCH_MP_TAC COMMUTE_CHURCH_ROSSER
    THEN REWRITE_TAC[BETA_R_CHURCH_ROSSER,ETA_R_CHURCH_ROSSER,
                     RED_BETA_COMMUTES_RED_ETA]
   );
(* Soli Deo Gloria!!!  To God Alone Be The Glory!!! *)


(* Barendregt Theorem 3.3.9 (ii), page 66. *)

val BETA_ETA_R_NORMAL_FORM_EXISTS = store_thm
   ("BETA_ETA_R_NORMAL_FORM_EXISTS",
    “!(M:^term) N.
          REQUAL (BETA_R UNION_R ETA_R) M N ==>
                (?Z. RED (BETA_R UNION_R ETA_R) M Z /\
                     RED (BETA_R UNION_R ETA_R) N Z)”,
    MATCH_MP_TAC NORMAL_FORM_EXISTS
    THEN REWRITE_TAC[BETA_ETA_R_CHURCH_ROSSER]
   );

(* Barendregt Corollary 3.3.10 (i), page 67. *)

val BETA_ETA_R_NORMAL_FORM_REDUCED_TO = store_thm
   ("BETA_ETA_R_NORMAL_FORM_REDUCED_TO",
    “!(M:^term) N.
          NORMAL_FORM_OF (BETA_R UNION_R ETA_R) N M ==>
               RED (BETA_R UNION_R ETA_R) M N”,
    MATCH_MP_TAC NORMAL_FORM_REDUCED_TO
    THEN REWRITE_TAC[BETA_ETA_R_CHURCH_ROSSER]
   );

(* Barendregt Corollary 3.3.10 (ii), page 67. *)

val BETA_ETA_R_NORMAL_FORM_UNIQUE = store_thm
   ("BETA_ETA_R_NORMAL_FORM_UNIQUE",
    “!(M:^term) N1 N2.
          NORMAL_FORM_OF (BETA_R UNION_R ETA_R) N1 M /\
                   NORMAL_FORM_OF (BETA_R UNION_R ETA_R) N2 M ==>
                  (N1 = N2)”,
    MATCH_MP_TAC NORMAL_FORM_UNIQUE
    THEN REWRITE_TAC[BETA_ETA_R_CHURCH_ROSSER]
   );





val _ = export_theory();

val _ = print_theory_to_file "-" "eta.lst";

val _ = html_theory "eta";

val _ = print_theory_size();
