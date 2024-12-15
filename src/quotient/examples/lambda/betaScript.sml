open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;



val _ = new_theory "beta";


(* In interactive sessions, do:

app load ["barendregt", "tactics"
         ];

*)

open prim_recTheory pairTheory listTheory rich_listTheory;
open combinTheory;
(* open listLib; *)
open more_listTheory;
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
open more_setTheory;
open variableTheory;
open termTheory;
open alphaTheory;
open liftTheory;
open barendregt;
open reductionTheory;


open tactics;


val term = ty_antiq ( ==`:'a term`== );
val subs = ty_antiq ( ==`:(var # 'a term) list`== );
val term_rel = ty_antiq ( ==`:'a term -> 'a term -> bool`== );


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



(* Barendregt's Lemma 3.2.2:  *)


val TC_DIAMOND1 = store_thm
   ("TC_DIAMOND1",
    “!R (a:'a) b. TC R a b ==>
          (DIAMOND R ==> (!c. R a c ==>
               (?d. R b d /\ TC R c d)))”,
    GEN_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ REWRITE_ALL_TAC[DIAMOND]
        THEN RES_TAC
        THEN EXISTS_TAC “d':'a”
        THEN IMP_RES_TAC TC_SUBSET
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN FIRST_ASSUM (IMP_RES_TAC o SPEC ``d:'a``)
        THEN EXISTS_TAC ``d':'a``
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC (REWRITE_RULE[transitive_def] TC_TRANSITIVE)
      ]
   );

val TC_DIAMOND2 = store_thm
   ("TC_DIAMOND2",
    “!R (a:'a) b. TC R a b ==>
          (DIAMOND R ==> (!c. TC R a c ==>
               (?d. TC R b d /\ TC R c d)))”,
    GEN_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC TC_DIAMOND1
        THEN EXISTS_TAC “d:'a”
        THEN IMP_RES_TAC TC_SUBSET
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN FIRST_ASSUM (IMP_RES_TAC o SPEC ``d:'a``)
        THEN EXISTS_TAC ``d':'a``
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC (REWRITE_RULE[transitive_def] TC_TRANSITIVE)
      ]
   );

val TC_DIAMOND = store_thm
   ("TC_DIAMOND",
    “!R:'a->'a->bool. DIAMOND R ==> DIAMOND (TC R)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[DIAMOND]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC TC_DIAMOND2
    THEN EXISTS_TAC ``d'':'a``
    THEN ASM_REWRITE_TAC[]
   );




(* --------------------------------------------------------------------- *)
(* Primitive semantics of the lambda-calculus:                           *)
(*    Barendregt, Definition 3.1.2, page 51                              *)
(* Here we define the primitive reduction operator of the calculus.      *)
(* It corresponds to applying a function to an argument.                 *)
(* --------------------------------------------------------------------- *)



(* --------------------------------------------------------------------- *)
(* Definition of the relation of beta reduction.                         *)
(* This is simple, but we define it by rule induction.                   *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* (BETA_R t1 t2) means that the term t1 reduces entirely to the         *)
(* term t2 in exactly one beta-reduction step, as defined in Barendregt, *)
(* Section 3.1.3, page 51.   Note that this is true ONLY on t1 of        *)
(* the form (App (Lam x u) t).                                           *)
(* --------------------------------------------------------------------- *)


val BETA_R =
“BETA_R : ^term_rel”;

val BETA_R_patterns = [“^BETA_R t1 t2”];

val BETA_R_rules_tm =
“
       (* -------------------------------------------- *)
            (^BETA_R (App (Lam x u) t) (u <[ [x,t]))
”;

val (BETA_R_rules_sat,BETA_R_ind_thm) =
    define_inductive_relations BETA_R_patterns BETA_R_rules_tm;

val BETA_R_inv_thms = prove_inversion_theorems
    BETA_R_rules_sat BETA_R_ind_thm;

val BETA_R_strong_ind = prove_strong_induction
    BETA_R_rules_sat BETA_R_ind_thm;

val _ = save_thm ("BETA_R_rules_sat", BETA_R_rules_sat);
val _ = save_thm ("BETA_R_ind_thm", BETA_R_ind_thm);
val _ = save_thm ("BETA_R_inv_thms", LIST_CONJ BETA_R_inv_thms);
val _ = save_thm ("BETA_R_strong_ind", BETA_R_strong_ind);




(* --------------------------------------------------------------------- *)
(* We claim that BETA_R is a binary relation on the lambda calculus      *)
(* language which is                                                     *)
(*  1) a notion of reduction on the sigma calculus, in the sense of      *)
(*     Berendregt, Definition 3.1.2, pg 51 (trivial, since a relation)   *)
(*  2) deterministic                                                     *)
(* --------------------------------------------------------------------- *)


(* BETA_R is a deterministic relation. *)

val SUB_RENAME_SUB = store_thm
   ("SUB_RENAME_SUB",
    “!a:^term x y t. ((a <[ [(x,Var y)]) <[ [(y,Var x)] = a) ==>
                          (((a <[ [(x,Var y)]) <[ [y,t]) = (a <[ [x,t]))”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL
      [ (* Con case *)
        REWRITE_TAC[SUB_term],

        (* Var case *)
        REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[term_one_one]
        THEN DISCH_THEN (ASSUME_TAC o SYM)
        THEN RES_TAC,

        (* App case *)
        REWRITE_TAC[SUB_term]
        THEN REWRITE_TAC[term_one_one]
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        (* Lam case *)
        SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[Lam_one_one]
        THEN REWRITE_TAC[subst_SAME_ONE]
        THEN STRIP_TAC
        THEN POP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

val SUB_RENAME_TERM = store_thm
   ("SUB_RENAME_TERM",
    “!a:^term b x y t. (Lam x a = Lam y b) ==>
                          ((a <[ [x,t]) = (b <[ [y,t]))”,
    REWRITE_TAC[Lam_one_one]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM (REWRITE_THM o SYM)
    THEN MATCH_MP_TAC SUB_RENAME_SUB
    THEN ASM_REWRITE_TAC[]
   );

val BETA_R_deterministic = store_thm
   ("BETA_R_deterministic",
    “!t1:^term t2.
         BETA_R t1 t2 ==> !t3.  BETA_R t1 t3 ==> (t2 = t3)”,
    rule_induct BETA_R_strong_ind
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC BETA_R_inv_thms
    THEN REWRITE_TAC[term_one_one]
    THEN STRIP_TAC
    THEN IMP_RES_TAC SUB_RENAME_TERM
    THEN ASM_REWRITE_TAC[]
   );

(* Note that BETA_R is not reflexive, symmetric, or transitive. *)

val FV_SUB = store_thm
   ("FV_SUB",
    “!u:^term x t. FV (u <[ [(x,t)]) SUBSET FV u DIFF {x} UNION FV t”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL
      [ (* Con case *)
        REWRITE_TAC[SUB_term,FV_term]
        THEN REWRITE_TAC[EMPTY_SUBSET],

        (* Var case *)
        REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[SUBSET_UNION]
        THEN REWRITE_TAC[SUBSET_DEF]
        THEN REWRITE_TAC[FV_term,IN_UNION,IN]
        THEN REPEAT STRIP_TAC
        THEN DISJ1_TAC
        THEN POP_ASSUM REWRITE_THM
        THEN DEP_REWRITE_TAC[IN_DIFF]
        THEN ASM_REWRITE_TAC[IN],

        (* App case *)
        REWRITE_TAC[SUB_term,FV_term]
        THEN REWRITE_TAC[UNION_DIFF,UNION_SUBSET]
        THEN REWRITE_ALL_TAC[SUBSET_DEF,IN_UNION]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        (* Lam case *)
        SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[FV_term]
        THEN POP_TAC
        THEN POP_TAC
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[SUBSET_DEF,IN_UNION,IN_DIFF,IN]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC(* 2 subgoals *)
        THEN ASM_REWRITE_TAC[]
      ]
   );

val BETA_FV = store_thm
   ("BETA_FV",
    “!t1:^term t2. BETA_R t1 t2 ==>
                           (FV t2 SUBSET FV t1)”,
    rule_induct BETA_R_strong_ind
    THEN REWRITE_TAC[FV_term]
    THEN REWRITE_TAC[FV_SUB]
   );


val BETA_R_equals = store_thm
   ("BETA_R_equals",
    “(!a t:^term. BETA_R (Con a) t = F) /\
        (!x t:^term. BETA_R (Var x) t = F) /\
        (!t u t':^term. BETA_R (App t u) t' =
                   (?x u'. (t = Lam x u') /\ (t' = u' <[ [x,u]))) /\
        (!x u t:^term. BETA_R (Lam x u) t = F)”,
    REWRITE_TAC BETA_R_inv_thms
    THEN REWRITE_TAC[term_distinct,term_one_one]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC “x:var”
        THEN EXISTS_TAC “u':^term”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “x:var”
        THEN EXISTS_TAC “u':^term”
        THEN EXISTS_TAC “u:^term”
        THEN ASM_REWRITE_TAC[]
      ]
   );


(* --------------------------------------------------------------------- *)
(* Now we claim that using the results of theory "reduction", that       *)
(* 1) RED1 BETA_R, RED BETA_R, and REQ BETA_R are compatible,            *)
(* 2) RED BETA_R is a reduction relation,                                *)
(* 3) REQ BETA_R is an equality relation,                                *)
(* 4) various theorems and relations hold (see the theory "reduction")   *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Now we begin to prove the Church-Rosser theorem for BETA_R.           *)
(* --------------------------------------------------------------------- *)


(* Barendregt Proposition 3.1.16, BETA_R is substitutive. *)

val BETA_R_SUBSTITUTIVE = store_thm
   ("BETA_R_SUBSTITUTIVE",
    “SUBSTITUTIVE (BETA_R:^term_rel)”,
    REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT GEN_TAC
    THEN DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE BETA_R_inv_thms)
    THEN ASM_REWRITE_TAC[]
    THEN ONCE_REWRITE_TAC[SUB_term]
    THEN SIMPLE_SUBST_TAC
    THEN IMP_RES_THEN REWRITE_THM SUB_RENAME_TERM
    THEN REWRITE_TAC BETA_R_inv_thms
    THEN REWRITE_TAC[term_one_one]
    THEN EXISTS_TAC “z:var”
    THEN EXISTS_TAC “(u':^term) <[ [x,L]”
    THEN EXISTS_TAC “(t:^term) <[ [x,L]”
    THEN REWRITE_TAC[]
    THEN MATCH_MP_TAC BARENDREGT_SUBSTITUTION_LEMMA
    THEN ASM_REWRITE_TAC[]
   );





(* --------------------------------------------------------------------- *)
(* (REDL o1 o2) will now be defined on the sigma calculus such that      *)
(*   1) REDL satisfies the diamond property, and                         *)
(*   2) the transitive closure of REDL is RED BETA_R.                    *)
(* Then it follows by TC_DIAMOND that RED BETA_R satifies the diamond    *)
(* property, i.e., that BETA_R is Church-Rosser.                         *)
(* --------------------------------------------------------------------- *)


val REDL =
“REDL : ^term_rel”;

val REDL_patterns = [“^REDL t1 t2”];

val REDL_rules_tm =
“

       (* -------------------------------------------- *)
                         (^REDL t t)                                    /\


                        ((^REDL t1 t2)
       (* -------------------------------------------- *) ==>
                (^REDL (Lam x t1) (Lam x t2)))                          /\


                ((^REDL t1 t2) /\ (^REDL u1 u2)
       (* -------------------------------------------- *) ==>
                (^REDL (App t1 u1) (App t2 u2)))                        /\


                ((^REDL t1 t2) /\ (^REDL u1 u2)
       (* -------------------------------------------- *) ==>
           (^REDL (App (Lam x t1) u1) (t2 <[ [x,u2])))
”;

val (REDL_rules_sat,REDL_ind_thm) =
    define_inductive_relations REDL_patterns REDL_rules_tm;

val REDL_inv_thms = prove_inversion_theorems
    REDL_rules_sat REDL_ind_thm;

val REDL_strong_ind = prove_strong_induction
    REDL_rules_sat REDL_ind_thm;

val _ = save_thm ("REDL_rules_sat", REDL_rules_sat);
val _ = save_thm ("REDL_ind_thm", REDL_ind_thm);
val _ = save_thm ("REDL_inv_thms", LIST_CONJ REDL_inv_thms);
val _ = save_thm ("REDL_strong_ind", REDL_strong_ind);


val [REDL_REFL, REDL_Lam, REDL_App, REDL_BETA]
   = CONJUNCTS REDL_rules_sat;




val REDL_height_ind_thm_LEMMA = store_thm
   ("REDL_height_ind_thm_LEMMA",
    “!n P_0:^term_rel.
         (!t. P_0 t t) /\
         (!x t1 t2. P_0 t1 t2 ==> P_0 (Lam x t1) (Lam x t2)) /\
         (!t1 u1 t2 u2.
           P_0 t1 t2 /\ P_0 u1 u2 ==>
           P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
           (!t1' t2'. REDL t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2') /\
           P_0 u1 u2 ==>
           P_0 (App (Lam x t1) u1) (t2 <[ [x,u2])) /\
         (!x t1 t2.
           (!t1' t2'. REDL t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2')
            ==> P_0 (Lam x t1) (Lam x t2)) ==>
         (!t1 t2. REDL t1 t2 ==>
                    ((HEIGHT t1 <= n) ==>
                     P_0 t1 t2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN UNDISCH_TAC “REDL (t1:^term) t2”
        THEN ONCE_REWRITE_TAC REDL_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct,term_one_one]
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct REDL_ind_thm
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 3 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THENL
              [ REPEAT STRIP_TAC
                THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
                THEN POP_ASSUM (REWRITE_THM o SYM)
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_MONO_EQ
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
                THEN ASM_REWRITE_TAC[],

                FIRST_ASSUM MATCH_MP_TAC
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
              ]
          ]
      ]
   );

val REDL_height_ind_thm = store_thm
   ("REDL_height_ind_thm",
    “!P_0:^term_rel.
         (!t. P_0 t t) /\
         (!x t1 t2. P_0 t1 t2 ==> P_0 (Lam x t1) (Lam x t2)) /\
         (!t1 u1 t2 u2.
            P_0 t1 t2 /\ P_0 u1 u2 ==> P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
            (!t1' t2'.
               REDL t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2') /\
            P_0 u1 u2 ==>
            P_0 (App (Lam x t1) u1) (t2 <[ [(x,u2)])) /\
         (!x t1 t2.
            (!t1' t2'.
               REDL t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2') ==>
            P_0 (Lam x t1) (Lam x t2)) ==>
         !t1 t2. REDL t1 t2 ==> P_0 t1 t2”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL
             (SPEC “HEIGHT (t1:^term)” REDL_height_ind_thm_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
   );

val REDL_height_strong_ind_LEMMA = store_thm
   ("REDL_height_strong_ind_LEMMA",
    “!n P_0:^term_rel.
         (!t. P_0 t t) /\
         (!t1 u1 t2 u2.
            P_0 t1 t2 /\ REDL t1 t2 /\ P_0 u1 u2 /\ REDL u1 u2 ==>
            P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
            (!t1' t2'.
             REDL t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDL t1 t2 /\
            P_0 u1 u2 /\ REDL u1 u2 ==>
            P_0 (App (Lam x t1) u1) (t2 <[ [(x,u2)])) /\
         (!x t1 t2.
           (!t1' t2'.
             REDL t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDL t1 t2 ==>
           P_0 (Lam x t1) (Lam x t2)) ==>
         !t1 t2. REDL t1 t2 ==> HEIGHT t1 <= n ==> P_0 t1 t2
    ”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN UNDISCH_TAC “REDL (t1:^term) t2”
        THEN ONCE_REWRITE_TAC REDL_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct]
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct REDL_strong_ind
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 3 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THENL
              [ ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
                THEN ASM_REWRITE_TAC[]
                THEN POP_ASSUM (REWRITE_THM o SYM)
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_MONO_EQ
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

                FIRST_ASSUM MATCH_MP_TAC
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
              ]
          ]
      ]
   );

val REDL_height_strong_ind = store_thm
   ("REDL_height_strong_ind",
    “!P_0.
         (!t:^term. P_0 t t) /\
         (!t1 u1 t2 u2.
            P_0 t1 t2 /\ REDL t1 t2 /\ P_0 u1 u2 /\ REDL u1 u2 ==>
            P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
           (!t1' t2'.
             REDL t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDL t1 t2 /\
            P_0 u1 u2 /\ REDL u1 u2 ==>
            P_0 (App (Lam x t1) u1) (t2 <[ [(x,u2)])) /\
         (!x t1 t2.
           (!t1' t2'.
             REDL t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDL t1 t2 ==>
           P_0 (Lam x t1) (Lam x t2)) ==>
         !t1 t2. REDL t1 t2 ==> P_0 t1 t2”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL (SPEC “HEIGHT (t1:^term)”
                                 REDL_height_strong_ind_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
   );


val REDL_FV = store_thm
   ("REDL_FV",
    “!(M:^term) M'.
          REDL M M' ==> (FV M' SUBSET FV M)”,
    rule_induct REDL_strong_ind (* strong, not weak induction *)
    THEN REWRITE_TAC[FV_term,SUBSET_REFL]
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ MATCH_MP_TAC SUBSET_DIFF
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC SUBSETS_UNION,

        MATCH_MP_TAC SUBSET_TRANS
        THEN EXISTS_TAC “FV (t2:^term) DIFF {x} UNION FV (u2:^term)”
        THEN REWRITE_TAC[FV_SUB,FV_term]
        THEN MATCH_MP_TAC SUBSETS_UNION
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC SUBSET_DIFF
        THEN ASM_REWRITE_TAC[]
      ]
   );


val REDL_RENAME = store_thm
   ("REDL_RENAME",
    “!t1:^term t2 t1' x y.
          REDL t1 t2 /\ (Lam x t1 = Lam y t1') ==>
          (Lam x t2 = Lam y (t2 <[ [x, Var y]))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_FV
    THEN IMP_RES_TAC LAMBDA_RENAME
   );



val REDL_SUBSTITUTIVE_BASE = store_thm
   ("REDL_SUBSTITUTIVE_BASE",
    “!(M:^term) N.
          REDL M N ==>
            !L x. REDL (M <[ [x,L]) (N <[ [x,L])”,
    rule_induct REDL_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ REWRITE_TAC[REDL_REFL],

        REWRITE_TAC[SUB_term]
        THEN MATCH_MP_TAC REDL_App
        THEN ASM_REWRITE_TAC[],

        ONCE_REWRITE_TAC[SUB_term]
        THEN SIMPLE_SUBST_TAC
        THEN IMP_RES_THEN IMP_RES_TAC REDL_RENAME
        THEN IMP_RES_THEN ONCE_REWRITE_THM SUB_RENAME_TERM
        THEN POP_TAC
        THEN DEP_ONCE_REWRITE_TAC[BARENDREGT_SUBSTITUTION_LEMMA]
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC REDL_BETA
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN MATCH_MP_TAC REDL_Lam
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

(* This is necessary for when we change a bound variable: *)

val REDL_CHANGE_VAR = store_thm
   ("REDL_CHANGE_VAR",
    “!t1:^term t2 x y t1'.
           REDL t1 t2 /\ (Lam x t1 = Lam y t1')  ==>
           REDL t1' (t2 <[ [x, Var y])”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
    THEN MATCH_MP_TAC REDL_SUBSTITUTIVE_BASE
    THEN FIRST_ASSUM ACCEPT_TAC
   );


(* This is Barendregt's Lemma 3.2.4 Case 1. *)
val REDL_SUBSTITUTIVE_SAME = store_thm
   ("REDL_SUBSTITUTIVE_SAME",
    “!M:^term.
          (!N N' x. REDL N N' ==>
                    REDL (M <[ [x,N]) (M <[ [x,N']))”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THEN REPEAT STRIP_TAC
    THENL (* 3 subgoals *)
      [ REWRITE_TAC[SUB_term]
        THEN REWRITE_TAC[REDL_REFL],

        REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[REDL_REFL],

        REWRITE_TAC[SUB_term]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        SIMPLE_SUBST_TAC
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat]
      ]
   );





(* This is Barendregt's Lemma 3.2.4. *)
val REDL_SUBSTITUTIVE = store_thm
   ("REDL_SUBSTITUTIVE",
    “!M:^term M'.
          REDL M M' ==>
            (!N N' x. REDL N N' ==>
                REDL (M <[ [x,N]) (M' <[ [x,N']))”,
    rule_induct REDL_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ (* Case 1 *)
        DEP_ASM_REWRITE_TAC[REDL_SUBSTITUTIVE_SAME],

        (* Case 3 *)
        REWRITE_TAC[SUB_term]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        (* Case 4 *)
        ONCE_REWRITE_TAC[SUB_term]
        THEN SIMPLE_SUBST_TAC
        THEN IMP_RES_THEN IMP_RES_TAC REDL_CHANGE_VAR
        THEN IMP_RES_THEN IMP_RES_TAC REDL_RENAME
        THEN IMP_RES_THEN ONCE_REWRITE_THM SUB_RENAME_TERM
        THEN DEP_ONCE_REWRITE_TAC[BARENDREGT_SUBSTITUTION_LEMMA]
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC REDL_BETA
        THEN DEP_ONCE_ASM_REWRITE_TAC[]
        THEN ASM_REWRITE_TAC[],

        (* Case 2 *)
        SIMPLE_SUBST_TAC
        THEN IMP_RES_THEN IMP_RES_TAC REDL_CHANGE_VAR
        THEN MATCH_MP_TAC REDL_Lam
        THEN DEP_ONCE_ASM_REWRITE_TAC[]
        THEN UNDISCH_LAST_TAC
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one
        THEN ASM_REWRITE_TAC[]
     ]
   );



(* Barendregt lemma 3.2.5 (expanded) *)

val REDL_cases = store_thm
   ("REDL_cases",
    “(!a t2:^term.
          REDL (Con a) t2 ==>
          (t2 = Con a)) /\
        (!x t2:^term.
          REDL (Var x) t2 ==>
          (t2 = Var x)) /\
        (!t u t2:^term.
          REDL (App t u) t2 ==>
          ((?t' u'. (t2 = (App t' u')) /\ REDL t t' /\ REDL u u') \/
           (?x t' t'' u'. (t = Lam x t') /\
                          (t2 = (t'' <[ [x,u'])) /\
                          REDL t' t'' /\
                          REDL u u'))) /\
        (!x t t2:^term.
          REDL (Lam x t) t2 ==>
          (?t'. (t2 = Lam x t') /\ REDL t t'))”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[term_distinct,term_one_one] o
            ONCE_REWRITE_RULE REDL_inv_thms)
    THENL (* 5 subgoals *)
      [ POP_ASSUM REWRITE_THM
        THEN DISJ1_TAC
        THEN EXISTS_TAC “t:^term”
        THEN EXISTS_TAC “u:^term”
        THEN REWRITE_TAC[REDL_REFL],

        DISJ1_TAC
        THEN EXISTS_TAC “t2':^term”
        THEN EXISTS_TAC “u2:^term”
        THEN ASM_REWRITE_TAC[],

        DISJ2_TAC
        THEN EXISTS_TAC “x:var”
        THEN EXISTS_TAC “t1':^term”
        THEN EXISTS_TAC “t2':^term”
        THEN EXISTS_TAC “u2:^term”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “t:^term”
        THEN ASM_REWRITE_TAC[REDL_REFL],

        EXISTS_TAC “(t2':^term) <[ [x', Var x]”
        THEN ASSUM_LIST (ASSUME_TAC o SYM o hd o rev)
        THEN IMP_RES_THEN IMP_RES_TAC REDL_RENAME
        THEN IMP_RES_TAC REDL_CHANGE_VAR
        THEN ASM_REWRITE_TAC[]
      ]
   );

val [REDL_Con_case, REDL_Var_case, REDL_App_case, REDL_Lam_case]
    = CONJUNCTS REDL_cases;


val REDL_Lam_CONF = store_thm
   ("REDL_Lam_CONF",
    “!t1:^term t2 t3 x.
          REDL (Lam x t1) t3 /\ REDL (Lam x t2) t3 ==>
          (?t4. t3 = Lam x t4)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_Lam_case
    THEN ASM_REWRITE_TAC[term_one_one]
    THEN EXISTS_TAC “t'':^term”
    THEN REFL_TAC
   );

val REDL_Lam_MONO = store_thm
   ("REDL_Lam_MONO",
    “!x t1:^term t2.
          REDL (Lam x t1) (Lam x t2) ==>
          REDL t1 t2”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_Lam_case
    THEN REWRITE_ALL_TAC[term_one_one]
    THEN ASM_REWRITE_TAC[]
   );



(* Barendregt Lemma 3.2.6. *)

val REDL_DIAMOND_LEMMA = store_thm
   ("REDL_DIAMOND_LEMMA",
    “!t1:^term t2.
          REDL t1 t2 ==>
          (!t3. REDL t1 t3 ==>
                (?t4. REDL t2 t4 /\ REDL t3 t4))”,
    rule_induct REDL_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC
    THENL (* 4 subgoals *)
      [ (* Case 1. *)
        EXISTS_TAC “t3:^term”
        THEN ASM_REWRITE_TAC[REDL_rules_sat],

        (* Case 4. *)
        IMP_RES_TAC REDL_cases
        THEN RES_TAC
        THEN EXISTS_TAC “Lam x (t4:^term)”
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        (* Case 3. *)
        IMP_RES_TAC REDL_cases
        THENL
          [ (* Subcase 3.1 *)
            RES_TAC
            THEN EXISTS_TAC “App t4'' (t4:^term)”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

            (* Subcase 3.2 *)
            UNDISCH_THEN “t1 = Lam x (t':^term)” REWRITE_ALL_THM
            THEN UNDISCH_THEN “(t3:^term) = t'' <[ [x,u']”
                          REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_Lam_case
            THEN UNDISCH_THEN “t2 = Lam x (t''':^term)” REWRITE_ALL_THM
            THEN ASSUME_TAC (SPEC_ALL (MATCH_MP REDL_Lam
                                       (ASSUME “REDL t' (t'':^term)”)))
            THEN RES_TAC
            THEN POP_TAC
            THEN ASSUM_LIST (fn asl =>
                     STRIP_ASSUME_TAC (MATCH_MP REDL_Lam_CONF
                                             (CONJ (hd asl) (hd (tl asl)))))
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN EXISTS_TAC “(t4''':^term) <[ [x,t4]”
            THEN IMP_RES_TAC REDL_Lam_MONO
            THEN DEP_ASM_REWRITE_TAC[REDL_BETA]
            THEN DEP_ASM_REWRITE_TAC[REDL_SUBSTITUTIVE]
          ],

        (* Case 2. *)
        IMP_RES_TAC REDL_cases
        THENL
          [ (* Subcase 2.1 *)
            IMP_RES_TAC REDL_Lam_case
            THEN UNDISCH_THEN “(t':^term) = Lam x t''” REWRITE_ALL_THM
            THEN RES_TAC
            THEN EXISTS_TAC “(t4'':^term) <[ [x, t4]”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat,REDL_SUBSTITUTIVE],

            (* Subcase 2.2 *)
            UNDISCH_THEN “(t3:^term) = t'' <[ [x',u']” REWRITE_ALL_THM
            THEN FIRST_ASSUM (fn th =>
                    (UNDISCH_THEN (concl th) (ASSUME_TAC o SYM)))
            THEN IMP_RES_THEN IMP_RES_TAC REDL_CHANGE_VAR
            THEN IMP_RES_THEN IMP_RES_TAC REDL_RENAME
            THEN RES_TAC
            THEN POP_TAC
            THEN EXISTS_TAC “(t4'':^term) <[ [x,t4]”
            THEN IMP_RES_THEN ONCE_REWRITE_THM SUB_RENAME_TERM
            THEN DEP_ASM_REWRITE_TAC[REDL_SUBSTITUTIVE]
          ]
      ]
   );



val REDL_DIAMOND = store_thm
   ("REDL_DIAMOND",
    “DIAMOND (REDL:^term_rel)”,
    REWRITE_TAC[DIAMOND]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_DIAMOND_LEMMA
    THEN EXISTS_TAC “t4'':^term”
    THEN ASM_REWRITE_TAC[]
   );





(* --------------------------------------------------------------------- *)
(* (REDC t1 t2) will now be defined on the sigma calculus such that      *)
(*   1) REDC provides the maximal parallel reduction step, that          *)
(*      contracts all redexes in t1.                                     *)
(*   2) We can close any diamond and prove the diamond lemma for REDL    *)
(*      by closing the left and right triangles independently.           *)
(* --------------------------------------------------------------------- *)

val REDC =
“REDC : ^term_rel”;

val REDC_patterns = [“^REDC t1 t2”];

val REDC_rules_tm =
“

       (* -------------------------------------------- *)
                    (^REDC (Con a) (Con a))                             /\


       (* -------------------------------------------- *)
                    (^REDC (Var x) (Var x))                             /\


                        ((^REDC t1 t2)
       (* -------------------------------------------- *) ==>
                (^REDC (Lam x t1) (Lam x t2)))                          /\


          ((^REDC t1 t2) /\ (^REDC u1 u2) /\ (!t x. ~(t1 = Lam x t))
       (* -------------------------------------------- *) ==>
                (^REDC (App t1 u1) (App t2 u2)))                        /\


                ((^REDC t1 t2) /\ (^REDC u1 u2)
       (* -------------------------------------------- *) ==>
           (^REDC (App (Lam x t1) u1) (t2 <[ [x,u2])))
”;

val (REDC_rules_sat,REDC_ind_thm) =
    define_inductive_relations REDC_patterns REDC_rules_tm;

val REDC_inv_thms = prove_inversion_theorems
    REDC_rules_sat REDC_ind_thm;

val REDC_strong_ind = prove_strong_induction
    REDC_rules_sat REDC_ind_thm;

val _ = save_thm ("REDC_rules_sat", REDC_rules_sat);
val _ = save_thm ("REDC_ind_thm", REDC_ind_thm);
val _ = save_thm ("REDC_inv_thms", LIST_CONJ REDC_inv_thms);
val _ = save_thm ("REDC_strong_ind", REDC_strong_ind);


val [REDC_Con, REDC_Var, REDC_Lam, REDC_App, REDC_BETA]
   = CONJUNCTS REDC_rules_sat;



val REDC_height_ind_thm_LEMMA = store_thm
   ("REDC_height_ind_thm_LEMMA",
    “!n P_0.
         (!a. P_0 (Con a) (Con a)) /\
         (!x. P_0 (Var x) (Var x)) /\
         (!x t1 t2.
           (!t1' t2'. REDC t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2')
            ==> P_0 (Lam x t1) (Lam x t2)) /\
         (!t1 u1 t2 u2.
           P_0 t1 t2 /\ P_0 u1 u2 /\ (!t x. ~(t1 = Lam x t)) ==>
           P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
           (!t1' t2'. REDC t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2') /\
           P_0 u1 u2 ==>
           P_0 (App (Lam x t1) u1) (t2 <[ [x,u2]))
 ==>
         (!t1:^term t2. REDC t1 t2 ==>
                    ((HEIGHT t1 <= n) ==>
                     P_0 t1 t2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN UNDISCH_TAC “REDC (t1:^term) t2”
        THEN ONCE_REWRITE_TAC REDC_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct,term_one_one]
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct REDC_ind_thm
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 3 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THENL
              [ REPEAT STRIP_TAC
                THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
                THEN POP_ASSUM (REWRITE_THM o SYM)
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_MONO_EQ
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
                THEN ASM_REWRITE_TAC[],

                FIRST_ASSUM MATCH_MP_TAC
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
              ]
          ]
      ]
   );

val REDC_height_ind_thm = store_thm
   ("REDC_height_ind_thm",
    “!P_0.
         (!a. P_0 (Con a) (Con a)) /\
         (!x. P_0 (Var x) (Var x)) /\
         (!x t1 t2.
           (!t1' t2'. REDC t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2')
            ==> P_0 (Lam x t1) (Lam x t2)) /\
         (!t1 u1 t2 u2.
            P_0 t1 t2 /\ P_0 u1 u2 /\ (!t x. ~(t1 = Lam x t)) ==>
            P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
            (!t1' t2'.
               REDC t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==> P_0 t1' t2') /\
            P_0 u1 u2 ==>
            P_0 (App (Lam x t1) u1) (t2 <[ [(x,u2)])) ==>
         !t1:^term t2. REDC t1 t2 ==> P_0 t1 t2”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL (SPEC “HEIGHT (t1:^term)”
                                REDC_height_ind_thm_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
   );

val REDC_height_strong_ind_LEMMA = store_thm
   ("REDC_height_strong_ind_LEMMA",
    “!n P_0.
         (!a. P_0 (Con a) (Con a)) /\
         (!x. P_0 (Var x) (Var x)) /\
         (!t1 u1 t2 u2.
            P_0 t1 t2 /\ REDC t1 t2 /\ P_0 u1 u2 /\ REDC u1 u2 /\
            (!t x. ~(t1 = Lam x t)) ==>
            P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
            (!t1' t2'.
             REDC t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDC t1 t2 /\
            P_0 u1 u2 /\ REDC u1 u2 ==>
            P_0 (App (Lam x t1) u1) (t2 <[ [(x,u2)])) /\
         (!x t1 t2.
           (!t1' t2'.
             REDC t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDC t1 t2 ==>
           P_0 (Lam x t1) (Lam x t2)) ==>
         !t1:^term t2. REDC t1 t2 ==> HEIGHT t1 <= n ==> P_0 t1 t2
    ”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN UNDISCH_TAC “REDC (t1:^term) t2”
        THEN ONCE_REWRITE_TAC REDC_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct]
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct REDC_strong_ind
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 3 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THENL
              [ ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
                THEN ASM_REWRITE_TAC[]
                THEN POP_ASSUM (REWRITE_THM o SYM)
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_MONO_EQ
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

                FIRST_ASSUM MATCH_MP_TAC
                THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
                THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
              ]
          ]
      ]
   );

val REDC_height_strong_ind = store_thm
   ("REDC_height_strong_ind",
    “!P_0.
         (!a. P_0 (Con a) (Con a)) /\
         (!x. P_0 (Var x) (Var x)) /\
         (!t1 u1 t2 u2.
            P_0 t1 t2 /\ REDC t1 t2 /\ P_0 u1 u2 /\ REDC u1 u2 /\
            (!t x. ~(t1 = Lam x t)) ==>
            P_0 (App t1 u1) (App t2 u2)) /\
         (!x t1 u1 t2 u2.
           (!t1' t2'.
             REDC t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDC t1 t2 /\
            P_0 u1 u2 /\ REDC u1 u2 ==>
            P_0 (App (Lam x t1) u1) (t2 <[ [(x,u2)])) /\
         (!x t1 t2.
           (!t1' t2'.
             REDC t1' t2' /\ (HEIGHT t1 = HEIGHT t1') ==>
             P_0 t1' t2') /\ REDC t1 t2 ==>
           P_0 (Lam x t1) (Lam x t2)) ==>
         !(t1:^term) t2. REDC t1 t2 ==> P_0 t1 t2”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL (SPEC “HEIGHT (t1:^term)”
                                 REDC_height_strong_ind_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
   );


val REDC_FV = store_thm
   ("REDC_FV",
    “!(M:^term) M'.
          REDC M M' ==> (FV M' SUBSET FV M)”,
    rule_induct REDC_strong_ind (* strong, not weak induction *)
    THEN REWRITE_TAC[FV_term,SUBSET_REFL]
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ MATCH_MP_TAC SUBSET_DIFF
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC SUBSETS_UNION,

        MATCH_MP_TAC SUBSET_TRANS
        THEN EXISTS_TAC “FV (t2:^term) DIFF {x} UNION FV (u2:^term)”
        THEN REWRITE_TAC[FV_SUB,FV_term]
        THEN MATCH_MP_TAC SUBSETS_UNION
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC SUBSET_DIFF
        THEN ASM_REWRITE_TAC[]
      ]
   );


val REDC_RENAME = store_thm
   ("REDC_RENAME",
    “!(t1:^term) t2 t1' x y.
          REDC t1 t2 /\ (Lam x t1 = Lam y t1') ==>
          (Lam x t2 = Lam y (t2 <[ [x, Var y]))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDC_FV
    THEN IMP_RES_TAC LAMBDA_RENAME
   );

(* NOT TRUE for REDC!  REDC (Var x) (Var x), but not REDC ((\x.x)N) ((\x.x)N) !

val REDC_SUBSTITUTIVE_BASE = store_thm
   ("REDC_SUBSTITUTIVE_BASE",
    “!(M:^term) N.
          REDC M N ==>
            !L x. REDC (M <[ [x,L]) (N <[ [x,L])”,
    rule_induct REDC_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ REWRITE_TAC[SUB_term,REDC_Var],

        REWRITE_TAC[SUB_term]
        THEN MATCH_MP_TAC REDC_App
        THEN ASM_REWRITE_TAC[],

        ONCE_REWRITE_TAC[SUB_term]
        THEN SIMPLE_SUBST_TAC
        THEN IMP_RES_THEN IMP_RES_TAC REDC_RENAME
        THEN IMP_RES_THEN ONCE_REWRITE_THM SUB_RENAME_TERM
        THEN POP_TAC
        THEN DEP_ONCE_REWRITE_TAC[BARENDREGT_SUBSTITUTION_LEMMA]
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC REDC_BETA
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN MATCH_MP_TAC REDC_Lam
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

*)

val NOT_LAMBDA_SUBSTITUTIVE = store_thm
   ("NOT_LAMBDA_SUBSTITUTIVE",
    “!(t1:^term) y z.
          (!t x. ~(t1 = Lam x t)) ==>
          (!t x. ~(t1 <[ [y,Var z] = Lam x t))”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC (* 4 subgoals *)
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SUB_term]
    THENL (* 4 subgoals *)
      [ REWRITE_TAC[term_distinct],

        REWRITE_TAC[SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[term_distinct],

        REWRITE_TAC[term_distinct],

        POP_ASSUM (MP_TAC o SPECL[``t1:^term``,``v:var``])
        THEN REWRITE_TAC[]
      ]
   );

val REDC_SUBSTITUTIVE_VAR = store_thm
   ("REDC_SUBSTITUTIVE_VAR",
    “!(M:^term) N.
          REDC M N ==>
            !y x. REDC (M <[ [x,Var y]) (N <[ [x,Var y])”,
    rule_induct REDC_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 5 subgoals *)
    THENL
      [ REWRITE_TAC[SUB_term]
        THEN REWRITE_TAC[REDC_Con],

        REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[REDC_Var],

        REWRITE_TAC[SUB_term]
        THEN MATCH_MP_TAC REDC_App
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC NOT_LAMBDA_SUBSTITUTIVE
        THEN ASM_REWRITE_TAC[],

        ONCE_REWRITE_TAC[SUB_term]
        THEN SIMPLE_SUBST_TAC
        THEN IMP_RES_THEN IMP_RES_TAC REDC_RENAME
        THEN IMP_RES_THEN ONCE_REWRITE_THM SUB_RENAME_TERM
        THEN POP_TAC
        THEN DEP_ONCE_REWRITE_TAC[BARENDREGT_SUBSTITUTION_LEMMA]
        THEN ASM_REWRITE_TAC[FV_term,IN]
        THEN MATCH_MP_TAC REDC_BETA
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN MATCH_MP_TAC REDC_Lam
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

(* This is for when we change a bound variable: *)

val REDC_CHANGE_VAR = store_thm
   ("REDC_CHANGE_VAR",
    “!(t1:^term) t2 x y t1'.
           REDC t1 t2 /\ (Lam x t1 = Lam y t1')  ==>
           REDC t1' (t2 <[ [x, Var y])”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN REWRITE_THM Lam_one_one_RENAME
    THEN MATCH_MP_TAC REDC_SUBSTITUTIVE_VAR
    THEN FIRST_ASSUM ACCEPT_TAC
   );


(* Takahashi's trick, an alternative way to prove the diamond lemma. *)


(* Complete developments exist. *)

val REDC_EXISTS = store_thm
   ("REDC_EXISTS",
    “!t:^term. ?t'. REDC t t'”,
    MUTUAL_INDUCT_THEN term_induct STRIP_ASSUME_TAC (* 3 subgoals *)
    THEN REPEAT GEN_TAC
    THENL (* 4 subgoals *)
      [ EXISTS_TAC ``Con a :^term``
        THEN REWRITE_TAC[REDC_Con],

        EXISTS_TAC ``Var v :^term``
        THEN REWRITE_TAC[REDC_Var],

        ASM_CASES_TAC ``?(M:^term) x. t = Lam x M``
        THENL
          [ POP_ASSUM STRIP_ASSUME_TAC
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN UNDISCH_ALL_TAC
            THEN DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE REDC_inv_thms)
            THEN REWRITE_TAC[term_distinct]
            THEN REPEAT STRIP_TAC
            THEN EXISTS_TAC ``(t2':^term) <[ [x',t''']``
            THEN ASM_REWRITE_TAC[]
            THEN MATCH_MP_TAC REDC_BETA
            THEN ASM_REWRITE_TAC[],

            UNDISCH_LAST_TAC
            THEN CONV_TAC (TOP_DEPTH_CONV NOT_EXISTS_CONV)
            THEN DISCH_TAC
            THEN EXISTS_TAC ``App t'' t''' :^term``
            THEN MATCH_MP_TAC REDC_App
            THEN ASM_REWRITE_TAC[]
          ],

        EXISTS_TAC ``Lam v t' :^term``
        THEN MATCH_MP_TAC REDC_Lam
        THEN ASM_REWRITE_TAC[]
      ]
   );

val TAKAHASHI_TRIANGLE = store_thm
   ("TAKAHASHI_TRIANGLE",
    “!(a:^term) d. REDC a d ==>
                      !b. REDL a b ==> REDL b d”,
    rule_induct REDC_ind_thm (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC
    THENL (* 5 subgoals *)
      [ IMP_RES_TAC REDL_Con_case
        THEN ASM_REWRITE_TAC[REDL_REFL],

        IMP_RES_TAC REDL_Var_case
        THEN ASM_REWRITE_TAC[REDL_REFL],

        IMP_RES_TAC REDL_Lam_case
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC REDL_Lam
        THEN RES_TAC,

        IMP_RES_TAC REDL_App_case
        THENL
          [ ASM_REWRITE_TAC[]
            THEN MATCH_MP_TAC REDL_App
            THEN RES_TAC
            THEN ASM_REWRITE_TAC[],

            RES_TAC
          ],

        IMP_RES_TAC REDL_App_case
        THENL
          [ IMP_RES_TAC REDL_Lam_case
            THEN ASM_REWRITE_TAC[]
            THEN MATCH_MP_TAC REDL_BETA
            THEN RES_TAC
            THEN ASM_REWRITE_TAC[],

            ASM_REWRITE_TAC[]
            THEN UNDISCH_THEN ``Lam x t1 = Lam x' t':^term`` (ASSUME_TAC o SYM)
            THEN IMP_RES_THEN IMP_RES_TAC REDL_CHANGE_VAR
            THEN IMP_RES_THEN IMP_RES_TAC REDL_RENAME
            THEN IMP_RES_THEN ONCE_REWRITE_THM SUB_RENAME_TERM
            THEN DEP_REWRITE_TAC[REDL_SUBSTITUTIVE]
            THEN RES_TAC
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );


val REDL_DIAMOND_TAKAHASHI = store_thm
   ("REDL_DIAMOND_TAKAHASHI",
    “DIAMOND (REDL:^term_rel)”,
    REWRITE_TAC[DIAMOND]
    THEN REPEAT STRIP_TAC
    THEN STRIP_ASSUME_TAC (SPEC ``a:^term`` REDC_EXISTS)
    THEN IMP_RES_TAC TAKAHASHI_TRIANGLE
    THEN EXISTS_TAC “t':^term”
    THEN ASM_REWRITE_TAC[]
   );




(* copied: *)

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


(*
Barendregt Lemma 3.2.7, page 62, the proof begins with the note that

    --->B    SUBSET     -->>     SUBSET     -->>B
     =                   l

which in our notation corresponds to

   RC (RED1 BETA_R)     SUBSET     REDL     SUBSET     RED BETA_R

We first deal with the first (left) subset relation.

Remember,

Hol prf  =   Barendregt   =   Description
-----------------------------------------
RED1 R   =   --->R        =   one-step R-reduction
RED  R   =   -->>R        =   R-reduction
REQ  R   =   === R        =   R-equality (also called R-convertibility)
RC   R   =   R-arrow with "=" underneath          =   reflexive closure
TC   R   =   R-arrow with "*" superscript after   =   transitive closure
*)

(*
val RC_BETA_IMP_REDL = store_thm
   ("RC_BETA_IMP_REDL",
    “!t1:^term t2. RC BETA_R t1 t2 ==> REDL t1 t2”,
    RC_INDUCT_TAC
    THEN ONCE_REWRITE_TAC BETA_R_inv_thms
    THEN REPEAT STRIP_TAC
    THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat]
   );
*)

val RED1_BETA_IMP_REDL_LEMMA = TAC_PROOF(([],
    “!R (t1:^term) t2.
          RED1 R t1 t2 ==> (R = BETA_R) ==> REDL t1 t2”),
    rule_induct RED1_ind_thm
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THENL
      [ POP_ASSUM (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE BETA_R_inv_thms)
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat]
      ]
   );

val RED1_BETA_IMP_REDL = store_thm
   ("RED1_BETA_IMP_REDL",
    “!t1:^term t2.
          RED1 BETA_R t1 t2 ==> REDL t1 t2”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_BETA_IMP_REDL_LEMMA
    THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[])
   );

val RC_RED1_BETA_IMP_REDL = store_thm
   ("RC_RED1_BETA_IMP_REDL",
    “!t1:^term t2. RC (RED1 BETA_R) t1 t2 ==> REDL t1 t2”,
    RC_INDUCT_TAC
    THEN REWRITE_TAC[REDL_rules_sat]
    THEN REWRITE_TAC[RED1_BETA_IMP_REDL]
   );

val [RED1_R, RED1_App1, RED1_App2, RED1_Lam] = CONJUNCTS RED1_rules_sat;


val [RED_RED1, RED_REFL, RED_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) RED_rules_sat);


val RED1_BETA_R = store_thm
   ("RED1_BETA_R",
    “!x t:^term u.
          RED1 BETA_R (App (Lam x t) u) (t <[ [x,u])”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC RED1_R
    THEN REWRITE_TAC[BETA_R_rules_sat]
   );

val RED_BETA_R = store_thm
   ("RED_BETA_R",
    “!x t1:^term t2 u1 u2.
          RED BETA_R t1 t2 /\
          RED BETA_R u1 u2 ==>
          RED BETA_R (App (Lam x t1) u1) (t2 <[ [x,u2])
    ”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC RED_TRANS
    THEN EXISTS_TAC “App (Lam x t2) u2:^term”
    THEN CONJ_TAC
    THENL
      [ MATCH_MP_TAC RED_TRANS
        THEN EXISTS_TAC “App (Lam x t2) u1:^term”
        THEN IMP_RES_TAC RED_COMPAT
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        DEP_ASM_REWRITE_TAC[RED_RED1]
        THEN REWRITE_TAC[RED1_BETA_R]
      ]
   );


val REDL_IMP_RED_BETA = store_thm
   ("REDL_IMP_RED_BETA",
    “!t1:^term t2. REDL t1 t2 ==> RED BETA_R t1 t2”,
    rule_induct REDL_ind_thm
    THEN REPEAT STRIP_TAC
    THENL (* 4 subgoals *)
      [ REWRITE_TAC[RED_REFL],

        IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC RED_COMPAT
        THEN MATCH_MP_TAC RED_TRANS
        THEN EXISTS_TAC “App t2 u1:^term”
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC RED_BETA_R
        THEN ASM_REWRITE_TAC[]
     ]
   );


val RC_RED1_IMP_RED = store_thm
   ("RC_RED1_IMP_RED",
    “!R t1:^term t2. RC (RED1 R) t1 t2
                         ==> RED R t1 t2”,
    GEN_TAC
    THEN RC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[RED_REFL]
    THEN IMP_RES_TAC RED_RED1
   );

val TC_RC_RED1_IMP_RED = store_thm
   ("TC_RC_RED1_IMP_RED",
    “!R t1:^term t2. TC (RC (RED1 R)) t1 t2
                         ==> RED R t1 t2”,
    GEN_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RC_RED1_IMP_RED
    THEN IMP_RES_TAC RED_TRANS
   );

(*
val TC_RC_BETA_IMP_RED_BETA = store_thm
   ("TC_RC_BETA_IMP_RED_BETA",
    “!t1:^term t2. TC (RC (RED1 BETA_R)) t1 t2
                       ==> RED BETA_R t1 t2”,
    TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RC_RED1_BETA_IMP_REDL
    THEN IMP_RES_TAC REDL_IMP_RED_BETA
    THEN IMP_RES_TAC RED_TRANS
   );
*)

val RED_IMP_TC_RC_RED1 = store_thm
   ("RED_IMP_TC_RC_RED1",
    “!R t1:^term t2. RED R t1 t2
                         ==> TC (RC (RED1 R)) t1 t2”,
    rule_induct RED_ind_thm
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC (REWRITE_RULE[transitive_def] TC_TRANSITIVE)
    THEN MATCH_MP_TAC TC_SUBSET
    THEN REWRITE_TAC[RC_REFLEXIVE]
    THEN IMP_RES_TAC RC_SUBSET
   );

val TC_RC_RED1_IS_RED = store_thm
   ("TC_RC_RED1_IS_RED",
    “!R:^term_rel. TC (RC (RED1 R)) = RED R”,
    CONV_TAC (TOP_DEPTH_CONV FUN_EQ_CONV)
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ IMP_RES_TAC TC_RC_RED1_IMP_RED,

        IMP_RES_TAC RED_IMP_TC_RC_RED1
      ]
   );


val TC_REDL_IMP_RED_BETA = store_thm
   ("TC_REDL_IMP_RED_BETA",
    “!t1:^term t2. TC REDL t1 t2 ==> RED BETA_R t1 t2”,
    TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_IMP_RED_BETA
    THEN IMP_RES_TAC RED_TRANS
   );


val TC_MONOTONIC_LEMMA = TAC_PROOF(([],
    “!R1 R2 (a:'a) b.
          TC R1 a b ==> (!x y. R1 x y ==> R2 x y) ==> TC R2 a b”),
    GEN_TAC THEN GEN_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ RES_TAC
        THEN IMP_RES_TAC TC_SUBSET,

        RES_TAC
        THEN IMP_RES_TAC (REWRITE_RULE[transitive_def] TC_TRANSITIVE)
      ]
   );

val TC_MONOTONIC = store_thm
   ("TC_MONOTONIC",
    “!R1 R2 (a:'a) b.
          (!x y. R1 x y ==> R2 x y) ==>
                (TC R1 a b ==> TC R2 a b)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC TC_MONOTONIC_LEMMA
   );


(* Barendregt Lemma 3.2.7. *)

val TC_REDL_IS_RED_BETA = store_thm
   ("TC_REDL_IS_RED_BETA",
    “TC (REDL:^term_rel) = RED BETA_R”,
    CONV_TAC (TOP_DEPTH_CONV FUN_EQ_CONV)
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THENL
      [ REWRITE_TAC[TC_REDL_IMP_RED_BETA],

        REWRITE_TAC[GSYM TC_RC_RED1_IS_RED]
        THEN MATCH_MP_TAC TC_MONOTONIC
        THEN REWRITE_TAC[RC_RED1_BETA_IMP_REDL]
      ]
   );


(* The Church-Rosser Theorem!
   Barendregt Theorem 3.2.8 (i)
*)

val BETA_R_CHURCH_ROSSER = store_thm
   ("BETA_R_CHURCH_ROSSER",
    “CHURCH_ROSSER (BETA_R:^term_rel)”,
    REWRITE_TAC[CHURCH_ROSSER]
    THEN REWRITE_TAC[GSYM TC_REDL_IS_RED_BETA]
    THEN REPEAT CONJ_TAC
    THEN MATCH_MP_TAC TC_DIAMOND
    THEN REWRITE_TAC[REDL_DIAMOND]
   );
(* Soli Deo Gloria!!!  To God Alone Be The Glory!!! *)


(* Barendregt Theorem 3.2.8 (ii). *)

val BETA_R_NORMAL_FORM_EXISTS = store_thm
   ("BETA_R_NORMAL_FORM_EXISTS",
    “!M:^term N. REQUAL BETA_R M N ==>
                      (?Z. RED BETA_R M Z /\ RED BETA_R N Z)”,
    MATCH_MP_TAC NORMAL_FORM_EXISTS
    THEN REWRITE_TAC[BETA_R_CHURCH_ROSSER]
   );

(* Barendregt Corollary 3.2.9 (i). *)

val BETA_R_NORMAL_FORM_REDUCED_TO = store_thm
   ("BETA_R_NORMAL_FORM_REDUCED_TO",
    “!M:^term N. NORMAL_FORM_OF BETA_R N M ==>
                     RED BETA_R M N”,
    MATCH_MP_TAC NORMAL_FORM_REDUCED_TO
    THEN REWRITE_TAC[BETA_R_CHURCH_ROSSER]
   );

(* Barendregt Corollary 3.2.9 (ii). *)

val BETA_R_NORMAL_FORM_UNIQUE = store_thm
   ("BETA_R_NORMAL_FORM_UNIQUE",
    “!M:^term N1 N2. NORMAL_FORM_OF BETA_R N1 M /\
                         NORMAL_FORM_OF BETA_R N2 M ==> (N1 = N2)”,
    MATCH_MP_TAC NORMAL_FORM_UNIQUE
    THEN REWRITE_TAC[BETA_R_CHURCH_ROSSER]
   );


val _ = export_theory();

val _ = print_theory_to_file "-" "beta.lst";

val _ = html_theory "beta";

val _ = print_theory_size();
