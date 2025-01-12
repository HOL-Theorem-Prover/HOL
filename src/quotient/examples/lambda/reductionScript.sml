open HolKernel Parse boolLib;

val _ = new_theory "reduction";


open prim_recTheory pairTheory listTheory rich_listTheory;
open combinTheory;
open listLib;
open pred_setTheory pred_setLib;
open numTheory;
open numLib;
open arithmeticTheory;
open bossLib;
open relationTheory;
open Mutual
open ind_rel;
open dep_rewrite;
open more_listTheory;
open more_setTheory;
open variableTheory;
open termTheory;
open alphaTheory;
open liftTheory;
open barendregt;
open relationTheory;


open tactics;



val vars   =  ty_antiq( ==`:var list`== );
val term   =  ty_antiq( ==`:'a term`== );
val subs   =  ty_antiq( ==`:(var # 'a term) list`== );


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



val HEIGHT_SUB_VAR = store_thm
   ("HEIGHT_SUB_VAR",
    “!t:^term x y.
          HEIGHT (t <[ [x,Var y]) = HEIGHT t”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL
      [ REWRITE_TAC[SUB_term],

        REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_term]
        THEN ASM_REWRITE_TAC[HEIGHT],

        SIMPLE_SUBST_TAC
        THEN ASM_REWRITE_TAC[HEIGHT]
      ]
   );



(* Barendregt's Substitution Lemma, 2.1.16, page 27: *)

val BARENDREGT_SUBSTITUTION_LEMMA = store_thm
   ("BARENDREGT_SUBSTITUTION_LEMMA",
    “!N L x y (M:^term).
          ~(x = y) /\ ~(x IN FV L) ==>
          (((M <[ [x,N]) <[ [y,L]) =
           ((M <[ [y,L]) <[ [x, (N <[ [y,L])]))”,
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term],

        REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THENL
          [ POP_ASSUM REWRITE_ALL_THM
            THEN EVERY_ASSUM REWRITE_THM
            THEN REWRITE_TAC[SUB_term,SUB],

            REWRITE_TAC[SUB_term,SUB]
            THEN COND_CASES_TAC
            THENL
              [ IMP_RES_THEN REWRITE_THM subst_EMPTY,

                ASM_REWRITE_TAC[SUB_term,SUB]
              ]
          ],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_term],

        REPEAT STRIP_TAC
        THEN SIMPLE_SUBST_TAC
        THEN DEP_ASM_REWRITE_TAC[]
      ]
   );


val COLLAPSE_SUBST = store_thm
   ("COLLAPSE_SUBST",
    “!(M:^term) x y N.
          ~(y IN FV M) ==>
          (((M <[ [x,Var y]) <[ [y,N]) = (M <[ [x,N]))”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THENL
      [ REWRITE_TAC[FV_term,IN]
        THEN REPEAT GEN_TAC
        THEN REWRITE_TAC[SUB_term],

        REWRITE_TAC[FV_term,IN]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THENL
          [ REWRITE_TAC[SUB_term,SUB],

            REWRITE_TAC[SUB_term,SUB]
            THEN EVERY_ASSUM (REWRITE_THM o GSYM)
          ],

        REWRITE_TAC[FV_term,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_term],

        REPEAT GEN_TAC
        THEN SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[FV_term,IN,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN DEP_ASM_REWRITE_TAC[]
        THEN UNDISCH_TAC “~(y IN FV (M':^term) DIFF {z})”
        THEN FIRST_ASSUM (REWRITE_THM o REWRITE_RULE[FV_term] o
                          AP_TERM “FV:^term -> var -> bool”)
        THEN REWRITE_TAC[IN_DIFF,IN,DE_MORGAN_THM]
        THEN EVERY_ASSUM (REWRITE_THM o GSYM)
      ]
   );



(* --------------------------------------------------------------------- *)
(* General reduction relations and theorems:                             *)
(*   "Lambda Calculus," Barendregt, Chapter 3, page 50-63                *)
(* --------------------------------------------------------------------- *)


(* Define the reflexive closure of a relation.                           *)

val RC_DEF =
   new_definition("RC_DEF",
   “RC (R:'a->'a->bool) a b =
       !P.
          (!x y. R x y ==> P x y) /\
          (!x. P x x)
          ==> P a b”);


val RC_REFLEXIVE = store_thm
   ("RC_REFLEXIVE",
    “!R (x:'a). RC R x x”,
    REWRITE_TAC[RC_DEF]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val RC_SUBSET = store_thm
   ("RC_SUBSET",
    “!R (x:'a) y. R x y ==> RC R x y”,
    REWRITE_TAC[RC_DEF]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val RC_INDUCT = store_thm
   ("RC_INDUCT",
    “!(R:'a->'a->bool) P.
          (!x y. R x y ==> P x y) /\
          (!x. P x x)
          ==> !u v. RC R u v ==> P u v”,
    REWRITE_TAC[RC_DEF]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );


val RC_INDUCT_TAC =
 let val rc_thm = RC_INDUCT
     fun tac (asl,w) =
      let open Rsyntax
          val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
        (*val (RC,[R,u',v']) = strip_comb ant*)
          val (RC,Ruv) = strip_comb ant
          val R = hd Ruv and u' = hd (tl Ruv) and v' = hd (tl (tl Ruv))
          val _ = assert (curry op = "RC") (#Name (dest_const RC))
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


val RC_CASES = store_thm
   ("RC_CASES",
    “!R (x:'a) y. RC R x y ==> R x y \/ (x = y)”,
    GEN_TAC
    THEN RC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );



(* --------------------------------------------------------------------- *)
(* Define compatible relations on the term/method language.              *)
(* --------------------------------------------------------------------- *)

val term_rel = ty_antiq ( ==`:'a term -> 'a term -> bool`== );

val compatible =
    new_definition ("compatible",
    “compatible R =
        (!t1:^term t2. R t1 t2 ==> (!u. R (App u t1) (App u t2))  /\
                                   (!u. R (App t1 u) (App t2 u))  /\
                                   (!x. R (Lam x t1) (Lam x t2)))”);

val reflexive =
    new_definition ("reflexive",
    “reflexive R =
        (!t:^term. R t t)”);

val symmetric =
    new_definition ("symmetric",
    “symmetric R =
        (!t1 t2:^term. R t1 t2 ==> R t2 t1)”);

(* Already defined in relationTheory:
val transitive_def =
    new_definition ("transitive_def",
    “transitve R =
        (!t1 t2 t3:^term. R t1 t2 /\ R t2 t3 ==> R t1 t3)”);
*)
val transitive = relationTheory.transitive_def;

val equality =
    new_definition ("equality",
    “equality (R:^term_rel) =
        (compatible R /\
         reflexive  R /\
         symmetric  R /\
         transitive R)”);

val reduction =
    new_definition ("reduction",
    “reduction (R:^term_rel) =
        (compatible R /\
         reflexive  R /\
         transitive R)”);


val RC_compatible = store_thm
   ("RC_compatible",
    “!R:^term_rel. compatible R ==> compatible (RC R)”,
    REWRITE_TAC[compatible]
    THEN REPEAT STRIP_TAC
    THEN ( IMP_RES_TAC RC_CASES
            THENL
              [ MATCH_MP_TAC RC_SUBSET
                THEN RES_TAC
                THEN ASM_REWRITE_TAC[],

                ASM_REWRITE_TAC[RC_REFLEXIVE]
              ]
         )
   );

val TC_compatible1 = TAC_PROOF(([],
    “!(R:^term_rel) t1 t2. TC R t1 t2 ==>
           compatible R ==>
           (!u. TC R (App u t1) (App u t2)) /\
           (!u. TC R (App t1 u) (App t2 u)) /\
           (!x. TC R (Lam x t1) (Lam x t2))”),
    GEN_TAC
    THEN TC_INDUCT_TAC
    THEN CONJ_TAC
    THENL
      [ REWRITE_TAC[compatible]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN MATCH_MP_TAC TC_SUBSET
        THEN ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN MATCH_MP_TAC TC_TRANS
        THENL
          [ EXISTS_TAC ``App u y :^term``,
            EXISTS_TAC ``App y u :^term``,
            EXISTS_TAC ``Lam x' y :^term``
          ]
        THEN ASM_REWRITE_TAC[]
      ]
   );

val TC_compatible = store_thm
   ("TC_compatible",
    “!(R:^term_rel). compatible R ==> compatible (TC R)”,
    GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[compatible]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN IMP_RES_TAC TC_compatible1
    THEN ASM_REWRITE_TAC[]
   );



(* --------------------------------------------------------------------- *)
(* (RED1 R t1 t2) means that the term t1 reduces to the term t2          *)
(*  in exactly one step, as defined in Barendregt, Definition 3.1.5,     *)
(*  page 51.  This is the compatible closure of R.                       *)
(* --------------------------------------------------------------------- *)


val RED1 =
“RED1 : ^term_rel -> ^term -> ^term -> bool”;

val RED1_patterns = [“^RED1 R t1 t2”];

val RED1_rules_tm =
“
                           ((R t1 t2)
       (* -------------------------------------------- *) ==>
                        (^RED1 R t1 t2))                                 /\


                        ((^RED1 R t1 t2)
       (* -------------------------------------------- *) ==>
                (^RED1 R (App t1 u) (App t2 u)))                         /\


                        ((^RED1 R u1 u2)
       (* -------------------------------------------- *) ==>
                (^RED1 R (App t u1) (App t u2)))                         /\


                        ((^RED1 R t1 t2)
       (* -------------------------------------------- *) ==>
                (^RED1 R (Lam x t1) (Lam x t2)))
”;

val (RED1_rules_sat,RED1_ind_thm) =
    define_inductive_relations RED1_patterns RED1_rules_tm;

val RED1_inv_thms = prove_inversion_theorems
    RED1_rules_sat RED1_ind_thm;

val RED1_strong_ind = prove_strong_induction
    RED1_rules_sat RED1_ind_thm;

val _ = save_thm ("RED1_rules_sat", RED1_rules_sat);
val _ = save_thm ("RED1_ind_thm", RED1_ind_thm);
val _ = save_thm ("RED1_inv_thms", LIST_CONJ RED1_inv_thms);
val _ = save_thm ("RED1_strong_ind", RED1_strong_ind);


val [RED1_R, RED1_App1, RED1_App2, RED1_Lam] = CONJUNCTS RED1_rules_sat;




val RED1_height_ind_thm_LEMMA = store_thm
   ("RED1_height_ind_thm_LEMMA",
    “!n (P_0:^term_rel -> ^term -> ^term -> bool).
         (!R t1 t2. R t1 t2 ==> P_0 R t1 t2) /\
         (!R t1 u t2. P_0 R t1 t2 ==> P_0 R (App t1 u) (App t2 u)) /\
         (!R t u1 u2. P_0 R u1 u2 ==> P_0 R (App t u1) (App t u2)) /\
         (!R x t1 t2.
           (!t1' t2'. RED1 R t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') /\
                      (HEIGHT t2 = HEIGHT t2') ==> P_0 R t1' t2')
            ==> P_0 R (Lam x t1) (Lam x t2)) ==>
         (!R t1 t2. RED1 R t1 t2 ==>
                    ((HEIGHT t1 <= n) /\
                     (HEIGHT t2 <= n) ==>
                     P_0 R t1 t2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN UNDISCH_TAC “RED1 R (t1:^term) t2”
        THEN ONCE_REWRITE_TAC RED1_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct RED1_ind_thm
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 4 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );

val RED1_height_ind_thm = store_thm
   ("RED1_height_ind_thm",
    “!P_0.
         (!R (t1:^term) t2. R t1 t2 ==> P_0 R t1 t2) /\
         (!R t1 t2 u. P_0 R t1 t2 ==> P_0 R (App t1 u) (App t2 u)) /\
         (!R t u1 u2. P_0 R u1 u2 ==> P_0 R (App t u1) (App t u2)) /\
         (!R x t1 t2.
           (!t1' t2'. RED1 R t1' t2' /\
                      (HEIGHT t1 = HEIGHT t1') /\
                      (HEIGHT t2 = HEIGHT t2') ==> P_0 R t1' t2')
            ==> P_0 R (Lam x t1) (Lam x t2)) ==>
         (!R t1 t2. RED1 R t1 t2 ==> P_0 R t1 t2)”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL
              (SPEC “(HEIGHT (t1:^term)) MAX (HEIGHT (t2:^term))”
                                RED1_height_ind_thm_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_MAX]
   );

val RED1_height_strong_ind_LEMMA = store_thm
   ("RED1_height_strong_ind_LEMMA",
    “!n P_0.
         (!R (t1:^term) t2. R t1 t2 ==> P_0 R t1 t2) /\
         (!R t1 t2 u.
           P_0 R t1 t2 /\ RED1 R t1 t2 ==>
           P_0 R (App t1 u) (App t2 u)) /\
         (!R t u1 u2.
           P_0 R u1 u2 /\ RED1 R u1 u2 ==>
           P_0 R (App t u1) (App t u2)) /\
         (!R x t1 t2.
           (!t1' t2'.
             RED1 R t1' t2' /\
             (HEIGHT t1 = HEIGHT t1') /\
             (HEIGHT t2 = HEIGHT t2') ==>
             P_0 R t1' t2') /\
           RED1 R t1 t2 ==>
           P_0 R (Lam x t1) (Lam x t2)) ==>
         (!R t1 t2. RED1 R t1 t2 ==>
                    ((HEIGHT t1 <= n) /\
                     (HEIGHT t2 <= n) ==>
                     P_0 R t1 t2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN UNDISCH_TAC “RED1 R (t1:^term) t2”
        THEN ONCE_REWRITE_TAC RED1_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct RED1_strong_ind
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 4 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THEN UNDISCH_THEN
                 “!(R:^term->^term->bool) t1 t2. R t1 t2 ==> P_0 R t1 t2”
                 (fn th => ALL_TAC)
            THEN FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO])
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );

val RED1_height_strong_ind = store_thm
   ("RED1_height_strong_ind",
    “!P_0.
         (!R (t1:^term) t2. R t1 t2 ==> P_0 R t1 t2) /\
         (!R t1 t2 u.
            P_0 R t1 t2 /\ RED1 R t1 t2 ==> P_0 R (App t1 u) (App t2 u)) /\
         (!R t u1 u2.
            P_0 R u1 u2 /\ RED1 R u1 u2 ==> P_0 R (App t u1) (App t u2)) /\
         (!R x t1 t2.
           (!t1' t2'.
             RED1 R t1' t2' /\
             (HEIGHT t1 = HEIGHT t1') /\
             (HEIGHT t2 = HEIGHT t2') ==>
             P_0 R t1' t2') /\
           RED1 R t1 t2 ==>
           P_0 R (Lam x t1) (Lam x t2)) ==>
         (!R t1 t2. RED1 R t1 t2 ==> P_0 R t1 t2)”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL
            (SPEC “(HEIGHT (t1:^term)) MAX (HEIGHT (t2:^term))”
                                RED1_height_strong_ind_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_MAX]
   );




(* --------------------------------------------------------------------- *)
(* We claim that RED1 is a binary relation on the object/method          *)
(* language which is                                                     *)
(*  1) compatible (in the sense of Barendregt, Definition 3.1.1, pg 50   *)
(*  2) the compatible closure of the R relation, in the sense of         *)
(*     Barendregt, Definition 3.1.4, pg 51                               *)
(* --------------------------------------------------------------------- *)


val RED1_compatible = store_thm
   ("RED1_compatible",
    “!R:^term_rel. compatible (RED1 R)”,
    REWRITE_TAC[compatible]
    THEN rule_induct RED1_strong_ind
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_R
    THEN FIRST (map (fn th => MATCH_MP_TAC th
                              THEN ASM_REWRITE_TAC[]
                              THEN NO_TAC)
                    (CONJUNCTS RED1_rules_sat))
   );

val RC_RED1_compatible = store_thm
   ("RC_RED1_compatible",
    “!R:^term_rel. compatible (RC (RED1 R))”,
    GEN_TAC
    THEN MATCH_MP_TAC RC_compatible
    THEN REWRITE_TAC[RED1_compatible]
   );

val TC_RC_RED1_compatible = store_thm
   ("TC_RC_RED1_compatible",
    “!R:^term_rel. compatible (TC (RC (RED1 R)))”,
    GEN_TAC
    THEN MATCH_MP_TAC TC_compatible
    THEN REWRITE_TAC[RC_RED1_compatible]
   );


(* If R is monotonic, then RED1 R is monotonic
    with respect to free variables. *)

val RED1_FV_LEMMA = TAC_PROOF(([],
    “!R (M:^term) M'.
          RED1 R M M' ==> (!N N'. R N N' ==> (FV N' SUBSET FV N)) ==>
          (FV M' SUBSET FV M)”),
    rule_induct RED1_strong_ind (* strong, not weak induction *)
    THEN REWRITE_TAC[FV_term]
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ RES_TAC,

        RES_TAC
        THEN MATCH_MP_TAC SUBSETS_UNION
        THEN ASM_REWRITE_TAC[SUBSET_REFL],

        RES_TAC
        THEN MATCH_MP_TAC SUBSETS_UNION
        THEN ASM_REWRITE_TAC[SUBSET_REFL],

        RES_TAC
        THEN MATCH_MP_TAC SUBSET_DIFF
        THEN ASM_REWRITE_TAC[]
      ]
   );

val RED1_FV = store_thm
   ("RED1_FV",
    “!R.
          (!(N:^term) N'. R N N' ==> (FV N' SUBSET FV N)) ==>
          (!M M'. RED1 R M M' ==> (FV M' SUBSET FV M))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_FV_LEMMA
   );



(* We now need to define the reflexive and transitive closure of this. *)

(* --------------------------------------------------------------------- *)
(* (RED R t1 t2) means that the term t1 reduces to the term t2           *)
(*  in zero or more steps, as defined in Barendregt, Definition 3.1.5,   *)
(*  page 51.  This is the reflexive and transitive closure of RED1 R.    *)
(* --------------------------------------------------------------------- *)

val RED =
“RED : ^term_rel -> ^term -> ^term -> bool”;

val RED_patterns = [“^RED R t1 t2”];

val RED_rules_tm =
“

                         (RED1 R t1 t2
       (* -------------------------------------------- *) ==>
                         ^RED R t1 t2)                                   /\


       (* -------------------------------------------- *)
                        (^RED R t1 t1)                                   /\


                 (^RED R t1 t2 /\ ^RED R t2 t3
       (* -------------------------------------------- *) ==>
                         ^RED R t1 t3)
”;


val (RED_rules_sat,RED_ind_thm) =
    define_inductive_relations RED_patterns RED_rules_tm;

val RED_inv_thms = prove_inversion_theorems
    RED_rules_sat RED_ind_thm;

val RED_strong_ind = prove_strong_induction
    RED_rules_sat RED_ind_thm;

val _ = save_thm ("RED_rules_sat", RED_rules_sat);
val _ = save_thm ("RED_ind_thm", RED_ind_thm);
val _ = save_thm ("RED_inv_thms", LIST_CONJ RED_inv_thms);
val _ = save_thm ("RED_strong_ind", RED_strong_ind);


(* --------------------------------------------------------------------- *)
(* We claim that RED is a binary relation on the object/method           *)
(* language which is                                                     *)
(*  1) compatible (in the sense of Barendregt, Definition 3.1.1, pg 50   *)
(*  2) the reflexive, transitive closure of the REDC relation, in the    *)
(*     sense of Barendregt, Definition 3.1.4 and 3.1.5, pg 51           *)
(*  3) a reduction relation, from 1) and 2).                             *)
(* --------------------------------------------------------------------- *)


val [RED_RED1, RED_REFL, RED_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) RED_rules_sat);


val [RED_inv]
    = RED_inv_thms;


val RED_reflexive = store_thm
   ("RED_reflexive",
    “!R:^term_rel. reflexive (RED R)”,
    REWRITE_TAC[reflexive]
    THEN REWRITE_TAC[RED_REFL]
   );

val RED_transitive = store_thm
   ("RED_transitive",
    “!R:^term_rel. transitive (RED R)”,
    REWRITE_TAC[transitive]
    THEN REWRITE_TAC[CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
                               RED_rules_sat]
   );

val RED_TRANS = save_thm("RED_TRANS",
                    REWRITE_RULE[transitive] RED_transitive);

val RED_compatible = store_thm
   ("RED_compatible",
    “!R:^term_rel. compatible (RED R)”,
    REWRITE_TAC[compatible]
    THEN rule_induct RED_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 9 subgoals *)
    THEN REWRITE_TAC[RED_REFL] (* takes care of 3 *)
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC RED_TRANS (* solves another 3 *)
    THEN IMP_RES_TAC (REWRITE_RULE[compatible] RED1_compatible)
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC RED_RED1 (* finishes the last 3 *)
   );

val RED_COMPAT = save_thm("RED_COMPAT",
                    (REWRITE_RULE[compatible] RED_compatible));



val RED_reduction = store_thm
   ("RED_reduction",
    “!R:^term_rel. reduction (RED R)”,
    REWRITE_TAC[reduction]
    THEN REWRITE_TAC[RED_compatible,RED_reflexive,RED_transitive]
   );


(* Barendregt's Substitution Remark, 3.1.7, page 52: *)

val BARENDREGT_SUBSTITUTION_REMARK = store_thm
   ("BARENDREGT_SUBSTITUTION_REMARK",
    “!(M:^term) N N' x R.
          RED R N N' ==>
          RED R (M <[ [x,N]) (M <[ [x,N'])”,
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term]
        THEN REWRITE_TAC[RED_REFL],

        REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[],

            REWRITE_TAC[RED_REFL]
          ],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN REWRITE_TAC[SUB_term]
        THEN MATCH_MP_TAC RED_TRANS
        THEN EXISTS_TAC “App ((M:^term) <[ [x,N']) (M' <[ [x,N])”
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC
        THEN SIMPLE_SUBST_TAC
        THEN RES_TAC
        THEN POP_ASSUM (ASSUME_TAC o SPEC “x:var”)
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[]
      ]
   );




(* We now need to define the equivalence relation generated by R. *)

(* --------------------------------------------------------------------- *)
(* (REQUAL R t1 t2) means that the term t1 is R-convertible to the       *)
(*  term t2, as defined in Barendregt, Definition 3.1.5, page 51.        *)
(*  This is the symmetric and transitive closure of RED R.               *)
(* --------------------------------------------------------------------- *)

val REQUAL =
“REQUAL : ^term_rel -> ^term -> ^term -> bool”;

val REQUAL_patterns = [“^REQUAL R t1 t2”];

val REQUAL_rules_tm =
“
                        (RED R t1 t2
       (* -------------------------------------------- *) ==>
                       ^REQUAL R t1 t2)                                 /\

                       (REQUAL R t1 t2
       (* -------------------------------------------- *) ==>
                       ^REQUAL R t2 t1)                                 /\

              (^REQUAL R t1 t2 /\ ^REQUAL R t2 t3
       (* -------------------------------------------- *) ==>
                       ^REQUAL R t1 t3)
”;


val (REQUAL_rules_sat,REQUAL_ind_thm) =
    define_inductive_relations REQUAL_patterns REQUAL_rules_tm;

val REQUAL_inv_thms = prove_inversion_theorems
    REQUAL_rules_sat REQUAL_ind_thm;

val REQUAL_strong_ind = prove_strong_induction
    REQUAL_rules_sat REQUAL_ind_thm;

val _ = save_thm ("REQUAL_rules_sat", REQUAL_rules_sat);
val _ = save_thm ("REQUAL_ind_thm", REQUAL_ind_thm);
val _ = save_thm ("REQUAL_inv_thms", LIST_CONJ REQUAL_inv_thms);
val _ = save_thm ("REQUAL_strong_ind", REQUAL_strong_ind);


(* --------------------------------------------------------------------- *)
(* We claim that REQUAL is a binary relation on the object/method           *)
(* language which is                                                     *)
(*  1) compatible (in the sense of Barendregt, Definition 3.1.1, pg 50   *)
(*  2) the symmetric, transitive closure of the RED relation, in the     *)
(*     sense of Barendregt, Definition 3.1.4 and 3.1.5, pg 51.           *)
(*  3) an equivalence relation, from 2) and that RED is reflexive.       *)
(*  4) an equality relation, as a compatible equivalence relation.       *)
(* --------------------------------------------------------------------- *)


val [REQUAL_RED, REQUAL_SYM, REQUAL_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) REQUAL_rules_sat);


val [REQUAL_inv] = REQUAL_inv_thms;


val REQUAL_reflexive = store_thm
   ("REQUAL_reflexive",
    “!R:^term_rel. reflexive (REQUAL R)”,
    REWRITE_TAC[reflexive]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC REQUAL_RED
    THEN REWRITE_TAC[RED_REFL]
   );

val REQUAL_symmetric = store_thm
   ("REQUAL_symmetric",
    “!R:^term_rel. symmetric (REQUAL R)”,
    REWRITE_TAC[symmetric]
    THEN REWRITE_TAC[REQUAL_SYM]
   );

val REQUAL_transitive = store_thm
   ("REQUAL_transitive",
    “!R:^term_rel. transitive (REQUAL R)”,
    REWRITE_TAC[transitive_def]
    THEN REWRITE_TAC[CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
                               REQUAL_rules_sat]
   );

val REQUAL_TRANS = save_thm("REQUAL_TRANS",
                   REWRITE_RULE[transitive_def] REQUAL_transitive);

val REQUAL_compatible = store_thm
   ("REQUAL_compatible",
    “!R:^term_rel. compatible (REQUAL R)”,
    REWRITE_TAC[compatible]
    THEN CONV_TAC (TOP_DEPTH_CONV FORALL_AND_CONV)
    THEN rule_induct REQUAL_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 9 subgoals *)
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC REQUAL_SYM (* takes care of 3 *)
    THEN IMP_RES_TAC REQUAL_TRANS (* solves another 3 *)
    THEN IMP_RES_TAC RED_COMPAT
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC REQUAL_RED (* finishes the last 3 *)
   );

val REQUAL_COMPAT = save_thm("REQUAL_COMPAT",
                    REWRITE_RULE[compatible] REQUAL_compatible);


val REQUAL_reduction = store_thm
   ("REQUAL_reduction",
    “!R:^term_rel. reduction (REQUAL R)”,
    REWRITE_TAC[reduction]
    THEN REWRITE_TAC[REQUAL_compatible,REQUAL_reflexive,REQUAL_transitive]
   );

val REQUAL_equality = store_thm
   ("REQUAL_equality",
    “!R:^term_rel. equality (REQUAL R)”,
    REWRITE_TAC[equality]
    THEN REWRITE_TAC[REQUAL_compatible,REQUAL_reflexive,
                    REQUAL_symmetric,REQUAL_transitive]
   );



                         (* ============ *)
                         (* NORMAL FORMS *)
                         (* ============ *)



val NORMAL_FORM =
    new_definition
    ("NORMAL_FORM",
     “NORMAL_FORM R a = (!a':^term. ~(RED1 R a a'))”);


val NORMAL_FORM_OF =
    new_definition
    ("NORMAL_FORM_OF",
     “NORMAL_FORM_OF R (a:^term) b =
         (NORMAL_FORM R a /\ REQUAL R b a)”);


val NORMAL_FORM_IDENT_LEMMA = store_thm
   ("NORMAL_FORM_IDENT_LEMMA",
    “!R (M:^term) N. RED R M N ==> (NORMAL_FORM R M ==> (M = N))”,
    rule_induct RED_ind_thm (* weak, not strong induction *)
    THEN REWRITE_TAC[NORMAL_FORM]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN RES_TAC
   );

val NORMAL_FORM_IDENT = store_thm
   ("NORMAL_FORM_IDENT",
    “!R (M:^term). NORMAL_FORM R M ==> (!N. RED R M N ==> (M = N))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC NORMAL_FORM_IDENT_LEMMA
   );


(* THE DIAMOND PROPERTY *)


val DIAMOND =
    new_definition
    ("DIAMOND",
     “DIAMOND R = (!a b c:'a. R a b /\ R a c ==> (?d. R b d /\ R c d))”);


(* THE CHURCH-ROSSER PROPERTY *)


val CHURCH_ROSSER =
    new_definition
    ("CHURCH_ROSSER",
     “CHURCH_ROSSER (R:^term_rel) = DIAMOND (RED R)”);



val NORMAL_FORM_EXISTS_LEMMA = store_thm
   ("NORMAL_FORM_EXISTS_LEMMA",
    “!R M N. REQUAL R M N ==>
                  (CHURCH_ROSSER R ==>
                   (?Z:^term. RED R M Z /\ RED R N Z))”,
    rule_induct REQUAL_ind_thm (* weak, not strong induction *)
    THEN REWRITE_TAC[CHURCH_ROSSER,DIAMOND]
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ EXISTS_TAC “t2:^term”
        THEN ASM_REWRITE_TAC[RED_REFL],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th => REPEAT DISCH_TAC THEN MP_TAC th)
        THEN ASM_REWRITE_TAC[]
        THEN STRIP_TAC
        THEN EXISTS_TAC “Z:^term”
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th1 =>
                DISCH_THEN (fn th2 =>
                    REPEAT DISCH_TAC THEN MP_TAC th2 THEN MP_TAC th1))
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM (fn imp => STRIP_ASSUME_TAC
                 (MATCH_MP imp (CONJ (ASSUME “RED R t2 (Z:^term)”)
                                     (ASSUME “RED R t2 (Z':^term)”))))
        THEN EXISTS_TAC “d:^term”
        THEN IMP_RES_TAC RED_TRANS
        THEN ASM_REWRITE_TAC[]
      ]
   );

val NORMAL_FORM_EXISTS = store_thm
   ("NORMAL_FORM_EXISTS",
    “!R. CHURCH_ROSSER R ==>
         (!M N. REQUAL R M N ==>
                (?Z:^term. RED R M Z /\ RED R N Z))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC NORMAL_FORM_EXISTS_LEMMA
    THEN EXISTS_TAC “Z:^term”
    THEN ASM_REWRITE_TAC[]
   );

val NORMAL_FORM_REDUCED_TO = store_thm
   ("NORMAL_FORM_REDUCED_TO",
    “!R. CHURCH_ROSSER R ==>
         (!(M:^term) N. NORMAL_FORM_OF R N M ==> RED R M N)”,
    REWRITE_TAC[NORMAL_FORM_OF]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC NORMAL_FORM_EXISTS
    THEN IMP_RES_TAC NORMAL_FORM_IDENT
    THEN ASM_REWRITE_TAC[]
   );

val NORMAL_FORM_UNIQUE = store_thm
   ("NORMAL_FORM_UNIQUE",
    “!R. CHURCH_ROSSER R ==>
         (!(M:^term) N1 N2.
                    NORMAL_FORM_OF R N1 M /\
                    NORMAL_FORM_OF R N2 M ==> (N1 = N2))”,
    REWRITE_TAC[NORMAL_FORM_OF]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REQUAL_SYM
    THEN UNDISCH_LAST_TAC
 (*   THEN POP_TAC *)
    THEN DISCH_TAC
    THEN IMP_RES_TAC REQUAL_TRANS
 (*   THEN POP_TAC THEN POP_TAC THEN POP_TAC *)
    THEN IMP_RES_TAC NORMAL_FORM_EXISTS
 (*   THEN POP_TAC THEN POP_TAC THEN POP_TAC
    THEN POP_TAC THEN POP_TAC THEN POP_TAC
    THEN POP_TAC THEN POP_TAC THEN POP_TAC *)
    THEN IMP_RES_TAC NORMAL_FORM_IDENT
    THEN ASM_REWRITE_TAC[]
   );


(* SUBSTITUTIVE RELATIONS *)


val SUBSTITUTIVE =
    new_definition
    ("SUBSTITUTIVE",
     “SUBSTITUTIVE R =
           (!(M:^term) (N:^term) L x.
             R M N ==> R (M <[ [x,L]) (N <[ [x,L]))”);


val RED1_SUBSTITUTIVE_LEMMA = TAC_PROOF(([],
    “!R (M:^term) N.
          RED1 R M N ==>
            ((!M N L x. R M N ==> R (M <[ [x,L]) (N <[ [x,L])) ==>
               (!L x. RED1 R (M <[ [x,L]) (N <[ [x,L])))”),
    rule_induct RED1_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ RES_TAC
        THEN MATCH_MP_TAC RED1_R
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_term]
        THEN MATCH_MP_TAC RED1_App1
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_term]
        THEN MATCH_MP_TAC RED1_App2
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN MATCH_MP_TAC RED1_Lam
        THEN FIRST_ASSUM
                (MATCH_MP_TAC o
                   REWRITE_RULE[AND_IMP_INTRO] o
                    CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM o CONJUNCT1 o
                          REWRITE_RULE[Lam_one_one])
        THEN POP_ASSUM (REWRITE_THM o SYM o CONJUNCT1 o
                          REWRITE_RULE[Lam_one_one])
        THEN FIRST_ASSUM
                (MATCH_MP_TAC o
                   REWRITE_RULE[AND_IMP_INTRO] o
                    CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
        THEN ASM_REWRITE_TAC[]
      ]
   );


val RED1_SUBSTITUTIVE = store_thm
   ("RED1_SUBSTITUTIVE",
    “!R:^term_rel. SUBSTITUTIVE R ==>
                      SUBSTITUTIVE (RED1 R)”,
    REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_SUBSTITUTIVE_LEMMA
    THEN ASM_REWRITE_TAC[]
   );



val RED1_SUBSTITUTIVE_ind_thm_LEMMA = store_thm
   ("RED1_SUBSTITUTIVE_ind_thm_LEMMA",
    “!n P_0.
         (!R (t1:^term) t2.
           SUBSTITUTIVE R /\
           R t1 t2 ==> P_0 R t1 t2) /\
         (!R t1 u t2.
           SUBSTITUTIVE R /\
           P_0 R t1 t2 ==> P_0 R (App t1 u) (App t2 u)) /\
         (!R t u1 u2.
           SUBSTITUTIVE R /\
           P_0 R u1 u2 ==> P_0 R (App t u1) (App t u2)) /\
         (!R x t1 t2. SUBSTITUTIVE R /\
           (!z. P_0 R (t1 <[ [x,Var z]) (t2 <[ [x,Var z]))
            ==> P_0 R (Lam x t1) (Lam x t2)) ==>
         (!R t1 t2. RED1 R t1 t2 ==>
                    (SUBSTITUTIVE R /\
                     (HEIGHT t1 <= n) /\
                     (HEIGHT t2 <= n) ==>
                     P_0 R t1 t2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN UNDISCH_TAC “RED1 R (t1:^term) t2”
        THEN ONCE_REWRITE_TAC RED1_inv_thms
        THEN ASM_REWRITE_TAC[term_distinct],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct RED1_strong_ind
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 4 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
                THEN REWRITE_TAC[SUBSTITUTIVE]
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN ASM_REWRITE_TAC[HEIGHT_SUB_VAR]
            THEN IMP_RES_TAC RED1_SUBSTITUTIVE
            THEN REWRITE_ALL_TAC[SUBSTITUTIVE]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );

val RED1_SUBSTITUTIVE_ind_thm_LEMMA1 = store_thm
   ("RED1_SUBSTITUTIVE_ind_thm_LEMMA1",
    “!P_0.
         (!R (t1:^term) t2. SUBSTITUTIVE R /\ R t1 t2 ==> P_0 R t1 t2) /\
         (!R t1 u t2.
            SUBSTITUTIVE R /\ P_0 R t1 t2 ==> P_0 R (App t1 u) (App t2 u)) /\
         (!R t u1 u2.
            SUBSTITUTIVE R /\ P_0 R u1 u2 ==> P_0 R (App t u1) (App t u2)) /\
         (!R x t1 t2.
            SUBSTITUTIVE R /\
            (!z. P_0 R (t1 <[ [(x,Var z)]) (t2 <[ [(x,Var z)])) ==>
            P_0 R (Lam x t1) (Lam x t2)) ==>
         (!R t1 t2.
            RED1 R t1 t2 ==>
            SUBSTITUTIVE R ==>
            P_0 R t1 t2)”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL
           (SPEC “(HEIGHT (t1:^term)) MAX (HEIGHT (t2:^term))”
                                RED1_SUBSTITUTIVE_ind_thm_LEMMA))
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_MAX]
   );


val RED1_SUBSTITUTIVE_ind_thm = store_thm
   ("RED1_SUBSTITUTIVE_ind_thm",
    “!R. SUBSTITUTIVE R ==>
         !P_0.
          (!R (t1:^term) t2. R t1 t2 ==> P_0 R t1 t2) /\
          (!R t1 u t2.
            P_0 R t1 t2 ==> P_0 R (App t1 u) (App t2 u)) /\
          (!R t u1 u2.
            P_0 R u1 u2 ==> P_0 R (App t u1) (App t u2)) /\
          (!R x t1 t2. SUBSTITUTIVE R /\
            (!z. P_0 R (t1 <[ [x,Var z]) (t2 <[ [x,Var z]))
             ==> P_0 R (Lam x t1) (Lam x t2)) ==>
          (!t1 t2. RED1 R t1 t2 ==> P_0 R t1 t2)”,
    GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN UNDISCH_TAC “SUBSTITUTIVE (R:^term_rel)”
    THEN CONV_TAC (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REWRITE_TAC[AND_IMP_INTRO]
    THEN ONCE_REWRITE_TAC[ISPEC “SUBSTITUTIVE (R:^term_rel)” CONJ_SYM]
    THEN REWRITE_TAC[GSYM AND_IMP_INTRO]
    THEN SPEC_TAC (“R:^term_rel”,“R:^term_rel”)
    THEN MATCH_MP_TAC RED1_SUBSTITUTIVE_ind_thm_LEMMA1
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );



val RED_SUBSTITUTIVE_LEMMA = TAC_PROOF(([],
    “!R (M:^term) N.
          RED R M N ==>
            (SUBSTITUTIVE R ==>
               (!L x. RED R (M <[ [x,L]) (N <[ [x,L])))”),
    rule_induct RED_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ IMP_RES_TAC RED1_SUBSTITUTIVE
        THEN REWRITE_ALL_TAC[SUBSTITUTIVE]
        THEN RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_RED1,

        REWRITE_TAC[RED_REFL],

        RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_TRANS
      ]
   );


val RED_SUBSTITUTIVE = store_thm
   ("RED_SUBSTITUTIVE",
    “!R:^term_rel.
               SUBSTITUTIVE R ==>
               SUBSTITUTIVE (RED R)”,
    GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED_SUBSTITUTIVE_LEMMA
    THEN ASM_REWRITE_TAC[]
   );



val REQUAL_SUBSTITUTIVE_LEMMA = TAC_PROOF(([],
    “!R (M:^term) N.
          REQUAL R M N ==>
            (SUBSTITUTIVE R ==>
               (!L x. REQUAL R (M <[ [x,L]) (N <[ [x,L])))”),
    rule_induct REQUAL_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 3 subgoals *)
    THENL
      [ IMP_RES_TAC RED_SUBSTITUTIVE
        THEN REWRITE_ALL_TAC[SUBSTITUTIVE]
        THEN RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC REQUAL_RED,

        RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC REQUAL_SYM,

        RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC REQUAL_TRANS
      ]
   );


val REQUAL_SUBSTITUTIVE = store_thm
   ("REQUAL_SUBSTITUTIVE",
    “!R:^term_rel.
               SUBSTITUTIVE R ==>
               SUBSTITUTIVE (REQUAL R)”,
    GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REQUAL_SUBSTITUTIVE_LEMMA
    THEN ASM_REWRITE_TAC[]
   );




val _ = export_theory();

val _ = print_theory_to_file "-" "reduction.lst";

val _ = html_theory "reduction";

val _ = print_theory_size();
