open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Embedding the semantaics of objects as a foundational layer,          *)
(* according to Abadi and Cardelli, "A Theory of Objects."               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "semantics";


open pairTheory listTheory;
open combinTheory;
open pred_setTheory;
open numLib;
open arithmeticTheory;
open bossLib;
open Mutual;
open ind_rel;
open dep_rewrite;
open more_setTheory;
open objectTheory;
open alphaTheory;
open liftTheory;
open barendregt;
open relationTheory;
open reductionTheory;

open tactics;



val vars   =  ty_antiq( ==`:var list`== );
val dict1  =  ty_antiq( ==`:(string # method1) list`== );
val entry1 =  ty_antiq( ==`:string # method1`== );
val dict   =  ty_antiq( ==`:(string # method) list`== );
val entry  =  ty_antiq( ==`:string # method`== );


val [ALPHA_obj_REFL, ALPHA_dict_REFL, ALPHA_entry_REFL,
     ALPHA_method_REFL]
    = CONJUNCTS ALPHA_REFL;

val [ALPHA_obj_SYM, ALPHA_dict_SYM, ALPHA_entry_SYM,
     ALPHA_method_SYM]
    = CONJUNCTS ALPHA_SYM;

val [ALPHA_obj_TRANS, ALPHA_dict_TRANS, ALPHA_entry_TRANS,
     ALPHA_method_TRANS]
    = CONJUNCTS ALPHA_TRANS;




(* Define the transitive closure of a relation.                          *)
(* Wait, it's already done: see file src/relation/relationScript.sml.    *)
(* This defines TC in the logic as TC R is the transitive closure of R,  *)
(* and "transitive R" as the property that R is transitite on 'a.        *)
(* There are also a bunch of theorems in structure TCScript, as well as  *)
(* induction tactis, cases theorems, etc.  It's theory "TC".             *)

(* copied: *)

val TC_INDUCT_TAC =
 let val tc_thm = TC_INDUCT
     fun tac (asl,w) =
      let open Rsyntax
          val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
          val (TC,Ru'v') = boolSyntax.strip_comb ant
          val R = hd Ru'v'
          val u'v' = tl Ru'v'
          val u' = hd u'v'
          val v' = hd (tl u'v')
          (*val (TC,[R,u',v']) = boolSyntax.strip_comb ant*)
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
(* Primitive semantics of the sigma-calculus:                            *)
(*   Abadi/Cardelli, Section 6.1.2, page 58-59                           *)
(* Here we define the primitive reduction operator of the calculus.      *)
(* It has two forms, one for method invocation and one for update.       *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Definition of method invocation.                                      *)
(* --------------------------------------------------------------------- *)

(* obj_0 is a null, meaningless object. *)

(* method_0 is a null, meaningless method. *)

val invoke_method = invoke_method_def;

Theorem FV_invoke_method:
  !m o'. FV_obj (invoke_method m o') SUBSET (FV_method m UNION FV_obj o')
Proof
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[invoke_method]
    THEN REWRITE_TAC[FV_object_subst]
    THEN REWRITE_TAC[FV_subst]
    THEN REWRITE_TAC[FV_object]
    THEN REWRITE_TAC[SUBSET_DEF]
    THEN GEN_TAC
    THEN REWRITE_TAC[IN_UNION_SET, IN_IMAGE, o_THM, IN_UNION, IN_DIFF, IN]
    THEN REWRITE_TAC[SUB]
    THEN STRIP_TAC
    THEN UNDISCH_ALL_TAC
    THEN COND_CASES_TAC
    THENL
      [ POP_ASSUM (REWRITE_THM o SYM)
        THEN DISCH_THEN REWRITE_THM
        THEN REPEAT DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        DISCH_THEN REWRITE_THM
        THEN REWRITE_TAC[FV_object,IN]
        THEN DISCH_TAC
        THEN DISCH_THEN REWRITE_THM
        THEN ASM_REWRITE_TAC[]
      ]
QED

val SUB_invoke_method = store_thm
   ("SUB_invoke_method",
    “!m o' x L. ((invoke_method m o') <[ [x,L]) =
                    invoke_method (m <[ [x,L]) (o' <[ [x,L])”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN SIMPLE_SUBST_TAC
    THEN REWRITE_TAC[invoke_method]
    THEN DEP_REWRITE_TAC[BARENDREGT_SUBSTITUTION_LEMMA]
    THEN ASM_REWRITE_TAC[]
   );


val FV_invoke_dict = store_thm
   ("FV_invoke_dict",
    “!d o' lb. FV_obj (invoke_dict d o' lb) SUBSET
                  (FV_dict d UNION FV_obj o')”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[invoke_dict]
    THEN REWRITE_TAC[obj_0, FV_object]
    THEN REWRITE_TAC[EMPTY_SUBSET]
    (* only one subgoal *)
    THEN REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC “p:^entry”
                                (hd (tl (tl (CONJUNCTS object_cases)))))
    THEN POP_ASSUM REWRITE_THM
    THEN REWRITE_TAC[invoke_dict]
    THEN REWRITE_TAC[FV_object]
    THEN COND_CASES_TAC
    THENL
      [ ASSUME_TAC (SPEC_ALL FV_invoke_method)
        THEN IMP_RES_TAC SUBSET_TRANS
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[UNION_SUBSET]
        THEN REWRITE_TAC[SUBSET_UNION]
        THEN REWRITE_TAC[GSYM UNION_ASSOC]
        THEN REWRITE_TAC[SUBSET_UNION],

        POP_TAC
        THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
        THEN IMP_RES_TAC SUBSET_TRANS
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[UNION_SUBSET]
        THEN REWRITE_TAC[SUBSET_UNION]
        THEN ONCE_REWRITE_TAC[UNION_COMM]
        THEN REWRITE_TAC[UNION_ASSOC]
        THEN REWRITE_TAC[SUBSET_UNION]
      ]
   );

val SUB_invoke_dict = store_thm
   ("SUB_invoke_dict",
    “!d o' l x L. ((invoke_dict d o' l) <[ [x,L]) =
                      invoke_dict (d <[ [x,L]) (o' <[ [x,L]) l”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL
      [ REWRITE_TAC[invoke_dict,SUB_object]
        THEN REWRITE_TAC[obj_0,SUB_object],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN REWRITE_TAC[invoke_dict,SUB_object,FST,SND]
        THEN COND_CASES_TAC
        THENL
          [ REWRITE_TAC[SUB_invoke_method],

            ASM_REWRITE_TAC[]
          ]
      ]
   );


val FV_invoke = store_thm
   ("FV_invoke",
    “!a lb. FV_obj (invoke a lb) SUBSET FV_obj a”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[invoke_def]
    THEN REWRITE_TAC[obj_0, FV_object, EMPTY_SUBSET]
    (* only one subgoal *)
    THEN GEN_TAC
    THEN MP_TAC (SPECL [“l:^dict”,“OBJ l”,“lb:string”]
                           FV_invoke_dict)
    THEN REWRITE_TAC[FV_object]
    THEN REWRITE_TAC[UNION_IDEMPOT]
   );

val SUB_invoke = store_thm
   ("SUB_invoke",
    “!d l x L. ((invoke (OBJ d) l) <[ [x,L]) =
                    invoke ((OBJ d) <[ [x,L]) l”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[invoke,SUB_object]
    THEN REWRITE_TAC[SUB_invoke_dict]
    THEN REWRITE_TAC[SUB_object]
   );



val FV_update_dict = store_thm
   ("FV_update_dict",
    “!d lb mth. FV_dict (update_dict d lb mth) SUBSET
                   (FV_dict d UNION FV_method mth)”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[update_dict]
    THEN REWRITE_TAC[FV_object, EMPTY_SUBSET]
    (* only one subgoal *)
    THEN REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[update_dict]
    THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[FV_object]
    THEN POP_TAC
    THEN REWRITE_TAC[UNION_SUBSET]
    THENL
      [ IMP_RES_TAC SUBSET_TRANS
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[GSYM UNION_ASSOC]
        THEN REWRITE_TAC[SUBSET_UNION],

        CONJ_TAC
        THENL
          [ REWRITE_TAC[GSYM UNION_ASSOC]
            THEN REWRITE_TAC[SUBSET_UNION],

            IMP_RES_TAC SUBSET_TRANS
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN REWRITE_TAC[GSYM UNION_ASSOC]
            THEN REWRITE_TAC[SUBSET_UNION]
          ]
      ]
   );

val SUB_update_dict = store_thm
   ("SUB_update_dict",
    “!d lb mth x L. ((update_dict d lb mth) <[ [x,L]) =
                        update_dict (d <[ [x,L]) lb (mth <[ [x,L])”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THENL
      [ REWRITE_TAC[update_dict,SUB_object],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN PURE_REWRITE_TAC[update_dict,SUB_object,FST,SND]
        THEN REPEAT GEN_TAC
        THEN COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[],

            ASM_REWRITE_TAC[SUB_object]
          ]
      ]
   );


val FV_update = store_thm
   ("FV_update",
    “!a lb mth. FV_obj (update a lb mth) SUBSET
                   (FV_obj a UNION FV_method mth)”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[update_def]
    THEN REWRITE_TAC[obj_0, FV_object, EMPTY_SUBSET]
    (* only one subgoal *)
    THEN REPEAT GEN_TAC
    THEN ASSUME_TAC (SPEC_ALL (SPEC “l:^dict” FV_update_dict))
    THEN ASM_REWRITE_TAC[UNION_SUBSET]
    THEN REWRITE_TAC[SUBSET_UNION]
   );

val SUB_update = store_thm
   ("SUB_update",
    “!d lb mth x L. ((update (OBJ d) lb mth) <[ [x,L]) =
                      update ((OBJ d) <[ [x,L]) lb (mth <[ [x,L])”,
    REWRITE_TAC[update,SUB_object,SUB_update_dict]
   );



(* --------------------------------------------------------------------- *)
(* Definition of the relation of primitive reduction.                    *)
(* This is simple, but we define it by rule induction.                   *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* (RED_one o1 o2) means that the object o1 reduces entirely to the      *)
(* object o2 in exactly one step, as defined in Abadi/Cardelli,          *)
(* Section 6.1.2, page 59.   Note that this is true ONLY on o1 of        *)
(* the forms                                                             *)
(*        INVOKE (OBJ d) l   or   UPDATE (OBJ d) l m                     *)
(* --------------------------------------------------------------------- *)


val SIGMA_R =
“SIGMA_R : obj -> obj -> bool”;

val SIGMA_R_patterns = [“^SIGMA_R o1 o2”];

val SIGMA_R_rules_tm =
“
       (* -------------------------------------------- *)
      (^SIGMA_R (INVOKE (OBJ d) l) (invoke (OBJ d) l))      /\


       (* -------------------------------------------- *)
    (^SIGMA_R (UPDATE (OBJ d) l m) (update (OBJ d) l m))
”;

val (SIGMA_R_rules_sat,SIGMA_R_ind_thm) =
    define_inductive_relations SIGMA_R_patterns SIGMA_R_rules_tm;

val SIGMA_R_inv_thms = prove_inversion_theorems
    SIGMA_R_rules_sat SIGMA_R_ind_thm;

val SIGMA_R_strong_ind = prove_strong_induction
    SIGMA_R_rules_sat SIGMA_R_ind_thm;

val _ = save_thm ("SIGMA_R_rules_sat", SIGMA_R_rules_sat);
val _ = save_thm ("SIGMA_R_ind_thm", SIGMA_R_ind_thm);
val _ = save_thm ("SIGMA_R_inv_thms", LIST_CONJ SIGMA_R_inv_thms);
val _ = save_thm ("SIGMA_R_strong_ind", SIGMA_R_strong_ind);




(* --------------------------------------------------------------------- *)
(* We claim that SIGMA_R is a binary relation on the object/method       *)
(* language which is                                                     *)
(*  1) a notion of reduction on the sigma calculus, in the sense of      *)
(*     Berendregt, Definition 3.1.2, pg 51 (trivial, since a relation)   *)
(*  2) deterministic                                                     *)
(* --------------------------------------------------------------------- *)


(* SIGMA_R is a deterministic relation. *)

val SIGMA_R_deterministic = store_thm
   ("SIGMA_R_deterministic",
    “!o1 o2. SIGMA_R o1 o2 ==>
                !o3. SIGMA_R o1 o3 ==>
                          (o2 = o3)”,
    rule_induct SIGMA_R_strong_ind
    THEN REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC SIGMA_R_inv_thms
    THEN REWRITE_TAC[object_distinct,object_one_one]
    THEN RW_TAC std_ss []
   );

(* Note that SIGMA_R is not reflexive, symmetric, or transitive. *)

val SIGMA_R_FV = store_thm
   ("SIGMA_R_FV",
    “!o1 o2. SIGMA_R o1 o2 ==>
                     (FV_obj o2 SUBSET FV_obj o1)”,
    rule_induct SIGMA_R_strong_ind
    THEN ONCE_REWRITE_TAC[FV_object]
    THEN REWRITE_TAC[FV_invoke,FV_update]
   );

val [obj_cases, dict_cases, entry_cases, method_cases]
    = CONJUNCTS object_cases;

val SIGMA_R_equals = store_thm
   ("SIGMA_R_equals",
    “(!o1 l o2. SIGMA_R (INVOKE o1 l) o2 =
                   (?d. (o1 = OBJ d) /\ (o2 = invoke o1 l))) /\
        (!o1 l o2. SIGMA_R (UPDATE o1 l m) o2 =
                   (?d. (o1 = OBJ d) /\ (o2 = update o1 l m))) /\
        (!x o2. SIGMA_R (OVAR x) o2 = F) /\
        (!d o2. SIGMA_R (OBJ d) o2 = F)”,
    REWRITE_TAC SIGMA_R_inv_thms
    THEN REWRITE_TAC[object_distinct,object_one_one]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC “d:^dict”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d:^dict”
        THEN EXISTS_TAC “l:string”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d:^dict”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d:^dict”
        THEN EXISTS_TAC “l:string”
        THEN EXISTS_TAC “m:method”
        THEN ASM_REWRITE_TAC[]
      ]
   );


(* --------------------------------------------------------------------- *)
(* Now we claim that using the results of theory "reduction", that       *)
(* 1) RED1 SIGMA_R, RED SIGMA_R, and REQ SIGMA_R are compatible,         *)
(* 2) RED SIGMA_R is a reduction relation,                               *)
(* 3) REQ SIGMA_R is an equality relation,                               *)
(* 4) various theorems and relations hold (see the theory "reduction")   *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Now we begin to prove the Church-Rosser theorem for SIGMA_R.          *)
(* --------------------------------------------------------------------- *)


(* Barendregt Proposition 3.1.16, SIGMA_R is substitutive. *)

val SIGMA_R_SUBSTITUTIVE = store_thm
   ("SIGMA_R_SUBSTITUTIVE",
    “SUBSTITUTIVE_obj SIGMA_R”,
    REWRITE_TAC[SUBSTITUTIVE]
    THEN MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[SIGMA_R_equals]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[SUB_object]
    THEN REWRITE_TAC[SIGMA_R_equals]
    THEN EXISTS_TAC “(d:^dict) <[ [x,L]”
    THEN REWRITE_TAC[SUB_invoke,SUB_update]
    THEN REWRITE_TAC[SUB_object]
   );



(* --------------------------------------------------------------------- *)
(* (REDL o1 o2) will now be defined on the sigma calculus such that      *)
(*   1) REDL satisfies the diamond property, and                         *)
(*   2) the transitive closure of REDL is RED SIGMA_R.                   *)
(* Then it follows by TC_DIAMOND that RED SIGMA_R satifies the diamond   *)
(* property, i.e., that SIGMA_R is Church-Rosser.                        *)
(* --------------------------------------------------------------------- *)


val REDL_obj =
“REDL_obj : obj -> obj -> bool”;
val REDL_dict =
“REDL_dict : ^dict -> ^dict -> bool”;
val REDL_entry =
“REDL_entry : ^entry -> ^entry -> bool”;
val REDL_method =
“REDL_method : method -> method -> bool”;

val REDL_patterns =     [“^REDL_obj o1 o2”,
                         “^REDL_dict d1 d2”,
                         “^REDL_entry e1 e2”,
                         “^REDL_method m1 m2”
                        ];

val REDL_rules_tm =
“

       (* -------------------------------------------- *)
                       (^REDL_obj o1 o1)                                  /\


                     ((^REDL_dict d1 d2)
       (* -------------------------------------------- *) ==>
                (^REDL_obj (OBJ d1) (OBJ d2)))                          /\


                      ((^REDL_obj o1 o2)
       (* -------------------------------------------- *) ==>
            (^REDL_obj (INVOKE o1 l) (INVOKE o2 l)))                    /\


           ((^REDL_obj o1 o2) /\ (^REDL_method m1 m2)
       (* -------------------------------------------- *) ==>
         (^REDL_obj (UPDATE o1 l m1) (UPDATE o2 l m2)))                 /\



       (* -------------------------------------------- *)
                       (^REDL_dict d d)                                   /\


           ((^REDL_entry e1 e2) /\ (^REDL_dict d1 d2)
       (* -------------------------------------------- *) ==>
             (^REDL_dict (CONS e1 d1) (CONS e2 d2)))                      /\



       (* -------------------------------------------- *)
                       (^REDL_entry e e)                                  /\


                    ((^REDL_method m1 m2)
       (* -------------------------------------------- *) ==>
                (^REDL_entry (l, m1) (l, m2)))                            /\



       (* -------------------------------------------- *)
                      (^REDL_method m m)                                  /\


                      ((^REDL_obj o1 o2)
       (* -------------------------------------------- *) ==>
           (^REDL_method (SIGMA x o1) (SIGMA x o2)))                    /\


                      ((^REDL_dict d1 d2)
       (* -------------------------------------------- *) ==>
     (^REDL_obj (INVOKE (OBJ d1) l) (invoke (OBJ d2) l)))             /\


           ((^REDL_dict d1 d2) /\ (^REDL_method m1 m2)
       (* -------------------------------------------- *) ==>
   (^REDL_obj (UPDATE (OBJ d1) l m1) (update (OBJ d2) l m2)))
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


val [REDL_obj_REFL, REDL_OBJ, REDL_INVOKE, REDL_UPDATE,
     REDL_invoke, REDL_update, REDL_dict_REFL, REDL_CONS,
     REDL_entry_REFL, REDL_PAIR, REDL_method_REFL, REDL_SIGMA]
   = CONJUNCTS REDL_rules_sat;



val REDL_height_ind_thm_LEMMA = store_thm
   ("REDL_height_ind_thm_LEMMA",
    “!n P_0 P_1 P_2 P_3.
         (!o1. P_0 o1 o1) /\
         (!d1 d2. P_1 d1 d2 ==> P_0 (OBJ d1) (OBJ d2)) /\
         (!o1 l o2. P_0 o1 o2 ==> P_0 (INVOKE o1 l) (INVOKE o2 l)) /\
         (!o1 l m1 o2 m2.
           P_0 o1 o2 /\ P_3 m1 m2 ==>
           P_0 (UPDATE o1 l m1) (UPDATE o2 l m2)) /\
         (!d1 l d2.
           P_1 d1 d2 ==> P_0 (INVOKE (OBJ d1) l) (invoke (OBJ d2) l)) /\
         (!d1 l m1 d2 m2.
           P_1 d1 d2 /\ P_3 m1 m2 ==>
           P_0 (UPDATE (OBJ d1) l m1) (update (OBJ d2) l m2)) /\
         (!d. P_1 d d) /\
         (!e1 d1 e2 d2.
           P_2 e1 e2 /\ P_1 d1 d2 ==> P_1 (CONS e1 d1) (CONS e2 d2)) /\
         (!e. P_2 e e) /\
         (!l m1 m2. P_3 m1 m2 ==> P_2 (l,m1) (l,m2)) /\
         (!m. P_3 m m) /\
         (!x o1 o2.
           (!o1' o2'. REDL_obj o1' o2' /\
                      (HEIGHT_obj o1 = HEIGHT_obj o1') ==> P_0 o1' o2')
            ==> P_3 (SIGMA x o1) (SIGMA x o2)) ==>
         (!o1 o2. REDL_obj o1 o2 ==>
                    ((HEIGHT_obj o1 <= n) ==>
                     P_0 o1 o2)) /\
         (!d1 d2. REDL_dict d1 d2 ==>
                    ((HEIGHT_dict d1 <= n) ==>
                     P_1 d1 d2)) /\
         (!e1 e2. REDL_entry e1 e2 ==>
                    ((HEIGHT_entry e1 <= n) ==>
                     P_2 e1 e2)) /\
         (!m1 m2. REDL_method m1 m2 ==>
                    ((HEIGHT_method m1 <= n) ==>
                     P_3 m1 m2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL
          [ UNDISCH_TAC “REDL_obj o1 o2”
            THEN ONCE_REWRITE_TAC REDL_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS,object_one_one]
            THEN DISCH_TAC
            THEN ASM_REWRITE_TAC[],

            UNDISCH_TAC “REDL_dict d1 d2”
            THEN ONCE_REWRITE_TAC REDL_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS,object_one_one]
            THEN DISCH_TAC
            THEN ASM_REWRITE_TAC[]
          ],

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
        THENL (* 8 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_MONO_EQ
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_MONO_EQ
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );


val REDL_height_ind_thm = store_thm
   ("REDL_height_ind_thm",
    “!P_0 P_1 P_2 P_3.
         (!o1. P_0 o1 o1) /\
         (!d1 d2. P_1 d1 d2 ==> P_0 (OBJ d1) (OBJ d2)) /\
         (!o1 l o2. P_0 o1 o2 ==> P_0 (INVOKE o1 l) (INVOKE o2 l)) /\
         (!o1 l m1 o2 m2.
           P_0 o1 o2 /\ P_3 m1 m2 ==>
           P_0 (UPDATE o1 l m1) (UPDATE o2 l m2)) /\
         (!d1 l d2.
           P_1 d1 d2 ==> P_0 (INVOKE (OBJ d1) l) (invoke (OBJ d2) l)) /\
         (!d1 l m1 d2 m2.
           P_1 d1 d2 /\ P_3 m1 m2 ==>
           P_0 (UPDATE (OBJ d1) l m1) (update (OBJ d2) l m2)) /\
         (!d. P_1 d d) /\
         (!e1 d1 e2 d2.
           P_2 e1 e2 /\ P_1 d1 d2 ==> P_1 (CONS e1 d1) (CONS e2 d2)) /\
         (!e. P_2 e e) /\
         (!l m1 m2. P_3 m1 m2 ==> P_2 (l,m1) (l,m2)) /\
         (!m. P_3 m m) /\
         (!x o1 o2.
           (!o1' o2'.
             REDL_obj o1' o2' /\ (HEIGHT_obj o1 = HEIGHT_obj o1') ==>
             P_0 o1' o2') ==>
           P_3 (SIGMA x o1) (SIGMA x o2)) ==>
         (!o1 o2. REDL_obj o1 o2 ==> P_0 o1 o2) /\
         (!d1 d2. REDL_dict d1 d2 ==> P_1 d1 d2) /\
         (!e1 e2. REDL_entry e1 e2 ==> P_2 e1 e2) /\
         (!m1 m2. REDL_method m1 m2 ==> P_3 m1 m2)”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL (SPEC tm REDL_height_ind_thm_LEMMA)))
           [“HEIGHT_obj o1”,
            “HEIGHT_dict d1”,
            “HEIGHT_entry e1”,
            “HEIGHT_method m1”])
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
   );


val REDL_height_strong_ind_LEMMA = store_thm
   ("REDL_height_strong_ind_LEMMA",
    “!n P_0 P_1 P_2 P_3.
         (!o1. P_0 o1 o1) /\
         (!d1 d2. P_1 d1 d2 /\ REDL_dict d1 d2 ==> P_0 (OBJ d1) (OBJ d2)) /\
         (!o1 l o2.
           P_0 o1 o2 /\ REDL_obj o1 o2 ==>
           P_0 (INVOKE o1 l) (INVOKE o2 l)) /\
         (!o1 l m1 o2 m2.
           P_0 o1 o2 /\ REDL_obj o1 o2 /\ P_3 m1 m2 /\ REDL_method m1 m2 ==>
           P_0 (UPDATE o1 l m1) (UPDATE o2 l m2)) /\
         (!d1 l d2.
           P_1 d1 d2 /\ REDL_dict d1 d2 ==>
           P_0 (INVOKE (OBJ d1) l) (invoke (OBJ d2) l)) /\
         (!d1 l m1 d2 m2.
           P_1 d1 d2 /\ REDL_dict d1 d2 /\ P_3 m1 m2 /\ REDL_method m1 m2 ==>
           P_0 (UPDATE (OBJ d1) l m1) (update (OBJ d2) l m2)) /\
         (!d. P_1 d d) /\
         (!e1 d1 e2 d2.
           P_2 e1 e2 /\ REDL_entry e1 e2 /\ P_1 d1 d2 /\ REDL_dict d1 d2 ==>
           P_1 (CONS e1 d1) (CONS e2 d2)) /\
         (!e. P_2 e e) /\
         (!l m1 m2. P_3 m1 m2 /\ REDL_method m1 m2 ==> P_2 (l,m1) (l,m2)) /\
         (!m. P_3 m m) /\
         (!x o1 o2.
           (!o1' o2'.
             REDL_obj o1' o2' /\ (HEIGHT_obj o1 = HEIGHT_obj o1') ==>
             P_0 o1' o2') /\ REDL_obj o1 o2 ==>
           P_3 (SIGMA x o1) (SIGMA x o2)) ==>
         (!o1 o2. REDL_obj o1 o2 ==> HEIGHT_obj o1 <= n ==> P_0 o1 o2) /\
         (!d1 d2. REDL_dict d1 d2 ==> HEIGHT_dict d1 <= n ==> P_1 d1 d2) /\
         (!e1 e2. REDL_entry e1 e2 ==> HEIGHT_entry e1 <= n ==> P_2 e1 e2) /\
         (!m1 m2. REDL_method m1 m2 ==> HEIGHT_method m1 <= n ==> P_3 m1 m2)
    ”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL
          [ UNDISCH_TAC “REDL_obj o1 o2”
            THEN ONCE_REWRITE_TAC REDL_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS]
            THEN DISCH_TAC
            THEN ASM_REWRITE_TAC[],

            UNDISCH_TAC “REDL_dict d1 d2”
            THEN ONCE_REWRITE_TAC REDL_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS]
            THEN DISCH_TAC
            THEN ASM_REWRITE_TAC[]
          ],

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
        THENL (* 8 subgoals *)
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_MONO_EQ
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_MONO_EQ
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THEN ASSUM_LIST
                    (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o hd o rev)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );


val REDL_height_strong_ind = store_thm
   ("REDL_height_strong_ind",
    “!P_0 P_1 P_2 P_3.
         (!o1. P_0 o1 o1) /\
         (!d1 d2. P_1 d1 d2 /\ REDL_dict d1 d2 ==> P_0 (OBJ d1) (OBJ d2)) /\
         (!o1 l o2.
           P_0 o1 o2 /\ REDL_obj o1 o2 ==>
           P_0 (INVOKE o1 l) (INVOKE o2 l)) /\
         (!o1 l m1 o2 m2.
           P_0 o1 o2 /\ REDL_obj o1 o2 /\ P_3 m1 m2 /\ REDL_method m1 m2 ==>
           P_0 (UPDATE o1 l m1) (UPDATE o2 l m2)) /\
         (!d1 l d2.
           P_1 d1 d2 /\ REDL_dict d1 d2 ==>
           P_0 (INVOKE (OBJ d1) l) (invoke (OBJ d2) l)) /\
         (!d1 l m1 d2 m2.
           P_1 d1 d2 /\ REDL_dict d1 d2 /\ P_3 m1 m2 /\ REDL_method m1 m2 ==>
           P_0 (UPDATE (OBJ d1) l m1) (update (OBJ d2) l m2)) /\
         (!d. P_1 d d) /\
         (!e1 d1 e2 d2.
           P_2 e1 e2 /\ REDL_entry e1 e2 /\ P_1 d1 d2 /\ REDL_dict d1 d2 ==>
           P_1 (CONS e1 d1) (CONS e2 d2)) /\
         (!e. P_2 e e) /\
         (!l m1 m2. P_3 m1 m2 /\ REDL_method m1 m2 ==> P_2 (l,m1) (l,m2)) /\
         (!m. P_3 m m) /\
         (!x o1 o2.
           (!o1' o2'.
             REDL_obj o1' o2' /\ (HEIGHT_obj o1 = HEIGHT_obj o1') ==>
             P_0 o1' o2') /\
           REDL_obj o1 o2 ==>
           P_3 (SIGMA x o1) (SIGMA x o2)) ==>
         (!o1 o2. REDL_obj o1 o2 ==> P_0 o1 o2) /\
         (!d1 d2. REDL_dict d1 d2 ==> P_1 d1 d2) /\
         (!e1 e2. REDL_entry e1 e2 ==> P_2 e1 e2) /\
         (!m1 m2. REDL_method m1 m2 ==> P_3 m1 m2)”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL (SPEC tm REDL_height_strong_ind_LEMMA)))
           [“HEIGHT_obj o1”,
            “HEIGHT_dict d1”,
            “HEIGHT_entry e1”,
            “HEIGHT_method m1”])
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
   );



val SUBSETS_UNION = TAC_PROOF(([],
    “!(s1:'a set) s2 t1 t2.
         s1 SUBSET t1 /\ s2 SUBSET t2 ==>
         (s1 UNION s2) SUBSET (t1 UNION t2)”),
    REWRITE_TAC[SUBSET_DEF]
    THEN REWRITE_TAC[IN_UNION]
    THEN REPEAT STRIP_TAC (* 2 subgoals *)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val REDL_FV = TAC_PROOF(([],
    “(!M M'.
          REDL_obj M M' ==> (FV_obj M' SUBSET FV_obj M)) /\
        (!M M'.
          REDL_dict M M' ==> (FV_dict M' SUBSET FV_dict M)) /\
         (!M M'.
          REDL_entry M M' ==> (FV_entry M' SUBSET FV_entry M)) /\
        (!M M'.
          REDL_method M M' ==> (FV_method M' SUBSET FV_method M))”),
    rule_induct REDL_strong_ind (* strong, not weak induction *)
    THEN REWRITE_TAC[FV_object,SUBSET_REFL]
    THEN REPEAT STRIP_TAC (* 5 subgoals *)
    THENL
      [ IMP_RES_TAC SUBSETS_UNION,

        MATCH_MP_TAC SUBSET_TRANS
        THEN EXISTS_TAC “FV_obj (OBJ d2)”
        THEN ASM_REWRITE_TAC[FV_invoke,FV_object],

        MATCH_MP_TAC SUBSET_TRANS
        THEN EXISTS_TAC “FV_obj (OBJ d2) UNION FV_method m2”
        THEN REWRITE_TAC[FV_update,FV_object]
        THEN IMP_RES_TAC SUBSETS_UNION,

        IMP_RES_TAC SUBSETS_UNION,

        MATCH_MP_TAC SUBSET_DIFF
        THEN ASM_REWRITE_TAC[]
      ]
   );


val SHIFT_IN_DIFF = TAC_PROOF(([],
    “!x y z w M M'.
        ~(y IN FV_obj M) /\ ~(z = y) /\
        (SIGMA x M = SIGMA z M') ==>
        ~(y IN FV_obj M' DIFF {w})”),
    REWRITE_TAC[IN_DIFF,IN]
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN FIRST_ASSUM (MP_TAC o
               REWRITE_RULE[FV_object] o
               AP_TERM “FV_method”)
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_DIFF,IN]
    THEN DISCH_THEN (MP_TAC o SPEC “y:var”)
    THEN ASM_REWRITE_TAC[]
    THEN EVERY_ASSUM (REWRITE_THM o GSYM)
    THEN DISCH_THEN REWRITE_THM
   );


val SHIFT_IN_DIFF2 = TAC_PROOF(([],
    “!x y z w M M'.
        (y = x) /\ ~(z = y) /\
        (SIGMA x M = SIGMA z M') ==>
        ~(x IN FV_obj M' DIFF {w})”),
    REWRITE_TAC[IN_DIFF,IN]
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN FIRST_ASSUM (MP_TAC o
               REWRITE_RULE[FV_object] o
               AP_TERM “FV_method”)
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_DIFF,IN]
    THEN DISCH_THEN (MP_TAC o SPEC “y:var”)
    THEN UNDISCH_THEN “(y:var) = x” REWRITE_ALL_THM
    THEN EVERY_ASSUM (REWRITE_THM o GSYM)
    THEN DISCH_THEN REWRITE_THM
   );


val SUBST_REVERSE = store_thm
   ("SUBST_REVERSE",
    “(!M x y. ~(y IN FV_obj M DIFF {x})    ==>
                (((M <[ [x,OVAR y]) <[ [y,OVAR x]) = M)) /\
        (!M x y. ~(y IN FV_dict M DIFF {x})    ==>
                (((M <[ [x,OVAR y]) <[ [y,OVAR x]) = M)) /\
        (!M x y. ~(y IN FV_entry M DIFF {x})    ==>
                (((M <[ [x,OVAR y]) <[ [y,OVAR x]) = M)) /\
        (!M x y. ~(y IN FV_method M DIFF {x})    ==>
                (((M <[ [x,OVAR y]) <[ [y,OVAR x]) = M))”,
    MUTUAL_INDUCT_THEN object_height_induct ASSUME_TAC
    THEN REWRITE_TAC[FV_object,IN_UNION,IN_DIFF,IN,DE_MORGAN_THM]
    THEN REPEAT STRIP_TAC
    THENL (* 16 subgoals *)
      [ REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[SUB_object,SUB]
        THEN EVERY_ASSUM (REWRITE_THM o GSYM),

        POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[SUB_object,SUB]
        THEN ASM_REWRITE_TAC[],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[SUB_object,object_one_one]
        THEN DEP_ASM_REWRITE_TAC[IN_DIFF,IN],

        SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[object_one_one]
        THEN DEP_ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC SHIFT_IN_DIFF
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[object_one_one]
        THEN DEP_ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC SHIFT_IN_DIFF2
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN REWRITE_TAC[object_one_one]
        THEN DEP_ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[IN_DIFF,IN]
      ]
   );


val REDL_SUBSTITUTIVE_SAME = TAC_PROOF(([],
    “(!M.
          (!N N' x. REDL_obj N N' ==>
                REDL_obj (M <[ [x,N]) (M <[ [x,N']))) /\
        (!M.
          (!N N' x. REDL_obj N N' ==>
                REDL_dict (M <[ [x,N]) (M <[ [x,N']))) /\
        (!M.
          (!N N' x. REDL_obj N N' ==>
                REDL_entry (M <[ [x,N]) (M <[ [x,N']))) /\
        (!M.
          (!N N' x. REDL_obj N N' ==>
                REDL_method (M <[ [x,N]) (M <[ [x,N'])))”),
    MUTUAL_INDUCT_THEN object_height_induct ASSUME_TAC
    THEN REPEAT STRIP_TAC
    THENL (* 8 subgoals *)
      [ REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[REDL_obj_REFL],

        REWRITE_TAC[SUB_object]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        REWRITE_TAC[SUB_object]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        REWRITE_TAC[SUB_object]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        REWRITE_TAC[SUB_object]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        REWRITE_TAC[SUB_object]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        REWRITE_TAC[SUB_object]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        SIMPLE_SUBST_TAC
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat]
      ]
   );


val REDL_SUBSTITUTIVE_LEMMA = store_thm
   ("REDL_SUBSTITUTIVE_LEMMA",
    “(!M M'.
          REDL_obj M M' ==>
            (!N N' x. REDL_obj N N' ==>
                REDL_obj (M <[ [x,N]) (M' <[ [x,N']))) /\
        (!M M'.
          REDL_dict M M' ==>
            (!N N' x. REDL_obj N N' ==>
                REDL_dict (M <[ [x,N]) (M' <[ [x,N']))) /\
        (!M M'.
          REDL_entry M M' ==>
            (!N N' x. REDL_obj N N' ==>
                REDL_entry (M <[ [x,N]) (M' <[ [x,N']))) /\
        (!M M'.
          REDL_method M M' ==>
            (!N N' x. REDL_obj N N' ==>
                REDL_method (M <[ [x,N]) (M' <[ [x,N'])))”,
    rule_induct REDL_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THEN SIMPLE_SUBST_TAC
    THEN REWRITE_TAC[SUB_object,SUB_invoke,SUB_update]
    THEN DEP_ASM_REWRITE_TAC[REDL_SUBSTITUTIVE_SAME,REDL_rules_sat]
    THEN POP_ASSUM (REWRITE_THM o SYM o CONJUNCT1 o
                        REWRITE_RULE[SIGMA_one_one])
    THEN POP_ASSUM (REWRITE_THM o SYM o CONJUNCT1 o
                        REWRITE_RULE[SIGMA_one_one])
    THEN DEP_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[REDL_rules_sat]
   );


val REDL_invoke_SAME = store_thm
   ("REDL_invoke_SAME",
    “(!M.
          (!N N' l. REDL_obj N N' ==>
                REDL_obj (invoke_dict M N l) (invoke_dict M N' l))) /\
        (!(M:^entry).
          (!N N'. REDL_obj N N' ==>
                REDL_obj (invoke_method (SND M) N)
                         (invoke_method (SND M) N'))) /\
        (!M.
          (!N N'. REDL_obj N N' ==>
                REDL_obj (invoke_method M N) (invoke_method M N')))”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REPEAT STRIP_TAC
    THENL (* 4 subgoals *)
      [ REWRITE_TAC[invoke_method]
        THEN DEP_ASM_REWRITE_TAC[REDL_SUBSTITUTIVE_SAME],

        REWRITE_TAC[invoke_dict]
        THEN REWRITE_TAC[REDL_obj_REFL],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN REWRITE_TAC[invoke_dict]
        THEN COND_CASES_TAC
        THEN DEP_ASM_REWRITE_TAC[],

        FIRST_ASSUM MATCH_MP_TAC
        THEN FIRST_ASSUM ACCEPT_TAC
      ]
   );


val REDL_invoke_LEMMA1 = TAC_PROOF(([],
    “(!M M'.
          REDL_obj M M' ==>
            (!d l. (OBJ d = M) ==>
                REDL_obj (invoke M l) (invoke M' l))) /\
        (!M M'.
          REDL_dict M M' ==>
            (!N N' l. REDL_obj N N' ==>
                REDL_obj (invoke_dict M N l) (invoke_dict M' N' l))) /\
        (!M M'.
          REDL_entry M M' ==>
            (!N N'. REDL_obj N N' ==>
                (FST M = FST M') /\
                REDL_obj (invoke_method (SND M) N)
                         (invoke_method (SND M') N'))) /\
        (!M M'.
          REDL_method M M' ==>
            (!N N'. REDL_obj N N' ==>
                REDL_obj (invoke_method M N) (invoke_method M' N')))”),
    rule_induct REDL_strong_ind (* strong, not weak induction *)
    THEN REWRITE_TAC[object_distinct,NOT_NIL_CONS,NOT_CONS_NIL,object_one_one]
    THEN REPEAT STRIP_TAC (* 7 subgoals *)
    THENL
      [ REWRITE_TAC[REDL_obj_REFL],

        REWRITE_TAC[invoke]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_invoke_SAME],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN REWRITE_TAC[invoke_dict]
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[],

        DEP_ASM_REWRITE_TAC[REDL_invoke_SAME],

        DEP_ASM_REWRITE_TAC[REDL_invoke_SAME],

        REWRITE_TAC[invoke_method]
        THEN DEP_ASM_REWRITE_TAC[REDL_SUBSTITUTIVE_LEMMA]
      ]
   );


val REDL_invoke_LEMMA = store_thm
   ("REDL_invoke_LEMMA",
    “(!D M'.
          REDL_obj (OBJ D) M' ==>
            (!l.
                REDL_obj (invoke (OBJ D) l) (invoke M' l))) /\
        (!M M'.
          REDL_dict M M' ==>
            (!N N' l. REDL_obj N N' ==>
                REDL_obj (invoke_dict M N l) (invoke_dict M' N' l))) /\
        (!M M'.
          REDL_entry M M' ==>
            (!N N'. REDL_obj N N' ==>
                (FST M = FST M') /\
                REDL_obj (invoke_method (SND M) N)
                         (invoke_method (SND M') N'))) /\
        (!M M'.
          REDL_method M M' ==>
            (!N N'. REDL_obj N N' ==>
                REDL_obj (invoke_method M N) (invoke_method M' N')))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_invoke_LEMMA1
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[] o SPEC “D:^dict”)
    THEN ASM_REWRITE_TAC[]
   );


val REDL_update_SAME1 = TAC_PROOF(([],
    “(!M.
          (!d N N' l. (OBJ d = M) /\ REDL_method N N' ==>
                REDL_obj (update M l N) (update M l N'))) /\
        (!M.
          (!N N' l. REDL_method N N' ==>
                REDL_dict (update_dict M l N) (update_dict M l N')))”),
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[object_distinct,NOT_NIL_CONS]
    THEN REPEAT STRIP_TAC
    THENL (* 3 subgoals *)
      [ REWRITE_TAC[update]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        REWRITE_TAC[update_dict,REDL_dict_REFL],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN REWRITE_TAC[update_dict]
        THEN COND_CASES_TAC
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat]
      ]
   );

val REDL_update_SAME = store_thm
   ("REDL_update_SAME",
    “(!D N N' l. REDL_method N N' ==>
                REDL_obj (update (OBJ D) l N) (update (OBJ D) l N')) /\
        (!M N N' l. REDL_method N N' ==>
                REDL_dict (update_dict M l N) (update_dict M l N'))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_update_SAME1
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN EXISTS_TAC “D:^dict”
    THEN REFL_TAC
   );


val REDL_update_LEMMA1 = TAC_PROOF(([],
    “(!M M'.
          REDL_obj M M' ==>
            (!d N N' l. (OBJ d = M) /\ REDL_method N N' ==>
                REDL_obj (update M l N) (update M' l N'))) /\
        (!M M'.
          REDL_dict M M' ==>
            (!N N' l. REDL_method N N' ==>
                REDL_dict (update_dict M l N) (update_dict M' l N'))) /\
        (!M M'.
          REDL_entry M M' ==>
                (FST M = FST M')) /\
        (!M M'.
          REDL_method M M' ==> T)”),
    rule_induct REDL_strong_ind (* strong, not weak induction *)
    THEN REWRITE_TAC[object_distinct,NOT_NIL_CONS,NOT_CONS_NIL,object_one_one]
    THEN REPEAT STRIP_TAC (* 4 subgoals *)
    THENL
      [ FIRST_ASSUM (REWRITE_THM o SYM)
        THEN DEP_REWRITE_TAC[REDL_update_SAME]
        THEN ASM_REWRITE_TAC[],

        REWRITE_TAC[update]
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_update_SAME],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN REWRITE_TAC[update_dict]
        THEN ASM_REWRITE_TAC[]
        THEN COND_CASES_TAC
        THENL
          [ DEP_ASM_REWRITE_TAC[],

            REWRITE_TAC[PAIR]
            THEN FIRST_ASSUM (REWRITE_THM o SYM)
            THEN REWRITE_TAC[PAIR]
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat]
          ]
      ]
   );


val REDL_update_LEMMA = store_thm
   ("REDL_update_LEMMA",
    “(!D M'.
          REDL_obj (OBJ D) M' ==>
            (!N N' l. REDL_method N N' ==>
                REDL_obj (update (OBJ D) l N) (update M' l N'))) /\
        (!M M'.
          REDL_dict M M' ==>
            (!N N' l. REDL_method N N' ==>
                REDL_dict (update_dict M l N) (update_dict M' l N')))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_update_LEMMA1
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN EXISTS_TAC “D:^dict”
    THEN REFL_TAC
   );


val REDL_OBJ_IMP = store_thm
   ("REDL_OBJ_IMP",
    “!o1 d.
          REDL_obj (OBJ d) o1 ==> (?d2. o1 = OBJ d2)”,
    ONCE_REWRITE_TAC REDL_inv_thms
    THEN REWRITE_TAC[object_distinct,NOT_NIL_CONS, object_one_one]
    THEN REPEAT STRIP_TAC
    THENL (* 2 subgoals *)
      [ EXISTS_TAC “d:^dict”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d2:^dict”
        THEN ASM_REWRITE_TAC[]
      ]
   );


val REDL_OBJ_IMP_dict = store_thm
   ("REDL_OBJ_IMP_dict",
    “!d1 d2.
          REDL_obj (OBJ d1) (OBJ d2) ==> REDL_dict d1 d2”,
    REPEAT GEN_TAC
    THEN DISCH_THEN (STRIP_ASSUME_TAC o
                REWRITE_RULE[object_distinct,NOT_NIL_CONS, object_one_one] o
                ONCE_REWRITE_RULE REDL_inv_thms)
    THENL (* 2 subgoals *)
      [ ASM_REWRITE_TAC[REDL_dict_REFL],

        ASM_REWRITE_TAC[]
      ]
   );


val NOT_IN_SUBSET_DIFF = store_thm
   ("NOT_IN_SUBSET_DIFF",
    “!s1 s2 t (x:'a).
          s2 SUBSET s1 /\ ~(x IN s1 DIFF t) ==> ~(x IN s2 DIFF t)”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[IN_DIFF,IN,DE_MORGAN_THM]
    THEN STRIP_TAC
    THENL (* 2 subgoals *)
      [ IMP_RES_TAC NOT_IN_SUBSET
        THEN ASM_REWRITE_TAC[],

        ASM_REWRITE_TAC[]
      ]
   );



val REDL_obj_cases = store_thm
   ("REDL_obj_cases",
    “(!d1 o2.
          REDL_obj (OBJ d1) o2 ==>
          (?d2. (o2 = (OBJ d2)) /\ REDL_dict d1 d2)) /\
        (!o1 l o2.
          REDL_obj (INVOKE o1 l) o2 ==>
          ((?o3. (o2 = (INVOKE o3 l)) /\ REDL_obj o1 o3) \/
           (?d1 d2. (o1 = OBJ d1) /\
                    (o2 = (invoke (OBJ d2) l)) /\
                    REDL_dict d1 d2))) /\
        (!o1 l m1 o2.
          REDL_obj (UPDATE o1 l m1) o2 ==>
          ((?o3 m2. (o2 = (UPDATE o3 l m2)) /\
                    REDL_obj o1 o3 /\
                    REDL_method m1 m2) \/
           (?d1 d2 m2. (o1 = OBJ d1) /\
                    (o2 = (update (OBJ d2) l m2)) /\
                    REDL_dict d1 d2 /\
                    REDL_method m1 m2)))”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[object_distinct,NOT_NIL_CONS,object_one_one] o
            ONCE_REWRITE_RULE REDL_inv_thms)
    THENL (* 8 subgoals *)
      [ POP_ASSUM REWRITE_THM
        THEN EXISTS_TAC “d1:^dict”
        THEN ASM_REWRITE_TAC[REDL_dict_REFL],

        EXISTS_TAC “d2:^dict”
        THEN ASM_REWRITE_TAC[],

        POP_ASSUM REWRITE_THM
        THEN DISJ1_TAC
        THEN EXISTS_TAC “o1:obj”
        THEN ASM_REWRITE_TAC[REDL_obj_REFL],

        DISJ1_TAC
        THEN EXISTS_TAC “o2':obj”
        THEN ASM_REWRITE_TAC[],

        DISJ2_TAC
        THEN EXISTS_TAC “d1:^dict”
        THEN EXISTS_TAC “d2:^dict”
        THEN ASM_REWRITE_TAC[],

        POP_ASSUM REWRITE_THM
        THEN DISJ1_TAC
        THEN EXISTS_TAC “o1:obj”
        THEN EXISTS_TAC “m1:method”
        THEN ASM_REWRITE_TAC[REDL_obj_REFL,REDL_method_REFL],

        DISJ1_TAC
        THEN EXISTS_TAC “o2':obj”
        THEN EXISTS_TAC “m2:method”
        THEN ASM_REWRITE_TAC[],

        DISJ2_TAC
        THEN EXISTS_TAC “d1:^dict”
        THEN EXISTS_TAC “d2:^dict”
        THEN EXISTS_TAC “m2:method”
        THEN ASM_REWRITE_TAC[]
      ]
   );


val REDL_dict_cases = store_thm
   ("REDL_dict_cases",
    “(!e1 d1 d2.
          REDL_dict (CONS e1 d1) d2 ==>
          (?e2 d3. (d2 = (CONS e2 d3)) /\
                   REDL_entry e1 e2 /\ REDL_dict d1 d3)) /\
        (!d2.
          REDL_dict [] d2 ==> (d2 = []))”,
    CONJ_TAC
    THEN REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[object_distinct,NOT_NIL_CONS,object_one_one] o
            ONCE_REWRITE_RULE REDL_inv_thms)
    THENL
      [ POP_ASSUM REWRITE_THM
        THEN EXISTS_TAC “e1:^entry”
        THEN EXISTS_TAC “d1:^dict”
        THEN ASM_REWRITE_TAC[REDL_entry_REFL,REDL_dict_REFL],

        EXISTS_TAC “e2:^entry”
        THEN EXISTS_TAC “d2':^dict”
        THEN ASM_REWRITE_TAC[]
      ]
   );


val REDL_entry_cases = store_thm
   ("REDL_entry_cases",
    “!l m1 e2.
          REDL_entry (l,m1) e2 ==>
          (?m2. (e2 = (l,m2)) /\ REDL_method m1 m2)”,
    REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            REWRITE_RULE[object_distinct,NOT_NIL_CONS,object_one_one] o
            ONCE_REWRITE_RULE REDL_inv_thms)
    THENL
      [ POP_ASSUM REWRITE_THM
        THEN EXISTS_TAC “m1:method”
        THEN ASM_REWRITE_TAC[REDL_method_REFL],

        EXISTS_TAC “m2:method”
        THEN ASM_REWRITE_TAC[]
      ]
   );


val REDL_method_cases = store_thm
   ("REDL_method_cases",
    “!x o1 m2.
          REDL_method (SIGMA x o1) m2 ==>
          (?o2. (m2 = SIGMA x o2) /\ REDL_obj o1 o2)”,
    REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o
            ONCE_REWRITE_RULE REDL_inv_thms)
    THENL
      [ POP_ASSUM REWRITE_THM
        THEN EXISTS_TAC “o1:obj”
        THEN ASM_REWRITE_TAC[REDL_obj_REFL],

        ASM_REWRITE_TAC[]
        THEN EXISTS_TAC “(o2:obj) <[ [x',OVAR x]”
        THEN IMP_RES_TAC SIGMA_one_one
        THEN POP_ASSUM (REWRITE_THM)
        THEN POP_TAC
        THEN DEP_REWRITE_TAC[REDL_SUBSTITUTIVE_LEMMA]
        THEN ASM_REWRITE_TAC[REDL_obj_REFL]
        THEN REWRITE_TAC[SIGMA_one_one]
        THEN DEP_REWRITE_TAC[SUBST_REVERSE]
        THEN (ASSUME_TAC o
                 REWRITE_RULE[IN_DIFF,IN] o
                 AP_TERM “$IN (x:var)” o
                 REWRITE_RULE[FV_object] o
                 AP_TERM “FV_method” o
                 ASSUME) “SIGMA x o1 = SIGMA x' o1'”
        THEN IMP_RES_TAC REDL_FV
        THEN IMP_RES_TAC NOT_IN_SUBSET_DIFF
        THEN DEP_ASM_REWRITE_TAC[]
        THEN ASM_REWRITE_TAC[IN_DIFF,IN]
      ]
   );



val REDL_DIAMOND_LEMMA = store_thm
   ("REDL_DIAMOND_LEMMA",
    “(!o1 o2.
          REDL_obj o1 o2 ==>
          (!o3. REDL_obj o1 o3 ==>
                (?o4. REDL_obj o2 o4 /\ REDL_obj o3 o4))) /\
        (!d1 d2.
          REDL_dict d1 d2 ==>
          (!d3. REDL_dict d1 d3 ==>
                (?d4. REDL_dict d2 d4 /\ REDL_dict d3 d4))) /\
        (!e1 e2.
          REDL_entry e1 e2 ==>
          (!e3. REDL_entry e1 e3 ==>
                (?e4. REDL_entry e2 e4 /\ REDL_entry e3 e4))) /\
        (!m1 m2.
          REDL_method m1 m2 ==>
          (!m3. REDL_method m1 m3 ==>
                (?m4. REDL_method m2 m4 /\ REDL_method m3 m4)))”,
    rule_induct REDL_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC
    THENL (* 12 subgoals *)
      [ EXISTS_TAC “o3:obj”
        THEN ASM_REWRITE_TAC[REDL_rules_sat],

        IMP_RES_TAC REDL_obj_cases
        THEN RES_TAC
        THEN EXISTS_TAC “OBJ d4”
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        IMP_RES_TAC REDL_obj_cases
        THENL
          [ RES_TAC
            THEN EXISTS_TAC “INVOKE o4 l”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

            UNDISCH_THEN “o1 = OBJ d1” REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_OBJ
            THEN RES_TAC
            THEN POP_TAC
            THEN IMP_RES_TAC REDL_OBJ_IMP
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN POP_TAC
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_OBJ_IMP_dict
            THEN EXISTS_TAC “invoke (OBJ d2') l”
            THEN DEP_ASM_REWRITE_TAC[REDL_invoke,REDL_invoke_LEMMA]
          ],

        IMP_RES_TAC REDL_obj_cases
        THENL
          [ RES_TAC
            THEN EXISTS_TAC “UPDATE o4 l m4”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

            UNDISCH_THEN “o1 = OBJ d1” REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_OBJ
            THEN RES_TAC
            THEN POP_TAC
            THEN IMP_RES_TAC REDL_OBJ_IMP
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN POP_TAC
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_OBJ_IMP_dict
            THEN EXISTS_TAC “update (OBJ d2') l m4”
            THEN DEP_ASM_REWRITE_TAC[REDL_update,REDL_update_LEMMA]
          ],

        IMP_RES_TAC REDL_obj_cases
        THENL
          [ IMP_RES_TAC REDL_OBJ_IMP
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_OBJ_IMP_dict
            THEN RES_TAC
            THEN EXISTS_TAC “invoke (OBJ d4) l”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat,REDL_invoke_LEMMA],

            UNDISCH_THEN “OBJ d1 = OBJ d1'”
                  (REWRITE_ALL_THM o SYM o REWRITE_RULE[object_one_one])
            THEN RES_TAC
            THEN POP_TAC
            THEN EXISTS_TAC “invoke (OBJ d4) l”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat,REDL_invoke_LEMMA]
          ],

        IMP_RES_TAC REDL_obj_cases
        THENL
          [ IMP_RES_TAC REDL_OBJ_IMP
            THEN POP_ASSUM REWRITE_ALL_THM
            THEN IMP_RES_TAC REDL_OBJ_IMP_dict
            THEN RES_TAC
            THEN EXISTS_TAC “update (OBJ d4) l m4”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat,REDL_update_LEMMA],

            UNDISCH_THEN “OBJ d1 = OBJ d1'”
                 (REWRITE_ALL_THM o SYM o REWRITE_RULE[object_one_one])
            THEN RES_TAC
            THEN POP_TAC
            THEN EXISTS_TAC “update (OBJ d4) l m4”
            THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat,REDL_update_LEMMA]
          ],

        EXISTS_TAC “d3:^dict”
        THEN ASM_REWRITE_TAC[REDL_rules_sat],

        IMP_RES_TAC REDL_dict_cases
        THEN RES_TAC
        THEN EXISTS_TAC “CONS e4 (d4:^dict)”
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        EXISTS_TAC “e3:^entry”
        THEN ASM_REWRITE_TAC[REDL_rules_sat],

        IMP_RES_TAC REDL_entry_cases
        THEN RES_TAC
        THEN EXISTS_TAC “(l,m4):^entry”
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        EXISTS_TAC “m3:method”
        THEN ASM_REWRITE_TAC[REDL_rules_sat],

        IMP_RES_TAC REDL_method_cases
        THEN RES_TAC
        THEN EXISTS_TAC “SIGMA x o4”
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat]
      ]
   );

val REDL_DIAMOND = store_thm
   ("REDL_DIAMOND",
    “DIAMOND REDL_obj /\
        DIAMOND REDL_dict /\
        DIAMOND REDL_entry /\
        DIAMOND REDL_method”,
    REWRITE_TAC[DIAMOND]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_DIAMOND_LEMMA
    THENL
      [ EXISTS_TAC “o4':obj”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d4':^dict”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “e4':^entry”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “m4':method”
        THEN ASM_REWRITE_TAC[]
      ]
   );


(* copied: *)

val RC_INDUCT_TAC =
 let val rc_thm = RC_INDUCT
     fun tac (asl,w) =
      let open Rsyntax
          val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
          val (RC,Ru'v') = boolSyntax.strip_comb ant
          val R = hd Ru'v'
          val u'v' = tl Ru'v'
          val u' = hd u'v'
          val v' = hd (tl u'v')
          (*val (RC,[R,u',v']) = boolSyntax.strip_comb ant*)
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

   RC (RED1 SIGMA_R)     SUBSET     REDL     SUBSET     RED SIGMA_R

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


val RED1_SIGMA_IMP_REDL_LEMMA = store_thm
   ("RED1_SIGMA_IMP_REDL_LEMMA",
    “(!R o1 o2.
          RED1_obj R o1 o2 ==> (R = SIGMA_R) ==> REDL_obj o1 o2) /\
        (!R d1 d2.
          RED1_dict R d1 d2 ==> (R = SIGMA_R) ==> REDL_dict d1 d2) /\
        (!R e1 e2.
          RED1_entry R e1 e2 ==> (R = SIGMA_R) ==> REDL_entry e1 e2) /\
        (!R m1 m2.
          RED1_method R m1 m2 ==> (R = SIGMA_R) ==> REDL_method m1 m2)”,
    rule_induct RED1_ind_thm
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THENL
      [ POP_ASSUM (STRIP_ASSUME_TAC o ONCE_REWRITE_RULE SIGMA_R_inv_thms)
        THEN DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat],

        DEP_ASM_REWRITE_TAC[REDL_rules_sat]
      ]
   );


val RED1_SIGMA_IMP_REDL = store_thm
   ("RED1_SIGMA_IMP_REDL",
    “(!o1 o2.
          RED1_obj SIGMA_R o1 o2 ==> REDL_obj o1 o2) /\
        (!d1 d2.
          RED1_dict SIGMA_R d1 d2 ==> REDL_dict d1 d2) /\
        (!e1 e2.
          RED1_entry SIGMA_R e1 e2 ==> REDL_entry e1 e2) /\
        (!m1 m2.
          RED1_method SIGMA_R m1 m2 ==> REDL_method m1 m2)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_SIGMA_IMP_REDL_LEMMA
    THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[])
   );

val RC_RED1_SIGMA_IMP_REDL = store_thm
   ("RC_RED1_SIGMA_IMP_REDL",
    “(!o1 o2. RC (RED1_obj SIGMA_R) o1 o2 ==> REDL_obj o1 o2) /\
        (!d1 d2. RC (RED1_dict SIGMA_R) d1 d2 ==> REDL_dict d1 d2) /\
        (!e1 e2. RC (RED1_entry SIGMA_R) e1 e2 ==> REDL_entry e1 e2) /\
        (!m1 m2. RC (RED1_method SIGMA_R) m1 m2 ==> REDL_method m1 m2)”,
    REPEAT CONJ_TAC
    THEN RC_INDUCT_TAC
    THEN REWRITE_TAC[REDL_rules_sat]
    THEN REWRITE_TAC[RED1_SIGMA_IMP_REDL]
   );

val [RED1_R, RED1_OBJ, RED1_INVOKE, RED1_UPDATE1, RED1_UPDATE,
     RED1_CONS1, RED1_CONS2, RED1_PAIR, RED1_SIGMA] = CONJUNCTS RED1_rules_sat;

val [RED_obj_RED1, RED_obj_REFL, RED_obj_TRANS,
     RED_dict_RED1, RED_dict_REFL, RED_dict_TRANS,
     RED_entry_RED1, RED_entry_REFL, RED_entry_TRANS,
     RED_method_RED1, RED_method_REFL, RED_method_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) RED_rules_sat);

val RED1_SIGMA_R = store_thm
   ("RED1_SIGMA_R",
    “(!d l.
          RED1_obj SIGMA_R (INVOKE (OBJ d) l) (invoke (OBJ d) l)) /\
        (!d l m.
          RED1_obj SIGMA_R (UPDATE (OBJ d) l m) (update (OBJ d) l m))”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC RED1_R
    THEN REWRITE_TAC[SIGMA_R_rules_sat]
   );

val RED_SIGMA_R = store_thm
   ("RED_SIGMA_R",
    “(!d1 d2 l.
          RED_dict SIGMA_R d1 d2 ==>
          RED_obj SIGMA_R (INVOKE (OBJ d1) l) (invoke (OBJ d2) l)) /\
        (!d1 d2 l m1 m2.
          RED_dict SIGMA_R d1 d2 /\
          RED_method SIGMA_R m1 m2 ==>
          RED_obj SIGMA_R (UPDATE (OBJ d1) l m1) (update (OBJ d2) l m2))
    ”,
    REPEAT STRIP_TAC
    THENL
      [ MATCH_MP_TAC RED_obj_TRANS
        THEN EXISTS_TAC “INVOKE (OBJ d2) l”
        THEN CONJ_TAC
        THENL
          [ IMP_RES_TAC RED_COMPAT
            THEN IMP_RES_TAC RED_COMPAT
            THEN ASM_REWRITE_TAC[],

            DEP_ASM_REWRITE_TAC[RED_RED1]
            THEN REWRITE_TAC[RED1_SIGMA_R]
          ],

        MATCH_MP_TAC RED_obj_TRANS
        THEN EXISTS_TAC “UPDATE (OBJ d2) l m2”
        THEN CONJ_TAC
        THENL
          [ IMP_RES_TAC RED_COMPAT
            THEN IMP_RES_TAC RED_COMPAT
            THEN MATCH_MP_TAC RED_obj_TRANS
            THEN EXISTS_TAC “UPDATE (OBJ d2) l m1”
            THEN ASM_REWRITE_TAC[],

            DEP_ASM_REWRITE_TAC[RED_RED1]
            THEN REWRITE_TAC[RED1_SIGMA_R]
          ]
      ]
   );


val REDL_IMP_RED_SIGMA = store_thm
   ("REDL_IMP_RED_SIGMA",
    “(!o1 o2. REDL_obj o1 o2 ==> RED_obj SIGMA_R o1 o2) /\
        (!d1 d2. REDL_dict d1 d2 ==> RED_dict SIGMA_R d1 d2) /\
        (!e1 e2. REDL_entry e1 e2 ==> RED_entry SIGMA_R e1 e2) /\
        (!m1 m2. REDL_method m1 m2 ==> RED_method SIGMA_R m1 m2)”,
    rule_induct REDL_ind_thm
    THEN REPEAT STRIP_TAC
    THENL (* 12 subgoals *)
      [ REWRITE_TAC[RED_REFL],

        IMP_RES_TAC RED_COMPAT,

        IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC RED_COMPAT
        THEN FIRST_ASSUM (ASSUME_TAC o SPECL[“m1:method”,“l:string”])
        THEN FIRST_ASSUM (ASSUME_TAC o SPECL[“o2:obj”,“l:string”])
        THEN IMP_RES_TAC RED_obj_TRANS,

        DEP_ASM_REWRITE_TAC[RED_SIGMA_R],

        DEP_ASM_REWRITE_TAC[RED_SIGMA_R],

        REWRITE_TAC[RED_REFL],

        IMP_RES_TAC RED_COMPAT
        THEN FIRST_ASSUM (ASSUME_TAC o SPEC “e1:^entry”)
        THEN FIRST_ASSUM (ASSUME_TAC o SPEC “d2:^dict”)
        THEN IMP_RES_TAC RED_TRANS,

        REWRITE_TAC[RED_REFL],

        IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        REWRITE_TAC[RED_REFL],

        IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[]
     ]
   );


val TC_RC_SIGMA_IMP_RED_SIGMA = store_thm
   ("TC_RC_SIGMA_IMP_RED_SIGMA",
    “(!o1 o2. TC (RC (RED1_obj SIGMA_R)) o1 o2
                 ==> RED_obj SIGMA_R o1 o2) /\
        (!d1 d2. TC (RC (RED1_dict SIGMA_R)) d1 d2
                 ==> RED_dict SIGMA_R d1 d2) /\
        (!e1 e2. TC (RC (RED1_entry SIGMA_R)) e1 e2
                 ==> RED_entry SIGMA_R e1 e2) /\
        (!m1 m2. TC (RC (RED1_method SIGMA_R)) m1 m2
                 ==> RED_method SIGMA_R m1 m2)”,
    REPEAT CONJ_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RC_RED1_SIGMA_IMP_REDL
    THEN IMP_RES_TAC REDL_IMP_RED_SIGMA
    THEN IMP_RES_TAC RED_TRANS
   );

val RED_IMP_TC_RC_RED1 = store_thm
   ("RED_IMP_TC_RC_RED1",
    “(!R o1 o2. RED_obj R o1 o2
                   ==> TC (RC (RED1_obj R)) o1 o2) /\
        (!R d1 d2. RED_dict R d1 d2
                   ==> TC (RC (RED1_dict R)) d1 d2) /\
        (!R e1 e2. RED_entry R e1 e2
                   ==> TC (RC (RED1_entry R)) e1 e2) /\
        (!R m1 m2. RED_method R m1 m2
                   ==> TC (RC (RED1_method R)) m1 m2)”,
    rule_induct RED_ind_thm
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC (REWRITE_RULE[transitive_def] TC_TRANSITIVE)
    THEN MATCH_MP_TAC TC_SUBSET
    THEN REWRITE_TAC[RC_REFLEXIVE]
    THEN IMP_RES_TAC RC_SUBSET
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val TC_RC_SIGMA_IS_RED_SIGMA = store_thm
   ("TC_RC_SIGMA_IS_RED_SIGMA",
    “(!o1 o2. TC (RC (RED1_obj SIGMA_R)) o1 o2
                 = RED_obj SIGMA_R o1 o2) /\
        (!d1 d2. TC (RC (RED1_dict SIGMA_R)) d1 d2
                 = RED_dict SIGMA_R d1 d2) /\
        (!e1 e2. TC (RC (RED1_entry SIGMA_R)) e1 e2
                 = RED_entry SIGMA_R e1 e2) /\
        (!m1 m2. TC (RC (RED1_method SIGMA_R)) m1 m2
                 = RED_method SIGMA_R m1 m2)”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN ( EQ_TAC
           THEN STRIP_TAC
           THENL
             [ IMP_RES_TAC TC_RC_SIGMA_IMP_RED_SIGMA,

               IMP_RES_TAC RED_IMP_TC_RC_RED1
             ])
   );


val TC_REDL_IMP_RED_SIGMA = store_thm
   ("TC_REDL_IMP_RED_SIGMA",
    “(!o1 o2. TC REDL_obj o1 o2 ==> RED_obj SIGMA_R o1 o2) /\
        (!d1 d2. TC REDL_dict d1 d2 ==> RED_dict SIGMA_R d1 d2) /\
        (!e1 e2. TC REDL_entry e1 e2 ==> RED_entry SIGMA_R e1 e2) /\
        (!m1 m2. TC REDL_method m1 m2 ==> RED_method SIGMA_R m1 m2)”,
    REPEAT CONJ_TAC
    THEN TC_INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REDL_IMP_RED_SIGMA
    THEN IMP_RES_TAC RED_TRANS
   );

val TC_MONOTONIC_LEMMA = store_thm
   ("TC_MONOTONIC_LEMMA",
    “!R1 R2 (a:'a) b.
          TC R1 a b ==> (!x y. R1 x y ==> R2 x y) ==> TC R2 a b”,
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

val TC_REDL_IS_RED_SIGMA_LEMMA = store_thm
   ("TC_REDL_IS_RED_SIGMA_LEMMA",
    “(!o1 o2. TC REDL_obj o1 o2 = RED_obj SIGMA_R o1 o2) /\
        (!d1 d2. TC REDL_dict d1 d2 = RED_dict SIGMA_R d1 d2) /\
        (!e1 e2. TC REDL_entry e1 e2 = RED_entry SIGMA_R e1 e2) /\
        (!m1 m2. TC REDL_method m1 m2 = RED_method SIGMA_R m1 m2)”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN ( EQ_TAC
           THEN STRIP_TAC
           THENL
             [ IMP_RES_TAC TC_REDL_IMP_RED_SIGMA,

               UNDISCH_LAST_TAC
               THEN REWRITE_TAC[GSYM TC_RC_SIGMA_IS_RED_SIGMA]
               THEN MATCH_MP_TAC TC_MONOTONIC
               THEN REWRITE_TAC[RC_RED1_SIGMA_IMP_REDL]
             ])
   );

val TC_REDL_IS_RED_SIGMA = store_thm
   ("TC_REDL_IS_RED_SIGMA",
    “(TC REDL_obj = RED_obj SIGMA_R) /\
        (TC REDL_dict = RED_dict SIGMA_R) /\
        (TC REDL_entry = RED_entry SIGMA_R) /\
        (TC REDL_method = RED_method SIGMA_R)”,
    REPEAT CONJ_TAC
    THENL
      [ EXT_TAC “o1:obj”
        THEN GEN_TAC
        THEN EXT_TAC “o2:obj”
        THEN GEN_TAC,

        EXT_TAC “d1:^dict”
        THEN GEN_TAC
        THEN EXT_TAC “d2:^dict”
        THEN GEN_TAC,

        EXT_TAC “e1:^entry”
        THEN GEN_TAC
        THEN EXT_TAC “e2:^entry”
        THEN GEN_TAC,

        EXT_TAC “m1:method”
        THEN GEN_TAC
        THEN EXT_TAC “m2:method”
        THEN GEN_TAC
      ]
    THEN REWRITE_TAC[TC_REDL_IS_RED_SIGMA_LEMMA]
   );



val SIGMA_R_CHURCH_ROSSER = store_thm
   ("SIGMA_R_CHURCH_ROSSER",
    “CHURCH_ROSSER SIGMA_R”,
    REWRITE_TAC[CHURCH_ROSSER]
    THEN REWRITE_TAC[GSYM TC_REDL_IS_RED_SIGMA]
    THEN REPEAT CONJ_TAC
    THEN MATCH_MP_TAC TC_DIAMOND
    THEN REWRITE_TAC[REDL_DIAMOND]
   );
(* Soli Deo Gloria!!!  To God Alone Be The Glory!!! *)


val SIGMA_R_NORMAL_FORM_EXISTS = store_thm
   ("SIGMA_R_NORMAL_FORM_EXISTS",
    “(!M N. REQUAL_obj SIGMA_R M N ==>
                (?Z. RED_obj SIGMA_R M Z /\ RED_obj SIGMA_R N Z)) /\
        (!M N. REQUAL_dict SIGMA_R M N ==>
                (?Z. RED_dict SIGMA_R M Z /\ RED_dict SIGMA_R N Z)) /\
        (!M N. REQUAL_entry SIGMA_R M N ==>
                (?Z. RED_entry SIGMA_R M Z /\ RED_entry SIGMA_R N Z)) /\
        (!M N. REQUAL_method SIGMA_R M N ==>
                (?Z. RED_method SIGMA_R M Z /\ RED_method SIGMA_R N Z))”,
    MATCH_MP_TAC NORMAL_FORM_EXISTS
    THEN REWRITE_TAC[SIGMA_R_CHURCH_ROSSER]
   );

val SIGMA_R_NORMAL_FORM_REDUCED_TO = store_thm
   ("SIGMA_R_NORMAL_FORM_REDUCED_TO",
    “(!M N. NORMAL_FORM_OF_obj SIGMA_R N M ==>
               RED_obj SIGMA_R M N) /\
        (!M N. NORMAL_FORM_OF_dict SIGMA_R N M ==>
               RED_dict SIGMA_R M N) /\
        (!M N. NORMAL_FORM_OF_entry SIGMA_R N M ==>
               RED_entry SIGMA_R M N) /\
        (!M N. NORMAL_FORM_OF_method SIGMA_R N M ==>
               RED_method SIGMA_R M N)”,
    MATCH_MP_TAC NORMAL_FORM_REDUCED_TO
    THEN REWRITE_TAC[SIGMA_R_CHURCH_ROSSER]
   );

val SIGMA_R_NORMAL_FORM_UNIQUE = store_thm
   ("SIGMA_R_NORMAL_FORM_UNIQUE",
    “(!M N1 N2. NORMAL_FORM_OF_obj SIGMA_R N1 M /\
                   NORMAL_FORM_OF_obj SIGMA_R N2 M ==> (N1 = N2)) /\
        (!M N1 N2. NORMAL_FORM_OF_dict SIGMA_R N1 M /\
                   NORMAL_FORM_OF_dict SIGMA_R N2 M ==> (N1 = N2)) /\
        (!M N1 N2. NORMAL_FORM_OF_entry SIGMA_R N1 M /\
                   NORMAL_FORM_OF_entry SIGMA_R N2 M ==> (N1 = N2)) /\
        (!M N1 N2. NORMAL_FORM_OF_method SIGMA_R N1 M /\
                   NORMAL_FORM_OF_method SIGMA_R N2 M ==> (N1 = N2))”,
    MATCH_MP_TAC NORMAL_FORM_UNIQUE
    THEN REWRITE_TAC[SIGMA_R_CHURCH_ROSSER]
   );


val _ = export_theory();

val _ = print_theory_to_file "semantics.lst";

val _ = html_theory "semantics";

val _ = print_theory_size();
