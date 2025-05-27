open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Embedding the reduction semantaics of objects as a foundational       *)
(* layer, according to Abadi and Cardelli, "A Theory of Objects."        *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "reduction";


open listTheory;
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

open tactics;



val vars   =  ty_antiq( ==`:var list`== );
val subs   =  ty_antiq( ==`:(var # obj) list`== );
val dict  =  ty_antiq( ==`:(string # method) list`== );
val entry =  ty_antiq( ==`:string # method`== );


val [ALPHA_obj_REFL, ALPHA_dict_REFL, ALPHA_entry_REFL,
     ALPHA_method_REFL]
    = CONJUNCTS ALPHA_REFL;

val [ALPHA_obj_SYM, ALPHA_dict_SYM, ALPHA_entry_SYM,
     ALPHA_method_SYM]
    = CONJUNCTS ALPHA_SYM;

val [ALPHA_obj_TRANS, ALPHA_dict_TRANS, ALPHA_entry_TRANS,
     ALPHA_method_TRANS]
    = CONJUNCTS ALPHA_TRANS;



val HEIGHT_SUB_VAR = store_thm
   ("HEIGHT_SUB_VAR",
    “(!a x y.
          HEIGHT_obj (a <[ [x,OVAR y]) = HEIGHT_obj a) /\
        (!d x y.
          HEIGHT_dict (d <[ [x,OVAR y]) = HEIGHT_dict d) /\
        (!e x y.
          HEIGHT_entry (e <[ [x,OVAR y]) = HEIGHT_entry e) /\
        (!m x y.
          HEIGHT_method (m <[ [x,OVAR y]) = HEIGHT_method m)”,
    MUTUAL_INDUCT_THEN object_height_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL
      [ REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_object]
        THEN ASM_REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_object]
        THEN ASM_REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_object]
        THEN ASM_REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_object]
        THEN ASM_REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_object]
        THEN ASM_REWRITE_TAC[HEIGHT],

        REWRITE_TAC[SUB_object]
        THEN ASM_REWRITE_TAC[HEIGHT],
(*
        SHIFT_SIGMAS_TAC
        THEN MAKE_SIMPLE_SUBST_TAC
*)
        SIMPLE_SUBST_TAC
        THEN ASM_REWRITE_TAC[HEIGHT]
      ]
   );



(* Barendregt's Substitution Lemma, 2.1.16, page 27: *)

val BARENDREGT_SUBSTITUTION_LEMMA = store_thm
   ("BARENDREGT_SUBSTITUTION_LEMMA",
    “(!(M:obj) N L x y.
          ~(x = y) /\ ~(x IN FV_obj L) ==>
          (((M <[ [x,N]) <[ [y,L]) =
           ((M <[ [y,L]) <[ [x, (N <[ [y,L])]))) /\
        (!(M:^dict) N L x y.
          ~(x = y) /\ ~(x IN FV_obj L) ==>
          (((M <[ [x,N]) <[ [y,L]) =
           ((M <[ [y,L]) <[ [x, (N <[ [y,L])]))) /\
        (!(M:^entry) N L x y.
          ~(x = y) /\ ~(x IN FV_obj L) ==>
          (((M <[ [x,N]) <[ [y,L]) =
           ((M <[ [y,L]) <[ [x, (N <[ [y,L])]))) /\
        (!(M:method) N L x y.
          ~(x = y) /\ ~(x IN FV_obj L) ==>
          (((M <[ [x,N]) <[ [y,L]) =
           ((M <[ [y,L]) <[ [x, (N <[ [y,L])])))”,
    MUTUAL_INDUCT_THEN object_height_induct ASSUME_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THENL
          [ POP_ASSUM REWRITE_ALL_THM
            THEN EVERY_ASSUM REWRITE_THM
            THEN REWRITE_TAC[SUB_object,SUB],

            REWRITE_TAC[SUB_object,SUB]
            THEN COND_CASES_TAC
            THENL
              [ IMP_RES_THEN REWRITE_THM subst_EMPTY,

                ASM_REWRITE_TAC[SUB_object,SUB]
              ]
          ],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REPEAT STRIP_TAC
        THEN SIMPLE_SUBST_TAC
        THEN DEP_ASM_REWRITE_TAC[]
      ]
   );


val COLLAPSE_SUBST = store_thm
   ("COLLAPSE_SUBST",
    “(!M x y N.
          ~(y IN FV_obj M) ==>
          (((M <[ [x,OVAR y]) <[ [y,N]) = (M <[ [x,N]))) /\
        (!M x y N.
          ~(y IN FV_dict M) ==>
          (((M <[ [x,OVAR y]) <[ [y,N]) = (M <[ [x,N]))) /\
        (!M x y N.
          ~(y IN FV_entry M) ==>
          (((M <[ [x,OVAR y]) <[ [y,N]) = (M <[ [x,N]))) /\
        (!M x y N.
          ~(y IN FV_method M) ==>
          (((M <[ [x,OVAR y]) <[ [y,N]) = (M <[ [x,N])))”,
    MUTUAL_INDUCT_THEN object_height_induct ASSUME_TAC
    THENL
      [ REWRITE_TAC[FV_object,IN]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THENL
          [ REWRITE_TAC[SUB_object,SUB],

            REWRITE_TAC[SUB_object,SUB]
            THEN EVERY_ASSUM (REWRITE_THM o GSYM)
          ],

        REWRITE_TAC[FV_object,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REWRITE_TAC[FV_object,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REWRITE_TAC[FV_object,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REWRITE_TAC[FV_object,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REWRITE_TAC[FV_object,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REWRITE_TAC[FV_object,IN,IN_UNION,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_object],

        REWRITE_TAC[FV_object,IN,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN SIMPLE_SUBST_TAC
        THEN DEP_ASM_REWRITE_TAC[]
        THEN UNDISCH_TAC “~(y IN FV_obj M DIFF {x})”
        THEN FIRST_ASSUM (REWRITE_THM o REWRITE_RULE[FV_object] o
                          AP_TERM “FV_method”)
        THEN REWRITE_TAC[IN_DIFF,IN,DE_MORGAN_THM]
        THEN EVERY_ASSUM (REWRITE_THM o GSYM)
      ]
   );



(* --------------------------------------------------------------------- *)
(* General reduction relations and theorems:                             *)
(*   "Lambda Calculus," Barendregt, Chapter 3, page 50-63                *)
(* --------------------------------------------------------------------- *)


(* Define the reflexive closure of a relation.                           *)

(* Wait!  Now, this is done in relationTheory!

But the following definition is not the same as that in relationTheory. *)

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
          val (RC,[R,u',v']) = boolSyntax.strip_comb ant
          val {Name = "RC",...} = dest_const RC
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

(* Must use what is provided now in relationTheory.
*)


(* --------------------------------------------------------------------- *)
(* Define compatible relations on the object/method language.            *)
(* --------------------------------------------------------------------- *)

val compatible =
    new_definition ("compatible",
    “compatible Ro Rd Re Rm =
        ((!o1 o2. Ro o1 o2 ==> (!l. Ro (INVOKE o1 l) (INVOKE o2 l))  /\
                               (!l m. Ro (UPDATE o1 l m) (UPDATE o2 l m))  /\
                               (!x. Rm (SIGMA x o1) (SIGMA x o2)))
          /\
         (!d1 d2. Rd d1 d2 ==> Ro (OBJ d1) (OBJ d2)  /\
                               (!e. Rd (CONS e d1) (CONS e d2)))
          /\
         (!e1 e2. Re e1 e2 ==> (!d. Rd (CONS e1 d) (CONS e2 d)))
          /\
         (!m1 m2. Rm m1 m2 ==> (!o' l. Ro (UPDATE o' l m1) (UPDATE o' l m2))
                               /\
                               (!l. Re (l, m1) (l, m2))))”);

val reflexve =
    new_definition ("reflexve",
    “reflexve Ro Rd Re Rm =
        ((!o1: obj. Ro o1 o1)  /\
         (!d1:^dict. Rd d1 d1)  /\
         (!e1:^entry. Re e1 e1)  /\
         (!m1: method. Rm m1 m1))”);

val _ = hide "symmetric";

val symmetric =
    new_definition ("symmetric",
    “symmetric Ro Rd Re Rm =
        ((!o1 o2: obj. Ro o1 o2 ==> Ro o2 o1)  /\
         (!d1 d2:^dict. Rd d1 d2 ==> Rd d2 d1)  /\
         (!e1 e2:^entry. Re e1 e2 ==> Re e2 e1)  /\
         (!m1 m2: method. Rm m1 m2 ==> Rm m2 m1))”);

val transitive =
    new_definition ("transitve",
    “transitve Ro Rd Re Rm =
        ((!o1 o2 o3: obj. Ro o1 o2 /\ Ro o2 o3 ==> Ro o1 o3)  /\
         (!d1 d2 d3:^dict. Rd d1 d2 /\ Rd d2 d3 ==> Rd d1 d3)  /\
         (!e1 e2 e3:^entry. Re e1 e2 /\ Re e2 e3 ==> Re e1 e3)  /\
         (!m1 m2 m3: method. Rm m1 m2 /\ Rm m2 m3 ==> Rm m1 m3))”);

val equality =
    new_definition ("equality",
    “equality Ro Rd Re Rm =
        (compatible Ro Rd Re Rm /\
         reflexve   Ro Rd Re Rm /\
         symmetric  Ro Rd Re Rm /\
         transitve  Ro Rd Re Rm)”);

val reduction =
    new_definition ("reduction",
    “reduction Ro Rd Re Rm =
        (compatible Ro Rd Re Rm /\
         reflexve   Ro Rd Re Rm /\
         transitve  Ro Rd Re Rm)”);




(* --------------------------------------------------------------------- *)
(* (RED1 R o1 o2) means that the object o1 reduces to the object o2      *)
(*  in exactly one step, as defined in Barendregt, Definition 3.1.5,     *)
(*  page 51.  This is the compatible closure of R.                       *)
(* --------------------------------------------------------------------- *)


val RED1_obj =
“RED1_obj : (obj -> obj -> bool) -> obj -> obj -> bool”;
val RED1_dict =
“RED1_dict : (obj -> obj -> bool) -> ^dict -> ^dict -> bool”;
val RED1_entry =
“RED1_entry : (obj -> obj -> bool) -> ^entry -> ^entry -> bool”;
val RED1_method =
“RED1_method : (obj -> obj -> bool) -> method -> method -> bool”;

val RED1_patterns =     [“^RED1_obj R o1 o2”,
                         “^RED1_dict R d1 d2”,
                         “^RED1_entry R e1 e2”,
                         “^RED1_method R m1 m2”
                        ];

val RED1_rules_tm =
“
                           ((R o1 o2)
       (* -------------------------------------------- *) ==>
                       (^RED1_obj R o1 o2))                                 /\


                     ((^RED1_dict R d1 d2)
       (* -------------------------------------------- *) ==>
                (^RED1_obj R (OBJ d1) (OBJ d2)))                          /\


                      ((^RED1_obj R o1 o2)
       (* -------------------------------------------- *) ==>
            (^RED1_obj R (INVOKE o1 l) (INVOKE o2 l)))                    /\


                      ((^RED1_obj R o1 o2)
       (* -------------------------------------------- *) ==>
         (^RED1_obj R (UPDATE o1 l m) (UPDATE o2 l m)))                   /\


                    ((^RED1_method R m1 m2)
       (* -------------------------------------------- *) ==>
         (^RED1_obj R (UPDATE a l m1) (UPDATE a l m2)))                   /\


                    ((^RED1_entry R e1 e2)
       (* -------------------------------------------- *) ==>
            (^RED1_dict R (CONS e1 d) (CONS e2 d)))                         /\


                     ((^RED1_dict R d1 d2)
       (* -------------------------------------------- *) ==>
            (^RED1_dict R (CONS e d1) (CONS e d2)))                         /\


                    ((^RED1_method R m1 m2)
       (* -------------------------------------------- *) ==>
                (^RED1_entry R (l, m1) (l, m2)))                            /\


                     ((^RED1_obj R o1 o2)
       (* -------------------------------------------- *) ==>
           (^RED1_method R (SIGMA x o1) (SIGMA x o2)))
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


val [RED1_R, RED1_OBJ, RED1_INVOKE, RED1_UPDATE1, RED1_UPDATE2,
     RED1_CONS1, RED1_CONS2, RED1_PAIR, RED1_SIGMA] = CONJUNCTS RED1_rules_sat;




val RED1_height_ind_thm_LEMMA = store_thm
   ("RED1_height_ind_thm_LEMMA",
    “!n P_0 P_1 P_2 P_3.
         (!R o1 o2. R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2. P_1 R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
         (!R o1 l o2. P_0 R o1 o2 ==> P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
         (!R o1 l m o2.
           P_0 R o1 o2 ==> P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
         (!R a l m1 m2.
           P_3 R m1 m2 ==> P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
         (!R e1 d e2. P_2 R e1 e2 ==> P_1 R (CONS e1 d) (CONS e2 d)) /\
         (!R e d1 d2. P_1 R d1 d2 ==> P_1 R (CONS e d1) (CONS e d2)) /\
         (!R l m1 m2. P_3 R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
         (!R x o1 o2.
           (!o1' o2'. RED1_obj R o1' o2' /\
                      (HEIGHT_obj o1 = HEIGHT_obj o1') /\
                      (HEIGHT_obj o2 = HEIGHT_obj o2') ==> P_0 R o1' o2')
            ==> P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
         (!R o1 o2. RED1_obj R o1 o2 ==>
                    ((HEIGHT_obj o1 <= n) /\
                     (HEIGHT_obj o2 <= n) ==>
                     P_0 R o1 o2)) /\
         (!R d1 d2. RED1_dict R d1 d2 ==>
                    ((HEIGHT_dict d1 <= n) /\
                     (HEIGHT_dict d2 <= n) ==>
                     P_1 R d1 d2)) /\
         (!R e1 e2. RED1_entry R e1 e2 ==>
                    ((HEIGHT_entry e1 <= n) /\
                     (HEIGHT_entry e2 <= n) ==>
                     P_2 R e1 e2)) /\
         (!R m1 m2. RED1_method R m1 m2 ==>
                    ((HEIGHT_method m1 <= n) /\
                     (HEIGHT_method m2 <= n) ==>
                     P_3 R m1 m2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN UNDISCH_TAC “RED1_obj R o1 o2”
            THEN ONCE_REWRITE_TAC RED1_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct],

            UNDISCH_TAC “RED1_dict R d1 d2”
            THEN ONCE_REWRITE_TAC RED1_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS]
          ],

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
        THENL (* 9 subgoals *)
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
    “!P_0 P_1 P_2 P_3.
         (!R o1 o2. R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2. P_1 R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
         (!R o1 l o2. P_0 R o1 o2 ==> P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
         (!R o1 l m o2.
           P_0 R o1 o2 ==> P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
         (!R a l m1 m2.
           P_3 R m1 m2 ==> P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
         (!R e1 d e2. P_2 R e1 e2 ==> P_1 R (CONS e1 d) (CONS e2 d)) /\
         (!R e d1 d2. P_1 R d1 d2 ==> P_1 R (CONS e d1) (CONS e d2)) /\
         (!R l m1 m2. P_3 R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
         (!R x o1 o2.
           (!o1' o2'. RED1_obj R o1' o2' /\
                      (HEIGHT_obj o1 = HEIGHT_obj o1') /\
                      (HEIGHT_obj o2 = HEIGHT_obj o2') ==> P_0 R o1' o2')
            ==> P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
         (!R o1 o2. RED1_obj R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2. RED1_dict R d1 d2 ==> P_1 R d1 d2) /\
         (!R e1 e2. RED1_entry R e1 e2 ==> P_2 R e1 e2) /\
         (!R m1 m2. RED1_method R m1 m2 ==> P_3 R m1 m2)”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL (SPEC tm RED1_height_ind_thm_LEMMA)))
           [“(HEIGHT_obj o1) MAX (HEIGHT_obj o2)”,
            “(HEIGHT_dict d1) MAX (HEIGHT_dict d2)”,
            “(HEIGHT_entry e1) MAX (HEIGHT_entry e2)”,
            “(HEIGHT_method m1) MAX (HEIGHT_method m2)”])
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_MAX]
   );


val RED1_height_strong_ind_LEMMA = store_thm
   ("RED1_height_strong_ind_LEMMA",
    “!n P_0 P_1 P_2 P_3.
         (!R o1 o2. R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2.
           P_1 R d1 d2 /\ RED1_dict R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
         (!R o1 l o2.
           P_0 R o1 o2 /\ RED1_obj R o1 o2 ==>
           P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
         (!R o1 l m o2.
           P_0 R o1 o2 /\ RED1_obj R o1 o2 ==>
           P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
         (!R a l m1 m2.
           P_3 R m1 m2 /\ RED1_method R m1 m2 ==>
           P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
         (!R e1 d e2.
           P_2 R e1 e2 /\ RED1_entry R e1 e2 ==>
           P_1 R (CONS e1 d) (CONS e2 d)) /\
         (!R e d1 d2.
           P_1 R d1 d2 /\ RED1_dict R d1 d2 ==>
           P_1 R (CONS e d1) (CONS e d2)) /\
         (!R l m1 m2.
           P_3 R m1 m2 /\ RED1_method R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
         (!R x o1 o2.
           (!o1' o2'.
             RED1_obj R o1' o2' /\
             (HEIGHT_obj o1 = HEIGHT_obj o1') /\
             (HEIGHT_obj o2 = HEIGHT_obj o2') ==>
             P_0 R o1' o2') /\
           RED1_obj R o1 o2 ==>
           P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
         (!R o1 o2. RED1_obj R o1 o2 ==>
                    ((HEIGHT_obj o1 <= n) /\
                     (HEIGHT_obj o2 <= n) ==>
                     P_0 R o1 o2)) /\
         (!R d1 d2. RED1_dict R d1 d2 ==>
                    ((HEIGHT_dict d1 <= n) /\
                     (HEIGHT_dict d2 <= n) ==>
                     P_1 R d1 d2)) /\
         (!R e1 e2. RED1_entry R e1 e2 ==>
                    ((HEIGHT_entry e1 <= n) /\
                     (HEIGHT_entry e2 <= n) ==>
                     P_2 R e1 e2)) /\
         (!R m1 m2. RED1_method R m1 m2 ==>
                    ((HEIGHT_method m1 <= n) /\
                     (HEIGHT_method m2 <= n) ==>
                     P_3 R m1 m2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN UNDISCH_TAC “RED1_obj R o1 o2”
            THEN ONCE_REWRITE_TAC RED1_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct],

            UNDISCH_TAC “RED1_dict R d1 d2”
            THEN ONCE_REWRITE_TAC RED1_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS]
          ],

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
        THENL (* 9 subgoals *)
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
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THEN UNDISCH_THEN
                 “!(R:obj->obj->bool) o1 o2. R o1 o2 ==> P_0 R o1 o2”
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
    “!P_0 P_1 P_2 P_3.
         (!R o1 o2. R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2.
           P_1 R d1 d2 /\ RED1_dict R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
         (!R o1 l o2.
           P_0 R o1 o2 /\ RED1_obj R o1 o2 ==>
           P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
         (!R o1 l m o2.
           P_0 R o1 o2 /\ RED1_obj R o1 o2 ==>
           P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
         (!R a l m1 m2.
           P_3 R m1 m2 /\ RED1_method R m1 m2 ==>
           P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
         (!R e1 d e2.
           P_2 R e1 e2 /\ RED1_entry R e1 e2 ==>
           P_1 R (CONS e1 d) (CONS e2 d)) /\
         (!R e d1 d2.
           P_1 R d1 d2 /\ RED1_dict R d1 d2 ==>
           P_1 R (CONS e d1) (CONS e d2)) /\
         (!R l m1 m2.
           P_3 R m1 m2 /\ RED1_method R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
         (!R x o1 o2.
           (!o1' o2'.
             RED1_obj R o1' o2' /\
             (HEIGHT_obj o1 = HEIGHT_obj o1') /\
             (HEIGHT_obj o2 = HEIGHT_obj o2') ==>
             P_0 R o1' o2') /\
           RED1_obj R o1 o2 ==>
           P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
         (!R o1 o2. RED1_obj R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2. RED1_dict R d1 d2 ==> P_1 R d1 d2) /\
         (!R e1 e2. RED1_entry R e1 e2 ==> P_2 R e1 e2) /\
         (!R m1 m2. RED1_method R m1 m2 ==> P_3 R m1 m2)”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL (SPEC tm RED1_height_strong_ind_LEMMA)))
           [“(HEIGHT_obj o1) MAX (HEIGHT_obj o2)”,
            “(HEIGHT_dict d1) MAX (HEIGHT_dict d2)”,
            “(HEIGHT_entry e1) MAX (HEIGHT_entry e2)”,
            “(HEIGHT_method m1) MAX (HEIGHT_method m2)”])
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
    “!R. compatible
                (RED1_obj R) (RED1_dict R) (RED1_entry R) (RED1_method R)”,
    REWRITE_TAC[compatible]
    THEN CONV_TAC (TOP_DEPTH_CONV FORALL_AND_CONV)
    THEN rule_induct RED1_strong_ind
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC RED1_R
    THEN FIRST (map (fn th => MATCH_MP_TAC th
                              THEN ASM_REWRITE_TAC[]
                              THEN NO_TAC)
                    (CONJUNCTS RED1_rules_sat))
   );



(* We now need to define the reflexive and transitive closure of this. *)

(* --------------------------------------------------------------------- *)
(* (RED R o1 o2) means that the object o1 reduces to the object o2       *)
(*  in zero or more steps, as defined in Barendregt, Definition 3.1.5,   *)
(*  page 51.  This is the reflexive and transitive closure of RED1 R.    *)
(* --------------------------------------------------------------------- *)

val RED_obj =
“RED_obj : (obj -> obj -> bool) -> obj -> obj -> bool”;
val RED_dict =
“RED_dict : (obj -> obj -> bool) -> ^dict -> ^dict -> bool”;
val RED_entry =
“RED_entry : (obj -> obj -> bool) -> ^entry -> ^entry -> bool”;
val RED_method =
“RED_method : (obj -> obj -> bool) -> method -> method -> bool”;

val RED_patterns =      [“^RED_obj R o1 o2”,
                         “^RED_dict R d1 d2”,
                         “^RED_entry R e1 e2”,
                         “^RED_method R m1 m2”
                        ];

val RED_rules_tm =
“

                       (RED1_obj R o1 o2
       (* -------------------------------------------- *) ==>
                       ^RED_obj R o1 o2)                                   /\


       (* -------------------------------------------- *)
                      (^RED_obj R o1 o1)                                   /\


              (^RED_obj R o1 o2 /\ ^RED_obj R o2 o3
       (* -------------------------------------------- *) ==>
                       ^RED_obj R o1 o3)                                   /\


                       (RED1_dict R d1 d2
       (* -------------------------------------------- *) ==>
                       ^RED_dict R d1 d2)                                 /\


       (* -------------------------------------------- *)
                      (^RED_dict R d1 d1)                                 /\


             (^RED_dict R d1 d2 /\ ^RED_dict R d2 d3
       (* -------------------------------------------- *) ==>
                       ^RED_dict R d1 d3)                                 /\


                      (RED1_entry R e1 e2
       (* -------------------------------------------- *) ==>
                      ^RED_entry R e1 e2)                                 /\


       (* -------------------------------------------- *)
                     (^RED_entry R e1 e1)                                 /\


            (^RED_entry R e1 e2 /\ ^RED_entry R e2 e3
       (* -------------------------------------------- *) ==>
                      ^RED_entry R e1 e3)                                 /\


                     (RED1_method R m1 m2
       (* -------------------------------------------- *) ==>
                     ^RED_method R m1 m2)                                 /\


       (* -------------------------------------------- *)
                    (^RED_method R m1 m1)                                 /\


           (^RED_method R m1 m2 /\ ^RED_method R m2 m3
       (* -------------------------------------------- *) ==>
                     ^RED_method R m1 m3)
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


val [RED_obj_RED1, RED_obj_REFL, RED_obj_TRANS,
     RED_dict_RED1, RED_dict_REFL, RED_dict_TRANS,
     RED_entry_RED1, RED_entry_REFL, RED_entry_TRANS,
     RED_method_RED1, RED_method_REFL, RED_method_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) RED_rules_sat);

val RED_RED1 = save_thm
  ("RED_RED1",
        LIST_CONJ [RED_obj_RED1, RED_dict_RED1,
                   RED_entry_RED1, RED_method_RED1]);

val RED_REFL = save_thm
  ("RED_REFL",
        LIST_CONJ [RED_obj_REFL, RED_dict_REFL,
                   RED_entry_REFL, RED_method_REFL]);


val [RED_obj_inv, RED_dict_inv, RED_entry_inv, RED_method_inv]
    = RED_inv_thms;


val RED_reflexive = store_thm
   ("RED_reflexive",
    “!R. reflexve
              (RED_obj R) (RED_dict R) (RED_entry R) (RED_method R)”,
    REWRITE_TAC[reflexve]
    THEN REWRITE_TAC[RED_REFL]
   );

val RED_transitive = store_thm
   ("RED_transitive",
    “!R. transitve
           (RED_obj R) (RED_dict R) (RED_entry R) (RED_method R)”,
    REWRITE_TAC[transitive]
    THEN REWRITE_TAC[CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
                               RED_rules_sat]
   );

val RED_TRANS = save_thm("RED_TRANS",
                   CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV)
                    (REWRITE_RULE[transitive] RED_transitive));

val RED_compatible = store_thm
   ("RED_compatible",
    “!R. compatible
             (RED_obj R) (RED_dict R) (RED_entry R) (RED_method R)”,
    REWRITE_TAC[compatible]
    THEN CONV_TAC (TOP_DEPTH_CONV FORALL_AND_CONV)
    THEN rule_induct RED_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 24 subgoals *)
    THEN REWRITE_TAC[RED_REFL] (* takes care of 8 *)
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC RED_TRANS (* solves another 8 *)
    THEN IMP_RES_TAC (REWRITE_RULE[compatible] RED1_compatible)
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC RED_RED1 (* finishes the last 8 *)
   );

val RED_COMPAT = save_thm("RED_COMPAT",
                   CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV)
                    (REWRITE_RULE[compatible] RED_compatible));

val [RED_obj_COMPAT, RED_dict_COMPAT, RED_entry_COMPAT, RED_method_COMPAT]
    = CONJUNCTS RED_COMPAT;



val RED_reduction = store_thm
   ("RED_reduction",
    “!R. reduction
               (RED_obj R) (RED_dict R) (RED_entry R) (RED_method R)”,
    REWRITE_TAC[reduction]
    THEN REWRITE_TAC[RED_compatible,RED_reflexive,RED_transitive]
   );



(* Barendregt's Substitution Remark, 3.1.7, page 52: *)

val BARENDREGT_SUBSTITUTION_REMARK = store_thm
   ("BARENDREGT_SUBSTITUTION_REMARK",
    “(!M N N' x.
          RED_obj R N N' ==>
          RED_obj R (M <[ [x,N]) (M <[ [x,N'])) /\
        (!M N N' x.
          RED_obj R N N' ==>
          RED_dict R (M <[ [x,N]) (M <[ [x,N'])) /\
        (!M N N' x.
          RED_obj R N N' ==>
          RED_entry R (M <[ [x,N]) (M <[ [x,N'])) /\
        (!M N N' x.
          RED_obj R N N' ==>
          RED_method R (M <[ [x,N]) (M <[ [x,N']))”,
    MUTUAL_INDUCT_THEN object_height_induct ASSUME_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_object,SUB]
        THEN COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[],

            REWRITE_TAC[RED_REFL]
          ],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT,

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED_obj_TRANS
        THEN EXISTS_TAC “UPDATE (M <[ [x,N']) l (M' <[ [x,N])”
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED_dict_TRANS
        THEN EXISTS_TAC “CONS ((M:^entry) <[ [x,N']) (M' <[ [x,N])”
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_object,RED_dict_REFL],

        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC
        THEN SIMPLE_SUBST_TAC
        THEN RES_TAC
        THEN POP_ASSUM (ASSUME_TAC o SPEC “x':var”)
        THEN IMP_RES_TAC RED_COMPAT
        THEN ASM_REWRITE_TAC[]
      ]
   );



(* We now need to define the equivalence relation generated by R. *)

(* --------------------------------------------------------------------- *)
(* (REQUAL R o1 o2) means that the object o1 is R-convertible to the     *)
(*  object o2, as defined in Barendregt, Definition 3.1.5, page 51.      *)
(*  This is the symmetric and transitive closure of RED R.               *)
(* --------------------------------------------------------------------- *)

val REQUAL_obj =
“REQUAL_obj : (obj -> obj -> bool) -> obj -> obj -> bool”;
val REQUAL_dict =
“REQUAL_dict : (obj -> obj -> bool) -> ^dict -> ^dict -> bool”;
val REQUAL_entry =
“REQUAL_entry : (obj -> obj -> bool) -> ^entry -> ^entry -> bool”;
val REQUAL_method =
“REQUAL_method : (obj -> obj -> bool) -> method -> method -> bool”;

val REQUAL_patterns =   [“^REQUAL_obj R o1 o2”,
                         “^REQUAL_dict R d1 d2”,
                         “^REQUAL_entry R e1 e2”,
                         “^REQUAL_method R m1 m2”
                        ];

val REQUAL_rules_tm =
“
                       (RED_obj R o1 o2
       (* -------------------------------------------- *) ==>
                      ^REQUAL_obj R o1 o2)                                 /\

                      (REQUAL_obj R o1 o2
       (* -------------------------------------------- *) ==>
                      ^REQUAL_obj R o2 o1)                                 /\

           (^REQUAL_obj R o1 o2 /\ ^REQUAL_obj R o2 o3
       (* -------------------------------------------- *) ==>
                      ^REQUAL_obj R o1 o3)                                 /\


                       (RED_dict R d1 d2
       (* -------------------------------------------- *) ==>
                      ^REQUAL_dict R d1 d2)                               /\

                     (^REQUAL_dict R d1 d2
       (* -------------------------------------------- *) ==>
                      ^REQUAL_dict R d2 d1)                               /\

          (^REQUAL_dict R d1 d2 /\ ^REQUAL_dict R d2 d3
       (* -------------------------------------------- *) ==>
                      ^REQUAL_dict R d1 d3)                               /\


                      (RED_entry R e1 e2
       (* -------------------------------------------- *) ==>
                     ^REQUAL_entry R e1 e2)                               /\

                    (^REQUAL_entry R e1 e2
       (* -------------------------------------------- *) ==>
                     ^REQUAL_entry R e2 e1)                               /\

         (^REQUAL_entry R e1 e2 /\ ^REQUAL_entry R e2 e3
       (* -------------------------------------------- *) ==>
                     ^REQUAL_entry R e1 e3)                               /\


                     (RED_method R m1 m2
       (* -------------------------------------------- *) ==>
                    ^REQUAL_method R m1 m2)                               /\

                    (REQUAL_method R m1 m2
       (* -------------------------------------------- *) ==>
                    ^REQUAL_method R m2 m1)                               /\


        (^REQUAL_method R m1 m2 /\ ^REQUAL_method R m2 m3
       (* -------------------------------------------- *) ==>
                    ^REQUAL_method R m1 m3)
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
(* We claim that REQUAL is a binary relation on the object/method        *)
(* language which is                                                     *)
(*  1) compatible (in the sense of Barendregt, Definition 3.1.1, pg 50   *)
(*  2) the symmetric, transitive closure of the RED relation, in the     *)
(*     sense of Barendregt, Definition 3.1.4 and 3.1.5, pg 51.           *)
(*  3) an equivalence relation, from 2) and that RED is reflexive.       *)
(*  4) an equality relation, as a compatible equivalence relation.       *)
(* --------------------------------------------------------------------- *)


val [REQUAL_obj_RED, REQUAL_obj_SYM, REQUAL_obj_TRANS,
     REQUAL_dict_RED, REQUAL_dict_SYM, REQUAL_dict_TRANS,
     REQUAL_entry_RED, REQUAL_entry_SYM, REQUAL_entry_TRANS,
     REQUAL_method_RED, REQUAL_method_SYM, REQUAL_method_TRANS]
    = CONJUNCTS (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) REQUAL_rules_sat);

val REQUAL_RED = save_thm
  ("REQUAL_RED",
        LIST_CONJ [REQUAL_obj_RED, REQUAL_dict_RED,
                   REQUAL_entry_RED, REQUAL_method_RED]);

val REQUAL_SYM = save_thm
  ("REQUAL_SYM",
        LIST_CONJ [REQUAL_obj_SYM, REQUAL_dict_SYM,
                   REQUAL_entry_SYM, REQUAL_method_SYM]);


val [REQUAL_obj_inv, REQUAL_dict_inv, REQUAL_entry_inv, REQUAL_method_inv]
    = REQUAL_inv_thms;


val REQUAL_reflexive = store_thm
   ("REQUAL_reflexive",
    “!R. reflexve
              (REQUAL_obj R)
              (REQUAL_dict R)
              (REQUAL_entry R)
              (REQUAL_method R)”,
    REWRITE_TAC[reflexve]
    THEN REPEAT STRIP_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS REQUAL_RED))
    THEN REWRITE_TAC[RED_REFL]
   );

val REQUAL_symmetric = store_thm
   ("REQUAL_symmetric",
    “!R. symmetric
              (REQUAL_obj R)
              (REQUAL_dict R)
              (REQUAL_entry R)
              (REQUAL_method R)”,
    REWRITE_TAC[symmetric]
    THEN REWRITE_TAC[REQUAL_SYM]
   );

val REQUAL_transitive = store_thm
   ("REQUAL_transitive",
    “!R. transitve
           (REQUAL_obj R)
              (REQUAL_dict R)
              (REQUAL_entry R)
              (REQUAL_method R)”,
    REWRITE_TAC[transitive]
    THEN REWRITE_TAC[CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
                               REQUAL_rules_sat]
   );

val REQUAL_TRANS = save_thm("REQUAL_TRANS",
                   CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV)
                    (REWRITE_RULE[transitive] REQUAL_transitive));

val REQUAL_compatible = store_thm
   ("REQUAL_compatible",
    “!R. compatible
             (REQUAL_obj R)
              (REQUAL_dict R)
              (REQUAL_entry R)
              (REQUAL_method R)”,
    REWRITE_TAC[compatible]
    THEN CONV_TAC (TOP_DEPTH_CONV FORALL_AND_CONV)
    THEN rule_induct REQUAL_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 24 subgoals *)
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC REQUAL_SYM (* takes care of 8 *)
    THEN IMP_RES_TAC REQUAL_TRANS (* solves another 8 *)
    THEN IMP_RES_TAC RED_COMPAT
    THEN RULE_ASSUM_TAC SPEC_ALL
    THEN IMP_RES_TAC REQUAL_RED (* finishes the last 8 *)
   );

val REQUAL_COMPAT = save_thm("REQUAL_COMPAT",
                   CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV)
                    (REWRITE_RULE[compatible] REQUAL_compatible));

val [REQUAL_obj_COMPAT, REQUAL_dict_COMPAT,
     REQUAL_entry_COMPAT, REQUAL_method_COMPAT]
    = CONJUNCTS REQUAL_COMPAT;


val REQUAL_reduction = store_thm
   ("REQUAL_reduction",
    “!R. reduction
               (REQUAL_obj R)
               (REQUAL_dict R)
               (REQUAL_entry R)
               (REQUAL_method R)”,
    REWRITE_TAC[reduction]
    THEN REWRITE_TAC[REQUAL_compatible,REQUAL_reflexive,REQUAL_transitive]
   );

val REQUAL_equality = store_thm
   ("REQUAL_equality",
    “!R. equality
               (REQUAL_obj R)
               (REQUAL_dict R)
               (REQUAL_entry R)
               (REQUAL_method R)”,
    REWRITE_TAC[equality]
    THEN REWRITE_TAC[REQUAL_compatible,REQUAL_reflexive,
                    REQUAL_symmetric,REQUAL_transitive]
   );



                         (* ============ *)
                         (* NORMAL FORMS *)
                         (* ============ *)


val NORMAL_FORM_obj =
    new_definition
    ("NORMAL_FORM_obj",
     “NORMAL_FORM_obj R a = (!a'. ~(RED1_obj R a a'))”);

val NORMAL_FORM_dict =
    new_definition
    ("NORMAL_FORM_dict",
     “NORMAL_FORM_dict R a = (!a'. ~(RED1_dict R a a'))”);

val NORMAL_FORM_entry =
    new_definition
    ("NORMAL_FORM_entry",
     “NORMAL_FORM_entry R a = (!a'. ~(RED1_entry R a a'))”);

val NORMAL_FORM_method =
    new_definition
    ("NORMAL_FORM_method",
     “NORMAL_FORM_method R a = (!a'. ~(RED1_method R a a'))”);

val NORMAL_FORM = save_thm
  ("NORMAL_FORM",
        LIST_CONJ [NORMAL_FORM_obj, NORMAL_FORM_dict,
                   NORMAL_FORM_entry, NORMAL_FORM_method]);


val NORMAL_FORM_OF_obj =
    new_definition
    ("NORMAL_FORM_OF_obj",
     “NORMAL_FORM_OF_obj R a b =
         (NORMAL_FORM_obj R a /\ REQUAL_obj R b a)”);

val NORMAL_FORM_OF_dict =
    new_definition
    ("NORMAL_FORM_OF_dict",
     “NORMAL_FORM_OF_dict R a b =
         (NORMAL_FORM_dict R a /\ REQUAL_dict R b a)”);

val NORMAL_FORM_OF_entry =
    new_definition
    ("NORMAL_FORM_OF_entry",
     “NORMAL_FORM_OF_entry R a b =
         (NORMAL_FORM_entry R a /\ REQUAL_entry R b a)”);

val NORMAL_FORM_OF_method =
    new_definition
    ("NORMAL_FORM_OF_method",
     “NORMAL_FORM_OF_method R a b =
         (NORMAL_FORM_method R a /\ REQUAL_method R b a)”);

val NORMAL_FORM_OF = save_thm
  ("NORMAL_FORM_OF",
        LIST_CONJ [NORMAL_FORM_OF_obj, NORMAL_FORM_OF_dict,
                   NORMAL_FORM_OF_entry, NORMAL_FORM_OF_method]);


val NORMAL_FORM_IDENT_LEMMA = store_thm
   ("NORMAL_FORM_IDENT_LEMMA",
    “(!R M N. RED_obj R M N ==> (NORMAL_FORM_obj R M ==> (M = N))) /\
        (!R M N. RED_dict R M N ==> (NORMAL_FORM_dict R M ==> (M = N))) /\
        (!R M N. RED_entry R M N ==> (NORMAL_FORM_entry R M ==> (M = N))) /\
        (!R M N. RED_method R M N ==> (NORMAL_FORM_method R M ==> (M = N)))
       ”,
    rule_induct RED_ind_thm (* weak, not strong induction *)
    THEN REWRITE_TAC[NORMAL_FORM]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN RES_TAC
   );

val NORMAL_FORM_IDENT = store_thm
   ("NORMAL_FORM_IDENT",
    “(!R M. NORMAL_FORM_obj R M ==> (!N. RED_obj R M N ==> (M = N))) /\
        (!R M. NORMAL_FORM_dict R M ==> (!N. RED_dict R M N ==> (M = N))) /\
        (!R M. NORMAL_FORM_entry R M ==> (!N. RED_entry R M N ==> (M = N))) /\
        (!R M. NORMAL_FORM_method R M ==> (!N. RED_method R M N ==> (M = N)))
       ”,
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
     “CHURCH_ROSSER R =
            (DIAMOND (RED_obj R) /\
             DIAMOND (RED_dict R) /\
             DIAMOND (RED_entry R) /\
             DIAMOND (RED_method R))”);



val NORMAL_FORM_EXISTS_LEMMA = store_thm
   ("NORMAL_FORM_EXISTS_LEMMA",
    “(!R M N. REQUAL_obj R M N ==>
                  (CHURCH_ROSSER R ==>
                   (?Z. RED_obj R M Z /\ RED_obj R N Z))) /\
        (!R M N. REQUAL_dict R M N ==>
                  (CHURCH_ROSSER R ==>
                   (?Z. RED_dict R M Z /\ RED_dict R N Z))) /\
        (!R M N. REQUAL_entry R M N ==>
                  (CHURCH_ROSSER R ==>
                   (?Z. RED_entry R M Z /\ RED_entry R N Z))) /\
        (!R M N. REQUAL_method R M N ==>
                  (CHURCH_ROSSER R ==>
                   (?Z. RED_method R M Z /\ RED_method R N Z)))”,
    rule_induct REQUAL_ind_thm (* weak, not strong induction *)
    THEN REWRITE_TAC[CHURCH_ROSSER,DIAMOND]
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THENL
      [ EXISTS_TAC “o2:obj”
        THEN ASM_REWRITE_TAC[RED_REFL],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th => REPEAT DISCH_TAC THEN MP_TAC th)
        THEN ASM_REWRITE_TAC[]
        THEN STRIP_TAC
        THEN EXISTS_TAC “Z:obj”
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th1 =>
                DISCH_THEN (fn th2 =>
                    REPEAT DISCH_TAC THEN MP_TAC th2 THEN MP_TAC th1))
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM (fn imp => STRIP_ASSUME_TAC
                 (MATCH_MP imp (CONJ (ASSUME “RED_obj R o2 Z”)
                                     (ASSUME “RED_obj R o2 Z'”))))
        THEN EXISTS_TAC “d:obj”
        THEN IMP_RES_TAC RED_TRANS
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d2:^dict”
        THEN ASM_REWRITE_TAC[RED_REFL],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th => REPEAT DISCH_TAC THEN MP_TAC th)
        THEN ASM_REWRITE_TAC[]
        THEN STRIP_TAC
        THEN EXISTS_TAC “Z:^dict”
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th1 =>
                DISCH_THEN (fn th2 =>
                    REPEAT DISCH_TAC THEN MP_TAC th2 THEN MP_TAC th1))
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM (fn imp => STRIP_ASSUME_TAC
                 (MATCH_MP imp (CONJ (ASSUME “RED_dict R d2 Z”)
                                     (ASSUME “RED_dict R d2 Z'”))))
        THEN EXISTS_TAC “d:^dict”
        THEN IMP_RES_TAC RED_TRANS
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “e2:^entry”
        THEN ASM_REWRITE_TAC[RED_REFL],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th => REPEAT DISCH_TAC THEN MP_TAC th)
        THEN ASM_REWRITE_TAC[]
        THEN STRIP_TAC
        THEN EXISTS_TAC “Z:^entry”
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th1 =>
                DISCH_THEN (fn th2 =>
                    REPEAT DISCH_TAC THEN MP_TAC th2 THEN MP_TAC th1))
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM (fn imp => STRIP_ASSUME_TAC
                 (MATCH_MP imp (CONJ (ASSUME “RED_entry R e2 Z”)
                                     (ASSUME “RED_entry R e2 Z'”))))
        THEN EXISTS_TAC “d:^entry”
        THEN IMP_RES_TAC RED_TRANS
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “m2:method”
        THEN ASM_REWRITE_TAC[RED_REFL],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th => REPEAT DISCH_TAC THEN MP_TAC th)
        THEN ASM_REWRITE_TAC[]
        THEN STRIP_TAC
        THEN EXISTS_TAC “Z:method”
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN (fn th1 =>
                DISCH_THEN (fn th2 =>
                    REPEAT DISCH_TAC THEN MP_TAC th2 THEN MP_TAC th1))
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM (fn imp => STRIP_ASSUME_TAC
                 (MATCH_MP imp (CONJ (ASSUME “RED_method R m2 Z”)
                                     (ASSUME “RED_method R m2 Z'”))))
        THEN EXISTS_TAC “d:method”
        THEN IMP_RES_TAC RED_TRANS
        THEN ASM_REWRITE_TAC[]
      ]
   );

val NORMAL_FORM_EXISTS = store_thm
   ("NORMAL_FORM_EXISTS",
    “!R. CHURCH_ROSSER R ==>
         (!M N. REQUAL_obj R M N ==>
                (?Z. RED_obj R M Z /\ RED_obj R N Z)) /\
         (!M N. REQUAL_dict R M N ==>
                (?Z. RED_dict R M Z /\ RED_dict R N Z)) /\
         (!M N. REQUAL_entry R M N ==>
                (?Z. RED_entry R M Z /\ RED_entry R N Z)) /\
         (!M N. REQUAL_method R M N ==>
                (?Z. RED_method R M Z /\ RED_method R N Z))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC NORMAL_FORM_EXISTS_LEMMA
    THENL
      [ EXISTS_TAC “Z:obj”,
        EXISTS_TAC “Z:^dict”,
        EXISTS_TAC “Z:^entry”,
        EXISTS_TAC “Z:method”
      ]
    THEN ASM_REWRITE_TAC[]
   );

val NORMAL_FORM_REDUCED_TO = store_thm
   ("NORMAL_FORM_REDUCED_TO",
    “!R. CHURCH_ROSSER R ==>
         (!M N. NORMAL_FORM_OF_obj R N M ==> RED_obj R M N) /\
         (!M N. NORMAL_FORM_OF_dict R N M ==> RED_dict R M N) /\
         (!M N. NORMAL_FORM_OF_entry R N M ==> RED_entry R M N) /\
         (!M N. NORMAL_FORM_OF_method R N M ==> RED_method R M N)”,
    REWRITE_TAC[NORMAL_FORM_OF]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC NORMAL_FORM_EXISTS
    THEN IMP_RES_TAC NORMAL_FORM_IDENT
    THEN ASM_REWRITE_TAC[]
   );

val NORMAL_FORM_UNIQUE = store_thm
   ("NORMAL_FORM_UNIQUE",
    “!R. CHURCH_ROSSER R ==>
         (!M N1 N2. NORMAL_FORM_OF_obj R N1 M /\
                    NORMAL_FORM_OF_obj R N2 M ==> (N1 = N2)) /\
         (!M N1 N2. NORMAL_FORM_OF_dict R N1 M /\
                    NORMAL_FORM_OF_dict R N2 M ==> (N1 = N2)) /\
         (!M N1 N2. NORMAL_FORM_OF_entry R N1 M /\
                    NORMAL_FORM_OF_entry R N2 M ==> (N1 = N2)) /\
         (!M N1 N2. NORMAL_FORM_OF_method R N1 M /\
                    NORMAL_FORM_OF_method R N2 M ==> (N1 = N2))”,
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


val SUBSTITUTIVE_obj =
    new_definition
    ("SUBSTITUTIVE_obj",
     “SUBSTITUTIVE_obj R =
           (!(M:obj) (N:obj) L x.
             R M N ==> R (M <[ [x,L]) (N <[ [x,L]))”);

val SUBSTITUTIVE_dict =
    new_definition
    ("SUBSTITUTIVE_dict",
     “SUBSTITUTIVE_dict R =
           (!(M:^dict) (N:^dict) L x.
             R M N ==> R (M <[ [x,L]) (N <[ [x,L]))”);

val SUBSTITUTIVE_entry =
    new_definition
    ("SUBSTITUTIVE_entry",
     “SUBSTITUTIVE_entry R =
           (!(M:^entry) (N:^entry) L x.
             R M N ==> R (M <[ [x,L]) (N <[ [x,L]))”);

val SUBSTITUTIVE_method =
    new_definition
    ("SUBSTITUTIVE_method",
     “SUBSTITUTIVE_method R =
           (!(M:method) (N:method) L x.
             R M N ==> R (M <[ [x,L]) (N <[ [x,L]))”);

val SUBSTITUTIVE = save_thm
  ("SUBSTITUTIVE",
        LIST_CONJ [SUBSTITUTIVE_obj, SUBSTITUTIVE_dict,
                   SUBSTITUTIVE_entry, SUBSTITUTIVE_method]);


val RED1_SUBSTITUTIVE_LEMMA = TAC_PROOF(([],
    “(!R M N.
          RED1_obj R M N ==>
            ((!M N L x. R M N ==> R (M <[ [x,L]) (N <[ [x,L])) ==>
               (!L x. RED1_obj R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          RED1_dict R M N ==>
            ((!M N L x. R M N ==> R (M <[ [x,L]) (N <[ [x,L])) ==>
               (!L x. RED1_dict R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          RED1_entry R M N ==>
            ((!M N L x. R M N ==> R (M <[ [x,L]) (N <[ [x,L])) ==>
               (!L x. RED1_entry R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          RED1_method R M N ==>
            ((!M N L x. R M N ==> R (M <[ [x,L]) (N <[ [x,L])) ==>
               (!L x. RED1_method R (M <[ [x,L]) (N <[ [x,L]))))”),
    rule_induct RED1_height_strong_ind (* strong, not weak induction *)
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THENL
      [ RES_TAC
        THEN MATCH_MP_TAC RED1_R
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_OBJ
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_INVOKE
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_UPDATE1
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_UPDATE2
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_CONS1
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_CONS2
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN REWRITE_TAC[SUB_object]
        THEN MATCH_MP_TAC RED1_PAIR
        THEN ASM_REWRITE_TAC[],

        SIMPLE_SUBST_TAC
        THEN MATCH_MP_TAC RED1_SIGMA
        THEN FIRST_ASSUM
                (MATCH_MP_TAC o
                   REWRITE_RULE[AND_IMP_INTRO] o
                    CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM o CONJUNCT1 o
                          REWRITE_RULE[SIGMA_one_one])
        THEN POP_ASSUM (REWRITE_THM o SYM o CONJUNCT1 o
                          REWRITE_RULE[SIGMA_one_one])
        THEN FIRST_ASSUM
                (MATCH_MP_TAC o
                   REWRITE_RULE[AND_IMP_INTRO] o
                    CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
        THEN ASM_REWRITE_TAC[]
      ]
   );


val RED1_SUBSTITUTIVE = store_thm
   ("RED1_SUBSTITUTIVE",
    “!R. SUBSTITUTIVE_obj R ==>
               SUBSTITUTIVE_obj (RED1_obj R) /\
               SUBSTITUTIVE_dict (RED1_dict R) /\
               SUBSTITUTIVE_entry (RED1_entry R) /\
               SUBSTITUTIVE_method (RED1_method R)”,
    REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THEN IMP_RES_TAC RED1_SUBSTITUTIVE_LEMMA
    THEN ASM_REWRITE_TAC[]
   );


val RED1_SUBSTITUTIVE_ind_thm_LEMMA = store_thm
   ("RED1_SUBSTITUTIVE_ind_thm_LEMMA",
    “!n P_0 P_1 P_2 P_3.
         (!R o1 o2. SUBSTITUTIVE_obj R /\
           R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2. SUBSTITUTIVE_obj R /\
           P_1 R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
         (!R o1 l o2. SUBSTITUTIVE_obj R /\
           P_0 R o1 o2 ==> P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
         (!R o1 l m o2.
           SUBSTITUTIVE_obj R /\
           P_0 R o1 o2 ==> P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
         (!R a l m1 m2.
           SUBSTITUTIVE_obj R /\
           P_3 R m1 m2 ==> P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
         (!R e1 d e2. SUBSTITUTIVE_obj R /\
           P_2 R e1 e2 ==> P_1 R (CONS e1 d) (CONS e2 d)) /\
         (!R e d1 d2. SUBSTITUTIVE_obj R /\
           P_1 R d1 d2 ==> P_1 R (CONS e d1) (CONS e d2)) /\
         (!R l m1 m2. SUBSTITUTIVE_obj R /\
           P_3 R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
         (!R x o1 o2. SUBSTITUTIVE_obj R /\
           (!z. P_0 R (o1 <[ [x,OVAR z]) (o2 <[ [x,OVAR z]))
            ==> P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
         (!R o1 o2. RED1_obj R o1 o2 ==>
                    (SUBSTITUTIVE_obj R /\
                     (HEIGHT_obj o1 <= n) /\
                     (HEIGHT_obj o2 <= n) ==>
                     P_0 R o1 o2)) /\
         (!R d1 d2. RED1_dict R d1 d2 ==>
                    (SUBSTITUTIVE_obj R /\
                     (HEIGHT_dict d1 <= n) /\
                     (HEIGHT_dict d2 <= n) ==>
                     P_1 R d1 d2)) /\
         (!R e1 e2. RED1_entry R e1 e2 ==>
                    (SUBSTITUTIVE_obj R /\
                     (HEIGHT_entry e1 <= n) /\
                     (HEIGHT_entry e2 <= n) ==>
                     P_2 R e1 e2)) /\
         (!R m1 m2. RED1_method R m1 m2 ==>
                    (SUBSTITUTIVE_obj R /\
                     (HEIGHT_method m1 <= n) /\
                     (HEIGHT_method m2 <= n) ==>
                     P_3 R m1 m2))”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN UNDISCH_TAC “RED1_obj R o1 o2”
            THEN ONCE_REWRITE_TAC RED1_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS],

            UNDISCH_TAC “RED1_dict R d1 d2”
            THEN ONCE_REWRITE_TAC RED1_inv_thms
            THEN ASM_REWRITE_TAC[object_distinct,NOT_NIL_CONS]
          ],

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
        THENL (* 9 subgoals *)
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
    “!P_0 P_1 P_2 P_3.
         (!R o1 o2. SUBSTITUTIVE_obj R /\
           R o1 o2 ==> P_0 R o1 o2) /\
         (!R d1 d2. SUBSTITUTIVE_obj R /\
           P_1 R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
         (!R o1 l o2. SUBSTITUTIVE_obj R /\
           P_0 R o1 o2 ==> P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
         (!R o1 l m o2. SUBSTITUTIVE_obj R /\
           P_0 R o1 o2 ==> P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
         (!R a l m1 m2. SUBSTITUTIVE_obj R /\
           P_3 R m1 m2 ==> P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
         (!R e1 d e2. SUBSTITUTIVE_obj R /\
           P_2 R e1 e2 ==> P_1 R (CONS e1 d) (CONS e2 d)) /\
         (!R e d1 d2. SUBSTITUTIVE_obj R /\
           P_1 R d1 d2 ==> P_1 R (CONS e d1) (CONS e d2)) /\
         (!R l m1 m2. SUBSTITUTIVE_obj R /\
           P_3 R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
         (!R x o1 o2. SUBSTITUTIVE_obj R /\
           (!z. P_0 R (o1 <[ [x,OVAR z]) (o2 <[ [x,OVAR z]))
            ==> P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
         (!R o1 o2. RED1_obj R o1 o2 ==>
                    (SUBSTITUTIVE_obj R ==>
                     P_0 R o1 o2)) /\
         (!R d1 d2. RED1_dict R d1 d2 ==>
                    (SUBSTITUTIVE_obj R ==>
                     P_1 R d1 d2)) /\
         (!R e1 e2. RED1_entry R e1 e2 ==>
                    (SUBSTITUTIVE_obj R ==>
                     P_2 R e1 e2)) /\
         (!R m1 m2. RED1_method R m1 m2 ==>
                    (SUBSTITUTIVE_obj R ==>
                     P_3 R m1 m2))”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL
                             (SPEC tm RED1_SUBSTITUTIVE_ind_thm_LEMMA)))
           [“(HEIGHT_obj o1) MAX (HEIGHT_obj o2)”,
            “(HEIGHT_dict d1) MAX (HEIGHT_dict d2)”,
            “(HEIGHT_entry e1) MAX (HEIGHT_entry e2)”,
            “(HEIGHT_method m1) MAX (HEIGHT_method m2)”])
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_MAX]
   );


val RED1_SUBSTITUTIVE_ind_thm = store_thm
   ("RED1_SUBSTITUTIVE_ind_thm",
    “!R. SUBSTITUTIVE_obj R ==>
         !P_0 P_1 P_2 P_3.
          (!R o1 o2. R o1 o2 ==> P_0 R o1 o2) /\
          (!R d1 d2. P_1 R d1 d2 ==> P_0 R (OBJ d1) (OBJ d2)) /\
          (!R o1 l o2. P_0 R o1 o2 ==> P_0 R (INVOKE o1 l) (INVOKE o2 l)) /\
          (!R o1 l m o2.
            P_0 R o1 o2 ==> P_0 R (UPDATE o1 l m) (UPDATE o2 l m)) /\
          (!R a l m1 m2.
            P_3 R m1 m2 ==> P_0 R (UPDATE a l m1) (UPDATE a l m2)) /\
          (!R e1 d e2. P_2 R e1 e2 ==> P_1 R (CONS e1 d) (CONS e2 d)) /\
          (!R e d1 d2. P_1 R d1 d2 ==> P_1 R (CONS e d1) (CONS e d2)) /\
          (!R l m1 m2. P_3 R m1 m2 ==> P_2 R (l,m1) (l,m2)) /\
          (!R x o1 o2. SUBSTITUTIVE_obj R /\
            (!z. P_0 R (o1 <[ [x,OVAR z]) (o2 <[ [x,OVAR z]))
             ==> P_3 R (SIGMA x o1) (SIGMA x o2)) ==>
          (!o1 o2. RED1_obj R o1 o2 ==> P_0 R o1 o2) /\
          (!d1 d2. RED1_dict R d1 d2 ==> P_1 R d1 d2) /\
          (!e1 e2. RED1_entry R e1 e2 ==> P_2 R e1 e2) /\
          (!m1 m2. RED1_method R m1 m2 ==> P_3 R m1 m2)”,
    GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN UNDISCH_TAC “SUBSTITUTIVE_obj R”
    THEN REWRITE_TAC[tautLib.TAUT_PROVE
               “(a ==> (b /\ c)) = ((a ==> b) /\ (a ==> c))”]
    THEN CONV_TAC (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REWRITE_TAC[AND_IMP_INTRO]
    THEN ONCE_REWRITE_TAC[ISPEC “SUBSTITUTIVE_obj R” CONJ_SYM]
    THEN REWRITE_TAC[GSYM AND_IMP_INTRO]
    THEN SPEC_TAC (“R:obj->obj->bool”,“R:obj->obj->bool”)
    THEN CONV_TAC (TOP_DEPTH_CONV FORALL_AND_CONV)
    THEN MATCH_MP_TAC RED1_SUBSTITUTIVE_ind_thm_LEMMA1
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );



val RED_SUBSTITUTIVE_LEMMA = TAC_PROOF(([],
    “(!R M N.
          RED_obj R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. RED_obj R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          RED_dict R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. RED_dict R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          RED_entry R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. RED_entry R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          RED_method R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. RED_method R (M <[ [x,L]) (N <[ [x,L]))))”),
    rule_induct RED_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THEN FIRST
      [ REWRITE_TAC[RED_REFL]
        THEN NO_TAC,

        RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_TRANS
        THEN NO_TAC,

        IMP_RES_TAC RED1_SUBSTITUTIVE
        THEN REWRITE_ALL_TAC[SUBSTITUTIVE]
        THEN RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC RED_RED1
        THEN NO_TAC
      ]
   );


val RED_SUBSTITUTIVE = store_thm
   ("RED_SUBSTITUTIVE",
    “!R. SUBSTITUTIVE_obj R ==>
               SUBSTITUTIVE_obj (RED_obj R) /\
               SUBSTITUTIVE_dict (RED_dict R) /\
               SUBSTITUTIVE_entry (RED_entry R) /\
               SUBSTITUTIVE_method (RED_method R)”,
    GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THEN IMP_RES_TAC RED_SUBSTITUTIVE_LEMMA
    THEN ASM_REWRITE_TAC[]
   );



val REQUAL_SUBSTITUTIVE_LEMMA = TAC_PROOF(([],
    “(!R M N.
          REQUAL_obj R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. REQUAL_obj R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          REQUAL_dict R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. REQUAL_dict R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          REQUAL_entry R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. REQUAL_entry R (M <[ [x,L]) (N <[ [x,L])))) /\
        (!R M N.
          REQUAL_method R M N ==>
            (SUBSTITUTIVE_obj R ==>
               (!L x. REQUAL_method R (M <[ [x,L]) (N <[ [x,L]))))”),
    rule_induct REQUAL_ind_thm (* weak, not strong induction *)
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THEN FIRST
      [ RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC REQUAL_SYM
        THEN NO_TAC,

        RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC REQUAL_TRANS
        THEN NO_TAC,

        IMP_RES_TAC RED_SUBSTITUTIVE
        THEN REWRITE_ALL_TAC[SUBSTITUTIVE]
        THEN RES_TAC
        THEN RULE_ASSUM_TAC SPEC_ALL
        THEN IMP_RES_TAC REQUAL_RED
        THEN NO_TAC
      ]
   );


val REQUAL_SUBSTITUTIVE = store_thm
   ("REQUAL_SUBSTITUTIVE",
    “!R. SUBSTITUTIVE_obj R ==>
               SUBSTITUTIVE_obj (REQUAL_obj R) /\
               SUBSTITUTIVE_dict (REQUAL_dict R) /\
               SUBSTITUTIVE_entry (REQUAL_entry R) /\
               SUBSTITUTIVE_method (REQUAL_method R)”,
    GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC[SUBSTITUTIVE]
    THEN REPEAT STRIP_TAC (* 12 subgoals *)
    THEN IMP_RES_TAC REQUAL_SUBSTITUTIVE_LEMMA
    THEN ASM_REWRITE_TAC[]
   );



val _ = export_theory();

val _ = print_theory_to_file "reduction.lst";

val _ = html_theory "reduction";

val _ = print_theory_size();
