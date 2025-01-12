open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Building the definitions of alpha equivalence for object expressions. *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "alpha";
val _ = ParseExtras.temp_loose_equality()


open prim_recTheory pairTheory pairLib listTheory;
open combinTheory;
open pred_setTheory;
open numTheory;
open arithmeticTheory;
open bossLib;
open Mutual;
open ind_rel;
open dep_rewrite;
open more_listTheory;
open more_setTheory;
open variableTheory;
open objectTheory;

open tactics;



val vars   =  ty_antiq( ==`:var list`== );
val subs1  =  ty_antiq( ==`:(var # obj1) list`== );
val dict1  =  ty_antiq( ==`:(string # method1) list`== );
val entry1 =  ty_antiq( ==`:string # method1`== );



(* --------------------------------------------------------------------- *)
(* Define semantics for objects, methods, and method dictionaries.       *)
(* --------------------------------------------------------------------- *)

(* Here is the syntax, repeated for clarity:

val _ = Hol_datatype

       (* obj1 ::= x | [li=mi] i in 1..n |  a.l | a.l:=m *)

        ` obj1  = OVAR1 of var
                | OBJ1 of (string # method1) list
                | INVOKE1 of obj1 => string
                | UPDATE1 of obj1 => string => method1 ;

       (* method ::= sigma(x)b *)

          method1 = SIGMA1 of var => obj1 ` ;

*)


(* ---------------------------------------------------------------------- *)
(* To define alpha equivalence between objects, we first need to define a *)
(* matching function, that checks if a pair of variables match according  *)
(* to a given pair of lists of variables; the lists are searched, and     *)
(* the variables must each be found at the same place.                    *)
(* ---------------------------------------------------------------------- *)

val alpha_match_def = Define
       `(alpha_match NIL ys x1 y1 = (if ys = [] then (x1 = y1) else F)) /\
        (alpha_match (CONS (x:var) xs) ys x1 y1 =
             (if ys = [] then F else
              (if x1 = x then (y1 = HD ys) /\ (LENGTH xs = LENGTH (TL ys)) else
               (if y1 = HD ys then F else
                alpha_match xs (TL ys) x1 y1))))`;

val alpha_match = store_thm
   ("alpha_match",
    “(!x1 y1. alpha_match [] [] x1 y1 = (x1 = y1)) /\
        (!ys y x1 y1. alpha_match [] (CONS y ys) x1 y1 = F) /\
        (!xs x x1 y1. alpha_match (CONS x xs) [] x1 y1 = F) /\
        (!xs ys x y x1 y1. alpha_match (CONS x xs) (CONS y ys) x1 y1 =
                           (((x1 = x) /\ (y1 = y)
                             /\ (LENGTH xs = LENGTH ys)) \/
                            (~(x1 = x) /\ ~(y1 = y)
                             /\ alpha_match xs ys x1 y1)))”,
    REWRITE_TAC[alpha_match_def]
    THEN REWRITE_TAC[NOT_CONS_NIL]
    THEN REWRITE_TAC[HD,TL]
    THEN REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THENL
      [ REWRITE_TAC[],

        COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

val alpha_match_NIL = store_thm
   ("alpha_match_NIL",
    “alpha_match [] [] = $=”,
    EXT_TAC “x:var”
    THEN GEN_TAC
    THEN EXT_TAC “y:var”
    THEN GEN_TAC
    THEN REWRITE_TAC[alpha_match]
   );

val alpha_match_REFL = store_thm
   ("alpha_match_REFL",
    “!xs x. alpha_match xs xs x x”,
    LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[alpha_match]
    THEN REWRITE_TAC[EXCLUDED_MIDDLE]
   );

val alpha_match_SYM = store_thm
   ("alpha_match_SYM",
    “!xs ys x1 y1. alpha_match xs ys x1 y1 = alpha_match ys xs y1 x1”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[alpha_match]
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN REPEAT GEN_TAC
        THEN CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[EQ_SYM_EQ]))
        THEN REFL_TAC,

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN REPEAT GEN_TAC
        THEN ASM_REWRITE_TAC[]
        THEN EQ_TAC
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

val alpha_match_TRANS = store_thm
   ("alpha_match_TRANS",
    “!xs ys zs x y z. alpha_match xs ys x y /\ alpha_match ys zs y z
                         ==> alpha_match xs zs x z”,
    LIST_INDUCT_TAC
    THENL
      [ LIST_INDUCT_TAC
        THENL
          [ LIST_INDUCT_TAC
            THEN REWRITE_TAC[alpha_match]
            THEN REWRITE_TAC[EQ_TRANS],

            REWRITE_TAC[alpha_match]
          ],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN REPEAT GEN_TAC
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN RES_TAC
      ]
   );


val alpha_match_SUB_var = store_thm
   ("alpha_match_SUB_var",
    “!xs ys x y. alpha_match xs ys x y =
                    ((LENGTH xs = LENGTH ys) /\
                     (SUB1 (xs // ys) x = OVAR1 y) /\
                     (SUB1 (ys // xs) y = OVAR1 x))”,
    LIST_INDUCT_TAC
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match,vsubst1,SUB1,object1_one_one,
                         LENGTH, GSYM NOT_SUC]
        THEN REPEAT GEN_TAC
        THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match,vsubst1,SUB1,object1_one_one,
                         LENGTH, NOT_SUC]
        THEN REPEAT GEN_TAC
        THEN ASM_REWRITE_TAC[prim_recTheory.INV_SUC_EQ]
        THEN COND_CASES_TAC  (* (x'' = x)? *)
        THENL
          [ POP_ASSUM REWRITE_THM
            THEN REWRITE_TAC[object1_one_one]
            THEN COND_CASES_TAC  (* (x' = y)? *)
            THENL
              [ POP_ASSUM REWRITE_THM,

                POP_ASSUM (REWRITE_THM o GSYM)
              ],

            FIRST_ASSUM (REWRITE_THM o GSYM)
            THEN COND_CASES_TAC  (* (x' = y)? *)
            THENL
              [ POP_ASSUM (REWRITE_THM o SYM)
                THEN REWRITE_TAC[object1_one_one]
                THEN FIRST_ASSUM (REWRITE_THM o GSYM),

                REWRITE_TAC[]
              ]
          ]
      ]
   );


val alpha_match_IDENT = store_thm
   ("alpha_match_IDENT",
    “!xs x y. alpha_match xs xs x y = (x = y)”,
    LIST_INDUCT_TAC
    THENL
      [ REWRITE_TAC[alpha_match],

        ASM_REWRITE_TAC[alpha_match]
        THEN REPEAT GEN_TAC
        THEN EQ_TAC
        THENL
          [ STRIP_TAC
            THEN ASM_REWRITE_TAC[],

            DISCH_THEN REWRITE_THM
            THEN REWRITE_TAC[EXCLUDED_MIDDLE]
          ]
      ]
   );


val alpha_match_NOT_EQ = store_thm
   ("alpha_match_NOT_EQ",
    “!xs ys x y x' y'.
         alpha_match (CONS x xs) (CONS y ys) x' y' /\ ~(x' = x)
          ==> alpha_match xs ys x' y' /\ ~(y' = y)”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[alpha_match_SUB_var]
    THEN REWRITE_TAC[LENGTH,INV_SUC_EQ,vsubst1,SUB1]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM (fn th => REWRITE_ALL_TAC[th] THEN MP_TAC th)
    THEN POP_ASSUM MP_TAC
    THEN COND_CASES_TAC
    THENL
      [ REWRITE_TAC[object1_one_one]
        THEN DISCH_THEN REWRITE_THM,

        DISCH_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


val alpha_match_pair = store_thm
   ("alpha_match_pair",
    “!xs ys x1 y1 x2 y2.
             alpha_match xs ys x1 y1 /\
             alpha_match xs ys x2 y2 ==>
               ((x1 = x2) = (y1 = y2))”,
    LIST_INDUCT_TAC
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN POP_ASSUM (fn th => ALL_TAC)
        THEN REPEAT STRIP_TAC (* 4 subgoals *)
        THEN ASM_REWRITE_TAC[]
        THEN ASSUM_LIST (EVERY o (map (REWRITE_THM o GSYM)))
        THEN RES_TAC
      ]
   );

val alpha_match_LENGTH = store_thm
   ("alpha_match_LENGTH",
    “!xs ys x y. alpha_match xs ys x y ==> (LENGTH xs = LENGTH ys)”,
    LIST_INDUCT_TAC
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN POP_TAC
        THEN REPEAT STRIP_TAC (* 2 subgoals *)
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[LENGTH]
      ]
   );



(* --------------------------------------------------------------------- *)
(* Definition of equivalence between objects.                            *)
(* --------------------------------------------------------------------- *)

val ALPHA1_obj =
“ALPHA1_obj : obj1 -> obj1 -> ^vars -> ^vars -> bool”;
val ALPHA1_dict =
“ALPHA1_dict : ^dict1 -> ^dict1 -> ^vars -> ^vars -> bool”;
val ALPHA1_entry =
“ALPHA1_entry : ^entry1 -> ^entry1 -> ^vars -> ^vars -> bool”;
val ALPHA1_method =
“ALPHA1_method : method1 -> method1 -> ^vars -> ^vars -> bool”;

val ALPHA1_patterns = [“^ALPHA1_obj o1 o2 xs ys”,
                           “^ALPHA1_dict d1 d2 xs ys”,
                           “^ALPHA1_entry e1 e2 xs ys”,
                           “^ALPHA1_method m1 m2 xs ys”
                          ];

val ALPHA1_rules_tm =
“
                      (alpha_match xs ys x y
       (* -------------------------------------------- *) ==>
             (^ALPHA1_obj (OVAR1 x) (OVAR1 y) xs ys))                       /\


                  ((^ALPHA1_dict d1 d2 xs ys)
       (* -------------------------------------------- *) ==>
             (^ALPHA1_obj (OBJ1 d1) (OBJ1 d2) xs ys))                       /\


                      ((^ALPHA1_obj o1 o2 xs ys)
       (* -------------------------------------------- *) ==>
          (^ALPHA1_obj (INVOKE1 o1 l) (INVOKE1 o2 l) xs ys))                /\


        ((^ALPHA1_obj o1 o2 xs ys) /\ (^ALPHA1_method m1 m2 xs ys)
       (* -------------------------------------------- *) ==>
        (^ALPHA1_obj (UPDATE1 o1 l m1) (UPDATE1 o2 l m2) xs ys))            /\


        ((^ALPHA1_entry e1 e2 xs ys) /\ (^ALPHA1_dict d1 d2 xs ys)
       (* -------------------------------------------- *) ==>
          (^ALPHA1_dict (CONS e1 d1) (CONS e2 d2) xs ys))                 /\


                     ((LENGTH xs = LENGTH ys)
       (* -------------------------------------------- *) ==>
                   (^ALPHA1_dict NIL NIL xs ys))                          /\


                 ((^ALPHA1_method m1 m2 xs ys)
       (* -------------------------------------------- *) ==>
              (^ALPHA1_entry (l,m1) (l,m2) xs ys))                        /\

(* Alpha conversion: *)

          ((^ALPHA1_obj o1 o2 (CONS x xs) (CONS y ys))
       (* -------------------------------------------- *) ==>
         (^ALPHA1_method (SIGMA1 x o1) (SIGMA1 y o2) xs ys))
”;

val (ALPHA1_rules_sat,ALPHA1_ind_thm) =
    define_inductive_relations ALPHA1_patterns ALPHA1_rules_tm;

val ALPHA1_inv_thms = prove_inversion_theorems
    ALPHA1_rules_sat ALPHA1_ind_thm;

val ALPHA1_strong_ind = prove_strong_induction
    ALPHA1_rules_sat ALPHA1_ind_thm;

val _ = save_thm ("ALPHA1_rules_sat", ALPHA1_rules_sat);
val _ = save_thm ("ALPHA1_ind_thm", ALPHA1_ind_thm);
val _ = save_thm ("ALPHA1_inv_thms", LIST_CONJ ALPHA1_inv_thms);
val _ = save_thm ("ALPHA1_strong_ind", ALPHA1_strong_ind);


val [ALPHA1_OVAR1, ALPHA1_OBJ1, ALPHA1_INVOKE1, ALPHA1_UPDATE1,
     ALPHA1_CONS, ALPHA1_NIL, ALPHA1_PAIR, ALPHA1_SIGMA1]
    = CONJUNCTS ALPHA1_rules_sat;



val ALPHA1_REFL = store_thm
   ("ALPHA1_REFL",
    “(!a xs. ALPHA1_obj a a xs xs) /\
        (!d xs. ALPHA1_dict d d xs xs) /\
        (!e xs. ALPHA1_entry e e xs xs) /\
        (!m xs. ALPHA1_method m m xs xs)”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REPEAT GEN_TAC
    THENL (* 8 subgoals *)
      [ MATCH_MP_TAC ALPHA1_OVAR1
        THEN REWRITE_TAC[alpha_match_REFL],

        MATCH_MP_TAC ALPHA1_OBJ1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_INVOKE1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_UPDATE1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_SIGMA1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_NIL
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_CONS
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_PAIR
        THEN ASM_REWRITE_TAC[]
      ]
   );


val ALPHA1_IMP_SYM = TAC_PROOF(([],
    “(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
                       ALPHA1_obj o2 o1 ys xs) /\
        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
                       ALPHA1_dict d2 d1 ys xs) /\
        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
                       ALPHA1_entry e2 e1 ys xs) /\
        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
                       ALPHA1_method m2 m1 ys xs)”),
    rule_induct ALPHA1_strong_ind
    THEN REPEAT STRIP_TAC
    THENL (* 8 subgoals *)
      [ MATCH_MP_TAC ALPHA1_OVAR1
        THEN IMP_RES_TAC alpha_match_SYM,

        MATCH_MP_TAC ALPHA1_OBJ1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_INVOKE1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_UPDATE1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_CONS
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_NIL
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_PAIR
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_SIGMA1
        THEN ASM_REWRITE_TAC[]
      ]
   );

val ALPHA1_SYM = store_thm
   ("ALPHA1_SYM",
    “(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys =
                       ALPHA1_obj o2 o1 ys xs) /\
        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys =
                       ALPHA1_dict d2 d1 ys xs) /\
        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys =
                       ALPHA1_entry e2 e1 ys xs) /\
        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys =
                       ALPHA1_method m2 m1 ys xs)”,
    REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_IMP_SYM
   );


val ALPHA1_TRANS1 = TAC_PROOF(([],
    “(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
               !o3 zs. ALPHA1_obj o2 o3 ys zs ==>
                       ALPHA1_obj o1 o3 xs zs) /\
        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
               !d3 zs. ALPHA1_dict d2 d3 ys zs ==>
                       ALPHA1_dict d1 d3 xs zs) /\
        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
               !e3 zs. ALPHA1_entry e2 e3 ys zs ==>
                       ALPHA1_entry e1 e3 xs zs) /\
        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
               !m3 zs. ALPHA1_method m2 m3 ys zs ==>
                       ALPHA1_method m1 m3 xs zs)”),
    rule_induct ALPHA1_strong_ind
    THEN REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ONCE_REWRITE_TAC ALPHA1_inv_thms
    THEN REWRITE_TAC[object1_one_one,object1_distinct]
    THEN REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL (* 9 subgoals *)
      [ UNDISCH_THEN“(y:var) = x'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “o3 = OVAR1 y'” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “x:var”
        THEN EXISTS_TAC “y':var”
        THEN REWRITE_TAC[]
        THEN IMP_RES_TAC alpha_match_TRANS,

        UNDISCH_THEN “(d2:^dict1) = d1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “o3 = OBJ1 d2'” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “d1:^dict1”
        THEN EXISTS_TAC “d2':^dict1”
        THEN REWRITE_TAC[]
        THEN RES_TAC,

        UNDISCH_THEN “(o2:obj1) = o1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(l:string) = l'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “o3 = INVOKE1 o2' l'” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “o1:obj1”
        THEN EXISTS_TAC “l':string”
        THEN EXISTS_TAC “o2':obj1”
        THEN REWRITE_TAC[]
        THEN RES_TAC,

        UNDISCH_THEN “(o2:obj1) = o1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(l:string) = l'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(m2:method1) = m1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “o3 = UPDATE1 o2' l' m2'” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “o1:obj1”
        THEN EXISTS_TAC “l':string”
        THEN EXISTS_TAC “m1:method1”
        THEN EXISTS_TAC “o2':obj1”
        THEN EXISTS_TAC “m2':method1”
        THEN REWRITE_TAC[]
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        UNDISCH_THEN “(e2:^entry1) = e1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(d2:^dict1) = d1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “d3 = CONS (e2':^entry1) d2'” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “e1:^entry1”
        THEN EXISTS_TAC “d1:^dict1”
        THEN EXISTS_TAC “e2':^entry1”
        THEN EXISTS_TAC “d2':^dict1”
        THEN REWRITE_TAC[]
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        ASM_REWRITE_TAC[],

        UNDISCH_THEN “(l:string) = l'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(m2:method1) = m1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(e3:^entry1) = (l',m2')” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “l':string”
        THEN EXISTS_TAC “m1:method1”
        THEN EXISTS_TAC “m2':method1”
        THEN REWRITE_TAC[]
        THEN RES_TAC,

        UNDISCH_THEN “(y:var) = x'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “(o2:obj1) = o1'” REWRITE_ALL_THM
        THEN UNDISCH_THEN “m3 = SIGMA1 y' o2'” REWRITE_ALL_THM
        THEN REWRITE_TAC[object1_one_one]
        THEN EXISTS_TAC “x:var”
        THEN EXISTS_TAC “o1:obj1”
        THEN EXISTS_TAC “y':var”
        THEN EXISTS_TAC “o2':obj1”
        THEN REWRITE_TAC[]
        THEN RES_TAC
      ]
   );


val ALPHA1_TRANS = store_thm
   ("ALPHA1_TRANS",
    “(!o1 o2 o3 xs ys zs. ALPHA1_obj o1 o2 xs ys /\
                             ALPHA1_obj o2 o3 ys zs ==>
                             ALPHA1_obj o1 o3 xs zs) /\
        (!d1 d2 d3 xs ys zs. ALPHA1_dict d1 d2 xs ys /\
                             ALPHA1_dict d2 d3 ys zs ==>
                             ALPHA1_dict d1 d3 xs zs) /\
        (!e1 e2 e3 xs ys zs. ALPHA1_entry e1 e2 xs ys /\
                             ALPHA1_entry e2 e3 ys zs ==>
                             ALPHA1_entry e1 e3 xs zs) /\
        (!m1 m2 m3 xs ys zs. ALPHA1_method m1 m2 xs ys /\
                             ALPHA1_method m2 m3 ys zs ==>
                             ALPHA1_method m1 m3 xs zs)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_TRANS1
   );


val ALPHA1_LENGTH = store_thm
   ("ALPHA1_LENGTH",
    “(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
                       (LENGTH xs = LENGTH ys)) /\
        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
                       (LENGTH xs = LENGTH ys)) /\
        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
                       (LENGTH xs = LENGTH ys)) /\
        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
                       (LENGTH xs = LENGTH ys))”,
    rule_induct ALPHA1_ind_thm
    THEN REWRITE_TAC[LENGTH,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC alpha_match_LENGTH
   );


val ALPHA1_HEIGHT = store_thm
   ("ALPHA1_HEIGHT",
    “(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
                       (HEIGHT_obj1 o1 = HEIGHT_obj1 o2)) /\
        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
                       (HEIGHT_dict1 d1 = HEIGHT_dict1 d2)) /\
        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
                       (HEIGHT_entry1 e1 = HEIGHT_entry1 e2)) /\
        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
                       (HEIGHT_method1 m1 = HEIGHT_method1 m2))”,
    rule_induct ALPHA1_ind_thm
    THEN REWRITE_TAC[HEIGHT1_def,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA1_object_similar = store_thm
   ("ALPHA1_object_similar",
    “(!x a xs ys. ALPHA1_obj (OVAR1 x) a xs ys ==> (?y. a = OVAR1 y)) /\
        (!d1 a xs ys. ALPHA1_obj (OBJ1 d1) a xs ys ==> (?d2. a = OBJ1 d2)) /\
        (!o1 l1 a xs ys. ALPHA1_obj (INVOKE1 o1 l1) a xs ys ==>
                   (?o2 l2. a = INVOKE1 o2 l2)) /\
        (!o1 l1 m1 a xs ys. ALPHA1_obj (UPDATE1 o1 l1 m1) a xs ys ==>
                      (?o2 l2 m2. a = UPDATE1 o2 l2 m2)) /\
        (!e1 d1 d xs ys. ALPHA1_dict (CONS e1 d1) d xs ys ==>
                       (?e2 d2. d = CONS e2 d2)) /\
        (!d xs ys. ALPHA1_dict NIL d xs ys ==> (d = NIL)) /\
        (!l1 m1 e xs ys. ALPHA1_entry (l1,m1) e xs ys ==>
                   (?l2 m2. e = (l2,m2))) /\
        (!x1 o1 m xs ys. ALPHA1_method (SIGMA1 x1 o1) m xs ys ==>
                   (?x2 o2. m = SIGMA1 x2 o2))”,
    PURE_ONCE_REWRITE_TAC ALPHA1_inv_thms
    THEN REWRITE_TAC[object1_one_one,object1_distinct]
    THEN REPEAT STRIP_TAC
    THENL (* 7 subgoals *)
      [ EXISTS_TAC “y:var”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “d2:^dict1”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “o2':obj1”
        THEN EXISTS_TAC “l:string”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “o2':obj1”
        THEN EXISTS_TAC “l:string”
        THEN EXISTS_TAC “m2:method1”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “e2:^entry1”
        THEN EXISTS_TAC “d2':^dict1”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “l:string”
        THEN EXISTS_TAC “m2:method1”
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “y:var”
        THEN EXISTS_TAC “o2:obj1”
        THEN ASM_REWRITE_TAC[]
      ]
   );


val ALPHA1_object_pos = store_thm
   ("ALPHA1_object_pos",
    “(!x y xs ys. ALPHA1_obj (OVAR1 x) (OVAR1 y) xs ys
                       = alpha_match xs ys x y) /\
        (!d1 d2 xs ys. ALPHA1_obj (OBJ1 d1) (OBJ1 d2) xs ys
                       = ALPHA1_dict d1 d2 xs ys) /\
        (!o1 o2 l1 l2 xs ys. ALPHA1_obj (INVOKE1 o1 l1) (INVOKE1 o2 l2) xs ys
                       = (ALPHA1_obj o1 o2 xs ys /\ (l1 = l2))) /\
        (!o1 o2 l1 l2 m1 m2 xs ys.
          ALPHA1_obj (UPDATE1 o1 l1 m1) (UPDATE1 o2 l2 m2) xs ys
                       = (ALPHA1_obj o1 o2 xs ys /\ (l1 = l2)
                          /\ ALPHA1_method m1 m2 xs ys)) /\
        (!e1 e2 d1 d2 xs ys. ALPHA1_dict (CONS e1 d1) (CONS e2 d2) xs ys
                       = (ALPHA1_entry e1 e2 xs ys
                          /\ ALPHA1_dict d1 d2 xs ys)) /\
        (ALPHA1_dict NIL NIL xs ys = (LENGTH xs = LENGTH ys)) /\
        (!l1 l2 m1 m2 xs ys. ALPHA1_entry (l1,m1) (l2,m2) xs ys
                       = ((l1 = l2) /\ ALPHA1_method m1 m2 xs ys)) /\
        (!x1 x2 o1 o2 xs ys. ALPHA1_method (SIGMA1 x1 o1) (SIGMA1 x2 o2) xs ys
                       = ALPHA1_obj o1 o2 (CONS x1 xs) (CONS x2 ys))”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN (EQ_TAC
          THENL [ DISCH_THEN (STRIP_ASSUME_TAC
                              o REWRITE_RULE[object1_one_one,object1_distinct]
                              o ONCE_REWRITE_RULE ALPHA1_inv_thms)
                  THEN ASM_REWRITE_TAC[],

                  REWRITE_TAC[]
                  THEN REPEAT STRIP_TAC
                  THEN FIRST (map (fn th => ASM_REWRITE_TAC[]
                                            THEN (MATCH_MP_TAC th
                                                  handle _ => ALL_TAC)
                                            THEN ASM_REWRITE_TAC[th]
                                            THEN NO_TAC)
                                  (CONJUNCTS ALPHA1_rules_sat))
                ])
   );


val ALPHA1_object_neg = store_thm
   ("ALPHA1_object_neg",
    “(!x d xs ys. ALPHA1_obj (OVAR1 x) (OBJ1 d) xs ys = F) /\
        (!x a l xs ys. ALPHA1_obj (OVAR1 x) (INVOKE1 a l) xs ys = F) /\
        (!x a l m xs ys. ALPHA1_obj (OVAR1 x) (UPDATE1 a l m) xs ys = F) /\
        (!d x xs ys. ALPHA1_obj (OBJ1 d) (OVAR1 x) xs ys = F) /\
        (!d a l xs ys. ALPHA1_obj (OBJ1 d) (INVOKE1 a l) xs ys = F) /\
        (!d a l m xs ys. ALPHA1_obj (OBJ1 d) (UPDATE1 a l m) xs ys = F) /\
        (!a l x xs ys. ALPHA1_obj (INVOKE1 a l) (OVAR1 x) xs ys = F) /\
        (!a l d xs ys. ALPHA1_obj (INVOKE1 a l) (OBJ1 d) xs ys = F) /\
        (!o1 l1 o2 l2 m2 xs ys.
          ALPHA1_obj (INVOKE1 o1 l1) (UPDATE1 o2 l2 m2) xs ys = F) /\
        (!a l m x xs ys. ALPHA1_obj (UPDATE1 a l m) (OVAR1 x) xs ys = F) /\
        (!a l m d xs ys. ALPHA1_obj (UPDATE1 a l m) (OBJ1 d) xs ys = F) /\
        (!o1 l1 m1 o2 l2 xs ys.
          ALPHA1_obj (UPDATE1 o1 l1 m1) (INVOKE1 o2 l2) xs ys = F)
         /\
        (!e d xs ys. ALPHA1_dict (CONS e d) NIL xs ys = F) /\
        (!e d xs ys. ALPHA1_dict NIL (CONS e d) xs ys = F)”,
    PURE_ONCE_REWRITE_TAC ALPHA1_inv_thms
    THEN REWRITE_TAC[object1_one_one,object1_distinct]
   );


(* We have no use for the following induction principle at present,
   but are keeping it in this comment in case it becomes useful later.

val ALPHA1_height_induct_LEMMA = TAC_PROOF(([],
    “!n P_0 P_1 P_2 P_3.
         (!x y xs ys.
           alpha_match xs ys x y ==> P_0 (OVAR1 x) (OVAR1 y) xs ys) /\
         (!d1 d2 xs ys.
           P_1 d1 d2 xs ys /\ ALPHA1_dict d1 d2 xs ys ==>
           P_0 (OBJ1 d1) (OBJ1 d2) xs ys) /\
         (!o1 l o2 xs ys.
           P_0 o1 o2 xs ys /\ ALPHA1_obj o1 o2 xs ys ==>
           P_0 (INVOKE1 o1 l) (INVOKE1 o2 l) xs ys) /\
         (!o1 l m1 o2 m2 xs ys.
           P_0 o1 o2 xs ys /\ ALPHA1_obj o1 o2 xs ys /\
           P_3 m1 m2 xs ys /\ ALPHA1_method m1 m2 xs ys ==>
           P_0 (UPDATE1 o1 l m1) (UPDATE1 o2 l m2) xs ys) /\
         (!e1 d1 e2 d2 xs ys.
           P_2 e1 e2 xs ys /\ ALPHA1_entry e1 e2 xs ys /\
           P_1 d1 d2 xs ys /\ ALPHA1_dict d1 d2 xs ys ==>
           P_1 (CONS e1 d1) (CONS e2 d2) xs ys) /\
         (!xs ys. (LENGTH xs = LENGTH ys) ==> P_1 [] [] xs ys) /\
         (!l m1 m2 xs ys.
           P_3 m1 m2 xs ys /\ ALPHA1_method m1 m2 xs ys ==>
           P_2 (l,m1) (l,m2) xs ys) /\
         (!x o1 y o2 xs ys.
           (!o' o''. ALPHA1_obj o' o'' (CONS x xs) (CONS y ys) /\
                     (HEIGHT_obj1 o1 = HEIGHT_obj1 o') /\
                     (HEIGHT_obj1 o2 = HEIGHT_obj1 o'') ==>
                     P_0 o' o'' (CONS x xs) (CONS y ys)) /\
           ALPHA1_obj o1 o2 (CONS x xs) (CONS y ys) ==>
           P_3 (SIGMA1 x o1) (SIGMA1 y o2) xs ys) ==>
         (!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
                        ((HEIGHT_obj1 o1 <= n) /\
                         (HEIGHT_obj1 o2 <= n) ==>
                         P_0 o1 o2 xs ys)) /\
         (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
                        ((HEIGHT_dict1 d1 <= n) /\
                         (HEIGHT_dict1 d2 <= n) ==>
                         P_1 d1 d2 xs ys)) /\
         (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
                        ((HEIGHT_entry1 e1 <= n) /\
                         (HEIGHT_entry1 e2 <= n) ==>
                         P_2 e1 e2 xs ys)) /\
         (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
                        ((HEIGHT_method1 m1 <= n) /\
                         (HEIGHT_method1 m2 <= n) ==>
                         P_3 m1 m2 xs ys))”),
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO1]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THENL
          [ UNDISCH_TAC “ALPHA1_obj o1 o2 xs ys”
            THEN ASM_REWRITE_TAC[ALPHA1_object_pos],

            IMP_RES_TAC ALPHA1_LENGTH
          ],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN rule_induct ALPHA1_strong_ind
        THEN REWRITE_TAC[HEIGHT1_def]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 8 subgoals *)
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
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[],

            FIRST_ASSUM MATCH_MP_TAC
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
            THEN FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO])
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );


val ALPHA1_height_induct = store_thm
   ("ALPHA1_height_induct",
    “!P_0 P_1 P_2 P_3.
         (!x y xs ys.
           alpha_match xs ys x y ==> P_0 (OVAR1 x) (OVAR1 y) xs ys) /\
         (!d1 d2 xs ys.
           P_1 d1 d2 xs ys /\ ALPHA1_dict d1 d2 xs ys ==>
           P_0 (OBJ1 d1) (OBJ1 d2) xs ys) /\
         (!o1 l o2 xs ys.
           P_0 o1 o2 xs ys /\ ALPHA1_obj o1 o2 xs ys ==>
           P_0 (INVOKE1 o1 l) (INVOKE1 o2 l) xs ys) /\
         (!o1 l m1 o2 m2 xs ys.
           P_0 o1 o2 xs ys /\ ALPHA1_obj o1 o2 xs ys /\
           P_3 m1 m2 xs ys /\ ALPHA1_method m1 m2 xs ys ==>
           P_0 (UPDATE1 o1 l m1) (UPDATE1 o2 l m2) xs ys) /\
         (!e1 d1 e2 d2 xs ys.
           P_2 e1 e2 xs ys /\ ALPHA1_entry e1 e2 xs ys /\
           P_1 d1 d2 xs ys /\ ALPHA1_dict d1 d2 xs ys ==>
           P_1 (CONS e1 d1) (CONS e2 d2) xs ys) /\
         (!xs ys. (LENGTH xs = LENGTH ys) ==> P_1 [] [] xs ys) /\
         (!l m1 m2 xs ys.
           P_3 m1 m2 xs ys /\ ALPHA1_method m1 m2 xs ys ==>
           P_2 (l,m1) (l,m2) xs ys) /\
         (!x o1 y o2 xs ys.
           (!o' o''. ALPHA1_obj o' o'' (CONS x xs) (CONS y ys) /\
                     (HEIGHT_obj1 o1 = HEIGHT_obj1 o') /\
                     (HEIGHT_obj1 o2 = HEIGHT_obj1 o'') ==>
                     P_0 o' o'' (CONS x xs) (CONS y ys)) /\
           ALPHA1_obj o1 o2 (CONS x xs) (CONS y ys) ==>
           P_3 (SIGMA1 x o1) (SIGMA1 y o2) xs ys) ==>
         (!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==> P_0 o1 o2 xs ys) /\
         (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==> P_1 d1 d2 xs ys) /\
         (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==> P_2 e1 e2 xs ys) /\
         (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==> P_3 m1 m2 xs ys)”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL (SPEC tm ALPHA1_height_induct_LEMMA)))
           [“(HEIGHT_obj1 o1) MAX (HEIGHT_obj1 o2)”,
            “(HEIGHT_dict1 d1) MAX (HEIGHT_dict1 d2)”,
            “(HEIGHT_entry1 e1) MAX (HEIGHT_entry1 e2)”,
            “(HEIGHT_method1 m1) MAX (HEIGHT_method1 m2)”])
    THEN ASM_REWRITE_TAC[AND_IMP_INTRO]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_MAX]
   );

(* Unfortunately, this induction principle is not that useful yet, because *)
(* we do not yet have the ability to shift the bound variable of a SIGMA1. *)


fun INSTANTIATE_TAC th (asm,gl) =
    let val {Bvar=x, Body=glb} = Rsyntax.dest_forall gl
    in
      (X_GEN_TAC x
       THEN STRIP_ASSUME_TAC (SPEC x th)
       (* If disjuncts in th, multiple subgoals here *)
       THEN POP_ASSUM REWRITE_ALL_THM
       THEN REWRITE_TAC[ALPHA1_object_pos,ALPHA1_object_neg]) (asm,gl)
    end;

fun FIND_INSTANTIATION th (asm,gl) =
    (FIRST (map INSTANTIATE_TAC (CONJUNCTS th))
     ORELSE (GEN_TAC THEN FIND_INSTANTIATION th)) (asm,gl);
*)


val ALPHA1_FV = store_thm
   ("ALPHA1_FV",
    (“(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
         (!x. x IN FV_obj1 o1 ==>
              (?y. y IN FV_obj1 o2 /\ alpha_match xs ys x y))) /\

        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
         (!x. x IN FV_dict1 d1 ==>
              (?y. y IN FV_dict1 d2 /\ alpha_match xs ys x y))) /\

        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
         (!x. x IN FV_entry1 e1 ==>
              (?y. y IN FV_entry1 e2 /\ alpha_match xs ys x y))) /\

        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
         (!x. x IN FV_method1 m1 ==>
              (?y. y IN FV_method1 m2 /\ alpha_match xs ys x y)))”),

    rule_induct ALPHA1_strong_ind
    THEN REWRITE_TAC[FV_object1_def]
    THEN REWRITE_TAC[IN_INSERT,NOT_IN_EMPTY,IN_UNION,IN_DIFF]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN TRY (EXISTS_TAC “y:var”
              THEN ASM_REWRITE_TAC[]
              THEN NO_TAC)
    (* only one goal here *)
    THEN EXISTS_TAC “y':var”
    THEN IMP_RES_TAC alpha_match_NOT_EQ
    THEN ASM_REWRITE_TAC[]
   );
(* Glory to God!  Soli Deo Gloria! *)



val FORALL_OR_IMP = TAC_PROOF(([],
    “!s t (f:'a->'b) g.
        (!x. x IN s \/ x IN t ==> (f x = g x)) ==>
        ((!x. x IN s ==> (f x = g x)) /\
         (!x. x IN t ==> (f x = g x)))”),
    PROVE_TAC []
   );


val ALPHA1_FREE_CONTEXT = store_thm
   ("ALPHA1_FREE_CONTEXT",
    “(!o1 o2 xs ys xs' ys'.
          ((LENGTH xs = LENGTH ys) = (LENGTH xs' = LENGTH ys')) /\
          (!x. (x IN FV_obj1 o1) ==>
               (SUB1 (xs // ys) x = SUB1 (xs' // ys') x)) /\
          (!y. (y IN FV_obj1 o2) ==>
               (SUB1 (ys // xs) y = SUB1 (ys' // xs') y))  ==>
          (ALPHA1_obj o1 o2 xs ys = ALPHA1_obj o1 o2 xs' ys')) /\
        (!d1 d2 xs ys xs' ys'.
          ((LENGTH xs = LENGTH ys) = (LENGTH xs' = LENGTH ys')) /\
          (!x. (x IN FV_dict1 d1) ==>
               (SUB1 (xs // ys) x = SUB1 (xs' // ys') x)) /\
          (!y. (y IN FV_dict1 d2) ==>
               (SUB1 (ys // xs) y = SUB1 (ys' // xs') y))  ==>
          (ALPHA1_dict d1 d2 xs ys = ALPHA1_dict d1 d2 xs' ys')) /\
        (!e1 e2 xs ys xs' ys'.
          ((LENGTH xs = LENGTH ys) = (LENGTH xs' = LENGTH ys')) /\
          (!x. (x IN FV_entry1 e1) ==>
               (SUB1 (xs // ys) x = SUB1 (xs' // ys') x)) /\
          (!y. (y IN FV_entry1 e2) ==>
               (SUB1 (ys // xs) y = SUB1 (ys' // xs') y))  ==>
          (ALPHA1_entry e1 e2 xs ys = ALPHA1_entry e1 e2 xs' ys')) /\
        (!m1 m2 xs ys xs' ys'.
          ((LENGTH xs = LENGTH ys) = (LENGTH xs' = LENGTH ys')) /\
          (!x. (x IN FV_method1 m1) ==>
               (SUB1 (xs // ys) x = SUB1 (xs' // ys') x)) /\
          (!y. (y IN FV_method1 m2) ==>
               (SUB1 (ys // xs) y = SUB1 (ys' // xs') y))  ==>
          (ALPHA1_method m1 m2 xs ys = ALPHA1_method m1 m2 xs' ys'))”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_object_similar
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN REWRITE_ALL_TAC[FV_object1_def,IN_DIFF,IN_UNION,IN]
    THEN UNDISCH_LAST_TAC
    THEN REWRITE_TAC[ALPHA1_object_pos]
    THENL
      [
        REWRITE_TAC[alpha_match_SUB_var]
        THEN POP_ASSUM (MP_TAC o SPEC “y:var”)
        THEN POP_ASSUM (MP_TAC o SPEC “v:var”)
        THEN REWRITE_TAC[]
        THEN DISCH_TAC
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        REWRITE_TAC[alpha_match_SUB_var]
        THEN POP_ASSUM (MP_TAC o SPEC “y:var”)
        THEN POP_ASSUM (MP_TAC o SPEC “v:var”)
        THEN REWRITE_TAC[]
        THEN DISCH_TAC
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        DISCH_TAC
        THEN RES_TAC,

        DISCH_TAC
        THEN RES_TAC,

        STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN RES_TAC,

        STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN RES_TAC,

        IMP_RES_TAC FORALL_OR_IMP
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC FORALL_OR_IMP
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        FIRST_ASSUM (fn th =>
         DEP_REWRITE_TAC[
           SPECL [“o2:obj1”,“CONS (v:var) xs”,“CONS (x2:var) ys”,
                  “CONS (v:var) xs'”,“CONS (x2:var) ys'”]
                 th])
        THEN ASM_REWRITE_TAC[LENGTH,INV_SUC_EQ]
        THEN CONJ_TAC
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN FIRST_ASSUM (REWRITE_THM o GSYM)
        THEN ASM_REWRITE_TAC[],

        FIRST_ASSUM (fn th =>
         DEP_ONCE_REWRITE_TAC[
           SPECL [“o2:obj1”,“CONS (v:var) xs'”,“CONS (x2:var) ys'”,
                  “CONS (v:var) xs”,“CONS (x2:var) ys”]
                 th])
        THEN ASM_REWRITE_TAC[LENGTH,INV_SUC_EQ]
        THEN CONJ_TAC
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        POP_TAC
        THEN POP_TAC
        THEN ASM_REWRITE_TAC[],

        POP_TAC
        THEN POP_TAC
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC FORALL_OR_IMP
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        IMP_RES_TAC FORALL_OR_IMP
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN RES_TAC,

        STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN RES_TAC
      ]
   );


val ALPHA1_EXTRANEOUS_CONTEXT = store_thm
   ("ALPHA1_EXTRANEOUS_CONTEXT",
    “(!o1 o2 xs ys x y.
          ~(x IN FV_obj1 o1) /\ ~(y IN FV_obj1 o2) ==>
          (ALPHA1_obj o1 o2 (CONS x xs) (CONS y ys) =
           ALPHA1_obj o1 o2 xs ys)) /\
        (!d1 d2 xs ys x y.
          ~(x IN FV_dict1 d1) /\ ~(y IN FV_dict1 d2) ==>
          (ALPHA1_dict d1 d2 (CONS x xs) (CONS y ys) =
           ALPHA1_dict d1 d2 xs ys)) /\
        (!e1 e2 xs ys x y.
          ~(x IN FV_entry1 e1) /\ ~(y IN FV_entry1 e2) ==>
          (ALPHA1_entry e1 e2 (CONS x xs) (CONS y ys) =
           ALPHA1_entry e1 e2 xs ys)) /\
        (!m1 m2 xs ys x y.
          ~(x IN FV_method1 m1) /\ ~(y IN FV_method1 m2) ==>
          (ALPHA1_method m1 m2 (CONS x xs) (CONS y ys) =
           ALPHA1_method m1 m2 xs ys))”,
    REPEAT STRIP_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA1_FREE_CONTEXT))
    THEN REWRITE_TAC[LENGTH,INV_SUC_EQ]
    THEN CONJ_TAC
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[vsubst1,SUB1]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN RES_TAC
   );

val [ALPHA1_EXTRANEOUS_CONTEXT_obj, ALPHA1_EXTRANEOUS_CONTEXT_dict1,
     ALPHA1_EXTRANEOUS_CONTEXT_entry1, ALPHA1_EXTRANEOUS_CONTEXT_method1] =
    CONJUNCTS ALPHA1_EXTRANEOUS_CONTEXT;



(* ---------------------------------------------------------------------- *)
(* Now we prepare to prove ALPHA1_SUB, the key and most important theorem *)
(* of this theory.  It is difficult, but critical.                        *)
(* ---------------------------------------------------------------------- *)


(* define ALPHA1_subst *)

val ALPHA1_subst =
    new_definition
    ("ALPHA1_subst",
     “ALPHA1_subst xs ys xs' ys' t1 t2 s1 s2 =
        (LENGTH xs' = LENGTH ys') /\
        (!x y. (x IN t1) /\ (y IN t2) /\
               alpha_match xs ys x y ==>
               ALPHA1_obj (SUB1 s1 x) (SUB1 s2 y) xs' ys')”);


val ALPHA1_subst_UNION = store_thm
   ("ALPHA1_subst_UNION",
    “!xs ys xs' ys' t11 t12 t21 t22 s1 s2.
         ALPHA1_subst xs ys xs' ys' (t11 UNION t12) (t21 UNION t22) s1 s2
         ==>
         (ALPHA1_subst xs ys xs' ys' t11 t21 s1 s2  /\
          ALPHA1_subst xs ys xs' ys' t12 t22 s1 s2)”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[ALPHA1_subst]
    THEN REWRITE_TAC[IN_UNION]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val ALPHA1_subst_LENGTH = store_thm
   ("ALPHA1_subst_LENGTH",
    “!xs ys xs' ys' t1 t2 s1 s2.
         ALPHA1_subst xs ys xs' ys' t1 t2 s1 s2
         ==>
         (LENGTH xs' = LENGTH ys')”,
    REWRITE_TAC[ALPHA1_subst]
    THEN REPEAT STRIP_TAC
   );



val variant_not_in_sub = store_thm
   ("variant_not_in_sub",
    “!v v' s t x.
         FINITE t /\ (x IN t) /\
         (v' = variant v (FV_subst1 s t))
         ==>
         ~(v' IN FV_obj1 (SUB1 s x))”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN MP_TAC (SPECL [“v:var”,“FV_subst1 s t”] variant_not_in_set)
    THEN IMP_RES_THEN REWRITE_THM FINITE_FV_subst1
    THEN FIRST_ASSUM (REWRITE_THM o SYM)
    THEN REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,combinTheory.o_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN DISCH_THEN (MP_TAC o SPEC “FV_obj1 (SUB1 s x)”)
    THEN STRIP_TAC
    THEN POP_ASSUM (MP_TAC o SPEC “x:var”)
    THEN ASM_REWRITE_TAC[]
   );



val ALPHA1_SUB = store_thm
   ("ALPHA1_SUB",
    “(!o1 o2 xs ys. ALPHA1_obj o1 o2 xs ys ==>
          (!xs' ys' s1 s2.
            ALPHA1_subst xs ys xs' ys' (FV_obj1 o1) (FV_obj1 o2) s1 s2 ==>
            ALPHA1_obj (o1 <[ s1) (o2 <[ s2) xs' ys')) /\
        (!d1 d2 xs ys. ALPHA1_dict d1 d2 xs ys ==>
          (!xs' ys' s1 s2.
            ALPHA1_subst xs ys xs' ys' (FV_dict1 d1) (FV_dict1 d2) s1 s2 ==>
            ALPHA1_dict (d1 <[ s1) (d2 <[ s2) xs' ys')) /\
        (!e1 e2 xs ys. ALPHA1_entry e1 e2 xs ys ==>
          (!xs' ys' s1 s2.
            ALPHA1_subst xs ys xs' ys' (FV_entry1 e1) (FV_entry1 e2) s1 s2 ==>
            ALPHA1_entry (e1 <[ s1) (e2 <[ s2) xs' ys')) /\
        (!m1 m2 xs ys. ALPHA1_method m1 m2 xs ys ==>
          (!xs' ys' s1 s2.
            ALPHA1_subst xs ys xs' ys' (FV_method1 m1) (FV_method1 m2) s1 s2 ==>
            ALPHA1_method (m1 <[ s1) (m2 <[ s2) xs' ys'))”,
    rule_induct ALPHA1_strong_ind
    THEN REWRITE_TAC[FV_object1_def]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_object1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[ALPHA1_object_pos]
    THEN IMP_RES_TAC ALPHA1_subst_UNION
    THEN IMP_RES_TAC ALPHA1_subst_LENGTH
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    (* two subgoals left: *)
    THENL
      [ UNDISCH_LAST_TAC
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[ALPHA1_subst]
        THEN REWRITE_TAC[IN]
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        POP_TAC
        THEN UNDISCH_LAST_TAC
        THEN DEFINE_NEW_VAR
             “x' = variant x (FV_subst1 s1 (FV_obj1 o1 DIFF {x}))”
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN DEFINE_NEW_VAR
             “y' = variant y (FV_subst1 s2 (FV_obj1 o2 DIFF {y}))”
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN DISCH_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[ALPHA1_subst]
        THEN STRIP_TAC
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[LENGTH]
        THEN FIRST_ASSUM REWRITE_THM
        THEN DISCH_TAC
        THEN REPEAT GEN_TAC
        THEN REWRITE_TAC[alpha_match]
        THEN REWRITE_TAC[SUB1]
        THEN COND_CASES_TAC
        THENL
          [ POP_ASSUM REWRITE_THM
            THEN COND_CASES_TAC
            THEN FIRST_ASSUM REWRITE_THM
            THEN POP_TAC
            THEN STRIP_TAC
            THEN REWRITE_TAC[ALPHA1_object_pos]
            THEN REWRITE_TAC[alpha_match]
            THEN FIRST_ASSUM ACCEPT_TAC,

            COND_CASES_TAC
            THEN FIRST_ASSUM REWRITE_THM
            THEN STRIP_TAC
            (* Here the extra x', y' are extraneous *)
            THEN DEP_REWRITE_TAC[ALPHA1_EXTRANEOUS_CONTEXT_obj]
            THEN FIRST_ASSUM (MP_TAC o SPECL[“x'':var”,“y'':var”])
            THEN REWRITE_TAC[IN_DIFF,IN]
            THEN DISCH_THEN IMP_RES_TAC
            THEN FIRST_ASSUM REWRITE_THM
            THEN CONJ_TAC
            THEN MATCH_MP_TAC variant_not_in_sub
            THENL
              [ EXISTS_TAC “x:var”
                THEN EXISTS_TAC “FV_obj1 o1 DIFF {x}”
                THEN ASM_REWRITE_TAC[IN_DIFF,IN]
                THEN MATCH_MP_TAC FINITE_DIFF
                THEN REWRITE_TAC[FINITE_FV_object1],

                EXISTS_TAC “y:var”
                THEN EXISTS_TAC “FV_obj1 o2 DIFF {y}”
                THEN ASM_REWRITE_TAC[IN_DIFF,IN]
                THEN MATCH_MP_TAC FINITE_DIFF
                THEN REWRITE_TAC[FINITE_FV_object1]
              ]
          ]
      ]
   );
(* Soli Deo Gloria!!! *)




val ALPHA1_CHANGE_VAR = store_thm
   ("ALPHA1_CHANGE_VAR",
    “!y x s v a.
         ~(x IN FV_subst1 s (FV_obj1 a DIFF {v})) /\
         ~(y IN FV_subst1 s (FV_obj1 a DIFF {v})) ==>
         ALPHA1_obj
             (a <[ CONS (v, OVAR1 x) s)
             (a <[ CONS (v, OVAR1 y) s)
             [x] [y]”,
    REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM,IN_DIFF,IN]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC (REWRITE_RULE[AND_IMP_INTRO]
                       (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
                        (CONJUNCT1 ALPHA1_SUB)))
    THEN EXISTS_TAC “[]:var list”
    THEN EXISTS_TAC “[]:var list”
    THEN REWRITE_TAC[ALPHA1_REFL]
    THEN REWRITE_TAC[ALPHA1_subst]
    THEN REWRITE_TAC[LENGTH]
    THEN REWRITE_TAC[alpha_match]
    THEN REWRITE_TAC[SUB1]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN POP_ASSUM (REWRITE_ALL_THM o SYM)
    THEN POP_TAC
    THEN UNDISCH_LAST_TAC
    THEN UNDISCH_LAST_TAC
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC “FV_obj1 (SUB1 s x')”)
    THENL
      [ POP_ASSUM (STRIP_ASSUME_TAC o SPEC “x':var”)
        THENL (* 3 subgoals *)
          [ UNDISCH_LAST_TAC
            THEN REWRITE_TAC[],

            REPEAT STRIP_TAC
            THEN RES_TAC,

            POP_ASSUM (REWRITE_THM o SYM)
            THEN REPEAT STRIP_TAC
            THEN POP_ASSUM REWRITE_THM
            THEN REWRITE_TAC[ALPHA1_object_pos,alpha_match]
          ],

        DISCH_THEN (STRIP_ASSUME_TAC o SPEC “FV_obj1 (SUB1 s x')”)
        THENL
          [ POP_ASSUM (STRIP_ASSUME_TAC o SPEC “x':var”)
            THENL (* 3 subgoals *)
              [ UNDISCH_LAST_TAC
                THEN REWRITE_TAC[],

                REPEAT STRIP_TAC
                THEN RES_TAC,

                POP_ASSUM REWRITE_THM
                THEN REPEAT STRIP_TAC
                THEN POP_ASSUM REWRITE_THM
                THEN REWRITE_TAC[ALPHA1_object_pos,alpha_match]
              ],

            STRIP_TAC
            THEN COND_CASES_TAC
            THENL
              [ REWRITE_TAC[ALPHA1_object_pos,alpha_match],

                REWRITE_TAC[]
                THEN DEP_REWRITE_TAC[CONJUNCT1 ALPHA1_EXTRANEOUS_CONTEXT]
                THEN ASM_REWRITE_TAC[ALPHA1_REFL]
              ]
          ]
      ]
   );



val obj_SUB_distinct = store_thm
   ("obj_SUB_distinct",
    “(!d xs ys x. ~(OBJ1 d = SUB1 (xs // ys) x)) /\
        (!o' l xs ys x. ~(INVOKE1 o' l = SUB1 (xs // ys) x)) /\
        (!o' l m xs ys x. ~(UPDATE1 o' l m = SUB1 (xs // ys) x)) /\
        (!d xs ys x. ~(SUB1 (xs // ys) x = OBJ1 d)) /\
        (!o' l xs ys x. ~(SUB1 (xs // ys) x = INVOKE1 o' l)) /\
        (!o' l m xs ys x. ~(SUB1 (xs // ys) x = UPDATE1 o' l m))”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC_ALL SUB_vsubst_OVAR1)
    THEN ASM_REWRITE_TAC[object1_distinct]
   );


val FREE_SUBST = store_thm
   ("FREE_SUBST",
    “(!a s.
          DISJOINT (FV_obj1 a) (BV_subst s) ==> ((a <[ s) = a)) /\
        (!d s.
          DISJOINT (FV_dict1 d) (BV_subst s) ==> ((d <[ s) = d)) /\
        (!e s.
          DISJOINT (FV_entry1 e) (BV_subst s) ==> ((e <[ s) = e)) /\
        (!m s.
          DISJOINT (FV_method1 m) (BV_subst s) ==> ((m <[ s) = m))”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REWRITE_TAC[FV_object1_def,SUB_object1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[DISJOINT_UNION,object1_one_one]
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THENL
      [ IMP_RES_TAC FREE_SUB1
        THEN POP_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[IN],

        IMP_RES_TAC FREE_IDENT_SUBST1
        THEN POP_ASSUM REWRITE_THM
        THEN MATCH_MP_TAC variant_ident
        THEN REWRITE_TAC[IN_DIFF,IN]
        THEN MATCH_MP_TAC FINITE_DIFF
        THEN REWRITE_TAC[FINITE_FV_object1],

        IMP_RES_TAC FREE_IDENT_SUBST1
        THEN POP_ASSUM REWRITE_THM
        THEN DEP_REWRITE_TAC[variant_ident]
        THEN DEP_REWRITE_TAC[FINITE_DIFF]
        THEN REWRITE_TAC[FINITE_FV_object1,IN_DIFF,IN]
        THEN MATCH_MP_TAC (CONJUNCT1 subst_IDENT1)
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN REWRITE_TAC[SUB1]
        THEN COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[],

            IMP_RES_TAC FREE_SUB1
            THEN POP_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[IN_DIFF,IN]
            THEN FIRST_ASSUM (REWRITE_THM o GSYM)
          ]
      ]
   );


val BLOCKED_SUBST = store_thm
   ("BLOCKED_SUBST",
    “!o' x o1.
          (SIGMA1 x o' <[ [x,o1]) = SIGMA1 x o'”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SUB_object1_def]
    THEN DEP_REWRITE_TAC[variant_ident]
    THEN DEP_REWRITE_TAC[FINITE_FV_subst1]
    THEN DEP_REWRITE_TAC[FINITE_DIFF]
    THEN REWRITE_TAC[FINITE_FV_object1]
    THEN DEP_REWRITE_TAC[FV_subst_IDENT1]
    THEN REWRITE_TAC[IN_DIFF,IN]
    THEN CONJ_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN FIRST_ASSUM REWRITE_THM,

        CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[object1_one_one]
        THEN DEP_REWRITE_TAC[subst_IDENT1]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


val PARTIALLY_BLOCKED_SUBST = store_thm
   ("PARTIALLY_BLOCKED_SUBST",
    “!xs ys x y o'.
         (LENGTH xs = LENGTH ys) ==>
         (SIGMA1 x o' <[ (APPEND xs [x] // APPEND ys [y]) =
          SIGMA1 x o' <[ (xs // ys))”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC (hd (rev (CONJUNCTS subst_EQ1)))
    THEN REWRITE_TAC[FV_object1_def,IN_DIFF,IN]
    THEN REPEAT STRIP_TAC
    THEN DEP_REWRITE_TAC[SUB_APPEND_vsubst1]
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THENL
      [ REFL_TAC,

        REWRITE_TAC[vsubst1,SUB1]
        THEN EVERY_ASSUM (REWRITE_THM o GSYM)
        THEN DEP_REWRITE_TAC[SUB_FREE_vsubst1]
        THEN ASM_REWRITE_TAC[]
      ]
   );


(* THe following two theorems are unnecessary.

val ALPHA1_DUPLICATE_CONTEXT = store_thm
   ("ALPHA1_DUPLICATE_CONTEXT",
    “(!o1 o2 x y xs ys.
          ALPHA1_obj o1 o2 (CONS x (CONS x xs)) (CONS y (CONS y ys)) =
          ALPHA1_obj o1 o2 (CONS x xs) (CONS y ys)) /\
        (!d1 d2 x y xs ys.
          ALPHA1_dict d1 d2 (CONS x (CONS x xs)) (CONS y (CONS y ys)) =
          ALPHA1_dict d1 d2 (CONS x xs) (CONS y ys)) /\
        (!e1 e2 x y xs ys.
          ALPHA1_entry e1 e2 (CONS x (CONS x xs)) (CONS y (CONS y ys)) =
          ALPHA1_entry e1 e2 (CONS x xs) (CONS y ys)) /\
        (!m1 m2 x y xs ys.
          ALPHA1_method m1 m2 (CONS x (CONS x xs)) (CONS y (CONS y ys)) =
          ALPHA1_method m1 m2 (CONS x xs) (CONS y ys))”,
    REPEAT STRIP_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS ALPHA1_FREE_CONTEXT))
    THEN REWRITE_TAC[LENGTH,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[vsubst1,SUB1]
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[]
   );


val ALPHA1_INNOCUOUS_SUBST = store_thm
   ("ALPHA1_INNOCUOUS_SUBST",
    “(!o' x y xs ys.
          ~(x IN SL ys) /\
          ALPHA1_obj (o' <[ (APPEND ys [x] // APPEND xs [y])) o' xs ys ==>
          ((x = y) \/ ~(x IN FV_obj1 o'))) /\
        (!d x y xs ys.
          ~(x IN SL ys) /\
          ALPHA1_dict (d <[ (APPEND ys [x] // APPEND xs [y])) d xs ys ==>
          ((x = y) \/ ~(x IN FV_dict1 d))) /\
        (!e x y xs ys.
          ~(x IN SL ys) /\
          ALPHA1_entry (e <[ (APPEND ys [x] // APPEND xs [y])) e xs ys ==>
          ((x = y) \/ ~(x IN FV_entry1 e))) /\
        (!m x y xs ys.
          ~(x IN SL ys) /\
          ALPHA1_method (m <[ (APPEND ys [x] // APPEND xs [y])) m xs ys ==>
          ((x = y) \/ ~(x IN FV_method1 m)))”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REWRITE_TAC[SUB_object1_def,FV_object1_def,IN_UNION,IN]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[ALPHA1_object_pos]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THENL
      [ ASM_CASES_TAC “(x:var) = v”
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_ALL_THM o SYM)
        THEN IMP_RES_TAC ALPHA1_LENGTH
        THEN POP_ASSUM (fn th1 =>
                POP_ASSUM (fn th2 =>
                   ASSUME_TAC th1 THEN MP_TAC th2))
        THEN DEP_REWRITE_TAC[SUB_APPEND_FREE_vsubst1]
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[SUB1,vsubst1]
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN REWRITE_TAC[alpha_match_SUB_var]
        THEN STRIP_TAC
        THEN UNDISCH_LAST_TAC
        THEN DEP_REWRITE_TAC[SUB_FREE_vsubst1]
        THEN ASM_REWRITE_TAC[object1_one_one],

        POP_TAC
        THEN UNDISCH_LAST_TAC
        THEN DEFINE_NEW_VAR
                “v' = variant v (FV_subst1 (APPEND ys [x] // APPEND xs [y])
                                             (FV_obj1 o' DIFF {v}))”
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN DISCH_TAC
        THEN ASM_CASES_TAC “(x:var) = v”
        THENL
          [ POP_ASSUM REWRITE_THM
            THEN REWRITE_TAC[IN_DIFF,IN],

            FIRST_ASSUM (MP_TAC o
                REWRITE_RULE[SUB1] o
                SPECL[“x:var”,“y:var”,
                      “CONS (v':var) xs”,“CONS (v:var) ys”])
            THEN REWRITE_TAC[SL,IN]
            THEN FIRST_ASSUM REWRITE_THM
            THEN UNDISCH_ALL_TAC
            THEN DISCH_TAC
            THEN POP_TAC
            THEN DISCH_TAC
            THEN DISCH_TAC
            THEN REWRITE_TAC[APPEND,vsubst1]
            THEN DISCH_THEN REWRITE_THM
            THEN REWRITE_TAC[IN_DIFF,IN,DE_MORGAN_THM]
            THEN DISCH_THEN ASM_REWRITE_THM
          ]
      ]
   );

*)



val ALPHA1_SWITCH_OVAR1 = TAC_PROOF(([],
    “!xs xs' ys ys' x y u v.
          (LENGTH xs = LENGTH xs') /\
          (LENGTH xs' = LENGTH ys) /\
          (LENGTH ys = LENGTH ys') /\
          ALPHA1_obj (SUB1 (APPEND xs [x] // APPEND xs' [y]) u)
                     (OVAR1 v) xs' ys /\
          ALPHA1_obj (OVAR1 u)
                     (SUB1 (APPEND ys [y] // APPEND ys' [x]) v) xs ys'
             ==>
          ALPHA1_obj (OVAR1 u) (OVAR1 v) (APPEND xs [x]) (APPEND ys [y])”),
    LIST_INDUCT_TAC
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,SUC_NOT]
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,SUC_NOT]
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,SUC_NOT]
        THEN REWRITE_TAC[APPEND,vsubst1,SUB1]
        THEN REPEAT GEN_TAC
        THEN COND_CASES_TAC
        THEN COND_CASES_TAC
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN REWRITE_TAC[alpha_match_SUB_var]
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN ASM_REWRITE_TAC[object1_one_one,LENGTH],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,NOT_SUC]
        THEN POP_TAC
        THEN GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,NOT_SUC]
        THEN POP_TAC
        THEN GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,NOT_SUC]
        THEN POP_TAC
        THEN X_GEN_TAC “x1:var”
        THEN X_GEN_TAC “x2:var”
        THEN REPEAT GEN_TAC
        THEN REWRITE_TAC[INV_SUC_EQ]
        THEN STRIP_TAC
        THEN UNDISCH_LAST_TAC
        THEN UNDISCH_LAST_TAC
        THEN REWRITE_TAC[APPEND,vsubst1,SUB1]
        THEN COND_CASES_TAC
        THEN POP_ASSUM (ASSUME_TAC o GSYM)
        THEN COND_CASES_TAC
        THEN POP_ASSUM (ASSUME_TAC o GSYM)
        THENL (* 4 subgoals *)
          [ REWRITE_TAC[ALPHA1_object_pos]
            THEN REWRITE_TAC[alpha_match_SUB_var]
            THEN ASM_REWRITE_TAC[LENGTH,LENGTH_APPEND,vsubst1,SUB1],

            REWRITE_TAC[ALPHA1_object_pos]
            THEN REWRITE_TAC[alpha_match_SUB_var]
            THEN REWRITE_TAC[vsubst1,SUB1]
            THEN ASM_REWRITE_TAC[object1_one_one],

            REWRITE_TAC[ALPHA1_object_pos]
            THEN REWRITE_TAC[alpha_match_SUB_var]
            THEN REWRITE_TAC[vsubst1,SUB1]
            THEN ASM_REWRITE_TAC[object1_one_one],

            ASM_CASES_TAC
                  “SUB1 (APPEND xs [x2] // APPEND xs' [y]) u = OVAR1 x'”
            THEN TRY (POP_ASSUM REWRITE_THM
                      THEN REWRITE_TAC[ALPHA1_object_pos]
                      THEN REWRITE_TAC[alpha_match_SUB_var]
                      THEN REWRITE_TAC[vsubst1,SUB1]
                      THEN ASM_REWRITE_TAC[object1_one_one]
                      THEN NO_TAC)
            THEN ASM_CASES_TAC
                  “SUB1 (APPEND ys [y] // APPEND ys' [x2]) v = OVAR1 x1”
            THEN TRY (FIRST_ASSUM REWRITE_THM
                      THEN REWRITE_TAC[ALPHA1_object_pos]
                      THEN REWRITE_TAC[alpha_match_SUB_var]
                      THEN REWRITE_TAC[vsubst1,SUB1]
                      THEN ASM_REWRITE_TAC[object1_one_one]
                      THEN NO_TAC)
            THEN DEP_REWRITE_TAC[ALPHA1_EXTRANEOUS_CONTEXT]
            THEN ASM_REWRITE_TAC[FV_object1_def,IN,IN_FV_SUB_vsubst1]
            THEN REPEAT DISCH_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN EXISTS_TAC “xs':var list”
            THEN EXISTS_TAC “ys':var list”
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );



val ALPHA1_SWITCH_LEMMA = TAC_PROOF(([],
    “(!o3 o2 xs' ys.
          ALPHA1_obj o3 o2 xs' ys ==>
          (!o1 x y xs ys'.
            (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
            (o3 = (o1 <[ (APPEND xs [x] // APPEND xs' [y]))) /\
            ALPHA1_obj o1 (o2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
             ==>
            ALPHA1_obj o1 o2 (APPEND xs [x]) (APPEND ys [y]))) /\
        (!d3 d2 xs' ys.
          ALPHA1_dict d3 d2 xs' ys ==>
          (!d1 x y xs ys'.
            (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
            (d3 = (d1 <[ (APPEND xs [x] // APPEND xs' [y]))) /\
            ALPHA1_dict d1 (d2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
             ==>
            ALPHA1_dict d1 d2 (APPEND xs [x]) (APPEND ys [y]))) /\
        (!e3 e2 xs' ys.
          ALPHA1_entry e3 e2 xs' ys ==>
          (!e1 x y xs ys'.
            (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
            (e3 = (e1 <[ (APPEND xs [x] // APPEND xs' [y]))) /\
            ALPHA1_entry e1 (e2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
             ==>
            ALPHA1_entry e1 e2 (APPEND xs [x]) (APPEND ys [y]))) /\
        (!m3 m2 xs' ys.
          ALPHA1_method m3 m2 xs' ys ==>
          (!m1 x y xs ys'.
            (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
            (m3 = (m1 <[ (APPEND xs [x] // APPEND xs' [y]))) /\
            ALPHA1_method m1 (m2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
             ==>
            ALPHA1_method m1 m2 (APPEND xs [x]) (APPEND ys [y])))”),
    rule_induct ALPHA1_strong_ind
    THEN REPEAT STRIP_TAC
    THEN UNDISCH_LAST_TAC
    THEN UNDISCH_LAST_TAC
    THENL (* 8 subgoals *)
      [ STRIP_ASSUME_TAC (SPEC “o1:obj1” obj1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_distinct]
        (* one subgoal *)
        THEN REPEAT DISCH_TAC
        THEN MATCH_MP_TAC ALPHA1_SWITCH_OVAR1
        THEN EXISTS_TAC “xs:var list”
        THEN EXISTS_TAC “ys':var list”
        THEN IMP_RES_TAC alpha_match_LENGTH
        THEN ASM_REWRITE_TAC[]
        THEN POP_TAC
        THEN UNDISCH_LAST_TAC
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN ASM_REWRITE_TAC[ALPHA1_object_pos],


        STRIP_ASSUME_TAC (SPEC “o1:obj1” obj1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_distinct,obj_SUB_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[object1_one_one]
        THEN DISCH_TAC
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN DISCH_TAC
        THEN RES_TAC,

        STRIP_ASSUME_TAC (SPEC “o1':obj1” obj1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_distinct,obj_SUB_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[object1_one_one]
        THEN STRIP_TAC
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN STRIP_TAC
        THEN POP_ASSUM REWRITE_THM
        THEN RES_TAC,

        STRIP_ASSUME_TAC (SPEC “o1':obj1” obj1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_distinct,obj_SUB_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[object1_one_one]
        THEN STRIP_TAC
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN STRIP_TAC
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        STRIP_ASSUME_TAC (SPEC “d1':^dict1” dict1_cases)
        (* two subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[object1_one_one]
        THEN STRIP_TAC
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        STRIP_ASSUME_TAC (SPEC “d1:^dict1” dict1_cases)
        (* two subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_distinct]
        (* one subgoal *)
        THEN ASM_REWRITE_TAC[ALPHA1_object_pos,LENGTH,LENGTH_APPEND],

        STRIP_ASSUME_TAC (SPEC “e1:^entry1” entry1_cases)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN REWRITE_TAC[object1_one_one]
        THEN STRIP_TAC
        THEN ASM_REWRITE_TAC[ALPHA1_object_pos]
        THEN STRIP_TAC
        THEN RES_TAC,

        STRIP_ASSUME_TAC (SPEC “m1:method1” method1_cases)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_object1_def]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[object1_one_one]
        THEN STRIP_TAC
        THEN REWRITE_TAC[ALPHA1_object_pos]
        THEN DISCH_TAC
        THEN REWRITE_TAC[GSYM (CONJUNCT2 APPEND)]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN EXISTS_TAC “CONS
                              (variant y
                                (FV_subst1 (APPEND ys [y'] // APPEND ys' [x'])
                                  (FV_obj1 o2 DIFF {y})))
                              ys'”
        THEN ASM_REWRITE_TAC[LENGTH,APPEND,vsubst1,SL,IN]
      ]
   );


val ALPHA1_SWITCH = store_thm
   ("ALPHA1_SWITCH",
    “(!o1 o2 xs xs' ys ys' x y.
          (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
          ALPHA1_obj (o1 <[ (APPEND xs [x] // APPEND xs' [y])) o2 xs' ys /\
          ALPHA1_obj o1 (o2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
            ==>
          ALPHA1_obj o1 o2 (APPEND xs [x]) (APPEND ys [y])) /\
       (!d1 d2 xs xs' ys ys' x y.
          (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
          ALPHA1_dict (d1 <[ (APPEND xs [x] // APPEND xs' [y])) d2 xs' ys /\
          ALPHA1_dict d1 (d2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
            ==>
          ALPHA1_dict d1 d2 (APPEND xs [x]) (APPEND ys [y])) /\
       (!e1 e2 xs xs' ys ys' x y.
          (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
          ALPHA1_entry (e1 <[ (APPEND xs [x] // APPEND xs' [y])) e2 xs' ys /\
          ALPHA1_entry e1 (e2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
            ==>
          ALPHA1_entry e1 e2 (APPEND xs [x]) (APPEND ys [y])) /\
       (!m1 m2 xs xs' ys ys' x y.
          (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
          ALPHA1_method (m1 <[ (APPEND xs [x] // APPEND xs' [y])) m2 xs' ys/\
          ALPHA1_method m1 (m2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
            ==>
          ALPHA1_method m1 m2 (APPEND xs [x]) (APPEND ys [y]))”,
    REPEAT STRIP_TAC
    THENL (map (MATCH_MP_TAC o
                REWRITE_RULE[AND_IMP_INTRO] o
                CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
                   (CONJUNCTS ALPHA1_SWITCH_LEMMA))
    THENL
      [ EXISTS_TAC “(o1: obj1) <[ (APPEND xs [x] // APPEND xs' [y])”,
        EXISTS_TAC “(d1:^dict1) <[ (APPEND xs [x] // APPEND xs' [y])”,
        EXISTS_TAC “(e1:^entry1) <[ (APPEND xs [x] // APPEND xs' [y])”,
        EXISTS_TAC “(m1: method1) <[ (APPEND xs [x] // APPEND xs' [y])”
      ]
    THEN EXISTS_TAC “xs':var list”
    THEN EXISTS_TAC “ys':var list”
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA1_SIGMA_subst = store_thm
   ("ALPHA1_SIGMA_subst",
    “!o1 o2 x y a.
         ALPHA1_method (SIGMA1 x o1) (SIGMA1 y o2) [] [] ==>
         (ALPHA1_obj (o1 <[ [x, a]) (o2 <[ [y, a]) [] [])”,
    REWRITE_TAC[ALPHA1_object_pos]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN IMP_RES_TAC (CONJUNCT1 ALPHA1_SUB)
    THEN POP_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[ALPHA1_subst]
    THEN REWRITE_TAC[alpha_match]
    THEN REWRITE_TAC[SUB1]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA1_REFL]
   );


val ALPHA1_method_one_one = store_thm
   ("ALPHA1_method_one_one",
    “!o1 o2 x y.
         ALPHA1_method (SIGMA1 x o1) (SIGMA1 y o2) [] [] =
         (ALPHA1_obj (o1 <[ [x, OVAR1 y]) o2 [] [] /\
          ALPHA1_obj o1 (o2 <[ [y, OVAR1 x]) [] [])”,
    REPEAT GEN_TAC
    THEN EQ_TAC
    THENL
      [ STRIP_TAC
        THEN IMP_RES_TAC ALPHA1_SYM
        THEN IMP_RES_THEN MP_TAC ALPHA1_SIGMA_subst
        THEN DISCH_THEN (ASSUME_TAC o SPEC “OVAR1 y”)
        THEN DISCH_THEN (MP_TAC o SPEC “OVAR1 x”)
        THEN POP_ASSUM MP_TAC
        THEN REWRITE_TAC[subst_SAME_ONE1]
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC ALPHA1_SYM
        THEN ASM_REWRITE_TAC[],

        REWRITE_TAC[ALPHA1_object_pos]
        THEN REPEAT STRIP_TAC
        THEN ONCE_REWRITE_TAC[GSYM (CONJUNCT1 APPEND)]
        THEN MATCH_MP_TAC (CONJUNCT1 ALPHA1_SWITCH)
        THEN EXISTS_TAC “[]:var list”
        THEN EXISTS_TAC “[]:var list”
        THEN ASM_REWRITE_TAC[LENGTH,APPEND,vsubst1]
      ]
   );



(* ========================================================== *)
(* Now we define the alpha-equivalence predicates themselves. *)
(* ========================================================== *)

val ALPHA_obj =
    new_definition ("ALPHA_obj",
    “ALPHA_obj o1 o2 = ALPHA1_obj o1 o2 [] []”);

val ALPHA_dict =
    new_definition ("ALPHA_dict",
    “ALPHA_dict d1 d2 = ALPHA1_dict d1 d2 [] []”);

val ALPHA_entry =
    new_definition ("ALPHA_entry",
    “ALPHA_entry e1 e2 = ALPHA1_entry e1 e2 [] []”);

val ALPHA_method =
    new_definition ("ALPHA_method",
    “ALPHA_method m1 m2 = ALPHA1_method m1 m2 [] []”);


val ALPHA_object = store_thm
   ("ALPHA_object",
    “(!o1 o2. ALPHA_obj o1 o2 = ALPHA1_obj o1 o2 [] []) /\
        (!d1 d2. ALPHA_dict d1 d2 = ALPHA1_dict d1 d2 [] []) /\
        (!e1 e2. ALPHA_entry e1 e2 = ALPHA1_entry e1 e2 [] []) /\
        (!m1 m2. ALPHA_method m1 m2 = ALPHA1_method m1 m2 [] [])”,
    REWRITE_TAC[ALPHA_obj,ALPHA_dict,ALPHA_entry,ALPHA_method]
   );


val ALPHA_HEIGHT = store_thm
   ("ALPHA_HEIGHT",
    “(!o1 o2. ALPHA_obj o1 o2 ==>
                       (HEIGHT_obj1 o1 = HEIGHT_obj1 o2)) /\
        (!d1 d2. ALPHA_dict d1 d2 ==>
                       (HEIGHT_dict1 d1 = HEIGHT_dict1 d2)) /\
        (!e1 e2. ALPHA_entry e1 e2 ==>
                       (HEIGHT_entry1 e1 = HEIGHT_entry1 e2)) /\
        (!m1 m2. ALPHA_method m1 m2 ==>
                       (HEIGHT_method1 m1 = HEIGHT_method1 m2))”,
    REWRITE_TAC[ALPHA_object,ALPHA1_HEIGHT]
   );


val ALPHA_object_similar = store_thm
   ("ALPHA_object_similar",
    “(!x a. ALPHA_obj (OVAR1 x) a ==> (?y. a = OVAR1 y)) /\
        (!d1 a. ALPHA_obj (OBJ1 d1) a ==> (?d2. a = OBJ1 d2)) /\
        (!o1 l1 a. ALPHA_obj (INVOKE1 o1 l1) a ==>
                   (?o2 l2. a = INVOKE1 o2 l2)) /\
        (!o1 l1 m1 a. ALPHA_obj (UPDATE1 o1 l1 m1) a ==>
                      (?o2 l2 m2. a = UPDATE1 o2 l2 m2)) /\
        (!e1 d1 d. ALPHA_dict (CONS e1 d1) d ==>
                       (?e2 d2. d = CONS e2 d2)) /\
        (!d. ALPHA_dict NIL d ==> (d = NIL)) /\
        (!l1 m1 e. ALPHA_entry (l1,m1) e ==>
                   (?l2 m2. e = (l2,m2))) /\
        (!x1 o1 m. ALPHA_method (SIGMA1 x1 o1) m ==>
                   (?x2 o2. m = SIGMA1 x2 o2))”,
    REWRITE_TAC[ALPHA_object,ALPHA1_object_similar]
   );


val ALPHA_REFL = store_thm
   ("ALPHA_REFL",
    “(!a. ALPHA_obj a a) /\
        (!d. ALPHA_dict d d) /\
        (!e. ALPHA_entry e e) /\
        (!m. ALPHA_method m m)”,
    REWRITE_TAC[ALPHA_object,ALPHA1_REFL]
   );


val ALPHA_SYM = store_thm
   ("ALPHA_SYM",
    “(!o1 o2. ALPHA_obj o1 o2 = ALPHA_obj o2 o1) /\
        (!d1 d2. ALPHA_dict d1 d2 = ALPHA_dict d2 d1) /\
        (!e1 e2. ALPHA_entry e1 e2 = ALPHA_entry e2 e1) /\
        (!m1 m2. ALPHA_method m1 m2 = ALPHA_method m2 m1)”,
    REWRITE_TAC[ALPHA_object]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN DISCH_THEN (REWRITE_THM o ONCE_REWRITE_RULE[ALPHA1_SYM])
   );


val ALPHA_TRANS = store_thm
   ("ALPHA_TRANS",
    “(!o1 o2 o3. ALPHA_obj o1 o2 /\ ALPHA_obj o2 o3 ==>
                             ALPHA_obj o1 o3) /\
        (!d1 d2 d3. ALPHA_dict d1 d2 /\ ALPHA_dict d2 d3 ==>
                             ALPHA_dict d1 d3) /\
        (!e1 e2 e3. ALPHA_entry e1 e2 /\ ALPHA_entry e2 e3 ==>
                             ALPHA_entry e1 e3) /\
        (!m1 m2 m3. ALPHA_method m1 m2 /\ ALPHA_method m2 m3 ==>
                             ALPHA_method m1 m3)”,
    REWRITE_TAC[ALPHA_object,ALPHA1_TRANS]
   );


val ALPHA_object_pos = store_thm
   ("ALPHA_object_pos",
    “(!x y.
          ALPHA_obj (OVAR1 x) (OVAR1 y) = (x = y)) /\
        (!d1 d2.
          ALPHA_obj (OBJ1 d1) (OBJ1 d2) = ALPHA_dict d1 d2) /\
        (!o1 o2 l1 l2.
          ALPHA_obj (INVOKE1 o1 l1) (INVOKE1 o2 l2) =
          ALPHA_obj o1 o2 /\ (l1 = l2)) /\
        (!o1 o2 l1 l2 m1 m2.
          ALPHA_obj (UPDATE1 o1 l1 m1) (UPDATE1 o2 l2 m2) =
          ALPHA_obj o1 o2 /\ (l1 = l2) /\ ALPHA_method m1 m2) /\
        (!e1 e2 d1 d2.
          ALPHA_dict (CONS e1 d1) (CONS e2 d2) =
          ALPHA_entry e1 e2 /\ ALPHA_dict d1 d2) /\
        (ALPHA_dict [] [] = T) /\
        (!l1 l2 m1 m2.
          ALPHA_entry (l1,m1) (l2,m2) =
          (l1 = l2) /\ ALPHA_method m1 m2) (* /\
        (!x1 x2 o1 o2.
          ALPHA_method (SIGMA1 x1 o1) (SIGMA1 x2 o2) =
          ALPHA1_obj o1 o2 [x1] [x2]) *)”,
    REWRITE_TAC[ALPHA_object,ALPHA1_object_pos,alpha_match]
   );


val ALPHA_method_SIGMA = store_thm
   ("ALPHA_method_SIGMA",
    “!x o1 o2.
          ALPHA_method (SIGMA1 x o1) (SIGMA1 x o2) = ALPHA_obj o1 o2”,
    REWRITE_TAC[ALPHA_object,ALPHA1_object_pos]
    THEN REPEAT GEN_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA1_FREE_CONTEXT))
    THEN REWRITE_TAC[vsubst1,SUB1]
    THEN REPEAT STRIP_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_object_neg = store_thm
   ("ALPHA_object_neg",
    “(!x d. ALPHA_obj (OVAR1 x) (OBJ1 d) = F) /\
        (!x a l. ALPHA_obj (OVAR1 x) (INVOKE1 a l) = F) /\
        (!x a l m. ALPHA_obj (OVAR1 x) (UPDATE1 a l m) = F) /\
        (!d x. ALPHA_obj (OBJ1 d) (OVAR1 x) = F) /\
        (!d a l. ALPHA_obj (OBJ1 d) (INVOKE1 a l) = F) /\
        (!d a l m. ALPHA_obj (OBJ1 d) (UPDATE1 a l m) = F) /\
        (!a l x. ALPHA_obj (INVOKE1 a l) (OVAR1 x) = F) /\
        (!a l d. ALPHA_obj (INVOKE1 a l) (OBJ1 d) = F) /\
        (!o1 l1 o2 l2 m2.
          ALPHA_obj (INVOKE1 o1 l1) (UPDATE1 o2 l2 m2) = F) /\
        (!a l m x. ALPHA_obj (UPDATE1 a l m) (OVAR1 x) = F) /\
        (!a l m d. ALPHA_obj (UPDATE1 a l m) (OBJ1 d) = F) /\
        (!o1 l1 m1 o2 l2.
          ALPHA_obj (UPDATE1 o1 l1 m1) (INVOKE1 o2 l2) = F)
         /\
        (!e d. ALPHA_dict (CONS e d) NIL = F) /\
        (!e d. ALPHA_dict NIL (CONS e d) = F)”,
    REWRITE_TAC[ALPHA_object,ALPHA1_object_neg]
   );


(* --------------------------------------------------------------------- *)
(* We claim that ALPHA is a binary relation on the object/method1         *)
(* language which is                                                     *)
(*  1) reflexive                                                         *)
(*  2) symmetric                                                         *)
(*  3) transitive                                                        *)
(*  4) compatible (in the sense of Barendregt, Definition 3.1.1, pg 50   *)
(* --------------------------------------------------------------------- *)


val ALPHA_FV = store_thm
   ("ALPHA_FV",
    “(!o1 o2. ALPHA_obj o1 o2 ==> (FV_obj1 o1 = FV_obj1 o2)) /\
        (!d1 d2. ALPHA_dict d1 d2 ==> (FV_dict1 d1 = FV_dict1 d2)) /\
        (!e1 e2. ALPHA_entry e1 e2 ==> (FV_entry1 e1 = FV_entry1 e2)) /\
        (!m1 m2. ALPHA_method m1 m2 ==> (FV_method1 m1 = FV_method1 m2))”,
    REWRITE_TAC[ALPHA_object]
    THEN REPEAT STRIP_TAC
    THENL (map IMP_RES_TAC (CONJUNCTS ALPHA1_SYM))
    THENL (map IMP_RES_TAC (CONJUNCTS ALPHA1_FV))
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[alpha_match_NIL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
   );



(*
val ALPHA1_subst =
    new_definition
    ("ALPHA1_subst",
     “ALPHA1_subst xs ys xs' ys' t1 t2 s1 s2 =
        (LENGTH xs' = LENGTH ys') /\
        (!x y. (x IN t1) /\ (y IN t2) /\
               alpha_match xs ys x y ==>
               ALPHA1_obj (SUB1 s1 x) (SUB1 s2 y) xs' ys')”);
*)

val ALPHA_subst =
    new_definition
    ("ALPHA_subst",
     “ALPHA_subst t s1 s2 =
        (!x. (x IN t) ==>
               ALPHA_obj (SUB1 s1 x) (SUB1 s2 x))”);


val ALPHA_SUB_CONTEXT = store_thm
   ("ALPHA_SUB_CONTEXT",
    “(!o1 o2 s1 s2. ALPHA_obj o1 o2 /\
                       ALPHA_subst (FV_obj1 o1) s1 s2 ==>
                       ALPHA_obj (o1 <[ s1) (o2 <[ s2)) /\
        (!d1 d2 s1 s2. ALPHA_dict d1 d2 /\
                       ALPHA_subst (FV_dict1 d1) s1 s2 ==>
                       ALPHA_dict (d1 <[ s1) (d2 <[ s2)) /\
        (!e1 e2 s1 s2. ALPHA_entry e1 e2 /\
                       ALPHA_subst (FV_entry1 e1) s1 s2 ==>
                       ALPHA_entry (e1 <[ s1) (e2 <[ s2)) /\
        (!m1 m2 s1 s2. ALPHA_method m1 m2 /\
                       ALPHA_subst (FV_method1 m1) s1 s2 ==>
                       ALPHA_method (m1 <[ s1) (m2 <[ s2))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA_FV
    THEN REWRITE_ALL_TAC[ALPHA_object]
    THEN FIRST (map (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o
                     CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
                    (CONJUNCTS ALPHA1_SUB))
    THEN EXISTS_TAC “[]:var list”
    THEN EXISTS_TAC “[]:var list”
    THEN ASM_REWRITE_TAC[]
    THEN UNDISCH_ALL_TAC
    THEN REWRITE_TAC[ALPHA_subst,ALPHA1_subst]
    THEN REWRITE_TAC[ALPHA_object,alpha_match]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_SUB = store_thm
   ("ALPHA_SUB",
    “(!o1 o2 s. ALPHA_obj o1 o2 ==>
                       ALPHA_obj (o1 <[ s) (o2 <[ s)) /\
        (!d1 d2 s. ALPHA_dict d1 d2 ==>
                       ALPHA_dict (d1 <[ s) (d2 <[ s)) /\
        (!e1 e2 s. ALPHA_entry e1 e2 ==>
                       ALPHA_entry (e1 <[ s) (e2 <[ s)) /\
        (!m1 m2 s. ALPHA_method m1 m2 ==>
                       ALPHA_method (m1 <[ s) (m2 <[ s))”,
    REPEAT STRIP_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS ALPHA_SUB_CONTEXT))
    THEN ASM_REWRITE_TAC[ALPHA_subst,ALPHA_REFL]
   );


val ALPHA_CHANGE_VAR = store_thm
   ("ALPHA_CHANGE_VAR",
    “!y x s v a.
         ~(x IN FV_subst1 s (FV_obj1 a DIFF {v})) /\
         ~(y IN FV_subst1 s (FV_obj1 a DIFF {v})) ==>
         ALPHA_method (SIGMA1 x (a <[ CONS (v, OVAR1 x) s))
                      (SIGMA1 y (a <[ CONS (v, OVAR1 y) s))”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[ALPHA_object,ALPHA1_object_pos]
    THEN MATCH_MP_TAC ALPHA1_CHANGE_VAR
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_CHANGE_ONE_VAR = store_thm
   ("ALPHA_CHANGE_ONE_VAR",
    “!x v a.
         ~(x IN (FV_obj1 a DIFF {v})) ==>
         ALPHA_method (SIGMA1 x (a <[ [v, OVAR1 x]))
                      (SIGMA1 v a)”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPECL [“v:var”,“x:var”,“[]:^subs1”,
                        “v:var”,“a:obj1”]
                     ALPHA_CHANGE_VAR)
    THEN REWRITE_TAC[FV_subst_NIL1]
    THEN UNDISCH_ALL_TAC
    THEN REWRITE_TAC[IN_DIFF,IN]
    THEN DISCH_THEN REWRITE_THM
    THEN DEP_ONCE_REWRITE_TAC[SPECL[“a:obj1”,“[v,OVAR1 v]”]
                                    (CONJUNCT1 subst_IDENT1)]
    THEN GEN_TAC
    THEN REWRITE_TAC[SUB1]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


(* The following theorem is unused.

val ALPHA_SWITCH = store_thm
   ("ALPHA_SWITCH",
    “(!o1 o2 x y.
          ALPHA_obj (o1 <[ [x,OVAR1 y]) o2 /\
          ALPHA_obj o1 (o2 <[ [y,OVAR1 x])
            ==>
          ALPHA1_obj o1 o2 [x] [y]) /\
        (!d1 d2 x y.
          ALPHA_dict (d1 <[ [x,OVAR1 y]) d2 /\
          ALPHA_dict d1 (d2 <[ [y,OVAR1 x])
            ==>
          ALPHA1_dict d1 d2 [x] [y]) /\
        (!e1 e2 x y.
          ALPHA_entry (e1 <[ [x,OVAR1 y]) e2 /\
          ALPHA_entry e1 (e2 <[ [y,OVAR1 x])
            ==>
          ALPHA1_entry e1 e2 [x] [y]) /\
        (!m1 m2 x y.
          ALPHA_method (m1 <[ [x,OVAR1 y]) m2 /\
          ALPHA_method m1 (m2 <[ [y,OVAR1 x])
            ==>
          ALPHA1_method m1 m2 [x] [y])”,
    REWRITE_TAC[ALPHA_object]
    THEN REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC[GSYM (CONJUNCT1 APPEND)]
    THENL (map MATCH_MP_TAC (CONJUNCTS ALPHA1_SWITCH))
    THEN EXISTS_TAC “[]:var list”
    THEN EXISTS_TAC “[]:var list”
    THEN ASM_REWRITE_TAC[APPEND,vsubst1]
   );

*)

val ALPHA_method_one_one = store_thm
   ("ALPHA_method_one_one",
    “!o1 o2 x y.
         ALPHA_method (SIGMA1 x o1) (SIGMA1 y o2) =
         (ALPHA_obj (o1 <[ [x, OVAR1 y]) o2 /\
          ALPHA_obj o1 (o2 <[ [y, OVAR1 x]))”,
    REWRITE_TAC[ALPHA_object,ALPHA1_method_one_one]
   );

val ALPHA_SIGMA_subst = store_thm
   ("ALPHA_SIGMA_subst",
    “!o1 o2 x y a.
         ALPHA_method (SIGMA1 x o1) (SIGMA1 y o2) ==>
         (ALPHA_obj (o1 <[ [x, a]) (o2 <[ [y, a]))”,
    REWRITE_TAC[ALPHA_object,ALPHA1_SIGMA_subst]
   );


(* --------------------------------------------------------------------- *)
(* Primitive semantics of the sigma-calculus:                            *)
(*   Abadi/Cardelli, Section 6.1.2, page 58-59                           *)
(* Here we define the primitive reduction operator of the calculus.      *)
(* It has two forms, one for method invocation and one for update.       *)
(* --------------------------------------------------------------------- *)

val obj1_0_RSP = store_thm
   ("obj1_0_RSP",
    “ALPHA_obj obj1_0 obj1_0”,
    REWRITE_TAC[ALPHA_REFL]
   );

val method1_0_RSP = store_thm
   ("method1_0_RSP",
    “ALPHA_method method1_0 method1_0”,
    REWRITE_TAC[ALPHA_REFL]
   );


(* --------------------------------------------------------------------- *)
(* Definition of method invocation.                                      *)
(* --------------------------------------------------------------------- *)

val invoke_method1_RSP = store_thm
   ("invoke_method1_RSP",
    “!m1 m2 o1 o2.
         ALPHA_method m1 m2 /\ ALPHA_obj o1 o2 ==>
         ALPHA_obj (invoke_method1 m1 o1) (invoke_method1 m2 o2)”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN GEN_TAC
    THEN MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[invoke_method1_def]
    THEN REWRITE_TAC[ALPHA_object,ALPHA1_object_pos]
    THEN STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_SUB
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[ALPHA1_subst]
    THEN REWRITE_TAC[alpha_match]
    THEN REWRITE_TAC[SUB1]
    THEN REPEAT STRIP_TAC
    THENL
      [ POP_ASSUM (REWRITE_ALL_THM o SYM)
        THEN POP_ASSUM (REWRITE_ALL_THM o SYM)
        THEN ASM_REWRITE_TAC[],

        POP_ASSUM (REWRITE_ALL_THM o SYM)
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[ALPHA1_REFL]
      ]
   );

val invoke_dict1_RSP = store_thm
   ("invoke_dict1_RSP",
    “!d1 d2 o1 o2 lb.
         ALPHA_dict d1 d2 /\ ALPHA_obj o1 o2 ==>
         ALPHA_obj (invoke_dict1 d1 o1 lb) (invoke_dict1 d2 o2 lb)”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REWRITE_TAC[ALPHA_object_neg]
    THEN REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN PURE_REWRITE_TAC[invoke_dict1]
    THEN PURE_REWRITE_TAC[ALPHA_object_pos]
    THEN REWRITE_TAC[ALPHA_REFL]
    THEN POP_TAC
    THEN STRIP_TAC
    THEN RES_TAC
    THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
    THEN IMP_RES_TAC invoke_method1_RSP
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );

val invoke1_RSP = store_thm
   ("invoke1_RSP",
    “!o1 o2 lb. ALPHA_obj o1 o2 ==>
                   ALPHA_obj (invoke1 o1 lb) (invoke1 o2 lb)”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THENL [GEN_TAC, ALL_TAC, GEN_TAC, GEN_TAC]
    THEN MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REWRITE_TAC[ALPHA_object_neg]
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[invoke1_def]
    THEN REWRITE_TAC[ALPHA_REFL]
    (* only one subgoal *)
    THEN DISCH_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[ALPHA_object_pos])
    THEN IMP_RES_TAC invoke_dict1_RSP
    THEN ASM_REWRITE_TAC[]
   );

val update_dict1_RSP = store_thm
   ("update_dict1_RSP",
    “!d1 d2 lb m1 m2.
         ALPHA_dict d1 d2 /\ ALPHA_method m1 m2 ==>
         ALPHA_dict (update_dict1 d1 lb m1) (update_dict1 d2 lb m2)”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REWRITE_TAC[ALPHA_object_neg]
    THEN REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN PURE_REWRITE_TAC[update_dict1]
    THEN PURE_REWRITE_TAC[ALPHA_object_pos]
    THEN REWRITE_TAC[ALPHA_REFL]
    THEN POP_TAC
    THEN STRIP_TAC
    THEN RES_TAC
    THEN POP_TAC
    THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN PURE_REWRITE_TAC[ALPHA_object_pos]
    THEN ASM_REWRITE_TAC[]
   );

val update1_RSP = store_thm
   ("update1_RSP",
    “!o1 o2 lb m1 m2.
         ALPHA_obj o1 o2 /\ ALPHA_method m1 m2 ==>
         ALPHA_obj (update1 o1 lb m1) (update1 o2 lb m2)”,
    MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THENL [GEN_TAC, ALL_TAC, GEN_TAC, GEN_TAC]
    THEN MUTUAL_INDUCT_THEN obj1_induction ASSUME_TAC
    THEN REWRITE_TAC[ALPHA_object_neg]
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[update1_def]
    THEN REWRITE_TAC[ALPHA_REFL]
    (* only one subgoal *)
    THEN REWRITE_TAC[ALPHA_object_pos]
    THEN STRIP_TAC
    THEN IMP_RES_TAC update_dict1_RSP
    THEN ASM_REWRITE_TAC[]
   );



val _ = export_theory();

val _ = print_theory_to_file "alpha.lst";

val _ = html_theory "alpha";

val _ = print_theory_size();
