open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Building the definitions of alpha equivalence for object expressions. *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "alpha";


open prim_recTheory pairTheory pairLib listTheory rich_listTheory;
open combinTheory;
open listLib;
open pred_setTheory pred_setLib;
open numTheory;
open numLib;
open arithmeticTheory;
open bossLib;
open MutualIndThen;
open ind_rel;
open dep_rewrite;
open more_listTheory;
open more_setTheory;
open variableTheory;
open termTheory;


open tactics;



val vars   =  ty_antiq( ==`:var list`== );
val subs   =  ty_antiq( ==`:(var # 'a term1) list`== );



(* --------------------------------------------------------------------- *)
(* Define alpha equivalence for lambda expressions.                      *)
(* --------------------------------------------------------------------- *)

(* Here is the syntax, repeated for clarity:

val _ = Hol_datatype

        ` term1 = Con1 of 'a
                | Var1 of var
                | App1 of term1 => term1
                | Lam1 of var => term1 ` ;

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
    (--`(!x1 y1. alpha_match [] [] x1 y1 = (x1 = y1)) /\
        (!ys y x1 y1. alpha_match [] (CONS y ys) x1 y1 = F) /\
        (!xs x x1 y1. alpha_match (CONS x xs) [] x1 y1 = F) /\
        (!xs ys x y x1 y1. alpha_match (CONS x xs) (CONS y ys) x1 y1 =
                           (((x1 = x) /\ (y1 = y)
                             /\ (LENGTH xs = LENGTH ys)) \/
                            (~(x1 = x) /\ ~(y1 = y)
                             /\ alpha_match xs ys x1 y1)))`--),
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
    (--`alpha_match [] [] = $=`--),
    EXT_TAC (--`x:var`--)
    THEN GEN_TAC
    THEN EXT_TAC (--`y:var`--)
    THEN GEN_TAC
    THEN REWRITE_TAC[alpha_match]
   );

val alpha_match_REFL = store_thm
   ("alpha_match_REFL",
    (--`!xs x. alpha_match xs xs x x`--),
    LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[alpha_match]
    THEN REWRITE_TAC[EXCLUDED_MIDDLE]
   );

val alpha_match_SYM = store_thm
   ("alpha_match_SYM",
    (--`!xs ys x1 y1. alpha_match xs ys x1 y1 = alpha_match ys xs y1 x1`--),
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
    (--`!xs ys zs x y z. alpha_match xs ys x y /\ alpha_match ys zs y z
                         ==> alpha_match xs zs x z`--),
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
    (--`!xs ys x y. alpha_match xs ys x y =
                    ((LENGTH xs = LENGTH ys) /\
                     (SUB1 (xs // ys) x = Var1 y:'a term1) /\
                     (SUB1 (ys // xs) y = Var1 x:'a term1))`--),
    LIST_INDUCT_TAC
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match,vsubst1,SUB1,term1_one_one,
                         LENGTH, GSYM NOT_SUC]
        THEN REPEAT GEN_TAC
        THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[alpha_match,vsubst1,SUB1,term1_one_one,
                         LENGTH, NOT_SUC]
        THEN REPEAT GEN_TAC
        THEN ASM_REWRITE_TAC[prim_recTheory.INV_SUC_EQ]
        THEN COND_CASES_TAC  (* (x'' = x)? *)
        THENL
          [ POP_ASSUM REWRITE_THM
            THEN REWRITE_TAC[term1_one_one]
            THEN COND_CASES_TAC  (* (x' = y)? *)
            THENL
              [ POP_ASSUM REWRITE_THM,

                POP_ASSUM (REWRITE_THM o GSYM)
              ],

            FIRST_ASSUM (REWRITE_THM o GSYM)
            THEN COND_CASES_TAC  (* (x' = y)? *)
            THENL
              [ POP_ASSUM (REWRITE_THM o SYM)
                THEN REWRITE_TAC[term1_one_one]
                THEN FIRST_ASSUM (REWRITE_THM o GSYM),

                REWRITE_TAC[]
              ]
          ]
      ]
   );


val alpha_match_IDENT = store_thm
   ("alpha_match_IDENT",
    (--`!xs x y. alpha_match xs xs x y = (x = y)`--),
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
    (--`!xs ys x y x' y'.
         alpha_match (CONS x xs) (CONS y ys) x' y' /\ ~(x' = x)
          ==> alpha_match xs ys x' y' /\ ~(y' = y)`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[alpha_match_SUB_var]
    THEN REWRITE_TAC[LENGTH,INV_SUC_EQ,vsubst1,SUB1]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM (fn th => REWRITE_ALL_TAC[th] THEN MP_TAC th)
    THEN POP_ASSUM MP_TAC
    THEN COND_CASES_TAC
    THENL
      [ REWRITE_TAC[term1_one_one]
        THEN DISCH_THEN REWRITE_THM,

        DISCH_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


val alpha_match_pair = store_thm
   ("alpha_match_pair",
    (--`!xs ys x1 y1 x2 y2.
             alpha_match xs ys x1 y1 /\
             alpha_match xs ys x2 y2 ==>
               ((x1 = x2) = (y1 = y2))`--),
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
    (--`!xs ys x y. alpha_match xs ys x y ==> (LENGTH xs = LENGTH ys)`--),
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

val ALPHA1 =
--`ALPHA1 : 'a term1 -> 'a term1 -> ^vars -> ^vars -> bool`--;

val ALPHA1_patterns = [--`^ALPHA1 t1 t2 xs ys`--];

val ALPHA1_rules_tm =
--`

       (* -------------------------------------------- *)
                (^ALPHA1 (Con1 a) (Con1 a) xs ys)                /\


                      (alpha_match xs ys x y
       (* -------------------------------------------- *) ==>
                (^ALPHA1 (Var1 x) (Var1 y) xs ys))               /\


         ((^ALPHA1 t1 t2 xs ys) /\ (^ALPHA1 u1 u2 xs ys)
       (* -------------------------------------------- *) ==>
           (^ALPHA1 (App1 t1 u1) (App1 t2 u2) xs ys))            /\

(* Alpha conversion: *)

            ((^ALPHA1 u1 u2 (CONS x xs) (CONS y ys))
       (* -------------------------------------------- *) ==>
            (^ALPHA1 (Lam1 x u1) (Lam1 y u2) xs ys))
`--;

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


val [ALPHA1_Con1, ALPHA1_Var1, ALPHA1_App1, ALPHA1_Lam1]
    = CONJUNCTS ALPHA1_rules_sat;



val ALPHA1_REFL = store_thm
   ("ALPHA1_REFL",
    (--`!t:'a term1 xs. ALPHA1 t t xs xs`--),
    Induct
    THEN REPEAT GEN_TAC
    THENL (* 4 subgoals *)
      [ REWRITE_TAC[ALPHA1_Con1],

        MATCH_MP_TAC ALPHA1_Var1
        THEN REWRITE_TAC[alpha_match_REFL],

        MATCH_MP_TAC ALPHA1_App1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_Lam1
        THEN ASM_REWRITE_TAC[]
      ]
   );


val ALPHA1_IMP_SYM = TAC_PROOF(([],
    (--`!t1 t2:'a term1 xs ys. ALPHA1 t1 t2 xs ys ==> ALPHA1 t2 t1 ys xs`--)),
    rule_induct ALPHA1_strong_ind
    THEN REPEAT STRIP_TAC
    THENL (* 4 subgoals *)
      [ ASM_REWRITE_TAC[ALPHA1_Con1],

        MATCH_MP_TAC ALPHA1_Var1
        THEN IMP_RES_TAC alpha_match_SYM,

        MATCH_MP_TAC ALPHA1_App1
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC ALPHA1_Lam1
        THEN ASM_REWRITE_TAC[]
      ]
   );

val ALPHA1_SYM = store_thm
   ("ALPHA1_SYM",
    (--`!t1 t2 :'a term1 xs ys. ALPHA1 t1 t2 xs ys = ALPHA1 t2 t1 ys xs`--),
    REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_IMP_SYM
   );


val ALPHA1_TRANS1 = TAC_PROOF(([],
    (--`!t1 t2 :'a term1 xs ys.
                      ALPHA1 t1 t2 xs ys ==>
              !t3 zs. ALPHA1 t2 t3 ys zs ==>
                      ALPHA1 t1 t3 xs zs`--)),
    rule_induct ALPHA1_strong_ind
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM MP_TAC
    THEN ONCE_REWRITE_TAC ALPHA1_inv_thms
    THEN REWRITE_TAC[term1_one_one,term1_distinct2]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN PROVE_TAC[alpha_match_TRANS]
   );


val ALPHA1_TRANS = store_thm
   ("ALPHA1_TRANS",
    (--`!t1 t2 t3 :'a term1 xs ys zs.
           ALPHA1 t1 t2 xs ys /\
           ALPHA1 t2 t3 ys zs ==>
           ALPHA1 t1 t3 xs zs`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_TRANS1
   );


val ALPHA1_HEIGHT = store_thm
   ("ALPHA1_HEIGHT",
    (--`!t1 t2 :'a term1 xs ys.
           ALPHA1 t1 t2 xs ys ==> (HEIGHT1 t1 = HEIGHT1 t2)`--),
    rule_induct ALPHA1_ind_thm
    THEN REWRITE_TAC[HEIGHT1_def,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA1_term_similar = store_thm
   ("ALPHA1_term_similar",
    (--`(!a t xs ys. ALPHA1 (Con1 a) t xs ys ==> (t = Con1 a :'a term1)) /\
        (!x t xs ys. ALPHA1 (Var1 x) t xs ys ==> (?y. t = Var1 y :'a term1)) /\
        (!t1 u1 t xs ys. ALPHA1 (App1 t1 u1) t xs ys ==>
                         (?t2 u2. t = App1 t2 u2 :'a term1)) /\
        (!x1 u1 t xs ys. ALPHA1 (Lam1 x1 u1) t xs ys ==>
                         (?x2 u2. t = Lam1 x2 u2 :'a term1))`--),
    PURE_ONCE_REWRITE_TAC ALPHA1_inv_thms
    THEN REWRITE_TAC[term1_one_one,term1_distinct2]
    THEN REPEAT STRIP_TAC
    THEN PROVE_TAC[]
   );


val ALPHA1_term_pos = store_thm
   ("ALPHA1_term_pos",
    (--`(!a b xs ys. ALPHA1 (Con1 a :'a term1) (Con1 b) xs ys
                       = ((a = b) (*/\ (LENGTH xs = LENGTH ys)*) )) /\
        (!x y xs ys. ALPHA1 (Var1 x :'a term1) (Var1 y) xs ys
                       = alpha_match xs ys x y) /\
        (!t1 t2 u1 u2 :'a term1 xs ys. ALPHA1 (App1 t1 u1) (App1 t2 u2) xs ys
                       = (ALPHA1 t1 t2 xs ys /\ ALPHA1 u1 u2 xs ys)) /\
        (!x1 x2 u1 u2 :'a term1 xs ys. ALPHA1 (Lam1 x1 u1) (Lam1 x2 u2) xs ys
                       = ALPHA1 u1 u2 (CONS x1 xs) (CONS x2 ys))`--),
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN (EQ_TAC
          THENL [ DISCH_THEN (STRIP_ASSUME_TAC
                              o REWRITE_RULE[term1_one_one,term1_distinct2]
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


val ALPHA1_term_neg = store_thm
   ("ALPHA1_term_neg",
    (--`(!a x   xs ys. ALPHA1 (Con1 a :'a term1) (Var1 x) xs ys = F) /\
        (!a t u xs ys. ALPHA1 (Con1 a :'a term1) (App1 t u) xs ys = F) /\
        (!a y u xs ys. ALPHA1 (Con1 a :'a term1) (Lam1 y u) xs ys = F) /\
        (!x a   xs ys. ALPHA1 (Var1 x :'a term1) (Con1 a) xs ys = F) /\
        (!x t u xs ys. ALPHA1 (Var1 x :'a term1) (App1 t u) xs ys = F) /\
        (!x y u xs ys. ALPHA1 (Var1 x :'a term1) (Lam1 y u) xs ys = F) /\
        (!t u a xs ys. ALPHA1 (App1 t u :'a term1) (Con1 a) xs ys = F) /\
        (!t u x xs ys. ALPHA1 (App1 t u :'a term1) (Var1 x) xs ys = F) /\
      (!t u y v xs ys. ALPHA1 (App1 t u :'a term1) (Lam1 y v) xs ys = F) /\
        (!y u a xs ys. ALPHA1 (Lam1 y u :'a term1) (Con1 a) xs ys = F) /\
        (!y u x xs ys. ALPHA1 (Lam1 y u :'a term1) (Var1 x) xs ys = F) /\
      (!y v t u xs ys. ALPHA1 (Lam1 y v :'a term1) (App1 t u) xs ys = F)`--),
    PURE_ONCE_REWRITE_TAC ALPHA1_inv_thms
    THEN REWRITE_TAC[term1_one_one,term1_distinct2]
   );



val ALPHA1_FV = store_thm
   ("ALPHA1_FV",
    (--`!t1 t2 :'a term1 xs ys.
         ALPHA1 t1 t2 xs ys ==>
         (!x. x IN FV1 t1 ==>
              (?y. y IN FV1 t2 /\ alpha_match xs ys x y))`--),

    rule_induct ALPHA1_strong_ind
    THEN REWRITE_TAC[FV1_def]
    THEN REWRITE_TAC[IN_INSERT,NOT_IN_EMPTY,IN_UNION,IN_DIFF]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN TRY (EXISTS_TAC (--`y:var`--)
              THEN ASM_REWRITE_TAC[]
              THEN NO_TAC)
    (* only one goal here *)
    THEN EXISTS_TAC (--`y':var`--)
    THEN IMP_RES_TAC alpha_match_NOT_EQ
    THEN ASM_REWRITE_TAC[]
   );
(* Glory to God!  Soli Deo Gloria! *)



val FORALL_OR_IMP = TAC_PROOF(([],
    --`!s t (f:'a->'b) g.
        (!x. x IN s \/ x IN t ==> (f x = g x)) ==>
        ((!x. x IN s ==> (f x = g x)) /\
         (!x. x IN t ==> (f x = g x)))`--),
    PROVE_TAC []
   );


val ALPHA1_FREE_CONTEXT = store_thm
   ("ALPHA1_FREE_CONTEXT",
    (--`!t1:'a term1 t2 xs ys xs' ys'.
          ((LENGTH xs = LENGTH ys) = (LENGTH xs' = LENGTH ys')) /\
          (!x. (x IN FV1 t1) ==>
               (SUB1 ((xs // ys):^subs) x = SUB1 (xs' // ys') x)) /\
          (!y. (y IN FV1 t2) ==>
               (SUB1 ((ys // xs):^subs) y = SUB1 (ys' // xs') y))  ==>
          (ALPHA1 t1 t2 xs ys = ALPHA1 t1 t2 xs' ys')`--),
    Induct
    THENL [GEN_TAC, GEN_TAC, ALL_TAC, GEN_TAC]
    THEN Cases
    THEN REWRITE_TAC[ALPHA1_term_neg]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[ALPHA1_term_pos]
    THEN REWRITE_ALL_TAC[FV1_def,IN_DIFF,IN_UNION,IN]
    THEN EQ_TAC
    THENL (* 8 subgoals *)
      [
        (*FIRST_ASSUM (REWRITE_THM o SYM),

        FIRST_ASSUM (REWRITE_THM o SYM),*)

        REWRITE_TAC[alpha_match_SUB_var]
        THEN RW_TAC list_ss [],

        REWRITE_TAC[alpha_match_SUB_var]
        THEN RW_TAC list_ss [],

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
           SPECL [--`t:'a term1`--,
                  --`CONS (v:var) xs `--,--`CONS (v':var) ys `--,
                  --`CONS (v:var) xs'`--,--`CONS (v':var) ys'`--]
                 th])
        THEN ASM_REWRITE_TAC[LENGTH,INV_SUC_EQ]
        THEN CONJ_TAC
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        FIRST_ASSUM (fn th =>
         DEP_REWRITE_TAC[
           SPECL [--`t:'a term1`--,
                  --`CONS (v:var) xs'`--,--`CONS (v':var) ys'`--,
                  --`CONS (v:var) xs `--,--`CONS (v':var) ys `--]
                 th])
        THEN ASM_REWRITE_TAC[LENGTH,INV_SUC_EQ]
        THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
        THEN CONJ_TAC
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );



val ALPHA1_EXTRANEOUS_CONTEXT = store_thm
   ("ALPHA1_EXTRANEOUS_CONTEXT",
    (--`!t1 t2 :'a term1 xs ys x y.
          ~(x IN FV1 t1) /\ ~(y IN FV1 t2) ==>
          (ALPHA1 t1 t2 (CONS x xs) (CONS y ys) =
           ALPHA1 t1 t2 xs ys)`--),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC ALPHA1_FREE_CONTEXT
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


(* ---------------------------------------------------------------------- *)
(* Now we prepare to prove ALPHA1_SUB, the key and most important theorem *)
(* of this theory.  It is difficult, but critical.                        *)
(* ---------------------------------------------------------------------- *)


(* define ALPHA1_subst *)

val ALPHA1_subst =
    new_definition
    ("ALPHA1_subst",
     --`ALPHA1_subst xs ys xs' ys' t1 t2 s1 (s2:^subs) =
        (LENGTH xs' = LENGTH ys') /\
        (!x y. (x IN t1) /\ (y IN t2) /\
               alpha_match xs ys x y ==>
               ALPHA1 (SUB1 s1 x) (SUB1 s2 y) xs' ys')`--);


val ALPHA1_subst_UNION = store_thm
   ("ALPHA1_subst_UNION",
    (--`!xs ys xs' ys' t11 t12 t21 t22 s1 (s2:^subs).
         ALPHA1_subst xs ys xs' ys' (t11 UNION t12) (t21 UNION t22) s1 s2
         ==>
         (ALPHA1_subst xs ys xs' ys' t11 t21 s1 s2  /\
          ALPHA1_subst xs ys xs' ys' t12 t22 s1 s2)`--),
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
    (--`!xs ys xs' ys' t1 t2 s1 (s2:^subs).
         ALPHA1_subst xs ys xs' ys' t1 t2 s1 s2
         ==>
         (LENGTH xs' = LENGTH ys')`--),
    REWRITE_TAC[ALPHA1_subst]
    THEN REPEAT STRIP_TAC
   );



val variant_not_in_sub = store_thm
   ("variant_not_in_sub",
    (--`!v v' (s:^subs) t x.
         FINITE t /\ (x IN t) /\
         (v' = variant v (FV_subst1 s t))
         ==>
         ~(v' IN FV1 (SUB1 s x))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN MP_TAC (SPECL [--`v:var`--,--`FV_subst1 (s:^subs) t`--]
                       variant_not_in_set)
    THEN IMP_RES_THEN REWRITE_THM FINITE_FV_subst1
    THEN FIRST_ASSUM (REWRITE_THM o SYM)
    THEN REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,combinTheory.o_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN DISCH_THEN (MP_TAC o SPEC (--`FV1 (SUB1 (s:^subs) x)`--))
    THEN STRIP_TAC
    THEN POP_ASSUM (MP_TAC o SPEC (--`x:var`--))
    THEN ASM_REWRITE_TAC[]
   );



(* This next IS TRUE!!!  *)

val ALPHA1_SUB = store_thm
   ("ALPHA1_SUB",
    (--`!t1 t2:'a term1 xs ys. ALPHA1 t1 t2 xs ys ==>
          (!xs' ys' s1 s2.
            ALPHA1_subst xs ys xs' ys' (FV1 t1) (FV1 t2) s1 s2 ==>
            ALPHA1 (t1 <[ s1) (t2 <[ s2) xs' ys')`--),
    rule_induct ALPHA1_strong_ind
    THEN REWRITE_TAC[FV1_def]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_term1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[ALPHA1_term_pos]
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
             (--`x' = variant x (FV_subst1 (s1:^subs)
                                           (FV1 (u1:'a term1) DIFF {x}))`--)
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN DEFINE_NEW_VAR
             (--`y' = variant y (FV_subst1 (s2:^subs)
                                           (FV1 (u2:'a term1) DIFF {y}))`--)
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
            THEN REWRITE_TAC[ALPHA1_term_pos]
            THEN REWRITE_TAC[alpha_match]
            THEN FIRST_ASSUM ACCEPT_TAC,

            COND_CASES_TAC
            THEN FIRST_ASSUM REWRITE_THM (* proves one goal *)
            THEN STRIP_TAC
            (* Here the extra x', y' are extraneous *)
            THEN DEP_REWRITE_TAC[ALPHA1_EXTRANEOUS_CONTEXT]
            THEN FIRST_ASSUM (MP_TAC o SPECL[--`x'':var`--,--`y'':var`--])
            THEN REWRITE_TAC[IN_DIFF,IN]
            THEN DISCH_THEN IMP_RES_TAC
            THEN FIRST_ASSUM REWRITE_THM
            THEN CONJ_TAC
            THEN MATCH_MP_TAC variant_not_in_sub
            THENL
              [ EXISTS_TAC (--`x:var`--)
                THEN EXISTS_TAC (--`FV1 (u1:'a term1) DIFF {x}`--)
                THEN ASM_REWRITE_TAC[IN_DIFF,IN]
                THEN MATCH_MP_TAC FINITE_DIFF
                THEN REWRITE_TAC[FINITE_FV1],

                EXISTS_TAC (--`y:var`--)
                THEN EXISTS_TAC (--`FV1 (u2:'a term1) DIFF {y}`--)
                THEN ASM_REWRITE_TAC[IN_DIFF,IN]
                THEN MATCH_MP_TAC FINITE_DIFF
                THEN REWRITE_TAC[FINITE_FV1]
              ]
          ]
      ]
   );
(* Soli Deo Gloria!!! *)




val ALPHA1_CHANGE_VAR = store_thm
   ("ALPHA1_CHANGE_VAR",
    (--`!y x s v t:'a term1.
         ~(x IN FV_subst1 s (FV1 t DIFF {v})) /\
         ~(y IN FV_subst1 s (FV1 t DIFF {v})) ==>
         ALPHA1
             (t <[ CONS (v, Var1 x) s)
             (t <[ CONS (v, Var1 y) s)
             [x] [y]`--),
    REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM,IN_DIFF,IN]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC (REWRITE_RULE[AND_IMP_INTRO]
                       (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
                        ALPHA1_SUB))
    THEN EXISTS_TAC (--`[]:var list`--)
    THEN EXISTS_TAC (--`[]:var list`--)
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
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`FV1 (SUB1 (s:^subs) x')`--))
    THENL
      [ POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`x':var`--))
        THENL (* 3 subgoals *)
          [ UNDISCH_LAST_TAC
            THEN REWRITE_TAC[],

            ASM_REWRITE_TAC[],

            POP_ASSUM (REWRITE_THM o SYM)
            THEN REPEAT STRIP_TAC
            THEN REWRITE_TAC[ALPHA1_term_pos,alpha_match]
          ],

        DISCH_THEN (STRIP_ASSUME_TAC o SPEC (--`FV1 (SUB1 (s:^subs) x')`--))
        THENL
          [ POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`x':var`--))
            THENL (* 3 subgoals *)
              [ UNDISCH_LAST_TAC
                THEN REWRITE_TAC[],

                ASM_REWRITE_TAC[],

                POP_ASSUM REWRITE_THM
                THEN STRIP_TAC
                THEN REWRITE_TAC[ALPHA1_term_pos,alpha_match]
              ],

            STRIP_TAC
            THEN COND_CASES_TAC
            THENL
              [ REWRITE_TAC[ALPHA1_term_pos,alpha_match],

                REWRITE_TAC[]
                THEN DEP_REWRITE_TAC[ALPHA1_EXTRANEOUS_CONTEXT]
                THEN ASM_REWRITE_TAC[ALPHA1_REFL]
              ]
          ]
      ]
   );



val obj_SUB_distinct = store_thm
   ("obj_SUB_distinct",
    (--`(!a xs ys x.            ~(Con1 a   = SUB1 ((xs // ys):^subs) x)) /\
        (!t u:'a term1 xs ys x. ~(App1 t u = SUB1 (xs // ys) x)) /\
        (!y u:'a term1 xs ys x. ~(Lam1 y u = SUB1 (xs // ys) x)) /\
        (!a    xs ys x. ~(SUB1 ((xs // ys):^subs) x = Con1 a)) /\
        (!t u:'a term1 xs ys x. ~(SUB1 (xs // ys) x = App1 t u)) /\
        (!y u:'a term1 xs ys x. ~(SUB1 (xs // ys) x = Lam1 y u))`--),
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC_ALL SUB_vsubst_Var1)
    THEN ASM_REWRITE_TAC[term1_distinct2]
   );


val FREE_SUBST = store_thm
   ("FREE_SUBST",
    (--`!(t:'a term1) s. DISJOINT (FV1 t) (BV_subst s) ==> ((t <[ s) = t)`--),
    Induct
    THEN REWRITE_TAC[FV1_def,SUB_term1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[DISJOINT_UNION,term1_one_one]
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
        THEN REWRITE_TAC[FINITE_FV1],

        IMP_RES_TAC FREE_IDENT_SUBST1
        THEN POP_ASSUM REWRITE_THM
        THEN DEP_REWRITE_TAC[variant_ident]
        THEN DEP_REWRITE_TAC[FINITE_DIFF]
        THEN REWRITE_TAC[FINITE_FV1,IN_DIFF,IN]
        THEN MATCH_MP_TAC subst_IDENT1
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN REWRITE_TAC[SUB1]
        THEN COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[],

            IMP_RES_TAC FREE_SUB1
            THEN POP_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[IN_DIFF,IN]
          ]
      ]
   );


val BLOCKED_SUBST = store_thm
   ("BLOCKED_SUBST",
    (--`!t:'a term1 x u.
          (Lam1 x u <[ [x,t]) = Lam1 x u`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SUB_term1_def]
    THEN DEP_REWRITE_TAC[variant_ident]
    THEN DEP_REWRITE_TAC[FINITE_FV_subst1]
    THEN DEP_REWRITE_TAC[FINITE_DIFF]
    THEN REWRITE_TAC[FINITE_FV1]
    THEN DEP_REWRITE_TAC[FV_subst_IDENT1]
    THEN REWRITE_TAC[IN_DIFF,IN]
    THEN CONJ_TAC
    THENL
      [ REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN FIRST_ASSUM REWRITE_THM,

        CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[term1_one_one]
        THEN DEP_REWRITE_TAC[subst_IDENT1]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


val PARTIALLY_BLOCKED_SUBST = store_thm
   ("PARTIALLY_BLOCKED_SUBST",
    (--`!xs ys x y u:'a term1.
         (LENGTH xs = LENGTH ys) ==>
         (Lam1 x u <[ (APPEND xs [x] // APPEND ys [y]) =
          Lam1 x u <[ (xs // ys))`--),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC (hd (rev (CONJUNCTS subst_EQ1)))
    THEN REWRITE_TAC[FV1_def,IN_DIFF,IN]
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
    (--`!t1 t2:'a term1 x y xs ys.
          ALPHA1 t1 t2 (CONS x (CONS x xs)) (CONS y (CONS y ys)) =
          ALPHA1 t1 t2 (CONS x xs) (CONS y ys)`--),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC ALPHA1_FREE_CONTEXT
    THEN REWRITE_TAC[LENGTH,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[vsubst1,SUB1]
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[]
   );


val ALPHA1_INNOCUOUS_SUBST = store_thm
   ("ALPHA1_INNOCUOUS_SUBST",
    (--`!t:'a term1 x y xs ys.
          ~(x IN SL ys) /\
          ALPHA1 (t <[ (APPEND ys [x] // APPEND xs [y])) t xs ys ==>
          ((x = y) \/ ~(x IN FV1 t))`--),
    Induct
    THEN REWRITE_TAC[SUB_term1_def,FV1_def,IN_UNION,IN]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[ALPHA1_term_pos]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THENL
      [ ASM_CASES_TAC (--`(x:var) = v`--)
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_ALL_THM o SYM)
        THEN IMP_RES_TAC ALPHA1_LENGTH
        THEN POP_ASSUM (fn th1 =>
                POP_ASSUM (fn th2 =>
                   ASSUME_TAC th1 THEN MP_TAC th2))
        THEN DEP_REWRITE_TAC[SUB_APPEND_FREE_vsubst1]
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[SUB1,vsubst1]
        THEN REWRITE_TAC[ALPHA1_term_pos]
        THEN REWRITE_TAC[alpha_match_SUB_var]
        THEN STRIP_TAC
        THEN UNDISCH_LAST_TAC
        THEN DEP_REWRITE_TAC[SUB_FREE_vsubst1]
        THEN ASM_REWRITE_TAC[term1_one_one],

        POP_TAC
        THEN UNDISCH_LAST_TAC
        THEN DEFINE_NEW_VAR
                (--`v' = variant v
                           (FV_subst1 ((APPEND ys [x] // APPEND xs [y]):^subs)
                                      (FV1 (t:'a term1) DIFF {v}))`--)
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN DISCH_TAC
        THEN ASM_CASES_TAC (--`(x:var) = v`--)
        THENL
          [ POP_ASSUM REWRITE_THM
            THEN REWRITE_TAC[IN_DIFF,IN],

            FIRST_ASSUM (MP_TAC o
                REWRITE_RULE[SUB1] o
                SPECL[--`x:var`--,--`y:var`--,
                      --`CONS (v':var) xs`--,--`CONS (v:var) ys`--])
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



val ALPHA1_Var1_pos1 = TAC_PROOF(([],
    (--`!xs ys x y t:'a term1 v.
          ~(x = v) /\ ALPHA1 (Var1 v) t (x::xs) (y::ys)
             ==>
          ~(t = Var1 y) /\
          ALPHA1 (Var1 v) t xs ys`--)),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_term_similar
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN UNDISCH_LAST_TAC
    THEN POP_ASSUM (ASSUME_TAC o GSYM)
    THEN REWRITE_TAC[ALPHA1_term_pos]
    THEN REWRITE_TAC[alpha_match]
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[term1_one_one]
   );

val ALPHA1_Var1_pos2 = TAC_PROOF(([],
    (--`!xs ys x y t:'a term1 v.
          ~(y = v) /\ ALPHA1 t (Var1 v) (x::xs) (y::ys)
             ==>
          ~(t = Var1 x) /\
          ALPHA1 t (Var1 v) xs ys`--)),
    ONCE_REWRITE_TAC[ALPHA1_SYM]
    THEN REWRITE_TAC[ALPHA1_Var1_pos1]
   );


val ALPHA1_SWITCH_Var1 = TAC_PROOF(([],
    (--`!xs xs' ys ys' x y u v.
          (LENGTH xs = LENGTH xs') /\
          (LENGTH xs' = LENGTH ys) /\
          (LENGTH ys = LENGTH ys') /\
          ALPHA1 (SUB1 ((APPEND xs [x] // APPEND xs' [y]) :^subs) u)
                     (Var1 v) xs' ys /\
          ALPHA1 (Var1 u)
                     (SUB1 ((APPEND ys [y] // APPEND ys' [x]) :^subs) v) xs ys'
             ==>
          ALPHA1 ((Var1 u):'a term1)
                     (Var1 v) (APPEND xs [x]) (APPEND ys [y])`--)),
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
        THEN REWRITE_TAC[ALPHA1_term_pos]
        THEN REWRITE_TAC[alpha_match_SUB_var]
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN ASM_REWRITE_TAC[term1_one_one,LENGTH],

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
        THEN X_GEN_TAC (--`x1:var`--)
        THEN X_GEN_TAC (--`x2:var`--)
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
          [ REWRITE_TAC[ALPHA1_term_pos]
            THEN REWRITE_TAC[alpha_match_SUB_var]
            THEN ASM_REWRITE_TAC[LENGTH,LENGTH_APPEND,vsubst1,SUB1],

            REWRITE_TAC[ALPHA1_term_pos]
            THEN REWRITE_TAC[alpha_match_SUB_var]
            THEN REWRITE_TAC[vsubst1,SUB1]
            THEN ASM_REWRITE_TAC[term1_one_one],

            REWRITE_TAC[ALPHA1_term_pos]
            THEN REWRITE_TAC[alpha_match_SUB_var]
            THEN REWRITE_TAC[vsubst1,SUB1]
            THEN ASM_REWRITE_TAC[term1_one_one],

            REPEAT STRIP_TAC
            THEN IMP_RES_THEN IMP_RES_TAC ALPHA1_Var1_pos1
            THEN IMP_RES_THEN IMP_RES_TAC ALPHA1_Var1_pos2
            THEN REWRITE_TAC[ALPHA1_term_pos]
            THEN REWRITE_TAC[alpha_match]
            THEN EVERY_ASSUM (REWRITE_THM o GSYM)
            THEN REWRITE_TAC[GSYM ALPHA1_term_pos]
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN EXISTS_TAC (--`xs':var list`--)
            THEN EXISTS_TAC (--`ys':var list`--)
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );




val ALPHA1_SWITCH_LEMMA = TAC_PROOF(([],
    (--`!t3 t2:'a term1 xs' ys.
          ALPHA1 t3 t2 xs' ys ==>
          (!t1 x y xs ys'.
            (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
            (t3 = (t1 <[ (APPEND xs [x] // APPEND xs' [y]))) /\
            ALPHA1 t1 (t2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
             ==>
            ALPHA1 t1 t2 (APPEND xs [x]) (APPEND ys [y]))`--)),
    rule_induct ALPHA1_strong_ind
    THEN REPEAT STRIP_TAC
    THEN UNDISCH_LAST_TAC
    THEN UNDISCH_LAST_TAC
    THENL (* 4 subgoals *)
      [ STRIP_ASSUME_TAC (SPEC (--`t1:'a term1`--) term1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_term1_def]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[term1_distinct2,obj_SUB_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[term1_one_one]
        THEN DISCH_THEN (REWRITE_THM o SYM)
        THEN REWRITE_TAC[ALPHA1_term_pos]
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[LENGTH_APPEND,LENGTH],


        STRIP_ASSUME_TAC (SPEC (--`t1:'a term1`--) term1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_term1_def]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[term1_distinct2]
        (* one subgoal *)
        THEN REPEAT DISCH_TAC
        THEN MATCH_MP_TAC ALPHA1_SWITCH_Var1
        THEN EXISTS_TAC (--`xs:var list`--)
        THEN EXISTS_TAC (--`ys':var list`--)
        THEN IMP_RES_TAC alpha_match_LENGTH
        THEN ASM_REWRITE_TAC[]
        THEN POP_TAC
        THEN UNDISCH_LAST_TAC
        THEN FIRST_ASSUM (REWRITE_THM o SYM)
        THEN ASM_REWRITE_TAC[ALPHA1_term_pos],


        STRIP_ASSUME_TAC (SPEC (--`t1':'a term1`--) term1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_term1_def]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[term1_distinct2,obj_SUB_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[term1_one_one]
        THEN STRIP_TAC
        THEN REWRITE_TAC[ALPHA1_term_pos]
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        STRIP_ASSUME_TAC (SPEC (--`t1:'a term1`--) term1_cases)
        (* four subgoals *)
        THEN POP_ASSUM REWRITE_THM
        THEN REWRITE_TAC[SUB_term1_def]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[term1_distinct2,obj_SUB_distinct]
        (* one subgoal *)
        THEN REWRITE_TAC[term1_one_one]
        THEN STRIP_TAC
        THEN REWRITE_TAC[ALPHA1_term_pos]
        THEN DISCH_TAC
        THEN REWRITE_TAC[GSYM (CONJUNCT2 APPEND)]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN EXISTS_TAC
             (--`CONS (variant y
                         (FV_subst1 ((APPEND ys [y'] // APPEND ys' [x']):^subs)
                                  (FV1 (u2:'a term1) DIFF {y})))
                              ys'`--)
        THEN ASM_REWRITE_TAC[LENGTH,APPEND,vsubst1,SL,IN]
      ]
   );


val ALPHA1_SWITCH = store_thm
   ("ALPHA1_SWITCH",
    (--`!t1 t2:'a term1 xs xs' ys ys' x y.
          (LENGTH xs = LENGTH xs') /\ (LENGTH ys = LENGTH ys') /\
          ALPHA1 (t1 <[ (APPEND xs [x] // APPEND xs' [y])) t2 xs' ys /\
          ALPHA1 t1 (t2 <[ (APPEND ys [y] // APPEND ys' [x])) xs ys'
            ==>
          ALPHA1 t1 t2 (APPEND xs [x]) (APPEND ys [y])`--),
    REPEAT STRIP_TAC
    THEN (MATCH_MP_TAC o
                REWRITE_RULE[AND_IMP_INTRO] o
                CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
                   ALPHA1_SWITCH_LEMMA
    THEN EXISTS_TAC (--`(t1:'a term1) <[ (APPEND xs [x] // APPEND xs' [y])`--)
    THEN EXISTS_TAC (--`xs':var list`--)
    THEN EXISTS_TAC (--`ys':var list`--)
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA1_Lam_subst = store_thm
   ("ALPHA1_Lam_subst",
    (--`!t:'a term1 t1 t2 x y.
         ALPHA1 (Lam1 x t1) (Lam1 y t2) [] [] ==>
         ALPHA1 (t1 <[ [x, t]) (t2 <[ [y, t]) [] []`--),
    REWRITE_TAC[ALPHA1_term_pos]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN IMP_RES_TAC ALPHA1_SUB
    THEN POP_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[ALPHA1_subst]
    THEN REWRITE_TAC[alpha_match]
    THEN REWRITE_TAC[SUB1]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA1_REFL]
   );


val ALPHA1_Lam_one_one = store_thm
   ("ALPHA1_Lam_one_one",
    (--`!t1 t2:'a term1 x y.
         ALPHA1 (Lam1 x t1) (Lam1 y t2) [] [] =
         (ALPHA1 (t1 <[ [x, Var1 y]) t2 [] [] /\
          ALPHA1 t1 (t2 <[ [y, Var1 x]) [] [])`--),
    REPEAT GEN_TAC
    THEN EQ_TAC
    THENL
      [ STRIP_TAC
        THEN IMP_RES_THEN (MP_TAC o SPEC (--`Var1 x :'a term1`--))
                    ALPHA1_Lam_subst
        THEN IMP_RES_THEN (MP_TAC o SPEC (--`Var1 y :'a term1`--))
                    ALPHA1_Lam_subst
        THEN REWRITE_TAC[subst_SAME_ONE1]
        THEN REPEAT (DISCH_THEN REWRITE_THM),

        REWRITE_TAC[ALPHA1_term_pos]
        THEN REPEAT STRIP_TAC
        THEN ONCE_REWRITE_TAC[GSYM (CONJUNCT1 APPEND)]
        THEN MATCH_MP_TAC ALPHA1_SWITCH
        THEN EXISTS_TAC (--`[]:var list`--)
        THEN EXISTS_TAC (--`[]:var list`--)
        THEN ASM_REWRITE_TAC[LENGTH,APPEND,vsubst1]
      ]
   );



(* ========================================================== *)
(* Now we define the alpha-equivalence predicates themselves. *)
(* ========================================================== *)


val ALPHA =
    new_definition ("ALPHA",
    (--`ALPHA (t1:'a term1) t2 = ALPHA1 t1 t2 [] []`--));


val ALPHA_term = store_thm
   ("ALPHA_term",
    (--`!t1 t2:'a term1. ALPHA t1 t2 = ALPHA1 t1 t2 [] []`--),
    REWRITE_TAC[ALPHA]
   );


val ALPHA_HEIGHT = store_thm
   ("ALPHA_HEIGHT",
    (--`!t1 t2:'a term1. ALPHA t1 t2 ==>
                         (HEIGHT1 t1 = HEIGHT1 t2)`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_HEIGHT]
   );


val ALPHA_term_similar = store_thm
   ("ALPHA_term_similar",
    (--`(!a t. ALPHA (Con1 a) t ==> (t = Con1 a :'a term1)) /\
        (!x t. ALPHA (Var1 x) t ==> (?y. t = Var1 y :'a term1)) /\
        (!t1 u1 t. ALPHA (App1 t1 u1) t ==>
                   (?t2 u2. t = App1 t2 u2 :'a term1)) /\
        (!x1 u1 t. ALPHA (Lam1 x1 u1) t ==>
                   (?x2 u2. t = Lam1 x2 u2 :'a term1))`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_term_similar]
   );



val ALPHA_REFL = store_thm
   ("ALPHA_REFL",
    (--`!t:'a term1. ALPHA t t`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_REFL]
   );


val ALPHA_SYM = store_thm
   ("ALPHA_SYM",
    (--`!t1 t2:'a term1. ALPHA t1 t2 = ALPHA t2 t1`--),
    REWRITE_TAC[ALPHA_term]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[ALPHA1_SYM]))
    THEN REFL_TAC
   );


val ALPHA_TRANS = store_thm
   ("ALPHA_TRANS",
    (--`!t1 t2 t3:'a term1. ALPHA t1 t2 /\ ALPHA t2 t3 ==> ALPHA t1 t3`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_TRANS]
   );


val ALPHA_term_pos = store_thm
   ("ALPHA_term_pos",
    (--`(!a b.
          ALPHA (Con1 a:'a term1) (Con1 b) = (a = b)) /\
        (!x y.
          ALPHA (Var1 x:'a term1) (Var1 y) = (x = y)) /\
        (!t1 t2 u1 u2.
          ALPHA (App1 t1 u1:'a term1) (App1 t2 u2) =
          ALPHA t1 t2 /\ ALPHA u1 u2) (* /\
        (!x1 x2 u1 u2.
          ALPHA (Lam1 x1 u1:'a term1) (Lam1 x2 u2) =
          ALPHA1 u1 u2 [x1] [x2]) *)`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_term_pos,alpha_match]
   );


val ALPHA_Lam = store_thm
   ("ALPHA_Lam",
    (--`!x u1 u2:'a term1.
          ALPHA (Lam1 x u1) (Lam1 x u2) = ALPHA u1 u2`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_term_pos]
    THEN REPEAT GEN_TAC
    THEN MATCH_MP_TAC ALPHA1_FREE_CONTEXT
    THEN REWRITE_TAC[vsubst1,SUB1]
    THEN REPEAT STRIP_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_term_neg = store_thm
   ("ALPHA_term_neg",
    (--`(!a x.     ALPHA (Con1 a) (Var1 x   :'a term1) = F) /\
        (!a t u.   ALPHA (Con1 a) (App1 t u :'a term1) = F) /\
        (!a y u.   ALPHA (Con1 a) (Lam1 y u :'a term1) = F) /\
        (!x a.     ALPHA (Var1 x) (Con1 a   :'a term1) = F) /\
        (!x t u.   ALPHA (Var1 x) (App1 t u :'a term1) = F) /\
        (!x y u.   ALPHA (Var1 x) (Lam1 y u :'a term1) = F) /\
        (!t u a.   ALPHA (App1 t u) (Con1 a :'a term1) = F) /\
        (!t u x.   ALPHA (App1 t u) (Var1 x :'a term1) = F) /\
        (!t u y v. ALPHA (App1 t u) (Lam1 y v :'a term1) = F) /\
        (!y u a.   ALPHA (Lam1 y u) (Con1 a :'a term1) = F) /\
        (!y u x.   ALPHA (Lam1 y u) (Var1 x :'a term1) = F) /\
        (!y v t u. ALPHA (Lam1 y v) (App1 t u :'a term1) = F)`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_term_neg]
   );


(* --------------------------------------------------------------------- *)
(* We claim that ALPHA is a binary relation on the term language         *)
(* which is                                                              *)
(*  1) reflexive                                                         *)
(*  2) symmetric                                                         *)
(*  3) transitive                                                        *)
(*  4) compatible (in the sense of Barendregt, Definition 3.1.1, pg 50   *)
(* --------------------------------------------------------------------- *)



val ALPHA_FV = store_thm
   ("ALPHA_FV",
    (--`!t1 t2:'a term1. ALPHA t1 t2 ==> (FV1 t1 = FV1 t2)`--),
    REWRITE_TAC[ALPHA_term]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA1_SYM
    THEN IMP_RES_TAC ALPHA1_FV
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
     --`ALPHA1_subst xs ys xs' ys' t1 t2 s1 (s2:^subs) =
        (LENGTH xs' = LENGTH ys') /\
        (!x y. (x IN t1) /\ (y IN t2) /\
               alpha_match xs ys x y ==>
               ALPHA1 (SUB1 s1 x) (SUB1 s2 y) xs' ys')`--);
*)

val ALPHA_subst =
    new_definition
    ("ALPHA_subst",
     --`ALPHA_subst t s1 (s2:^subs) =
        (!x. (x IN t) ==>
               ALPHA (SUB1 s1 x) (SUB1 s2 x))`--);


val ALPHA_SUB_CONTEXT = store_thm
   ("ALPHA_SUB_CONTEXT",
    (--`!t1 t2:'a term1 s1 s2.
          ALPHA t1 t2 /\
          ALPHA_subst (FV1 t1) s1 s2 ==>
          ALPHA (t1 <[ s1) (t2 <[ s2)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA_FV
    THEN REWRITE_ALL_TAC[ALPHA_term]
    THEN (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o
                     CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
                    ALPHA1_SUB
    THEN EXISTS_TAC (--`[]:var list`--)
    THEN EXISTS_TAC (--`[]:var list`--)
    THEN ASM_REWRITE_TAC[]
    THEN UNDISCH_ALL_TAC
    THEN REWRITE_TAC[ALPHA_subst,ALPHA1_subst]
    THEN REWRITE_TAC[ALPHA_term,alpha_match]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_SUB = store_thm
   ("ALPHA_SUB",
    (--`!t1 t2 s:^subs. ALPHA t1 t2 ==>
                        ALPHA (t1 <[ s) (t2 <[ s)`--),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC ALPHA_SUB_CONTEXT
    THEN ASM_REWRITE_TAC[ALPHA_subst,ALPHA_REFL]
   );



val ALPHA_CHANGE_VAR = store_thm
   ("ALPHA_CHANGE_VAR",
    (--`!y x s:^subs v t:'a term1.
         ~(x IN FV_subst1 s (FV1 t DIFF {v})) /\
         ~(y IN FV_subst1 s (FV1 t DIFF {v})) ==>
         ALPHA (Lam1 x (t <[ CONS (v, Var1 x) s))
               (Lam1 y (t <[ CONS (v, Var1 y) s))`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[ALPHA_term,ALPHA1_term_pos]
    THEN MATCH_MP_TAC ALPHA1_CHANGE_VAR
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_CHANGE_ONE_VAR = store_thm
   ("ALPHA_CHANGE_ONE_VAR",
    (--`!x v t:'a term1.
         ~(x IN (FV1 t DIFF {v})) ==>
         ALPHA (Lam1 x (t <[ [v, Var1 x]))
               (Lam1 v t)`--),
    REPEAT STRIP_TAC
    THEN MP_TAC (SPECL [--`v:var`--,--`x:var`--,--`[]:^subs`--,
                        --`v:var`--,--`t:'a term1`--]
                     ALPHA_CHANGE_VAR)
    THEN REWRITE_TAC[FV_subst_NIL1]
    THEN UNDISCH_ALL_TAC
    THEN REWRITE_TAC[IN_DIFF,IN]
    THEN DISCH_THEN REWRITE_THM
    THEN DEP_ONCE_REWRITE_TAC[SPECL[--`t:'a term1`--,--`[v,Var1 v:'a term1]`--]
                                    subst_IDENT1]
    THEN GEN_TAC
    THEN REWRITE_TAC[SUB1]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_SWITCH = store_thm
   ("ALPHA_SWITCH",
    (--`!t1 t2:'a term1 x y.
          ALPHA (t1 <[ [x,Var1 y]) t2 /\
          ALPHA t1 (t2 <[ [y,Var1 x])
            ==>
          ALPHA1 t1 t2 [x] [y]`--),
    REWRITE_TAC[ALPHA_term]
    THEN REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC[GSYM (CONJUNCT1 APPEND)]
    THEN MATCH_MP_TAC ALPHA1_SWITCH
    THEN EXISTS_TAC (--`[]:var list`--)
    THEN EXISTS_TAC (--`[]:var list`--)
    THEN ASM_REWRITE_TAC[APPEND,vsubst1]
   );


val ALPHA_Lam_one_one = store_thm
   ("ALPHA_Lam_one_one",
    (--`!t1 t2:'a term1 x y.
         ALPHA (Lam1 x t1) (Lam1 y t2) =
         (ALPHA (t1 <[ [x, Var1 y]) t2 /\
          ALPHA t1 (t2 <[ [y, Var1 x]))`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_Lam_one_one]
   );

val ALPHA_Lam_subst = store_thm
   ("ALPHA_Lam_subst",
    (--`!t1 t2 x y t:'a term1.
         ALPHA (Lam1 x t1) (Lam1 y t2) ==>
         (ALPHA (t1 <[ [x, t]) (t2 <[ [y, t]))`--),
    REWRITE_TAC[ALPHA_term,ALPHA1_Lam_subst]
   );



val _ = export_theory();

val _ = print_theory_to_file "-" "alpha.lst";

val _ = html_theory "alpha";

val _ = print_theory_size();
