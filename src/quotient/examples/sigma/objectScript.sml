open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Embedding objects as a foundational layer, according to               *)
(* Abadi and Cardelli, "A Theory of Objects."                            *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "object";
val _ = ParseExtras.temp_loose_equality()


(* In interactive sessions, do:

app load ["combinTheory", "listTheory",
          "arithmeticTheory", "numTheory", "prim_recTheory",
          "pairTheory", "pairLib", "pred_setTheory",
          "dep_rewrite", "more_listTheory", "more_setTheory",
          "variableTheory",
          "bossLib", "MutualIndThen"];

*)

open combinTheory;
open listTheory;
open arithmeticTheory numTheory prim_recTheory;
open pairTheory pairLib pred_setTheory;
open dep_rewrite;
open more_listTheory;
open more_setTheory;
open variableTheory;
open bossLib;
open Mutual;


open tactics;



(* --------------------------------------------------------------------- *)
(* Create datatypes for objects, methods, and method dictionaries.       *)
(* --------------------------------------------------------------------- *)


val _ = Hol_datatype

       (* obj1 ::= x | [li=mi] i in 1..n |  a.l | a.l:=m *)

        ` obj1  = OVAR1 of var
                | OBJ1 of (string # method1) list
                | INVOKE1 of obj1 => string
                | UPDATE1 of obj1 => string => method1 ;

       (* method ::= sigma(x)b *)

          method1 = SIGMA1 of var => obj1 `

handle e => Raise e;


val obj1_distinct = theorem "obj1_distinct";
val obj1_one_one = theorem "obj1_11";
val obj1_cases = theorem "obj1_nchotomy";
val obj1_case_cong = theorem "obj1_case_cong";


(* val method1_distinct = theorem "method1_distinct"; *)
val method1_one_one = theorem "method1_11";
val method1_cases = theorem "method1_nchotomy";
val method1_case_cong = theorem "method1_case_cong";


val object1_induct = theorem "obj1_induction";
val object1_Axiom = theorem "obj1_Axiom";

val object1_distinct = LIST_CONJ[obj1_distinct,list_distinct];
val object1_distinct = save_thm("object1_distinct",
                         CONJ object1_distinct (GSYM object1_distinct));
val object1_one_one  = save_thm("object1_one_one",
                         LIST_CONJ[obj1_one_one,list_11,CLOSED_PAIR_EQ,
                                   method1_one_one]);



(* Abbreviations for the other two types, dict(ionary) and entry (in a dict) *)
val dict1  =  ty_antiq( ==`:(string # method1) list`== );
val entry1 =  ty_antiq( ==`:string # method1`== );
val subs1  =  ty_antiq( ==`:(var # obj1) list`== );


val object1_cases = store_thm
   ("object1_cases",
    “(!a. (?x. a = OVAR1 x) \/
             (?d. a = OBJ1 d) \/
             (?b l. a = INVOKE1 b l) \/
             (?b l m. a = UPDATE1 b l m)) /\
        (!d:^dict1. (?e d'. d = CONS e d') \/
                   (d = NIL)) /\
        (!e:^entry1. (?l m. e = (l,m))) /\
        (!m. (?x a. m = SIGMA1 x a))”,
    REWRITE_TAC[obj1_cases, ABS_PAIR_THM, method1_cases]
    THEN GEN_TAC
    THEN STRIP_ASSUME_TAC (ISPEC “d:^dict1” list_CASES)
    THEN ASM_REWRITE_TAC[GSYM list_distinct]
    THEN EXISTS_TAC “h:^entry1”
    THEN EXISTS_TAC “t:^dict1”
    THEN REFL_TAC
   );

val [obj1_cases, dict1_cases, entry1_cases, method1_cases]
    = CONJUNCTS object1_cases;

val _ = save_thm ("obj1_cases", obj1_cases);
val _ = save_thm ("dict1_cases", dict1_cases);
val _ = save_thm ("entry1_cases", entry1_cases);
val _ = save_thm ("method1_cases", method1_cases);



(* =================================================================== *)
(* We want to do an induction on the height of these object expression *)
(* trees; because the structural induction as defined is not powerful  *)
(* enough to really do some jobs.  Instead, we want to do complete     *)
(* numerical induction on the height of the tree.  So we need to be    *)
(* able to measure the height of the tree!                             *)
(* =================================================================== *)


val MAX =
    new_infixr_definition
    ("MAX",
     “$MAX x y = (if x < y then y else x)”,
     490);


val LESS_EQ_MAX = store_thm
   ("LESS_EQ_MAX",
    “(!x y. x <= x MAX y) /\ (!x y. y <= x MAX y)”,
    RW_TAC arith_ss [MAX]
   );

val MAX_SUC = store_thm
   ("MAX_SUC",
    “!x y. (SUC x MAX SUC y) = SUC(x MAX y)”,
    RW_TAC arith_ss [MAX]
   );

val MAX_LESS_EQ = store_thm
   ("MAX_LESS_EQ",
    “!x y z. ((x MAX y) <= z) = ((x <= z) /\ (y <= z))”,
    RW_TAC arith_ss [MAX]
   );



Definition HEIGHT1_def:
    (HEIGHT_obj1 (OVAR1 x)       = 0)                                        /\
    (HEIGHT_obj1 (OBJ1 d)        = SUC (HEIGHT_dict1 d))                     /\
    (HEIGHT_obj1 (INVOKE1 a l)   = SUC (HEIGHT_obj1 a))                      /\
    (HEIGHT_obj1 (UPDATE1 a l m) = SUC (HEIGHT_obj1 a MAX HEIGHT_method1 m))
     /\
    (HEIGHT_dict1 (CONS e d)     = SUC (HEIGHT_entry1 e MAX HEIGHT_dict1 d)) /\
    (HEIGHT_dict1 (NIL)          = 0)
     /\
    (HEIGHT_entry1 (l, m)        = SUC (HEIGHT_method1 m))
     /\
    (HEIGHT_method1 (SIGMA1 x a) = SUC (HEIGHT_obj1 a))
End


val HEIGHT_LESS_EQ_ZERO1 = store_thm
   ("HEIGHT_LESS_EQ_ZERO1",
    “(!a. (HEIGHT_obj1 a <= 0) = (?x. a = OVAR1 x)) /\
        (!d. (HEIGHT_dict1 d <= 0) = (d = NIL)) /\
        (!e. (HEIGHT_entry1 e <= 0) = F) /\
        (!m. (HEIGHT_method1 m <= 0) = F)”,
    MUTUAL_INDUCT_THEN object1_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[HEIGHT1_def]
    THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,LESS_EQ_REFL]
    THEN REWRITE_TAC[object1_distinct]
    THEN REWRITE_TAC[object1_one_one]
    THEN EXISTS_TAC “v:var”
    THEN REWRITE_TAC[]
   );



(* --------------------------------------------------------------------- *)
(* Definition of free variables.                                         *)
(* --------------------------------------------------------------------- *)

Definition FV_object1_def:
    (FV_obj1 (OVAR1 x)        = {x})                                /\
    (FV_obj1 (OBJ1 d)         = FV_dict1 d)                         /\
    (FV_obj1 (INVOKE1 a l)    = FV_obj1 a)                          /\
    (FV_obj1 (UPDATE1 a l m)  = FV_obj1 a UNION FV_method1 m)
     /\
    (FV_dict1 (CONS e es)     = FV_entry1 e UNION FV_dict1 es)      /\
    (FV_dict1 (NIL)           = {})
     /\
    (FV_entry1 (l, m)         = FV_method1 m)
     /\
    (FV_method1 (SIGMA1 y b)  = FV_obj1 b DIFF {y})
End



val FINITE_FV_object1 = store_thm
   ("FINITE_FV_object1",
    “(!a. FINITE (FV_obj1 a)) /\
        (!d. FINITE (FV_dict1 d)) /\
        (!e. FINITE (FV_entry1 e)) /\
        (!m. FINITE (FV_method1 m))”,
    MUTUAL_INDUCT_THEN object1_induct ASSUME_TAC
    THEN REWRITE_TAC[FV_object1_def]
    THEN ASM_REWRITE_TAC[FINITE_INSERT,FINITE_EMPTY,FINITE_UNION]
    THEN GEN_TAC
    THEN MATCH_MP_TAC FINITE_DIFF
    THEN ASM_REWRITE_TAC[]
   );



(* --------------------------------------------------------------------- *)
(* Definition of proper substitution.                                    *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Application of a substitution to a single variable.                   *)
(* --------------------------------------------------------------------- *)

val SUB1_def =
    Define
    `(SUB1 (CONS p s) y = let (x,c) = p in
                                (if y = x then c else SUB1 s y)) /\
     (SUB1 NIL y = OVAR1 y)`;

val SUB1 = store_thm
   ("SUB1",
    “(!y. SUB1 [] y = OVAR1 y) /\
        (!y x c s. SUB1 ((x,c) :: s) y = (if y = x then c else SUB1 s y))”,
    MP_TAC SUB1_def
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN DISCH_THEN REWRITE_THM
    THEN REWRITE_TAC[FST,SND]
   );


(* Variable-for-variable substitutions *)

Definition vsubst1_def:
        ($// NIL ys = NIL) /\
        ($// (CONS (x:var) xs) ys = (if ys = [] then [] else
                                                CONS (x, OVAR1 (HD ys))
                                                     ($// xs (TL ys))))
End

val _ = add_infix("//", 150, NONASSOC);


val vsubst1 = store_thm
   ("vsubst1",
    “(!ys. [] // ys = []) /\
        (!xs. xs // [] = []) /\
        (!xs ys x y. (CONS x xs) // (CONS y ys) =
                      CONS (x,OVAR1 y) (xs // ys))”,
    REWRITE_TAC[vsubst1_def]
    THEN CONJ_TAC
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[vsubst1_def],

        REWRITE_TAC[NOT_CONS_NIL,HD,TL]
      ]
   );


val SUB_vsubst_OVAR1 = store_thm
   ("SUB_vsubst_OVAR1",
    “!xs ys x. ?y. SUB1 (xs // ys) x = OVAR1 y”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[vsubst1,SUB1]
    THENL
      [ GEN_TAC
        THEN EXISTS_TAC “x:var”
        THEN REFL_TAC,

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN REPEAT GEN_TAC
        THENL
          [ EXISTS_TAC “x':var”
            THEN REFL_TAC,

            POP_ASSUM (fn th => ALL_TAC)
            THEN COND_CASES_TAC
            THENL
              [ EXISTS_TAC “x':var”
                THEN REFL_TAC,

                FIRST_ASSUM (STRIP_ASSUME_TAC o
                             SPECL[“ys:var list”,“x'':var”])
                THEN EXISTS_TAC “y:var”
                THEN FIRST_ASSUM ACCEPT_TAC
              ]
          ]
      ]
   );


val IN_FV_SUB_vsubst1 = store_thm
   ("IN_FV_SUB_vsubst1",
    “!xs ys x y.
         (y IN FV_obj1 (SUB1 (xs // ys) x)) =
         (SUB1 (xs // ys) x = OVAR1 y)”,
    REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC_ALL SUB_vsubst_OVAR1)
    THEN ASM_REWRITE_TAC[FV_object1_def,object1_one_one,IN]
    THEN EQ_TAC
    THEN DISCH_THEN REWRITE_THM
   );


val SUB_APPEND_vsubst1 = store_thm
   ("SUB_APPEND_vsubst1",
    “!xs ys xs' ys' x.
         (LENGTH xs = LENGTH ys) ==>
         (SUB1 (APPEND xs xs' // APPEND ys ys') x =
          (if (x IN SL xs) then SUB1 (xs // ys) x else SUB1 (xs' // ys') x))”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[SL,IN]
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,SUC_NOT]
        THEN REWRITE_TAC[APPEND],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,NOT_SUC]
        THEN POP_TAC
        THEN REWRITE_TAC[INV_SUC_EQ]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_TAC[APPEND,vsubst1,SUB1]
        THEN COND_CASES_TAC
        THENL
          [ POP_ASSUM REWRITE_THM,

            FIRST_ASSUM (REWRITE_THM o GSYM)
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );


val SUB_FREE_vsubst1 = store_thm
   ("SUB_FREE_vsubst1",
    “!xs ys x.
         ~(x IN SL xs) ==>
         (SUB1 (xs // ys) x = OVAR1 x)”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[SL,IN]
    THENL
      [ REWRITE_TAC[vsubst1,SUB1],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[vsubst1,SUB1]
        THEN POP_TAC
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN UNDISCH_LAST_TAC
        THEN FIRST_ASSUM (REWRITE_THM o GSYM)
        THEN ASM_REWRITE_TAC[]
      ]
   );

val SUB_APPEND_FREE_vsubst1 = store_thm
   ("SUB_APPEND_FREE_vsubst1",
    “!xs ys xs' ys' x.
         (LENGTH xs = LENGTH ys) /\ ~(x IN SL xs) ==>
         (SUB1 (APPEND xs xs' // APPEND ys ys') x = SUB1 (xs' // ys') x)”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[SL,IN]
    THENL
      [ LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,SUC_NOT]
        THEN REWRITE_TAC[APPEND],

        GEN_TAC
        THEN LIST_INDUCT_TAC
        THEN REWRITE_TAC[LENGTH,NOT_SUC]
        THEN POP_TAC
        THEN REWRITE_TAC[INV_SUC_EQ,DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC
        THEN REWRITE_TAC[APPEND,vsubst1,SUB1]
        THEN UNDISCH_LAST_TAC
        THEN FIRST_ASSUM REWRITE_THM
        THEN DISCH_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );



(* --------------------------------------------------------------------- *)
(* Definition of bound variables of a substitution:                      *)
(*   This consists of the variables on the LHS of each pair              *)
(*   Only these variables are changed by a substitution                  *)
(* --------------------------------------------------------------------- *)

val BV_subst_def =
    Define
       `(BV_subst NIL = {}) /\
        (BV_subst (CONS (x:(var # 'a)) xs) = (FST x INSERT BV_subst xs))`;


val FINITE_BV_subst = store_thm
   ("FINITE_BV_subst",
    “!s:(var # 'a)list. FINITE (BV_subst s)”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[BV_subst_def]
    THEN ASM_REWRITE_TAC[FINITE_EMPTY,FINITE_INSERT]
   );


(* --------------------------------------------------------------------- *)
(* Definition of free variables of a substitution:                       *)
(*   This involves also the source or bound variables to be the targets  *)
(*   of the substitution; else the result is infinite                    *)
(* --------------------------------------------------------------------- *)

val FV_subst1 =
    new_definition("FV_subst1",
    “FV_subst1 s xs = UNION_SET (IMAGE (FV_obj1 o SUB1 s) xs)”);



val FINITE_FV_subst1 = store_thm
   ("FINITE_FV_subst1",
    “!x s. FINITE s ==> FINITE (FV_subst1 x s)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[FV_subst1]
    THEN DEP_REWRITE_TAC[FINITE_UNION_SET]
    THEN DEP_REWRITE_TAC[IMAGE_FINITE]
    THEN ASM_REWRITE_TAC[IN_IMAGE]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[o_THM,FINITE_FV_object1]
    THEN MATCH_MP_TAC FINITE_DIFF
    THEN ASM_REWRITE_TAC[]
   );


val FV_subst_EQ1 = store_thm
   ("FV_subst_EQ1",
    “!s1 s2 t.
          (!x. (x IN t) ==> (SUB1 s1 x = SUB1 s2 x)) ==>
          (FV_subst1 s1 t = FV_subst1 s2 t)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC “si:var set”
        THEN FIRST_ASSUM REWRITE_THM
        THEN EXISTS_TAC “x':var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “si:var set”
        THEN FIRST_ASSUM REWRITE_THM
        THEN EXISTS_TAC “x':var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


val FV_subst_IDENT1 = store_thm
   ("FV_subst_IDENT1",
    “!s t. (!x. (x IN t) ==> (SUB1 s x = OVAR1 x)) ==>
              (FV_subst1 s t = t)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ UNDISCH_LAST_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[FV_object1_def,IN]
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “{x:var}”
        THEN REWRITE_TAC[IN]
        THEN EXISTS_TAC “x:var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[FV_object1_def]
      ]
   );


val FV_subst_NIL1 = store_thm
   ("FV_subst_NIL1",
    “!s. FV_subst1 [] s = s”,
    GEN_TAC
    THEN MATCH_MP_TAC FV_subst_IDENT1
    THEN REWRITE_TAC[SUB1]
   );


val FREE_SUB1 = store_thm
   ("FREE_SUB1",
    “!s t.
          DISJOINT t (BV_subst s) ==>
          (!x. (x IN t) ==> (SUB1 s x = OVAR1 x))”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[BV_subst_def]
    THEN REWRITE_TAC[DISJOINT_EMPTY,DISJOINT_INSERT2]
    THEN REPEAT STRIP_TAC
    THENL
      [ REWRITE_TAC[SUB1_def],

        ONCE_REWRITE_TAC[GSYM PAIR]
        THEN REWRITE_TAC[SUB1]
        THEN IMP_RES_TAC IN_NOT_IN
        THEN FIRST_ASSUM REWRITE_THM
        THEN RES_TAC
      ]
   );

val FREE_FV_SUB1 = store_thm
   ("FREE_FV_SUB1",
    “!s t.
          DISJOINT t (BV_subst s) ==>
          (!x. (x IN t) ==> (FV_obj1 (SUB1 s x) = {x}))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC FREE_SUB1
    THEN ASM_REWRITE_TAC[FV_object1_def]
   );


val FREE_IDENT_SUBST1 = store_thm
   ("FREE_IDENT_SUBST1",
    “!s t.
          DISJOINT t (BV_subst s) ==>
          (FV_subst1 s t = t)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC FREE_FV_SUB1
    THEN REWRITE_TAC[FV_subst1]
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM,IN]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ UNDISCH_LAST_TAC
        THEN ASM_REWRITE_TAC[]
        THEN RES_THEN REWRITE_THM
        THEN REWRITE_TAC[IN]
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “{x:var}”
        THEN REWRITE_TAC[IN]
        THEN EXISTS_TAC “x:var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


(* --------------------------------------------------------------------- *)
(* Proper substitution is defined as the distribution on the             *)
(* substitution among subterms, where for the SIGMA1 forms, the          *)
(* bound variable is automatically renamed in order to avoid capture.    *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Naive substitution; not proper; only here for pedagogical reasons.    *)
(* --------------------------------------------------------------------- *)

Definition NSUB_object1_def:
    ($NSUB1o (OVAR1 x) s        = SUB1 s x)                                /\
    ($NSUB1o (OBJ1 d) s         = OBJ1 ($NSUB1d d s))                      /\
    ($NSUB1o (INVOKE1 a l) s    = INVOKE1 ($NSUB1o a s) l)                 /\
    ($NSUB1o (UPDATE1 a l m) s  = UPDATE1 ($NSUB1o a s) l ($NSUB1m m s))
     /\
    ($NSUB1d (CONS e es) s      = CONS ($NSUB1e e s) ($NSUB1d es s))       /\
    ($NSUB1d (NIL) s            = NIL)
     /\
    ($NSUB1e (l, m) s           = (l, ($NSUB1m m s)))
     /\
    ($NSUB1m (SIGMA1 x a) s     = SIGMA1 x ($NSUB1o a s))
End

val _ = map (fn s => add_infix(s,250,LEFT))
            ["NSUB1o","NSUB1d","NSUB1e","NSUB1m"];

(* Printed interactively, we read
- > val NSUB_object1_def =
    |- (!x s. OVAR1 x NSUB1o s = SUB1 s x) /\
       (!d s. OBJ1 d NSUB1o s = OBJ1 (d NSUB1d s)) /\
       (!a l s. INVOKE1 a l NSUB1o s = INVOKE1 (a NSUB1o s) l) /\
       (!a l m s.
          UPDATE1 a l m NSUB1o s = UPDATE1 (a NSUB1o s) l (m NSUB1m s)) /\
       (!e es s. (e::es) NSUB1d s = e NSUB1e s::es NSUB1d s) /\
       (!s. [] NSUB1d s = []) /\ (!l m s. (l,m) NSUB1e s = (l,m NSUB1m s)) /\
       !x a s. SIGMA1 x a NSUB1m s = SIGMA1 x (a NSUB1o s)
    : Thm.thm
*)



(* --------------------------------------------------------------------- *)
(* Proper substitution, including renaming of bound variables.           *)
(* --------------------------------------------------------------------- *)

Definition SUB_object1_def:
    ($SUB1o (OVAR1 x) s        = SUB1 s x)                               /\
    ($SUB1o (OBJ1 d) s         = OBJ1 ($SUB1d d s))                      /\
    ($SUB1o (INVOKE1 a l) s    = INVOKE1 ($SUB1o a s) l)                 /\
    ($SUB1o (UPDATE1 a l m) s  = UPDATE1 ($SUB1o a s) l ($SUB1m m s))
     /\
    ($SUB1d (CONS e es) s      = CONS ($SUB1e e s) ($SUB1d es s))        /\
    ($SUB1d (NIL) s            = NIL)
     /\
    ($SUB1e (l, m) s           = (l, ($SUB1m m s)))
     /\
    ($SUB1m (SIGMA1 y b) s     =
          let y' = variant y (FV_subst1 s (FV_obj1 b DIFF {y}))  in
          SIGMA1 y' ($SUB1o b (CONS (y, OVAR1 y') s)))
End


(* Define the infix substitution operator, <[, with higher precedence *)
(* than the substitution-creation operator //, but lower than CONS:   *)

val _ = add_infix("<[",250,LEFT);

(*
term_grammar();
remove_rules_for_term "<[";
clear_overloads_on "<[";
*)


(* Now overload the substitution operator <[ to refer to any of the  *)
(* object, dict, entry, or method substitution operators defined:    *)

val _ = map (fn t => overload_on("<[", t))
            [“$SUB1o”,“$SUB1d”,“$SUB1e”,“$SUB1m”]
handle e => Raise e;


(* Now, printed interactively, we read
- > val SUB_object1_def =
    |- (!x s. OVAR1 x <[ s = SUB1 s x) /\
       (!d s. OBJ1 d <[ s = OBJ1 (d <[ s)) /\
       (!a l s. INVOKE1 a l <[ s = INVOKE1 (a <[ s) l) /\
       (!a l m s. UPDATE1 a l m <[ s = UPDATE1 (a <[ s) l (m <[ s)) /\
       (!e es s. e::es <[ s = (e <[ s)::(es <[ s)) /\ (!s. [] <[ s = []) /\
       (!l m s. (l,m) <[ s = (l,m <[ s)) /\
       !y b s.
         SIGMA1 y b <[ s =
         (let y' = variant y (FV_subst1 s (FV_obj1 b DIFF {y})) in
            SIGMA1 y' (b <[ (y,OVAR1 y')::s))
    : Thm.thm
*)



val TAUT_PROVE = EQT_ELIM o tautLib.TAUT_CONV;
val OR_IMP = TAUT_PROVE “(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))”;


val subst_EQ1 = store_thm
   ("subst_EQ1",
    “(!a s1 s2. (!x. (x IN FV_obj1 a) ==> (SUB1 s1 x = SUB1 s2 x)) ==>
                   ((a <[ s1) = (a <[ s2))) /\
        (!d s1 s2. (!x. (x IN FV_dict1 d) ==> (SUB1 s1 x = SUB1 s2 x)) ==>
                   ((d <[ s1) = (d <[ s2))) /\
        (!e s1 s2. (!x. (x IN FV_entry1 e) ==> (SUB1 s1 x = SUB1 s2 x)) ==>
                   ((e <[ s1) = (e <[ s2))) /\
        (!m s1 s2. (!x. (x IN FV_method1 m) ==> (SUB1 s1 x = SUB1 s2 x)) ==>
                   ((m <[ s1) = (m <[ s2)))”,
    MUTUAL_INDUCT_THEN object1_induct ASSUME_TAC
    THEN REWRITE_TAC[FV_object1_def,IN_UNION,IN]
    THEN REWRITE_TAC[OR_IMP]
    THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_object1_def]
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    (* 2 subgoals left *)
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        IMP_RES_THEN REWRITE_THM FV_subst_EQ1
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[object1_one_one]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[IN_DIFF,IN]
        THEN FIRST_ASSUM (REWRITE_THM o GSYM)
      ]
   );

val subst_IDENT1 = store_thm
   ("subst_IDENT1",
    “(!a s. (!x. (x IN FV_obj1 a) ==> (SUB1 s x = OVAR1 x)) ==>
               ((a <[ s) = a)) /\
        (!d s. (!x. (x IN FV_dict1 d) ==> (SUB1 s x = OVAR1 x)) ==>
               ((d <[ s) = d)) /\
        (!e s. (!x. (x IN FV_entry1 e) ==> (SUB1 s x = OVAR1 x)) ==>
               ((e <[ s) = e)) /\
        (!m s. (!x. (x IN FV_method1 m) ==> (SUB1 s x = OVAR1 x)) ==>
               ((m <[ s) = m))”,
    MUTUAL_INDUCT_THEN object1_induct ASSUME_TAC
    THEN REWRITE_TAC[FV_object1_def,IN_UNION,IN]
    THEN REWRITE_TAC[OR_IMP]
    THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_object1_def]
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    (* 2 subgoals left *)
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        IMP_RES_THEN REWRITE_THM FV_subst_IDENT1
        THEN DEP_REWRITE_TAC[variant_ident]
        THEN DEP_REWRITE_TAC[FINITE_DIFF]
        THEN REWRITE_TAC[FINITE_FV_object1,IN_DIFF,IN]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN DEP_ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[SUB1]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[IN_DIFF,IN]
        THEN FIRST_ASSUM (REWRITE_THM o GSYM)
      ]
   );

val subst_NIL1 = store_thm
   ("subst_NIL1",
    “(!a: obj1. (a <[ []) = a) /\
        (!d:^dict1. (d <[ []) = d) /\
        (!e:^entry1. (e <[ []) = e) /\
        (!m: method1. (m <[ []) = m)”,
    REPEAT CONJ_TAC
    THEN GEN_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS subst_IDENT1))
    THEN REWRITE_TAC[SUB1]
   );

val subst_SAME_ONE1 = store_thm
   ("subst_SAME_ONE1",
    “(!(a: obj1) x. (a <[ [x,OVAR1 x]) = a) /\
        (!(d:^dict1) x. (d <[ [x,OVAR1 x]) = d) /\
        (!(e:^entry1) x. (e <[ [x,OVAR1 x]) = e) /\
        (!(m: method1) x. (m <[ [x,OVAR1 x]) = m)”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS subst_IDENT1))
    THEN REWRITE_TAC[SUB1]
    THEN GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );

val subst_SAME_TWO1 = store_thm
   ("subst_SAME_TWO1",
    “(!(a: obj1) x t u. (a <[ [x,t; x,u]:^subs1) = (a <[ [x,t])) /\
        (!(d:^dict1) x t u. (d <[ [x,t; x,u]:^subs1) = (d <[ [x,t])) /\
        (!(e:^entry1) x t u. (e <[ [x,t; x,u]:^subs1) = (e <[ [x,t])) /\
        (!(m: method1) x t u. (m <[ [x,t; x,u]:^subs1) = (m <[ [x,t]))”,
    REPEAT STRIP_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS subst_EQ1))
    THEN REWRITE_TAC[SUB1]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[]
   );


val FV_vsubst1 = store_thm
   ("FV_vsubst1",
    “(!a xs ys.
          FV_obj1 a DIFF SL xs SUBSET FV_obj1 (a <[ (xs // ys):^subs1)) /\
        (!d xs ys.
          FV_dict1 d DIFF SL xs SUBSET FV_dict1 (d <[ (xs // ys):^subs1)) /\
        (!e xs ys.
          FV_entry1 e DIFF SL xs SUBSET FV_entry1 (e <[ (xs // ys):^subs1)) /\
        (!m xs ys.
          FV_method1 m DIFF SL xs SUBSET FV_method1 (m <[ (xs // ys):^subs1))
       ”,
    MUTUAL_INDUCT_THEN object1_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SUB_object1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[FV_object1_def,SUB1,EMPTY_DIFF,INSERT_DIFF,SUBSET]
    THEN REWRITE_TAC[UNION_DIFF,UNION_SUBSET]
    THENL
      [ COND_CASES_TAC
        THENL
          [ REWRITE_TAC[SUBSET],

            IMP_RES_TAC SUB_FREE_vsubst1
            THEN ASM_REWRITE_TAC[FV_object1_def,SUBSET_REFL]
          ],

        ASM_REWRITE_TAC[],

        ASM_REWRITE_TAC[],

        POP_ASSUM (MP_TAC o SPEC_ALL)
        THEN POP_ASSUM (MP_TAC o SPEC_ALL)
        THEN REWRITE_TAC[SUBSET_DEF,IN_UNION]
        THEN PROVE_TAC[],

        REWRITE_TAC[DIFFF]
        THEN REWRITE_TAC[DELETE_DIFF_SL]
        THEN REWRITE_TAC[GSYM vsubst1]
        THEN REWRITE_TAC[SUBSET_DELETE]
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC variant_not_in_subset
        THEN DEP_REWRITE_TAC[FINITE_FV_subst1]
        THEN REWRITE_TAC[FINITE_DELETE,FINITE_FV_object1]
        THEN REWRITE_TAC[FV_subst1]
        THEN REWRITE_TAC[SUBSET_DEF,IN_DIFF,SL,IN]
        THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,IN_DELETE]
        THEN REWRITE_TAC[o_THM,DE_MORGAN_THM]
        THEN GEN_TAC
        THEN STRIP_TAC
        THEN EXISTS_TAC “FV_obj1 (SUB1 (xs // ys) x)”
        THEN IMP_RES_TAC SUB_FREE_vsubst1
        THEN ASM_REWRITE_TAC[FV_object1_def,IN]
        THEN EXISTS_TAC “x:var”
        THEN ASM_REWRITE_TAC[EXTENSION,FV_object1_def,IN],

        POP_ASSUM (MP_TAC o SPEC_ALL)
        THEN POP_ASSUM (MP_TAC o SPEC_ALL)
        THEN REWRITE_TAC[SUBSET_DEF,IN_UNION]
        THEN PROVE_TAC[],

        ASM_REWRITE_TAC[]
      ]
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

(* obj1_0 is a null, meaningless object. *)

val obj1_0 = new_definition(
      "obj1_0",
      “obj1_0 = OBJ1 []”);

(* method1_0 is a null, meaningless method. *)

val method1_0 = new_definition(
      "method1_0",
      “method1_0 = SIGMA1 (VAR "" 0) obj1_0”);


val invoke_method1_def = Define
   `invoke_method1 (SIGMA1 x a) o'   = a <[ [x,o']`;


val invoke_dict1_def = Define
   `(invoke_dict1 (CONS e d) o' lb = let ((l:string), m) = e
                                      in (if l = lb then invoke_method1 m o'
                                                    else invoke_dict1 d o' lb))  /\
    (invoke_dict1 (NIL) o' lb       = obj1_0)`
handle e => Raise e;

val invoke_dict1 = store_thm
   ("invoke_dict1",
    “(!l m d o' lb.
          invoke_dict1 (CONS (l, m) d) o' lb =
                        (if l = lb then invoke_method1 m o'
                                   else invoke_dict1 d o' lb)) /\
        (!o' lb. invoke_dict1 (NIL) o' lb = obj1_0)”,
    REWRITE_TAC[invoke_dict1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[]
   );


val invoke1_def = Define
   `(invoke1 (OBJ1 d) lb        = invoke_dict1 d (OBJ1 d) lb)             /\
    (invoke1 (allelse) lb       = obj1_0)`;

val invoke1 = store_thm
   ("invoke1",
    “!d lb. invoke1 (OBJ1 d) lb = invoke_dict1 d (OBJ1 d) lb”,
    REWRITE_TAC[invoke1_def]
   );


val update_dict1_def = Define
   `(update_dict1 (CONS e d) (lb:string) (mth:method1) =
              let (l,m) = (e:^entry1) in
                    (if l = lb then          (update_dict1 d lb mth)
                               else  (CONS e (update_dict1 d lb mth)) ))   /\
    (update_dict1 (NIL) lb mth      = NIL)`;

val update_dict1 = store_thm
   ("update_dict1",
    “(!l m (d:^dict1) lb mth.
          update_dict1 (CONS (l, m) d) lb mth =
                    (if l = lb then               (update_dict1 d lb mth)
                               else  (CONS (l, m) (update_dict1 d lb mth)) ))   /\
        (!lb mth.
          update_dict1 (NIL) lb mth = NIL)”,
    REWRITE_TAC[update_dict1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );



val update1_def = Define
   `(update1 (OBJ1 d) lb mth = OBJ1 (CONS (lb,mth) (update_dict1 d lb mth))) /\
    (update1 (allelse) lb mth = obj1_0)`;

val update1 = store_thm
   ("update1",
    “!d lb mth.
        update1 (OBJ1 d) lb mth =
               OBJ1 (CONS (lb,mth) (update_dict1 d lb mth))”,
    REWRITE_TAC[update1_def]
   );



val _ = export_theory();

val _ = print_theory_to_file "object.lst";

val _ = html_theory "object";

val _ = print_theory_size();
