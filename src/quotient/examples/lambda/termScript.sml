open HolKernel Parse boolLib;


(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* Version 2.2.                                                          *)
(* Date: August 11, 2005                                                 *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Representing the lambda calculus as a new datatype in the HOL logic.  *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "term";


(* In interactive sessions, do:

app load ["listTheory", "pred_setTheory", "pairTheory",
          "arithmeticTheory", "numTheory", "prim_recTheory",
          "dep_rewrite", "more_listTheory", "more_setTheory",
          "variableTheory",
          "pairLib", "numLib", "listLib",
          "tautLib", "bossLib"];

*)

open Psyntax combinTheory;
open listTheory listLib;
open arithmeticTheory numTheory prim_recTheory;
open pairTheory;
open pred_setTheory;
open dep_rewrite more_listTheory more_setTheory variableTheory;
open pairLib;
open numLib;
open bossLib;
open Mutual;


open tactics;



(* --------------------------------------------------------------------- *)
(* Create datatypes for lambda expressions.                              *)
(* --------------------------------------------------------------------- *)


val _ = Hol_datatype

        ` term1 = Con1 of 'a
                | Var1 of var
                | App1 of term1 => term1
                | Lam1 of var => term1 ` ;


val term1_distinct = theorem "term1_distinct";
val term1_one_one = theorem "term1_11";
val term1_cases = theorem "term1_nchotomy";
val term1_case_cong = theorem "term1_case_cong";

val term1_induct = theorem "term1_induction";
val term1_Axiom = theorem "term1_Axiom";

val term1_distinct2 = save_thm("term1_distinct2",
                         CONJ term1_distinct (GSYM term1_distinct));
val _ = save_thm("term1_one_one", term1_one_one);
val _ = save_thm("term1_cases", term1_cases);



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
    (HEIGHT1 (Con1 a)    = 0)                                       /\
    (HEIGHT1 (Var1 x)    = 0)                                       /\
    (HEIGHT1 (App1 t u)  = SUC (HEIGHT1 t MAX HEIGHT1 u)) /\
    (HEIGHT1 (Lam1 x u)  = SUC (HEIGHT1 u))
End


val HEIGHT_LESS_EQ_ZERO1 = store_thm
   ("HEIGHT_LESS_EQ_ZERO1",
    “!t. (HEIGHT1 t <= 0) = ((?a:'a. t = Con1 a) \/ (?x. t = Var1 x))”,
    Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[HEIGHT1_def]
    THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,LESS_EQ_REFL]
    THEN REWRITE_TAC[term1_distinct2]
    THEN REWRITE_TAC[term1_one_one]
    THEN REWRITE_TAC[GSYM EXISTS_REFL]
   );


(* --------------------------------------------------------------------- *)
(* Definition of free variables.                                         *)
(* --------------------------------------------------------------------- *)

val FV1_def = Define
   `(FV1 (Con1 a)        = {})                                 /\
    (FV1 (Var1 x)        = {x})                                /\
    (FV1 (App1 t u)      = FV1 t UNION FV1 u)                  /\
    (FV1 (Lam1 x u)      = FV1 u DIFF {x})`;


val FINITE_FV1 = store_thm
   ("FINITE_FV1",
    “!t:'a term1. FINITE (FV1 t)”,
    Induct
    THEN REWRITE_TAC[FV1_def]
    THEN ASM_REWRITE_TAC[FINITE_INSERT,FINITE_EMPTY,FINITE_UNION]
    THEN GEN_TAC
    THEN MATCH_MP_TAC FINITE_DIFF
    THEN ASM_REWRITE_TAC[]
   );



(* --------------------------------------------------------------------- *)
(* Definition of proper substitution.                                    *)
(* --------------------------------------------------------------------- *)

val subs = ty_antiq( ==`:(var # 'a term1) list`== );


(* --------------------------------------------------------------------- *)
(* Application of a substitution to a single variable.                   *)
(* --------------------------------------------------------------------- *)

val SUB1_def =
    Define
    `(SUB1 (CONS p s) y = let (x, c:'a term1) = p in
                                (if y = x then c else SUB1 s y)) /\
     (SUB1 NIL y = Var1 y)`;

val SUB1 = store_thm
   ("SUB1",
    “(!y. SUB1 [] y = (Var1 y :'a term1)) /\
        (!y x (c :'a term1) s.
          SUB1 ((x,c) :: s) y = (if y = x then c else SUB1 s y))”,
    MP_TAC SUB1_def
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN DISCH_THEN REWRITE_THM
   );


(* Variable-for-variable substitutions *)

Definition vsubst1_def:
  ($// NIL ys = NIL) /\
  ($// (CONS (x:var) xs) ys =
   (if ys = [] then [] else
      CONS (x, (Var1 (HD ys) :'a term1))
           ($// xs (TL ys))))
End

val _ = set_fixity "//" (Infixl 470);


Theorem vsubst1:
   (!ys. [] // ys = []:^subs) /\
   (!xs. xs // [] = []:^subs) /\
   (!xs ys x y.
       (CONS x xs) // (CONS y ys) = CONS (x, Var1 y :'a term1) (xs // ys))
Proof
    REWRITE_TAC[vsubst1_def]
    THEN CONJ_TAC
    THENL
      [ Cases
        THEN REWRITE_TAC[vsubst1_def],

        REWRITE_TAC[NOT_CONS_NIL,HD,TL]
      ]
QED


val SUB_vsubst_Var1 = store_thm
   ("SUB_vsubst_Var1",
    “!xs ys x. ?y. SUB1 (xs // ys) x = Var1 y :'a term1”,
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
         (y IN FV1 (SUB1 (xs // ys) x :'a term1)) =
         (SUB1 (xs // ys) x = Var1 y :'a term1)”,
    REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC_ALL SUB_vsubst_Var1)
    THEN ASM_REWRITE_TAC[FV1_def,term1_one_one,IN]
    THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
   );


val SUB_APPEND_vsubst1 = store_thm
   ("SUB_APPEND_vsubst1",
    “!xs ys xs' ys' x.
         (LENGTH xs = LENGTH ys) ==>
         (SUB1 (APPEND xs xs' // APPEND ys ys') x :'a term1 =
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
         (SUB1 (xs // ys) x = Var1 x :'a term1)”,
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
         (SUB1 (APPEND xs xs' // APPEND ys ys') x =
          SUB1 (xs' // ys') x :'a term1)”,
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

(*
val BV_subst_IDENT = store_thm
   ("BV_subst_IDENT",
    “!s x. ~(x IN (BV_subst s)) ==> (SUB1 s x = Var1 x :'a term1)”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[BV_subst_def,SUB1_def]
    THEN REWRITE_TAC[IN,DE_MORGAN_THM]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN ASM_REWRITE_TAC[]
   );

val BV_vsubst1 = store_thm
   ("BV_vsubst1",
    “!xs ys. (LENGTH xs = LENGTH ys) ==>
                (BV_subst ((xs // ys) :^subs) = SL xs)”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[BV_subst_def,vsubst1,SL]
    THEN GEN_TAC
    THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC,INV_SUC_EQ]
    THEN POP_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[BV_subst_def,vsubst1,FST]
   );
*)

(* --------------------------------------------------------------------- *)
(* Definition of free variables of a substitution:                       *)
(*   This involves also the source or bound variables to be the targets  *)
(*   of the substitution; else the result is infinite                    *)
(* --------------------------------------------------------------------- *)

val FV_subst1 =
    new_definition("FV_subst1",
    “FV_subst1 (s:^subs) xs = UNION_SET (IMAGE (FV1 o SUB1 s) xs)”);



val FINITE_FV_subst1 = store_thm
   ("FINITE_FV_subst1",
    “!t s:^subs. FINITE t ==> FINITE (FV_subst1 s t)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[FV_subst1]
    THEN DEP_REWRITE_TAC[FINITE_UNION_SET]
    THEN DEP_REWRITE_TAC[IMAGE_FINITE]
    THEN ASM_REWRITE_TAC[IN_IMAGE]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[o_THM,FINITE_FV1]
    THEN MATCH_MP_TAC FINITE_DIFF
    THEN ASM_REWRITE_TAC[]
   );


val FV_subst_EQ1 = store_thm
   ("FV_subst_EQ1",
    “!s1:^subs s2 t.
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
      [ EXISTS_TAC “si:var -> bool”
        THEN FIRST_ASSUM REWRITE_THM
        THEN EXISTS_TAC “x':var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “si:var -> bool”
        THEN FIRST_ASSUM REWRITE_THM
        THEN EXISTS_TAC “x':var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );


val FV_subst_IDENT1 = store_thm
   ("FV_subst_IDENT1",
    “!s:^subs t. (!x. (x IN t) ==> (SUB1 s x = Var1 x)) ==>
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
        THEN ASM_REWRITE_TAC[FV1_def,IN]
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC “{x:var}”
        THEN REWRITE_TAC[IN]
        THEN EXISTS_TAC “x:var”
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[FV1_def]
      ]
   );


val FV_subst_NIL1 = store_thm
   ("FV_subst_NIL1",
    “!s. FV_subst1 ([]:^subs) s = s”,
    GEN_TAC
    THEN MATCH_MP_TAC FV_subst_IDENT1
    THEN REWRITE_TAC[SUB1]
   );


val FREE_SUB1 = store_thm
   ("FREE_SUB1",
    “!s:^subs t.
          DISJOINT t (BV_subst s) ==>
          (!x. (x IN t) ==> (SUB1 s x = Var1 x))”,
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
    “!s:^subs t.
          DISJOINT t (BV_subst s) ==>
          (!x. (x IN t) ==> (FV1 (SUB1 s x) = {x}))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC FREE_SUB1
    THEN ASM_REWRITE_TAC[FV1_def]
   );

val FREE_IDENT_SUBST1 = store_thm
   ("FREE_IDENT_SUBST1",
    “!s:^subs t.
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
(* Naive substitution; not proper; will fix later.                       *)
(* This DOES typecheck and create! Compare to PVS.                       *)
(* --------------------------------------------------------------------- *)

val NSUB1_def = xDefine  "NSUB1"
   `($NSUB1 (Con1 (a:'a)) s  = Con1 a)                                  /\
    ($NSUB1 (Var1 x) s       = SUB1 s x)                                /\
    ($NSUB1 (App1 t u) s     = App1 ($NSUB1 t s) ($NSUB1 u s))          /\
    ($NSUB1 (Lam1 x u) s     = Lam1 x ($NSUB1 u s))` ;

val _ = map (fn s => add_infix(s,250,LEFT))
            ["NSUB1"];



(* --------------------------------------------------------------------- *)
(* Proper substitution, including renaming of bound variables.           *)
(* This DOES typecheck and create! Compare to PVS.                       *)
(* --------------------------------------------------------------------- *)

Definition SUB_term1_def:
    ($SUB1t (Con1 (a:'a)) s = Con1 a)                                    /\
    ($SUB1t (Var1 x) s      = SUB1 s x)                                  /\
    ($SUB1t (App1 t u) s    = App1 ($SUB1t t s) ($SUB1t u s))            /\
    ($SUB1t (Lam1 x u) s    =
          let x' = variant x (FV_subst1 s (FV1 u DIFF {x}))  in
          Lam1 x' ($SUB1t u (CONS (x, Var1 x') s)))
End


(* Define the infix substitution operator, <[, with higher precedence *)
(* than the substitution-creation operator //, but lower than CONS:   *)

val _ = set_fixity "<[" (Infixl 480)

(*
term_grammar();
remove_rules_for_term "<[";
clear_overloads_on "<[";
*)

(* Maybe later:
val _ = overload_on("<[", “$SUB1”)
handle e => Raise e;
*)

(* Now overload the substitution operator <[ to refer to any of the  *)
(* object, dict, entry, or method substitution operators defined:    *)

val _ = map (fn t => overload_on("<[", t))
            [“$SUB1t :'a term1 -> ^subs -> 'a term1”]
handle e => Raise e;


(* Now, printed interactively, we read
- > val SUB_term1_def =
    |- (!x s. Var1 x <[ s = SUB1 s x) /\
       (!t u s. App1 t u <[ s = App1 (t <[ s) (u <[ s)) /\
       !x u s.
         Lam1 x u <[ s =
         (let x' = variant x (FV_subst1 s (FV1 u DIFF {x})) in
            Lam1 x' (u <[ (x,Var1 x')::s)) : thm
*)



val TAUT_PROVE = EQT_ELIM o tautLib.TAUT_CONV;
val OR_IMP = TAUT_PROVE “(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))”;

(*
tautLib.TAUT_CONV “(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))”
handle e => Raise e;
*)

val subst_EQ1 = store_thm
   ("subst_EQ1",
    “!a s1 s2:^subs.
          (!x. (x IN FV1 a) ==> (SUB1 s1 x = SUB1 s2 x)) ==>
                   ((a <[ s1) = (a <[ s2))”,
    Induct
    THEN REWRITE_TAC[FV1_def,IN_UNION,IN]
    THEN REWRITE_TAC[OR_IMP]
    THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_term1_def]
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    (* 2 subgoals left *)
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        IMP_RES_THEN REWRITE_THM FV_subst_EQ1
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN REWRITE_TAC[term1_one_one]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[IN_DIFF,IN]
      ]
   );

val subst_IDENT1 = store_thm
   ("subst_IDENT1",
    “!a s:^subs.
          (!x. (x IN FV1 a) ==> (SUB1 s x = Var1 x)) ==>
              ((a <[ s) = a)”,
    Induct
    THEN REWRITE_TAC[FV1_def,IN_UNION,IN]
    THEN REWRITE_TAC[OR_IMP]
    THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_term1_def]
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    (* 2 subgoals left *)
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        IMP_RES_THEN REWRITE_THM FV_subst_IDENT1
        THEN DEP_REWRITE_TAC[variant_ident]
        THEN DEP_REWRITE_TAC[FINITE_DIFF]
        THEN REWRITE_TAC[FINITE_FV1,IN_DIFF,IN]
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN DEP_ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[SUB1]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[IN_DIFF,IN]
      ]
   );

val subst_NIL1 = store_thm
   ("subst_NIL1",
    “!a. (a <[ []:^subs) = a”,
    GEN_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS subst_IDENT1))
    THEN REWRITE_TAC[SUB1]
   );

val subst_SAME_ONE1 = store_thm
   ("subst_SAME_ONE1",
    “!a x. (a <[ [x,Var1 x]:^subs) = a”,
    REPEAT GEN_TAC
    THEN MATCH_MP_TAC subst_IDENT1
    THEN REWRITE_TAC[SUB1]
    THEN GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val subst_SAME_TWO1 = store_thm
   ("subst_SAME_TWO1",
    “!a x t u. (a <[ [x,t; x,u]:^subs) = (a <[ [x,t])”,
    REPEAT GEN_TAC
    THEN MATCH_MP_TAC subst_EQ1
    THEN REWRITE_TAC[SUB1]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[]
   );


val FV_vsubst1 = store_thm
   ("FV_vsubst1",
    “!t xs ys.
           FV1 t DIFF SL xs SUBSET FV1 (t <[ (xs // ys):^subs) ”,
    Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SUB_term1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[FV1_def,SUB1,EMPTY_DIFF,INSERT_DIFF,SUBSET]
    THEN REWRITE_TAC[UNION_DIFF,UNION_SUBSET]
    THENL
      [ COND_CASES_TAC
        THENL
          [ REWRITE_TAC[SUBSET],

            IMP_RES_TAC SUB_FREE_vsubst1
            THEN ASM_REWRITE_TAC[FV1_def,SUBSET_REFL]
          ],

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
        THEN REWRITE_TAC[FINITE_DELETE,FINITE_FV1]
        THEN REWRITE_TAC[FV_subst1]
        THEN REWRITE_TAC[SUBSET_DEF,IN_DIFF,SL,IN]
        THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,IN_DELETE]
        THEN REWRITE_TAC[o_THM,DE_MORGAN_THM]
        THEN GEN_TAC
        THEN STRIP_TAC
        THEN EXISTS_TAC “FV1 ((SUB1 (xs // ys) x) :'a term1)”
        THEN IMP_RES_TAC SUB_FREE_vsubst1
        THEN ASM_REWRITE_TAC[FV1_def,IN]
        THEN EXISTS_TAC “x:var”
        THEN ASM_REWRITE_TAC[EXTENSION,FV1_def,IN]
      ]
   );


val _ = export_theory();

val _ = print_theory_to_file "-" "term.lst";

val _ = html_theory "term";

val _ = print_theory_size();
