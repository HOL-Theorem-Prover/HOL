(* ===================================================================== *)
(* FILE          : variableScript.sml                                    *)
(* VERSION       : 1.0                                                   *)
(* DESCRIPTION   : Defines variables data structure, and variants of     *)
(*                 variables.                      .                     *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : October 19, 2000                                      *)
(* COPYRIGHT     : Copyright (c) 2000 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

                        (* ================== *)
                        (* THE SUNRISE SYSTEM *)
                        (*       \ | /        *)
                        (*     ---_*_---      *)
                        (* ================== *)


(* --------------------------------------------------------------------- *)
(* Boilerplate.                                                          *)
(* --------------------------------------------------------------------- *)
open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Create the theory.                                                    *)
(* --------------------------------------------------------------------- *)
val _ = new_theory "variable";
val _ = ParseExtras.temp_loose_equality()


(*
app load ["stringTheory", "stringLib", "pred_setTheory", "pred_setLib",
          "listTheory", "rich_listTheory", "listLib",
          "numLib", "Datatype",
          "arithmeticTheory", "Psyntax", "Define_type",
          "more_listTheory", "more_setTheory",
          "dep_rewrite", "bossLib" ];
*)
open stringTheory stringLib pred_setTheory pred_setLib;
open listTheory rich_listTheory listLib;
open numLib prim_recTheory combinTheory PairedLambda;
open arithmeticTheory Psyntax;
open more_listTheory more_setTheory;
open dep_rewrite bossLib;


open tactics;



(*===========================================================*)
(* The actual "names" of variables will be defined as a      *)
(* composite type, containing not only a string but also a   *)
(* "variant" number; initially this will be zero, but when   *)
(* this is positive, it indicates a numeric postfix to the   *)
(* variable name.  This is to make it easier to define       *)
(* recognizable variants of variable names.  A zero postfix  *)
(* will not be read; thus ("x",0) => "x" but ("y",2) => "y2".*)
(*===========================================================*)

val _ = Hol_datatype `var = VAR of string => num`;

(*
val var_Axiom = theorem "var_Axiom";
val var_induct = theorem "var_induction";
val var_cases = theorem "var_nchotomy";
val var_one_one = theorem "var_11";
*)



(* =============================================================== *)
(* We define Base v as the string which is the base of v.          *)
(* =============================================================== *)

val Base_def =
    Define `(Base (VAR s n) = s)`;

(* =============================================================== *)
(* We define Index v as the "variant" number attached to the base. *)
(* =============================================================== *)

val Index_def =
    Define `(Index (VAR s n) = n)`;


val Base_Index = store_thm
   ("Base_Index",
    “!x. VAR (Base x) (Index x) = x”,
    Induct
    THEN REWRITE_TAC[Base_def,Index_def]
   );

(* RW_TAC std_ss (type_rws "var") (* or list_ss or arith_ss *) *)


val VAR_EQ_IMP = store_thm
   ("VAR_EQ_IMP",
    “!x y. (Base x = Base y) /\ (Index x = Index y) ==> (x = y)”,
    Induct
    THEN GEN_TAC THEN GEN_TAC
    THEN Induct
    THEN RW_TAC std_ss [Base_def,Index_def]
   );

val VAR_EQ = store_thm
   ("VAR_EQ",
    “!x y. (x = y) = (Base x = Base y) /\ (Index x = Index y)”,
    GEN_TAC THEN GEN_TAC  THEN
    EQ_TAC  THENL
    [ DISCH_THEN REWRITE_THM,
      REWRITE_TAC[VAR_EQ_IMP] ]
   );


(* =============================================================== *)
(* Variants of variables are variables with the same name, but     *)
(* with different numbers attached.  They are considered different *)
(* variables in the state.  For a clean definition, a variable     *)
(* itself is also considered to be a (null) variant of itself.     *)
(* =============================================================== *)

(* =============================================================== *)
(* An easy way to make a variant is to take an existing variable   *)
(* and add an integer to its "variant" number.                     *)
(* =============================================================== *)

val mk_variant_def =
    Define
      `mk_variant (VAR s n) m = (VAR s (n+m))`;

val Index_mk_variant = store_thm
   ("Index_mk_variant",
    “!x k. Index(mk_variant x k) = Index x + k”,
    Induct  THEN
    REWRITE_TAC[mk_variant_def,Index_def]
   );

val Base_mk_variant = store_thm
   ("Base_mk_variant",
    “!x k. Base(mk_variant x k) = Base x”,
    Induct  THEN
    REWRITE_TAC[mk_variant_def,Base_def]
   );

val mk_variant_ident = store_thm
   ("mk_variant_ident",
    “!x k. (mk_variant x k = x) = (k = 0)”,
    Induct
    THEN RW_TAC arith_ss [mk_variant_def]
   );

val mk_variant_equal = store_thm
   ("mk_variant_equal",
    “!x m n. (mk_variant x m = mk_variant x n) = (m = n)”,
    Induct
    THEN RW_TAC arith_ss [mk_variant_def]
   );

val mk_variant_compose = store_thm
   ("mk_variant_compose",
    “!x m n. mk_variant (mk_variant x m) n = (mk_variant x (m+n))”,
    Induct
    THEN RW_TAC arith_ss [mk_variant_def]
   );


(* =============================================================== *)
(* We would like to be able to test if a variable is a variant of  *)
(* another variable.                                               *)
(* =============================================================== *)

(* For Taupo-1 (to come!):
new_infix("is_variant",  ==`:var->var->bool`==, 450);
*)

val is_variant = new_definition (
  "is_variant",
  ``$is_variant y x =
            ((Base y = Base x) /\ (Index x <= Index y))``)
val _ = set_fixity "is_variant" (Infix(NONASSOC, 450))


val is_variant_reflexive = store_thm
   ("is_variant_reflexive",
    “!x. x is_variant x”,
    Induct
    THEN RW_TAC arith_ss [is_variant]
   );

val mk_variant_is_variant = store_thm
   ("mk_variant_is_variant",
    “!x k. (mk_variant x k) is_variant x”,
    Induct
    THEN RW_TAC arith_ss [mk_variant_def,is_variant,Base_def,Index_def]
   );

val is_variant_TRANS = store_thm
   ("is_variant_TRANS",
    “!x y z. (z is_variant y) /\ (y is_variant x) ==> (z is_variant x)”,
    RW_TAC arith_ss [is_variant]
   );

val is_variant_SOME_mk_variant = store_thm
   ("is_variant_SOME_mk_variant",
    “!x y. y is_variant x = (?k. y = mk_variant x k)”,
    Induct
    THEN GEN_TAC THEN GEN_TAC
    THEN Induct
    THEN RW_TAC arith_ss [mk_variant_def,is_variant,Base_def,Index_def]
    THEN EQ_TAC
    THENL
      [  STRIP_TAC
         THEN EXISTS_TAC “n' - n”
         THEN RW_TAC arith_ss [],

         STRIP_TAC
         THEN RW_TAC arith_ss []
      ]
   );

Theorem is_variant_NOT_EQ:
   !x y. (y is_variant x) /\ ~(x = y) ==> (y is_variant mk_variant x 1)
Proof
    RW_TAC arith_ss [is_variant,Base_mk_variant,Index_mk_variant,VAR_EQ] THEN
    REV_FULL_SIMP_TAC arith_ss []
QED

(* =============================================================== *)
(* Once we can make variants of a variable, we can make a whole    *)
(* set of them, of any size we like, all distinct from each other. *)
(* =============================================================== *)

fun new_prim_rec_definition (name,tm) =
 new_recursive_definition
      {rec_axiom = prim_recTheory.num_Axiom,
       name      = name,
       def       = tm};

val variant_set =
    new_prim_rec_definition
    ("variant_set",
      “(variant_set x 0       = EMPTY)  /\
          (variant_set x (SUC k) = (mk_variant x k) INSERT
                                       (variant_set x k))”);

val IN_variant_set = store_thm
   ("IN_variant_set",
    “!m x y. (y IN variant_set x m)
           = (?n. (n < m) /\ (y = mk_variant x n))”,
    INDUCT_TAC
    THEN ASM_REWRITE_TAC[variant_set,IN,NOT_LESS_0,LESS_THM]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THENL
       [ REPEAT STRIP_TAC  THENL
         [ EXISTS_TAC “m:num”  THEN
           ASM_REWRITE_TAC[],

           EXISTS_TAC “n:num”  THEN
           ASM_REWRITE_TAC[]
         ],

         REPEAT STRIP_TAC  THENL
         [ ASM_REWRITE_TAC[],

           DISJ2_TAC  THEN
           EXISTS_TAC “n:num”  THEN
           ASM_REWRITE_TAC[]
         ]
      ]
   );


val FINITE_variant_set = store_thm
   ("FINITE_variant_set",
    “!m x. FINITE (variant_set x m)”,
    INDUCT_TAC
    THEN REWRITE_TAC[variant_set]
    THEN ASM_REWRITE_TAC[FINITE_EMPTY,FINITE_INSERT]
   );


val FINITE_SL = store_thm
   ("FINITE_SL",
    “!l:('a)list. FINITE (SL l)”,
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[SL]
    THEN ASM_REWRITE_TAC[FINITE_EMPTY,FINITE_INSERT]
   );


val CARD_variant_set = store_thm
   ("CARD_variant_set",
    “!m x. CARD (variant_set x m) = m”,
    INDUCT_TAC
    THEN REWRITE_TAC[variant_set,CARD_DEF]
    THEN GEN_TAC
    THEN DEP_REWRITE_TAC[CONJUNCT2 CARD_DEF]
    THEN REWRITE_TAC[FINITE_variant_set]
    THEN REWRITE_TAC[IN_variant_set,mk_variant_equal]
    THEN COND_CASES_TAC
    THENL [POP_ASSUM STRIP_ASSUME_TAC
           THEN IMP_RES_TAC EQ_SYM
           THEN IMP_RES_TAC LESS_NOT_EQ,

           ASM_REWRITE_TAC[]
          ]
   );


(* =================================================================== *)
(* We need to be able to detect when a variable is a variant of        *)
(* another variable, and when it is the *minimum* such variant,        *)
(* subject to the condition that it not be a member of a given set of  *)
(* forbidden variables.                                                *)
(* =================================================================== *)


(* ======================================================= *)
(* Here finally is the definition of the variant function. *)
(* "variant x s" is a string with x as its prefix, but     *)
(* with some number appended to x.  This variant is        *)
(* guaranteed to not be in s, and to be the smallest       *)
(* such variant (with the least index appended).           *)
(* ======================================================= *)

val variant_EXISTS =
    TAC_PROOF
    (([], “!x s. ?y.
              FINITE s ==>
              (y IN variant_set x (SUC(CARD s)) /\ ~(y IN s))
              /\ !z. z IN variant_set x (SUC(CARD s)) /\ ~(z IN s) ==>
                     (Index y <= Index z)”),
     REWRITE_TAC[GSYM IN_DIFF]
     THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_IMP_CONV)
     THEN REWRITE_TAC[GSYM SET_MINIMUM]
     THEN REWRITE_TAC[MEMBER_NOT_EMPTY]
     THEN REPEAT GEN_TAC
     THEN STRIP_TAC
     THEN DEP_REWRITE_TAC[GSYM CARD_EQ_0]
     THEN CONJ_TAC
     THENL
        [ MATCH_MP_TAC FINITE_DIFF
          THEN REWRITE_TAC[FINITE_variant_set],

          ONCE_REWRITE_TAC[EQ_SYM_EQ]
          THEN MATCH_MP_TAC LESS_NOT_EQ
          THEN DEP_REWRITE_TAC[IMP2AND
                 (CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV) LESS_CARD_DIFF)]
          THEN ASM_REWRITE_TAC[FINITE_variant_set,CARD_variant_set,
                               LESS_SUC_REFL]
        ]
    );



local
open Rsyntax
in
val variant =
    let val th1 = CONV_RULE SKOLEM_CONV variant_EXISTS in
       new_specification
         {name    = "variant[notuserdef]",
          consts  = [{const_name = "variant", fixity = NONE (*700*)}],
          sat_thm = th1}
    end
end;



(* variant =
  |- !x s.
       FINITE s ==>
       (variant x s IN variant_set x (SUC (CARD s)) /\
       ~(variant x s IN s)) /\
       (!z.
         z IN variant_set x (SUC (CARD s)) /\ ~(z IN s) ==>
         Index (variant x s) <= Index z) : thm
*)


(* We may want to use any of these three properties specifically. *)
(* The next three corollaries select each property.               *)
(* We prove two versions of each, one for general finite sets,    *)
(* and one for sets made using the SL function on a list, which   *)
(* is guarranteed to be finite.                                   *)


val variant_in_variant_set = store_thm
   ("variant_in_variant_set",
    “!x s. FINITE s ==> (variant x s) IN (variant_set x (SUC(CARD s)))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN REWRITE_THM variant
   );


val variant_not_in_set = store_thm
   ("variant_not_in_set",
    “!x s. FINITE s ==> ~(variant x s IN s)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_THEN REWRITE_THM variant
   );


val variant_minimum = store_thm
   ("variant_minimum",
    “!x s y. FINITE s /\ y IN (variant_set x (SUC(CARD s))) /\ ~(y IN s) ==>
                     (Index(variant x s)) <= (Index y)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_TAC variant
   );



val variant_not_in_subset = store_thm
   ("variant_not_in_subset",
    “!x s t. FINITE s /\ t SUBSET s ==> ~(variant x s IN t)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) variant_not_in_set
    THEN IMP_RES_TAC NOT_IN_SUBSET
   );

val variant_is_variant = store_thm
   ("variant_is_variant",
    “!x s. FINITE s ==> (variant x s) is_variant x”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC_ALL)
            (REWRITE_RULE[IN_variant_set] variant_in_variant_set)
    THEN ASM_REWRITE_TAC[mk_variant_is_variant]
   );


(* Now we wish to express the variant definition more simply,   *)
(* by just saying that the variant selected is just a variant,  *)
(* without referring to any variant-sets.                       *)


val variant_DEF = store_thm
   ("variant_DEF",
    “!x s.
              FINITE s ==>
              ((variant x s) is_variant x /\ ~((variant x s) IN s))
              /\ !z. z is_variant x /\ ~(z IN s) ==>
                     (Index (variant x s) <= Index z)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_THEN REWRITE_THM variant
    THEN IMP_RES_THEN REWRITE_THM variant_is_variant
    THEN IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC_ALL o
                               REWRITE_RULE[IN_variant_set])
                      variant_in_variant_set
    THEN REWRITE_TAC[is_variant_SOME_mk_variant]
    THEN REPEAT STRIP_TAC
    THEN DISJ_CASES_TAC (SPECL [“k:num”,
                                “SUC(CARD (s:var -> bool))”] LESS_CASES)
    THENL
      [  MATCH_MP_TAC variant_minimum
         THEN ASM_REWRITE_TAC[IN_variant_set]
         THEN EXISTS_TAC “k:num”
         THEN ASM_REWRITE_TAC[],

         ASM_REWRITE_TAC[Index_mk_variant]
         THEN ONCE_REWRITE_TAC[ADD_SYM]
         THEN REWRITE_TAC[LESS_EQ_MONO_ADD_EQ]
         THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
         THEN IMP_RES_TAC LESS_EQ_TRANS
      ]
   );


val variant_minimum_DEF = store_thm
   ("variant_minimum_DEF",
    “!x s y. FINITE s /\ y is_variant x /\ ~(y IN s) ==>
                     (Index(variant x s) <= Index y)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC variant_DEF
   );

(* =============================================================== *)
(* Now we need to prove that the variant function as defined above *)
(* satisfies the three properties that we require:                 *)
(*                                                                 *)
(* 1. the variant is a real variant of the original variable;      *)
(*                                                                 *)
(* 2. the variant is not a member of the exclusion list; and       *)
(*                                                                 *)
(* 3. the variant is the minimum such variant, as reckoned by      *)
(*    its Index.                                                   *)
(* =============================================================== *)


val Base_variant = store_thm
   ("Base_variant",
    “!x s. FINITE s ==> (Base (variant x s) = Base x)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC_ALL)
               (REWRITE_RULE[is_variant] variant_is_variant)
   );

val Index_variant = store_thm
   ("Index_variant",
    “!x s. FINITE s ==> Index x <= Index (variant x s)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC_ALL)
               (REWRITE_RULE[is_variant] variant_is_variant)
   );


val variant_EMPTY = store_thm
   ("variant_EMPTY",
    “!x. variant x EMPTY = x”,
    GEN_TAC
    THEN ASSUME_TAC (INST_TYPE[==`:'a`== |-> ==`:var`==] FINITE_EMPTY)
    THEN IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC_ALL)
                     (REWRITE_RULE[is_variant] variant_is_variant)
    THEN STRIP_ASSUME_TAC (SPEC_ALL is_variant_reflexive)
    THEN MATCH_MP_TAC VAR_EQ_IMP
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC variant_minimum
    THEN REWRITE_TAC[IN_variant_set,FINITE_EMPTY,IN]
    THEN EXISTS_TAC “0”
    THEN REWRITE_TAC[LESS_0]
    THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
    THEN REWRITE_TAC[mk_variant_ident]
   );


val LESS_EQ_NOT_EQ = store_thm
   ("LESS_EQ_NOT_EQ",
    “!m n. m <= n /\ ~(m = n) ==> (m+1) <= n”,
    REWRITE_TAC[SYM(SPEC_ALL ADD1),SYM(SPEC_ALL LESS_EQ)]
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN RES_TAC
   );


val SET_IN_OUT =
    TAC_PROOF
    (([], “!(x:'a) y s. (x IN s) /\ ~(y IN s) ==> ~(x = y)”),
     REPEAT STRIP_TAC
     THEN UNDISCH_TAC “(x:'a) IN s”
     THEN ASM_REWRITE_TAC[]
    );


val variant_not_ident = store_thm
   ("variant_not_ident",
    “!x s. FINITE s /\ (x IN s) ==> ~(x = variant x s)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN MATCH_MP_TAC SET_IN_OUT
    THEN EXISTS_TAC “s:var -> bool”
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC variant_not_in_set
    THEN ASM_REWRITE_TAC[]
   );


val Index_variant_not_ident = store_thm
   ("Index_variant_not_ident",
    “!x s. FINITE s /\ (x IN s) ==> ~(Index x = Index (variant x s))”,
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN (ASSUME_TAC o SYM o SPEC_ALL) Base_variant
    THEN IMP_RES_TAC VAR_EQ
    THEN IMP_RES_TAC variant_not_ident
   );

val variant_mk_variant_is_variant = store_thm
   ("variant_mk_variant_is_variant",
    “!x k s. FINITE s ==> (variant (mk_variant x k) s) is_variant x”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC is_variant_TRANS
    THEN EXISTS_TAC “mk_variant x k”
    THEN IMP_RES_TAC variant_is_variant
    THEN ASM_REWRITE_TAC[mk_variant_is_variant]
   );

val variant_mk_variant_not_ident = store_thm
   ("variant_mk_variant_not_ident",
    “!x s. FINITE s ==> ~(variant (mk_variant x 1) s = x)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ONCE_REWRITE_TAC[SYM(SPEC_ALL Base_Index)]
    THEN RW_TAC std_ss []
    THEN IMP_RES_THEN REWRITE_THM Base_variant
    THEN REWRITE_TAC[Base_mk_variant]
    THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
    THEN MATCH_MP_TAC LESS_NOT_EQ
    THEN REWRITE_TAC[LESS_EQ,ADD1]
    THEN REWRITE_TAC[SYM(SPEC_ALL Index_mk_variant)]
    THEN IMP_RES_THEN REWRITE_THM Index_variant
   );


val variant_THM = store_thm
   ("variant_THM",
    “!x s. FINITE s ==>
              (variant x s = (if x IN s then variant (mk_variant x 1) s  else  x))”,
    REPEAT STRIP_TAC
    THEN COND_CASES_TAC
    THEN MATCH_MP_TAC VAR_EQ_IMP
    THEN IMP_RES_THEN REWRITE_THM Base_variant
    THEN REWRITE_TAC[Base_mk_variant]
    THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM
    THENL
      [  STRIP_TAC
         THEN MATCH_MP_TAC variant_minimum_DEF
         THEN IMP_RES_THEN REWRITE_THM variant_not_in_set
         THEN IMP_RES_THEN ASM_REWRITE_THM variant_mk_variant_is_variant
         THEN REWRITE_TAC[is_variant]
         THEN IMP_RES_THEN REWRITE_THM Base_variant
         THEN REWRITE_TAC[Base_mk_variant,Index_mk_variant]
         THEN MATCH_MP_TAC LESS_EQ_NOT_EQ
         THEN IMP_RES_THEN REWRITE_THM Index_variant
         THEN IMP_RES_TAC Index_variant_not_ident,

         STRIP_TAC
         THENL
           [
              MATCH_MP_TAC variant_minimum_DEF
              THEN ASM_REWRITE_TAC[is_variant_reflexive],

              IMP_RES_THEN REWRITE_THM Index_variant
           ]
      ]
   );


val variant_ident =
 store_thm
  ("variant_ident",
   “!x s. FINITE s /\ ~(x IN s) ==> (variant x s = x)”,
    REPEAT STRIP_TAC THEN
    IMP_RES_THEN ONCE_REWRITE_THM variant_THM THEN
    ASM_REWRITE_TAC[]
  );


val variant_DELETE =
 store_thm
  ("variant_DELETE",
   “!x s. FINITE s ==> (variant x (s DELETE x) = x)”,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC variant_ident THEN
    ASM_REWRITE_TAC[FINITE_DELETE,IN_DELETE]
  );


val variant_increment =
 store_thm
  ("variant_increment",
   “!x s.
      FINITE s /\ (x IN s) ==> (variant x s = variant (mk_variant x 1) s)”,
   REPEAT STRIP_TAC
   THEN IMP_RES_THEN (ASSUME_TAC o SPEC “x:var”) variant_THM
   THEN ASM_REWRITE_TAC[]
  );



(* We define the function 'variants', to take a list of variables  *)
(* and form a list of variants of the variables in the list, with  *)
(* the provision that the list produced should have no duplicates. *)


fun new_list_rec_def name tm =
  new_recursive_definition
      {rec_axiom = list_Axiom,
       name      = name,
       def       = tm};

val variants =
    new_list_rec_def "variants"
      “(variants NIL s  =  NIL)  /\
          (variants (CONS x xs) s  =
               (let x' = variant x s in
                  (CONS x' (variants xs (x' INSERT s)))))”;

(* Alternative definition of variants:

val variants =
    new_list_rec_def "variants"
      “(variants NIL s  =  NIL)  /\
          (variants (CONS x xs) s  =
               (let xs' = variants xs s in
                  (CONS (variant x (SL xs' UNION s)) xs')))”;
*)


val variants_THM =
 store_thm
  ("variants_THM",
   “(variants NIL s  =  NIL)  /\
    (variants (CONS x xs) s  =
         (CONS (variant x s) (variants xs ((variant x s) INSERT s))))”,
   REWRITE_TAC[variants]
   THEN CONV_TAC (DEPTH_CONV let_CONV)
   THEN REFL_TAC
  );


val NOT_IN_variants_INSERT =
 store_thm
  ("NOT_IN_variants_INSERT",
   “!xs y s. FINITE s ==> ~(y IN SL (variants xs (y INSERT s)))”,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC[variants_THM,SL,IN,DE_MORGAN_THM]
   THEN REPEAT GEN_TAC
   THEN STRIP_TAC
   THEN STRIP_TAC
   THENL
     [  MATCH_MP_TAC IN_NOT_IN
        THEN EXISTS_TAC “(y:var) INSERT s”
        THEN REWRITE_TAC[COMPONENT]
        THEN MATCH_MP_TAC variant_not_in_set
        THEN ASM_REWRITE_TAC[FINITE_INSERT],

        ONCE_REWRITE_TAC[INSERT_COMM]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[FINITE_INSERT]
     ]
  );


val variants_APPEND =
 store_thm
  ("variants_APPEND",
   “!x y s.
        variants (APPEND x y) s  =
        APPEND (variants x s) (variants y (SL(variants x s) UNION s))”,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC[variants_THM,SL,APPEND,UNION]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[CONS_11]
   THEN ONCE_REWRITE_TAC[UNION_COMM]
   THEN REWRITE_TAC[UNION]
  );


val DISJOINT_variants =
 store_thm
  ("DISJOINT_variants",
   “!x s. FINITE s ==> (DISJOINT (SL (variants x s)) s)”,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC[variants_THM,SL,DISJOINT_EMPTY,DISJOINT_INSERT]
   THEN REPEAT GEN_TAC
   THEN DISCH_TAC
   THEN IMP_RES_THEN REWRITE_THM variant_not_in_set
   THEN FIRST_ASSUM (MP_TAC o SPEC “(variant x' s) INSERT s”)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN ASM_REWRITE_TAC[DISJOINT_INSERT,FINITE_INSERT]
   THEN DISCH_THEN REWRITE_THM
  );

val DISJOINT_variants_SL =
 store_thm
  ("DISJOINT_variants_SL",
   “!x l. DISJOINT (SL (variants x (SL l))) (SL l)”,
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC DISJOINT_variants
   THEN REWRITE_TAC[FINITE_SL]
  );



val DL_variants =
 store_thm
  ("DL_variants",
   “!x s. FINITE s ==> DL (variants x s)”,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC[variants_THM,DL]
   THEN REPEAT GEN_TAC
   THEN DISCH_TAC
   THEN IMP_RES_THEN REWRITE_THM NOT_IN_variants_INSERT
   THEN FIRST_ASSUM MATCH_MP_TAC
   THEN ASM_REWRITE_TAC[FINITE_INSERT]
  );

val DL_variants_SL =
 store_thm
  ("DL_variants_SL",
   “!x l. DL (variants x (SL l))”,
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC DL_variants
   THEN REWRITE_TAC[FINITE_SL]
  );


val LENGTH_variants =
 store_thm
  ("LENGTH_variants",
   “!x s. LENGTH (variants x s) = LENGTH x”,
   LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC[variants_THM,LENGTH]
  );


val NOT_IN_variants =
 store_thm
  ("NOT_IN_variants",
   “!x y s. FINITE s /\ y IN s ==> ~(y IN SL (variants x s))”,
   REPEAT GEN_TAC THEN STRIP_TAC
   THEN IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) DISJOINT_variants
   THEN IMP_RES_TAC IN_DISJOINT_IMP
  );


val DISJOINT_variants_UNION =
 store_thm
  ("DISJOINT_variants_UNION",
   “!x s t.
     FINITE s /\ FINITE t ==>
     DISJOINT (SL(variants x (s UNION t))) s /\
     DISJOINT (SL(variants x (s UNION t))) t”,
   REPEAT GEN_TAC
   THEN STRIP_TAC
   THEN (MP_TAC o SPECL[“x:(var)list”,“(s:(var)-> bool) UNION t”])
             DISJOINT_variants
   THEN ASM_REWRITE_TAC[FINITE_UNION]
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
  );


val DISJOINT_variants_APPEND =
 store_thm
  ("DISJOINT_variants_APPEND",
    “!x a b.
     DISJOINT (SL (variants x (SL (APPEND a b)))) (SL a) /\
     DISJOINT (SL (variants x (SL (APPEND a b)))) (SL b) ”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[SL_APPEND]
   THEN MATCH_MP_TAC DISJOINT_variants_UNION
   THEN REWRITE_TAC[FINITE_SL]
  );


val DISJOINT_variants_UNION1 =
 store_thm
  ("DISJOINT_variants_UNION1",
    “!x s t.
         FINITE s /\ FINITE t ==>
         DISJOINT (SL (variants x (s UNION t))) s”,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC DISJOINT_variants_UNION
   THEN ASM_REWRITE_TAC[]
  );


val DISJOINT_variants_UNION2 =
 store_thm
  ("DISJOINT_variants_UNION2",
    “!x s t.
         FINITE s /\ FINITE t ==>
         DISJOINT (SL (variants x (s UNION t))) t”,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC DISJOINT_variants_UNION
   THEN ASM_REWRITE_TAC[]
  );


val DISJOINT_variants_UNION3 =
 store_thm
  ("DISJOINT_variants_UNION3",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT (SL(variants x (s UNION (t UNION u)))) s /\
      DISJOINT (SL(variants x (s UNION (t UNION u)))) t /\
      DISJOINT (SL(variants x (s UNION (t UNION u)))) u /\
      DISJOINT s (SL(variants x (s UNION (t UNION u)))) /\
      DISJOINT t (SL(variants x (s UNION (t UNION u)))) /\
      DISJOINT u (SL(variants x (s UNION (t UNION u))))”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN ASM_REWRITE_TAC[]
  );

val DISJOINT_variants_UNION_LEFT_1 =
 store_thm
  ("DISJOINT_variants_UNION_LEFT_1",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT (SL(variants x (s UNION (t UNION u)))) s”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
  );

val DISJOINT_variants_UNION_LEFT_2 =
 store_thm
  ("DISJOINT_variants_UNION_LEFT_2",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT (SL(variants x (s UNION (t UNION u)))) t”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
  );

val DISJOINT_variants_UNION_LEFT_3 =
 store_thm
  ("DISJOINT_variants_UNION_LEFT_3",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT (SL(variants x (s UNION (t UNION u)))) u”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
  );

val DISJOINT_variants_UNION_RIGHT_1 =
 store_thm
  ("DISJOINT_variants_UNION_RIGHT_1",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT s (SL(variants x (s UNION (t UNION u))))”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN ASM_REWRITE_TAC[]
  );

val DISJOINT_variants_UNION_RIGHT_2 =
 store_thm
  ("DISJOINT_variants_UNION_RIGHT_2",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT t (SL(variants x (s UNION (t UNION u))))”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN ASM_REWRITE_TAC[]
  );

val DISJOINT_variants_UNION_RIGHT_3 =
 store_thm
  ("DISJOINT_variants_UNION_RIGHT_3",
    “!x s t u.
      FINITE s /\ FINITE t /\ FINITE u ==>
      DISJOINT u (SL(variants x (s UNION (t UNION u))))”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[(SYM o SPEC_ALL) FINITE_UNION]
   THEN DISCH_THEN (MP_TAC o SPEC_ALL o MATCH_MP DISJOINT_variants)
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN REWRITE_TAC[DISJOINT_UNION]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC[DISJOINT_SYM]
   THEN ASM_REWRITE_TAC[]
  );


val _ = export_theory();

val _ = print_theory_to_file "-" "variable.lst";

val _ = html_theory "variable";

val _ = print_theory_size();
