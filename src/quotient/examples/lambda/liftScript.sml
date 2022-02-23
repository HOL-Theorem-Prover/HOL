open HolKernel Parse boolLib;


(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "lift";

(* In interactive sessions, do:
val _ = map load ["more_listTheory","more_setTheory","variableTheory","termTheory","alphaTheory"];
*)

open prim_recTheory;
open pairTheory;
open pairLib;
open listTheory;
open rich_listTheory;
open combinTheory;
open listLib;
open pred_setTheory;
open pred_setLib;
open numTheory;
open numLib;
open arithmeticTheory;
open bossLib;
open Mutual;
open ind_rel;
open dep_rewrite;
open more_listTheory;
open more_setTheory;
open variableTheory;
open termTheory;
open alphaTheory;

open quotientLib;

open tactics;
open Rsyntax;


val _ = associate_restriction ("?!!",  "RES_EXISTS_EQUIV");

val term = ty_antiq (``:'a term1``);
val subs = ty_antiq (``:(var # 'a term1) list``);


(* ===================================================================== *)
(* We now prove that the term constructor functions at the term1 level   *)
(* respect alpha-equivalence.                                            *)
(* ===================================================================== *)

val Con1_ALPHA = store_thm
  ("Con1_ALPHA",
   “!a. ALPHA (Con1 a :^term) (Con1 a)”,
   REWRITE_TAC[ALPHA_term_pos]
  );

val Var1_ALPHA = store_thm
   ("Var1_ALPHA",
    “!x. ALPHA (Var1 x :^term) (Var1 x)”,
    REWRITE_TAC[ALPHA_term_pos]
   );

val App1_ALPHA = store_thm
   ("App1_ALPHA",
    “!t1 :^term t2 u1 u2. ALPHA t1 t2 /\ ALPHA u1 u2 ==>
                      ALPHA (App1 t1 u1) (App1 t2 u2)”,
    REWRITE_TAC[ALPHA_term_pos]
   );

val Lam1_ALPHA = store_thm
   ("Lam1_ALPHA",
    “!x t1:^term t2. ALPHA t1 t2 ==>
                      ALPHA (Lam1 x t1) (Lam1 x t2)”,
    REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA_Lam]
   );


val ALPHA_SYM' = GEN_ALL (CONJUNCT2 (SPEC_ALL
                   (REWRITE_RULE[EQ_IMP_THM] ALPHA_SYM)));

val ALPHA_EQUIV = save_thm("ALPHA_EQUIV",
    refl_sym_trans_equiv ALPHA_REFL ALPHA_SYM' ALPHA_TRANS);

val ALPHA_PEQUIV = store_thm
   ("ALPHA_PEQUIV",
    “(?t:^term. ALPHA t t) /\
        (!t u:^term. ALPHA t u <=>
                     ALPHA t t /\ ALPHA u u /\ (ALPHA t = ALPHA u))”,
    REWRITE_TAC[REWRITE_RULE[EQUIV_def]ALPHA_EQUIV]
   );

(*
val op_EQUIVs = [LIST_EQUIV,PAIR_EQUIV];
val equivs = [ALPHA_EQUIV];
val ty = ``:(var # 'a term1) list``;
*)

val SUBST_EQUIV = make_equiv [ALPHA_EQUIV] [LIST_EQUIV, PAIR_EQUIV]
                      ``:(var # 'a term1) list``;



val vsubst1_RSP = store_thm
   ("vsubst1_RSP",
    “!xs ys.
          LIST_REL ($= ### ALPHA) (xs // ys) ((xs // ys):^subs)”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[REWRITE_RULE[EQUIV_def]SUBST_EQUIV]
   );

val ALPHA_SUB1 = store_thm
   ("ALPHA_SUB1",
    “!s1:^subs s2 x. LIST_REL ($= ### ALPHA) s1 s2 ==>
                        ALPHA (SUB1 s1 x) (SUB1 s2 x)”,
    LIST_INDUCT_TAC
    THENL [ALL_TAC, GEN_TAC]
    THEN LIST_INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LIST_REL_def]
    THEN REWRITE_TAC[SUB1_def]
    THEN REWRITE_TAC[ALPHA_REFL]
    THEN POP_TAC
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN CONV_TAC (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
               (PURE_REWRITE_CONV[PAIR_REL]
                THENC DEPTH_CONV GEN_BETA_CONV)))))
    THEN STRIP_TAC
    THEN RES_TAC
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );

(*
val SUB1_RSP = store_thm
   ("SUB1_RSP",
    “!s1:^subs s2 x1 x2.
         LIST_REL ($= ### ALPHA) s1 s2 /\ (x1 = x2) ==>
         ALPHA (SUB1 s1 x1) (SUB1 s2 x2)”,
    REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN ASM_REWRITE_TAC[]
   );
*)

(*
val FV1_o_SUB1_RSP = TAC_PROOF(([],
    “!s1:^subs s2.
         LIST_REL ($= ### ALPHA) s1 s2 ==>
         ((FV1 o SUB1 s1) = (FV1 o SUB1 s2))”),
    REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[o_THM]
    THEN MATCH_MP_TAC ALPHA_FV
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN ASM_REWRITE_TAC[]
   );

val FV_subst_RSP = store_thm
   ("FV_subst_RSP",
    “!s1:^subs s2 xs ys.
         LIST_REL ($= ### ALPHA) s1 s2 /\ (xs = ys) ==>
         (FV_subst1 s1 xs = FV_subst1 s2 ys)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC FV1_o_SUB1_RSP
    THEN ASM_REWRITE_TAC[FV_subst1]
   );
*)

val FV_subst_RSP = store_thm
   ("FV_subst_RSP",
    “!s1:^subs s2 xs.
         LIST_REL ($= ### ALPHA) s1 s2 ==>
         (FV_subst1 s1 xs = FV_subst1 s2 xs)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[FV_subst1]
    THEN AP_TERM_TAC
    THEN AP_THM_TAC
    THEN AP_TERM_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[o_THM]
    THEN MATCH_MP_TAC ALPHA_FV
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN ASM_REWRITE_TAC[]
   );



val ALPHA_subst_ALL = store_thm
   ("ALPHA_subst_ALL",
    “!s1:^subs s2 (t:var -> bool).
         LIST_REL ($= ### ALPHA) s1 s2 ==>
         ALPHA_subst t s1 s2”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[ALPHA_subst]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val SUBt_RSP = store_thm
   ("SUBt_RSP",
    “!t1:^term t2 s1 s2.
         ALPHA t1 t2 /\ LIST_REL ($= ### ALPHA) s1 s2 ==>
         ALPHA (t1 <[ s1) (t2 <[ s2)”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC ALPHA_SUB_CONTEXT
    THEN IMP_RES_TAC ALPHA_subst_ALL
    THEN ASM_REWRITE_TAC[]
   );

val ALPHA_subst_RSP = store_thm
   ("ALPHA_subst_RSP",
    “!s1:^subs s2 t1 t2 (t:var -> bool).
         LIST_REL ($= ### ALPHA) s1 s2 /\
         LIST_REL ($= ### ALPHA) t1 t2 ==>
         (ALPHA_subst t s1 t1 = ALPHA_subst t s2 t2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[ALPHA_subst]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) ALPHA_SUB1
    THEN IMP_RES_TAC ALPHA_SYM
    THEN IMP_RES_TAC ALPHA_TRANS
   );


val BV_subst_RSP = store_thm
   ("BV_subst_RSP",
    “!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2.
          (LIST_REL ($= ### R)) s1 s2 ==>
          (BV_subst s1 = BV_subst s2)”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ALL_TAC, GEN_TAC]
    THEN Induct
    THEN REWRITE_TAC[LIST_REL_def]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[BV_subst_def]
    THEN MK_COMB_TAC
    THENL
      [ AP_TERM_TAC
        THEN IMP_RES_TAC (MATCH_MP FST_RSP (identity_quotient (==`:var`==))),

        FIRST_ASSUM MATCH_MP_TAC
        THEN FIRST_ASSUM ACCEPT_TAC
      ]
   );

val BV_subst_PRS = store_thm
   ("BV_subst_PRS",
    “!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s. BV_subst s = BV_subst (MAP (I ## rep) s)”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN REWRITE_TAC[MAP]
    THEN REWRITE_TAC[BV_subst_def]
    THEN Cases
    THEN REWRITE_TAC[PAIR_MAP_THM,I_THM,FST]
    THEN AP_TERM_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val term_EQ_IS_ALPHA =
    TAC_PROOF
   (([],
     “!t:^term y a.
          ((t = Con1 a) = ALPHA t (Con1 a)) /\
          ((t = Var1 y) = ALPHA t (Var1 y))”),
    Cases
    THEN GEN_TAC
    THEN REWRITE_TAC[term1_one_one,term1_distinct2,
                     ALPHA_term_pos,ALPHA_term_neg]
   );

val FV_subst_EQ1' = store_thm
   ("FV_subst_EQ1'",
    “!s1:^subs s2 t.
          (!x. (x IN t) ==> ALPHA (SUB1 s1 x) (SUB1 s2 x)) ==>
          (FV_subst1 s1 t = FV_subst1 s2 t)”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[FV_subst1]
    THEN AP_TERM_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[IN_IMAGE,o_THM]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC “x':var”
        THEN ASM_REWRITE_TAC[]
        THEN MATCH_MP_TAC ALPHA_FV
        THEN RES_TAC,

        EXISTS_TAC “x':var”
        THEN ASM_REWRITE_TAC[]
        THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
        THEN MATCH_MP_TAC ALPHA_FV
        THEN RES_TAC
      ]
   );


val TAUT_PROVE = EQT_ELIM o tautLib.TAUT_CONV;
val OR_IMP = TAUT_PROVE “(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))”;

val subst_EQ1' = store_thm
   ("subst_EQ1'",
    “!a:^term s1 s2.
            (!x. (x IN FV1 a) ==> ALPHA (SUB1 s1 x) (SUB1 s2 x)) ==>
                  ALPHA (a <[ s1) (a <[ s2)”,
    Induct
    THEN REWRITE_TAC[FV1_def,IN_UNION,IN]
    THEN REWRITE_TAC[OR_IMP]
    THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_term1_def]
    THEN RES_TAC
    (* 4 subgoals *)
    THENL
      [ REWRITE_TAC[ALPHA_REFL],

        FIRST_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        MATCH_MP_TAC App1_ALPHA
        THEN CONJ_TAC
        THEN FIRST_ASSUM ACCEPT_TAC,

        IMP_RES_THEN REWRITE_THM FV_subst_EQ1'
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN MATCH_MP_TAC Lam1_ALPHA
        THEN REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[ALPHA_REFL]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[IN_DIFF,IN]
      ]
   );

val BV_subst_IDENT1 = store_thm
   ("BV_subst_IDENT1",
    “!s:^subs x. ~(x IN (BV_subst s)) ==> (SUB1 s x = Var1 x)”,
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

val HEIGHT1_SUB1_var = store_thm
   ("HEIGHT1_SUB1_var",
    “!xs ys v.
          HEIGHT1 (SUB1 ((xs // ys):^subs) v) = 0”,
    Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Cases
    THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[vsubst1,SUB1,HEIGHT1_def]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[HEIGHT1_def]
   );

val HEIGHT1_var_list_subst = store_thm
   ("HEIGHT1_var_list_subst",
    “!t:^term xs ys.
          HEIGHT1 (t <[ (xs // ys)) = HEIGHT1 t”,
    Induct
    THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[SUB_term1_def,SUB1,HEIGHT1_def]
    THENL
      [ REWRITE_TAC[HEIGHT1_SUB1_var],

        CONV_TAC (DEPTH_CONV let_CONV)
        THEN ONCE_REWRITE_TAC[GSYM vsubst1]
        THEN ASM_REWRITE_TAC[HEIGHT1_def]
      ]
   );

val HEIGHT1_var_subst = store_thm
   ("HEIGHT1_var_subst",
    “!t:^term x y.
          HEIGHT1 (t <[ [x, Var1 y]) = HEIGHT1 t”,
    REWRITE_TAC[GSYM vsubst1]
    THEN REWRITE_TAC[HEIGHT1_var_list_subst]
   );


val term1_distinct' = store_thm
   ("term1_distinct'",
    “((!a x.     ~(ALPHA (Con1 a)   (Var1 x   : ^term))) /\
         (!a t u.   ~(ALPHA (Con1 a)   (App1 t u : ^term))) /\
         (!a y u.   ~(ALPHA (Con1 a)   (Lam1 y u : ^term))) /\
         (!x a.     ~(ALPHA (Var1 x)   (Con1 a   : ^term))) /\
         (!x t u.   ~(ALPHA (Var1 x)   (App1 t u : ^term))) /\
         (!x y u.   ~(ALPHA (Var1 x)   (Lam1 y u : ^term))) /\
         (!t u a.   ~(ALPHA (App1 t u) (Con1 a   : ^term))) /\
         (!t u x.   ~(ALPHA (App1 t u) (Var1 x   : ^term))) /\
         (!t u y v. ~(ALPHA (App1 t u) (Lam1 y v : ^term))) /\
         (!y u a.   ~(ALPHA (Lam1 y u) (Con1 a   : ^term))) /\
         (!y u x.   ~(ALPHA (Lam1 y u) (Var1 x   : ^term))) /\
         (!y v t u. ~(ALPHA (Lam1 y v) (App1 t u : ^term))))”,
    REWRITE_TAC[ALPHA_term,ALPHA1_term_neg]
   );


val term1_cases' = store_thm
   ("term1_cases'",
    “!t:^term. (?a. ALPHA t (Con1 a)) \/
                  (?v. ALPHA t (Var1 v)) \/
                  (?t' t0. ALPHA t (App1 t' t0)) \/
                  (?v t'. ALPHA t (Lam1 v t'))”,
    GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC “t:^term” term1_cases)
    THENL (* four subgoals *)
          [ DISJ1_TAC
            THEN EXISTS_TAC “a:'a”
            THEN ASM_REWRITE_TAC[ALPHA_term_pos],

            DISJ2_TAC
            THEN DISJ1_TAC
            THEN EXISTS_TAC “v:var”
            THEN ASM_REWRITE_TAC[ALPHA_term_pos],

            DISJ2_TAC
            THEN DISJ2_TAC
            THEN DISJ1_TAC
            THEN EXISTS_TAC “t':^term”
            THEN EXISTS_TAC “t0:^term”
            THEN ASM_REWRITE_TAC[ALPHA_term_pos,ALPHA_REFL],

            DISJ2_TAC
            THEN DISJ2_TAC
            THEN DISJ2_TAC
            THEN EXISTS_TAC “v:var”
            THEN EXISTS_TAC “t':^term”
            THEN ASM_REWRITE_TAC[ALPHA_term_pos,ALPHA_REFL]
          ]
    );


val term1_one_one' = store_thm
   ("term1_one_one'",
    “(!a:'a a'. ALPHA (Con1 a) (Con1 a') = (a = a')) /\
        (!x t t':^term. ALPHA (Lam1 x t) (Lam1 x t') = ALPHA t t') /\
        (!x x'. ALPHA (Var1 x :^term) (Var1 x') = (x = x')) /\
        (!t u t' u':^term. ALPHA (App1 t u) (App1 t' u') <=>
                              ALPHA t t' /\ ALPHA u u')”,
    REWRITE_TAC[ALPHA_term_pos,ALPHA_Lam_one_one,subst_SAME_ONE1]
   );

val CHANGE_VAR1 = store_thm
   ("CHANGE_VAR1",
    “!x v t:'a term1.
         ~(x IN FV1 (Lam1 v t)) ==>
         ALPHA (Lam1 v t) (Lam1 x (t <[ [(v,Var1 x)]))”,
    REWRITE_TAC[FV1_def]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA_CHANGE_ONE_VAR
    THEN ONCE_REWRITE_TAC[ALPHA_SYM]
    THEN ASM_REWRITE_TAC[]
   );

(* AXIOM 3 *)

(* Melham and Gordon's third axiom, on alpha-equivalence. *)

val CHANGE_ONE_VAR1 = store_thm
   ("CHANGE_ONE_VAR1",
    “!x v t:'a term1.
         ~(x IN FV1 (Lam1 v t)) ==>
         ALPHA (Lam1 v t) (Lam1 x (t <[ [(v,Var1 x)]))”,
    REWRITE_TAC[FV1_def]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA_CHANGE_ONE_VAR
    THEN ONCE_REWRITE_TAC[ALPHA_SYM]
    THEN ASM_REWRITE_TAC[]
   );



(* ----------------------------------------------------------------- *)
(* We now begin the development that leads to the lifting of         *)
(* the "function existance" theorem for the lambda calculus.         *)
(* This is AXIOM 4 for Gordon and Melham in "Five Axioms" paper.     *)
(* They proved their axiom from an underlying deBruijn representa-   *)
(* tion, but to my knowledge this has never been proven for a name-  *)
(* carrying syntax at the lower level like this before, and has      *)
(* never been automatically lifted to the higher, abstract level.    *)
(*                                                                   *)
(* Most of this is to express this theorem at the lower level as:    *)
(*                                                                   *)
(* !(con : 'a -> 'b) (var : var->'b) app abs.                        *)
(*    ?!hom :: respects(ALPHA,$=).                                   *)
(*       (!x.   hom (Con1 a)   = con a) /\                           *)
(*       (!x.   hom (Var1 x)   = var x) /\                           *)
(*       (!t u. hom (App1 t u) = app (hom t) (hom u) t u) /\         *)
(*       (!x u. hom (Lam1 x u) = abs (\y. hom (u <[ [x, Var1 y]))    *)
(*                                   (\y. u <[ [x, Var1 y]))         *)
(*                                                                   *)
(* ----------------------------------------------------------------- *)

val term1_hom_def =
    Hol_defn "term1_hom"
    `(term1_hom con var app abs (Con1 a :^term) = (con a):'b) /\
     (term1_hom con var app abs (Var1 x) = (var x)) /\
     (term1_hom con var app abs (App1 t u) =
           app (term1_hom con var app abs t)
               (term1_hom con var app abs u) t u) /\
     (term1_hom con var app abs (Lam1 x u) =
           abs (\y. term1_hom con var app abs
                              (u <[ [x, Var1 y]))
               (\y. u <[ [x, Var1 y]))`;

(*
Defn.tgoal term1_hom_def;
e(WF_REL_TAC `measure (HEIGHT1 o SND o SND o SND o SND)`);
e(REPEAT CONJ_TAC);

  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_MAX]);

  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_MAX]);

  e(REWRITE_TAC[HEIGHT1_var_subst]);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_REFL]);
*)

val (term1_hom_eqns, term1_hom_ind) =
   Defn.tprove
    (term1_hom_def,
     WF_REL_TAC `measure (HEIGHT1 o SND o SND o SND o SND)`
     THEN REPEAT CONJ_TAC
     THEN REWRITE_TAC[HEIGHT1_var_subst]
     THEN REWRITE_TAC[HEIGHT1_def]
     THEN REPEAT GEN_TAC
     THEN MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC
     THEN REWRITE_TAC[LESS_EQ_MAX,LESS_EQ_REFL]
    );



val term1_hom_RSP_LEMMA = TAC_PROOF(([],
    “!(con :'a -> 'b) var app abs.
         respects($= ===> $= ===> ALPHA ===> ALPHA ===> $=) app /\
         respects($= ===> ($= ===> ALPHA) ===> $=) abs ==>
         !n t:^term u. (HEIGHT1 t <= n) /\ ALPHA t u ==>
             (term1_hom con var app abs t = term1_hom con var app abs u)”),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[RESPECTS,FUN_REL]
    THEN CONV_TAC (RATOR_CONV (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
    THEN REWRITE_TAC[AND_IMP_INTRO,GSYM CONJ_ASSOC]
    THEN STRIP_TAC
    THEN INDUCT_TAC (* two subgoals *)
    THEN Cases THEN Cases (* 32 subgoals *)
    THEN REWRITE_TAC[HEIGHT1_def,LESS_EQ_0,NOT_SUC,SUC_NOT]
    THEN REWRITE_TAC[ALPHA_term_neg]
    THEN REWRITE_TAC[ALPHA_term_pos]
    THEN REWRITE_TAC[INV_SUC_EQ,LESS_EQ_MONO,MAX_LESS_EQ]
    THEN REWRITE_TAC[ZERO_LESS_EQ]
    THEN REWRITE_TAC[term1_hom_eqns]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN CONJ_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[],

        FIRST_ASSUM MATCH_MP_TAC
        THEN CONJ_TAC
        THENL
          [ CONV_TAC FUN_EQ_CONV
            THEN GEN_TAC
            THEN BETA_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[HEIGHT1_var_subst]
            THEN MATCH_MP_TAC ALPHA_Lam_subst
            THEN FIRST_ASSUM ACCEPT_TAC,

            REPEAT GEN_TAC
            THEN DISCH_THEN REWRITE_THM
            THEN BETA_TAC
            THEN MATCH_MP_TAC ALPHA_Lam_subst
            THEN FIRST_ASSUM ACCEPT_TAC
          ]
      ]
   );


val term1_hom_RSP = TAC_PROOF(([],
    “! (con :'a -> 'b) var app abs.
         respects($= ===> $= ===> ALPHA ===> ALPHA ===> $=) app /\
         respects($= ===> ($= ===> ALPHA) ===> $=) abs ==>
         respects(ALPHA ===> $=) (term1_hom con var app abs)”),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[RESPECTS,FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC term1_hom_RSP_LEMMA
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN EXISTS_TAC “HEIGHT1 (x:^term <[ [(v,Var1 v'')])”
    THEN REWRITE_TAC[HEIGHT1_var_subst]
    THEN REWRITE_TAC[LESS_EQ_REFL]
   );

val term1_respects_Axiom_exists = store_thm(
    "term1_respects_Axiom_exists",
    “!(con : 'a -> 'b) var
         (app :: respects($= ===> $= ===> ALPHA ===> ALPHA ===> $=))
         (abs :: respects($= ===> ($= ===> ALPHA) ===> $=)) .
         ?hom :: respects(ALPHA ===> $=).
           (!a.   hom (Con1 a) = con a) /\
           (!x.   hom (Var1 x) = var x) /\
           (!t u. hom (App1 t u) = app (hom t) (hom u) t u) /\
           (!x u. hom (Lam1 x u) = abs (\y. hom (u <[ [x, Var1 y]))
                                       (\y. u <[ [x, Var1 y]))”,
    CONV_TAC (DEPTH_CONV res_quanLib.RES_FORALL_CONV)
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_CONV)
    THEN REWRITE_TAC[SPECIFICATION]
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC “(term1_hom con var app abs):^term -> 'b”
    THEN REWRITE_TAC[term1_hom_eqns]
    THEN MATCH_MP_TAC term1_hom_RSP
    THEN ASM_REWRITE_TAC[]
   );


val term1_respects_Axiom_11_LEMMA = TAC_PROOF(([],
    “!hom1 hom2
         (con : 'a -> 'b) var app abs.
           hom1 IN respects (ALPHA ===> $=) /\
           hom2 IN respects (ALPHA ===> $=) /\
           ((!a.   hom1 (Con1 a) = con a) /\
            (!x.   hom1 (Var1 x) = var x) /\
            (!t u. hom1 (App1 t u) = app (hom1 t) (hom1 u) t u) /\
            (!x u. hom1 (Lam1 x u) = abs (\y. hom1 (u <[ [x, Var1 y]))
                                         (\y. u <[ [x, Var1 y]))) /\
           ((!a.   hom2 (Con1 a) = con a) /\
            (!x.   hom2 (Var1 x) = var x) /\
            (!t u. hom2 (App1 t u) = app (hom2 t) (hom2 u) t u) /\
            (!x u. hom2 (Lam1 x u) = abs (\y. hom2 (u <[ [x, Var1 y]))
                                         (\y. u <[ [x, Var1 y])))
           ==>
           (!n t. (HEIGHT1 t <= n) ==> (hom1 t = hom2 t))”),
    REWRITE_TAC[SPECIFICATION,RESPECTS_THM]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN Induct
    THEN Cases (* 8 subgoals *)
    THEN REWRITE_TAC[HEIGHT1_def,LESS_EQ_0,NOT_SUC]
    THEN REWRITE_TAC[LESS_EQ_MONO,MAX_LESS_EQ]
    THEN REWRITE_TAC[ZERO_LESS_EQ]
    THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC
    THENL
      [ RES_TAC
        THEN ASM_REWRITE_TAC[],

        AP_THM_TAC
        THEN AP_TERM_TAC
        THEN CONV_TAC FUN_EQ_CONV
        THEN GEN_TAC
        THEN BETA_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[HEIGHT1_var_subst]
      ]
   );

val term1_respects_Axiom_11_LEMMA2 = TAC_PROOF(([],
    “!hom1 hom2
         (con : 'a -> 'b) var app abs.
           hom1 IN respects (ALPHA ===> $=) /\
           hom2 IN respects (ALPHA ===> $=) /\
           ((!a.   hom1 (Con1 a) = con a) /\
            (!x.   hom1 (Var1 x) = var x) /\
            (!t u. hom1 (App1 t u) = app (hom1 t) (hom1 u) t u) /\
            (!x u. hom1 (Lam1 x u) = abs (\y. hom1 (u <[ [x, Var1 y]))
                                         (\y. u <[ [x, Var1 y]))) /\
           ((!a.   hom2 (Con1 a) = con a) /\
            (!x.   hom2 (Var1 x) = var x) /\
            (!t u. hom2 (App1 t u) = app (hom2 t) (hom2 u) t u) /\
            (!x u. hom2 (Lam1 x u) = abs (\y. hom2 (u <[ [x, Var1 y]))
                                         (\y. u <[ [x, Var1 y])))
           ==>
           (hom1 = hom2)”),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN DEFINE_NEW_VAR “n = HEIGHT1 (t:^term)”
    THEN POP_ASSUM (MP_TAC o MATCH_MP (DECIDE “(a=b) ==> (a<=b)”) o SYM)
    THEN SPEC_TAC (“t:^term”,“t:^term”)
    THEN SPEC_TAC (“n:num”,“n:num”)
    THEN MATCH_MP_TAC (SPEC_ALL term1_respects_Axiom_11_LEMMA)
    THEN ASM_REWRITE_TAC[]
   );

val term1_respects_Axiom_11 = store_thm(
    "term1_respects_Axiom_11",
    “!(con : 'a -> 'b) var app abs.
        !hom1 hom2 :: respects(ALPHA ===> $=).
          ((!a.   hom1 (Con1 a) = con a) /\
           (!x.   hom1 (Var1 x) = var x) /\
           (!t u. hom1 (App1 t u) = app (hom1 t) (hom1 u) t u) /\
           (!x u. hom1 (Lam1 x u) = abs (\y. hom1 (u <[ [x, Var1 y]))
                                        (\y. u <[ [x, Var1 y]))) /\
          ((!a.   hom2 (Con1 a) = con a) /\
           (!x.   hom2 (Var1 x) = var x) /\
           (!t u. hom2 (App1 t u) = app (hom2 t) (hom2 u) t u) /\
           (!x u. hom2 (Lam1 x u) = abs (\y. hom2 (u <[ [x, Var1 y]))
                                        (\y. u <[ [x, Var1 y])))
           ==>
           (hom1 = hom2)”,
    REPEAT GEN_TAC
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN STRIP_TAC
    THEN MATCH_MP_TAC (SPEC_ALL term1_respects_Axiom_11_LEMMA2)
    THEN ASM_REWRITE_TAC[]
   );


val term1_respects_Axiom = store_thm(
    "term1_respects_Axiom",
    “!(con : 'a -> 'b) var
         (app :: respects ($= ===> $= ===> ALPHA ===> ALPHA ===> $=))
         (abs :: respects ($= ===> ($= ===> ALPHA) ===> $=)).
         ?!hom :: respects(ALPHA ===> $=).
           (!a.   hom (Con1 a) = con a) /\
           (!x.   hom (Var1 x) = var x) /\
           (!t u. hom (App1 t u) = app (hom t) (hom u) t u) /\
           (!x u. hom (Lam1 x u) = abs (\y. hom (u <[ [x, Var1 y]))
                                       (\y. u <[ [x, Var1 y]))”,
    CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_UNIQUE_CONV)
    THEN REPEAT GEN_TAC
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN IMP_RES_TAC (res_quanLib.RESQ_REWR_CANON term1_respects_Axiom_exists)
    THEN ASM_REWRITE_TAC[term1_respects_Axiom_11]
   );


(* Now we develop the last of the Gordon-Melham axioms, that states *)
(* the existence of a function `Abs' such that                      *)
(*         Lam v t = Abs (\y. t <[ [v, Var y])                      *)

val Abs1_def =
    Define
    `Abs1 (f : var -> ^term) =
        let x = VAR "x" 0 in
        let v = variant x (FV1 (f x)) in
           Lam1 v (f v)`;

(* Prove Abs1 is respectful. *)

val Lam1_ALPHA1 = TAC_PROOF(([],
    “!x y t1:^term t2. (x = y) /\ ALPHA t1 t2 ==>
                      ALPHA (Lam1 x t1) (Lam1 y t2)”),
    REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC Lam1_ALPHA
    THEN ASM_REWRITE_TAC[]
   );

val Abs1_ALPHA_LEMMA = store_thm
   ("Abs1_ALPHA_LEMMA",
    “!f1 f2 x.
          ($= ===> ALPHA) f1 f2  ==>
          (variant x (FV1 ((f1 x):^term)) = variant x (FV1 (f2 x)))”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN AP_TERM_TAC
    THEN MATCH_MP_TAC ALPHA_FV
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REFL_TAC
   );

val Abs1_ALPHA = store_thm
   ("Abs1_ALPHA",
    “!f1 f2 :var->^term.
          ($= ===> ALPHA) f1 f2  ==>
          ALPHA (Abs1 f1) (Abs1 f2)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC Abs1_ALPHA_LEMMA
    THEN ASM_REWRITE_TAC[Abs1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN MATCH_MP_TAC Lam1_ALPHA
    THEN REWRITE_ALL_TAC[FUN_REL]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REFL_TAC
   );

val SINGLE_vsubst = TAC_PROOF(([],
    “!x y:var.
          [x, Var1 y :^term] = ([x] // [y])”),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[vsubst1]
   );

val SINGLE_SL = TAC_PROOF(([],
    “!x:var.
          {x} = SL [x]”),
    GEN_TAC
    THEN REWRITE_TAC[SL]
   );

(* Melham and Gordon's fifth and final axiom. *)

val Lam1_Abs1 = store_thm
   ("Lam1_Abs1",
    “!v t:^term.
           ALPHA (Lam1 v t) (Abs1 (\y. t <[ [v, Var1 y]))”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[Abs1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN BETA_TAC
    THEN ONCE_REWRITE_TAC[ALPHA_SYM]
    THEN MATCH_MP_TAC ALPHA_CHANGE_ONE_VAR
    THEN MATCH_MP_TAC variant_not_in_subset
    THEN REWRITE_TAC[FINITE_FV1]
    THEN REWRITE_TAC[SINGLE_vsubst,SINGLE_SL]
    THEN REWRITE_TAC[FV_vsubst1]
   );


val equivs = [ALPHA_EQUIV];

val fnlist = [{def_name="Con_def", fname="Con",
               func= “Con1 :'a->^term”, fixity=NONE
                                        (* see structure Parse *)},
              {def_name="Var_def", fname="Var",
               func= “Var1 :var -> ^term”, fixity=NONE},
              {def_name="App_def", fname="App",
               func= “App1 :^term -> ^term -> ^term”,
               fixity=NONE},
              {def_name="Lam_def", fname="Lam",
               func= “Lam1 :var -> ^term -> ^term”, fixity=NONE},
              {def_name="Abs_def", fname="Abs",
               func= “Abs1 :(var -> ^term) -> ^term”, fixity=NONE},
              {def_name="HEIGHT_def", fname="HEIGHT",
               func= “HEIGHT1 :^term -> num”, fixity=NONE},
              {def_name="FV_def", fname="FV",
               func= “FV1 :^term -> var -> bool”, fixity=NONE},
              {def_name="SUB_def", fname="SUB",
               func= “SUB1 :^subs -> var -> ^term”, fixity=NONE},
              {def_name="FV_subst_def", fname="FV_subst",
               func= “FV_subst1 :^subs -> (var -> bool) -> var -> bool”,
               fixity=NONE},
              {def_name="SUBt_def", fname="SUBt",
               func= “SUB1t :^term -> ^subs -> ^term”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="vsubst_def", fname="/",
               func= “$// :var list -> var list -> ^subs”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="subst_eq_def", fname="subst_eq",
               func= “ALPHA_subst:(var -> bool) ->^subs ->^subs -> bool”,
               fixity=NONE}
             ];


val respects = [(*Con1_ALPHA,*) Var1_ALPHA, App1_ALPHA, Lam1_ALPHA, Abs1_ALPHA,
                ALPHA_HEIGHT, ALPHA_FV, ALPHA_SUB1, FV_subst_RSP,
                (*vsubst1_RSP,*) SUBt_RSP, ALPHA_subst_RSP]

val polydfs = [BV_subst_PRS]

val polywfs = [BV_subst_RSP]


fun gg tm = proofManagerLib.set_goal([],tm);


val old_thms =
     [HEIGHT1_def,
      REWRITE_RULE[term_EQ_IS_ALPHA] HEIGHT_LESS_EQ_ZERO1,
      FV1_def,
      FINITE_FV1,
      SUB1,
      SUB1_def,
      SUB_vsubst_Var1,
      REWRITE_RULE[term_EQ_IS_ALPHA] IN_FV_SUB_vsubst1,
      SUB_APPEND_vsubst1,
      SUB_FREE_vsubst1,
      FV_subst1,
      FINITE_FV_subst1,
      FV_subst_EQ1',
      REWRITE_RULE[term_EQ_IS_ALPHA] FV_subst_IDENT1,
      FV_subst_NIL1,
      SUB_term1_def,
      ALPHA_Lam,
      subst_SAME_ONE1,
      subst_SAME_TWO1,
      subst_EQ1',
      FREE_SUB1,
      BV_subst_IDENT1,
      BV_vsubst1,
      FREE_FV_SUB1,
      FREE_IDENT_SUBST1,
      REWRITE_RULE[term_EQ_IS_ALPHA] subst_IDENT1,
      subst_NIL1,
      HEIGHT1_SUB1_var,
      HEIGHT1_var_list_subst,
      HEIGHT1_var_subst,
      term1_distinct',
      term1_cases',
      term1_one_one',
      ALPHA_Lam_one_one,
      vsubst1_def,
      vsubst1,
      SUB_APPEND_FREE_vsubst1,
      ALPHA_subst,
      ALPHA_SUB_CONTEXT,
      ALPHA_CHANGE_VAR,
      ALPHA_CHANGE_ONE_VAR,
      CHANGE_ONE_VAR1,
      ALPHA_Lam_subst,
      Lam1_Abs1,
      term1_induction,
      term1_respects_Axiom
      ]


(* ==================================================== *)
(*   LIFT TYPES, CONSTANTS, AND THEOREMS BY QUOTIENTS   *)
(* ==================================================== *)

val _ = quotient.chatting := true;

val [HEIGHT,
     HEIGHT_LESS_EQ_ZERO,
     FV_term, (* AXIOM 1 of Gordon and Melham *)
     FINITE_FV,
     SUB,
     SUB_def,
     SUB_vsubst_Var,
     IN_FV_SUB_vsubst,
     SUB_APPEND_vsubst,
     SUB_FREE_vsubst,
     FV_subst,
     FINITE_FV_subst,
     FV_subst_EQ,
     FV_subst_IDENT,
     FV_subst_NIL,
     SUB_term,
     Lam_EQ,
     subst_SAME_ONE,
     subst_SAME_TWO,
     subst_EQ,
     FREE_SUB,
     BV_subst_IDENT,
     BV_vsubst,
     FREE_FV_SUB,
     FREE_IDENT_SUBST,
     subst_IDENT,
     subst_NIL,
     HEIGHT_SUB_var,
     HEIGHT_var_list_subst,
     HEIGHT_var_subst,
     term_distinct,
     term_cases,
     term_one_one,
     Lam_one_one',
     vsubst_def,
     vsubst,
     SUB_APPEND_FREE_vsubst,
     EQ_SUBST,
     EQ_SUBST_CONTEXT,
     LAMBDA_CHANGE_VAR,
     LAMBDA_CHANGE_ONE_VAR,
     CHANGE_ONE_VAR, (* AXIOM 3 of Gordon and Melham *)
     Lam_subst,
     Lam_Abs,
     term_induct,
     term_Axiom
     ] =
    define_quotient_types_full {
      types = [{name = "term", equiv = ALPHA_EQUIV}],
      defs = fnlist, tyop_equivs = [], tyop_quotients = [],
      tyop_simps = [],
      respects = respects, poly_respects = polywfs,
      poly_preserves = polydfs,
      old_thms = old_thms
    };

(* Testing:

val LIFT_RULE =
    define_quotient_types_rule
    {types = [{name = "term", equiv = ALPHA_EQUIV}],
     defs = fnlist,
     tyop_equivs = [LIST_EQUIV, PAIR_EQUIV],
     tyop_quotients = [LIST_QUOTIENT, PAIR_QUOTIENT, FUN_QUOTIENT],
     tyop_simps = [LIST_REL_EQ, LIST_MAP_I, PAIR_REL_EQ, PAIR_MAP_I,
                   FUN_REL_EQ, FUN_MAP_I],
     respects = respects,
     poly_preserves = polydfs,
     poly_respects = polywfs} handle e => Raise e;

LIFT_RULE SUB1;

fun print_thm' th = (print_thm th; print "\n"; th);
val _ = print "\nLifted theorems:\n";
val new_thms = map (print_thm' o LIFT_RULE)
                    old_thms   handle e => (print "excn\n"; Raise e);

LIFT_RULE (INST_TYPE[alpha |-> ``:'a term1``,
                     gamma |-> ``:'c term1``] o_THM);

LIFT_RULE (INST_TYPE[beta  |-> ``:'b term1``] o_THM) handle e => Raise e;

LIFT_RULE (INST_TYPE[alpha |-> ``:'a term1``] o_THM);

LIFT_RULE (INST_TYPE[alpha |-> ``:'a term1``,
                     gamma |-> ``:'c term1``] o_ASSOC) handle e => Raise e;

LIFT_RULE (INST_TYPE[gamma |-> ``:'c term1``] o_DEF) handle e => Raise e;

LIFT_RULE (INST_TYPE[alpha |-> ``:'a term1``,
                     beta  |-> ``:'b term1``] I_o_ID) handle e => Raise e;

LIFT_RULE (INST_TYPE[beta  |-> ``:'b term1``] pairTheory.CURRY_UNCURRY_THM)
 handle e => Raise e;

-- or --

fun is_match_term tm1 tm2 =
    (match_term tm1 tm2; true) handle _ => false;

val partial_equiv_tm =
    “(?(x:'a). R x x) /\
       (!(x:'a) (y:'a). R x y = R x x /\ R y y /\ (R x = R y))”;

fun is_partial_equiv th = is_match_term partial_equiv_tm (concl th);

val types = [{name = "term", equiv = ALPHA_EQUIV}]
val defs = fnlist
val tyop_equivs = [LIST_EQUIV, PAIR_EQUIV]
val tyop_quotients = [LIST_QUOTIENT, PAIR_QUOTIENT, FUN_QUOTIENT]
val tyop_simps = [LIST_REL_EQ, LIST_MAP_I, PAIR_REL_EQ, PAIR_MAP_I,
                   FUN_REL_EQ, FUN_MAP_I]
val respects = respects
val poly_preserves = polydfs
val poly_respects = polywfs
(* val equivs = map #equiv types *)
val equivs = map #equiv (filter (not o is_partial_equiv o #equiv) types)
val quotients = map (fn {name, equiv} =>
            define_quotient_type name (name^"_ABS") (name^"_REP") equiv)
                          types
val fn_defns = map (define_quotient_lifted_function
                          quotients tyop_quotients tyop_simps) defs


... read in quotient.sml here

val ntys = enrich_types quotients tyop_quotients respects
val equivs = equivs @ map (make_equiv (equivs @ tyop_equivs)) ntys
val quotients =
    quotients @ map (make_quotient (quotients @ tyop_quotients)) ntys

val LIFT_RULE =
    lift_theorem_by_quotients quotients equivs tyop_quotients fn_defns
                              respects poly_preserves poly_respects

-or-

val quot_ths = quotients
val tyops = tyop_quotients
val newdefs = fn_defns

... read in lift_theorem_by_quotients quot_ths equivs tyops newdefs respects polydfs polywfs

TESTS:

LIFT_RULE HEIGHT1_def;
LIFT_RULE (REWRITE_RULE[term_EQ_IS_ALPHA] HEIGHT_LESS_EQ_ZERO1);
LIFT_RULE FV1_def;
LIFT_RULE FINITE_FV1;
LIFT_RULE SUB1;
LIFT_RULE SUB1_def;
LIFT_RULE SUB_vsubst_Var1;
LIFT_RULE (REWRITE_RULE[term_EQ_IS_ALPHA] IN_FV_SUB_vsubst1);
LIFT_RULE SUB_APPEND_vsubst1;
LIFT_RULE SUB_FREE_vsubst1;
LIFT_RULE swap1_def;
LIFT_RULE FV_subst1;
LIFT_RULE FINITE_FV_subst1;
LIFT_RULE FV_subst_EQ1';
LIFT_RULE (REWRITE_RULE[term_EQ_IS_ALPHA] FV_subst_IDENT1);
LIFT_RULE FV_subst_NIL1;
LIFT_RULE SUB_term1_def;
LIFT_RULE ALPHA_Lam;
LIFT_RULE subst_SAME_ONE1;
LIFT_RULE subst_SAME_TWO1;
LIFT_RULE subst_EQ1';
LIFT_RULE FREE_SUB1;
LIFT_RULE BV_subst_IDENT1;
LIFT_RULE BV_vsubst1;
LIFT_RULE FREE_FV_SUB1;
LIFT_RULE FREE_IDENT_SUBST1;
LIFT_RULE (REWRITE_RULE[term_EQ_IS_ALPHA] subst_IDENT1);
LIFT_RULE subst_NIL1;
LIFT_RULE HEIGHT1_SUB1_var;
LIFT_RULE HEIGHT1_var_list_subst;
LIFT_RULE HEIGHT1_var_subst;
LIFT_RULE term1_distinct';
LIFT_RULE term1_cases';
LIFT_RULE term1_one_one';
LIFT_RULE ALPHA_Lam_one_one;
LIFT_RULE vsubst1_def;
LIFT_RULE vsubst1;
LIFT_RULE SUB_APPEND_FREE_vsubst1;
LIFT_RULE ALPHA_CHANGE_VAR;
LIFT_RULE ALPHA_CHANGE_ONE_VAR;
LIFT_RULE CHANGE_ONE_VAR1; (* AXIOM 3 of Gordon and Melham *)
LIFT_RULE Lam1_Abs1,
LIFT_RULE ALPHA_Lam_subst;
LIFT_RULE term1_induction;

LIFT_RULE term1_respects_Axiom;

val th = INST_TYPE[alpha |-> mk_type{Tyop="fun", Args=[``:'a term1``,bool]},
                   beta  |-> mk_type{Tyop="fun", Args=[bool,``:'c term1``]}]
                (GEN_ALL PAIR_EQ);

val PAIR_EQ' = store_thm
   ("PAIR_EQ'",
    “!((y:bool -> 'c term1)::respects ($= ===> ALPHA))
         ((x:'a term1 -> bool)::respects (ALPHA ===> $=))
         (b::respects ($= ===> ALPHA))
         (a::respects (ALPHA ===> $=)).
           ((ALPHA ===> $=) ### $= ===> ALPHA) (x,y) (a,b) =
           (ALPHA ===> $=) x a /\ ($= ===> ALPHA) y b”,
    CONV_TAC (DEPTH_CONV res_quanLib.RES_FORALL_CONV)
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[PAIR_REL_THM]
   );

LIFT_RULE PAIR_EQ' handle e => Raise e;

... walk through lift_theorem_by_quotients1

val new_thms = map LIFT_RULE old_thms handle e => Raise e
length new_thms; (* 42 at present *)

END OF TESTS
*)


(* Now overload the substitution operator <[ to refer to the  *)
(* term substitution operator defined:                        *)

val term = ty_antiq (==`:'a term`==);
val subs = ty_antiq (==`:(var # 'a term) list`==);


val _ = map (fn t => overload_on("<[", t))
            [“$SUBt:'a term -> ^subs -> 'a term”];



(* ---------------------------------------------------------------- *)
(* Save the (important) theorems lifted by the quotient operations. *)
(* ---------------------------------------------------------------- *)

val HEIGHT = save_thm ("HEIGHT", HEIGHT); (* was 12 lines *)

val HEIGHT_LESS_EQ_ZERO = save_thm("HEIGHT_LESS_EQ_ZERO", HEIGHT_LESS_EQ_ZERO);
(* was 12 lines *)

(* AXIOM 1 of Gordon and Melham *)
val FV_term = save_thm ("FV_term", FV_term); (* was 11 lines *)

val FINITE_FV = save_thm ("FINITE_FV", FINITE_FV); (* was 10 lines *)

val SUB = save_thm ("SUB", SUB); (* was 12 lines *)

(* val SUB_def = save_thm ("SUB_def",SUB_def); (* was not lifted *) *)

(* val SUB_vsubst_Var = save_thm ("SUB_vsubst_Var", SUB_vsubst_Var); *)
(* was 32 lines *)

(* val IN_FV_SUB_vsubst = save_thm ("IN_FV_SUB_vsubst", IN_FV_SUB_vsubst); *)
(* was 10 lines *)

(* val SUB_APPEND_vsubst = save_thm ("SUB_APPEND_vsubst", SUB_APPEND_vsubst);*)
(* was 30 lines *)

(* val SUB_FREE_vsubst = save_thm ("SUB_FREE_vsubst", SUB_FREE_vsubst); *)
(* was 21 lines *)

val FV_subst = save_thm ("FV_subst", FV_subst);
(* was 7 lines *)

(* val FINITE_FV_subst = save_thm ("FINITE_FV_subst", FINITE_FV_subst); *)
(* was 13 lines *)

(* val FV_subst_EQ = save_thm ("FV_subst_EQ", FV_subst_EQ); *)
(* was 26 lines *)


(* val FV_subst_IDENT = save_thm ("FV_subst_IDENT", FV_subst_IDENT); *)
(* was 35 lines *)

(* val FV_subst_NIL = save_thm ("FV_subst_NIL", FV_subst_NIL); *)
(* was 7 lines *)

val SUB_term    = save_thm ("SUB_term", SUB_term);
(* was 19 lines *)
(* Glory to God!  Soli Deo Gloria! *)

val Lam_EQ = save_thm ("Lam_EQ", Lam_EQ);
(* was not lifted *)

val subst_SAME_ONE = save_thm ("subst_SAME_ONE", subst_SAME_ONE);
(* was 10 lines *)

val subst_SAME_TWO = save_thm ("subst_SAME_TWO", subst_SAME_TWO);
(* was not lifted *)

val subst_EQ = save_thm ("subst_EQ", subst_EQ);
(* was 31 lines *)

(* val FREE_SUB = save_thm ("FREE_SUB", FREE_SUB); *)
(* was not lifted *)

val BV_subst_IDENT = save_thm ("BV_subst_IDENT", BV_subst_IDENT);
(* was 11 lines *)

(* val BV_vsubst = save_thm ("BV_vsubst", BV_vsubst); *)
(* was not lifted *)


(* val FREE_FV_SUB = save_thm ("FREE_FV_SUB", FREE_FV_SUB); *)
(* was not lifted *)

(* val FREE_IDENT_SUBST = save_thm ("FREE_IDENT_SUBST", FREE_IDENT_SUBST); *)
(* was not lifted *)

val subst_IDENT = save_thm ("subst_IDENT", subst_IDENT);
(* was 32 lines *)

(* val subst_NIL = save_thm ("subst_NIL", subst_NIL); *)
(* was 7 lines *)


val HEIGHT_SUB_var = save_thm ("HEIGHT_SUB_var", HEIGHT_SUB_var);

val HEIGHT_var_list_subst = save_thm ("HEIGHT_var_list_subst",
                                       HEIGHT_var_list_subst);

val HEIGHT_var_subst = save_thm ("HEIGHT_var_subst", HEIGHT_var_subst);

val term_distinct = save_thm("term_distinct", term_distinct);
(* was 12 lines (now 11) *)

(* val term_cases = save_thm("term_cases", term_cases); *)
(* was 36 lines (now 25 lines) *)

val term_one_one = save_thm("term_one_one", term_one_one);
(* was 38 lines, now 9 lines *)

(* val vsubst_def = save_thm("vsubst_def", vsubst_def); *)
(* was not lifted *)

val vsubst = save_thm("vsubst", vsubst);
(* was not lifted *)

(* val SUB_APPEND_FREE_vsubst = save_thm("SUB_APPEND_FREE_vsubst",
                                       SUB_APPEND_FREE_vsubst);    *)
(* was 24 lines *)

val EQ_SUBST = save_thm("EQ_SUBST", EQ_SUBST);

val EQ_SUBST_CONTEXT = save_thm("EQ_SUBST_CONTEXT", EQ_SUBST_CONTEXT);

val LAMBDA_CHANGE_VAR = save_thm("LAMBDA_CHANGE_VAR", LAMBDA_CHANGE_VAR);
(* was 22 lines *)

val LAMBDA_CHANGE_ONE_VAR = save_thm("LAMBDA_CHANGE_ONE_VAR",
                                      LAMBDA_CHANGE_ONE_VAR);

(* AXIOM 3 of Gordon and Melham. *)
val CHANGE_ONE_VAR = save_thm("CHANGE_ONE_VAR", CHANGE_ONE_VAR);

(* val Lam_subst = save_thm("Lam_subst", Lam_subst); *)
(* was not lifted *)

(* AXIOM 5 of Gordon and Melham. *)
val Lam_Abs = save_thm("Lam_Abs", Lam_Abs);
(* was not lifted *)


(*
term1_induction;
    |- !P.
         (!v. P (Var1 v)) /\
         (!t t0. P t /\ P t0 ==> P (App1 t t0)) /\
         (!t. P t ==> !v. P (Lam1 v t)) ==>
         !t. P t
*)

val term_induct = save_thm("term_induct", term_induct);
(* was 17 lines *)
(* Glory to God!  Soli Deo Gloria! *)

(* AXIOM 4 for Gordon and Melham. *)
val term_Axiom = save_thm("term_Axiom", term_Axiom);
(* was not lifted *)

(* ---------------------------------------------------------------- *)
(*      End of saving important theorems from lifting.              *)
(* ---------------------------------------------------------------- *)







(* AXIOM 2 for Gordon and Melham. *)
val SUBSTITUTION = store_thm
   ("SUBSTITUTION",
    “(!a:'a x u. Con a <[ [x,u] = Con a) /\
        (!x u:'a term. Var x <[ [x,u] = u) /\
        (!x u:'a term y. ~(x = y) ==> (Var y <[ [x,u] = Var y)) /\
        (!t:'a term u v x. App t u <[ [x,v] = App (t <[ [x,v]) (u <[ [x,v])) /\
        (!x t:'a term u. Lam x t <[ [x,u] = Lam x t) /\
        (!x y u:'a term. ~(x = y) /\ ~(y IN FV u) ==>
                 !t. Lam y t <[ [x,u] = Lam y (t <[ [x,u]))”,
    REWRITE_TAC[SUB_term,SUB]
    THEN REPEAT STRIP_TAC
    THENL
      [ POP_ASSUM (REWRITE_THM o GSYM),

        DEP_REWRITE_TAC[FV_subst_IDENT]
        THEN CONJ_TAC
        THENL
          [ REWRITE_TAC[IN_DIFF,IN,SUB]
            THEN GEN_TAC
            THEN STRIP_TAC
            THEN ASM_REWRITE_TAC[],

            DEP_REWRITE_TAC[variant_ident,FINITE_DIFF]
            THEN REWRITE_TAC[FINITE_FV,IN_DIFF,IN]
            THEN CONV_TAC (DEPTH_CONV let_CONV)
            THEN REWRITE_TAC[Lam_EQ]
            THEN REWRITE_TAC[subst_SAME_TWO]
            THEN REWRITE_TAC[subst_SAME_ONE]
          ],

        DEP_REWRITE_TAC[variant_ident]
        THEN REPEAT CONJ_TAC
        THENL
          [ DEP_REWRITE_TAC[FINITE_FV_subst,FINITE_DIFF]
            THEN REWRITE_TAC[FINITE_FV],

            REWRITE_TAC[FV_subst]
            THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE]
            THEN REWRITE_TAC[o_THM,SUB,IN_DIFF,IN]

            THEN CONV_TAC NOT_EXISTS_CONV
            THEN GEN_TAC
            THEN REWRITE_TAC[DE_MORGAN_THM]
            THEN ONCE_REWRITE_TAC[DISJ_SYM]
            THEN REWRITE_TAC[GSYM IMP_DISJ_THM]
            THEN DISCH_TAC
            THEN CONV_TAC NOT_EXISTS_CONV
            THEN GEN_TAC
            THEN REWRITE_TAC[DE_MORGAN_THM]
            THEN COND_CASES_TAC
            THENL
              [ POP_ASSUM REWRITE_THM
                THEN ASM_REWRITE_TAC[]
                THEN REWRITE_TAC[GSYM IMP_DISJ_THM]
                THEN DISCH_THEN REWRITE_ALL_THM
                THEN RES_TAC,

                REWRITE_TAC[FV_term]
                THEN REWRITE_TAC[GSYM IMP_DISJ_THM]
                THEN DISCH_THEN REWRITE_ALL_THM
                THEN REWRITE_ALL_TAC[IN]
                THEN ASM_REWRITE_TAC[]
              ],
(* or,
            THEN PROVE_TAC[FV_term,IN], *)

            CONV_TAC (DEPTH_CONV let_CONV)
            THEN REWRITE_TAC[Lam_EQ]
            THEN MATCH_MP_TAC subst_EQ
            THEN GEN_TAC
            THEN DISCH_TAC
            THEN REWRITE_TAC[SUB]
            THEN REPEAT COND_CASES_TAC
            THENL
              [ POP_ASSUM REWRITE_ALL_THM
                THEN RES_TAC,

                ASM_REWRITE_TAC[],

                REFL_TAC,

                REFL_TAC
              ]
          ]
      ]
   );

val SUBSTITUTION_CONJS = CONJUNCTS SUBSTITUTION;
val Var_SUBST_NOT_EQUAL = el 3 SUBSTITUTION_CONJS;
val Lam_SUBST_NOT_EQUAL = last SUBSTITUTION_CONJS;




val Lam_one_one = store_thm
   ("Lam_one_one",
    “!(a:'a term) b x y. (Lam x a = Lam y b) =
                                ((a <[ [x,Var y] = b) /\
                                 (b <[ [y,Var x] = a))”,
    REPEAT GEN_TAC
    THEN CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV EQ_SYM_EQ)))
    THEN REWRITE_TAC[Lam_one_one']
   );
(* was 16 lines, now 10 *)

val Lam_one_one_RENAME = store_thm
   ("Lam_one_one_RENAME",
    “!a:'a term b x y. (Lam x a = Lam y b) ==>
                              (b = a <[ [x,Var y])”,
    REWRITE_TAC[Lam_one_one]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );



(* Now test the higher term induction principle: *)

val term_height_induct_LEMMA = store_thm
   ("term_height_induct_LEMMA",
    “!n term_Prop:'a term -> bool.
         (!a. term_Prop (Con a)) /\
         (!x. term_Prop (Var x)) /\
         (!t u. term_Prop t /\ term_Prop u ==> term_Prop (App t u)) /\
         (!t. (!t'. (HEIGHT t = HEIGHT t') ==> term_Prop t') ==>
               (!v. term_Prop (Lam v t))) ==>
         (!t. (HEIGHT t <= n) ==> term_Prop t)”,
    INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THENL
      [ REWRITE_TAC[HEIGHT_LESS_EQ_ZERO]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[],

        UNDISCH_ALL_TAC
        THEN DISCH_THEN ((fn th => REPEAT DISCH_TAC
                                   THEN ASSUME_TAC th) o SPEC_ALL)
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN (fn th => UNDISCH_ALL_TAC THEN STRIP_ASSUME_TAC th)
        THEN REPEAT DISCH_TAC
        THEN MUTUAL_INDUCT_THEN term_induct ASSUME_TAC
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL
          [ FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN REPEAT STRIP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN FIRST_ASSUM REWRITE_THM
          ]
      ]
   );

val term_height_induct = store_thm
   ("term_height_induct",
    “!term_Prop:'a term -> bool.
         (!a. term_Prop (Con a)) /\
         (!x. term_Prop (Var x)) /\
         (!t u. term_Prop t /\ term_Prop u ==> term_Prop (App t u)) /\
         (!t. (!t'. (HEIGHT t = HEIGHT t') ==> term_Prop t') ==>
               (!v. term_Prop (Lam v t))) ==>
         (!t. term_Prop t)”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC_ALL
           (SPEC “HEIGHT (t:'a term)” term_height_induct_LEMMA))
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[LESS_EQ_REFL]
   );


(* Variable-for-variable substitutions *)


val HEIGHT_SUB_vsubst = store_thm
   ("HEIGHT_SUB_vsubst",
    “!xs ys x.
         HEIGHT (SUB ((xs / ys):^subs) x) = 0”,
    REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC_ALL SUB_vsubst_Var)
    THEN ASM_REWRITE_TAC[HEIGHT]
   );



val subst_EMPTY = store_thm
   ("subst_EMPTY",
    “!t:'a term x u. ~(x IN FV t) ==> ((t <[ [x,u]) = t)”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC subst_IDENT
    THEN REWRITE_TAC[SUB]
    THEN GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );



val FV_term_subst = store_thm
   ("FV_term_subst",
    “!t:'a term s. FV (t <[ s) = FV_subst s (FV t)”,
    REWRITE_TAC[FV_subst]
    THEN MUTUAL_INDUCT_THEN term_induct ASSUME_TAC
    THEN REWRITE_TAC[SUB_term]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[FV_term]
    THEN ASM_REWRITE_TAC[IMAGE_UNION,UNION_SET_UNION]
    THEN REWRITE_TAC[IMAGE,UNION_SET,UNION_EMPTY,o_THM]
    (* only one subgoal at this point! *)
    THEN REPEAT GEN_TAC
    THEN DEFINE_NEW_VAR
         “v' = variant v (FV_subst (s:^subs) (FV (t:'a term) DIFF {v}))”
    THEN FIRST_ASSUM (REWRITE_THM o SYM)
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_DIFF,IN_UNION_SET,IN_IMAGE]
    THEN REWRITE_TAC[IN,o_THM]
    THEN GEN_TAC
    THEN EQ_TAC
    THENL
      [ STRIP_TAC
        THEN EXISTS_TAC “si:var -> bool”
        THEN (CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC))
        THEN EXISTS_TAC “x':var”
        THEN REWRITE_ALL_TAC[SUB]
        THEN SUBGOAL_THEN “~(x' = (v:var))” ASSUME_TAC
        THENL
          [ DISCH_THEN REWRITE_ALL_THM
            THEN REWRITE_ALL_TAC[FV_term]
            THEN UNDISCH_THEN “si = {v':var}” REWRITE_ALL_THM
            THEN REWRITE_ALL_TAC[IN]
            THEN RES_TAC,

            POP_ASSUM REWRITE_ALL_THM
            THEN CONJ_TAC
            THEN FIRST_ASSUM ACCEPT_TAC
          ],

        STRIP_TAC
        THEN CONJ_TAC
        THENL
          [ EXISTS_TAC “si:var -> bool”
            THEN (CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC))
            THEN EXISTS_TAC “x':var”
            THEN (CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC))
            THEN REWRITE_TAC[SUB]
            THEN POP_ASSUM MP_TAC
            THEN FIRST_ASSUM REWRITE_THM
            THEN ASM_REWRITE_TAC[],

            MATCH_MP_TAC IN_NOT_IN
            THEN EXISTS_TAC“FV_subst (s:^subs) (FV (t:'a term) DIFF {v})”
            THEN CONJ_TAC
            THENL
              [ REWRITE_TAC[FV_subst]
                THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,IN_DIFF]
                THEN REWRITE_TAC[IN,o_THM]
                THEN EXISTS_TAC “si:var -> bool”
                THEN FIRST_ASSUM REWRITE_THM
                THEN EXISTS_TAC “x':var”
                THEN REPEAT CONJ_TAC
                THEN FIRST_ASSUM ACCEPT_TAC,

                ASM_REWRITE_TAC[]
                THEN MATCH_MP_TAC variant_not_in_set
                THEN MATCH_MP_TAC FINITE_FV_subst
                THEN MATCH_MP_TAC FINITE_DIFF
                THEN REWRITE_TAC[FINITE_FV]
              ]
          ]
      ]
   );


val NOT_IN_FV_subst = store_thm
   ("NOT_IN_FV_subst",
    “!y x t:'a term s.
         ~(y IN FV t) /\ ~(y IN s)
          ==> ~(y IN FV_subst [x,t] s)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[FV_subst]
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM,SUB]
    THEN STRIP_TAC
    THEN UNDISCH_LAST_TAC
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THENL
      [ ASM_REWRITE_TAC[],

        ASM_REWRITE_TAC[FV_term,IN]
        THEN IMP_RES_THEN (IMP_RES_THEN (REWRITE_THM o GSYM)) IN_NOT_IN
      ]
   );


val NOT_IN_FV_subst2 = store_thm
   ("NOT_IN_FV_subst2",
    “!y x1 (t1:^term) x2 t2 s.
         ~(y IN FV t1) /\ ~(y IN FV t2) /\ ~(y IN s)
          ==> ~(y IN FV_subst [(x1,t1);(x2,t2)] s)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[FV_subst]
    THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,o_THM,SUB]
    THEN STRIP_TAC
    THEN UNDISCH_LAST_TAC
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THENL
      [ ASM_REWRITE_TAC[],

        COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[],

            ASM_REWRITE_TAC[FV_term,IN]
            THEN IMP_RES_THEN (IMP_RES_THEN (REWRITE_THM o GSYM)) IN_NOT_IN
          ]
      ]
   );



val LAMBDA_CHANGE_BOUND_VAR = store_thm
   ("LAMBDA_CHANGE_BOUND_VAR",
    “!y x t:'a term.
         ~(y IN (FV t DIFF {x})) ==>
         (Lam x t =
          Lam y (t <[ [x, Var y]))”,
    REPEAT STRIP_TAC
    THEN ASSUME_TAC (SPECL [“t:'a term”,“x:var”] subst_SAME_ONE)
    THEN FIRST_ASSUM (SUBST1_TAC o SYM)
    THEN FIRST_ASSUM (CONV_TAC o RAND_CONV o REWRITE_CONV o C cons nil)
    THEN MATCH_MP_TAC LAMBDA_CHANGE_VAR
    THEN ASM_REWRITE_TAC[FV_subst_NIL]
    THEN REWRITE_TAC[IN_DIFF,IN,DE_MORGAN_THM]
   );


val LAMBDA_RENAME = store_thm
   ("LAMBDA_RENAME",
    “!t1:'a term t2:'a term t1' x y.
          (Lam x t1 = Lam y t1') /\ (FV t2 SUBSET FV t1) ==>
          (Lam x t2 = Lam y (t2 <[ [x, Var y]))”,
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC LAMBDA_CHANGE_BOUND_VAR
    THEN IMP_RES_TAC SUBSET_DIFF
    THEN POP_ASSUM (MP_TAC o SPEC “{x:var}”)
    THEN POP_TAC
    THEN DISCH_TAC
    THEN IMP_RES_THEN MATCH_MP_TAC NOT_IN_SUBSET
    THEN ASM_REWRITE_TAC[GSYM FV_term]
    THEN REWRITE_TAC[FV_term,IN_DIFF,IN]
   );



val LAMBDA_CLEAN_VAR = store_thm
   ("LAMBDA_CLEAN_VAR",
    “!s x t:'a term. FINITE s ==>
         ?x' t'.
          ~(x' IN (FV t DIFF {x})) /\ ~(x' IN s) /\
          (HEIGHT t = HEIGHT t') /\
          (Lam x t = Lam x' t')”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPECL [“variant x ((FV (t:'a term) DIFF {x}) UNION s)”,
                        “x:var”,“t:'a term”]
                       LAMBDA_CHANGE_BOUND_VAR)
    THEN MP_TAC (SPECL [“x:var”,“(FV (t:'a term) DIFF {x}) UNION s”]
                       variant_not_in_set)
    THEN ASM_REWRITE_TAC[FINITE_UNION]
    THEN ASSUME_TAC (SPEC_ALL FINITE_FV)
    THEN IMP_RES_THEN REWRITE_THM FINITE_DIFF
    THEN REWRITE_TAC[IN_UNION,DE_MORGAN_THM]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[HEIGHT,INV_SUC_EQ] o
                      AP_TERM “HEIGHT:'a term -> num”)
    THEN EXISTS_TAC “variant x ((FV (t:'a term) DIFF {x}) UNION s)”
    THEN EXISTS_TAC
         “t <[ [x,Var (variant x ((FV (t:'a term) DIFF {x}) UNION s))]”
    THEN ASM_REWRITE_TAC[]
   );



val LAMBDA_LIST_CHANGE_BOUND_VAR = TAC_PROOF(([],
    “!os y x.
         EVERY (\t:'a term. ~(y IN (FV t DIFF {x}))) os ==>
         EVERY (\t:'a term. Lam x t = Lam y (t <[ [x, Var y])) os”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[EVERY_DEF]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC LAMBDA_CHANGE_BOUND_VAR,

        RES_TAC
      ]
   );

val FINITE_FOLDR = TAC_PROOF(([],
    “!(l:'a list) f (i:'b -> bool).
          (!x y. FINITE y ==> FINITE (f x y)) /\ FINITE i ==>
          FINITE (FOLDR f i l)”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[FOLDR]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN RES_TAC
   );

val FINITE_FOLDR_LEMMA = TAC_PROOF(([],
    “!os s x.
         FINITE s ==>
         FINITE (FOLDR (\t:'a term s. (FV t DIFF {x}) UNION s) s os)”),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FINITE_FOLDR
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[FINITE_UNION]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC FINITE_DIFF
    THEN REWRITE_TAC[FINITE_FV]
   );

val IN_FOLDR = TAC_PROOF(([],
    “!os s x z.
         ~(z IN FOLDR (\t:'a term s. (FV t DIFF {x}) UNION s) s os) ==>
         ~(z IN s) /\
         EVERY (\t:'a term. ~(z IN FV t DIFF {x})) os”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[EVERY_DEF,FOLDR]
    THEN BETA_TAC
    THEN REWRITE_TAC[IN_UNION,DE_MORGAN_THM]
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
   );

val EVERY_HEIGHT_LEMMA = TAC_PROOF(([],
    “!os x z.
         EVERY (\t:'a term. Lam x t = Lam z (t <[ [x,Var z])) os ==>
         EVERY (\x':'a term. HEIGHT x' = HEIGHT (x' <[ [x,Var z])) os
       ”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[EVERY_DEF]
    THEN BETA_TAC
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN UNDISCH_LAST_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[HEIGHT,INV_SUC_EQ] o
                       AP_TERM “HEIGHT:'a term -> num”)
    THEN STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val MAP2_MAP = TAC_PROOF(([],
    “!l (f:'a->'b->'c) g.
         MAP2 f l (MAP g l) = MAP (\x. f x (g x)) l”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[MAP2,MAP]
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[]
   );

val EVERY_MAP = TAC_PROOF(([],
    “!l P (f:'a->'b).
         EVERY P (MAP f l) = EVERY (P o f) l”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[EVERY_DEF,MAP]
    THEN ASM_REWRITE_TAC[o_THM]
   );

val LAMBDA_LIST_CLEAN_VAR = store_thm
   ("LAMBDA_LIST_CLEAN_VAR",
    “!s x os. FINITE s ==>
         ?z os'.
          ~(z IN s) /\
          EVERY (\t:'a term. ~(z IN (FV t DIFF {x}))) os /\
          EVERY I (MAP2 (\t t'. HEIGHT t = HEIGHT t') os os') /\
          EVERY I (MAP2 (\t t'. Lam x t = Lam z t') os os') /\
          (LENGTH os' = LENGTH os)”,

    let val s = “FOLDR (\t':'a term s. (FV t' DIFF {x}) UNION s) s os”
        val z = “variant x ^s”
    in
    REPEAT STRIP_TAC
    THEN DEFINE_NEW_VAR “z = ^z”
    THEN POP_ASSUM (ASSUME_TAC o SYM)
    THEN EXISTS_TAC “z:var”
    THEN EXISTS_TAC “MAP (\t:'a term. t <[ [x,Var z]) os”
    THEN MP_TAC (SPECL [“os:'a term list”,z,“x:var”]
                       LAMBDA_LIST_CHANGE_BOUND_VAR)
    THEN MP_TAC (SPECL [“x:var”,s] variant_not_in_set)
    THEN ASM_REWRITE_TAC[LENGTH_MAP]
    THEN IMP_RES_THEN REWRITE_THM FINITE_FOLDR_LEMMA
    THEN DISCH_TAC
    THEN IMP_RES_THEN REWRITE_THM IN_FOLDR
    THEN DISCH_TAC
    THEN REWRITE_TAC[MAP2_MAP]
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[EVERY_MAP,I_o_ID]
    THEN IMP_RES_TAC EVERY_HEIGHT_LEMMA
    end
   );



val EQ_subst =
    new_definition
    ("EQ_subst",
     “EQ_subst t (s1:^subs) s2 =
        (!x. (x IN t) ==>
             (SUB s1 x = SUB s2 x))”);


val SUB_CONTEXT = store_thm
   ("SUB_CONTEXT",
    “!t:'a term s1 s2.
         EQ_subst (FV t) s1 s2 ==> ((t <[ s1) = (t <[ s2))”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[EQ_subst,subst_EQ]
   );



val LAMBDA_SUBST_SIMPLE = store_thm
   ("LAMBDA_SUBST_SIMPLE",
    “!x t:'a term s.
         ~(x IN FV_subst s (FV t DIFF {x})) /\
         ~(x IN BV_subst s) ==>
         (Lam x t <[ s = Lam x (t <[ s))”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_term]
    THEN DEP_REWRITE_TAC[variant_ident,FINITE_FV_subst,FINITE_DIFF]
    THEN IMP_RES_TAC BV_subst_IDENT
    THEN ASM_REWRITE_TAC[FINITE_FV]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN DEP_ONCE_REWRITE_TAC[SPECL [“t:'a term”,
                        “CONS (x, Var x:'a term) s”,“s:^subs”]
                       SUB_CONTEXT]
    THEN REWRITE_TAC[EQ_subst]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


(*
val LAMBDA_SUBST_VAR = store_thm
   ("LAMBDA_SUBST_VAR",
    “!x t:'a term s.
         ?x' t':'a term.
          ~(x' IN (FV t DIFF {x})) /\
          ~(x' IN FV_subst s (FV t DIFF {x})) /\
          ~(x' IN FV_subst s (FV t' DIFF {x'})) /\
          ~(x' IN BV_subst s) /\
           (SUB s x' = Var x') /\
           (HEIGHT t = HEIGHT t') /\
           (Lam x t = Lam x' t') /\
          ((Lam x t <[ s) = Lam x' (t' <[ s))”,
    REPEAT GEN_TAC
    THEN MP_TAC (SPECL [“FV_subst (s:^subs) (FV (t:'a term) DIFF {x})
                           UNION BV_subst s”,
                        “x:var”,“t:'a term”]
                       LAMBDA_CLEAN_VAR)
    THEN REWRITE_TAC[FINITE_UNION,FINITE_BV_subst]
    THEN DEP_REWRITE_TAC[FINITE_FV_subst,FINITE_DIFF]
    THEN REWRITE_TAC[FINITE_FV,IN_UNION,DE_MORGAN_THM]
    THEN STRIP_TAC
    THEN EXISTS_TAC “x':var”
    THEN EXISTS_TAC “t':'a term”
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM (ASSUME_TAC o SYM o REWRITE_RULE[FV_term] o
                      AP_TERM “FV:'a term -> var -> bool”)
    THEN IMP_RES_TAC BV_subst_IDENT
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC LAMBDA_SUBST_SIMPLE
    THEN ASM_REWRITE_TAC[]
   );


val ALL_LAMBDA_OBJ_EQ = store_thm
   ("ALL_LAMBDA_OBJ_EQ",
    “!term_Prop:'a term -> bool.
          (!t. (\t. !t'. (?v x. Lam v t = Lam x t')
                          ==> term_Prop t') t)
          =
          (!t. term_Prop t)”,
    GEN_TAC
    THEN BETA_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN GEN_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN EXISTS_TAC “t:'a term”
    THEN EXISTS_TAC “v:var”
    THEN EXISTS_TAC “v:var”
    THEN REFL_TAC
   );
*)



(* ===================================================================== *)
(* End of the lifting of lambda calculus types and basic definitions     *)
(* to the higher, more abstract level where alpha-equivalent expressions *)
(* are actually equal in HOL.                                            *)
(* ===================================================================== *)




val _ = export_theory();

val _ = print_theory_to_file "-" "lift.lst";

val _ = html_theory "lift";

val _ = print_theory_size();
