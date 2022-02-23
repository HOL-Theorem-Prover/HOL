open HolKernel Parse boolLib;


(* --------------------------------------------------------------------- *)
(* Embedding the semantaics of objects as a foundational layer,          *)
(* according to Abadi and Cardelli, "A Theory of Objects."               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "lift";
val _ = ParseExtras.temp_loose_equality()


open prim_recTheory pairTheory pairLib listTheory;
open combinTheory pred_setTheory;
open numTheory numLib arithmeticTheory;
open bossLib;
open Mutual;
open dep_rewrite;
open more_listTheory more_setTheory;
open variableTheory;
open objectTheory;
open alphaTheory;

open quotientLib;

open tactics;
open Rsyntax;



val vars  =  ty_antiq( ==`:var list`== );
val subs  =  ty_antiq( ==`:(var # obj1) list`== );
val obj   =  ty_antiq( ==`:obj1`== );
val dict  =  ty_antiq( ==`:(string # method1) list`== );
val entry =  ty_antiq( ==`:string # method1`== );
val method = ty_antiq( ==`:method1`== );


val [ALPHA_obj_REFL, ALPHA_dict_REFL, ALPHA_entry_REFL, ALPHA_method_REFL]
    = CONJUNCTS ALPHA_REFL;

val [ALPHA_obj_SYM, ALPHA_dict_SYM, ALPHA_entry_SYM, ALPHA_method_SYM]
    = map (GEN_ALL o CONJUNCT2 o SPEC_ALL o REWRITE_RULE[EQ_IMP_THM])
                (CONJUNCTS ALPHA_SYM);

val [ALPHA_obj_TRANS, ALPHA_dict_TRANS, ALPHA_entry_TRANS, ALPHA_method_TRANS]
    = CONJUNCTS ALPHA_TRANS;

val ALPHA_obj_EQUIV = save_thm("ALPHA_obj_EQUIV",
    refl_sym_trans_equiv ALPHA_obj_REFL ALPHA_obj_SYM ALPHA_obj_TRANS);

val ALPHA_dict_EQUIV = save_thm("ALPHA_dict_EQUIV",
    refl_sym_trans_equiv ALPHA_dict_REFL ALPHA_dict_SYM ALPHA_dict_TRANS);

val ALPHA_entry_EQUIV = save_thm("ALPHA_entry_EQUIV",
    refl_sym_trans_equiv ALPHA_entry_REFL ALPHA_entry_SYM ALPHA_entry_TRANS);

val ALPHA_method_EQUIV = save_thm("ALPHA_method_EQUIV",
    refl_sym_trans_equiv ALPHA_method_REFL ALPHA_method_SYM ALPHA_method_TRANS);

val ALPHA_EQUIV = LIST_CONJ
    [ALPHA_obj_EQUIV, ALPHA_dict_EQUIV, ALPHA_entry_EQUIV, ALPHA_method_EQUIV];


(* ALPHA_dict/entry_EQUIV will not be used, rather SUBST_EQUIV: *)

val SUBST_EQUIV = make_equiv [ALPHA_obj_EQUIV] [LIST_EQUIV, PAIR_EQUIV]
                      ``:(var # obj1) list``;


val ALPHA_entry_EQ = store_thm
   ("ALPHA_entry_EQ",
    “ALPHA_entry = ($= ### ALPHA_method)”,
    CONV_TAC (FUN_EQ_CONV THENC RAND_CONV (ABS_CONV FUN_EQ_CONV))
    THEN Cases
    THEN Cases
    THEN ASM_REWRITE_TAC[ALPHA_object_pos,ALPHA_object_neg,PAIR_REL_THM]
   );

val ALPHA_dict_EQ = store_thm
   ("ALPHA_dict_EQ",
    “ALPHA_dict = LIST_REL ($= ### ALPHA_method)”,
    CONV_TAC (FUN_EQ_CONV THENC RAND_CONV (ABS_CONV FUN_EQ_CONV))
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[ALPHA_object_pos,ALPHA_object_neg,LIST_REL_def,
                         ALPHA_entry_EQ]
   );





(* Prove the respectfulness theorems for the functions to be lifted. *)

val ALPHA_object_pos1 =
    REWRITE_RULE[ALPHA_dict_EQ,ALPHA_entry_EQ] ALPHA_object_pos;

val OVAR1_RSP = store_thm
   ("OVAR1_RSP",
    “!x1 x2.
          (x1 = x2) ==>
          ALPHA_obj (OVAR1 x1) (OVAR1 x2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA_object_pos1]
   );

val OBJ1_RSP = store_thm
   ("OBJ1_RSP",
    “!d1 d2.
          LIST_REL ($= ### ALPHA_method) d1 d2 ==>
          ALPHA_obj (OBJ1 d1) (OBJ1 d2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA_object_pos1]
   );

val INVOKE1_RSP = store_thm
   ("INVOKE1_RSP",
    “!o1 o2 s1 s2.
          ALPHA_obj o1 o2 /\ (s1 = s2) ==>
          ALPHA_obj (INVOKE1 o1 s1) (INVOKE1 o2 s2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA_object_pos1]
   );

val UPDATE1_RSP = store_thm
   ("UPDATE1_RSP",
    “!o1 o2 s1 s2 m1 m2.
          ALPHA_obj o1 o2 /\ (s1 = s2) /\ ALPHA_method m1 m2 ==>
          ALPHA_obj (UPDATE1 o1 s1 m1) (UPDATE1 o2 s2 m2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA_object_pos]
   );

val SIGMA1_RSP = store_thm
   ("SIGMA1_RSP",
    “!x1 x2 o1 o2.
          (x1 = x2) /\ ALPHA_obj o1 o2 ==>
          ALPHA_method (SIGMA1 x1 o1) (SIGMA1 x2 o2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ALPHA_method_SIGMA]
   );

val [HEIGHT_obj1_RSP, HEIGHT_dict1_RSP, HEIGHT_entry1_RSP, HEIGHT_method1_RSP]
    = CONJUNCTS (REWRITE_RULE[ALPHA_dict_EQ,ALPHA_entry_EQ] ALPHA_HEIGHT);

val [FV_obj1_RSP, FV_dict1_RSP, FV_entry1_RSP, FV_method1_RSP]
    = CONJUNCTS (REWRITE_RULE[ALPHA_dict_EQ,ALPHA_entry_EQ] ALPHA_FV);

val vsubst1_RSP = store_thm
   ("vsubst1_RSP",
    “!xs1 xs2 ys1 ys2.
          (xs1 = xs2) /\ (ys1 = ys2) ==>
          LIST_REL ($= ### ALPHA_obj) (xs1 // ys1) ((xs2 // ys2):^subs)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[equiv_refl SUBST_EQUIV]
   );

val ALPHA_SUB1 = store_thm
   ("ALPHA_SUB1",
    “!s1:^subs s2 x. LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
                        ALPHA_obj (SUB1 s1 x) (SUB1 s2 x)”,
    LIST_INDUCT_TAC
    THENL [ALL_TAC, GEN_TAC]
    THEN LIST_INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LIST_REL_def]
    THEN REWRITE_TAC[SUB1_def]
    THEN REWRITE_TAC[ALPHA_obj_REFL]
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

val SUB1_RSP = store_thm
   ("SUB1_RSP",
    “!s1:^subs s2 x1 x2.
         LIST_REL ($= ### ALPHA_obj) s1 s2 /\ (x1 = x2) ==>
         ALPHA_obj (SUB1 s1 x1) (SUB1 s2 x2)”,
    REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN ASM_REWRITE_TAC[]
   );


val FV_subst_RSP = store_thm
   ("FV_subst_RSP",
    “!s1:^subs s2 xs ys.
         LIST_REL ($= ### ALPHA_obj) s1 s2 /\ (xs = ys) ==>
         (FV_subst1 s1 xs = FV_subst1 s2 ys)”,
    REPEAT STRIP_TAC
    THEN POP_ASSUM REWRITE_THM
    THEN REWRITE_TAC[FV_subst1]
    THEN AP_TERM_TAC
    THEN AP_THM_TAC
    THEN AP_TERM_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[o_THM]
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_FV))
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_subst_obj_RSP = store_thm
   ("ALPHA_subst_obj_RSP",
    “!s1:^subs s2 o1:obj1.
         LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ALPHA_subst (FV_obj1 o1) s1 s2”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[ALPHA_subst]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val ALPHA_subst_dict_RSP = store_thm
   ("ALPHA_subst_dict_RSP",
    “!s1:^subs s2 d.
         LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ALPHA_subst (FV_dict1 d) s1 s2”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[ALPHA_subst]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val ALPHA_subst_entry_RSP = store_thm
   ("ALPHA_subst_entry_RSP",
    “!s1:^subs s2 e.
         LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ALPHA_subst (FV_entry1 e) s1 s2”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[ALPHA_subst]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val ALPHA_subst_method_RSP = store_thm
   ("ALPHA_subst_method_RSP",
    “!s1:^subs s2 m.
         LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ALPHA_subst (FV_method1 m) s1 s2”,
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[ALPHA_subst]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN MATCH_MP_TAC ALPHA_SUB1
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val SUBo_RSP = store_thm
   ("SUBo_RSP",
    “!o1:^obj o2 s1 s2.
         ALPHA_obj o1 o2 /\ LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ALPHA_obj (o1 <[ s1) (o2 <[ s2)”,
    REPEAT STRIP_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_SUB_CONTEXT))
    THEN IMP_RES_TAC ALPHA_subst_obj_RSP
    THEN ASM_REWRITE_TAC[]
   );

val ALPHA_SUB_CONTEXT =
    REWRITE_RULE[ALPHA_dict_EQ,ALPHA_entry_EQ] ALPHA_SUB_CONTEXT;

val SUBd_RSP = store_thm
   ("SUBd_RSP",
    “!d1 d2 s1 s2.
         LIST_REL ($= ### ALPHA_method) d1 d2 /\
         LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         LIST_REL ($= ### ALPHA_method) (d1 <[ s1) (d2 <[ s2)”,
    REPEAT STRIP_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS (ALPHA_SUB_CONTEXT)))
    THEN IMP_RES_TAC ALPHA_subst_dict_RSP
    THEN ASM_REWRITE_TAC[]
   );

val SUBe_RSP = store_thm
   ("SUBe_RSP",
    “!e1 e2 s1 s2.
         ($= ### ALPHA_method) e1 e2 /\ LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ($= ### ALPHA_method) (e1 <[ s1) (e2 <[ s2)”,
    REPEAT STRIP_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_SUB_CONTEXT))
    THEN IMP_RES_TAC ALPHA_subst_entry_RSP
    THEN ASM_REWRITE_TAC[]
   );

val SUBm_RSP = store_thm
   ("SUBm_RSP",
    “!m1 m2 s1 s2.
         ALPHA_method m1 m2 /\ LIST_REL ($= ### ALPHA_obj) s1 s2 ==>
         ALPHA_method (m1 <[ s1) (m2 <[ s2)”,
    REPEAT STRIP_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_SUB_CONTEXT))
    THEN IMP_RES_TAC ALPHA_subst_method_RSP
    THEN ASM_REWRITE_TAC[]
   );


val ALPHA_subst_RSP = store_thm
   ("ALPHA_subst_RSP",
    “!s1:^subs s2 t1 t2 (t:var -> bool).
         LIST_REL ($= ### ALPHA_obj) s1 s2 /\
         LIST_REL ($= ### ALPHA_obj) t1 t2 ==>
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
    “!REL (abs:'a -> 'b) rep.
         QUOTIENT REL abs rep
         ==>
         !s1 s2.
          (LIST_REL ($= ### REL)) s1 s2 ==>
          (BV_subst s1 = BV_subst s2)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
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
    “!REL (abs:'a -> 'b) rep.
         QUOTIENT REL abs rep
         ==>
         !s. BV_subst s = BV_subst (MAP(I ## rep) s)”,
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN Induct
    THEN REWRITE_TAC[MAP]
    THEN REWRITE_TAC[BV_subst_def]
    THEN Cases
    THEN REWRITE_TAC[PAIR_MAP_THM,I_THM,FST]
    THEN AP_TERM_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val FV_subst_EQ1' = store_thm
   ("FV_subst_EQ1'",
    “!s1:^subs s2 t.
          (!x. (x IN t) ==> ALPHA_obj (SUB1 s1 x) (SUB1 s2 x)) ==>
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
        THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_FV))
        THEN RES_TAC,

        EXISTS_TAC “x':var”
        THEN ASM_REWRITE_TAC[]
        THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
        THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_FV))
        THEN RES_TAC
      ]
   );


val TAUT_PROVE = EQT_ELIM o tautLib.TAUT_CONV;
val OR_IMP = TAUT_PROVE “(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))”;

val subst_EQ1' = store_thm
   ("subst_EQ1'",
    “(!a s1 s2.
            (!x. (x IN FV_obj1 a) ==> ALPHA_obj (SUB1 s1 x) (SUB1 s2 x)) ==>
                  ALPHA_obj (a <[ s1) (a <[ s2)) /\
        (!a s1 s2.
            (!x. (x IN FV_dict1 a) ==> ALPHA_obj (SUB1 s1 x) (SUB1 s2 x)) ==>
                  LIST_REL ($= ### ALPHA_method) (a <[ s1) (a <[ s2)) /\
        (!a s1 s2.
            (!x. (x IN FV_entry1 a) ==> ALPHA_obj (SUB1 s1 x) (SUB1 s2 x)) ==>
                  ($= ### ALPHA_method) (a <[ s1) (a <[ s2)) /\
        (!a s1 s2.
            (!x. (x IN FV_method1 a) ==> ALPHA_obj (SUB1 s1 x) (SUB1 s2 x)) ==>
                  ALPHA_method (a <[ s1) (a <[ s2))”,
    Induct
    THEN REWRITE_TAC[FV_object1_def,IN_UNION,IN]
    THEN REWRITE_TAC[OR_IMP]
    THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_object1_def]
    THEN RES_TAC
    (* 8 subgoals *)
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN REFL_TAC,

        MATCH_MP_TAC OBJ1_RSP
        THEN FIRST_ASSUM ACCEPT_TAC,

        MATCH_MP_TAC INVOKE1_RSP
        THEN ASM_REWRITE_TAC[],

        MATCH_MP_TAC UPDATE1_RSP
        THEN REWRITE_TAC[]
        THEN CONJ_TAC
        THEN FIRST_ASSUM ACCEPT_TAC,

        IMP_RES_THEN REWRITE_THM FV_subst_EQ1'
        THEN CONV_TAC (DEPTH_CONV let_CONV)
        THEN MATCH_MP_TAC SIGMA1_RSP
        THEN REWRITE_TAC[]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN REWRITE_TAC[SUB1]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[ALPHA_REFL]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[IN_DIFF,IN],

        REWRITE_TAC[LIST_REL_def],

        REWRITE_TAC[LIST_REL_def]
        THEN CONJ_TAC
        THEN FIRST_ASSUM ACCEPT_TAC,

        REWRITE_TAC[PAIR_REL_THM]
        THEN FIRST_ASSUM ACCEPT_TAC
      ]
   );


val BV_subst_IDENT1 = store_thm
   ("BV_subst_IDENT1",
    “!s:^subs x. ~(x IN (BV_subst s)) ==> (SUB1 s x = OVAR1 x)”,
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
          HEIGHT_obj1 (SUB1 ((xs // ys):^subs) v) = 0”,
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
    “(!t:^obj xs ys.
          HEIGHT_obj1 (t <[ (xs // ys)) = HEIGHT_obj1 t) /\
        (!t:^dict xs ys.
          HEIGHT_dict1 (t <[ (xs // ys)) = HEIGHT_dict1 t) /\
        (!t:^entry xs ys.
          HEIGHT_entry1 (t <[ (xs // ys)) = HEIGHT_entry1 t) /\
        (!t:^method xs ys.
          HEIGHT_method1 (t <[ (xs // ys)) = HEIGHT_method1 t)”,
    Induct
    THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[SUB_object1_def,SUB1,HEIGHT1_def]
    THENL
      [ REWRITE_TAC[HEIGHT1_SUB1_var],

        CONV_TAC (DEPTH_CONV let_CONV)
        THEN ONCE_REWRITE_TAC[GSYM vsubst1]
        THEN ASM_REWRITE_TAC[HEIGHT1_def]
      ]
   );

val HEIGHT1_var_subst = store_thm
   ("HEIGHT1_var_subst",
    “(!t:^obj x y.
          HEIGHT_obj1 (t <[ [x, OVAR1 y]) = HEIGHT_obj1 t) /\
        (!t:^dict x y.
          HEIGHT_dict1 (t <[ [x, OVAR1 y]) = HEIGHT_dict1 t) /\
        (!t:^entry x y.
          HEIGHT_entry1 (t <[ [x, OVAR1 y]) = HEIGHT_entry1 t) /\
        (!t:^method x y.
          HEIGHT_method1 (t <[ [x, OVAR1 y]) = HEIGHT_method1 t)”,
    REWRITE_TAC[GSYM vsubst1]
    THEN REWRITE_TAC[HEIGHT1_var_list_subst]
   );


val object1_distinct' = store_thm
   ("object1_distinct'",
    “((!x d.       ~(ALPHA_obj (OVAR1 x)       (OBJ1 d        : ^obj))) /\
         (!x a l.     ~(ALPHA_obj (OVAR1 x)       (INVOKE1 a l   : ^obj))) /\
         (!x a l m.   ~(ALPHA_obj (OVAR1 x)       (UPDATE1 a l m : ^obj))) /\
         (!d a l.     ~(ALPHA_obj (OBJ1 d)        (INVOKE1 a l   : ^obj))) /\
         (!d a l m.   ~(ALPHA_obj (OBJ1 d)        (UPDATE1 a l m : ^obj))) /\
         (!a l b s m. ~(ALPHA_obj (INVOKE1 a l)   (UPDATE1 b s m : ^obj))) /\
         (!d x.       ~(ALPHA_obj (OBJ1 d)        (OVAR1 x       : ^obj))) /\
         (!a l x.     ~(ALPHA_obj (INVOKE1 a l)   (OVAR1 x       : ^obj))) /\
         (!a l m x.   ~(ALPHA_obj (UPDATE1 a l m) (OVAR1 x       : ^obj))) /\
         (!a l d.     ~(ALPHA_obj (INVOKE1 a l)   (OBJ1 d        : ^obj))) /\
         (!a l m d.   ~(ALPHA_obj (UPDATE1 a l m) (OBJ1 d        : ^obj))) /\
         (!a l m b s. ~(ALPHA_obj (UPDATE1 a l m) (INVOKE1 b s   : ^obj))))
       ”,
    REWRITE_TAC[ALPHA_object,ALPHA1_object_neg]
   );


val object1_cases' = store_thm
   ("object1_cases'",
    “(!a:^obj. (?x. ALPHA_obj a (OVAR1 x)) \/
                  (?d. ALPHA_obj a (OBJ1 d)) \/
                  (?b l. ALPHA_obj a (INVOKE1 b l)) \/
                  (?b l m. ALPHA_obj a (UPDATE1 b l m))) /\
        (!d.      (?e d'. ALPHA_dict d (e::d')) \/
                  (ALPHA_dict d [])) /\
        (!e.      (?l m. ALPHA_entry e (l,m))) /\
        (!m.      (?x a. ALPHA_method m (SIGMA1 x a)))”,
    REPEAT STRIP_TAC
    THENL (map (STRIP_ASSUME_TAC o SPEC_ALL) (CONJUNCTS object1_cases))
    THEN PROVE_TAC[ALPHA_object_pos,ALPHA_REFL]
    );


val object1_one_one' = store_thm
   ("object1_one_one'",
    “(!a a'. ALPHA_obj (OVAR1 a) (OVAR1 a') = (a = a')) /\
        (!a a'. ALPHA_obj (OBJ1 a) (OBJ1 a') = ALPHA_dict a a') /\
        (!a0 a1 a0' a1'.
                  ALPHA_obj (INVOKE1 a0 a1) (INVOKE1 a0' a1') =
                  ALPHA_obj a0 a0' /\ (a1 = a1')) /\
        (!a0 a1 a2 a0' a1' a2'.
                  ALPHA_obj (UPDATE1 a0 a1 a2) (UPDATE1 a0' a1' a2') =
                  ALPHA_obj a0 a0' /\ (a1 = a1') /\ ALPHA_method a2 a2') /\
        (!a0 a1 a0' a1'. ALPHA_dict (a0::a1) (a0'::a1') =
                       ALPHA_entry a0 a0' /\ ALPHA_dict a1 a1') /\
        (!a0 a1 a0' a1'. ALPHA_entry (a0,a1) (a0',a1') =
                       (a0 = a0') /\ ALPHA_method a1 a1') /\
        (!a0 a1 a1'. ALPHA_method (SIGMA1 a0 a1) (SIGMA1 a0 a1') =
                       ALPHA_obj a1 a1')”,
    REWRITE_TAC[ALPHA_object_pos,ALPHA_method_one_one,subst_SAME_ONE1]
   );


(* AXIOM 3 *)

(* Melham and Gordon's third axiom, on alpha-equivalence. *)

val CHANGE_ONE_VAR1 = store_thm
   ("CHANGE_ONE_VAR1",
    “!x v t.
         ~(x IN FV_method1 (SIGMA1 v t)) ==>
         ALPHA_method (SIGMA1 v t) (SIGMA1 x (t <[ [(v, OVAR1 x)]))”,
    REWRITE_TAC[FV_object1_def]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC ALPHA_CHANGE_ONE_VAR
    THEN ONCE_REWRITE_TAC[ALPHA_SYM]
    THEN ASM_REWRITE_TAC[]
   );




(* ------------------------------------------------------------------- *)
(* We now begin the development that leads to the lifting of           *)
(* the "function existance" theorem for the lambda calculus.           *)
(* This is AXIOM 4 for Gordon and Melham in "Five Axioms" paper.       *)
(* They proved their axiom from an underlying deBruijn representa-     *)
(* tion, but to my knowledge this has never been proven for a name-    *)
(* carrying syntax at the lower level like this before, and has        *)
(* never been automatically lifted to the higher, abstract level.      *)
(*                                                                     *)
(* Most of this is to express this theorem at the lower level as:      *)
(*                                                                     *)
(* !(var : var->'a) obj inv upd cns nil par sgm.                       *)
(*    ?!ho :: respects(ALPHA_obj,$=).                                  *)
(*    ?!hd :: respects(ALPHA_dict,$=).                                 *)
(*    ?!he :: respects(ALPHA_entry,$=).                                *)
(*    ?!hm :: respects(ALPHA_method,$=).                               *)
(*       (!x.     ho (OVAR1 x) = var x) /\                             *)
(*       (!d.     ho (OBJ1 d) = obj (hd d)) /\                         *)
(*       (!a l.   ho (INVOKE1 a l) = inv (ho a) l) /\                  *)
(*       (!a l m. ho (UPDATE1 a l m) = upd (ho a) l (hm m)) /\         *)
(*       (!e d.   hd (e::d) = cns (he e) (hd d)) /\                    *)
(*       (        hd [] = nil) /\                                      *)
(*       (!l m.   he (l,m) = par l (hm m)) /\                          *)
(*       (!x a.   hm (SIGMA1 x a) = sgm (\y. ho (a <[ [x, OVAR1 y])))  *)
(*                                                                     *)
(* ------------------------------------------------------------------- *)

(*
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
*)

val object1_hom_def =
    Hol_defn "object1_hom"
    `(hom_o (OVAR1 x) var obj nvk upd cns nil par sgm = (var x):'a) /\
     (hom_o (OBJ1 d) var obj nvk upd cns nil par sgm =
         obj (hom_d d var obj nvk upd cns nil par sgm) d) /\
     (hom_o (INVOKE1 a l) var obj nvk upd cns nil par sgm =
         nvk (hom_o a var obj nvk upd cns nil par sgm) a l) /\
     (hom_o (UPDATE1 a l m) var obj nvk upd cns nil par sgm =
         upd (hom_o a var obj nvk upd cns nil par sgm)
            (hom_m m var obj nvk upd cns nil par sgm) a l m) /\
     (hom_d (e::d) var obj nvk upd cns nil par sgm =
         cns (hom_e e var obj nvk upd cns nil par sgm)
             (hom_d d var obj nvk upd cns nil par sgm) e d) /\
     (hom_d ([]) var obj nvk upd cns nil par sgm = nil:'b) /\
     (hom_e (l,m) var obj nvk upd cns nil par sgm =
         (par (hom_m m var obj nvk upd cns nil par sgm) l m):'c) /\
     (hom_m (SIGMA1 x a) var obj nvk upd cns nil par sgm =
         (sgm (\y. hom_o (a <[ [x, OVAR1 y]) var obj nvk upd cns nil par sgm)
              (\y. a <[ [x, OVAR1 y])
          :'d))`;

val _ = set_fixity "+-+" (Infixr 490);

Definition SUMVAL_def:
  (($+-+ f g) (INL (x:'a)) = ((f x):'c)) /\
  (($+-+ f g) (INR (y:'b)) = ((g y):'c))
End

val PBETA_TAC = PairRules.PBETA_TAC
val PGEN_TAC = PairRules.PGEN_TAC

(*
Defn.tgoal object1_hom_def;
e(WF_REL_TAC `measure (
           HEIGHT_obj1 o FST
       +-+ HEIGHT_dict1 o FST
       +-+ HEIGHT_entry1 o FST
       +-+ HEIGHT_method1 o FST)`);
e(REPEAT CONJ_TAC);
(* 8 subgoals *)

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_REFL]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def,HEIGHT1_var_subst]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_REFL]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_MAX]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_MAX]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT PGEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_MAX]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_REFL]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_REFL]);

  e(REWRITE_TAC[SUMVAL_def]);
  e(PBETA_TAC);
  e(REWRITE_TAC[HEIGHT1_def]);
  e(REPEAT GEN_TAC);
  e(MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC);
  e(REWRITE_TAC[LESS_EQ_MAX]);
*)

val (object1_hom_eqns, object1_hom_ind) =
   Defn.tprove
    (object1_hom_def,
     WF_REL_TAC `measure (
                    HEIGHT_obj1 o FST
                +-+ HEIGHT_dict1 o FST
                +-+ HEIGHT_entry1 o FST
                +-+ HEIGHT_method1 o FST)`
     THEN REWRITE_TAC[SUMVAL_def]
     THEN PBETA_TAC
     THEN REWRITE_TAC[HEIGHT1_var_subst]
     THEN REWRITE_TAC[HEIGHT1_def]
     THEN REPEAT CONJ_TAC
     THEN REPEAT PGEN_TAC
     THEN MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC
     THEN REWRITE_TAC[LESS_EQ_MAX,LESS_EQ_REFL]
    );



val object1_hom_RSP_LEMMA = TAC_PROOF(([],
    “!(var :var -> 'a) obj nvk upd cns (nil:'b)
           (par:'d -> string -> method1 -> 'c) sgm.
         respects($= ===> ALPHA_dict ===> $=) obj /\
         respects($= ===> ALPHA_obj ===> $= ===> $=) nvk /\
         respects($= ===> $= ===> ALPHA_obj ===> $= ===> ALPHA_method ===> $=)
               upd /\
         respects($= ===> $= ===> ALPHA_entry ===> ALPHA_dict ===> $=) cns /\
         respects($= ===> $= ===> ALPHA_method ===> $=) par /\
         respects($= ===> ($= ===> ALPHA_obj) ===> $=) sgm ==>
        !n.
         (!t:^obj u. (HEIGHT_obj1 t <= n) /\ ALPHA_obj t u ==>
             (hom_o t var obj nvk upd cns nil par sgm =
              hom_o u var obj nvk upd cns nil par sgm)) /\
         (!t:^dict u. (HEIGHT_dict1 t <= n) /\ ALPHA_dict t u ==>
             (hom_d t var obj nvk upd cns nil par sgm =
              hom_d u var obj nvk upd cns nil par sgm)) /\
         (!t:^entry u. (HEIGHT_entry1 t <= n) /\ ALPHA_entry t u ==>
             (hom_e t var obj nvk upd cns nil par sgm =
              hom_e u var obj nvk upd cns nil par sgm)) /\
         (!t:^method u. (HEIGHT_method1 t <= n) /\ ALPHA_method t u ==>
             (hom_m t var obj nvk upd cns nil par sgm =
              hom_m u var obj nvk upd cns nil par sgm))”),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[RESPECTS,FUN_REL]
    THEN CONV_TAC (RATOR_CONV (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
    THEN REWRITE_TAC[AND_IMP_INTRO,GSYM CONJ_ASSOC]
    THEN STRIP_TAC
    THEN INDUCT_TAC (* two subgoals *)
    THENL [ ALL_TAC, POP_ASSUM STRIP_ASSUME_TAC ]
    THEN REPEAT CONJ_TAC (* 8 subgoals *)
    THEN Cases THEN Cases (* 44 subgoals *)
    THEN REWRITE_TAC[HEIGHT1_def,LESS_EQ_0,NOT_SUC,SUC_NOT]
    THEN REWRITE_TAC[ALPHA_object_neg]
    THEN REWRITE_TAC[ALPHA_object_pos]
    THEN REWRITE_TAC[INV_SUC_EQ,LESS_EQ_MONO,MAX_LESS_EQ]
    THEN REWRITE_TAC[ZERO_LESS_EQ]
    THEN REWRITE_TAC[object1_hom_eqns]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[] (* 6 subgoals *)
    THEN TRY (FIRST_ASSUM MATCH_MP_TAC
              THEN ASM_REWRITE_TAC[]
              THEN REPEAT CONJ_TAC
              THEN FIRST_ASSUM MATCH_MP_TAC
              THEN ASM_REWRITE_TAC[]
              THEN NO_TAC)
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN CONJ_TAC
    THENL
      [ CONV_TAC FUN_EQ_CONV
        THEN GEN_TAC
        THEN BETA_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[HEIGHT1_var_subst]
        THEN MATCH_MP_TAC ALPHA_SIGMA_subst
        THEN FIRST_ASSUM ACCEPT_TAC,

        REPEAT GEN_TAC
        THEN DISCH_THEN REWRITE_THM
        THEN BETA_TAC
        THEN MATCH_MP_TAC ALPHA_SIGMA_subst
        THEN FIRST_ASSUM ACCEPT_TAC
      ]
   );


val object1_hom_RSP = TAC_PROOF(([],
    “!(var :var -> 'a) obj nvk upd cns (nil:'b)
           (par:'d -> string -> method1 -> 'c) sgm.
          respects($= ===> ALPHA_dict ===> $=) obj /\
          respects($= ===> ALPHA_obj ===> $= ===> $=) nvk /\
          respects($= ===> $= ===> ALPHA_obj ===> $= ===> ALPHA_method ===> $=)
                upd /\
          respects($= ===> $= ===> ALPHA_entry ===> ALPHA_dict ===> $=) cns /\
          respects($= ===> $= ===> ALPHA_method ===> $=) par /\
          respects($= ===> ($= ===> ALPHA_obj) ===> $=) sgm ==>
          respects(ALPHA_obj ===> $=)
                     (\a. hom_o a var obj nvk upd cns nil par sgm) /\
          respects(ALPHA_dict ===> $=)
                     (\d. hom_d d var obj nvk upd cns nil par sgm) /\
          respects(ALPHA_entry ===> $=)
                     (\e. hom_e e var obj nvk upd cns nil par sgm) /\
          respects(ALPHA_method ===> $=)
                     (\m. hom_m m var obj nvk upd cns nil par sgm)”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[RESPECTS,FUN_REL]
    THEN MP_TAC (SPEC_ALL object1_hom_RSP_LEMMA)
    THEN ASM_REWRITE_TAC[]
    THEN CONV_TAC (TOP_DEPTH_CONV FORALL_AND_CONV)
    THEN REPEAT STRIP_TAC
    THEN BETA_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN PROVE_TAC[LESS_EQ_REFL]
   );



val RESPECTS_PAIR_REL = store_thm(
    "RESPECTS_PAIR_REL",
    “!R1 R2 (a:'a) (b:'b).
          respects (R1 ### R2) (a,b) =
          respects R1 a /\ respects R2 b”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[RESPECTS,PAIR_REL_THM]
   );

val object1_respects_Axiom_exists = store_thm(
    "object1_respects_Axiom_exists",
    “!(var :var -> 'a) obj nvk upd cns (nil:'b)
           (par:'d -> string -> method1 -> 'c) sgm.
          respects($= ===> ALPHA_dict ===> $=) obj /\
          respects($= ===> ALPHA_obj ===> $= ===> $=) nvk /\
          respects($= ===> $= ===> ALPHA_obj ===> $= ===> ALPHA_method ===> $=)
                upd /\
          respects($= ===> $= ===> ALPHA_entry ===> ALPHA_dict ===> $=) cns /\
          respects($= ===> $= ===> ALPHA_method ===> $=) par /\
          respects($= ===> ($= ===> ALPHA_obj) ===> $=) sgm ==>
         ?(hom_o, hom_d, hom_e, hom_m)
              :: respects((ALPHA_obj ===> $=) ###
                          (ALPHA_dict ===> $=) ###
                          (ALPHA_entry ===> $=) ###
                          (ALPHA_method ===> $=)).
           (!x.     hom_o (OVAR1 x) = var x) /\
           (!d.     hom_o (OBJ1 d) = obj (hom_d d) d) /\
           (!a l.   hom_o (INVOKE1 a l) = nvk (hom_o a) a l) /\
           (!a l m. hom_o (UPDATE1 a l m) = upd (hom_o a) (hom_m m) a l m) /\
           (!e d.   hom_d (e::d) = cns (hom_e e) (hom_d d) e d) /\
           (        hom_d ([]) = nil) /\
           (!l m.   hom_e (l,m) = (par (hom_m m) l m):'c) /\
           (!x a.   hom_m (SIGMA1 x a) =
                    ((sgm (\y. hom_o (a <[ [x, OVAR1 y]))
                          (\y. a <[ [x, OVAR1 y]) )):'d)”,
    REPEAT GEN_TAC
    THEN DISCH_THEN (STRIP_ASSUME_TAC o SPEC_ALL o MATCH_MP object1_hom_RSP)
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_CONV)
    THEN EXISTS_TAC
           “((\t:^obj.    hom_o t (var:var->'a) obj nvk upd cns
                                   (nil:'b) (par:'d->string->method1->'c) sgm),
                (\t:^dict.   hom_d t var obj nvk upd cns nil par sgm),
                (\t:^entry.  hom_e t var obj nvk upd cns nil par sgm),
                (\t:^method. hom_m t var obj nvk upd cns nil par sgm))”
    THEN REWRITE_TAC[SPECIFICATION]
    THEN REWRITE_TAC[RESPECTS_PAIR_REL]
    THEN ASM_REWRITE_TAC[]
    THEN PairRules.PBETA_TAC
    THEN BETA_TAC
    THEN REWRITE_TAC[object1_hom_eqns]
   );


val object1_respects_Axiom_11_LEMMA = TAC_PROOF(([],
    “!hom_o1 hom_o2 hom_d1 hom_d2 hom_e1 hom_e2 hom_m1 hom_m2
         (var :var -> 'a) obj nvk upd cns (nil:'b)
           (par:'d -> string -> method1 -> 'c) sgm.
           hom_o1 IN respects (ALPHA_obj ===> $=) /\
           hom_o2 IN respects (ALPHA_obj ===> $=) /\
           hom_d1 IN respects (ALPHA_dict ===> $=) /\
           hom_d2 IN respects (ALPHA_dict ===> $=) /\
           hom_e1 IN respects (ALPHA_entry ===> $=) /\
           hom_e2 IN respects (ALPHA_entry ===> $=) /\
           hom_m1 IN respects (ALPHA_method ===> $=) /\
           hom_m2 IN respects (ALPHA_method ===> $=) /\
           ((!x.     hom_o1 (OVAR1 x) = var x) /\
            (!d.     hom_o1 (OBJ1 d) = obj (hom_d1 d) d) /\
            (!a l.   hom_o1 (INVOKE1 a l) = nvk (hom_o1 a) a l) /\
            (!a l m. hom_o1 (UPDATE1 a l m) = upd (hom_o1 a)(hom_m1 m)a l m) /\
            (!e d.   hom_d1 (e::d) = cns (hom_e1 e) (hom_d1 d) e d) /\
            (        hom_d1 ([]) = nil) /\
            (!l m.   hom_e1 (l,m) = (par (hom_m1 m) l m):'c) /\
            (!x a.   hom_m1 (SIGMA1 x a) =
                     ((sgm (\y. hom_o1 (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d)) /\
           ((!x.     hom_o2 (OVAR1 x) = var x) /\
            (!d.     hom_o2 (OBJ1 d) = obj (hom_d2 d) d) /\
            (!a l.   hom_o2 (INVOKE1 a l) = nvk (hom_o2 a) a l) /\
            (!a l m. hom_o2 (UPDATE1 a l m) = upd (hom_o2 a)(hom_m2 m)a l m) /\
            (!e d.   hom_d2 (e::d) = cns (hom_e2 e) (hom_d2 d) e d) /\
            (        hom_d2 ([]) = nil) /\
            (!l m.   hom_e2 (l,m) = (par (hom_m2 m) l m):'c) /\
            (!x a.   hom_m2 (SIGMA1 x a) =
                     ((sgm (\y. hom_o2 (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d))
           ==>
           (!n. (!t. (HEIGHT_obj1 t <= n) ==> (hom_o1 t = hom_o2 t)) /\
                (!t. (HEIGHT_dict1 t <= n) ==> (hom_d1 t = hom_d2 t)) /\
                (!t. (HEIGHT_entry1 t <= n) ==> (hom_e1 t = hom_e2 t)) /\
                (!t. (HEIGHT_method1 t <= n) ==> (hom_m1 t = hom_m2 t)))”),
    REWRITE_TAC[SPECIFICATION,RESPECTS_THM]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN Induct
    THENL [ ALL_TAC, POP_ASSUM STRIP_ASSUME_TAC ]
    THEN REPEAT CONJ_TAC
    THEN Cases (* 16 subgoals *)
    THEN REWRITE_TAC[HEIGHT1_def,LESS_EQ_0,NOT_SUC]
    THEN REWRITE_TAC[LESS_EQ_MONO,MAX_LESS_EQ]
    THEN REWRITE_TAC[ZERO_LESS_EQ]
    THEN ASM_REWRITE_TAC[] (* 6 subgoals *)
    THEN STRIP_TAC
    THEN TRY (RES_TAC
              THEN ASM_REWRITE_TAC[]
              THEN NO_TAC)
    THEN AP_THM_TAC
    THEN AP_TERM_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN BETA_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[HEIGHT1_var_subst]
   );

val object1_respects_Axiom_11_LEMMA2 = TAC_PROOF(([],
    “!hom_o1 hom_o2 hom_d1 hom_d2 hom_e1 hom_e2 hom_m1 hom_m2
         (var :var -> 'a) obj nvk upd cns (nil:'b)
           (par:'d -> string -> method1 -> 'c) sgm.
           hom_o1 IN respects (ALPHA_obj ===> $=) /\
           hom_o2 IN respects (ALPHA_obj ===> $=) /\
           hom_d1 IN respects (ALPHA_dict ===> $=) /\
           hom_d2 IN respects (ALPHA_dict ===> $=) /\
           hom_e1 IN respects (ALPHA_entry ===> $=) /\
           hom_e2 IN respects (ALPHA_entry ===> $=) /\
           hom_m1 IN respects (ALPHA_method ===> $=) /\
           hom_m2 IN respects (ALPHA_method ===> $=) /\
           ((!x.     hom_o1 (OVAR1 x) = var x) /\
            (!d.     hom_o1 (OBJ1 d) = obj (hom_d1 d) d) /\
            (!a l.   hom_o1 (INVOKE1 a l) = nvk (hom_o1 a) a l) /\
            (!a l m. hom_o1 (UPDATE1 a l m) = upd (hom_o1 a)(hom_m1 m)a l m) /\
            (!e d.   hom_d1 (e::d) = cns (hom_e1 e) (hom_d1 d) e d) /\
            (        hom_d1 ([]) = nil) /\
            (!l m.   hom_e1 (l,m) = (par (hom_m1 m) l m):'c) /\
            (!x a.   hom_m1 (SIGMA1 x a) =
                     ((sgm (\y. hom_o1 (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d)) /\
           ((!x.     hom_o2 (OVAR1 x) = var x) /\
            (!d.     hom_o2 (OBJ1 d) = obj (hom_d2 d) d) /\
            (!a l.   hom_o2 (INVOKE1 a l) = nvk (hom_o2 a) a l) /\
            (!a l m. hom_o2 (UPDATE1 a l m) = upd (hom_o2 a)(hom_m2 m)a l m) /\
            (!e d.   hom_d2 (e::d) = cns (hom_e2 e) (hom_d2 d) e d) /\
            (        hom_d2 ([]) = nil) /\
            (!l m.   hom_e2 (l,m) = (par (hom_m2 m) l m):'c) /\
            (!x a.   hom_m2 (SIGMA1 x a) =
                     ((sgm (\y. hom_o2 (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d))
           ==>
           (hom_o1 = hom_o2) /\
           (hom_d1 = hom_d2) /\
           (hom_e1 = hom_e2) /\
           (hom_m1 = hom_m2)”),
    REPEAT GEN_TAC
    THEN DISCH_THEN (STRIP_ASSUME_TAC o
                      MATCH_MP object1_respects_Axiom_11_LEMMA)
    THEN POP_ASSUM (STRIP_ASSUME_TAC o
                      CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV))
    THEN REPEAT CONJ_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN PROVE_TAC[LESS_EQ_REFL]
   );

val object1_respects_Axiom_11 = store_thm(
    "object1_respects_Axiom_11",
    “!(var :var -> 'a) obj nvk upd cns (nil:'b)
         (par:'d -> string -> method1 -> 'c) sgm.
        !(hom_o1, hom_d1, hom_e1, hom_m1) ::
                 respects((ALPHA_obj ===> $=) ###
                          (ALPHA_dict ===> $=) ###
                          (ALPHA_entry ===> $=) ###
                          (ALPHA_method ===> $=)) .
        !(hom_o2, hom_d2, hom_e2, hom_m2) ::
                 respects((ALPHA_obj ===> $=) ###
                          (ALPHA_dict ===> $=) ###
                          (ALPHA_entry ===> $=) ###
                          (ALPHA_method ===> $=)) .
           ((!x.     hom_o1 (OVAR1 x) = var x) /\
            (!d.     hom_o1 (OBJ1 d) = obj (hom_d1 d) d) /\
            (!a l.   hom_o1 (INVOKE1 a l) = nvk (hom_o1 a) a l) /\
            (!a l m. hom_o1 (UPDATE1 a l m) = upd (hom_o1 a)(hom_m1 m)a l m) /\
            (!e d.   hom_d1 (e::d) = cns (hom_e1 e) (hom_d1 d) e d) /\
            (        hom_d1 ([]) = nil) /\
            (!l m.   hom_e1 (l,m) = (par (hom_m1 m) l m):'c) /\
            (!x a.   hom_m1 (SIGMA1 x a) =
                     ((sgm (\y. hom_o1 (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d)) /\
           ((!x.     hom_o2 (OVAR1 x) = var x) /\
            (!d.     hom_o2 (OBJ1 d) = obj (hom_d2 d) d) /\
            (!a l.   hom_o2 (INVOKE1 a l) = nvk (hom_o2 a) a l) /\
            (!a l m. hom_o2 (UPDATE1 a l m) = upd (hom_o2 a)(hom_m2 m)a l m) /\
            (!e d.   hom_d2 (e::d) = cns (hom_e2 e) (hom_d2 d) e d) /\
            (        hom_d2 ([]) = nil) /\
            (!l m.   hom_e2 (l,m) = (par (hom_m2 m) l m):'c) /\
            (!x a.   hom_m2 (SIGMA1 x a) =
                     ((sgm (\y. hom_o2 (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d))
           ==>
           (hom_o1 = hom_o2) /\
           (hom_d1 = hom_d2) /\
           (hom_e1 = hom_e2) /\
           (hom_m1 = hom_m2)”,
    REPEAT GEN_TAC
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN PairRules.PBETA_TAC
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN PairRules.PBETA_TAC
    THEN STRIP_TAC
    THEN MATCH_MP_TAC (SPEC_ALL object1_respects_Axiom_11_LEMMA2)
    THEN ASM_REWRITE_TAC[]
    THEN UNDISCH_ALL_TAC
    THEN DISCH_THEN (ASSUME_TAC o PURE_ONCE_REWRITE_RULE [GSYM PAIR])
    THEN DISCH_THEN (ASSUME_TAC o PURE_ONCE_REWRITE_RULE [GSYM PAIR])
    THEN UNDISCH_ALL_TAC
    THEN PURE_REWRITE_TAC[SPECIFICATION,RESPECTS_PAIR_REL]
    THEN STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o PURE_ONCE_REWRITE_RULE [GSYM PAIR])
    THEN STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o PURE_ONCE_REWRITE_RULE [GSYM PAIR])
    THEN UNDISCH_ALL_TAC
    THEN PURE_REWRITE_TAC[SPECIFICATION,RESPECTS_PAIR_REL]
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o PURE_ONCE_REWRITE_RULE [GSYM PAIR])
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o PURE_ONCE_REWRITE_RULE [GSYM PAIR])
    THEN UNDISCH_ALL_TAC
    THEN PURE_REWRITE_TAC[SPECIFICATION,RESPECTS_PAIR_REL]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );



fun PAIR_LAMBDA_CONV abs =
   let val {Bvar=x, Body=body} = dest_abs abs
       val {Name, Ty} = dest_var x
       val tys = strip_prod Ty
       val free = free_vars abs
       val xs = foldl (fn (ty,vrs) =>
                         vrs @ [prim_variant (vrs @ free)
                                        (mk_var{Name=Name, Ty=ty})]) [] tys
       val p = list_mk_pair xs
       val body' = beta_conv (mk_comb{Rator=abs, Rand=p})
       val abs' = mk_pabs(p, body')
       val eq_tm = mk_eq{lhs=abs, rhs=abs'}
       val th = TAC_PROOF(([],eq_tm),
                     CONV_TAC FUN_EQ_CONV
                     THEN PairRules.PBETA_TAC
                     THEN GEN_TAC
                     THEN REFL_TAC)
   in th end;

fun CHECK_RATOR_NAME_CONV nm tm =
    let val {Rator, Rand} = dest_comb tm
        val _ = assert (curry op = nm o #Name o dest_const) Rator
    in
        REFL tm
    end;

val PAIR_EXISTS_CONV = CHECK_RATOR_NAME_CONV "?"
                       THENC RAND_CONV PAIR_LAMBDA_CONV;

val PAIR_FORALL_CONV = CHECK_RATOR_NAME_CONV "!"
                       THENC RAND_CONV PAIR_LAMBDA_CONV;

val PAIR_RES_EXISTS_CONV = RATOR_CONV (CHECK_RATOR_NAME_CONV "RES_EXISTS")
                       THENC RAND_CONV PAIR_LAMBDA_CONV;

val PAIR_RES_FORALL_CONV = RATOR_CONV (CHECK_RATOR_NAME_CONV "RES_FORALL")
                       THENC RAND_CONV PAIR_LAMBDA_CONV;



val object1_respects_Axiom = store_thm(
    "object1_respects_Axiom",
    “!(var :var -> 'a)
         (obj :: respects($= ===> ALPHA_dict ===> $=))
         (nvk :: respects($= ===> ALPHA_obj ===> $= ===> $=))
         (upd :: respects($= ===> $= ===> ALPHA_obj ===> $= ===>
                           ALPHA_method ===> $=))
         (cns :: respects($= ===> $= ===> ALPHA_entry ===> ALPHA_dict ===> $=))
         (nil:'b)
         (par:'d -> string -> method1 -> 'c
             :: respects($= ===> $= ===> ALPHA_method ===> $=))
         (sgm :: respects($= ===> ($= ===> ALPHA_obj) ===> $=)).
        ?!(hom_o, hom_d, hom_e, hom_m)
          :: respects((ALPHA_obj ===> $=) ###
                      (ALPHA_dict ===> $=) ###
                      (ALPHA_entry ===> $=) ###
                      (ALPHA_method ===> $=)).
            (!x.     hom_o (OVAR1 x) = var x) /\
            (!d.     hom_o (OBJ1 d) = obj (hom_d d) d) /\
            (!a l.   hom_o (INVOKE1 a l) = nvk (hom_o a) a l) /\
            (!a l m. hom_o (UPDATE1 a l m) = upd (hom_o a) (hom_m m) a l m) /\
            (!e d.   hom_d (e::d) = cns (hom_e e) (hom_d d) e d) /\
            (        hom_d ([]) = nil) /\
            (!l m.   hom_e (l,m) = (par (hom_m m) l m):'c) /\
            (!x a.   hom_m (SIGMA1 x a) =
                     ((sgm (\y. hom_o (a <[ [x, OVAR1 y]))
                           (\y. a <[ [x, OVAR1 y]))):'d)”,
    REPEAT (GEN_TAC ORELSE res_quanLib.RESQ_GEN_TAC)
    THEN CONV_TAC res_quanLib.RES_EXISTS_UNIQUE_CONV
    THEN CONJ_TAC
    THENL
      [ CONV_TAC PAIR_RES_EXISTS_CONV
        THEN PairRules.PBETA_TAC
        THEN REWRITE_ALL_TAC[SPECIFICATION]
        THEN IMP_RES_TAC (res_quanLib.RESQ_REWR_CANON
                                object1_respects_Axiom_exists)
        THEN ASM_REWRITE_TAC[],

        CONV_TAC (DEPTH_CONV PAIR_RES_FORALL_CONV)
        THEN PairRules.PBETA_TAC
        THEN REWRITE_TAC[PAIR_EQ]
        THEN REWRITE_TAC[object1_respects_Axiom_11]
      ]
   );


(* ---------------------------------------------------------------- *)
(* Now we develop the last of the Gordon-Melham axioms, that states *)
(* the existence of a function `Abs' such that                      *)
(*         SIGMA x a = ABS (\y. a <[ [x, OVAR y])                   *)
(* ---------------------------------------------------------------- *)

val ABS1_def =
    Define
    `ABS1 (f : var -> obj1) =
        let x = VAR "x" 0 in
        let v = variant x (FV_obj1 (f x)) in
           SIGMA1 v (f v)`;

(* Prove ABS1 is respectful. *)

val ABS1_ALPHA_LEMMA = store_thm
   ("ABS1_ALPHA_LEMMA",
    “!f1 f2 x.
          ($= ===> ALPHA_obj) f1 f2  ==>
          (variant x (FV_obj1 (f1 x)) = variant x (FV_obj1 (f2 x)))”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN AP_TERM_TAC
    THEN FIRST (map MATCH_MP_TAC (CONJUNCTS ALPHA_FV))
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REFL_TAC
   );

val ABS1_ALPHA = store_thm
   ("ABS1_ALPHA",
    “!f1 f2 :var->obj1.
          ($= ===> ALPHA_obj) f1 f2  ==>
          ALPHA_method (ABS1 f1) (ABS1 f2)”,
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC ABS1_ALPHA_LEMMA
    THEN ASM_REWRITE_TAC[ABS1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN MATCH_MP_TAC SIGMA1_RSP
    THEN REWRITE_ALL_TAC[FUN_REL]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REFL_TAC
   );

val SINGLE_vsubst = TAC_PROOF(([],
    “!x y:var.
          [x, OVAR1 y :obj1] = ([x] // [y])”),
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

val SIGMA1_ABS1 = store_thm
   ("SIGMA1_ABS1",
    “!x a:obj1.
           ALPHA_method (SIGMA1 x a) (ABS1 (\y. a <[ [x, OVAR1 y]))”,
    REPEAT GEN_TAC
    THEN REWRITE_TAC[ABS1_def]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN BETA_TAC
    THEN ONCE_REWRITE_TAC[ALPHA_SYM]
    THEN MATCH_MP_TAC ALPHA_CHANGE_ONE_VAR
    THEN MATCH_MP_TAC variant_not_in_subset
    THEN REWRITE_TAC[FINITE_FV_object1]
    THEN REWRITE_TAC[SINGLE_vsubst,SINGLE_SL]
    THEN REWRITE_TAC[FV_vsubst1]
   );


(* ---------------------------------------------------------------- *)
(* Now we prepare for the creation of the quotient of the object    *)
(* calculus syntax by alpha-equivalence.  Accordingly, we establish *)
(* the arguments to be passed to the quotient tool.                 *)
(* ---------------------------------------------------------------- *)

val equivs = [ALPHA_obj_EQUIV, ALPHA_method_EQUIV];

val fnlist = [{def_name="OVAR_def", fname="OVAR",
               func= “OVAR1 :var->^obj”, fixity=NONE
                                        (* see structure Parse *)},
              {def_name="OBJ_def", fname="OBJ",
               func= “OBJ1 :^dict -> ^obj”, fixity=NONE},
              {def_name="INVOKE_def", fname="INVOKE",
               func= “INVOKE1 :^obj -> string -> ^obj”, fixity=NONE},
              {def_name="UPDATE_def", fname="UPDATE",
               func= “UPDATE1 :^obj -> string -> ^method -> ^obj”,
               fixity=NONE},
              {def_name="SIGMA_def", fname="SIGMA",
               func= “SIGMA1 :var -> ^obj -> ^method”, fixity=NONE},
              {def_name="ABS_def", fname="ABS",
               func= “ABS1 :(var -> ^obj) -> ^method”, fixity=NONE},
              {def_name="HEIGHT_obj_def", fname="HEIGHT_obj",
               func= “HEIGHT_obj1 :^obj -> num”, fixity=NONE},
              {def_name="HEIGHT_dict_def", fname="HEIGHT_dict",
               func= “HEIGHT_dict1 :^dict -> num”, fixity=NONE},
              {def_name="HEIGHT_entry_def", fname="HEIGHT_entry",
               func= “HEIGHT_entry1 :^entry -> num”, fixity=NONE},
              {def_name="HEIGHT_method_def", fname="HEIGHT_method",
               func= “HEIGHT_method1 :^method -> num”, fixity=NONE},
              {def_name="FV_obj_def", fname="FV_obj",
               func= “FV_obj1 :^obj -> var -> bool”, fixity=NONE},
              {def_name="FV_dict_def", fname="FV_dict",
               func= “FV_dict1 :^dict -> var -> bool”, fixity=NONE},
              {def_name="FV_entry_def", fname="FV_entry",
               func= “FV_entry1 :^entry -> var -> bool”, fixity=NONE},
              {def_name="FV_method_def", fname="FV_method",
               func= “FV_method1 :^method -> var -> bool”,fixity=NONE},
              {def_name="SUB_def", fname="SUB",
               func= “SUB1 :^subs -> var -> ^obj”, fixity=NONE},
              {def_name="FV_subst_def", fname="FV_subst",
               func= “FV_subst1 :^subs -> (var -> bool) -> var -> bool”,
               fixity=NONE},
              {def_name="SUBo_def", fname="SUBo",
               func= “SUB1o :^obj -> ^subs -> ^obj”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="SUBd_def", fname="SUBd",
               func= “SUB1d :^dict -> ^subs -> ^dict”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="SUBe_def", fname="SUBe",
               func= “SUB1e :^entry -> ^subs -> ^entry”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="SUBm_def", fname="SUBm",
               func= “SUB1m :^method -> ^subs -> ^method”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="vsubst_def", fname="/",
               func= “$// :var list -> var list -> ^subs”,
               fixity=SOME(Infix(NONASSOC,150))},
              {def_name="obj_0_def", fname="obj_0",
               func= “obj1_0”, fixity=NONE},
              {def_name="method_0_def", fname="method_0",
               func= “method1_0”, fixity=NONE},
              {def_name="invoke_method_def", fname="invoke_method",
               func= “invoke_method1”, fixity=NONE},
              {def_name="invoke_dict_def", fname="invoke_dict",
               func= “invoke_dict1”, fixity=NONE},
              {def_name="invoke_def", fname="invoke",
               func= “invoke1”, fixity=NONE},
              {def_name="update_dict_def", fname="update_dict",
               func= “update_dict1”, fixity=NONE},
              {def_name="update_def", fname="update",
               func= “update1”, fixity=NONE},
              {def_name="subst_eq_def", fname="subst_eq",
               func= “ALPHA_subst:(var -> bool) ->^subs ->^subs -> bool”,
               fixity=NONE}
             ];


val respects = [OVAR1_RSP, OBJ1_RSP, INVOKE1_RSP, UPDATE1_RSP, SIGMA1_RSP,
                ABS1_ALPHA, ALPHA_subst_RSP,
                HEIGHT_obj1_RSP, HEIGHT_dict1_RSP, HEIGHT_entry1_RSP,
                HEIGHT_method1_RSP, FV_obj1_RSP, FV_dict1_RSP, FV_entry1_RSP,
                FV_method1_RSP, SUB1_RSP, FV_subst_RSP, vsubst1_RSP,
                SUBo_RSP, SUBd_RSP, SUBe_RSP, SUBm_RSP,
                obj1_0_RSP,method1_0_RSP,
                invoke_method1_RSP,
                REWRITE_RULE[ALPHA_dict_EQ] invoke_dict1_RSP,
                invoke1_RSP,
                REWRITE_RULE[ALPHA_dict_EQ] update_dict1_RSP,
                update1_RSP]

val polydfs = [BV_subst_PRS]

val polywfs = [BV_subst_RSP]


fun gg tm = proofManagerLib.set_goal([],tm);


val term_EQ_IS_ALPHA =
    TAC_PROOF
   (([],
     “(!t x.
           (t = OVAR1 x) = ALPHA_obj t (OVAR1 x)) /\
         (!d:(string # method1) list.
           (d = []) = LIST_REL ($= ### ALPHA_method) d [])”),
    REPEAT CONJ_TAC
    THEN Cases
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[object1_one_one,object1_distinct,
                     ALPHA_object_pos,ALPHA_object_neg,GSYM ALPHA_dict_EQ]
   );


val old_thms =
     [HEIGHT1_def,
      REWRITE_RULE[term_EQ_IS_ALPHA] HEIGHT_LESS_EQ_ZERO1,
      FV_object1_def,
      FINITE_FV_object1,
      SUB1,
      SUB1_def,
      SUB_vsubst_OVAR1,
      REWRITE_RULE[term_EQ_IS_ALPHA] IN_FV_SUB_vsubst1,
      SUB_APPEND_vsubst1,
      SUB_FREE_vsubst1,
      FV_subst1,
      FINITE_FV_subst1,
      FV_subst_EQ1',
      REWRITE_RULE[term_EQ_IS_ALPHA] FV_subst_IDENT1,
      FV_subst_NIL1,
      SUB_object1_def,
      ALPHA_method_SIGMA,
      subst_SAME_ONE1,
      (* subst_SAME_TWO1, *)
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
      object1_distinct',
      object1_cases, (* not regular, but lifts! *)
      REWRITE_RULE[ALPHA_dict_EQ,ALPHA_entry_EQ] object1_one_one',
      ALPHA_method_one_one,
      vsubst1_def,
      vsubst1,
      SUB_APPEND_FREE_vsubst1,
      (* ALPHA_subst, *)
      ALPHA_SUB_CONTEXT,
      ALPHA_CHANGE_VAR,
      ALPHA_CHANGE_ONE_VAR,
      CHANGE_ONE_VAR1,
      ALPHA_SIGMA_subst,

      obj1_0,
      method1_0,
      invoke_method1_def,
      invoke_dict1_def,
      invoke_dict1,
      LIST_CONJ (map GEN_ALL (CONJUNCTS invoke1_def)),
      invoke1,
      update_dict1_def,
      update_dict1,
      LIST_CONJ (map GEN_ALL (CONJUNCTS update1_def)),
      update1,

      SIGMA1_ABS1,
      obj1_induction,
      REWRITE_RULE[ALPHA_dict_EQ,ALPHA_entry_EQ(*,FUN_REL_EQ*)]
            object1_respects_Axiom
      ];


(* ==================================================== *)
(*   LIFT TYPES, CONSTANTS, AND THEOREMS BY QUOTIENTS   *)
(* ==================================================== *)

val _ = quotient.chatting := true;

val [HEIGHT,
     HEIGHT_LESS_EQ_ZERO,
     FV_object, (* AXIOM 1 of Gordon and Melham *)
     FINITE_FV_object,
     SUB,
     SUB_def,
     SUB_vsubst_OVAR,
     IN_FV_SUB_vsubst,
     SUB_APPEND_vsubst,
     SUB_FREE_vsubst,
     FV_subst,
     FINITE_FV_subst,
     FV_subst_EQ,
     FV_subst_IDENT,
     FV_subst_NIL,
     SUB_object,
     SIGMA_EQ,
     subst_SAME_ONE,
     (* subst_SAME_TWO, *)
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
     object_distinct,
     object_cases,
     object_one_one,
     SIGMA_one_one,
     vsubst_def,
     vsubst,
     SUB_APPEND_FREE_vsubst,
     SUB_CONTEXT,
     SIGMA_CHANGE_VAR,
     SIGMA_CHANGE_ONE_VAR,
     CHANGE_ONE_VAR,
     SIGMA_subst,
     obj_0,
     method_0,
     invoke_method_def,
     invoke_dict_def,
     invoke_dict,
     invoke_def,
     invoke,
     update_dict_def,
     update_dict,
     update_def,
     update,
     SIGMA_ABS,
     object_induct,
     object_Axiom
     ] =
    define_quotient_types_full
    {types = [{name = "obj",    equiv = ALPHA_obj_EQUIV},
              {name = "method", equiv = ALPHA_method_EQUIV}],
     tyop_equivs = [],
     tyop_quotients = [],
     tyop_simps = [],
     defs = fnlist,
     respects = respects,
     poly_preserves = polydfs,
     poly_respects = polywfs,
     old_thms = old_thms};


val _ = map save_thm
    [("HEIGHT",HEIGHT),
     ("HEIGHT_LESS_EQ_ZERO",HEIGHT_LESS_EQ_ZERO),
     ("FV_object",FV_object), (* AXIOM 1 of Gordon and Melham *)
     ("FINITE_FV_object",FINITE_FV_object),
     ("SUB",SUB),
     ("SUB_def",SUB_def),
     ("SUB_vsubst_OVAR",SUB_vsubst_OVAR),
     ("IN_FV_SUB_vsubst",IN_FV_SUB_vsubst),
     ("SUB_APPEND_vsubst",SUB_APPEND_vsubst),
     ("SUB_FREE_vsubst",SUB_FREE_vsubst),
     ("FV_subst",FV_subst),
     ("FINITE_FV_subst",FINITE_FV_subst),
     ("FV_subst_EQ",FV_subst_EQ),
     ("FV_subst_IDENT",FV_subst_IDENT),
     ("FV_subst_NIL",FV_subst_NIL),
     ("SUB_object",SUB_object),
     ("SIGMA_EQ",SIGMA_EQ),
     ("subst_SAME_ONE",subst_SAME_ONE),
     (* ("subst_SAME_TWO",subst_SAME_TWO), *)
     ("subst_EQ",subst_EQ),
     ("FREE_SUB",FREE_SUB),
     ("BV_subst_IDENT",BV_subst_IDENT),
     ("BV_vsubst",BV_vsubst),
     ("FREE_FV_SUB",FREE_FV_SUB),
     ("FREE_IDENT_SUBST",FREE_IDENT_SUBST),
     ("subst_IDENT",subst_IDENT),
     ("subst_NIL",subst_NIL),
     ("HEIGHT_SUB_var",HEIGHT_SUB_var),
     ("HEIGHT_var_list_subst",HEIGHT_var_list_subst),
     ("HEIGHT_var_subst",HEIGHT_var_subst),
     ("object_distinct",object_distinct),
     ("object_cases",object_cases),
     ("object_one_one",object_one_one),
     ("SIGMA_one_one",SIGMA_one_one),
     ("vsubst_def",vsubst_def),
     ("vsubst",vsubst),
     ("SUB_APPEND_FREE_vsubst",SUB_APPEND_FREE_vsubst),
     ("SUB_CONTEXT",SUB_CONTEXT),
     ("SIGMA_CHANGE_VAR",SIGMA_CHANGE_VAR),
     ("SIGMA_CHANGE_ONE_VAR",SIGMA_CHANGE_ONE_VAR),
     ("CHANGE_ONE_VAR",CHANGE_ONE_VAR),
     ("SIGMA_subst",SIGMA_subst),
     ("obj_0",obj_0),
     ("method_0",method_0),
     ("invoke_method_def",invoke_method_def),
     ("invoke_dict_def",invoke_dict_def),
     ("invoke_dict",invoke_dict),
     ("invoke_def",invoke_def),
     ("invoke",invoke),
     ("update_dict_def",update_dict_def),
     ("update_dict",update_dict),
     ("update_def",update_def),
     ("update",update),
     ("SIGMA_ABS",SIGMA_ABS),
     ("object_induct",object_induct),
     ("object_Axiom",object_Axiom)
    ];



(* Now overload the substitution operator <[ to refer to any of the  *)
(* object, dict, entry, or method substitution operators defined:    *)

val _ = map (fn t => overload_on("<[", t))
            [“$SUBo”,“$SUBd”,“$SUBe”,“$SUBm”]
handle e => Raise e;

val subs  =  ty_antiq( ==`:(var # obj) list`== );
val obj   =  ty_antiq( ==`:obj`== );
val dict  =  ty_antiq( ==`:(string # method) list`== );
val entry =  ty_antiq( ==`:string # method`== );
val method = ty_antiq( ==`:method`== );






(* Now test the lifted induction principle: *)

val HEIGHT_LESS_EQ_ZERO = store_thm
   ("HEIGHT_LESS_EQ_ZERO",
    “(!o'. (HEIGHT_obj o' <= 0) = (?x. o' = OVAR x)) /\
        (!d. (HEIGHT_dict d <= 0) = (d = NIL)) /\
        (!e. (HEIGHT_entry e <= 0) = F) /\
        (!m. (HEIGHT_method m <= 0) = F)”,
    MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[HEIGHT]
    THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,LESS_EQ_REFL]
    THEN REWRITE_TAC[object_distinct,NOT_CONS_NIL,NOT_NIL_CONS]
    THEN REWRITE_TAC[object_one_one]
    THEN EXISTS_TAC “v:var”
    THEN REWRITE_TAC[]
   );


(* We will sometimes wish to induct on the height of an object. *)

val object_height_induct_LEMMA = store_thm
   ("object_height_induct_LEMMA",
    “!n obj_Prop dict_Prop entry_Prop method_Prop.
         (!x. obj_Prop (OVAR x)) /\
         (!d. dict_Prop d ==> obj_Prop (OBJ d)) /\
         (!o'. obj_Prop o' ==> (!l. obj_Prop (INVOKE o' l))) /\
         (!o' m.
           obj_Prop o' /\ method_Prop m ==> (!l. obj_Prop (UPDATE o' l m))) /\
         (!e d. entry_Prop e /\ dict_Prop d ==> dict_Prop (CONS e d)) /\
         dict_Prop [] /\
         (!m. method_Prop m ==> (!l. entry_Prop (l,m))) /\
         (!o'. (!o''. (HEIGHT_obj o' = HEIGHT_obj o'') ==> obj_Prop o'') ==>
               (!x. method_Prop (SIGMA x o'))) ==>
         (!o'. (HEIGHT_obj o' <= n) ==> obj_Prop o') /\
         (!d. (HEIGHT_dict d <= n) ==> dict_Prop d) /\
         (!e. (HEIGHT_entry e <= n) ==> entry_Prop e) /\
         (!m. (HEIGHT_method m <= n) ==> method_Prop m)”,
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
        THEN MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
        THEN REWRITE_TAC[HEIGHT]
        THEN REWRITE_TAC[MAX_SUC,MAX_LESS_EQ,LESS_EQ_MONO,ZERO_LESS_EQ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL (* 6 subgoals *)
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
            THEN REPEAT STRIP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN POP_ASSUM (REWRITE_THM o SYM)
            THEN FIRST_ASSUM ACCEPT_TAC,

            FIRST_ASSUM MATCH_MP_TAC
            THEN CONJ_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ,

            FIRST_ASSUM MATCH_MP_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
          ]
      ]
   );


val object_height_induct = store_thm
   ("object_height_induct",
    “!obj_Prop dict_Prop entry_Prop method_Prop.
         (!x. obj_Prop (OVAR x)) /\
         (!d. dict_Prop d ==> obj_Prop (OBJ d)) /\
         (!o'. obj_Prop o' ==> (!l. obj_Prop (INVOKE o' l))) /\
         (!o' m.
           obj_Prop o' /\ method_Prop m ==> (!l. obj_Prop (UPDATE o' l m))) /\
         (!e d. entry_Prop e /\ dict_Prop d ==> dict_Prop (CONS e d)) /\
         dict_Prop [] /\
         (!m. method_Prop m ==> (!l. entry_Prop (l,m))) /\
         (!o'. (!o2. (HEIGHT_obj o' = HEIGHT_obj o2) ==> obj_Prop o2) ==>
               (!x. method_Prop (SIGMA x o'))) ==>
         (!a. obj_Prop a) /\
         (!d. dict_Prop d) /\
         (!e. entry_Prop e) /\
         (!m. method_Prop m)”,
    REPEAT STRIP_TAC
    THENL
      (map (fn tm => MP_TAC (SPEC_ALL (SPEC tm object_height_induct_LEMMA)))
           [“HEIGHT_obj a”,“HEIGHT_dict d”,
            “HEIGHT_entry e”,“HEIGHT_method m”])
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[LESS_EQ_REFL]
   );


val HEIGHT_SUB_vsubst = store_thm
   ("HEIGHT_SUB_vsubst",
    “!xs ys x.
         HEIGHT_obj (SUB (xs / ys) x) = 0”,
    REPEAT GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC_ALL SUB_vsubst_OVAR)
    THEN ASM_REWRITE_TAC[HEIGHT]
   );


val subst_EMPTY = store_thm
   ("subst_EMPTY",
    “(!a x b. ~(x IN FV_obj a) ==> ((a <[ [x,b]) = a)) /\
        (!d x b. ~(x IN FV_dict d) ==> ((d <[ [x,b]) = d)) /\
        (!e x b. ~(x IN FV_entry e) ==> ((e <[ [x,b]) = e)) /\
        (!m x b. ~(x IN FV_method m) ==> ((m <[ [x,b]) = m))”,
    REPEAT STRIP_TAC
    THENL (map MATCH_MP_TAC (CONJUNCTS subst_IDENT))
    THEN REWRITE_TAC[SUB]
    THEN GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val FV_object_subst = store_thm
   ("FV_object_subst",
    “(!a s. FV_obj (a <[ s)    = FV_subst s (FV_obj a)) /\
        (!d s. FV_dict (d <[ s)   = FV_subst s (FV_dict d)) /\
        (!e s. FV_entry (e <[ s)  = FV_subst s (FV_entry e)) /\
        (!m s. FV_method (m <[ s) = FV_subst s (FV_method m))”,
    REWRITE_TAC[FV_subst]
    THEN MUTUAL_INDUCT_THEN object_induct ASSUME_TAC
    THEN REWRITE_TAC[SUB_object]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN REWRITE_TAC[FV_object]
    THEN ASM_REWRITE_TAC[IMAGE_UNION,UNION_SET_UNION]
    THEN REWRITE_TAC[IMAGE,UNION_SET,UNION_EMPTY,o_THM]
    (* only one subgoal at this point! *)
    THEN REPEAT GEN_TAC
    THEN DEFINE_NEW_VAR
         “v' = variant v (FV_subst s (FV_obj a DIFF {v}))”
    THEN FIRST_ASSUM (REWRITE_THM o SYM)
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_DIFF,IN_UNION_SET,IN_IMAGE]
    THEN REWRITE_TAC[IN,o_THM]
    THEN GEN_TAC
    THEN EQ_TAC
    THENL
      [ STRIP_TAC
        THEN EXISTS_TAC “si:var set”
        THEN (CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC))
        THEN EXISTS_TAC “x':var”
        THEN REWRITE_ALL_TAC[SUB]
        THEN SUBGOAL_THEN “~((v:var) = x')” ASSUME_TAC
        THENL
          [ DISCH_THEN (REWRITE_ALL_THM o SYM)
            THEN REWRITE_ALL_TAC[FV_object]
            THEN UNDISCH_THEN “si = {v':var}” REWRITE_ALL_THM
            THEN REWRITE_ALL_TAC[IN]
            THEN RES_TAC,

            FIRST_ASSUM (REWRITE_ALL_THM o GSYM)
            THEN CONJ_TAC
            THEN FIRST_ASSUM ACCEPT_TAC
          ],

        STRIP_TAC
        THEN CONJ_TAC
        THENL
          [ EXISTS_TAC “si:var set”
            THEN (CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC))
            THEN EXISTS_TAC “x':var”
            THEN (CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC))
            THEN REWRITE_TAC[SUB]
            THEN POP_ASSUM MP_TAC
            THEN FIRST_ASSUM (REWRITE_THM o GSYM)
            THEN ASM_REWRITE_TAC[],

            MATCH_MP_TAC IN_NOT_IN
            THEN EXISTS_TAC “FV_subst s (FV_obj a DIFF {v})”
            THEN CONJ_TAC
            THENL
              [ REWRITE_TAC[FV_subst]
                THEN REWRITE_TAC[IN_UNION_SET,IN_IMAGE,IN_DIFF]
                THEN REWRITE_TAC[IN,o_THM]
                THEN EXISTS_TAC “si:var set”
                THEN FIRST_ASSUM REWRITE_THM
                THEN EXISTS_TAC “x':var”
                THEN REPEAT CONJ_TAC
                THEN FIRST_ASSUM ACCEPT_TAC,

                ASM_REWRITE_TAC[]
                THEN MATCH_MP_TAC variant_not_in_set
                THEN MATCH_MP_TAC FINITE_FV_subst
                THEN MATCH_MP_TAC FINITE_DIFF
                THEN REWRITE_TAC[FINITE_FV_object]
              ]
          ]
      ]
   );


val NOT_IN_FV_subst = store_thm
   ("NOT_IN_FV_subst",
    “!y x a s.
         ~(y IN FV_obj a) /\ ~(y IN s)
          ==> ~(y IN FV_subst [x,a] s)”,
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

        ASM_REWRITE_TAC[FV_object,IN]
        THEN IMP_RES_THEN (IMP_RES_THEN (REWRITE_THM o GSYM)) IN_NOT_IN
      ]
   );


val NOT_IN_FV_subst2 = store_thm
   ("NOT_IN_FV_subst2",
    “!y x1 (t1:^obj) x2 t2 s.
         ~(y IN FV_obj t1) /\ ~(y IN FV_obj t2) /\ ~(y IN s)
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

            ASM_REWRITE_TAC[FV_object,IN]
            THEN IMP_RES_THEN (IMP_RES_THEN (REWRITE_THM o GSYM)) IN_NOT_IN
          ]
      ]
   );


val SIGMA_CHANGE_BOUND_VAR = store_thm
   ("SIGMA_CHANGE_BOUND_VAR",
    “!y x a.
         ~(y IN (FV_obj a DIFF {x})) ==>
         (SIGMA x a =
          SIGMA y (a <[ [x, OVAR y]))”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPECL [“y:var”,“x:var”,“[]:^subs”,
                        “x:var”,“a:obj”]
                       SIGMA_CHANGE_VAR)
    THEN REWRITE_TAC[FV_subst_NIL]
    THEN POP_ASSUM REWRITE_THM
    THEN REWRITE_TAC[IN_DIFF,IN,DE_MORGAN_THM]
    THEN DEP_ONCE_REWRITE_TAC[subst_IDENT]
    THEN GEN_TAC
    THEN REWRITE_TAC[SUB]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val SIGMA_CLEAN_VAR = store_thm
   ("SIGMA_CLEAN_VAR",
    “!s x a. FINITE s ==>
         ?x' o'.
          ~(x' IN (FV_obj a DIFF {x})) /\ ~(x' IN s) /\
          (HEIGHT_obj a = HEIGHT_obj o') /\
          (SIGMA x a = SIGMA x' o')”,
    REPEAT STRIP_TAC
    THEN MP_TAC (SPECL [“variant x ((FV_obj a DIFF {x}) UNION s)”,
                        “x:var”,“a:obj”]
                       SIGMA_CHANGE_BOUND_VAR)
    THEN MP_TAC (SPECL [“x:var”,“(FV_obj a DIFF {x}) UNION s”]
                       variant_not_in_set)
    THEN ASM_REWRITE_TAC[FINITE_UNION]
    THEN ASSUME_TAC (SPEC_ALL (CONJUNCT1 FINITE_FV_object))
    THEN IMP_RES_THEN REWRITE_THM FINITE_DIFF
    THEN REWRITE_TAC[IN_UNION,DE_MORGAN_THM]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[HEIGHT,INV_SUC_EQ] o
                      AP_TERM “HEIGHT_method”)
    THEN EXISTS_TAC “variant x ((FV_obj a DIFF {x}) UNION s)”
    THEN EXISTS_TAC
         “a <[ [x,OVAR (variant x ((FV_obj a DIFF {x}) UNION s))]”
    THEN ASM_REWRITE_TAC[]
   );


val SIGMA_LIST_CHANGE_BOUND_VAR = TAC_PROOF(([],
    “!os y x.
         EVERY (\a. ~(y IN (FV_obj a DIFF {x}))) os ==>
         EVERY (\a. SIGMA x a = SIGMA y (a <[ [x, OVAR y])) os”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[EVERY_DEF]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC SIGMA_CHANGE_BOUND_VAR,

        RES_TAC
      ]
   );

val FINITE_FOLDR = TAC_PROOF(([],
    “!(l:'a list) f (i:'b set).
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
         FINITE (FOLDR (\o' s. (FV_obj o' DIFF {x}) UNION s) s os)”),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FINITE_FOLDR
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[FINITE_UNION]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC FINITE_DIFF
    THEN REWRITE_TAC[FINITE_FV_object]
   );

val IN_FOLDR = TAC_PROOF(([],
    “!os s x z.
         ~(z IN FOLDR (\o' s. (FV_obj o' DIFF {x}) UNION s) s os) ==>
         ~(z IN s) /\
         EVERY (\a. ~(z IN FV_obj a DIFF {x})) os”),
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
         EVERY (\a. SIGMA x a = SIGMA z (a <[ [x,OVAR z])) os ==>
         EVERY (\x'. HEIGHT_obj x' = HEIGHT_obj (x' <[ [x,OVAR z])) os
       ”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[EVERY_DEF]
    THEN BETA_TAC
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN UNDISCH_LAST_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[HEIGHT,INV_SUC_EQ] o
                       AP_TERM “HEIGHT_method”)
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

val SIGMA_LIST_CLEAN_VAR = store_thm
   ("SIGMA_LIST_CLEAN_VAR",
    “!s x os. FINITE s ==>
         ?z os'.
          ~(z IN s) /\
          EVERY (\a. ~(z IN (FV_obj a DIFF {x}))) os /\
          EVERY I (MAP2 (\a o'. HEIGHT_obj a = HEIGHT_obj o') os os') /\
          EVERY I (MAP2 (\a o'. SIGMA x a = SIGMA z o') os os') /\
          (LENGTH os' = LENGTH os)”,

    let val s = “FOLDR (\o' s. (FV_obj o' DIFF {x}) UNION s) s os”
        val z = “variant x ^s”
    in
    REPEAT STRIP_TAC
    THEN DEFINE_NEW_VAR “z = ^z”
    THEN POP_ASSUM (ASSUME_TAC o SYM)
    THEN EXISTS_TAC “z:var”
    THEN EXISTS_TAC “MAP (\a:obj. a <[ [x,OVAR z]) os”
    THEN MP_TAC (SPECL [“os:obj list”,z,“x:var”]
                       SIGMA_LIST_CHANGE_BOUND_VAR)
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

(*
val EQ_subst =
    new_definition
    ("EQ_subst",
     “EQ_subst t s1 s2 =
        (!x. (x IN t) ==>
             (SUB s1 x = SUB s2 x))”);


val SUB_CONTEXT = store_thm
   ("SUB_CONTEXT",
    “(!a s1 s2.
          EQ_subst (FV_obj a) s1 s2 ==> ((a <[ s1) = (a <[ s2))) /\
        (!d s1 s2.
          EQ_subst (FV_dict d) s1 s2 ==> ((d <[ s1) = (d <[ s2))) /\
        (!e s1 s2.
          EQ_subst (FV_entry e) s1 s2 ==> ((e <[ s1) = (e <[ s2))) /\
        (!m s1 s2.
          EQ_subst (FV_method m) s1 s2 ==> ((m <[ s1) = (m <[ s2)))”,
    REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[EQ_subst,FV_object,SUB_def]
    THEN DISCH_TAC
    THEN REWRITE_TAC[object_REP_equal_equiv]
    THENL (map (REWRITE_THM o ALPHA_EQ_RULES) (CONJUNCTS REP_SUB_object))
    THENL (map MATCH_MP_TAC (CONJUNCTS ALPHA_SUB_CONTEXT))
    THEN REWRITE_TAC[ALPHA_REFL]
    THEN REWRITE_TAC[ALPHA_subst]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN UNDISCH_LAST_TAC
    THEN REWRITE_TAC[object_equiv_ABS_equal]
   );
*)

val SIGMA_SUBST_SIMPLE = store_thm
   ("SIGMA_SUBST_SIMPLE",
    “!x a s.
         ~(x IN FV_subst s (FV_obj a DIFF {x})) /\
         ~(x IN BV_subst s) ==>
         (SIGMA x a <[ s = SIGMA x (a <[ s))”,
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB_object]
    THEN DEP_REWRITE_TAC[variant_ident,FINITE_FV_subst,FINITE_DIFF]
    THEN IMP_RES_TAC BV_subst_IDENT
    THEN ASM_REWRITE_TAC[FINITE_FV_object]
    THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN DEP_ONCE_REWRITE_TAC[SPECL [“a:obj”,
                        “CONS (x, OVAR x) s”,“s:^subs”]
                       (CONJUNCT1 subst_EQ)]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SUB]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val SIGMA_SUBST_VAR = store_thm
   ("SIGMA_SUBST_VAR",
    “!x a s.
         ?x' o'.
          ~(x' IN (FV_obj a DIFF {x})) /\
          ~(x' IN FV_subst s (FV_obj a DIFF {x})) /\
          ~(x' IN FV_subst s (FV_obj o' DIFF {x'})) /\
          ~(x' IN BV_subst s) /\
           (SUB s x' = OVAR x') /\
           (HEIGHT_obj a = HEIGHT_obj o') /\
           (SIGMA x a = SIGMA x' o') /\
          ((SIGMA x a <[ s) = SIGMA x' (o' <[ s))”,
    REPEAT GEN_TAC
    THEN MP_TAC (SPECL [“FV_subst s (FV_obj a DIFF {x})
                           UNION BV_subst s”,
                        “x:var”,“a:obj”]
                       SIGMA_CLEAN_VAR)
    THEN REWRITE_TAC[FINITE_UNION,FINITE_BV_subst]
    THEN DEP_REWRITE_TAC[FINITE_FV_subst,FINITE_DIFF]
    THEN REWRITE_TAC[FINITE_FV_object,IN_UNION,DE_MORGAN_THM]
    THEN DISCH_THEN (Q.X_CHOOSE_THEN `x'`
                                     (Q.X_CHOOSE_THEN `o'` STRIP_ASSUME_TAC))
    THEN EXISTS_TAC “x':var”
    THEN EXISTS_TAC “o':obj”
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM (ASSUME_TAC o SYM o REWRITE_RULE[FV_object] o
                      AP_TERM “FV_method”)
    THEN IMP_RES_TAC BV_subst_IDENT
    THEN ASM_REWRITE_TAC[]
    THEN MATCH_MP_TAC SIGMA_SUBST_SIMPLE
    THEN ASM_REWRITE_TAC[]
   );


val ALL_SIGMA_OBJ_EQ = store_thm
   ("ALL_SIGMA_OBJ_EQ",
    “!obj_Prop.
          (!o'. (\o'. !o2. (?v x. SIGMA v o' = SIGMA x o2)
                            ==> obj_Prop o2) o')
          =
          (!o'. obj_Prop o')”,
    GEN_TAC
    THEN BETA_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN GEN_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN EXISTS_TAC “o':obj”
    THEN EXISTS_TAC “v:var”
    THEN EXISTS_TAC “v:var”
    THEN REFL_TAC
   );



(* ===================================================================== *)
(* End of the lifting of object calculus types and basic definitions     *)
(* to the higher, more abstract level where alpha-equivalent expressions *)
(* are actually equal in HOL.                                            *)
(* ===================================================================== *)



val _ = export_theory();

val _ = print_theory_to_file "lift.lst";

val _ = html_theory "lift";

val _ = print_theory_size();
