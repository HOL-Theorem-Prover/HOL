(*---------------------------------------------------------------------------*)
(* Higher order recursion on N-ary trees.                                    *)
(*---------------------------------------------------------------------------*)

set_trace "Unicode" 0;
set_trace "pp_annotations" 0;

use (HOLDIR^"/src/pfl/defchoose");

quietdec := true;
open arithmeticTheory optionTheory;
quietdec := false;

(*---------------------------------------------------------------------------*)
(* General purpose support.                                                  *)
(*---------------------------------------------------------------------------*)

val MAX_LE_THM = Q.prove
(`!m n. m <= MAX m n /\ n <= MAX m n`,
 RW_TAC arith_ss [MAX_DEF]);

val IS_SOME_EXISTS = Q.prove
(`!x. IS_SOME x = ?y. x = SOME y`,
 Cases THEN METIS_TAC [optionTheory.IS_SOME_DEF]);

(*---------------------------------------------------------------------------*)
(* Declare tree type.                                                        *)
(*---------------------------------------------------------------------------*)

Hol_datatype `tree = Node of 'a => tree list`;

(*---------------------------------------------------------------------------*)
(* pEXISTS : ('a -> bool option) -> 'a list -> bool option                   *)
(*                                                                           *)
(* Since we are in a setting with no notion of evaluation order, we have to  *)
(* imagine that any evaluation order will take place. Ugh. pEXISTS P l must  *)
(* return NONE if an invocation of P on any list element returns NONE.       *)
(* Otherwise, if there is an element x s.t. P x = SOME T, then return        *)
(* SOME T. Otherwise, return SOME F.                                         *)
(*---------------------------------------------------------------------------*)

val pEXISTS_def =
 Define
   `(pEXISTS P [] = SOME F) /\
    (pEXISTS P (h::t) =
       case pEXISTS P t
        of NONE -> NONE
        || SOME b ->
              case P h
               of NONE -> NONE
               || SOME F -> SOME b
               || SOME T -> SOME T)`;

val pEXISTS_CONG = Q.prove
(`!l1 l2 P P'.
     (l1 = l2) /\ (!x. MEM x l2 ==> (P x = P' x)) ==>
     (pEXISTS P l1 = pEXISTS P' l2)`,
 Induct THENL [ALL_TAC, GEN_TAC] THEN Induct
   THEN RW_TAC list_ss [pEXISTS_def]
   THEN FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss [] THEN
   REPEAT CASE_TAC THEN METIS_TAC [NOT_SOME_NONE,SOME_11]);

val pEXISTS_DEFINED_LIST = Q.prove
(`!l t. MEM t l /\ IS_SOME (pEXISTS P l) ==> IS_SOME (P t)`,
 Induct THEN SIMP_TAC list_ss [pEXISTS_def] THEN
   REPEAT (GEN_TAC ORELSE CASE_TAC) THEN RW_TAC list_ss [] THEN
   METIS_TAC [IS_SOME_EXISTS, IS_SOME_DEF]);

val IS_SOME_PEXISTS_DISTRIB = Q.prove
(`!l. IS_SOME (pEXISTS P l) <=> !t. MEM t l ==> IS_SOME(P t)`,
Induct THEN SIMP_TAC list_ss [pEXISTS_def,EQ_IMP_THM] THEN
  REPEAT (GEN_TAC ORELSE CASE_TAC) THEN RW_TAC list_ss [] THEN
   METIS_TAC [IS_SOME_EXISTS, IS_SOME_DEF]);


(*---------------------------------------------------------------------------*)
(* Indexed function definition                                               *)
(*---------------------------------------------------------------------------*)

val iintree_def =
 Define
  `iintree d x tree =
     if d=0 then NONE else
     case tree
      of Node y tlist -> if x=y then SOME T
                         else pEXISTS (iintree (d-1) x) tlist`;

(*---------------------------------------------------------------------------*)
(* Domain of the function.                                                   *)
(*---------------------------------------------------------------------------*)

val dom_def = Define `dom x tree = ?d. IS_SOME(iintree d x tree)`;

(*---------------------------------------------------------------------------*)
(* Measure on recursion depth.                                               *)
(*---------------------------------------------------------------------------*)

val rdepth_thm =
 MINCHOOSE ("rdepth_thm", "rdepth",
            ``!x tree. ?d. IS_SOME (iintree d x tree)``);

(*---------------------------------------------------------------------------*)
(* Define intree                                                             *)
(*---------------------------------------------------------------------------*)

val intree_def =
 Define
   `intree x tree = THE (iintree (rdepth x tree) x tree)`;

(*---------------------------------------------------------------------------*)
(* Lemmas about izero and definedness                                        *)
(*---------------------------------------------------------------------------*)

val IS_SOME_IINTREE = Q.prove
(`!d x tree. IS_SOME (iintree d x tree) ==> d <> 0`,
 Cases THEN RW_TAC std_ss [Once iintree_def]);

val IS_SOME_PEXISTS = Q.prove
(`!l d x. IS_SOME (pEXISTS (iintree d x) l) ==> (l=[]) \/ d <> 0`,
 Cases THEN RW_TAC list_ss [Once iintree_def,pEXISTS_def] THEN CASE_TAC);

val iintree_dlem = Q.prove
(`!d x tree. IS_SOME (iintree d x tree) ==> (iintree d x tree = iintree (SUC d) x tree)`,
Induct THENL [METIS_TAC [IS_SOME_IINTREE], ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [iintree_def] THEN
  REPEAT CASE_TAC THEN FULL_SIMP_TAC arith_ss [] THEN
  METIS_TAC[IS_SOME_EXISTS,SOME_11,IS_SOME_DEF,NOT_SOME_NONE]);

val iintree_determ = Q.prove
(`!d1 d2 x tree.
    IS_SOME(iintree d1 x tree) /\
    IS_SOME(iintree d2 x tree) ==> (iintree d1 x tree = iintree d2 x tree)`,
 Induct THENL [METIS_TAC [IS_SOME_IINTREE,numTheory.NOT_SUC],
 Induct THENL [METIS_TAC [IS_SOME_IINTREE,numTheory.NOT_SUC],
   POP_ASSUM (K ALL_TAC) THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [iintree_def] THEN SIMP_TAC arith_ss [] THEN
   REPEAT CASE_TAC THEN RW_TAC std_ss [] THEN
   MATCH_MP_TAC pEXISTS_CONG THEN RW_TAC list_ss [] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN METIS_TAC [IS_SOME_PEXISTS_DISTRIB]]]);

val iintree_monotone_step = Q.prove
(`!d x tree. IS_SOME(iintree d x tree) ==> IS_SOME(iintree (SUC d) x tree)`,
e (Induct THENL [RW_TAC arith_ss [Once iintree_def], ONCE_REWRITE_TAC [iintree_def]]);
e (SIMP_TAC arith_ss [] THEN REPEAT GEN_TAC THEN REPEAT CASE_TAC THEN STRIP_TAC);
e (`(l=[]) \/ d<>0` by METIS_TAC [IS_SOME_PEXISTS]);
(*1*)
e (RW_TAC list_ss [pEXISTS_def]);
(*2*)
e (`iintree (SUC d) x (Node a l) = pEXISTS (iintree d x) l`
   by (RW_TAC list_ss [Once iintree_def] THEN METIS_TAC[]));
e (RW_TAC list_ss [Once iintree_def]);
e (`IS_SOME (iintree (SUC d) x (Node a l))` by METIS_TAC []);

REPEAT STRIP_TAC THEN RW_TAC list_ss [Once iintree_def] THEN
 CASE_TAC THEN RW_TAC list_ss [] THEN
 `d<>0` by METIS_TAC [IS_SOME_IINTREE] THEN
 Q.PAT_ASSUM `IS_SOME thing` MP_TAC THEN
 ASM_SIMP_TAC list_ss [Once iintree_def] THEN CASE_TAC THEN RW_TAC list_ss []

 METIS_TAC [IS_SOME_EXISTS,NOT_SOME_NONE,SOME_11,iintree_determ]);

val iintree_monotone = Q.prove
(`!d1 d2 x list. IS_SOME(iintree d1 x list) /\ d1 <= d2 ==> IS_SOME(iintree d2 x list)`,
 RW_TAC arith_ss [LESS_EQ_EXISTS] THEN
 Induct_on `p` THEN METIS_TAC [ADD_CLAUSES,iintree_monotone_step]);

val iintree_norm = Q.prove
(`!d x list. IS_SOME(iintree d x list) ==> (iintree d n = iintree (rdepth x list) x list)`,
  METIS_TAC [iintree_determ,rdepth_thm]);
