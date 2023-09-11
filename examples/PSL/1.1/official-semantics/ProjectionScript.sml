

(*****************************************************************************)
(* Definition and validation of the "projection view" of clocked semantics   *)
(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Started:   Tue Mar 9, 2004                                                *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
loadPath
 :=
 "../official-semantics" :: "../../regexp" :: "../../path" :: !loadPath;
map load
 ["UnclockedSemanticsTheory",
  "SyntacticSugarTheory", "ClockedSemanticsTheory", "RewritesTheory", "whileTheory",
  "rich_listTheory", "intLib", "res_quanLib", "res_quanTheory",
  "LemmasTheory","RewritesPropertiesTheory"];
open FinitePSLPathTheory PSLPathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory whileTheory listTheory rich_listTheory
     res_quanLib res_quanTheory
     arithmeticTheory listTheory whileTheory rich_listTheory res_quanLib res_quanTheory
     ClockedSemanticsTheory LemmasTheory RewritesPropertiesTheory;
val _ = intLib.deprecate_int();
quietdec := false;
*)


(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open FinitePSLPathTheory PSLPathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
     whileTheory ClockedSemanticsTheory LemmasTheory RewritesPropertiesTheory
     arithmeticTheory listTheory whileTheory rich_listTheory res_quanLib
     res_quanTheory ClockedSemanticsTheory LemmasTheory
     RewritesPropertiesTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called Project
******************************************************************************)
val _ = new_theory "Projection";
val _ = ParseExtras.temp_loose_equality()

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS =
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [IN_DEF,LESS_def,LESSX_def,LENGTH_def]];

(******************************************************************************
* CLOCK c s is true is clock c is true in state s
******************************************************************************)

val CLOCK_def = Define `CLOCK c s = B_SEM s c`;

open FinitePSLPathTheory;

val LIST_PROJ_def =
 Define `LIST_PROJ l c = FILTER (CLOCK c) l`;

val LENGTH_FILTER_NON_EMPTY =
 store_thm
  ("LENGTH_FILTER_NON_EMPTY",
   ``!l P. (LENGTH(FILTER P l) > 0) ==> LENGTH l > 0``,
   Induct
    THEN RW_TAC list_ss []);

val LENGTH_FILTER_1_NON_EMPTY =
 store_thm
  ("LENGTH_FILTER_1_NON_EMPTY",
   ``!l P. (LENGTH(FILTER P l) = 1) ==> LENGTH l > 0``,
   Induct
    THEN RW_TAC list_ss []);

val FILTER_NON_EMPTY =
 store_thm
  ("FILTER_NON_EMPTY",
   ``!l P. LENGTH l > 0 /\ (?n. n < LENGTH l /\ P(EL n l)) ==> ~(FILTER P l = [])``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `n`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN PROVE_TAC[]);

val LAST_FILTER_NON_EMPTY =
 store_thm
  ("LAST_FILTER_NON_EMPTY",
   ``!l P. LENGTH l > 0 /\ P(LAST l) ==> ~(FILTER P l = [])``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `l`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss [LAST_CONS]
    THEN PROVE_TAC[]);

val LENGTH_APPEND_GREATER_1 =
 store_thm
  ("LENGTH_APPEND_GREATER_1",
   ``LENGTH(l1 <> [x] <> l2 <> [y]) > 1``,
   RW_TAC list_ss []);

val FIRSTN_SUC_EL =
 store_thm
  ("FIRSTN_SUC_EL",
   ``!l n. n < LENGTH l ==> (FIRSTN (SUC n) l = FIRSTN n l <> [EL n l])``,
   Induct
    THEN Cases_on `n`
    THEN RW_TAC list_ss  [FIRSTN]);

val FIRSTN_LASTN_SPLIT =
 store_thm
  ("FIRSTN_LASTN_SPLIT",
   ``!n l. n < LENGTH l
           ==>
           (l = FIRSTN n l <> [EL n l] <> BUTFIRSTN (SUC n) l)``,
   RW_TAC list_ss [GSYM FIRSTN_SUC_EL,APPEND_FIRSTN_BUTFIRSTN]);

val LENGTH_FILTER_1_NOT =
 store_thm
  ("LENGTH_FILTER_1_NOT",
   ``!l P. P(LAST l) /\ (LENGTH(FILTER P l) = 1)
           ==> !i. i < LENGTH l - 1 ==> ~P(EL i l)``,
   RW_TAC list_ss []
    THEN Cases_on `P (EL i l)`
    THEN RW_TAC list_ss []
    THEN IMP_RES_TAC LENGTH_FILTER_1_NON_EMPTY
    THEN `~(l=[])` by PROVE_TAC[LENGTH_NIL,DECIDE``n>0 ==> ~(n=0)``]
    THEN `i <= LENGTH l` by DECIDE_TAC
    THEN IMP_RES_TAC APPEND_FRONT_LAST
    THEN IMP_RES_TAC LENGTH_BUTLAST
    THEN `i < LENGTH(BUTLAST l)` by DECIDE_TAC
    THEN IMP_RES_TAC FIRSTN_LASTN_SPLIT
    THEN `i < PRE(LENGTH l)` by DECIDE_TAC
    THEN IMP_RES_TAC EL_BUTLAST
    THEN `l = (FIRSTN i (BUTLAST l) <> [EL i l] <>
               BUTFIRSTN (SUC i) (BUTLAST l)) <> [LAST l]`
          by PROVE_TAC[]
    THEN ASSUM_LIST
          (fn thl =>
           ASSUME_TAC
            (SIMP_RULE list_ss [el 11 thl,el 14 thl,FILTER_APPEND]
              (Q.AP_TERM `FILTER P` (el 1 thl))))
    THEN `LENGTH(FILTER P l) > 1` by PROVE_TAC[LENGTH_APPEND_GREATER_1]
    THEN DECIDE_TAC);

val TOP_FREE_def =
 Define
  `(TOP_FREE[]             = T) /\
   (TOP_FREE(TOP::v)       = F) /\
   (TOP_FREE(BOTTOM::v)    = TOP_FREE v) /\
   (TOP_FREE((STATE s)::v) = TOP_FREE v)`;

val TOP_FREE_APPEND =
 store_thm
  ("TOP_FREE_APPEND",
   ``!v1 v2. TOP_FREE (v1 <> v2) = TOP_FREE v1 /\ TOP_FREE v2``,
   Induct
    THEN RW_TAC list_ss [TOP_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]);

val TOP_FREE_EL =
 store_thm
  ("TOP_FREE_EL",
   ``!l. TOP_FREE l = !i. i < LENGTH l ==> ~(EL i l = TOP)``,
   Induct
    THEN RW_TAC list_ss [TOP_FREE_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss [TOP_FREE_def]
    THENL
     [Cases_on `i`
       THEN Cases_on `h`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_def],
      Cases_on `h`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]
       THENL
        [POP_ASSUM
          (fn th =>
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [] (SPEC ``0`` th))),
         POP_ASSUM
          (fn th =>
            STRIP_ASSUME_TAC(GEN_ALL(SIMP_RULE list_ss [] (SPEC ``SUC i`` th)))),
         POP_ASSUM
          (fn th =>
            STRIP_ASSUME_TAC(GEN_ALL(SIMP_RULE list_ss [] (SPEC ``SUC i`` th))))]]);


val BOTTOM_FREE_EL =
 store_thm
  ("BOTTOM_FREE_EL",
   ``!l. BOTTOM_FREE l = !i. i < LENGTH l ==> ~(EL i l = BOTTOM)``,
   Induct
    THEN RW_TAC list_ss [BOTTOM_FREE_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss [BOTTOM_FREE_def]
    THENL
     [Cases_on `i`
       THEN Cases_on `h`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def],
      Cases_on `h`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]
       THENL
        [POP_ASSUM
          (fn th =>
            STRIP_ASSUME_TAC(GEN_ALL(SIMP_RULE list_ss [] (SPEC ``SUC i`` th)))),
         POP_ASSUM
          (fn th =>
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [] (SPEC ``0`` th))),
         POP_ASSUM
          (fn th =>
            STRIP_ASSUME_TAC(GEN_ALL(SIMP_RULE list_ss [] (SPEC ``SUC i`` th))))]]);

val CLOCK_TICK_LENGTH_1 =
 store_thm
  ("CLOCK_TICK_LENGTH_1",
   ``!l c. TOP_FREE l /\ CLOCK_TICK l c
           ==>
           (LENGTH (FILTER (CLOCK c) l) = 1)``,
   RW_TAC (list_ss++resq_SS) [CLOCK_TICK_def,CLOCK_def,ELEM_EL]
    THEN `~(LENGTH l = 0)` by DECIDE_TAC
    THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
    THEN IMP_RES_TAC APPEND_FRONT_LAST
    THEN POP_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM th])
    THEN `LENGTH l >= 1` by DECIDE_TAC
    THEN RW_TAC list_ss [GSYM EL_PRE_LENGTH,FILTER_APPEND,LENGTH_APPEND,CLOCK_def]
    THEN Induct_on `l`
    THEN RW_TAC list_ss []
    THEN Cases_on `l = []`
    THEN RW_TAC list_ss []
    THEN ASM_REWRITE_TAC [FRONT_DEF]
    THEN `~(LENGTH l = 0)` by PROVE_TAC[LENGTH_NIL]
    THEN `0 < LENGTH l` by DECIDE_TAC
    THEN RES_TAC
    THEN FULL_SIMP_TAC list_ss [CLOCK_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss [B_SEM_def,TOP_FREE_def,EL_CONS,DECIDE``PRE n = n-1``]
    THEN ASSUM_LIST
          (fn thl =>
            ASSUME_TAC
             (Q.GEN `i`
               (SIMP_RULE list_ss
                 [DECIDE ``SUC n < m:num = n < m-1``] (Q.SPEC `SUC i` (el 5 thl)))))
    THEN PROVE_TAC[]);

val S_CLOCK_LAST =
 store_thm
  ("S_CLOCK_LAST",
   ``!r. S_CLOCK_FREE r
         ==>
         !v c. S_SEM v c r /\ LENGTH v > 0 ==> CLOCK c (LAST v)``,
   RW_TAC std_ss [CLOCK_def]
    THEN `LENGTH v >= 1` by DECIDE_TAC
    THEN PROVE_TAC[Lemma2,ELEM_EL,EL_PRE_LENGTH]);

val LENGTH_FILTER_1_LAST =
 store_thm
  ("LENGTH_FILTER_1_LAST",
   ``!l P. P(LAST l) /\ (LENGTH(FILTER P l) = 1)
           ==> (HD(FILTER P l) = LAST l)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC LENGTH_FILTER_1_NOT
    THEN Induct_on `l`
    THEN RW_TAC list_ss [FILTER]
    THENL
     [Cases_on `l`
       THEN FULL_SIMP_TAC list_ss []
       THEN `0 < SUC (LENGTH t)` by DECIDE_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [],
      IMP_RES_TAC LENGTH_FILTER_1_NON_EMPTY
       THEN `~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN FULL_SIMP_TAC list_ss [LAST_DEF]
       THEN ASSUM_LIST
             (fn thl =>
               ASSUME_TAC
                (GEN_ALL
                 (SIMP_RULE list_ss
                   [EL,DECIDE ``(SUC i < n:num ) = (i < n - 1)``]
                   (Q.SPEC `SUC i` (el 4 thl)))))
       THEN RES_TAC]);

val CONCAT_NIL =
 store_thm
  ("CONCAT_NIL",
   ``!l. (CONCAT l = []) = ALL_EL (\x. x=[]) l``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def]);

val S_PROJ_EMPTY =
 store_thm
  ("S_PROJ_EMPTY",
   ``!r c. S_CLOCK_FREE r ==> (US_SEM [] r = S_SEM [] c r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def]
       THEN RW_TAC list_ss [CLOCK_TICK_def,ELEM_EL],
      (* S_CAT(r,r') *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_FUSION (r,r') *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_OR (r,r') *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_AND (r,r') *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_EMPTY *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_REPEAT r *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def,CONCAT_NIL]
       THEN EQ_TAC
       THEN RW_TAC list_ss []
       THEN Q.EXISTS_TAC `[]`
       THEN RW_TAC list_ss [],
      (* S_CLOCK (r,p_2) *)
       RW_TAC list_ss [S_CLOCK_FREE_def]]);


(******************************************************************************
* Make FIRSTN executable (for testing)
******************************************************************************)

val FIRSTN_AUX =
 store_thm
  ("FIRSTN_AUX",
   ``FIRSTN n l =
      if n=0 then []
             else (if NULL l then FIRSTN n []
                             else HD l :: FIRSTN (n-1) (TL l))``,
   Cases_on `n` THEN Cases_on `l`
    THEN RW_TAC list_ss [FIRSTN]);

val _ = computeLib.add_funs[FIRSTN_AUX]

val TAKE_FIRST_def =
 Define
  `(TAKE_FIRST P [] = [])
   /\
   (TAKE_FIRST P (x::l) =
     if P x then [x] else x :: TAKE_FIRST P l)`;

val TAKE_FIRSTN_def =
 Define
  `(TAKE_FIRSTN P 0 l = [])
   /\
   (TAKE_FIRSTN P (SUC n) l =
     TAKE_FIRST P l <> TAKE_FIRSTN P n (BUTFIRSTN (LENGTH(TAKE_FIRST P l)) l))`;

(******************************************************************************
* Make BUTFIRSTN executable for testing (not sure is this is needed)
******************************************************************************)

val BUTFIRSTN_AUX =
 store_thm
  ("BUTFIRSTN_AUX",
   ``BUTFIRSTN n l =
      if n=0 then l
             else (if NULL l then BUTFIRSTN n []
                             else BUTFIRSTN (n-1) (TL l))``,
   Cases_on `n` THEN Cases_on `l`
    THEN RW_TAC list_ss [BUTFIRSTN]);

val _ = computeLib.add_funs[BUTFIRSTN_AUX];

val TAKE_FIRST_NIL =
 store_thm
  ("TAKE_FIRST_NIL",
   ``!l. (TAKE_FIRST P l = []) ==> (l = [])``,
   Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,FILTER_APPEND]);

Theorem TAKE_FIRSTN_EQ_NIL_E:
  !P n l. 0 < n ==> (TAKE_FIRSTN P n l = []) ==> (l = [])
Proof
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss [TAKE_FIRSTN_def]
    THEN PROVE_TAC[TAKE_FIRST_NIL]
QED

val HD_TAKE_FIRST =
 store_thm
  ("HD_TAKE_FIRST",
   ``!l. (?n. n < LENGTH l /\ P(EL n l))
         ==>
         (HD(FILTER P l) = LAST(TAKE_FIRST P l))``,
   Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,FILTER_APPEND]
    THEN Cases_on `n`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN RES_TAC
    THEN RW_TAC list_ss []
    THEN `LENGTH l > 0` by DECIDE_TAC
    THEN IMP_RES_TAC FILTER_NON_EMPTY
    THEN `~(LENGTH l = 0)` by DECIDE_TAC
    THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
    THEN `~(TAKE_FIRST P l = [])` by PROVE_TAC[TAKE_FIRST_NIL]
    THEN RW_TAC list_ss [LAST_DEF]);

val BUTFIRSTN_ONE =
 store_thm
  ("BUTFIRSTN_ONE",
   ``BUTFIRSTN 1 (h::l) = l``,
   PROVE_TAC[ONE,BUTFIRSTN]);

val FIRSTN_TAKE_FIRSTN =
 store_thm
  ("FIRSTN_TAKE_FIRSTN",
   ``!P n l. FIRSTN (LENGTH(TAKE_FIRSTN P n l)) l = TAKE_FIRSTN P n l``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN]
    THEN Induct_on `l`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN,GSYM COND_RAND]
    THEN FULL_SIMP_TAC list_ss [BUTFIRSTN_ONE,BUTFIRSTN]
    THENL
     [FIRST_ASSUM (fn th => ONCE_REWRITE_TAC[GSYM th])
       THEN SIMP_TAC list_ss [],
      RW_TAC list_ss [FIRSTN,DECIDE``m + SUC n = SUC(m + n)``]]);

val FIRSTN_FILTER_TAKE_FIRSTN =
 store_thm
  ("FIRSTN_FILTER_TAKE_FIRSTN",
   ``!P n l. n <= LENGTH(FILTER P l)
             ==>
             (FIRSTN n (FILTER P l) = FILTER P (TAKE_FIRSTN P n l))``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN]
    THEN Induct_on `l`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN]
    THEN FULL_SIMP_TAC list_ss []);

val REVERSE_REVERSE_EQ =
 store_thm
  ("REVERSE_REVERSE_EQ",
   ``!l1 l2. (l1 = l2) = (REVERSE l1 = REVERSE l2)``,
   PROVE_TAC[REVERSE_REVERSE]);

val EQ_APPEND_IMP =
 store_thm
  ("EQ_APPEND_IMP",
   ``(l = v1 <> v2) ==> (l = FIRSTN (LENGTH v1) l <> LASTN (LENGTH v2) l)``,
   RW_TAC std_ss []
    THEN PROVE_TAC
          [LENGTH_APPEND,
           APPEND_FIRSTN_LASTN,FIRSTN_LENGTH_APPEND,LASTN_LENGTH_APPEND]);

val APPEND_NIL_NIL =
 store_thm
  ("APPEND_NIL_NIL",
   ``!l1 l2. (l1 <> l2 = []) = (l1 = []) /\ (l2 = [])``,
   Induct
    THEN RW_TAC list_ss []);

val HOLDS_LAST_def =
 Define
  `HOLDS_LAST P l = (?n. n < LENGTH l /\ P(EL n l)) /\ P(LAST l)`;

val LENGTH_TAKE_FIRST =
 store_thm
  ("LENGTH_TAKE_FIRST",
   ``!P l. LENGTH (TAKE_FIRST P l) <= LENGTH l``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def]);

val HOLDS_LAST_BUTFIRSTN =
 store_thm
  ("HOLDS_LAST_BUTFIRSTN",
   ``!P l. LENGTH(FILTER P l) > 1 /\ HOLDS_LAST P l
           ==>
           HOLDS_LAST P (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [HOLDS_LAST_def,TAKE_FIRST_def,BUTFIRSTN_ONE]
    THENL
     [Cases_on `0 < LENGTH l`
       THEN RW_TAC list_ss []
       THENL
        [`LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
          THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
          THEN `P(LAST l)` by PROVE_TAC[LAST_DEF]
          THEN PROVE_TAC[EL_PRE_LENGTH],
         `LENGTH l = 0` by DECIDE_TAC
          THEN `n = 0` by DECIDE_TAC
          THEN RW_TAC list_ss []
          THEN `LENGTH (FILTER P l) > 0` by DECIDE_TAC
          THEN IMP_RES_TAC LENGTH_FILTER_NON_EMPTY
          THEN DECIDE_TAC],
      Cases_on `0 < LENGTH l`
       THEN RW_TAC list_ss []
       THENL
        [`LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
          THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
          THEN `P(LAST l)` by PROVE_TAC[LAST_DEF],
         `LENGTH l = 0` by DECIDE_TAC
          THEN `n = 0` by DECIDE_TAC
          THEN `l = []` by PROVE_TAC[LENGTH_NIL]
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss []],
      RES_TAC
       THEN `n <= LENGTH l` by DECIDE_TAC
       THEN RW_TAC list_ss [BUTFIRSTN,LENGTH_BUTFIRSTN,LENGTH_TAKE_FIRST]
       THEN Cases_on `n = 0`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `n-1 < LENGTH l` by DECIDE_TAC
       THEN `LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN `P(LAST l)` by PROVE_TAC[LAST_DEF]
       THEN `n = SUC(n-1)` by DECIDE_TAC
       THEN `P(EL (n-1) l)` by PROVE_TAC[TL,EL]
       THEN `HOLDS_LAST P l` by PROVE_TAC[HOLDS_LAST_def]
       THEN RES_TAC
       THEN POP_ASSUM(STRIP_ASSUME_TAC o SIMP_RULE list_ss [HOLDS_LAST_def])
       THEN PROVE_TAC[BUTFIRSTN,LENGTH_BUTFIRSTN,LENGTH_TAKE_FIRST],
      RES_TAC
       THEN `n <= LENGTH l` by DECIDE_TAC
       THEN RW_TAC list_ss [BUTFIRSTN,LENGTH_BUTFIRSTN,LENGTH_TAKE_FIRST]
       THEN Cases_on `n = 0`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `n-1 < LENGTH l` by DECIDE_TAC
       THEN `LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN `P(LAST l)` by PROVE_TAC[LAST_DEF]
       THEN `n = SUC(n-1)` by DECIDE_TAC
       THEN `P(EL (n-1) l)` by PROVE_TAC[TL,EL]
       THEN `HOLDS_LAST P l` by PROVE_TAC[HOLDS_LAST_def]
       THEN RES_TAC
       THEN POP_ASSUM(STRIP_ASSUME_TAC o SIMP_RULE list_ss [HOLDS_LAST_def])]);

val LENGTH_FILTER_BUTFIRSTN =
 store_thm
  ("LENGTH_FILTER_BUTFIRSTN",
   ``!P l. LENGTH(FILTER P (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)) =
           LENGTH(FILTER P l) - 1``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,BUTFIRSTN,BUTFIRSTN_ONE,GSYM COND_RAND]);

val LENGTH_1_BUTFIRSTN =
 store_thm
  ("LENGTH_1_BUTFIRSTN",
   ``!P l. HOLDS_LAST P l /\ (LENGTH (FILTER P l) = 1)
           ==>
           (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l = [])``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,BUTFIRSTN,BUTFIRSTN_ONE,HOLDS_LAST_def,GSYM COND_RAND]
    THENL
     [Cases_on `l = []`
       THEN RW_TAC list_ss []
       THEN `~(LENGTH l = 0)` by PROVE_TAC[LENGTH_NIL]
       THEN `LENGTH l > 0` by DECIDE_TAC
       THEN PROVE_TAC[LAST_FILTER_NON_EMPTY,LENGTH_NIL,LAST_DEF],
      Cases_on `n = 0`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `n-1 < LENGTH l` by DECIDE_TAC
       THEN `LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN `P(LAST l)` by PROVE_TAC[LAST_DEF]
       THEN `n = SUC(n-1)` by DECIDE_TAC
       THEN `P(EL (n-1) l)` by PROVE_TAC[TL,EL]
       THEN `HOLDS_LAST P l` by PROVE_TAC[HOLDS_LAST_def]
       THEN RES_TAC]);

val HOLDS_LAST_1_TAKE_FIRST =
 store_thm
  ("HOLDS_LAST_1_TAKE_FIRST",
   ``!P l. HOLDS_LAST P l /\ (LENGTH(FILTER P l) = 1) ==> (TAKE_FIRST P l = l)``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [HOLDS_LAST_def,TAKE_FIRST_def]
    THENL
     [Cases_on `l = []`
       THEN RW_TAC list_ss []
       THEN `~(LENGTH l = 0)` by PROVE_TAC[LENGTH_NIL]
       THEN `LENGTH l > 0` by DECIDE_TAC
       THEN PROVE_TAC[LAST_FILTER_NON_EMPTY,LENGTH_NIL,LAST_DEF],
      Cases_on `n = 0`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `n-1 < LENGTH l` by DECIDE_TAC
       THEN `LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN `P(LAST l)` by PROVE_TAC[LAST_DEF]
       THEN `n = SUC(n-1)` by DECIDE_TAC
       THEN `P(EL (n-1) l)` by PROVE_TAC[TL,EL]
       THEN `HOLDS_LAST P l` by PROVE_TAC[HOLDS_LAST_def]
       THEN RES_TAC]);

val TAKE_FIRST_APPEND =
 store_thm
  ("TAKE_FIRST_APPEND",
   ``!P l. TAKE_FIRST P l <> BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l = l``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [HOLDS_LAST_def,TAKE_FIRST_def,BUTFIRSTN_ONE,BUTFIRSTN]
    THEN Cases_on `n = 0`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN `n-1 < LENGTH l` by DECIDE_TAC
    THEN `LENGTH l >= 1 /\ LENGTH l - 1 < LENGTH l /\ ~(LENGTH l = 0)` by DECIDE_TAC
    THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
    THEN `P(LAST l)` by PROVE_TAC[LAST_DEF]
    THEN `n = SUC(n-1)` by DECIDE_TAC
    THEN `P(EL (n-1) l)` by PROVE_TAC[TL,EL]
    THEN `HOLDS_LAST P l` by PROVE_TAC[HOLDS_LAST_def]
    THEN RES_TAC);

val HOLDS_LAST_TAKE_FIRSTN =
 store_thm
  ("HOLDS_LAST_TAKE_FIRSTN",
   ``!P l. HOLDS_LAST P l ==> (TAKE_FIRSTN P (LENGTH(FILTER P l)) l = l)``,
   Induct_on `LENGTH(FILTER P l)`
    THEN RW_TAC list_ss []
    THENL
     [FULL_SIMP_TAC list_ss [HOLDS_LAST_def]
       THEN `LENGTH l > 0` by DECIDE_TAC
       THEN IMP_RES_TAC FILTER_NON_EMPTY
       THEN PROVE_TAC[LENGTH_NIL],
      `v = LENGTH (FILTER P l) - 1` by DECIDE_TAC
       THEN RW_TAC list_ss []
       THEN ASSUM_LIST(fn thl => ONCE_REWRITE_TAC[GSYM(el 2 thl)])
       THEN REWRITE_TAC[TAKE_FIRSTN_def]
       THEN ASSUM_LIST
             (fn thl =>
               ASSUME_TAC(Q.SPECL[`P`,`BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l`](el 3 thl)))
       THEN `LENGTH(FILTER P l) > 0` by DECIDE_TAC
       THEN Cases_on `LENGTH (FILTER P l) = 1`
       THEN RW_TAC list_ss [LENGTH_1_BUTFIRSTN,TAKE_FIRSTN_def,HOLDS_LAST_1_TAKE_FIRST]
       THEN `LENGTH(FILTER P l) > 1` by DECIDE_TAC
       THEN IMP_RES_TAC HOLDS_LAST_BUTFIRSTN
       THEN `TAKE_FIRSTN P
              (LENGTH (FILTER P l) - 1)
              (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l) =
             BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l` by PROVE_TAC[LENGTH_FILTER_BUTFIRSTN]
       THEN RW_TAC list_ss [TAKE_FIRST_APPEND]]);

val LENGTH_TAKE_FIRSTN =
 store_thm
  ("LENGTH_TAKE_FIRSTN",
   ``!P n l. LENGTH(TAKE_FIRSTN P n l) <= LENGTH l``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def]
    THEN Induct_on `l`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN,BUTFIRSTN,BUTFIRSTN_ONE]
    THEN FULL_SIMP_TAC list_ss []
    THENL
     [POP_ASSUM
       (ACCEPT_TAC o SIMP_RULE list_ss [TAKE_FIRSTN_def] o Q.SPEC `[]`),
      RW_TAC list_ss [DECIDE ``m+1 <= SUC n = m <= n``],
      RW_TAC list_ss [DECIDE ``m + SUC n <= SUC p = m + n <= p``]
       THEN RW_TAC std_ss [GSYM LENGTH_APPEND,GSYM TAKE_FIRSTN_def]]);

val LENGTH_LESS_TAKE_FIRSTN =
 store_thm
  ("LENGTH_LESS_TAKE_FIRSTN",
   ``!P n l. 0 < n /\ n < LENGTH(FILTER P l) ==> LENGTH(TAKE_FIRSTN P n l) < LENGTH l``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def]
    THEN Induct_on `l`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN,BUTFIRSTN,BUTFIRSTN_ONE]
    THEN FULL_SIMP_TAC list_ss []
    THENL
     [Cases_on `n=0`
       THEN RW_TAC list_ss [TAKE_FIRSTN_def]
       THENL
        [`LENGTH (FILTER P l) > 0` by DECIDE_TAC
          THEN IMP_RES_TAC LENGTH_FILTER_NON_EMPTY
          THEN DECIDE_TAC,
         `0 < n` by DECIDE_TAC
           THEN RES_TAC
           THEN DECIDE_TAC],
      RW_TAC list_ss [DECIDE ``m + SUC n < SUC p = m + n < p``]
       THEN RW_TAC std_ss (map GSYM [LENGTH_APPEND,TAKE_FIRSTN_def])]);


val TOP_FREE_FIRSTN =
 store_thm
  ("TOP_FREE_FIRSTN",
   ``!l n. n <= LENGTH l /\ TOP_FREE l ==> TOP_FREE(FIRSTN n l)``,
   Induct
    THEN RW_TAC list_ss [TOP_FREE_def,FIRSTN]
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [FIRSTN,BUTFIRSTN,BUTFIRSTN_ONE]
    THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss
          [B_SEM_def,TOP_FREE_def,EL_CONS,DECIDE``PRE n = n-1``]);

val BOTTOM_FREE_FIRSTN =
 store_thm
  ("BOTTOM_FREE_FIRSTN",
   ``!l n. n <= LENGTH l /\ BOTTOM_FREE l ==> BOTTOM_FREE(FIRSTN n l)``,
   Induct
    THEN RW_TAC list_ss [BOTTOM_FREE_def,FIRSTN]
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [FIRSTN,BUTFIRSTN,BUTFIRSTN_ONE]
    THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss
          [B_SEM_def,BOTTOM_FREE_def,EL_CONS,DECIDE``PRE n = n-1``]);

val TOP_FREE_TAKE_FIRSTN =
 store_thm
  ("TOP_FREE_TAKE_FIRSTN",
   ``!l P n. TOP_FREE l ==> TOP_FREE(TAKE_FIRSTN P n l)``,
   Induct
    THEN RW_TAC list_ss [TOP_FREE_def,TAKE_FIRST_def]
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN,BUTFIRSTN,BUTFIRSTN_ONE]
    THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss
          [B_SEM_def,TOP_FREE_def,EL_CONS,DECIDE``PRE n = n-1``]
    THEN RW_TAC list_ss [GSYM TAKE_FIRSTN_def]);

val BOTTOM_FREE_TAKE_FIRSTN =
 store_thm
  ("BOTTOM_FREE_TAKE_FIRSTN",
   ``!l P n. BOTTOM_FREE l ==> BOTTOM_FREE(TAKE_FIRSTN P n l)``,
   Induct
    THEN RW_TAC list_ss [BOTTOM_FREE_def,TAKE_FIRST_def]
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN,BUTFIRSTN,BUTFIRSTN_ONE]
    THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss
          [B_SEM_def,BOTTOM_FREE_def,EL_CONS,DECIDE``PRE n = n-1``]
    THEN RW_TAC list_ss [GSYM TAKE_FIRSTN_def]);

val TOP_FREE_REVERSE =
 store_thm
  ("TOP_FREE_REVERSE",
   ``!l. TOP_FREE(REVERSE l) = TOP_FREE l``,
   Induct
    THEN RW_TAC list_ss [TOP_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss
          [B_SEM_def,TOP_FREE_def,EL_CONS,
           DECIDE``PRE n = n-1``,TOP_FREE_APPEND]);

val BOTTOM_FREE_REVERSE =
 store_thm
  ("BOTTOM_FREE_REVERSE",
   ``!l. BOTTOM_FREE(REVERSE l) = BOTTOM_FREE l``,
   Induct
    THEN RW_TAC list_ss [BOTTOM_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss
          [B_SEM_def,BOTTOM_FREE_def,EL_CONS,
           DECIDE``PRE n = n-1``,BOTTOM_FREE_APPEND]);

val LASTN_REVERSE_FIRSTN =
 store_thm
  ("LASTN_REVERSE_FIRSTN",
   ``!n l. n <= LENGTH l ==> (LASTN n l = REVERSE(FIRSTN n (REVERSE l)))``,
   PROVE_TAC[REVERSE_REVERSE,FIRSTN_REVERSE]);

val TOP_FREE_LAST =
 store_thm
  ("TOP_FREE_LAST",
   ``!l. 0 < LENGTH l /\ TOP_FREE l ==> TOP_FREE[LAST l]``,
   Induct
    THEN RW_TAC list_ss [TOP_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss [B_SEM_def,TOP_FREE_def]
    THEN Cases_on `l`
    THEN RW_TAC list_ss [TOP_FREE_def]);

Theorem TOP_FREE_LASTN:
  !l n. n <= LENGTH l /\ TOP_FREE l ==> TOP_FREE(LASTN n l)
Proof
  Induct_on ‘l’  using SNOC_INDUCT >> simp[LASTN] >>
  Cases_on ‘n’ >> simp[LASTN, TOP_FREE_def] >>
  simp[SNOC_APPEND, TOP_FREE_APPEND]
QED

val BOTTOM_FREE_LAST =
 store_thm
  ("BOTTOM_FREE_LAST",
   ``!l. 0 < LENGTH l /\ BOTTOM_FREE l ==> BOTTOM_FREE[LAST l]``,
   Induct
    THEN RW_TAC list_ss [BOTTOM_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss [B_SEM_def,BOTTOM_FREE_def]
    THEN Cases_on `l`
    THEN RW_TAC list_ss [BOTTOM_FREE_def]);

Theorem BOTTOM_FREE_LASTN:
  !l n. n <= LENGTH l /\ BOTTOM_FREE l ==> BOTTOM_FREE(LASTN n l)
Proof
  Induct_on ‘l’ using SNOC_INDUCT >> simp[LASTN] >>
  Cases_on ‘n’ >> simp[LASTN, BOTTOM_FREE_def] >>
  simp[SNOC_APPEND, BOTTOM_FREE_APPEND]
QED

val LAST_TAKE_FIRST =
 store_thm
  ("LAST_TAKE_FIRST",
   ``!P l. 0 < LENGTH(FILTER P l) ==> P(LAST(TAKE_FIRST P l))``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN,LAST_DEF]
    THEN RES_TAC
    THEN Cases_on `TAKE_FIRST P l = []`
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC TAKE_FIRST_NIL
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []);

val LAST_TAKE_FIRSTN =
 store_thm
  ("LAST_TAKE_FIRSTN",
   ``!P l n. 0 < n /\ n <= LENGTH(FILTER P l) ==> P(LAST(TAKE_FIRSTN P n l))``,
   GEN_TAC
    THEN Induct
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN]
    THEN FULL_SIMP_TAC list_ss [BUTFIRSTN,BUTFIRSTN_ONE]
    THENL
     [Cases_on `n = 0`
       THEN RW_TAC list_ss [TAKE_FIRSTN_def]
       THEN `0 < n` by DECIDE_TAC
       THEN RES_TAC
       THEN RW_TAC list_ss [LAST_DEF],
      Cases_on `n = 0`
       THEN RW_TAC list_ss [TAKE_FIRSTN_def]
       THENL
        [`0 < 1 /\ 1 <= LENGTH (FILTER P l) /\ 0 < SUC 0` by DECIDE_TAC
          THEN RES_TAC
          THEN RW_TAC list_ss [LAST_DEF]
          THEN FULL_SIMP_TAC list_ss [TAKE_FIRSTN_def]
          THEN IMP_RES_TAC TAKE_FIRST_NIL
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [],
         `0 < SUC n` by DECIDE_TAC
          THEN RES_TAC
          THEN RW_TAC list_ss [GSYM TAKE_FIRSTN_def]
          THEN RW_TAC list_ss [LAST_DEF]
          THEN FULL_SIMP_TAC list_ss [TAKE_FIRSTN_def]
          THEN IMP_RES_TAC TAKE_FIRST_NIL
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss []]]);

val LENGTH_FILTER_FIRSTN =
 store_thm
  ("LENGTH_FILTER_FIRSTN",
   ``!P n l.
      n <= LENGTH (FILTER P l)
      ==>
      (LENGTH(FILTER P (FIRSTN (LENGTH (TAKE_FIRSTN P n l)) l)) = n)``,
   RW_TAC list_ss [FIRSTN_TAKE_FIRSTN,GSYM FIRSTN_FILTER_TAKE_FIRSTN,LENGTH_FIRSTN]);

val SPLIT_APPEND = store_thm
  ("SPLIT_APPEND",
  ``!u1 u2 v1 v2:'a list.
      (u1 <> u2 = v1 <> v2) /\ (LENGTH u1 = LENGTH v1) ==> (u2 = v2)``,
    Induct
 >> RW_TAC list_ss []
 >> Cases_on `v1`
 >> RW_TAC list_ss []
 >> FULL_SIMP_TAC list_ss []);

val S_PROJ_S_BOOL =
 store_thm
  ("S_PROJ_S_BOOL",
   ``!b l c.
      S_CLOCK_FREE (S_BOOL b) /\ TOP_FREE l /\ BOTTOM_FREE l ==>
      ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) (S_BOOL b) =
       S_SEM l c (S_BOOL b))``,
   RW_TAC list_ss [LIST_PROJ_def,S_SEM_def,US_SEM_def,CLOCK_def]
    THEN RW_TAC list_ss [CLOCK_TICK_def,ELEM_EL]
    THEN RW_TAC (list_ss++resq_SS) []
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN IMP_RES_TAC LENGTH_FILTER_1_NON_EMPTY
    THEN `LENGTH l >= 1` by DECIDE_TAC
    THEN ZAP_TAC std_ss [EL_PRE_LENGTH]
    THENL
     [FULL_SIMP_TAC std_ss [GSYM CLOCK_def]
      THEN IMP_RES_TAC
             (ISPECL [``l :'a letter list``,``CLOCK c``] LENGTH_FILTER_1_NOT)
       THEN Cases_on `EL i l`
       THEN FULL_SIMP_TAC std_ss [CLOCK_def,B_SEM_def]
       THEN `i < LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC BOTTOM_FREE_EL,
      IMP_RES_TAC
       (SIMP_RULE std_ss [CLOCK_def]
         (ISPECL[``l :'a letter list``,``CLOCK c``] LENGTH_FILTER_1_LAST))
       THEN IMP_RES_TAC EL_PRE_LENGTH
       THEN PROVE_TAC[],
      `CLOCK_TICK l c`
       by PROVE_TAC[SIMP_RULE (list_ss++resq_SS) [ELEM_EL] CLOCK_TICK_def]
       THEN IMP_RES_TAC CLOCK_TICK_LENGTH_1,
      `CLOCK_TICK l c`
       by PROVE_TAC[SIMP_RULE (list_ss++resq_SS) [ELEM_EL] CLOCK_TICK_def]
       THEN IMP_RES_TAC EL_PRE_LENGTH
       THEN PROVE_TAC
             [SIMP_RULE std_ss [CLOCK_def]
               (ISPECL[``l :'a letter list``,``CLOCK c``] LENGTH_FILTER_1_LAST),
              CLOCK_TICK_LENGTH_1]]);

val S_PROJ_S_CAT_LEMMA1 =
 store_thm
  ("S_PROJ_S_CAT_LEMMA1",
   ``LENGTH (TAKE_FIRSTN (CLOCK(c:'a bexp)) (LENGTH(v1:'a letter list)) l) <= LENGTH l
     ==>
     ((FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l
      <>
      LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l) = l)``,
   RW_TAC std_ss []
    THEN `(LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) +
          (LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) = LENGTH l`
          by DECIDE_TAC
    THEN IMP_RES_TAC APPEND_FIRSTN_LASTN);

val S_PROJ_S_CAT_LEMMA2 =
 store_thm
  ("S_PROJ_S_CAT_LEMMA2",
   ``LENGTH
         (TAKE_FIRSTN (CLOCK (c :'a bexp)) (LENGTH (v1 :'a letter list))
            (l :'a letter list)) <= LENGTH l ==>
       ((FILTER (CLOCK c) (FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l) <>
          FILTER (CLOCK c) (LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l)) =
        (FILTER (CLOCK c) l))``,
   RW_TAC std_ss [GSYM FILTER_APPEND]
    THEN IMP_RES_TAC S_PROJ_S_CAT_LEMMA1
    THEN RW_TAC std_ss []);

val S_PROJ_S_CAT_LEMMA3 =
 store_thm
  ("S_PROJ_S_CAT_LEMMA3",
   ``(FILTER (CLOCK c) l =  v1 <> v2)
     ==>
     (FILTER
       (CLOCK c)
       (LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l) =
      v2)``,
   RW_TAC list_ss []
    THEN `LENGTH(TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) <= LENGTH l`
          by PROVE_TAC[LENGTH_TAKE_FIRSTN]
    THEN `LENGTH(FILTER (CLOCK c) l) = LENGTH(v1 <> v2)` by PROVE_TAC[]
    THEN FULL_SIMP_TAC list_ss [LENGTH_APPEND]
    THEN `LENGTH v1 <= LENGTH (FILTER (CLOCK c) l)` by DECIDE_TAC
    THEN PROVE_TAC[SPLIT_APPEND,LENGTH_FILTER_FIRSTN,S_PROJ_S_CAT_LEMMA2]);

val S_PROJ_S_CAT =
 store_thm
  ("S_PROJ_S_CAT",
   ``(!l c. S_CLOCK_FREE r /\ TOP_FREE l /\ BOTTOM_FREE l ==>
            ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r = S_SEM l c r))
     /\
     (!l c. S_CLOCK_FREE r' /\ TOP_FREE l /\ BOTTOM_FREE l ==>
            ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r' = S_SEM l c r'))
     ==>
     !l c. S_CLOCK_FREE (S_CAT (r,r')) /\ TOP_FREE l /\ BOTTOM_FREE l ==>
           ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) (S_CAT (r,r')) =
            S_SEM l c (S_CAT (r,r')))``,
   RW_TAC list_ss [LIST_PROJ_def,S_SEM_def,US_SEM_def,S_CLOCK_FREE_def]
    THEN RW_TAC list_ss [CLOCK_TICK_def,ELEM_EL]
    THEN RW_TAC (list_ss++resq_SS) []
    THEN EQ_TAC
    THEN RW_TAC list_ss [FILTER_APPEND]
    THENL
     [Cases_on `v1=[]` THEN Cases_on `v2=[]` (* Case split may be overkill *)
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THENL
        [Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [GSYM S_PROJ_EMPTY]
          THEN Cases_on `LENGTH l > 0`
          THEN IMP_RES_TAC
                 (ISPECL
                   [``l :'a letter list``,``CLOCK(c :'a bexp)``]LAST_FILTER_NON_EMPTY)
          THEN ZAP_TAC list_ss [CLOCK_def,LENGTH_NIL,DECIDE``~(n > 0) = (n = 0)``],
         Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [GSYM S_PROJ_EMPTY]
          THEN ASSUM_LIST
                (fn thl =>
                 ACCEPT_TAC
                  (SIMP_RULE list_ss [el 2 thl,el 4 thl,el 5 thl,el 6 thl,CLOCK_def]
                    (Q.SPECL[`l`,`c`](el 9 thl)))),
         Q.EXISTS_TAC `l` THEN Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [GSYM S_PROJ_EMPTY]
          THEN ASSUM_LIST
                (fn thl =>
                 ACCEPT_TAC
                  (SIMP_RULE list_ss [el 3 thl,el 4 thl,el 5 thl,el 6 thl,CLOCK_def]
                    (Q.SPECL[`l`,`c`](el 10 thl)))),
         `LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) <= LENGTH l`
           by PROVE_TAC[LENGTH_TAKE_FIRSTN]
          THEN `(LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l))
                + (LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) =
                LENGTH l` by DECIDE_TAC
          THEN Q.EXISTS_TAC `TAKE_FIRSTN (CLOCK c) (LENGTH v1) l`
          THEN Q.EXISTS_TAC `LASTN (LENGTH l - LENGTH(TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l`
          THEN ONCE_REWRITE_TAC[GSYM FIRSTN_TAKE_FIRSTN]
          THEN RW_TAC list_ss
                [AP_TERM ``LENGTH:'a list->num`` (SPEC_ALL FIRSTN_TAKE_FIRSTN)]
          THEN RW_TAC list_ss [APPEND_FIRSTN_LASTN]
          THEN `~(LENGTH v1 = 0) /\ ~(LENGTH v2 = 0)` by PROVE_TAC[LENGTH_NIL]
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC
                   (SIMP_RULE std_ss
                     [LENGTH_APPEND] (AP_TERM ``LENGTH:'a letter list->num`` (el 9 thl))))
          THENL
           [`LENGTH v1 <= LENGTH(FILTER (CLOCK c) l)` by DECIDE_TAC
             THEN RW_TAC list_ss [FIRSTN_TAKE_FIRSTN]
             THEN `TOP_FREE (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)`
                   by PROVE_TAC[TOP_FREE_TAKE_FIRSTN]
             THEN `BOTTOM_FREE (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)`
                   by PROVE_TAC[BOTTOM_FREE_TAKE_FIRSTN]
             THEN IMP_RES_TAC
                   (GSYM
                    (ISPECL[``CLOCK c``,``LENGTH(v1:'a letter list)``]
                      FIRSTN_FILTER_TAKE_FIRSTN))
             THEN ASSUM_LIST
                   (fn thl =>
                     (ASSUME_TAC o GSYM)
                      (SIMP_RULE std_ss
                        [FIRSTN_LENGTH_APPEND,
                         el 1 thl,el 2 thl,el 3 thl,el 4 thl,el 13 thl,el 14 thl]
                        (Q.SPECL
                          [`TAKE_FIRSTN (CLOCK c) (LENGTH(v1:'a letter list)) l`,`c`]
                          (el 21 thl))))
             THEN RW_TAC std_ss []
             THEN `0 < LENGTH v1` by DECIDE_TAC
             THEN PROVE_TAC[LAST_TAKE_FIRSTN],
            `LENGTH v2 <= LENGTH(FILTER (CLOCK c) l)` by DECIDE_TAC
             THEN `LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) <= LENGTH l`
                   by DECIDE_TAC
             THEN IMP_RES_TAC S_PROJ_S_CAT_LEMMA3
             THEN `LENGTH v2 > 0` by DECIDE_TAC
             THEN `LENGTH
                   (FILTER (CLOCK c)
                    (LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l)) > 0`
                   by PROVE_TAC[]
             THEN IMP_RES_TAC LENGTH_FILTER_NON_EMPTY
             THEN ASSUM_LIST
                   (fn thl =>
                     (ASSUME_TAC o GSYM)
                      (SIMP_RULE list_ss
                        [TOP_FREE_LASTN,BOTTOM_FREE_LASTN,LAST_LASTN_LAST,
                         el 1 thl,el 5 thl,el 18 thl,el 19 thl,el 20 thl]
                        (Q.SPECL
                          [`LASTN
                             (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH(v1:'a letter list)) l))
                             l`,
                           `c`]
                          (el 22 thl))))
             THEN IMP_RES_TAC(DECIDE ``~(n = 0) ==> 0 < n``)
             THEN IMP_RES_TAC(DECIDE ``(n = n1+n2) ==> 0<n1 ==> 0<n2 ==> n1<n``)
             THEN IMP_RES_TAC LAST_LASTN_LAST
             THEN `LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) < LENGTH l`
                   by PROVE_TAC[LENGTH_LESS_TAKE_FIRSTN]
             THEN IMP_RES_TAC
                    (DECIDE ``(LENGTH l1):num < (LENGTH l2):num ==> 0 < LENGTH l2 - LENGTH l1``)
             THEN IMP_RES_TAC LAST_LASTN_LAST
             THEN ASSUM_LIST
                   (fn thl =>
                     ASSUME_TAC(SIMP_RULE list_ss [el 1 thl,el 15 thl] (el 11 thl)))
             THEN RW_TAC std_ss []
             THEN Cases_on `LENGTH l > 0`
             THEN RW_TAC std_ss []
             THEN IMP_RES_TAC(DECIDE``~(LENGTH l:num > 0) ==> (LENGTH l = 0)``)
             THEN `l = []` by PROVE_TAC[LENGTH_NIL]
             THEN RW_TAC list_ss []]],
      Cases_on `v2`
       THEN RW_TAC list_ss [LAST_APPEND_CONS]
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_APPEND,BOTTOM_FREE_APPEND]
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [],
      Q.EXISTS_TAC `FILTER (CLOCK c) v1` THEN Q.EXISTS_TAC `FILTER (CLOCK c) v2`
       THEN RW_TAC list_ss [FILTER_APPEND]
       THEN PROVE_TAC[TOP_FREE_APPEND,BOTTOM_FREE_APPEND]]);

val LENGTH_TAKE_FIRST_SUC =
 store_thm
  ("LENGTH_TAKE_FIRST_SUC",
   ``!n P l.  LENGTH(TAKE_FIRSTN P n l) <=  LENGTH(TAKE_FIRSTN P (SUC n) l)``,
   Induct
    THEN RW_TAC list_ss [TAKE_FIRSTN_def]
    THEN Induct_on `l`
    THEN RW_TAC list_ss [TAKE_FIRST_def,TAKE_FIRSTN_def,BUTFIRSTN_ONE,BUTFIRSTN]
    THEN ASM_REWRITE_TAC[GSYM LENGTH_APPEND, GSYM TAKE_FIRSTN_def]);

val LENGTH_TAKE_FIRST_MONO =
 store_thm
  ("LENGTH_TAKE_FIRST_MONO",
   ``!n m P l.  m <= n ==> LENGTH(TAKE_FIRSTN P m l) <=  LENGTH(TAKE_FIRSTN P n l)``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `m = SUC n`
    THEN RW_TAC list_ss []
    THEN `m <= n` by DECIDE_TAC
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN PROVE_TAC
          [LENGTH_TAKE_FIRST_SUC,DECIDE``(m:num) <= (n:num) /\ n <= (p:num) ==> m <= p``]);

val LENGTH_TAKE_FIRST_GREATER =
 store_thm
  ("LENGTH_TAKE_FIRST_GREATER",
   ``!n P l. n <= LENGTH l ==> n <= LENGTH(TAKE_FIRSTN P n l)``,
   Induct
    THEN RW_TAC list_ss [TAKE_FIRSTN_def]
    THEN Induct_on `l`
    THEN RW_TAC list_ss [TAKE_FIRST_def,TAKE_FIRSTN_def,BUTFIRSTN_ONE,GSYM COND_RAND]
    THEN RES_TAC
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN RW_TAC list_ss [DECIDE ``SUC n <= m + SUC p = n <= m + p``]
    THEN IMP_RES_TAC LENGTH_BUTFIRSTN
    THEN RW_TAC list_ss [BUTFIRSTN]
    THEN REWRITE_TAC[GSYM LENGTH_APPEND, GSYM TAKE_FIRSTN_def]
    THEN `LENGTH(TAKE_FIRSTN P n l) <=  LENGTH(TAKE_FIRSTN P (SUC n) l)`
          by PROVE_TAC[LENGTH_TAKE_FIRST_SUC]
    THEN DECIDE_TAC);

val S_PROJ_S_FUSION_TOP_LEMMA =
 store_thm
  ("S_PROJ_S_FUSION_TOP_LEMMA",
   ``0 < LENGTH l /\ TOP_FREE l
     ==>
     TOP_FREE
      (LAST(FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)
       ::
       LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)``,
   RW_TAC list_ss []
    THEN `(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) <= LENGTH l`
          by PROVE_TAC[LENGTH_TAKE_FIRSTN]
    THEN `TOP_FREE(FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)`
          by PROVE_TAC[TOP_FREE_FIRSTN]
    THEN `1 <= LENGTH l` by DECIDE_TAC
    THEN `1 <= LENGTH (TAKE_FIRSTN (CLOCK c) 1 l)`
          by PROVE_TAC[LENGTH_TAKE_FIRST_GREATER]
    THEN `1 <= SUC(LENGTH v1)` by DECIDE_TAC
    THEN `LENGTH (TAKE_FIRSTN (CLOCK c) 1 l) <= LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)`
          by PROVE_TAC[LENGTH_TAKE_FIRST_MONO]
    THEN `0 < LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)`
          by DECIDE_TAC
    THEN `TOP_FREE[LAST(TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)]`
          by PROVE_TAC[TOP_FREE_LAST,TOP_FREE_TAKE_FIRSTN]
    THEN `TOP_FREE[LAST(FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)]`
          by PROVE_TAC[FIRSTN_TAKE_FIRSTN]
    THEN ONCE_REWRITE_TAC[GSYM(SIMP_CONV list_ss [] ``[x]<>l``)]
    THEN RW_TAC list_ss [TOP_FREE_APPEND,TOP_FREE_LASTN]);

val S_PROJ_S_FUSION_BOTTOM_LEMMA =
 store_thm
  ("S_PROJ_S_FUSION_BOTTOM_LEMMA",
   ``0 < LENGTH l /\ BOTTOM_FREE l
     ==>
     BOTTOM_FREE
      (LAST(FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)
       ::
       LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)``,
   RW_TAC list_ss []
    THEN `(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) <= LENGTH l`
          by PROVE_TAC[LENGTH_TAKE_FIRSTN]
    THEN `BOTTOM_FREE(FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)`
          by PROVE_TAC[BOTTOM_FREE_FIRSTN]
    THEN `1 <= LENGTH l` by DECIDE_TAC
    THEN `1 <= LENGTH (TAKE_FIRSTN (CLOCK c) 1 l)`
          by PROVE_TAC[LENGTH_TAKE_FIRST_GREATER]
    THEN `1 <= SUC(LENGTH v1)` by DECIDE_TAC
    THEN `LENGTH (TAKE_FIRSTN (CLOCK c) 1 l) <= LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)`
          by PROVE_TAC[LENGTH_TAKE_FIRST_MONO]
    THEN `0 < LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)`
          by DECIDE_TAC
    THEN `BOTTOM_FREE[LAST(TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)]`
          by PROVE_TAC[BOTTOM_FREE_LAST,BOTTOM_FREE_TAKE_FIRSTN]
    THEN `BOTTOM_FREE[LAST(FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)]`
          by PROVE_TAC[FIRSTN_TAKE_FIRSTN]
    THEN ONCE_REWRITE_TAC[GSYM(SIMP_CONV list_ss [] ``[x]<>l``)]
    THEN RW_TAC list_ss [BOTTOM_FREE_APPEND,BOTTOM_FREE_LASTN]);

val S_PROJ_S_CAT_LEMMA4 =
 store_thm
  ("S_PROJ_S_CAT_LEMMA4",
   ``!v1 v2 l c.
      (FILTER (CLOCK c) l =  v1 <> v2)
      ==>
      (FILTER
        (CLOCK c)
        (FIRSTN (LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l)) l) =
       v1)``,
   RW_TAC list_ss []
    THEN `LENGTH(FILTER (CLOCK c) l) = LENGTH(v1 <> v2)` by PROVE_TAC[]
    THEN FULL_SIMP_TAC list_ss [LENGTH_APPEND]
    THEN `LENGTH v1 <= LENGTH (FILTER (CLOCK c) l)` by DECIDE_TAC
    THEN `LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) <= LENGTH l` by PROVE_TAC[LENGTH_TAKE_FIRSTN]
    THEN `LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) +
          LENGTH (TAKE_FIRSTN (CLOCK c) (LENGTH v1) l) =
          LENGTH l` by DECIDE_TAC
    THEN IMP_RES_TAC
          (Q.ISPECL
            [`LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK(c:'a bexp)) (LENGTH(v1:'a letter list)) l)`,
             `LENGTH (TAKE_FIRSTN (CLOCK(c:'a bexp)) (LENGTH(v1:'a letter list)) l)`,
             `l:'a letter list`]
           APPEND_FIRSTN_LASTN)
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE list_ss [FILTER_APPEND]
                              o AP_TERM ``FILTER (CLOCK c):'a letter list->'a letter list``)
    THEN IMP_RES_TAC S_PROJ_S_CAT_LEMMA3
    THEN PROVE_TAC[APPEND_RIGHT_CANCEL]);

val S_PROJ_S_FUSION_LEMMA1 =
 store_thm
  ("S_PROJ_S_FUSION_LEMMA1",
   ``(FILTER (CLOCK c) l = v1 <> [l'] <> v2)
     ==>
     (FILTER (CLOCK c)
      (LASTN (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) l)
      = v2)``,
   ACCEPT_TAC
    (REWRITE_RULE
      [GSYM ADD1,LENGTH_TAKE_FIRSTN]
      (SIMP_RULE list_ss []
        (Q.SPECL [`v2`,`v1<>[l']`,`l`,`c`](GEN_ALL S_PROJ_S_CAT_LEMMA3)))));

val S_PROJ_S_FUSION_LEMMA2 =
 store_thm
  ("S_PROJ_S_FUSION_LEMMA2",
   ``(FILTER (CLOCK c) l = v1 <> [l'] <> v2)
     ==>
     (FILTER (CLOCK c) (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l) = v1 <> [l'])``,
     PROVE_TAC
           [LENGTH_TAKE_FIRSTN, FIRSTN_TAKE_FIRSTN, LENGTH_APPEND,
            (SIMP_RULE
              list_ss
              [LENGTH_APPEND,GSYM ADD1]
              (ISPECL
                [``(v1<>[l']) :'a letter list``, ``v2 :'a letter list``, ``l :'a letter list``, ``c :'a bexp``]
                S_PROJ_S_CAT_LEMMA4))]);

val LAST_FILTER =  (* Must be a nicer proof than this! *)
 store_thm
  ("LAST_FILTER",
   ``!P l. P(LAST l) ==> (LAST(FILTER P l) = LAST l)``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `l`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN Cases_on `h=h'`
    THEN RW_TAC list_ss []
    THEN RES_TAC
    THEN Cases_on `t = []`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN `?x l'. t = x::l'` by PROVE_TAC[NULL_EQ_NIL,CONS]
    THEN ASM_REWRITE_TAC[LAST_CONS]
    THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [GSYM th])
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE list_ss [el 1 thl,LAST_DEF] (el 4 thl)))
    THEN `~(LENGTH t = 0)` by PROVE_TAC[LENGTH_NIL]
    THEN `LENGTH t >= 1` by DECIDE_TAC
    THEN IMP_RES_TAC EL_PRE_LENGTH
    THEN `LENGTH t - 1 < LENGTH t` by DECIDE_TAC
    THEN `LENGTH t > 0` by DECIDE_TAC
    THEN `~(FILTER P t = [])` by PROVE_TAC[FILTER_NON_EMPTY]
    THEN PROVE_TAC[LAST_DEF]);

val S_PROJ_S_FUSION_LEMMA3 =
 store_thm
  ("S_PROJ_S_FUSION_LEMMA3",
   ``!v1 l' v2.
      (FILTER (CLOCK c) l = v1 <> [l'] <> v2)
      ==>
      (LAST (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l) = l')``,
   RW_TAC list_ss []
    THEN IMP_RES_TAC S_PROJ_S_FUSION_LEMMA2
    THEN `LAST(FILTER (CLOCK c) (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l)) = l'`
          by PROVE_TAC[LAST_SINGLETON]
    THEN `LENGTH(FILTER (CLOCK c) l) =  LENGTH(v1 <> [l'] <> v2)`
          by PROVE_TAC[]
    THEN FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH]
    THEN `0 < SUC (LENGTH v1)` by DECIDE_TAC
    THEN `SUC (LENGTH v1) <= LENGTH(FILTER (CLOCK c) l)`
          by DECIDE_TAC
    THEN `CLOCK c (LAST (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l))`
          by PROVE_TAC[LAST_TAKE_FIRSTN]
    THEN PROVE_TAC[LAST_FILTER]);

val FILTER_LAST =
 store_thm
  ("FILTER_LAST",
   ``!P l l' x. (FILTER P l = l' <> [x]) ==> P x``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
    THEN `TL(h::FILTER P l) = TL(l' <> [x])` by PROVE_TAC[]
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE list_ss [])
    THEN Cases_on `l'`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []);

val S_PROJ_S_FUSION =
 store_thm
  ("S_PROJ_S_FUSION",
   ``(!l c. S_CLOCK_FREE r /\ TOP_FREE l /\ BOTTOM_FREE l ==>
            ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r = S_SEM l c r))
     /\
     (!l c. S_CLOCK_FREE r' /\ TOP_FREE l /\ BOTTOM_FREE l ==>
            ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r' = S_SEM l c r'))
     ==>
     !l c. S_CLOCK_FREE (S_FUSION (r,r')) /\ TOP_FREE l /\ BOTTOM_FREE l ==>
           ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) (S_FUSION (r,r')) =
            S_SEM l c (S_FUSION (r,r')))``,
   RW_TAC list_ss [LIST_PROJ_def,S_SEM_def,US_SEM_def,S_CLOCK_FREE_def]
    THEN RW_TAC list_ss [CLOCK_TICK_def,ELEM_EL]
    THEN RW_TAC (list_ss++resq_SS) []
    THEN EQ_TAC
    THEN RW_TAC list_ss [FILTER_APPEND]
    THENL
     [Cases_on `l = []`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `0 < SUC(LENGTH v1)` by DECIDE_TAC
       THEN `~(TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l = [])`
         by PROVE_TAC[TAKE_FIRSTN_EQ_NIL_E]
       THEN Q.EXISTS_TAC `BUTLAST(TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l)`
       THEN Q.EXISTS_TAC `LASTN (LENGTH l - LENGTH(TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l)) l`
       THEN Q.EXISTS_TAC `LAST(TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l)`
       THEN RW_TAC list_ss [APPEND_FRONT_LAST]
       THEN ONCE_REWRITE_TAC[GSYM FIRSTN_TAKE_FIRSTN]
       THEN RW_TAC list_ss
             [AP_TERM ``LENGTH:'a list->num`` (SPEC_ALL FIRSTN_TAKE_FIRSTN)]
       THENL
        [`LENGTH (TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l) <= LENGTH l`
          by PROVE_TAC[LENGTH_TAKE_FIRSTN]
          THEN `(LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l))
                + (LENGTH (TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l)) =
                LENGTH l` by DECIDE_TAC
          THEN RW_TAC list_ss [APPEND_FIRSTN_LASTN],
         RW_TAC list_ss [FIRSTN_TAKE_FIRSTN]
          THEN `TOP_FREE (TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l)`
                by PROVE_TAC[TOP_FREE_TAKE_FIRSTN]
          THEN `BOTTOM_FREE (TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l)`
                by PROVE_TAC[BOTTOM_FREE_TAKE_FIRSTN]
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC
                   (SIMP_RULE list_ss
                     [LENGTH_APPEND] (AP_TERM ``LENGTH:'a letter list->num`` (el 8 thl))))
          THEN `SUC (LENGTH v1) <= LENGTH (FILTER (CLOCK c) l)` by DECIDE_TAC
          THEN IMP_RES_TAC
                  (GSYM
                   (ISPECL[``CLOCK c``,``SUC(LENGTH(v1:'a letter list))``]
                     FIRSTN_FILTER_TAKE_FIRSTN))
          THEN `SUC(LENGTH v1) = LENGTH(v1 <> [l'])` by RW_TAC list_ss []
          THEN ASSUM_LIST
                (fn thl =>
                 (ASSUME_TAC o GSYM)
                  (SIMP_RULE std_ss
                    [FIRSTN_LENGTH_APPEND,
                     el 1 thl,el 2 thl,el 4 thl,el 5 thl,el 6 thl,el 11 thl,el 12 thl]
                    (Q.SPECL
                      [`TAKE_FIRSTN (CLOCK c) (SUC(LENGTH(v1:'a letter list))) l`,`c`]
                      (el 19 thl))))
          THEN RW_TAC std_ss []
          THEN `0 < LENGTH(v1 <> [l'])` by RW_TAC list_ss []
          THEN `LENGTH(v1 <> [l']) <= LENGTH (FILTER (CLOCK c) l)` by RW_TAC list_ss []
          THEN PROVE_TAC[LAST_TAKE_FIRSTN],
         `~(LENGTH l = 0)` by PROVE_TAC[LENGTH_NIL]
          THEN `0 < LENGTH l` by DECIDE_TAC
          THEN ASSUM_LIST
                (fn thl =>
                  (ASSUME_TAC o GSYM)
                   (SIMP_RULE std_ss
                     [S_PROJ_S_FUSION_TOP_LEMMA,S_PROJ_S_FUSION_BOTTOM_LEMMA,FIRSTN_TAKE_FIRSTN,
                      el 1 thl,el 10 thl,el 11 thl]
                     (Q.SPECL
                       [`(LAST
                          (FIRSTN
                           (LENGTH
                            (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH(v1:'a letter list))) l)) l)
                          ::
                          LASTN
                           (LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l))
                            l)`,
                        `c`]
                       (el 14 thl))))
          THEN ASM_REWRITE_TAC[FIRSTN_TAKE_FIRSTN]
          THEN POP_ASSUM(K ALL_TAC)
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC
                   (SIMP_RULE list_ss
                     [LENGTH_APPEND] (AP_TERM ``LENGTH:'a letter list->num`` (el 8 thl))))
          THEN `SUC (LENGTH v1) <= LENGTH(FILTER (CLOCK c) l)` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THENL
           [Cases_on `(LENGTH l - LENGTH (TAKE_FIRSTN (CLOCK c) (SUC (LENGTH v1)) l))`
             THEN RW_TAC list_ss [LASTN,LAST_TAKE_FIRSTN]
             THEN `SUC n <= LENGTH l` by DECIDE_TAC
             THEN Cases_on `LASTN (SUC n) l = []`
             THEN RW_TAC list_ss [LAST_LASTN_LAST,LAST_TAKE_FIRSTN]
             THEN `?x l'. LASTN (SUC n) l = x::l'` by PROVE_TAC[NULL_EQ_NIL,CONS]
             THEN RW_TAC list_ss [LAST_CONS]
             THEN POP_ASSUM(fn th => REWRITE_TAC[GSYM th])
             THEN RW_TAC list_ss [LAST_LASTN_LAST],
            IMP_RES_TAC S_PROJ_S_FUSION_LEMMA3
             THEN ASM_REWRITE_TAC []
             THEN IMP_RES_TAC S_PROJ_S_FUSION_LEMMA1
             THEN IMP_RES_TAC S_PROJ_S_FUSION_LEMMA2
             THEN ONCE_REWRITE_TAC[GSYM(SIMP_CONV list_ss [] ``[x]<>l``)]
             THEN ASM_REWRITE_TAC[FILTER_APPEND]
             THEN IMP_RES_TAC FILTER_LAST
             THEN RW_TAC list_ss []]],
      Cases_on `v2`
       THEN RW_TAC list_ss [LAST_APPEND_CONS]
       THEN IMP_RES_TAC S_CLOCK_LAST
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_APPEND,BOTTOM_FREE_APPEND,LAST_SINGLETON],
      Q.EXISTS_TAC `FILTER (CLOCK c) v1`
       THEN Q.EXISTS_TAC `FILTER (CLOCK c) v2`
       THEN Q.EXISTS_TAC `l'`
       THEN RW_TAC list_ss [FILTER_APPEND]
       THENL
        [IMP_RES_TAC S_CLOCK_LAST
          THEN FULL_SIMP_TAC list_ss [LAST_SINGLETON],
         `TOP_FREE(v1 <> [l'])` by PROVE_TAC[TOP_FREE_APPEND]
          THEN `BOTTOM_FREE(v1 <> [l'])` by PROVE_TAC[BOTTOM_FREE_APPEND]
          THEN `US_SEM (FILTER (CLOCK c)(v1 <> [l'])) r` by PROVE_TAC[]
          THEN IMP_RES_TAC S_CLOCK_LAST
          THEN FULL_SIMP_TAC list_ss [FILTER_APPEND,LAST_SINGLETON],
         `TOP_FREE([l'] <> v2)` by PROVE_TAC[TOP_FREE_APPEND]
          THEN `BOTTOM_FREE([l'] <> v2)` by PROVE_TAC[BOTTOM_FREE_APPEND]
          THEN FULL_SIMP_TAC list_ss []
          THEN `US_SEM (FILTER (CLOCK c)(l' :: v2)) r'` by PROVE_TAC[]
          THEN IMP_RES_TAC S_CLOCK_LAST
          THEN FULL_SIMP_TAC list_ss [FILTER_APPEND,LAST_SINGLETON]]]);

val US_SEM_S_EMPTY =
 store_thm
  ("US_SEM_S_EMPTY",
   ``US_SEM l S_EMPTY = (l = [])``,
   RW_TAC std_ss [US_SEM_def]);

val S_SEM_S_EMPTY =
 store_thm
  ("S_SEM_S_EMPTY",
   ``S_SEM l c S_EMPTY = (l = [])``,
   RW_TAC std_ss [S_SEM_def]);

val S_PROJ_S_EMPTY =
 store_thm
  ("S_PROJ_S_EMPTY",
   ``!l c.
      TOP_FREE l /\ BOTTOM_FREE l ==>
      ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\
       US_SEM (LIST_PROJ l c) S_EMPTY =
       S_SEM l c S_EMPTY)``,
   RW_TAC list_ss [S_SEM_def,US_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss [CLOCK_def,BOTTOM_FREE_def]
    THEN FULL_SIMP_TAC list_ss [LIST_PROJ_def,GSYM CLOCK_def]
    THEN IMP_RES_TAC LAST_FILTER_NON_EMPTY
    THEN Cases_on `l = []`
    THEN RW_TAC list_ss []
    THEN `~(LENGTH l = 0)` by PROVE_TAC[LENGTH_NIL]
    THEN `LENGTH l > 0` by DECIDE_TAC
    THEN PROVE_TAC[LAST_FILTER_NON_EMPTY]);

val S_CATN_def =
 Define
  `(S_CATN 0 r = S_EMPTY) /\ (S_CATN (SUC n) r = S_CAT(r, S_CATN n r))`;

val US_SEM_REPEAT_CATN =
 store_thm
  ("US_SEM_REPEAT_CATN",
   ``!v r. US_SEM v (S_REPEAT r) = ?n. US_SEM v (S_CATN n r)``,
   RW_TAC list_ss [US_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]
       THENL
        [Q.EXISTS_TAC `0`
          THEN RW_TAC list_ss [S_CATN_def,US_SEM_S_EMPTY],
         RES_TAC
          THEN Q.EXISTS_TAC `SUC n`
          THEN RW_TAC list_ss [S_CATN_def,US_SEM_def]
          THEN Q.EXISTS_TAC `h`
          THEN Q.EXISTS_TAC `CONCAT vlist`
          THEN RW_TAC list_ss []],
      Q.UNDISCH_TAC `US_SEM v (S_CATN n r)`
       THEN Q.SPEC_TAC(`v`,`v`)
       THEN Q.SPEC_TAC(`r`,`r`)
       THEN Q.SPEC_TAC(`n`,`n`)
       THEN Induct
       THEN RW_TAC list_ss [S_CATN_def,US_SEM_S_EMPTY]
       THENL
        [Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [CONCAT_def],
         FULL_SIMP_TAC list_ss [US_SEM_def]
          THEN RES_TAC
          THEN RW_TAC std_ss []
          THEN Q.EXISTS_TAC `v1::vlist`
          THEN RW_TAC list_ss [CONCAT_def]]]);


val S_SEM_REPEAT_CATN =
 store_thm
  ("S_SEM_REPEAT_CATN",
   ``!v r c. S_SEM v c (S_REPEAT r) = ?n. S_SEM v c (S_CATN n r)``,
   RW_TAC list_ss [S_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]
       THENL
        [Q.EXISTS_TAC `0`
          THEN RW_TAC list_ss [S_CATN_def,S_SEM_S_EMPTY],
         RES_TAC
          THEN Q.EXISTS_TAC `SUC n`
          THEN RW_TAC list_ss [S_CATN_def,S_SEM_def]
          THEN Q.EXISTS_TAC `h`
          THEN Q.EXISTS_TAC `CONCAT vlist`
          THEN RW_TAC list_ss []],
      Q.UNDISCH_TAC `S_SEM v c (S_CATN n r)`
       THEN Q.SPEC_TAC(`v`,`v`)
       THEN Q.SPEC_TAC(`r`,`r`)
       THEN Q.SPEC_TAC(`n`,`n`)
       THEN Induct
       THEN RW_TAC list_ss [S_CATN_def,S_SEM_S_EMPTY]
       THENL
        [Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [CONCAT_def],
         FULL_SIMP_TAC list_ss [S_SEM_def]
          THEN RES_TAC
          THEN RW_TAC std_ss []
          THEN Q.EXISTS_TAC `v1::vlist`
          THEN RW_TAC list_ss [CONCAT_def]]]);

val S_PROJ_CORRECT_def =
 Define
  `S_PROJ_CORRECT r =
    !l c.
     S_CLOCK_FREE r /\ TOP_FREE l /\ BOTTOM_FREE l ==>
     ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r = S_SEM l c r)`;

val S_PROJ_CORRECT_EMPTY =
 store_thm
  ("S_PROJ_CORRECT_EMPTY",
   ``S_PROJ_CORRECT S_EMPTY``,
   RW_TAC std_ss [S_PROJ_CORRECT_def,S_PROJ_S_EMPTY]);

val S_PROJ_CORRECT_CAT =
 store_thm
  ("S_PROJ_CORRECT_CAT",
   ``!r1 r2. S_PROJ_CORRECT r1 /\ S_PROJ_CORRECT r2
             ==>
             S_PROJ_CORRECT(S_CAT(r1,r2))``,
   RW_TAC std_ss [S_PROJ_CORRECT_def,S_PROJ_S_CAT]);

val S_PROJ_CORRECT_CATN =
 store_thm
  ("S_PROJ_CORRECT_CATN",
   ``!r. S_PROJ_CORRECT r ==> !n. S_PROJ_CORRECT(S_CATN n r)``,
   GEN_TAC THEN DISCH_TAC
    THEN Induct
    THEN RW_TAC std_ss [S_CATN_def,S_PROJ_CORRECT_EMPTY,S_PROJ_CORRECT_CAT]);

val S_CLOCK_FREE_CATN =
 store_thm
  ("S_CLOCK_FREE_CATN",
   ``!r. S_CLOCK_FREE r ==> !n. S_CLOCK_FREE(S_CATN n r)``,
   GEN_TAC THEN DISCH_TAC
    THEN Induct
    THEN RW_TAC list_ss [S_CATN_def,S_CLOCK_FREE_def]);

val S_PROJ_S_REPEAT =
 store_thm
  ("S_PROJ_S_REPEAT",
   ``(!l c.
       S_CLOCK_FREE r /\ TOP_FREE l /\ BOTTOM_FREE l ==>
       ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r = S_SEM l c r))
     ==>
     !l c.
       S_CLOCK_FREE (S_REPEAT r) /\ TOP_FREE l /\ BOTTOM_FREE l ==>
       ((LENGTH l > 0 ==> CLOCK c (LAST l)) /\
        US_SEM (LIST_PROJ l c) (S_REPEAT r) =
        S_SEM l c (S_REPEAT r))``,
   RW_TAC std_ss [US_SEM_REPEAT_CATN,S_SEM_REPEAT_CATN,S_CLOCK_FREE_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC std_ss [GSYM S_PROJ_CORRECT_def]
    THEN `S_CLOCK_FREE(S_CATN n r)` by PROVE_TAC[S_CLOCK_FREE_CATN]
    THEN IMP_RES_TAC S_PROJ_CORRECT_CATN
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [S_PROJ_CORRECT_def] o SPEC_ALL)
    THEN PROVE_TAC[]);

val S_PROJ =
 store_thm
  ("S_PROJ",
   ``!r.
      S_CLOCK_FREE r
      ==>
      !l. TOP_FREE l /\ BOTTOM_FREE l
          ==>
          !c. S_SEM l c r = (LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      RW_TAC std_ss [S_PROJ_S_BOOL],
      (* S_CAT(r,r') *)
      RW_TAC std_ss [S_PROJ_S_CAT],
      (* S_FUSION (r,r') *)
      RW_TAC std_ss [S_PROJ_S_FUSION],
      (* S_OR (r,r') *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN EQ_TAC
       THEN ZAP_TAC list_ss [CLOCK_def],
      (* S_AND (r,r') *)
      RW_TAC list_ss [S_SEM_def,US_SEM_def,CLOCK_def,S_CLOCK_FREE_def]
       THEN EQ_TAC
       THEN ZAP_TAC list_ss [CLOCK_def],
      (* S_EMPTY *)
      PROVE_TAC[S_PROJ_S_EMPTY],  (* for some reason RW_TAC std_ss [S_PROJ_S_EMPTY] fails *)
      (* S_REPEAT r *)
      RW_TAC std_ss [S_PROJ_S_REPEAT],
      (* S_CLOCK (r,p_2) *)
      RW_TAC list_ss [S_CLOCK_FREE_def]]);

val S_PROJ_COR =
 store_thm
  ("S_PROJ_COR",
   ``!r l c.
      S_CLOCK_FREE r
      ==>
      TOP_FREE l /\ BOTTOM_FREE l
      ==>
      (S_SEM l c r =
       (LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r)``,
   PROVE_TAC[S_PROJ]);

(*****************************************************************************)
(* Start developing projection view for formulas                             *)
(*****************************************************************************)

(*****************************************************************************)
(* Switch default to general (i.e. finite or infinite) paths                 *)
(*****************************************************************************)
open PSLPathTheory;

(******************************************************************************
* FUN_FILTER_COUNT P f m n = P is true for the mth time in f at position n
******************************************************************************)
val FUN_FILTER_COUNT_def =
 Define
  `(FUN_FILTER_COUNT P f 0 n = P(f n) /\ !i :: LESS n. ~P(f i))
   /\
   (FUN_FILTER_COUNT P f (SUC m) n =
     ?n' :: LESS n.
      FUN_FILTER_COUNT P f m n'  /\ P(f n) /\ !i :: LESS n. n' < i ==> ~P(f i))`;

val PATH_FILTER_def =
 Define
  `(PATH_FILTER P (FINITE l) = FINITE(FILTER P l))
   /\
   (PATH_FILTER P (INFINITE f) =
     if (!m:num. ?n. m <= n /\ P(f n))
      then INFINITE(f o (\m. LEAST n. FUN_FILTER_COUNT P f m n))
      else FINITE(FILTER P (GENLIST f (LEAST i. !j. i <= j ==> ~P(f j)))))`;

val PROJ_def = Define `PROJ p c = PATH_FILTER (CLOCK c) p`;

val FUN_FILTER_COUNT_UNIQUE =
 store_thm
  ("FUN_FILTER_COUNT_UNIQUE",
   ``!P f m n1 n2.
      FUN_FILTER_COUNT P f m n1 /\ FUN_FILTER_COUNT P f m n2 ==> (n1 = n2)``,
   GEN_TAC THEN GEN_TAC
    THEN Induct
    THEN RW_TAC (list_ss++resq_SS) [FUN_FILTER_COUNT_def]
    THENL
     [Cases_on `n1 < n2`
       THEN RES_TAC
       THEN Cases_on `n2 < n1`
       THEN RES_TAC
       THEN DECIDE_TAC,
      `n' = n''` by PROVE_TAC[]
       THEN Cases_on `n1 < n2`
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN Cases_on `n2 < n1`
       THEN RES_TAC
       THEN DECIDE_TAC]);

(*
val PROJ_def =
 Define
  `(PROJ (FINITE l) c = FINITE(LIST_PROJ l c))
   /\
   (PROJ (INFINITE f) c =
     if !m. ?n. FUN_FILTER_COUNT (CLOCK c) f m n
      then INFINITE(\m. f(@n. FUN_FILTER_COUNT (CLOCK c) f m n))
      else FINITE
            (FILTER
             (CLOCK c)
             (GENLIST f (LEAST i. !j. j > i ==> ~CLOCK c (f j)))))`;
*)

(******************************************************************************
* F_CLOCK_FREE f means f contains no clocking statements
******************************************************************************)
val F_CLOCK_FREE_def =
 Define
  `(F_CLOCK_FREE (F_STRONG_BOOL b)   = T)
   /\
   (F_CLOCK_FREE (F_WEAK_BOOL b)     = T)
   /\
   (F_CLOCK_FREE (F_NOT f)           = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_AND(f1,f2))      = F_CLOCK_FREE f1 /\ F_CLOCK_FREE f2)
   /\
   (F_CLOCK_FREE (F_STRONG_SERE r)   = S_CLOCK_FREE r)
   /\
   (F_CLOCK_FREE (F_WEAK_SERE r)     = S_CLOCK_FREE r)
   /\
   (F_CLOCK_FREE (F_NEXT f)          = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_UNTIL(f1,f2))    = F_CLOCK_FREE f1 /\ F_CLOCK_FREE f2)
   /\
   (F_CLOCK_FREE (F_ABORT (f,b))     = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_SUFFIX_IMP(r,f)) = F_CLOCK_FREE f /\ S_CLOCK_FREE r)
   /\
   (F_CLOCK_FREE (F_CLOCK v)         = F)`;

val PATH_TOP_FREE_def =
 Define
  `(PATH_TOP_FREE(FINITE l)   = TOP_FREE l)
   /\
   (PATH_TOP_FREE(INFINITE f) = !n. ~(f n = TOP))`;

val PATH_BOTTOM_FREE_def =
 Define
  `(PATH_BOTTOM_FREE(FINITE l)   = BOTTOM_FREE l)
   /\
   (PATH_BOTTOM_FREE(INFINITE f) = !n. ~(f n = BOTTOM))`;

val HD_RESTN_TL =
 store_thm
  ("HD_RESTN_TL",
   ``!n l. HD (RESTN (TL l) n) = EL n (TL l)``,
   Induct
    THEN RW_TAC list_ss
          [FinitePSLPathTheory.RESTN_def,FinitePSLPathTheory.REST_def,EL]);

val ELEM_FINITE =
 store_thm
  ("ELEM_FINITE",
   ``!n l. ELEM (FINITE l) n = EL n l``,
   Induct
    THEN RW_TAC list_ss
          [ELEM_def,HEAD_def,RESTN_def,
           FinitePSLPathTheory.RESTN_def,FinitePSLPathTheory.REST_def,
           REST_def,RESTN_FINITE,HD_RESTN_TL,EL]);

val ELEM_INFINITE =
 store_thm
  ("ELEM_INFINITE",
   ``!n f. ELEM (INFINITE f) n = f n``,
   Induct
    THEN RW_TAC list_ss
          [ELEM_def,HEAD_def,RESTN_INFINITE]);

val LENGTH_FILTER_NON_ZERO_EXISTS =
 store_thm
  ("LENGTH_FILTER_NON_ZERO_EXISTS",
   ``!P l. LENGTH (FILTER P l) > 0 ==> ?n. n < LENGTH l /\ P (EL n l)``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
    THENL
     [Q.EXISTS_TAC `0`
       THEN RW_TAC list_ss [],
      RES_TAC
       THEN Q.EXISTS_TAC `SUC n`
       THEN RW_TAC list_ss []]);

val NON_ZERO_EXISTS_LENGTH_FILTER =
 store_thm
  ("NON_ZERO_EXISTS_LENGTH_FILTER",
   ``!P l n. n < LENGTH l /\ P (EL n l) ==> LENGTH (FILTER P l) > 0``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `n`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN RES_TAC);


(*
val FUN_FILTER_COUNT =
 store_thm
  ("FUN_FILTER_COUNT",
   ``!P f.
      (!m. ?n. FUN_FILTER_COUNT P f m n)
      ==>
      !m.
       FUN_FILTER_COUNT P f m ((\m. @n. FUN_FILTER_COUNT P f m n)m)``,
   RW_TAC std_ss []
     THEN POP_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL)
     THEN IMP_RES_TAC SELECT_AX
     THEN CONV_TAC(DEPTH_CONV ETA_CONV)
     THEN RW_TAC std_ss []);
*)

val FUN_FILTER_COUNT =
 store_thm
  ("FUN_FILTER_COUNT",
   ``!P f.
      (!m. ?n. FUN_FILTER_COUNT P f m n)
      ==>
      !m.
       FUN_FILTER_COUNT P f m (@n. FUN_FILTER_COUNT P f m n)``,
   RW_TAC std_ss []
     THEN POP_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL)
     THEN IMP_RES_TAC SELECT_AX
     THEN CONV_TAC(DEPTH_CONV ETA_CONV)
     THEN RW_TAC std_ss []);

val FUN_FILTER_COUNT_EXISTS =
 store_thm
  ("FUN_FILTER_COUNT_EXISTS",
   ``!P f.
      (!n:num. ?n'. n <= n' /\ P(f n'))
      ==>
      !m. ?n. FUN_FILTER_COUNT P f m n``,
   RW_TAC std_ss []
    THEN Induct_on `m`
    THEN RW_TAC (list_ss++resq_SS) [FUN_FILTER_COUNT_def]
    THENL
     [POP_ASSUM(STRIP_ASSUME_TAC o SPEC ``0``)
       THEN FULL_SIMP_TAC arith_ss []
       THEN IMP_RES_TAC
             (SIMP_RULE std_ss []
               (ISPEC ``(P :'a -> bool) o (f :num -> 'a)`` LEAST_EXISTS))
       THEN Q.EXISTS_TAC `$LEAST (P o f)`
       THEN RW_TAC arith_ss [],
      ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `SUC n` (el 2 thl)))
       THEN IMP_RES_TAC
             (SIMP_RULE std_ss []
               (ISPEC ``\n':num. (P :'a -> bool)(f n') /\ SUC n <= n'`` LEAST_EXISTS))
       THEN Q.EXISTS_TAC `LEAST n'. P (f n') /\ SUC n <= n'`
       THEN Q.EXISTS_TAC `n`
       THEN RW_TAC arith_ss []
       THEN `SUC n <= i` by DECIDE_TAC
       THEN Cases_on `P (f i)`
       THEN RW_TAC arith_ss []
       THEN IMP_RES_TAC LESS_LEAST
       THEN POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[GSYM NOT_LESS] o SIMP_RULE std_ss [])]);

val NOT_FUN_FILTER_COUNT =
 store_thm
  ("NOT_FUN_FILTER_COUNT",
   ``!P f.
      ~(!m. ?n. FUN_FILTER_COUNT P f m n)
      ==>
      ?n:num. !n'. n <= n' ==> ~P(f n')``,
   PROVE_TAC[FUN_FILTER_COUNT_EXISTS]);

val LEAST0 =
 store_thm
  ("LEAST0",
   ``!P. (?i. P i) /\ ((LEAST i. P i) = 0) = P 0``,
   GEN_TAC
    THEN EQ_TAC
    THEN ZAP_TAC list_ss [LESS_LEAST]
    THEN IMP_RES_TAC FULL_LEAST_INTRO
    THENL
     [ASSUM_LIST
       (fn thl => ASSUME_TAC(GSYM(CONV_RULE(DEPTH_CONV ETA_CONV)(el 5 thl))))
       THEN RW_TAC arith_ss [],
      CONV_TAC(DEPTH_CONV ETA_CONV)
       THEN DECIDE_TAC]);

val IS_LEAST_def =
 Define
  `IS_LEAST P n = P n /\ !m:num. m < n ==> ~P m`;

val IS_LEAST_UNIQUE =
 store_thm
  ("IS_LEAST_UNIQUE",
   ``!P m n. IS_LEAST P m /\ IS_LEAST P n ==> (m = n)``,
   RW_TAC arith_ss [IS_LEAST_def]
    THEN Cases_on `m < n`
    THEN RES_TAC
    THEN Cases_on `n < m`
    THEN RES_TAC
    THEN DECIDE_TAC);

val IS_LEAST_SUC =
 store_thm
  ("IS_LEAST_SUC",
   ``!P n. ~(P 0) ==> (IS_LEAST P (SUC n) = IS_LEAST (P o SUC) n)``,
   RW_TAC arith_ss [IS_LEAST_def]
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THEN Cases_on `m = 0`
    THEN RW_TAC arith_ss []
    THEN `PRE m < n` by DECIDE_TAC
    THEN `SUC(PRE m) = m` by DECIDE_TAC
    THEN PROVE_TAC[]);

val IS_LEAST_LEAST =
 store_thm
  ("IS_LEAST_LEAST",
   ``!P n. P n ==> IS_LEAST P (LEAST n. P n)``,
   CONV_TAC(DEPTH_CONV ETA_CONV)
    THEN RW_TAC std_ss [IS_LEAST_def]
    THEN IMP_RES_TAC LEAST_INTRO
    THEN IMP_RES_TAC LESS_LEAST);

val IS_LEAST_EQ_IMP =
 store_thm
  ("IS_LEAST_EQ_IMP",
   ``!P m. IS_LEAST P m ==> (m = $LEAST P)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC IS_LEAST_def
    THEN IMP_RES_TAC IS_LEAST_LEAST
    THEN IMP_RES_TAC IS_LEAST_UNIQUE
    THEN RW_TAC std_ss []
    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
    THEN RW_TAC std_ss []);

val IS_LEAST_EQ =
 store_thm
  ("IS_LEAST_EQ",
   ``!P n. IS_LEAST P n = (?n. P n) /\ (n = $LEAST P)``,
   RW_TAC std_ss []
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [IMP_RES_TAC IS_LEAST_def
       THEN PROVE_TAC[],
      IMP_RES_TAC IS_LEAST_EQ_IMP,
      IMP_RES_TAC IS_LEAST_LEAST
       THEN POP_ASSUM(ASSUME_TAC o CONV_RULE(DEPTH_CONV ETA_CONV))
       THEN PROVE_TAC[]]);

val LEAST_SUC =
 store_thm
  ("LEAST_SUC",
   ``!P i. ~(P 0) /\ P i ==> ((LEAST i. P i) = SUC(LEAST i. P(SUC i)))``,
   RW_TAC list_ss []
    THEN IMP_RES_TAC IS_LEAST_SUC
    THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC)
    THEN FULL_SIMP_TAC list_ss [IS_LEAST_EQ]
    THEN Cases_on `i = 0`
    THEN RW_TAC std_ss []
    THEN RES_TAC
    THEN `?j. i = SUC j` by Cooper.COOPER_TAC
    THEN RW_TAC list_ss []
    THEN `(P  o SUC) j` by RW_TAC std_ss []
    THEN CONV_TAC(RHS_CONV(REWRITE_CONV[GSYM(SIMP_CONV std_ss [] ``(P o SUC) j:bool``)]))
    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
    THEN `!n. (SUC n = $LEAST P) = (n = $LEAST (P o SUC))`  by PROVE_TAC[]
    THEN PROVE_TAC[]);

val LENGTH_PATH_FILTER_NON_ZERO_EXISTS =
 store_thm
  ("LENGTH_PATH_FILTER_NON_ZERO_EXISTS",
   ``!v. LENGTH(PATH_FILTER P v) > 0 ==> ?n. n < LENGTH v /\ P(ELEM v n)``,
   GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss
          [PATH_FILTER_def,LENGTH_def,GT,ELEM_FINITE,
           LENGTH_FILTER_NON_ZERO_EXISTS,LS]
    THENL
     [POP_ASSUM(STRIP_ASSUME_TAC                         o
                SIMP_RULE list_ss [FUN_FILTER_COUNT_def] o
                Q.SPEC `0`)
       THEN Q.EXISTS_TAC `n`
       THEN RW_TAC list_ss [ELEM_INFINITE],
      RW_TAC std_ss [ELEM_INFINITE]
       THEN FULL_SIMP_TAC list_ss []
       THEN `!n. m <= n ==> ~P (f n)` by PROVE_TAC[]
       THEN Cases_on `(LEAST i. !j. i <= j ==> ~P (f j)) = 0`
       THENL
        [ASSUM_LIST
          (fn thl => STRIP_ASSUME_TAC(SIMP_RULE list_ss [el 1 thl,GENLIST] (el 3 thl))),
         Cases_on `!j. 0 <= j ==> ~P (f j)`
          THENL
           [POP_ASSUM
             (STRIP_ASSUME_TAC o
              ONCE_REWRITE_RULE
               [SIMP_RULE std_ss []
                (GSYM(ISPEC ``\i:num. !j. i <= j ==> ~(P:'a->bool) ((f:num->'a) j)`` LEAST0))] o
              REWRITE_RULE[ZERO_LESS_EQ]),
            FULL_SIMP_TAC std_ss []
             THEN PROVE_TAC[]]]]);

val LE_LS_TRANS_X =
 store_thm
  ("LE_LS_TRANS_X",
   ``m:num <= n ==> n:num < p:xnum ==> m < p``,
   Cases_on `p`
    THEN RW_TAC arith_ss [LS,LE]);

val LEAST_TAKE_FIRST =
 store_thm
  ("LEAST_TAKE_FIRST",
   ``!l. (?n. n < LENGTH l /\ P(EL n l))
         ==>
         (EL (LEAST n. P(EL n l)) l = LAST(TAKE_FIRST P l))``,
   Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,FILTER_APPEND]
    THEN Induct_on `n`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN RES_TAC
    THEN RW_TAC list_ss []
    THENL
     [`(\n. P(EL n (h::l))) 0` by RW_TAC list_ss []
       THEN IMP_RES_TAC(GSYM LEAST0)
       THEN FULL_SIMP_TAC list_ss [],
      `(\n. P(EL n (h::l))) 0` by RW_TAC list_ss []
       THEN IMP_RES_TAC(GSYM LEAST0)
       THEN FULL_SIMP_TAC list_ss [],
      Cases_on `TAKE_FIRST P l = []`
       THEN IMP_RES_TAC TAKE_FIRST_NIL
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN RW_TAC list_ss [LAST_DEF]
       THEN IMP_RES_TAC
             (SIMP_RULE list_ss []
               (ISPECL
                 [``\n. (P :'a -> bool) (EL n ((h :'a)::(l :'a list)))``,``SUC n``]
                 LEAST_SUC))
       THEN RW_TAC list_ss []]);

Theorem HD_FILTER_LEAST:
  !P l n. n < LENGTH l /\ P(EL n l) ==>
          (HD (FILTER P l) = EL (LEAST n. P (EL n l)) l)
Proof
   RW_TAC std_ss []
    THEN IMP_RES_TAC HD_TAKE_FIRST
    THEN IMP_RES_TAC  LEAST_TAKE_FIRST
    THEN RW_TAC list_ss []
QED

val IS_LEAST_MIN =
 store_thm
  ("IS_LEAST_MIN",
   ``!P. IS_LEAST P = IS_LEAST (\n. P n /\ !m. m < n ==> ~(P m))``,
   CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
    THEN RW_TAC list_ss [IS_LEAST_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss []);

val LEAST_MIN =
 store_thm
  ("LEAST_MIN",
   ``!P n. P n ==> ((LEAST n. P n) = LEAST n. P n /\ !m. m < n ==> ~(P m))``,
   RW_TAC list_ss []
    THEN IMP_RES_TAC LEAST_EXISTS_IMP
    THEN IMP_RES_TAC IS_LEAST_LEAST
    THEN `?n. P n /\ !m. m < n ==> ~(P m)` by PROVE_TAC[]
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[IS_LEAST_MIN](el 3 thl)))
    THEN IMP_RES_TAC
          (SIMP_RULE list_ss []
            (ISPEC ``\(n :num). (P :num -> bool) n /\ !(m :num). m < n ==> ~P m``
             IS_LEAST_LEAST))
    THEN IMP_RES_TAC IS_LEAST_UNIQUE);

val HD_APPEND =
 store_thm
  ("HD_APPEND",
   ``!l1 l2. ~(l1 = []) ==> (HD(l1 <> l2) = HD l1)``,
   Induct
    THEN RW_TAC list_ss [GENLIST]);

val HD_GENLIST_APPEND =
 store_thm
  ("HD_GENLIST_APPEND",
   ``!n l. 0 < n ==> (HD(GENLIST f n <> l) = HD(GENLIST f n))``,
   RW_TAC list_ss []
    THEN Cases_on `GENLIST f n`
    THEN RW_TAC list_ss []
    THEN POP_ASSUM(ASSUME_TAC o AP_TERM ``LENGTH:'a list->num``)
    THEN FULL_SIMP_TAC list_ss [LENGTH_GENLIST]);

val TL_APPEND =
 store_thm
  ("TL_APPEND",
   ``!l1 l2. ~(l1 = []) ==> (TL(l1 <> l2) = TL l1 <> l2)``,
   Induct
    THEN RW_TAC list_ss [GENLIST]);

val EL_GENLIST =
 store_thm
  ("EL_GENLIST",
   ``!f m n. m < n ==> (EL m (GENLIST f n) = f m)``,
   GEN_TAC
    THEN Induct
    THEN Induct
    THEN RW_TAC list_ss [GENLIST,SNOC_APPEND]
    THENL
     [Cases_on `0 < n`
       THEN RW_TAC list_ss []
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [HD_GENLIST_APPEND]
       THEN `n = 0` by DECIDE_TAC
       THEN RW_TAC list_ss [GENLIST],
     FULL_SIMP_TAC list_ss []
      THEN Cases_on `GENLIST f n`
      THEN RW_TAC list_ss [TL_APPEND]
      THEN POP_ASSUM(ASSUME_TAC o AP_TERM ``LENGTH:'a list->num``)
      THEN FULL_SIMP_TAC list_ss [LENGTH_GENLIST]
      THEN Cases_on `m = LENGTH t`
      THEN RW_TAC list_ss [EL_APPEND2]
      THEN `m < LENGTH t` by DECIDE_TAC
      THEN RES_TAC
      THEN RW_TAC list_ss [EL_APPEND1]]);

val LESS_IS_LEAST_EQ =
 store_thm
  ("LESS_IS_LEAST_EQ",
   ``!P Q n. P n /\ (!m. m <= n ==> (P m = Q m))
             ==>
             !n. IS_LEAST P n = IS_LEAST Q n``,
   RW_TAC list_ss [IS_LEAST_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN RES_TAC
    THENL
     [Cases_on `n' <= n`
       THEN RES_TAC
       THEN RW_TAC list_ss []
       THEN `n < n'` by DECIDE_TAC
       THEN RES_TAC,
      Cases_on `m <= n`
       THEN RES_TAC
       THEN ZAP_TAC list_ss []
       THEN `n < n'` by DECIDE_TAC
       THEN RES_TAC,
     Cases_on `n' <= n`
       THEN RES_TAC
       THEN RW_TAC list_ss []
       THEN `n < n'` by DECIDE_TAC
       THEN `n <= n` by DECIDE_TAC
       THEN RES_TAC,
      Cases_on `m <= n`
       THEN RES_TAC
       THEN ZAP_TAC list_ss []
       THEN `n < n'` by DECIDE_TAC
       THEN `n <= n` by DECIDE_TAC
       THEN RES_TAC]);

val LESS_LEAST_EQ =
 store_thm
  ("LESS_LEAST_EQ",
   ``!P Q n. P n /\ (!m. m <= n ==> (P m = Q m))
             ==>
             ((LEAST n. P n) = (LEAST n. Q n))``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC LESS_IS_LEAST_EQ
    THEN IMP_RES_TAC IS_LEAST_LEAST
    THEN RES_TAC
    THEN IMP_RES_TAC IS_LEAST_EQ_IMP
    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC[]);

val PATH_FILTER_LEAST =
 store_thm
  ("PATH_FILTER_LEAST",
   ``!P v.
      (?n. n < LENGTH v /\ P(ELEM v n))
      ==>
      (ELEM (PATH_FILTER P v) 0 = ELEM v LEAST n. P (ELEM v n))``,
   Cases_on `v`
    THEN RW_TAC std_ss [PATH_FILTER_def]
    THEN FULL_SIMP_TAC (list_ss++resq_SS) [ELEM_FINITE,ELEM_INFINITE,FUN_FILTER_COUNT_def,LS,HD]
    THENL
     [IMP_RES_TAC HD_FILTER_LEAST,
      IMP_RES_TAC(SIMP_RULE list_ss [] (ISPEC ``(P:'a->bool) o (f:num->'a)`` LEAST_MIN))
       THEN RW_TAC std_ss [],
      `!n. m <= n ==> ~(P(f n))` by PROVE_TAC[]
       THEN Cases_on `n <  LEAST i. !j. i <= j ==> ~P (f j)`
       THENL
        [ASSUM_LIST
          (fn thl =>
            ASSUME_TAC
             (SIMP_RULE list_ss [el 1 thl,EL_GENLIST]
               (SIMP_RULE
                 list_ss [LENGTH_GENLIST]
                 (ISPECL
                   [``P :'a -> bool``,
                    ``GENLIST (f :num -> 'a) LEAST (i :num). !(j :num). i <= j ==> ~P (f j)``,
                    ``n:num``]
                   HD_FILTER_LEAST))))
          THEN RW_TAC list_ss []
          THEN `(\n. P (EL n (GENLIST f LEAST i. !j. i <= j ==> ~P (f j)))) n`
                by RW_TAC list_ss [EL_GENLIST]
          THEN IMP_RES_TAC FULL_LEAST_INTRO
          THEN `(LEAST n. P (EL n (GENLIST f LEAST i. !j. i <= j ==> ~P (f j))))
                < LEAST i. !j. i <= j ==> ~P (f j)` by DECIDE_TAC
          THEN RW_TAC list_ss [EL_GENLIST]
          THEN `!m. m <= n
                    ==>
                    ((\n. P (EL n (GENLIST f LEAST i. !j. i <= j ==> ~P (f j)))) m =
                     (\n. P(f n)) m)`
                by RW_TAC list_ss [EL_GENLIST]
          THEN POP_ASSUM(ASSUME_TAC o GSYM)
          THEN `(\n. P (f n)) n` by RW_TAC std_ss []
          THEN IMP_RES_TAC LESS_LEAST_EQ
          THEN FULL_SIMP_TAC std_ss [],
      `(LEAST i. !j. i <= j ==> ~P (f j)) <= n` by DECIDE_TAC
       THEN `(\i. !j. i <= j ==> ~P (f j)) m` by PROVE_TAC[]
       THEN IMP_RES_TAC
             (ISPEC
               ``(\(i :num). !(j :num). i <= j ==> ~(P :'a -> bool) ((f :num -> 'a) j))``
               LEAST_INTRO)
       THEN FULL_SIMP_TAC std_ss []]]);

val PATH_FILTER_LEAST_COR =
 store_thm
  ("PATH_FILTER_LEAST_COR",
   ``!P1 P2 v.
      LENGTH(PATH_FILTER P1 v) > 0
      ==>
      P2 (ELEM (PATH_FILTER P1 v) 0)
      ==>
      ?n. n < LENGTH v /\ P1(ELEM v n) /\ (!m. m < n ==> ~P1(ELEM v m)) /\ P2(ELEM v n)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC LENGTH_PATH_FILTER_NON_ZERO_EXISTS
    THEN IMP_RES_TAC
          (SIMP_RULE std_ss []
            (ISPECL[``\n:num. (P1:'a -> bool) (ELEM v n)``, ``n:num``]
                   (GEN_ALL FULL_LEAST_INTRO)))
    THEN Q.EXISTS_TAC `LEAST n. P1 (ELEM v n)`
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC LESS_LEAST
    THEN FULL_SIMP_TAC std_ss []
    THENL
     [IMP_RES_TAC FULL_LEAST_INTRO
       THEN IMP_RES_TAC LE_LS_TRANS_X,
      IMP_RES_TAC(GSYM PATH_FILTER_LEAST)
       THEN RW_TAC std_ss []]);

val PATH_TOP_FREE_ELEM =
 store_thm
  ("PATH_TOP_FREE_ELEM",
   ``!v. PATH_TOP_FREE v = !i. i < LENGTH v ==> ~(ELEM v i = TOP)``,
   GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss
          [PATH_TOP_FREE_def,TOP_FREE_EL,ELEM_EL,
           ELEM_FINITE,ELEM_INFINITE,LENGTH_def,LS]);

val PATH_BOTTOM_FREE_ELEM =
 store_thm
  ("PATH_BOTTOM_FREE_ELEM",
   ``!v. PATH_BOTTOM_FREE v = !i. i < LENGTH v ==> ~(ELEM v i = BOTTOM)``,
   GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss
          [PATH_BOTTOM_FREE_def,BOTTOM_FREE_EL,ELEM_EL,
           ELEM_FINITE,ELEM_INFINITE,LENGTH_def,LS]);

val LENGTH_PATH_FILTER_NON_ZERO =
 store_thm
  ("LENGTH_PATH_FILTER_NON_ZERO",
   ``!P n v. n < LENGTH v /\ P(ELEM v n) ==> LENGTH (PATH_FILTER P v) > 0``,
   RW_TAC list_ss []
    THEN Cases_on `v`
    THEN FULL_SIMP_TAC list_ss
          [PATH_FILTER_def,LENGTH_def,GT,ELEM_def,LS,
           RESTN_FINITE,RESTN_INFINITE,HEAD_def,HD_RESTN]
    THEN IMP_RES_TAC NON_ZERO_EXISTS_LENGTH_FILTER
    THEN Cases_on `!m. ?n. m <= n /\ P (f n)`
    THEN RW_TAC list_ss [GT,LENGTH_def]
    THEN FULL_SIMP_TAC list_ss []
    THENL
     [ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(SPEC ``XNUM m`` (el 2 thl)))
       THEN PROVE_TAC[LE],
      Cases_on `(LEAST i. !j. i <= j ==> ~P (f j)) = 0`
       THEN RW_TAC list_ss [GENLIST]
       THENL
        [`(\m. !n. m <= n ==> ~P(f n)) m'` by PROVE_TAC[]
          THEN IMP_RES_TAC LEAST_INTRO
          THEN FULL_SIMP_TAC list_ss [],
         Cases_on `n < LEAST i. !j. i <= j ==> ~P (f j)`
          THENL
           [`n < LENGTH(GENLIST f LEAST i. !j. i <= j ==> ~P (f j))`
             by RW_TAC list_ss [LENGTH_GENLIST]
             THEN `P(EL n (GENLIST f LEAST i. !j. i <= j ==> ~P (f j)))`
                   by RW_TAC list_ss [EL_GENLIST]
             THEN IMP_RES_TAC NON_ZERO_EXISTS_LENGTH_FILTER,
            `(LEAST i. !j. i <= j ==> ~P (f j)) <= n` by DECIDE_TAC
             THEN `(\m. !n. m <= n ==> ~P(f n)) m'` by PROVE_TAC[]
             THEN IMP_RES_TAC LEAST_INTRO
             THEN FULL_SIMP_TAC list_ss []]]]);

(*
val ELEM_LEAST =
 store_thm
  ("ELEM_LEAST",
   ``!P v j. j < LENGTH v /\ P(ELEM v j) ==> P(ELEM v LEAST n. P(ELEM v n))``,
   REPEAT GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss [ELEM_FINITE,ELEM_INFINITE,LENGTH_def,LS]
    THENL
     [`(\n. P(EL n l)) j` by PROVE_TAC[]
       THEN IMP_RES_TAC FULL_LEAST_INTRO
       THEN FULL_SIMP_TAC list_ss [],
      `(\n. P(f n)) j` by PROVE_TAC[]
       THEN IMP_RES_TAC FULL_LEAST_INTRO
       THEN FULL_SIMP_TAC list_ss []]);
*)

val ELEM_LEAST =
 store_thm
  ("ELEM_LEAST",
   ``!P1 P2 v j.
      j < LENGTH v /\ P1(ELEM v j) /\ P2(ELEM v j) /\ (!i. i < j ==> ~(P2(ELEM v i)))
      ==> P1(ELEM v LEAST n. P2(ELEM v n))``,
   REPEAT GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss [ELEM_FINITE,ELEM_INFINITE,LENGTH_def,LS]
    THENL
     [`(\n. P2(EL n l)) j` by PROVE_TAC[]
       THEN IMP_RES_TAC FULL_LEAST_INTRO
       THEN FULL_SIMP_TAC list_ss []
       THEN Cases_on `j = LEAST n. P2 (EL n l)`
       THEN RW_TAC list_ss []
       THEN `(LEAST n. P2 (EL n l)) < j` by DECIDE_TAC
       THEN RES_TAC,
      `(\n. P2(f n)) j` by PROVE_TAC[]
       THEN IMP_RES_TAC FULL_LEAST_INTRO
       THEN FULL_SIMP_TAC list_ss []
       THEN Cases_on `j = LEAST n. P2 (f n)`
       THEN RW_TAC list_ss []
       THEN `(LEAST n. P2 (f n)) < j` by DECIDE_TAC
       THEN RES_TAC]);

val CLOCK_NOT_LEMMA =
 store_thm
  ("CLOCK_NOT_LEMMA",
   ``PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v
     ==>
     !i. i < LENGTH v ==> (CLOCK (B_NOT c) (ELEM v i) =  ~(CLOCK c (ELEM v i)))``,
   RW_TAC list_ss []
    THEN Cases_on `(ELEM v i)`
    THEN RW_TAC list_ss [CLOCK_def,B_SEM_def]
    THEN IMP_RES_TAC PATH_TOP_FREE_ELEM
    THEN IMP_RES_TAC PATH_BOTTOM_FREE_ELEM);

val CLOCK_NOT_LEMMA_COR =
 prove
  (``!j:num.
      PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v /\ j < LENGTH v
      ==>
      ((!i:num. i < j ==> ~(CLOCK c (ELEM v i)))
       =
      (!i:num. i < j ==> CLOCK (B_NOT c) (ELEM v i))) ``,
   RW_TAC list_ss []
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN RES_TAC
    THEN IMP_RES_TAC LS_TRANS_X
    THEN PROVE_TAC[CLOCK_NOT_LEMMA]);

val F_PROJ_F_STRONG_BOOL =
 store_thm
  ("F_PROJ_F_STRONG_BOOL",
   ``!b. F_CLOCK_FREE (F_STRONG_BOOL b) ==>
         !v. PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
             !c. UF_SEM (PROJ v c) (F_STRONG_BOOL b) =
                 F_SEM v c (F_STRONG_BOOL b)``,
   RW_TAC (list_ss++resq_SS) [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [IMP_RES_TAC
       (ISPECL[``CLOCK(c :'a bexp)``,``CLOCK(b :'a bexp)``]PATH_FILTER_LEAST_COR)
       THEN Q.EXISTS_TAC `n`
       THEN RW_TAC (list_ss++resq_SS) [CLOCK_TICK_def,LENGTH_SEL]
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [CLOCK_def,ELEM_EL,EL_SEL0,B_SEM_def]
       THEN Cases_on `(ELEM v i)`
       THEN RW_TAC std_ss [B_SEM_def]
       THEN IMP_RES_TAC LS_TRANS_X
       THEN IMP_RES_TAC PATH_BOTTOM_FREE_ELEM,
      FULL_SIMP_TAC (list_ss++resq_SS) [CLOCK_TICK_def,LENGTH_SEL,ELEM_EL,EL_SEL0]
       THEN FULL_SIMP_TAC list_ss [GSYM CLOCK_def]
       THEN IMP_RES_TAC LENGTH_PATH_FILTER_NON_ZERO,
      FULL_SIMP_TAC (list_ss++resq_SS) [CLOCK_TICK_def,LENGTH_SEL,ELEM_EL,EL_SEL0]
       THEN FULL_SIMP_TAC list_ss [GSYM CLOCK_def]
       THEN IMP_RES_TAC PATH_FILTER_LEAST
       THEN RW_TAC std_ss []
       THEN IMP_RES_TAC CLOCK_NOT_LEMMA_COR
       THEN IMP_RES_TAC(ISPECL[``CLOCK (b :'a bexp)``,``CLOCK (c :'a bexp)``]ELEM_LEAST)]);

val NEUTRAL_COMPLEMENT =
 store_thm
  ("NEUTRAL_COMPLEMENT",
   ``!v. PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==> (COMPLEMENT v = v)``,
   GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss [PATH_TOP_FREE_def,PATH_BOTTOM_FREE_def,COMPLEMENT_def]
    THENL
     [Induct_on `l`
       THEN RW_TAC list_ss []
       THEN Cases_on `h`
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_def,BOTTOM_FREE_def,COMPLEMENT_LETTER_def],
      CONV_TAC FUN_EQ_CONV
       THEN Induct
       THEN RW_TAC list_ss []
       THENL
        [Cases_on `f 0`
          THEN FULL_SIMP_TAC list_ss [COMPLEMENT_LETTER_def]
          THEN RES_TAC,
         Cases_on `f(SUC n)`
          THEN FULL_SIMP_TAC list_ss [COMPLEMENT_LETTER_def]
          THEN RES_TAC]]);

val NOT_XNUM_0 =
 store_thm
  ("NOT_XNUM_0",
   ``!v. ~(v = XNUM 0) = v > 0``,
   GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss [xnum_11,GT]);

val F_PROJ_F_WEAK_BOOL =
 store_thm
  ("F_PROJ_F_WEAK_BOOL",
   ``!b. F_CLOCK_FREE (F_WEAK_BOOL b) ==>
         !v. PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
             !c. UF_SEM (PROJ v c) (F_WEAK_BOOL b) =
                 F_SEM v c (F_WEAK_BOOL b)``,
   RW_TAC (list_ss++resq_SS) [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Cases_on `PATH_FILTER (CLOCK c) v`
       THEN FULL_SIMP_TAC (list_ss++resq_SS)
             [LENGTH_def,xnum_11,xnum_distinct,LENGTH_NIL,CLOCK_TICK_def,LENGTH_SEL,
              ELEM_EL,EL_SEL0]
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC std_ss [GSYM CLOCK_def,ELEM_COMPLEMENT]
       THEN POP_ASSUM(ASSUME_TAC o Q.AP_TERM `LENGTH`)
       THEN FULL_SIMP_TAC list_ss [LENGTH_def]
       THEN Cases_on `LENGTH (PATH_FILTER (CLOCK c) v) > 0`
       THENL
        [`XNUM 0 > 0` by PROVE_TAC[]
          THEN FULL_SIMP_TAC list_ss [GT],
         `~(?n. n < LENGTH v /\ CLOCK c (ELEM v n))` by PROVE_TAC[LENGTH_PATH_FILTER_NON_ZERO]
          THEN FULL_SIMP_TAC list_ss []
          THEN `!n. n < LENGTH v ==> ~CLOCK c (ELEM v n)` by PROVE_TAC[]
          THEN RES_TAC
          THEN Cases_on `(ELEM v j)`
          THEN IMP_RES_TAC PATH_TOP_FREE_ELEM
          THEN IMP_RES_TAC PATH_BOTTOM_FREE_ELEM
          THEN IMP_RES_TAC ELEM_COMPLEMENT
          THEN PROVE_TAC[COMPLEMENT_LETTER_def]],
      IMP_RES_TAC NEUTRAL_COMPLEMENT
       THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
       THEN FULL_SIMP_TAC (list_ss++resq_SS)
             [GSYM CLOCK_def,CLOCK_TICK_def,LENGTH_SEL,ELEM_EL,EL_SEL0]
       THEN IMP_RES_TAC PATH_FILTER_LEAST
       THEN `CLOCK b (ELEM v LEAST n. CLOCK c (ELEM v n))` by PROVE_TAC[]
       THEN IMP_RES_TAC CLOCK_NOT_LEMMA_COR
       THEN `IS_LEAST (\j. CLOCK c (ELEM v j)) j`
             by RW_TAC list_ss
                 [SIMP_RULE list_ss []
                   (ISPECL[``(\j. CLOCK c (ELEM v j))``,``j:num``]IS_LEAST_def)]
       THEN IMP_RES_TAC IS_LEAST_EQ_IMP
       THEN RW_TAC list_ss [],
      Cases_on `LENGTH (PATH_FILTER (CLOCK c) v) = XNUM 0`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [NOT_XNUM_0]
       THEN IMP_RES_TAC LENGTH_PATH_FILTER_NON_ZERO_EXISTS
       THEN IMP_RES_TAC PATH_FILTER_LEAST
       THEN RW_TAC list_ss []
       THEN IMP_RES_TAC NEUTRAL_COMPLEMENT
       THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
       THEN IMP_RES_TAC
             (SIMP_RULE list_ss []
               (ISPEC ``(\n. CLOCK c (ELEM v n))``(GEN_ALL FULL_LEAST_INTRO)))
       THEN IMP_RES_TAC LE_LS_TRANS_X
       THEN FULL_SIMP_TAC (list_ss++resq_SS)
             [GSYM CLOCK_def,CLOCK_TICK_def,LENGTH_SEL,ELEM_EL,EL_SEL0]
       THEN ASSUM_LIST
             (fn thl =>
               ASSUME_TAC
                (SIMP_RULE list_ss [el 1 thl,el 3 thl]
                  (Q.SPEC `LEAST n. CLOCK c (ELEM v n)` (el 8 thl))))
       THEN `(!i. i < (LEAST n. CLOCK c (ELEM v n)) ==> CLOCK (B_NOT c) (ELEM v i))
             =
             (!i. i < (LEAST n. CLOCK c (ELEM v n)) ==> ~(CLOCK c (ELEM v i)))`
             by PROVE_TAC[CLOCK_NOT_LEMMA_COR]
        THEN POP_ASSUM(fn th => FULL_SIMP_TAC list_ss [th])
        THEN FULL_SIMP_TAC list_ss
              [SIMP_RULE std_ss [] (ISPEC ``\n. CLOCK c (ELEM v n)`` LESS_LEAST)]]);

val COMPLEMENT_LETTER_FILTER =
 store_thm
  ("COMPLEMENT_LETTER_FILTER",
   ``!f. (COMPLEMENT_LETTER o f = f)
         ==>
         !n. MAP COMPLEMENT_LETTER (FILTER P (GENLIST f n)) = FILTER P (GENLIST f n)``,
   RW_TAC list_ss []
    THEN Induct_on `n`
    THEN RW_TAC list_ss [GENLIST,FILTER,SNOC_APPEND,FILTER_APPEND]
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(CONV_RULE FUN_EQ_CONV (el 3 thl)))
    THEN FULL_SIMP_TAC list_ss []);

val COMPLEMENT_PATH_FILTER =
 store_thm
  ("COMPLEMENT_PATH_FILTER",
   ``!v. (COMPLEMENT v = v)
         ==>
         (COMPLEMENT(PATH_FILTER P v) = PATH_FILTER P v)``,
   GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss
          [PATH_TOP_FREE_def,PATH_BOTTOM_FREE_def,COMPLEMENT_def,PATH_FILTER_def]
    THENL
     [Induct_on `l`
       THEN RW_TAC list_ss [PATH_FILTER_def,COMPLEMENT_def]
       THEN Cases_on `h`
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_def,BOTTOM_FREE_def,COMPLEMENT_LETTER_def],
      ASM_REWRITE_TAC [GSYM(SIMP_CONV std_ss [] ``(f o g) o h``)],
      IMP_RES_TAC COMPLEMENT_LETTER_FILTER
       THEN RW_TAC list_ss []]);

val F_PROJ_F_NOT_BOOL =
 store_thm
  ("F_PROJ_F_NOT_BOOL",
   ``(F_CLOCK_FREE f ==>
      !v. PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
          !c. UF_SEM (PROJ v c) f = F_SEM v c f)
     ==>
     F_CLOCK_FREE (F_NOT f) ==>
     !v. PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
         !c. UF_SEM (PROJ v c) (F_NOT f) = F_SEM v c (F_NOT f)``,
   RW_TAC (list_ss++resq_SS) [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def]
    THEN RES_TAC
    THEN IMP_RES_TAC NEUTRAL_COMPLEMENT
    THEN RW_TAC std_ss [COMPLEMENT_PATH_FILTER]);

val F_PROJ_F_NOT_BOOL_FINITE =
 store_thm
  ("F_PROJ_F_NOT_BOOL_FINITE",
   ``(F_CLOCK_FREE f ==>
      !l.
        PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
        !c. UF_SEM (PROJ (FINITE l) c) f = F_SEM (FINITE l) c f) ==>
     F_CLOCK_FREE (F_NOT f) ==>
     !l.
       PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
       !c.
         UF_SEM (PROJ (FINITE l) c) (F_NOT f) =
         F_SEM (FINITE l) c (F_NOT f)``,
   RW_TAC (list_ss++resq_SS) [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def]
    THEN RES_TAC
    THEN IMP_RES_TAC NEUTRAL_COMPLEMENT
    THEN RW_TAC std_ss [COMPLEMENT_PATH_FILTER]);

val F_PROJ_F_AND_BOOL =
 store_thm
  ("F_PROJ_F_AND_BOOL",
   ``(F_CLOCK_FREE f ==>
          !v.
            PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
            !c. UF_SEM (PROJ v c) f = F_SEM v c f)
     /\
     (F_CLOCK_FREE f' ==>
          !v.
            PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
            !c. UF_SEM (PROJ v c) f' = F_SEM v c f')
     ==>
     F_CLOCK_FREE (F_AND (f,f')) ==>
     !v.
      PATH_TOP_FREE v /\ PATH_BOTTOM_FREE v ==>
      !c. UF_SEM (PROJ v c) (F_AND (f,f')) = F_SEM v c (F_AND (f,f'))``,
   RW_TAC (list_ss++resq_SS) [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def]);

val F_PROJ_F_AND_BOOL_FINITE =
 store_thm
  ("F_PROJ_F_AND_BOOL_FINITE",
   ``(F_CLOCK_FREE f ==>
       !l.
        PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
        !c. UF_SEM (PROJ (FINITE l) c) f = F_SEM (FINITE l) c f) /\
     (F_CLOCK_FREE f' ==>
      !l.
        PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
        !c. UF_SEM (PROJ (FINITE l) c) f' = F_SEM (FINITE l) c f') ==>
     F_CLOCK_FREE (F_AND (f,f')) ==>
     !l.
       PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
       !c.
         UF_SEM (PROJ (FINITE l) c) (F_AND (f,f')) =
         F_SEM (FINITE l) c (F_AND (f,f'))``,
   RW_TAC (list_ss++resq_SS) [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def]);

val PATH_TOP_FREE_SEL =
 store_thm
  ("PATH_TOP_FREE_SEL",
   ``!v. PATH_TOP_FREE v ==> !j. j < LENGTH v ==> TOP_FREE (SEL v (0,j))``,
   Induct
    THEN RW_TAC list_ss
          [PATH_TOP_FREE_def,TOP_FREE_EL,LENGTH_SEL,LENGTH_def,LS,EL_SEL0,
           ELEM_FINITE,ELEM_INFINITE]);

val PATH_BOTTOM_FREE_SEL =
 store_thm
  ("PATH_BOTTOM_FREE_SEL",
   ``!v. PATH_BOTTOM_FREE v ==> !j. j < LENGTH v ==> BOTTOM_FREE (SEL v (0,j))``,
   Induct
    THEN RW_TAC list_ss
          [PATH_BOTTOM_FREE_def,BOTTOM_FREE_EL,LENGTH_SEL,LENGTH_def,LS,EL_SEL0,
           ELEM_FINITE,ELEM_INFINITE]);

val LENGTH_FILTER =
 store_thm
  ("LENGTH_FILTER",
   ``!l. LENGTH(FILTER P l) <= LENGTH l``,
   Induct
    THEN RW_TAC list_ss []);

val LENGTH_PATH_FILTER =
 store_thm
  ("LENGTH_PATH_FILTER",
   ``!v. LENGTH(PATH_FILTER P v) <= LENGTH v``,
   Induct
    THEN RW_TAC list_ss [LENGTH_FILTER,PATH_FILTER_def,LENGTH_def,LE]);

val LS_LE_TRANS_X =
 store_thm
  ("LS_LE_TRANS_X",
   ``m:num < n:xnum ==> n <= p:xnum ==> m < p``,
   Cases_on `n` THEN Cases_on `p`
    THEN RW_TAC arith_ss [LS,LE]);

val PATH_TAKE_FIRST_def =
 Define
  `(PATH_TAKE_FIRST P (FINITE l) = TAKE_FIRST P l)
   /\
   (PATH_TAKE_FIRST P (INFINITE f) = GENLIST f (SUC(LEAST n. P(f n))))`;

val PATH_TAKE_FIRSTN_def =
 Define
  `(PATH_TAKE_FIRSTN P n (FINITE l) = TAKE_FIRSTN P n l)
   /\
   (PATH_TAKE_FIRSTN P 0 (INFINITE f) = [])
   /\
   (PATH_TAKE_FIRSTN P (SUC n) (INFINITE f) =
     PATH_TAKE_FIRST P (INFINITE f)
     <>
     PATH_TAKE_FIRSTN P n
      (INFINITE(\n. f(n + LENGTH(PATH_TAKE_FIRST P (INFINITE f))))))`;

val TAKE_FIRSTN_1 =
 store_thm
  ("TAKE_FIRSTN_1",
   ``!P l. TAKE_FIRSTN P 1 l = TAKE_FIRST P l``,
   PROVE_TAC[ONE,TAKE_FIRSTN_def,APPEND_NIL]);

val SEL_REC_FINITE =
 store_thm
  ("SEL_REC_FINITE",
   ``!m n l. SEL_REC m n (FINITE l) = SEL_REC m n l``,
   Induct THEN Induct THEN Induct
    THEN RW_TAC list_ss
          [HEAD_def,REST_def,SEL_def,SEL_REC_def,
           FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
           FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]);

val SEL_FINITE =
 store_thm
  ("SEL_FINITE",
   ``!l m n. SEL (FINITE l) (m,n) = SEL l (m,n)``,
   RW_TAC list_ss
    [SEL_def,FinitePSLPathTheory.SEL_def,SEL_REC_FINITE]);

val LENGTH_TAKE_FIRST_NON_EMPTY =
 store_thm
  ("LENGTH_TAKE_FIRST_NON_EMPTY",
   ``!P l. LENGTH l > 0 ==> LENGTH(TAKE_FIRST P l) > 0``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def]);

val FILTER_TAKE_FIRST =
 store_thm
  ("FILTER_TAKE_FIRST",
   ``!l. (?n. n < LENGTH l /\ P (EL n l))
         ==> (FILTER P (TAKE_FIRST P l) = [HD (FILTER P l)])``,
   Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,FILTER_APPEND]
    THEN Cases_on `n`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN RES_TAC
    THEN RW_TAC list_ss []);

val TAKE_FIRSTN_NIL =
 store_thm
  ("TAKE_FIRSTN_NIL",
   ``!P n. TAKE_FIRSTN P n [] = []``,
   Induct_on `n`
    THEN RW_TAC list_ss [TAKE_FIRSTN_def,TAKE_FIRST_def,BUTFIRSTN]);

val LENGTH_TAKE_FIRST_TAKE_FIRSTN =
 store_thm
  ("LENGTH_TAKE_FIRST_TAKE_FIRSTN",
   ``LENGTH (TAKE_FIRST P l) <= LENGTH (TAKE_FIRSTN P (SUC n) l)``,
   RW_TAC list_ss [GSYM TAKE_FIRSTN_1,LENGTH_TAKE_FIRST_MONO]);

val LENGTH_TAKE_FIRSTN_LEMMA =
 prove
  (``LENGTH (TAKE_FIRST P l)
      +
      LENGTH(TAKE_FIRSTN P (SUC n) (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)) =
     LENGTH(TAKE_FIRSTN P (SUC(SUC n)) l)``,
   RW_TAC std_ss [GSYM LENGTH_APPEND,GSYM TAKE_FIRSTN_def]);

val SEL_TAKE_FIRST =
 store_thm
  ("SEL_TAKE_FIRST",
   ``LENGTH l > 0 ==> (SEL l (0, LENGTH(TAKE_FIRST P l)-1) = TAKE_FIRST P l)``,
   RW_TAC std_ss []
    THEN `LENGTH (TAKE_FIRST P l) > 0` by PROVE_TAC[LENGTH_TAKE_FIRST_NON_EMPTY]
    THEN CONV_TAC(LHS_CONV(RATOR_CONV(ONCE_REWRITE_CONV[GSYM TAKE_FIRST_APPEND])))
    THEN RW_TAC list_ss [SEL_APPEND1,SEL_RESTN_EQ0]);

val SEL_BUTFIRSTN =
 store_thm
  ("SEL_BUTFIRSTN",
    ``!l m n.
       LENGTH l > m+n /\ n > 0
       ==>
       (SEL l (0, m+n)  = SEL l (0,m) <> SEL (BUTFIRSTN (SUC m) l) (0,n-1))``,
    SIMP_TAC list_ss [FinitePSLPathTheory.SEL_def]
     THEN Induct_on `m`
     THEN RW_TAC list_ss [FinitePSLPathTheory.SEL_REC_def,ADD_CLAUSES,FinitePSLPathTheory.REST_def]
     THEN `BUTFIRSTN (SUC m) l = BUTFIRSTN m (TL l)`
           by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``n>(p:num) ==> ~(n=0)``,CONS,BUTFIRSTN]
     THEN RW_TAC list_ss []
     THENL
      [`(HD l::TL l) = l`
        by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``n>(p:num) ==> ~(n=0)``,CONS]
        THEN ONCE_REWRITE_TAC[ONE,GSYM ADD1]
        THEN `BUTFIRSTN (SUC 0) l = TL l` by PROVE_TAC[BUTFIRSTN]
        THEN ASM_REWRITE_TAC
               [FinitePSLPathTheory.SEL_REC_def,FinitePSLPathTheory.HEAD_def,
                FinitePSLPathTheory.REST_def,APPEND,TWO,ADD_CLAUSES,CONS_11],
       Cases_on `m = 0`
        THEN RW_TAC list_ss [BUTFIRSTN]
        THEN ONCE_REWRITE_TAC[ONE,GSYM ADD1]
        THEN REWRITE_TAC
               [FinitePSLPathTheory.SEL_REC_def,FinitePSLPathTheory.HEAD_def,
                FinitePSLPathTheory.REST_def,APPEND,TWO,ADD_CLAUSES]
        THEN FULL_SIMP_TAC list_ss []
        THENL
         [`LENGTH l > SUC(SUC 0)` by DECIDE_TAC
            THEN `(HD l::TL l) = l`
                  by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``n>(p:num) ==> ~(n=0)``,CONS]
            THEN `0 < LENGTH l` by DECIDE_TAC
            THEN `LENGTH (TL l) = LENGTH l - 1` by PROVE_TAC[LENGTH_TL]
            THEN `LENGTH (TL l) > 0` by DECIDE_TAC
            THEN ONCE_REWRITE_TAC[TWO]
            THEN ONCE_REWRITE_TAC[ONE]
            THEN `(HD(TL l)::TL(TL l)) = TL l`
                  by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``n>(p:num) ==> ~(n=0)``,CONS]
            THEN `BUTFIRSTN (SUC(SUC 0)) l = TL(TL l)` by PROVE_TAC[BUTFIRSTN]
            THEN RW_TAC list_ss [],
          `0 < LENGTH l` by DECIDE_TAC
            THEN `LENGTH (TL l) = LENGTH l - 1` by PROVE_TAC[LENGTH_TL]
            THEN `LENGTH (TL l) > m + n` by DECIDE_TAC
            THEN RES_TAC
            THEN FULL_SIMP_TAC std_ss [DECIDE``m + (n + 1) = SUC(m + n)``,GSYM ADD1]
            THEN `LENGTH (TL l) > 0` by DECIDE_TAC
            THEN `(HD(TL l)::TL(TL l)) = TL l`
                  by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``n>(p:num) ==> ~(n=0)``,CONS]
            THEN FULL_SIMP_TAC std_ss
                  [FinitePSLPathTheory.SEL_REC_def,FinitePSLPathTheory.HEAD_def,
                   FinitePSLPathTheory.REST_def]
            THEN `HD (TL l)::SEL_REC (m + n) 0 (TL (TL l)) =
                  (HD (TL l)::SEL_REC m 0 (TL (TL l))) <>
                  SEL_REC n 0 (BUTFIRSTN m (TL(TL l)))`
                  by PROVE_TAC[BUTFIRSTN]
            THEN FULL_SIMP_TAC std_ss [APPEND,CONS_11]
            THEN `(HD l::TL l) = l`
                  by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``n>(p:num) ==> ~(n=0)``,CONS]
            THEN PROVE_TAC[BUTFIRSTN]]]);

Theorem SEL_TAKE_FIRSTN:
  !P n l.
    LENGTH l > 0 ==>
    (SEL l (0, LENGTH(TAKE_FIRSTN P (SUC n) l)-1) = TAKE_FIRSTN P (SUC n) l)
Proof
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [REWRITE_RULE[ONE]TAKE_FIRSTN_1,SEL_TAKE_FIRST]
    THEN ONCE_REWRITE_TAC[TAKE_FIRSTN_def]
    THEN RW_TAC list_ss []
    THEN `LENGTH (TAKE_FIRST P l) > 0` by PROVE_TAC[LENGTH_TAKE_FIRST_NON_EMPTY]
    THEN Cases_on `BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l = []`
    THEN RW_TAC list_ss [TAKE_FIRSTN_NIL,SEL_TAKE_FIRST]
    THEN `~(LENGTH(BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)=0)`
      by PROVE_TAC[LENGTH_NIL]
    THEN `LENGTH(BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l) > 0` by DECIDE_TAC
    THEN `LENGTH(TAKE_FIRST P (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)) > 0`
          by PROVE_TAC[LENGTH_TAKE_FIRST_NON_EMPTY]
    THEN `LENGTH(TAKE_FIRSTN P (SUC n)
                             (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)) > 0`
          by PROVE_TAC
              [LENGTH_TAKE_FIRST_TAKE_FIRSTN,
               DECIDE``m:num > 0 /\ m <= n:num ==> n > 0``]
    THEN `LENGTH(TAKE_FIRSTN P (SUC(SUC n)) l) > 0`
          by PROVE_TAC
              [LENGTH_TAKE_FIRST_TAKE_FIRSTN,LENGTH_TAKE_FIRST_SUC,
               DECIDE``m:num > 0 /\ m <= n:num /\ n <= p:num ==> p > 0``]
    THEN `LENGTH(TAKE_FIRSTN P (SUC(SUC n)) l) <= LENGTH l`
      by PROVE_TAC[LENGTH_TAKE_FIRSTN]
    THEN `LENGTH l > LENGTH(TAKE_FIRSTN P (SUC(SUC n)) l) - 1` by DECIDE_TAC
    THEN `LENGTH l > LENGTH (TAKE_FIRST P l)
                     +
                     LENGTH(TAKE_FIRSTN P (SUC n)
                                   (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)) - 1`
          by PROVE_TAC[LENGTH_TAKE_FIRSTN_LEMMA]
    THEN `LENGTH l > (LENGTH (TAKE_FIRST P l) - 1)
                     +
                     LENGTH(TAKE_FIRSTN P (SUC n)
                                   (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l))`
          by DECIDE_TAC
    THEN RW_TAC std_ss [DECIDE ``m > 0 ==> (m + n - 1 = (m - 1) + n)``]
    THEN RW_TAC list_ss [SEL_BUTFIRSTN,SEL_TAKE_FIRST]
    THEN `SEL (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)
              (0,LENGTH (TAKE_FIRSTN P (SUC n)
                               (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)) - 1) =
         TAKE_FIRSTN P (SUC n) (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l)`
      by PROVE_TAC[]
    THEN `SUC(LENGTH (TAKE_FIRST P l) - 1) = LENGTH(TAKE_FIRST P l)`
      by DECIDE_TAC
    THEN RW_TAC list_ss []
QED

val FIRSTN_SEL =
 store_thm
  ("FIRSTN_SEL",
   ``!n l. n < LENGTH l ==> (FIRSTN (SUC n) l = SEL l (0,n))``,
   Induct
    THEN RW_TAC list_ss
           [FIRSTN,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
            FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def,ADD_CLAUSES]
    THEN REWRITE_TAC
          [ONE,GSYM ADD1,FIRSTN,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
           FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def,ADD_CLAUSES]
    THEN `(HD l::TL l) = l` by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``p:num<n ==> ~(n=0)``,CONS]
    THEN ZAP_TAC list_ss [FIRSTN,ONE]
    THEN `0 < LENGTH l` by DECIDE_TAC
    THEN IMP_RES_TAC LENGTH_TL
    THEN `0 < LENGTH(TL l)` by DECIDE_TAC
    THEN `(HD(TL l)::TL(TL l)) = TL l` by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``p:num<n ==> ~(n=0)``,CONS]
    THEN ASSUM_LIST(fn thl => ONCE_REWRITE_TAC[GSYM(el 5 thl)])
    THEN ASSUM_LIST(fn thl => ONCE_REWRITE_TAC[GSYM(el 1 thl)])
    THEN REWRITE_TAC
          [FIRSTN,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
           FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]
    THEN RW_TAC list_ss []
    THEN `n < LENGTH(TL l)` by DECIDE_TAC
    THEN FULL_SIMP_TAC list_ss
          [FIRSTN,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
           FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]
    THEN `FIRSTN (SUC n) (HD (TL l)::TL (TL l)) = SEL_REC (SUC n) 0 (HD (TL l)::TL (TL l))`
          by PROVE_TAC[ADD1]
    THEN FULL_SIMP_TAC list_ss
          [FIRSTN,ADD1,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
           FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]);

val FILTER_SEL =
 store_thm
  ("FILTER_SEL",
   ``!P n l.
      n < LENGTH (FILTER P l)
      ==>
      (FILTER P (SEL l (0,LENGTH (TAKE_FIRSTN P (SUC n) l) - 1)) =
       SEL (FILTER P l) (0,n))``,
   RW_TAC list_ss []
    THEN `LENGTH (FILTER P l) > 0` by DECIDE_TAC
    THEN IMP_RES_TAC LENGTH_FILTER_NON_EMPTY
    THEN RW_TAC list_ss [SEL_TAKE_FIRSTN, GSYM FIRSTN_FILTER_TAKE_FIRSTN]
    THEN `LENGTH (FILTER P l) <= LENGTH l` by PROVE_TAC[LENGTH_FILTER]
    THEN `n < LENGTH l` by DECIDE_TAC
    THEN RW_TAC list_ss [FIRSTN_SEL]);

val FILTER_SEL_PATH_FILTER_FINITE =
 store_thm
  ("FILTER_SEL_PATH_FILTER_FINITE",
   ``!P n l.
      n < LENGTH (PATH_FILTER P (FINITE l))
      ==>
      (FILTER P (SEL (FINITE l) (0, LENGTH (PATH_TAKE_FIRSTN P (SUC n) (FINITE l)) - 1))
       =
       SEL (PATH_FILTER P (FINITE l)) (0, n))``,
   REPEAT GEN_TAC
    THEN RW_TAC list_ss
          [PATH_FILTER_def,LENGTH_def,SEL_FINITE,LS,FILTER_SEL,PATH_TAKE_FIRSTN_def]);


(*
val FILTER_SEL_PATH_FILTER =
 store_thm
  ("FILTER_SEL_PATH_FILTER",
   ``!P n v.
      n < LENGTH (PATH_FILTER P v)
      ==>
      (FILTER P (SEL v (0, LENGTH (PATH_TAKE_FIRSTN P (SUC n) v) - 1))
       =
       SEL (PATH_FILTER P v) (0, n))``,
   GEN_TAC THEN GEN_TAC
    THEN Cases
    THEN RW_TAC list_ss [FILTER_SEL_PATH_FILTER_FINITE]
    THEN RW_TAC list_ss [PATH_FILTER_def]
    THEN FULL_SIMP_TAC list_ss []
*)

val TOP_FREE_CONS =
 store_thm
  ("TOP_FREE_CONS",
   ``!x l. TOP_FREE(x::l) = TOP_FREE[x] /\ TOP_FREE l``,
   GEN_TAC
    THEN Induct_on `l`
    THEN Cases_on `x`
    THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]);

val BOTTOM_FREE_CONS =
 store_thm
  ("BOTTOM_FREE_CONS",
   ``!x l. BOTTOM_FREE(x::l) = BOTTOM_FREE[x] /\ BOTTOM_FREE l``,
   GEN_TAC
    THEN Induct_on `l`
    THEN Cases_on `x`
    THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]);

(*****************************************************************************)
(* Proofs of TOP_FREE_SEL and BOTTOM_FREE_SEL that follow can probably be    *)
(* simplified.                                                               *)
(*****************************************************************************)
val TOP_FREE_SEL =
 store_thm
  ("TOP_FREE_SEL",
   ``!l n. TOP_FREE l /\ n < LENGTH l ==> TOP_FREE(SEL l (0,n))``,
   SIMP_TAC list_ss
    [GSYM ADD1,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
     FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]
    THEN Induct_on `n`
    THEN RW_TAC std_ss [FinitePSLPathTheory.SEL_REC_def]
    THEN `(HD l::TL l) = l` by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``p:num<n ==> ~(n=0)``,CONS]
    THEN Cases_on `HD l`
    THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]
    THENL
     [PROVE_TAC[TOP_FREE_CONS,TOP_FREE_def],
      PROVE_TAC[TOP_FREE_CONS,TOP_FREE_def],
      `0 < LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LENGTH_TL
       THEN `n < LENGTH(TL l)` by DECIDE_TAC
       THEN `TOP_FREE(TL l)` by PROVE_TAC[TOP_FREE_CONS]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN `TOP_FREE (HD l::SEL_REC n 0 (TL l))` by PROVE_TAC[]
       THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def],
      `0 < LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LENGTH_TL
       THEN `n < LENGTH(TL l)` by DECIDE_TAC
       THEN `TOP_FREE(TL l)` by PROVE_TAC[TOP_FREE_CONS]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN `TOP_FREE (HD l::SEL_REC n 0 (TL l))` by PROVE_TAC[]
       THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]]);

val BOTTOM_FREE_SEL =
 store_thm
  ("BOTTOM_FREE_SEL",
   ``!l n. BOTTOM_FREE l /\ n < LENGTH l ==> BOTTOM_FREE(SEL l (0,n))``,
   SIMP_TAC list_ss
    [GSYM ADD1,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
     FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]
    THEN Induct_on `n`
    THEN RW_TAC std_ss [FinitePSLPathTheory.SEL_REC_def]
    THEN `(HD l::TL l) = l` by PROVE_TAC[NULL_EQ_NIL,LENGTH_NIL,DECIDE``p:num<n ==> ~(n=0)``,CONS]
    THEN Cases_on `HD l`
    THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]
    THENL
     [PROVE_TAC[BOTTOM_FREE_CONS,BOTTOM_FREE_def],
      `0 < LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LENGTH_TL
       THEN `n < LENGTH(TL l)` by DECIDE_TAC
       THEN `BOTTOM_FREE(TL l)` by PROVE_TAC[BOTTOM_FREE_CONS]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN `BOTTOM_FREE (HD l::SEL_REC n 0 (TL l))` by PROVE_TAC[]
       THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def],
      PROVE_TAC[BOTTOM_FREE_CONS,BOTTOM_FREE_def],
      `0 < LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LENGTH_TL
       THEN `n < LENGTH(TL l)` by DECIDE_TAC
       THEN `BOTTOM_FREE(TL l)` by PROVE_TAC[BOTTOM_FREE_CONS]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN `BOTTOM_FREE (HD l::SEL_REC n 0 (TL l))` by PROVE_TAC[]
       THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]]);

(*****************************************************************************)
(* |- !p. EL n (SEL p (0,n)) = EL n p                                        *)
(*****************************************************************************)
val EL_SEL0_LEMMA =
 SIMP_RULE arith_ss
   [FinitePSLPathTheory.ELEM_def,FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def,
    FinitePSLPathTheory.HD_RESTN]
   (Q.SPECL[`n`,`n`]FinitePSLPathTheory.EL_SEL0);

(*****************************************************************************)
(* |- !p. LENGTH (SEL p (0,n)) = n + 1                                       *)
(*****************************************************************************)
val LENGTH_SEL0 =
  SIMP_RULE arith_ss [] (Q.SPECL[`0`,`n`]FinitePSLPathTheory.LENGTH_SEL);

val LENGTH_TAKE_FIRSTN_SEL_LEMMA =
 store_thm
  ("LENGTH_TAKE_FIRSTN_SEL_LEMMA",
   ``P(EL n l) /\ n < LENGTH l
     ==>
     (LENGTH(TAKE_FIRSTN P (SUC (LENGTH (FILTER P (SEL l (0,n))) - 1)) (SEL l (0,n))) - 1 = n)``,
   RW_TAC list_ss []
    THEN `LENGTH(SEL l (0,n)) = n+1` by PROVE_TAC[LENGTH_SEL0]
    THEN `P(EL n (SEL l (0,n)))` by PROVE_TAC[EL_SEL0_LEMMA]
    THEN `n < LENGTH (SEL l (0,n))` by DECIDE_TAC
    THEN `LENGTH (FILTER P (SEL l (0,n))) > 0` by PROVE_TAC[NON_ZERO_EXISTS_LENGTH_FILTER]
    THEN `SUC (LENGTH (FILTER P (SEL l (0,n))) - 1) = LENGTH (FILTER P (SEL l (0,n)))` by DECIDE_TAC
    THEN RW_TAC list_ss []
    THEN `P(LAST (SEL l (0,n)))` by PROVE_TAC[EL_LAST_SEL]
    THEN `HOLDS_LAST P (SEL l (0,n))` by PROVE_TAC[HOLDS_LAST_def]
    THEN IMP_RES_TAC HOLDS_LAST_TAKE_FIRSTN
    THEN RW_TAC list_ss []);

(*
val LENGTH_TAKE_FIRSTN_SEL_LEMMA =
 store_thm
  ("LENGTH_TAKE_FIRSTN_SEL_LEMMA",
   ``P(EL n l) /\ n < LENGTH l
     ==>
     (LENGTH(TAKE_FIRSTN P (SUC (LENGTH (FILTER P (SEL l (0,n))) - 1)) l) - 1 = n)``,
   RW_TAC list_ss []
    THEN `LENGTH(SEL l (0,n)) = n+1` by PROVE_TAC[LENGTH_SEL0]
    THEN `P(EL n (SEL l (0,n)))` by PROVE_TAC[EL_SEL0_LEMMA]
    THEN `n < LENGTH (SEL l (0,n))` by DECIDE_TAC
    THEN `LENGTH (FILTER P (SEL l (0,n))) > 0` by PROVE_TAC[NON_ZERO_EXISTS_LENGTH_FILTER]
    THEN `SUC (LENGTH (FILTER P (SEL l (0,n))) - 1) = LENGTH (FILTER P (SEL l (0,n)))` by DECIDE_TAC
    THEN RW_TAC list_ss []
    THEN `P(LAST (SEL l (0,n)))` by PROVE_TAC[EL_LAST_SEL]
    THEN `HOLDS_LAST P (SEL l (0,n))` by PROVE_TAC[HOLDS_LAST_def]
    THEN RW_TAC list_ss [GSYM FIRSTN_SEL]

Want
LENGTH (TAKE_FIRSTN P (LENGTH (FILTER P (FIRSTN n l))) l) = n
reduce using
LENGTH_FILTER_FIRSTN
to
TAKE_FIRSTN P (LENGTH (FILTER P (FIRSTN n l))) l = FILTER P (FIRSTN (LENGTH (TAKE_FIRSTN P n l)) l
reduce using
FIRSTN_TAKE_FIRSTN
to
TAKE_FIRSTN P (LENGTH (FILTER P (FIRSTN n l))) l = FILTER P (TAKE_FIRSTN P n l)
reduce using
FIRSTN_FILTER_TAKE_FIRSTN
to
TAKE_FIRSTN P (LENGTH (FILTER P (FIRSTN n l))) l = FIRSTN n (FILTER P l)


    THEN IMP_RES_TAC HOLDS_LAST_TAKE_FIRSTN
    THEN RW_TAC list_ss []);
*)

val SEL_SEL =
 store_thm
  ("SEL_SEL",
   ``!(l:'a list) n. SEL (SEL l (0,n)) (0,n) = SEL l (0,n)``,
   SIMP_TAC list_ss
    [FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
     FinitePSLPathTheory.HEAD_def,FinitePSLPathTheory.REST_def]
    THEN REWRITE_TAC[GSYM ADD1]
    THEN Induct_on `n`
    THEN FULL_SIMP_TAC list_ss
          [FinitePSLPathTheory.SEL_REC_def,FinitePSLPathTheory.HEAD_def,
           FinitePSLPathTheory.REST_def]);

(*****************************************************************************)
(*     |- !n l P.                                                            *)
(*          P (EL n l) /\ n < LENGTH l ==>                                   *)
(*          0 < LENGTH (FILTER P (SEL l (0,n))) ==>                          *)
(*          (FILTER P (SEL l (0,n)) =                                        *)
(*           SEL (FILTER P (SEL l (0,n)))                                    *)
(*             (0,LENGTH (FILTER P (SEL l (0,n))) - 1))                      *)
(*****************************************************************************)
val FILTER_SEL_COR =
 GEN_ALL
  (DISCH_ALL
   (SIMP_RULE
    list_ss
    [SEL_SEL,ASSUME``P(EL n l) /\ n < LENGTH(l:'a letter list)``,
     LENGTH_TAKE_FIRSTN_SEL_LEMMA]
    (Q.ISPECL
      [`P:'a letter -> bool`,`LENGTH(FILTER P (SEL (l:'a letter list) (0,n))) - 1`,`SEL (l:'a letter list) (0,n)`]
      FILTER_SEL)));

(*****************************************************************************)
(*  |- j < LENGTH l - 1 ==> (l = SEL l (0,j) <> SEL l (j + 1,LENGTH l - 1))  *)
(*****************************************************************************)
val SEL_SPLIT_LEMMA =
 SIMP_RULE
  list_ss
  [SEL_LENGTH]
  (SPECL
    [``l:'a list``,``j:num``,``0``,``LENGTH(l:'a list)-1``]
    FinitePSLPathTheory.SEL_SPLIT);

val SEL_CHOP =
 store_thm
  ("SEL_CHOP",
   ``j < LENGTH l ==> ?l'. l = SEL l (0,j) <> l'``,
   Cases_on `j = LENGTH l - 1`
    THEN RW_TAC list_ss [SEL_LENGTH]
    THENL
     [Q.EXISTS_TAC `[]`
       THEN RW_TAC list_ss [],
      `j < LENGTH l - 1` by DECIDE_TAC
       THEN PROVE_TAC[SEL_SPLIT_LEMMA]]);

local
open FinitePSLPathTheory
in
val F_PROJ_F_STRONG_SERE_FINITE_LEMMA1 =
 SIMP_RULE
  list_ss
  [ELEM_EL,EL_SEL0,LENGTH_SEL]
  (ISPECL
    [``CLOCK c``,``SEL (l :'a letter list) (0,j)``,``j:num``]
    NON_ZERO_EXISTS_LENGTH_FILTER)
val F_PROJ_F_STRONG_SERE_FINITE_LEMMA2 =
 SIMP_RULE
  list_ss
  []
  (ISPECL
    [``FILTER (CLOCK c) (SEL (l :'a letter list) (0,j))``,
     ``l' :'a letter list``,
     ``LENGTH (FILTER (CLOCK c) (SEL (l :'a letter list) (0,j))) - 1``]
    SEL_APPEND1)
end;

val F_PROJ_F_STRONG_SERE_FINITE =
 store_thm
  ("F_PROJ_F_STRONG_SERE_FINITE",
   ``!r.
      F_CLOCK_FREE (F_STRONG_SERE r) ==>
      !l.
        PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
        !c.
          UF_SEM (PROJ (FINITE l) c) (F_STRONG_SERE r) =
          F_SEM (FINITE l) c (F_STRONG_SERE r)``,
   RW_TAC (list_ss++resq_SS)
    [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def,LS,PATH_FILTER_def,
     PATH_TOP_FREE_def,PATH_BOTTOM_FREE_def,SEL_FINITE,LIST_PROJ_def]
      THEN EQ_TAC
      THEN RW_TAC list_ss []
      THENL
       [`LENGTH (FILTER (CLOCK c) l) <= LENGTH l` by PROVE_TAC[LENGTH_FILTER]
         THEN `j < LENGTH l` by DECIDE_TAC
         THEN Q.EXISTS_TAC `LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1`
         THEN RW_TAC list_ss [LIST_PROJ_def,FILTER_SEL]
         THENL
          [`LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) <= LENGTH l` by PROVE_TAC[LENGTH_TAKE_FIRSTN]
            THEN DECIDE_TAC,
           `LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) <= LENGTH l` by PROVE_TAC[LENGTH_TAKE_FIRSTN]
            THEN `LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1 < LENGTH l` by DECIDE_TAC
            THEN `S_SEM (SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1))) c r =
                  (LENGTH(SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1))) > 0
                  ==> CLOCK c (LAST(SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1)))))
                      /\
                      US_SEM (LIST_PROJ (SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1))) c) r`
            by PROVE_TAC[S_PROJ,TOP_FREE_SEL,BOTTOM_FREE_SEL]
           THEN RW_TAC list_ss [LIST_PROJ_def,FILTER_SEL,SEL_TAKE_FIRSTN,LAST_TAKE_FIRSTN]],
        `(LENGTH (SEL l (0,j)) > 0
          ==>
          CLOCK c (LAST (SEL l (0,j)))) /\ US_SEM (FILTER (CLOCK c) (SEL l (0,j))) r`
         by PROVE_TAC[S_PROJ,TOP_FREE_SEL,BOTTOM_FREE_SEL,LIST_PROJ_def]
         THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.LENGTH_SEL,FinitePSLPathTheory.EL_LAST_SEL]
         THEN Q.EXISTS_TAC `LENGTH (FILTER (CLOCK c) (SEL l (0,j))) - 1`
         THEN IMP_RES_TAC NON_ZERO_EXISTS_LENGTH_FILTER
         THEN RW_TAC list_ss []
         THEN IMP_RES_TAC SEL_CHOP
         THENL
          [POP_ASSUM(fn th => CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[th])))
            THEN RW_TAC list_ss [FILTER_APPEND],
           POP_ASSUM(fn th => CONV_TAC((RATOR_CONV o RAND_CONV o RATOR_CONV) (ONCE_REWRITE_CONV[th])))
            THEN IMP_RES_TAC F_PROJ_F_STRONG_SERE_FINITE_LEMMA1
            THEN `LENGTH (FILTER (CLOCK c) (SEL l (0,j))) - 1 < LENGTH(FILTER (CLOCK c) (SEL l (0,j)))`
                  by DECIDE_TAC
            THEN `0 < LENGTH (FILTER (CLOCK c) (SEL l (0,j)))` by DECIDE_TAC
            THEN RW_TAC std_ss [F_PROJ_F_STRONG_SERE_FINITE_LEMMA2,FILTER_APPEND,SEL_LENGTH]]]);

(*

val F_PROJ_F_WEAK_SERE_FINITE =
 store_thm
  ("F_PROJ_F_WEAK_SERE_FINITE",
   ``!r.
      F_CLOCK_FREE (F_WEAK_SERE r) ==>
      !l.
        PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
        !c.
          UF_SEM (PROJ (FINITE l) c) (F_WEAK_SERE r) =
          F_SEM (FINITE l) c (F_WEAK_SERE r)``,
   RW_TAC (list_ss++resq_SS)
    [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def,LS,PATH_FILTER_def,
     PATH_TOP_FREE_def,PATH_BOTTOM_FREE_def,SEL_FINITE,LIST_PROJ_def]
      THEN EQ_TAC
      THEN RW_TAC list_ss [TOP_OMEGA_def,LENGTH_def,LS,LENGTH_CAT]
      THENL
       [`LENGTH (FILTER (CLOCK c) l) <= LENGTH l` by PROVE_TAC[LENGTH_FILTER]
         THEN `j < LENGTH l` by DECIDE_TAC
         THEN Q.EXISTS_TAC `LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1`
         THEN RW_TAC list_ss [LIST_PROJ_def,FILTER_SEL]
         THENL
          [`LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) <= LENGTH l` by PROVE_TAC[LENGTH_TAKE_FIRSTN]
            THEN DECIDE_TAC,
           `LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) <= LENGTH l` by PROVE_TAC[LENGTH_TAKE_FIRSTN]
            THEN `LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1 < LENGTH l` by DECIDE_TAC
            THEN `S_SEM (SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1))) c r =
                  (LENGTH(SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1))) > 0
                  ==> CLOCK c (LAST(SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1)))))
                      /\
                      US_SEM (LIST_PROJ (SEL l (0,(LENGTH (TAKE_FIRSTN (CLOCK c) (SUC j) l) - 1))) c) r`
            by PROVE_TAC[S_PROJ,TOP_FREE_SEL,BOTTOM_FREE_SEL]
           THEN RW_TAC list_ss [LIST_PROJ_def,FILTER_SEL,SEL_TAKE_FIRSTN,LAST_TAKE_FIRSTN]],
        `(LENGTH (SEL l (0,j)) > 0
          ==>
          CLOCK c (LAST (SEL l (0,j)))) /\ US_SEM (FILTER (CLOCK c) (SEL l (0,j))) r`
         by PROVE_TAC[S_PROJ,TOP_FREE_SEL,BOTTOM_FREE_SEL,LIST_PROJ_def]
         THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.LENGTH_SEL,FinitePSLPathTheory.EL_LAST_SEL]
         THEN Q.EXISTS_TAC `LENGTH (FILTER (CLOCK c) (SEL l (0,j))) - 1`
         THEN IMP_RES_TAC NON_ZERO_EXISTS_LENGTH_FILTER
         THEN RW_TAC list_ss []
         THEN IMP_RES_TAC SEL_CHOP
         THENL
          [POP_ASSUM(fn th => CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[th])))
            THEN RW_TAC list_ss [FILTER_APPEND],
           POP_ASSUM(fn th => CONV_TAC((RATOR_CONV o RAND_CONV o RATOR_CONV) (ONCE_REWRITE_CONV[th])))
            THEN IMP_RES_TAC F_PROJ_F_STRONG_SERE_FINITE_LEMMA1
            THEN `LENGTH (FILTER (CLOCK c) (SEL l (0,j))) - 1 < LENGTH(FILTER (CLOCK c) (SEL l (0,j)))`
                  by DECIDE_TAC
            THEN `0 < LENGTH (FILTER (CLOCK c) (SEL l (0,j)))` by DECIDE_TAC
            THEN RW_TAC std_ss [F_PROJ_F_STRONG_SERE_FINITE_LEMMA2,FILTER_APPEND,SEL_LENGTH]]]);


val F_PROJ_F_NEXT_FINITE =
 store_thm
  ("F_PROJ_F_NEXT_FINITE",
   ``!f.
      (F_CLOCK_FREE f ==>
       !l. PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
           !c. UF_SEM (PROJ (FINITE l) c) f = F_SEM (FINITE l) c f)
      ==>
      F_CLOCK_FREE (F_NEXT f) ==>
       !l. PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l) ==>
          !c. UF_SEM (PROJ (FINITE l) c) (F_NEXT f) =
              F_SEM (FINITE l) c (F_NEXT f)``,
   RW_TAC (list_ss++resq_SS)
    [UF_SEM,F_SEM,GSYM CLOCK_def,PROJ_def,F_CLOCK_FREE_def,LS,PATH_FILTER_def,
     PATH_TOP_FREE_def,PATH_BOTTOM_FREE_def,SEL_FINITE,LIST_PROJ_def]
      THEN EQ_TAC
      THEN RW_TAC list_ss []

val F_PROJ_FINITE =
 store_thm
  ("F_PROJ_FINITE",
   ``!f.
      F_CLOCK_FREE f
      ==>
      !l. PATH_TOP_FREE (FINITE l) /\ PATH_BOTTOM_FREE (FINITE l)
          ==>
          !c. UF_SEM (PROJ (FINITE l) c) f = F_SEM (FINITE l) c f``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_STRONG_BOOL b *)
      RW_TAC std_ss [F_PROJ_F_STRONG_BOOL],
      (* F_WEAK_BOOL b *)
      RW_TAC std_ss [F_PROJ_F_WEAK_BOOL],
      (* F_NOT_BOOL b *)
      RW_TAC std_ss [F_PROJ_F_NOT_BOOL_FINITE],
      (* F_AND_BOOL b *)
      RW_TAC std_ss [F_PROJ_F_AND_BOOL_FINITE],
      (* F_STRONG_SERE b *)
      RW_TAC std_ss [F_PROJ_F_STRONG_SERE_FINITE],

*)

val _ = export_theory();
