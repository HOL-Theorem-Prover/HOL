

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
  "SyntacticSugarTheory", "ClockedSemanticsTheory", "RewritesTheory", 
  "rich_listTheory", "intLib", "res_quanLib", "res_quanTheory",
  "LemmasTheory","RewritesPropertiesTheory"];
open FinitePathTheory PathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
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
open FinitePathTheory PathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
     ClockedSemanticsTheory LemmasTheory RewritesPropertiesTheory;

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

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS = 
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [IN_DEF,LESS_def,LESSX_def,LENGTH_def]];

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

(******************************************************************************
* CLOCK c s is true is clock c is true in state s
******************************************************************************)

val CLOCK_def = Define `CLOCK c s = B_SEM s c`;

open FinitePathTheory;

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
  ("FIRSTN_AUX",
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

val TAKE_FIRSTN_NIL =
 store_thm
  ("TAKE_FIRSTN_NIL",
   ``!P n l. 0 < n ==> (TAKE_FIRSTN P n l = []) ==> (l = [])``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss [TAKE_FIRSTN_def]
    THEN PROVE_TAC[TAKE_FIRST_NIL]);

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
          [TAKE_FIRST_def,TAKE_FIRSTN_def,FIRSTN]
    THEN FULL_SIMP_TAC list_ss [BUTFIRSTN_ONE,BUTFIRSTN]
    THENL
     [REWRITE_TAC[GSYM ADD1,FIRSTN]
       THEN RW_TAC list_ss [],
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
    THEN FULL_SIMP_TAC list_ss []
    THENL
     [REWRITE_TAC[ONE]
       THEN RW_TAC list_ss [BUTFIRSTN],
      RW_TAC list_ss [BUTFIRSTN]]);

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
    THEN RW_TAC list_ss [TAKE_FIRST_def,BUTFIRSTN,BUTFIRSTN_ONE]);

val LENGTH_1_BUTFIRSTN =
 store_thm
  ("LENGTH_1_BUTFIRSTN",
   ``!P l. HOLDS_LAST P l /\ (LENGTH (FILTER P l) = 1) 
           ==> 
           (BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l = [])``,
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss [TAKE_FIRST_def,BUTFIRSTN,BUTFIRSTN_ONE,HOLDS_LAST_def]
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

val HOLDS_LAST_TAKE_FIRST =
 store_thm
  ("HOLDS_LAST_TAKE_FIRST",
   ``!P l. HOLDS_LAST P l 
           ==>
           (TAKE_FIRST P l <> BUTFIRSTN (LENGTH (TAKE_FIRST P l)) l = l)``,
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
       THEN RW_TAC list_ss [HOLDS_LAST_TAKE_FIRST]]);


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

val TOP_FREE_LASTN =
 store_thm
  ("TOP_FREE_LASTN",
   ``!l n. n <= LENGTH l /\ TOP_FREE l ==> TOP_FREE(LASTN n l)``,
   SIMP_TAC list_ss [LASTN_REVERSE_FIRSTN]
    THEN Induct_on `l`
    THEN RW_TAC list_ss [TOP_FREE_def,FIRSTN]
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [FIRSTN,TOP_FREE_def]
    THEN FULL_SIMP_TAC list_ss [TOP_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss 
          [B_SEM_def,TOP_FREE_def,EL_CONS,
           DECIDE``PRE n = n-1``,TOP_FREE_REVERSE]
    THEN RES_TAC
    THEN Cases_on `n = LENGTH l`
    THEN RW_TAC list_ss []
    THENL
     [`LENGTH(REVERSE l <> [BOTTOM]) = SUC(LENGTH l)` 
       by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `LENGTH l < LENGTH(REVERSE l <> [BOTTOM])` by DECIDE_TAC
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[BOTTOM]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [BOTTOM]) = BOTTOM` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN RW_TAC list_ss [FIRSTN_SUC_EL,TOP_FREE_APPEND,TOP_FREE_def],
      `SUC n <= LENGTH l` by DECIDE_TAC
       THEN RES_TAC 
       THEN `LENGTH l < LENGTH(REVERSE l <> [BOTTOM])` 
             by RW_TAC list_ss [LENGTH_APPEND,LENGTH_REVERSE]
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[BOTTOM]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [BOTTOM]) = BOTTOM` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN RW_TAC list_ss [EL_APPEND1,FIRSTN_SUC_EL,TOP_FREE_APPEND,TOP_FREE_def]
       THEN RW_TAC list_ss [TOP_FREE_EL]
       THEN `i = 0` by DECIDE_TAC
       THEN RW_TAC list_ss []
       THEN `TOP_FREE(REVERSE l)` by PROVE_TAC[TOP_FREE_REVERSE]
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_EL],
      `LENGTH(REVERSE l <> [STATE f]) = SUC(LENGTH l)` 
       by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `LENGTH l < LENGTH(REVERSE l <> [STATE f])` by DECIDE_TAC
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[STATE f]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [STATE f]) = STATE f` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN RW_TAC list_ss [FIRSTN_SUC_EL,TOP_FREE_APPEND,TOP_FREE_def],
      `SUC n <= LENGTH l` by DECIDE_TAC
       THEN RES_TAC 
       THEN `LENGTH l < LENGTH(REVERSE l <> [STATE f])` 
             by RW_TAC list_ss [LENGTH_APPEND,LENGTH_REVERSE]
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[STATE f]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [STATE f]) = STATE f` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN RW_TAC list_ss [EL_APPEND1,FIRSTN_SUC_EL,TOP_FREE_APPEND,TOP_FREE_def]
       THEN RW_TAC list_ss [TOP_FREE_EL]
       THEN `i = 0` by DECIDE_TAC
       THEN RW_TAC list_ss []
       THEN `TOP_FREE(REVERSE l)` by PROVE_TAC[TOP_FREE_REVERSE]
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_EL]]);

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
     
val BOTTOM_FREE_LASTN =
 store_thm
  ("BOTTOM_FREE_LASTN",
   ``!l n. n <= LENGTH l /\ BOTTOM_FREE l ==> BOTTOM_FREE(LASTN n l)``,
   SIMP_TAC list_ss [LASTN_REVERSE_FIRSTN]
    THEN Induct_on `l`
    THEN RW_TAC list_ss [BOTTOM_FREE_def,FIRSTN]
    THEN Induct_on `n`
    THEN RW_TAC list_ss
          [FIRSTN,BOTTOM_FREE_def]
    THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss 
          [B_SEM_def,BOTTOM_FREE_def,EL_CONS,
           DECIDE``PRE n = n-1``,BOTTOM_FREE_REVERSE]
    THEN RES_TAC
    THEN Cases_on `n = LENGTH l`
    THEN RW_TAC list_ss []
    THENL
     [`LENGTH(REVERSE l <> [TOP]) = SUC(LENGTH l)` 
       by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `LENGTH l < LENGTH(REVERSE l <> [TOP])` by DECIDE_TAC
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[TOP]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [TOP]) = TOP` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN RW_TAC list_ss [FIRSTN_SUC_EL,BOTTOM_FREE_APPEND,BOTTOM_FREE_def],
      `SUC n <= LENGTH l` by DECIDE_TAC
       THEN RES_TAC 
       THEN `LENGTH l < LENGTH(REVERSE l <> [TOP])` 
             by RW_TAC list_ss [LENGTH_APPEND,LENGTH_REVERSE]
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[TOP]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [TOP]) = TOP` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN RW_TAC list_ss [EL_APPEND1,FIRSTN_SUC_EL,BOTTOM_FREE_APPEND,BOTTOM_FREE_def]
       THEN RW_TAC list_ss [BOTTOM_FREE_EL]
       THEN `i = 0` by DECIDE_TAC
       THEN RW_TAC list_ss []
       THEN `BOTTOM_FREE(REVERSE l)` by PROVE_TAC[BOTTOM_FREE_REVERSE]
       THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_EL],
      `LENGTH(REVERSE l <> [STATE f]) = SUC(LENGTH l)` 
       by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `LENGTH l < LENGTH(REVERSE l <> [STATE f])` by DECIDE_TAC
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[STATE f]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [STATE f]) = STATE f` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN RW_TAC list_ss [FIRSTN_SUC_EL,BOTTOM_FREE_APPEND,BOTTOM_FREE_def],
      `SUC n <= LENGTH l` by DECIDE_TAC
       THEN RES_TAC 
       THEN `LENGTH l < LENGTH(REVERSE l <> [STATE f])` 
             by RW_TAC list_ss [LENGTH_APPEND,LENGTH_REVERSE]
       THEN `LENGTH(REVERSE l) = LENGTH l` by RW_TAC list_ss [LENGTH_REVERSE]
       THEN `~NULL[STATE f]` by RW_TAC list_ss []
       THEN `EL (LENGTH l) (REVERSE l <> [STATE f]) = STATE f` by PROVE_TAC[EL_LENGTH_APPEND,HD]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN RW_TAC list_ss [EL_APPEND1,FIRSTN_SUC_EL,BOTTOM_FREE_APPEND,BOTTOM_FREE_def]
       THEN RW_TAC list_ss [BOTTOM_FREE_EL]
       THEN `i = 0` by DECIDE_TAC
       THEN RW_TAC list_ss []
       THEN `BOTTOM_FREE(REVERSE l)` by PROVE_TAC[BOTTOM_FREE_REVERSE]
       THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_EL]]);

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

val SPLIT_APPEND =
 store_thm
  ("SPLIT_APPEND",
   ``!u1 u2 v1 v2:'a list.
      (u1 <> u2 = v1 <> v2) /\ (LENGTH u1 = LENGTH v1) ==> (u2 = v2)``,
   Induct
    THEN RW_TAC list_ss []
    THENL
     [`v1 = []` by PROVE_TAC[LENGTH_NIL]
       THEN RW_TAC list_ss [],
      Cases_on `v1`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []]);

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
    THEN RW_TAC list_ss [TAKE_FIRST_def,TAKE_FIRSTN_def,BUTFIRSTN_ONE]
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
    THEN `0 < SUC (LENGTH v1)` by DECIDE_TAC
    THEN `LENGTH(FILTER (CLOCK c) l) =  LENGTH(v1 <> [l'] <> v2)`
          by PROVE_TAC[]
    THEN FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH]
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
       THEN `~(TAKE_FIRSTN (CLOCK c) (SUC(LENGTH v1)) l = [])` by PROVE_TAC[TAKE_FIRSTN_NIL]
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
          !c. (LENGTH l > 0 ==> CLOCK c (LAST l)) /\ US_SEM (LIST_PROJ l c) r = S_SEM l c r``,
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

val _ = export_theory();

