
(*****************************************************************************)
(* Some properties of the Sugar 2.0 semantics                                *)
(* ------------------------------------------------------------------------- *)
(* Runs in                                                                   *)
(*  HOL [Kananaskis 2 (built Sat Aug 10 21:39:46 2002)]                      *)
(* but not in the currently broken newer releases HOL                        *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(*
load "Sugar2SemanticsTheory"; 
load "rich_listTheory"; load "intLib"; 
load "res_quanLib";load "res_quanTheory";

quietdec := true;
open Sugar2SemanticsTheory PathTheory 
     arithmeticTheory listTheory rich_listTheory res_quanTheory;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open Globals HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open Sugar2SemanticsTheory PathTheory 
     arithmeticTheory listTheory rich_listTheory res_quanTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

val resd = 
 simpLib.SIMPSET {ac = [], congs = [],
                  convs = 
                   [{conv = K (K (res_quanLib.RES_FORALL_CONV 
                                  ORELSEC res_quanLib.RES_EXISTS_CONV)),
                    key = SOME([],``(P:('a -> bool) -> ('a -> bool) -> bool)(\x. Q x)``), 
                    name = "RES_CONV", trace = 2}],
                    dprocs = [], filter = NONE, rewrs = []};

(******************************************************************************
* Start a new theory called Sugar2
******************************************************************************)
val _ = new_theory "Sugar2";

(******************************************************************************
* w |=T= b is equivalent to ?l. (w =[l]) /\ l |= b
******************************************************************************)
val S_BOOL_TRUE =
 store_thm
  ("S_BOOL_TRUE",
   ``S_SEM M w B_TRUE (S_BOOL b) = ?l. (w =[l]) /\ B_SEM M l b``,
   RW_TAC arith_ss 
    [S_SEM_def,B_SEM_def,CONJ_ASSOC,
     Cooper.COOPER_PROVE``(n >= 1 /\ (!i. ~(1 <= i) \/ ~(i < n))) = (n = 1)``]
    THEN RW_TAC list_ss [LENGTH_CONS,arithmeticTheory.ONE,LENGTH_NIL]
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THEN FULL_SIMP_TAC list_ss [LENGTH,EL]);

(******************************************************************************
* Some lemmas about FIRST_RISE and NEXT_RISE
******************************************************************************)
val S_REPEAT_BOOL_TRUE =
 store_thm
  ("S_REPEAT_BOOL_TRUE",
   ``S_SEM M w B_TRUE (S_REPEAT(S_BOOL b))  = 
      !i. i < LENGTH w ==> B_SEM M (EL i w) b``,
   RW_TAC std_ss 
    [S_SEM_def,B_SEM_def,CONJ_ASSOC, LENGTH_CONS,LENGTH_NIL,
     Cooper.COOPER_PROVE ``(n >= 1n /\ !i. ~(1 <= i) \/ ~(i < n)) = (n = 1)``]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [IMP_RES_TAC
       (SIMP_RULE std_ss [] (Q.ISPEC `\x. B_SEM M x b` ALL_EL_CONCAT))
       THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [EVERY_EL])
       THEN RES_TAC,
      Q.EXISTS_TAC `MAP (\l. [l]) w`
       THEN RW_TAC list_ss 
             [EVERY_EL,CONCAT_MAP_SINGLETON,LENGTH_EL_MAP_SINGLETON,
              HD_EL_MAP]]);

val FIRST_RISE_IMP =
 store_thm
  ("FIRST_RISE_IMP",
   ``FIRST_RISE M p c i ==>
      (!j. j < i ==> ~B_SEM M (getL M (PATH_EL p j)) c) 
      /\ 
      B_SEM M (getL M (PATH_EL p i)) c``,
   REWRITE_TAC [FIRST_RISE_def]
    THEN ONCE_REWRITE_TAC[S_SEM_def]
    THEN SIMP_TAC list_ss 
          [S_REPEAT_BOOL_TRUE,S_BOOL_TRUE,APPEND_INFIX_def,B_SEM_def]
    THEN ONCE_REWRITE_TAC [EQ_SINGLETON]
    THEN RW_TAC std_ss []
    THENL
     [ASSUM_LIST
       (fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 3 thl](el 5 thl)))	
       THEN IMP_RES_TAC(DECIDE ``j < i ==> i > 0``)
       THEN IMP_RES_TAC MAP_PATH_SEG_APPEND_SINGLETON_IMP0
       THEN ASSUM_LIST
              (fn thl 
                => ASSUME_TAC
                    (Q.AP_TERM 
                     `LENGTH`
                     (el 9 thl)))
       THEN POP_ASSUM
             (ASSUME_TAC o 
              SIMP_RULE list_ss [LENGTH_MAP,LENGTH_PATH_SEG_REC,PATH_SEG_def])
       THEN ASSUM_LIST
              (fn thl 
                => ASSUME_TAC
                    (Q.AP_TERM 
                     `LENGTH`
                     (el 8 thl)))
       THEN POP_ASSUM
             (ASSUME_TAC o 
              SIMP_RULE list_ss [GSYM arithmeticTheory.ONE])
       THEN IMP_RES_TAC
              (DECIDE``(n = 1) ==> (i + 1 = m + n) ==> j < i ==> j < m``)
       THEN RES_TAC
       THEN RW_TAC std_ss []
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(REWRITE_RULE[LENGTH_MAP](el 2 thl)))
       THEN POP_ASSUM
             (fn th => 
               ASSUME_TAC
                (ISPEC 
                  ``getL
                     (M :'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool))`` 
                  (MATCH_MP EL_MAP th)))
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl](el 2 thl)))
       THEN ASSUM_LIST
             (fn thl  => 
               ASSUME_TAC
                (SIMP_RULE std_ss 
                  [LENGTH_MAP,LENGTH_PATH_SEG_REC,PATH_SEG_def](el 4 thl)))
       THEN IMP_RES_TAC(DECIDE``j < i - 1 - 0 + 1 ==> j <= i-1``)
       THEN PROVE_TAC[EL_PATH_SEG0],
      ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 2 thl](el 4 thl)))
       THEN ASSUM_LIST
             (fn thl => 
               ASSUME_TAC
                (SIMP_RULE arith_ss 
                  [LENGTH_MAP,LENGTH_APPEND,LENGTH,PATH_SEG_def,
                   LENGTH_PATH_SEG_REC]
                  (Q.AP_TERM `LENGTH` (el 1 thl))))
       THEN Cases_on `i=0`
       THENL
        [RW_TAC arith_ss []
          THEN IMP_RES_TAC(DECIDE``(0 + 1 = m + SUC 0) ==> (m = 0)``)
          THEN FULL_SIMP_TAC arith_ss [LENGTH_NIL]
          THEN FULL_SIMP_TAC list_ss [LENGTH,PATH_SEG_EL],
         IMP_RES_TAC
           (DECIDE
             ``(i + 1 = m + SUC 0) ==> ~(i = 0) ==>  0 <= i-1 /\ i-1 < i``)
          THEN IMP_RES_TAC(ISPEC ``p :'e path`` PATH_SEG_SPLIT)
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl] (el 6 thl)))
          THEN IMP_RES_TAC(DECIDE``~(i = 0) ==> (i - 1 + 1 = i)``)
          THEN POP_ASSUM
                (fn th => 
                  FULL_SIMP_TAC list_ss 
                   [MAP_APPEND,th,PATH_SEG_EL,APPEND_CANCEL])]]);

val NEXT_RISE_IMP =
 store_thm
  ("NEXT_RISE_IMP",
   ``NEXT_RISE M p c (i,j) ==>
      (!k. i <= k /\ k < j ==> ~B_SEM M (getL M (PATH_EL p k)) c) 
      /\ 
      (i <= j ==> B_SEM M (getL M (PATH_EL p j)) c)``,
   REWRITE_TAC [NEXT_RISE_def]
    THEN ONCE_REWRITE_TAC[S_SEM_def]
    THEN SIMP_TAC list_ss 
          [S_REPEAT_BOOL_TRUE,S_BOOL_TRUE,APPEND_INFIX_def,B_SEM_def]
    THEN ONCE_REWRITE_TAC [EQ_SINGLETON]
    THEN RW_TAC std_ss []
    THENL
     [ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 4 thl](el 6 thl)))	
       THEN IMP_RES_TAC(DECIDE ``i <= k ==> k < j ==> j > i``)
       THEN IMP_RES_TAC MAP_PATH_SEG_APPEND_SINGLETON_IMP
       THEN ASSUM_LIST
              (fn thl 
                => ASSUME_TAC
                    (Q.AP_TERM 
                     `LENGTH`
                     (el 10 thl)))
       THEN POP_ASSUM
             (ASSUME_TAC o 
              SIMP_RULE list_ss [LENGTH_MAP,LENGTH_PATH_SEG_REC,PATH_SEG_def])
       THEN ASSUM_LIST
              (fn thl 
                => ASSUME_TAC
                    (Q.AP_TERM 
                     `LENGTH`
                     (el 9 thl)))
       THEN POP_ASSUM
             (ASSUME_TAC o SIMP_RULE list_ss [GSYM arithmeticTheory.ONE])
       THEN IMP_RES_TAC
              (DECIDE``(n = 1) ==> (j - i + 1 = m + n) 
                       ==> i <= k ==> k < j ==> k - i < m``)
       THEN RES_TAC
       THEN RW_TAC std_ss []
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(REWRITE_RULE[LENGTH_MAP](el 2 thl)))
       THEN POP_ASSUM
             (fn th => 
               ASSUME_TAC
                (ISPEC 
                  ``getL
                     (M :'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool))`` 
                  (MATCH_MP EL_MAP th)))
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl](el 2 thl)))
       THEN ASSUM_LIST
             (fn thl  =>
               ASSUME_TAC
                (SIMP_RULE std_ss [LENGTH_MAP,LENGTH_PATH_SEG](el 4 thl)))
       THEN IMP_RES_TAC(DECIDE``i <= k ==> k < j ==>  k <= j - 1``)
       THEN PROVE_TAC[EL_PATH_SEG],
      ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 3 thl](el 5 thl)))	
       THEN ASSUM_LIST
             (fn thl => 
               ASSUME_TAC
                (SIMP_RULE arith_ss 
                  [LENGTH_MAP,LENGTH_APPEND,LENGTH,PATH_SEG_def,
                   LENGTH_PATH_SEG_REC]
                  (Q.AP_TERM `LENGTH` (el 1 thl))))
       THEN Cases_on `i=j`
       THENL
        [RW_TAC arith_ss []
          THEN IMP_RES_TAC(DECIDE``(i - i + 1 = m + SUC 0) ==> (m = 0)``)
          THEN FULL_SIMP_TAC arith_ss [LENGTH_NIL]
          THEN RW_TAC arith_ss []
          THEN FULL_SIMP_TAC list_ss [LENGTH,PATH_SEG_EL],
         IMP_RES_TAC
          (DECIDE``(j - i + 1 = m + SUC 0) 
                   ==> ~(i = j) ==> i <= j ==>  i <= j-1 /\ j-1 < j``)
          THEN IMP_RES_TAC(ISPEC ``p :'e path`` PATH_SEG_SPLIT)
          THEN POP_ASSUM(K ALL_TAC)
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl] (el 6 thl)))
          THEN IMP_RES_TAC(DECIDE``j-1 < j ==> (j - 1 + 1 = j)``)
          THEN POP_ASSUM
                (fn th => FULL_SIMP_TAC list_ss 
                  [MAP_APPEND,th,PATH_SEG_EL,APPEND_CANCEL])]]);

val EL_MAP_COR =
 store_thm
  ("EL_MAP_COR",
   ``!f. n < LENGTH l ==> (EL n (MAP f l) = f (EL n l))``,
   RW_TAC std_ss [EL_MAP]);

val FIRST_RISE_REVIMP =
 store_thm
  ("FIRST_RISE_REVIMP",
   ``(!j. j < i ==> ~B_SEM M (getL M (PATH_EL p j)) c) 
     /\ B_SEM M (getL M (PATH_EL p i)) c
     ==>
     FIRST_RISE M p c i``,
   REWRITE_TAC [FIRST_RISE_def]
    THEN ONCE_REWRITE_TAC[S_SEM_def]
    THEN RW_TAC list_ss 
          [S_REPEAT_BOOL_TRUE,S_BOOL_TRUE,APPEND_INFIX_def,B_SEM_def]
    THEN Cases_on `i`
     THENL
      [Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `MAP (getL M) (PATH_SEG p (0,0))` 
        THEN RW_TAC list_ss [PATH_SEG_EL],
      Q.EXISTS_TAC `MAP (getL M) (PATH_SEG p (0,n))`
        THEN Q.EXISTS_TAC `MAP (getL M) (PATH_SEG p (SUC n,SUC n))` 
        THEN RW_TAC list_ss []
        THENL
         [RW_TAC arith_ss [GSYM MAP_APPEND]
           THEN REWRITE_TAC
                 [SIMP_RULE arith_ss 
                   [GSYM arithmeticTheory.ADD1] 
                   (Q.SPECL[`p`,`n`,`0`,`SUC n`]PATH_SEG_SPLIT)],
          POP_ASSUM
            (ASSUME_TAC o 
             SIMP_RULE arith_ss 
              [PATH_SEG_def,PATH_SEG_REC_def,LENGTH_PATH_SEG_REC])
           THEN FULL_SIMP_TAC std_ss [GSYM arithmeticTheory.ADD1]
           THEN RES_TAC
           THEN IMP_RES_TAC(DECIDE ``m < SUC n ==> m <= n``)
           THEN IMP_RES_TAC
                 (ISPECL[``i':num``,``n:num``,``p :'e path``] EL_PATH_SEG0)
           THEN ASSUME_TAC
                 (SIMP_RULE arith_ss [] 
                   ((ISPECL[``0``,``n:num``,``p :'e path``] LENGTH_PATH_SEG)))
           THEN IMP_RES_TAC(DECIDE ``(m = n+1) ==> i <= n ==> i < m``)
           THEN IMP_RES_TAC
                  (ISPECL
                    [``getL
                        (M :'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool))``]
                    EL_MAP_COR)
           THEN RW_TAC std_ss [],
          Q.EXISTS_TAC `getL M (PATH_EL p (SUC n))`          
           THEN RW_TAC list_ss [PATH_SEG_EL]]]);

val FIRST_RISE =
 store_thm
  ("FIRST_RISE",
   ``FIRST_RISE M p c i =
      (!j. j < i ==> ~B_SEM M (getL M (PATH_EL p j)) c) 
      /\ 
      B_SEM M (getL M (PATH_EL p i)) c``,
   PROVE_TAC[FIRST_RISE_IMP, FIRST_RISE_REVIMP]);

val FIRST_RISE_TRUE =
 store_thm
  ("FIRST_RISE_TRUE",
   ``FIRST_RISE M p B_TRUE i = (i = 0)``,
   RW_TAC std_ss [FIRST_RISE,L_def,B_SEM_def]
    THEN EQ_TAC
    THEN ZAP_TAC std_ss [intLib.COOPER_PROVE``(!j. ~(j < i)) = (i=0)``]);

val NEXT_RISE_REVIMP =
 store_thm
  ("NEXT_RISE_REVIMP",
   ``i <= j                                                       /\
     (!k. i <= k /\ k < j ==> ~B_SEM M (getL M (PATH_EL p k)) c)  /\ 
     B_SEM M (getL M (PATH_EL p j)) c  
     ==>
     NEXT_RISE M p c (i,j)``,
   REWRITE_TAC [NEXT_RISE_def]
    THEN ONCE_REWRITE_TAC[S_SEM_def]
    THEN RW_TAC list_ss 
          [S_REPEAT_BOOL_TRUE,S_BOOL_TRUE,APPEND_INFIX_def,B_SEM_def]
    THEN Cases_on `i=j`
     THENL
      [RW_TAC std_ss []
        THEN Q.EXISTS_TAC `[]` 
        THEN Q.EXISTS_TAC `MAP (getL M) (PATH_SEG p (i,i))` 
        THEN RW_TAC list_ss [PATH_SEG_EL],
      Q.EXISTS_TAC `MAP (getL M) (PATH_SEG p (i,j-1))`
        THEN Q.EXISTS_TAC `MAP (getL M) (PATH_SEG p (j,j))` 
        THEN RW_TAC list_ss []
        THENL
         [RW_TAC arith_ss [GSYM MAP_APPEND]
           THEN RW_TAC arith_ss [Q.SPECL[`p`,`j-1`,`i`,`j`]PATH_SEG_SPLIT],
          POP_ASSUM
            (ASSUME_TAC o 
             SIMP_RULE arith_ss 
              [PATH_SEG_def,PATH_SEG_REC_def,LENGTH_PATH_SEG_REC])
           THEN IMP_RES_TAC
                 (DECIDE``i <= j ==> ~(i = j) 
                          ==> i' < j - (i + 1) + 1 ==> i <= i+i' /\ i+i' < j``)
           THEN RES_TAC
           THEN POP_ASSUM(K ALL_TAC)
           THEN IMP_RES_TAC
                  (DECIDE ``i <= i + i' ==> i + i' < j ==> i + i' <= j - 1``)
           THEN IMP_RES_TAC
                 (ISPECL[``i:num``,``i+i'``, ``j-1``,``p :'e path``]EL_PATH_SEG)
           THEN FULL_SIMP_TAC std_ss [DECIDE ``i + i' - i = i'``]
           THEN ASSUME_TAC
                 (ISPECL[``i:num``,``j-1``,``p :'e path``]LENGTH_PATH_SEG)
           THEN IMP_RES_TAC
                 (DECIDE ``(m = j - 1 - i + 1) ==> i + i' < j ==> i' < m``)
           THEN IMP_RES_TAC
                  (ISPECL
                    [``getL
                        (M :'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool))``]
                    EL_MAP_COR)
           THEN RW_TAC std_ss [],
          Q.EXISTS_TAC `getL M (PATH_EL p j)`          
           THEN RW_TAC list_ss [PATH_SEG_EL]]]);

val NEXT_RISE =
 store_thm
  ("NEXT_RISE",
   ``i <= j
     ==>
     (NEXT_RISE M p c (i,j) =
       (!k. i <= k /\ k < j ==> ~B_SEM M (getL M (PATH_EL p k)) c)
        /\ 
        B_SEM M (getL M (PATH_EL p j)) c)``,
   PROVE_TAC[NEXT_RISE_IMP, NEXT_RISE_REVIMP]);

val NEXT_RISE_TRUE =
 store_thm
  ("NEXT_RISE_TRUE",
   ``i <= j ==> (NEXT_RISE M p B_TRUE (i,j) = (i = j))``,
   RW_TAC std_ss [NEXT_RISE,L_def,B_SEM_def]
    THEN EQ_TAC
    THENL
     [RW_TAC arith_ss []
       THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE arith_ss [] o SPEC ``i:num``)
       THEN DECIDE_TAC,
      intLib.COOPER_TAC]);

val NEXT_RISE_TRUE_COR =
 store_thm
  ("NEXT_RISE_TRUE_COR",
   ``i <= j /\ NEXT_RISE M p B_TRUE (i,j) = (i = j)``,
   EQ_TAC
    THEN RW_TAC arith_ss [NEXT_RISE_TRUE]
    THEN PROVE_TAC[NEXT_RISE_TRUE]);

val NEXT_RISE_TRUE_EXISTS =
 store_thm
  ("NEXT_RISE_TRUE_EXISTS",
   ``?k. NEXT_RISE M p B_TRUE (j,k)``,
   Q.EXISTS_TAC `j`
    THEN RW_TAC std_ss 
     [SIMP_RULE arith_ss [] (Q.SPECL[`p`,`j`,`j`](GEN_ALL NEXT_RISE_TRUE))]);

val NEXT_RISE_LEQ_TRUE_EXISTS =
 store_thm
  ("NEXT_RISE_LEQ_TRUE_EXISTS",
   ``?k. j <= k /\ NEXT_RISE M p B_TRUE (j,k)``,
   Q.EXISTS_TAC `j`
    THEN RW_TAC arith_ss 
     [SIMP_RULE arith_ss [] (Q.SPECL[`p`,`j`,`j`](GEN_ALL NEXT_RISE_TRUE))]);

val NEXT_RISE_LESS =
 store_thm
  ("NEXT_RISE_LESS",
   ``i <= j /\ NEXT_RISE M p c (i,j) =
      i <= j 
      /\
      (!k. i <= k /\ k < j ==> ~B_SEM M (getL M (PATH_EL p k)) c) 
      /\
      B_SEM M (getL M (PATH_EL p j)) c``,
   PROVE_TAC[NEXT_RISE]);

val FIRST_RISE_RESTN =
 store_thm
  ("FIRST_RISE_RESTN",
   ``!i j. FIRST_RISE M (RESTN p i) c j = NEXT_RISE M p c (i,i+j)``,
   Induct
    THEN RW_TAC arith_ss [FIRST_RISE, NEXT_RISE, RESTN_def,PATH_EL_RESTN]
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THEN `k - SUC i < j` by DECIDE_TAC
    THEN `(k - SUC i) + SUC i = k` by DECIDE_TAC
    THEN PROVE_TAC[]);

val NEXT_RISE_FIRST_RISE =
 store_thm
  ("FIRST_RISE_RESTN",
   ``!i j. i <= j 
           ==> 
           (NEXT_RISE M p c (i,j) = FIRST_RISE M (RESTN p i) c (j-i))``,
   RW_TAC std_ss []
    THEN `i + (j-i) = j` by DECIDE_TAC
    THEN PROVE_TAC [FIRST_RISE_RESTN]);

val NEXT_RISE_RESTN =
 store_thm
  ("NEXT_RISE_RESTN",
   ``!i j p. NEXT_RISE M (RESTN p i) c (j,k) = NEXT_RISE M p c (i+j,i+k)``,
   Induct
    THEN RW_TAC arith_ss [NEXT_RISE, RESTN_def,PATH_EL_RESTN]
    THEN RW_TAC arith_ss [NEXT_RISE_def]
    THEN `PATH_SEG (REST p) (i + j,i + k) = PATH_SEG (RESTN p 1) (i + j,i + k)`
         by PROVE_TAC[RESTN_def, DECIDE``SUC 0 = 1``]
    THEN RW_TAC arith_ss [PATH_SEG_RESTN, DECIDE``i + (j + 1) = j + SUC i``]);

(******************************************************************************
* Structural induction rule for FL formulas
******************************************************************************)
val fl_induct =
  (Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2 /\ B3)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`,`\(f,b). P f`,`\(r,f). P f`]
         (TypeBase.induction_of "fl")))));

(******************************************************************************
* Negated clocking of f with T! equal to clocking with T of F_NOT f:
* ~(p |=T!= f)  <==>  p |=T= !f
******************************************************************************)
val F_SEM_TRUE_WEAK_NOT_EQ =
 store_thm
  ("F_SEM_TRUE_WEAK_NOT_EQ",
   ``!f M p. 
      F_SEM M p (WEAK_CLOCK B_TRUE) (F_NOT f) = ~(F_SEM M p (STRONG_CLOCK B_TRUE) f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss [F_SEM_def]);

val F_SEM_TRUE_STRONG_NOT_EQ =
 store_thm
  ("F_SEM_TRUE_STRONG_NOT_EQ",
   ``!f M p. 
       F_SEM M p (STRONG_CLOCK B_TRUE) (F_NOT f) = ~(F_SEM M p (WEAK_CLOCK B_TRUE) f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss [F_SEM_def]);

val INFINITE_PL =
 store_thm
  ("INFINITE_PL",
   ``IS_INFINITE_PATH p ==> !n. PL p n``,
   PROVE_TAC[PL_def,NOT_IS_INFINITE_PATH]);

val PL0 =
 store_thm
  ("PL0",
   ``!p. PL p 0``,
   Cases
    THEN RW_TAC std_ss [PL_def,FINITE_PATH_NONEMPTY]);
   
val FORALL_NOT_PL =
 store_thm
  ("FORALL_NOT_PL",
   ``~!n. ~PL p n``,
   Cases_on `p`
    THEN ZAP_TAC arith_ss 
          [IS_INFINITE_PATH_def,IS_FINITE_PATH_def,
           PL_def,FINITE_PATH_NONEMPTY]);

val NEXT_TRUE_GE =
 store_thm
  ("NEXT_TRUE_GE",
   ``x' >= x /\ NEXT_RISE M p B_TRUE (x,x') = (x=x')``,
   EQ_TAC
    THEN RW_TAC arith_ss [NEXT_RISE_TRUE]
    THEN IMP_RES_TAC(DECIDE``x' >= x = x <= x'``)
    THEN FULL_SIMP_TAC std_ss [NEXT_RISE_TRUE]);

val PL_EXISTS_FORALL_LEMMA =
 store_thm
  ("PL_EXISTS_FORALL_LEMMA",
   ``IS_FINITE_PATH p 
     ==> 
     ((PL p x /\ !x'. PL p x' ==> ~(x' >= x)) = F)``,
   ZAP_TAC arith_ss 
    [PL_def,
     intLib.COOPER_PROVE``x < n /\ (!x'. x' < n ==> ~(x' >= x)) = F``]);

(******************************************************************************
* Strong clocking with T equal to weak clocking with T:
* (p |=T!= f  <==>  p |=T= f)
******************************************************************************)
local
val INIT_TAC =
 RW_TAC std_ss 
  [F_SEM_def,FIRST_RISE_TRUE,B_SEM_def,RES_FORALL,RES_EXISTS,IN_DEF,PL0,
   NEXT_RISE_TRUE_EXISTS,RESTN_def,IS_FINITE_PATH_RESTN];
val INFINITE_TAC =
 RW_TAC std_ss
  [F_SEM_def,FIRST_RISE_TRUE,B_SEM_def,
   RES_FORALL,RES_EXISTS,IN_DEF,RESTN_def,
   NEXT_RISE_TRUE_EXISTS,
   IS_FINITE_PATH_def,IS_INFINITE_PATH_def]
  THEN IMP_RES_TAC NOT_IS_INFINITE_PATH
  THEN IMP_RES_TAC INFINITE_PL
  THEN RW_TAC arith_ss 
        [intLib.COOPER_PROVE ``((?k. !l. ~(l >= k))=F) /\ ((?k. !l. ~(l > k))=F)``,
         NEXT_RISE_LEQ_TRUE_EXISTS,
         NEXT_TRUE_GE,PL_def,IS_FINITE_PATH_RESTN,
         IS_FINITE_PATH_def,IS_INFINITE_PATH_def];
in
val F_SEM_TRUE_EQ =
 store_thm
  ("F_SEM_TRUE_EQ",
   ``!f M p. 
      F_SEM M p (STRONG_CLOCK B_TRUE) f = F_SEM M p (WEAK_CLOCK B_TRUE) f``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC,
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      INIT_TAC,
      (* F_UNTIL(f1,f2) f *)
      Cases_on `p`
       THENL
        [INIT_TAC
          THEN RW_TAC arith_ss
                [PL_EXISTS_FORALL_LEMMA,FINITE_PATH_NONEMPTY,IS_FINITE_PATH_def]
          THEN EQ_TAC
          THEN RW_TAC std_ss []
          THENL
           [Q.EXISTS_TAC `x`
             THEN RW_TAC std_ss []
             THEN Cases_on `!x'. PL (FINITE_PATH p') x' ==> ~(x <= x')`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
             THEN PROVE_TAC[],
            Q.EXISTS_TAC `x`
             THEN ZAP_TAC std_ss []
             THEN RES_TAC
             THENL
              [PROVE_TAC[],
               `~(x'' <= x)` by PROVE_TAC[]
                THEN `F` by DECIDE_TAC],
            Q.EXISTS_TAC `x`
             THEN RW_TAC std_ss []
             THEN RES_TAC
             THEN`F` by DECIDE_TAC],
         INFINITE_TAC
          THEN RW_TAC std_ss [Cooper.COOPER_PROVE``(!x''. ~(x' <= x'')) = F``]],
      (* F_SUFFIX_IMP(s,f) *)
      INIT_TAC,
      (* F_STRONG_IMP(s1,s2) *)
      Cases_on `p`
       THENL
        [INIT_TAC 
          THEN RW_TAC arith_ss 
                [PL_EXISTS_FORALL_LEMMA,IS_FINITE_PATH_def,FINITE_PATH_NONEMPTY],
         INFINITE_TAC],
      (* F_WEAK_IMP(s1,s2) *)
      INIT_TAC 
       THEN EQ_TAC
       THEN RW_TAC std_ss [NEXT_RISE_TRUE_COR]
       THEN PROVE_TAC[],
      (* F_ABORT(f,b)) *)
      INIT_TAC 
       THEN PROVE_TAC[IS_FINITE_PATH_CAT],
      (* F_WEAK_CLOCK(f,c) *)
      INIT_TAC,
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC]);
end;

(******************************************************************************
* US_SEM M w r means "w is in the language of r" in the unclocked semantics
******************************************************************************)
val US_SEM_def =
 Define
  `(US_SEM M w (S_BOOL b) = ?l. (w = [l]) /\ B_SEM M l b)
   /\
   (US_SEM M w (S_CAT(r1,r2)) = 
     ?w1 w2. (w = w1 <> w2) /\ US_SEM M w1 r1 /\ US_SEM M w2 r2)
   /\
   (US_SEM M w (S_FUSION(r1,r2)) = 
     ?w1 w2 l. (w = w1 <> [l] <> w2) /\ 
               US_SEM M (w1<>[l]) r1 /\ US_SEM M ([l]<>w2) r2) 
   /\
   (US_SEM M w (S_OR(r1,r2)) = 
     US_SEM M w r1 \/ US_SEM M w r2) 
   /\
   (US_SEM M w (S_RIG_AND(r1,r2)) = 
     US_SEM M w r1 /\ US_SEM M w r2) 
   /\
   (US_SEM M w (S_FLEX_AND(r1,r2)) = 
     ?w1 w2. (w = w1 <> w2) /\ 
             ((US_SEM M w r1 /\ US_SEM M w1 r2) 
              \/
              (US_SEM M w r2 /\ US_SEM M w1 r1) ))
   /\
   (US_SEM M w (S_REPEAT r) = 
     ?wlist. (w = CONCAT wlist) /\ EVERY (\w. US_SEM M w r) wlist)`;

(******************************************************************************
* UF_SEM M p f means "p |= f"  in the unclocked semantics
* (F_WEAK_IMP case unfolded to make totality proof go through)
******************************************************************************)
val UF_SEM_def =
 Define
   `(UF_SEM M p (F_BOOL b) = 
      B_SEM M (L M (PATH_EL p 0)) b)
    /\
    (UF_SEM M p (F_NOT f) = 
      ~(UF_SEM M p f)) 
    /\
    (UF_SEM M p (F_AND(f1,f2)) = 
      UF_SEM M p f1 /\ UF_SEM M p f2)
    /\
    (UF_SEM M p (F_NEXT f) = 
      PL p 1 /\ UF_SEM M (RESTN p 1) f)
    /\
    (UF_SEM M p (F_UNTIL(f1,f2)) = 
      ?k :: PL p. UF_SEM M (RESTN p k) f2 /\
                  !j :: PL p. j < k ==> UF_SEM M (RESTN p j) f1)
    /\
    (UF_SEM M p (F_SUFFIX_IMP(r,f)) = 
      !j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r
                  ==>
                  UF_SEM M (RESTN p j) f)
    /\
    (UF_SEM M p (F_STRONG_IMP(r1,r2)) = 
      !j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1
                  ==>
                  ?k :: PL p. j <= k /\ US_SEM M (LHAT M (PATH_SEG p (j,k))) r2)
    /\
    (UF_SEM M p (F_WEAK_IMP(r1,r2)) = 
      !j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1 ==>
                  (?k :: PL p. j <= k /\ US_SEM M (LHAT M (PATH_SEG p (j,k))) r2) 
                  \/
                  !k :: PL p. 
                   j <= k ==> ?w. US_SEM M (LHAT M (PATH_SEG p (j,k)) <> w) r2)  
    /\
    (UF_SEM M p (F_ABORT (f,b)) =
      UF_SEM M p f 
      \/
      ?j :: PL p. 0 < j
        /\
        ?p'. UF_SEM M (RESTN p j) (F_BOOL b) /\ 
             UF_SEM M (PATH_CAT(PATH_SEG p (0,j-1),p')) f)`;

(******************************************************************************
* UF_SEM M p f means "p |= f"  in the unclocked semantics
* Derivation of folded equation
******************************************************************************)
val UF_SEM =
 store_thm
  ("UF_SEM",
   ``(UF_SEM M p (F_BOOL b) = 
       B_SEM M (L M (PATH_EL p 0)) b)
     /\
     (UF_SEM M p (F_NOT f) = 
       ~(UF_SEM M p f)) 
     /\
     (UF_SEM M p (F_AND(f1,f2)) = 
       UF_SEM M p f1 /\ UF_SEM M p f2)
     /\
     (UF_SEM M p (F_NEXT f) = 
       PL p 1 /\ UF_SEM M (RESTN p 1) f)
     /\
     (UF_SEM M p (F_UNTIL(f1,f2)) = 
       ?k :: PL p. UF_SEM M (RESTN p k) f2 /\
                   !j :: PL p. j < k ==> UF_SEM M (RESTN p j) f1)
     /\
     (UF_SEM M p (F_SUFFIX_IMP(r,f)) = 
       !j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r
                   ==>
                   UF_SEM M (RESTN p j) f)
     /\
     (UF_SEM M p (F_STRONG_IMP(r1,r2)) = 
       !j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1
                   ==>
                   ?k :: PL p. j <= k /\ US_SEM M (LHAT M (PATH_SEG p (j,k))) r2)
     /\
    (UF_SEM M p (F_WEAK_IMP(r1,r2)) = 
       !j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1 ==>
                   (?k :: PL p. j <= k /\ US_SEM M (LHAT M (PATH_SEG p (j,k))) r2) 
                   \/  
                    !k :: PL p. 
                      j <= k ==> ?w. US_SEM M (LHAT M (PATH_SEG p (j,k)) <> w) r2)  
     /\
     (UF_SEM M p (F_ABORT (f,b)) =
       UF_SEM M p f 
       \/
       ?j :: PL p. 0 < j 
        /\
        ?p'. UF_SEM M (RESTN p j) (F_BOOL b) /\ 
             UF_SEM M (PATH_CAT(PATH_SEG p (0,j-1),p')) f)``,
   SIMP_TAC std_ss [UF_SEM_def]);

(******************************************************************************
* Structural induction rule for SEREs
******************************************************************************)
val sere_induct =
  (Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2 /\ B3)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(r1,r2). P r1 /\ P r2`,`\(r,b). P r`]
         (TypeBase.induction_of "sere")))));

(******************************************************************************
* S_CLOCK_FREE r means r contains no clocking statements
******************************************************************************)
val S_CLOCK_FREE_def =
 Define
  `(S_CLOCK_FREE (S_BOOL b)          = T)
   /\
   (S_CLOCK_FREE (S_CAT(r1,r2))      =  S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (S_CLOCK_FREE (S_FUSION(r1,r2))   = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_OR(r1,r2))       = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_RIG_AND(r1,r2))  = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_FLEX_AND(r1,r2)) = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_REPEAT r)        = S_CLOCK_FREE r)
   /\
   (S_CLOCK_FREE (S_CLOCK v)         = F)`;

(******************************************************************************
* Proof that if S_CLOCK_FREE r then the unclocked semantics of
* a SERE r is the same as the clocked semantics with clock equal to T
******************************************************************************)

val S_SEM_TRUE_LEMMA =
 store_thm
  ("S_SEM_TRUE_LEMMA",
   ``!r M w. 
      S_CLOCK_FREE r
      ==>
      (S_SEM M w B_TRUE r = US_SEM M w r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_SEM_def, US_SEM_def, S_CLOCK_FREE_def]
    THEN RW_TAC std_ss 
          [B_SEM_def,CONJ_ASSOC,LENGTH1,
           intLib.COOPER_PROVE ``n >= 1 /\ (!i. ~(1 <= i) \/ ~(i < n)) = (n = 1)``]
       THEN EQ_TAC
       THEN RW_TAC list_ss [LENGTH]
       THEN RW_TAC list_ss [LENGTH]
       THEN FULL_SIMP_TAC list_ss [LENGTH]);

val S_SEM_TRUE =
 store_thm
  ("S_SEM_TRUE",
   ``S_CLOCK_FREE r ==> (S_SEM M w B_TRUE r = US_SEM M w r)``,
   Cases_on `M` THEN Cases_on `r'` THEN Cases_on `r''` THEN Cases_on `r'`
    THEN RW_TAC std_ss [S_SEM_TRUE_LEMMA]);

(******************************************************************************
* F_CLOCK_FREE f means f contains no clocking statements
******************************************************************************)
val F_CLOCK_FREE_def =
 Define
  `(F_CLOCK_FREE (F_BOOL b)            = T)
   /\
   (F_CLOCK_FREE (F_NOT f)             = F_CLOCK_FREE f) 
   /\
   (F_CLOCK_FREE (F_AND(f1,f2))        = F_CLOCK_FREE f1 /\ F_CLOCK_FREE f2)
   /\
   (F_CLOCK_FREE (F_NEXT f)            = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_UNTIL(f1,f2))      = F_CLOCK_FREE f1 /\ F_CLOCK_FREE f2)
   /\
   (F_CLOCK_FREE (F_SUFFIX_IMP(r,f))   = F_CLOCK_FREE f /\ S_CLOCK_FREE r)
   /\
   (F_CLOCK_FREE (F_STRONG_IMP(r1,r2)) = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (F_CLOCK_FREE (F_WEAK_IMP(r1,r2))   = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (F_CLOCK_FREE (F_ABORT (f,b))       = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_WEAK_CLOCK v)      = F)
   /\
   (F_CLOCK_FREE (F_STRONG_CLOCK v)    = F)`;

(******************************************************************************
* If F_CLOCK_FREE f then the unclocked semantics of an
* FL formula f is the same as the clocked semantics with clock equal to T!
* (i.e. strongly clocked)
******************************************************************************)
local
val INIT_TAC =
 RW_TAC arith_ss 
  [F_SEM_def,UF_SEM_def,F_CLOCK_FREE_def,FIRST_RISE_TRUE,RESTN_def,
   PL_def,RES_FORALL_DEF,RES_EXISTS_DEF,IN_DEF,FINITE_PATH_NONEMPTY,
   DECIDE``0 < n-1 = n > 1``,DECIDE``n >= 0``,DECIDE``0 <= n``];
in
val F_SEM_STRONG_FREE_TRUE_LEMMA =
 store_thm
  ("F_SEM_STRONG_FREE_TRUE_LEMMA",
   ``!f M p. 
      F_CLOCK_FREE f
      ==>
      (F_SEM M p (STRONG_CLOCK B_TRUE) f = UF_SEM M p f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC THEN PROVE_TAC[F_SEM_TRUE_EQ],
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      INIT_TAC
       THEN EQ_TAC
       THEN RW_TAC arith_ss [DECIDE``0 < x = 1 <= x``]
       THENL
        [RES_TAC
          THEN DECIDE_TAC,
         IMP_RES_TAC NEXT_RISE_TRUE
          THEN RW_TAC std_ss [],
         Q.EXISTS_TAC `1`
          THEN RW_TAC arith_ss [NEXT_RISE_TRUE]],
      (* F_UNTIL(f1,f2) f *)
      INIT_TAC 
       THEN RW_TAC std_ss 
             [DECIDE ``A /\ B /\ C /\ D = A /\ (B /\ C) /\ D``,
              Cooper.COOPER_PROVE``(!k. ~(x <= k) \/ ~(k < x')) = x' <= x``,
              NEXT_RISE_LESS,B_SEM_def]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [`x=x'` by DECIDE_TAC
          THEN RW_TAC arith_ss []
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN IMP_RES_TAC(DECIDE``m <= n ==> n <= m ==> (m=n)``)
          THEN PROVE_TAC[],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [FINITE_PATH_NONEMPTY]
          THEN PROVE_TAC[DECIDE``m<=m``]],
      (* F_SUFFIX_IMP(s,f) *)
      INIT_TAC THEN RW_TAC std_ss [S_SEM_TRUE],
      (* F_STRONG_IMP(s1,s2) *)
      INIT_TAC 
       THEN RW_TAC std_ss [S_SEM_TRUE,NEXT_TRUE_GE,DECIDE``m <= n = n >= m``] 
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[],
      (* F_WEAK_IMP(s1,s2) *)
      INIT_TAC 
       THEN RW_TAC std_ss [S_SEM_TRUE,NEXT_TRUE_GE,DECIDE``m <= n = n >= m``] 
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[],
      (* F_ABORT(f,b)) *)
      INIT_TAC THEN RW_TAC std_ss [B_SEM_def],
      (* F_WEAK_CLOCK(f,c) *)
      INIT_TAC,
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC]);
end;

(******************************************************************************
* Rules for compiling clocked SEREs to unclocked SEREs
* (from B.1, page 66, of Sugar 2.0 Accellera document)
******************************************************************************)
val S_CLOCK_COMP_def =
 Define
  `(S_CLOCK_COMP c (S_BOOL b) = 
     (S_CAT (S_REPEAT (S_BOOL (B_NOT c)),S_BOOL(B_AND(c, b)))))
   /\
   (S_CLOCK_COMP c (S_CAT(r1,r2)) =  
     S_CAT(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_FUSION(r1,r2)) = 
     S_FUSION(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_OR(r1,r2)) = 
     S_OR(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_RIG_AND(r1,r2))  = 
     S_RIG_AND(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_FLEX_AND(r1,r2)) = 
     S_FLEX_AND(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_REPEAT r) = 
     S_REPEAT(S_CLOCK_COMP c r))
   /\
   (S_CLOCK_COMP c (S_CLOCK(r, c1)) = 
     S_CLOCK_COMP c1 r)`;

(******************************************************************************
* S_CLOCK_COMP c r contains no clocked SEREs
******************************************************************************)
val S_CLOCK_COMP_CLOCK_FREE =
 store_thm
  ("S_CLOCK_COMP_CLOCK_FREE",
   ``!r c. S_CLOCK_FREE(S_CLOCK_COMP c r)
           /\
           S_CLOCK_FREE(S_CLOCK_COMP c r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss 
          [S_CLOCK_FREE_def,S_CLOCK_COMP_def]);

(******************************************************************************
* Some ad hoc lemmas followed by a gross proof that S_CLOCK_COMP works
******************************************************************************)

val LENGTH_NIL_LEMMA =
 store_thm
  ("LENGTH_NIL_LEMMA",
   ``LENGTH l >= 1 ==> ~(l = [])``,
   RW_TAC list_ss [DECIDE``m>=1 = ~(m=0)``,LENGTH_NIL]);

val EL_BUTLAST =
 store_thm
  ("EL_BUTLAST",
   ``!w n. n < PRE(LENGTH w) ==> (EL n (BUTLAST w) = EL n w)``,
   Induct
    THEN RW_TAC list_ss [FRONT_DEF]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]);

val EL_PRE_LENGTH =
 store_thm
  ("EL_PRE_LENGTH",
   ``!w. LENGTH w >= 1 ==> (EL (LENGTH w - 1) w = LAST w)``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `LENGTH w`
    THEN RW_TAC list_ss [EL,LAST_DEF]
    THEN IMP_RES_TAC LENGTH_NIL
    THEN IMP_RES_TAC(SIMP_CONV list_ss [] ``LENGTH [] = SUC n``)
    THEN RES_TAC
    THEN FULL_SIMP_TAC arith_ss []);
 
val EVERY_EL_SINGLETON_LENGTH =
 store_thm
  ("EVERY_EL_SINGLETON_LENGTH",
   ``!wlist P.
      (!n. n < LENGTH wlist ==> ?l. (EL n wlist = [l]) /\ P l)
      ==>
      (LENGTH(CONCAT wlist) = LENGTH wlist)``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def,APPEND_INFIX_def]
    THEN ASSUM_LIST
          (fn thl => 
            ASSUME_TAC(Q.GEN `n` (SIMP_RULE list_ss [EL] (Q.SPEC `SUC n` (el 1 thl)))))
    THEN ASSUM_LIST
          (fn thl => 
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [EL] (Q.SPEC `0` (el 2 thl))))
    THEN RES_TAC
    THEN RW_TAC list_ss []);

val EVERY_EL_SINGLETON =
 store_thm
  ("EVERY_EL_SINGLETON",
   ``!wlist P.
      (!n. n < LENGTH wlist ==> ?l. (EL n wlist = [l]) /\ P l)
      ==>
      (CONCAT wlist = MAP HD wlist)``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def,APPEND_INFIX_def]
    THEN ASSUM_LIST
          (fn thl => 
            ASSUME_TAC(Q.GEN `n` (SIMP_RULE list_ss [EL] (Q.SPEC `SUC n` (el 1 thl)))))
    THEN ASSUM_LIST
          (fn thl => 
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [EL] (Q.SPEC `0` (el 2 thl))))
    THEN RES_TAC
    THEN RW_TAC list_ss []);

(******************************************************************************
* w |=c= r  <==>  w |= (S_CLOCK_COMP c r)
******************************************************************************)
val S_CLOCK_COMP_ELIM =
 store_thm
  ("S_CLOCK_COMP_ELIM",
   ``!r M w c. S_SEM M w c r = US_SEM M w (S_CLOCK_COMP c r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def,APPEND_INFIX_def]   
    THEN RW_TAC list_ss [EVERY_EL]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN RW_TAC list_ss [LENGTH_APPEND,DECIDE``m + SUC 0 - 1 = m``]
    THENL
     [Q.EXISTS_TAC `BUTLAST w`
       THEN Q.EXISTS_TAC `[LAST w]` 
       THEN RW_TAC list_ss []
       THEN RW_TAC list_ss [APPEND_BUTLAST_LAST, LENGTH_NIL_LEMMA]
       THENL
        [Q.EXISTS_TAC `MAP(\l.[l])(BUTLAST w)`
          THEN RW_TAC list_ss [CONCAT_MAP_SINGLETON]
          THEN Q.EXISTS_TAC `HD(EL n (MAP (\l. [l]) (BUTLAST w)))`
          THEN RW_TAC list_ss [HD_EL_MAP,EL_MAP]
          THEN IMP_RES_TAC LENGTH_NIL_LEMMA
          THEN IMP_RES_TAC LENGTH_BUTLAST
          THEN IMP_RES_TAC
                (DECIDE``n < m ==> (m = PRE p) ==> (1 <= SUC n /\ SUC n < p)``)
          THEN RES_TAC
          THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE arith_ss [])
          THEN RW_TAC list_ss [EL_BUTLAST],
         IMP_RES_TAC EL_PRE_LENGTH
          THEN POP_ASSUM(fn th => RW_TAC list_ss [GSYM th])],
      IMP_RES_TAC
       (SIMP_RULE std_ss []
        (Q.SPECL
          [`wlist`,`\l. B_SEM (M :'b # 'c # 'd # ('a -> bool) # 'e) l (B_NOT c)`]
          (INST_TYPE[``:'a``|->``:'a->bool``]EVERY_EL_SINGLETON_LENGTH)))
       THEN FULL_SIMP_TAC list_ss [LENGTH_APPEND]
       THEN IMP_RES_TAC(DECIDE ``1 <= i ==> i < m + SUC 0 ==> i - 1 < m``)
       THEN RW_TAC list_ss [EL_APPEND1]
       THEN IMP_RES_TAC
             (SIMP_RULE std_ss []
              (Q.SPECL
                [`wlist`,`\l. B_SEM (M :'b # 'c # 'd # ('a -> bool) # 'e) l (B_NOT c)`]
                (INST_TYPE[``:'a``|->``:'a->bool``]EVERY_EL_SINGLETON)))
       THEN RW_TAC list_ss [EL_MAP,LENGTH_MAP]
       THEN RES_TAC
       THEN IMP_RES_TAC EQ_SINGLETON
       THEN RW_TAC list_ss [],
      IMP_RES_TAC
       (SIMP_RULE std_ss []
        (Q.SPECL
          [`wlist`,`\l. B_SEM (M :'b # 'c # 'd # ('a -> bool) # 'e) l (B_NOT c)`]
          (INST_TYPE[``:'a``|->``:'a->bool``]EVERY_EL_SINGLETON_LENGTH)))
       THEN RW_TAC list_ss [EL_APPEND2]]);

(******************************************************************************
* Definition of falsity
******************************************************************************)

val B_FALSE =
 prove
  (``B_SEM M l (B_NOT B_TRUE) = F``,
   RW_TAC std_ss [B_SEM_def]);

(******************************************************************************
* Some abbreviations needed for definition of F_CLOCK_COMP
******************************************************************************)

val F_U_CLOCK_def =
 Define
  `F_U_CLOCK c f = F_UNTIL(F_BOOL(B_NOT c),F_AND(F_BOOL c, f))`;

val UF_SEM_F_U_CLOCK =
 store_thm
  ("UF_SEM_F_U_CLOCK",
   ``UF_SEM M p (F_U_CLOCK c f) =
      ?i :: PL p. FIRST_RISE M p c i /\ UF_SEM M (RESTN p i) f``,
   Cases_on `p`
    THEN RW_TAC arith_ss 
          [F_U_CLOCK_def,PATH_EL_RESTN,L_def,
           UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
           RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN Q.EXISTS_TAC `x`
    THEN RW_TAC std_ss []
    THEN`j < PATH_LENGTH (FINITE_PATH p')` by DECIDE_TAC
    THEN PROVE_TAC[]);

(******************************************************************************
* UF_SEM M p (F_U_CLOCK c (F_U_CLOCK c f)) = UF_SEM M p (F_U_CLOCK c f)
******************************************************************************)
local

val INFINITE_UF_U_CLOCK_UF_U_CLOCK =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     (UF_SEM M p (F_U_CLOCK c (F_U_CLOCK c f)) = UF_SEM M p (F_U_CLOCK c f))``,
   RW_TAC arith_ss 
    [F_U_CLOCK_def, UF_SEM,RES_FORALL,RES_EXISTS,PL_def,IN_DEF,
     PATH_EL_RESTN,RESTN_RESTN,IS_FINITE_PATH_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `x+x'`
       THEN RW_TAC arith_ss []
       THEN Cases_on `x'' < x`
       THEN RW_TAC arith_ss []
       THEN `x'' - x < x'` by DECIDE_TAC
       THEN `x + (x'' - x) = x''` by DECIDE_TAC
       THEN PROVE_TAC[],
      Q.EXISTS_TAC `x`
       THEN RW_TAC arith_ss []
       THEN Q.EXISTS_TAC `0`
       THEN RW_TAC arith_ss [ADD_CLAUSES]]);

val FINITE_UF_U_CLOCK_UF_U_CLOCK =
 prove
  (``IS_FINITE_PATH p
     ==>
     (UF_SEM M p (F_U_CLOCK c (F_U_CLOCK c f)) = UF_SEM M p (F_U_CLOCK c f))``,
   RW_TAC arith_ss 
    [F_U_CLOCK_def, UF_SEM,RES_FORALL,RES_EXISTS,PL_def,IN_DEF,
     PATH_EL_RESTN,RESTN_RESTN,IS_FINITE_PATH_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [`PATH_LENGTH(RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `x + x' < PATH_LENGTH p` by DECIDE_TAC
       THEN Q.EXISTS_TAC `x+x'`
       THEN RW_TAC arith_ss []
       THEN Cases_on `x'' < x`
       THEN RW_TAC arith_ss []
       THEN `x'' - x < x'` by DECIDE_TAC
       THEN `x + (x'' - x) = x''` by DECIDE_TAC
       THEN `x'' - x < PATH_LENGTH (RESTN p x)` by DECIDE_TAC
       THEN PROVE_TAC[],
      Q.EXISTS_TAC `x`
       THEN RW_TAC arith_ss []
       THEN Q.EXISTS_TAC `0`
       THEN RW_TAC arith_ss [FINITE_PATH_NONEMPTY,ADD_CLAUSES,PATH_LENGTH_RESTN]]);
in

val UF_U_CLOCK_UF_U_CLOCK =
 prove
  (``UF_SEM M p (F_U_CLOCK c (F_U_CLOCK c f)) = UF_SEM M p (F_U_CLOCK c f)``,
   Cases_on `IS_FINITE_PATH p`
    THEN RW_TAC std_ss [INFINITE_UF_U_CLOCK_UF_U_CLOCK,FINITE_UF_U_CLOCK_UF_U_CLOCK]);

end;

val F_CLOCK_FREE_F_U_CLOCK  =
 store_thm
  ("F_CLOCK_FREE_F_U_CLOCK",
   ``!f. F_CLOCK_FREE f ==> !c. F_CLOCK_FREE(F_U_CLOCK c f)``,
   RW_TAC std_ss [F_U_CLOCK_def,F_CLOCK_FREE_def]);

(******************************************************************************
* F_U_CLOCK_INIT_LEMMA =
*     |- !i j::PL p.
*          FIRST_RISE M p c i /\ j <= i ==>
*          (UF_SEM M (RESTN p j) (F_U_CLOCK c f) = UF_SEM M p (F_U_CLOCK c f))
******************************************************************************)
local

val F_U_CLOCK_INFINITE_INIT_LEMMA =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     !i i1 :: PL p.
      FIRST_RISE M p c i /\ i1 <= i
      ==>
      (UF_SEM M (RESTN p i1) (F_U_CLOCK c f) = UF_SEM M p (F_U_CLOCK c f))``,
   RW_TAC arith_ss 
    [FIRST_RISE,F_U_CLOCK_def,UF_SEM,RES_FORALL,RES_EXISTS,B_SEM_def,
     RESTN_RESTN,PATH_EL_RESTN,L_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `x' + x''`
       THEN RW_TAC arith_ss []
       THEN Cases_on `x''' < x`
       THEN RW_TAC arith_ss []
       THEN IMP_RES_TAC(DECIDE``x' <= x ==> x''' < x' + x'' ==> ~(x''' < x) ==> x''' - x' < x''``)
       THEN IMP_RES_TAC(DECIDE``x' <= x ==> x''' < x' + x'' ==> ~(x''' < x) ==> (x' + (x''' - x') = x''')``)
       THEN PROVE_TAC[],
      Q.EXISTS_TAC `x'' - x'`
       THEN Cases_on `x'' < x`
       THEN RES_TAC
       THEN RW_TAC arith_ss [DECIDE``x' <= x ==> ~(x'' < x) ==> (x' + (x'' - x') = x'')``]]);

val F_U_CLOCK_FINITE_INIT_LEMMA =
 prove
  (``IS_FINITE_PATH p
     ==>
     !i i1 :: PL p.
      FIRST_RISE M p c i /\ i1 <= i
      ==>
      (UF_SEM M (RESTN p i1) (F_U_CLOCK c f) = UF_SEM M p (F_U_CLOCK c f))``,
   RW_TAC arith_ss 
    [FIRST_RISE,F_U_CLOCK_def,UF_SEM,RES_FORALL,RES_EXISTS,B_SEM_def,
     RESTN_RESTN,PATH_EL_RESTN,L_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `x' + x''`
       THEN RW_TAC arith_ss []
       THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'` by RW_TAC arith_ss [PATH_LENGTH_RESTN]
       THENL
        [DECIDE_TAC,
         Cases_on `x''' < x`
          THEN RW_TAC arith_ss []
          THEN `x''' - x' < PATH_LENGTH (RESTN p x')` by DECIDE_TAC
          THEN `x''' - x' < x''` by DECIDE_TAC
          THEN `x' + (x''' - x') = x'''` by DECIDE_TAC
          THEN PROVE_TAC[]],
      Q.EXISTS_TAC `x'' - x'`
       THEN Cases_on `x'' < x`
       THEN RES_TAC
       THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'` by RW_TAC arith_ss [PATH_LENGTH_RESTN]
       THEN `x' + (x'' - x') = x''` by DECIDE_TAC
       THEN `x'' - x' < PATH_LENGTH p - x'` by DECIDE_TAC
       THEN RW_TAC std_ss []
       THEN `x' + x''' < PATH_LENGTH p` by DECIDE_TAC
       THEN `x' + x''' < x''` by DECIDE_TAC
       THEN PROVE_TAC[]]);

in

val F_U_CLOCK_INIT_LEMMA =
 store_thm
  ("F_U_CLOCK_INIT_LEMMA",
   ``!i j :: PL p.
      FIRST_RISE M p c i /\ j <= i
      ==>
      (UF_SEM M (RESTN p j) (F_U_CLOCK c f) = UF_SEM M p (F_U_CLOCK c f))``,
   Cases_on `IS_FINITE_PATH p`
    THEN RW_TAC std_ss [F_U_CLOCK_INFINITE_INIT_LEMMA,F_U_CLOCK_FINITE_INIT_LEMMA]);

end;

(******************************************************************************
* F_U_CLOCK_NEXT_LEMMA =
*     |- !i j k::PL p.
*          NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j ==>
*          (UF_SEM M (RESTN p k) (F_U_CLOCK c f) =
*           UF_SEM M (RESTN p j) (F_U_CLOCK c f)) : thm
******************************************************************************)
local

val F_U_CLOCK_INFINITE_NEXT_LEMMA =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     !i j k :: PL p.
      NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j
      ==>
      (UF_SEM M (RESTN p k) (F_U_CLOCK c f) = UF_SEM M (RESTN p j) (F_U_CLOCK c f))``,
   ONCE_REWRITE_TAC[PROVE
                     [DECIDE``i <= k /\ k <= j==> i <= j``]
                     ``P /\ i <= k /\ k <= j = ((i <= j) /\ P) /\ i <= k /\ k <= j``]
    THEN RW_TAC arith_ss 
        [NEXT_RISE_LESS,F_U_CLOCK_def,UF_SEM,RES_FORALL,RES_EXISTS,B_SEM_def,
         RESTN_RESTN,PATH_EL_RESTN,L_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Cases_on `x <= x'' + x''' /\ x'' + x''' < x'`
       THEN ZAP_TAC arith_ss []
       THEN `x' + (x'' + x''' - x') = x'' + x''' ` by DECIDE_TAC
       THEN Q.EXISTS_TAC `x'' + x''' - x'`
       THEN RW_TAC arith_ss []
       THEN `x' + x'''' - x'' < x'''` by DECIDE_TAC
       THEN `x'' + (x' + x'''' - x'') = x' + x''''` by DECIDE_TAC
       THEN PROVE_TAC[],
      Q.EXISTS_TAC `x' + x''' - x''`
       THEN ZAP_TAC std_ss []
       THEN `x'' + (x' + x''' - x'') = x' + x'''` by DECIDE_TAC
       THEN ZAP_TAC std_ss []
       THEN Cases_on `(x <= x'' + x'''' /\ x'' + x'''' < x')`
       THEN RW_TAC arith_ss []
       THEN `x'' + x'''' - x' < x'''` by DECIDE_TAC
       THEN `x' + (x'' + x'''' - x') = x'' + x''''` by DECIDE_TAC
       THEN PROVE_TAC[]]);

val F_U_CLOCK_FINITE_NEXT_LEMMA =
 prove
  (``IS_FINITE_PATH p
     ==>
     !i j k :: PL p.
      NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j
      ==>
      (UF_SEM M (RESTN p k) (F_U_CLOCK c f) = UF_SEM M (RESTN p j) (F_U_CLOCK c f))``,
   ONCE_REWRITE_TAC[PROVE
                     [DECIDE``i <= k /\ k <= j==> i <= j``]
                     ``P /\ i <= k /\ k <= j = ((i <= j) /\ P) /\ i <= k /\ k <= j``]
    THEN RW_TAC arith_ss 
        [NEXT_RISE_LESS,F_U_CLOCK_def,UF_SEM,RES_FORALL,RES_EXISTS,B_SEM_def,
         RESTN_RESTN,PATH_EL_RESTN,L_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Cases_on `x <= x'' + x''' /\ x'' + x''' < x'`
       THEN ZAP_TAC arith_ss []
       THEN RW_TAC arith_ss [PATH_LENGTH_RESTN]
       THEN `x' + (x'' + x''' - x') = x'' + x''' ` by DECIDE_TAC
       THEN `PATH_LENGTH (RESTN p x'') = PATH_LENGTH p - x''` 
            by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `x'' + x''' < PATH_LENGTH p` by DECIDE_TAC
       THEN Q.EXISTS_TAC `x'' + x''' - x'`
       THEN RW_TAC arith_ss []
       THEN `x' + x''''' - x'' < PATH_LENGTH (RESTN p x'')` by DECIDE_TAC
       THEN `x' + x''''' - x'' < x'''` by DECIDE_TAC
       THEN `x'' + (x' + x''''' - x'') = x' + x'''''` by DECIDE_TAC
       THEN PROVE_TAC[],
      `PATH_LENGTH (RESTN p x'') = PATH_LENGTH p - x''` 
        by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'` 
            by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `x'' + (x' + x''' - x'') = x' + x'''` by DECIDE_TAC
       THEN Q.EXISTS_TAC `x' + x''' - x''`
       THEN ZAP_TAC std_ss []
       THEN Cases_on `(x <= x'' + x'''' /\ x'' + x'''' < x')`
       THEN RW_TAC arith_ss []
       THEN `x'' + x'''' - x' < PATH_LENGTH (RESTN p x')` by DECIDE_TAC
       THEN `x'' + x'''' - x' < x'''` by DECIDE_TAC
       THEN `x' + (x'' + x'''' - x') = x'' + x''''` by DECIDE_TAC
       THEN PROVE_TAC[]]);

in

val F_U_CLOCK_NEXT_LEMMA =
 store_thm
  ("F_U_CLOCK_NEXT_LEMMA",
   ``!i j k :: PL p.
      NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j
      ==>
      (UF_SEM M (RESTN p k) (F_U_CLOCK c f) = UF_SEM M (RESTN p j) (F_U_CLOCK c f))``,
   Cases_on `IS_FINITE_PATH p`
    THEN RW_TAC std_ss [F_U_CLOCK_INFINITE_NEXT_LEMMA,F_U_CLOCK_FINITE_NEXT_LEMMA]);

end;

val F_OR_def =
 Define
  `F_OR(f1,f2) = F_NOT(F_AND(F_NOT f1, F_NOT f2))`;

val UF_SEM_F_OR =
 store_thm
  ("UF_SEM_F_OR",
   ``UF_SEM M p (F_OR(f1,f2)) = UF_SEM M p f1 \/ UF_SEM M p f2``,
   RW_TAC std_ss [UF_SEM,F_OR_def]);

val F_F_def =
 Define
  `F_F f = F_UNTIL(F_BOOL B_TRUE, f)`;

val UF_SEM_F_F =
 store_thm
  ("UF_SEM_F_F",
   ``UF_SEM M p (F_F f) = ?i :: PL p. UF_SEM M (RESTN p i) f``,
   RW_TAC std_ss [UF_SEM,F_F_def,B_SEM_def,RES_FORALL]);
      
val F_G_def =
 Define
  `F_G f = F_NOT(F_F(F_NOT f))`;

val UF_SEM_F_G =
 store_thm
  ("UF_SEM_F_G",
   ``UF_SEM M p (F_G f) = !i :: PL p. UF_SEM M (RESTN p i) f``,
   RW_TAC std_ss [UF_SEM,F_G_def,UF_SEM_F_F,RES_EXISTS,RES_FORALL]
    THEN PROVE_TAC[]);

val UF_SEM_F_F_G =
 store_thm
  ("UF_SEM_F_F_G",
   ``UF_SEM M p (F_F(F_G f)) = 
     ?i :: PL p. !j :: PL(RESTN p i). UF_SEM M (RESTN p (i+j)) f``,
   RW_TAC std_ss [UF_SEM,F_G_def,UF_SEM_F_F,RES_EXISTS,RES_FORALL,RESTN_RESTN]
    THEN PROVE_TAC[]);

val UF_SEM_F_G_F =
 store_thm
  ("UF_SEM_F_G_F",
   ``UF_SEM M p (F_G(F_F f)) = 
     !i :: PL p. ?j :: PL(RESTN p i). UF_SEM M (RESTN p (i+j)) f``,
   RW_TAC std_ss [UF_SEM,F_G_def,UF_SEM_F_F,RES_EXISTS,RES_FORALL,RESTN_RESTN]
    THEN PROVE_TAC[]);

val UF_SEM_NOT_F_G =
 store_thm
  ("UF_SEM_NOT_F_G",
   ``~(UF_SEM M p (F_G f)) = 
       ?i :: PL p. UF_SEM M (RESTN p i) (F_NOT f)``,
   RW_TAC std_ss [UF_SEM,F_G_def,UF_SEM_F_F,RES_EXISTS,RES_FORALL]
    THEN PROVE_TAC[]);

val F_WEAK_NEXT_def =
 Define `F_WEAK_NEXT f = F_NOT(F_NEXT(F_NOT f))`;

val UF_SEM_WEAK_NEXT =
 store_thm
  ("UF_SEM_WEAK_NEXT",
   ``UF_SEM M p (F_WEAK_NEXT f) = PL p 1 ==> UF_SEM M p (F_NEXT f)``,
   RW_TAC std_ss [UF_SEM,F_WEAK_NEXT_def]
    THEN PROVE_TAC[]);

val WOP_EQ =
 prove
  (``!P. (?n. P n) = ?n. P n /\ !m. m < n ==> ~P m``,
   PROVE_TAC[WOP]);

val WOP_Inst_Lemma =
 SIMP_RULE std_ss []
  (ISPEC
  ``\(x :num).
        x IN PL (p :'e path) /\
        ~UF_SEM (M :'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool))
           (RESTN p x) (f :'d fl)``
  WOP_EQ);

val UF_SEM_WOP_NOT_F_G =
 store_thm
  ("UF_WOP_SEM_NOT_F_G",
   ``~(UF_SEM M p (F_G f)) = 
       ?i :: PL p. UF_SEM M (RESTN p i) (F_NOT f) /\
                   !j :: PL p. j < i ==> UF_SEM M (RESTN p j) f``,
   RW_TAC std_ss [UF_SEM,F_G_def,UF_SEM_F_F,RES_EXISTS,RES_FORALL]
    THEN EQ_TAC
    THEN PROVE_TAC[WOP_Inst_Lemma]);

val F_W_def =
 Define
  `F_W(f1,f2) = F_OR(F_UNTIL(f1,f2), F_G f1)`;

val UF_SEM_F_W =
 store_thm
  ("UF_SEM_F_W",
   ``UF_SEM M p (F_W(f1,f2)) = UF_SEM M p (F_UNTIL(f1,f2)) \/ UF_SEM M p (F_G f1)``,
   RW_TAC std_ss [UF_SEM,F_W_def,UF_SEM_F_OR]);

val F_W_CLOCK_def =
 Define
  `F_W_CLOCK c f = F_W(F_BOOL(B_NOT c),F_AND(F_BOOL c, f))`;

val UF_SEM_F_W_CLOCK =
 store_thm
  ("UF_SEM_F_W_CLOCK",
   ``UF_SEM M p (F_W_CLOCK c f) = 
      UF_SEM M p (F_U_CLOCK c f) \/ !i::PL p.~UF_SEM M (RESTN p i) (F_BOOL c)``,
   RW_TAC std_ss 
    [F_U_CLOCK_def, F_W_CLOCK_def, UF_SEM_F_W, UF_SEM_F_G,B_SEM_def,UF_SEM_def]);


(******************************************************************************
* F_W_CLOCK_NEXT_LEMMA =
*     |- !i j k::PL p.
*          NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j ==>
*          (UF_SEM M (RESTN p k) (F_W_CLOCK c f) =
*           UF_SEM M (RESTN p j) (F_W_CLOCK c f)) : thm
******************************************************************************)
local

val INFINITE_F_W_CLOCK_NEXT_LEMMA =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     !i j k :: PL p.
      NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j
      ==>
      (UF_SEM M (RESTN p k) (F_W_CLOCK c f) = UF_SEM M (RESTN p j) (F_W_CLOCK c f))``,
    RW_TAC std_ss [UF_SEM_F_W_CLOCK,RES_FORALL,PL_def,IN_DEF,RESTN_RESTN,
                   IS_FINITE_PATH_RESTN,L_def]
     THEN EQ_TAC
     THEN RW_TAC std_ss []
     THENL
      [`UF_SEM M (RESTN p x') (F_U_CLOCK c f)`
        by PROVE_TAC[SIMP_RULE std_ss [RES_FORALL,PL_def,IN_DEF]F_U_CLOCK_NEXT_LEMMA]
        THEN PROVE_TAC[],
       DISJ2_TAC
        THEN RW_TAC std_ss []
        THEN POP_ASSUM(ASSUME_TAC o Q.SPEC `x' + x''' - x''`)
        THEN `x'' + (x' + x''' - x'') = x' + x'''` by DECIDE_TAC
        THEN PROVE_TAC[],
       `UF_SEM M (RESTN p x'') (F_U_CLOCK c f)`
        by PROVE_TAC[SIMP_RULE std_ss [RES_FORALL,PL_def,IN_DEF]F_U_CLOCK_NEXT_LEMMA]
        THEN PROVE_TAC[],
       DISJ2_TAC
        THEN RW_TAC arith_ss []
        THEN FULL_SIMP_TAC arith_ss [UF_SEM,PATH_EL_RESTN]
        THEN `x <= x'` by DECIDE_TAC
        THEN ASSUM_LIST
              (fn thl => 
                STRIP_ASSUME_TAC
                 (SIMP_RULE std_ss [NEXT_RISE_LESS] (CONJ(el 1 thl)(el 5 thl))))
        THEN `x <= x'' + x'''` by DECIDE_TAC
        THEN Cases_on `x'' + x''' < x'`
        THEN RW_TAC arith_ss [L_def]
        THEN FULL_SIMP_TAC std_ss [L_def]
        THEN `x'' + x''' = x' + (x'' + x''' - x')` by DECIDE_TAC
        THEN ASSUM_LIST(fn thl => ASSUME_TAC(SPEC ``x'' + x''' - x'`` (el 7 thl)))
        THEN PROVE_TAC[]]);

val FINITE_F_W_CLOCK_NEXT_LEMMA =
 prove
  (``IS_FINITE_PATH p
     ==>
     !i j k :: PL p.
      NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j
      ==>
      (UF_SEM M (RESTN p k) (F_W_CLOCK c f) = UF_SEM M (RESTN p j) (F_W_CLOCK c f))``,
    RW_TAC std_ss [UF_SEM_F_W_CLOCK,RES_FORALL,PL_def,IN_DEF,RESTN_RESTN,
                   IS_FINITE_PATH_RESTN,L_def]
     THEN EQ_TAC
     THEN RW_TAC std_ss []
     THENL
      [`UF_SEM M (RESTN p x') (F_U_CLOCK c f)`
        by PROVE_TAC[SIMP_RULE std_ss [RES_FORALL,PL_def,IN_DEF]F_U_CLOCK_NEXT_LEMMA]
        THEN PROVE_TAC[],
       DISJ2_TAC
        THEN RW_TAC std_ss []
        THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `x' + x''' - x''` (el 2 thl)))
        THEN `x'' + (x' + x''' - x'') = x' + x'''` by DECIDE_TAC
        THEN `PATH_LENGTH (RESTN p x'') = PATH_LENGTH p - x''` by PROVE_TAC[PATH_LENGTH_RESTN]
        THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'` by PROVE_TAC[PATH_LENGTH_RESTN]
        THEN `x' + x''' - x'' < PATH_LENGTH (RESTN p x'')` by DECIDE_TAC
        THEN PROVE_TAC[],
       `UF_SEM M (RESTN p x'') (F_U_CLOCK c f)`
        by PROVE_TAC[SIMP_RULE std_ss [RES_FORALL,PL_def,IN_DEF]F_U_CLOCK_NEXT_LEMMA]
        THEN PROVE_TAC[],
       DISJ2_TAC
        THEN RW_TAC arith_ss []
        THEN FULL_SIMP_TAC arith_ss [UF_SEM,PATH_EL_RESTN]
        THEN `x <= x'` by DECIDE_TAC
        THEN ASSUM_LIST
              (fn thl => 
                STRIP_ASSUME_TAC
                 (SIMP_RULE std_ss [NEXT_RISE_LESS] (CONJ(el 1 thl)(el 6 thl))))
        THEN `x <= x'' + x'''` by DECIDE_TAC
        THEN Cases_on `x'' + x''' < x'`
        THEN RW_TAC arith_ss [L_def]
        THEN FULL_SIMP_TAC std_ss [L_def]
        THEN `x'' + x''' = x' + (x'' + x''' - x')` by DECIDE_TAC
        THEN ASSUM_LIST(fn thl => ASSUME_TAC(SPEC ``x'' + x''' - x'`` (el 8 thl)))
        THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'` by PROVE_TAC[PATH_LENGTH_RESTN]
        THEN `PATH_LENGTH (RESTN p x'') = PATH_LENGTH p - x''` by PROVE_TAC[PATH_LENGTH_RESTN]
        THEN `x'' + x''' - x' < PATH_LENGTH (RESTN p x')` by DECIDE_TAC
        THEN PROVE_TAC[]]);

in

val F_W_CLOCK_NEXT_LEMMA =
 store_thm
  ("F_W_CLOCK_NEXT_LEMMA",
   ``!i j k :: PL p.
      NEXT_RISE M p c (i,j) /\ i <= k /\ k <= j
      ==>
      (UF_SEM M (RESTN p k) (F_W_CLOCK c f) = UF_SEM M (RESTN p j) (F_W_CLOCK c f))``,
   Cases_on `IS_FINITE_PATH p`
    THEN RW_TAC std_ss [INFINITE_F_W_CLOCK_NEXT_LEMMA,FINITE_F_W_CLOCK_NEXT_LEMMA]);

end;

(******************************************************************************
* UF_W_CLOCK_UF_W_CLOCK =
*  |- UF_SEM M p (F_W_CLOCK c (F_W_CLOCK c f)) = UF_SEM M p (F_W_CLOCK c f) 
******************************************************************************)
local

val INFINITE_UF_W_CLOCK_UF_W_CLOCK =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     (UF_SEM M p (F_W_CLOCK c (F_W_CLOCK c f)) = UF_SEM M p (F_W_CLOCK c f))``,
    RW_TAC std_ss [UF_SEM_F_W_CLOCK,RES_FORALL,PL_def,IN_DEF,RESTN_RESTN,
                   IS_FINITE_PATH_RESTN,L_def,UF_U_CLOCK_UF_U_CLOCK]
     THEN EQ_TAC
     THEN RW_TAC arith_ss 
           [F_W_CLOCK_def,F_U_CLOCK_def,F_OR_def,F_F_def,RESTN_RESTN,
            F_G_def,F_W_def,F_W_CLOCK_def,UF_SEM,PATH_EL_RESTN,B_SEM_def,
            RES_FORALL,RES_EXISTS,PL_def,IN_DEF,L_def,IS_FINITE_PATH_RESTN]
     THEN RW_TAC std_ss []
     THENL
      [DISJ1_TAC
        THEN Q.EXISTS_TAC`x+x'`
        THEN RW_TAC std_ss []
        THEN Cases_on `x'' < x`
        THEN RW_TAC std_ss []
        THEN FULL_SIMP_TAC std_ss [DECIDE ``~(m < n) \/ P = m < n ==> P``]
        THEN `(x'' - x) < x'` by DECIDE_TAC
        THEN `x + (x'' - x) = x''` by DECIDE_TAC
        THEN PROVE_TAC[],
       ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE arith_ss [] (SPEC ``0`` (el 2 thl))))
        THEN PROVE_TAC[],
       DISJ1_TAC
        THEN Q.EXISTS_TAC`x`
        THEN RW_TAC std_ss []
        THEN DISJ1_TAC
        THEN Q.EXISTS_TAC `0`
        THEN RW_TAC arith_ss []]);
      

val FINITE_UF_W_CLOCK_UF_W_CLOCK =
 prove
  (``IS_FINITE_PATH p
     ==>
     (UF_SEM M p (F_W_CLOCK c (F_W_CLOCK c f)) = UF_SEM M p (F_W_CLOCK c f))``,
    RW_TAC std_ss [UF_SEM_F_W_CLOCK,RES_FORALL,PL_def,IN_DEF,RESTN_RESTN,
                   IS_FINITE_PATH_RESTN,L_def,UF_U_CLOCK_UF_U_CLOCK]
     THEN EQ_TAC
     THEN RW_TAC arith_ss 
           [F_W_CLOCK_def,F_U_CLOCK_def,F_OR_def,F_F_def,RESTN_RESTN,
            F_G_def,F_W_def,F_W_CLOCK_def,UF_SEM,PATH_EL_RESTN,B_SEM_def,
            RES_FORALL,RES_EXISTS,PL_def,IN_DEF,L_def,IS_FINITE_PATH_RESTN]
     THEN RW_TAC std_ss []
     THENL
      [DISJ1_TAC
        THEN Q.EXISTS_TAC`x+x'`
        THEN RW_TAC std_ss []
        THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
        THEN `x + x' < PATH_LENGTH p` by DECIDE_TAC
        THEN RW_TAC std_ss []
        THEN FULL_SIMP_TAC std_ss [DECIDE ``~(m < n) \/ P = m < n ==> P``]
        THEN Cases_on `x'' < x`
        THEN RW_TAC std_ss []
        THEN `(x'' - x) < x'` by DECIDE_TAC
        THEN `(x'' - x) < PATH_LENGTH p - x` by DECIDE_TAC
        THEN `x + (x'' - x) = x''` by DECIDE_TAC
        THEN PROVE_TAC[],
       ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE arith_ss [] (SPEC ``0`` (el 2 thl))))
        THEN PROVE_TAC[FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN],
       DISJ1_TAC
        THEN Q.EXISTS_TAC`x`
        THEN RW_TAC std_ss []
        THEN DISJ1_TAC
        THEN Q.EXISTS_TAC `0`
        THEN RW_TAC arith_ss [FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]]);
      
in

val UF_W_CLOCK_UF_W_CLOCK =
 store_thm
  ("UF_W_CLOCK_UF_W_CLOCK",
   ``UF_SEM M p (F_W_CLOCK c (F_W_CLOCK c f)) = UF_SEM M p (F_W_CLOCK c f)``,
   Cases_on `IS_FINITE_PATH p`
    THEN RW_TAC std_ss [INFINITE_UF_W_CLOCK_UF_W_CLOCK,FINITE_UF_W_CLOCK_UF_W_CLOCK]);

end;

val F_CLOCK_FREE_F_W_CLOCK  =
 store_thm
  ("F_CLOCK_FREE_F_W_CLOCK",
   ``!f. F_CLOCK_FREE f ==> !c. F_CLOCK_FREE(F_W_CLOCK c f)``,
   RW_TAC std_ss [F_W_CLOCK_def,F_G_def,F_F_def,F_W_def,F_OR_def,F_CLOCK_FREE_def]);

(******************************************************************************
* Rules for compiling clocked FL formulas to unclocked formulas
* (from B.1, page 66 and 67, of Sugar 2.0 Accellera document)
*
* Update from IBM: the correct rewrite rules for X! should be:
*  
*  (X! f)@clk! = [!clk U clk & X! (!clk U clk & (f@clk!))]
*  (X! f)@clk  = [!clk W clk & X! (!clk U clk & (f@clk!))]
*  
* Change by MJCG on 12.09.02:
*  (X! f)@clk  = [!clk W clk & X! (!clk U clk & (f@clk))]
******************************************************************************)
val F_CLOCK_COMP_def =
 Define
  `(F_CLOCK_COMP (STRONG_CLOCK c) (F_BOOL b) = 
     F_U_CLOCK c (F_BOOL b))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_NOT f) = 
      F_NOT(F_CLOCK_COMP (WEAK_CLOCK c) f))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_AND(f1,f2)) = 
      F_U_CLOCK c (F_AND(F_CLOCK_COMP (STRONG_CLOCK c) f1, 
                         F_CLOCK_COMP (STRONG_CLOCK c) f2)))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_NEXT f) = 
      F_U_CLOCK c (F_NEXT(F_U_CLOCK c (F_CLOCK_COMP (STRONG_CLOCK c) f))))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_UNTIL(f1,f2)) = 
      F_UNTIL(F_U_CLOCK c (F_CLOCK_COMP (STRONG_CLOCK c) f1),
              F_U_CLOCK c (F_CLOCK_COMP (STRONG_CLOCK c) f2)))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_UNTIL(f1,f2)) = 
      F_U_CLOCK c (F_UNTIL(F_CLOCK_COMP (STRONG_CLOCK c) f1,
                           F_CLOCK_COMP (STRONG_CLOCK c) f2)))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_SUFFIX_IMP(r,f)) = 
      F_U_CLOCK c (F_SUFFIX_IMP(S_CLOCK_COMP c r, 
                                F_CLOCK_COMP (STRONG_CLOCK c) f)))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)) = 
      F_U_CLOCK c (F_STRONG_IMP (S_CLOCK_COMP c r1,
                                 S_CLOCK_COMP c r2)))
    /\

    (F_CLOCK_COMP (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
      F_U_CLOCK c (F_OR
                    (F_STRONG_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2),
                     F_AND
                      (F_G(F_F(F_BOOL c)),
                       F_WEAK_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2)))))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_ABORT (f,b)) =
      F_U_CLOCK c (F_ABORT(F_CLOCK_COMP (STRONG_CLOCK c) f, B_AND(c,b))))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_WEAK_CLOCK(f,c1)) =   
      F_CLOCK_COMP (WEAK_CLOCK c1) f)
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_CLOCK(f,c1)) =   
      F_CLOCK_COMP (STRONG_CLOCK c1) f)
    /\ 
(******************************************************************************
* Start of weak clock clauses
******************************************************************************)
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_BOOL b) = 
      F_W_CLOCK c (F_BOOL b))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_NOT f) = 
      F_NOT(F_CLOCK_COMP (STRONG_CLOCK c) f))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_AND(f1,f2)) = 
      F_W_CLOCK c (F_AND(F_CLOCK_COMP (WEAK_CLOCK c) f1, 
                         F_CLOCK_COMP (WEAK_CLOCK c) f2)))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_NEXT f) = 
      F_W_CLOCK c (F_NEXT(F_U_CLOCK c (F_CLOCK_COMP (WEAK_CLOCK c) f))))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_UNTIL(f1,f2)) = 
      F_UNTIL(F_W_CLOCK c (F_CLOCK_COMP (WEAK_CLOCK c) f1), 
              F_W_CLOCK c (F_CLOCK_COMP (WEAK_CLOCK c) f2)))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_SUFFIX_IMP(r,f)) = 
      F_W_CLOCK c (F_SUFFIX_IMP(S_CLOCK_COMP c r, 
                                F_CLOCK_COMP (WEAK_CLOCK c) f)))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_STRONG_IMP(r1,r2)) = 
      F_W_CLOCK c (F_OR
                    (F_STRONG_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2),
                     F_AND
                      (F_F(F_G(F_BOOL(B_NOT c))),
                       F_WEAK_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2)))))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
      F_W_CLOCK c (F_WEAK_IMP (S_CLOCK_COMP c r1,
                               S_CLOCK_COMP c r2)))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_ABORT (f,b)) =
      F_W_CLOCK c (F_ABORT(F_CLOCK_COMP (WEAK_CLOCK c) f, B_AND(c,b))))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_CLOCK(f,c1)) =   
      F_CLOCK_COMP (WEAK_CLOCK c1) f)
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_STRONG_CLOCK(f,c1)) =   
      F_CLOCK_COMP (STRONG_CLOCK c1) f)`;

(******************************************************************************
* F_CLOCK_COMP k f contains no clocked formulas
******************************************************************************)
val F_CLOCK_COMP_CLOCK_FREE_LEMMA =
 store_thm
  ("F_CLOCK_COMP_CLOCK_FREE_LEMMA",
   ``!f c. F_CLOCK_FREE(F_CLOCK_COMP (STRONG_CLOCK c) f)
           /\
           F_CLOCK_FREE(F_CLOCK_COMP (WEAK_CLOCK c) f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss 
          [F_CLOCK_FREE_def,F_CLOCK_COMP_def,F_U_CLOCK_def,F_OR_def,F_F_def,
           F_G_def,F_W_def,F_W_CLOCK_def,S_CLOCK_COMP_CLOCK_FREE]);

val F_CLOCK_COMP_CLOCK_FREE =
 store_thm
  ("F_CLOCK_COMP_CLOCK_FREE",
   ``!k f. F_CLOCK_FREE(F_CLOCK_COMP k f)``,
   Cases
    THEN RW_TAC std_ss [F_CLOCK_COMP_CLOCK_FREE_LEMMA]);

(******************************************************************************
* Compiled strong clocking with T equal to compiled weak clocking with T:
******************************************************************************)
local

val INIT_TAC =
 RW_TAC std_ss 
  [UF_SEM,FIRST_RISE_TRUE,B_SEM_def,RES_FORALL,RES_EXISTS,IN_DEF,PL0,
   NEXT_RISE_TRUE_EXISTS,RESTN_def,IS_FINITE_PATH_RESTN,RESTN_RESTN,
   F_CLOCK_COMP_def,F_U_CLOCK_def,F_OR_def,F_F_def,
   F_G_def,F_W_def,F_W_CLOCK_def,NOT_IS_INFINITE_PATH,
   RES_FORALL,RES_EXISTS,IN_DEF,FORALL_NOT_PL]
 THEN TRY(PROVE_TAC[]);

val TAC2 =
 INIT_TAC
  THEN EQ_TAC
  THEN RW_TAC std_ss []
  THEN Q.EXISTS_TAC `x`
  THEN RW_TAC std_ss []
  THEN PROVE_TAC[];

in

val F_SEM_CLOCK_COMP_TRUE_EQ =
 store_thm
  ("F_SEM_CLOCK_COMP_TRUE_EQ",
   ``!f M p. 
      UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK B_TRUE) f) = 
       UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK B_TRUE) f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC,
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      TAC2,
      (* F_UNTIL(f1,f2) f *)
      REPEAT GEN_TAC
       THEN Cases_on `IS_FINITE_PATH p`
       THEN INIT_TAC
       THEN RW_TAC arith_ss
             [PL_def,IN_DEF,PL_EXISTS_FORALL_LEMMA,FINITE_PATH_NONEMPTY,
              IS_FINITE_PATH_def,IS_FINITE_PATH_RESTN]
       THEN TAC2,
      (* F_SUFFIX_IMP(s,f) *)
       TAC2,
      (* F_STRONG_IMP(s1,s2) *)
       TAC2,
      (* F_WEAK_IMP(s1,s2) *)
       TAC2,
      (* F_ABORT(f,b)) *)
       TAC2,
      (* F_WEAK_CLOCK(f,c) *)
      INIT_TAC,
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC]);

end;

(******************************************************************************
* CLOCK_COMP_CORRECT f  =  (p |=k= f  <==>  p |= (F_CLOCK_COMP k f))
* where k is (STRONG_CLOCK c) or (WEAK_CLOCK c)
*
* We prove lemmas CLOCK_COMP_CORRECT M f for various cases of f.
* Note that we cannot define 
*   |- CLOCK_COMP_CORRECT f = !M. ...
* because there would then be unbound types variables in the rhs.
*
******************************************************************************)
val CLOCK_COMP_CORRECT_def =
 Define
  `CLOCK_COMP_CORRECT M f =
    !p c. (F_SEM M p (STRONG_CLOCK c) f =
            UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) f))
          /\
          (F_SEM M p (WEAK_CLOCK c) f =
            UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) f))`;

val F_BOOL_STRONG_CLOCK_COMP_ELIM =
 store_thm
  ("F_BOOL_STRONG_CLOCK_COMP_ELIM",
   ``!b M p c.
      F_SEM M p (STRONG_CLOCK c) (F_BOOL b) =
       UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_BOOL b))``,
   RW_TAC arith_ss [F_SEM_def, UF_SEM_def, F_CLOCK_COMP_def,PATH_EL_RESTN,
                    F_U_CLOCK_def, F_W_CLOCK_def,FIRST_RISE,B_SEM_def,L_def,
                    RES_FORALL,RES_EXISTS,PL_def,pred_setTheory.SPECIFICATION]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [PROVE_TAC[],
      Q.EXISTS_TAC `x`
       THEN RW_TAC std_ss []
       THEN `IS_FINITE_PATH p ==> j < PATH_LENGTH p` 
              by ZAP_TAC arith_ss [DECIDE``m<n ==> n<p ==> m<p``]
       THEN PROVE_TAC[]]);

val PL_MONO =
 store_thm
  ("PL_MONO",
   ``!m n. m <= n ==> !p. PL p n ==> PL p m``,
  RW_TAC arith_ss [PL_def]
   THEN RES_TAC
   THEN DECIDE_TAC);

val PL_LESS_MONO =
 store_thm
  ("PL_LESS_MONO",
   ``!m n. m < n ==> !p. PL p n ==> PL p m``,
  RW_TAC arith_ss [PL_def]
   THEN RES_TAC
   THEN DECIDE_TAC);

val F_BOOL_WEAK_CLOCK_COMP_ELIM =
 store_thm
  ("F_BOOL_WEAK_CLOCK_COMP_ELIM",
   ``!b M p c.
      F_SEM M p (WEAK_CLOCK c) (F_BOOL b) =
       UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_BOOL b))``,
   RW_TAC arith_ss [F_SEM_def, UF_SEM_def, F_CLOCK_COMP_def,F_W_CLOCK_def,
                    UF_SEM_F_W,FIRST_RISE,PATH_EL_RESTN]
    THEN Cases_on `UF_SEM M p (F_G (F_BOOL (B_NOT c)))`
    THEN RW_TAC std_ss []
    THENL
     [RW_TAC std_ss [RES_FORALL, IN_DEF]
       THEN FULL_SIMP_TAC arith_ss 
             [UF_SEM,B_SEM_def,UF_SEM_F_G,RES_FORALL,IN_DEF,PATH_EL_RESTN,L_def]
       THEN RES_TAC,
      FULL_SIMP_TAC arith_ss 
            [UF_SEM_WOP_NOT_F_G,RES_FORALL,RES_EXISTS,IN_DEF,UF_SEM,
             PATH_EL_RESTN,B_SEM_def,L_def]
       THEN RW_TAC std_ss [RES_FORALL,RES_EXISTS,IN_DEF,B_SEM_def]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN PROVE_TAC[PL_LESS_MONO],
         MAP_EVERY Cases_on [`x''< x`, `x < x''`, `x'< x`, `x < x'`]
          THEN PROVE_TAC[DECIDE``~(m < n)==>~(n < m)==>(m=n)``]]]);

val F_BOOL_CLOCK_COMP_ELIM =
 store_thm
  ("F_BOOL_CLOCK_COMP_ELIM",
   ``!M b. CLOCK_COMP_CORRECT M (F_BOOL b)``,
   RW_TAC std_ss 
    [CLOCK_COMP_CORRECT_def,
     F_BOOL_WEAK_CLOCK_COMP_ELIM,F_BOOL_STRONG_CLOCK_COMP_ELIM]);

val F_NOT_CLOCK_COMP_ELIM =
 store_thm
  ("F_NOT_CLOCK_COMP_ELIM",
   ``!M f. CLOCK_COMP_CORRECT M f ==> CLOCK_COMP_CORRECT M (F_NOT f)``,
   RW_TAC std_ss [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def]);

val F_AND_CLOCK_COMP_ELIM_LEMMA =
 prove
  (``PL p x /\ (!j. j < x ==> P p j) = 
     PL p x /\ (!j. PL p j ==> j < x ==> P p j)``,
   PROVE_TAC[PL_LESS_MONO]);

val WOP_LESS =
 store_thm
  ("WOP_LESS",
   ``!P n. P n ==> ?m. P m /\ m <= n /\ !n. n < m ==> ~P n``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC WOP
    THEN Cases_on `n' <= n`
    THEN IMP_RES_TAC(DECIDE``~(m <= n) = n < m``)
    THEN PROVE_TAC[]);

val F_AND_CLOCK_COMP_ELIM =
 store_thm
  ("F_AND_CLOCK_COMP_ELIM",
   ``!M f1 f2. CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 
               ==> CLOCK_COMP_CORRECT M (F_AND(f1,f2))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,
     FIRST_RISE,F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,
     PATH_EL_RESTN,RES_FORALL,RES_EXISTS,L_def,B_SEM_def,IN_DEF]
    THEN REWRITE_TAC[DECIDE``~A\/B = A==>B``]
    THEN TRY(PROVE_TAC[PL_LESS_MONO])
    THEN Cases_on `UF_SEM M p (F_G (F_BOOL (B_NOT c)))`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC arith_ss 
          [UF_SEM_F_G,RES_FORALL,IN_DEF,UF_SEM,L_def,PATH_EL_RESTN,B_SEM_def]
    THEN RES_TAC
    THEN REWRITE_TAC
          [DECIDE``A==>B/\C==>D/\E = (A/\B)/\C==>D/\E``,
           DECIDE``A/\(B/\C/\D)/\E=(A/\E)/\B/\C/\D``]
    THEN Ho_Rewrite.REWRITE_TAC[GSYM F_AND_CLOCK_COMP_ELIM_LEMMA]
    THEN EQ_TAC
    THEN SIMP_TAC std_ss []
    THENL
     [DISCH_TAC
       THEN ASSUM_LIST
             (fn thl => 
               STRIP_ASSUME_TAC
                (SIMP_RULE std_ss []
                  (ISPEC``\^(rand(concl(el 3 thl))).^(concl(el 2 thl))``WOP_LESS)))
       THEN ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(MATCH_MP(el 1 thl) (el 3 thl)))
       THEN Q.EXISTS_TAC `m`
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[PL_MONO],
      RW_TAC std_ss []
       THEN MAP_EVERY Cases_on [`x''< x`, `x < x''`, `x'< x`, `x < x'`]
       THEN PROVE_TAC[DECIDE``~(m < n)==>~(n < m)==>(m=n)``]]);

val F_SUFFIX_IMP_CLOCK_COMP_ELIM =
 store_thm
  ("F_SUFFIX_IMP_CLOCK_COMP_ELIM",
   ``!M r f. CLOCK_COMP_CORRECT M f
           ==> CLOCK_COMP_CORRECT M (F_SUFFIX_IMP(r,f))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,
     F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
     UF_SEM_F_W,UF_SEM_F_G,
     UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
     RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH]
    THEN Cases_on `IS_INFINITE_PATH p`
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC std_ss []
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [RESTN_RESTN]
          THEN FULL_SIMP_TAC arith_ss 
                [GSYM S_CLOCK_COMP_ELIM,PATH_SEG_RESTN],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [RESTN_RESTN]
          THEN ASSUM_LIST(fn thl => 
                           FULL_SIMP_TAC arith_ss 
                            [el 6 thl,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,
                             GSYM S_CLOCK_COMP_ELIM,RESTN_RESTN])
          THEN `x + (x' - x) = x'` by DECIDE_TAC
          THEN PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN ASSUM_LIST(fn thl => 
                           FULL_SIMP_TAC arith_ss 
                            [el 6 thl,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,
                             GSYM S_CLOCK_COMP_ELIM,RESTN_RESTN]
                           THEN ASSUME_TAC(el 6 thl))
          THEN RES_TAC
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x + x' < PATH_LENGTH p` by DECIDE_TAC
          THEN PROVE_TAC[DECIDE``x <= x + x'``],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [RESTN_RESTN]
          THENL[`j < PATH_LENGTH p` by DECIDE_TAC THEN PROVE_TAC[], ALL_TAC]
          THEN ASSUM_LIST(fn thl => 
                           FULL_SIMP_TAC arith_ss 
                            [el 7 thl,el 8 thl, IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,
                             GSYM S_CLOCK_COMP_ELIM,RESTN_RESTN]
                           THEN ASSUME_TAC(el 7 thl) THEN ASSUME_TAC(el 8 thl))
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x + (x' - x) = x'` by DECIDE_TAC
          THEN `x' - x < PATH_LENGTH(RESTN p x)` by DECIDE_TAC
          THEN PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `!x. ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\x. ^(concl(el 1 thl))` WOP)))
          THEN `?n. B_SEM M (getL M (PATH_EL p n)) c /\
                    !m. m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `n`
          THEN RW_TAC std_ss [RESTN_RESTN]
          THEN FULL_SIMP_TAC arith_ss 
                [GSYM S_CLOCK_COMP_ELIM,PATH_SEG_RESTN]
          THEN `!x'. n <= x' /\ S_SEM M (LHAT M (PATH_SEG p (n,x'))) c r ==>
                     UF_SEM M (RESTN p x') (F_CLOCK_COMP (WEAK_CLOCK c) f)`
               by PROVE_TAC[]
          THEN PROVE_TAC[DECIDE``n <= n + x'``],
         ASSUM_LIST(fn thl => 
                     FULL_SIMP_TAC arith_ss 
                      [el 8 thl,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,
                       GSYM S_CLOCK_COMP_ELIM,RESTN_RESTN])
          THEN Cases_on `x < x'`
          THEN Cases_on `x' < x`
          THEN RES_TAC
          THEN `x=x'` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THEN PROVE_TAC[DECIDE ``x <= x'' ==> (x + (x'' - x) = x'')``],
         PROVE_TAC[L_def]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `!x. x < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC
                            (SIMP_RULE std_ss [] 
                              (Q.ISPEC `\x. ^(concl(el 2 thl)) /\ ^(concl(el 1 thl))` WOP)))
          THEN `?n. n < PATH_LENGTH p /\ B_SEM M (getL M (PATH_EL p n)) c /\
                    !m. m < PATH_LENGTH p ==> m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `n`
          THEN RW_TAC std_ss [RESTN_RESTN]
          THEN FULL_SIMP_TAC arith_ss 
                [GSYM S_CLOCK_COMP_ELIM,PATH_SEG_RESTN]
          THEN `!j. j < n ==> j < PATH_LENGTH p` by DECIDE_TAC
          THEN `!j. j < n ==> ~B_SEM M (getL M (PATH_EL p j)) c`
                by PROVE_TAC[]
          THEN `!x'. x' < PATH_LENGTH p ==>
                     n <= x' /\ S_SEM M (LHAT M (PATH_SEG p (n,x'))) c r ==>
                     UF_SEM M (RESTN p x') (F_CLOCK_COMP (WEAK_CLOCK c) f)`
               by PROVE_TAC[]
          THEN `PATH_LENGTH (RESTN p n) = PATH_LENGTH p - n` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN FULL_SIMP_TAC std_ss [IS_FINITE_PATH_RESTN]
          THEN `x' < PATH_LENGTH p - n` by PROVE_TAC[]
          THEN PROVE_TAC
                [DECIDE``x < PATH_LENGTH p ==> x' < PATH_LENGTH p - n ==> n + x' < PATH_LENGTH p``,
                 DECIDE ``n <= n + x'``],
         ASSUM_LIST(fn thl => 
                     FULL_SIMP_TAC arith_ss 
                      [el 11 thl,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,
                       GSYM S_CLOCK_COMP_ELIM,RESTN_RESTN]
                     THEN ASSUME_TAC(el 11 thl))
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x' < PATH_LENGTH p` by DECIDE_TAC
          THEN Cases_on `x < x'`
          THEN Cases_on `x' < x`
          THEN RES_TAC
          THEN `x=x'` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THEN IMP_RES_TAC(DECIDE``(m = n - x) ==> x <= x'' ==> x'' < n ==> x < n ==> x'' - x < m``)
          THEN PROVE_TAC[DECIDE ``x <= x'' ==> (x + (x'' - x) = x'')``],
         PROVE_TAC[L_def]]]);

val F_ABORT_CLOCK_COMP_ELIM =
 store_thm
  ("F_ABORT_CLOCK_COMP_ELIM",
   ``!M b f. CLOCK_COMP_CORRECT M f
             ==> CLOCK_COMP_CORRECT M (F_ABORT(f,b))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,
     F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
     UF_SEM_F_W,UF_SEM_F_G,
     UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
     RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH]
    THEN Cases_on `IS_INFINITE_PATH p`
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC std_ss []
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [PROVE_TAC[],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN Cases_on `UF_SEM M (RESTN p x) (F_CLOCK_COMP (STRONG_CLOCK c) f)`
          THEN RW_TAC std_ss [IS_FINITE_PATH_RESTN]
          THEN `0 < x'-x` by DECIDE_TAC
          THEN `x + (x'-x) = x'` by DECIDE_TAC
          THEN `x + ((x'-x) - 1) = x' - 1` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x'-x`
          THEN RW_TAC arith_ss [PATH_SEG_RESTN]
          THEN FULL_SIMP_TAC arith_ss [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN PROVE_TAC[],
         PROVE_TAC[],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN Cases_on `UF_SEM M (RESTN p x) (F_CLOCK_COMP (STRONG_CLOCK c) f)`
          THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN `x < x + x'` by DECIDE_TAC
          THEN FULL_SIMP_TAC arith_ss [PATH_SEG_RESTN]
          THEN PROVE_TAC[DECIDE``(x+x') - 1 = x + x' - 1``]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [PROVE_TAC[],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN Cases_on `UF_SEM M (RESTN p x) (F_CLOCK_COMP (STRONG_CLOCK c) f)`
          THEN RW_TAC std_ss [IS_FINITE_PATH_RESTN]
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN FULL_SIMP_TAC arith_ss [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN `IS_FINITE_PATH p ==> 0 < PATH_LENGTH (RESTN p x')` by RW_TAC arith_ss []
          THEN `x'-x < PATH_LENGTH (RESTN p x)` by DECIDE_TAC
          THEN `0 < x'-x` by DECIDE_TAC
          THEN `x + (x'-x) = x'` by DECIDE_TAC
          THEN `x + ((x'-x) - 1) = x' - 1` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x'-x`
          THEN RW_TAC arith_ss [PATH_SEG_RESTN]
          THEN PROVE_TAC[],
         `!j. j < x ==> ~B_SEM M (getL M (PATH_EL p j)) c` by RW_TAC arith_ss []
          THEN PROVE_TAC[],
         `!j. j < x ==> ~B_SEM M (getL M (PATH_EL p j)) c` by RW_TAC arith_ss []
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN Cases_on `UF_SEM M (RESTN p x) (F_CLOCK_COMP (STRONG_CLOCK c) f)`
          THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN FULL_SIMP_TAC std_ss [IS_FINITE_PATH_RESTN]
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x' < PATH_LENGTH (RESTN p x)` by PROVE_TAC[]
          THEN `x + x' < PATH_LENGTH p` by DECIDE_TAC
          THEN `x < x + x'` by DECIDE_TAC
          THEN FULL_SIMP_TAC arith_ss [PATH_SEG_RESTN]
          THEN RW_TAC arith_ss [FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]
          THEN PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `!x. ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\x. ^(concl(el 1 thl))` WOP)))
          THEN `?n. B_SEM M (getL M (PATH_EL p n)) c /\
                    !m. m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `n`
          THEN RW_TAC std_ss [RESTN_RESTN,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN]
          THEN Cases_on `UF_SEM M (RESTN p n) (F_CLOCK_COMP (WEAK_CLOCK c) f)`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss 
                [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN ASSUM_LIST(fn thl => FULL_SIMP_TAC std_ss [el 7 thl])
          THEN `?x''. n < x'' /\
                      ?p'. (B_SEM M (getL M (PATH_EL p x'')) c /\
                            B_SEM M (getL M (PATH_EL p x'')) b) /\
                           UF_SEM M (PATH_CAT (PATH_SEG p (n,x'' - 1),p'))
                            (F_CLOCK_COMP (WEAK_CLOCK c) f)` by PROVE_TAC[]
          THEN `0 < x'' - n` by DECIDE_TAC
          THEN `(n + (x'' -n) = x'') /\ (n + ((x'' - n) - 1) = x'' - 1)` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x''-n`
          THEN RW_TAC std_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN]
          THEN PROVE_TAC[],
         Cases_on `x' < x` 
          THEN Cases_on `x < x'`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN `x = x'` by DECIDE_TAC
          THEN RW_TAC std_ss [],
         Cases_on `UF_SEM M (RESTN p x'') (F_CLOCK_COMP (WEAK_CLOCK c) f)`
          THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN Cases_on `x'' < x` 
          THEN Cases_on `x < x''`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN `x = x''` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THEN Q.EXISTS_TAC `x+x'`
          THEN RW_TAC arith_ss []
          THEN FULL_SIMP_TAC arith_ss [PATH_SEG_RESTN]
          THEN `x + (x' - 1) = x + x' - 1` by DECIDE_TAC
          THEN PROVE_TAC[],
         PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `!x. x < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]

          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC
                            (SIMP_RULE std_ss [] 
                              (Q.ISPEC `\x. ^(concl(el 2 thl)) /\ ^(concl(el 1 thl))` WOP)))
          THEN `?n. n < PATH_LENGTH p /\ B_SEM M (getL M (PATH_EL p n)) c /\
                    !m. m < PATH_LENGTH p ==> m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `n`
          THEN RW_TAC std_ss [RESTN_RESTN,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN]
          THEN FULL_SIMP_TAC arith_ss 
                [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN Cases_on `UF_SEM M (RESTN p n) (F_CLOCK_COMP (WEAK_CLOCK c) f)`
          THEN RW_TAC std_ss []
          THEN ASSUM_LIST(fn thl => FULL_SIMP_TAC std_ss [el 9 thl] THEN ASSUME_TAC(el 9 thl))
          THEN `!j. j < n ==> j < PATH_LENGTH p` by DECIDE_TAC
          THEN `!j. j < n ==> ~B_SEM M (getL M (PATH_EL p j)) c`
                by PROVE_TAC[]
          THEN `!x. 0 < PATH_LENGTH(RESTN p x)` by PROVE_TAC[IS_FINITE_PATH_RESTN,FINITE_PATH_NONEMPTY]
          THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
          THEN ASSUM_LIST
                (fn thl => 
                  STRIP_ASSUME_TAC(SIMP_RULE std_ss (map(fn n=>el n thl)[1,4,6,7]) (Q.SPEC `n` (el 11 thl))))
          THEN `PATH_LENGTH (RESTN p n) = PATH_LENGTH p - n` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x'' - n < PATH_LENGTH (RESTN p n) /\ 0 < x'' - n` by RW_TAC arith_ss []
          THEN Q.EXISTS_TAC `x'' - n`
          THEN RW_TAC arith_ss []
          THEN PROVE_TAC[],
         Cases_on `x' < x` 
          THEN Cases_on `x < x'`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN `x = x'` by DECIDE_TAC
          THEN PROVE_TAC[]
          THEN RW_TAC std_ss [],
         Cases_on `UF_SEM M (RESTN p x'') (F_CLOCK_COMP (WEAK_CLOCK c) f)`
          THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,intLib.COOPER_PROVE``(!j. ~(j < x''))=(x''=0)``]
          THEN Cases_on `x'' < x` 
          THEN Cases_on `x < x''`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN `x = x''` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss [PATH_SEG_RESTN,IS_FINITE_PATH_RESTN]
          THEN RW_TAC std_ss []
          THEN `x' < PATH_LENGTH (RESTN p x)` by PROVE_TAC[]
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x + x' < PATH_LENGTH p` by DECIDE_TAC
          THEN `x < x + x'` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x+x'`
          THEN RW_TAC arith_ss []
          THEN `x + (x' - 1) = x + x' - 1` by DECIDE_TAC
          THEN PROVE_TAC[],
         PROVE_TAC[]]]);

val F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM =
 store_thm
  ("F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM",
   ``!M r1 r2 p c. 
      F_SEM M p (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)) = 
       UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)))``,
   RW_TAC arith_ss 
    [F_SEM_def,UF_SEM,F_CLOCK_COMP_def,
     F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
     UF_SEM_F_W,UF_SEM_F_G,
     UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
     RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH]
    THEN Cases_on `IS_INFINITE_PATH p`
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,GSYM S_CLOCK_COMP_ELIM]
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN `x <= x + x'` by DECIDE_TAC
          THEN RES_TAC
          THEN `x' <= x''' - x` by DECIDE_TAC
          THEN `x + (x''' - x) = x'''` by DECIDE_TAC
          THEN PROVE_TAC[],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN `x + (x' - x) = x'` by DECIDE_TAC
          THEN ASSUM_LIST(fn thl => 
                           STRIP_ASSUME_TAC
                             (SIMP_RULE arith_ss [el 1 thl, el 2 thl] (Q.SPEC `x'-x` (el 5 thl))))
          THEN PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [`!x'. x' < PATH_LENGTH p ==> x' < x ==> ~B_SEM M (getL M (PATH_EL p x')) c`
           by PROVE_TAC[DECIDE``x' < x ==> x < PATH_LENGTH p ==> x' < PATH_LENGTH p``]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x+x' < PATH_LENGTH p` by DECIDE_TAC
          THEN `x <= x+x'` by DECIDE_TAC
          THEN ASSUM_LIST(fn thl => 
                           STRIP_ASSUME_TAC
                             (SIMP_RULE arith_ss [el 2 thl,el 4 thl] (Q.SPEC `x+x'` (el 7 thl))))
          THEN `x'' - x < PATH_LENGTH (RESTN p x)` by DECIDE_TAC
          THEN `x' <= x'' - x` by DECIDE_TAC
          THEN `x + (x'' - x) = x''` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x'' - x`
          THEN RW_TAC std_ss [],
         `!j. j < x ==> ~B_SEM M (getL M (PATH_EL p j)) c` 
               by PROVE_TAC[DECIDE``j < x ==> x < PATH_LENGTH p ==> j < PATH_LENGTH p``]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x' - x < PATH_LENGTH (RESTN p x)` by DECIDE_TAC
          THEN `x + (x' - x) = x'` by DECIDE_TAC
          THEN ASSUM_LIST(fn thl => 
                           STRIP_ASSUME_TAC
                             (SIMP_RULE arith_ss [el 1 thl, el 2 thl,el 4 thl] (Q.SPEC `x'-x` (el 9 thl))))
          THEN `x + x'' < PATH_LENGTH p /\ x' <= x + x''` by DECIDE_TAC
          THEN PROVE_TAC[]]]);

val F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM =
 store_thm
  ("F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM",
   ``!M r1 r2 p c. 
      F_SEM M p (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
       UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)))``,
   RW_TAC arith_ss 
    [F_SEM_def,UF_SEM,F_CLOCK_COMP_def,
     F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
     UF_SEM_F_W,UF_SEM_F_G,LHAT_def,
     UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
     RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH]
    THEN Cases_on `IS_INFINITE_PATH p`
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,GSYM S_CLOCK_COMP_ELIM]
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `!x. ~B_SEM M (getL M (PATH_EL p x)) c` 
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\x. ^(concl(el 1 thl))` WOP)))
          THEN `?n. B_SEM M (getL M (PATH_EL p n)) c /\
                    !m. m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `n`
          THEN RW_TAC std_ss [RESTN_RESTN,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,LHAT_def]
          THEN Cases_on `(?x''. x' <= x'' /\ S_SEM M (MAP (getL M) (PATH_SEG p (n + x',n + x''))) c r2)`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 4 thl,el 5 thl] (Q.SPEC `n` (el 8 thl))))
          THEN ASSUM_LIST
                (fn thl => STRIP_ASSUME_TAC(SIMP_RULE arith_ss [el 4 thl ] (Q.SPEC `n+x'` (el 1 thl))))
          THENL
           [`x' <= x''' - n` by DECIDE_TAC
             THEN `n + (x''' - n) = x'''` by DECIDE_TAC
             THEN PROVE_TAC[],
            `n + x' <= n + x''` by DECIDE_TAC
             THEN PROVE_TAC[]],
         Cases_on `!x'''. x'' <= x''' ==>
                          ?w. S_SEM M (MAP (getL M) (PATH_SEG p (x'',x''')) <> w) c r2`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Cases_on `x' < x` 
          THEN Cases_on `x < x'`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN `x = x'` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC)
          THEN `x + (x'' - x) = x''` by DECIDE_TAC
          THEN ASSUM_LIST
                (fn thl => STRIP_ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl,el 4 thl] (Q.SPEC `x'' - x` (el 9 thl))))
          THENL
           [`x'' <= x + x''''` by DECIDE_TAC
             THEN PROVE_TAC[],
            `x'' <= x + (x''' - x)` by DECIDE_TAC
             THEN `x + (x''' - x) = x'''` by DECIDE_TAC
             THEN PROVE_TAC[]],
         PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `!x. x < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p x)) c` 
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC
                            (SIMP_RULE std_ss [] 
                              (Q.ISPEC `\x. ^(concl(el 2 thl)) /\ ^(concl(el 1 thl))` WOP)))
          THEN `?n. n < PATH_LENGTH p /\ B_SEM M (getL M (PATH_EL p n)) c /\
                    !m. m < PATH_LENGTH p ==> m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `n`
          THEN RW_TAC std_ss [RESTN_RESTN,IS_FINITE_PATH_RESTN,PATH_SEG_RESTN]
          THEN Cases_on 
                `?x''. x'' < PATH_LENGTH (RESTN p n) /\ x' <= x'' /\
                       S_SEM M (MAP (getL M) (PATH_SEG p (n + x',n + x''))) c r2`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss [NOT_EXISTS_THM]
          THEN `!j. j < n ==> j < PATH_LENGTH p` by DECIDE_TAC
          THEN `!j. j < n ==> ~B_SEM M (getL M (PATH_EL p j)) c` by PROVE_TAC[]
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl,el 9 thl,el 10 thl] (Q.SPEC `n` (el 14 thl))))
          THEN `PATH_LENGTH (RESTN p n) = PATH_LENGTH p - n` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `n + x' < PATH_LENGTH p` by RW_TAC arith_ss []
          THEN ASSUM_LIST
                (fn thl => STRIP_ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl,el 9 thl] (Q.SPEC `n+x'` (el 3 thl))))
          THENL
           [`x''' - n < PATH_LENGTH (RESTN p n)` by RW_TAC arith_ss []
             THEN `x' <= x''' - n` by RW_TAC arith_ss []
             THEN `n + (x''' - n) = x'''` by RW_TAC arith_ss []
             THEN PROVE_TAC[],
            `n + x' <= n + x''` by RW_TAC arith_ss []
             THEN `n + x'' < PATH_LENGTH p` by RW_TAC arith_ss []
             THEN PROVE_TAC[]],
         Cases_on `!x'''. x''' < PATH_LENGTH p ==>
                          x'' <= x''' ==>
                          ?w. S_SEM M (MAP (getL M) (PATH_SEG p (x'',x''')) <> w) c r2`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Cases_on `x' < x` 
          THEN Cases_on `x < x'`
          THEN RW_TAC std_ss []
          THEN RES_TAC
          THEN `x = x'` by DECIDE_TAC
          THEN RW_TAC std_ss []
          THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC)
          THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC)
          THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC)
          THEN `x + (x'' - x) = x''` by RW_TAC arith_ss []
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x'' - x < PATH_LENGTH (RESTN p x)` by RW_TAC arith_ss []
          THEN ASSUM_LIST
                (fn thl => STRIP_ASSUME_TAC
                             (SIMP_RULE arith_ss [el 1 thl,el 3 thl,el 7 thl] 
                               (Q.SPEC `x'' - x` (el 14 thl))))
          THENL
           [`x'' <= x + x''''` by RW_TAC arith_ss []
             THEN `x + x'''' < PATH_LENGTH p` by RW_TAC arith_ss []
             THEN PROVE_TAC[],
            `x'' <= x + (x''' - x)` by RW_TAC arith_ss []
             THEN `x''' - x < PATH_LENGTH (RESTN p x)` by RW_TAC arith_ss []
             THEN `x + (x''' - x) = x'''` by RW_TAC arith_ss []
             THEN PROVE_TAC[]],
         PROVE_TAC[]]]);

(******************************************************************************
* Lemma suggested by Cindy Eisner
*
*  p |=clk! {r1} |-> {r2}
*  <=>
*  p |= ({r1} |-> {r2}! @clk!) | (({r1} |-> {r2} @ clk) & GF clk)
******************************************************************************)

val F_WEAK_IMP_STRONG_CLOCK_INFINITE_LEMMA =
 prove
  (``!M r1 r2 p c. 
      IS_INFINITE_PATH p
      ==>
      (F_SEM M p (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
        UF_SEM M p
         (F_OR
          (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)),
           F_AND
            (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)),
             F_G(F_F(F_BOOL c))))))``,
   ONCE_REWRITE_TAC[F_SEM_def]
    THEN REWRITE_TAC [F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM,F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM]
    THEN RW_TAC arith_ss 
          [UF_SEM,F_CLOCK_COMP_def,PATH_SEG_RESTN,NEXT_RISE_LESS,
           F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
           UF_SEM_F_W,UF_SEM_F_G,UF_SEM_F_F,LHAT_def,
           UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
           RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH,
           UF_SEM_F_OR]
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,GSYM S_CLOCK_COMP_ELIM]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [PROVE_TAC[],
      Cases_on
      `(?x.
          (B_SEM M (getL M (PATH_EL p x)) c /\
           !x'.
             S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
             ?x''.
               x' <= x'' /\
               S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2) /\
          !x'. x' < x ==> ~B_SEM M (getL M (PATH_EL p x')) c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
       THENL
        [Cases_on `!x. ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [],
         ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x'` (el 2 thl)))
          THEN `x' + (x'' - x') = x''` by DECIDE_TAC
          THEN PROVE_TAC[]],
      PROVE_TAC[],
      PROVE_TAC[],
      Cases_on
      `(?x.
          (B_SEM M (getL M (PATH_EL p x)) c /\
           !x'.
             S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
             ?x''.
               x' <= x'' /\
               S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2) /\
          !x'. x' < x ==> ~B_SEM M (getL M (PATH_EL p x')) c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
       THENL
        [Cases_on `!x. ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [],
         ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x'` (el 2 thl)))
          THEN ASSUM_LIST
                (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\x''. ^(concl(el 1 thl))` WOP)))
          THEN `?n. B_SEM M (getL M (PATH_EL p (x' + n))) c /\
                    !m. m < n ==> ~B_SEM M (getL M (PATH_EL p (x' + m))) c`
               by PROVE_TAC[]
          THEN Q.EXISTS_TAC `x'+n`
          THEN RW_TAC arith_ss []
          THEN `x' + (k - x') = k` by DECIDE_TAC
          THEN `(k - x') < n` by DECIDE_TAC
          THEN PROVE_TAC[]],
      PROVE_TAC[]]);

val F_WEAK_IMP_STRONG_CLOCK_FINITE_LEMMA =
 prove
  (``!M r1 r2 p c. 
      IS_FINITE_PATH p
      ==>
      (F_SEM M p (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
        UF_SEM M p
         (F_OR
          (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)),
           F_AND
            (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)),
             F_G(F_F(F_BOOL c))))))``,
   ONCE_REWRITE_TAC[F_SEM_def]
    THEN REWRITE_TAC [F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM,F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM]
    THEN RW_TAC arith_ss 
          [UF_SEM,F_CLOCK_COMP_def,PATH_SEG_RESTN,NEXT_RISE_LESS,
           F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
           UF_SEM_F_W,UF_SEM_F_G,UF_SEM_F_F,LHAT_def,
           UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
           RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH,
           UF_SEM_F_OR]
    THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,GSYM S_CLOCK_COMP_ELIM]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [DISJ1_TAC 
       THEN Q.EXISTS_TAC `x`
       THEN PROVE_TAC[],
      Cases_on
      `(?x. x < PATH_LENGTH p /\
            (B_SEM M (getL M (PATH_EL p x)) c /\
             !x'.
               x' < PATH_LENGTH (RESTN p x) ==>
               S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
               ?x''.
                 x'' < PATH_LENGTH (RESTN p x) /\ x' <= x'' /\
                 S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2) /\
            !x'.
              x' < PATH_LENGTH p ==>
              x' < x ==>
              ~B_SEM M (getL M (PATH_EL p x')) c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
       THENL
        [Cases_on `!x. x < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [],
         ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(SIMP_RULE std_ss [el 7 thl] (Q.SPEC `x'` (el 3 thl))))
          THEN RES_TAC
          THEN `x' + (x'' - x') = x''` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x'' - x'`
          THEN RW_TAC arith_ss [PATH_LENGTH_RESTN]],
      PROVE_TAC[],
      DISJ1_TAC
       THEN Q.EXISTS_TAC `x`
       THEN PROVE_TAC[],
      Cases_on
       `(?x. x < PATH_LENGTH p /\
             (B_SEM M (getL M (PATH_EL p x)) c /\
              !x'.
                x' < PATH_LENGTH (RESTN p x) ==>
                S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
                ?x''.
                  x'' < PATH_LENGTH (RESTN p x) /\ x' <= x'' /\
                  S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2) /\
             !x'.
               x' < PATH_LENGTH p ==>
               x' < x ==>
               ~B_SEM M (getL M (PATH_EL p x')) c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
       THENL
        [Cases_on `!x. x < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p x)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [],
         ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x'` (el 3 thl)))
          THEN ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(MATCH_MP (el 1 thl) (el 2 thl)))
          THEN ASSUM_LIST
                (fn thl => 
                 ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\x''. ^(concl(el 2 thl)) /\ ^(concl(el 1 thl))` WOP)))
          THEN `?n. (n < PATH_LENGTH (RESTN p x') /\
                    B_SEM M (getL M (PATH_EL p (x' + n))) c) /\
                    !m. m < n ==>
                        m < PATH_LENGTH (RESTN p x') ==>
                        ~B_SEM M (getL M (PATH_EL p (x' + m))) c`
               by PROVE_TAC[]
          THEN `PATH_LENGTH(RESTN p x') = PATH_LENGTH p - x'` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `n + x' < PATH_LENGTH p` by DECIDE_TAC
          THEN Q.EXISTS_TAC `x'+n`
          THEN RW_TAC arith_ss []
          THEN `x' + (k - x') = k` by DECIDE_TAC
          THEN `(k - x') < n` by DECIDE_TAC
          THEN `(k - x') < PATH_LENGTH (RESTN p x')` by DECIDE_TAC
          THEN PROVE_TAC[]],
      DISJ2_TAC
       THEN RW_TAC std_ss []
       THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN RES_TAC
       THEN Q.EXISTS_TAC `x + x'`
       THEN RW_TAC arith_ss [PATH_LENGTH_RESTN]]);

val F_WEAK_IMP_STRONG_CLOCK_LEMMA =
 store_thm
  ("F_WEAK_IMP_STRONG_CLOCK_LEMMA",
   ``!M r1 r2 p c. 
      F_SEM M p (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
       UF_SEM M p
        (F_OR
         (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)),
          F_AND
           (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)),
            F_G(F_F(F_BOOL c)))))``,
   REPEAT GEN_TAC
    THEN Cases_on `IS_FINITE_PATH p`
    THEN PROVE_TAC
          [NOT_IS_INFINITE_PATH,
           F_WEAK_IMP_STRONG_CLOCK_INFINITE_LEMMA,
           F_WEAK_IMP_STRONG_CLOCK_FINITE_LEMMA]);

(******************************************************************************
* Another lemma suggested by Cindy Eisner
*
*  p |= ({r1} |-> {r2}! @clk!) | (({r1} |-> {r2} @ clk) & GF clk)
*  <=>
*  p |= ([clk! U (clk & ({r1@clk} |-> {r2@clk}! |
*                        ((GF clk) & {r1@clk} |-> {r2@clk})))])
******************************************************************************)

val UF_WEAK_IMP_STRONG_CLOCK_LEMMA =
 store_thm
  ("UF_WEAK_IMP_STRONG_CLOCK_LEMMA",
   ``!M r1 r2 p c. 
       UF_SEM M p
        (F_OR
         (F_CLOCK_COMP (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)),
          F_AND
           (F_CLOCK_COMP (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)),
            F_G(F_F(F_BOOL c))))) =
       UF_SEM M p
        (F_U_CLOCK c (F_OR
                      (F_STRONG_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2),
                       F_AND
                        (F_G(F_F(F_BOOL c)),
                         F_WEAK_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2)))))``,
   ONCE_REWRITE_TAC[F_SEM_def]
    THEN REWRITE_TAC [F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM,F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM]
    THEN RW_TAC arith_ss 
          [UF_SEM,F_CLOCK_COMP_def,PATH_SEG_RESTN,NEXT_RISE_LESS,
           F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
           UF_SEM_F_W,UF_SEM_F_G,UF_SEM_F_F,LHAT_def,
           UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
           RES_FORALL,RES_EXISTS,PL_def,IN_DEF,NOT_IS_INFINITE_PATH,
           UF_SEM_F_OR]
    THEN Cases_on `IS_INFINITE_PATH p`
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,GSYM S_CLOCK_COMP_ELIM]
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [PROVE_TAC[],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN Cases_on 
                `(!x'. S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
                       ?x''.
                         x' <= x'' /\
                         S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2)`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x + x'` (el 3 thl)))
          THEN `x + x' + x''' = x + (x' + x''')` by DECIDE_TAC
          THEN PROVE_TAC[],
         PROVE_TAC[],
         PROVE_TAC[],
         Cases_on
          `(?x. (B_SEM M (getL M (PATH_EL p x)) c /\
                !x'.
                  S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
                  ?x''.
                    x' <= x'' /\
                    S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2) /\
               !x'. x' < x ==> ~B_SEM M (getL M (PATH_EL p x')) c)`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
          THENL
           [Cases_on `!x. ~B_SEM M (getL M (PATH_EL p x)) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
             THEN Q.EXISTS_TAC `x`
             THEN RW_TAC std_ss [],
            ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x'` (el 4 thl)))
             THEN `x + (x' + x'') = x' + (x + x'')` by DECIDE_TAC
             THEN PROVE_TAC[]]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [],
         Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss []
          THEN Cases_on 
                `(!x'. x' < PATH_LENGTH (RESTN p x) ==>
                       S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
                       ?x''.
                         x'' < PATH_LENGTH (RESTN p x) /\ x' <= x'' /\
                         S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2)`
          THEN RW_TAC std_ss [RESTN_RESTN]
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x`  by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `x + x' < PATH_LENGTH p` by DECIDE_TAC
          THEN `PATH_LENGTH (RESTN p (x + x')) = PATH_LENGTH p - (x + x')`  by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x + x'` (el 8 thl)))
          THEN ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(MATCH_MP (el 1 thl) (el 3 thl)))
          THEN `x + x' + x''' = x + (x' + x''')` by DECIDE_TAC
          THEN PROVE_TAC[],

         ASSUM_LIST(fn thl => (STRIP_ASSUME_TAC(SIMP_RULE arith_ss [] (Q.SPEC `0` (el 1 thl)))))
          THEN `?x'. x' < PATH_LENGTH(RESTN p 0) /\ B_SEM M (getL M (PATH_EL p x')) c`
               by ZAP_TAC arith_ss [FINITE_PATH_NONEMPTY,PATH_LENGTH_RESTN]
          THEN `PATH_LENGTH (RESTN p 0) =  PATH_LENGTH p` 
               by RW_TAC arith_ss [PATH_LENGTH_RESTN,FINITE_PATH_NONEMPTY]
          THEN PROVE_TAC[],
         DISJ1_TAC
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC std_ss [],
         Cases_on
          `(?x. x < PATH_LENGTH p /\
                (B_SEM M (getL M (PATH_EL p x)) c /\
                 !x'.
                   x' < PATH_LENGTH (RESTN p x) ==>
                   S_SEM M (MAP (getL M) (PATH_SEG p (x,x + x'))) c r1 ==>
                   ?x''.
                     x'' < PATH_LENGTH (RESTN p x) /\ x' <= x'' /\
                     S_SEM M (MAP (getL M) (PATH_SEG p (x + x',x + x''))) c r2) /\
                !x'.
                  x' < PATH_LENGTH p ==>
                  x' < x ==>
                  ~B_SEM M (getL M (PATH_EL p x')) c)`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
          THENL
           [Cases_on `!x. x < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p x)) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
             THEN Q.EXISTS_TAC `x`
             THEN RW_TAC std_ss [],
            Cases_on `x' < x` 
             THENL
              [ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `0` (el 6 thl)))
                THEN FULL_SIMP_TAC arith_ss [RESTN_RESTN]
                THEN `?x''. x'' < PATH_LENGTH (RESTN p x) /\ B_SEM M (getL M (PATH_EL p (x + x''))) c`
                     by PROVE_TAC[FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]
                THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x`  by PROVE_TAC[PATH_LENGTH_RESTN]
                THEN `x' + (x-x') = x` by DECIDE_TAC
                THEN Q.EXISTS_TAC `x-x'`
                THEN RW_TAC arith_ss [FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]
                THEN `PATH_LENGTH (RESTN p x') = PATH_LENGTH p - x'`  by PROVE_TAC[PATH_LENGTH_RESTN]
                THEN RW_TAC arith_ss [],
               ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `x'-x` (el 6 thl)))
                THEN `PATH_LENGTH (RESTN p x) = PATH_LENGTH p - x`  by PROVE_TAC[PATH_LENGTH_RESTN]
                THEN `x' - x < PATH_LENGTH (RESTN p x)` by DECIDE_TAC
                THEN ASSUM_LIST
                      (fn thl => (STRIP_ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl ] (el 3 thl))))
                THEN `x + (x' - x + x'') = x' + x''` by DECIDE_TAC
                THEN Q.EXISTS_TAC `x''`
                THEN ZAP_TAC std_ss []
                THEN FULL_SIMP_TAC arith_ss [RESTN_RESTN]]]]]);

val F_WEAK_IMP_STRONG_CLOCK_COMP_ELIM =
 store_thm
  ("F_WEAK_IMP_STRONG_CLOCK_COMP_ELIM",
   ``!M r1 r2 p c. 
       F_SEM M p (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
        UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)))``,
  PROVE_TAC[F_WEAK_IMP_STRONG_CLOCK_LEMMA, 
            UF_WEAK_IMP_STRONG_CLOCK_LEMMA,
            F_CLOCK_COMP_def]);


val F_WEAK_IMP_CLOCK_COMP_ELIM =
 store_thm
  ("F_WEAK_IMP_CLOCK_COMP_ELIM",
   ``!M r1 r2. CLOCK_COMP_CORRECT M (F_WEAK_IMP(r1,r2))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_WEAK_IMP_STRONG_CLOCK_COMP_ELIM,
     F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM]);

val F_STRONG_IMP_WEAK_CLOCK_COMP_ELIM =
 store_thm
  ("F_STRONG_IMP_WEAK_CLOCK_COMP_ELIM",
   ``!M r1 r2 p c. 
       F_SEM M p (WEAK_CLOCK c) (F_STRONG_IMP(r1,r2)) = 
        UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_STRONG_IMP(r1,r2)))``,
   ONCE_REWRITE_TAC[F_SEM_def]
    THEN REWRITE_TAC [F_WEAK_IMP_WEAK_CLOCK_COMP_ELIM,F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM]
    THEN RW_TAC (arith_ss++resd)
          [F_SEM_def,UF_SEM,F_CLOCK_COMP_def,
           F_W_CLOCK_def,F_U_CLOCK_def,PATH_EL_RESTN,L_def,
           UF_SEM_F_W,UF_SEM_F_G,UF_SEM_F_F,LHAT_def,
           UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
           NOT_IS_INFINITE_PATH,UF_SEM_F_OR,IS_FINITE_PATH_RESTN,
           PATH_EL_RESTN,IN_DEF,PL_def,
           intLib.COOPER_PROVE``(!j. ~(j < i)) = (i=0)``]
    THEN Cases_on `IS_INFINITE_PATH p`
    THEN FULL_SIMP_TAC std_ss [NOT_IS_INFINITE_PATH]
    THEN RW_TAC arith_ss [IS_FINITE_PATH_RESTN,PATH_SEG_RESTN,GSYM S_CLOCK_COMP_ELIM]
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [PROVE_TAC[],
         Cases_on `!i. ~B_SEM M (getL M (PATH_EL p i)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Q.EXISTS_TAC `k`
          THEN RW_TAC std_ss []
          THEN Cases_on `?i. !i'. ~B_SEM M (getL M (PATH_EL p (i + (i' + k)))) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
          THEN RES_TAC
          THENL
           [PROVE_TAC[],
            ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `k'` (el 3 thl)))
             THEN ASSUM_LIST
                   (fn thl => STRIP_ASSUME_TAC(Q.SPEC `k' + (i' + k)` (el 6 thl)))
             THEN PROVE_TAC[DECIDE``k' + (i' + k) >= k'``]],
         PROVE_TAC[],
         PROVE_TAC[],
         Cases_on
          `(?k. (B_SEM M (getL M (PATH_EL p k)) c /\
             !j.
              S_SEM M (MAP (getL M) (PATH_SEG p (k,j + k))) c r1 ==>
              ?k'.
                j <= k' /\
                S_SEM M (MAP (getL M) (PATH_SEG p (j + k,k + k'))) c r2) /\
           !j. j < k ==> ~B_SEM M (getL M (PATH_EL p j)) c)`
          THEN RW_TAC std_ss []
          THENL
           [Cases_on `!i. ~B_SEM M (getL M (PATH_EL p i)) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,NOT_EXISTS_THM]
             THEN Q.EXISTS_TAC `k`
             THEN RW_TAC std_ss [],
            FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
             THEN Q.EXISTS_TAC `i+k`
             THEN PROVE_TAC[intLib.COOPER_PROVE``l >= i + k ==> ?i'. l = i + (i' + k)``]],
         PROVE_TAC[]],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [DISJ1_TAC
          THEN Q.EXISTS_TAC `k`
          THEN RW_TAC std_ss [],
         Cases_on `!i. i < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p i)) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
          THEN Q.EXISTS_TAC `k`
          THEN RW_TAC std_ss []
          THEN Cases_on
                `?i. i < PATH_LENGTH (RESTN p k) /\
                  !i'.
                    i' < PATH_LENGTH (RESTN (RESTN p k) i) ==>
                    ~B_SEM M (getL M (PATH_EL p (i + (i' + k)))) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
          THEN RES_TAC
          THENL
           [`PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k`
              by RW_TAC std_ss [PATH_LENGTH_RESTN]
              THEN `k'' < PATH_LENGTH (RESTN p k)` by DECIDE_TAC
              THEN Q.EXISTS_TAC `k''`
              THEN RW_TAC std_ss [],
            FULL_SIMP_TAC arith_ss [RESTN_RESTN]
             THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` 
                   by RW_TAC std_ss [PATH_LENGTH_RESTN]
             THEN `0 < PATH_LENGTH (RESTN p k)`
                  by RW_TAC std_ss [FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]
             THEN `~(k >= k')` by PROVE_TAC[]
             THEN `k < k'` by DECIDE_TAC
             THEN `k' - k < PATH_LENGTH (RESTN p k)` by DECIDE_TAC
             THEN ASSUM_LIST
                   (fn thl => 
                    STRIP_ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (Q.SPEC `k'-k` (el 15 thl))))
             THEN `k' - k + (i'' + k) = k' + i''` by DECIDE_TAC
             THEN ASSUM_LIST
                   (fn thl => STRIP_ASSUME_TAC(Q.SPEC `k' + i''` (el 21 thl)))
             THEN `k' + i'' >= k'` by DECIDE_TAC
             THEN `0 < PATH_LENGTH (RESTN p (k' + i''))` 
                  by RW_TAC std_ss [FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]
             THEN ASSUM_LIST
                   (fn thl => 
                    STRIP_ASSUME_TAC(SIMP_RULE std_ss [el 1 thl,el 2 thl,el 4 thl] 
                                                      (LIST_CONJ[el 3 thl,el 5 thl])))
             THEN `k + (k' - k) = k'` by DECIDE_TAC            
             THEN ASSUM_LIST
                   (fn thl => 
                    STRIP_ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl,RESTN_RESTN] (el 9 thl)))
             THEN `PATH_LENGTH (RESTN p k') = PATH_LENGTH p - k'` 
                   by RW_TAC std_ss [PATH_LENGTH_RESTN]
             THEN `k' + i'' < PATH_LENGTH p` by DECIDE_TAC
             THEN RES_TAC],
         DISJ2_TAC
          THEN RW_TAC arith_ss [],
         DISJ1_TAC
          THEN Q.EXISTS_TAC `k`
          THEN RW_TAC arith_ss [],
         Cases_on
          `(?k. k < PATH_LENGTH p /\
             (B_SEM M (getL M (PATH_EL p k)) c /\
              !j.
                j < PATH_LENGTH (RESTN p k) ==>
                S_SEM M (MAP (getL M) (PATH_SEG p (k,j + k))) c r1 ==>
                ?k'. k' < PATH_LENGTH (RESTN p k) /\ j <= k' /\
                     S_SEM M (MAP (getL M) (PATH_SEG p (j + k,k + k'))) c r2) /\
             !j. j < PATH_LENGTH p ==>
                 j < k ==>
                 ~B_SEM M (getL M (PATH_EL p j)) c)`
          THEN RW_TAC std_ss []
          THENL
           [Cases_on`!i. i < PATH_LENGTH p ==> ~B_SEM M (getL M (PATH_EL p i)) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,NOT_EXISTS_THM]
             THEN Q.EXISTS_TAC `k`
             THEN RW_TAC std_ss [],
            FULL_SIMP_TAC std_ss 
             [NOT_EXISTS_THM,FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN]
             THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k`
                   by RW_TAC arith_ss [PATH_LENGTH_RESTN]
             THEN `i + k < PATH_LENGTH p` by DECIDE_TAC
             THEN Q.EXISTS_TAC `i+k`
             THEN RW_TAC std_ss []
             THEN IMP_RES_TAC(intLib.COOPER_PROVE``l >= i + k ==> ?i'. l = i + (i' + k)``)
             THEN RW_TAC std_ss []
             THEN `PATH_LENGTH (RESTN (RESTN p k) i) = PATH_LENGTH (RESTN p k) - i`
                   by RW_TAC arith_ss [PATH_LENGTH_RESTN,IS_FINITE_PATH_RESTN]
             THEN `i' < PATH_LENGTH (RESTN (RESTN p k) i)` by DECIDE_TAC
             THEN PROVE_TAC[]],
         DISJ2_TAC
          THEN ZAP_TAC std_ss [FINITE_PATH_NONEMPTY]]]);

val F_STRONG_IMP_CLOCK_COMP_ELIM =
 store_thm
  ("F_STRONG_IMP_CLOCK_COMP_ELIM",
   ``!M r1 r2. CLOCK_COMP_CORRECT M (F_STRONG_IMP(r1,r2))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_STRONG_IMP_STRONG_CLOCK_COMP_ELIM,
     F_STRONG_IMP_WEAK_CLOCK_COMP_ELIM]);

val F_STRONG_CLOCK_CLOCK_COMP_ELIM =
 store_thm
  ("F_STRONG_CLOCK_CLOCK_COMP_ELIM",
   ``!M f. CLOCK_COMP_CORRECT M f
           ==> !c1. CLOCK_COMP_CORRECT M (F_STRONG_CLOCK(f,c1))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def]);

val F_WEAK_CLOCK_CLOCK_COMP_ELIM =
 store_thm
  ("F_WEAK_CLOCK_CLOCK_COMP_ELIM",
   ``!M f. CLOCK_COMP_CORRECT M f
           ==> !c1. CLOCK_COMP_CORRECT M (F_WEAK_CLOCK(f,c1))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def]);

(******************************************************************************
* Ken McMillan's rule for compositional reasoning
* Not(f2 U f1) And Not(f1 U f2) Implies G(f1 And f2)
******************************************************************************)

val UF_SEM_NOT_UNTIL_NOT =
 store_thm
  ("UF_SEM_NOT_UNTIL_NOT",
   ``UF_SEM M p (F_NOT(F_UNTIL (f1, F_NOT f2))) =
      !i :: PL p. (!j. j < i ==> UF_SEM M (RESTN p j) f1) 
                  ==> UF_SEM M (RESTN p i) f2``,
   Cases_on `IS_FINITE_PATH p`
    THEN RW_TAC (arith_ss++resd)
          [PATH_EL_RESTN,L_def,IS_FINITE_PATH_RESTN,
           UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
           PL_def,IN_DEF,NOT_IS_INFINITE_PATH]
    THEN TRY(PROVE_TAC[])
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [ASSUM_LIST(fn thl => STRIP_ASSUME_TAC(Q.SPEC `i` (el 3 thl)))
       THEN PROVE_TAC[],
      Cases_on `?j. j < PATH_LENGTH p /\ j < k /\ ~UF_SEM M (RESTN p j) f1`
       THEN RW_TAC std_ss []
       THEN Cases_on `k < PATH_LENGTH p`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC arith_ss [NOT_EXISTS_THM]
       THEN `!j. j < k ==> j < PATH_LENGTH p` by RW_TAC arith_ss []
       THEN PROVE_TAC[]]);

val McMillan_RULE =
 store_thm
  ("McMillan_RULE",
   ``UF_SEM M p (F_NOT(F_UNTIL (f2, F_NOT f1)))
     /\
     UF_SEM M p (F_NOT(F_UNTIL (f1, F_NOT f2)))
     ==>
     UF_SEM M p (F_G(F_AND(f1,f2)))``,
   RW_TAC (std_ss++resd) [UF_SEM_NOT_UNTIL_NOT,IN_DEF]
    THEN SIMP_TAC (std_ss++resd) [UF_SEM_F_G,UF_SEM,IN_DEF]
    THEN INDUCT_THEN COMPLETE_INDUCTION ASSUME_TAC
    THEN RW_TAC arith_ss []
    THEN FULL_SIMP_TAC arith_ss [PL_def]
    THEN `!m. m < i ==> (IS_FINITE_PATH p ==> m < PATH_LENGTH p)` by RW_TAC arith_ss [PL_def]
    THEN TRY(PROVE_TAC[])
    THEN RES_TAC
    THEN DECIDE_TAC);

(******************************************************************************
* Formula implication f1 --> f2
******************************************************************************)
val F_IMPLIES_def =
 Define 
  `F_IMPLIES(f1,f2) = F_OR(F_NOT f1, f2)`;

val UF_SEM_F_IMPLIES =
 store_thm
  ("UF_SEM_F_IMPLIES",
   ``UF_SEM M p (F_IMPLIES (f1,f2)) = UF_SEM M p f1 ==> UF_SEM M p f2``,
   RW_TAC std_ss [UF_SEM,F_IMPLIES_def,UF_SEM_F_OR]
    THEN PROVE_TAC[]);

(******************************************************************************
* Iterate a function
******************************************************************************)
val ITER_def =
 Define
  `(ITER g 0 x = x) /\ (ITER g (SUC n) x = ITER g n (g x))`;

val ITER_ALT =
 prove
  (``!n x. ITER g (SUC n) x = g(ITER g n x)``,
   Induct
    THEN PROVE_TAC[ITER_def]);

(******************************************************************************
* A recursive form of a while-loop with test b and body g
******************************************************************************)
val REC_def =
 Define
  `REC f b g = !n. f n = if b n then f(g n) else n`;

val REC_ITER_LEMMA1 =
 prove
  (``REC f b g 
     ==> 
     !n x. (!m. m < n ==> b(ITER g m x)) /\ ~(b(ITER g n x)) ==> (f x = ITER g n x)``,
   DISCH_TAC
    THEN Induct
    THEN RW_TAC arith_ss [ITER_def]
    THENL
     [PROVE_TAC[REC_def],
      ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `g x` (el 3 thl)))
       THEN `b x` by PROVE_TAC[ITER_def,DECIDE ``0 < SUC m``]
       THEN `f(g x) = f x` by PROVE_TAC[REC_def]
       THEN `!m. m < n ==> b (ITER g m (g x))` by ALL_TAC
       THEN TRY(PROVE_TAC[])
       THEN RW_TAC arith_ss []
       THEN `SUC m < SUC n` by DECIDE_TAC
       THEN PROVE_TAC[ITER_def]]);

val REC_ITER_LEMMA2 =
 prove
  (``REC f b g
     /\
     (!m. m < n ==> b(seq m) ==> (seq(m+1) = g(seq m))) 
     /\ 
     (!m. m < n ==> b(seq m))
     ==> 
     (!m. m <= n ==> (seq m = ITER g m (seq 0)))``,
   STRIP_TAC
    THEN Induct
    THEN RW_TAC arith_ss [ITER_def]
    THEN `m < n` by DECIDE_TAC
    THEN RES_TAC
    THEN RES_TAC
    THEN RW_TAC std_ss [ADD1]
    THEN `m <= n` by DECIDE_TAC
    THEN PROVE_TAC[ITER_ALT,ITER_def]);

(******************************************************************************
* A kind of Hoare logic while-rule.
* b, g are arbitary functions, and f satisfies:
*
*  All x. f x = if b x then f(g x) else x
*
* The atomic proposition "s = x" means the state has value x
*
*          p |= G((s = x) --> X!(s = g x)
*     ------------------------------------------
*       p |= (s = x) --> [b W (!b & (s = f x))]
*
******************************************************************************)
val REC_UNTIL =
 store_thm
  ("REC_UNTIL",
   ``!B R f b g.
      REC f b g 
      /\
      (!n. UF_SEM (SIMPLE_KRIPKE_STRUCTURE B R) p
            (F_G
             (F_IMPLIES
              (F_AND(F_BOOL(B_PROP(\s. s = n)),F_BOOL(B_PROP b)),
               F_NEXT(F_BOOL(B_PROP(\s. s = g n)))))))
      ==> 
      (!n. UF_SEM (SIMPLE_KRIPKE_STRUCTURE B R) p
            (F_IMPLIES
              (F_BOOL(B_PROP(\s. s = n)),
               F_W(F_BOOL(B_PROP b), 
                   F_AND(F_NOT(F_BOOL(B_PROP b)), 
                         F_BOOL(B_PROP(\s. s = f n)))))))``,
   Cases_on `~(IS_FINITE_PATH p)`
    THEN RW_TAC (arith_ss++resd)
     [UF_SEM,PATH_EL_RESTN,UF_SEM_F_W,UF_SEM_F_G,IN_DEF,PL_def,L_def,B_SEM_def,
      UF_SEM_F_IMPLIES,UF_SEM_F_G,IS_FINITE_PATH_RESTN,
      getL_def,getP_def,SIMPLE_KRIPKE_STRUCTURE_def]
    THENL
     [Cases_on `!i. b (PATH_EL p i)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\i. ^(concl(el 1 thl))` WOP)))
       THEN `?n. ~b (PATH_EL p n) /\ !m. m < n ==> b (PATH_EL p m)`
            by PROVE_TAC[]
       THEN Q.EXISTS_TAC `n`
       THEN ASM_SIMP_TAC std_ss []
       THEN IMP_RES_TAC REC_ITER_LEMMA2
       THEN `!m. m < n ==> b (ITER g m (PATH_EL p 0))` by PROVE_TAC[DECIDE``m<n ==> m<=n``]
       THEN `~b (ITER g n (PATH_EL p 0))` by PROVE_TAC[DECIDE``n<=n``]
       THEN IMP_RES_TAC REC_ITER_LEMMA1
       THEN PROVE_TAC[DECIDE``m <= m``],
      RW_TAC std_ss []
       THEN Cases_on `!i. i < PATH_LENGTH p ==> b (PATH_EL p i)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] 
                         (Q.ISPEC `\i. ^(concl(el 2 thl)) /\ ^(concl(el 1 thl))` WOP)))
       THEN `?n. (n < PATH_LENGTH p /\ ~b (PATH_EL p n)) /\
                 !m. m < n ==> ~(m < PATH_LENGTH p) \/ b (PATH_EL p m)`
             by PROVE_TAC[]
       THEN Q.EXISTS_TAC `n`
       THEN `!m. m < PATH_LENGTH p ==> m < n ==> b (PATH_EL p m)` by PROVE_TAC[]
       THEN ASM_SIMP_TAC std_ss []
       THEN `!m. m < n ==> b (PATH_EL p m)` by PROVE_TAC[DECIDE``m < n /\ n < r ==> m < r``]
       THEN `!m. m < n ==> b (PATH_EL p m) ==> (PATH_EL p (m + 1) = g (PATH_EL p m))` 
            by PROVE_TAC[DECIDE``m < n /\ n < r ==> m < r``]
       THEN IMP_RES_TAC REC_ITER_LEMMA2
       THEN `!m. m < n ==> b (ITER g m (PATH_EL p 0))` by PROVE_TAC[DECIDE``m<n ==> m<=n``]
       THEN `~b (ITER g n (PATH_EL p 0))` by PROVE_TAC[DECIDE``n<=n``]
       THEN IMP_RES_TAC REC_ITER_LEMMA1
       THEN PROVE_TAC[DECIDE``m <= m``]]);

val UF_SEM_NOT_SUFFIX_IMP_FALSE =
 store_thm
  ("UF_SEM_NOT_SUFFIX_IMP_FALSE",
   ``UF_SEM M p (F_NOT (F_SUFFIX_IMP (r,F_BOOL (B_NOT B_TRUE)))) =
      ?j :: PL p. US_SEM M (LHAT M (PATH_SEG p (0,j))) r``,
   RW_TAC (arith_ss++resd) 
    [PATH_EL_RESTN,L_def,IS_FINITE_PATH_RESTN,
     UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
     PL_def,IN_DEF,NOT_IS_INFINITE_PATH]);

val UF_SEM_STRONG_IMP_DEF =
 store_thm
  ("UF_SEM_STRONG_IMP_DEF",
   ``UF_SEM M p (F_STRONG_IMP(r1,r2)) =
     UF_SEM M p 
      (F_SUFFIX_IMP(r1, F_NOT(F_SUFFIX_IMP(r2, F_BOOL(B_NOT B_TRUE)))))``,
   RW_TAC (arith_ss++resd) 
    [PATH_EL_RESTN,L_def,IS_FINITE_PATH_RESTN,
     UF_SEM,B_SEM_def,FIRST_RISE,IS_FINITE_PATH_def,
     PL_def,IN_DEF,NOT_IS_INFINITE_PATH,PATH_SEG_RESTN]
    THEN Cases_on `~(IS_FINITE_PATH p)`
    THEN RW_TAC std_ss []
    THENL
     [EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [RES_TAC
          THEN `j + (k-j) = k` by DECIDE_TAC
          THEN EXISTS_TAC ``k-j``
          THEN RW_TAC arith_ss [],
         RES_TAC
          THEN EXISTS_TAC ``j+j'``
          THEN RW_TAC arith_ss []],
      EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [RES_TAC
          THEN `PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `j + (k-j) = k` by DECIDE_TAC
          THEN EXISTS_TAC ``k-j``
          THEN RW_TAC arith_ss [],
         RES_TAC
          THEN `PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN EXISTS_TAC ``j+j'``
          THEN RW_TAC arith_ss []]]);

val F_NEXT_STRONG_CLOCK_COMP_INFINITE_ELIM =
 prove
  (``!M f. ~(IS_FINITE_PATH p) /\ CLOCK_COMP_CORRECT M f ==> 
           (F_SEM M p (STRONG_CLOCK c) (F_NEXT f) =
            UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_NEXT f)))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,RESTN_RESTN,
     FIRST_RISE,F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN,
     DECIDE``A /\ B /\ C /\ D = A /\ (B /\ C) /\ D``,DECIDE``m < n = m+1 <= n``,
     intLib.COOPER_PROVE``(!j. ~(j + 1 <= i)) = (i=0)``,
     NEXT_RISE_LESS,PL0]
    THEN EQ_TAC
    THEN RW_TAC std_ss [DECIDE``m+1 <= n = m < n``]
    THENL
     [Q.EXISTS_TAC `i`
       THEN RW_TAC std_ss []
       THEN `i + ((j-i-1) + 1) = j` by DECIDE_TAC
       THEN Q.EXISTS_TAC `j-i-1`
       THEN RW_TAC std_ss []
       THEN `i < j' + (i + 1) /\ j' + (i + 1) < j` by DECIDE_TAC
       THEN PROVE_TAC[],
     Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `k + (k' + 1)`
       THEN RW_TAC arith_ss []
       THEN `k''-k-1 < k'` by DECIDE_TAC
       THEN `(k''-k-1) + (k + 1) = k''` by DECIDE_TAC]
       THEN PROVE_TAC[]);

val F_NEXT_STRONG_CLOCK_COMP_FINITE_ELIM =
 prove
  (``!M f. IS_FINITE_PATH p /\ CLOCK_COMP_CORRECT M f ==> 
           (F_SEM M p (STRONG_CLOCK c) (F_NEXT f) =
            UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_NEXT f)))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,RESTN_RESTN,
     FIRST_RISE,F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN,
     DECIDE``A /\ B /\ C /\ D = A /\ (B /\ C) /\ D``,DECIDE``m < n = m+1 <= n``,
     intLib.COOPER_PROVE``(!j. ~(j + 1 <= i)) = (i=0)``,
     NEXT_RISE_LESS,PL0]
    THEN EQ_TAC
    THEN RW_TAC std_ss [DECIDE``m+1 <= n = m < n``]
    THENL
     [`PATH_LENGTH (RESTN p i) = PATH_LENGTH p - i` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `2 <= PATH_LENGTH (RESTN p i)` by DECIDE_TAC
       THEN Q.EXISTS_TAC `i`
       THEN RW_TAC std_ss []
       THEN `(j-i-1) < PATH_LENGTH (RESTN p (i + 1))` by RW_TAC arith_ss [PATH_LENGTH_RESTN]
       THEN Q.EXISTS_TAC `j-i-1`
       THEN RW_TAC std_ss []
       THENL
        [`i + ((j-i-1) + 1) = j` by DECIDE_TAC
           THEN PROVE_TAC[],
         `i + ((j-i-1) + 1) = j` by DECIDE_TAC
           THEN PROVE_TAC[],
         `i < j' + (i + 1) /\ j' + (i + 1) < j` by DECIDE_TAC
           THEN PROVE_TAC[]],
     Q.EXISTS_TAC `k`
       THEN RW_TAC arith_ss []
       THEN Q.EXISTS_TAC `k + (k' + 1)`
       THEN RW_TAC arith_ss []
       THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `k+1 < PATH_LENGTH p` by DECIDE_TAC
       THEN `PATH_LENGTH (RESTN p (k+1)) = PATH_LENGTH p - (k+1)` by PROVE_TAC[PATH_LENGTH_RESTN]
       THENL
        [DECIDE_TAC,
         `k''-k-1 < k'` by DECIDE_TAC
           THEN `k''-k-1 < PATH_LENGTH(RESTN p (k+1))` by DECIDE_TAC
           THEN `(k''-k-1) + (k + 1) = k''` by DECIDE_TAC
           THEN PROVE_TAC[]]]);

val F_NEXT_STRONG_CLOCK_COMP_ELIM =
 prove
  (``!M f. CLOCK_COMP_CORRECT M f ==> 
           (F_SEM M p (STRONG_CLOCK c) (F_NEXT f) =
            UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_NEXT f)))``,
   Cases_on `IS_FINITE_PATH p`
    THEN PROVE_TAC[F_NEXT_STRONG_CLOCK_COMP_FINITE_ELIM,
                   F_NEXT_STRONG_CLOCK_COMP_INFINITE_ELIM]);


val F_NEXT_WEAK_CLOCK_COMP_INFINITE_ELIM =
 prove
  (``!M f. ~(IS_FINITE_PATH p) /\ CLOCK_COMP_CORRECT M f ==> 
           (F_SEM M p (WEAK_CLOCK c) (F_NEXT f) =
            UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_NEXT f)))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,RESTN_RESTN,
     FIRST_RISE,F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN,
     DECIDE``A /\ B /\ C /\ D = A /\ (B /\ C) /\ D``,DECIDE``m < n = m+1 <= n``,
     intLib.COOPER_PROVE``(!j. ~(j + 1 <= i)) = (i=0)``,UF_SEM_F_G,
     NEXT_RISE_LESS,PL0]
    THEN EQ_TAC
    THEN RW_TAC std_ss [DECIDE``m+1 <= n = m < n``]
    THENL
     [Cases_on `!i. ~B_SEM M (getL M (PATH_EL p i)) c`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN REWRITE_TAC[DECIDE``(~A \/ B) = (A ==> B)``]
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] (Q.ISPEC `\i. ^(concl(el 1 thl))` WOP)))
       THEN `?n. B_SEM M (getL M (PATH_EL p n)) c /\
                 !m. m < n ==> ~B_SEM M (getL M (PATH_EL p m)) c`
               by PROVE_TAC[]
       THEN Q.EXISTS_TAC `n`
       THEN RW_TAC std_ss []
       THEN `?j.
              (n < j /\
               (!k. n < k /\ k < j ==> ~B_SEM M (getL M (PATH_EL p k)) c) /\
               B_SEM M (getL M (PATH_EL p j)) c) /\
              UF_SEM M (RESTN p j) (F_CLOCK_COMP (WEAK_CLOCK c) f)`
              by RW_TAC std_ss []
       THEN `n + ((j-n-1) + 1) = j` by DECIDE_TAC
       THEN Q.EXISTS_TAC `j-n-1`
       THEN RW_TAC std_ss []
       THEN `n < j' + (n + 1) /\ j' + (n + 1) < j` by DECIDE_TAC
       THEN PROVE_TAC[],
     Q.EXISTS_TAC `k + (k' + 1)`
       THEN ZAP_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [DECIDE``~A\/B = A==>B``]
       THENL
        [Cases_on `k < i`
          THEN RW_TAC arith_ss []
          THEN Cases_on `k + (k' + 1) < i`
          THEN ZAP_TAC arith_ss [],
         Cases_on `k'=0`
          THEN RW_TAC arith_ss []
          THENL
           [`k'' < k \/ (k'' = k)` by DECIDE_TAC
              THEN PROVE_TAC[],
            `k''-k-1 < k'` by DECIDE_TAC
             THEN Cases_on `k'' < k`
             THEN RW_TAC arith_ss []
             THEN `k <= k''` by DECIDE_TAC
             THEN Cases_on `k'' = k`
             THEN ZAP_TAC arith_ss []
             THEN `(k''-k-1) + (k + 1) = k''` by DECIDE_TAC
             THEN PROVE_TAC[]]],
      PROVE_TAC[]]);


val F_NEXT_WEAK_CLOCK_COMP_FINITE_ELIM =
 prove
  (``!M f. IS_FINITE_PATH p /\ CLOCK_COMP_CORRECT M f ==> 
           (F_SEM M p (WEAK_CLOCK c) (F_NEXT f) =
            UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_NEXT f)))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,UF_SEM,F_CLOCK_COMP_def,RESTN_RESTN,
     FIRST_RISE,F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN,
     DECIDE``A /\ B /\ C /\ D = A /\ (B /\ C) /\ D``,DECIDE``m < n = m+1 <= n``,
     intLib.COOPER_PROVE``(!j. ~(j + 1 <= i)) = (i=0)``,UF_SEM_F_G,
     NEXT_RISE_LESS,PL0]
    THEN EQ_TAC
    THEN RW_TAC std_ss [DECIDE``m+1 <= n = m < n``]
    THENL
     [Cases_on `!i. ~(i < PATH_LENGTH p) \/ ~B_SEM M (getL M (PATH_EL p i)) c`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN REWRITE_TAC[DECIDE``(~A \/ B) = (A ==> B)``]
       THEN ASSUM_LIST
             (fn thl => ASSUME_TAC(SIMP_RULE std_ss [] 
                         (Q.ISPEC `\i. ^(concl(el 2 thl)) /\ ^(concl(el 1 thl))` WOP)))
       THEN `?n. (n < PATH_LENGTH p /\ B_SEM M (getL M (PATH_EL p n)) c) /\
                 !m.
                   m < n ==> ~(m < PATH_LENGTH p) \/ ~B_SEM M (getL M (PATH_EL p m)) c`
             by PROVE_TAC[]
       THEN `!j. j < n ==> ~B_SEM M (getL M (PATH_EL p j)) c` 
            by PROVE_TAC[DECIDE``n < PATH_LENGTH p ==> m < n ==> m < PATH_LENGTH p``]
       THEN ASSUM_LIST
             (fn thl => STRIP_ASSUME_TAC(MATCH_MP (el 8 thl) (el 4 thl)))
       THEN ASSUM_LIST
             (fn thl => STRIP_ASSUME_TAC(MATCH_MP (el 1 thl) (LIST_CONJ[el 2 thl,el 4 thl])))
       THEN `PATH_LENGTH (RESTN p n) = PATH_LENGTH p - n` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN Q.EXISTS_TAC `n`
       THEN RW_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [DECIDE``(~A \/ B) = (A ==> B)``]
       THEN `n+1 < PATH_LENGTH p` by DECIDE_TAC
       THEN `PATH_LENGTH (RESTN p (n+1)) = PATH_LENGTH p - (n+1)` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `n + ((j-n-1) + 1) = j` by DECIDE_TAC
       THEN Q.EXISTS_TAC `j-n-1`
       THEN POP_ASSUM(fn th => RW_TAC arith_ss [th]),
     Q.EXISTS_TAC `k + (k' + 1)`
       THEN ZAP_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [DECIDE``~A\/B = A==>B``]
       THENL
        [`PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `k+1 < PATH_LENGTH p` by DECIDE_TAC
          THEN `PATH_LENGTH (RESTN p (k+1)) = PATH_LENGTH p - (k+1)` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN DECIDE_TAC,
         Cases_on `k < i`
          THEN RW_TAC arith_ss []
          THEN Cases_on `k + (k' + 1) < i`
          THEN ZAP_TAC arith_ss [],
         Cases_on `k'=0`
          THEN RW_TAC arith_ss []
          THENL
           [`PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
              THEN `k'' < k \/ (k'' = k)` by DECIDE_TAC
              THEN ZAP_TAC arith_ss [],
            `k''-k-1 < k'` by DECIDE_TAC
             THEN Cases_on `k'' < k`
             THEN RW_TAC arith_ss []
             THEN `k <= k''` by DECIDE_TAC
             THEN Cases_on `k'' = k`
             THEN ZAP_TAC arith_ss []
             THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
             THEN `k+1 < PATH_LENGTH p` by DECIDE_TAC
             THEN `PATH_LENGTH (RESTN p (k+1)) = PATH_LENGTH p - (k+1)` by PROVE_TAC[PATH_LENGTH_RESTN]
             THEN `k''-k-1 < PATH_LENGTH(RESTN p (k+1))` by DECIDE_TAC
             THEN `(k''-k-1) + (k + 1) = k''` by DECIDE_TAC
             THEN PROVE_TAC[]]],
      PROVE_TAC[]]);

val F_NEXT_WEAK_CLOCK_COMP_ELIM =
 prove
  (``!M f. CLOCK_COMP_CORRECT M f ==> 
           (F_SEM M p (WEAK_CLOCK c) (F_NEXT f) =
            UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_NEXT f)))``,
   Cases_on `IS_FINITE_PATH p`
    THEN PROVE_TAC[F_NEXT_WEAK_CLOCK_COMP_FINITE_ELIM,
                   F_NEXT_WEAK_CLOCK_COMP_INFINITE_ELIM]);

val F_NEXT_CLOCK_COMP_ELIM =
 store_thm
  ("F_NEXT_CLOCK_COMP_ELIM",
   ``!M f. CLOCK_COMP_CORRECT M f ==> CLOCK_COMP_CORRECT M (F_NEXT f)``,
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[CLOCK_COMP_CORRECT_def]
    THEN PROVE_TAC[F_NEXT_WEAK_CLOCK_COMP_ELIM,F_NEXT_STRONG_CLOCK_COMP_ELIM]);

val UF_SEM_STRONG_INFINITE_UNTIL_LEMMA =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     (UF_SEM M p (F_UNTIL(F_U_CLOCK c f1, F_U_CLOCK c f2)) =
      ?i. (?k. i <= k /\ NEXT_RISE M p c (i,k) /\ UF_SEM M (RESTN p k) f2)
          /\
          !j. j < i ==>
              ?k. j <= k /\ NEXT_RISE M p c (j,k) /\ UF_SEM M (RESTN p k) f1)``,
   RW_TAC
    (arith_ss++resd)
    [UF_SEM,RESTN_RESTN,PL0,PL_def,FIRST_RISE_RESTN,CONJ_ASSOC,
     F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,FIRST_RISE_TRUE,NEXT_RISE_TRUE,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,IS_FINITE_PATH_RESTN,NEXT_RISE_RESTN,NEXT_RISE,
     NEXT_RISE_LESS]
     THEN EQ_TAC
     THEN RW_TAC std_ss []
     THENL
      [Q.EXISTS_TAC `k`
        THEN RW_TAC std_ss []
        THENL
         [Q.EXISTS_TAC `k+k'`
           THEN RW_TAC arith_ss []
           THEN `k''-k < k'` by DECIDE_TAC
           THEN `(k''-k) + k = k''` by DECIDE_TAC
           THEN PROVE_TAC[],
          RES_TAC
           THEN Q.EXISTS_TAC `j+k''`
           THEN RW_TAC arith_ss []
           THEN `k'''-j < k''` by DECIDE_TAC
           THEN `j + (k'''-j) = k'''` by DECIDE_TAC
           THEN PROVE_TAC[]],
        Q.EXISTS_TAC `i`
         THEN RW_TAC arith_ss []
         THENL
         [Q.EXISTS_TAC `k-i`
           THEN RW_TAC arith_ss [],
          RES_TAC
           THEN Q.EXISTS_TAC `k'-j`
           THEN RW_TAC arith_ss []]]);

val F_UNTIL_STRONG_CLOCK_COMP_INFINITE_ELIM =
 prove
  (``!M f1 f2. ~(IS_FINITE_PATH p) /\ CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
           (F_SEM M p (STRONG_CLOCK c) (F_UNTIL(f1,f2)) =
            UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_UNTIL(f1, f2))))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,RESTN_RESTN,
     FIRST_RISE,PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN,
     UF_SEM_STRONG_INFINITE_UNTIL_LEMMA,F_CLOCK_COMP_def,GSYM F_U_CLOCK_def]);

val UF_SEM_STRONG_FINITE_UNTIL_LEMMA =
 prove
  (``IS_FINITE_PATH p
     ==>
     (UF_SEM M p (F_UNTIL(F_U_CLOCK c f1, F_U_CLOCK c f2)) =
      ?i :: PL p. (?k :: PL p. i <= k /\ NEXT_RISE M p c (i,k) /\ UF_SEM M (RESTN p k) f2)
          /\
          !j :: PL p. 
           j < i ==>
           ?k :: PL p. j <= k /\ NEXT_RISE M p c (j,k) /\ UF_SEM M (RESTN p k) f1)``,
   RW_TAC std_ss [NEXT_RISE_LESS,CONJ_ASSOC]
    THEN RW_TAC
          (arith_ss++resd)
          [UF_SEM,RESTN_RESTN,PL0,PL_def,FIRST_RISE_RESTN,CONJ_ASSOC,
           F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,FIRST_RISE_TRUE,NEXT_RISE_TRUE,
           PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,IS_FINITE_PATH_RESTN,NEXT_RISE_RESTN,NEXT_RISE,
           NEXT_RISE_LESS]
     THEN EQ_TAC
     THEN RW_TAC std_ss []
     THENL
      [Q.EXISTS_TAC `k`
        THEN RW_TAC std_ss []
        THENL
         [Q.EXISTS_TAC `k+k'`
           THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC [PATH_LENGTH_RESTN]
           THEN `k + k' < PATH_LENGTH p` by DECIDE_TAC
           THEN ZAP_TAC arith_ss []
           THEN `k''-k < k'` by DECIDE_TAC
           THEN `(k''-k) + k = k''` by DECIDE_TAC
           THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `k''-k < PATH_LENGTH(RESTN p k)` by DECIDE_TAC
           THEN PROVE_TAC[],
          RES_TAC
           THEN Q.EXISTS_TAC `j+k''`
           THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `j + k'' < PATH_LENGTH p` by DECIDE_TAC
           THEN RW_TAC arith_ss []
           THEN `k'''-j < k''` by DECIDE_TAC
           THEN `k'''-j < PATH_LENGTH(RESTN p j)` by DECIDE_TAC
           THEN `j + (k'''-j) = k'''` by DECIDE_TAC
           THEN PROVE_TAC[]],
        Q.EXISTS_TAC `i`
         THEN RW_TAC arith_ss []
         THENL
         [`PATH_LENGTH (RESTN p i) = PATH_LENGTH p - i` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `k-i < PATH_LENGTH (RESTN p i)` by DECIDE_TAC
           THEN Q.EXISTS_TAC `k-i`
           THEN RW_TAC arith_ss [],
          RES_TAC
           THEN Q.EXISTS_TAC `k'-j`
           THEN `PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `k' - j < PATH_LENGTH (RESTN p j)` by DECIDE_TAC
           THEN RW_TAC arith_ss []]]);

val F_UNTIL_STRONG_CLOCK_COMP_FINITE_ELIM =
 prove
  (``!M f1 f2. IS_FINITE_PATH p /\ CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
           (F_SEM M p (STRONG_CLOCK c) (F_UNTIL(f1,f2)) =
            UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_UNTIL(f1, f2))))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,RESTN_RESTN,
     FIRST_RISE,PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,PL_def,IS_FINITE_PATH_RESTN,
     UF_SEM_STRONG_FINITE_UNTIL_LEMMA,F_CLOCK_COMP_def,GSYM F_U_CLOCK_def]);

val F_UNTIL_STRONG_CLOCK_COMP_ELIM =
 prove
  (``!M f1 f2. 
       CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
        (F_SEM M p (STRONG_CLOCK c) (F_UNTIL(f1,f2)) =
         UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_UNTIL(f1, f2))))``,
   Cases_on `IS_FINITE_PATH p`
    THEN PROVE_TAC[F_UNTIL_STRONG_CLOCK_COMP_INFINITE_ELIM,F_UNTIL_STRONG_CLOCK_COMP_FINITE_ELIM]);

val UF_SEM_WEAK_INFINITE_UNTIL_LEMMA =
 prove
  (``~(IS_FINITE_PATH p)
     ==>
     (UF_SEM M p (F_UNTIL(F_W_CLOCK c f1, F_W_CLOCK c f2)) =
      ?i. ((?k. i <= k /\ NEXT_RISE M p c (i,k) /\ UF_SEM M (RESTN p k) f2)
           \/
           UF_SEM M (RESTN p i) (F_G (F_BOOL (B_NOT c))))
          /\
          !j. j < i ==>
              ((?k. j <= k /\ NEXT_RISE M p c (j,k) /\ UF_SEM M (RESTN p k) f1)
               \/
               UF_SEM M (RESTN p j) (F_G (F_BOOL (B_NOT c)))))``,
   RW_TAC
    (arith_ss++resd)
    [UF_SEM,RESTN_RESTN,PL0,PL_def,FIRST_RISE_RESTN,CONJ_ASSOC,
     F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,FIRST_RISE_TRUE,NEXT_RISE_TRUE,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,IS_FINITE_PATH_RESTN,NEXT_RISE_RESTN,NEXT_RISE,
     NEXT_RISE_LESS,UF_SEM_F_G]
     THEN EQ_TAC
     THEN RW_TAC std_ss []
     THENL
      [Q.EXISTS_TAC `k`
        THEN RW_TAC std_ss []
        THENL
         [Cases_on `!i'. ~B_SEM M (getL M (PATH_EL p (k + i'))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN Q.EXISTS_TAC `k+k'`
           THEN RW_TAC arith_ss []
           THEN `k''-k < k'` by DECIDE_TAC
           THEN `(k''-k) + k = k''` by DECIDE_TAC
           THEN PROVE_TAC[],
          Cases_on `!i'. ~B_SEM M (getL M (PATH_EL p (i' + j))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN RES_TAC
           THENL
            [Q.EXISTS_TAC `j+k''`
              THEN RW_TAC arith_ss []
              THEN `k'''-j < k''` by DECIDE_TAC
              THEN `j + (k'''-j) = k'''` by DECIDE_TAC
              THEN PROVE_TAC[],
             RES_TAC]],
       Q.EXISTS_TAC `k`
        THEN RW_TAC std_ss []
        THENL
         [Cases_on `!i'. ~B_SEM M (getL M (PATH_EL p (k + i'))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN PROVE_TAC[ADD_SYM],
          Cases_on `!i'. ~B_SEM M (getL M (PATH_EL p (i' + j))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN RES_TAC
           THENL
            [Q.EXISTS_TAC `j+k'`
              THEN RW_TAC arith_ss []
              THEN `k''-j < k'` by DECIDE_TAC
              THEN `j + (k''-j) = k''` by DECIDE_TAC
              THEN PROVE_TAC[],
             RES_TAC]],
       Q.EXISTS_TAC `i`
        THEN RW_TAC arith_ss []
        THENL
        [Cases_on `!i'. ~B_SEM M (getL M (PATH_EL p (i + i'))) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
          THEN Q.EXISTS_TAC `k-i`
          THEN RW_TAC arith_ss [],
         RES_TAC
          THENL
           [Cases_on `!i. ~B_SEM M (getL M (PATH_EL p (i + j))) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
             THEN Q.EXISTS_TAC `k'-j`
             THEN RW_TAC arith_ss [],
            Cases_on `!i. ~B_SEM M (getL M (PATH_EL p (i + j))) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
             THEN RES_TAC]],
       Q.EXISTS_TAC `i`
        THEN RW_TAC arith_ss []
        THEN Cases_on `!i. ~B_SEM M (getL M (PATH_EL p (i + j))) c`
        THEN RW_TAC std_ss []
        THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
        THEN RES_TAC
        THENL
         [Q.EXISTS_TAC `k-j`
           THEN RW_TAC arith_ss [],
          RES_TAC]]);

local

val ADD_FORALL_LEMMA1 =
 prove
  (``!P n. (!m. P(m+n)) = !m. n <= m ==> P m``,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THEN `(m-n)+n = m` by DECIDE_TAC
    THEN PROVE_TAC[]);

val ADD_FORALL_LEMMA2 =
 prove
  (``!P n. (!m. P(n+m)) = !m. n <= m ==> P m``,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THEN `(m-n)+n = m` by DECIDE_TAC
    THEN PROVE_TAC[]);

val Lemma1 =
 SIMP_RULE
  std_ss
  []
  (ISPEC
    ``\m. UF_SEM (M:'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool)) (RESTN p m) (F_BOOL (B_NOT c))``
    ADD_FORALL_LEMMA1);

val Lemma2 =
 SIMP_RULE
  std_ss
  []
  (ISPEC
    ``\m. UF_SEM (M:'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool)) (RESTN p m) (F_BOOL (B_NOT c))``
    ADD_FORALL_LEMMA2);

in

val F_UNTIL_WEAK_CLOCK_COMP_INFINITE_ELIM =
 prove
  (``!M f1 f2. ~(IS_FINITE_PATH p) /\ CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
           (F_SEM M p (WEAK_CLOCK c) (F_UNTIL(f1,f2)) =
            UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_UNTIL(f1, f2))))``,
   RW_TAC (arith_ss ++ resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,FIRST_RISE_RESTN,NEXT_RISE_TRUE,
     DECIDE ``(m = n + m) = (n=0)``,IN_DEF,PL0,PATH_EL_RESTN,PL_def,
     F_CLOCK_COMP_def,UF_SEM_WEAK_INFINITE_UNTIL_LEMMA,PATH_LENGTH_RESTN,
     IS_FINITE_PATH_RESTN,UF_SEM_F_G,RESTN_RESTN,Lemma1,Lemma2]
    THEN RW_TAC arith_ss [UF_SEM,PATH_EL_RESTN]);

end;

val UF_SEM_WEAK_FINITE_UNTIL_LEMMA =
 prove
  (``IS_FINITE_PATH p
     ==>
     (UF_SEM M p (F_UNTIL(F_W_CLOCK c f1, F_W_CLOCK c f2)) =
      ?i :: PL p.
        ((?k :: PL p. i <= k /\ NEXT_RISE M p c (i,k) /\ UF_SEM M (RESTN p k) f2)
         \/
         UF_SEM M (RESTN p i) (F_G (F_BOOL (B_NOT c))))
        /\
        !j :: PL p. j < i ==>
          ((?k :: PL p. j <= k /\ NEXT_RISE M p c (j,k) /\ UF_SEM M (RESTN p k) f1)
           \/
           UF_SEM M (RESTN p j) (F_G (F_BOOL (B_NOT c)))))``,
   RW_TAC
    (arith_ss++resd)
    [UF_SEM,RESTN_RESTN,PL0,PL_def,FIRST_RISE_RESTN,CONJ_ASSOC,
     F_U_CLOCK_def,F_W_CLOCK_def,F_W_def,F_OR_def,FIRST_RISE_TRUE,NEXT_RISE_TRUE,
     PATH_EL_RESTN,L_def,B_SEM_def,IN_DEF,IS_FINITE_PATH_RESTN,NEXT_RISE_RESTN,NEXT_RISE,
     NEXT_RISE_LESS,UF_SEM_F_G]
     THEN EQ_TAC
     THEN RW_TAC std_ss []
     THENL
      [Q.EXISTS_TAC `k`
        THEN RW_TAC std_ss []
        THENL
         [Cases_on `!i'. i' < PATH_LENGTH (RESTN p k) ==> ~B_SEM M (getL M (PATH_EL p (k + i'))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `k+k' < PATH_LENGTH p` by DECIDE_TAC
           THEN Q.EXISTS_TAC `k+k'`
           THEN RW_TAC arith_ss [NEXT_RISE]
           THEN `k''-k < k'` by DECIDE_TAC
           THEN `(k''-k) + k = k''` by DECIDE_TAC
           THEN `k''-k < PATH_LENGTH (RESTN p k)` by DECIDE_TAC
           THEN PROVE_TAC[],
          Cases_on `!i'. i' < PATH_LENGTH (RESTN p j) ==> ~B_SEM M (getL M (PATH_EL p (i' + j))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN RES_TAC
           THENL
            [`PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
              THEN RW_TAC std_ss [DECIDE``((A/\B)/\C)/\D=A/\(B/\C)/\D``,NEXT_RISE_LESS]
              THEN `j+k'' < PATH_LENGTH p` by DECIDE_TAC
              THEN Q.EXISTS_TAC `j+k''`
              THEN RW_TAC arith_ss []
              THEN `k'''-j < k''` by DECIDE_TAC
              THEN `j + (k'''-j) = k'''` by DECIDE_TAC
              THEN `PATH_LENGTH (RESTN p k) = PATH_LENGTH p - k` by PROVE_TAC[PATH_LENGTH_RESTN]
              THEN `k'''-j < PATH_LENGTH (RESTN p j)` by DECIDE_TAC
              THEN PROVE_TAC[],
             RES_TAC]],
       Q.EXISTS_TAC `k`
        THEN RW_TAC std_ss []
        THENL
         [Cases_on `!i'. i' < PATH_LENGTH (RESTN p k) ==> ~B_SEM M (getL M (PATH_EL p (k + i'))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN PROVE_TAC[ADD_SYM],
          Cases_on `!i'. i' < PATH_LENGTH (RESTN p j) ==> ~B_SEM M (getL M (PATH_EL p (i' + j))) c`
           THEN RW_TAC std_ss []
           THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
           THEN RES_TAC
           THENL
            [RW_TAC std_ss [NEXT_RISE_LESS,DECIDE``((A/\B)/\C)/\D= A/\(B/\C)/\D``]
              THEN `PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
              THEN `j+k' < PATH_LENGTH p` by DECIDE_TAC
              THEN Q.EXISTS_TAC `j+k'`
              THEN RW_TAC arith_ss []
              THEN `k''-j < k'` by DECIDE_TAC
              THEN `j + (k''-j) = k''` by DECIDE_TAC
              THEN `k''-j < PATH_LENGTH (RESTN p j)` by DECIDE_TAC
              THEN PROVE_TAC[],
             RES_TAC]],
       Q.EXISTS_TAC `i`
        THEN RW_TAC arith_ss []
        THEN FULL_SIMP_TAC std_ss [DECIDE``~A\/B = A==>B``]
        THENL
        [Cases_on `!i'. i' < PATH_LENGTH (RESTN p i) ==> ~B_SEM M (getL M (PATH_EL p (i + i'))) c`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
          THEN `PATH_LENGTH (RESTN p i) = PATH_LENGTH p - i` by PROVE_TAC[PATH_LENGTH_RESTN]
          THEN `k-i < PATH_LENGTH (RESTN p i)` by DECIDE_TAC
          THEN Q.EXISTS_TAC `k-i`
          THEN IMP_RES_TAC NEXT_RISE
          THEN SIMP_TAC std_ss [DECIDE``(A==>~B)\/C = A ==> B ==> C``]
          THEN RW_TAC arith_ss [],
         RES_TAC
          THENL
           [Cases_on `!i'. i' < PATH_LENGTH (RESTN p j) ==> ~B_SEM M (getL M (PATH_EL p (i' + j))) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
             THEN `PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
             THEN `k'-j < PATH_LENGTH (RESTN p j)` by DECIDE_TAC
             THEN Q.EXISTS_TAC `k'-j`
             THEN IMP_RES_TAC NEXT_RISE
             THEN RW_TAC arith_ss []
             THEN SIMP_TAC std_ss [DECIDE``(A==>~B)\/C = A ==> B ==> C``]
             THEN RW_TAC arith_ss [],
            Cases_on `!i'. i' < PATH_LENGTH (RESTN p j) ==> ~B_SEM M (getL M (PATH_EL p (i' + j))) c`
             THEN RW_TAC std_ss []
             THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
             THEN RES_TAC]],
       Q.EXISTS_TAC `i`
        THEN ZAP_TAC arith_ss []
        THEN Cases_on `!i. ~(i < PATH_LENGTH (RESTN p j)) \/ ~B_SEM M (getL M (PATH_EL p (i + j))) c`
        THEN RW_TAC std_ss []
        THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A\/B = A==>B``]
        THEN RES_TAC
        THENL
         [`PATH_LENGTH (RESTN p j) = PATH_LENGTH p - j` by PROVE_TAC[PATH_LENGTH_RESTN]
           THEN `k-j < PATH_LENGTH (RESTN p j)` by DECIDE_TAC
           THEN SIMP_TAC std_ss [DECIDE``(A==>~B)\/C = A ==> B ==> C``]
           THEN IMP_RES_TAC NEXT_RISE
           THEN Q.EXISTS_TAC `k-j`
           THEN RW_TAC arith_ss [DECIDE``(A==>~B)\/C = A ==> B ==> C``],
          RES_TAC]]);

val UF_SEM_RESTN_F_G =
 prove
  (``PL p n ==>(UF_SEM M (RESTN p n) (F_G f) = !i :: PL p. n <= i ==> UF_SEM M (RESTN p i) f)``,
   RW_TAC (std_ss ++ resd) [UF_SEM_F_G,IN_DEF,RESTN_RESTN,PL_def,IS_FINITE_PATH_RESTN]
    THEN Cases_on `IS_FINITE_PATH p`
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [`n < PATH_LENGTH p` by DECIDE_TAC
       THEN `PATH_LENGTH (RESTN p n) = PATH_LENGTH p - n` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `i-n < PATH_LENGTH (RESTN p n)` by DECIDE_TAC
       THEN `n+(i-n) = i` by DECIDE_TAC
       THEN PROVE_TAC[],
      `n < PATH_LENGTH p` by PROVE_TAC[]
       THEN `PATH_LENGTH (RESTN p n) = PATH_LENGTH p - n` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `n+i <  PATH_LENGTH p` by DECIDE_TAC
       THEN `n <= n+i` by DECIDE_TAC
       THEN PROVE_TAC[],
      `n+(i-n) = i` by DECIDE_TAC
       THEN PROVE_TAC[],
      `n <= n + i` by DECIDE_TAC
       THEN PROVE_TAC[]]);

val F_UNTIL_WEAK_CLOCK_COMP_FINITE_ELIM =
 prove
  (``!M f1 f2. IS_FINITE_PATH p /\ CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
           (F_SEM M p (WEAK_CLOCK c) (F_UNTIL(f1,f2)) =
            UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_UNTIL(f1, f2))))``,
   RW_TAC (std_ss++resd)
    [CLOCK_COMP_CORRECT_def,F_SEM_def,IN_DEF,FIRST_RISE_RESTN,IN_DEF,PL_def,PL0,
     F_CLOCK_COMP_def,UF_SEM_RESTN_F_G,UF_SEM_WEAK_FINITE_UNTIL_LEMMA,
     UF_SEM_F_G,RESTN_RESTN,UF_SEM_F_G,IS_FINITE_PATH_RESTN,PATH_EL_RESTN]
    THEN RW_TAC arith_ss
          [UF_SEM,PATH_EL_RESTN,NEXT_RISE_TRUE,FINITE_PATH_NONEMPTY,IS_FINITE_PATH_RESTN,
           DECIDE``(k = i + k) = (i=0)``]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `i`
       THEN ZAP_TAC std_ss [UF_SEM_RESTN_F_G]
       THEN Cases_on
             `!i'. i' < PATH_LENGTH p ==>
                   j <= i' ==>
                   B_SEM M (L M (PATH_EL p i')) (B_NOT c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN RES_TAC,
      Q.EXISTS_TAC `i`
       THEN ZAP_TAC std_ss [UF_SEM_RESTN_F_G]
       THEN Cases_on
             `!i'. i' < PATH_LENGTH (RESTN p i) ==>
                   B_SEM M (L M (PATH_EL p (i + i'))) (B_NOT c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN `PATH_LENGTH (RESTN p i) = PATH_LENGTH p - i` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `i+i' < PATH_LENGTH p` by DECIDE_TAC
       THEN `i <= i+i'` by DECIDE_TAC
       THEN PROVE_TAC[],
      Q.EXISTS_TAC `i`
       THEN ZAP_TAC std_ss [UF_SEM_RESTN_F_G],
      Q.EXISTS_TAC `i`
       THEN ZAP_TAC std_ss [UF_SEM_RESTN_F_G]
       THEN Cases_on
             `!k. k < PATH_LENGTH p ==> i <= k ==> B_SEM M (L M (PATH_EL p k)) (B_NOT c)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN `PATH_LENGTH (RESTN p i) = PATH_LENGTH p - i` by PROVE_TAC[PATH_LENGTH_RESTN]
       THEN `k-i < PATH_LENGTH (RESTN p i)` by DECIDE_TAC
       THEN `i + (k-i) = k` by DECIDE_TAC
       THEN PROVE_TAC[]]);

val F_UNTIL_WEAK_CLOCK_COMP_ELIM =
 prove
  (``!M f1 f2. 
       CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
        (F_SEM M p (WEAK_CLOCK c) (F_UNTIL(f1,f2)) =
         UF_SEM M p (F_CLOCK_COMP (WEAK_CLOCK c) (F_UNTIL(f1, f2))))``,
   Cases_on `IS_FINITE_PATH p`
    THEN PROVE_TAC[F_UNTIL_WEAK_CLOCK_COMP_INFINITE_ELIM,F_UNTIL_WEAK_CLOCK_COMP_FINITE_ELIM]);

val F_UNTIL_CLOCK_COMP_ELIM =
 prove
  (``!M f1 f2. 
       CLOCK_COMP_CORRECT M f1 /\ CLOCK_COMP_CORRECT M f2 ==> 
        CLOCK_COMP_CORRECT M (F_UNTIL(f1, f2))``,
   RW_TAC arith_ss 
    [CLOCK_COMP_CORRECT_def,F_UNTIL_STRONG_CLOCK_COMP_ELIM,
     F_UNTIL_WEAK_CLOCK_COMP_ELIM]);

val F_CLOCK_COMP_ELIM =
 store_thm
  ("F_CLOCK_COMP_ELIM",
   ``!M f. CLOCK_COMP_CORRECT M f``,
   GEN_TAC
    THEN INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss 
          [F_BOOL_CLOCK_COMP_ELIM,
           F_NOT_CLOCK_COMP_ELIM,
           F_AND_CLOCK_COMP_ELIM,
           F_SUFFIX_IMP_CLOCK_COMP_ELIM,
           F_ABORT_CLOCK_COMP_ELIM,
           F_WEAK_IMP_CLOCK_COMP_ELIM,
           F_STRONG_IMP_CLOCK_COMP_ELIM,
           F_STRONG_CLOCK_CLOCK_COMP_ELIM,
           F_WEAK_CLOCK_CLOCK_COMP_ELIM,
           F_NEXT_CLOCK_COMP_ELIM,
           F_UNTIL_CLOCK_COMP_ELIM]);

(* Examples from LRM Version 0.8 (Draft 1), page 3

always(a -> next[3] b)         -- an on-the-fly property
(SIMP_CONV
  (arith_ss++resd)
  [UF_SEM_F_G,UF_SEM_F_IMPLIES,UF_SEM_WEAK_NEXT,UF_SEM,RESTN_RESTN,PATH_EL_RESTN,IN_DEF,
   PL_def,IS_FINITE_PATH_RESTN,PATH_LENGTH_RESTN,DECIDE ``m < n - p = m + p < n``]
  THENC SIMP_CONV std_ss [GSYM PL_def])
 ``UF_SEM M p (F_G(F_IMPLIES(F_BOOL a, F_WEAK_NEXT(F_WEAK_NEXT(F_WEAK_NEXT(F_BOOL b))))))``;

always((a & next[3] b) -> c)   -- not an on-the-fly property
(SIMP_CONV
  (arith_ss++resd)
  [UF_SEM_F_G,UF_SEM_F_IMPLIES,UF_SEM_WEAK_NEXT,UF_SEM,RESTN_RESTN,PATH_EL_RESTN,IN_DEF,
   PL_def,IS_FINITE_PATH_RESTN,PATH_LENGTH_RESTN,DECIDE ``m < n - p = m + p < n``]
  THENC SIMP_CONV std_ss [GSYM PL_def])
 ``UF_SEM M p 
    (F_G(F_IMPLIES(F_AND(F_BOOL a, F_WEAK_NEXT(F_WEAK_NEXT(F_WEAK_NEXT(F_BOOL b)))),F_BOOL c)))``;

*)


val _ = export_theory();




