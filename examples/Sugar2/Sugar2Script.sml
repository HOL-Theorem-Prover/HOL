(*****************************************************************************)
(* Some sanity checking properties of the Sugar 2.0 semantics in HOL         *)
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
load "rich_listTheory"; load "intLib"; load "res_quanTheory";

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

val FINITE_PL =
 store_thm
  ("FINITE_PL",
   ``IS_FINITE_PATH p ==> PL p 0``,
   RW_TAC std_ss [PL_def,FINITE_PATH_NONEMPTY]);
   
val NEXT_TRUE_GE =
 store_thm
  ("NEXT_TRUE_GE",
   ``x' >= x /\ NEXT_RISE M p B_TRUE (x,x') = (x=x')``,
   EQ_TAC
    THEN RW_TAC arith_ss [NEXT_RISE_TRUE]
    THEN IMP_RES_TAC(DECIDE``x' >= x = x <= x'``)
    THEN FULL_SIMP_TAC std_ss [NEXT_RISE_TRUE]);

(******************************************************************************
* Strong clocking with T equal to weaking clocking with T for infinite paths
* IS_INFINITE_PATH p ==> (p |=T!= f  <==>  p |=T= f)
******************************************************************************)
val F_SEM_INFINITE_TRUE_EQ =
 store_thm
  ("F_SEM_INFINITE_TRUE_EQ",
   ``!f M p. 
      IS_INFINITE_PATH p
      ==>
      (F_SEM M p (STRONG_CLOCK B_TRUE) f = F_SEM M p (WEAK_CLOCK B_TRUE) f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss
          [F_SEM_def,FIRST_RISE_TRUE,B_SEM_def,
           RES_FORALL,RES_EXISTS,IN_DEF,RESTN_def,
           NEXT_RISE_TRUE_EXISTS]
    THEN IMP_RES_TAC NOT_IS_INFINITE_PATH
    THEN IMP_RES_TAC INFINITE_PL
    THEN RW_TAC arith_ss 
          [intLib.COOPER_PROVE ``((?k. !l. ~(l >= k))=F) /\ ((?k. !l. ~(l > k))=F)``,
           NEXT_RISE_LEQ_TRUE_EXISTS,
           NEXT_TRUE_GE,SAME_PATH_KIND_def,PL_def,IS_FINITE_PATH_RESTN]
    THEN TRY(PROVE_TAC[IS_INFINITE_PATH_RESTN,IS_INFINITE_PATH_CAT]));

val PL_EXISTS_FORALL_LEMMA =
 store_thm
  ("PL_EXISTS_FORALL_LEMMA",
   ``IS_FINITE_PATH p 
     ==> 
     ((PL p x /\ !x'. PL p x' ==> ~(x' >= x)) = F)``,
   ZAP_TAC arith_ss 
    [PL_def,
     intLib.COOPER_PROVE``x < n /\ (!x'. x' < n ==> ~(x' >= x)) = F``]);

val SAME_PATH_KIND_LEMMA =
 store_thm
  ("SAME_PATH_KIND_LEMMA",
   ``SAME_PATH_KIND p1 p2 /\ IS_FINITE_PATH p1 ==> IS_FINITE_PATH p2``,
    PROVE_TAC [SAME_PATH_KIND]);

(******************************************************************************
* Strong clocking with T equal to weaking clocking with T for finite paths:
* IS_FINITE p ==> (p |=T!= f  <==>  p |=T= f)
******************************************************************************)
local
val INIT_TAC =
 RW_TAC std_ss 
  [F_SEM_def,FIRST_RISE_TRUE,B_SEM_def,RES_FORALL,RES_EXISTS,IN_DEF,FINITE_PL,
   NEXT_RISE_TRUE_EXISTS,RESTN_def,IS_FINITE_PATH_RESTN];
in
val F_SEM_FINITE_TRUE_EQ =
 store_thm
  ("F_SEM_FINITE_TRUE_EQ",
   ``!f M p. 
      IS_FINITE_PATH p
      ==>
      (F_SEM M p (STRONG_CLOCK B_TRUE) f = F_SEM M p (WEAK_CLOCK B_TRUE) f)``,
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
      INIT_TAC 
       THEN RW_TAC arith_ss 
             [PL_EXISTS_FORALL_LEMMA,FINITE_PATH_NONEMPTY],
      (* F_SUFFIX_IMP(s,f) *)
      INIT_TAC,
      (* F_STRONG_IMP(s1,s2) *)
      INIT_TAC 
       THEN RW_TAC arith_ss 
             [PL_EXISTS_FORALL_LEMMA,FINITE_PATH_NONEMPTY],
      (* F_WEAK_IMP(s1,s2) *)
      INIT_TAC 
       THEN EQ_TAC
       THEN RW_TAC std_ss [NEXT_RISE_TRUE_COR]
       THEN PROVE_TAC[],
      (* F_ABORT(f,b)) *)
      INIT_TAC 
       THEN PROVE_TAC[IS_FINITE_PATH_CAT,SAME_PATH_KIND_LEMMA],
      (* F_WEAK_CLOCK(f,c) *)
      INIT_TAC,
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC]);
end;

val F_SEM_TRUE_EQ =
 store_thm
  ("F_SEM_TRUE_EQ",
   ``!p f M. 
       F_SEM M p (STRONG_CLOCK B_TRUE) f = F_SEM M p (WEAK_CLOCK B_TRUE) f``,
   Cases
    THEN PROVE_TAC[IS_INFINITE_PATH_def,IS_FINITE_PATH_def,
                   F_SEM_INFINITE_TRUE_EQ,F_SEM_FINITE_TRUE_EQ]);

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
        ?p' :: SAME_PATH_KIND p. 
          UF_SEM M (RESTN p j) (F_BOOL b) /\ 
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
        ?p' :: SAME_PATH_KIND p.
          UF_SEM M (RESTN p j) (F_BOOL b) /\ 
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
* Sanity checking that F_UNTIL(F_BOOL B_TRUE, f) get right semantics
* with strong clock T
******************************************************************************)
local
val INIT_TAC =
 RW_TAC arith_ss 
  [F_SEM_def,UF_SEM_def,F_CLOCK_FREE_def,FIRST_RISE_TRUE,RESTN_def,B_SEM_def,
   PL_def,RES_FORALL_DEF,RES_EXISTS_DEF,IN_DEF,FINITE_PATH_NONEMPTY,
   DECIDE``0 < n-1 = n > 1``,DECIDE``n >= 0``,DECIDE``0 <= n``];
in
val F_TRUE_UNTIL = 
 store_thm
  ("F_TRUE_UNTIL",
   ``F_SEM M p (STRONG_CLOCK B_TRUE) (F_UNTIL(F_BOOL B_TRUE, f)) =
      ?n :: PL p. F_SEM M (RESTN p n) (STRONG_CLOCK B_TRUE) f ``,
   INIT_TAC
    THEN EQ_TAC
    THEN ZAP_TAC std_ss []
    THEN Q.EXISTS_TAC `0`
    THEN ZAP_TAC std_ss [FINITE_PATH_NONEMPTY,DECIDE``n >= 0``]);
end;

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
      INIT_TAC THEN RW_TAC std_ss [B_SEM_def]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `x'`
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC std_ss [DECIDE ``0 <= n``],
         Q.EXISTS_TAC `0`
          THEN RW_TAC std_ss [FINITE_PATH_NONEMPTY]
          THEN Q.EXISTS_TAC `x`
          THEN RW_TAC arith_ss []],
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
* Some abbreviations needed for definition of F_CLOCK_COMP
******************************************************************************)

val F_U_CLOCK_def =
 Define
  `F_U_CLOCK c f = F_UNTIL(F_BOOL(B_NOT c),F_AND(F_BOOL c, f))`;

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

val UF_SEM_NOT_F_G =
 store_thm
  ("UF_SEM_NOT_F_G",
   ``~(UF_SEM M p (F_G f)) =
       ?i :: PL p. UF_SEM M (RESTN p i) (F_NOT f)``,
   RW_TAC std_ss [UF_SEM,F_G_def,UF_SEM_F_F,RES_EXISTS,RES_FORALL]
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

(******************************************************************************
* Rules for compiling clocked FL formulas to unclocked formulas
* (from B.1, page 66 and 67, of Sugar 2.0 Accellera document)
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
      F_U_CLOCK c (F_NEXT(F_CLOCK_COMP (STRONG_CLOCK c) f)))
    /\
    (F_CLOCK_COMP (STRONG_CLOCK c) (F_UNTIL(f1,f2)) = 
      F_UNTIL(F_U_CLOCK c f1, F_U_CLOCK c f2))
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
      F_W_CLOCK c (F_NEXT(F_CLOCK_COMP (WEAK_CLOCK c) f)))
    /\
    (F_CLOCK_COMP (WEAK_CLOCK c) (F_UNTIL(f1,f2)) = 
      F_UNTIL(F_W_CLOCK c f1, F_W_CLOCK c f2))
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
* p |=k= f  <==>  p |= (F_CLOCK_COMP k f)
* where k is (STRONG_CLOCK c) or (WEAK_CLOCK c)
*
* We proceed case by case.
******************************************************************************)

val F_BOOL_STRONG_CLOCK_COMP_ELIM =
 store_thm
  ("F_BOOL_STRONG_CLOCK_COMP_ELIM",
   ``!b M p c.
      F_SEM M p (STRONG_CLOCK c) (F_BOOL b) =
       UF_SEM M p (F_CLOCK_COMP (STRONG_CLOCK c) (F_BOOL b))``,
   RW_TAC std_ss [F_SEM_def, UF_SEM_def, F_CLOCK_COMP_def,PATH_EL_RESTN,
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
   RW_TAC std_ss [F_SEM_def, UF_SEM_def, F_CLOCK_COMP_def,F_W_CLOCK_def,
                  UF_SEM_F_W,FIRST_RISE,PATH_EL_RESTN]
    THEN Cases_on `UF_SEM M p (F_G (F_BOOL (B_NOT c)))`
    THEN RW_TAC std_ss []
    THENL
     [RW_TAC std_ss [RES_FORALL, IN_DEF]
       THEN FULL_SIMP_TAC std_ss
             [UF_SEM,B_SEM_def,UF_SEM_F_G,RES_FORALL,IN_DEF,PATH_EL_RESTN,L_def]
       THEN RES_TAC,
      FULL_SIMP_TAC std_ss
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

val _ = export_theory();



