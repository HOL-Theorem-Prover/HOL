(*****************************************************************************)
(* Some sanity checking properties of the Sugar 2.0 semantics in HOL         *)
(*****************************************************************************)

(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(*
load "Sugar2SemanticsTheory"; load "rich_listTheory"; load "intLib";
*)


(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open Globals HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open Sugar2SemanticsTheory PathTheory listTheory rich_listTheory;

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
 prove
  (``FIRST_RISE M p c i ==>
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
 prove
  (``NEXT_RISE M p c (i,j) ==>
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
 prove
  (``!f. n < LENGTH l ==> (EL n (MAP f l) = f (EL n l))``,
   RW_TAC std_ss [EL_MAP]);

val FIRST_RISE_REVIMP =
 prove
  (``(!j. j < i ==> ~B_SEM M (getL M (PATH_EL p j)) c) 
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
 prove
  (``i <= j                                                       /\
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

val NEXT_RISE_TRUE_EXISTS =
 prove
  (``?k. NEXT_RISE M p B_TRUE (j,k)``,
   Q.EXISTS_TAC `j`
    THEN RW_TAC std_ss 
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
* Strong clocking with T equal to weaking clocking with T:
* p |=T!= f  <==>  p |=T= f
******************************************************************************)
val F_SEM_TRUE_EQ =
 store_thm
  ("F_SEM_TRUE_EQ",
   ``!f M p. 
      (F_SEM M p (STRONG_CLOCK B_TRUE) f = F_SEM M p (WEAK_CLOCK B_TRUE) f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss 
          [F_SEM_def,FIRST_RISE_TRUE,B_SEM_def,
           intLib.COOPER_PROVE ``(?k. !l. ~(l > k))=F``,NEXT_RISE_TRUE_EXISTS]
    THEN PROVE_TAC[]);

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
      (IS_FINITE_PATH p ==> PATH_LENGTH p > 1) /\
       UF_SEM M (RESTN p 1) f)
    /\
    (UF_SEM M p (F_UNTIL(f1,f2)) = 
      ?k. (IS_FINITE_PATH p ==> k < PATH_LENGTH p) /\
          UF_SEM M (RESTN p k) f2              /\
          !j. j < k ==> UF_SEM M (RESTN p j) f1)
    /\
    (UF_SEM M p (F_SUFFIX_IMP(r,f)) = 
      !j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r
          ==>
          UF_SEM M (RESTN p j) f)
    /\
    (UF_SEM M p (F_STRONG_IMP(r1,r2)) = 
      !j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1
          ==>
          ?k. US_SEM M (LHAT M (PATH_SEG p (j,k))) r2)
    /\
    (UF_SEM M p (F_WEAK_IMP(r1,r2)) = 
      !j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1 ==>
           (?k. US_SEM M (LHAT M (PATH_SEG p (j,k))) r2) \/
           !k. (IS_FINITE_PATH p ==> k < PATH_LENGTH p)
               ==> ?w. US_SEM M (LHAT M (PATH_SEG p (j,k)) <> w) r2)  
    /\
    (UF_SEM M p (F_ABORT (f,b)) =
      UF_SEM M p f 
      \/
      ?j p'. UF_SEM M (RESTN p j) (F_BOOL b) /\ 
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
       (IS_FINITE_PATH p ==> PATH_LENGTH p > 1) /\
        UF_SEM M (RESTN p 1) f)
     /\
     (UF_SEM M p (F_UNTIL(f1,f2)) = 
       ?k. (IS_FINITE_PATH p ==> k < PATH_LENGTH p) /\
           UF_SEM M (RESTN p k) f2              /\
           !j. j < k ==> UF_SEM M (RESTN p j) f1)
     /\
     (UF_SEM M p (F_SUFFIX_IMP(r,f)) = 
       !j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r
           ==>
           UF_SEM M (RESTN p j) f)
     /\
     (UF_SEM M p (F_STRONG_IMP(r1,r2)) = 
       !j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1
           ==>
           ?k. US_SEM M (LHAT M (PATH_SEG p (j,k))) r2)
     /\
    (UF_SEM M p (F_WEAK_IMP(r1,r2)) = 
       !j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1 ==>
           (?k. US_SEM M (LHAT M (PATH_SEG p (j,k))) r2) \/  
           !k. (IS_FINITE_PATH p ==> k < PATH_LENGTH p)
               ==> ?w. US_SEM M (LHAT M (PATH_SEG p (j,k)) <> w) r2)  
     /\
     (UF_SEM M p (F_ABORT (f,b)) =
       UF_SEM M p f 
       \/
       ?j p'. UF_SEM M (RESTN p j) (F_BOOL b) /\ 
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

(******************************************************************************
* Old proof (now commented out)
val S_SEM_TRUE_LEMMA =
 prove
  (``!M w r. 
      S_CLOCK_FREE r
      ==>
      (S_SEM M w B_TRUE r = US_SEM M w r)``,
   recInduct (fetch "-" "US_SEM_ind")
    THEN RW_TAC std_ss [S_SEM_def, US_SEM_def, S_CLOCK_FREE_def]
    THENL
     [RW_TAC std_ss 
       [B_SEM_def,CONJ_ASSOC,LENGTH1,
        intLib.COOPER_PROVE ``n >= 1 /\ (!i. ~(1 <= i) \/ ~(i < n)) = (n = 1)``]
       THEN EQ_TAC
       THEN RW_TAC list_ss [LENGTH]
       THEN RW_TAC list_ss [LENGTH]
       THEN FULL_SIMP_TAC list_ss [LENGTH],
      RW_TAC list_ss [EVERY_EL]
       THEN EQ_TAC
       THEN RW_TAC list_ss [LENGTH]
       THEN Q.EXISTS_TAC `wlist`
       THEN FULL_SIMP_TAC list_ss [EVERY_EL]
       THEN ZAP_TAC list_ss [EL_IS_EL]]);
******************************************************************************)

val S_SEM_TRUE_LEMMA =
 prove
  (``!r M w. 
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
    THEN RW_TAC std_ss [ S_SEM_TRUE_LEMMA]);

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
* Proof that if F_CLOCK_FREE f then the unclocked semantics of
* an FL formula f is the same as the clocked semantics with clock equal to T
******************************************************************************)
local
val INIT_TAC =
 RW_TAC std_ss 
  [F_SEM_def,UF_SEM_def,F_CLOCK_FREE_def,FIRST_RISE_TRUE,RESTN_def,
   DECIDE``0 < n-1 = n > 1``,DECIDE``n >= 0``,DECIDE``0 <= n``]
in
val F_SEM_TRUE_LEMMA =
 store_thm
  ("F_SEM_TRUE_LEMMA",
   ``!M p f. 
      F_CLOCK_FREE f 
      ==>
      (F_SEM M p (WEAK_CLOCK B_TRUE) f = UF_SEM M p f)``,
   REWRITE_TAC[GSYM F_SEM_TRUE_EQ]
    THEN recInduct (fetch "-" "UF_SEM_ind")
    THEN REPEAT CONJ_TAC
    THENL
     [(* F_STRONG_CLOCK v16 *)
      INIT_TAC,
      (* F_WEAK_CLOCK v14 *)
      INIT_TAC,
      (* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC THEN RW_TAC std_ss [GSYM F_SEM_TRUE_EQ],
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      INIT_TAC,
      (* F_UNTIL(f1,f2) f *)
      INIT_TAC THEN RW_TAC std_ss [B_SEM_def],
      (* F_SUFFIX_IMP f *)
      INIT_TAC THEN RW_TAC std_ss [S_SEM_TRUE],
      (* F_STRONG_IMP f *)
      INIT_TAC THEN RW_TAC std_ss [S_SEM_TRUE],
      (* F_WEAK_IMP f *)
      INIT_TAC THEN ZAP_TAC std_ss [S_SEM_TRUE,NEXT_RISE_TRUE_EXISTS],
      (* F_ABORT(f,b)) *)
      INIT_TAC THEN RW_TAC std_ss [B_SEM_def]])
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
 prove
  (``LENGTH l >= 1 ==> ~(l = [])``,
   RW_TAC list_ss [DECIDE``m>=1 = ~(m=0)``,LENGTH_NIL]);

val EL_BUTLAST =
 prove
  (``!w n. n < PRE(LENGTH w) ==> (EL n (BUTLAST w) = EL n w)``,
   Induct
    THEN RW_TAC list_ss [FRONT_DEF]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]);

val EL_PRE_LENGTH =
 prove
  (``!w. LENGTH w >= 1 ==> (EL (LENGTH w - 1) w = LAST w)``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `LENGTH w`
    THEN RW_TAC list_ss [EL,LAST_DEF]
    THEN IMP_RES_TAC LENGTH_NIL
    THEN IMP_RES_TAC(SIMP_CONV list_ss [] ``LENGTH [] = SUC n``)
    THEN RES_TAC
    THEN FULL_SIMP_TAC arith_ss []);
 
val EVERY_EL_SINGLETON_LENGTH =
 prove
  (``!wlist P.
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
 prove
  (``!wlist P.
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
          THEN IMP_RES_TAC(DECIDE``n < m ==> (m = PRE p) ==> (1 <= SUC n /\ SUC n < p)``)
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

val F_F_def =
 Define
  `F_F f = F_UNTIL(F_BOOL B_TRUE, f)`;

val F_G_def =
 Define
  `F_G f = F_NOT(F_F(F_NOT f))`;

val F_W_def =
 Define
  `F_W(f1,f2) = F_OR(F_UNTIL(f1,f2), F_G f1)`;

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

val _ = export_theory();



