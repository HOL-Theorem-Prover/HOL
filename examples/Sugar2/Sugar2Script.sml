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
open Globals HolKernel Parse boolLib;
infixr 3 -->;
infix 8 by;
infix &&;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open bossLib;

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
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val S_REPEAT_BOOL_TRUE =
 store_thm
  ("S_REPEAT_BOOL_TRUE",
   ``S_SEM M w B_TRUE (S_REPEAT(S_BOOL b))  = 
      !i. i < LENGTH w ==> B_SEM M (EL i w) b``,
   RW_TAC std_ss 
    [S_SEM_def,B_SEM_def,CONJ_ASSOC, LENGTH_CONS,LENGTH_NIL,
     Cooper.COOPER_PROVE ``(n >= 1 /\ !i. ~(1 <= i) \/ ~(i < n)) = (n = 1)``]
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

val F_SEM_TRUE_EQ_LEMMA =
 store_thm
  ("F_SEM_TRUE_EQ_LEMMA",
   ``!m1 m2 m3 m4 m5 p v1 f v2.
       (v1 = STRONG_CLOCK B_TRUE) /\
       (v2 = WEAK_CLOCK B_TRUE)
       ==>
       (F_SEM (m1,m2,m3,m4,m5) p v1 f =
         F_SEM (m1,m2,m3,m4,m5) p v2 f)``,
   recInduct (fetch "Sugar2Semantics" "F_SEM_ind")
    THEN REPEAT CONJ_TAC
    THEN RW_TAC std_ss 
          [F_SEM_def,FIRST_RISE_TRUE,B_SEM_def,
           intLib.COOPER_PROVE ``(?k. !l. ~(l > k))=F``,NEXT_RISE_TRUE_EXISTS]
    THEN PROVE_TAC[]);

val F_SEM_TRUE_EQ =
 store_thm
  ("F_SEM_TRUE_EQ",
   ``!m1 m2 m3 m4 m5 p v1 f v2.
       (F_SEM (m1,m2,m3,m4,m5) p (STRONG_CLOCK B_TRUE) f =
         F_SEM (m1,m2,m3,m4,m5) p (WEAK_CLOCK B_TRUE) f)``,
   RW_TAC std_ss [F_SEM_TRUE_EQ_LEMMA]);

val F_SEM_TRUE_EQ =
 store_thm
  ("F_SEM_TRUE_EQ",
   	``F_SEM M p (STRONG_CLOCK B_TRUE) f = F_SEM M p (WEAK_CLOCK B_TRUE) f``,
   Cases_on `M` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r`
    THEN RW_TAC std_ss [F_SEM_TRUE_EQ_LEMMA]);

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
          (*  deleted then undeleted for proof *)
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
(*     UF_SEM M p (F_STRONG_IMP(r1,r2))     *)
       (!j. US_SEM M (LHAT M (PATH_SEG p (0,j))) r1
          ==>
          ?k. US_SEM M (LHAT M (PATH_SEG p (j,k))) r2)
       \/
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
          (*  deleted then undeleted for proof *)
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
       UF_SEM M p (F_STRONG_IMP(r1,r2))   
       \/
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
* SEREs is the same as the clocked semantics with clock equal to T
******************************************************************************)
val S_SEM_TRUE_LEMMA =
 prove
  (``!m1 m2 m3 m4 m5 w r. 
      S_CLOCK_FREE r
      ==>
      (S_SEM (m1,m2,m3,m4,m5) w B_TRUE r =
        US_SEM (m1,m2,m3,m4,m5) w r)``,
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

val INIT_TAC =
 RW_TAC std_ss 
  [F_SEM_def,UF_SEM_def,F_CLOCK_FREE_def,FIRST_RISE_TRUE,RESTN_def,
   DECIDE``0 < n-1 = n > 1``,DECIDE``n >= 0``,DECIDE``0 <= n``];

(* Proof in progress
fun g t = set_goal([],t);
fun CHEAT(asl,t) = ([],fn [] => mk_thm([],t));
fun step () = e(CHEAT);
*)

val F_SEM_TRUE_LEMMA =
 store_thm
  ("F_SEM_TRUE_LEMMA",
   ``!m1 m2 m3 m4 m5 p f. 
      F_CLOCK_FREE f
      ==>
      (F_SEM (m1,m2,m3,m4,m5) p (STRONG_CLOCK B_TRUE) f =
        UF_SEM (m1,m2,m3,m4,m5) p f)``,
   recInduct (fetch "-" "UF_SEM_ind")
    THEN REPEAT CONJ_TAC
    THENL
     [(* F_STRONG_CLOCK v16 *)
      INIT_TAC,
      (* F_WEAK_CLOCK v14 *)
      INIT_TAC,
      (* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC,
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
      INIT_TAC THEN RW_TAC std_ss [S_SEM_TRUE,NEXT_RISE_TRUE_EXISTS],
      (* F_ABORT(f,b)) *)
      INIT_TAC THEN RW_TAC std_ss [B_SEM_def]]);

val _ = export_theory();
