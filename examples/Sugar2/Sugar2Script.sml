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
val _ = intLib.deprecate_int();

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
             [EVERY_EL,CONCAT_MAP_SINGLETON,LENGTH_EL_MAP_SINGLETON,HD_EL_MAP]]);

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
     [ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 3 thl](el 5 thl)))	
       THEN IMP_RES_TAC(DECIDE ``j < i ==> i > 0``)
       THEN IMP_RES_TAC MAP_PATH_SEG_APPLED_SINGLETON_IMP
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
       THEN IMP_RES_TAC(DECIDE``(n = 1) ==> (i + 1 = m + n) ==> j < i ==> j < m``)
       THEN RES_TAC
       THEN RW_TAC std_ss []
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(REWRITE_RULE[LENGTH_MAP](el 2 thl)))
       THEN POP_ASSUM
             (fn th => 
               ASSUME_TAC
                (ISPEC 
                  ``getL (M :'a # 'b # 'c # ('d -> bool) # ('e -> 'd -> bool))`` 
                  (MATCH_MP EL_MAP th)))
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl](el 2 thl)))
       THEN ASSUM_LIST
             (fn thl  => 
               ASSUME_TAC
                (SIMP_RULE std_ss [LENGTH_MAP,LENGTH_PATH_SEG_REC,PATH_SEG_def](el 4 thl)))
       THEN IMP_RES_TAC(DECIDE``j < i - 1 - 0 + 1 ==> j <= i-1``)
       THEN PROVE_TAC[EL_MAP_PATH_SEG],
      ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 2 thl](el 4 thl)))	
       THEN ASSUM_LIST
             (fn thl => 
               ASSUME_TAC
                (SIMP_RULE arith_ss 
                  [LENGTH_MAP,LENGTH_APPEND,LENGTH,PATH_SEG_def,LENGTH_PATH_SEG_REC]
                  (Q.AP_TERM `LENGTH` (el 1 thl))))
       THEN Cases_on `i=0`
       THENL
        [RW_TAC arith_ss []
          THEN IMP_RES_TAC(DECIDE``(0 + 1 = m + SUC 0) ==> (m = 0)``)
          THEN FULL_SIMP_TAC arith_ss [LENGTH_NIL]
          THEN RW_TAC arith_ss []
          THEN FULL_SIMP_TAC list_ss [LENGTH,PATH_SEG_EL],
         IMP_RES_TAC(DECIDE``(i + 1 = m + SUC 0) ==> ~(i = 0) ==>  0 <= i-1 /\ i-1 < i``)
          THEN IMP_RES_TAC(ISPEC ``p :'e path`` PATH_SEG_SPLIT)
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC(SIMP_RULE arith_ss [el 1 thl] (el 6 thl)))
          THEN IMP_RES_TAC(DECIDE``~(i = 0) ==> (i - 1 + 1 = i)``)
          THEN POP_ASSUM
                (fn th => FULL_SIMP_TAC list_ss [MAP_APPEND,th,PATH_SEG_EL,APPEND_CANCEL])]]);

(* To be proved (needs i>0 for <== direction?)
val FIRST_RISE =
 prove
  (``FIRST_RISE M p c i = 
       (!j. j < i ==> ~B_SEM M (getL M (PATH_EL p j)) c) 
       /\ 
       B_SEM M (getL M (PATH_EL p i)) c``,
*)


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
* S_CLOCK_FREE r means r contains no clocking statements
******************************************************************************)

val S_CLOCK_FREE_def =
 Define
  `(S_CLOCK_FREE (S_BOOL b) = T)
   /\
   (S_CLOCK_FREE (S_CAT(r1,r2)) = 
     S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (S_CLOCK_FREE (S_FUSION(r1,r2)) = 
     S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_OR(r1,r2)) = 
     S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_RIG_AND(r1,r2)) = 
     S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_FLEX_AND(r1,r2)) = 
     S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2) 
   /\
   (S_CLOCK_FREE (S_REPEAT r) = 
     S_CLOCK_FREE r)
   /\
   (S_CLOCK_FREE (S_CLOCK v) = F)`;

(******************************************************************************
* Proof that if S_CLOCK_FREE r then the unclocked semantics of
* SEREs is the same as the clocked semantics with clock equal to T
******************************************************************************)

val LENGTH1 =
 prove
  (``(LENGTH l = 1) = ?x. l=[x]``,
   EQ_TAC
    THEN RW_TAC list_ss [LENGTH,LENGTH_NIL,LENGTH_CONS,arithmeticTheory.ONE]);

val S_SEM_TRUE_LEMMA =
 prove
  (``!p1 p2 p3 p4 p5 w r. 
      S_CLOCK_FREE r
      ==>
      (S_SEM (p1,p2,p3,p4,p5) w B_TRUE r =
        US_SEM (p1,p2,p3,p4,p5) w r)``,
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


val _ = export_theory();
