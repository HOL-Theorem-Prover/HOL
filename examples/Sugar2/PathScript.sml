(*****************************************************************************)
(* Create PathTheory to support Sugar2Theory                                 *)
(*****************************************************************************)

(* Load additional definitions of functions on lists 
   (commented out for compilation)
load "rich_listTheory"; load "intLib";
*)

(* Boilerplate needed for compilation *)
open Globals HolKernel Parse boolLib;
infixr 3 -->;
infix 8 by;
infix &&;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open bossLib;

open listTheory rich_listTheory intLib;

val _ = intLib.deprecate_int();

(******************************************************************************
* Start a new theory called Path
******************************************************************************)
val _ = new_theory "Path";

(******************************************************************************
* Infix list concatenation
******************************************************************************)
val _ = set_fixity "<>" (Infixl 500);
val APPEND_INFIX_def =  xDefine "APPEND_INFIX" `$<>  = APPEND`;

(******************************************************************************
* Concatenate a list of lists
******************************************************************************)
val CONCAT_def =
 Define `(CONCAT [] = []) /\ (CONCAT(l::ll) = l <> CONCAT ll)`;

(******************************************************************************
* A path is is finite ot infinite
******************************************************************************)
val path_def =
 Hol_datatype
  `path = FINITE_PATH   of 's list
        | INFINITE_PATH of (num -> 's)`;

(******************************************************************************
* Tests
******************************************************************************)
val IS_FINITE_PATH_def = 
 Define `(IS_FINITE_PATH(FINITE_PATH l)   = T)
         /\
         (IS_FINITE_PATH(INFINITE_PATH f) = F)`;

val IS_INFINITE_PATH_def = 
 Define `(IS_INFINITE_PATH(FINITE_PATH l)   = F)
         /\
         (IS_INFINITE_PATH(INFINITE_PATH f) = T)`;

(******************************************************************************
* PATH_LENGTH(FINITE_PATH l) = LENGTH l
* (PATH_LENGTH is not specified on infinite paths)
******************************************************************************)
val PATH_LENGTH_def = 
 Define `PATH_LENGTH (FINITE_PATH l)   = LENGTH l`;

(******************************************************************************
* HEAD (p0 p1 p2 p3 ...) = p0(p1 p2 p3 ...)
******************************************************************************)
val HEAD_def = 
 Define `(HEAD (FINITE_PATH l)   = HD l)
         /\
         (HEAD (INFINITE_PATH f) = f 0)`;

(******************************************************************************
* REST (p0 p1 p2 p3 ...) = (p1 p2 p3 ...)
******************************************************************************)
val REST_def = 
 Define `(REST (FINITE_PATH l)   = FINITE_PATH(TL l))
         /\
         (REST (INFINITE_PATH f) = INFINITE_PATH(\n. f(n+1)))`;

(******************************************************************************
* RESTN (p0 p1 p2 p3 ...) n = (pn p(n+1) p(n+2) ...)
******************************************************************************)
val RESTN_def = 
 Define `(RESTN p 0 = p) /\ (RESTN p (SUC n) = RESTN (REST p) n)`;

(******************************************************************************
* PATH_EL (p0 p1 p2 p3 ...) n = pn
******************************************************************************)
val PATH_EL_def = Define ` PATH_EL p n = HEAD(RESTN p n)`;

(******************************************************************************
* Form needeed for computeLib
******************************************************************************)
val RESTN_AUX = 
 store_thm
  ("RESTN_AUX",
   ``RESTN p n = if n=0 then p else RESTN (REST p) (n-1)``,
   Cases_on `n` THEN RW_TAC arith_ss [RESTN_def]);

val _ = computeLib.add_funs[RESTN_AUX];

(******************************************************************************
* PATH_SEG_REC m n p = [p(n); p(n+1); ... ; p(n+m)]
* (Recursive form for easy definition using Define)
******************************************************************************)
val PATH_SEG_REC_def =
 Define
  `(PATH_SEG_REC 0 n p = [])
   /\
   (PATH_SEG_REC (SUC m) 0 p = (HEAD p)::PATH_SEG_REC m 0 (REST p))
   /\
   (PATH_SEG_REC (SUC m) (SUC n) p = PATH_SEG_REC (SUC m) n (REST p))`;

(******************************************************************************
* PATH_SEG_REC m n p = [p(n); p(n+1); ... ; p(n+m-1)]
* (Version for computeLib)
******************************************************************************)
val PATH_SEG_REC_AUX =
 store_thm
  ("PATH_SEG_REC_AUX",
   ``PATH_SEG_REC m n p =
      if m = 0   then [] else
      if (n = 0) then (HEAD p)::PATH_SEG_REC (m-1) 0 (REST p) 
                 else PATH_SEG_REC m (n-1) (REST p)``,
    Cases_on `m` THEN Cases_on `n` THEN RW_TAC arith_ss [PATH_SEG_REC_def]);

val _ = computeLib.add_funs[PATH_SEG_REC_AUX];

val PATH_SEG_REC_SUC =
 store_thm
  ("PATH_SEG_REC_SUC",
   ``!p. PATH_SEG_REC (SUC m) n p = PATH_EL p n :: PATH_SEG_REC m (SUC n) p``,
   Induct_on `n`
    THEN RW_TAC arith_ss [PATH_SEG_REC_def,PATH_EL_def,RESTN_def]
    THEN Induct_on `m`
    THEN RW_TAC arith_ss [PATH_SEG_REC_def,PATH_EL_def,RESTN_def]);

(******************************************************************************
* PATH_SEG p (m,n) = [p m; ... ; p n]
******************************************************************************)
val PATH_SEG_def = Define `PATH_SEG p (m,n) = PATH_SEG_REC (n-m+1) m p`;

(******************************************************************************
* PATH_CONS(x,p) add x to the fron of p
******************************************************************************)
val PATH_CONS_def = 
 Define 
  `(PATH_CONS(x, FINITE_PATH l) = FINITE_PATH(x :: l))
   /\
   (PATH_CONS(x, INFINITE_PATH f) = 
     INFINITE_PATH(\n. if n=0 then x else f(n-1)))`;

(******************************************************************************
* PATH_CAT(w,p) creates a new path by concatenating w in front of p
******************************************************************************)
val PATH_CAT_def = 
 Define 
  `(PATH_CAT([], p) = p) 
   /\ 
   (PATH_CAT((x::w), p) = PATH_CONS(x, PATH_CAT(w,p)))`;

val ALL_EL_F =
 store_thm
  ("ALL_EL_F",
   ``ALL_EL (\x. F) l = (l = [])``,
   Cases_on `l`
    THEN RW_TAC list_ss []);

val ALL_EL_CONCAT =
 store_thm
  ("ALL_EL_CONCAT",
   ``!P. ALL_EL (\l. (LENGTH l = 1) /\ P(EL(LENGTH l - 1)l)) ll 
          ==> ALL_EL P (CONCAT ll)``,
   Induct_on `ll`
    THEN RW_TAC list_ss [CONCAT_def,APPEND_INFIX_def]
    THEN RW_TAC list_ss [EVERY_EL,DECIDE``n<1 ==> (n=0)``]
    THEN ASSUM_LIST(fn thl => ACCEPT_TAC(SIMP_RULE arith_ss [el 4 thl,EL] (el 3 thl))));

val CONCAT_MAP_SINGLETON =
 store_thm
  ("CONCAT_MAP_SINGLETON",
   ``!ll. CONCAT (MAP (\l. [l]) ll) = ll``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def,MAP,APPEND_INFIX_def]);

val LENGTH_EL_MAP_SINGLETON =
 store_thm
  ("LENGTH_EL_MAP_SINGLETON",
   ``!ll n. n < LENGTH ll ==> (LENGTH (EL n (MAP (\l. [l]) ll)) = 1)``,
   Induct
    THEN RW_TAC list_ss [MAP]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]);

val HD_EL_MAP =
 store_thm
  ("HD_EL_MAP",
   ``!ll n. n < LENGTH ll ==> ((HD (EL n (MAP (\l. [l]) ll))) = EL n ll)``,
   Induct
    THEN RW_TAC list_ss [MAP]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]);

val EQ_SINGLETON =
 store_thm
  ("EQ_SINGLETON",
   ``(l = [x]) = (x = HD l) /\ (l = [HD l])``,
   Induct_on `l`
    THEN ZAP_TAC list_ss []);

val PATH_SEG_REC_SPLIT =
 store_thm
  ("PATH_SEG_REC_SPLIT",
   ``!n. PATH_SEG_REC (m+k) n p = 
          APPEND (PATH_SEG_REC k n p) (PATH_SEG_REC m (n+k) p)``,
    Induct_on `k`
     THEN RW_TAC list_ss [PATH_SEG_def,PATH_SEG_REC_def,arithmeticTheory.ONE]
     THEN RW_TAC std_ss [DECIDE ``m + SUC k = SUC(m+k)``,
                         PATH_SEG_REC_SUC,APPEND,arithmeticTheory.ADD]);

val PATH_SEG_SPLIT =
 store_thm
  ("PATH_SEG_SPLIT",
   ``!p k m n.
      m <= k /\ k < n 
      ==> 
      (PATH_SEG p (m,n) = APPEND (PATH_SEG p (m,k)) (PATH_SEG p (k+1,n)))``,
   RW_TAC list_ss [PATH_SEG_def]
    THEN IMP_RES_TAC
          (DECIDE ``m <= k ==> k < n ==> (n + 1 - m = (n-k) + (k+1-m))``)
    THEN IMP_RES_TAC(DECIDE ``m <= k ==> (k+ 1 = m + (k + 1 - m))``)
    THEN ASSUM_LIST(fn thl => CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[el 2 thl])))
    THEN ASSUM_LIST(fn thl => CONV_TAC(RHS_CONV(RAND_CONV(ONCE_REWRITE_CONV[el 1 thl]))))
    THEN REWRITE_TAC[PATH_SEG_REC_SPLIT]);

val PATH_SEG_EL =
 store_thm
  ("PATH_SEG_EL",
   ``!p m. PATH_SEG p (m,m) = [PATH_EL p m]``,
   Induct_on `m`
    THEN RW_TAC arith_ss [PATH_SEG_def,PATH_SEG_REC_def,PATH_EL_def,
                          arithmeticTheory.ONE,RESTN_def,
                          PATH_SEG_REC_SUC]);

val APPEND_CANCEL =
 store_thm
  ("APPEND_CANCEL",
   ``(APPEND l1 [x1] = APPEND l2 [x2]) = (l1 = l2) /\ (x1 = x2)``,
   ZAP_TAC list_ss [GSYM SNOC_APPEND,SNOC_11]);

val MAP_PATH_SEG_APPEND_SINGLETON_IMP =
 store_thm
  ("MAP_PATH_SEG_APPEND_SINGLETON_IMP",
   ``j > i
     ==>
     (MAP f (PATH_SEG p (i,j)) = APPEND w [l])
     ==>
     ((MAP f (PATH_SEG p (i,j-1)) = w)
      /\
      (f(PATH_EL p j) = l))``,
   REPEAT DISCH_TAC
    THEN IMP_RES_TAC(DECIDE ``j > i ==> (i <= (j-1) /\ (j-1) < j)``)
    THEN IMP_RES_TAC(DECIDE``j > i ==> (j - 1 + 1 = j)``)
    THEN IMP_RES_TAC(ISPEC ``p :'b path`` PATH_SEG_SPLIT)
    THEN ASSUM_LIST
          (fn thl => 
            ASSUME_TAC
             (AP_TERM 
               ``MAP(f:'b -> 'a)`` 
               (SPEC_ALL(SIMP_RULE std_ss [el 2 thl,PATH_SEG_EL](el 1 thl)))))
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(TRANS (GSYM(el 6 thl)) (el 1 thl)))
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [APPEND_CANCEL,MAP_APPEND,MAP])
    THEN RW_TAC std_ss []);

val MAP_PATH_SEG_APPEND_SINGLETON_IMP0 =
 store_thm
  ("MAP_PATH_SEG_APPEND_SINGLETON_IMP0",
   ``i > 0
     ==>
     (MAP f (PATH_SEG p (0,i)) = APPEND w [l])
     ==>
     ((MAP f (PATH_SEG p (0,i-1)) = w)
      /\
      (f(PATH_EL p i) = l))``,
   ZAP_TAC arith_ss [MAP_PATH_SEG_APPEND_SINGLETON_IMP]);

val MAP_PATH_SEG_APPEND_SINGLETON =
 store_thm
  ("MAP_PATH_SEG_APPEND_SINGLETON",
   ``j > i
     ==>
     ((MAP f (PATH_SEG p (i,j)) = APPEND w [l])
      =
      ((MAP f (PATH_SEG p (i,j-1)) = w)
       /\
       (f(PATH_EL p j) = l)))``,
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ZAP_TAC std_ss [MAP_PATH_SEG_APPEND_SINGLETON_IMP]
    THEN IMP_RES_TAC(DECIDE ``j > i ==> i <= j - 1 /\ j - 1 < j``)
    THEN IMP_RES_TAC
          (ISPECL [``p :'b path``,``j-1``,``i:num``,``j:num``] PATH_SEG_SPLIT)
    THEN RW_TAC arith_ss [MAP_APPEND,APPEND_CANCEL,PATH_SEG_EL,MAP]);

val MAP_PATH_SEG_APPEND_SINGLETON0 =
 store_thm
  ("MAP_PATH_SEG_APPEND_SINGLETON0",
   ``i > 0
     ==>
     ((MAP f (PATH_SEG p (0,i)) = APPEND w [l])
      =
      ((MAP f (PATH_SEG p (0,i-1)) = w)
       /\
       (f(PATH_EL p i) = l)))``,
   RW_TAC arith_ss [MAP_PATH_SEG_APPEND_SINGLETON]);

val LENGTH_PATH_SEG_REC =
 store_thm
  ("LENGTH_PATH_SEG_REC",
   ``!m n p. LENGTH(PATH_SEG_REC m n p) = m``,
   Induct_on `m`THEN Induct_on `n`
    THEN RW_TAC list_ss [PATH_SEG_REC_def]);

val LENGTH_PATH_SEG =
 store_thm
  ("LENGTH_PATH_SEG",
   ``!m n p. LENGTH(PATH_SEG p (m,n)) = n-m+1``,
   RW_TAC arith_ss [PATH_SEG_def,PATH_SEG_REC_def,LENGTH_PATH_SEG_REC]);
   
val HD_PATH_SEG =
 store_thm
  ("HD_PATH_SEG",
   ``!i j p. i <= j ==> (HD(PATH_SEG p (i,j)) = PATH_EL p i)``,
   Induct
    THEN RW_TAC list_ss 
          [PATH_SEG_def,PATH_SEG_REC_def,GSYM arithmeticTheory.ADD1,
           PATH_EL_def,RESTN_def]
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> ((SUC (j - SUC i)) = (j-i))``)
    THEN RW_TAC arith_ss []
    THEN ASSUM_LIST
          (fn thl => 
           ASSUME_TAC
            (GSYM
             (Q.GEN `p`
              (SIMP_RULE arith_ss thl (Q.SPECL [`p`,`i`,`j-1`] PATH_SEG_def)))))
    THEN RW_TAC arith_ss [PATH_EL_def]);

val HD_PATH_SEG0 =
 store_thm
  ("HD_PATH_SEG0",
   ``HD(PATH_SEG p (0,i)) = HEAD p``,
   RW_TAC list_ss [PATH_SEG_def,PATH_SEG_REC_def,GSYM arithmeticTheory.ADD1]);

val TL_PATH_SEG_SUC =
 store_thm
  ("TL_PATH_SEG_SUC",
   ``!i j p. i <= j ==> (TL(PATH_SEG p (i,SUC j)) = PATH_SEG (REST p) (i,j))``,
   Induct
    THEN RW_TAC list_ss 
          [PATH_SEG_def,PATH_SEG_REC_def,GSYM arithmeticTheory.ADD1,
           PATH_EL_def,RESTN_def]
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> ((SUC (j - SUC i)) = (j-i))``)
    THEN RW_TAC arith_ss []
    THEN ASSUM_LIST
          (fn thl => 
           ASSUME_TAC
            (GSYM
             (Q.GEN `p`
              (SIMP_RULE arith_ss thl (Q.SPECL [`p`,`i`,`j`] PATH_SEG_def)))))
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> (SUC (j - i) = j + 1 - i)``)
    THEN RW_TAC arith_ss []
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> i <= j-1``)
    THEN RES_TAC
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> (SUC(j-1)=j)``)
    THEN ASSUM_LIST
          (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (el 2 thl)))
    THEN RW_TAC arith_ss [PATH_SEG_def]);

val TL_PATH_SEG =
 store_thm
  ("TL_PATH_SEG",
   ``!i j p. i < j ==> (TL(PATH_SEG p (i,j)) = PATH_SEG (REST p) (i,j-1))``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC(DECIDE ``i < j ==> i <= j-1``)
    THEN IMP_RES_TAC TL_PATH_SEG_SUC
    THEN IMP_RES_TAC(DECIDE ``i < j ==> (SUC(j-1)=j)``)
    THEN ASSUM_LIST
          (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (el 2 thl)))
    THEN RW_TAC arith_ss []);

val TL_PATH_SEG0 =
 store_thm
  ("TL_PATH_SEG0",
   ``TL(PATH_SEG p (0,SUC i)) = PATH_SEG (REST p) (0,i)``,
   RW_TAC list_ss [PATH_SEG_def,PATH_SEG_REC_def,GSYM arithmeticTheory.ADD1]);

val EL_PATH_SEG_LEMMA =
 prove
  (``!m i j p. 
      i <= j /\ m <= j-i ==> (EL m (PATH_SEG p (i,j)) = PATH_EL p (i+m))``,
   Induct
    THEN RW_TAC list_ss 
          [PATH_SEG_REC_def,PATH_EL_def,RESTN_def,
           HD_PATH_SEG,TL_PATH_SEG,RESTN_def,DECIDE``i + SUC m = SUC(i+m)``]);

val EL_PATH_SEG =
 store_thm
  ("EL_PATH_SEG",
   ``!i k j p. 
      i <= k ==> k <= j  ==> (EL (k-i) (PATH_SEG p (i,j)) = PATH_EL p k)``,
   RW_TAC arith_ss [EL_PATH_SEG_LEMMA]);
   
val EL_PATH_SEG0 =
 store_thm
  ("EL_PATH_SEG0",
   ``!j i p. j <= i ==> (EL j (PATH_SEG p (0,i)) = PATH_EL p j)``,
   Induct
    THEN RW_TAC list_ss [PATH_SEG_REC_def,PATH_EL_def,RESTN_def,HD_PATH_SEG0]
    THEN Induct_on `i`
    THEN RW_TAC list_ss [PATH_SEG_REC_def,PATH_EL_def,RESTN_def,TL_PATH_SEG0]);

val LENGTH1 =
 store_thm
  ("LENGTH1",
   ``(LENGTH l = 1) = ?x. l=[x]``,
   EQ_TAC
    THEN RW_TAC list_ss [LENGTH,LENGTH_NIL,LENGTH_CONS,arithmeticTheory.ONE]);

val _ = export_theory();







