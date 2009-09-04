
(*****************************************************************************)
(* Create "FinitePathTheory", a theory of finite paths represented as lists. *)
(* Note that finite paths can be empty in the "SEM_1" semantics.             *)
(*                                                                           *)
(* The theory "PathTheory" defines a type ``:'a path`` of finite and         *)
(* infinite paths, and extends the path operators to work on these.          *)
(*                                                                           *)
(* Created Wed Dec 27 2002                                                   *)
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
app load ["bossLib", "rich_listTheory", "intLib", "arithmeticTheory"];
open listTheory rich_listTheory arithmeticTheory intLib;
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
open listTheory rich_listTheory arithmeticTheory intLib;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Versions of simpsets that deal properly with theorems containing SUC
******************************************************************************)
val simp_arith_ss = simpLib.++ (arith_ss, numSimps.SUC_FILTER_ss);
val simp_list_ss  = simpLib.++ (list_ss,  numSimps.SUC_FILTER_ss);

(******************************************************************************
* Simpsets to deal properly with theorems containing SUC
******************************************************************************)
val simp_arith_ss = simpLib.++ (arith_ss, numSimps.SUC_FILTER_ss);

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(******************************************************************************
* Start a new theory called FinitePath
******************************************************************************)
val _ = new_theory "FinitePath";

(******************************************************************************
* Infix list concatenation
******************************************************************************)
val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);

(******************************************************************************
* Concatenate a list of lists
******************************************************************************)
val CONCAT_def =
 Define `(CONCAT [] = []) /\ (CONCAT(l::ll) = l <> CONCAT ll)`;

(******************************************************************************
* HEAD (p0 p1 p2 p3 ...) = p0
******************************************************************************)
val HEAD_def = Define `HEAD = list$HD`;

(******************************************************************************
* REST (p0 p1 p2 p3 ...) = (p1 p2 p3 ...)
******************************************************************************)
val REST_def = Define `REST = list$TL`;

(******************************************************************************
* RESTN (p0 p1 p2 p3 ...) n = (pn p(n+1) p(n+2) ...)
******************************************************************************)
val RESTN_def =
 Define `(RESTN p 0 = p) /\ (RESTN p (SUC n) = RESTN (REST p) n)`;

(******************************************************************************
* ELEM (p0 p1 p2 p3 ...) n = pn
******************************************************************************)
val ELEM_def = Define `ELEM p n = HEAD(RESTN p n)`;

val LENGTH_REST =
 store_thm
  ("LENGTH_REST",
   ``!p. 0 < LENGTH p ==> (LENGTH(REST p) = LENGTH p - 1)``,
    Cases
     THEN RW_TAC list_ss [LENGTH,REST_def,LENGTH_CONS,
                         Cooper.COOPER_PROVE``0 < n = ?m. n = SUC m``]);

val LENGTH_TL =
 store_thm
  ("LENGTH_TL",
   ``!l. 0 < LENGTH l ==> (LENGTH(TL l) = LENGTH l - 1)``,
   Induct
    THEN RW_TAC list_ss []);

(******************************************************************************
* HD(RESTN p i) = EL i p for finite paths
******************************************************************************)
val HD_RESTN =
 store_thm
  ("HD_RESTN",
   ``!p. HD(RESTN p i) = EL i p``,
   Induct_on `i`
    THEN RW_TAC list_ss [HEAD_def,REST_def,RESTN_def]);

(******************************************************************************
* ELEM p i = EL i p for finite paths
******************************************************************************)
val ELEM_EL =
 store_thm
  ("ELEM_EL",
   ``!p. ELEM p i = EL i p``,
   RW_TAC list_ss [ELEM_def,HEAD_def,REST_def,RESTN_def,HD_RESTN]);

val LENGTH_RESTN =
 store_thm
  ("LENGTH_RESTN",
   ``!n p. n < LENGTH p ==> (LENGTH(RESTN p n) = LENGTH p - n)``,
   Induct
    THEN RW_TAC arith_ss [LENGTH,RESTN_def,LENGTH_REST]);

val RESTN_TL =
 store_thm
  ("RESTN_TL",
   ``!l i. 0 < i /\ i < LENGTH l ==> (RESTN (TL l) (i-1) = RESTN l i)``,
   Induct_on `i`
    THEN RW_TAC list_ss [REST_def,RESTN_def]);

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
* SEL_REC m n p = [p(n); p(n+1); ... ; p(n+m)]
* (Recursive form for easy definition using Define)
*
* SEL_REC defined here is a fully specified version of SEG from
* rich_listTheory.  SEG is only partially specified using
* new_specification.
******************************************************************************)
val SEL_REC_def =
 Define
  `(SEL_REC 0 n p = [])
   /\
   (SEL_REC (SUC m) 0 p = (HEAD p)::SEL_REC m 0 (REST p))
   /\
   (SEL_REC (SUC m) (SUC n) p = SEL_REC (SUC m) n (REST p))`;

(******************************************************************************
* SEL_REC m n p = [p(n); p(n+1); ... ; p(n+m-1)]
* (Version for computeLib)
******************************************************************************)
val SEL_REC_AUX =
 store_thm
  ("SEL_REC_AUX",
   ``SEL_REC m n p =
      if m = 0   then [] else
      if (n = 0) then (HEAD p)::SEL_REC (m-1) 0 (REST p)
                 else SEL_REC m (n-1) (REST p)``,
    Cases_on `m` THEN Cases_on `n` THEN RW_TAC arith_ss [SEL_REC_def]);

val _ = computeLib.add_funs[SEL_REC_AUX];

val SEL_REC_SUC =
 store_thm
  ("SEL_REC_SUC",
   ``!p. SEL_REC (SUC m) n p = ELEM p n :: SEL_REC m (SUC n) p``,
   Induct_on `n`
    THEN RW_TAC arith_ss [SEL_REC_def,ELEM_def,RESTN_def]
    THEN Induct_on `m`
    THEN RW_TAC simp_arith_ss [SEL_REC_def,ELEM_def,RESTN_def]);

(******************************************************************************
* SEL p (m,n) = [p m; ... ; p n]
******************************************************************************)
val SEL_def = Define `SEL p (m,n) = SEL_REC (n-m+1) m p`;

(******************************************************************************
* RESTN (RESTN p m) n = RESTN p (m+n)
******************************************************************************)
val RESTN_RESTN =
 store_thm
  ("RESTN_RESTN",
   ``!m n p. RESTN (RESTN p m) n = RESTN p (m+n)``,
   Induct
    THEN RW_TAC arith_ss [RESTN_def,arithmeticTheory.ADD_CLAUSES]);

(******************************************************************************
* ELEM (RESTN p m) n = ELEM p (m+n)
******************************************************************************)
val ELEM_RESTN =
 store_thm
  ("ELEM_RESTN",
   ``!m n p.  ELEM (RESTN p m) n = ELEM p (n+m)``,
   Induct
    THEN RW_TAC arith_ss [RESTN_def,ELEM_def,RESTN_RESTN]);

(******************************************************************************
* CAT(w,p) creates a new path by concatenating w in front of p
******************************************************************************)
val CAT_def =
 Define
  `(CAT([], p) = p)
   /\
   (CAT((x::w), p) = x :: CAT(w,p))`;

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
    THEN RW_TAC list_ss [CONCAT_def]
    THEN RW_TAC list_ss [EVERY_EL,DECIDE``n<1 ==> (n=0)``]
    THEN ASSUM_LIST(fn thl => ACCEPT_TAC(SIMP_RULE arith_ss [el 4 thl,EL] (el 3 thl))));

val CONCAT_MAP_SINGLETON =
 store_thm
  ("CONCAT_MAP_SINGLETON",
   ``!ll. CONCAT (MAP (\l. [l]) ll) = ll``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def,MAP]);

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

val SEL_REC_SPLIT =
 store_thm
  ("SEL_REC_SPLIT",
   ``!n. SEL_REC (m+k) n p =
          APPEND (SEL_REC k n p) (SEL_REC m (n+k) p)``,
    Induct_on `k`
     THEN RW_TAC list_ss [SEL_def,SEL_REC_def,arithmeticTheory.ONE]
     THEN RW_TAC std_ss [DECIDE ``m + SUC k = SUC(m+k)``,
                         SEL_REC_SUC,APPEND,arithmeticTheory.ADD]);

val SEL_SPLIT =
 store_thm
  ("SEL_SPLIT",
   ``!p k m n.
      m <= k /\ k < n
      ==>
      (SEL p (m,n) = APPEND (SEL p (m,k)) (SEL p (k+1,n)))``,
   RW_TAC list_ss [SEL_def]
    THEN IMP_RES_TAC
          (DECIDE ``m <= k ==> k < n ==> (n + 1 - m = (n-k) + (k+1-m))``)
    THEN IMP_RES_TAC(DECIDE ``m <= k ==> (k+ 1 = m + (k + 1 - m))``)
    THEN ASSUM_LIST(fn thl => CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[el 2 thl])))
    THEN ASSUM_LIST(fn thl => CONV_TAC(RHS_CONV(RAND_CONV(ONCE_REWRITE_CONV[el 1 thl]))))
    THEN REWRITE_TAC[SEL_REC_SPLIT]);

val SEL_ELEM =
 store_thm
  ("SEL_ELEM",
   ``!p m. SEL p (m,m) = [ELEM p m]``,
   Induct_on `m`
    THEN RW_TAC simp_arith_ss [SEL_def,SEL_REC_def,ELEM_def,
                               RESTN_def, SEL_REC_SUC]);

val APPEND_LAST_CANCEL =
 store_thm
  ("APPEND_LAST_CANCEL",
   ``(APPEND l1 [x1] = APPEND l2 [x2]) = (l1 = l2) /\ (x1 = x2)``,
   ZAP_TAC list_ss [GSYM SNOC_APPEND,SNOC_11]);

val APPEND_RIGHT_CANCEL =
 store_thm
  ("APPEND_RIGHT_CANCEL",
   ``(APPEND l1 l = APPEND l2 l) = (l1 = l2)``,
   Induct_on `l`
    THEN ZAP_TAC list_ss [GSYM SNOC_APPEND,SNOC_11]);

val APPEND_LEFT_CANCEL =
 store_thm
  ("APPEND_LEFT_CANCEL",
   ``(APPEND l l1 = APPEND l l2) = (l1 = l2)``,
   Induct_on `l`
    THEN ZAP_TAC list_ss []);

val SEL_APPEND_SINGLETON_IMP =
 store_thm
  ("SEL_APPEND_SINGLETON_IMP",
   ``j > i
     ==>
     (SEL p (i,j) = APPEND w [l]) ==> (SEL p (i,j-1) = w) /\ (ELEM p j = l)``,
   REPEAT DISCH_TAC
    THEN IMP_RES_TAC(DECIDE ``j > i ==> (i <= (j-1) /\ (j-1) < j)``)
    THEN IMP_RES_TAC(DECIDE``j:num > i:num ==> (j - 1 + 1 = j)``)
    THEN IMP_RES_TAC(ISPEC ``p :'a list`` SEL_SPLIT)
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(TRANS (GSYM(el 5 thl)) (el 1 thl)))
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE std_ss [SEL_ELEM,el 3 thl] (el 1 thl)))
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [APPEND_LAST_CANCEL])
    THEN RW_TAC std_ss []);

val SEL_APPEND_SINGLETON =
 store_thm
  ("SEL_APPEND_SINGLETON",
   ``j > i
     ==>
     ((SEL p (i,j) = APPEND w [l])
      =
      (SEL p (i,j-1) = w) /\ (ELEM p j = l))``,
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ZAP_TAC std_ss [SEL_APPEND_SINGLETON_IMP]
    THEN IMP_RES_TAC(DECIDE ``j > i ==> i <= j - 1 /\ j - 1 < j``)
    THEN IMP_RES_TAC
          (ISPECL [``p :'a list``,``j:num-1``,``i:num``,``j:num``] SEL_SPLIT)
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN IMP_RES_TAC(DECIDE``j:num > i:num ==> (j - 1 + 1 = j)``)
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE std_ss [SEL_ELEM,el 1 thl] (el 2 thl)))
    THEN ZAP_TAC arith_ss [APPEND_LAST_CANCEL,SEL_ELEM]);

val LENGTH_SEL_REC =
 store_thm
  ("LENGTH_SEL_REC",
   ``!m n p. LENGTH(SEL_REC m n p) = m``,
   Induct_on `m`THEN Induct_on `n`
    THEN RW_TAC list_ss [SEL_REC_def]);

val LENGTH_SEL =
 store_thm
  ("LENGTH_SEL",
   ``!m n p. LENGTH(SEL p (m,n)) = n-m+1``,
   RW_TAC arith_ss [SEL_def,SEL_REC_def,LENGTH_SEL_REC]);

val HD_SEL =
 store_thm
  ("HD_SEL",
   ``!i j p. i <= j ==> (HD(SEL p (i,j)) = ELEM p i)``,
   Induct
    THEN RW_TAC list_ss
          [SEL_def,SEL_REC_def,GSYM arithmeticTheory.ADD1,
           ELEM_def,RESTN_def]
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> ((SUC (j - SUC i)) = (j-i))``)
    THEN RW_TAC arith_ss []
    THEN ASSUM_LIST
          (fn thl =>
           ASSUME_TAC
            (GSYM
             (Q.GEN `p`
              (SIMP_RULE arith_ss thl (Q.SPECL [`p`,`i`,`j-1`] SEL_def)))))
    THEN RW_TAC arith_ss [ELEM_def]);

val HD_SEL0 =
 store_thm
  ("HD_SEL0",
   ``HD(SEL p (0,i)) = HEAD p``,
   RW_TAC list_ss [SEL_def,SEL_REC_def,GSYM arithmeticTheory.ADD1]);

val TL_SEL_SUC =
 store_thm
  ("TL_SEL_SUC",
   ``!i j p. i <= j ==> (TL(SEL p (i,SUC j)) = SEL (REST p) (i,j))``,
   Induct
    THEN RW_TAC list_ss
          [SEL_def,SEL_REC_def,GSYM arithmeticTheory.ADD1,
           ELEM_def,RESTN_def]
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> ((SUC (j - SUC i)) = (j-i))``)
    THEN RW_TAC arith_ss []
    THEN ASSUM_LIST
          (fn thl =>
           ASSUME_TAC
            (GSYM
             (Q.GEN `p`
              (SIMP_RULE arith_ss thl (Q.SPECL [`p`,`i`,`j`] SEL_def)))))
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> (SUC (j - i) = j + 1 - i)``)
    THEN RW_TAC arith_ss []
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> i <= j-1``)
    THEN RES_TAC
    THEN IMP_RES_TAC(DECIDE ``SUC i <= j ==> (SUC(j-1)=j)``)
    THEN ASSUM_LIST
          (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (el 2 thl)))
    THEN RW_TAC arith_ss [SEL_def]);

val TL_SEL =
 store_thm
  ("TL_SEL",
   ``!i j p. i < j ==> (TL(SEL p (i,j)) = SEL (REST p) (i,j-1))``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC(DECIDE ``i < j ==> i <= j-1``)
    THEN IMP_RES_TAC TL_SEL_SUC
    THEN IMP_RES_TAC(DECIDE ``i < j ==> (SUC(j-1)=j)``)
    THEN ASSUM_LIST
          (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (el 2 thl)))
    THEN RW_TAC arith_ss []);

val TL_SEL0 =
 store_thm
  ("TL_SEL0",
   ``TL(SEL p (0,SUC i)) = SEL (REST p) (0,i)``,
   RW_TAC list_ss [SEL_def,SEL_REC_def,GSYM arithmeticTheory.ADD1]);

val EL_SEL_LEMMA =
 prove
  (``!m i j p.
      i <= j /\ m <= j-i ==> (EL m (SEL p (i,j)) = ELEM p (i+m))``,
   Induct
    THEN RW_TAC list_ss
          [SEL_REC_def,ELEM_def,RESTN_def,
           HD_SEL,TL_SEL,RESTN_def,DECIDE``i + SUC m = SUC(i+m)``]);

val EL_SEL =
 store_thm
  ("EL_SEL",
   ``!i k j p.
      i <= k ==> k <= j  ==> (EL (k-i) (SEL p (i,j)) = ELEM p k)``,
   RW_TAC arith_ss [EL_SEL_LEMMA]);

val EL_SEL0 =
 store_thm
  ("EL_SEL0",
   ``!j i p. j <= i ==> (EL j (SEL p (0,i)) = ELEM p j)``,
   Induct
    THEN RW_TAC list_ss [SEL_REC_def,ELEM_def,RESTN_def,HD_SEL0]
    THEN Induct_on `i`
    THEN RW_TAC list_ss [SEL_REC_def,ELEM_def,RESTN_def,TL_SEL0]);

val SEL_REC_REST =
 store_thm
  ("SEL_REC_REST",
   ``!p. SEL_REC m n (REST p) = SEL_REC m (SUC n) p``,
   Induct_on `m`
    THEN RW_TAC arith_ss [SEL_REC_def]);

val SEL_REC_RESTN =
 store_thm
  ("SEL_REC_RESTN",
   ``!p. SEL_REC m n (RESTN p r) = SEL_REC m (n + r) p``,
   Induct_on `r`
    THEN RW_TAC arith_ss [SEL_REC_def,RESTN_def,arithmeticTheory.ADD_CLAUSES]
    THEN PROVE_TAC[SEL_REC_REST]);

val SEL_RESTN =
 store_thm
  ("SEL_RESTN",
   ``!p. SEL (RESTN p r) (n,m) = SEL p (r + n, r + m)``,
   RW_TAC arith_ss [SEL_def,SEL_REC_RESTN]);

val LENGTH1 =
 store_thm
  ("LENGTH1",
   ``(LENGTH l = 1) = ?x. l=[x]``,
   REWRITE_TAC [arithmeticTheory.ONE]
    THEN EQ_TAC
    THEN RW_TAC list_ss [LENGTH,LENGTH_NIL,LENGTH_CONS]);

(******************************************************************************
* Some ad hoc lemmas for the rather gross proof that S_CLOCK_COMP works
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
      (!n. n < LENGTH wlist ==> ?l. EL n wlist = [l])
      ==>
      (LENGTH(CONCAT wlist) = LENGTH wlist)``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def]
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
      (!n. n < LENGTH wlist ==> ?l. EL n wlist = [l])
      ==>
      (CONCAT wlist = MAP HD wlist)``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def]
    THEN ASSUM_LIST
          (fn thl =>
            ASSUME_TAC(Q.GEN `n` (SIMP_RULE list_ss [EL] (Q.SPEC `SUC n` (el 1 thl)))))
    THEN ASSUM_LIST
          (fn thl =>
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [EL] (Q.SPEC `0` (el 2 thl))))
    THEN RES_TAC
    THEN RW_TAC list_ss []);

val APPEND_SINGLETON_EQ =
 store_thm
  ("APPEND_SINGLETON_EQ",
   ``(l <> [x] = [y]) = (l = []) /\ (x = y)``,
   EQ_TAC
    THEN RW_TAC list_ss []
    THEN Cases_on `l`
    THEN FULL_SIMP_TAC list_ss []);

val APPEND_CONS =
 store_thm
  ("APPEND_CONS",
   ``l1 <> (x :: l2) = (l1 <> [x]) <> l2``,
   Induct_on `l1`
    THEN RW_TAC list_ss []);

val SEL_RESTN_EQ0 =
 store_thm
  ("SEL_RESTN_EQ0",
   ``0 < LENGTH w ==> (SEL w (0, LENGTH w - 1) = w)``,
   RW_TAC list_ss [SEL_def]
    THEN Induct_on `w`
    THEN RW_TAC list_ss [SEL_REC_def,HEAD_def,REST_def]
    THEN Cases_on `w`
    THEN RW_TAC list_ss [SEL_REC_def]);

val SEL_RESTN_EQ =
 store_thm
  ("SEL_RESTN_EQ",
   ``!w. i < LENGTH w ==> (SEL w (i, LENGTH w - 1) = RESTN w i)``,
   Induct_on `i`
    THEN SIMP_TAC std_ss [SEL_RESTN_EQ0,RESTN_def]
    THEN FULL_SIMP_TAC std_ss [SEL_def]
    THEN Induct
    THEN RW_TAC list_ss [SEL_REC_def,HEAD_def,REST_def]
    THEN Cases_on `w`
    THEN RW_TAC list_ss [SEL_REC_def]
    THEN FULL_SIMP_TAC list_ss [DECIDE``(i < 1) = (i = 0)``]
    THEN RW_TAC simp_list_ss [SEL_REC_def,RESTN_def,HEAD_def]
    THEN FULL_SIMP_TAC list_ss [DECIDE ``n + 1 - SUC i = n - i``,REST_def]
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE list_ss [] (Q.SPEC `h'::t` (el 3 thl))))
    THEN PROVE_TAC[]);

val RESTN_EL =
 store_thm
  ("RESTN_EL",
   ``!i w. i < LENGTH w ==> (RESTN w i = EL i w :: RESTN w (i + 1))``,
   Induct
    THEN RW_TAC simp_list_ss [RESTN_def,REST_def,LENGTH_NIL_LEMMA,DECIDE``0 < n = n >= 1``]
    THENL
     [PROVE_TAC[LENGTH_NIL_LEMMA,CONS,NULL_EQ_NIL],
      FULL_SIMP_TAC std_ss
       [DECIDE``PRE (PRE (SUC i + 1)) = i``, DECIDE ``i+1 = SUC i``,
        GSYM HEAD_def, GSYM REST_def,GSYM ELEM_EL]
       THEN FULL_SIMP_TAC std_ss [RESTN_def]
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `REST w` (el 2 thl)))
       THEN PROVE_TAC[DECIDE``SUC m < n = m < n - 1``, DECIDE``SUC m < n ==> 0 < n``,
                      LENGTH_REST]]);

val LAST_SINGLETON =
 store_thm
  ("LAST_SINGLETON",
   ``!l x. LAST(l <> [x]) = x``,
   Induct
    THEN RW_TAC list_ss [LAST_DEF]);

val EL_LAST_SEL =
 store_thm
  ("EL_LAST_SEL",
   ``LAST(SEL w (0,i)) = EL i w``,
   Cases_on `0 < i`
    THEN RW_TAC std_ss
          [SIMP_RULE arith_ss [SEL_ELEM,ELEM_EL] (Q.SPECL[`w`,`n-1`,`0`,`n`]SEL_SPLIT)]
    THEN RW_TAC std_ss [LAST_SINGLETON]
    THEN `i=0` by DECIDE_TAC
    THEN RW_TAC list_ss [SEL_ELEM,ELEM_EL]);

val RESTN_APPEND =
 store_thm
  ("RESTN_APPEND",
   ``!w1 w2. RESTN (w1 <> w2) (LENGTH w1) = w2``,
   Induct
    THEN RW_TAC list_ss [RESTN_def,REST_def]);

val FINITE_SEL_REC =
 store_thm
  ("FINITE_SEL_REC",
   ``(SEL_REC 0 n l = []) /\
     (SEL_REC (SUC m) 0 (x::l) = x::SEL_REC m 0 l) /\
     (SEL_REC (SUC m) (SUC n) (x::l) = SEL_REC (SUC m) n l)``,
   RW_TAC list_ss [SEL_REC_def,HEAD_def,REST_def]);

(******************************************************************************
* SEL_REC on lists is a totally specified extension of SEG.
* Proofs below extracts theorems about SEG for SEL_REC
* from rich_listScript.sml sources
******************************************************************************)
local open prim_recTheory

val ADD_SUC_lem =
   let val l = CONJUNCTS ADD_CLAUSES
   in
        GEN_ALL (TRANS (el 4 l) (SYM (el 3 l)))
   end ;

in

val FINITE_SEL_REC_SEL_REC = store_thm("FINITE_SEL_REC_SEL_REC",
    (--`!n1 m1 n2 m2 (l:'a list).
     (((n1 + m1) <= (LENGTH l)) /\ ((n2 + m2) <= n1)) ==>
     (SEL_REC n2 m2 (SEL_REC n1 m1 l) = SEL_REC n2 (m1 + m2) l)`--),
    REPEAT numLib.INDUCT_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN REWRITE_TAC[LENGTH,FINITE_SEL_REC,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THENL[
        GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO,CONS_11]
        THEN STRIP_TAC THEN SUBST_OCCS_TAC[([3],SYM(SPEC(--`0`--)ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC[([2],SYM(SPEC(--`m2:num`--)(CONJUNCT1 ADD)))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC[([2],SYM(SPEC(--`m1:num`--)ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[LESS_EQ_MONO,ADD_0],

        PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN STRIP_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL[
            PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC_lem]
            THEN FIRST_ASSUM ACCEPT_TAC,
            ASM_REWRITE_TAC[ADD,LESS_EQ_MONO]]]);

val FINITE_SEL_REC_SUC_CONS = store_thm("FINITE_SEL_REC_SUC_CONS",
    (--`!m n l (x:'a). (SEL_REC m (SUC n) (CONS x l) = SEL_REC m n l)`--),
    numLib.INDUCT_TAC THEN REWRITE_TAC[FINITE_SEL_REC]);

val FINITE_SEL_REC_APPEND = store_thm("FINITE_SEL_REC_APPEND",
    (--`!m (l1:'a list) n l2. (m < LENGTH l1) /\ ((LENGTH l1) <= (n + m)) /\
      ((n + m) <= ((LENGTH l1) + (LENGTH l2))) ==>
      (SEL_REC n m (APPEND l1 l2) =
        APPEND (SEL_REC ((LENGTH l1) - m) m l1) (SEL_REC ((n + m)-(LENGTH l1)) 0 l2))`--),
    numLib.INDUCT_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN REPEAT (FILTER_GEN_TAC (--`n:num`--))
    THEN numLib.INDUCT_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH,FINITE_SEL_REC,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0,SUB_0]
    THEN REWRITE_TAC
        [LESS_EQ_MONO,SUB_0,SUB_MONO_EQ,APPEND,FINITE_SEL_REC,NOT_SUC_LESS_EQ_0,CONS_11]
    THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_0,SUB_0])
    THENL[
        DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
        THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
        THEN REWRITE_TAC[FINITE_SEL_REC,APPEND_NIL,SUB_EQUAL_0],
        STRIP_TAC THEN DISJ_CASES_TAC (SPEC (--`LENGTH (l1:'a list)`--)LESS_0_CASES)
        THENL[
            POP_ASSUM (ASSUME_TAC o SYM) THEN IMP_RES_TAC LENGTH_NIL
            THEN ASM_REWRITE_TAC[APPEND,FINITE_SEL_REC,SUB_0],
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]],
        DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
        THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
        THEN REWRITE_TAC[FINITE_SEL_REC,APPEND_NIL,SUB_EQUAL_0],
        REWRITE_TAC[LESS_MONO_EQ,GSYM NOT_LESS] THEN STRIP_TAC THEN RES_TAC,
        DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
        THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
        THEN REWRITE_TAC[FINITE_SEL_REC,APPEND_NIL,SUB_EQUAL_0]
        THEN REWRITE_TAC[ADD_SUC_lem,ADD_SUB,FINITE_SEL_REC],
        REWRITE_TAC[LESS_MONO_EQ,FINITE_SEL_REC_SUC_CONS] THEN STRIP_TAC
        THEN PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[GSYM ADD_SUC_lem,LENGTH]]);

end;

val SEL_APPEND =
 store_thm
  ("SEL_APPEND",
   ``!m n w1 w2.
      m < LENGTH w1 /\ LENGTH w1 <= n /\
      n + 1 <= LENGTH w1 + LENGTH w2 ==>
      (SEL (w1 <> w2) (m,n) =
       SEL w1 (m, LENGTH w1 - 1) <> SEL w2 (0, n - LENGTH w1))``,
   RW_TAC list_ss
    [SEL_def,DISCH_ALL
      (SIMP_RULE arith_ss
        [ASSUME``m<=n``] (Q.SPECL[`m`,`w1`,`n-m+1`,`w2`]FINITE_SEL_REC_APPEND))]);

val SEL_APPEND_COR =
 save_thm
  ("SEL_APPEND_COR",
   SIMP_RULE arith_ss [SEL_ELEM,ELEM_EL] (Q.SPECL[`0`,`list$LENGTH w1`,`w1`,`w2`]SEL_APPEND));

val RESTN_LENGTH =
 store_thm
  ("RESTN_LENGTH",
   ``!w. RESTN w (LENGTH w) = []``,
   Induct
    THEN RW_TAC list_ss [RESTN_def,REST_def]);

val _ = export_theory();
