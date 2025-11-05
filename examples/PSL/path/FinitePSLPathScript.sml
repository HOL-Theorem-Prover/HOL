
(*****************************************************************************)
(* Create "FinitePSLPathTheory", a theory of finite paths represented as     *)
(* lists. Note that finite paths can be empty in the "SEM_1" semantics.      *)
(*                                                                           *)
(* The theory "PSLPathTheory" defines a type ``:'a path`` of finite and      *)
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
quietdec := false;
*)

Theory FinitePSLPath
Ancestors
  list rich_list arithmetic
Libs
  intLib


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

val _ = ParseExtras.temp_loose_equality()

(******************************************************************************
 * Infix list concatenation
 ******************************************************************************)
val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);

(******************************************************************************
 * Concatenate a list of lists
 ******************************************************************************)
Definition CONCAT_def:
 (CONCAT [] = []) /\ (CONCAT(l::ll) = l <> CONCAT ll)
End

(******************************************************************************
 * HEAD (p0 p1 p2 p3 ...) = p0
 ******************************************************************************)
Definition HEAD_def:   HEAD = list$HD
End

(******************************************************************************
 * REST (p0 p1 p2 p3 ...) = (p1 p2 p3 ...)
 ******************************************************************************)
Definition REST_def:   REST = list$TL
End

(******************************************************************************
 * RESTN (p0 p1 p2 p3 ...) n = (pn p(n+1) p(n+2) ...)
 ******************************************************************************)
Definition RESTN_def:
 (RESTN p 0 = p) /\ (RESTN p (SUC n) = RESTN (REST p) n)
End

(******************************************************************************
 * ELEM (p0 p1 p2 p3 ...) n = pn
 ******************************************************************************)
Definition ELEM_def:   ELEM p n = HEAD(RESTN p n)
End

Theorem LENGTH_REST:
   !p. 0 < LENGTH p ==> (LENGTH(REST p) = LENGTH p - 1)
Proof
                                                       Cases
 THEN RW_TAC list_ss [LENGTH,REST_def,LENGTH_CONS,
                      Cooper.COOPER_PROVE``0 < n = ?m. n = SUC m``]
QED

Theorem LENGTH_TL:
   !l. 0 < LENGTH l ==> (LENGTH(TL l) = LENGTH l - 1)
Proof
                                                     Induct
 THEN RW_TAC list_ss []
QED

(******************************************************************************
 * HD(RESTN p i) = EL i p for finite paths
 ******************************************************************************)
Theorem HD_RESTN:
   !p. HD(RESTN p i) = EL i p
Proof
                          Induct_on `i`
 THEN ASM_SIMP_TAC list_ss [HEAD_def,REST_def,RESTN_def, EL]
QED

(******************************************************************************
 * ELEM p i = EL i p for finite paths
 ******************************************************************************)
Theorem ELEM_EL:
   !p. ELEM p i = EL i p
Proof
                     RW_TAC list_ss [ELEM_def,HEAD_def,REST_def,RESTN_def,HD_RESTN]
QED

Theorem LENGTH_RESTN:
   !n p. n < LENGTH p ==> (LENGTH(RESTN p n) = LENGTH p - n)
Proof
                                                            Induct
 THEN RW_TAC arith_ss [LENGTH,RESTN_def,LENGTH_REST]
QED

Theorem RESTN_TL:
   !l i. 0 < i /\ i < LENGTH l ==> (RESTN (TL l) (i-1) = RESTN l i)
Proof
                                                                   Induct_on `i`
 THEN RW_TAC list_ss [REST_def,RESTN_def]
QED

(******************************************************************************
 * Form needeed for computeLib
 ******************************************************************************)
Theorem RESTN_AUX:
   RESTN p n = if n=0 then p else RESTN (REST p) (n-1)
Proof
                                        Cases_on `n` THEN RW_TAC arith_ss [RESTN_def]
QED

val _ = computeLib.add_funs[RESTN_AUX];

(******************************************************************************
 * SEL_REC m n p = [p(n); p(n+1); ... ; p(n+m)]
 * (Recursive form for easy definition using Define)
 *
 * SEL_REC defined here is a fully specified version of SEG from
 * rich_listTheory.  SEG is only partially specified using
 * new_specification.
 ******************************************************************************)
Definition SEL_REC_def:
 (SEL_REC 0 n p = [])
/\
(SEL_REC (SUC m) 0 p = (HEAD p)::SEL_REC m 0 (REST p))
/\
(SEL_REC (SUC m) (SUC n) p = SEL_REC (SUC m) n (REST p))
End

(******************************************************************************
 * SEL_REC m n p = [p(n); p(n+1); ... ; p(n+m-1)]
 * (Version for computeLib)
 ******************************************************************************)
Theorem SEL_REC_AUX:
   SEL_REC m n p =
 if m = 0   then [] else
   if (n = 0) then (HEAD p)::SEL_REC (m-1) 0 (REST p)
   else SEL_REC m (n-1) (REST p)
Proof
                Cases_on `m` THEN Cases_on `n` THEN RW_TAC arith_ss [SEL_REC_def]
QED

val _ = computeLib.add_funs[SEL_REC_AUX];

Theorem SEL_REC_SUC:
   !p. SEL_REC (SUC m) n p = ELEM p n :: SEL_REC m (SUC n) p
Proof
                                  Induct_on `n`
 THEN RW_TAC arith_ss [SEL_REC_def,ELEM_def,RESTN_def]
 THEN Induct_on `m`
 THEN RW_TAC simp_arith_ss [SEL_REC_def,ELEM_def,RESTN_def]
QED

(******************************************************************************
 * SEL p (m,n) = [p m; ... ; p n]
 ******************************************************************************)
Definition SEL_def:   SEL p (m,n) = SEL_REC (n-m+1) m p
End

(******************************************************************************
 * RESTN (RESTN p m) n = RESTN p (m+n)
 ******************************************************************************)
Theorem RESTN_RESTN:
   !m n p. RESTN (RESTN p m) n = RESTN p (m+n)
Proof
                                       Induct
 THEN RW_TAC arith_ss [RESTN_def,arithmeticTheory.ADD_CLAUSES]
QED

(******************************************************************************
 * ELEM (RESTN p m) n = ELEM p (m+n)
 ******************************************************************************)
Theorem ELEM_RESTN:
   !m n p.  ELEM (RESTN p m) n = ELEM p (n+m)
Proof
                                      Induct
 THEN RW_TAC arith_ss [RESTN_def,ELEM_def,RESTN_RESTN]
QED

(******************************************************************************
 * CAT(w,p) creates a new path by concatenating w in front of p
 ******************************************************************************)
Definition CAT_def:
 (CAT([], p) = p)
/\
(CAT((x::w), p) = x :: CAT(w,p))
End

Theorem ALL_EL_F:
   ALL_EL (\x. F) l = (l = [])
Proof
                              Cases_on `l`
 THEN RW_TAC list_ss []
QED

Theorem ALL_EL_CONCAT:
  !P. ALL_EL (\l. (LENGTH l = 1) /\ P(EL(LENGTH l - 1)l)) ll ==>
      ALL_EL P (CONCAT ll)
Proof
  Induct_on `ll` THEN RW_TAC list_ss [CONCAT_def] THEN
  gvs[LENGTH_EQ_NUM_compute]
QED

Theorem CONCAT_MAP_SINGLETON:
     !ll. CONCAT (MAP (\l. [l]) ll) = ll
Proof
   Induct
    THEN RW_TAC list_ss [CONCAT_def,MAP]
QED

Theorem LENGTH_EL_MAP_SINGLETON:
     !ll n. n < LENGTH ll ==> (LENGTH (EL n (MAP (\l. [l]) ll)) = 1)
Proof
   Induct
    THEN RW_TAC list_ss [MAP]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]
QED

Theorem HD_EL_MAP:
     !ll n. n < LENGTH ll ==> ((HD (EL n (MAP (\l. [l]) ll))) = EL n ll)
Proof
   Induct
    THEN RW_TAC list_ss [MAP]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]
QED

Theorem EQ_SINGLETON:
     (l = [x]) = (x = HD l) /\ (l = [HD l])
Proof
   Induct_on `l`
    THEN ZAP_TAC list_ss []
QED

Theorem SEL_REC_SPLIT:
     !n. SEL_REC (m+k) n p =
          APPEND (SEL_REC k n p) (SEL_REC m (n+k) p)
Proof
    Induct_on `k`
     THEN RW_TAC list_ss [SEL_def,SEL_REC_def,arithmeticTheory.ONE]
     THEN RW_TAC std_ss [DECIDE ``m + SUC k = SUC(m+k)``,
                         SEL_REC_SUC,APPEND,arithmeticTheory.ADD]
QED

Theorem SEL_SPLIT:
     !p k m n.
      m <= k /\ k < n
      ==>
      (SEL p (m,n) = APPEND (SEL p (m,k)) (SEL p (k+1,n)))
Proof
   RW_TAC list_ss [SEL_def]
    THEN IMP_RES_TAC
          (DECIDE ``m <= k ==> k < n ==> (n + 1 - m = (n-k) + (k+1-m))``)
    THEN IMP_RES_TAC(DECIDE ``m <= k ==> (k+ 1 = m + (k + 1 - m))``)
    THEN ASSUM_LIST(fn thl => CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[el 2 thl])))
    THEN ASSUM_LIST(fn thl => CONV_TAC(RHS_CONV(RAND_CONV(ONCE_REWRITE_CONV[el 1 thl]))))
    THEN REWRITE_TAC[SEL_REC_SPLIT]
QED

Theorem SEL_ELEM:
     !p m. SEL p (m,m) = [ELEM p m]
Proof
   Induct_on `m`
    THEN RW_TAC simp_arith_ss [SEL_def,SEL_REC_def,ELEM_def,
                               RESTN_def, SEL_REC_SUC]
QED

Theorem APPEND_LAST_CANCEL:
     (APPEND l1 [x1] = APPEND l2 [x2]) = (l1 = l2) /\ (x1 = x2)
Proof
   ZAP_TAC list_ss [GSYM SNOC_APPEND,SNOC_11]
QED

Theorem APPEND_RIGHT_CANCEL:
     (APPEND l1 l = APPEND l2 l) = (l1 = l2)
Proof
   Induct_on `l`
    THEN ZAP_TAC list_ss [GSYM SNOC_APPEND,SNOC_11]
QED

Theorem APPEND_LEFT_CANCEL:
     (APPEND l l1 = APPEND l l2) = (l1 = l2)
Proof
   Induct_on `l`
    THEN ZAP_TAC list_ss []
QED

Theorem SEL_APPEND_SINGLETON_IMP:
     j > i
     ==>
     (SEL p (i,j) = APPEND w [l]) ==> (SEL p (i,j-1) = w) /\ (ELEM p j = l)
Proof
   REPEAT DISCH_TAC
    THEN IMP_RES_TAC(DECIDE ``j > i ==> (i <= (j-1) /\ (j-1) < j)``)
    THEN IMP_RES_TAC(DECIDE``j:num > i:num ==> (j - 1 + 1 = j)``)
    THEN IMP_RES_TAC(ISPEC ``p :'a list`` SEL_SPLIT)
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(TRANS (GSYM(el 5 thl)) (el 1 thl)))
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE std_ss [SEL_ELEM,el 3 thl] (el 1 thl)))
    THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [APPEND_LAST_CANCEL])
    THEN RW_TAC std_ss []
QED

Theorem SEL_APPEND_SINGLETON:
     j > i
     ==>
     ((SEL p (i,j) = APPEND w [l])
      =
      (SEL p (i,j-1) = w) /\ (ELEM p j = l))
Proof
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ZAP_TAC std_ss [SEL_APPEND_SINGLETON_IMP]
    THEN IMP_RES_TAC(DECIDE ``j > i ==> i <= j - 1 /\ j - 1 < j``)
    THEN IMP_RES_TAC
          (ISPECL [``p :'a list``,``j:num-1``,``i:num``,``j:num``] SEL_SPLIT)
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN IMP_RES_TAC(DECIDE``j:num > i:num ==> (j - 1 + 1 = j)``)
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SIMP_RULE std_ss [SEL_ELEM,el 1 thl] (el 2 thl)))
    THEN ZAP_TAC arith_ss [APPEND_LAST_CANCEL,SEL_ELEM]
QED

Theorem LENGTH_SEL_REC:
     !m n p. LENGTH(SEL_REC m n p) = m
Proof
   Induct_on `m`THEN Induct_on `n`
    THEN RW_TAC list_ss [SEL_REC_def]
QED

Theorem LENGTH_SEL:
     !m n p. LENGTH(SEL p (m,n)) = n-m+1
Proof
   RW_TAC arith_ss [SEL_def,SEL_REC_def,LENGTH_SEL_REC]
QED

Theorem HD_SEL:
     !i j p. i <= j ==> (HD(SEL p (i,j)) = ELEM p i)
Proof
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
    THEN RW_TAC arith_ss [ELEM_def]
QED

Theorem HD_SEL0:
     HD(SEL p (0,i)) = HEAD p
Proof
   RW_TAC list_ss [SEL_def,SEL_REC_def,GSYM arithmeticTheory.ADD1]
QED

Theorem TL_SEL_SUC:
     !i j p. i <= j ==> (TL(SEL p (i,SUC j)) = SEL (REST p) (i,j))
Proof
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
    THEN RW_TAC arith_ss [SEL_def]
QED

Theorem TL_SEL:
     !i j p. i < j ==> (TL(SEL p (i,j)) = SEL (REST p) (i,j-1))
Proof
   RW_TAC std_ss []
    THEN IMP_RES_TAC(DECIDE ``i < j ==> i <= j-1``)
    THEN IMP_RES_TAC TL_SEL_SUC
    THEN IMP_RES_TAC(DECIDE ``i < j ==> (SUC(j-1)=j)``)
    THEN ASSUM_LIST
          (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (el 2 thl)))
    THEN RW_TAC arith_ss []
QED

Theorem TL_SEL0:
     TL(SEL p (0,SUC i)) = SEL (REST p) (0,i)
Proof
   RW_TAC list_ss [SEL_def,SEL_REC_def,GSYM arithmeticTheory.ADD1]
QED

val EL_SEL_LEMMA =
 prove
  (``!m i j p.
      i <= j /\ m <= j-i ==> (EL m (SEL p (i,j)) = ELEM p (i+m))``,
   Induct
    THEN RW_TAC list_ss
          [SEL_REC_def,ELEM_def,RESTN_def, EL,
           HD_SEL,TL_SEL,RESTN_def,DECIDE``i + SUC m = SUC(i+m)``]);

Theorem EL_SEL:
     !i k j p.
      i <= k ==> k <= j  ==> (EL (k-i) (SEL p (i,j)) = ELEM p k)
Proof
   RW_TAC arith_ss [EL_SEL_LEMMA]
QED

Theorem EL_SEL0:
     !j i p. j <= i ==> (EL j (SEL p (0,i)) = ELEM p j)
Proof
   Induct
    THEN RW_TAC list_ss [SEL_REC_def,ELEM_def,RESTN_def,HD_SEL0,EL]
    THEN Induct_on `i`
    THEN RW_TAC list_ss [SEL_REC_def,ELEM_def,RESTN_def,TL_SEL0,EL]
QED

Theorem SEL_REC_REST:
     !p. SEL_REC m n (REST p) = SEL_REC m (SUC n) p
Proof
   Induct_on `m`
    THEN RW_TAC arith_ss [SEL_REC_def]
QED

Theorem SEL_REC_RESTN:
     !p. SEL_REC m n (RESTN p r) = SEL_REC m (n + r) p
Proof
   Induct_on `r`
    THEN RW_TAC arith_ss [SEL_REC_def,RESTN_def,arithmeticTheory.ADD_CLAUSES]
    THEN PROVE_TAC[SEL_REC_REST]
QED

Theorem SEL_RESTN:
     !p. SEL (RESTN p r) (n,m) = SEL p (r + n, r + m)
Proof
   RW_TAC arith_ss [SEL_def,SEL_REC_RESTN]
QED

Theorem LENGTH1:
     (LENGTH l = 1) = ?x. l=[x]
Proof
   REWRITE_TAC [arithmeticTheory.ONE]
    THEN EQ_TAC
    THEN RW_TAC list_ss [LENGTH,LENGTH_NIL,LENGTH_CONS]
QED

(******************************************************************************
* Some ad hoc lemmas for the rather gross proof that S_CLOCK_COMP works
******************************************************************************)
Theorem LENGTH_NIL_LEMMA:
     LENGTH l >= 1 ==> ~(l = [])
Proof
   RW_TAC list_ss [DECIDE``m>=1 = ~(m=0)``,LENGTH_NIL]
QED

Theorem EL_BUTLAST:
     !w n. n < PRE(LENGTH w) ==> (EL n (BUTLAST w) = EL n w)
Proof
   Induct
    THEN RW_TAC list_ss [FRONT_DEF]
    THEN Cases_on `n`
    THEN RW_TAC list_ss [EL]
QED

Theorem EL_PRE_LENGTH:
     !w. LENGTH w >= 1 ==> (EL (LENGTH w - 1) w = LAST w)
Proof
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `LENGTH w`
    THEN RW_TAC list_ss [EL,LAST_DEF]
    THEN IMP_RES_TAC LENGTH_NIL
    THEN IMP_RES_TAC(SIMP_CONV list_ss [] ``LENGTH [] = SUC n``)
    THEN RES_TAC
    THEN FULL_SIMP_TAC arith_ss []
QED

Theorem EVERY_EL_SINGLETON_LENGTH:
     !wlist P.
      (!n. n < LENGTH wlist ==> ?l. EL n wlist = [l])
      ==>
      (LENGTH(CONCAT wlist) = LENGTH wlist)
Proof
   Induct
    THEN RW_TAC list_ss [CONCAT_def]
    THEN ASSUM_LIST
          (fn thl =>
            ASSUME_TAC(Q.GEN `n` (SIMP_RULE list_ss [EL] (Q.SPEC `SUC n` (el 1 thl)))))
    THEN ASSUM_LIST
          (fn thl =>
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [EL] (Q.SPEC `0` (el 2 thl))))
    THEN RES_TAC
    THEN RW_TAC list_ss []
QED

Theorem EVERY_EL_SINGLETON:
     !wlist P.
      (!n. n < LENGTH wlist ==> ?l. EL n wlist = [l])
      ==>
      (CONCAT wlist = MAP HD wlist)
Proof
   Induct
    THEN RW_TAC list_ss [CONCAT_def]
    THEN ASSUM_LIST
          (fn thl =>
            ASSUME_TAC(Q.GEN `n` (SIMP_RULE list_ss [EL] (Q.SPEC `SUC n` (el 1 thl)))))
    THEN ASSUM_LIST
          (fn thl =>
            STRIP_ASSUME_TAC(SIMP_RULE list_ss [EL] (Q.SPEC `0` (el 2 thl))))
    THEN RES_TAC
    THEN RW_TAC list_ss []
QED

Theorem APPEND_SINGLETON_EQ:
     (l <> [x] = [y]) = (l = []) /\ (x = y)
Proof
   EQ_TAC
    THEN RW_TAC list_ss []
    THEN Cases_on `l`
    THEN FULL_SIMP_TAC list_ss []
QED

Theorem APPEND_CONS:
     l1 <> (x :: l2) = (l1 <> [x]) <> l2
Proof
   Induct_on `l1`
    THEN RW_TAC list_ss []
QED

Theorem SEL_RESTN_EQ0:
     0 < LENGTH w ==> (SEL w (0, LENGTH w - 1) = w)
Proof
   RW_TAC list_ss [SEL_def]
    THEN Induct_on `w`
    THEN RW_TAC list_ss [SEL_REC_def,HEAD_def,REST_def]
    THEN Cases_on `w`
    THEN RW_TAC list_ss [SEL_REC_def]
QED

Theorem SEL_RESTN_EQ:
     !w. i < LENGTH w ==> (SEL w (i, LENGTH w - 1) = RESTN w i)
Proof
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
    THEN PROVE_TAC[]
QED

Theorem RESTN_EL:
     !i w. i < LENGTH w ==> (RESTN w i = EL i w :: RESTN w (i + 1))
Proof
   Induct
    THEN RW_TAC simp_list_ss [RESTN_def,REST_def,LENGTH_NIL_LEMMA,EL,DECIDE``0 < n = n >= 1``]
    THENL
     [PROVE_TAC[LENGTH_NIL_LEMMA,CONS,NULL_EQ_NIL],
      FULL_SIMP_TAC std_ss
       [DECIDE``PRE (PRE (SUC i + 1)) = i``, DECIDE ``i+1 = SUC i``,
        GSYM HEAD_def, GSYM REST_def,GSYM ELEM_EL]
       THEN FULL_SIMP_TAC std_ss [RESTN_def]
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `REST w` (el 2 thl)))
       THEN PROVE_TAC[DECIDE``SUC m < n = m < n - 1``, DECIDE``SUC m < n ==> 0 < n``,
                      LENGTH_REST]]
QED

Theorem LAST_SINGLETON:
     !l x. LAST(l <> [x]) = x
Proof
   Induct
    THEN RW_TAC list_ss [LAST_DEF]
QED

Theorem EL_LAST_SEL:
     LAST(SEL w (0,i)) = EL i w
Proof
   Cases_on `0 < i`
    THEN RW_TAC std_ss
          [SIMP_RULE arith_ss [SEL_ELEM,ELEM_EL] (Q.SPECL[`w`,`n-1`,`0`,`n`]SEL_SPLIT)]
    THEN RW_TAC std_ss [LAST_SINGLETON]
    THEN `i=0` by DECIDE_TAC
    THEN RW_TAC list_ss [SEL_ELEM,ELEM_EL]
QED

Theorem RESTN_APPEND:
     !w1 w2. RESTN (w1 <> w2) (LENGTH w1) = w2
Proof
   Induct
    THEN RW_TAC list_ss [RESTN_def,REST_def]
QED

Theorem FINITE_SEL_REC:
     (SEL_REC 0 n l = []) /\
     (SEL_REC (SUC m) 0 (x::l) = x::SEL_REC m 0 l) /\
     (SEL_REC (SUC m) (SUC n) (x::l) = SEL_REC (SUC m) n l)
Proof
   RW_TAC list_ss [SEL_REC_def,HEAD_def,REST_def]
QED

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

Theorem FINITE_SEL_REC_SEL_REC:
      !n1 m1 n2 m2 (l:'a list).
     (((n1 + m1) <= (LENGTH l)) /\ ((n2 + m2) <= n1)) ==>
     (SEL_REC n2 m2 (SEL_REC n1 m1 l) = SEL_REC n2 (m1 + m2) l)
Proof
    REPEAT numLib.INDUCT_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN REWRITE_TAC[LENGTH,FINITE_SEL_REC,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THENL[
        GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO,CONS_11]
        THEN STRIP_TAC THEN SUBST_OCCS_TAC[([3],SYM(SPEC(``0``)ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC[([2],SYM(SPEC(``m2:num``)(CONJUNCT1 ADD)))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC[([2],SYM(SPEC(``m1:num``)ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[LESS_EQ_MONO,ADD_0],

        PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN STRIP_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL[
            PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC_lem]
            THEN FIRST_ASSUM ACCEPT_TAC,
            ASM_REWRITE_TAC[ADD,LESS_EQ_MONO]]]
QED

Theorem FINITE_SEL_REC_SUC_CONS:
      !m n l (x:'a). (SEL_REC m (SUC n) (CONS x l) = SEL_REC m n l)
Proof
    numLib.INDUCT_TAC THEN REWRITE_TAC[FINITE_SEL_REC]
QED

Theorem FINITE_SEL_REC_APPEND:
      !m (l1:'a list) n l2. (m < LENGTH l1) /\ ((LENGTH l1) <= (n + m)) /\
      ((n + m) <= ((LENGTH l1) + (LENGTH l2))) ==>
      (SEL_REC n m (APPEND l1 l2) =
        APPEND (SEL_REC ((LENGTH l1) - m) m l1) (SEL_REC ((n + m)-(LENGTH l1)) 0 l2))
Proof
    numLib.INDUCT_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN REPEAT (FILTER_GEN_TAC (``n:num``))
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
        STRIP_TAC THEN DISJ_CASES_TAC (SPEC (``LENGTH (l1:'a list)``)LESS_0_CASES)
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
        THEN ASM_REWRITE_TAC[GSYM ADD_SUC_lem,LENGTH]]
QED

end;

Theorem SEL_APPEND:
     !m n w1 w2.
      m < LENGTH w1 /\ LENGTH w1 <= n /\
      n + 1 <= LENGTH w1 + LENGTH w2 ==>
      (SEL (w1 <> w2) (m,n) =
       SEL w1 (m, LENGTH w1 - 1) <> SEL w2 (0, n - LENGTH w1))
Proof
   RW_TAC list_ss
    [SEL_def,DISCH_ALL
      (SIMP_RULE arith_ss
        [ASSUME``m<=n``] (Q.SPECL[`m`,`w1`,`n-m+1`,`w2`]FINITE_SEL_REC_APPEND))]
QED

val SEL_APPEND_COR =
 save_thm
  ("SEL_APPEND_COR",
   SIMP_RULE arith_ss [SEL_ELEM,ELEM_EL] (Q.SPECL[`0`,`list$LENGTH w1`,`w1`,`w2`]SEL_APPEND));

Theorem RESTN_LENGTH:
     !w. RESTN w (LENGTH w) = []
Proof
   Induct
    THEN RW_TAC list_ss [RESTN_def,REST_def]
QED
