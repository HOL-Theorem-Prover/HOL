(*****************************************************************************)
(* Create "PSLPathTheory", the theory of (finite and infinite) sequences.    *)
(* Note that finite paths can be empty.                                      *)
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
map load ["intLib","FinitePSLPathTheory"];
open intLib rich_listTheory FinitePSLPathTheory;
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
open intLib rich_listTheory FinitePSLPathTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Simpsets to deal properly with theorems containing SUC
******************************************************************************)
val simp_arith_ss = simpLib.++ (arith_ss, numSimps.SUC_FILTER_ss);

(******************************************************************************
* Start a new theory called PSLPath
******************************************************************************)
val _ = new_theory "PSLPath";
val _ = ParseExtras.temp_loose_equality()

(******************************************************************************
* A path is finite or infinite
******************************************************************************)
val path_def =
 Hol_datatype
  `path = FINITE   of ('s list)
        | INFINITE of (num -> 's)`;

(******************************************************************************
* Tests
******************************************************************************)
val IS_FINITE_def =
 Define `(IS_FINITE(FINITE p)   = T)
         /\
         (IS_FINITE(INFINITE f) = F)`;

val IS_INFINITE_def =
 Define `(IS_INFINITE(FINITE p)   = F)
         /\
         (IS_INFINITE(INFINITE f) = T)`;

(******************************************************************************
* HEAD (p0 p1 p2 p3 ...) = p0
******************************************************************************)
val HEAD_def =
 Define `(HEAD (FINITE p) = HD p)
         /\
         (HEAD (INFINITE f)  = f 0)`;

(******************************************************************************
* REST (p0 p1 p2 p3 ...) = (p1 p2 p3 ...)
******************************************************************************)
val REST_def =
 Define `(REST (FINITE p) = FINITE(TL p))
         /\
         (REST (INFINITE f) = INFINITE(\n. f(n+1)))`;

(******************************************************************************
* RESTN (p0 p1 p2 p3 ...) n = (pn p(n+1) p(n+2) ...)
******************************************************************************)
val RESTN_def =
 Define `(RESTN p 0 = p) /\ (RESTN p (SUC n) = RESTN (REST p) n)`;

(******************************************************************************
* Simple properties
******************************************************************************)
val NOT_IS_INFINITE =
 store_thm
  ("NOT_IS_INFINITE",
   ``IS_INFINITE p = ~(IS_FINITE p)``,
   Cases_on `p`
    THEN RW_TAC std_ss [IS_INFINITE_def,IS_FINITE_def]);

val NOT_IS_FINITE =
 store_thm
  ("NOT_IS_FINITE",
   ``IS_FINITE p = ~(IS_INFINITE p)``,
   Cases_on `p`
    THEN RW_TAC std_ss [IS_INFINITE_def,IS_FINITE_def]);

val IS_INFINITE_REST =
 store_thm
  ("IS_INFINITE_REST",
   ``!p. IS_INFINITE(REST p) = IS_INFINITE p``,
   Induct
    THEN RW_TAC list_ss [REST_def,IS_INFINITE_def,IS_FINITE_def]);

val IS_INFINITE_RESTN =
 store_thm
  ("IS_INFINITE_RESTN",
   ``!n p. IS_INFINITE(RESTN p n) = IS_INFINITE p``,
   Induct
    THEN RW_TAC list_ss [RESTN_def,IS_INFINITE_REST]);

val IS_FINITE_REST =
 store_thm
  ("IS_FINITE_REST",
   ``!p. IS_FINITE(REST p) = IS_FINITE p``,
   Induct
    THEN RW_TAC list_ss [REST_def,IS_INFINITE_def,IS_FINITE_def]);

val IS_FINITE_RESTN =
 store_thm
  ("IS_FINITE_RESTN",
   ``!n p. IS_FINITE(RESTN p n) = IS_FINITE p``,
   Induct
    THEN RW_TAC list_ss [RESTN_def,IS_FINITE_REST]);

val RESTN_FINITE =
 store_thm
  ("RESTN_FINITE",
   ``!l n. RESTN (FINITE l) n = FINITE(RESTN l n)``,
   Induct_on `n`
    THEN RW_TAC std_ss
          [RESTN_def,FinitePSLPathTheory.RESTN_def,
           REST_def,FinitePSLPathTheory.REST_def]);

val FINITE_TL =
 store_thm
  ("FINITE_TL",
   ``!l. 0 < LENGTH l ==> (FINITE(TL l) = REST(FINITE l))``,
   Induct
    THEN RW_TAC list_ss [REST_def]);

(******************************************************************************
* Extended numbers.
******************************************************************************)
val xnum_def =
 Hol_datatype
  `xnum = INFINITY                            (* length of an infinite path  *)
        | XNUM of num`;                       (* length of a finite path     *)

(******************************************************************************
* The constant ``to`` is a left associative infix with precedence 500.
* It is overloaded so that
* (m to n) i        means m <= i /\ i < n  (num_to_def)
* (m to XNUM n) i   means m <= i /\ i < n  (xnum_to_def)
* (m to INFINITY) i means m <= i           (xnum_to_def)
******************************************************************************)
val num_to_def =
 Define `$num_to m n i = m <= i /\ i < n`;

val xnum_to_def =
 Define
  `($xnum_to m (XNUM n) i = m <= i /\ i < n)
   /\
   ($xnum_to m INFINITY i = m <= i)`;

val _ = overload_on("to", ``num_to``);
val _ = overload_on("to", ``xnum_to``);

val _ = set_fixity "to" (Infixl 500);

(******************************************************************************
* Extend subtraction (-) to extended numbers
******************************************************************************)
val SUB_num_xnum_def =
 Define
  `($SUB_num_xnum (m:num) (XNUM (n:num)) = XNUM((m:num) - (n:num)))
   /\
   ($SUB_num_xnum (m:num) INFINITY = INFINITY)`;

val SUB_xnum_num_def =
 Define
  `($SUB_xnum_num (XNUM (m:num)) (n:num) = XNUM((m:num) - (n:num)))
   /\
   ($SUB_xnum_num INFINITY (n:num) = INFINITY)`;

val SUB_xnum_xnum_def =
 Define
  `($SUB_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = XNUM((m:num) - (n:num)))
   /\
   ($SUB_xnum_xnum (XNUM (m:num)) INFINITY = XNUM 0)
   /\
   ($SUB_xnum_xnum INFINITY (XNUM (n:num)) = INFINITY)`;

val SUB =
 save_thm
  ("SUB", LIST_CONJ[SUB_num_xnum_def,SUB_xnum_num_def,SUB_xnum_xnum_def]);

val _ = overload_on("-", ``SUB_num_xnum``);
val _ = overload_on("-", ``SUB_xnum_num``);
val _ = overload_on("-", ``SUB_xnum_xnum``);

(******************************************************************************
* Extend less-than predicate (<) to extended numbers
******************************************************************************)
val LS_num_xnum_def =
 Define
  `($LS_num_xnum (m:num) (XNUM (n:num)) = (m:num) < (n:num))
   /\
   ($LS_num_xnum (m:num) INFINITY = T)`;

val LS_xnum_num_def =
 Define
  `($LS_xnum_num (XNUM (m:num)) (n:num) = (m:num) < (n:num))
   /\
   ($LS_xnum_num INFINITY (n:num) = F)`;

val LS_xnum_xnum_def =
 Define
  `($LS_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) < (n:num))
   /\
   ($LS_xnum_xnum (XNUM (m:num)) INFINITY = T)
   /\
   ($LS_xnum_xnum INFINITY (XNUM (n:num)) = F)`;

val LS =
 save_thm
  ("LS", LIST_CONJ[LS_num_xnum_def,LS_xnum_num_def,LS_xnum_xnum_def]);

val _ = overload_on("<", ``LS_num_xnum``);
val _ = overload_on("<", ``LS_xnum_num``);
val _ = overload_on("<", ``LS_xnum_xnum``);

(******************************************************************************
* Extend less-than-or-equal predicate (<=) to extended numbers
******************************************************************************)
val LE_num_xnum_def =
 Define
  `($LE_num_xnum (m:num) (XNUM (n:num)) = (m:num) <= (n:num))
   /\
   ($LE_num_xnum (m:num) INFINITY = T)`;

val LE_xnum_num_def =
 Define
  `($LE_xnum_num (XNUM (m:num)) (n:num) = (m:num) <= (n:num))
   /\
   ($LE_xnum_num INFINITY (n:num) = F)`;

val LE_xnum_xnum_def =
 Define
  `($LE_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) <= (n:num))
   /\
   ($LE_xnum_xnum (XNUM (m:num)) INFINITY = T)
   /\
   ($LE_xnum_xnum INFINITY (XNUM (n:num)) = F)
   /\
   ($LE_xnum_xnum INFINITY INFINITY = T)`;

val LE =
 save_thm("LE",LIST_CONJ[LE_num_xnum_def,LE_xnum_num_def,LE_xnum_xnum_def]);

val _ = overload_on("<=", ``LE_num_xnum``);
val _ = overload_on("<=", ``LE_xnum_num``);
val _ = overload_on("<=", ``LE_xnum_xnum``);

(******************************************************************************
* Extend greater-than predicate (>) to extended numbers
******************************************************************************)

Definition GT_num_xnum_def:
  ($GT_num_xnum (m:num) (XNUM (n:num)) <=> (m:num) > (n:num))
   /\
  ($GT_num_xnum (m:num) INFINITY <=> F)
End

val GT_xnum_num_def =
 Define
  `($GT_xnum_num (XNUM (m:num)) (n:num) = (m:num) > (n:num))
   /\
   ($GT_xnum_num INFINITY (n:num) = T)`;

val GT_xnum_xnum_def =
 Define
  `($GT_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) > (n:num))
   /\
   ($GT_xnum_xnum (XNUM (m:num)) INFINITY = F)
   /\
   ($GT_xnum_xnum INFINITY (XNUM (n:num)) = T)`;

val GT =
 save_thm("GT",LIST_CONJ[GT_num_xnum_def,GT_xnum_num_def,GT_xnum_xnum_def]);

val _ = overload_on(">", ``GT_num_xnum``);
val _ = overload_on(">", ``GT_xnum_num``);
val _ = overload_on(">", ``GT_xnum_xnum``);

(******************************************************************************
* Extend greater-than-or-equal predicate (>=) to extended numbers
******************************************************************************)

Definition GE_num_xnum_def:
  ($GE_num_xnum (m:num) (XNUM (n:num)) = (m:num) >= (n:num))
   /\
  ($GE_num_xnum (m:num) INFINITY = F)
End

val GE_xnum_num_def =
 Define
  `($GE_xnum_num (XNUM (m:num)) (n:num) = (m:num) >= (n:num))
   /\
   ($GE_xnum_num INFINITY (n:num) = T)`;

val GE_xnum_xnum_def =
 Define
  `($GE_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) >= (n:num))
   /\
   ($GE_xnum_xnum (XNUM (m:num)) INFINITY = F)
   /\
   ($GE_xnum_xnum INFINITY (XNUM (n:num)) = T)`;

val GE =
 save_thm("GE",LIST_CONJ[GE_num_xnum_def,GE_xnum_num_def,GE_xnum_xnum_def]);

val _ = overload_on(">=", ``GE_num_xnum``);
val _ = overload_on(">=", ``GE_xnum_num``);
val _ = overload_on(">=", ``GE_xnum_xnum``);

val GT_LS =
 store_thm
  ("GT_LS",
   ``!x:xnum n:num. (x > n) = (n < x)``,
   Cases_on `x`
    THEN RW_TAC arith_ss [GT_xnum_num_def,LS_num_xnum_def]);

(******************************************************************************
* LESS m is predicate to test if a number is less than m
* LESS : num -> num -> bool
******************************************************************************)
val LESS_def =
 Define `LESS (m:num) (n:num) = n < m`;

(******************************************************************************
* LESSX m is predicate to test if a number is less than extended number m
* LESSX : xnum -> num -> bool
******************************************************************************)
val LESSX_def =
 Define `LESSX (m:xnum) (n:num) = n < m`;

val _ = overload_on ("LESS", Term`LESSX`);

val IN_LESS =
 store_thm
  ("IN_LESS",
   ``!m n:num. m IN LESS n = m < n``,
   RW_TAC arith_ss [IN_DEF,LESS_def]);

val IN_LESSX =
 store_thm
  ("IN_LESSX",
   ``!m:num. (m IN LESSX INFINITY) /\ !n:num. m IN LESSX (XNUM n) = m < n``,
   RW_TAC arith_ss [IN_DEF,LESSX_def,LS]);

(******************************************************************************
* LENGTH(FINITE l)   = XNUM(LENGTH l)
* LENGTH(INFINITE l) = INFINITY
******************************************************************************)
val LENGTH_def =
 Define `(LENGTH(FINITE l)   = XNUM(list$LENGTH l))
         /\
         (LENGTH(INFINITE p) = INFINITY)`;

(******************************************************************************
* ELEM (p0 p1 p2 p3 ...) n = pn
******************************************************************************)
val ELEM_def = Define `ELEM p n = HEAD(RESTN p n)`;

val LENGTH_REST =
 store_thm
  ("LENGTH_REST",
   ``!p. IS_FINITE p /\ 0 < LENGTH p
           ==> (LENGTH(REST p) = LENGTH p - 1)``,
    Cases
     THEN RW_TAC std_ss
           [LENGTH_def,REST_def,IS_FINITE_def,LENGTH_CONS,SUB,LS,IS_FINITE_def,
           Cooper.COOPER_PROVE``0 < n = ?m. n = SUC m``]
     THEN RW_TAC list_ss []);

val LENGTH_REST_COR =
 store_thm
  ("LENGTH_REST_COR",
   ``!l. 0 < LENGTH(FINITE l) ==> (LENGTH(REST(FINITE l)) = LENGTH(FINITE l) - 1)``,
    PROVE_TAC[LENGTH_REST,IS_FINITE_def]);

val LENGTH_RESTN =
 store_thm
  ("LENGTH_RESTN",
   ``!n p. IS_FINITE p /\ n < LENGTH p
           ==> (LENGTH(RESTN p n) = LENGTH p - n)``,
   Induct
    THEN Cases
    THEN RW_TAC list_ss
          [LENGTH_def,RESTN_def,IS_FINITE_REST,SUB,
           IS_FINITE_def,REST_def,LENGTH_RESTN,LS,EL]
    THEN `PSLPath$LENGTH(FINITE(TL l)) = XNUM(list$LENGTH(TL l))` by RW_TAC std_ss [LENGTH_def]
    THEN Cases_on `l`
    THEN FULL_SIMP_TAC list_ss [DECIDE ``~(SUC n < 0)``]
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `FINITE t` (el 3 thl)))
    THEN FULL_SIMP_TAC std_ss [IS_FINITE_def,LENGTH_def,LS,SUB,EL]);

val LENGTH_RESTN_COR =
 store_thm
  ("LENGTH_RESTN_COR",
   ``!n l. n < LENGTH(FINITE l)
           ==>
           (LENGTH(RESTN(FINITE l) n) = LENGTH(FINITE l) - n)``,
   PROVE_TAC[LENGTH_RESTN,IS_FINITE_def]);

(******************************************************************************
* 0 < i ==> (RESTN (REST(INFINITE f)) (i-1) = RESTN (INFINITE f) i)
******************************************************************************)
val RESTN_REST_INFINITE =
 store_thm
  ("RESTN_REST_INFINITE",
   ``!f i. 0 < i ==> (RESTN (REST(INFINITE f)) (i-1) = RESTN (INFINITE f) i)``,
   Induct_on `i`
    THEN RW_TAC list_ss [RESTN_def]);

(******************************************************************************
* RESTN (REST (INFINITE f)) k = RESTN (INFINITE f) (k + 1)
******************************************************************************)
val RESTN_REST_INFINITE_COR =
 save_thm
  ("RESTN_REST_INFINITE_COR",
   SIMP_RULE arith_ss
    [DECIDE``(k+1)-1=k``](Q.SPECL[`f`,`k+1`]RESTN_REST_INFINITE));

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
* CONS(x,p) add x to the front of p
******************************************************************************)
val CONS_def =
 Define
  `(CONS(x, FINITE l) = FINITE(list$CONS x l))
   /\
   (CONS(x, INFINITE f) =
     INFINITE(\n. if n=0 then x else f(n-1)))`;

val IS_INFINITE_CONS =
 store_thm
  ("IS_INFINITE_CONS",
   ``!p x. IS_INFINITE(CONS(x,p)) = IS_INFINITE p``,
   Induct
    THEN RW_TAC list_ss [IS_INFINITE_def,CONS_def]);

val IS_FINITE_CONS =
 store_thm
  ("IS_FINITE_CONS",
   ``!p x. IS_FINITE(CONS(x,p)) = IS_FINITE p``,
   Induct
    THEN RW_TAC list_ss [IS_FINITE_def,CONS_def]);

val HEAD_CONS =
 store_thm
  ("HEAD_CONS",
   ``!x p. HEAD(CONS(x,p)) = x``,
   REPEAT GEN_TAC
    THEN Cases_on `p`
    THEN RW_TAC list_ss [HEAD_def,CONS_def]);

val REST_CONS =
 store_thm
  ("REST_CONS",
   ``!x p. REST(CONS(x,p)) = p``,
   REPEAT GEN_TAC
    THEN Cases_on `p`
    THEN RW_TAC list_ss [REST_def,CONS_def,ETA_AX]);

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
* 0 < i /\ 0 < LENGTH l ==> (ELEM (FINITE(TL l)) (i-1) = ELEM (FINITE l) i)
******************************************************************************)
val ELEM_FINITE_TL =
 store_thm
  ("ELEM_FINITE_TL",
   ``!l i. 0 < i /\ 0 < LENGTH l
           ==>
           (ELEM (FINITE(TL l)) (i-1) = ELEM (FINITE l) i)``,
   Induct_on `i`
    THEN RW_TAC list_ss [ELEM_def,REST_def,RESTN_def]);

(******************************************************************************
* 0 < LENGTH l ==> (ELEM (FINITE (TL l)) k = ELEM (FINITE l) (k + 1))
******************************************************************************)
val ELEM_FINITE_TL_COR =
 save_thm
  ("ELEM_FINITE_TL_COR",
   SIMP_RULE arith_ss [DECIDE``(k+1)-1=k``](Q.SPECL[`l`,`k+1`]ELEM_FINITE_TL));

(******************************************************************************
* REST(INFINITE f) = INFINITE(\n. f(n+1))
******************************************************************************)
val REST_INFINITE =
 store_thm
  ("REST_INFINITE",
   ``!f. REST (INFINITE f) = INFINITE(\n. f(n+1))``,
   RW_TAC list_ss [REST_def]);

(******************************************************************************
* RESTN (INFINITE f) i = INFINITE(\n. f(n+i))
******************************************************************************)
val RESTN_INFINITE =
 store_thm
  ("RESTN_INFINITE",
   ``!f i. RESTN (INFINITE f) i = INFINITE(\n. f(n+i))``,
   Induct_on `i`
    THEN RW_TAC list_ss
          [REST_INFINITE,ETA_AX,RESTN_def,
           DECIDE``i + (n + 1) = n + SUC i``]);

(******************************************************************************
* LENGTH (RESTN (INFINITE p) n) = INFINITY
******************************************************************************)
val LENGTH_RESTN_INFINITE =
 store_thm
  ("LENGTH_RESTN_INFINITE",
   ``!p n. LENGTH (RESTN (INFINITE p) n) = INFINITY``,
   RW_TAC std_ss [RESTN_INFINITE,LENGTH_def]);

val LENGTH_RESTN_THM =
 store_thm
  ("LENGTH_RESTN_THM",
   ``n < LENGTH p ==> (LENGTH (RESTN p n) = LENGTH p - n)``,
   Cases_on `p`
    THEN RW_TAC std_ss
          [LS_num_xnum_def,LENGTH_RESTN,LENGTH_RESTN_INFINITE,RESTN_FINITE,
           LENGTH_def,SUB,FinitePSLPathTheory.LENGTH_RESTN]);

(******************************************************************************
* 0 < i  ==> (ELEM (FINITE(TL l)) (i-1) = ELEM (FINITE l) i)
******************************************************************************)
val ELEM_REST_INFINITE =
 store_thm
  ("ELEM_REST_INFINITE",
   ``!f i. 0 < i ==> (ELEM (REST(INFINITE f)) (i-1) = ELEM (INFINITE f) i)``,
   Induct_on `i`
    THEN RW_TAC list_ss [ELEM_def,RESTN_def]);

(******************************************************************************
* ELEM (REST (INFINITE l)) k = ELEM (INFINITE l) (k + 1)
******************************************************************************)
val ELEM_REST_INFINITE_COR =
 save_thm
  ("ELEM_REST_INFINITE_COR",
   SIMP_RULE arith_ss [DECIDE``(k+1)-1=k``](Q.SPECL[`l`,`k+1`]ELEM_REST_INFINITE));

(******************************************************************************
* CAT(w,p) creates a new path by concatenating w in front of p
******************************************************************************)
val CAT_def =
 Define
  `(CAT([], p) = p)
   /\
   (CAT((x::w), p) = CONS(x, CAT(w,p)))`;

val CAT_FINITE_APPEND =
 store_thm
  ("CAT_FINITE_APPEND",
   ``!l p. CAT(l, FINITE p) = FINITE(APPEND l p)``,
   Induct
    THEN RW_TAC list_ss [CAT_def,CONS_def]);

val LENGTH_CAT_FINITE =
 store_thm
  ("LENGTH_CAT_FINITE",
   ``!l1 l2. LENGTH(CAT(l1, FINITE l2)) = XNUM(LENGTH l1 + LENGTH l2)``,
   Induct
    THEN RW_TAC list_ss
          [CAT_def,LENGTH_def,CAT_FINITE_APPEND,CONS_def]);

val IS_INFINITE_EXISTS =
 store_thm
  ("IS_INFINITE_EXISTS",
   ``!w. IS_INFINITE w = ?p. w = INFINITE p``,
   Induct
    THEN RW_TAC list_ss [IS_INFINITE_def]);

val CAT_INFINITE =
 store_thm
  ("CAT_INFINITE",
   ``!l p. IS_INFINITE(CAT(l, INFINITE p))``,
   Induct
    THEN RW_TAC list_ss [CAT_def,CONS_def,IS_INFINITE_def]
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN IMP_RES_TAC IS_INFINITE_EXISTS
    THEN RW_TAC std_ss [CONS_def,IS_INFINITE_def]);

val LENGTH_CAT_INFINITE =
 store_thm
  ("LENGTH_CAT_INFINITE",
   ``!l p. LENGTH(CAT(l, INFINITE p)) = INFINITY``,
   Induct
    THEN RW_TAC list_ss
          [CAT_def,LENGTH_def,CONS_def]
    THEN `IS_INFINITE(CAT (l,INFINITE p))` by PROVE_TAC[CAT_INFINITE]
    THEN IMP_RES_TAC IS_INFINITE_EXISTS
    THEN RW_TAC std_ss [CONS_def,LENGTH_def]);

val LENGTH_CAT =
 save_thm("LENGTH_CAT",CONJ LENGTH_CAT_FINITE LENGTH_CAT_INFINITE);


(******************************************************************************
* Append paths
******************************************************************************)
val PATH_APPEND_def =
 Define
  `(PATH_APPEND (FINITE l1) (FINITE l2) = FINITE(APPEND l1 l2))
   /\
   (PATH_APPEND (FINITE l) p = CAT(l, p))
   /\
   (PATH_APPEND (INFINITE f) _ = INFINITE f)`;

(******************************************************************************
* Infix list concatenation
******************************************************************************)
val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);
val _ = overload_on ("<>", Term`PATH_APPEND`);

val IS_INFINITE_CAT =
 store_thm
  ("IS_INFINITE_CAT",
   ``!p l. IS_INFINITE(CAT(l,p)) = IS_INFINITE p``,
   Induct_on `l`
    THEN RW_TAC list_ss [IS_INFINITE_def,CAT_def,IS_INFINITE_CONS]);

val IS_FINITE_CAT =
 store_thm
  ("IS_FINITE_CAT",
   ``!p l. IS_FINITE(CAT(l,p)) = IS_FINITE p``,
   Induct_on `l`
    THEN RW_TAC list_ss [IS_FINITE_def,CAT_def,IS_FINITE_CONS]);

val ELEM_CAT_SEL =
 store_thm
  ("ELEM_CAT_SEL",
   ``!(w:'a path) i (w':'a path). ELEM (CAT (SEL w (0,i),w')) 0 = ELEM w 0``,
   Induct_on `i`
    THEN RW_TAC simp_arith_ss
          [SEL_ELEM,CAT_def,ELEM_def,HEAD_def,RESTN_def,REST_def,HEAD_CONS,
           SEL_def,SEL_REC_def,FinitePSLPathTheory.SEL_def,FinitePSLPathTheory.SEL_REC_def,
           CAT_def,DECIDE``SUC i + 1= SUC(i+1)``]);

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

val SEL_APPEND_SINGLETON_IMP =
 store_thm
  ("SEL_APPEND_SINGLETON_IMP",
   ``j > i
     ==>
     (SEL p (i,j) = APPEND w [l]) ==> (SEL p (i,j-1) = w) /\ (ELEM p j = l)``,
   REPEAT DISCH_TAC
    THEN IMP_RES_TAC(DECIDE ``j:num > i:num ==> (i <= (j-1) /\ (j-1) < j)``)
    THEN IMP_RES_TAC(DECIDE``j:num > i:num ==> (j - 1 + 1 = j)``)
    THEN IMP_RES_TAC(ISPEC ``p :'a path`` SEL_SPLIT)
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
    THEN IMP_RES_TAC(DECIDE ``j:num > i:num ==> i <= j - 1 /\ j - 1 < j``)
    THEN IMP_RES_TAC
          (ISPECL [``p :'a path``,``j:num-1``,``i:num``,``j:num``] SEL_SPLIT)
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
    THEN IMP_RES_TAC(DECIDE ``SUC i:num <= j:num ==> ((SUC (j - SUC i)) = (j-i))``)
    THEN RW_TAC arith_ss []
    THEN ASSUM_LIST
          (fn thl =>
           ASSUME_TAC
            (GSYM
             (Q.GEN `p`
              (SIMP_RULE arith_ss thl (Q.SPECL [`p`,`i`,`j`] SEL_def)))))
    THEN IMP_RES_TAC(DECIDE ``SUC i:num <= j:num ==> (SUC (j - i) = j + 1 - i)``)
    THEN RW_TAC arith_ss []
    THEN IMP_RES_TAC(DECIDE ``SUC i:num <= j:num ==> i <= j-1``)
    THEN RES_TAC
    THEN IMP_RES_TAC(DECIDE ``SUC i:num <= j:num ==> (SUC(j-1)=j)``)
    THEN ASSUM_LIST
          (fn thl => ASSUME_TAC(SIMP_RULE std_ss [el 1 thl] (el 2 thl)))
    THEN RW_TAC arith_ss [SEL_def]);

val TL_SEL =
 store_thm
  ("TL_SEL",
   ``!i j p. i < j ==> (TL(SEL p (i,j)) = SEL (REST p) (i,j-1))``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC(DECIDE ``i:num < j:num ==> i <= j-1``)
    THEN IMP_RES_TAC TL_SEL_SUC
    THEN IMP_RES_TAC(DECIDE ``i:num < j:num ==> (SUC(j-1)=j)``)
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
          [SEL_REC_def,ELEM_def,RESTN_def,EL,
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
    THEN RW_TAC list_ss [SEL_REC_def,ELEM_def,RESTN_def,HD_SEL0,EL]
    THEN Induct_on `i`
    THEN RW_TAC list_ss [SEL_REC_def,ELEM_def,RESTN_def,TL_SEL0,EL]);

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

val _ = export_theory();
