open HolKernel Parse boolLib bossLib

val _ = new_theory "ctl"; 

open pairTheory;
open pairLib;
open pairTools;
open pairSyntax;
open PairRules;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open stringTheory;
open sumTheory;
open ksTheory;
open numLib;
open setLemmasTheory;
open res_quanLib
open envTheory

val _ = numLib.prefer_num();

(* Most of this is cannibalised from MJCG's old Sugar2 theories *)

(******************************************************************************
* Boolean expressions
******************************************************************************)
val bexp_def =
 Hol_datatype
  `bexp = B_TRUE                                  (* truth *)
        | B_PROP   of 'a                         (* atomic proposition       *)
        | B_NOT    of bexp                       (* negation                 *)
        | B_AND    of bexp # bexp`;              (* conjunction              *)

(******************************************************************************
* Definition of disjunction
******************************************************************************)

val B_OR_def =
 Define `B_OR(b1,b2) = B_NOT(B_AND(B_NOT b1, B_NOT b2))`;

(******************************************************************************
* Definition of falsity
******************************************************************************)

val B_FALSE_def =
 Define `B_FALSE = B_NOT B_TRUE`;


(******************************************************************************
* Formulas of Sugar Optional Branching Extension (CTL)
******************************************************************************)
val ctl_def =
 Hol_datatype
  `ctl = C_BOOL        of 'a bexp                (* boolean expression       *)
       | C_NOT         of ctl                    (* \neg f                   *)
       | C_AND         of ctl # ctl              (* f1 \wedge f2             *)
       | C_EX          of ctl                    (* EX f                     *)
       | C_EU          of ctl # ctl              (* E[f1 U f2]               *)
       | C_EG          of ctl`;                  (* EG f                     *)

(******************************************************************************
* ``: ('state,'prop)kripke_structure``
******************************************************************************)
val kripke_structure_def =
 Hol_datatype
  `kripke_structure = 
    <| S: 'state -> bool;
       S0:'state -> bool;
       R: 'state # 'state -> bool;
       P: 'prop -> bool;
       L: 'state -> ('prop -> bool) |>`;

val TOTAL_def = Define `TOTAL R = !s. ?s'. R(s,s')`;

(* show that the totalisation in ctlTools works *)
val TOTAL_THM = save_thm("TOTAL_THM",prove(``!R. TOTAL \(s,s').(R(s,s') \/ ((~?s'.R(s,s')) /\ (s'=s)))``,
REWRITE_TAC [TOTAL_def] THEN PBETA_TAC
THEN REPEAT GEN_TAC
THEN CONV_TAC (EXISTS_OR_CONV)
THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV)
THEN Cases_on `(?s'. R (s,s'))` THENL [
DISJ1_TAC THEN ASM_REWRITE_TAC [],
DISJ2_TAC THEN ASM_REWRITE_TAC []
THEN Q.EXISTS_TAC `s` THEN REFL_TAC]))

(******************************************************************************
* B_SEM l b means "l |= b" where l is a letter, i.e. l : 'prop -> bool
******************************************************************************)
val B_SEM_def =
 Define
  `(B_SEM l B_TRUE = T) 
   /\ 
   (B_SEM l (B_PROP(p:'prop)) = p IN l)
   /\
   (B_SEM l (B_NOT b)         = ~(B_SEM l b))
   /\
   (B_SEM l (B_AND(b1,b2))    = B_SEM l b1 /\ B_SEM l b2)`;

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

(*val RESTN_FINITE =
 store_thm
  ("RESTN_FINITE",
   ``!l n. RESTN (FINITE l) n = FINITE(RESTN l n)``,
   Induct_on `n`
    THEN RW_TAC std_ss 
          [RESTN_def,FinitePathTheory.RESTN_def,
           REST_def,FinitePathTheory.REST_def]);*)

val FINITE_TL =
 store_thm
  ("FINITE_TL",
   ``!l. 0 < LENGTH l ==> (FINITE(TL l) = REST(FINITE l))``,
   Induct
    THEN RW_TAC list_ss [REST_def]);

(******************************************************************************
* LENGTH(FINITE l) = LENGTH l
* LENGTH is not specified on infinite paths, but LEN (defined below) is.
******************************************************************************)
val LENGTH_def = 
 Define `LENGTH (FINITE l)   = list$LENGTH l`;

(******************************************************************************
* ELEM (p0 p1 p2 p3 ...) n = pn
******************************************************************************)
val ELEM_def = Define `ELEM p n = HEAD(RESTN p n)`;

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
  `$SUB_num_xnum (m:num) (XNUM (n:num)) = XNUM((m:num) - (n:num))	`;

val SUB_xnum_num_def =
 Define `$SUB_xnum_num (XNUM (m:num)) (n:num) = XNUM((m:num) - (n:num))`;

val SUB_xnum_xnum_def =
 Define 
  `($SUB_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = XNUM((m:num) - (n:num)))
   /\
   ($SUB_xnum_xnum INFINITY (XNUM (n:num)) = INFINITY)`;

val SUB = 
 save_thm
  ("SUB",
   LIST_CONJ(type_rws "xnum"@[SUB_num_xnum_def,SUB_xnum_num_def,SUB_xnum_xnum_def]));

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
 Define `$LS_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) < (n:num)`;

val LS = 
 save_thm("LS",LIST_CONJ[LS_num_xnum_def,LS_xnum_num_def,LS_xnum_xnum_def]);

val _ = overload_on("<", ``LS_num_xnum``);
val _ = overload_on("<", ``LS_xnum_num``);
val _ = overload_on("<", ``LS_xnum_xnum``);

(******************************************************************************
* Extend greater-than predicate (>) to extended numbers
******************************************************************************)
val GT_num_xnum_def =
 Define `$GT_num_xnum (m:num) (XNUM (n:num)) = (m:num) > (n:num)`;

val GT_num_xnum_def =
 Define 
  `($GT_num_xnum (m:num) (XNUM (n:num)) = (m:num) > (n:num))
   /\
   ($GT_num_xnum (m:num) INFINITY = F)`;

val GT_xnum_num_def =
 Define 
  `($GT_xnum_num (XNUM (m:num)) (n:num) = (m:num) > (n:num))
   /\
   ($GT_xnum_num INFINITY (n:num) = T)`;

val GT_xnum_xnum_def =
 Define `$GT_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) > (n:num)`;

val GT = 
 save_thm("GT",LIST_CONJ[GT_num_xnum_def,GT_xnum_num_def,GT_xnum_xnum_def]);

val _ = overload_on(">", ``GT_num_xnum``);
val _ = overload_on(">", ``GT_xnum_num``);
val _ = overload_on(">", ``GT_xnum_xnum``);

(******************************************************************************
* LENGTH(FINITE l)   = XNUM(LENGTH l)
* LENGTH(INFINITE l) = INFINITY
******************************************************************************)
val LENGTH_def = 
 Define `(LENGTH(FINITE l)   = XNUM(list$LENGTH l))
         /\
         (LENGTH(INFINITE p) = INFINITY)`;

(******************************************************************************
* PATH M p is true iff p is a path with respect to transition relation M.R
******************************************************************************)
val PATH_def = Define `PATH M p s = IS_INFINITE p /\ (ELEM p 0 = s) /\ (!n. M.R(ELEM p n, ELEM p (n+1)))`;

(******************************************************************************
* C_SEM M s f means "M, s |= f" 
******************************************************************************)
val C_SEM_def =
 Define
  `(C_SEM M (C_BOOL b) s = B_SEM (M.L s) b)
   /\
   (C_SEM M (C_NOT f) s = ~(C_SEM M f s)) 
   /\
   (C_SEM M (C_AND(f1,f2)) s = C_SEM M f1 s /\ C_SEM M f2 s)
   /\
   (C_SEM M (C_EX f) s = 
     ?p. PATH M p s /\ C_SEM M f (ELEM p 1))
   /\
   (C_SEM M (C_EU(f1,f2)) s = 
     ?p. PATH M p s /\ 
         ?k :: (0 to LENGTH p). C_SEM M f2 (ELEM p k) /\ !j. j < k ==> C_SEM M f1 (ELEM p j))
   /\
   (C_SEM M (C_EG f) s = 
     ?p. PATH M p s /\ !j :: (0 to LENGTH p). C_SEM M f (ELEM p j))`;

val CTL_MODEL_SAT_def = Define `CTL_MODEL_SAT M f = (!s. s IN M.S0 ==> C_SEM M f s)`

val C_AX_def = Define `C_AX (f: 'prop ctl) = C_NOT (C_EX (C_NOT f))`;
val C_EF_def = Define `C_EF (f: 'prop ctl) = C_EU(C_BOOL B_TRUE,f)`;
val C_AF_def = Define `C_AF (f: 'prop ctl) = C_NOT(C_EG (C_NOT f))`;
val C_AG_def = Define `C_AG (f: 'prop ctl) = C_NOT (C_EF (C_NOT f))`;
val C_AU_def = Define `C_AU ((f1: 'prop ctl),(f2: 'prop ctl)) = C_AND(C_NOT(C_EU(C_NOT f2,C_AND(C_NOT f1,C_NOT f2))),C_NOT(C_EG(C_NOT f2)))`; 
val C_AR_def = Define `C_AR(f,g) = C_NOT (C_EU (C_NOT f,C_NOT g))`;
val C_OR_def = Define `C_OR((f1: 'prop ctl),(f2: 'prop ctl)) = C_NOT(C_AND(C_NOT f1, C_NOT f2))`;
val C_IMP_def = Define `C_IMP((f: 'prop ctl),(g: 'prop ctl)) = C_OR(C_NOT f,g)`;
val C_IFF_def = Define `C_IFF (f: 'prop ctl) (g: 'prop ctl) = C_AND(C_IMP(f,g),C_IMP(g,f))`;
val B_IMP_def = Define `B_IMP((f: 'a bexp),(g: 'a bexp)) = B_OR(B_NOT f,g)`;
val B_IFF_def = Define `B_IFF (f: 'a bexp) (g: 'a bexp) = B_AND(B_IMP(f,g),B_IMP(g,f))`;
val B_AND2_def = Define `B_AND2 (f: 'a bexp) (g: 'a bexp) = B_AND(f,g)`;
val B_OR2_def = Define `B_OR2 (f: 'a bexp) (g: 'a bexp) = B_OR(f,g)`;
val C_AND2_def = Define `C_AND2 (f: 'prop ctl) (g: 'prop ctl) = C_AND(f,g)`;
val C_OR2_def = Define `C_OR2 (f: 'prop ctl) (g: 'prop ctl) = C_OR(f,g)`;
val C_IMP2_def = Define `C_IMP2 (f: 'prop ctl) (g: 'prop ctl) = C_IMP(f,g)`;
val B_IMP2_def = Define `B_IMP2 (f: 'a bexp) (g: 'a bexp) = B_IMP(f,g)`;

val _ = overload_on ("~", mk_const("~",Type`:bool -> bool`));
val _ = overload_on ("~", (Term`C_NOT`));
val _ = overload_on ("~", (Term`B_NOT`));
val _ = overload_on ("~", mk_const("~",Type`:bool -> bool`));
fun prepOverload s = overload_on (s, mk_const(s,Type`:bool -> bool -> bool`));
val _ = app prepOverload ["/\\", "\\/","==>"];
val _ = overload_on ("/\\", (Term `C_AND2`)); val _ = prepOverload "/\\";
val _ = overload_on ("\\/", (Term `C_OR2`)); val _ = prepOverload "\\/";
val _ = overload_on ("/\\", (Term `B_AND2`)); val _ = prepOverload "/\\";
val _ = overload_on ("\\/", (Term `B_OR2`)); val _ = prepOverload "\\/";
val _ = overload_on ("==>", (Term `C_IMP2`)); val _ = prepOverload "==>";
val _ = overload_on ("==>", (Term `B_IMP2`)); val _ = prepOverload "==>";
val _ = overload_on ("=", (Term `C_IFF`)); val _ = prepOverload "=";
val _ = overload_on ("=", (Term `B_IFF`)); val _ = prepOverload "=";
val _ = overload_on ("T",Term`T:bool`); val _ = overload_on ("T",Term`B_TRUE`); val _ = overload_on ("T",Term`T:bool`);
val _ = overload_on ("F",Term`F:bool`); val _ = overload_on ("F",Term`B_FALSE`); val _ = overload_on ("F",Term`F:bool`);

val CTL_NNF = Define `
(CTL_NNF (C_BOOL b) = C_BOOL b) /\
(CTL_NNF (C_AND(f,g))  = C_AND(CTL_NNF f,CTL_NNF g)) /\
(CTL_NNF (C_EX f)  = C_EX (CTL_NNF f)) /\
(CTL_NNF (C_EG f)  = C_EG (CTL_NNF f)) /\
(CTL_NNF (C_EU(f,g))  = C_EU (CTL_NNF f,CTL_NNF g)) /\
(CTL_NNF (C_NOT (C_BOOL b)) = C_NOT (C_BOOL b)) /\
(CTL_NNF (C_NOT (C_AND(f,g))) = C_OR(CTL_NNF(C_NOT f),CTL_NNF(C_NOT g))) /\
(CTL_NNF (C_NOT (C_NOT f)) = f) /\
(CTL_NNF (C_NOT (C_EX f)) = C_AX (CTL_NNF (C_NOT f))) /\
(CTL_NNF (C_NOT (C_EG f)) = C_AF (CTL_NNF (C_NOT f))) /\
(CTL_NNF (C_NOT (C_EU(f,g))) = C_AR(CTL_NNF(C_NOT f),CTL_NNF(C_NOT g)))`;

val CTL_BOOL_SUB = Define `
(CTL_BOOL_SUB g (B_PROP (b:'prop)) = (g = B_PROP b)) /\
(CTL_BOOL_SUB g (B_NOT be1) = (CTL_BOOL_SUB g be1) \/ (g = B_NOT be1)) /\
(CTL_BOOL_SUB g (B_AND(be1,be2)) = (CTL_BOOL_SUB g be1) \/ (CTL_BOOL_SUB g be2) \/ (g = B_AND(be1,be2)))`;

val CTL_SUB = Define `
(CTL_SUB g (C_BOOL b) = ?b'. (g = C_BOOL b') /\ CTL_BOOL_SUB b' b) /\
(CTL_SUB g (C_AND(f1,f2)) = (CTL_SUB g f1) \/ (CTL_SUB g f2) \/ (g = C_AND(f1,f2))) /\
(CTL_SUB g (C_NOT f) = (CTL_SUB g f) \/ (g=C_NOT f)) /\
(CTL_SUB g (C_EX f) = (CTL_SUB g f) \/ (g=C_EX f)) /\
(CTL_SUB g (C_EG f) = (CTL_SUB g f) \/ (g=C_EG f)) /\
(CTL_SUB g (C_EU(f1,f2)) = (CTL_SUB g f1) \/ (CTL_SUB g f2) \/ (g=C_EU(f1,f2)))`;

val IS_ACTL = Define `IS_ACTL f = (!g. ~CTL_SUB (C_EX g) (CTL_NNF f)) /\ (!g. ~CTL_SUB (C_EG g) (CTL_NNF f)) /\ (!g1 g2. ~CTL_SUB (C_EU(g1,g2)) (CTL_NNF f))`;   

val SAT_NNF_ID = save_thm("SAT_NNF_ID",prove(``!f M. C_SEM M (CTL_NNF f) = C_SEM M f``,
REWRITE_TAC [FUN_EQ_THM]
THEN recInduct (theorem "CTL_NNF_ind") THEN SIMP_TAC std_ss [CTL_NNF]
THEN REWRITE_TAC [FUN_EQ_THM,C_AR_def,C_AX_def,C_AF_def,C_OR_def]  THEN SIMP_TAC std_ss [C_SEM_def]));

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


val _ = export_theory()
