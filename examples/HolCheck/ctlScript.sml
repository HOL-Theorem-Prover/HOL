(* app load ["envTheory","setLemmasTheory","res_quanLib","stringLib","pred_setLib","ksTheory"] *)
Theory ctl
Ancestors
  pair pred_set list string sum ks setLemmas env
Libs
  pairLib pairTools pairSyntax PairRules pred_setLib stringLib
  simpLib numLib res_quanLib


val _ = numLib.temp_prefer_num();

(* Most of this is cannibalised from MJCG's old Sugar2 theories *)

(******************************************************************************
* Boolean expressions
******************************************************************************)
Datatype:
   bexp = B_TRUE                                 (* truth *)
        | B_PROP   of 'a                         (* atomic proposition       *)
        | B_NOT    of bexp                       (* negation                 *)
        | B_AND    of bexp # bexp                (* conjunction              *)
End

(******************************************************************************
* Definition of disjunction
******************************************************************************)

Definition B_OR_def:
  B_OR(b1,b2) = B_NOT(B_AND(B_NOT b1, B_NOT b2))
End

(******************************************************************************
* Definition of falsity
******************************************************************************)

Definition B_FALSE_def:
  B_FALSE = B_NOT B_TRUE
End


(******************************************************************************
* Formulas of Sugar Optional Branching Extension (CTL)
******************************************************************************)
Datatype:
   ctl = C_BOOL        of 'a bexp                (* boolean expression       *)
       | C_NOT         of ctl                    (* \neg f                   *)
       | C_AND         of ctl # ctl              (* f1 \wedge f2             *)
       | C_EX          of ctl                    (* EX f                     *)
       | C_EU          of ctl # ctl              (* E[f1 U f2]               *)
       | C_EG          of ctl                    (* EG f                     *)
End

(******************************************************************************
* ``: ('prop,'state)kripke_structure``
******************************************************************************)
Datatype:
   kripke_structure =
    <| S: 'state -> bool;
       S0:'state -> bool;
       R: 'state # 'state -> bool;
       P: 'prop -> bool;
       L: 'state -> ('prop -> bool) |>
End

(******************************************************************************
* B_SEM l b means "l |= b" where l is a letter, i.e. l : 'prop -> bool
******************************************************************************)
Definition B_SEM_def:
   (B_SEM l B_TRUE = T)
   /\
   (B_SEM l (B_PROP(p:'prop)) = p IN l)
   /\
   (B_SEM l (B_NOT b)         = ~(B_SEM l b))
   /\
   (B_SEM l (B_AND(b1,b2))    = B_SEM l b1 /\ B_SEM l b2)
End

(******************************************************************************
* A path is finite or infinite
******************************************************************************)
Datatype:
   path = FINITE   of ('s list)
        | INFINITE of (num -> 's)
End

(******************************************************************************
* Tests
******************************************************************************)
Definition IS_FINITE_def:
  (IS_FINITE(FINITE p)   = T)
         /\
         (IS_FINITE(INFINITE f) = F)
End

Definition IS_INFINITE_def:
  (IS_INFINITE(FINITE p)   = F)
         /\
         (IS_INFINITE(INFINITE f) = T)
End

(******************************************************************************
* HEAD (p0 p1 p2 p3 ...) = p0
******************************************************************************)
Definition HEAD_def:
  (HEAD (FINITE p) = HD p)
         /\
         (HEAD (INFINITE f)  = f 0)
End

(******************************************************************************
* REST (p0 p1 p2 p3 ...) = (p1 p2 p3 ...)
******************************************************************************)
Definition REST_def:
  (REST (FINITE p) = FINITE(TL p))
         /\
         (REST (INFINITE f) = INFINITE(\n. f(n+1)))
End

(******************************************************************************
* RESTN (p0 p1 p2 p3 ...) n = (pn p(n+1) p(n+2) ...)
******************************************************************************)
Definition RESTN_def:
  (RESTN p 0 = p) /\ (RESTN p (SUC n) = RESTN (REST p) n)
End

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
(*val LENGTH_def =
 Define `LENGTH (FINITE l)   = list$LENGTH l`;*)

(******************************************************************************
* ELEM (p0 p1 p2 p3 ...) n = pn
******************************************************************************)
Definition ELEM_def:   ELEM p n = HEAD(RESTN p n)
End

(******************************************************************************
* Extended numbers.
******************************************************************************)
Datatype:
   xnum = INFINITY                            (* length of an infinite path  *)
        | XNUM of num                         (* length of a finite path     *)
End

(******************************************************************************
* The constant ``to`` is a left associative infix with precedence 500.
* It is overloaded so that
* (m to n) i        means m <= i /\ i < n  (num_to_def)
* (m to XNUM n) i   means m <= i /\ i < n  (xnum_to_def)
* (m to INFINITY) i means m <= i           (xnum_to_def)
******************************************************************************)
Definition num_to_def:
  $num_to m n i = m <= i /\ i < n
End

Definition xnum_to_def:
   ($xnum_to m (XNUM n) i = m <= i /\ i < n)
   /\
   ($xnum_to m INFINITY i = m <= i)
End

val _ = overload_on("to", ``num_to``);
val _ = overload_on("to", ``xnum_to``);

val _ = set_fixity "to" (Infixl 500);

(******************************************************************************
* Extend subtraction (-) to extended numbers
******************************************************************************)
Definition SUB_num_xnum_def:
   $SUB_num_xnum (m:num) (XNUM (n:num)) = XNUM((m:num) - (n:num))
End

Definition SUB_xnum_num_def:
  $SUB_xnum_num (XNUM (m:num)) (n:num) = XNUM((m:num) - (n:num))
End

Definition SUB_xnum_xnum_def:
   ($SUB_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = XNUM((m:num) - (n:num)))
   /\
   ($SUB_xnum_xnum INFINITY (XNUM (n:num)) = INFINITY)
End

val SUB =
 save_thm
  ("SUB",
   LIST_CONJ(type_rws ``:xnum`` @
             [SUB_num_xnum_def,SUB_xnum_num_def,SUB_xnum_xnum_def]));

val _ = overload_on("-", ``SUB_num_xnum``);
val _ = overload_on("-", ``SUB_xnum_num``);
val _ = overload_on("-", ``SUB_xnum_xnum``);

(******************************************************************************
* Extend less-than predicate (<) to extended numbers
******************************************************************************)
Definition LS_num_xnum_def:
   ($LS_num_xnum (m:num) (XNUM (n:num)) = (m:num) < (n:num))
   /\
   ($LS_num_xnum (m:num) INFINITY = T)
End

Definition LS_xnum_num_def:
   ($LS_xnum_num (XNUM (m:num)) (n:num) = (m:num) < (n:num))
   /\
   ($LS_xnum_num INFINITY (n:num) = F)
End

Definition LS_xnum_xnum_def:
  $LS_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) < (n:num)
End

val LS =
 save_thm("LS",LIST_CONJ[LS_num_xnum_def,LS_xnum_num_def,LS_xnum_xnum_def]);

val _ = overload_on("<", ``LS_num_xnum``);
val _ = overload_on("<", ``LS_xnum_num``);
val _ = overload_on("<", ``LS_xnum_xnum``);

(******************************************************************************
* Extend greater-than predicate (>) to extended numbers
******************************************************************************)
Definition GT_num_xnum_def:
  $GT_num_xnum (m:num) (XNUM (n:num)) = (m:num) > (n:num)
End

Definition GT_num_xnum_def:
   ($GT_num_xnum (m:num) (XNUM (n:num)) = (m:num) > (n:num))
   /\
   ($GT_num_xnum (m:num) INFINITY = F)
End

Definition GT_xnum_num_def:
   ($GT_xnum_num (XNUM (m:num)) (n:num) = (m:num) > (n:num))
   /\
   ($GT_xnum_num INFINITY (n:num) = T)
End

Definition GT_xnum_xnum_def:
  $GT_xnum_xnum (XNUM (m:num)) (XNUM (n:num)) = (m:num) > (n:num)
End

val GT =
 save_thm("GT",LIST_CONJ[GT_num_xnum_def,GT_xnum_num_def,GT_xnum_xnum_def]);

val _ = overload_on(">", ``GT_num_xnum``);
val _ = overload_on(">", ``GT_xnum_num``);
val _ = overload_on(">", ``GT_xnum_xnum``);

(******************************************************************************
* PLENGTH(FINITE l)   = XNUM(LENGTH l)
* PLENGTH(INFINITE l) = INFINITY
******************************************************************************)
Definition PLENGTH_def:
  (PLENGTH(FINITE l)   = XNUM(list$LENGTH l))
         /\
         (PLENGTH(INFINITE p) = INFINITY)
End

(*val PATH_LENGTH = save_thm("PATH_LENGTH",LENGTH_def);*)

val ALL_IN_INF = save_thm("ALL_IN_INF",prove(``!j. j IN 0 to INFINITY``, SIMP_TAC arith_ss [IN_DEF,xnum_to_def]));

(******************************************************************************
* PATH M p is true iff p is a path with respect to transition relation M.R
******************************************************************************)
Definition PATH_def:   PATH M p s = IS_INFINITE p /\ (ELEM p 0 = s) /\ (!n. M.R(ELEM p n, ELEM p (n+1)))
End

val PATH_INF = save_thm("PATH_INF",prove(``!M p s. PATH M p s ==> (PLENGTH p = INFINITY)``,
Induct_on `p` THEN
SIMP_TAC std_ss [IS_FINITE_def,PATH_def,IS_INFINITE_def,PLENGTH_def]));

val ALL_IN_INF_PATH = save_thm("ALL_IN_INF_PATH",prove(``!M p s j. PATH M p s ==> j IN 0 to PLENGTH p``,
Induct_on `p`
THENL [
 SIMP_TAC arith_ss [PATH_def,IS_INFINITE_def],
 SIMP_TAC std_ss [ALL_IN_INF,PLENGTH_def]
]));

(******************************************************************************
* C_SEM M s f means "M, s |= f"
* The mutual recursion is not necessary here, but makes fCTL defs easier
******************************************************************************)
val csem_eqns as [CEG_def, CEU_def, CEX_def,C_SEM_def_aux] =
 TotalDefn.multiDefine
  `(C_SEM M (C_BOOL b) s = B_SEM (M.L s) b) /\
   (C_SEM M (C_NOT f) s = ~(C_SEM M f s)) /\
   (C_SEM M (C_AND(f1,f2)) s = C_SEM M f1 s /\ C_SEM M f2 s) /\
   (C_SEM M (C_EX f) s = CEX M (C_SEM M f) s) /\
   (C_SEM M (C_EU(f1,f2)) s = CEU M (C_SEM M f1, C_SEM M f2) s) /\
   (C_SEM M (C_EG f) s = CEG M (C_SEM M f) s) /\
   (CEX M X s = ?p. PATH M p s /\ (ELEM p 1) IN X) /\
   (CEU M (X1,X2) s = ?p. PATH M p s /\ ?k :: (0 to PLENGTH p). (ELEM p k) IN X2 /\ !j. j < k ==> (ELEM p j) IN X1) /\
   (CEG M X s = ?p. PATH M p s /\ !j :: (0 to PLENGTH p). (ELEM p j) IN X)
`;

val C_SEM_def = save_thm("C_SEM_def",LIST_CONJ csem_eqns);

Definition CTL_MODEL_SAT_def:   CTL_MODEL_SAT M f = (!s. s IN M.S0 ==> C_SEM M f s)
End

Definition C_AX_def:   C_AX (f: 'prop ctl) = C_NOT (C_EX (C_NOT f))
End
Definition C_EF_def:   C_EF (f: 'prop ctl) = C_EU(C_BOOL B_TRUE,f)
End
Definition C_AF_def:   C_AF (f: 'prop ctl) = C_NOT(C_EG (C_NOT f))
End
Definition C_AG_def:   C_AG (f: 'prop ctl) = C_NOT (C_EF (C_NOT f))
End
Definition C_AU_def:   C_AU ((f1: 'prop ctl),(f2: 'prop ctl)) = C_AND(C_NOT(C_EU(C_NOT f2,C_AND(C_NOT f1,C_NOT f2))),C_NOT(C_EG(C_NOT f2)))
End
Definition C_AR_def:   C_AR(f,g) = C_NOT (C_EU (C_NOT f,C_NOT g))
End
Definition C_OR_def:   C_OR((f1: 'prop ctl),(f2: 'prop ctl)) = C_NOT(C_AND(C_NOT f1, C_NOT f2))
End
Definition C_IMP_def:   C_IMP((f: 'prop ctl),(g: 'prop ctl)) = C_OR(C_NOT f,g)
End
Definition C_IFF_def:   C_IFF (f: 'prop ctl) (g: 'prop ctl) = C_AND(C_IMP(f,g),C_IMP(g,f))
End
Definition B_IMP_def:   B_IMP((f: 'a bexp),(g: 'a bexp)) = B_OR(B_NOT f,g)
End
Definition B_IFF_def:   B_IFF (f: 'a bexp) (g: 'a bexp) = B_AND(B_IMP(f,g),B_IMP(g,f))
End
Definition B_AND2_def:   B_AND2 (f: 'a bexp) (g: 'a bexp) = B_AND(f,g)
End
Definition B_OR2_def:   B_OR2 (f: 'a bexp) (g: 'a bexp) = B_OR(f,g)
End
Definition C_AND2_def:   C_AND2 (f: 'prop ctl) (g: 'prop ctl) = C_AND(f,g)
End
Definition C_OR2_def:   C_OR2 (f: 'prop ctl) (g: 'prop ctl) = C_OR(f,g)
End
Definition C_IMP2_def:   C_IMP2 (f: 'prop ctl) (g: 'prop ctl) = C_IMP(f,g)
End
Definition B_IMP2_def:   B_IMP2 (f: 'a bexp) (g: 'a bexp) = B_IMP(f,g)
End

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

(* FIXME: these NNF defs are not right because they do not move all negs inwards to atoms (because OR is defined in terms of AND, etc)*)
Definition BEXP_NNF:
(BEXP_NNF B_TRUE                = B_TRUE) /\
(BEXP_NNF (B_PROP p)            = B_PROP p) /\
(BEXP_NNF (B_AND(b1,b2))        = B_AND(BEXP_NNF b1,BEXP_NNF b2)) /\
(BEXP_NNF (B_NOT B_TRUE)        = B_FALSE) /\
(BEXP_NNF (B_NOT (B_PROP p))    = B_NOT (B_PROP p)) /\
(BEXP_NNF (B_NOT (B_NOT b))     = BEXP_NNF b) /\
(BEXP_NNF (B_NOT (B_AND(b1,b2)))= B_OR(BEXP_NNF (B_NOT b1),BEXP_NNF (B_NOT b2)))
End

Definition CTL_NNF:
(CTL_NNF (C_BOOL b) = C_BOOL b) /\
(CTL_NNF (C_AND(f,g))  = C_AND(CTL_NNF f,CTL_NNF g)) /\
(CTL_NNF (C_EX f)  = C_EX (CTL_NNF f)) /\
(CTL_NNF (C_EG f)  = C_EG (CTL_NNF f)) /\
(CTL_NNF (C_EU(f,g))  = C_EU (CTL_NNF f,CTL_NNF g)) /\
(CTL_NNF (C_NOT (C_BOOL b)) = (C_BOOL (BEXP_NNF (B_NOT b)))) /\
(CTL_NNF (C_NOT (C_AND(f,g))) = (C_OR(CTL_NNF(C_NOT f),CTL_NNF(C_NOT g)))) /\
(CTL_NNF (C_NOT (C_NOT f)) = CTL_NNF f) /\
(CTL_NNF (C_NOT (C_EX f)) = (C_AX (CTL_NNF (C_NOT f)))) /\
(CTL_NNF (C_NOT (C_EG f)) = (C_AF (CTL_NNF (C_NOT f)))) /\
(CTL_NNF (C_NOT (C_EU(f,g))) = (C_AR(CTL_NNF (C_NOT f),CTL_NNF (C_NOT g))))
End

val ctl_size_def = snd (TypeBase.size_of ``:'a ctl``)
Definition ctl_size2_def:   ctl_size2 (f: 'prop ctl) =  ctl_size (\(a:('prop)).0) f
End
val bexp_size_def = snd (TypeBase.size_of ``:'a bexp``);
Definition bexp_size2_def:   bexp_size2 (b: 'prop bexp) =  bexp_size (\(a:('prop)).0) b
End

Definition bexp_pstv_size:
(bexp_pstv_size B_TRUE                = 0) /\
(bexp_pstv_size (B_PROP p)            = 1) /\
(bexp_pstv_size (B_AND(b1,b2))        = 1+(bexp_pstv_size b1)+(bexp_pstv_size b2)) /\
(bexp_pstv_size (B_NOT b)             = (bexp_pstv_size b))
End

Definition ctl_pstv_size:
(ctl_pstv_size (C_BOOL b) = 1+(bexp_pstv_size b)) /\
(ctl_pstv_size (C_AND(f1,f2)) = 1+(ctl_pstv_size f1) + (ctl_pstv_size f2)) /\
(ctl_pstv_size (C_NOT f) = (ctl_pstv_size f)) /\
(ctl_pstv_size (C_EX f) = 1+(ctl_pstv_size f)) /\
(ctl_pstv_size (C_EG f) = 1+(ctl_pstv_size f)) /\
(ctl_pstv_size (C_EU(f1,f2)) =1+(ctl_pstv_size f1) + (ctl_pstv_size f2))
End

(*val cdefn = Defn.Hol_defn "CTL_NNF" `
(CTL_NNF (C_BOOL b) = C_BOOL b) /\
(CTL_NNF (C_AND(f,g))  = C_AND(CTL_NNF f,CTL_NNF g)) /\
(CTL_NNF (C_EX f)  = C_EX (CTL_NNF f)) /\
(CTL_NNF (C_EG f)  = C_EG (CTL_NNF f)) /\
(CTL_NNF (C_EU(f,g))  = C_EU (CTL_NNF f,CTL_NNF g)) /\
(CTL_NNF (C_NOT (C_BOOL b)) = (C_BOOL (BEXP_NNF (B_NOT b)))) /\
(CTL_NNF (C_NOT (C_AND(f,g))) = (C_OR(CTL_NNF(C_NOT f),CTL_NNF(C_NOT g)))) /\
(CTL_NNF (C_NOT (C_NOT f)) = CTL_NNF f) /\
(CTL_NNF (C_NOT (C_EX f)) = (C_AX (CTL_NNF (C_NOT f)))) /\
(CTL_NNF (C_NOT (C_EG f)) = (C_AF (CTL_NNF (C_NOT f)))) /\
(CTL_NNF (C_NOT (C_EU(f,g))) = (C_AR(CTL_NNF (C_NOT f),CTL_NNF (C_NOT g))))`;

val (CTL_NNF_def,CTL_NNF_ind) = Defn.tprove(cdefn,
 WF_REL_TAC `measure ctl_pstv_size`
 THEN REPEAT (FIRST [Induct_on `f`,Induct_on `g`,Induct_on `b`])
 THEN FULL_SIMP_TAC arith_ss [ctl_pstv_size,bexp_pstv_size,C_AX_def,C_AR_def,C_AF_def,BEXP_NNF,B_OR_def,B_FALSE_def]*)

Definition CTL_BOOL_SUB:
(CTL_BOOL_SUB g (B_PROP (b:'prop)) = (g = B_PROP b)) /\
(CTL_BOOL_SUB g (B_NOT be1) = (CTL_BOOL_SUB g be1) \/ (g = B_NOT be1)) /\
(CTL_BOOL_SUB g (B_AND(be1,be2)) = (CTL_BOOL_SUB g be1) \/ (CTL_BOOL_SUB g be2) \/ (g = B_AND(be1,be2)))
End

Definition CTL_SUB:
(CTL_SUB g (C_BOOL b) = ?b'. (g = C_BOOL b') /\ CTL_BOOL_SUB b' b) /\
(CTL_SUB g (C_AND(f1,f2)) = (CTL_SUB g f1) \/ (CTL_SUB g f2) \/ (g = C_AND(f1,f2))) /\
(CTL_SUB g (C_NOT f) = (CTL_SUB g f) \/ (g=C_NOT f)) /\
(CTL_SUB g (C_EX f) = (CTL_SUB g f) \/ (g=C_EX f)) /\
(CTL_SUB g (C_EG f) = (CTL_SUB g f) \/ (g=C_EG f)) /\
(CTL_SUB g (C_EU(f1,f2)) = (CTL_SUB g f1) \/ (CTL_SUB g f2) \/ (g=C_EU(f1,f2)))
End

Definition IS_ACTL:   IS_ACTL f = (!g. ~CTL_SUB (C_EX g) (CTL_NNF f)) /\ (!g. ~CTL_SUB (C_EG g) (CTL_NNF f)) /\ (!g1 g2. ~CTL_SUB (C_EU(g1,g2)) (CTL_NNF f))
End

val CTL_NNF_ID = save_thm("CTL_NNF_ID",prove(``!f M. C_SEM M (CTL_NNF f) = C_SEM M f``,
REWRITE_TAC [FUN_EQ_THM]
THEN recInduct (theorem "CTL_NNF_ind") THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss [CTL_NNF]
THEN REWRITE_TAC [FUN_EQ_THM,C_AR_def,C_AX_def,C_AF_def,C_OR_def]  THEN SIMP_TAC std_ss [C_SEM_def]
THEN recInduct (theorem "BEXP_NNF_ind") THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss [BEXP_NNF]
THEN REWRITE_TAC [FUN_EQ_THM,B_FALSE_def,B_OR_def] THEN SIMP_TAC std_ss [B_SEM_def]
));

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

val REST_FINITE =
 store_thm
  ("REST_FINITE",
   ``!l. REST (FINITE l) = FINITE(TL l)``,
   RW_TAC list_ss [REST_def]);
