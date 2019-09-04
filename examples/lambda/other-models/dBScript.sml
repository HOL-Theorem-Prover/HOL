(*---------------------------------------------------------------------------
                    Five Axioms of Alpha Conversion
                      (Andy Gordon & Tom Melham)


                        Part I: deBruijn terms

 ---------------------------------------------------------------------------*)

(* Interactive use:
   app load ["bossLib", "Q", "pred_setTheory", "stringTheory"];
*)

open HolKernel Parse boolLib
     bossLib numLib IndDefLib
     pred_setTheory arithmeticTheory
     basic_swapTheory

val _ = new_theory"dB";


(*---------------------------------------------------------------------------
            Support bumpf.
 ---------------------------------------------------------------------------*)

val FUN_EQ_TAC = CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
                   THEN GEN_TAC THEN BETA_TAC;

val MAX_00 = Q.prove(
  `!m n. (MAX m n = 0) ⇔ (m=0) /\ (n=0)`,  RW_TAC arith_ss [MAX_DEF]);

val MAX_LESS_EQ = Q.prove(
  `!m n p. MAX m n <= p ⇔ m <= p /\ n <= p`,  RW_TAC arith_ss [MAX_DEF]);


val UNION_DELETE = Q.store_thm("UNION_DELETE",
 `!s t x. (s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)`,
ZAP_TAC
   (std_ss && [EXTENSION,IN_UNION,IN_DELETE]) []);

val UNION_SUBSET = Q.prove(
 `!X Y Z. (X UNION Y) SUBSET Z ⇔ X SUBSET Z /\ Y SUBSET Z`,
PROVE_TAC
   [SUBSET_DEF, IN_UNION]);

val GSPEC_DEF = Q.prove
(`!f. GSPEC f = \v. ?z. f z = (v,T)`,
 FUN_EQ_TAC
  THEN ONCE_REWRITE_TAC
        [BETA_RULE (ONCE_REWRITE_CONV
            [GSYM SPECIFICATION](Term`(\x. GSPEC f x) x`))]
  THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)
  THEN PROVE_TAC [GSPECIFICATION]);

(* ===================================================================== *)
(* PART I: A type of de Bruijn terms.                                    *)
(* ===================================================================== *)

val _ = Hol_datatype
           `dB = dCON   of 'a
               | dVAR   of string
               | dBOUND of num
               | dABS   of dB
               | dAPP   of dB => dB`;


(* --------------------------------------------------------------------- *)
(* Free variables.                                                       *)
(* --------------------------------------------------------------------- *)

val dFV =
 Define
    `(dFV (dCON c)   = {})
 /\  (dFV (dVAR x)   = {x})
 /\  (dFV (dBOUND n) = {})
 /\  (dFV (dABS t)   = dFV t)
 /\  (dFV (dAPP t u) = (dFV t) UNION (dFV u))`;


val FINITE_dFV = Q.store_thm("FINITE_dFV", `!t. FINITE (dFV t)`,
Induct THEN RW_TAC std_ss [dFV, FINITE_UNION, FINITE_EMPTY, FINITE_SING]);

val FRESH_VAR = Q.store_thm("FRESH_VAR", `!t. ?x. ~(x IN dFV t)`,
                            PROVE_TAC [new_exists, SPEC_ALL FINITE_dFV]);

(* --------------------------------------------------------------------- *)
(* Functions defined by recursion on de Bruijn terms.                    *)
(* --------------------------------------------------------------------- *)

val dDEG =
 Define
    `(dDEG (dCON c)   = 0)
 /\  (dDEG (dVAR x)   = 0)
 /\  (dDEG (dBOUND n) = SUC n)
 /\  (dDEG (dABS t)   = dDEG t - 1)
 /\  (dDEG (dAPP t u) = MAX (dDEG t) (dDEG u))`;


val Abst =
 Define
    `(Abst i x (dCON c)   = dCON c)
 /\  (Abst i x (dVAR y)   = if x=y then dBOUND i else dVAR y)
 /\  (Abst i x (dBOUND j) = dBOUND j)
 /\  (Abst i x (dABS t)   = dABS (Abst (SUC i) x t))
 /\  (Abst i x (dAPP t u) = dAPP (Abst i x t) (Abst i x u))`;

val Inst =
 Define
    `(Inst i (dCON c) u     = dCON c)
 /\  (Inst i (dVAR x) u     = dVAR x)
 /\  (Inst i (dBOUND j) u   = if i=j then u else dBOUND j)
 /\  (Inst i (dABS t) u     = dABS (Inst (SUC i) t u))
 /\  (Inst i (dAPP t1 t2) u = dAPP (Inst i t1 u) (Inst i t2 u))`;


val dFV_Abst = Q.store_thm("dFV_Abst",
`!t i x. ~(x IN dFV t) ==> (Abst i x t = t)`,
Induct
  THEN RW_TAC std_ss [Abst, dFV, IN_UNION, IN_SING]);

val dDEG_Abst = Q.store_thm("dDEG_Abst",
`!t x i. dDEG t <= i ==> dDEG (Abst i x t) <= (SUC i)`,
Induct
  THEN RW_TAC arith_ss [dDEG, Abst, MAX_LESS_EQ, GSYM ADD1]);


val dDEG_Inst = Q.store_thm("dDEG_Inst",
`!t i x. dDEG t <= SUC i ==> dDEG (Inst i t (dVAR x)) <= i`,
Induct
  THEN RW_TAC arith_ss [Inst, dDEG, MAX_LESS_EQ, GSYM ADD1]);


val dDEG_Inst_Abst = Q.store_thm("dDEG_Inst_Abst",
`!t i x. dDEG t <= i ==> (Inst i (Abst i x t) (dVAR x) = t)`,
Induct
  THEN RW_TAC arith_ss [Inst, Abst, dDEG, MAX_LESS_EQ]);


val dDEG_Abst_Inst = Q.store_thm("dDEG_Abst_Inst",
`!t i x.
   ~(x IN dFV t) /\ dDEG t <= SUC i ==> (Abst i x (Inst i t (dVAR x)) = t)`,
Induct
   THEN RW_TAC arith_ss
         [Inst, Abst, dFV, dDEG, MAX_LESS_EQ, IN_UNION, IN_SING]);

val Rename = Q.store_thm("Rename",
`!t i x y.
   ~(y IN (dFV t)) /\ dDEG t <= i
     ==>
     (Abst i x t = Abst i y (Inst i (Abst i x t) (dVAR y)))`,
Induct
  THEN ZAP_TAC (arith_ss &&
     [Inst, Abst, dFV, dDEG, IN_UNION, MAX_LESS_EQ, IN_SING, GSYM ADD1]) []);


(* --------------------------------------------------------------------- *)
(* Lambda-abstraction.                                                   *)
(* --------------------------------------------------------------------- *)

val dLAMBDA = Define `dLAMBDA x t = dABS(Abst 0 x t)`;

val dFV_dLAMBDA_lemma = Q.store_thm("dFV_dLAMBDA_lemma",
`!t i x. dFV (Abst i x t) = (dFV t) DELETE x`,
Induct
   THEN ZAP_TAC (std_ss && [Abst,dFV,UNION_DELETE,EMPTY_DELETE,SING_DELETE])
                [DELETE_NON_ELEMENT, IN_SING]);

val dFV_dLAMBDA = Q.store_thm("dFV_dLAMBDA",
`!t x. dFV (dLAMBDA x t) = (dFV t) DELETE x`,
RW_TAC std_ss [dFV, dLAMBDA, dFV_dLAMBDA_lemma]);


(* --------------------------------------------------------------------- *)
(* Inductive definition of proper terms.                                 *)
(* --------------------------------------------------------------------- *)

val (dOK_DEF, dOK_ind, dOK_cases) = Hol_reln
  `(!x. dOK (dVAR x)) /\
   (!x. dOK (dCON x)) /\
   (!x t. dOK t ==> dOK (dLAMBDA x t)) /\
   (!t u. dOK t /\ dOK u ==> dOK (dAPP t u))`;

val _ = save_thm("dOK_DEF", dOK_DEF);
val _ = save_thm("dOK_ind",   dOK_ind);


(* --------------------------------------------------------------------- *)
(* Proof of |- !t. dOK t = (dDEG t = 0)                                  *)
(* --------------------------------------------------------------------- *)

val Forwards = Q.store_thm("Forwards",
  `!t. dOK t ==> (dDEG t = 0)`,
  HO_MATCH_MP_TAC dOK_ind THEN
  RW_TAC bool_ss [ONE, dDEG, MAX_00, dLAMBDA,SUB_EQ_0] THEN
  MATCH_MP_TAC dDEG_Abst THEN ASM_SIMP_TAC arith_ss []);


val dWT =
 Define
    `(dWT (dCON c)   = 0)
 /\  (dWT (dVAR x)   = 0)
 /\  (dWT (dBOUND n) = 0)
 /\  (dWT (dABS t)   = SUC (dWT t))
 /\  (dWT (dAPP t u) = SUC (dWT t + dWT u))`;

val dWT_Inst = Q.store_thm("dWT_Inst",
 `!t i x. dWT (Inst i t (dVAR x)) = dWT t`,
Induct
   THEN RW_TAC arith_ss [dWT, Inst]);

val dDEG_dABS_dLAMBDA = Q.store_thm("dDEG_dABS_dLAMBDA",
`!t. (dDEG t <= 1) ==>
     ?x u.
       (dABS t = dLAMBDA x u) /\
         dWT u < dWT (dABS t) /\
       (dDEG u = 0)`,
RW_TAC arith_ss [dLAMBDA]
  THEN Q.X_CHOOSE_TAC `x` (Q.SPEC `t:'a dB` FRESH_VAR)
  THEN ID_EX_TAC THEN Q.EXISTS_TAC `Inst 0 t (dVAR x)`
  THEN RW_TAC arith_ss [dWT,dWT_Inst,dDEG_Inst,dDEG_Abst_Inst,GSYM LESS_EQ_0]);

val Backwards = Q.store_thm("Backwards",
`!n t. (dDEG t = 0) /\ (dWT t = n) ==> dOK t`,
completeInduct_on `n` THEN Cases
  THEN ONCE_REWRITE_TAC [dOK_cases]
  THEN ZAP_TAC (arith_ss && [dDEG,dWT,MAX_00]) [dDEG_dABS_dLAMBDA,dWT]);

val dDEG_dOK = Q.store_thm("dDEG_dOK", `!t. dOK t = (dDEG t = 0)`,
PROVE_TAC [Forwards,Backwards]);


(* --------------------------------------------------------------------- *)
(* Substitution.                                                         *)
(* --------------------------------------------------------------------- *)

val dSUB = Define `dSUB x u t = Inst 0 (Abst 0 x t) u`;

val _ = add_rule {term_name = "dSUB", fixity = Parse.Closefix,
                  pp_elements = [TOK "[", TM, HardSpace 1, TOK "|->",
                                 BreakSpace(1,0), TM, TOK "]"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.CONSISTENT, 2))};


(* --------------------------------------------------------------------- *)
(* Substitution preserves propriety.                                     *)
(* --------------------------------------------------------------------- *)

val dOK_dSUB_lemma = Q.store_thm("dOK_dSUB_lemma",
`!t u i j x.
   dDEG t <= i /\ dDEG u <= j ==> dDEG (Inst i (Abst i x t) u) <= i+j`,
Induct
   THEN ZAP_TAC (arith_ss && [Inst, Abst, dDEG, MAX_LESS_EQ, GSYM ADD1])
                [ADD_CLAUSES]);

val dOK_dSUB = Q.store_thm("dOK_dSUB",
 `!t u x. dOK t /\ dOK u ==> dOK ([x |-> u] t)`,
ZAP_TAC (arith_ss && [dDEG_dOK, dSUB])
     [DECIDE (Term `(x=0) ⇔ x <= 0`), dOK_dSUB_lemma, ADD_CLAUSES]);


(* --------------------------------------------------------------------- *)
(* Distributive laws for substitution.                                   *)
(* --------------------------------------------------------------------- *)

val EQ_dVAR_dSUB = Q.store_thm("EQ_dVAR_dSUB",
 `!u x. [x |-> u] (dVAR x) = u`,
RW_TAC arith_ss [dSUB, Inst, Abst]);

val NEQ_dVAR_dSUB = Q.store_thm("NEQ_dVAR_dSUB",
 `!u x y. ~(x=y) ==> ([x |-> u] (dVAR y) = dVAR y)`,
RW_TAC arith_ss  [dSUB, Inst, Abst]);

val dCON_dSUB = Q.store_thm("dCON_dSUB",
  `!x t c. [x |-> t] (dCON c) = dCON c`,
RW_TAC arith_ss  [dSUB, Inst, Abst]);

val dAPP_dSUB = Q.store_thm("dAPP_dSUB",
`!x M t u. [x |-> M] (dAPP t u) = dAPP ([x |-> M] t) ([x |-> M] u)`,
RW_TAC arith_ss [Inst, Abst, dSUB]);

val dLAMBDA_dSUB_lemma = Q.store_thm("dLAMBDA_dSUB_lemma",
`!t u i x y.
   ~(x=y) /\ ~(y IN dFV u) /\ dDEG t <= i
    ==>
      (Inst (SUC i) (Abst (SUC i) x (Abst i y t)) u =
       Abst i y (Inst i (Abst i x t) u))`,
Induct
  THEN RW_TAC arith_ss [Inst, Abst, dFV_Abst, dDEG, MAX_LESS_EQ]);

val dLAMBDA_dSUB = Q.store_thm("dLAMBDA_dSUB",
  `!t u x y.
      ~(x=y) /\ ~(y IN dFV u) /\ dOK t ==>
      ([x |-> u] (dLAMBDA y t) = dLAMBDA y ([x |-> u] t))`,
  SIMP_TAC (srw_ss()) [dLAMBDA, dSUB, Abst, Inst, dDEG_dOK] THEN
  SIMP_TAC (bool_ss ++ ARITH_ss) [ONE, dLAMBDA_dSUB_lemma]);

val dLAMBDA_dSUB_EQ_lemma = Q.store_thm("dLAMBDA_dSUB_EQ_lemma",
`!t u x i.
   dDEG t <= SUC i ==>
       (Inst (SUC i) (Abst (SUC i) x (Abst i x t)) u = Abst i x t)`,
Induct
   THEN RW_TAC arith_ss [Abst, Inst, dDEG, MAX_LESS_EQ]);

val dLAMBDA_dSUB_EQ = Q.store_thm("dLAMBDA_dSUB_EQ",
  `!t u x.
      dOK t ==> ([x |-> u] (dLAMBDA x t) = dLAMBDA x t)`,
  RW_TAC bool_ss [dDEG_dOK, dLAMBDA, dSUB, Abst, Inst, DECIDE ``0 <= SUC x``,
                  dLAMBDA_dSUB_EQ_lemma]);

val dSUB_ID_lemma = Q.store_thm("dSUB_ID_lemma",
`!t i x. dDEG t <= i ==> (Inst i (Abst i x t) (dVAR x) = t)`,
Induct THEN RW_TAC arith_ss [Inst, Abst, dDEG, MAX_LESS_EQ]);

val dSUB_ID = Q.store_thm("dSUB_ID",
`!t x. dOK t ==> ([x |-> dVAR x]t = t)`,
RW_TAC arith_ss [dDEG_dOK, dSUB, dSUB_ID_lemma]);


(* --------------------------------------------------------------------- *)
(* Alpha-conversion.                                                     *)
(* --------------------------------------------------------------------- *)

val dALPHA = Q.store_thm("dALPHA",
`!t x y.
    ~(y IN dFV t) /\ dOK t
       ==>
    (dLAMBDA x t = dLAMBDA y ([x |-> dVAR y] t))`,
ZAP_TAC (arith_ss && [dDEG_dOK, dLAMBDA, dSUB])
  [Rename,LESS_EQ_REFL]);

val dALPHA_STRONG = Q.store_thm("dALPHA_STRONG",
 `!t x y.
      ~(y IN dFV (dLAMBDA x t)) /\ dOK t
        ==>
      (dLAMBDA x t = dLAMBDA y ([x |-> dVAR y] t))`,
ZAP_TAC (arith_ss && [dFV_dLAMBDA,IN_DELETE])
  [dALPHA,dSUB_ID]);

(* --------------------------------------------------------------------- *)
(* Beta-conversion.                                                      *)
(* --------------------------------------------------------------------- *)

val dBETA =
 Define
    `dBETA (dABS u) t = Inst 0 u t`;

val dBETA_THM = Q.store_thm("dBETA_THM",
 `!t u x. dBETA (dLAMBDA x t) u = [x |-> u] t`,
RW_TAC arith_ss [dBETA, dLAMBDA, dSUB]);

(* --------------------------------------------------------------------- *)
(* The length of a term: the number of occurrences of atoms.             *)
(* --------------------------------------------------------------------- *)

val dLGH =
 Define
     `(dLGH (dCON c)   = 1)
  /\  (dLGH (dVAR x)   = 1)
  /\  (dLGH (dBOUND n) = 1)
  /\  (dLGH (dABS t)   = 1 + dLGH t)
  /\  (dLGH (dAPP t u) = dLGH t + dLGH u)`;

val dLGH_dSUB = Q.store_thm("dLGH_dSUB",
`!t x y. dLGH([y |-> dVAR x]t) = dLGH t`,
RW_TAC arith_ss [dSUB] THEN
 `!t i x y. dLGH (Inst i (Abst i y t) (dVAR x)) = dLGH t`
  suffices_by simp[] THEN
Induct THEN RW_TAC arith_ss [Inst,Abst,dLGH]);

val dLGH_Abst = Q.store_thm("dLGH_Abst",
`!t x i. dLGH(Abst i x t) = dLGH t`,
Induct THEN RW_TAC arith_ss [Abst, dLGH]);

val dLGH_NOT_ZERO = Q.store_thm("dLGH_NOT_ZERO",
`!t. ~(dLGH t = 0)`,
Induct THEN RW_TAC arith_ss [dLGH]);

val dLGH_dAPP_LESS_1 = Q.store_thm("dLGH_dAPP_LESS_1",
`!t u. dLGH u < dLGH (dAPP t u)`,
RW_TAC arith_ss  [dLGH]
  THEN MP_TAC (SPEC_ALL dLGH_NOT_ZERO)
  THEN RW_TAC arith_ss []);

val dLGH_dAPP_LESS_2 = Q.store_thm("dLGH_dAPP_LESS_2",
`!t u. dLGH t < dLGH (dAPP t u)`,
RW_TAC arith_ss  [dLGH]
  THEN MP_TAC (Q.SPEC`u` dLGH_NOT_ZERO)
  THEN RW_TAC arith_ss []);

val dLGH_dLAMBDA_LESS = Q.store_thm("dLGH_dLAMBDA_LESS",
`!t x. dLGH t < dLGH (dLAMBDA x t)`,
RW_TAC arith_ss [dLAMBDA, dLGH, dLGH_Abst]);

val NTH =
 Define
    `(NTH 0 (h::t)       = h)
 /\  (NTH (SUC n) (h::t) = NTH n t)`;


(* --------------------------------------------------------------------- *)
(* Initiality.........                                                   *)
(* --------------------------------------------------------------------- *)

val CHOM =
 Define
    `(CHOM con var abs app xs (dCON c)   = (con:'a ->'b) c)
 /\  (CHOM con var abs app xs (dVAR x)   = var x)
 /\  (CHOM con var abs app xs (dBOUND n) =
        if n < LENGTH xs then var (NTH n xs) else ARB)
 /\  (CHOM con var abs app xs (dABS t) =
       abs (\x. CHOM con var abs app (x::xs) t))
 /\  (CHOM con var abs app xs (dAPP t u) =
         app (CHOM con var abs app xs t) (CHOM con var abs app xs u))`;

val HOM =
 Define
    `HOM (con:'a ->'b) var abs app = CHOM con var abs app []`;

val hom  = Term`HOM  (con:'a ->'b) var abs app`;
val chom = Term`CHOM (con:'a ->'b) var abs app`;

(*---------------------------------------------------------------------------
    Parallel substitution
 ---------------------------------------------------------------------------*)

val PSUB =
 Define
    `(PSUB d xs (dCON c)   = dCON c)
 /\  (PSUB d xs (dVAR x)   = dVAR x)
 /\  (PSUB d xs (dBOUND n) = if d <= n /\ n < d + LENGTH xs
                             then dVAR (NTH (n-d) xs) else dBOUND n)
 /\  (PSUB d xs (dABS t)   = dABS (PSUB (SUC d) xs t))
 /\  (PSUB d xs (dAPP t u) = dAPP (PSUB d xs t) (PSUB d xs u))`;

val SUB_ELIM_LEM = Q.prove(
`!x y. x < y ==> ?m. y-x = SUC m`,
RW_TAC arith_ss []
  THEN Q.EXISTS_TAC `PRE(y-x)`
  THEN RW_TAC arith_ss []);

val PSUB_Lemma0 = Q.store_thm("PSUB_Lemma0",
`!u d. PSUB d [] u = u`,
Induct THEN RW_TAC list_ss [PSUB]);

(* Awkward proof *)
val PSUB_Lemma1 = Q.store_thm("PSUB_Lemma1",
`!t d x xs. PSUB d (x::xs) t = Inst d (PSUB (SUC d) xs t) (dVAR x)`,
Induct
  THEN RW_TAC list_ss [Inst, PSUB] THENL
 [`d < n` by DECIDE_TAC THEN
  `?m. n-d = SUC m` by PROVE_TAC [SUB_ELIM_LEM]
    THEN ZAP_TAC (list_ss && [NTH])
          [DECIDE (Term `(n-d = SUC m) ==> (n-SUC d = m)`),NTH],
  `n - d = 0` by (REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC ARITH_CONV)
    THEN RW_TAC list_ss [NTH]]);


val PSUB_dCON = Q.store_thm("PSUB_dCON",
 `(PSUB 0 xs (dCON x) = PSUB 0 ys u) = (u = dCON x)`,
Cases_on `u`
  THEN ZAP_TAC (list_ss && [PSUB]) []);


val PSUB_dAPP = Q.store_thm("PSUB_dAPP",
 `(PSUB 0 xs (dAPP t1 t2) = PSUB 0 ys u)
     ==>
  ?u1 u2. u = dAPP u1 u2`,
Cases_on `u` THEN RW_TAC arith_ss [PSUB]);

val PSUB_dABS = Q.store_thm("PSUB_dABS",
 `(PSUB 0 xs (dABS t) = PSUB 0 ys u) ==> ?u1. u = dABS u1`,
Cases_on `u` THEN RW_TAC list_ss [PSUB]);

val PSUB_dVAR = Q.store_thm("PSUB_dVAR",
`(PSUB 0 xs (dVAR s) = PSUB 0 ys u)
  ==>
    ((u = dVAR s) \/
     ?n. (u = dBOUND n) /\ (n < LENGTH ys) /\ (NTH n ys = s))`,
Cases_on `u` THEN RW_TAC list_ss [PSUB]);

val PSUB_dBOUND = Q.store_thm("PSUB_dBOUND",
`(PSUB 0 xs (dBOUND n) = PSUB 0 ys u)
  ==>
     if n < LENGTH xs
     then (u = dVAR (NTH n xs)) \/
         ?m. m < LENGTH ys /\ (NTH n xs = NTH m ys) /\ (u = dBOUND m)
     else (u = dBOUND n) /\ ~(n < LENGTH ys)`,
Cases_on `u` THEN RW_TAC list_ss [PSUB]);

val PSUB_Lemma2 = Q.store_thm("PSUB_Lemma2",
`(PSUB (SUC 0) xs t = PSUB (SUC 0) ys u')
  ==>
   !x. (PSUB 0 (x::xs) t = PSUB 0 (x::ys) u')`,
PROVE_TAC [PSUB_Lemma1]);


val PSUB_Lemma3 = Q.store_thm("PSUB_Lemma3",
`!t xs u ys.
     (PSUB 0 xs t = PSUB 0 ys u)
       ==>
     (^chom xs t = ^chom ys u)`,
Induct THEN RW_TAC std_ss [] THENL
  map IMP_RES_TAC [PSUB_dCON, PSUB_dVAR, PSUB_dBOUND, PSUB_dABS, PSUB_dAPP]
  THEN BasicProvers.NORM_TAC std_ss [CHOM]
  THEN IMP_RES_TAC (PROVE [] (Term `x ==> ~x ==> F`))
  THEN Q.PAT_X_ASSUM `PSUB p q r = PSUB a b c` MP_TAC
  THEN RW_TAC std_ss [CHOM,PSUB]
  THENL [AP_TERM_TAC THEN PROVE_TAC[PSUB_Lemma2, ONE], PROVE_TAC []]);

val HOM_lemma = Q.store_thm("HOM_lemma",
  `(!x.   ^hom (dVAR x)   = var x) /\
   (!c.   ^hom (dCON c)   = con c) /\
   (!t u. ^hom (dAPP t u) = app (^hom t) (^hom u)) /\
   (!t.   ^hom (dABS t)   = abs (\x. ^hom (Inst 0 t (dVAR x))))`,
RW_TAC std_ss [HOM,CHOM]
  THEN AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV
  THEN RW_TAC arith_ss [PSUB_Lemma3,PSUB_Lemma0,PSUB_Lemma1]);


(* --------------------------------------------------------------------- *)
(* HOM is an iterator.                                                   *)
(* --------------------------------------------------------------------- *)

val HOM_THM = Q.store_thm("HOM_THM",
 `(!x.   ^hom (dVAR x)      = var x) /\
  (!c.   ^hom (dCON c)      = con c) /\
  (!t u. ^hom (dAPP t u)    = app (^hom t) (^hom u)) /\
  (!t x. ^hom (dLAMBDA x t) = abs (\y. ^hom ([x |-> dVAR y]t)))`,
RW_TAC std_ss [dLAMBDA, HOM_lemma, dSUB]);


(* ===================================================================== *)
(* HOM is the unique iterator.                                           *)
(* ===================================================================== *)

val UNIQUE_HOM = Q.store_thm("UNIQUE_HOM",
  `!f var con app abs.
      (!x. f (dVAR x) = var x) /\
      (!c. f (dCON c) = con c) /\
      (!t u. dOK t /\ dOK u ==> (f (dAPP t u) = app (f t) (f u))) /\
      (!t x.  dOK t ==> (f (dLAMBDA x t) = abs (\y. f ([x |-> dVAR y]t))))
      ==>
      !t. dOK t ==> (f t = ^hom t)`,
RW_TAC std_ss []
  THEN measureInduct_on `dLGH t`
  THEN ONCE_REWRITE_TAC [dOK_cases] THEN RW_TAC std_ss []
  THEN RW_TAC arith_ss [HOM_THM] THENL
  [AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN GEN_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[AND_IMP_INTRO]) THEN FIRST_ASSUM MATCH_MP_TAC
    THEN RW_TAC arith_ss [dLGH_dSUB,dLAMBDA,dLGH,dLGH_Abst,dOK_dSUB,dOK_DEF],
   RW_TAC arith_ss [dLGH_dAPP_LESS_1, dLGH_dAPP_LESS_2]]);


val UNIQUE_HOM_THM = Q.store_thm("UNIQUE_HOM_THM",
`!var con app lam (f:'a dB->'b) (g:'a dB->'b).
  (!x. f (dVAR x) = var x) /\
  (!c. f (dCON c) = con c) /\
  (!t u. (dOK t /\ dOK u) ==> (f (dAPP t u) = app (f t) (f u))) /\
  (!t x. dOK t ==> (f (dLAMBDA x t) = lam (\y. f ([x |-> dVAR y]t)))) /\
  (!x. g (dVAR x) = var x) /\
  (!c. g (dCON c) = con c) /\
  (!t u. (dOK t /\ dOK u) ==> (g (dAPP t u) = app (g t) (g u))) /\
  (!t x. dOK t ==> (g (dLAMBDA x t) = lam (\y. g ([x |-> dVAR y]t))))
  ==>
    !t. dOK t ==> (f t = g t)`,
REPEAT STRIP_TAC
  THEN IMP_RES_TAC UNIQUE_HOM THEN ASM_REWRITE_TAC[]);


(* --------------------------------------------------------------------- *)
(* Construct a model of the wrapping function.                           *)
(* --------------------------------------------------------------------- *)

val lemma1 = Q.prove(
`!f:'a->'b->bool.
   (!x. FINITE (f x)) ==> FINITE {z | !x. z IN (f x)}`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_FINITE_I THEN
Q.EXISTS_TAC `f a` THEN SRW_TAC [][SUBSET_DEF]);

val lemma2 = Q.prove(
`!u. dOK u
      ==>
       !x. FINITE {z | !y. z IN dFV ([x |-> dVAR y] u)}`,
REPEAT STRIP_TAC
  THEN MATCH_MP_TAC
        (BETA_RULE (Q.ISPEC `\y:string. dFV ([x |-> dVAR y] u)` lemma1))
  THEN REWRITE_TAC [FINITE_dFV]);

val NEW_UNION1 = prove(
  ``FINITE (s UNION t) ==> ~(NEW (s UNION t) IN s)``,
  STRIP_TAC THEN NEWLib.NEW_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) []);

val NOT_EQ_NEW = prove(
  ``!X. FINITE X /\ x IN X ==> ~(x = NEW X)``,
  PROVE_TAC [NEW_def]);


val lemma3 =
 Q.prove(
  `!t x y z.
     dOK t /\ z IN dFV t /\ ~(z = x)
       ==>
     z IN dFV ([x |-> dVAR y] t)`,
measureInduct_on `dLGH t`
  THEN ONCE_REWRITE_TAC [dOK_cases] THEN RW_TAC std_ss [] THENL
  [Q.PAT_X_ASSUM `_ IN _` MP_TAC THEN RW_TAC std_ss [dFV, IN_SING]
     THEN RW_TAC std_ss [dFV, IN_SING, NEQ_dVAR_dSUB],
   PROVE_TAC [dCON_dSUB, NOT_IN_EMPTY, dFV],
   `FINITE (dFV t' UNION {x;y;z})`
      by RW_TAC std_ss [FINITE_UNION,FINITE_INSERT, FINITE_EMPTY, FINITE_dFV]
    THEN MP_TAC (Q.SPECL [`t'`, `x'`, `NEW (dFV t' UNION {x;y;z})`] dALPHA)
    THEN RW_TAC std_ss [NEW_UNION1] THEN POP_ASSUM (K ALL_TAC) THEN
     `~(x:string = NEW (dFV (t':'a dB) UNION {x;y;z}))
      /\ ~(NEW (dFV t' UNION {x;y;z}) IN dFV (dVAR y:'a dB))
      /\ dOK ([x' |-> dVAR (NEW (dFV t' UNION {x;y;z}))] t')`
      by (REPEAT CONJ_TAC THENL
          [RW_TAC std_ss [NOT_EQ_NEW,IN_UNION,IN_INSERT],
           RW_TAC std_ss [dFV,IN_SING,GSYM NOT_EQ_NEW,IN_UNION,IN_INSERT],
           RW_TAC std_ss [dOK_dSUB,dOK_DEF]])
   THEN RW_TAC std_ss [dLAMBDA_dSUB,dFV_dLAMBDA, IN_DELETE] THENL
    [Q.PAT_X_ASSUM `$! M` MP_TAC
      THEN RW_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]
      THEN FIRST_ASSUM MATCH_MP_TAC THEN RW_TAC std_ss [] THENL
      [RW_TAC std_ss [dLGH_dSUB,dLGH_dLAMBDA_LESS],
       FIRST_ASSUM MATCH_MP_TAC THEN RW_TAC std_ss [dLGH_dLAMBDA_LESS]
         THEN Q.PAT_X_ASSUM `_ IN _` MP_TAC
         THEN RW_TAC std_ss [dFV_dLAMBDA,IN_DELETE]],
     RW_TAC std_ss [NOT_EQ_NEW, IN_UNION,IN_INSERT]],
   Q.PAT_X_ASSUM `_ IN _` MP_TAC
    THEN ZAP_TAC (std_ss && [dFV, IN_UNION, dAPP_dSUB])
            [dLGH_dAPP_LESS_2,dLGH_dAPP_LESS_1]]);

val lemma4 =
 Q.prove(
  `!u x.
     dOK u
      ==>
     dFV (dLAMBDA x u) SUBSET {z | !y. z IN dFV([x |-> dVAR y] u)}`,
RW_TAC std_ss
  (SUBSET_DEF::GSPEC_DEF::SPECIFICATION::dFV_dLAMBDA
    ::map (REWRITE_RULE [SPECIFICATION]) [IN_DELETE, lemma3]));

val lemma5 = Q.prove(
 `!x s t. s SUBSET t /\ ~(x IN t) ==> ~(x IN s)`,
 PROVE_TAC [SUBSET_DEF]);


val WRAP_DB_EXISTS = Q.store_thm("WRAP_DB_EXISTS",
 `?wrap. !u. dOK u ==> !x. wrap(\s:string. [x |-> dVAR s] u) = dLAMBDA x u`,
Q.EXISTS_TAC
   `\f:string->'a dB.
         let vs = {z | !y. z IN dFV (f y)} in
         let  v = @v. ~(v IN vs)
         in dLAMBDA v (f v)`
 THEN RW_TAC std_ss [LET_THM]
 THEN MATCH_MP_TAC (GSYM dALPHA_STRONG) THEN RW_TAC std_ss []
 THEN MATCH_MP_TAC lemma5
 THEN Q.EXISTS_TAC `{z | !y. z IN dFV([x |-> dVAR y] u)}`
 THEN RW_TAC std_ss [lemma4]
 THEN CONV_TAC SELECT_CONV
 THEN MATCH_MP_TAC new_exists THEN MATCH_MP_TAC lemma2 THEN
 ASM_REWRITE_TAC []);

val _ = export_theory();
