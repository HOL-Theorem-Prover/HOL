

(* ========================================================================= *)
(* Formalization and verification of fixed-point arithmetic.                 *)
(* ========================================================================= *)

(*---------------------------------------------------------------------------*
 * First, make standard environment available.                               *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib;

(*---------------------------------------------------------------------------*
 * Next, bring in extra tools used.                                          *
 *---------------------------------------------------------------------------*)

(*app load ["Psyntax", "hol88Lib", "numTheory", "prim_recTheory", "integerTheory", "tautLib", "Ho_Rewrite", "reduceLib",
            "tautLib", "jrhUtils", "Canon_Port", "AC", "Arbint", "prim_recTheory", "bword_bitopTheory", "realTheory",
            "pred_setTheory", "pairTheory", "mesonLib", "bossLib", "wordTheory", "Num_conv", "Canon_Port", "RealArith",
            "word_baseTheory", "numLib", "arithmeticTheory", "listTheory", "rich_listTheory", "liteLib", "bword_numTheory",
            "res_quanTheory"];*)

open Psyntax hol88Lib numTheory prim_recTheory integerTheory tautLib
     Ho_Rewrite reduceLib tautLib jrhUtils Canon_Port AC Arbint
     prim_recTheory bword_bitopTheory realTheory pred_setTheory
     pairTheory mesonLib bossLib wordTheory Num_conv Canon_Port
     RealArith word_baseTheory numLib arithmeticTheory listTheory
     rich_listTheory liteLib bword_numTheory res_quanTheory;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "fxp";

val Suff = Q_TAC SUFF_TAC ;

(*-----------------------------------------------------------------------

 Derived parameters for fixed point attributs.

------------------------------------------------------------------------- *)

val streamlength = Define `streamlength (b:num,ib:num,sf:num) = b` handle e => Raise e;

val intbits = Define `intbits (b: num, ib:num, sf: num) = ib`;

val signtype = Define `signtype (b: num, ib: num, st: num) = st`;

(*-----------------------------------------------------------------------

 Basic predicates for the fixed point format.

-------------------------------------------------------------------------*)

val is_signed = Define `is_signed(X) = (signtype((X : (num # num # num))) = 1)`;

val is_unsigned = Define `is_unsigned(X) = (signtype(X : (num # num # num)) = 0) `;

val fracbits = Define `fracbits(X : (num # num # num)) =
  (if is_unsigned (X) then streamlength (X) - intbits (X)
   else streamlength (X) - intbits (X) - 1 )`;

(*-----------------------------------------------------------------------

 Extractor functions for a fixed-point number.

-------------------------------------------------------------------------*)

val stream = Define `stream (v : bool word, a: (num # num # num) ) = v`;

val attrib = Define `attrib (v : bool word, a: (num # num # num)) = a`;

(*-----------------------------------------------------------------------

 Predicates for validity of a set of attributes and a fixed-point number.

-------------------------------------------------------------------------*)

val validAttr = Define `validAttr (X : (num # num # num)) =
  (streamlength (X) > 0   /\  streamlength (X) < 257) /\
  (intbits (X) < (streamlength (X) + 1)) /\ (signtype (X)  < 2)`;

val is_valid = Define `is_valid (a : (bool word # (num # num # num))) =
  validAttr (attrib a) /\ (WORDLEN (stream a) = streamlength (attrib a))`;

(*-----------------------------------------------------------------------
 Actual fxp type.
-------------------------------------------------------------------------*)

val fxp_tybij= define_new_type_bijections {
  name ="fxp_tybij",
  ABS ="fxp",
  REP ="defxp",
  tyax = new_type_definition ("fxp",
  Q.prove(`?(a: (bool word # (num # num # num))). is_valid a`,
  EXISTS_TAC (--`(WORD[F],(1,0,0)): (bool word # (num # num # num))`--) THEN
  RW_TAC arith_ss [is_valid,validAttr,attrib,signtype,intbits,streamlength,stream,WORDLEN_DEF,LENGTH]))};


val Stream = Define `(Stream (a: fxp)) = (stream (defxp a))`;

val Attrib = Define `(Attrib (a: fxp)) = (attrib (defxp a))`;

val Streamlength = Define `Streamlength (a: fxp) = streamlength (Attrib a)`;

val Intbits = Define `Intbits (a: fxp) = intbits (Attrib a)`;

val Fracbits = Define `Fracbits (a: fxp) = fracbits (Attrib a)`;

val Signtype = Define `Signtype (a: fxp) = signtype (Attrib a)`;

val Issigned = Define `Issigned (a:fxp) = is_signed (Attrib a)`;

val Isunsigned = Define `Isunsigned (a:fxp) = is_unsigned (Attrib a)`;

val Isvalid = Define `Isvalid (a: fxp) = is_valid (defxp a)`;

val Null = Define `Null = @(a: fxp). ~(Isvalid a)`;

(*-----------------------------------------------------------------------

 Fixed-point real number valuations.
-------------------------------------------------------------------------*)

val value = Define `(value (a:fxp)) = (if Isunsigned a then &(BNVAL(Stream a)) / (&2 pow Fracbits a) else
  (&(BNVAL (Stream a)) - &(((BV(MSB (Stream a)))) * (2 EXP (Streamlength a))))/(&2 pow Fracbits a))`;

(*-----------------------------------------------------------------------

 Smallest and largest fixed-point numbers for a given set of attributes and their real values.

 -------------------------------------------------------------------------*)

val MAX = Define `MAX (X: (num # num # num)) = (if (is_unsigned (X)) then
  ((&2 pow streamlength (X)) - &1) / (&2 pow fracbits (X)) else
  ((&2 pow (streamlength (X) - 1)) - &1) / (&2 pow fracbits (X)))`;


val MIN = Define `MIN (X: (num # num # num)) = (if (is_unsigned (X)) then &0
  else ((~(&2 pow (streamlength (X) - 1))) / &2 pow fracbits (X)))`;


val topfxp = Define `topfxp (X:(num # num # num)) =
  (if is_unsigned (X) then fxp (WORD (REPLICATE (streamlength (X)) T),X)
   else fxp (WCAT ((WORD [F]), (WORD (REPLICATE ((streamlength (X)) - 1) T))),X))`;

val bottomfxp = Define `bottomfxp (X:(num # num # num)) =
  (if is_unsigned (X) then fxp (WORD (REPLICATE (streamlength (X)) F),X)
   else fxp (WCAT ((WORD [T]), (WORD (REPLICATE ((streamlength (X)) - 1) F))),X))`;

(*-----------------------------------------------------------------------
 Characterization of best approximation from a set of abstract values
 ------------------------------------------------------------------------*)

val is_fxp_closest = Define `is_fxp_closest
  (v : fxp -> real) (s : fxp -> bool) (x : real) (a : fxp) =
  a IN s /\ !(b:fxp). b IN s ==> abs(v(a) - x) <= abs(v(b) - x)`;

(*-----------------------------------------------------------------------
 Best approximation with a deciding preference for multiple possibilities
 -------------------------------------------------------------------------*)

val fxp_closest = Define `fxp_closest
  (v : fxp -> real) (p : fxp -> bool) (s : fxp -> bool) (x : real) =
  @ a: fxp. (is_fxp_closest v s x a) /\ ((?b : fxp. is_fxp_closest v s x b /\ p(b)) ==> p(a))`;

(*----------------------------------------------------------------------
 Wrapping
 ------------------------------------------------------------------------*)

val floor = Define `floor (x: real) = @ n: num . & n <= abs x /\ !i: num. &i <= abs x ==> i <= n`;

val fraction = Define `fraction (x: real) = x - &(floor x)`;

val BDIG = Define `BDIG (n: num) (a: num) = (VB((a DIV (2 EXP n)) MOD 2))`;

val BDIGFUN = Define `BDIGFUN (a: num) = \n. BDIG n a`;

val BWORD = Define `BWORD (n: num) (m: num) = WORD(GENLIST (BDIGFUN n) m)`;

val TWOEXPONENT = Define `TWOEXPONENT (x: real) =
  @n: num . (&2 pow n) >= abs x /\ !m: num . (&2 pow m) >= abs x ==> n <= m`;

val POSITIVE = Define `POSITIVE (x: real) = (&2 pow (TWOEXPONENT x)) + x`;

val Wrapp = Define `Wrapp (X: num # num # num) (x: real) =
  (if x >= &0 then fxp (WCAT ((BWORD (floor x) (intbits X)) ,
  (BWORD (floor ((&2 pow fracbits X) * (fraction x))) (fracbits X))),X) else
  fxp (WCAT (((BWORD (floor (POSITIVE x)) (intbits X)) WOR (BWORD ((2 EXP (TWOEXPONENT x))) (intbits X))),
  (BWORD (floor ((&2 pow fracbits X) * (fraction (POSITIVE x)))) (fracbits X))),X))`;

(*-----------------------------------------------------------------------

 Enumerated type for fixed-point rounding, overflow, and exception handling modes.
 ------------------------------------------------------------------------*)

val fxp_roundmode = Hol_datatype
  `fxp_roundmode = Round
  | To_zero
  | To_plus_infinity
  | Truncate
  | Convergent` ;

val overflowmode = Hol_datatype
  `overflowmode = Wrap
  | Clip` ;

val Exception = Hol_datatype
  `Exception = no_except
  | overflow
  | invalid
  | loss_sign` ;

(*-----------------------------------------------------------------------

 Rounding to fixed-point formats.

 -------------------------------------------------------------------------*)

val fxp_round = TotalDefn.Define `(fxp_round (X: num # num # num ) (Convergent) (x:real) (mode:overflowmode)  =
  (if (x > (MAX(X)) /\ (mode = Clip) ) then (topfxp (X),overflow)
   else if (x < (MIN(X)) /\ (mode = Clip)) then (bottomfxp (X),overflow)
   else if (x > (MAX(X)) /\ (mode = Wrap) ) then (Wrapp(X) x,overflow)
   else if (x < (MIN(X)) /\ (mode = Wrap)) then (Wrapp(X) x,overflow)
   else
  (fxp_closest (value) (\a. LSB (Stream a) = F)
  {(a : fxp) | Isvalid a /\ ((Attrib a) = X) } x , no_except))) /\

  (fxp_round (X) (To_zero) x mode =
   (if (x > (MAX(X)) /\ (mode = Clip) ) then (topfxp (X),overflow)
   else if (x < (MIN(X)) /\ (mode = Clip) ) then (bottomfxp (X),overflow)
   else if (x >= (MAX(X)) /\ (mode = Wrap) ) then (Wrapp(X) x,overflow)
   else if (x < (MIN(X)) /\ (mode = Wrap)) then (Wrapp(X) x,overflow)
   else
  (fxp_closest (value) (\a.T)
  {a | Isvalid a /\ ((Attrib a) = X) /\ abs(value a) <= abs(x)} x, no_except))) /\

  (fxp_round (X) (To_plus_infinity) x mode =
   (if (x > (MAX(X)) /\ (mode = Clip) ) then (topfxp (X),overflow)
   else if (x < (MIN(X)) /\ (mode = Clip) ) then (bottomfxp (X),overflow)
   else if (x > (MAX(X)) /\ (mode = Wrap) ) then (Wrapp(X) x,overflow)
   else if (x < (MIN(X)) /\ (mode = Wrap)) then (Wrapp(X) x,overflow)
   else
  (fxp_closest (value) (\a.T)
  {a | Isvalid a /\ ((Attrib a) = X) /\ ((value a) >= x) } x, no_except))) /\

  (fxp_round (X) (Truncate) x mode =
   (if (x > (MAX(X)) /\ (mode = Clip) ) then (topfxp (X),overflow)
   else if (x < (MIN(X)) /\ (mode = Clip) ) then (bottomfxp (X),overflow)
   else if (x > (MAX(X)) /\ (mode = Wrap) ) then (Wrapp(X) x,overflow)
   else if (x < (MIN(X)) /\ (mode = Wrap)) then (Wrapp(X) x,overflow)
   else
  (fxp_closest (value) (\a.T)
  {a | Isvalid a /\ ((Attrib a) = X) /\ ((value a) <= x) } x , no_except))) /\

  (fxp_round (X) (Round) x mode =
   (if (x > (MAX(X)) /\ (mode = Clip) ) then (topfxp (X),overflow)
   else if (x < (MIN(X)) /\ (mode = Clip) ) then (bottomfxp (X),overflow)
   else if (x > (MAX(X)) /\ (mode = Wrap) ) then (Wrapp(X) x,overflow)
   else if (x < (MIN(X)) /\ (mode = Wrap)) then (Wrapp(X) x,overflow)
   else
  (fxp_closest (value) (\a.value (fxp (Stream a, X)) >= x )
  {a | Isvalid a /\ ((Attrib a) = X) } x, no_except)))`;

(*-----------------------------------------------------------------------

 Definitions of the fixed-point arithmetic operations.
  ------------------------------------------------------------------------*)

val fxpAdd = Define `fxpAdd (X:(num#num#num)) (rnd: fxp_roundmode) (over:overflowmode) (a:fxp) (b:fxp) =
  (if ~((Isvalid a) /\ (Isvalid b)) then (Null,invalid)
   else if (value a + value b < &0) /\ is_unsigned (X) then (fxp (WORD(REPLICATE (streamlength (X)) F),(X)) , loss_sign)
   else (fxp_round (X) (rnd) (value a + value b) over))`;

val fxpAbs = Define `fxpAbs (X:(num#num#num)) (rnd: fxp_roundmode) (over:overflowmode) (a:fxp) =
  (if ~(Isvalid a) then (Null,invalid)
   else (fxp_round (X) (rnd) (abs(value a)) over))`;

val fxpAShift = Define `fxpAShift (X:(num#num#num)) (rnd: fxp_roundmode) (over:overflowmode) (a:fxp) (b:int) =
  (if ~(Isvalid a) then (Null,invalid)
   else if (b < &0) then
  (fxp_round (X) (rnd)
  (value (fxp (WCAT(WORD(REPLICATE (Num(ABS(b))) (MSB (Stream a))), WSEG (streamlength (Attrib a) - 1)
  (streamlength (Attrib a) - Num(ABS(b)) ) (Stream a) ) , Attrib a))) over)
   else
  (fxp_round (X) (rnd)
  (value (fxp (WCAT(WORD(REPLICATE (Num(ABS(b))) F),
  WSEG (streamlength (Attrib a) - (SUC(Num(ABS(b))))) 0 (Stream a) ), Attrib a))) over))`;

val fxpAnd = Define `fxpAnd (X:(num#num#num)) (a:fxp) (b:fxp) =
  (if ~((Isvalid a) /\ (Isvalid b)) \/ ~((Attrib a) = X) \/ ~((Attrib b) = X) then (Null,invalid)
   else
  (fxp (((Stream a) WAND  (Stream b)), X), no_except))`;

val fxpOr = Define `fxpOr (X:(num#num#num)) (a:fxp) (b:fxp) =
  (if ~((Isvalid a) /\ (Isvalid b)) \/  ~((Attrib a) = X) \/ ~((Attrib b) = X)  then (Null,invalid)
   else
  (fxp (((Stream a) WOR  (Stream b)), X), no_except))`;

val fxpSub = Define `fxpSub(X:(num#num#num)) (rnd: fxp_roundmode) (over:overflowmode) (a:fxp) (b:fxp) =
  (if ~((Isvalid a) /\ (Isvalid b)) then (Null,invalid)
   else if (value a - value b < &0) /\ is_unsigned (X) then (fxp (WORD(REPLICATE (streamlength (X)) F),(X)) , loss_sign)
   else
  (fxp_round (X) (rnd) (value a - value b) over))`;

val fxpMul = Define `fxpMul(X:(num#num#num)) (rnd: fxp_roundmode) (over:overflowmode) (a:fxp) (b:fxp)=
  (if ~((Isvalid a) /\ (Isvalid b)) then (Null,invalid)
   else if (value a * value b < &0) /\ is_unsigned (X) then (fxp (WORD(REPLICATE (streamlength (X)) F),(X)) , loss_sign)
   else
  (fxp_round (X) (rnd) (value a * value b) over))`;

val fxpDiv = Define `fxpDiv(X:(num#num#num)) (rnd: fxp_roundmode) (over:overflowmode) (a:fxp) (b:fxp)=
  (if ~((Isvalid a) /\ (Isvalid b)) then (Null,invalid)
   else if (value b = &0) then
  (fxp (WORD(REPLICATE (streamlength (X)) F),(X)) , invalid)
   else if (value a / value b < &0) /\ is_unsigned (X) then (fxp (WORD(REPLICATE (streamlength (X)) F),(X)) , loss_sign)
   else
  (fxp_round (X) (rnd) (value a / value b) over))`;

(* ------------------------------------------------------------------------- *)

(* Lemmas for analyzing the fixed-point rounding operation. *)
(* ------------------------------------------------------------------------- *)

val STREAM = prove_thm (
  "STREAM",
  (--`!a: (bool word # (num # num # num)). stream a = FST a`--),
  GEN_TAC THEN SUBST1_TAC (SYM(REWRITE_CONV[PAIR] (--`FST(a):bool word, SND(a): (num # num # num)`--))) THEN
  PURE_REWRITE_TAC [stream] THEN REWRITE_TAC [FST]);

(*----------------------------------*)

val ATTRIB = prove_thm (
  "ATTRIB",
  (--`!a: (bool word # (num # num # num)). attrib a = SND a`--),
  GEN_TAC THEN SUBST1_TAC (SYM(REWRITE_CONV[PAIR] (--`FST(a):bool word, SND(a): (num # num # num)`--))) THEN
  PURE_REWRITE_TAC [attrib] THEN REWRITE_TAC [SND]);

(*----------------------------------*)

val STREAMLEN = prove_thm (
  "STREAMLEN",
  (--`!X. streamlength (X) = FST (X)`--),
  GEN_TAC THEN SUBST1_TAC (SYM(REWRITE_CONV[PAIR] (--`FST(X):num, FST(SND(X)):num, SND(SND(X)):num`--))) THEN
  PURE_REWRITE_TAC [streamlength] THEN REWRITE_TAC [FST]);

(*-----------------------------------*)

val INTBITS = prove_thm (
  "INTBITS",
  (--`!X: (num#num#num). intbits (X) = FST (SND (X))`--),
  GEN_TAC THEN SUBST1_TAC (SYM(REWRITE_CONV[PAIR] (--`FST(X):num, FST(SND(X)):num, SND(SND(X)):num`--))) THEN
  REWRITE_TAC [intbits] THEN REWRITE_TAC [FST,SND]);

(*------------------------------------*)

val SIGN = prove_thm (
  "SIGN",
  (--`!X: (num#num#num). signtype (X) = SND (SND (X))`--),
  GEN_TAC THEN SUBST1_TAC (SYM(REWRITE_CONV[PAIR] (--`FST(X):num, FST(SND(X)):num, SND(SND(X)):num`--))) THEN
  REWRITE_TAC [signtype] THEN REWRITE_TAC [SND]);

(*------------------------------------*)

val IS_FXP_CLOSEST_EXISTS = prove_thm (
  "IS_FXP_CLOSEST_EXISTS",
  (--`!(v :fxp -> real)  (x : real) (s :fxp -> bool) . FINITE (s:fxp -> bool) ==> ~(s = EMPTY)
      ==> ?(a:fxp). is_fxp_closest v s x a`--),
  GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC pred_setTheory.FINITE_INDUCT THEN
  REWRITE_TAC [NOT_INSERT_EMPTY] THEN X_GEN_TAC (--`s : (fxp -> bool)`--) THEN
  ASM_CASES_TAC (--` (s: (fxp -> bool)) = EMPTY`--) THENL [
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [FINITE_EMPTY] THEN REWRITE_TAC [NOT_IN_EMPTY] THEN
    X_GEN_TAC (--`e: fxp`--) THEN EXISTS_TAC (--`e : fxp`--) THEN REWRITE_TAC [is_fxp_closest] THEN
    REWRITE_TAC [IN_SING] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL],
    ASM_CASES_TAC (--` FINITE (s: (fxp -> bool))`--) THENL [
      ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (--`a:fxp`--)) THEN X_GEN_TAC (--`e: fxp`--) THEN
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (--`abs (v (a :fxp ) - (x : real )) <= abs (v (e :fxp ) - (x : real ))`--) THENL [
        EXISTS_TAC (--`a:fxp`--) THEN UNDISCH_TAC (--`is_fxp_closest v s x a`--) THEN REWRITE_TAC [is_fxp_closest] THEN
        REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THENL [
          ASM_REWRITE_TAC [] , ASM_REWRITE_TAC [REAL_LE_REFL] , PROVE_TAC []],
        EXISTS_TAC (--`e:fxp`--) THEN UNDISCH_TAC(--`is_fxp_closest v s x a`--) THEN REWRITE_TAC [is_fxp_closest] THEN
        REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THENL [
          ASM_REWRITE_TAC [REAL_LE_REFL],
          PAT_ASSUM (--`!b:fxp . b IN s ==> abs (v a - x) <= abs (v b - x)`--) (MP_TAC o SPEC (--`b:fxp`--)) THEN
          ASM_REWRITE_TAC [] THEN PAT_ASSUM (--`~(abs (v a - x) <= abs (v e - x))`--) MP_TAC THEN REAL_ARITH_TAC]],
      ASM_REWRITE_TAC []]]);

(*------------------------------------*)

val FXP_CLOSEST_IS_EVERYTHING = prove_thm  (
  "FXP_CLOSEST_IS_EVERYTHING",
  (--`! (v :fxp -> real) (p:fxp -> bool) (x : real) (s : fxp -> bool).
      FINITE(s) ==> ~(s = EMPTY) ==> is_fxp_closest v s x (fxp_closest v p s x) /\
      ((?b:fxp . is_fxp_closest v s x b /\ p b) ==> p (fxp_closest v p s x))`--),
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC [fxp_closest] THEN
  CONV_TAC SELECT_CONV THEN ASM_CASES_TAC (--`?a:fxp. is_fxp_closest v s x a /\ p a`--) THENL [
    POP_ASSUM (X_CHOOSE_TAC (--`a : fxp`--)) THEN EXISTS_TAC (--`a : fxp`--) THEN
    RW_TAC arith_ss [],FIRST_ASSUM (MP_TAC o MATCH_MP (IS_FXP_CLOSEST_EXISTS)) THEN
    RW_TAC arith_ss []]);

(*------------------------------------*)

val FXP_CLOSEST_IN_SET = prove_thm (
  "FXP_CLOSEST_IN_SET",
  (--`!(v:fxp ->real) (p:fxp -> bool) (x : real) (s : fxp -> bool).
      FINITE(s) ==> ~(s = EMPTY) ==> (fxp_closest v p s x) IN s`--),
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (FXP_CLOSEST_IS_EVERYTHING)) THEN
  ASM_MESON_TAC[is_fxp_closest]);

(*------------------------------------*)

val FXP_CLOSEST_IS_FXP_CLOSEST = prove_thm (
  "FXP_CLOSEST_IS_FXP_CLOSEST",
  (--`!(v:fxp ->real) (p:fxp -> bool) (x : real) (s : fxp -> bool).
      FINITE(s) ==> ~(s = EMPTY) ==> is_fxp_closest v s x (fxp_closest v p s x)`--),
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP FXP_CLOSEST_IS_EVERYTHING) THEN
  ASM_MESON_TAC[is_fxp_closest]);

(*------------------------------------*)

val WORDINDUCT = prove_thm (
  "WORDINDUCT",
  (--`!n:num. {w :(bool word ) | WORDLEN w = SUC n} =
      (IMAGE (\w. WCAT (WORD [T],w)) {w | WORDLEN w = n}) UNION
      (IMAGE (\w. WCAT (WORD [F],w)) {w | WORDLEN w = n})`--),
  GEN_TAC THEN PURE_REWRITE_TAC [EXTENSION,IN_UNION] THEN
  RW_TAC arith_ss [GSPECIFICATION,IMAGE_DEF] THEN
  Cases_on `x` THEN Cases_on `l` THENL [
    REWRITE_TAC [WORDLEN_DEF,LENGTH,SUC_NOT] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN
    RW_TAC arith_ss [NOT_EXISTS_THM] THENL [
    Cases_on `w` THEN RW_TAC arith_ss [WCAT_DEF,APPEND,NOT_EXISTS_THM],
    Cases_on `w` THEN RW_TAC arith_ss [WCAT_DEF,APPEND]],
    EQ_TAC THENL [
      STRIP_TAC THEN CONV_TAC OR_EXISTS_CONV THEN
      EXISTS_TAC (--`WORD t:bool word`--) THEN
      UNDISCH_TAC (--`WORDLEN ((WORD (h::t): bool word)) = SUC (n:num)`--) THEN
      Cases_on `h` THENL [
        RW_TAC arith_ss [WORDLEN_DEF, listTheory.APPEND, WCAT_DEF,listTheory.LENGTH],
        RW_TAC arith_ss [WORDLEN_DEF, listTheory.APPEND, WCAT_DEF,listTheory.LENGTH]],
      RW_TAC arith_ss [WORDLEN_DEF, listTheory.APPEND, WCAT_DEF,listTheory.LENGTH] THENL [
        Cases_on `w` THEN
        UNDISCH_TAC (--`(WORD (h::t):bool word) = WCAT (WORD [T],WORD l)`--) THEN
        RW_TAC arith_ss [WORDLEN_DEF, listTheory.APPEND, WCAT_DEF,listTheory.LENGTH],
        Cases_on `w` THEN
        UNDISCH_TAC (--`(WORD (h::t):bool word) = WCAT (WORD [F],WORD l)`--) THEN
        RW_TAC arith_ss [WORDLEN_DEF, listTheory.APPEND, WCAT_DEF,listTheory.LENGTH]]]]);

(*---------------------*)

val WORDBASIS = prove_thm (
  "WORDBASIS",
  (--`FINITE {w: bool word | WORDLEN w = 0} = FINITE { WORD [] }`--),
  Suff `{w: bool word | WORDLEN w = 0} = { WORD [] }` THENL [
    RW_TAC std_ss [FINITE_SING], ONCE_REWRITE_TAC [EXTENSION, WORDLEN_DEF] THEN
    RW_TAC arith_ss [GSPECIFICATION, WORDLEN_DEF, listTheory.LENGTH] THEN
    Cases_on `x` THEN Cases_on `l` THEN
    RW_TAC arith_ss [GSPECIFICATION, IN_SING, WORDLEN_DEF,listTheory.LENGTH]]);

(*---------------------*)

val WORDFINITE = prove_thm (
  "WORDFINITE",
  (--`!x: num . FINITE {w: bool word| WORDLEN w = x}`--),
  INDUCT_TAC THENL [
    RW_TAC arith_ss [FINITE_SING,WORDBASIS],
    RW_TAC arith_ss [FINITE_UNION , IMAGE_FINITE, WORDINDUCT]]);

(*---------------------*)

val WORDPAIRIMAGE = prove_thm (
    "WORDPAIRIMAGE",
    (--`!n:num.{(w: bool word,x: num)|(WORDLEN w = x) /\ (x=n)} =
        IMAGE (\w. (w: bool word , WORDLEN w)) {w: bool word| WORDLEN w = n}`--),
    GEN_TAC THEN REWRITE_TAC [IMAGE_DEF] THEN RW_TAC arith_ss [GSPECIFICATION] THEN
    PURE_REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL [
      Cases_on `x` THEN RW_TAC arith_ss [GSPECIFICATION] THEN
      UNDISCH_TAC (--`((q,r),T) = (\(w,x). ((w,x),(WORDLEN (w: bool word) = x) /\ (x = n))) x`--) THEN
      Cases_on `x` THEN RW_TAC arith_ss [], Cases_on `x` THEN RW_TAC arith_ss [GSPECIFICATION] THEN
      EXISTS_TAC (--`((q:bool word,WORDLEN q))`--) THEN RW_TAC arith_ss []]);

(*---------------------*)

val FXP_FIRSTCROSS00 = prove_thm (
  "FXP_FIRSTCROSS00",
  (--`! (x: (bool word # (num # num # num))) (p:num) (q:num) (r:num).
   x = (\ ((w,x),y,z). (w,x,y,z))
      ((FST x,FST (SND x)),FST (SND (SND x)),SND (SND (SND x)))`--),

REPEAT GEN_TAC THEN Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN
RW_TAC arith_ss []);

(*---------------------*)

val FXP_FIRSTCROSS0 = prove_thm (
  "FXP_FIRSTCROSS0", (--`! (x: (bool word # (num # num # num))) (p:num) (q:num) (r:num).
   (FST (SND x) < p /\ FST (SND (SND x)) < q /\ SND (SND (SND x)) < r /\
   (WORDLEN (FST x) = FST (SND x))) ==>
   (?x''. (FST ((FST x,FST (SND x)),FST (SND (SND x)),SND (SND (SND x))),T) =
   (\ (w,x). ((w,x),(WORDLEN w = x) /\ x < p)) x'') /\
   FST (SND ((FST x,FST (SND x)),FST (SND (SND x)),SND (SND (SND x)))) <
   q /\ SND (SND ((FST x,FST (SND x)),FST (SND (SND x)),SND (SND (SND x)))) < r`--),

REPEAT GEN_TAC THEN
RW_TAC arith_ss [] THEN
EXISTS_TAC (--`(FST (x: (bool word # (num # num # num))),FST (SND (x: (bool word # (num # num # num))))):(bool word # num)`--) THEN
RW_TAC arith_ss []);

(*---------------------*)

val FXP_FIRSTCROSS1 = prove_thm (
  "FXP_FIRSTCROSS1",
  (--`! (x: (bool word # (num # num # num))) (p:num) (q:num) (r:num). FST (SND x) < p /\ FST (SND (SND x)) < q /\ SND (SND (SND x)) < r /\
    (WORDLEN (FST x) = FST (SND x)) ==>
    ?x'.
      (x = ( \ ((w,x),y,z). (w,x,y,z)) x') /\
      (?x. (FST x',T) = (\ (w,x). ((w,x),(WORDLEN w = x) /\ x < p)) x) /\
      FST (SND x') < q /\ SND (SND x') < r`--),

    REPEAT GEN_TAC THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC (--`((FST (x: (bool word # (num # num # num))), FST (SND (x: (bool word # (num # num # num))))), (FST (SND(SND (x: (bool word # (num # num # num))))) , SND(SND(SND (x: (bool word # (num # num # num))))))):((bool word#num)#(num#num)) `--) THEN
    CONJ_TAC THENL [

MP_TAC(SPECL [(--`(x: (bool word # (num # num # num)))`--), (--`(p:num)`--), (--`(q:num)`--), (--`(r:num)`--)] FXP_FIRSTCROSS00) THEN

RW_TAC arith_ss [],

MP_TAC(SPECL [(--`(x: (bool word # (num # num # num)))`--), (--`(p:num)`--), (--`(q:num)`--), (--`(r:num)`--)] FXP_FIRSTCROSS0) THEN

RW_TAC arith_ss []]);

(*---------------------*)

val FXP_FIRSTCROSS2 = prove_thm (
  "FXP_FIRSTCROSS2",
  (--` ! (x: (bool word # (num # num # num))) (p:num) (q:num) (r:num).

(?x'. (x = (\ ((w,x),y,z). (w,x,y,z)) x') /\
       (?x. (FST x',T) = (\ (w,x). ((w,x),(WORDLEN w = x) /\ x < p)) x) /\
       FST (SND x') < q /\ SND (SND x') < r) ==>
    FST (SND x) < p /\ FST (SND (SND x)) < q /\ SND (SND (SND x)) < r /\
    (WORDLEN (FST x) = FST (SND x))`--),

      REPEAT STRIP_TAC THENL [
      Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r''` THEN Cases_on `x'` THEN Cases_on `r''` THEN
      Cases_on `q''''` THEN Cases_on `x''` THEN
      UNDISCH_TAC (--`(q': bool word,q'': num,q''': num,r': num) =
      ( \ ((w,x),y,z). (w,x,y,z)) ((q'''''',r''),q''''',r''')`--) THEN
      UNDISCH_TAC (--`(FST ((q'''''': bool word,r'': num),q''''': num,r''': num),T) =
      (\ (w,x). ((w,x),(WORDLEN w = x) /\ x < p)) (q'''',r'''')`--) THEN
      RW_TAC arith_ss [], Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r''` THEN Cases_on `x'` THEN Cases_on `r''` THEN
      Cases_on `q''''` THEN Cases_on `x''` THEN
      UNDISCH_TAC (--`(q': bool word,q'': num,q''': num,r': num) =
      (\ ((w,x),y,z). (w,x,y,z)) ((q'''''',r''),q''''',r''')`--) THEN
      UNDISCH_TAC (--`FST (SND ((q'''''': bool word,r'': num),q''''': num,r''': num)) < q`--) THEN
      RW_TAC arith_ss [], Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r''` THEN Cases_on `x'` THEN Cases_on `r''` THEN
      Cases_on `q''''` THEN Cases_on `x''` THEN
      UNDISCH_TAC (--`(q': bool word,q'': num,q''': num,r': num) =
      (\ ((w,x),y,z). (w,x,y,z)) ((q'''''',r''),q''''',r''')`--) THEN
      UNDISCH_TAC (--`SND (SND ((q'''''': bool word,r'': num),q''''': num,r''':num)) < r`--) THEN
      RW_TAC arith_ss [], Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r''` THEN Cases_on `x'` THEN Cases_on `r''` THEN
      Cases_on `q''''` THEN Cases_on `x''` THEN
      UNDISCH_TAC (--`(q': bool word,q'': num,q''': num,r': num) =
      (\ ((w,x),y,z). (w,x,y,z)) ((q'''''',r''),q''''',r''')`--) THEN
      UNDISCH_TAC (--`(FST ((q'''''': bool word,r'': num),q''''': num,r''': num),T) =
      (\ (w,x). ((w,x),(WORDLEN w = x) /\ x < p)) (q'''',r'''')`--) THEN
      RW_TAC arith_ss []]);

(*-------------------------------------------*)

val FXP_FIRSTCROSS3 = prove_thm (
  "FXP_FIRSTCROSS3",
  (--`! (x: (bool word # (num # num # num))) (p:num) (q:num) (r:num).
   FST (SND x) < p /\ FST (SND (SND x)) < q /\ SND (SND (SND x)) < r /\
    (WORDLEN (FST x) = FST (SND x)) =
    ?x'.
      (x = (\ ((w,x),y,z). (w,x,y,z)) x') /\
      (?x. (FST x',T) = (\ (w,x). ((w,x),(WORDLEN w = x) /\ x < p)) x) /\
      FST (SND x') < q /\ SND (SND x') < r`--),

REPEAT GEN_TAC THEN
EQ_TAC THENL [
MP_TAC(SPECL [(--`(x: (bool word # (num # num # num)))`--), (--`(p:num)`--), (--`(q:num)`--), (--`(r:num)`--)] FXP_FIRSTCROSS1) THEN
RW_TAC arith_ss [],
MP_TAC(SPECL [(--`(x: (bool word # (num # num # num)))`--), (--`(p:num)`--), (--`(q:num)`--), (--`(r:num)`--)] FXP_FIRSTCROSS2) THEN
RW_TAC arith_ss []]);

(*-------------------------------------------*)

val FXP_FIRSTCROSS = prove_thm (
  "FXP_FIRSTCROSS",
  (--`! p:num q:num r:num . {a: (bool word # (num # num # num)) |
      (FST (SND a) < p) /\ (FST(SND (SND a)) < q) /\ (SND (SND (SND a)) < r) /\ (WORDLEN (FST a) = FST (SND a)) } =
      IMAGE (\ ((w: bool word, x: num), (y: num, z: num)). (w,(x,y,z))) ({(w: bool word,x: num) |
      (WORDLEN (w) = x) /\ (x < p) } CROSS ({y: num | y < q} CROSS {z: num | z < r}))`--),

REPEAT GEN_TAC THEN
REWRITE_TAC [GSPECIFICATION,CROSS_DEF, IMAGE_DEF] THEN
PURE_REWRITE_TAC [EXTENSION] THEN
RW_TAC arith_ss [GSPECIFICATION] THEN
MP_TAC(SPECL [(--`(x: (bool word # (num # num # num)))`--), (--`(p:num)`--), (--`(q:num)`--), (--`(r:num)`--)] FXP_FIRSTCROSS3) THEN RW_TAC arith_ss []);

(*-------------------------------------------*)

val COUNTINDUCT = prove_thm (
  "COUNTINDUCT",
  (--`! n:num. ({x:num | x < 0} = EMPTY) /\ ({x | x < SUC n} = n INSERT {x | x < n})`--),
  REPEAT GEN_TAC THEN PURE_REWRITE_TAC [EXTENSION,IN_INSERT] THEN
  RW_TAC arith_ss [GSPECIFICATION,LESS_THM,NOT_IN_EMPTY]);

(*-------------------------------*)

val FINITECOUNT = prove_thm (
  "FINITECOUNT",
  (--`! n:num. FINITE {x:num | x < n}`--),
  INDUCT_TAC THENL [
    RW_TAC arith_ss [COUNTINDUCT,FINITE_EMPTY],RW_TAC arith_ss [COUNTINDUCT,FINITE_INSERT]]);

(*----------------------------------------------*)

val FINITELESSBASIS = prove_thm (
  "FINITELESSBASIS",
  (--` {(w: bool word, x: num)| (WORDLEN w = x) /\ x < 0} = EMPTY`--),
  PURE_REWRITE_TAC [EXTENSION] THEN RW_TAC arith_ss [GSPECIFICATION, NOT_IN_EMPTY] THEN
  Cases_on `x'` THEN RW_TAC arith_ss []);

(*-------------------------------*)

val FINITELESSINDUCT = prove_thm (
  "FINITELESSINDUCT",
  (--`!n. ( FINITE {(w: bool word,x: num)| (WORDLEN w = x) /\ (x < SUC n)} =
      FINITE ({(w: bool word,x: num)| (WORDLEN w = x) /\ (x = n)} UNION
      {(w: bool word,x: num)| (WORDLEN w = x) /\ (x < n)}))`--),
  REPEAT GEN_TAC THEN
  Suff `{(w: bool word,x: num)| (WORDLEN w = x) /\ (x < SUC n)} =
  ({(w: bool word,x: num)| (WORDLEN w = x) /\ (x = n)} UNION
  {(w: bool word,x: num)| (WORDLEN w = x) /\ (x < n)})` THENL [
    RW_TAC std_ss [], ONCE_REWRITE_TAC [EXTENSION] THEN
    PURE_REWRITE_TAC [GSPECIFICATION,IN_UNION] THEN
    GEN_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THEN RW_TAC arith_ss [GSYM EXISTS_OR_THM] THEN
      Cases_on `x'` THEN Cases_on `x` THEN EXISTS_TAC (--`(q,r):(bool word # num)`--) THEN
      RW_TAC arith_ss [], REPEAT STRIP_TAC THENL [
        Cases_on `x'` THEN Cases_on `x` THEN EXISTS_TAC (--`(q,r):(bool word # num)`--) THEN
        UNDISCH_TAC (--`((q': bool word,r': num),T) = (\ (w,x). ((w,x),(WORDLEN w = x) /\ (x = n))) (q,r)`--) THEN
        RW_TAC arith_ss [], Cases_on `x'` THEN Cases_on `x` THEN
        UNDISCH_TAC (--`((q': bool word,r': num),T) = (\ (w,x). ((w,x),(WORDLEN w = x) /\ (x < n))) (q,r)`--) THEN
        REPEAT STRIP_TAC THEN EXISTS_TAC (--`(q,r):(bool word # num)`--) THEN
        UNDISCH_TAC (--`((q': bool word,r': num),T) = (\ (w,x). ((w,x),(WORDLEN w = x) /\ (x < n))) (q,r)`--) THEN
        RW_TAC arith_ss []]]]);

(*-----------------------------------------------*)

val FINITEPAIRLESS = prove_thm (
  "FINITEPAIRLESS",
  (--`!m: num. FINITE {(w: bool word, x: num) | (WORDLEN w = x) /\ x < m}`--),
  INDUCT_TAC THENL [
    RW_TAC arith_ss [FINITELESSBASIS,FINITE_EMPTY ],
    RW_TAC arith_ss [FINITELESSINDUCT] THEN
    RW_TAC arith_ss [FINITE_UNION] THEN
    RW_TAC arith_ss [WORDPAIRIMAGE, WORDFINITE, IMAGE_FINITE]]);

(*----------------------------------------------*)

val FINITEGENERAL = prove_thm (
  "FINITEGENERAL",
  (--`! p:num q:num r:num . FINITE {a: (bool word # (num # num # num)) | (FST (SND a) < p)
      /\ (FST(SND (SND a)) < q) /\ (SND (SND (SND a)) < r) /\ (WORDLEN (FST a) = FST (SND a)) }`--),
  REPEAT GEN_TAC THEN
  RW_TAC arith_ss [FXP_FIRSTCROSS,FINITECOUNT,FINITEPAIRLESS,IMAGE_FINITE,FINITE_CROSS]);

(*---------------------------------------------*)

val INSTANCEFINITE = prove_thm (
  "INSTANCEFINITE",
  (--`FINITE {a: (bool word # (num # num # num)) | (FST (SND a) < 257: num) /\
      (FST (SND (SND a)) < 257) /\ (SND (SND (SND a)) < 2: num) /\ (WORDLEN (FST a) = FST (SND a)) }`--),
  RW_TAC arith_ss [FINITEGENERAL]);

(*-----------------------------------*)

val ISVALID_SUB = prove_thm (
  "ISVALID_SUB",
  (--`{a: (bool word # (num # num # num)) | is_valid a } SUBSET
      {a | (FST (SND a) < 257) /\ (FST (SND (SND a)) < (FST (SND a) + 1))
      /\ (SND (SND (SND a)) < 2) /\ (WORDLEN (FST a) = FST (SND a)) }`--),
  REWRITE_TAC [is_valid, SUBSET_DEF, validAttr, STREAMLEN,SIGN,STREAM,ATTRIB,INTBITS] THEN
  RW_TAC arith_ss [GSPECIFICATION]);

(*----------------------------*)

val INSTANCE = prove_thm (
  "INSTANCE",
  (--`{a: (bool word # (num # num # num)) | (FST (SND a) < (257: num)) /\ (FST (SND (SND a)) <
      (((FST (SND a)):num) + (1:num))) /\ (SND (SND (SND a)) < (2: num)) /\ (WORDLEN (FST a) = FST (SND a)) } SUBSET
      {a: (bool word # (num # num # num)) | (FST (SND a) < 257: num) /\ (FST (SND (SND a)) < 257)
      /\ (SND (SND (SND a)) < 2: num) /\ (WORDLEN (FST a) = FST (SND a)) }`--),
  REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN RW_TAC arith_ss [GSPECIFICATION]);

(*-------------------------------*)

val MATCHFINITE = prove_thm (
  "MATCHFINITE",
  (--`{a: (bool word # (num # num # num)) | (FST (SND a) < (257: num)) /\ (FST (SND (SND a)) <
      (((FST (SND a)):num) + (1:num))) /\ (SND (SND (SND a)) < (2: num)) /\ (WORDLEN (FST a) = FST (SND a)) } SUBSET
      {a: (bool word # (num # num # num)) | (FST (SND a) < 257: num) /\ (FST (SND (SND a)) < 257)
      /\ (SND (SND (SND a)) < 2: num) /\ (WORDLEN (FST a) = FST (SND a)) } ==>
      FINITE {a: (bool word # (num # num # num)) | (FST (SND a) < (257: num)) /\ (FST (SND (SND a)) <
      (((FST (SND a)):num) + (1:num))) /\ (SND (SND (SND a)) < (2: num)) /\ (WORDLEN (FST a) = FST (SND a)) } `--),
  MATCH_MP_TAC SUBSET_FINITE THEN REWRITE_TAC [INSTANCEFINITE]);

(*---------------------------------*)

val MAINFINITE = prove_thm (
  "MAINFINITE",
  (--`FINITE {a: (bool word # (num # num # num)) | (FST (SND a) < (257: num)) /\
      (FST (SND (SND a)) < (((FST (SND a)):num) + (1:num))) /\ (SND (SND (SND a)) < (2: num)) /\ (WORDLEN (FST a) =
      FST (SND a)) } `--),
  MATCH_MP_TAC MATCHFINITE THEN REWRITE_TAC [INSTANCE]);

(*---------------------------------*)

val MATCHFINITEVALID = prove_thm (
  "MATCHFINITEVALID",
  (--`{ a: (bool word # (num # num # num)) | is_valid a}   SUBSET
      {a | (FST (SND a) < 257) /\ (FST (SND (SND a)) < (FST (SND a) + 1)) /\ (SND (SND (SND a)) < 2) /\
      (WORDLEN (FST a) = FST (SND a)) }  ==> FINITE { a: (bool word # (num # num # num)) | is_valid a}`--),
  MATCH_MP_TAC SUBSET_FINITE THEN REWRITE_TAC [MAINFINITE]);

(*------------------------------*)

val FINITEVALID = prove_thm (
  "FINITEVALID",
  (--`FINITE { a: (bool word # (num # num # num)) | is_valid a}`--),
  MATCH_MP_TAC MATCHFINITEVALID THEN REWRITE_TAC [ISVALID_SUB]);

(*------------------------------*)

val MATCHFINITEVALIDATTR = prove_thm (
  "MATCHFINITEVALIDATTR",
  (--`! (n: num) (m: num) (s: num) .
      { a: (bool word # (num # num # num)) | is_valid a /\ (attrib a = (n,m,s))} SUBSET { a | is_valid a}
      ==> FINITE { a: (bool word # (num # num # num)) | is_valid a /\ (attrib a = (n,m,s))}`--),
  MATCH_MP_TAC SUBSET_FINITE THEN REWRITE_TAC [FINITEVALID]);

(*-----------------------------*)

val ISVALID_ATTR_SUB = prove_thm (
  "ISVALID_ATTR_SUB",
  (--`! n m s . { a: (bool word # (num # num # num)) | is_valid a /\ (attrib a =
      (n,m,s))} SUBSET { a | is_valid a}`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET_DEF] THEN RW_TAC arith_ss [GSPECIFICATION]);

(*-----------------------------*)

val FINITEVALIDATTR = prove_thm (
  "FINITEVALIDATTR",
  (--`! (n: num) (m: num) (s: num) .FINITE { a: (bool word # (num # num # num)) |
      is_valid a /\ (attrib a = (n,m,s))}`--),
  REPEAT GEN_TAC THEN MATCH_MP_TAC  MATCHFINITEVALIDATTR THEN
  REWRITE_TAC [ISVALID_ATTR_SUB]);

(*---------------------------------*)

val ISVALID_ATTR_IMAGE = prove_thm (
  "ISVALID_ATTR_IMAGE",
  (--`! (n: num) (m: num) (s: num) .{ a:fxp | Isvalid a /\ (Attrib a = (n,m,s))} =
      IMAGE fxp { a: (bool word # (num # num # num)) | is_valid a /\ (attrib a = (n,m,s))}`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [IMAGE_DEF] THEN RW_TAC arith_ss [GSPECIFICATION] THEN
  PURE_REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL [
    RW_TAC arith_ss [GSPECIFICATION] THEN EXISTS_TAC (--`defxp (x:fxp)`--) THEN
    RW_TAC arith_ss [GSYM fxp_tybij] THENL [
      RW_TAC arith_ss [fxp_tybij], UNDISCH_TAC (--`Isvalid (x:fxp)`--) THEN
      RW_TAC arith_ss [Isvalid], UNDISCH_TAC (--`Attrib (x:fxp) = (n,m,s)`--) THEN
      RW_TAC arith_ss [Attrib]],
    RW_TAC arith_ss [GSPECIFICATION] THENL[
      UNDISCH_TAC (--`is_valid (x':(bool word #(num#num#num)))`--) THEN
      RW_TAC arith_ss [Isvalid,fxp_tybij],
      UNDISCH_TAC (--`attrib (x':(bool word #(num#num#num))) = (n,m,s)`--) THEN
      UNDISCH_TAC (--`is_valid (x':(bool word #(num#num#num)))`--) THEN
      RW_TAC arith_ss [Attrib,fxp_tybij]]]);

(*--------------------------------------*)

val FINITEFXPVALIDATTR = prove_thm (
  "FINITEFXPVALIDATTR",
  (--`! (n: num) (m: num) (s: num) .FINITE { a:fxp  | Isvalid a /\ (Attrib a = (n,m,s))}`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [ISVALID_ATTR_IMAGE,IMAGE_FINITE,FINITEVALIDATTR]);

(*--------------------------------------*)

val FINITEFXPVALIDATTRX = prove_thm (
  "FINITEFXPVALIDATTRX",
  (--`! (X: (num#num#num)) .FINITE { a:fxp  | Isvalid a /\ (Attrib a = X)}`--),
  GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN REWRITE_TAC [FINITEFXPVALIDATTR]);

(*--------------------------------------*)

val REPLICATELENGTH = prove_thm (
  "REPLICATELENGTH",
  (--`! n: num. LENGTH (REPLICATE n T) = n`--),
  INDUCT_TAC THENL [
    RW_TAC arith_ss [REPLICATE,LENGTH], RW_TAC arith_ss [REPLICATE,LENGTH]]);

(*----------------------*)

val ISVALIDREPLICATE = prove_thm (
  "ISVALIDREPLICATE",
  (--`! n: num m: num s : num. validAttr (n,m,s) ==> is_valid (WORD (REPLICATE n T),n,m,s)`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [is_valid,attrib,stream,streamlength,WORDLEN_DEF,REPLICATE,REPLICATELENGTH]);

(*-------------------------------------------*)

val ISVALIDNBWORD = prove_thm (
  "ISVALIDNBWORD",
  (--`!(n: num) (m: num) (s:num) (k:num). validAttr (n,m,s) ==> is_valid ((NBWORD n k),(n,m,s))`--),
    REPEAT GEN_TAC THEN RW_TAC arith_ss [is_valid,attrib,stream,streamlength,WORDLEN_DEF,WORDLEN_NBWORD ]);

(*-------------------------------------------*)

val DEFXP_FXP_NBWORD = prove_thm (
  "DEFXP_FXP_NBWORD",
  (--`!(n: num) (m: num) (s:num) (k:num). validAttr (n,m,s) ==> (defxp (fxp ((NBWORD n k),(n,m,s))) =
      ((NBWORD n k),(n,m,s)))`--),
  RW_TAC arith_ss [ISVALIDNBWORD, GSYM fxp_tybij]);

(*-------------------------------------------*)

val DEFXP_FXP_REPLICATE = prove_thm (
  "DEFXP_FXP_REPLICATE",
  (--`! n: num m: num s : num. validAttr (n,m,s) ==>
      (defxp (fxp (WORD (REPLICATE n T),n,m,s)) = (WORD (REPLICATE n T),n,m,s))`--),
  RW_TAC arith_ss [ISVALIDREPLICATE,GSYM fxp_tybij]);

(*-------------------------------------------*)

val IS_VALID_FXP_CLOSEST = prove_thm (
  "IS_VALID_FXP_CLOSEST",
  (--`!(v: fxp ->real) (p: fxp -> bool) (x : real) n: num m: num s : num  . validAttr (n,m,s) ==>
      Isvalid (fxp_closest v p {a: fxp | Isvalid a /\ ((Attrib a) = (n,m,s))} x)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`(fxp_closest v p {a |Isvalid a /\ (Attrib a = (n,m,s))} x) IN
  {a |Isvalid a /\ (Attrib a = (n,m,s))}`--) MP_TAC THENL [
    MATCH_MP_TAC (REWRITE_RULE [TAUT (`a ==> b
    ==> c = a /\ b ==> c`)] FXP_CLOSEST_IN_SET) THEN
    CONJ_TAC THENL [
      REWRITE_TAC [FINITEFXPVALIDATTR] ,
      REWRITE_TAC [EXTENSION] THEN
      RW_TAC arith_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
      EXISTS_TAC (--`fxp (WORD (REPLICATE (n:num) T),(n:num,m:num,s:num))`--) THEN
      RW_TAC arith_ss [Isvalid] THENL [
      RW_TAC arith_ss [is_valid] THENL [
      RW_TAC arith_ss [attrib] THEN
      UNDISCH_TAC (--`validAttr (n:num,m:num,s:num)`--) THEN
      RW_TAC arith_ss [ISVALIDREPLICATE,GSYM fxp_tybij,attrib] THEN
      RW_TAC arith_ss [DEFXP_FXP_REPLICATE,attrib] ,
      UNDISCH_TAC (--`validAttr (n:num,m:num,s:num)`--) THEN
      RW_TAC arith_ss [attrib] THEN
      RW_TAC arith_ss [DEFXP_FXP_REPLICATE] THEN
      RW_TAC arith_ss [stream,attrib,streamlength,WORDLEN_DEF,REPLICATE,REPLICATELENGTH] ],
      RW_TAC arith_ss [Attrib] THEN
      UNDISCH_TAC (--`validAttr (n:num,m:num,s:num)`--) THEN
      RW_TAC arith_ss [DEFXP_FXP_REPLICATE,attrib]]],
    RW_TAC arith_ss [GSPECIFICATION]]);

(*-------------------------------------------*)

val IS_VALID_ROUND_CONV_CLIP = prove_thm (
  "IS_VALID_ROUND_CONV_CLIP",
  (--`!n: num m: num s: num  x: real. (validAttr (n,m,s) /\ ~ (x > MAX (n,m,s)) /\
      ~ (x < MIN (n,m,s))) ==> Isvalid (FST (fxp_round (n,m,s) (Convergent) x Clip))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN RW_TAC arith_ss [fxp_round] THEN
  RW_TAC arith_ss [IS_VALID_FXP_CLOSEST]);

(*-----------------------------------*)

val ISVALISPECIAL = prove_thm (
  "ISVALISPECIAL",
  (--`is_valid (WORD (REPLICATE (2:num) (T:bool)),(2:num,1:num,1:num))`--),
  RW_TAC arith_ss [is_valid,validAttr,attrib,streamlength,stream,intbits,signtype] THEN
  RW_TAC arith_ss [is_valid,validAttr,attrib,streamlength,stream,intbits,signtype] THEN
  RW_TAC arith_ss [WORDLEN_DEF,REPLICATELENGTH]);

(*-----------------------------------*)

val DEFXP_FXP_SPECIAL = prove_thm (
  "DEFXP_FXP_SPECIAL",
  (--`defxp (fxp (WORD (REPLICATE (2:num) (T:bool)),(2:num,1:num,1:num))) =
      (WORD (REPLICATE (2:num) (T:bool)),(2:num,1:num,1:num))`--),
  RW_TAC arith_ss [GSYM fxp_tybij,ISVALISPECIAL]);

(*------------------------------------*)

val IS_VALID_NONEMPTY = prove_thm (
  "IS_VALID_NONEMPTY",
  (--`~({a: fxp| Isvalid a} = EMPTY)`--),
  RW_TAC arith_ss [EXTENSION,NOT_FORALL_THM] THEN
  EXISTS_TAC (--`fxp (WORD (REPLICATE (2:num) (T:bool)),(2:num,1:num,1:num))`--) THEN
  RW_TAC arith_ss [NOT_IN_EMPTY] THEN RW_TAC arith_ss [GSPECIFICATION ] THEN
  RW_TAC arith_ss [Isvalid,is_valid,attrib,validAttr,streamlength,stream] THENL [
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,attrib,streamlength] ,
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,attrib,streamlength] ,
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,intbits] THEN
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,attrib,signtype] THEN
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,attrib,streamlength] THEN
    RW_TAC arith_ss [intbits], RW_TAC arith_ss [DEFXP_FXP_SPECIAL,attrib,signtype],
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,attrib,streamlength] THEN
    RW_TAC arith_ss [DEFXP_FXP_SPECIAL,stream,WORDLEN_DEF,REPLICATELENGTH]]);

(*--------------------------------------*)

val IS_VALID_ATTRIB_NONEMPTY = prove_thm (
  "IS_VALID_ATTRIB_NONEMPTY",
  (--`! n:num m:num s:num. validAttr (n,m,s) ==>
      ~({a: fxp| Isvalid a /\ (Attrib a = (n,m,s))} = EMPTY)`--),
  RW_TAC arith_ss [EXTENSION,NOT_FORALL_THM] THEN
  EXISTS_TAC (--`fxp (WORD (REPLICATE (n:num) (T:bool)),(n:num,m:num,s:num))`--) THEN
  RW_TAC arith_ss [NOT_IN_EMPTY] THEN RW_TAC arith_ss [GSPECIFICATION ] THENL [
    RW_TAC arith_ss [Isvalid] THEN RW_TAC arith_ss [DEFXP_FXP_REPLICATE, ISVALIDREPLICATE],
    RW_TAC arith_ss [Attrib,DEFXP_FXP_REPLICATE,attrib]]);

(* ------------------------------------------------------------------------- *)
(* Rounding error in fixed-point arithmetic operations.                      *)
(* ------------------------------------------------------------------------- *)

val fxperror = Define `fxperror (X: (num # num # num)) (rnd: fxp_roundmode) (over: overflowmode) (x: real) =
    ((value (FST(fxp_round (X) (rnd) x over))) - x)`;

(*-------------------------------------------------------------*)

val REPLICATELENGTHF = prove_thm (
  "REPLICATELENGTHF",
  (--`! n: num. LENGTH (REPLICATE n F) = n`--),
  INDUCT_TAC THENL[
  RW_TAC arith_ss [REPLICATE,LENGTH],
  RW_TAC arith_ss [REPLICATE,LENGTH]]);

(*---------------------------------------------------*)

val ISVALIDREPLICATEF = prove_thm (
  "ISVALIDREPLICATEF",
  (--`! n: num m: num s : num. validAttr (n,m,s) ==> is_valid (WORD (REPLICATE n F),n,m,s)`--),
  REPEAT GEN_TAC THEN
  RW_TAC arith_ss [is_valid,attrib,stream,streamlength,WORDLEN_DEF,REPLICATE,REPLICATELENGTHF]);

(*---------------------------------------------------*)

val DEFXP_FXP_REPLICATEF = prove_thm ("DEFXP_FXP_REPLICATEF", (--`! n: num m: num s : num. validAttr (n,m,s) ==>
(defxp (fxp (WORD (REPLICATE n F),n,m,s)) =
(WORD (REPLICATE n F),n,m,s))`--),

RW_TAC arith_ss [ISVALIDREPLICATEF,GSYM fxp_tybij]);

(*----------------------------------------------------*)

val FXP_ADD_THM = prove_thm (
  "FXP_ADD_THM",
  (--`! a: fxp  b: fxp  n: num m: num s: num. (Isvalid a) /\ (Isvalid b) /\ validAttr (n,m,s) /\
      ~((value (a) + value (b)) > MAX (n,m,s)) /\ ~((value (a) + value (b)) < MIN (n,m,s)) ==>
      (Isvalid (FST(fxpAdd (n,m,s) Convergent Clip a b))) /\ ((value (FST(fxpAdd (n,m,s) Convergent Clip a b))) =
      (value (a: fxp)) + (value (b: fxp)) + (fxperror (n,m,s) Convergent Clip (value (a: fxp) + value (b: fxp))))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN RW_TAC arith_ss [fxpAdd, IS_VALID_ROUND_CONV_CLIP, fxperror] THENL [
    RW_TAC arith_ss [Isvalid] THEN UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN
    RW_TAC arith_ss [streamlength,DEFXP_FXP_REPLICATEF,ISVALIDREPLICATEF] ,
    UNDISCH_TAC (--`is_unsigned (n,m,s)`--) THEN UNDISCH_TAC (--`~(value a + value b < MIN (n,m,s))`--) THEN
    RW_TAC arith_ss [MIN] ,REAL_ARITH_TAC]);

(*----------------------------------------------------*)

val FXP_SUB_THM = prove_thm (
  "FXP_SUB_THM",
  (--`! a: fxp  b: fxp  n: num m: num s: num. (Isvalid a) /\ (Isvalid b) /\ validAttr (n,m,s) /\
      ~((value (a) - value (b)) > MAX (n,m,s)) /\ ~((value (a) - value (b)) < MIN (n,m,s)) ==>
      (Isvalid (FST(fxpSub (n,m,s) Convergent Clip a b))) /\ ((value (FST(fxpSub (n,m,s) Convergent Clip a b))) =
      (value (a: fxp)) - (value (b: fxp)) + (fxperror (n,m,s) Convergent Clip (value (a: fxp) - value (b: fxp))))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN RW_TAC arith_ss [fxpSub, IS_VALID_ROUND_CONV_CLIP, fxperror] THENL [
    RW_TAC arith_ss [Isvalid] THEN UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN
    RW_TAC arith_ss [streamlength,DEFXP_FXP_REPLICATEF,ISVALIDREPLICATEF], UNDISCH_TAC (--`is_unsigned (n,m,s)`--) THEN
    UNDISCH_TAC (--`~(value a - value b < MIN (n,m,s))`--) THEN RW_TAC arith_ss [MIN], REAL_ARITH_TAC]);

(*----------------------------------------------------*)

val FXP_MUL_THM = prove_thm (
  "FXP_MUL_THM",
  (--`! a: fxp  b: fxp  n: num m: num s: num. (Isvalid a) /\ (Isvalid b) /\ validAttr (n,m,s) /\
      ~((value (a) * value (b)) > MAX (n,m,s)) /\ ~((value (a) * value (b)) < MIN (n,m,s)) ==>
      (Isvalid (FST(fxpMul (n,m,s) Convergent Clip a b))) /\ ((value (FST(fxpMul (n,m,s) Convergent Clip a b))) =
      (value (a: fxp)) * (value (b: fxp)) + (fxperror (n,m,s) Convergent Clip (value (a: fxp) * value (b: fxp))))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN RW_TAC arith_ss [fxpMul, IS_VALID_ROUND_CONV_CLIP, fxperror] THENL [
    RW_TAC arith_ss [Isvalid] THEN UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN
    RW_TAC arith_ss [streamlength,DEFXP_FXP_REPLICATEF,ISVALIDREPLICATEF], UNDISCH_TAC (--`is_unsigned (n,m,s)`--) THEN
    UNDISCH_TAC (--`~(value a * value b < MIN (n,m,s))`--) THEN RW_TAC arith_ss [MIN], REAL_ARITH_TAC]);

(*----------------------------------------------------*)

val FXP_DIV_THM = prove_thm (
  "FXP_DIV_THM",
  (--`! a: fxp  b: fxp  n: num m: num s: num. (Isvalid a) /\ (Isvalid b) /\ validAttr (n,m,s) /\
      ~((value (a) / value (b)) > MAX (n,m,s)) /\ ~((value (a) / value (b)) < MIN (n,m,s)) /\ ~(value b = &0) ==>
      (Isvalid (FST(fxpDiv (n,m,s) Convergent Clip a b))) /\ ((value (FST(fxpDiv (n,m,s) Convergent Clip a b))) =
      (value (a: fxp)) / (value (b: fxp)) + (fxperror (n,m,s) Convergent Clip (value (a: fxp) / value (b: fxp))))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN RW_TAC arith_ss [fxpDiv, IS_VALID_ROUND_CONV_CLIP, fxperror] THENL [
    RW_TAC arith_ss [Isvalid] THEN UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN
    RW_TAC arith_ss [streamlength,DEFXP_FXP_REPLICATEF,ISVALIDREPLICATEF] ,
    UNDISCH_TAC (--`is_unsigned (n,m,s)`--) THEN UNDISCH_TAC (--`~(value a / value b < MIN (n,m,s))`--) THEN
    RW_TAC arith_ss [MIN],REAL_ARITH_TAC]);

(* ------------------------------------------------------------------------- *)
(* Lemmas about general fixed-point error bound theorem                      *)
(* ------------------------------------------------------------------------- *)

val FXP_BOUND_AT_WORST_LEMMA = prove_thm (
  "FXP_BOUND_AT_WORST_LEMMA",
  (--`! (a: fxp) (x: real) n: num m: num s: num. ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      Isvalid a /\ (Attrib a = (n,m,s))  ==> abs (value (FST (fxp_round (n,m,s) (Convergent) x Clip)) - x) <= abs((value a) - x)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN RW_TAC arith_ss [fxp_round] THEN
  MP_TAC (MATCH_MP FXP_CLOSEST_IS_FXP_CLOSEST (SPEC (--`(n:num,m:num,s:num)`--) FINITEFXPVALIDATTRX)) THEN
  RW_TAC arith_ss [IS_VALID_ATTRIB_NONEMPTY] THEN UNDISCH_TAC (--`!v p x'. is_fxp_closest v {a | Isvalid a /\ (Attrib a = (n,m,s))} x'
  (fxp_closest v p {a | Isvalid a /\ (Attrib a = (n,m,s))} x')`--) THEN DISCH_THEN (MP_TAC o SPEC (--`value`--)) THEN
  DISCH_THEN (MP_TAC o SPEC (--`(\a. ~LSB (Stream a))`--)) THEN DISCH_THEN (MP_TAC o SPEC (--`x:real`--)) THEN
  REWRITE_TAC [is_fxp_closest] THEN DISCH_THEN (MATCH_MP_TAC o SPEC (--`a:fxp`--) o CONJUNCT2) THEN RW_TAC arith_ss [GSPECIFICATION]);

(*-----------------------*)

val FXP_ERROR_AT_WORST_LEMMA = prove_thm (
  "FXP_ERROR_AT_WORST_LEMMA",
  (--`! (a: fxp) (x: real) n: num m: num s: num. ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      Isvalid a /\ (Attrib a = (n,m,s)) ==> abs (fxperror (n,m,s) (Convergent) (Clip) (x: real)) <= abs((value a) - x)`--),
  REWRITE_TAC [fxperror,FXP_BOUND_AT_WORST_LEMMA]);

(*-----------------------*)

val ADD_SUB2 = ONCE_REWRITE_RULE [ADD_COMM] ADD_SUB

val REAL_LT_LCANCEL_IMP = prove(
  ``!(x:real) (y:real) (z:real). &0 < x /\ x * y < x * z ==> y < z``,
  REPEAT GEN_TAC THEN DISCH_THEN (fn th => ASSUME_TAC (CONJUNCT1 th) THEN
                                           MP_TAC th) THEN
  RW_TAC arith_ss [REAL_LT_LMUL]);

(*-----------------------*)

val REAL_LE_LCANCEL_IMP = prove(
  ``!(x:real) (y:real) (z:real). &0 < x /\ x * y <= x * z ==> y <= z``,
  REPEAT GEN_TAC THEN RW_TAC arith_ss [REAL_LE_LMUL] THEN
  UNDISCH_TAC (--`((x:real) * (y:real) <= x * (z:real))`--) THEN
  UNDISCH_TAC (--`0 < (x:real)`--) THEN RW_TAC arith_ss [REAL_LE_LMUL]);

(*-----------------------*)

val REAL_OF_NUM_LT = REAL_LT

val vfracnot0 = prove(
  ``!n m s. ~ ((&2 pow fracbits (n,m,s)) = &0)``,
  REPEAT GEN_TAC THEN MATCH_MP_TAC POW_NZ THEN
  RW_TAC arith_ss [REAL_INJ])

(*---------------------------*)

val v126not0 = prove (
  ``~(2 pow 126 = 0)``,
  MATCH_MP_TAC POW_NZ THEN RW_TAC arith_ss [REAL_INJ])

(*---------------------------*)

val v23not0 = prove(
  (--` ~ ((&2 pow 23) = &0)`--),
  MATCH_MP_TAC POW_NZ THEN
  REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  RW_TAC arith_ss [SUC_NOT, REAL_NZ_IMP_LT] THEN
  RW_TAC arith_ss [REAL] THEN REAL_ARITH_TAC);

(*---------------------------*)

val invfracge0 = prove_thm (
  "invfracge0",
  (--`!(n:num) (m:num) (s:num). &0 <= inv (&2 pow fracbits (n,m,s))`--),
  RW_TAC arith_ss [REAL_LE_INV_EQ] THEN MP_TAC REAL_LE_01 THEN
  MP_TAC POW_2_LE1 THEN DISCH_THEN (MP_TAC o SPEC (--`fracbits (n,m,s)`--)) THEN
  REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN REAL_ARITH_TAC);

(*---------------------------*)

val invfracgt0 = prove_thm (
  "invfracgt0",
  (--`!(n:num) (m:num) (s:num). &0 < inv (&2 pow fracbits (n,m,s))`--),
  RW_TAC arith_ss [REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN
  REWRITE_TAC[num_CONV(--`2:num`--)] THEN RW_TAC arith_ss [SUC_NOT, REAL_NZ_IMP_LT]);

(*---------------------------*)

val vfracgt0 = prove(
  (--`!(n:num) (m:num) (s:num). &0 < (&2 pow fracbits (n,m,s))`--),
  RW_TAC arith_ss [REAL_LT, REAL_POW_LT]);

(*---------------------------*)

val v126gt0 = prove(
  (--`&0 < (&2 pow 126)`--),
  MATCH_MP_TAC REAL_POW_LT THEN
  RW_TAC arith_ss [REAL_LT]);

(*---------------------------*)

val v23gt0 = prove (
  (--`&0 < (&2 pow 23)`--),
  RW_TAC arith_ss [REAL_LT, REAL_POW_LT]);

(*-------------------------*)

val REAL_OF_NUM_GT = prove_thm (
  "REAL_OF_NUM_GT",
  (--`!(m:num) (n:num). ((&m:real) > (&n:real)) = (m > n)`--),
  REWRITE_TAC[GREATER_DEF , real_gt, REAL_OF_NUM_LT]);

(*-------------------------*)

val pwvfraclt1 = prove_thm (
  "pwvfraclt1",
  (--`!(n:num) (m:num) (s:num) (y:num). (& y / &2 pow fracbits (n,m,s)) < &1 =
      ((&2 pow fracbits (n,m,s)) * (& y / (&2 pow fracbits (n,m,s)))) < ((&2 pow fracbits (n,m,s)) * &1)`--),
  GEN_TAC THEN RW_TAC arith_ss [REAL_LT_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfracle11 = prove_thm (
  "pwvfracle11",
  (--`! (x:real) (n:num) (m:num) (s:num) . x <= (&2 pow (streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s)) =
      &2 pow fracbits (n,m,s) * x <= &2 pow fracbits (n,m,s) * (&2 pow (streamlength (n,m,s) - 1) / &2 pow fracbits (n,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LE_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfracltt1 = prove_thm (
  "pwvfracltt1",
  (--`! (x:real) (n:num) (m:num) (s:num) . x < (&2 pow (streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s)) =
      &2 pow fracbits (n,m,s) * x < &2 pow fracbits (n,m,s) * (&2 pow (streamlength (n,m,s) - 1) / &2 pow fracbits (n,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfracle1 = prove_thm (
  "pwvfracle1",
  (--`! (x:real) (n:num) (m:num) (s:num) . x <= (&2 pow streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s) =
      &2 pow fracbits (n,m,s) * x <= &2 pow fracbits (n,m,s) * ((&2 pow streamlength (n,m,s) - 1) / &2 pow fracbits (n,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LE_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfraclt2 = prove_thm (
  "pwvfraclt2",
  (--`!(x:real) (n:num) (m:num) (s:num). (& k / &2 pow fracbits (n,m,s) < x) = &2 pow fracbits (n,m,s) *
      (& k / &2 pow fracbits (n,m,s)) < &2 pow fracbits (n,m,s) * x`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfracle2 = prove_thm (
  "pwvfracle2",
  (--`!(x:real) (n:num) (m:num) (s:num). (& k / &2 pow fracbits (n,m,s) <= x) = &2 pow fracbits (n,m,s) *
      (& k / &2 pow fracbits (n,m,s)) <= &2 pow fracbits (n,m,s) * x`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LE_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfraclt21 = prove_thm (
  "pwvfraclt21",
  (--`!(x:real) (n:num) (m:num) (s:num). (& k / &2 pow fracbits (n,m,s) < x) = (&k < &2 pow fracbits (n,m,s) * x)`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [pwvfraclt2,REAL_DIV_LMUL,vfracnot0]);

(*-------------------------*)

val pwvfracle21 = prove_thm (
  "pwvfracle21",
  (--`!(x:real) (n:num) (m:num) (s:num). (& k / &2 pow fracbits (n,m,s) <= x) = (&k <= &2 pow fracbits (n,m,s) * x)`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0,pwvfracle2]);

(*-------------------------*)

val pwvfraclt111 = prove_thm (
  "pwvfraclt111",
  (--`! (x:real) (n:num) (m:num) (s:num) . x < (&2 pow (streamlength (n,m,s) - 1)) / &2 pow fracbits (n,m,s) =
      &2 pow fracbits (n,m,s) * x < (&2 pow (streamlength (n,m,s) - 1))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [pwvfracltt1,REAL_DIV_LMUL,vfracnot0]);

(*-------------------------*)

val pwvfracle111 = prove_thm (
  "pwvfracle111",
  (--`! (x:real) (n:num) (m:num) (s:num) . x <= (2 pow (streamlength (n,m,s) - 1)) / 2 pow fracbits (n,m,s) =
      &2 pow fracbits (n,m,s) * x <= (&2 pow (streamlength (n,m,s) - 1))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [pwvfracle11,REAL_DIV_LMUL,vfracnot0]);

(*-------------------------*)

val pwvfracle11 = prove_thm (
  "pwvfracle11",
  (--`! (x:real) (n:num) (m:num) (s:num) . x <= (2 pow streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s) =
      &2 pow fracbits (n,m,s) * x <= ((&2 pow streamlength (n,m,s) - 1))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [pwvfracle1,REAL_DIV_LMUL,vfracnot0]);

(*-------------------------*)

val pwv23le1 = prove_thm (
  "pwv23le1",
  (--`! (x:real) (n:num). (& n / (&2 pow 23) <= x) = ((&2 pow 23) * (& n / (&2 pow 23))) <= ((&2 pow 23) * x)`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LE_LMUL,v23gt0]);

(*-------------------------*)

val pwv23le11 = prove_thm (
  "pwv23le11",
  (--`!(x:real) (n:num). (& n / (&2 pow 23) <= x) = (& n <= ((&2 pow 23) * x))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [pwv23le1,REAL_DIV_LMUL,v23not0]);

(*-------------------------*)

val pwv23lt1 = prove_thm (
  "pwv23lt1",
  (--`!(n:num). (& n / &2 pow 23) < &1 = ((&2 pow 23) * (& n / (&2 pow 23))) < ((&2 pow 23) * &1)`--),
  GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,v23gt0]);

(*-------------------------*)

val pwvfraclt11 = prove_thm (
  "pwvfraclt11",
  (--`!(n:num) (m:num) (s:num) (y:num) . (& y / &2 pow fracbits (n,m,s)) < &1 = (& y < &2 pow fracbits (n,m,s))`--),
  GEN_TAC THEN RW_TAC arith_ss [pwvfraclt1] THEN RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN
  RW_TAC arith_ss [REAL_MUL_RID]);

(*-------------------------*)

val pwv23lt11 = prove_thm (
  "pwv23lt11",
  (--`!(x:real). (& n / &2 pow 23) < &1 = (& n < &2 pow 23)`--),
  GEN_TAC THEN RW_TAC arith_ss [pwv23lt1] THEN
  RW_TAC arith_ss [REAL_DIV_LMUL,v23not0] THEN
  RW_TAC arith_ss [REAL_MUL_RID]);

(*-------------------------*)

val pwvfraclereal = prove_thm (
  "pwvfraclereal",
  (--`!(n:num) (m:num) (s:num) (y:real). (x < (y / (&2 pow fracbits (n,m,s)))) = ((&2 pow fracbits (n,m,s)) * x) <
      ((&2 pow fracbits (n,m,s)) * (y / (&2 pow fracbits (n,m,s))))`--),
 REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,vfracgt0]);

(*-------------------------*)

val PWFLT_REAL = prove_thm (
  "PWFLT_REAL",
  (--`!(n:num) (m:num) (s:num) (y:real). (x <= (y / (&2 pow fracbits (n,m,s)))) = ((&2 pow fracbits (n,m,s)) * x) <=
      ((&2 pow fracbits (n,m,s)) * (y / (&2 pow fracbits (n,m,s))))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LE_LMUL,vfracgt0]);

(*-------------------------*)

val pwvfraclt = prove_thm (
  "pwvfraclt",
  (--`!(n:num) (m:num) (s:num) (y:num). (x < (& y / (&2 pow fracbits (n,m,s)))) = ((&2 pow fracbits (n,m,s)) * x) <
      ((&2 pow fracbits (n,m,s)) * (& y / (&2 pow fracbits (n,m,s))))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,vfracgt0]);

(*-------------------------*)

val pwv23lt = prove_thm (
  "pwv23lt",
  (--`!(x:real). (x < (& n / (&2 pow 23))) = ((&2 pow 23) * x) < ((&2 pow 23) * (& n / (&2 pow 23)))`--),
  GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,v23gt0]);

(*-------------------------*)

val pwvexpfraclt = prove_thm (
  "pwvexpfraclt",
  (--`!(n:num) (m:num) (s:num) (y:num) . (y > (2 EXP fracbits (n,m,s))) = ((&2 pow fracbits (n,m,s)) < &y)`--),
  GEN_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN
  ASM_REWRITE_TAC [GREATER_DEF,REAL_OF_NUM_LT,REAL_OF_NUM_POW]);

(*-------------------------*)

val pwvexp23lt = prove_thm (
  "pwvexp23lt",
  (--`!(n:num) . (n > (2 EXP 23)) = ((&2 pow 23) < &n)`--),
  GEN_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN
  RW_TAC arith_ss [REAL_OF_NUM_LT]);

(*-------------------------*)

val pwvexp23gt = prove_thm (
  "pwvexp23gt",
  (--`!(n:num) . (n < (2 EXP 23)) = (&n < (&2 pow 23))`--),
  GEN_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN
  RW_TAC arith_ss [REAL_OF_NUM_LT]);

(*-------------------------*)

val pwvexpfraclt1 = prove_thm (
  "pwvexpfraclt1",
  (--`!(n:num) (m:num) (s:num) (x:real) . (x < &1) = ((&2 pow fracbits (n,m,s)) * x) <
      ((&2 pow fracbits (n,m,s)) * &1)`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,vfracgt0,REAL_MUL_LID ]);

(*-------------------------*)

val pwvexp126lt1 = prove_thm (
  "pwvexp126lt1",
  (--`!(x:real) . (x < inv (&2 pow 126)) = ((&2 pow 126) * x) < ((&2 pow 126) * inv (&2 pow 126))`--),
  RW_TAC arith_ss [GSYM REAL_LT_LMUL ,v126gt0]);

(*-------------------------*)

val pwvexp126lt11 = prove_thm (
  "pwvexp126lt11",
  (--`!(x:real) . (x < inv (&2 pow 126)) = ((&2 pow 126) * x) < &1`--),
  RW_TAC arith_ss [pwvexp126lt1,GSYM real_div,REAL_DIV_REFL,v126not0]);

(*-------------------------*)

val pwvexp23lt1 = prove_thm (
  "pwvexp23lt1",
  (--`!(x:real) . (x < &1) = ((&2 pow 23) * x) < ((&2 pow 23) * &1)`--),
  GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_LT_LMUL,v23gt0,REAL_MUL_LID ]);

(*-------------------------*)

val pwvexp23lt11 = prove_thm (
  "pwvexp23lt11",
  (--`!(x:real) . (x < &1) = ((&2 pow 23) * x) < (&2 pow 23) `--),
  GEN_TAC THEN RW_TAC arith_ss [pwvexp23lt1,REAL_MUL_RID ]);

(*-------------------------*)

val twoone = prove_thm (
  "twoone",
  (--`(2:num) = (1:num) + (1:num)`--),
  REWRITE_TAC [num_CONV(--`2:num`--)] THEN
  REWRITE_TAC [ADD1]);

(*-------------------------*)

val opopow = prove_thm (
  "opopow",
  (--`! n:num m:num s:num . (0:num) < streamlength (n,m,s) ==> &1 + & (streamlength (n,m,s)) * &1 <= ((&1 :real) +
      (&1 :real)) pow streamlength ((n :num),(m :num),(s :num))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [REAL_LT_01 ,POW_PLUS1, REAL_MUL_RID]);

(*-------------------------*)

val opstream = prove_thm (
  "opstream",
  (--`! n:num m:num s:num . (0:num) < streamlength (n,m,s) ==> (&1:real) + (&0:real) < (&1:real) + &(streamlength (n,m,s)) * &1`--),
  RW_TAC arith_ss [REAL_LT_LADD,REAL_MUL_RID,REAL_OF_NUM_LT]);

(*-------------------------*)

val opstream1 = prove_thm (
  "opstream1",
  (--`! n:num m:num s:num . (0:num) < streamlength (n,m,s) ==> (&1:real) + (&0:real) < ((&1 :real) +
      (&1 :real)) pow streamlength ((n :num),(m :num),(s :num))`--),
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP opstream) THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP opopow) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN
  ASM_REWRITE_TAC [REAL_LTE_TRANS]);

(*------------------------*)

val twoexpsl = prove_thm (
  "twoexpsl",
  ``!n m s.
      validAttr (n,m,s) ==> (1 <= 2 EXP streamlength (n,m,s))``,
  REPEAT GEN_TAC THEN REWRITE_TAC [validAttr] THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_LE] THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_POW] THEN RW_TAC arith_ss [POW_2_LE1]);

(*-----------*)

val otwoexpsl = prove_thm (
  "otwoexpsl",
  (--`!n:num m:num s:num. validAttr (n,m,s) ==> (1 + (2 EXP streamlength (n,m,s) - 1) = 2 EXP streamlength (n,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [] THEN RW_TAC arith_ss [GSYM LESS_EQ_ADD_SUB ,twoexpsl]);

(*-----------*)

val otwoexpsl1 = prove_thm (
  "otwoexpsl1",
  (--`!n:num m:num s:num. (validAttr (n,m,s)) ==> (((2 EXP streamlength (n,m,s)) - 1 + 1) =
      (2 EXP streamlength (n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [SUB_ADD,twoexpsl]);

(*-----------*)

val otwoexpsl11 = prove_thm (
  "otwoexpsl11",
  (--`!n:num m:num s:num. (validAttr (n,m,s)) ==> ((&2 pow streamlength (n,m,s) - &1) =
      (& (2 EXP streamlength (n,m,s) - 1)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN
  REWRITE_TAC [REAL_EQ_SUB_RADD] THEN REWRITE_TAC [REAL_OF_NUM_ADD] THEN
  RW_TAC arith_ss [otwoexpsl1]);

(*-----------*)

val twogz = prove (
  ``!(n:num). &0 < &2 pow n``,
  MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC);

(*-----------*)

val twoexpgo = prove(
  ``! (n:num). (1:num) <= (2:num) EXP n ``,
  GEN_TAC THEN
  REWRITE_TAC [GSYM REAL_OF_NUM_LE, GSYM REAL_OF_NUM_POW, POW_2_LE1 ]);

(*--------------------------------------------*)

val s3 = prove_thm (
  "s3",
  ``!n m s.
       (2 pow (streamlength (n,m,s) - 1) - 1) * inv (2 pow fracbits (n,m,s))
              <=
       2 pow (streamlength (n,m,s) - 1) * inv (2 pow fracbits (n,m,s))``,
  REPEAT GEN_TAC THEN REWRITE_TAC [real_sub,REAL_ADD_RDISTRIB] THEN
  ONCE_REWRITE_TAC[REAL_ARITH (--`((a+b)<= a) = ((b) <= (&0:real))`--)] THEN
  REWRITE_TAC [GSYM REAL_NEG_MINUS1] THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``(~a <= 0r) = (0r <= a)``] THEN
  REWRITE_TAC [invfracge0]);

(*------------------------*)

val FXP_ERROR_BOUND_LEMMA1_UNSIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA1_UNSIGNED",
  (--`! x:real n: num m: num s: num. ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      is_unsigned (n,m,s) ==> (?(k:num) . (k < ((2 EXP streamlength (n,m,s))) /\
      (&k / (&2 pow (fracbits (n,m,s))) <= x) /\ (x < (& (SUC k) / (&2 pow (fracbits (n,m,s)))))))`--),
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC (--`\ (k:num). (&k / ((&2 pow fracbits (n,m,s)):real) <= (x:real))`--) (EXISTS_GREATEST )) THEN
  REWRITE_TAC [] THEN W(C SUBGOAL_THEN MP_TAC o lhs o lhand o snd) THENL [
    CONJ_TAC THENL [
      EXISTS_TAC (--`0:num`--) THEN RW_TAC arith_ss [REAL_MUL_LZERO,real_div] THEN
      UNDISCH_TAC (--`~(x < MIN (n,m,s))`--) THEN RW_TAC arith_ss [GSYM real_lte,MIN] ,
      EXISTS_TAC (--`((2 EXP streamlength (n,m,s)))`--) THEN X_GEN_TAC (--`k:num`--) THEN
      DISCH_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN RW_TAC arith_ss [GSYM real_lt] THEN
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (--`inv((&2) pow (fracbits (n,m,s)))`--) THEN
      RW_TAC arith_ss [] THENL [
        RW_TAC arith_ss [invfracgt0], RW_TAC arith_ss [REAL_LT_LMUL,invfracgt0]  THEN
        RW_TAC arith_ss [GSYM REAL_OF_NUM_POW] THEN RW_TAC arith_ss [pwvfraclt] THEN
        RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN UNDISCH_TAC (--`k > 2 EXP streamlength (n,m,s)`--) THEN
        REWRITE_TAC [GREATER_DEF] THEN DISCH_TAC THEN UNDISCH_TAC (--`~(x > MAX (n,m,s))`--) THEN
        REWRITE_TAC [real_gt,GSYM real_lte] THEN RW_TAC arith_ss [MAX] THEN
        UNDISCH_TAC (--`x <= (&2 pow streamlength (n,m,s) - 1) / &2 pow fracbits (n,m,s)`--) THEN
        REWRITE_TAC [pwvfracle11] THEN UNDISCH_TAC (--`2 EXP streamlength (n,m,s) < k`--) THEN
        REWRITE_TAC [GSYM REAL_OF_NUM_LT, GSYM REAL_OF_NUM_POW] THEN REAL_ARITH_TAC]],
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_THEN(MP_TAC o SPEC (--`SUC k`--)) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN EXISTS_TAC (--`k:num`--) THEN REPEAT CONJ_TAC THENL [
      RW_TAC arith_ss [GSYM REAL_OF_NUM_POW ,GSYM REAL_OF_NUM_LT ] THEN
      UNDISCH_TAC (--`(\k. & k / 2 pow fracbits (n,m,s) <= x) k`--) THEN
      UNDISCH_TAC (--`~(x > MAX (n,m,s))`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN
      RW_TAC arith_ss [MAX,real_gt, GSYM real_lte] THEN
      UNDISCH_TAC (--`x <= (2 pow streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s)`--) THEN
      UNDISCH_TAC (--`& k / 2 pow fracbits (n,m,s) <= x`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
      REWRITE_TAC [pwvfracle21,pwvfracle11] THEN
      REAL_ARITH_TAC, UNDISCH_TAC (--`(\k. & k / 2 pow fracbits (n,m,s) <= x) k`--) THEN
      RW_TAC arith_ss [],
      UNDISCH_TAC (--`(SUC k > k ==> ~(\k. & k / 2 pow fracbits (n,m,s) <= x) (SUC k))`--) THEN
      RW_TAC arith_ss [REAL_NOT_LE]]]);

(*------------------------*)

val FXP_ERROR_BOUND_LEMMA2_UNSIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA2_UNSIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num) . ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      is_unsigned (n,m,s) ==> (?(k:num) . (k <= ((2 EXP streamlength (n,m,s))) /\
      abs (x - &k / (&2 pow (fracbits (n,m,s)))) <= inv (&2 pow (fracbits (n,m,s)))))`--),
  let val lemma1 = REAL_ARITH
  (--`!a b x d. a <= x /\ x < b ==> b <= a + &2 * d ==> abs(x - a) <= d \/ abs(x - b) <= d`--) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP FXP_ERROR_BOUND_LEMMA1_UNSIGNED) THEN
  DISCH_THEN (X_CHOOSE_THEN (--`k:num`--) MP_TAC) THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN (MP_TAC o MATCH_MP lemma1) THEN
  DISCH_THEN(MP_TAC o SPEC (--`inv (&2 pow (fracbits (n,m,s)))`--)) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC, real_div, REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN RW_TAC arith_ss [REAL_LE_RMUL,invfracgt0] THEN
  REAL_ARITH_TAC, DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
  DISCH_THEN DISJ_CASES_TAC THENL [
    EXISTS_TAC (--`k:num`--) THEN ASM_REWRITE_TAC [GSYM LESS_EQ] THEN
    MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC [],
    EXISTS_TAC (--`SUC k`--) THEN ASM_REWRITE_TAC [GSYM LESS_EQ]]] end);

(*------------------------*)

val REAL_BNVAL_NBWORD = prove_thm (
  "REAL_BNVAL_NBWORD",
  (--`! (n:num) (k:num). k < 2 EXP n ==> (& (BNVAL (NBWORD n k)) = & k)`--),
  RW_TAC arith_ss [REAL_OF_NUM_EQ,BNVAL_NBWORD]);

(*------------------------*)

val NOTiIsigned = prove_thm (
  "NOTiIsigned",
  (--`!(n: num) (m: num) (s: num) (k:num). validAttr (n,m,s) /\ ~ is_unsigned (n,m,s) ==>
      ~ Isunsigned (fxp ((NBWORD n k),(n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [Isunsigned,DEFXP_FXP_NBWORD] THEN
  RW_TAC arith_ss [Attrib,DEFXP_FXP_NBWORD] THEN RW_TAC arith_ss [attrib]);

(*------------------------*)

val iIsigned = prove_thm (
  "iIsigned",
  (--`!(n: num) (m: num) (s: num) (k:num). validAttr (n,m,s) /\ is_unsigned (n,m,s) ==>
      Isunsigned (fxp ((NBWORD n k),(n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [Isunsigned,DEFXP_FXP_NBWORD] THEN
  RW_TAC arith_ss [Attrib,DEFXP_FXP_NBWORD] THEN RW_TAC arith_ss [attrib]);

(*------------------------*)

val TWOEXP = prove_thm (
  "TWOEXP",
  (--`! (n:num). (2 EXP n - 1) < 2 EXP n`--),
  GEN_TAC THEN RW_TAC arith_ss [] THEN
  REWRITE_TAC [num_CONV(--`2:num`--)] THEN
  RW_TAC arith_ss[ZERO_LESS_EXP]);

(*------------------------*)

val TWOEXPGE1 = prove_thm (
  "TWOEXPGE1",
  (--`! (n:num). 1 <= 2 EXP n`--),
  GEN_TAC THEN RW_TAC arith_ss [GSYM REAL_OF_NUM_LE, GSYM REAL_OF_NUM_POW] THEN
  RW_TAC arith_ss [POW_2_LE1]);

(*------------------------*)

val ADD_SUB2 = prove_thm (
  "ADD_SUB2",
  (--`!(m:num) (n:num). (m + n) - m = n`--),
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_ACCEPT_TAC ADD_SUB);

(*------------------------*)

val REAL_OF_NUM_SUB = prove_thm (
  "REAL_OF_NUM_SUB",
  (--`!(m:num) (n:num). m <= n ==> ((&n:real) - (&m:real) = &(n - m))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ADD_SUB2] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC] THEN
  MESON_TAC[REAL_ADD_LINV, REAL_ADD_SYM, REAL_ADD_LID]);

(*------------------------*)

val TWOEXPONM = prove(
  (--`! (n:num). & (2 EXP n - 1) = &(2 EXP n) - (&1:real)`--),
  RW_TAC arith_ss [GSYM REAL_OF_NUM_SUB,TWOEXPGE1 ]);

(*------------------------*)

val A1 = prove(
  ``!n m s x.
      (x - 2 pow n * inv (2 pow fracbits (n,m,s)) -
       inv (2 pow fracbits (n,m,s))
          <=
       x - (2 pow n * inv (2 pow fracbits (n,m,s))) + 0)
    =
      ~inv (2 pow fracbits (n,m,s)) <= 0 ``,
  REPEAT GEN_TAC THEN REWRITE_TAC [real_sub] THEN
  RW_TAC arith_ss [REAL_LE_LADD]);

(*------------------------*)

val A2 = prove(
  ``! (n:num) (m:num) (s:num) (x:real) . (x - &2 pow n * inv (&2 pow fracbits (n,m,s)) -
      inv (&2 pow fracbits (n,m,s)) <= x - (&2 pow n * inv (&2 pow fracbits (n,m,s)))) =
      ~ inv (&2 pow fracbits (n,m,s)) <= &0 ``,
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);

(*------------------------*)

val B1 = prove (
  (--`!(n:num). ~((& (2 EXP n) + ~1)) = ~& (2 EXP n) + (&1:real)`--),
  RW_TAC arith_ss [REAL_NEG_ADD,REAL_NEG_NEG]);

(*------------------------*)

val B2 = prove_thm (
  "B2",
  (--`! (n:num) (m:num) (s:num) (x:real) . (x - ((&2:real) pow n) * inv ((&2:real) pow fracbits (n,m,s))) <=
      (x - ((&2:real) pow n * inv ((&2:real) pow fracbits (n,m,s)) - inv ((&2:real) pow fracbits (n,m,s))))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [REAL_ARITH (--` (a:real)-(b-c) = (a-b)+c`--)] THEN
  REWRITE_TAC [REAL_ARITH (--` (a:real) <= a + b = 0 <= b`--)] THEN RW_TAC arith_ss [invfracge0]);

(*------------------------*)

val B3 = prove(
  (--`! (n:num) (m:num) (s:num). (&2 pow n * inv (&2 pow fracbits (n,m,s)) + ~inv (&2 pow fracbits (n,m,s)) <=
      &2 pow n * inv (2 pow fracbits (n,m,s))) = ~inv (&2 pow fracbits (n,m,s)) <= &0 `--),
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);

(*------------------------*)

val B4 = prove_thm (
  "B4",
  (--`! (n:num) (m:num) (s:num). (2 pow n - 1) / 2 pow fracbits (n,m,s) <= 2 pow n * inv (2 pow fracbits (n,m,s))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [real_div] THEN REWRITE_TAC [real_sub] THEN RW_TAC arith_ss [REAL_NEG_LMUL,B1] THEN
  REWRITE_TAC [REAL_ADD_RDISTRIB] THEN REWRITE_TAC [GSYM REAL_NEG_MINUS1] THEN REWRITE_TAC [B3] THEN
  REWRITE_TAC [REAL_NEG_LE0] THEN REWRITE_TAC [invfracge0]);

(*------------------------*)

val FXP_ERROR_BOUND_LEMMA3_UNSIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA3_UNSIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      is_unsigned (n,m,s) ==> (?(w:bool word) . abs (value (fxp (w,(n,m,s))) - x) <= inv (&2 pow (fracbits (n,m,s))) /\
      (WORDLEN (w) = n))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP FXP_ERROR_BOUND_LEMMA2_UNSIGNED) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) MP_TAC) THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[LESS_OR_EQ ]) THENL [
    EXISTS_TAC (--`(NBWORD n k)`--) THEN RW_TAC arith_ss [value,iIsigned] THENL [
      RW_TAC arith_ss [Stream] THEN UNDISCH_TAC (--`k < 2 EXP streamlength (n,m,s)`--) THEN
      REWRITE_TAC [streamlength] THEN RW_TAC arith_ss [DEFXP_FXP_NBWORD] THEN
      REWRITE_TAC [stream] THEN RW_TAC arith_ss [BNVAL_NBWORD,REAL_OF_NUM_EQ,streamlength] THEN
      RW_TAC arith_ss [Fracbits,Attrib,DEFXP_FXP_NBWORD] THEN REWRITE_TAC [attrib] THEN
      RW_TAC arith_ss [ABS_SUB], RW_TAC arith_ss [WORDLEN_NBWORD]],
    EXISTS_TAC (--`(NBWORD n (k-1))`--) THEN RW_TAC arith_ss [value,iIsigned] THENL [
      RW_TAC arith_ss [Stream] THEN RW_TAC arith_ss [DEFXP_FXP_NBWORD] THEN
      RW_TAC arith_ss [stream] THEN REWRITE_TAC [streamlength] THEN
      RW_TAC arith_ss [Fracbits] THEN RW_TAC arith_ss [Attrib] THEN
      RW_TAC arith_ss [DEFXP_FXP_NBWORD] THEN RW_TAC arith_ss [attrib] THEN
      RW_TAC arith_ss [ABS_SUB] THEN RW_TAC arith_ss [BNVAL_NBWORD,TWOEXP] THEN
      UNDISCH_TAC (--`abs (x - & (2 EXP streamlength (n,m,s)) / 2 pow fracbits (n,m,s)) <=
      inv (2 pow fracbits (n,m,s))`--) THEN REWRITE_TAC [streamlength] THEN
      REWRITE_TAC [ABS_BOUNDS] THEN ASM_REWRITE_TAC [TWOEXPONM] THEN
      ASM_REWRITE_TAC [GSYM REAL_OF_NUM_POW] THEN REWRITE_TAC [real_div] THEN
      REWRITE_TAC [real_sub] THEN REWRITE_TAC [REAL_ADD_RDISTRIB] THEN
      REWRITE_TAC [GSYM real_sub,REAL_MUL_LNEG ] THEN REWRITE_TAC [REAL_MUL_LID] THEN
      RW_TAC arith_ss [] THENL [
        UNDISCH_TAC (--`~inv (2 pow fracbits (n,m,s)) <= x - &2 pow n * inv (2 pow fracbits (n,m,s))`--) THEN
        MP_TAC B2  THEN DISCH_THEN (MP_TAC o SPEC_ALL) THEN REWRITE_TAC [GSYM real_sub] THEN
        REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN REAL_ARITH_TAC,
        UNDISCH_TAC (--`~(x > MAX (n,m,s))`--) THEN
        RW_TAC arith_ss [MAX,real_gt, GSYM real_lte,streamlength,GSYM REAL_OF_NUM_POW] THEN
        UNDISCH_TAC (--`x <= (2 pow n - 1) / 2 pow fracbits (n,m,s)`--) THEN MP_TAC B4 THEN
        DISCH_THEN (MP_TAC o SPEC_ALL) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN
        REAL_ARITH_TAC],
      RW_TAC arith_ss [WORDLEN_NBWORD]]]);

(*--------------------------------------------*)

val REAL_ABS_NUM = SPEC_ALL realTheory.ABS_N

val REAL_ABS_POW = GSYM realTheory.POW_ABS

(*-------------------------------------------*)

val ISVALIDWORDLEN = prove_thm (
  "ISVALIDWORDLEN",
  (--`! (w: bool word) (m: num) (s:num). validAttr (WORDLEN w ,m,s) ==> is_valid (w, (WORDLEN w,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [is_valid,attrib,stream,streamlength]);

(*-------------------------------------------*)

val DEFXP_FXP_WORDLEN = prove_thm (
  "DEFXP_FXP_WORDLEN",
  (--`! (w: bool word) (m: num) (s:num). validAttr (WORDLEN w ,m,s) ==> (defxp (fxp (w,(WORDLEN w,m,s))) =
      (w ,(WORDLEN w,m,s)))`--),
  RW_TAC arith_ss [ISVALIDWORDLEN, GSYM fxp_tybij]);

(*-------------------------------------------*)

val FXP_MAIN_ERROR_BOUND_THEOREM_UNSIGNED = prove_thm (
  "FXP_MAIN_ERROR_BOUND_THEOREM_UNSIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      is_unsigned (n,m,s) ==> abs (fxperror (n,m,s) (Convergent) (Clip) x) <= (inv (&2 pow (fracbits (n,m,s))))`--),
  REPEAT STRIP_TAC THEN SUBGOAL_THEN (--`? (a:fxp). Isvalid a /\ (Attrib a = (n,m,s)) /\ abs(value a - x) <=
  (inv (&2 pow (fracbits (n,m,s))))`--) CHOOSE_TAC THENL [
    MP_TAC FXP_ERROR_BOUND_LEMMA3_UNSIGNED THEN DISCH_THEN (MP_TAC o SPEC_ALL) THEN
    RW_TAC arith_ss [] THEN EXISTS_TAC (--`fxp (w,WORDLEN w,m,s)`--) THEN
    RW_TAC arith_ss [] THENL [
      RW_TAC arith_ss [Isvalid] THEN RW_TAC arith_ss [DEFXP_FXP_WORDLEN,is_valid] THENL [
        RW_TAC arith_ss [attrib], RW_TAC arith_ss [attrib,streamlength,stream]],
      RW_TAC arith_ss [Attrib] THEN
      RW_TAC arith_ss [DEFXP_FXP_WORDLEN,attrib]],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(value a - x)`--) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FXP_ERROR_AT_WORST_LEMMA THEN
    ASM_REWRITE_TAC []]);

(*-------------------------*)

val FXP_ERROR_BOUND_LEMMA1_POS_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA1_POS_SIGNED",
  ``! (x:real) (n: num) (m: num) (s: num).
         0r <= x /\ (x <= (2r pow (streamlength (n,m,s) - 1)) /
                           2r pow fracbits (n,m,s)) /\
         validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==>
         ? (k:num). k < (2 EXP (streamlength (n,m,s) - 1)) /\
                    (&k:real) / (&2 pow (fracbits (n,m,s))) <= x /\
                    x <= (& (SUC k) / (2r pow (fracbits (n,m,s))))``,
  REPEAT STRIP_TAC THEN
  Cases_on
    `x = (2r pow (streamlength (n,m,s) - 1)) / (2r pow fracbits (n,m,s))`
  THENL [
    EXISTS_TAC (--`2 EXP (streamlength (n,m,s) - 1) - 1`--) THEN
    REWRITE_TAC [streamlength] THEN Cases_on `n` THENL [
      RW_TAC arith_ss [] THENL [
        REWRITE_TAC [GSYM REAL_OF_NUM_LT, GSYM REAL_OF_NUM_POW] THEN
        RW_TAC arith_ss [POW_2_LT] THEN
        REWRITE_TAC [streamlength] THEN RW_TAC arith_ss [PWFLT_REAL] THEN
        RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN
        RW_TAC arith_ss [EXP ] THEN MP_TAC twogz THEN
        DISCH_THEN(MP_TAC o SPEC (--`0 : num`--)) THEN
        REWRITE_TAC [REAL_LT_IMP_LE],

        RW_TAC arith_ss [EXP ] THEN REWRITE_TAC [streamlength] THEN
        RW_TAC arith_ss [PWFLT_REAL] THEN
        RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN
        RW_TAC arith_ss [pow] THEN
        RW_TAC arith_ss [REAL_OF_NUM_LE]
      ],
      RW_TAC arith_ss [] THENL [
        REWRITE_TAC [streamlength] THEN
        RW_TAC arith_ss [PWFLT_REAL] THEN
        RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN
        RW_TAC arith_ss [REAL_OF_NUM_LE,REAL_OF_NUM_POW],

        RW_TAC arith_ss [PWFLT_REAL] THEN
        RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN
        REWRITE_TAC [streamlength] THEN
        REWRITE_TAC [SUC_SUB1] THEN REWRITE_TAC [SUC_ONE_ADD] THEN
        RW_TAC arith_ss [GSYM REAL_OF_NUM_ADD] THEN
        RW_TAC arith_ss [twoexpgo,GSYM REAL_OF_NUM_SUB] THEN
        ONCE_REWRITE_TAC[REAL_ARITH (--`((a:real) + (b - a)) = b`--)] THEN
        RW_TAC arith_ss [GSYM REAL_OF_NUM_POW] THEN REAL_ARITH_TAC
      ]
    ],
    MP_TAC(SPEC (--`\ (k:num). ((&k:real) / ((2r pow fracbits (n,m,s)):real) <= (x:real))`--) (EXISTS_GREATEST )) THEN
    REWRITE_TAC [] THEN W(C SUBGOAL_THEN MP_TAC o lhs o lhand o snd) THENL [
      CONJ_TAC THENL [
        EXISTS_TAC (--`0:num`--) THEN RW_TAC arith_ss [REAL_MUL_LZERO,real_div],
        EXISTS_TAC (--`(2 EXP (streamlength (n,m,s) - 1))`--) THEN
        X_GEN_TAC (--`k:num`--) THEN DISCH_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN
        RW_TAC arith_ss [GSYM real_lt] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
        EXISTS_TAC (--`inv(2r pow (fracbits (n,m,s)))`--) THEN RW_TAC arith_ss [] THENL [
          RW_TAC arith_ss [invfracgt0], RW_TAC arith_ss [REAL_LT_LMUL,invfracgt0] THEN
          RW_TAC arith_ss [GSYM REAL_OF_NUM_POW] THEN RW_TAC arith_ss [pwvfraclt] THEN
          RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN UNDISCH_TAC (--`k > 2 EXP (streamlength (n,m,s)-1)`--) THEN
          REWRITE_TAC [GREATER_DEF] THEN DISCH_TAC THEN
          UNDISCH_TAC (--`x <= (2r pow (streamlength (n,m,s) - 1) / 2r pow fracbits (n,m,s))`--) THEN
          REWRITE_TAC [pwvfracle111] THEN UNDISCH_TAC (--`2 EXP (streamlength (n,m,s)-1) < k`--) THEN
          REWRITE_TAC [GSYM REAL_OF_NUM_LT, GSYM REAL_OF_NUM_POW] THEN REAL_ARITH_TAC]],
      DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_THEN(MP_TAC o SPEC (--`SUC k`--)) THEN
      REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN EXISTS_TAC (--`k:num`--) THEN REPEAT CONJ_TAC THENL [
        RW_TAC arith_ss [GSYM REAL_OF_NUM_POW ,GSYM REAL_OF_NUM_LT ] THEN RW_TAC arith_ss [GSYM otwoexpsl11] THEN
        UNDISCH_TAC (--`(\k. (& k:real) / (&2 :real) pow fracbits (n,m,s) <= x) k`--) THEN
        UNDISCH_TAC (--` x <= 2r pow (streamlength (n,m,s) - 1) / 2r pow fracbits (n,m,s)`--) THEN
        REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN RW_TAC arith_ss [real_gt, GSYM real_lte] THEN
        UNDISCH_TAC (--`x <= (2r pow (streamlength (n,m,s) - 1) / 2r pow fracbits (n,m,s))`--) THEN
        REWRITE_TAC[REAL_LE_LT] THEN
        UNDISCH_TAC (--`~(x = 2r pow (streamlength (n,m,s) - 1) / 2r pow fracbits (n,m,s))`--) THEN
        RW_TAC arith_ss [] THEN
        UNDISCH_TAC (--`x < (2r pow (streamlength (n,m,s) - 1) / 2r pow fracbits (n,m,s))`--) THEN
        UNDISCH_TAC (--`(& k / 2r pow fracbits (n,m,s) <= x)`--) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
        REWRITE_TAC [pwvfracle21,pwvfraclt111] THEN REAL_ARITH_TAC, UNDISCH_TAC (--`(\k. & k / 2r pow fracbits (n,m,s) <= x) k`--) THEN
        RW_TAC arith_ss [], UNDISCH_TAC (--`SUC k > k ==> ~(\k. & k / 2r pow fracbits (n,m,s) <= x) (SUC k)`--) THEN
        RW_TAC arith_ss [] THEN UNDISCH_TAC (--`~(& (SUC k) / 2r pow fracbits (n,m,s) <= x)`--) THEN
        REWRITE_TAC [REAL_NOT_LE] THEN REWRITE_TAC [REAL_LT_IMP_LE]]]]);

(*---------------------------------------*)

val FXP_ERROR_BOUND_LEMMA1_NEG_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA1_NEG_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). (&0 <= ~x) /\ (~x <= (&2 pow (streamlength (n,m,s) - 1)) /
      &2 pow fracbits (n,m,s)) /\ validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==>
      (?(k:num) . (k < (2 EXP (streamlength (n,m,s) - 1))) /\ (& (k) / (&2 pow (fracbits (n,m,s))) <= ~x) /\
      (~x <= (& (SUC k) / (&2 pow (fracbits (n,m,s))))))`--),
  REPEAT GEN_TAC THEN MP_TAC FXP_ERROR_BOUND_LEMMA1_POS_SIGNED THEN DISCH_THEN (MP_TAC o SPEC (--`(~x:real)`--)) THEN
  DISCH_THEN (MP_TAC o SPEC_ALL) THEN REWRITE_TAC []);

(*------------------------------------------*)

val FXP_ERROR_BOUND_LEMMA2_POS_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA2_POS_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). (&0 <= x) /\ (x <= (&2 pow (streamlength (n,m,s) - 1)) /
      &2 pow fracbits (n,m,s)) /\ validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==>
      (?(k:num) . (k < (2 EXP (streamlength (n,m,s) - 1))) /\ abs (x - &k / (&2 pow (fracbits (n,m,s)))) <=
      inv (&2 pow (fracbits (n,m,s))))`--),
  let val lemma4 = REAL_ARITH (--`!a b x d. a <= x /\ x <= b ==> b <= a + d ==> abs(x - a) <= d`--) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP FXP_ERROR_BOUND_LEMMA1_POS_SIGNED) THEN
  DISCH_THEN (X_CHOOSE_THEN (--`(k:num)`--) MP_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN (MP_TAC o MATCH_MP lemma4) THEN DISCH_THEN(MP_TAC o SPEC (--`inv (&2 pow (fracbits (n,m,s)))`--)) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC, real_div, REAL_ADD_RDISTRIB] THEN REWRITE_TAC[REAL_LE_LADD] THEN
    RW_TAC arith_ss [REAL_LE_RMUL,invfracgt0] THEN REAL_ARITH_TAC, DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
    DISCH_TAC THEN EXISTS_TAC (--`k:num`--) THEN ASM_REWRITE_TAC [GSYM LESS_EQ]] end );

(*------------------------*)

val FXP_ERROR_BOUND_LEMMA2_NEG_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA2_NEG_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). (&0 <= ~x) /\ (~x <= (&2 pow (streamlength (n,m,s) - 1)) /
      &2 pow fracbits (n,m,s)) /\ validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==>
      (?(k:num) . (k < (2 EXP (streamlength (n,m,s) - 1))) /\ abs (~(&k / (&2 pow (fracbits (n,m,s)))) - x) <=
      inv (&2 pow (fracbits (n,m,s))))`--),
  let val lemma5 = REAL_ARITH (--`!a b x d. a <= ~x /\ ~x <= b ==> b <= a + d ==> abs(~a - x) <= d`--) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP FXP_ERROR_BOUND_LEMMA1_NEG_SIGNED) THEN
  DISCH_THEN (X_CHOOSE_THEN (--`(k:num)`--) MP_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN (MP_TAC o MATCH_MP lemma5) THEN DISCH_THEN(MP_TAC o SPEC (--`inv (&2 pow (fracbits (n,m,s)))`--)) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC, real_div, REAL_ADD_RDISTRIB] THEN REWRITE_TAC[REAL_LE_LADD] THEN
    RW_TAC arith_ss [REAL_LE_RMUL,invfracgt0] THEN REAL_ARITH_TAC, DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
    DISCH_TAC THEN EXISTS_TAC (--`k:num`--) THEN ASM_REWRITE_TAC [GSYM LESS_EQ] ] end );

(*-------------------------------------------*)

val ISVALID_WCATT = prove_thm (
  "ISVALID_WCATT",
  (--`! n m s k. validAttr (n,m,s) ==> is_valid (WCAT (WORD [T],NBWORD (n - 1) k),(n,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [is_valid,attrib,stream,streamlength] THEN
  REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN REWRITE_TAC [WORDLEN_DEF] THEN
  REWRITE_TAC [LENGTH] THEN REWRITE_TAC [GSYM WORDLEN_DEF] THEN REWRITE_TAC [GSYM NBWORD_DEF] THEN
  REWRITE_TAC [WORDLEN_NBWORD] THEN RW_TAC arith_ss [SUC_ONE_ADD] THEN RW_TAC arith_ss [SUB_LEFT_ADD] THEN
  UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN RW_TAC arith_ss [validAttr,streamlength]);

(*----------------------------------*)

val ISVALID_WCAT = prove_thm (
  "ISVALID_WCAT",
  (--`! n m s k. validAttr (n,m,s) ==> is_valid (WCAT (WORD [F],NBWORD (n - 1) k),(n,m,s))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [is_valid,attrib,stream,streamlength] THEN
  REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN REWRITE_TAC [WORDLEN_DEF] THEN
  REWRITE_TAC [LENGTH] THEN REWRITE_TAC [GSYM WORDLEN_DEF] THEN REWRITE_TAC [GSYM NBWORD_DEF] THEN
  REWRITE_TAC [WORDLEN_NBWORD] THEN RW_TAC arith_ss [SUC_ONE_ADD] THEN RW_TAC arith_ss [SUB_LEFT_ADD] THEN
  UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN RW_TAC arith_ss [validAttr,streamlength]);

(*-------------------*)

val DEFXP_FXP_WCATT = prove_thm (
  "DEFXP_FXP_WCATT",
  (--`!(w: bool word) (n:num) (m: num) (s:num) (k:num). validAttr (n,m,s) ==>
      ((defxp (fxp(WCAT (WORD [T],NBWORD (n - 1) k),(n,m,s))))  = (WCAT (WORD [T],NBWORD (n - 1) k),(n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [ISVALID_WCATT, GSYM fxp_tybij]);

(*------------------*)

val DEFXP_FXP_WCAT = prove_thm (
  "DEFXP_FXP_WCAT",
  (--`! (w: bool word) (n:num) (m: num) (s:num) (k:num). validAttr (n,m,s) ==>
      ((defxp (fxp(WCAT (WORD [F],NBWORD (n - 1) k),(n,m,s))))  = (WCAT (WORD [F],NBWORD (n - 1) k),(n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [ISVALID_WCAT, GSYM fxp_tybij]);

(*--------------------*)

val LASTN1 = prove_thm (
  "LASTN1",
  (--`!(n:num) (k:num). LASTN (n) (F::NLIST (n) VB 2 k) = LASTN (n) (NLIST (n) VB 2 k)`--),
  REPEAT GEN_TAC THEN MATCH_MP_TAC LASTN_CONS THEN REWRITE_TAC [GSYM WORDLEN_DEF] THEN
  REWRITE_TAC [GSYM NBWORD_DEF] THEN RW_TAC arith_ss [WORDLEN_NBWORD]);

(*--------------------*)

val NOTTiIsigned = prove_thm (
  "NOTTiIsigned",
  (--`!(n: num) (m: num) (s: num) (k:num). validAttr (n,m,s) /\ ~ is_unsigned (n,m,s) ==>
  ~ Isunsigned (fxp (WCAT (WORD [T],NBWORD (n - 1) k),(n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [Isunsigned,DEFXP_FXP_WCATT] THEN
  RW_TAC arith_ss [Attrib,DEFXP_FXP_WCATT] THEN RW_TAC arith_ss [attrib]);

(*-----------------------------*)

val NOTiIsigned = prove_thm (
  "NOTiIsigned",
  (--`!(n: num) (m: num) (s: num) (k:num). validAttr (n,m,s) /\ ~ is_unsigned (n,m,s) ==>
  ~ Isunsigned (fxp (WCAT (WORD [F],NBWORD (n - 1) k),(n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [Isunsigned,DEFXP_FXP_WCAT] THEN
  RW_TAC arith_ss [Attrib,DEFXP_FXP_WCAT] THEN RW_TAC arith_ss [attrib]);

(*------------------------*)

val PWLGSNBW = prove_thm (
  "PWLGSNBW",
  (--`! (n:num) (k:num) .(WORD (NLIST (n) VB (2:num) k) IN PWORDLEN n)`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [GSYM NBWORD_DEF,PWORDLEN_NBWORD]);

(*------------------------*)

val PWL1 = prove_thm (
  "PWL1",
  (--`(WORD [F] IN PWORDLEN 1)`--),
  REWRITE_TAC [PWORDLEN1]);

(*------------------------*)

val BNVAL_WCAT2_SPLIT = prove_thm (
  "BNVAL_WCAT2_SPLIT",
  (--`!(n:num) (w:bool word) x . (w IN PWORDLEN n) ==> (BNVAL (WCAT (WORD [x],w)) = BV x * 2 EXP n + BNVAL w)`--),
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN MP_TAC BNVAL_WCAT2 THEN REWRITE_TAC [RES_FORALL] THEN
  DISCH_THEN (MP_TAC o SPEC (--`n:num`--)) THEN DISCH_THEN (MP_TAC o SPEC (--`w:bool word`--)) THEN
  RW_TAC arith_ss []);

(*--------------------------*)

val BNVAL_WCATT_NBWORD = prove_thm (
  "BNVAL_WCATT_NBWORD",
  (--`! (n:num) k.(BNVAL (WCAT (WORD [T],NBWORD (n - 1) k)) = BV T * 2 EXP (n-1) + BNVAL (NBWORD (n - 1) k))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [NBWORD_DEF] THEN MP_TAC BNVAL_WCAT2_SPLIT THEN
  DISCH_THEN (MP_TAC o SPEC (--`(n-1):num`--)) THEN DISCH_THEN (MP_TAC o SPEC (--`WORD (NLIST (n - 1) VB 2 k)`--)) THEN
  DISCH_THEN (MP_TAC o SPEC (--`T`--)) THEN RW_TAC arith_ss [PWLGSNBW]);

(*---------------------------*)

val BNVAL_WCAT_NBWORD = prove_thm (
  "BNVAL_WCAT_NBWORD",
  (--`! (n:num) k.(BNVAL (WCAT (WORD [F],NBWORD (n - 1) k)) = BV F * 2 EXP (n-1) + BNVAL (NBWORD (n - 1) k))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [NBWORD_DEF] THEN MP_TAC BNVAL_WCAT2_SPLIT THEN
  DISCH_THEN (MP_TAC o SPEC (--`(n-1):num`--)) THEN DISCH_THEN (MP_TAC o SPEC (--`WORD (NLIST (n - 1) VB 2 k)`--)) THEN
  DISCH_THEN (MP_TAC o SPEC (--`F`--)) THEN RW_TAC arith_ss [PWLGSNBW]);

(*--------------------------------------*)

val FXP_ERROR_BOUND_LEMMA3_POS_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA3_POS_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). (&0 <= x) /\ (x <= (&2 pow (streamlength (n,m,s) - 1)) /
      &2 pow fracbits (n,m,s)) /\ validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==>
      (? (w:bool word) . abs (value (fxp (w,(n,m,s))) - x) <= inv (&2 pow (fracbits (n,m,s))) /\ (WORDLEN (w) = n))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP FXP_ERROR_BOUND_LEMMA2_POS_SIGNED) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) MP_TAC) THEN STRIP_TAC THEN EXISTS_TAC (--`(WCAT (WORD [F], NBWORD (n-1) k))`--) THEN
  UNDISCH_TAC (--`0 <= x /\ x <= 2 pow (streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s) /\ validAttr (n,m,s) /\ ~is_unsigned (n,m,s)`--) THEN
  REPEAT STRIP_TAC THENL [
    UNDISCH_TAC (--`~is_unsigned ((n :num),(m :num),(s :num))`--) THEN UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN
    REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN RW_TAC arith_ss [value,NOTiIsigned] THEN
    RW_TAC arith_ss [Fracbits,fracbits,Attrib,attrib,streamlength,Streamlength,Stream, DEFXP_FXP_WCAT,stream,intbits] THEN
    RW_TAC arith_ss [BNVAL_WCAT_NBWORD] THEN UNDISCH_TAC (--`k < 2 EXP (streamlength (n,m,s) - 1)`--) THEN
    REWRITE_TAC [streamlength] THEN RW_TAC arith_ss [BNVAL_NBWORD] THEN REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN
    REWRITE_TAC [MSB_DEF] THEN REWRITE_TAC [HD] THEN REWRITE_TAC [BV_DEF] THEN RW_TAC arith_ss [MULT_CLAUSES] THEN
    UNDISCH_TAC (--`abs (x - & k / &2 pow fracbits (n,m,s)) <= inv (&2 pow fracbits (n,m,s))`--) THEN
    RW_TAC arith_ss [fracbits,intbits,streamlength,ABS_SUB,REAL_SUB_RZERO], REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN
    REWRITE_TAC [WORDLEN_DEF] THEN REWRITE_TAC [LENGTH] THEN REWRITE_TAC [GSYM WORDLEN_DEF] THEN REWRITE_TAC [GSYM NBWORD_DEF] THEN
    REWRITE_TAC [WORDLEN_NBWORD] THEN RW_TAC arith_ss [SUC_ONE_ADD] THEN RW_TAC arith_ss [SUB_LEFT_ADD] THEN
    UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN RW_TAC arith_ss [validAttr,streamlength]]);

(*-----------------------------------*)

val lessneg = prove(
  (--`!(n:num) (k:num). (0 < k) /\ (k < n) ==> (n - k) < n`--),
  RW_TAC arith_ss []);

(*-----------------------------------*)

val exp1 = prove(
  (--`!(n:num). 2 * 2 EXP (n - 1) = 2 EXP 1 * 2 EXP (n - 1)`--),
  GEN_TAC THEN RW_TAC arith_ss [EXP_1]);

(*----------------------------------*)

val exp2 = prove(
  (--`!(n:num). (0 < n) ==> (((2:num) EXP n) = ((2:num) EXP (n-1) + (2:num) EXP (n-1)))`--),
  GEN_TAC THEN RW_TAC arith_ss [] THEN RW_TAC arith_ss [exp1 ,GSYM EXP_ADD]);

(*---------------------------------*)

val FXP_ERROR_BOUND_LEMMA3_NEG_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA3_NEG_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). (&0 <= ~x) /\ (~x <= (2r pow (streamlength (n,m,s) - 1)) /
      2r pow fracbits (n,m,s)) /\ validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==>
      (?(w:bool word) . abs (value (fxp (w,(n,m,s))) - x) <= inv (&2 pow (fracbits (n,m,s))) /\ (WORDLEN (w) = n))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP FXP_ERROR_BOUND_LEMMA2_NEG_SIGNED) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) MP_TAC) THEN STRIP_TAC THEN Cases_on `k` THENL [
    EXISTS_TAC (--`(WCAT (WORD [F], NBWORD (n-1) (0)))`--) THEN
    UNDISCH_TAC (--`0 <= ~x /\ ~x <= 2 pow (streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s) /\
    validAttr (n,m,s) /\ ~is_unsigned (n,m,s)`--) THEN REPEAT STRIP_TAC THENL [
      UNDISCH_TAC (--`~is_unsigned ((n :num),(m :num),(s :num))`--) THEN
      UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
      RW_TAC arith_ss [value,NOTiIsigned] THEN
      RW_TAC arith_ss [Fracbits,fracbits,Attrib,attrib,streamlength,Streamlength,Stream,DEFXP_FXP_WCAT,stream,intbits] THEN
      RW_TAC arith_ss [BNVAL_WCAT_NBWORD] THEN UNDISCH_TAC (--`0 < 2 EXP (streamlength (n,m,s) - 1)`--) THEN
      REWRITE_TAC [streamlength] THEN REWRITE_TAC [GSYM REAL_OF_NUM_ADD] THEN RW_TAC arith_ss [BNVAL_NBWORD] THEN
      REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN REWRITE_TAC [MSB_DEF] THEN REWRITE_TAC [HD] THEN
      REWRITE_TAC [BV_DEF] THEN RW_TAC arith_ss [MULT_CLAUSES] THEN
      UNDISCH_TAC (--` abs (~(0 / 2 pow fracbits (n,m,s)) - x) <= inv (2 pow fracbits (n,m,s))`--) THEN
      ASM_REWRITE_TAC [fracbits,intbits,streamlength] THEN ASM_REWRITE_TAC [real_div] THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN REWRITE_TAC [REAL_NEG_0,REAL_ADD_RID] THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
      REWRITE_TAC [SUB_PLUS], REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN REWRITE_TAC [WORDLEN_DEF] THEN
      REWRITE_TAC [LENGTH] THEN REWRITE_TAC [GSYM WORDLEN_DEF] THEN REWRITE_TAC [GSYM NBWORD_DEF] THEN
      REWRITE_TAC [WORDLEN_NBWORD] THEN RW_TAC arith_ss [SUC_ONE_ADD] THEN RW_TAC arith_ss [SUB_LEFT_ADD] THEN
      UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN RW_TAC arith_ss [validAttr,streamlength]],
    EXISTS_TAC (--`(WCAT (WORD [T], NBWORD (n-1) (2 EXP (n-1) - SUC n')))`--) THEN
    UNDISCH_TAC (--`0 <= ~x /\ ~x <= 2 pow (streamlength (n,m,s) - 1) / 2 pow fracbits (n,m,s) /\
    validAttr (n,m,s) /\ ~is_unsigned (n,m,s)`--) THEN REPEAT STRIP_TAC THENL [
      UNDISCH_TAC (--`~is_unsigned ((n :num),(m :num),(s :num))`--) THEN UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN RW_TAC arith_ss [value,NOTTiIsigned] THEN
      RW_TAC arith_ss [Fracbits,fracbits,Attrib,attrib,streamlength,Streamlength,Stream,DEFXP_FXP_WCATT,stream,intbits] THEN
      RW_TAC arith_ss [BNVAL_WCATT_NBWORD] THEN UNDISCH_TAC (--`SUC n' < 2 EXP (streamlength (n,m,s) - 1)`--) THEN
      REWRITE_TAC [streamlength] THEN RW_TAC arith_ss [lessneg,SUC_NOT,NOT_ZERO_LT_ZERO,BNVAL_NBWORD] THEN
      RW_TAC arith_ss [LESS_IMP_LESS_OR_EQ,GSYM REAL_OF_NUM_SUB] THEN REWRITE_TAC [BV_DEF] THEN
      REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN REWRITE_TAC [MSB_DEF] THEN REWRITE_TAC [HD] THEN
      REWRITE_TAC [GSYM ONE] THEN REWRITE_TAC [MULT_LEFT_1] THEN REWRITE_TAC [GSYM REAL_OF_NUM_ADD] THEN
      UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN REWRITE_TAC [validAttr,streamlength] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      ONCE_REWRITE_TAC[REAL_ARITH (--`((a:real) + b - c - d) = (a + b - d - c)`--)] THEN RW_TAC arith_ss [exp2] THEN
      RW_TAC arith_ss [GSYM REAL_OF_NUM_MUL] THEN ONCE_REWRITE_TAC[REAL_ARITH (--`((a:real) + a - (&2 * a)) = (&0)`--)] THEN
      ONCE_REWRITE_TAC[REAL_ARITH (--`((&0:real) - &a) = (~&a)`--)] THEN
      UNDISCH_TAC (--`abs (~(& (SUC n') / 2 pow fracbits (n,m,s)) - x) <= inv (2 pow fracbits (n,m,s))`--) THEN
      ASM_REWRITE_TAC [fracbits,streamlength,intbits] THEN REWRITE_TAC [SUB_PLUS] THEN ASM_REWRITE_TAC [real_div] THEN
      REWRITE_TAC [GSYM REAL_NEG_LMUL], REWRITE_TAC [NBWORD_DEF,GSYM WORD_CONS_WCAT] THEN REWRITE_TAC [WORDLEN_DEF] THEN
      REWRITE_TAC [LENGTH] THEN REWRITE_TAC [GSYM WORDLEN_DEF] THEN REWRITE_TAC [GSYM NBWORD_DEF] THEN
      REWRITE_TAC [WORDLEN_NBWORD] THEN RW_TAC arith_ss [SUC_ONE_ADD] THEN RW_TAC arith_ss [SUB_LEFT_ADD] THEN
      UNDISCH_TAC (--`validAttr (n,m,s)`--) THEN RW_TAC arith_ss [validAttr,streamlength]]]);

(*----------------------------------*)

val FXP_ERROR_BOUND_LEMMA3_ABS_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA3_ABS_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). (abs x <= (&2 pow (streamlength (n,m,s) - 1)) / &2 pow fracbits (n,m,s))
      /\ validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)) ==> (?(w:bool word) . abs (value (fxp (w,(n,m,s))) - x) <=
      inv (&2 pow (fracbits (n,m,s))) /\ (WORDLEN (w) = n))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (--`((&0 <= x) /\ (x <= (&2 pow (streamlength (n,m,s) - 1)) /
  &2 pow fracbits (n,m,s))) \/ ((&0 <= ~ x) /\ (~ x <= (&2 pow (streamlength (n,m,s) - 1)) / &2 pow fracbits (n,m,s)))`--) MP_TAC THENL [
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC, RW_TAC arith_ss [] THENL [
      UNDISCH_TAC (--`(&0:real) <= (x:real)`--) THEN UNDISCH_TAC (--`x <= &2 pow (streamlength (n,m,s) - 1) / &2 pow fracbits (n,m,s)`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN RW_TAC arith_ss [FXP_ERROR_BOUND_LEMMA3_POS_SIGNED],
      UNDISCH_TAC (--`0 <= (~x:real)`--) THEN UNDISCH_TAC (--`(~x:real) <= &2 pow (streamlength (n,m,s) - 1) / &2 pow fracbits (n,m,s)`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN RW_TAC arith_ss [FXP_ERROR_BOUND_LEMMA3_NEG_SIGNED]]]);

(*--------------------------------*)

val maxmin = prove_thm (
  "maxmin",
  (--`! (x:real) (n: num) (m: num) (s: num). ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      ~ (is_unsigned (n,m,s)) ==> (abs x <= (&2 pow (streamlength (n,m,s) - 1)) / &2 pow fracbits (n,m,s) /\
      validAttr (n,m,s) /\ ~(is_unsigned (n,m,s)))`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [MAX,MIN] THEN RW_TAC arith_ss [ABS_BOUNDS] THENL [
    UNDISCH_TAC (--`~(x < ~(&2 pow (streamlength (n,m,s) - 1)) / &2 pow fracbits (n,m,s))`--) THEN
    ASM_REWRITE_TAC [GSYM real_lte] THEN ASM_REWRITE_TAC [real_div] THEN ASM_REWRITE_TAC [REAL_NEG_LMUL],
    UNDISCH_TAC (--`~(x > (2 pow (streamlength (n,m,s) - 1) - 1) / 2 pow fracbits (n,m,s))`--) THEN
    ASM_REWRITE_TAC [real_gt ] THEN ASM_REWRITE_TAC [GSYM real_lte] THEN ASM_REWRITE_TAC [pwvfraclereal,PWFLT_REAL] THEN
    RW_TAC arith_ss [REAL_DIV_LMUL,vfracnot0] THEN
    UNDISCH_TAC (--`&2 pow fracbits (n,m,s) * x <= &2 pow (streamlength (n,m,s) - 1) - &1`--) THEN
    REAL_ARITH_TAC]);

(*--------------------------------------------*)

val FXP_ERROR_BOUND_LEMMA3_SIGNED = prove_thm (
  "FXP_ERROR_BOUND_LEMMA3_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      ~ (is_unsigned (n,m,s)) ==> (?(w:bool word) . abs (value (fxp (w,(n,m,s))) - x) <= inv (&2 pow (fracbits (n,m,s)))
      /\ (WORDLEN (w) = n))`--),
  REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP maxmin) THEN RW_TAC arith_ss [FXP_ERROR_BOUND_LEMMA3_ABS_SIGNED]);

(*------------------------*)

val FXP_MAIN_ERROR_BOUND_THEOREM_SIGNED = prove_thm (
  "FXP_MAIN_ERROR_BOUND_THEOREM_SIGNED",
  (--`! (x:real) (n: num) (m: num) (s: num). ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) /\
      ~ (is_unsigned (n,m,s)) ==> abs (fxperror (n,m,s) (Convergent) (Clip) x) <= (inv (&2 pow (fracbits (n,m,s))))`--),
  REPEAT STRIP_TAC THEN SUBGOAL_THEN (--`? (a:fxp). Isvalid a /\ (Attrib a = (n,m,s)) /\ abs(value a - x) <=
  (inv (&2 pow (fracbits (n,m,s))))`--) CHOOSE_TAC THENL [
    MP_TAC FXP_ERROR_BOUND_LEMMA3_SIGNED THEN DISCH_THEN (MP_TAC o SPEC_ALL) THEN
    RW_TAC arith_ss [] THEN EXISTS_TAC (--`fxp (w,WORDLEN w,m,s)`--) THEN
    RW_TAC arith_ss [] THENL [
      RW_TAC arith_ss [Isvalid] THEN RW_TAC arith_ss [DEFXP_FXP_WORDLEN,is_valid] THENL [
        RW_TAC arith_ss [attrib], RW_TAC arith_ss [attrib,streamlength,stream]],
      RW_TAC arith_ss [Attrib] THEN RW_TAC arith_ss [DEFXP_FXP_WORDLEN,attrib]],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(value a - x)`--) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FXP_ERROR_AT_WORST_LEMMA THEN
    ASM_REWRITE_TAC []]);

(*--------------------------*)

val FXP_MAIN_ERROR_BOUND_THEOREM = prove_thm (
  "FXP_MAIN_ERROR_BOUND_THEOREM",
  (--`! (x:real) (n: num) (m: num) (s: num). ~(x > MAX (n,m,s)) /\ ~(x < MIN (n,m,s)) /\ validAttr (n,m,s) ==>
      abs (fxperror (n,m,s) (Convergent) (Clip) x) <= (inv (&2 pow (fracbits (n,m,s))))`--),
  REPEAT GEN_TAC THEN Cases_on `is_unsigned (n,m,s)` THEN
  RW_TAC arith_ss [FXP_MAIN_ERROR_BOUND_THEOREM_UNSIGNED] THEN
  RW_TAC arith_ss [FXP_MAIN_ERROR_BOUND_THEOREM_SIGNED]);

(*------------------------------------- *)
(* Fixed-Point Absolute Error Analysis. *)
(*------------------------------------- *)

val representable = new_definition ("representable", --`representable (X:num#num#num) (x:real)
 = ~(x > MAX X) /\ ~(x < MIN X)`--);

val Fxp_round = Define `Fxp_round (X:(num#num#num)) x =
    (FST(fxp_round (X) (Convergent) x Clip))`;

val Fxperror = Define `Fxperror (X: (num # num # num)) (x: real) =
    fxperror X Convergent Clip x`;

val FxpAdd = Define `FxpAdd (X:(num#num#num)) (a:fxp) (b:fxp) =
    (FST(fxpAdd X Convergent Clip a b))`;

val FxpSub = Define `FxpSub (X:(num#num#num)) (a:fxp) (b:fxp) =
    (FST(fxpSub X Convergent Clip a b))`;

val FxpMul = Define `FxpMul (X:(num#num#num)) (a:fxp) (b:fxp) =
    (FST(fxpMul X Convergent Clip a b))`;

(*------------------------------------------------- *)

val FXP_ABSOLUTE_ERROR = prove_thm (
  "FXP_ABSOLUTE_ERROR",
  (--`! (x:real) (X:num#num#num). (validAttr X) /\ (representable X x)
      ==> ? (e:real). abs(e) <= (inv (&2 pow (fracbits X))) /\
      (value (Fxp_round X x) = x + e)`--),
  RW_TAC arith_ss [representable] THEN EXISTS_TAC (--`Fxperror X x`--) THEN
  STRIP_TAC THEN RW_TAC arith_ss [Fxperror] THEN Cases_on `X` THEN
  Cases_on `r` THEN RW_TAC arith_ss [FXP_MAIN_ERROR_BOUND_THEOREM] THEN
  RW_TAC arith_ss [Fxperror,Fxp_round,fxperror] THEN REAL_ARITH_TAC);

(*------------------------------------------------- *)

val FXP_ADD_ABSOLUTE_THM = prove_thm (
  "FXP_ADD_ABSOLUTE_THM",
  (--`! (a:fxp) (b: fxp) (X:num#num#num).
      (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a + value b)) ==>
      (Isvalid (FxpAdd X a b)) /\
      ? (e:real). abs(e) <= (inv (&2 pow (fracbits X))) /\
      (value (FxpAdd X a b) = (value a) + (value b) + e)`--),
  REPEAT GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN
  RW_TAC arith_ss [FXP_ADD_THM,representable,FxpAdd] THEN
  EXISTS_TAC (--`Fxperror (q,q',r') (value a + value b)`--) THEN
  RW_TAC arith_ss [FXP_MAIN_ERROR_BOUND_THEOREM,Fxperror]);

(*------------------------------------------------- *)

val FXP_ADD_ISVALID = prove_thm (
  "FXP_ADD_ISVALID",
  (--`! (a:fxp) (b: fxp) (X:num#num#num). (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a + value b)) ==> (Isvalid (FxpAdd X a b))`--),
  RW_TAC arith_ss [FXP_ADD_ABSOLUTE_THM]);


(*------------------------------------------------- *)

val FXP_ADD = prove_thm (
  "FXP_ADD",
  (--`! (a:fxp) (b: fxp) (X:num#num#num). (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a + value b)) ==> (Isvalid (FxpAdd X a b)) /\
      (value (FxpAdd X a b) = (value a) + (value b) + Fxperror (X: (num # num # num)) (value a + value b))`--),
  REPEAT GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN
  RW_TAC arith_ss [FxpAdd,Fxperror,representable,FXP_ADD_THM]);

(*------------------------------------------------- *)

val FXP_SUB_ABSOLUTE_THM = prove_thm (
  "FXP_SUB_ABSOLUTE_THM",
  (--`! (a:fxp) (b: fxp) (X:num#num#num).
      (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\ (representable X (value a - value b)) ==>
      (Isvalid (FxpSub X a b)) /\ ? (e:real). abs(e) <= (inv (&2 pow (fracbits X))) /\
      (value (FxpSub X a b) = (value a) - (value b) + e)`--),
  REPEAT GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN
  RW_TAC arith_ss [FXP_SUB_THM,representable,FxpSub] THEN
  EXISTS_TAC (--`Fxperror (q,q',r') (value a - value b)`--) THEN
  RW_TAC arith_ss [FXP_MAIN_ERROR_BOUND_THEOREM,Fxperror]);

(*------------------------------------------------- *)

val FXP_SUB_ISVALID = prove_thm (
  "FXP_SUB_ISVALID",
  (--`! (a:fxp) (b: fxp) (X:num#num#num). (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a - value b)) ==> (Isvalid (FxpSub X a b))`--),
  RW_TAC arith_ss [FXP_SUB_ABSOLUTE_THM]);

(*------------------------------------------------- *)

val FXP_SUB = prove_thm (
  "FXP_SUB",
  (--`! (a:fxp) (b: fxp) (X:num#num#num). (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a - value b)) ==> (Isvalid (FxpSub X a b)) /\
      (value (FxpSub X a b) = (value a) - (value b) + Fxperror (X: (num # num # num)) (value a - value b))`--),
  REPEAT GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN RW_TAC arith_ss [FxpSub,Fxperror,representable,FXP_SUB_THM]);

(*------------------------------------------------- *)

val FXP_MUL_ABSOLUTE_THM = prove_thm (
  "FXP_MUL_ABSOLUTE_THM",
  (--`! (a:fxp) (b: fxp) (X:num#num#num).
      (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\ (representable X (value a * value b))
      ==>
      (Isvalid (FxpMul X a b)) /\ ? (e:real). abs(e) <= (inv (&2 pow (fracbits X))) /\
      (value (FxpMul X a b) = (value a) * (value b) + e)`--),
  REPEAT GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN
  RW_TAC arith_ss [FXP_MUL_THM,representable,FxpMul] THEN
  EXISTS_TAC (--`Fxperror (q,q',r') (value a * value b)`--) THEN
  RW_TAC arith_ss [FXP_MAIN_ERROR_BOUND_THEOREM,Fxperror]);

(*------------------------------------------------- *)

val FXP_MUL_ISVALID = prove_thm (
  "FXP_MUL_ISVALID",
  (--`! (a:fxp) (b: fxp) (X:num#num#num). (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a * value b)) ==> (Isvalid (FxpMul X a b))`--),
  RW_TAC arith_ss [FXP_MUL_ABSOLUTE_THM]);

(*------------------------------------------------- *)

val FXP_MUL = prove_thm (
  "FXP_MUL",
  (--`! (a:fxp) (b: fxp) (X:num#num#num). (Isvalid a) /\ (Isvalid b) /\ validAttr (X) /\
      (representable X (value a * value b)) ==> (Isvalid (FxpMul X a b)) /\
      (value (FxpMul X a b) = (value a) * (value b) + Fxperror (X: (num # num # num)) (value a * value b))`--),
  REPEAT GEN_TAC THEN Cases_on `X` THEN Cases_on `r` THEN RW_TAC arith_ss [FxpMul,Fxperror,representable,FXP_MUL_THM]);

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)
val _ = export_theory();
