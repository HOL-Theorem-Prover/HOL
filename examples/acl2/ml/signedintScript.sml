(*****************************************************************************)
(* signedintScript.sml                                                       *)
(*     Creates operators sw2i and i2sw to relate words to signed integers    *)
(*     and companion theorems.                                               *)
(*                                                                           *)
(*****************************************************************************)

(* Interactive use only -
load "wordsTheory";
load "intLib";
*)

open Theory Thm Term Type Tactic Tactical bossLib Drule
open Rewrite Conv HolKernel boolSyntax
open boolTheory
open wordsTheory arithmeticTheory integerTheory bitTheory intLib;

(* Profiling -
val list = ref [];
fun prove x =
let	val s = Time.now();
	val r = Tactical.prove x
	val e = Time.now();
	val _ = list := (Time.-(e,s),fst x)::(!list)
in
	r
end;
fun store_thm (a,b,c) = save_thm(a,prove (b,c));
*)

val _ = new_theory "signedint";

val int_sub_calc1 = prove(
    ``& a - & b = if b <= a then & (a - b) else ~ &(b - a):int``,
    RW_TAC int_ss [INT_SUB,ARITH_PROVE ``(a = ~b) = (~a = b:int)``]);

val int_sub_calc2 = prove(
    ``& a - & b = if b < a then & (a - b) else ~ &(b - a):int``,
    RW_TAC int_ss [INT_SUB,ARITH_PROVE ``(a = ~b) = (~a = b:int)``]);

val dimword_pos = prove(
    ``~(& (dimword (:'a)) = 0i) /\ ~(dimword (:'a) = 0n) /\ 0 < dimword (:'a)``,
    PROVE_TAC [INT_LT_NZ,ZERO_LT_TWOEXP,INT_NZ_IMP_LT,
    	      DECIDE ``0 < a = ~(a = 0n)``,dimword_def]);

val w2n_lt_full = save_thm("w2n_lt_full",
    LIST_CONJ [w2n_lt,REWRITE_RULE [dimword_def] w2n_lt,
    REWRITE_RULE [dimword_def,GSYM NOT_LESS_EQUAL] w2n_lt]);

val bint_ss = int_ss ++ boolSimps.LET_ss;

val BIT_RWR =
    save_thm("BIT_RWR",SIMP_RULE arith_ss
    	      [BITS_THM2,DECIDE ``(a = 1) = 0 < a /\ a < 2n``,
     	       DIV_LT_X,X_LT_DIV,MOD_LESS,GSYM EXP] BIT_def);

val SUC_SUB_INDEX = prove(
    ``SUC (dimindex (:'a) - 1) = dimindex (:'a)``,
    RW_TAC arith_ss [DECIDE ``0 < a ==> (SUC (a - 1) = a)``,DIMINDEX_GT_0]);

(*****************************************************************************)
(*            A ?- a < c                     A ?- a <= c                     *)
(*     ------------------------ LT     ------------------------- LE          *)
(*     A ?- ?b. a < b /\ b < c         A ?- ?b. a <= b /\ b <= c             *)
(*                                                                           *)
(*            A ?- a < c                     A ?- a < c                      *)
(*     ------------------------ LTLE   ------------------------ LELT         *)
(*     A ?- ?b. a < b /\ b <= c        A ?- ?b. a <= b /\ b < c              *)
(*                                                                           *)
(*****************************************************************************)

local
val q = Q.EXISTS_TAC
val lelt = DECIDE ``!a b c. a <= b /\ b < c ==> a < c:num``
val ltle = DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``
fun try thm = FIRST [MATCH_MP_TAC thm,
    	      	     MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN MATCH_MP_TAC thm]
in
fun NLT_TRANS_TAC w = try LESS_TRANS THEN q w
fun NLE_TRANS_TAC w = MATCH_MP_TAC LESS_EQ_TRANS THEN q w
fun NLELT_TRANS_TAC w = try lelt THEN q w
fun NLTLE_TRANS_TAC w = try ltle THEN q w
end;

(*****************************************************************************)
(*                               A ?- t                                      *)
(*      ----------------------------------------------------------           *)
(*      A [& c / x] ?- t [& c / x]    A [~& c / x] ?- t [~& c / x]           *)
(*                                                                           *)
(*****************************************************************************)

local
val thm1 = ARITH_PROVE ``!a. 0 <= ~a \/ 0 <= a``
val thm2 = prove(``!a. 0 <= a ==> ?c. a = & c``,
    REPEAT STRIP_TAC THEN Q.EXISTS_TAC `Num a` THEN
    ASM_REWRITE_TAC
        [ONCE_REWRITE_RULE [ISPEC ``a:int`` EQ_SYM_EQ] INT_OF_NUM,
	 ARITH_PROVE ``(a = ~ & b) = (~a = & b)``]);
val thm3 = prove(``!a. 0 <= ~a ==> ?c. a = ~ & c``,
    REPEAT STRIP_TAC THEN Q.EXISTS_TAC `Num ~a` THEN
    ASM_REWRITE_TAC
        [ONCE_REWRITE_RULE [ISPEC ``a:int`` EQ_SYM_EQ] INT_OF_NUM,
	 ARITH_PROVE ``(a = ~ & b) = (~a = & b)``]);
in
fun INT_CASE_TAC tm =
	DISJ_CASES_TAC (Q.SPEC tm thm1) THENL [
		POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP thm3),
		POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP thm2)] THEN
	POP_ASSUM SUBST_ALL_TAC
end;

(*****************************************************************************)
(*        A u {!x. P} ?- t[tm]                                               *)
(*    --------------------------- pTAC tm f                                  *)
(*    A ?- P [f tm / x] ==> t[tm]                                            *)
(*                                                                           *)
(*****************************************************************************)

fun pTAC tm f (a,g) =
let	val x = find_terms (can (match_term tm)) g
	val t = f (hd x)
in
	(PAT_ASSUM ``!m:'a.P`` (MP_TAC o SPEC t)) (a,g)
end	handle e => NO_TAC (a,g)



(*****************************************************************************)
(* Bit support theorems:                                                     *)
(*                                                                           *)
(* BIT_MOD : |- !a b c. BIT a (b MOD 2 ** c) = a < c /\ BIT a b              *)
(* MOD_HIGH_MOD : |- !a b. b <= a ==> ((2 ** a - 1) MOD 2 ** b = 2 ** b - 1) *)
(* MOD_HIGH_SUM : |- !a b. 2 ** b - 1 =                                      *)
(*                          (2 ** b - 2 ** a + (2 ** a - 1)) MOD 2 ** b      *)
(* MOD_HIGH_EQ_ADD : |- !b c d. (2 ** b - 1 = c MOD 2 ** b + d MOD 2 ** b) = *)
(*                                       (2 ** b - 1 = (c + d) MOD 2 ** b)   *)
(*                                                                           *)
(* BIT_DIV : |- !x m. BIT (SUC m) x = BIT m (x DIV 2)                        *)
(* BIT_ZERO_ODD : |- !a. BIT 0 a = ODD a                                     *)
(*                                                                           *)
(* BITWISE_DIV : |- !m op x y. BITWISE (SUC m) op x y =                      *)
(*    	                         (if op (ODD x) (ODD y) then 1 else 0) +     *)
(*	                         2 * BITWISE m op (x DIV 2) (y DIV 2)``,     *)
(* BITWISE_ZERO : |- !op x y. BITWISE 0 op x y = 0                           *)
(*                                                                           *)
(*****************************************************************************)

val BIT_MOD = store_thm("BIT_MOD",
    ``!a b c. BIT a (b MOD 2 ** c) = a < c /\ BIT a b``,
    REPEAT GEN_TAC THEN REWRITE_TAC [BIT_RWR] THEN
    `a < c \/ c < SUC a` by DECIDE_TAC THEN1
          (IMP_RES_TAC LESS_ADD_1 THEN
	   RW_TAC arith_ss [DECIDE ``a + (p + 1) = SUC a + p``]  THEN
	   RW_TAC arith_ss [ONCE_REWRITE_RULE [MULT_COMM] MOD_MULT_MOD,
                            EXP_ADD]) THEN
    RW_TAC arith_ss [NOT_LESS_EQUAL] THEN
    `b MOD 2 ** c < 2 ** a` by NLTLE_TRANS_TAC `2 ** c` THEN
    RW_TAC arith_ss [MOD_LESS] THEN
    `b MOD 2 ** c < 2 ** SUC a` by NLT_TRANS_TAC `2 ** a` THEN
    RW_TAC arith_ss [MOD_LESS]);

val MOD_HIGH_MOD = store_thm("MOD_HIGH_MOD",
    ``!a b. b <= a ==> ((2 ** a - 1) MOD 2 ** b = 2 ** b - 1)``,
    Induct THEN RW_TAC arith_ss [EXP] THEN
    Cases_on `b = SUC a` THEN RW_TAC arith_ss [EXP] THEN
    `a = b + (a - b)` by DECIDE_TAC THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [MATCH_MP (DISCH_ALL (MATCH_MP
    			(DECIDE ``0 < a ==> (a + a - 1 = a + (a - 1n))``)
			(UNDISCH (SPEC_ALL LESS_MULT2))))
		(CONJ (SPEC_ALL ZERO_LT_TWOEXP) (Q.SPEC `m` ZERO_LT_TWOEXP)),
		EXP_ADD,TIMES2,ONCE_REWRITE_RULE [MULT_COMM]
			(MATCH_MP MOD_TIMES (SPEC_ALL ZERO_LT_TWOEXP))] THEN
    RW_TAC arith_ss [GSYM EXP_ADD]);

val MOD_HIGH_SUM = store_thm("MOD_HIGH_SUM",
    ``!a b. 2 ** b - 1 = (2 ** b - 2 ** a + (2 ** a - 1)) MOD 2 ** b``,
    REPEAT GEN_TAC THEN `a <= b \/ b <= a` by DECIDE_TAC THEN
    METIS_TAC [TWOEXP_MONO2,
        DECIDE ``a <= b /\ 0 < b /\ 0 < a ==> (b - a + (a - 1) = b - 1n)``,
	ZERO_LT_TWOEXP,DECIDE ``0 < b ==> (b - 1n < b)``,LESS_MOD,MOD_HIGH_MOD,
	DECIDE ``b <= a ==> (b - a + c = c:num)``]);

val MOD_HIGH_EQ_ADD = store_thm("MOD_HIGH_EQ_ADD",
    ``!b c d. (2 ** b - 1 = c MOD 2 ** b + d MOD 2 ** b) =
    	      	      (2 ** b - 1 = (c + d) MOD 2 ** b)``,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [GSYM (MATCH_MP MOD_PLUS (SPEC_ALL ZERO_LT_TWOEXP))] THEN
    Q.ABBREV_TAC `A = c MOD 2 ** b` THEN Q.ABBREV_TAC `B = d MOD 2 ** b` THEN
    Q.ABBREV_TAC `D = 2n ** b` THEN
    `A < D /\ B < D /\ 0 < D` by METIS_TAC [MOD_LESS,ZERO_LT_TWOEXP] THEN
    `A + B < D \/ D <= A + B /\ A + B <= 2 * D - 2` by DECIDE_TAC THEN
    IMP_RES_TAC (Q.SPECL [`A + B`,`D`] (GSYM SUB_MOD)) THEN RW_TAC arith_ss []);

val BIT_DIV = store_thm("BIT_DIV",
    ``!x m. BIT (SUC m) x = BIT m (x DIV 2)``,
    RW_TAC arith_ss [BIT_def,BITS_def,MOD_2EXP_def,DIV_2EXP_def,
        DECIDE ``SUC a - a = 1``,DIV_DIV_DIV_MULT,ZERO_LT_TWOEXP,EXP]);

val BIT_ZERO_ODD = store_thm("BIT_ZERO_ODD",
    ``!a. BIT 0 a = ODD a``,
    RW_TAC arith_ss [BIT_def,BITS_THM,ODD_MOD2_LEM]);

val SBIT_DIV = store_thm("SBIT_DIV",
    ``!x m. 2 * SBIT x m = SBIT x (SUC m)``,
    RW_TAC arith_ss [SBIT_def,EXP]);

val SBIT_ZERO = store_thm("SBIT_ZERO",
    ``!b. SBIT b 0 = if b then 1 else 0``,
    RW_TAC arith_ss [SBIT_def]);

val BITWISE_DIV = store_thm("BITWISE_DIV",
    ``!m op x y. BITWISE (SUC m) op x y =
    	      (if op (ODD x) (ODD y) then 1 else 0) +
	      2 * BITWISE m op (x DIV 2) (y DIV 2)``,
    RW_TAC int_ss [BITWISE_EVAL,SBIT_def,LSB_def,BIT_ZERO_ODD]);

val BITWISE_ZERO = store_thm("BITWISE_ZERO",
    ``!op x y. BITWISE 0 op x y = 0``,
    RW_TAC arith_ss [BITWISE_def,SBIT_DIV,LEFT_ADD_DISTRIB,BIT_DIV]);

(*****************************************************************************)
(* Word support theorems:                                                    *)
(* TOP_BIT_LE : |- !a. BIT (dimindex (:'a) - 1) (w2n a) =                    *)
(*    	      	                          2 ** (dimindex (:'a) - 1) <= w2n a *)
(* DIMINDEX_DOUBLE : |- 2n ** (dimindex (:'a)) =                             *)
(*                                        2 * 2 ** (dimindex (:'a) - 1)      *)
(*                                                                           *)
(*****************************************************************************)
val TOP_BIT_LE = store_thm("TOP_BIT_LE",
    ``!a. BIT (dimindex (:'a) - 1) (w2n (a:'a word)) =
    	      		2 ** (dimindex (:'a) - 1) <= w2n a``,
    RW_TAC int_ss [BIT_RWR,DIMINDEX_GT_0,SUC_SUB_INDEX,LESS_MOD,w2n_lt_full]);

val DIMINDEX_DOUBLE = store_thm("DIMINDEX_DOUBLE",
    ``2n ** (dimindex (:'a)) = 2 * 2 ** (dimindex (:'a) - 1)``,
    RW_TAC arith_ss [GSYM EXP,DIMINDEX_GT_0,SUC_SUB_INDEX]);

(*****************************************************************************)
(* Other arithmetic theorems:                                                *)
(* ODD_TWOEXP : |- !x. ODD (2 ** x) = (x = 0)                                *)
(* MOD2_ODD_EVEN : |- (!a. (a MOD 2 = 0) = EVEN a) /\                        *)
(*                    (!a. (a MOD 2 = 1) = ODD a)                            *)
(* EVEN_SUB : |- !a b. EVEN (a - b) = a <= b \/ (EVEN a = EVEN b)            *)
(* ODD_SUB  : |- !a b. ODD (a - b) = b < a /\ ~(ODD a = ODD b)               *)
(*                                                                           *)
(* DIV2_MULT_SUB1 : |- !a. 0 < a ==> ((2 * a - 1) DIV 2 = a - 1)             *)
(* NOT_MOD2 : |- (!c. ~(c MOD 2 = 0) = (c MOD 2 = 1n)) /\                    *)
(*               (!c. ~(c MOD 2 = 1n) = (c MOD 2 = 0n))                      *)
(* BITWISE_TOP : |- !a b. b < 2 ** a ==> (BITWISE a $/\ (2 ** a - 1) b = b)  *)
(*                                                                           *)
(*****************************************************************************)

val ODD_TWOEXP = store_thm("ODD_TWOEXP",``!x. ODD (2 ** x) = (x = 0n)``,
    Induct THEN RW_TAC arith_ss [EXP,EVEN_DOUBLE,GSYM EVEN_ODD]);

val MOD2_ODD_EVEN = store_thm("MOD2_ODD_EVEN",
    ``(!a. (a MOD 2 = 0) = EVEN a) /\ (!a. (a MOD 2 = 1) = ODD a)``,
    PROVE_TAC [ODD_MOD2_LEM,MOD_LESS,DECIDE ``0 < 2n``,
        DECIDE ``a < 2 = (a = 0n) \/ (a = 1n)``,
	EVEN_ODD,DECIDE ``~(0 = 1n)``]);

val EVEN_SUB = store_thm("EVEN_SUB",
    ``!a b. EVEN (a - b) = a <= b \/ (EVEN a = EVEN b)``,
    Induct THEN GEN_TAC THEN EQ_TAC THEN Cases_on `SUC a <= b` THEN
    RW_TAC arith_ss [EVEN,ADD1] THEN
    FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL,ADD1,
    		  DECIDE ``(a + 1 <= b) ==> (a + 1 - b = 0n)``] THEN
    IMP_RES_TAC LESS_EQUAL_ADD THEN POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC arith_ss [EVEN_ADD] THEN METIS_TAC []);

val ODD_SUB = store_thm("ODD_SUB",
    ``!a b. ODD (a - b) = b < a /\ ~(ODD a = ODD b)``,
    METIS_TAC [NOT_LESS_EQUAL,EVEN_ODD,EVEN_SUB]);

val DIV2_MULT_SUB1 = store_thm("DIV2_MULT_SUB1",
    ``!a. 0 < a ==> ((2 * a - 1) DIV 2 = a - 1)``,
    GEN_TAC THEN DISCH_TAC THEN `?b. a = SUC b` by Q.EXISTS_TAC `a - 1` THEN
    RW_TAC arith_ss [ADD1,LEFT_ADD_DISTRIB,
    	   ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]);

val NOT_MOD2 = store_thm("NOT_MOD",
    ``(!c. ~(c MOD 2 = 0) = (c MOD 2 = 1n)) /\
      (!c. ~(c MOD 2 = 1n) = (c MOD 2 = 0n))``,
    PROVE_TAC [MOD2_ODD_EVEN,EVEN_OR_ODD,EVEN_ODD]);

val BITWISE_TOP = store_thm("BITWISE_TOP",
    ``!a b. b < 2 ** a ==> (BITWISE a $/\ (2 ** a - 1) b = b)``,
    Induct THEN GEN_TAC THEN TRY (POP_ASSUM (MP_TAC o Q.SPEC `b DIV 2`)) THEN
    RW_TAC int_ss [BITWISE_DIV,BITWISE_ZERO,ODD_SUB,GSYM EVEN_ODD,EVEN_EXP,
    	   DIV2_MULT_SUB1,EXP,EVEN_MULT,DIV_LT_X,DIV_MULT_THM2] THEN
    Cases_on `b` THEN FULL_SIMP_TAC int_ss [GSYM MOD2_ODD_EVEN,NOT_MOD2]);

(*****************************************************************************)
(* Definitions                                                               *)
(*     i2n i l : Convert an integer i to a natural number < 2 ** l           *)
(*     extend r l : Sign extend an integer i to fit in l bits                *)
(*                                                                           *)
(*     sw2i x : Convert the word x to a signed integer                       *)
(*     i2sw x : Convert the integer x to a word                              *)
(*                                                                           *)
(*     iand a b : Bitwise and of two integers                                *)
(*     inot a : Bitwise negation of an integer                               *)
(*     ibit i j : Determine if bit i of integer j is set                     *)
(*                                                                           *)
(*****************************************************************************)

val i2n_def = Define `i2n i l =
    Num (if 0 <= i then i % 2 ** l else (i + 1) rem (2 ** l) - 1 + 2 ** l)`;

val extend_def = Define `extend i l =
    let m = i2n i l in if BIT (l - 1) m then & m - 2 ** l else & m`;

val sw2i_def = Define `sw2i (x:'a word) =
         (if BIT (dimindex (:'a) - 1) (w2n x) then
            & (w2n x) - 2 ** dimindex (:'a)
          else
            & (w2n x))`;

val i2sw_def = Define `i2sw x =
	let m = extend x (dimindex (:'b))
	in  if m < 0 	then n2w (Num (m + 2 ** dimindex (:'b)))
			else n2w (Num m):'b word`;

val iand_def = tDefine "iand"
       `iand i j =
	if (i = 0) then 0
	else if (j = 0) then 0
	else if (i = ~1) then j
	else if (j = ~1) then i
	else 	let 	x = 2 * iand (i / 2) (j / 2)
		in	x + (if (i % 2 = 1) /\ (j % 2 = 1) then 1 else 0)`
	(WF_REL_TAC `measure (Num o ABS o FST)` THEN
	RW_TAC int_ss [INT_ABS] THEN
	ONCE_REWRITE_TAC [GSYM INT_LT] THEN
	RW_TAC std_ss [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),
	      ARITH_PROVE ``a < 0 ==> 0i <= ~a``,
	      ARITH_PROVE ``~(a < 0) ==> 0i <= a``] THEN ARITH_TAC);

val inot_def = Define `inot x = ~(x + 1i)`;

val ibit_def = Define `ibit i j = ODD (Num (ABS (j / 2 ** i)))`;

(*****************************************************************************)
(* I2N_NUM        : |- !a b. i2n (& a) b = a MOD 2 ** b                      *)
(* EXTEND_LE_ZERO : |- !a b. extend a b < 0 = BIT (b - 1) (i2n a b)          *)
(* EXTEND_ZERO    : |- !a b. (extend 0 a = 0) /\ (extend b 0 = 0)            *)
(*                                                                           *)
(* EXTEND_POS_EQ  : |- !a b. a < 2 ** (b - 1) ==> (extend (& a) b = & a      *)
(* EXTEND_POS_NE  : |- !a b. 2 ** (b - 1) < a /\ a < 2 ** b ==>              *)
(*                                          (extend (& a) b = & a - 2 ** b)  *)
(* EXTEND_POS_NEG : |- !b. 0 < b ==> (extend (& (2 ** (b - 1))) b =          *)
(*                                                       ~ & (2 ** (b - 1))) *)
(* EXTEND_POS_REC : |- !a b. 2 ** b <= a ==> (extend (& a) b =               *)
(*                                                extend (& (a - 2 ** b)) b) *)
(*                                                                           *)
(* EXTEND_NEG_EQ  : |- !a b. a < 2 ** (b - 1) ==> (extend (~ & a) b = ~ & a) *)
(* EXTEND_NEG_NE  : |- !a b. 2 ** (b - 1) < a /\ a < 2 ** b ==>              *)
(*                                        (extend (~ & a) b = 2 ** b - & a)  *)
(* EXTEND_NEG_NEG : |- !b. 0 < b ==> (extend (~ & (2 ** (b - 1))) b =        *)
(*                                                      ~ & (2 ** (b - 1)))  *)
(* EXTEND_NEG_REC : |- !a b. 2 ** b <= a ==> (extend (~ & a) b =             *)
(*                                             extend (~ & (a - 2 ** b)) b)  *)
(*                                                                           *)
(* EXTEND_EQ      : |- !n a b. (extend a (SUC n) = b) =                      *)
(*                                   ~(2 ** n) <= b /\ b < 2 ** n /\         *)
(*                                   ?m. b = a + m * 2 ** SUC n              *)
(* EXTEND_LIMIT   : |- !n a. ~(2 ** n) <= extend a (SUC n) /\                *)
(*                           extend a (SUC n) < 2 ** n                       *)
(* EXTEND_11      : |- !n a b. (extend a (SUC n) = extend b (SUC n)) =       *)
(*                                              ?m. a = b + m * 2 ** SUC n   *)
(* EXTEND_LINEAR  : |- !n m x b. extend (m * extend x (SUC n) + b) (SUC n) = *)
(*                                                extend (m * x + b) (SUC n) *)
(* EXTEND_LINEAR_IMP : |- !n f x. (?m b. !x. f x = m * x + b) ==>            *)
(*                                  (extend (f (extend x (SUC n))) (SUC n) = *)
(*                                                     extend (f x) (SUC n)) *)
(*                                                                           *)
(* EXTEND_POS_CALCULATE, EXTEND_NEG_CALCULATE:                               *)
(*     Calculates extend (& a) b or extend (~& a) b using the above theorems *)
(*                                                                           *)
(*****************************************************************************)

val I2N_NUM = store_thm("I2N_NUM",
    ``!a b. i2n (& a) b = a MOD 2 ** b``,RW_TAC int_ss [i2n_def]);

val mod_p1_eq =
    MATCH_MP (DISCH_ALL (MATCH_MP
             (DECIDE ``a < b ==> (a + 1 < b = ~(a = b - 1n))``)
	     (UNDISCH (SPEC_ALL MOD_LESS)))) (SPEC_ALL ZERO_LT_TWOEXP);

val EXTEND_LE_ZERO = store_thm("EXTEND_LE_ZERO",
    ``!a b. extend a b < 0 = BIT (b - 1) (i2n a b)``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [extend_def,i2n_def] THEN
    FULL_SIMP_TAC std_ss [] THENL [
		`?c. a = & c` by Q.EXISTS_TAC `Num a`,
		`?c. (a = ~ & c)` by Q.EXISTS_TAC `Num (~a)`] THEN
    RW_TAC int_ss [INT_OF_NUM,ARITH_PROVE ``(a = ~ & b) = (~a = & b:int)``,
    	   	   ARITH_PROVE ``~(0 <= a) ==> a <= 0i``,
		   ARITH_PROVE ``a - b < 0i = a < b``,MOD_LESS] THEN
    FULL_SIMP_TAC int_ss [ONCE_REWRITE_RULE [INT_ADD_COMM] (GSYM int_sub),
    		  	  int_sub_calc2,DECIDE ``a < 1 = (a = 0n)``,INT_ADD,
			  ARITH_PROVE ``~a - 1 + b = b - (a + 1i)``,
			  mod_p1_eq] THEN
    Cases_on `((c - 1) MOD 2 ** b = 2 ** b - 1)` THEN
    FULL_SIMP_TAC int_ss [MATCH_MP (DECIDE ``0 < b ==> (b - 1 + 1 - b = 0n)``)
    		  (SPEC_ALL ZERO_LT_TWOEXP),
		  DECIDE ``a <= a - b = (b = 0n) \/ (a = 0n)``]);

val EXTEND_ZERO = store_thm("EXTEND_ZERO",
    ``!a b. (extend 0 a = 0) /\ (extend b 0 = 0)``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [extend_def,i2n_def,BIT_def,BITS_THM2,
    	   ZERO_DIV] THEN
    FULL_SIMP_TAC bint_ss [GSYM INT_OF_NUM] THEN
    TRY (POP_ASSUM (SUBST_ALL_TAC o GSYM)) THEN
    FULL_SIMP_TAC bint_ss [INT_OF_NUM] THEN
    `?c. b = ~ & c` by Q.EXISTS_TAC `Num (~ b)` THEN
    TRY (POP_ASSUM SUBST_ALL_TAC THEN Cases_on `c <= 1`) THEN
    FULL_SIMP_TAC int_ss [ARITH_PROVE ``(b = ~ & a) = (~b = & a)``,INT_OF_NUM,
		ARITH_PROVE ``~(0 <= b) ==> b <= 0i``,INT_ADD_CALCULATE,
		INT_SUB_CALCULATE]);

val EXTEND_POS_EQ = store_thm("EXTEND_POS_EQ",
    ``!a b. a < 2 ** (b - 1) ==> (extend (& a) b = & a)``,
    REPEAT GEN_TAC THEN Cases_on `b = 0n` THEN
    RW_TAC bint_ss [extend_def,i2n_def,BIT_RWR,MOD_MOD,
    	   DECIDE ``~(b = 0) ==> (SUC (b - 1) = b)``] THEN
    `a < 2 ** b` by PROVE_TAC [LESS_TRANS,TWOEXP_MONO,
           DECIDE ``~(b = 0) ==> b - 1n < b``] THEN
    FULL_SIMP_TAC int_ss [MOD_LESS]);

val EXTEND_POS_NE = store_thm("EXTEND_POS_NE",
    ``2 ** (b - 1) < a /\ a < 2 ** b ==> (extend (& a) b = & a - 2 ** b)``,
    Cases_on `b = 0n` THEN
    RW_TAC bint_ss [extend_def,i2n_def,BIT_RWR,MOD_MOD,
        DECIDE ``~(b = 0) ==> (SUC (b - 1) = b)``] );

val EXTEND_POS_NEG = store_thm("EXTEND_POS_NEG",
    ``0 < b ==> (extend (& (2 ** (b - 1))) b = ~ & (2 ** (b - 1)))``,
    Cases_on `b` THEN RW_TAC bint_ss [extend_def,i2n_def,BIT_RWR,MOD_MOD] THEN
    RW_TAC int_ss [EXP,int_sub_calc1]);

val thms = [BIT_MOD,DECIDE ``b - 1 < b = 0n < b``,int_sub_calc1,INT_EXP,
            DECIDE ``(a - b = 0n) = (a <= b)``,
	    REWRITE_RULE [GSYM NOT_LESS_EQUAL]
	    		 (MATCH_MP MOD_LESS (SPEC_ALL ZERO_LT_TWOEXP)),
            extend_def,I2N_NUM,LET_DEF,INT_LE,INT_EQ_CALCULATE];

val EXTEND_POS_REC = store_thm("EXTEND_POS_REC",
    ``!a b. 2 ** b <= a ==> (extend (& a) b = extend (& (a - 2 ** b)) b)``,
    REPEAT GEN_TAC THEN Cases_on `0 < b` THEN
    TRY (`SUC (b - 1) = b` by DECIDE_TAC) THEN
    ASM_REWRITE_TAC thms THEN BETA_TAC THEN
    ASM_REWRITE_TAC (BIT_RWR::thms) THEN
    REPEAT STRIP_TAC THEN REPEAT IF_CASES_TAC THEN ASM_REWRITE_TAC thms THEN
    PROVE_TAC [SUB_MOD,ZERO_LT_TWOEXP]);

val EXTEND_POS_CALCULATE = store_thm("EXTEND_POS_CALCULATE",
    ``extend (& a) b =
      	     if a < 2 ** (b - 1) then & a
	     else if (a = 2 ** (b - 1)) /\ 0 < b then ~ & a
	     else if 2 ** (b - 1) < a /\ a < 2 ** b then & a - 2 ** b
	     else extend (& (a - 2 ** b)) b``,
    RW_TAC bint_ss [EXTEND_POS_NEG,EXTEND_POS_EQ,EXTEND_POS_NE] THEN
    MATCH_MP_TAC EXTEND_POS_REC THEN
    REPEAT (FULL_SIMP_TAC arith_ss [NOT_LESS]));

val EXTEND_NEG_EQ = store_thm("EXTEND_NEG_EQ",
    ``a < 2 ** (b - 1) ==> (extend (~ & a) b = ~ & a)``,
    REWRITE_TAC [extend_def,i2n_def,BIT_RWR] THEN RW_TAC bint_ss [] THEN
    FULL_SIMP_TAC bint_ss [ARITH_PROVE ``~a + 1 = 1i - a``] THENL [
		ALL_TAC,CCONTR_TAC] THEN
    `a - 1 < 2 ** b` by NLTLE_TRANS_TAC `2 ** (b - 1)` THEN
    `1 - & a = ~& (a - 1)` by RW_TAC int_ss [int_sub_calc1] THEN
    FULL_SIMP_TAC int_ss [ARITH_PROVE ``~a - b + c = c - (a + b):int``,INT_ADD,
                          int_sub_calc1] THEN
    Cases_on `b` THEN FULL_SIMP_TAC int_ss [NOT_LESS_EQUAL,EXP]);

val EXTEND_NEG_NEG = store_thm("EXTEND_NEG_NEG",
    ``0 < b ==> (extend (~ & (2 ** (b - 1))) b = ~ & (2 ** (b - 1)))``,
    RW_TAC bint_ss [BIT_RWR,extend_def,i2n_def,INT_ADD_CALCULATE,
    	   INT_SUB_CALCULATE,INT_REM_CALCULATE,
	   DECIDE ``(a <= 1) = ~(0n < a) \/ (a = 1n)``] THEN
    FULL_SIMP_TAC bint_ss [INT_ADD_CALCULATE,INT_SUB_CALCULATE,
           DECIDE ``a + 1n <= b = a < b``] THEN
    Cases_on `b` THEN FULL_SIMP_TAC int_ss [EXP] THEN
    FULL_SIMP_TAC int_ss [GSYM EXP]);

val EXTEND_NEG_NE = store_thm("EXTEND_NEG_NE",
    ``2 ** (b - 1) < a  /\ a < 2 ** b ==> (extend (~ (& a)) b = 2 ** b - & a)``,
    Cases_on `b` THEN RW_TAC bint_ss [extend_def,i2n_def,EXTEND_ZERO] THEN
    Cases_on `a <= 1n` THEN
    FULL_SIMP_TAC int_ss [INT_SUB_CALCULATE,INT_ADD_CALCULATE,BIT_RWR] THEN
    FULL_SIMP_TAC int_ss [EXP]);

val lem1 = prove(``2 ** SUC n < a ==>
    	   	     ((~ & (a - 2 ** SUC n) + 1) rem & (2 ** SUC n) =
		     	  ~&( (a - 1) MOD (2 ** SUC n)))``,
    RW_TAC int_ss [INT_SUB_CALCULATE,INT_ADD_CALCULATE] THEN
    (`a = 2 ** SUC n + 1` by DECIDE_TAC ORELSE
     `a - (2 ** SUC n + 1) = (a - 1) - 2 ** SUC n` by DECIDE_TAC) THEN
    ASM_REWRITE_TAC [] THEN TRY (MATCH_MP_TAC SUB_MOD) THEN
    RW_TAC arith_ss []);

val EXTEND_NEG_REC = store_thm("EXTEND_NEG_REC",
    ``2 ** b <= a ==> (extend (~ & a) b = extend (~ & (a - 2 ** b)) b)``,
    Cases_on `b` THEN RW_TAC bint_ss [EXTEND_ZERO] THEN
    `2 <= a /\ 1 <= a` by (Induct_on `n` THEN RW_TAC int_ss [EXP]) THEN
    `(~ & a + 1 = ~ & (a - 1)) /\ (~ & (a - 1) - 1 = ~ & a)` by
         RW_TAC int_ss [INT_SUB_CALCULATE,INT_ADD_CALCULATE] THEN
    RW_TAC (std_ss ++ boolSimps.LET_ss) [extend_def,i2n_def] THEN
    FULL_SIMP_TAC std_ss [ARITH_PROVE ``(0i <= ~ & a) = (a = 0n)``] THEN
    TRY (`a = 2 ** SUC n` by DECIDE_TAC) THEN
    FULL_SIMP_TAC int_ss [BIT_ZERO,BIT_RWR,
    		  ARITH_PROVE ``~ & a - 1 + b = b - & (a + 1)``,
		  DECIDE ``0 < a ==> (a - 1 + 1n = a)``,lem1]);

val EXTEND_NEG_CALCULATE = store_thm("EXTEND_NEG_CALCULATE",
    ``extend (~ & a) b =
    	     if a < 2 ** (b - 1) then ~ & a
	     else if (a = 2 ** (b - 1)) /\ 0 < b then ~ & a
	     else if 2 ** (b - 1) < a /\ a < 2 ** b then 2 ** b - & a
	     else extend (~ & (a - 2 ** b)) b``,
    RW_TAC int_ss [EXTEND_ZERO,EXTEND_NEG_NE,EXTEND_NEG_EQ,EXTEND_NEG_NEG] THEN
    Cases_on `a` THEN MATCH_MP_TAC EXTEND_NEG_REC THEN
    FULL_SIMP_TAC int_ss [NOT_LESS]);

val extend_eq_base = prove(``a < 2 ** SUC n ==>
       (!b. (extend (& a) (SUC n) = b) =
             ~(2 ** n) <= b /\ b < 2 ** n /\ ?m. b = & a + m * 2 ** SUC n) /\
       (!b. (extend (~ & a) (SUC n) = b) =
             ~ (2 ** n) <= b /\ b < 2 ** n /\ ?m. b = ~ & a + m * 2 ** SUC n)``,
    ONCE_REWRITE_TAC [EXTEND_POS_CALCULATE,EXTEND_NEG_CALCULATE] THEN
    RW_TAC int_ss [EXP,ADD1,INT_ADD_CALCULATE,INT_SUB_CALCULATE] THEN
    EQ_TAC THEN NTAC 2 (RW_TAC int_ss []) THEN
    TRY (Q.EXISTS_TAC `0` THEN RW_TAC int_ss [] THEN NO_TAC) THEN
    TRY (Q.EXISTS_TAC `~1` THEN
         RW_TAC int_ss [INT_MUL_CALCULATE,INT_ADD_CALCULATE] THEN NO_TAC) THEN
    TRY (Q.EXISTS_TAC `1` THEN
         RW_TAC int_ss [INT_MUL_CALCULATE,INT_ADD_CALCULATE] THEN NO_TAC) THEN
    INT_CASE_TAC `m` THEN Cases_on `c` THEN REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [LEFT_ADD_DISTRIB,INT_ADD_CALCULATE,INT_MUL_CALCULATE,
                   ADD1,RIGHT_ADD_DISTRIB] THEN
    Cases_on `n'` THEN
    FULL_SIMP_TAC int_ss [ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]);

val EXTEND_EQ = store_thm("EXTEND_EQ",
    ``!n a b. (extend a (SUC n) = b) =
                  ~ (2 ** n) <= b /\ b < 2 ** n /\ ?m. b = a + m * 2 ** SUC n``,
    REPEAT GEN_TAC THEN INT_CASE_TAC `a` THEN completeInduct_on `c` THEN
    Cases_on `c < 2 ** SUC n` THEN
    FULL_SIMP_TAC int_ss [extend_eq_base,NOT_LESS,
                          EXTEND_NEG_REC,EXTEND_POS_REC] THEN
    (Cases_on `c = 0` THEN1
            (POP_ASSUM SUBST_ALL_TAC THEN EQ_TAC THEN
	     RW_TAC int_ss [EXTEND_ZERO] THEN INT_CASE_TAC `m` THEN
 	     TRY (Cases_on `c`) THEN
	     FULL_SIMP_TAC int_ss [])) THEN
    PAT_ASSUM ``!m:'a.P`` (MP_TAC o Q.SPEC `c - 2 ** SUC n`) THEN
    RW_TAC int_ss [NOT_LESS_EQUAL] THEN
    POP_ASSUM (K ALL_TAC) THEN
    EQ_TAC THEN RW_TAC int_ss [] THENL
        (map Q.EXISTS_TAC [`m' + 1`,`m - 1`,`m' - 1`,`m + 1`]) THEN
    RW_TAC int_ss [INT_RDISTRIB,INT_SUB_RDISTRIB,GSYM INT_SUB] THEN
    RW_TAC int_ss [int_sub] THEN
    FIRST [CONV_TAC (AC_CONV (INT_ADD_ASSOC,INT_ADD_COMM)),ARITH_TAC]);

val EXTEND_LIMIT = store_thm("EXTEND_LIMIT",
    ``!n a. ~ (2 ** n) <= extend a (SUC n) /\ extend a (SUC n) < 2 ** n``,
    REPEAT GEN_TAC THEN INT_CASE_TAC `a` THEN completeInduct_on `c` THEN
    ONCE_REWRITE_TAC [EXTEND_POS_CALCULATE,EXTEND_NEG_CALCULATE] THEN
    RW_TAC int_ss [INT_SUB_CALCULATE,INT_ADD_CALCULATE] THEN
    FULL_SIMP_TAC int_ss [NOT_LESS_EQUAL,NOT_LESS,EXP]);

val lem = prove(``?m''. b + m * n + m' * n = b + m'' * n:int``,
    Q.EXISTS_TAC `m + m'` THEN RW_TAC int_ss [INT_RDISTRIB,INT_ADD_ASSOC]);

fun CF m tac v1 v2 (a,g) =
	if exists (free_in m) (g::a) then
		tac v1 (a,g)
	else 	tac v2 (a,g);

val lem2 = prove(``?m. ~ & (2 ** n) <= b + m * & (2 ** SUC n) /\
    	   	   b + m * & (2 ** SUC n) < & (2 ** n)``,
    INT_CASE_TAC `b` THEN completeInduct_on `c` THEN
    (Cases_on `c = 0` THEN1
                  (Q.EXISTS_TAC `0` THEN FULL_SIMP_TAC int_ss [])) THEN
    `c < 2 ** n \/ (c = 2 ** n) \/ 2 ** n < c /\
         c < 2 ** SUC n \/ 2 ** SUC n <= c` by DECIDE_TAC THEN
    TRY (MAP_FIRST (fn x => Q.EXISTS_TAC x THEN
          FULL_SIMP_TAC int_ss [EXP,INT_ADD_CALCULATE,INT_SUB_CALCULATE,
	         INT_MUL_CALCULATE,
                 DECIDE ``0 < a ==> (a < 2 * a) /\ ~(2n * a <= a)``] THEN
          NO_TAC) [`0`,`1`,`~1`]) THEN
    PAT_ASSUM ``!m:'a. P`` (MP_TAC o Q.SPEC `c - 2 ** SUC n`) THEN
    RW_TAC int_ss [] THEN
    FULL_SIMP_TAC int_ss [] THEN IMP_RES_TAC (GSYM INT_SUB) THENL [
          CF ``m:int`` Q.EXISTS_TAC `m + 1` `m' + 1`,
          CF ``m:int`` Q.EXISTS_TAC `m - 1` `m' - 1`] THEN
    FULL_SIMP_TAC int_ss [INT_RDISTRIB,int_sub,INT_NEG_ADD,
    		  INT_ADD_ASSOC,INT_MUL_CALCULATE] THEN
    METIS_TAC [INT_ADD_ASSOC,INT_ADD_COMM]);

val EXTEND_11 = store_thm("EXTEND_11",
    ``!n a b. (extend a (SUC n) = extend b (SUC n)) =
    	 ?m. a = b + m * 2 ** SUC n``,
    REPEAT GEN_TAC THEN EQ_TAC THEN RW_TAC int_ss [EXTEND_EQ,EXTEND_LIMIT] THEN
    RW_TAC int_ss [lem] THEN1
        (Q.EXISTS_TAC `m' - m` THEN RW_TAC int_ss [INT_SUB_RDISTRIB] THEN
	 ARITH_TAC) THEN
     STRIP_ASSUME_TAC lem2 THEN
     Q.EXISTS_TAC `~m + m'` THEN ARITH_TAC);

val EXTEND_LINEAR = store_thm("EXTEND_LINEAR",
    ``!n m x b. extend (m * (extend x (SUC n)) + b) (SUC n) =
    	 extend (m * x + b) (SUC n)``,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [EXTEND_11,
         ARITH_PROVE ``(a + b = c + b + d) = (a = c + d:int)``] THEN
    SUBGOAL_THEN ``?y. extend x (SUC n) = x + y * 2 ** SUC n``
    	STRIP_ASSUME_TAC THEN1
    RW_TAC int_ss [EXTEND_EQ,lem2,
    	   prove(``?m. y * b = m * b:int``,Q.EXISTS_TAC `y` THEN REFL_TAC)] THEN
    Q.EXISTS_TAC `m * y` THEN RW_TAC int_ss [INT_LDISTRIB,INT_MUL_ASSOC]);

val EXTEND_LINEAR_IMP = store_thm("EXTEND_LINEAR_IMP",
    ``!n f x. (?m b. !x. f x = m * x + b) ==>
    	 (extend (f (extend x (SUC n))) (SUC n) = extend (f x) (SUC n))``,
    NTAC 2 (RW_TAC int_ss [EXTEND_LINEAR]));

(*****************************************************************************)
(*    extend (f (extend a (dimindex (:'a)))) (dimindex (:'a))                *)
(*    ======================================================= EXTEND_CONV    *)
(*                extend (f a) (dimindex (:'a))                              *)
(*                                                                           *)
(*    Provided f is a combination of +,*,-,~                                 *)
(*                                                                           *)
(*****************************************************************************)
fun eindex tm = REWRITE_RULE [SUC_SUB_INDEX] (Q.SPEC `dimindex (:'a) - 1` tm);

local
val linear = ``\f. ?m b. !x. f x = m * x + b:int``;
val add = prove(``^linear f /\ ^linear g ==> ^linear (\x. f x + g x)``,
    BETA_TAC THEN REPEAT STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`m + m'`,`b + b'`] THEN
    RW_TAC int_ss [INT_RDISTRIB] THEN ARITH_TAC);
val mul1 = prove(``^linear f ==> ^linear (\x. f x * c)``,
    BETA_TAC THEN REPEAT STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`m * c`,`b * c`] THEN
    RW_TAC int_ss [INT_RDISTRIB] THEN ARITH_TAC);
val mul2 = prove(``^linear f ==> ^linear (\x. c * f x)``,
    BETA_TAC THEN REPEAT STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`m * c`,`b * c`] THEN
    RW_TAC int_ss [INT_RDISTRIB] THEN ARITH_TAC);
val sub = prove(``^linear (\x. a x + ~b x) ==> ^linear (\x. a x - b x)``,
    RW_TAC int_ss [int_sub]);
val neg = prove(``^linear f ==> ^linear (\x. ~ f x)``,
    BETA_TAC THEN REPEAT STRIP_TAC THEN MAP_EVERY Q.EXISTS_TAC [`~m`,`~b`] THEN
    RW_TAC int_ss [INT_RDISTRIB] THEN ARITH_TAC);
val id = prove(``^linear (\x.x)``,
    BETA_TAC THEN MAP_EVERY Q.EXISTS_TAC [`1`,`0`] THEN
    BETA_TAC THEN ARITH_TAC);
val const = prove(``^linear(\x.c)``,
    BETA_TAC THEN MAP_EVERY Q.EXISTS_TAC [`0`,`c`] THEN
    BETA_TAC THEN ARITH_TAC);
val rules = map (CONV_RULE
    	    	(TRY_CONV (LAND_CONV (DEPTH_CONV BETA_CONV))) o BETA_RULE)
	    [add,mul1,mul2,neg,sub,id,const];
val extend = ``extend a (dimindex (:'a))``
fun prove_it tm =
let val x = fst (dest_forall (snd (strip_exists tm)))
    val thm1 = STRIP_QUANT_CONV (STRIP_QUANT_CONV
    	       				(LAND_CONV (UNBETA_CONV x))) tm
    val thm2 = tryfind (CONV_RULE (RAND_CONV
	    (REWR_CONV (GSYM thm1)) ORELSEC (REWR_CONV (GSYM thm1))) o
	     C (HO_PART_MATCH (snd o strip_imp)) (rhs (concl thm1))) rules
    val tms = if is_imp_only (concl thm2) then strip_conj
    	      (fst (dest_imp (concl thm2))) else []
in
    if null tms then thm2 else MATCH_MP thm2 (LIST_CONJ (map prove_it tms))
end;
fun remove e x =
let val thm = (RATOR_CONV (RAND_CONV (UNBETA_CONV e)) THENC
	       (UNDISCH o PART_MATCH (lhs o snd o strip_imp)
	        (eindex EXTEND_LINEAR_IMP))) x;
    val thms1 = map (GSYM o REDEPTH_CONV BETA_CONV) (hyp thm)
    val thms2 = map (prove_it o lhs o concl) thms1
    val thms3 = map2 EQ_MP thms1 thms2
in
    CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV BETA_CONV)))
              (foldl (uncurry PROVE_HYP) thm thms3)
end
in
fun EXTEND_CONV x =
let 	val _  = match_term extend x
	val extends = find_terms (can (match_term extend)) (rand (rator x));
in
	tryfind (C remove x) extends
end
end;

(*****************************************************************************)
(* Signed integer theorems:                                                  *)
(*****************************************************************************)

val sw2i_thm = store_thm("sw2i_thm",
    ``sw2i (x:'a word) = extend (& (w2n x)) (dimindex (:'a))``,
    RW_TAC int_ss [eindex EXTEND_EQ,sw2i_def,BIT_RWR,SUC_SUB_INDEX,
	INT_SUB_CALCULATE,INT_ADD_CALCULATE,w2n_lt_full] THEN
    RW_TAC int_ss [DIMINDEX_DOUBLE] THENL [
		Q.EXISTS_TAC `~1`,Q.EXISTS_TAC `0`] THEN
    RW_TAC int_ss [INT_MUL_CALCULATE,GSYM INT_SUB,GSYM DIMINDEX_DOUBLE,
        w2n_lt_full,INT_SUB_CALCULATE,INT_ADD_CALCULATE]);

val sw2i_LIMIT = Q.GEN `a`
    (REWRITE_RULE [GSYM sw2i_thm] (Q.SPEC `& (w2n (a:'a word))`
        (eindex EXTEND_LIMIT)));

val I2N_LT = store_thm("I2N_LT",
    ``!x b. i2n x b < 2 ** b``,
    RW_TAC arith_ss [i2n_def] THENL [
        `?c. x = & c` by Q.EXISTS_TAC `Num x`,
	`?c. x = ~ & c` by Q.EXISTS_TAC `Num (~x)`] THEN
    RW_TAC int_ss [INT_OF_NUM,ARITH_PROVE ``(x = ~ & y) = (~x = & y)``] THEN1
        ARITH_TAC THEN
    RW_TAC int_ss [ARITH_PROVE ``~ & c + 1 = 1i - & c``,int_sub_calc1,
        ARITH_PROVE ``~ & c - 1 + b = b - (1 + & c)``,INT_ADD,
	DECIDE ``a + 1 <= b = a < b:num``] THEN
    FULL_SIMP_TAC int_ss [] THEN `c = 1` by DECIDE_TAC THEN
    RW_TAC int_ss [ARITH_PROVE ``~1 + b = b - 1i``,int_sub_calc1,
    	   DECIDE ``1 <= a = 0n < a``]);

(*****************************************************************************)
(* i2sw_sw2i : |- !x. i2sw (sw2i x) = sw2sw x                                *)
(* sw2i_i2sw : |- !x. sw2i ((i2sw x) : 'a word) = extend x (dimindex (:'a))  *)
(*****************************************************************************)

val rwr1 = prove(``& (w2n (x:'a word)) - & (2 ** dimindex (:'a)):int =
    	   	     ~ & (2 ** dimindex (:'a) - w2n x)``,
    RW_TAC int_ss [GSYM dimword_def,int_sub_calc1] THEN
    MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN MATCH_ACCEPT_TAC w2n_lt);

val rwra1 = prove(``~ & (dimword (:'a) - w2n x) + 1i =
    	    	      	~ & (dimword (:'a) - w2n (x:'a word) - 1)``,
    RW_TAC std_ss [int_sub_calc1,ONCE_REWRITE_RULE [INT_ADD_COMM]
    	   	  		(GSYM int_sub)] THEN
    ASSUME_TAC (Q.SPEC `x` w2n_lt) THEN
    `w2n (x:'a word) = dimword (:'a) - 1` by ARITH_TAC THEN
    RW_TAC int_ss []);

val mod_add_lem = prove(``0 < a /\ 2 ** (a - 1) <= c /\ c < 2 ** a ==>
				(2 ** b - ((2 ** a - (c + 1)) MOD 2 ** b + 1) =
				    (2 ** b - 2 ** a + c) MOD 2 ** b)``,
    `b <= a \/ a <= b` by DECIDE_TAC THEN IMP_RES_TAC TWOEXP_MONO2 THEN
    RW_TAC arith_ss [LESS_MOD,DECIDE ``b <= a ==> (b - a + c = c:num)``] THEN
    RW_TAC arith_ss [MOD_LESS,MOD_HIGH_EQ_ADD,MOD_HIGH_MOD,
    	   DECIDE ``a < b ==> ((b - (a + 1) = c) = (b - 1n = c + a))``]);

val i2sw = SIMP_RULE (int_ss ++ boolSimps.LET_ss) [] i2sw_def;

val i2sw_sw2i = store_thm("i2sw_sw2i",
    ``!x. i2sw (sw2i x) = sw2sw (x:'a word) : 'b word``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [i2sw,sw2i_def,sw2sw_def,
    	   SIGN_EXTEND_def,rwr1,INT_ADD,DECIDE ``~(a - 1 < a) = ~(0n < a)``,
	   EXTEND_LE_ZERO,I2N_NUM,BIT_MOD,DIMINDEX_GT_0,extend_def,n2w_11,
	   MOD_MOD,dimword_def,w2n_lt_full,MOD_LESS] THEN
    RW_TAC int_ss [i2n_def,ARITH_PROVE ``0i <= ~&a = (a = 0n)``,w2n_lt_full,
	   ARITH_PROVE ``~ & a + 1 = 1i - & a``,int_sub_calc1,
	   REWRITE_RULE [dimword_def] dimword_pos,
	   DECIDE ``a < b ==> (b <= a + 1n = (b = a + 1n))``,
	   ARITH_PROVE ``~1 + a = a - 1i``,DECIDE ``1 <= a = 0n < a``] THENL [
        POP_ASSUM (SUBST_ALL_TAC o MATCH_MP (MATCH_MP
	 	   (DECIDE ``0 < a ==> (a = b + 1) ==> (b = a - 1n)``)
		   (SPEC_ALL ZERO_LT_TWOEXP))) THEN
	RW_TAC std_ss [ZERO_LT_TWOEXP,
	     DECIDE ``0 < a ==> (a - 1n + 1 = a)``] THEN
	MATCH_ACCEPT_TAC MOD_HIGH_SUM,
	RW_TAC int_ss [INT_ADD,int_sub_calc1,ARITH_PROVE ``~a + b = b - a:int``,
	       ARITH_PROVE ``~a - b = ~(a + b:int)``,
	       DECIDE ``a + 1n <= b = a < b``]] THEN
	MATCH_MP_TAC mod_add_lem THEN
	FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0,w2n_lt_full,
	       BIT_RWR,SUC_SUB_INDEX]);

val sw2i_i2sw = store_thm("sw2i_i2sw",
    ``!x. sw2i ((i2sw x):'a word) = extend x (dimindex (:'a))``,
    RW_TAC (int_ss ++ boolSimps.LET_ss) [i2sw,sw2i_def,sw2sw_def,
    	   SIGN_EXTEND_def,rwr1,INT_ADD,dimword_def,w2n_lt_full,
	   EXTEND_LE_ZERO,I2N_NUM,BIT_MOD,DECIDE ``~(a - 1 < a) = ~(0n < a)``,
	   DIMINDEX_GT_0,extend_def,n2w_11,MOD_MOD,MOD_LESS,w2n_n2w,I2N_LT]);

(*****************************************************************************)
(* sw2i_twocomp : |- !a. sw2i (- a) = extend (~ (sw2i a)) (dimindex (:'a))   *)
(* sw2i_add     : |- !a. sw2i (a + b) =                                      *)
(*                       extend (sw2i a + sw2i b) (dimindex (:'a))           *)
(* sw2i_sub     : |- !a. sw2i (a - b) =                                      *)
(*                       extend (sw2i a - sw2i b) (dimindex (:'a))           *)
(*****************************************************************************)

val mod_lem = prove(``0 < b ==> ((?m. & (a MOD b) = c + m * & b) =
    	      		(?m. & a = c + m * & b))``,
    completeInduct_on `a` THEN `a < b \/ b <= a` by DECIDE_TAC THEN
    RW_TAC int_ss [MOD_LESS] THEN
    PAT_ASSUM ``!a:'a.P`` (MP_TAC o Q.SPEC `a - b`) THEN
    RW_TAC arith_ss [SUB_MOD] THEN
    IMP_RES_TAC (GSYM INT_SUB) THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        Q.EXISTS_TAC `m + 1`,Q.EXISTS_TAC `m - 1`] THEN
    FULL_SIMP_TAC int_ss [INT_RDISTRIB,INT_SUB_RDISTRIB] THEN ARITH_TAC);

val extend_mod = prove(``!b a. extend (& (a MOD 2 ** SUC b)) (SUC b) =
    	       	 	           extend (& a) (SUC b)``,
    RW_TAC int_ss [EXTEND_11,mod_lem] THEN
    Q.EXISTS_TAC `0` THEN ARITH_TAC);

val sw2i_twocomp = store_thm("sw2i_twocomp",
    ``!a. sw2i (- a:'a word) = extend (~ (sw2i a)) (dimindex (:'a))``,
    REWRITE_TAC [sw2i_thm] THEN
    CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    RW_TAC int_ss [mod_lem,eindex EXTEND_11,
    	   	   word_2comp_def,w2n_n2w,dimword_def] THEN
    Q.EXISTS_TAC `1` THEN
    RW_TAC int_ss [INT_ADD_CALCULATE,GSYM NOT_LESS_EQUAL] THEN
    PROVE_TAC [NOT_LESS_EQUAL,NOT_LESS,LESS_IMP_LESS_OR_EQ,w2n_lt_full]);

val sw2i_add = store_thm("sw2i_add",
    ``!a b. sw2i (a + (b:'a word)) =
    	    extend (sw2i a + sw2i b) (dimindex (:'a))``,
    REWRITE_TAC [sw2i_thm] THEN CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    REWRITE_TAC [word_add_def,w2n_n2w,INT_ADD] THEN
    RW_TAC int_ss [eindex EXTEND_11,mod_lem,dimword_def] THEN
    Q.EXISTS_TAC `0` THEN ARITH_TAC);

val sw2i_sub = store_thm("sw2i_sub",
    ``!a b. sw2i (a - (b:'a word)) =
    	    	 extend (sw2i a - sw2i b) (dimindex (:'a))``,
    REWRITE_TAC [sw2i_thm] THEN CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    RW_TAC int_ss [word_sub_def,word_add_def,word_2comp_def,w2n_n2w,
    	   dimword_def,eindex EXTEND_11,mod_lem] THEN
    Cases_on `w2n b = 0` THEN RW_TAC int_ss [] THENL
    	     (map Q.EXISTS_TAC [`0`,`1`]) THEN
    RW_TAC int_ss [w2n_lt_full,ARITH_PROVE ``a - b + c = (a + c) + ~b:int``,
    	   INT_ADD_CALCULATE] THEN
    TRY (MATCH_MP_TAC (DECIDE ``c < b ==> (a + (b - c) = a + b - c:num)``)) THEN
    PROVE_TAC [w2n_lt_full,NOT_LESS_EQUAL,
               DECIDE ``a < b ==> ~(c + b < a:num)``]);

val sw2i_mul = store_thm("sw2i_mul",
    ``!a b. sw2i (a * b : 'a word) =
    	    	 extend (sw2i a * sw2i b) (dimindex (:'a))``,
    REWRITE_TAC [sw2i_thm,word_mul_def,w2n_n2w,dimword_def] THEN
    CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    REWRITE_TAC [word_mul_def,w2n_n2w,dimword_def] THEN
    RW_TAC int_ss [eindex EXTEND_11,mod_lem] THEN
    Q.EXISTS_TAC `0` THEN ARITH_TAC);

(*****************************************************************************)
(* IAND_COMM : |- !a b. iand a b = iand b a                                  *)
(* IAND_ZERO : |- !a. (iand a 0 = 0) /\ (iand 0 a = 0)                       *)
(* IAND_ID   : |- !a. iand a a = a                                           *)
(*****************************************************************************)

val bitwise_mod_lem = prove(``BITWISE a b c d MOD 2 ** a = BITWISE a b c d``,
    PROVE_TAC [BITWISE_LT_2EXP,ZERO_LT_TWOEXP,LESS_MOD]);

val AND_ZERO = prove(``!x a. (BITWISE x $/\ a 0 = 0) /\
    	       		     (BITWISE x $/\ 0 a = 0)``,
    Induct THEN RW_TAC int_ss [BITWISE_DIV,BITWISE_ZERO]);

val bitwise_iand1 = prove(``!x a b. a < 2 ** x /\ b < 2 ** x ==>
    		    	       (& (BITWISE x $/\ a b) = iand (& a) (& b))``,
    Induct THEN ONCE_REWRITE_TAC [iand_def] THEN
    RW_TAC bint_ss [BITWISE_DIV,BITWISE_ZERO,ODD_MOD2_LEM,AND_ZERO,
        ARITH_PROVE ``(& (2 * a) = 2i * b) = (& a = b)``,
        ARITH_PROVE ``(& (2 * a + 1) = 2i * b + 1) = (& a = b)``] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN RW_TAC int_ss [DIV_LT_X,GSYM EXP]);

val bitwise_iand2 = MATCH_MP bitwise_iand1
    (REWRITE_RULE [dimword_def] (CONJ (Q.SPEC `a` w2n_lt) (Q.SPEC `b` w2n_lt)));

val bitwise_iand3 = prove(``& (2 ** (dimindex (:'a)) -
    		  BITWISE (dimindex (:'a)) $/\ (w2n a) (w2n b)) =
		  	  2i ** (dimindex (:'a)) - iand (& (w2n (a:'a word)))
			     	(& (w2n (b:'a word)))``,
    RW_TAC int_ss [GSYM bitwise_iand2,int_sub_calc1] THEN
    METIS_TAC [BITWISE_LT_2EXP,NOT_LESS_EQUAL,LESS_IMP_LESS_OR_EQ]);

val div2_lem = prove(``~ & a / 2 = if EVEN a then ~ & (a DIV 2) else
    	       		   ~ & (a DIV 2 + 1)``,
    REPEAT (RW_TAC int_ss [MOD2_ODD_EVEN,EVEN,int_div,INT_ADD_CALCULATE] THEN
    POP_ASSUM MP_TAC));

val IAND_COMM = store_thm("IAND_COMM",``!a b. iand a b = iand b a``,
    GEN_TAC THEN INT_CASE_TAC `a` THEN
    completeInduct_on `c` THEN ONCE_REWRITE_TAC [iand_def] THEN
    GEN_TAC THEN REPEAT IF_CASES_TAC THEN
    ASM_REWRITE_TAC [LET_DEF] THEN BETA_TAC THEN
    REWRITE_TAC [div2_lem] THEN
    RW_TAC int_ss [ARITH_PROVE ``~(2 * a + 1i = 2 * b)``] THEN
    TRY (FIRST_ASSUM (MATCH_MP_TAC o CONV_RULE
    	(STRIP_QUANT_CONV RIGHT_IMP_FORALL_CONV))) THEN
    FULL_SIMP_TAC int_ss [DIV_LT_X,DECIDE ``c < 2 * c = 0n < c``,
        DECIDE ``0 < b ==> (a + 1 < b = a < b - 1n)``,
	DECIDE ``c < 2 * (c - 1) = 2n < c``] THEN
    CCONTR_TAC THEN `c = 2` by DECIDE_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [EVEN]);

val IAND_ZERO = store_thm("IAND_ZERO",
    ``!a. (iand a 0 = 0) /\ (iand 0 a = 0)``,
    ONCE_REWRITE_TAC [iand_def] THEN RW_TAC int_ss []);

fun two_rule x = REWRITE_RULE [DECIDE ``~(0 = 2n)``,DECIDE ``0 < 2n``]
    	       	 (Q.SPEC `2` x);

val IAND_ID = store_thm("IAND_ID",``!a. iand a a = a``,
    GEN_TAC THEN INT_CASE_TAC `a` THEN completeInduct_on `c` THEN
    ONCE_REWRITE_TAC [iand_def] THEN
    NTAC 2 (RW_TAC bint_ss [DIV_MULT_THM2,INT_ADD_CALCULATE,
    	   	   DECIDE ``(a - b = a) = (a = 0) \/ (b = 0n)``,DIV_LE_X,
		   int_div,int_mod,INT_SUB_CALCULATE,INT_MUL_CALCULATE,NOT_MOD2,
		   IAND_ZERO,DECIDE ``(a DIV b = 0) = (a DIV b <= 0)``] THEN
           REPEAT (POP_ASSUM MP_TAC)) THEN
    REPEAT STRIP_TAC THEN
    Cases_on `c = 2` THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC int_ss [] THEN
    TRY (pTAC ``iand a b`` (rand o rand o rand)) THEN
    FULL_SIMP_TAC int_ss [LEFT_ADD_DISTRIB,DIV_MULT_THM2] THEN
    DISJ_CASES_TAC (Q.SPEC `c` EVEN_OR_ODD) THEN
    IMP_RES_TAC EVEN_ODD_EXISTS THEN
    FULL_SIMP_TAC int_ss [ADD1,ONCE_REWRITE_RULE [MULT_COMM] MOD_MULT,
    		  	  ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]);

(*****************************************************************************)
(* sw2i_and : |- !a b. sw2i (a && b) = iand (sw2i a) (sw2i b)                *)
(*****************************************************************************)

val exp_add_lem = prove(``!x. (2 ** x + 1) DIV 2 = 2 ** (x - 1)``,
    Induct THEN RW_TAC arith_ss [EXP,ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]);

val rwr1 = prove(``!b n. ~ & (2 * 2 ** n - b) / 2 = ~ & (2 ** n - b DIV 2)``,
    REPEAT GEN_TAC THEN DISJ_CASES_TAC (Q.SPEC `b` EVEN_OR_ODD) THEN
    IMP_RES_TAC EVEN_ODD_EXISTS THEN
    Cases_on `2 ** n <= m` THEN
    RW_TAC int_ss [GSYM LEFT_SUB_DISTRIB,ADD1,
    	 DECIDE ``a <= b ==> (a - b = 0n)``,
    ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,
         ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT,
	 DECIDE ``~(a <= b) ==> (2 * a - (2 * b + 1) = 2 * (a - b) - 1n)``] THEN
    RW_TAC int_ss [int_div,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,MOD2_ODD_EVEN,
    	 EVEN_MULT,EVEN_SUB,DIV2_MULT_SUB1,INT_ADD_CALCULATE]);

val rwr2 = SIMP_RULE arith_ss [] (Q.SPEC `0` rwr1);

val iand_lem1 = prove(``!a x. a < 2 ** x ==> (iand (~ & (2 ** x - a))
    	      		   (~ & (2 ** x)) = ~ & (2 ** x))``,
    completeInduct_on `a` THEN Cases THEN ONCE_REWRITE_TAC [iand_def] THEN
    RW_TAC bint_ss [rwr1,rwr2,EXP] THEN1
        FULL_SIMP_TAC int_ss [int_mod,rwr1,rwr2,INT_SUB_CALCULATE,
	    INT_ADD_CALCULATE,INT_MUL_CALCULATE] THEN
    Cases_on `a = 0` THEN TRY (POP_ASSUM SUBST_ALL_TAC) THEN
    PAT_ASSUM ``!m:'a. P`` (MP_TAC o Q.SPEC `a DIV 2`) THEN
    RW_TAC int_ss [DIV_LT_X] THEN
    FULL_SIMP_TAC int_ss [IAND_ID,INT_MUL_CALCULATE]);

val div2_lem = prove(``!a b. a DIV 2 + b DIV 2 < a + b = 0 < a \/ 0 < b``,
    REPEAT GEN_TAC THEN EQ_TAC THEN Cases_on `0 < a` THEN Cases_on `0 < b` THEN
    FULL_SIMP_TAC arith_ss [DECIDE ``~(0 < a) = (a = 0n)``] THEN
    MATCH_MP_TAC LT_ADD2 THEN RW_TAC arith_ss [DIV_LT_X]);

val iand_top1 = prove(``b < 2 ** a ==> (iand (& (2 ** a - 1)) (& b) = & b)``,
    `2 ** a - 1 < 2n ** a` by ALL_TAC THEN
    RW_TAC int_ss [Q.SPECL [`a`,`2 ** a - 1`,`b`] (GSYM bitwise_iand1),
    	   BITWISE_TOP]);

val sub_mod_lem = prove(``& a - & (a - a MOD 2) = & (a MOD 2)``,
    DISJ_CASES_TAC (Q.SPEC `a` EVEN_OR_ODD) THEN Cases_on `a` THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [int_sub_calc1,GSYM MOD2_ODD_EVEN]);

val sub_mod_lem2 = prove(``a < 2 * 2 ** n ==>
    	(& (2 * 2 ** n - (a - a MOD 2)) - & (2 * 2 ** n - a) = & (a MOD 2))``,
    DISJ_CASES_TAC (Q.SPEC `a` EVEN_OR_ODD) THEN Cases_on `a` THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [int_sub_calc1,GSYM MOD2_ODD_EVEN]);

val lem2 = prove(``!n a. ~(a = 0) /\ a < 2 * 2 ** n ==>
    	 (& (2 * 2 ** n - (a - 1)) - & (2 * 2 ** n - a) = 1)``,
    Induct THEN
    RW_TAC int_ss [ARITH_PROVE ``(a - b = c) = (a = b + c:int)``,INT_ADD,
    	   	   INT_EQ_CALCULATE]);

val lem3 = prove(``!a. (2 * 2 ** a - 1) MOD 2 = 1``,
    Induct THEN RW_TAC arith_ss [MOD2_ODD_EVEN,ODD_SUB,ODD_MULT,EXP,
    	   	DECIDE ``0 < a ==> 1n < 4 * a``]);

val iand_nbit = prove(``!b n. b < 2 ** n ==> (iand (~ & (2 ** n)) (& b) = 0)``,
    GEN_TAC THEN completeInduct_on `b` THEN Cases THEN
    ONCE_REWRITE_TAC [iand_def] THEN
    RW_TAC bint_ss [int_mod,rwr1,rwr2,EXP,INT_SUB_CALCULATE,
    	   INT_ADD_CALCULATE,INT_MUL_CALCULATE] THEN
    FIRST_ASSUM (MATCH_MP_TAC o CONV_RULE (STRIP_QUANT_CONV
	RIGHT_IMP_FORALL_CONV THENC REWRITE_CONV [AND_IMP_INTRO])) THEN
    RW_TAC int_ss [DIV_LT_X]);

val IAND_NEG_TAC =
    NTAC 2 GEN_TAC THEN completeInduct_on `a + b` THEN
    ONCE_REWRITE_TAC [iand_def] THEN NTAC 3 STRIP_TAC THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases THEN REWRITE_TAC [EXP,INT_EQ_CALCULATE,INT_EXP,
    	  DECIDE ``(a - b = 0n) = (a <= b)``,DECIDE ``(a < 1n) = (a = 0n)``,
	  DECIDE ``(a - b = 1) = (a = 1n + b)``,DECIDE ``~(1 = 0n)``,
          SIMP_RULE int_ss [] (Q.SPECL [`i`,`2`] int_mod),LET_DEF,
	  SIMP_RULE arith_ss [] (Q.SPECL [`i`,`2`] INT_DIV),rwr1,rwr2,
	  INT_MUL_CALCULATE,INT_ADD_CALCULATE,RIGHT_SUB_DISTRIB,
          ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT_THM2] THEN
    POP_ASSUM  (MP_TAC o Q.SPEC `a DIV 2 + b DIV 2`) THEN1 RW_TAC int_ss [] THEN
    REPEAT IF_CASES_TAC THEN BETA_TAC THEN
    ASM_REWRITE_TAC [NOT_LESS_EQUAL,two_rule ZERO_DIV,
          two_rule (Q.SPECL [`x`,`y`] DIV_LT_X),ADD_CLAUSES,ZERO_LT_TWOEXP,
	  MULT_CLAUSES,DECIDE ``b < b * 2 = 0n < b``,ZERO_LESS_MULT,
	  INT_SUB_LZERO,INT_EQ_CALCULATE,DECIDE ``(a = 0) = ~(0n < a)``,
	  DECIDE ``0 < 2n /\ ~(0 < 0n) /\ 0 < 1n``,
	  DECIDE ``(1 = 1 - b) = (b = 0n)``,div2_lem,sub_mod_lem,
	  DECIDE ``b < 1 = (b = 0n)``,SUB_0,INT_ADD_CALCULATE] THEN
    RW_TAC int_ss [] THEN
    IMP_RES_TAC (REWRITE_RULE [GSYM NOT_LESS_EQUAL] sub_mod_lem2) THEN
    FULL_SIMP_TAC int_ss [ARITH_PROVE ``(~& (2 * a) = 2 * b) = (~ & a = b)``,
         sub_mod_lem,
	 ARITH_PROVE ``(2 * i + 1 - & (2 * b) = 2 * j + 1i) = (i - & b = j)``,
	 ARITH_PROVE ``(2 * i - & (2 * b) = 2i* j) = (i - & b = j)``] THEN
    TRY (MAP_FIRST (fn x => x by (RW_TAC arith_ss [DIV_LT_X] THEN NO_TAC) THEN
                   POP_ASSUM SUBST_ALL_TAC)
         [`a DIV 2 < 2 ** n /\ (b = 2 * 2 ** n - 1)`,
          `b DIV 2 < 2 ** n /\ (a = 2 * 2 ** n - 1)`]) THEN
    TRY (FIRST_ASSUM (MATCH_MP_TAC o CONV_RULE (STRIP_QUANT_CONV
           RIGHT_IMP_FORALL_CONV THENC REWRITE_CONV [AND_IMP_INTRO])) THEN
	      RW_TAC int_ss [DIV_LT_X]) THEN
    TRY (MATCH_MP_TAC (GSYM (ONCE_REWRITE_RULE [IAND_COMM] iand_lem1)) THEN
    	   RW_TAC int_ss [DIV_LT_X]) THEN
    TRY (MATCH_MP_TAC (GSYM iand_lem1) THEN RW_TAC int_ss [DIV_LT_X]) THEN
    REPEAT (PAT_ASSUM ``a = & (b MOD 2)`` (K ALL_TAC)) THEN
    PAT_ASSUM ``!m:'a.P`` (K ALL_TAC) THEN
    FULL_SIMP_TAC bool_ss [DECIDE ``(a - 1 + 1 = (if 0 < a then a else 1n))``,
          ZERO_LESS_MULT,ZERO_LT_TWOEXP,DECIDE ``0 < 2n``,
	  MATCH_MP DIV2_MULT_SUB1 (SPEC_ALL ZERO_LT_TWOEXP),NOT_MOD2] THEN
    RW_TAC std_ss [INT_MUL,iand_top1,
          ONCE_REWRITE_RULE [IAND_COMM] iand_top1] THEN
    RW_TAC int_ss [INT_EQ_SUB_RADD,INT_ADD_CALCULATE,DIV_MULT_THM2] THEN
    TRY (METIS_TAC [REWRITE_RULE [GSYM NOT_LESS_EQUAL] lem2,lem3,
	  SIMP_RULE arith_ss [EXP,GSYM (CONJUNCT1 NOT_MOD2)]
                  (Q.SPECL [`SUC n`,`1`] MOD_HIGH_MOD)]);

val iand_neg1 = prove(``!a b x. a < 2 ** x /\ b < 2 ** x ==>
                        (iand (& a) (& b) - & 2 ** x =
			 iand (~ & (2 ** x - a)) (~ & (2 ** x - b)))``,
     IAND_NEG_TAC);

val iand_neg2 = prove(``!a b x. a <  2 ** x /\ b < 2 ** x ==>
    	      		   (iand (& a) (& b) = iand (~ & (2 ** x - a)) (& b))``,
    IAND_NEG_TAC THEN MATCH_MP_TAC iand_nbit THEN RW_TAC arith_ss [DIV_LT_X]);


val sw2i_and = store_thm("sw2i_and",
    ``!a b. sw2i (a && b) = iand (sw2i a) (sw2i b)``,
    REWRITE_TAC [REWRITE_RULE [n2w_w2n]
          (Q.SPECL [`w2n a`,`w2n b`] word_and_n2w)] THEN
    RW_TAC int_ss [sw2i_def,w2n_n2w,BIT_MOD,BITWISE_THM,DIMINDEX_GT_0,
          DECIDE ``0 < a ==> (a - 1n < a)``,dimword_def] THEN
    FULL_SIMP_TAC int_ss [TOP_BIT_LE,int_sub_calc1,w2n_lt_full,
    REWRITE_RULE [GSYM NOT_LESS_EQUAL] MOD_LESS,bitwise_mod_lem,
          bitwise_iand2,bitwise_iand3,
	  REWRITE_RULE [GSYM NOT_LESS_EQUAL,INT_EXP] iand_neg1,
	  REWRITE_RULE [GSYM NOT_LESS_EQUAL,INT_EXP] iand_neg2,
	  ONCE_REWRITE_RULE [IAND_COMM]
	      (REWRITE_RULE [GSYM NOT_LESS_EQUAL,INT_EXP] iand_neg2)]);

(*****************************************************************************)
(* sw2i_not : |- !a. sw2i (~a) = inot (sw2i a)                               *)
(*****************************************************************************)

val sw2i_not = store_thm("sw2i_not",``!a. sw2i (~a) = inot (sw2i a)``,
    REWRITE_TAC [inot_def,WORD_NOT,sw2i_sub,sw2i_twocomp] THEN
    REWRITE_TAC [sw2i_thm] THEN CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    RW_TAC int_ss [eindex EXTEND_EQ,eindex EXTEND_LIMIT,
	   ARITH_PROVE ``a + 1i <= b = a < b``,
	   ARITH_PROVE ``~(a + 1i) < b = ~b <= a``,word_1_n2w] THEN
    RW_TAC int_ss [ARITH_PROVE ``(~(a + 1) = ~b - 1 + m) = (b = a + m)``] THEN
    Cases_on `w2n a < 2 ** (dimindex (:'a) - 1)` THENL
    	     (map Q.EXISTS_TAC [`0`,`1`]) THEN
    RW_TAC int_ss [GSYM sw2i_thm,sw2i_def,BIT_RWR,SUC_SUB_INDEX,w2n_lt_full]);

(*****************************************************************************)
(* sw2i_div : |- !a b. ~(b = 0w) ==> (sw2i (a / b) =                         *)
(*                             extend (sw2i a quot sw2i b) (dimindex (:'a))) *)
(*****************************************************************************)

val num_msb = REWRITE_RULE [n2w_w2n] (Q.SPEC `w2n a` word_msb_n2w);

val lem1 = prove(``~(b = 0w) /\ ~word_msb a /\ ~word_msb b ==>
    	   	       (& (w2n (a / b)) = & (w2n a) / & (w2n b))``,
     REPEAT STRIP_TAC THEN
     `0 < w2n b` by METIS_TAC [w2n_eq_0,DECIDE ``~(a = 0) = 0n < a``] THEN
     RW_TAC int_ss [word_sdiv_def,word_div_def,w2n_n2w,dimword_def] THEN
     NLELT_TRANS_TAC `w2n a` THEN
     RW_TAC int_ss [w2n_lt_full,DIV_LESS_EQ]);

val plem1 = prove(``!b. ~(b = 0w : 'a word) ==>
      ((w2n (a:'a word) DIV w2n b) MOD 2 ** dimindex (:'a) = w2n a DIV w2n b)``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_MOD THEN
    NLELT_TRANS_TAC `w2n a` THEN CONJ_TAC THEN
    TRY (MATCH_MP_TAC DIV_LESS_EQ) THEN
    RW_TAC int_ss [w2n_lt_full,w2n_eq_0,DECIDE ``0 < b = ~(b = 0n)``]);

val plem2 = REWRITE_RULE [WORD_NEG_EQ_0] (Q.SPEC `- b` plem1);

val plem3 = prove(``!n. 0 < n ==> (2 ** (n - 1) <= (2 ** n - x) MOD 2 ** n =
    	    		  0 < x /\ x <= 2 ** (n - 1))``,
    Cases THEN Cases_on `x` THEN
    RW_TAC int_ss [DIVMOD_ID,
           DECIDE ``a <= b - c = a + c <= b:num \/ (a = 0n)``] THEN
    RW_TAC int_ss [EXP]);

val plem4 = REWRITE_RULE [DIMINDEX_GT_0] (Q.SPEC `dimindex (:'a)` plem3);

val plem5 = GSYM (REWRITE_RULE [w2n_n2w]
    	    	 	(PART_MATCH rhs w2n_eq_0 ``n2w a = 0w``));

val plem6 = prove(``0 < b ==> ((a DIV b = 0) = a < b)``,
    RW_TAC int_ss [DECIDE ``(a = 0) = a < 1n``,DIV_LT_X]);

val slem = prove(``!a b D. 0 < b /\ a:num < D ==> a * D + D < b + D ** 2``,
    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_ADD_1 THEN
    REWRITE_TAC [GSYM (EVAL ``1 + 1n``),EXP_ADD,EXP_1] THEN
    RW_TAC arith_ss [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]);

val msb_div = prove(``~(b = 0w) /\ ~(b = UINT_MAXw) ==>
    	    (word_msb (a / b) = ~(word_msb a = word_msb b) /\ ~(a / b = 0w))``,
    REPEAT STRIP_TAC THEN
    `0 < w2n b /\ 0 < w2n (- b)` by METIS_TAC
       [DECIDE ``0 < a = ~(a = 0n)``,w2n_eq_0,WORD_NEG_EQ_0] THEN
    Cases_on `a / b = 0w` THEN POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [WORD_NEG_EQ_0,num_msb,word_sdiv_def,BIT_RWR,SUC_SUB_INDEX,
           w2n_lt_full,NOT_LESS_EQUAL,word_div_def,w2n_n2w,dimword_def,plem1,
	   plem2,plem4,plem5,plem6] THEN
    RW_TAC int_ss [word_2comp_n2w,w2n_n2w,dimword_def,plem1,plem2,plem4,plem6,
    	   plem5,X_LT_DIV] THEN
    RW_TAC int_ss [DIMINDEX_DOUBLE,
           DECIDE ``a <= 2 * a - b = (a = 0n) \/ b <= a``] THENL [
        ALL_TAC,NLE_TRANS_TAC `w2n (- a)`,
	NLE_TRANS_TAC `w2n a`,NLELT_TRANS_TAC `w2n a`] THEN
    RW_TAC int_ss [DIV_LESS_EQ,word_2comp_def,w2n_n2w,
    	   dimword_def,DIMINDEX_DOUBLE] THEN
    `0 < 2 ** dimindex (:'a) - w2n b` by ALL_TAC THEN
    Cases_on `w2n a = 0` THEN
    RW_TAC int_ss [GSYM DIMINDEX_DOUBLE,DIV_LT_X,w2n_lt_full,
    	   DECIDE ``0n < a - b = b < a``,ZERO_LESS_MULT,LEFT_SUB_DISTRIB] THEN
    IMP_RES_TAC LESS_EQUAL_ADD THEN
    RW_TAC int_ss [DIMINDEX_DOUBLE,DECIDE ``2 * a < b + a + c = a < b + c:num``,
    	   RIGHT_ADD_DISTRIB] THEN
    `p < 2 ** (dimindex (:'a) - 1)` by METIS_TAC [TIMES2,LT_ADD_LCANCEL,
           DIMINDEX_DOUBLE,w2n_lt_full] THEN
    MATCH_MP_TAC (DECIDE ``(D:num) + a * D < b + D ** 2 /\ a * D < D ** 2 ==>
    		 	 D < b + (D ** 2 - a * D)``) THEN
    REWRITE_TAC [GSYM (EVAL ``1 + 1n``),EXP_ADD,EXP_1] THEN
    RW_TAC int_ss [] THEN
    Cases_on `p' = 0` THEN RW_TAC int_ss [] THENL [
        REWRITE_TAC [REWRITE_RULE [MULT_CLAUSES]
		    (GSYM (Q.SPECL [`a`,`1`,`b`] RIGHT_ADD_DISTRIB)),
		    GSYM (EVAL ``1 + 1n``),EXP_ADD,EXP_1,LT_MULT_RCANCEL] THEN
        RW_TAC int_ss [DECIDE ``a + 1 < b = a < b /\ ~(a = b - 1n)``] THEN
	CCONTR_TAC THEN
	FULL_SIMP_TAC int_ss [GSYM DIMINDEX_DOUBLE,word_T_def,
		      UINT_MAX_def,dimword_def] THEN
        METIS_TAC [n2w_w2n],
	MATCH_MP_TAC slem] THEN
    RW_TAC int_ss []);

val lem2 = prove(``~(b = 0w) /\ (w2n a = 0) ==> (a / b = 0w)``,
    `w2n b < 2 ** dimindex (:'a)` by ALL_TAC THEN
    RW_TAC int_ss [word_sdiv_def,word_div_def,word_2comp_def,w2n_n2w,
           dimword_def,ZERO_DIV,GSYM w2n_eq_0,w2n_lt_full]);

val lem3 = prove(``~(a = 0) /\ ~(b = 0) ==> (((2 ** n - a) DIV b) MOD 2 ** n =
    	   	       	 (2 ** n - a) DIV b)``,
    Cases_on `2 ** n <= a` THEN
    RW_TAC int_ss [DECIDE ``a <= b ==> (a - b = 0n)``,ZERO_DIV] THEN
    FULL_SIMP_TAC int_ss [NOT_LESS_EQUAL] THEN IMP_RES_TAC LESS_ADD THEN
    POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN RW_TAC int_ss [] THEN
    NLELT_TRANS_TAC `p` THEN RW_TAC int_ss [DIV_LESS_EQ]);

val lem4 = prove(``(w2n a = 0) ==> ~word_msb a``,
    RW_TAC int_ss [num_msb,BIT_RWR]);

val lem5 = prove(``~(w2n a = 0) ==> (2 ** dimindex (:'a) - w2n (a:'a word))
    	   		 DIV (2 ** dimindex (:'a) - w2n (b:'a word))
			     < 2 ** dimindex (:'a)``,
    DISCH_TAC THEN NLELT_TRANS_TAC `2 ** dimindex (:'a) - w2n a` THEN
    RW_TAC int_ss [DIV_LESS_EQ,DECIDE ``a < b ==> 0n < b - a``,w2n_lt_full]);

val lem6 = prove(``~(w2n a = 0) ==> ~(w2n b = 0) ==>
    	   	(2 ** dimindex (:'a) - w2n (a:'a word)) DIV w2n (b:'a word)
			< 2 ** dimindex (:'a)``,
    REPEAT DISCH_TAC THEN NLELT_TRANS_TAC `2 ** dimindex (:'a) - w2n a` THEN
    RW_TAC int_ss [DIV_LESS_EQ,DECIDE ``a < b ==> 0n < b - a``,w2n_lt_full]);

val lem7 = prove(``(2 ** a - b) MOD 2 ** a = if b = 0 then 0 else 2 ** a - b``,
    RW_TAC arith_ss []);

val lem8 = prove(``~(b = 0) /\ (a DIV b = 0) ==> (a MOD b = a)``,
    REPEAT (RW_TAC int_ss [DECIDE ``(a = 0) = a < 1n``,DIV_LT_X,
        DECIDE ``~(b = 0n) = 0 < b``] THEN REPEAT (POP_ASSUM MP_TAC)));

val lem9 = prove(``~(b = 0) ==> ((a DIV b = 0) = a < b)``,
    REPEAT (RW_TAC int_ss [DECIDE ``(a = 0) = a < 1n``,DIV_LT_X,
        DECIDE ``~(b = 0n) = 0 < b``] THEN REPEAT (POP_ASSUM MP_TAC)));

val slem1 = prove(``a < 2 ** D /\ 2 ** D <= b /\ b < 2 * 2 ** D /\
    	    	      ~(b = 2 * 2 ** D - 1) ==>
		           a < 2n * 2 ** D * (2 * 2 ** D - b)``,
    STRIP_TAC THEN NLT_TRANS_TAC `2 * 2 ** D` THEN
    RW_TAC int_ss [REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`D`,`1`,`p`]
    	   LT_MULT_LCANCEL)]);

val sw2i_div_1 = prove(``!a b. ~(b = 0w) /\ ~(b = UINT_MAXw) ==>
    	       (sw2i (a / b : 'a word) = (sw2i a) quot (sw2i b))``,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP msb_div) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC int_ss [sw2i_def,GSYM num_msb,lem1,msb_div] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [] THEN
    RW_TAC int_ss [word_0_n2w,int_sub_calc1,w2n_lt_full] THEN
    `~(w2n b = 0)` by ASM_REWRITE_TAC [w2n_eq_0] THEN
    TRY (`~(w2n a = 0)` by (CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
        MAP_EVERY IMP_RES_TAC [lem2,lem4] THEN NO_TAC)) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LESS_MOD o MATCH_MP lem5) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP lem6) THEN
    POP_ASSUM IMP_RES_TAC THEN RW_TAC int_ss [int_quot,word_div_def,
    	      word_sdiv_def,word_2comp_def,w2n_n2w,
	      dimword_def,w2n_lt,plem6,lem7] THEN
    TRY (PAT_ASSUM ``~(a / b= 0w:'a word)`` MP_TAC) THEN
    TRY (PAT_ASSUM ``a / b= 0w:'a word`` MP_TAC) THEN
    RW_TAC int_ss [word_div_def,word_sdiv_def,word_2comp_def,w2n_n2w,
    	   dimword_def,w2n_lt_full,GSYM w2n_eq_0,lem7,plem6,
	   DECIDE ``a < b ==> (0n < b - a)``] THEN
    FULL_SIMP_TAC int_ss [plem6,num_msb,BIT_RWR,SUC_SUB_INDEX,w2n_lt_full,
           NOT_LESS_EQUAL] THEN
    `(w2n a DIV (2 ** dimindex (:'a) - w2n b)) MOD 2 ** dimindex (:'a) =
    	  w2n a DIV (2 ** dimindex (:'a) - w2n b)` by MATCH_MP_TAC LESS_MOD THEN
    TRY (NLELT_TRANS_TAC `w2n a` THEN
         RW_TAC int_ss [DIV_LESS_EQ,w2n_lt_full,
               DECIDE ``a < b ==> 0n < b - a``] THEN NO_TAC) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [plem6,DECIDE ``a < b ==> 0n < b - a``,
    		  w2n_lt_full,NOT_LESS] THEN
    FULL_SIMP_TAC int_ss [X_LE_DIV,DECIDE ``a < b ==> 0n < b - a``,w2n_lt_full,
    		  LEFT_SUB_DISTRIB,DIMINDEX_DOUBLE,EXP_BASE_MULT] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_LESS_EQUAL] THEN
    MATCH_MP_TAC (SIMP_RULE int_ss [LEFT_SUB_DISTRIB,
    		 DECIDE ``a < b - c = a + c:num < b``] slem1) THEN
    FULL_SIMP_TAC int_ss [GSYM DIMINDEX_DOUBLE,w2n_lt_full,word_T_def,
    		  UINT_MAX_def,dimword_def] THEN
    METIS_TAC [n2w_w2n]);

val sw2i_word_T = store_thm("sw2i_word_T",``sw2i UINT_MAXw = ~1``,
    RW_TAC int_ss [word_T_def,UINT_MAX_def,dimword_def,sw2i_def,w2n_n2w,BIT_RWR,
           SUC_SUB_INDEX,INT_SUB_CALCULATE,INT_ADD_CALCULATE] THEN
    FULL_SIMP_TAC int_ss [DIMINDEX_DOUBLE,DECIDE ``a <= a - 1n = (a = 0n)``]);

val lem1 = prove(``1 MOD 2 ** dimindex (:'a) = 1``,
    MATCH_MP_TAC LESS_MOD THEN
    RW_TAC int_ss [DIMINDEX_DOUBLE,DECIDE ``1 < 2 * a = 0n < a``]);

val sw2i_div_T = prove(``sw2i ((a:'a word) / UINT_MAXw) =
        extend (sw2i a quot sw2i (UINT_MAXw:'a word)) (dimindex (:'a))``,
    RW_TAC int_ss [sw2i_word_T,sw2i_thm] THEN
    CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    RW_TAC int_ss [eindex EXTEND_11,word_T_def,word_div_def,
    	   word_sdiv_def,num_msb,BIT_RWR,SUC_SUB_INDEX,DIV_1,lem1,
           UINT_MAX_def,dimword_def,w2n_n2w,w2n_lt_full,word_2comp_def,
	   DECIDE ``0 < a ==> (a - (a - 1) = 1n)``] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DIMINDEX_DOUBLE]) THEN
    FULL_SIMP_TAC int_ss [] THENL [
        Q.EXISTS_TAC `1`,
	Cases_on `w2n a = 0` THENL (map Q.EXISTS_TAC [`0`,`1`])] THEN
    RW_TAC int_ss [lem7,INT_ADD_CALCULATE] THEN
    FULL_SIMP_TAC int_ss [w2n_lt_full,NOT_LESS_EQUAL,
    		  DECIDE ``a < b = a <= b /\ ~(a = b:num)``]);

val sw2i_div = store_thm("sw2i_div",
    ``!a b. ~(b = 0w) ==> (sw2i ((a:'a word) / b) =
                           extend (sw2i a quot sw2i b) (dimindex (:'a)))``,
    REPEAT GEN_TAC THEN Cases_on `b = UINT_MAXw` THEN
    RW_TAC int_ss [sw2i_div_1,sw2i_div_T] THEN
    RW_TAC int_ss [eindex EXTEND_EQ,GSYM sw2i_div_1,sw2i_def,BIT_RWR,
    	   w2n_lt_full,SUC_SUB_INDEX,
	   INT_ADD_CALCULATE,INT_SUB_CALCULATE] THEN
    TRY (Q.EXISTS_TAC `0`) THEN RW_TAC int_ss [DIMINDEX_DOUBLE]);

val rwr3 = MATCH_MP LESS_MOD (SPEC_ALL BITWISE_LT_2EXP);

val bit_lem = prove(``~BIT (dimindex (:'b) - 1) (w2n (a:'b word) DIV 2)``,
    RW_TAC int_ss [BIT_RWR,NOT_LESS_EQUAL,SUC_SUB_INDEX,DIV_MOD_MOD_DIV,
    	   DIV_LT_X,GSYM EXP] THEN
    `!a. 2n ** a < 2n ** SUC a` by
        METIS_TAC [TWOEXP_MONO,DECIDE ``a < SUC a``] THEN
    METIS_TAC [w2n_lt_full,TWOEXP_MONO,
               DECIDE ``a < SUC a``,LESS_MOD,LESS_TRANS]);

val bitwise_lem = prove(``!n x. x < 2 ** n ==>
    		  (BITWISE (SUC n) $\/ (2 ** n) x = 2 ** n + x)``,
    Induct THEN ONCE_REWRITE_TAC [BITWISE_DIV] THEN
    RW_TAC int_ss [BITWISE_ZERO,EXP,ODD_MULT,
    	   ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,ODD_TWOEXP] THEN
    FULL_SIMP_TAC int_ss [BITWISE_ZERO] THEN
    FULL_SIMP_TAC int_ss [GSYM MOD2_ODD_EVEN,NOT_MOD2] THEN
    PAT_ASSUM ``!m:'a.P`` (MP_TAC o Q.SPEC `x DIV 2`) THEN
    RW_TAC int_ss [DIV_LT_X,LEFT_ADD_DISTRIB,DIV_MULT_THM2] THEN
    Cases_on `x` THEN FULL_SIMP_TAC int_ss []);

val rwr4 = REWRITE_RULE [SUC_SUB_INDEX] (MATCH_MP bitwise_lem
               (prove(``w2n (a:'a word) DIV 2 < 2 ** (dimindex (:'a) - 1)``,
    RW_TAC int_ss [DIV_LT_X,GSYM EXP,SUC_SUB_INDEX,w2n_lt_full])));

val rwr5 = prove(``(dimindex (:'a) = 1) ==>
               (w2n (a:'a word) = 0) \/ (w2n a = 1)``,
    METIS_TAC [w2n_lt_full,EXP_1,DECIDE ``a < 2 = (a = 0) \/ (a = 1n)``]);

val sw2i_asr_1 = prove(``!b a. sw2i (a >> 1) = sw2i a / 2``,
    RW_TAC std_ss [REWRITE_RULE [n2w_w2n]
               (AP_TERM ``n2w:num -> 'a word`` (SPEC_ALL w2n_lsr)),rwr2,rwr3,
	   word_asr_n2w,sw2i_def,word_or_n2w,MIN_DEF,dimword_def,w2n_n2w,rwr1,
	   int_sub_calc1,INT_EXP] THEN
    FULL_SIMP_TAC int_ss [word_msb_n2w,w2n_n2w,
    	   REWRITE_RULE [n2w_w2n] (Q.SPEC `w2n w` word_msb_n2w),
	   REWRITE_RULE [GSYM NOT_LESS_EQUAL] BITWISE_LT_2EXP,rwr1,dimword_def,
	   rwr3,w2n_lt_full] THEN
    FULL_SIMP_TAC int_ss [rwr1,rwr2,rwr3,DIMINDEX_DOUBLE,bit_lem,BITWISE_THM,
    	   BIT_B,DIV_LT_X,MATCH_MP (DECIDE ``0 < a ==> (~(1 < a) = (a = 1n))``)
	   			   DIMINDEX_GT_0,BIT_MOD,rwr4,rwr5] THEN
    TRY (IMP_RES_TAC rwr5 THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `a`) THEN
         POP_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC int_ss [BIT_RWR,SIMP_RULE arith_ss []
                  (PART_MATCH lhs BITWISE_DIV ``BITWISE (SUC 0) a b c``),
		  BITWISE_ZERO] THEN
    NLT_TRANS_TAC `2 ** dimindex (:'b)` THEN
    REWRITE_TAC [GSYM (EVAL ``2 * 2n``),GSYM MULT_ASSOC,GSYM (CONJUNCT2 EXP),
    		SUC_SUB_INDEX] THEN
    RW_TAC int_ss [w2n_lt_full]);

val pos = prove(``!b a. & a / & (2 ** SUC b) = (& a / 2) / 2 ** b``,
    RW_TAC int_ss [int_div,EXP,DIV_DIV_DIV_MULT]);

val DIV_PLUS_1 = prove(``(m + 1) DIV 2 ** b = m DIV 2 ** b +
    	       	 	    if (m MOD 2 ** b + 1 = 2 ** b) then 1 else 0``,
    ONCE_REWRITE_TAC [DECIDE ``(a = b) = a <= b /\ b <= a:num``] THEN
    RW_TAC int_ss [DIV_LE_X,X_LE_DIV,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] THEN
    RW_TAC int_ss [DIV_MULT_THM] THEN
    Cases_on `m < 2 ** b` THEN FULL_SIMP_TAC int_ss [NOT_LESS] THEN
    `m MOD 2 ** b < m` by (NLTLE_TRANS_TAC `2 ** b` THEN RW_TAC int_ss []) THEN
    RW_TAC int_ss [DECIDE ``a < b - c = a + c < b:num``,
                   DECIDE ``a + 1 < b = a < b /\ ~(a + 1n = b)``]);

val neg = prove(``!b a. ~ & a / & (2 ** SUC b) = (~ & a / 2) / 2 ** b``,
    REPEAT GEN_TAC THEN Cases_on `a = 0` THENL
        [ALL_TAC,Cases_on `a MOD 2 = 0`] THEN
    ASM_REWRITE_TAC [SIMP_RULE int_ss [] (Q.SPECL [`i`,`2 ** a`] int_div),
             INT_EXP,ARITH_PROVE ``0 <= ~ & a = (a = 0n)``,INT_NEGNEG,
	     NUM_OF_INT,SIMP_RULE int_ss [] (Q.SPECL [`i`,`2`] int_div),
	     INT_NEG_0,SIMP_RULE arith_ss [] (Q.SPEC `2 ** a` ZERO_DIV),
	     EVAL ``0 DIV 2``,GSYM INT_NEG_ADD,INT_ADD,
	     DECIDE ``~(a + 1 = 0n)``,INT_ADD_RID] THEN
    RW_TAC int_ss [plem6,EXP,DIV_DIV_DIV_MULT,DIV_MOD_MOD_DIV,GSYM INT_NEG_ADD,
    	     INT_EQ_CALCULATE,INT_ADD,
	     DECIDE ``a < 2 = (a = 0) \/ (a = 1n)``] THEN
    FULL_SIMP_TAC arith_ss [GSYM DIV_DIV_DIV_MULT,ZERO_DIV,MOD2_ODD_EVEN,
             GSYM ODD_EVEN] THEN
    IMP_RES_TAC EVEN_ODD_EXISTS THEN
    FULL_SIMP_TAC int_ss [GSYM MOD_COMMON_FACTOR,
             SIMP_RULE arith_ss [] (Q.SPECL [`2`,`1`] DIV_MULT),ADD1,MOD_PLUS_1,
             SIMP_RULE arith_ss [EXP] (Q.SPEC `2 ** SUC n` MOD_PLUS_1),
             DIV_PLUS_1]);

val both = prove(``!a b. a / & (2 ** SUC b) = (a / 2) / 2 ** b``,
    GEN_TAC THEN INT_CASE_TAC `a` THEN
    RW_TAC arith_ss [pos,neg]);

val sw2i_asr = store_thm("sw2i_asr",``!b a. sw2i (a >> b) = sw2i a / 2 ** b``,
    Induct THEN RW_TAC int_ss [SHIFT_ZERO,both,GSYM sw2i_asr_1] THEN
    REWRITE_TAC [ONCE_REWRITE_RULE [ADD_COMM] ADD1,GSYM ASR_ADD] THEN
    POP_ASSUM (MP_TAC o Q.SPEC `a >> 1`) THEN RW_TAC int_ss []);

val sw2i_lsl = store_thm("sw2i_lsl",
    ``sw2i ((a:'a word) << b) = extend (sw2i a * 2 ** b) (dimindex (:'a))``,
    RW_TAC int_ss [REWRITE_RULE [n2w_w2n] (Q.SPECL [`n`,`w2n m`] word_lsl_n2w),
    	   sw2i_thm,word_0_n2w,
	   EXTEND_ZERO,w2n_n2w] THEN
    CONV_TAC (DEPTH_CONV EXTEND_CONV) THEN
    RW_TAC int_ss [INT_MUL,eindex EXTEND_EQ,eindex EXTEND_11,dimword_def] THEN
    FULL_SIMP_TAC int_ss [DECIDE ``a < b + 1n = a <= b``,mod_lem] THENL [
        Q.EXISTS_TAC `~& (w2n a * 2 ** (b - dimindex (:'a)))`,
	Q.EXISTS_TAC `0`,Q.EXISTS_TAC `0`] THEN
    IMP_RES_TAC LESS_EQUAL_ADD THEN
    RW_TAC int_ss [EXP_ADD,INT_MUL_CALCULATE,INT_ADD_CALCULATE,
           INT_SUB_CALCULATE]);

val sw2i_msb = store_thm("sw2i_msb",
    ``word_msb a = sw2i a < 0``,
    RW_TAC int_ss [num_msb,sw2i_def,BIT_RWR,INT_SUB_CALCULATE,
           INT_ADD_CALCULATE,w2n_lt_full]);

(*****************************************************************************)
(* sw2i_bit : |- !a b. b < dimindex (:'a) ==> (a ' b = ibit b (sw2i a))      *)
(*****************************************************************************)

val lem1 = prove(``b < dimindex (:'a) ==>
    	   	     (BIT b (w2n (a : 'a word)) = a ' b)``,
    ONCE_REWRITE_TAC [SIMP_RULE arith_ss [n2w_w2n]
                    (Q.SPEC `w2n a` word_index_n2w)] THEN
    RW_TAC int_ss []);

val lem2 = prove(``ODD (w2n a) = word_lsb a``,
    RW_TAC int_ss [GSYM BIT_ZERO_ODD,word_lsb_def,lem1,DIMINDEX_GT_0]);

val lem3 = prove(``b < dimindex (:'a) ==>
             (ODD (w2n (a >> b)) = 2 ** b <= w2n (a:'a word) MOD 2 ** SUC b)``,
    RW_TAC int_ss [lem2,word_lsb_def,fcpTheory.FCP_BETA,word_asr_def] THEN
    ONCE_REWRITE_TAC [SIMP_RULE arith_ss [n2w_w2n]
    		     (Q.SPEC `w2n a` word_index_n2w)] THEN
    RW_TAC int_ss [BIT_RWR]);

val sw2i_bit = store_thm("sw2i_bit",
    ``!a b. b < dimindex (:'a) ==> (a ' b = ibit b (sw2i (a:'a word)))``,
    ONCE_REWRITE_TAC [SIMP_RULE arith_ss [n2w_w2n]
         (Q.SPEC `w2n a` word_index_n2w)] THEN
    RW_TAC int_ss [BIT_RWR,ibit_def,REWRITE_RULE [INT_EXP] (GSYM sw2i_asr)] THEN
    RW_TAC int_ss [sw2i_def,BIT_RWR,SUC_SUB_INDEX,w2n_lt_full,INT_SUB_CALCULATE,
    	   INT_ADD_CALCULATE,INT_ABS_NEG,INT_ABS_NUM,ODD_SUB,ODD_TWOEXP,lem3]);


(*****************************************************************************)
(* sw2i_eq : |- !a b. (a = b) = (sw2i a = sw2i b)                            *)
(* sw2i_lt : |- !a b. (a < b) = sw2i a < sw2i b                              *)
(* sw2i_le : |- !a b. (a <= b) = sw2i a <= sw2i b                            *)
(*                                                                           *)
(*****************************************************************************)

val sw2i_eq = store_thm("sw2i_eq",``!a b. (a = b) = (sw2i a = sw2i b)``,
    RW_TAC int_ss [sw2i_def,INT_SUB_CALCULATE,INT_ADD_CALCULATE,BIT_RWR,
    	   SUC_SUB_INDEX,w2n_lt_full,w2n_11,
	   DECIDE ``b < a /\ c < a ==> ((a - b = a - c) = (b = c:num))``] THEN
    METIS_TAC []);

val sw2i_lt = store_thm("sw2i_lt",``!a b. a < b = sw2i a < sw2i b``,
    RW_TAC int_ss [WORD_LT,sw2i_def,num_msb,INT_SUB_CALCULATE,
    	   INT_ADD_CALCULATE,w2n_lt_full,DECIDE ``0n < a - b = b < a``,
	   DECIDE ``b < a /\ c < a ==> (a < b + (a - c) = c < b:num)``]);

val sw2i_le = store_thm("sw2i_le",``!a b. a <= b = sw2i a <= sw2i b``,
    RW_TAC int_ss [WORD_LESS_OR_EQ,sw2i_lt,INT_LE_LT,sw2i_eq]);

(*****************************************************************************)
(* sw2i_n2w : |- !a. sw2i (n2w a : 'a word) = extend (& a) (dimindex (:'a))  *)
(*                                                                           *)
(*****************************************************************************)

val mod_lem = prove(``!a b. 0 < b ==> (a MOD b = a - a DIV b * b)``,
    REPEAT STRIP_TAC THEN IMP_RES_TAC DIVISION THEN
    FIRST_ASSUM (CONV_TAC o RAND_CONV o LAND_CONV o REWR_CONV) THEN
    RW_TAC int_ss []);

val sw2i_n2w = store_thm("sw2i_n2w",
    ``!a. sw2i (n2w a : 'a word) = extend (& a) (dimindex (:'a))``,
    RW_TAC int_ss [sw2i_thm,w2n_n2w,dimword_def,mod_lem,
    	   eindex EXTEND_11] THEN
    Q.EXISTS_TAC `~ & (a DIV 2 ** dimindex (:'a))` THEN
    RW_TAC int_ss [INT_ADD_CALCULATE,INT_MUL_CALCULATE] THEN
    METIS_TAC [ZERO_LT_TWOEXP,X_LE_DIV,LESS_EQ_REFL]);

(*****************************************************************************)
(* Theorems relating word definitions to definitions using operators         *)
(* that can be converted to use signed integers.                             *)
(*****************************************************************************)

(*****************************************************************************)
(* WORD_BITS_THM : |- !h l a. (h -- l) a =                                   *)
(*                                   a >>> l && n2w (2 ** (h + 1 - l) - 1)   *)
(*****************************************************************************)
val BIT_SHIFT_THM4 = store_thm("BIT_SHIFT_THM4",
    ``BIT i (a * 2 ** b) = BIT (i - b) a /\ b <= i``,
    METIS_TAC [BIT_SHIFT_THM3,NOT_LESS_EQUAL,BIT_SHIFT_THM2]);

val TOP_BIT_THM = store_thm("TOP_BIT_THM",``!a b. BIT a (2 ** b - 1) = a < b``,
    Induct_on `a` THEN Cases THEN
    RW_TAC int_ss [BIT_ZERO_ODD,ODD_SUB,ODD_TWOEXP,EXP,
           DECIDE ``1 < 2 * n = 0n < n``,BIT_ZERO,BIT_DIV,DIV2_MULT_SUB1]);

val BIT_RANGE = store_thm("BIT_RANGE",
    ``!h l i. BIT i (2 ** h - 2 ** l) = l <= i /\ i < h``,
    REPEAT GEN_TAC THEN Cases_on `l < h` THEN
    FULL_SIMP_TAC int_ss [NOT_LESS] THEN
    MAP_EVERY IMP_RES_TAC [LESS_ADD_1,LESS_EQUAL_ADD] THEN
    RW_TAC int_ss (EXP_ADD::GSYM EXP::BIT_SHIFT_THM4::TOP_BIT_THM::BIT_ZERO::
    	   DECIDE ``0 < a ==> (1 - a = 0n)``::
	   map (GSYM o REWRITE_RULE [MULT_CLAUSES])
	       [Q.SPECL [`p`,`1`,`l`] LEFT_SUB_DISTRIB,
		Q.SPECL [`1`,`p`,`l`] LEFT_SUB_DISTRIB]));

val WORD_BITS_THM = store_thm("WORD_BITS_THM",
    ``(h -- l) a = a >>> l && n2w (2 ** (h + 1 - l) - 1)``,
    RW_TAC int_ss [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_bits_def,
    	   word_and_def,word_lsr_def,
	   PROVE [word_index_n2w] ``i < dimindex (:'a) ==>
	   	 ((n2w n :'a word) ' i = BIT i n)``,word_asr_def,
	   BIT_RANGE,TOP_BIT_THM] THEN EQ_TAC THEN
    RW_TAC int_ss [DECIDE ``i < a + 1 - b = i + b <= a:num``]);

val WORD_SLICE_THM = store_thm("WORD_SLICE_THM",
    ``(h '' l) a = a && n2w (2 ** SUC h - 2 ** l)``,
    RW_TAC int_ss [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_bits_def,
    	   word_and_def,word_lsr_def,
	   PROVE [word_index_n2w] 
             ``i < dimindex (:'a) ==> ((n2w n :'a word) ' i = BIT i n)``, 
            word_asr_def, BIT_RANGE,TOP_BIT_THM,word_slice_def] THEN
    EQ_TAC THEN RW_TAC int_ss []);

val _ = export_theory();
