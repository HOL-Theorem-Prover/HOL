(* ===================================================================== *)
(* FILE          : mk_arithmetic.sml                                     *)
(* DESCRIPTION   : Definitions and properties of +,-,*,EXP, <=, >=, etc. *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge               *)
(* DATE          : 88.04.02                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ADDITIONS     : December 22, 1992                                     *)
(* ===================================================================== *)


structure arithmeticScript =
struct

open HolKernel basicHol90Lib Parse;
infix THEN THENC THENL |-> ORELSE;

(* interactive use:
   app load ["prim_recTheory","primWFTheory", "QLib"];
*)

val _ = new_theory "arithmetic";

val NOT_SUC     = numTheory.NOT_SUC
and INV_SUC     = numTheory.INV_SUC
and INDUCTION   = numTheory.INDUCTION;

val num_Axiom     = prim_recTheory.num_Axiom;
val INV_SUC_EQ    = prim_recTheory.INV_SUC_EQ
and LESS_REFL     = prim_recTheory.LESS_REFL
and SUC_LESS      = prim_recTheory.SUC_LESS
and NOT_LESS_0    = prim_recTheory.NOT_LESS_0
and LESS_MONO     = prim_recTheory.LESS_MONO
and LESS_SUC_REFL = prim_recTheory.LESS_SUC_REFL
and LESS_SUC      = prim_recTheory.LESS_SUC
and LESS_THM      = prim_recTheory.LESS_THM
and LESS_SUC_IMP  = prim_recTheory.LESS_SUC_IMP
and LESS_0        = prim_recTheory.LESS_0
and EQ_LESS       = prim_recTheory.EQ_LESS
and SUC_ID        = prim_recTheory.SUC_ID
and NOT_LESS_EQ   = prim_recTheory.NOT_LESS_EQ
and LESS_NOT_EQ   = prim_recTheory.LESS_NOT_EQ
and LESS_SUC_SUC  = prim_recTheory.LESS_SUC_SUC
and PRE           = prim_recTheory.PRE;


(*---------------------------------------------------------------------------*
 * The basic arithmetic operations.                                          *
 *---------------------------------------------------------------------------*)

val ADD = new_recursive_definition
   {name = "ADD",
    fixity = Infixl 500,
    rec_axiom = num_Axiom,
    def = --`($+ 0 n = n) /\
             ($+ (SUC m) n = SUC($+ m n))`--};

(*---------------------------------------------------------------------------*
 * Define NUMERAL, a tag put on numeric literals, and the basic constructors *
 * of the "numeral type".                                                    *
 *---------------------------------------------------------------------------*)

val NUMERAL_DEF = new_definition("NUMERAL_DEF", --`NUMERAL (x:num) = x`--);
val ALT_ZERO    = new_definition("ALT_ZERO",    --`ALT_ZERO = 0`--);
val NUMERAL_BIT1 =
  new_definition("NUMERAL_BIT1",
                 --`NUMERAL_BIT1 n = n + (n + SUC 0)`--);
val NUMERAL_BIT2 =
  new_definition("NUMERAL_BIT2",
                 --`NUMERAL_BIT2 n = n + (n + SUC (SUC 0))`--);

(*---------------------------------------------------------------------------*
 * After this call, numerals parse into `NUMERAL( ... )`                     *
 *---------------------------------------------------------------------------*)

val _ = add_numeral_form (#"n", NONE);

val SUB = new_recursive_definition
   {name = "SUB",
    fixity = Infixl 500,
    rec_axiom = num_Axiom,
    def = --`($- 0 m = 0) /\
             ($- (SUC m) n = ((m < n) => 0 | SUC($- m n)))`--};

val MULT = new_recursive_definition
   {name = "MULT",
    fixity = Infixl 600,
    rec_axiom = num_Axiom,
    def = --`($* 0 n = 0) /\
             ($* (SUC m) n = ($* m n) + n)`--};

val EXP = new_recursive_definition
   {name = "EXP",
    fixity = Infixr 700,
    rec_axiom = num_Axiom,
    def = --`($EXP m 0 = 1) /\
             ($EXP m (SUC n) = m * ($EXP m n))`--};

val GREATER_DEF = new_infixr_definition
  ("GREATER_DEF", --`$> m n = n < m`--,   450);

val LESS_OR_EQ = new_infixr_definition
  ("LESS_OR_EQ", --`$<= m n = m < n \/ (m = n)`--,  450);

val GREATER_OR_EQ = new_infixr_definition
  ("GREATER_OR_EQ", --`$>= m n = m > n \/ (m = n)`--, 450);

val EVEN = new_recursive_definition
   {name = "EVEN",
    fixity = Prefix,
    rec_axiom = num_Axiom,
    def = --`(EVEN 0 = T) /\
             (EVEN (SUC n) = ~EVEN n)`--};

val ODD = new_recursive_definition
   {name = "ODD",
    fixity = Prefix,
    rec_axiom = num_Axiom,
    def = --`(ODD 0 = F) /\
             (ODD (SUC n) = ~ODD n)`--};

val num_case_def = new_recursive_definition
   {name = "num_case_def",
    fixity = Prefix,
    rec_axiom = num_Axiom,
    def = --`(num_case b f 0 = (b:'a)) /\
             (num_case b f (SUC n) = f n)`--};

val FUNPOW = new_recursive_definition
   {name = "FUNPOW",
    fixity = Prefix,
    rec_axiom = num_Axiom,
    def = --`(FUNPOW f 0 x = x) /\
             (FUNPOW f (SUC n) x = FUNPOW f n (f x))`--};


(*---------------------------------------------------------------------------
                        THEOREMS
 ---------------------------------------------------------------------------*)

val ONE = store_thm("ONE",
  Term `1 = SUC 0`,
REWRITE_TAC [NUMERAL_DEF, NUMERAL_BIT1, ALT_ZERO, ADD]);

val TWO = store_thm("TWO",
  Term`2 = SUC 1`,
REWRITE_TAC
   [NUMERAL_DEF, NUMERAL_BIT2, ONE,
    ADD, ALT_ZERO,NUMERAL_BIT1]);

fun INDUCT_TAC g = INDUCT_THEN INDUCTION ASSUME_TAC g;

val EQ_SYM_EQ' = INST_TYPE [alpha |-> Type`:num`] EQ_SYM_EQ;


(* --------------------------------------------------------------------- *)
(* SUC_NOT = |- !n. ~(0 = SUC n)                                         *)
(* --------------------------------------------------------------------- *)

val SUC_NOT = save_thm("SUC_NOT",
    GEN (--`n:num`--) (NOT_EQ_SYM (SPEC (--`n:num`--) NOT_SUC)));

val ADD_0 = store_thm("ADD_0",
   --`!m. m + 0 = m`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD]);

val ADD_SUC = store_thm("ADD_SUC",
   --`!m n. SUC(m + n) = (m + SUC n)`--,
   INDUCT_TAC
   THEN GEN_TAC
   THEN ASM_REWRITE_TAC[ADD]);

val ADD_CLAUSES = store_thm("ADD_CLAUSES",
   --`(0 + m = m)              /\
      (m + 0 = m)              /\
      (SUC m + n = SUC(m + n)) /\
      (m + SUC n = SUC(m + n))`--,
   REWRITE_TAC[ADD, ADD_0, ADD_SUC]);

val ADD_SYM = store_thm ("ADD_SYM",
  --`!m n. m + n = n + m`--,
  INDUCT_TAC
   THEN GEN_TAC
   THEN ASM_REWRITE_TAC[ADD_0, ADD, ADD_SUC]);

val ADD_COMM = save_thm("ADD_COMM", ADD_SYM);

val ADD_ASSOC = store_thm ("ADD_ASSOC",
   --`!m n p. m + (n + p) = (m + n) + p`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]);

val num_CASES = store_thm ("num_CASES",
   --`!m. (m = 0) \/ ?n. m = SUC n`--,
   INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC]
    THEN EXISTS_TAC (--`(m:num)`--)
    THEN REWRITE_TAC[]);

val NOT_ZERO_LT_ZERO = store_thm(
  "NOT_ZERO_LT_ZERO",
  Term`!n. ~(n = 0) = 0 < n`,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `n` num_CASES) THEN
  REWRITE_TAC [NOT_LESS_0, LESS_0, NOT_SUC]);

(* --------------------------------------------------------------------- *)
(* LESS_ADD proof rewritten: TFM 90.O9.21                               *)
(* --------------------------------------------------------------------- *)
val LESS_ADD = store_thm ("LESS_ADD",
     --`!m n. (n<m) ==> ?p. p+n = m`--,
     INDUCT_TAC THEN GEN_TAC THEN
     REWRITE_TAC[NOT_LESS_0,LESS_THM] THEN
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC (--`SUC 0`--) THEN ASM_REWRITE_TAC[ADD],
      RES_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
      EXISTS_TAC (--`SUC p`--) THEN REWRITE_TAC [ADD]]);

val LESS_TRANS = store_thm ("LESS_TRANS",
   --`!m n p. (m < n) /\ (n < p) ==> (m < p)`--,
   REPEAT GEN_TAC
    THEN SPEC_TAC(--`(n:num)`--,--`(n:num)`--)
    THEN SPEC_TAC(--`(m:num)`--,--`(m:num)`--)
    THEN SPEC_TAC(--`(p:num)`--,--`(p:num)`--)
    THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_LESS_0, LESS_THM]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THENL [SUBST_TAC[SYM(ASSUME (--`n:num = p`--))], ALL_TAC]
    THEN ASM_REWRITE_TAC[]);


val LESS_ANTISYM = store_thm  ("LESS_ANTISYM",
   --`!m n. ~((m < n) /\ (n < m))`--,
   INDUCT_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN IMP_RES_TAC LESS_REFL
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

val LESS_LESS_SUC = store_thm ("LESS_LESS_SUC",
   --`!m n. ~((m < n) /\ (n < SUC m))`--,
   REWRITE_TAC[LESS_THM]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN IMP_RES_TAC(DISCH_ALL(SUBS[ASSUME(--`(n:num)=m`--)]
                                   (ASSUME(--`m<n`--))))
    THEN IMP_RES_TAC LESS_REFL
    THEN ASM_REWRITE_TAC[]);

(* Doesn't belong here. kls. *)
val FUN_EQ_LEMMA = store_thm ("FUN_EQ_LEMMA",
   --`!f:'a->bool. !x1 x2. f x1 /\ ~f x2 ==> ~(x1 = x2)`--,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME (--`(x1:'a)=x2`--)]
                         (ASSUME(--`(f:'a->bool)x1`--))))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------
 *  |- !m n. SUC m < SUC n = m < n
 *---------------------------------------------------------------------------*)
val LESS_MONO_REV = store_thm ("LESS_MONO_REV",
   --`!m n. SUC m < SUC n ==> m < n`--,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[LESS_THM]
    THEN STRIP_TAC
    THEN IMP_RES_TAC SUC_LESS
    THEN IMP_RES_TAC EQ_LESS
    THEN ASM_REWRITE_TAC[]);

val LESS_MONO_EQ = save_thm("LESS_MONO_EQ",
   GENL [--`m:num`--, --`n:num`--]
        (IMP_ANTISYM_RULE (SPEC_ALL LESS_MONO_REV)
                          (SPEC_ALL LESS_MONO)));


val LESS_OR = store_thm ("LESS_OR",
   --`!m n. m < n ==> SUC m <= n`--,
   REWRITE_TAC[LESS_OR_EQ]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_LESS_0,LESS_MONO_EQ,INV_SUC_EQ, LESS_THM]
    THEN STRIP_TAC THENL [ALL_TAC, RES_TAC] THEN ASM_REWRITE_TAC[]);


val LESS_SUC_EQ = LESS_OR;

val OR_LESS = store_thm ("OR_LESS",
   --`!m n. (SUC m <= n) ==> (m < n)`--,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN STRIP_TAC
    THEN IMP_RES_TAC SUC_LESS
    THEN IMP_RES_TAC EQ_LESS
    THEN ASM_REWRITE_TAC[]);


(* |-   !m n. (m < n) = (SUC m <= n) *)
val LESS_EQ = save_thm("LESS_EQ",
   GENL [--`m:num`--, --`n:num`--]
        (IMP_ANTISYM_RULE (SPEC_ALL LESS_OR)
                          (SPEC_ALL OR_LESS)));


val LESS_SUC_EQ_COR = store_thm ("LESS_SUC_EQ_COR",
   --`!m n. ((m < n) /\ (~(SUC m = n))) ==> (SUC m < n)`--,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_SUC_EQ
    THEN MP_TAC(ASSUME (--`(SUC m) <= n`--))
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);  (* RES_TAC doesn't solve the goal when --`F`-- is
                           in the assumptions *)

val LESS_NOT_SUC = store_thm("LESS_NOT_SUC",
   --`!m n. (m < n) /\ ~(n = SUC m) ==> SUC m < n`--,
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC (--`n = SUC m`--)
    THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC
    THEN MP_TAC(REWRITE_RULE[LESS_OR_EQ]
                            (EQ_MP(SPEC_ALL LESS_EQ)
                                  (ASSUME (--`m < n`--))))
    THEN STRIP_TAC
    THEN ASSUME_TAC(SYM(ASSUME (--`SUC m = n`--)))
    THEN RES_TAC); (* RES_TAC doesn't solve --`F`-- in assumptions *)

val LESS_0_CASES = store_thm("LESS_0_CASES",
   --`!m. (0 = m) \/ 0<m`--,
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_0]);

val LESS_CASES_IMP = store_thm("LESS_CASES_IMP",
   --`!m n. ~(m < n) /\  ~(m = n) ==> (n < m)`--,
   GEN_TAC
    THEN INDUCT_TAC
    THEN STRIP_TAC
    THENL
    [MP_TAC(ASSUME (--`~(m = 0)`--))
      THEN ACCEPT_TAC
            (DISJ_IMP
             (SUBS
               [SPECL[--`0`--, --`m:num`--]EQ_SYM_EQ']
               (SPEC_ALL LESS_0_CASES))),
     MP_TAC(ASSUME (--`~(m < (SUC n))`--))
      THEN REWRITE_TAC[LESS_THM, DE_MORGAN_THM]
      THEN STRIP_TAC
      THEN RES_TAC
      THEN IMP_RES_TAC LESS_NOT_SUC
      THEN ASM_REWRITE_TAC[]]);

val LESS_CASES = store_thm("LESS_CASES",
   --`!m n. (m < n) \/ (n <= m)`--,
   REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[LESS_OR_EQ, DE_MORGAN_THM]
    THEN ASM_CASES_TAC (--`(m:num) = n`--)
    THEN ASM_CASES_TAC (--`m < n`--)
    THEN IMP_RES_TAC LESS_CASES_IMP
    THEN ASM_REWRITE_TAC[]);

val ADD_INV_0 = store_thm("ADD_INV_0",
   --`!m n. (m + n = m) ==> (n = 0)`--,
   REPEAT GEN_TAC
    THEN SPEC_TAC(--`(m:num)`--,--`(m:num)`--)
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES, INV_SUC_EQ]);

val LESS_EQ_ADD = store_thm ("LESS_EQ_ADD",
   --`!m n. m <= m + n`--,
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
    THEN MP_TAC(ASSUME (--`(m < (m + n)) \/ (m = (m + n))`--))
    THEN STRIP_TAC
    THENL
    [IMP_RES_TAC LESS_SUC
      THEN ASM_REWRITE_TAC[],
     REWRITE_TAC[SYM(ASSUME (--`m = m + n`--)),LESS_SUC_REFL]]);

val LESS_EQ_SUC_REFL = store_thm ("LESS_EQ_SUC_REFL",
   --`!m. m <= SUC m`--,
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ,LESS_SUC_REFL]);

val LESS_ADD_NONZERO = store_thm ("LESS_ADD_NONZERO",
   --`!m n. ~(n = 0) ==> m < m + n`--,
   GEN_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC,ADD_CLAUSES]
    THEN ASM_CASES_TAC (--`n = 0`--)
    THEN ASSUME_TAC(SPEC (--`m + n`--) LESS_SUC_REFL)
    THEN RES_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_SUC_REFL]);

val LESS_EQ_ANTISYM = store_thm ("LESS_EQ_ANTISYM",
   --`!m n. ~(m < n /\ n <= m)`--,
   REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ANTISYM
    THEN ASM_REWRITE_TAC[]
    THEN ASSUME_TAC(SYM(ASSUME (--`(n:num) = m`--)))
    THEN IMP_RES_TAC NOT_LESS_EQ
    THEN ASM_REWRITE_TAC[]);

val NOT_LESS = store_thm ("NOT_LESS",
   --`!m n. ~(m < n) = (n <= m)`--,
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC (--`m < n`--)
    THEN ASM_CASES_TAC (--`n <= m`--)
    THEN IMP_RES_TAC(DISJ_IMP(SPEC_ALL LESS_CASES))
    THEN IMP_RES_TAC(CONTRAPOS(DISJ_IMP(SPEC_ALL LESS_CASES)))
    THEN RES_TAC
    THEN IMP_RES_TAC LESS_EQ_ANTISYM
    THEN ASM_REWRITE_TAC[]);

val _ = print "Now proving properties of subtraction\n"

val SUB_0 = store_thm ("SUB_0",
   --`!m. (0 - m = 0) /\ (m - 0 = m)`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[SUB, NOT_LESS_0]);


(* I was exhausted when I did the proof below - it can almostly certainly be
  drastically shortened. *)
val SUB_EQ_0 = store_thm ("SUB_EQ_0",
   --`!m n. (m - n = 0) = (m <= n)`--,
   INDUCT_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[SUB,LESS_OR_EQ]
    THENL
     [REWRITE_TAC[SPECL[--`0 < n`--, --`0 = n`--]DISJ_SYM,LESS_0_CASES],
      ALL_TAC]
    THEN ASM_CASES_TAC (--`m < n`--)
    THEN ASM_CASES_TAC (--`SUC m = n`--)
    THEN IMP_RES_TAC EQ_LESS
    THEN IMP_RES_TAC LESS_SUC_EQ_COR
    THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL NOT_LESS)))
    THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL LESS_OR_EQ)))
    THEN ASM_REWRITE_TAC
          [SPECL[--`(n:num)=m`--,--`n<m`--]DISJ_SYM,
           NOT_SUC,NOT_LESS,LESS_OR_EQ,LESS_THM]);


val ADD1 = store_thm ("ADD1",
  --`!m. SUC m = m + 1`--,
  INDUCT_TAC THENL [
    REWRITE_TAC [ADD_CLAUSES, ONE],
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [ONE, ADD_CLAUSES]
  ]);


val SUC_SUB1 = store_thm("SUC_SUB1",
   --`!m. SUC m - 1 = m`--,
INDUCT_TAC THENL [
  REWRITE_TAC [SUB, LESS_0, ONE],
  PURE_ONCE_REWRITE_TAC[SUB] THEN
  ASM_REWRITE_TAC[NOT_LESS_0, LESS_MONO_EQ, ONE]
]);

val PRE_SUB1 = store_thm ("PRE_SUB1",
   --`!m. (PRE m = (m - 1))`--,
   GEN_TAC
    THEN STRUCT_CASES_TAC(SPEC (--`m:num`--) num_CASES)
    THEN ASM_REWRITE_TAC[PRE, CONJUNCT1 SUB, SUC_SUB1]);


val MULT_0 = store_thm ("MULT_0",
   --`!m. m * 0 = 0`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT,ADD_CLAUSES]);

val MULT_SUC = store_thm ("MULT_SUC",
   --`!m n. m * (SUC n) = m + m*n`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT,ADD_CLAUSES,ADD_ASSOC]);

val MULT_LEFT_1 = store_thm ("MULT_LEFT_1",
   --`!m. 1 * m = m`--,
   GEN_TAC THEN REWRITE_TAC[ONE, MULT,ADD_CLAUSES]);

val MULT_RIGHT_1 = store_thm ("MULT_RIGHT_1",
   --`!m. m * 1 = m`--,
   REWRITE_TAC [ONE] THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC[MULT, ADD_CLAUSES]);

val MULT_CLAUSES = store_thm ("MULT_CLAUSES",
   --`!m n. (0 * m = 0)                 /\
            (m * 0 = 0)                 /\
            (1 * m = m)                 /\
            (m * 1 = m)                 /\
          (SUC m * n = m * n + n) /\
          (m * SUC n = m + m * n)`--,
    REWRITE_TAC[MULT,MULT_0,MULT_LEFT_1,MULT_RIGHT_1,MULT_SUC]);

val MULT_SYM = store_thm("MULT_SYM",
  --`!m n. m * n = n * m`--,
  INDUCT_TAC
   THEN GEN_TAC
   THEN ASM_REWRITE_TAC[MULT_CLAUSES,SPECL[--`m*n`--,--`n:num`--]ADD_SYM]);

val MULT_COMM = save_thm("MULT_COMM", MULT_SYM);

val RIGHT_ADD_DISTRIB = store_thm ("RIGHT_ADD_DISTRIB",
   --`!m n p. (m + n) * p = (m * p) + (n * p)`--,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,ADD_ASSOC]
    THEN REWRITE_TAC[SPECL[--`m+(m*p)`--,--`n:num`--]ADD_SYM,ADD_ASSOC]
    THEN SUBST_TAC[SPEC_ALL ADD_SYM]
    THEN REWRITE_TAC[]);

(* A better proof of LEFT_ADD_DISTRIB would be using
   MULT_SYM and RIGHT_ADD_DISTRIB *)
val LEFT_ADD_DISTRIB = store_thm ("LEFT_ADD_DISTRIB",
   --`!m n p. p * (m + n) = (p * m) + (p * n)`--,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
    THEN REWRITE_TAC[SPECL[--`m:num`--,--`(p*n)+n`--]ADD_SYM,
                     SYM(SPEC_ALL ADD_ASSOC)]
    THEN SUBST_TAC[SPEC_ALL ADD_SYM]
    THEN REWRITE_TAC[]);

val MULT_ASSOC = store_thm ("MULT_ASSOC",
   --`!m n p. m * (n * p) = (m * n) * p`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT_CLAUSES,RIGHT_ADD_DISTRIB]);

val SUB_ADD = store_thm ("SUB_ADD",
   --`!m n. (n <= m) ==> ((m - n) + n = m)`--,
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[SUB,ADD_CLAUSES,LESS_SUC_REFL]
    THEN IMP_RES_TAC NOT_LESS_0
    THEN ASM_CASES_TAC (--`m < n`--)
    THEN IMP_RES_TAC LESS_LESS_SUC
    THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL NOT_LESS)))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]);

val PRE_SUB = store_thm ("PRE_SUB",
   --`!m n. PRE(m - n) = (PRE m) - n`--,
   INDUCT_TAC
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[SUB,PRE]
    THEN ASM_CASES_TAC (--`m < n`--)
    THEN ASM_REWRITE_TAC
          [PRE,LESS_OR_EQ,
           SUBS[SPECL[--`m-n`--,--`0`--]EQ_SYM_EQ']
               (SPECL [--`m:num`--,--`n:num`--] SUB_EQ_0)])

val ADD_EQ_0 = store_thm ("ADD_EQ_0",
   --`!m n. (m + n = 0) = (m = 0) /\ (n = 0)`--,
   INDUCT_TAC
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,NOT_SUC]);

val ADD_EQ_1 = store_thm(
  "ADD_EQ_1",
  --`!m n. (m + n = 1) = (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)`--,
  INDUCT_TAC THENL [
     REWRITE_TAC [ADD_CLAUSES, ONE, GSYM NOT_SUC],
     REWRITE_TAC [NOT_SUC, ADD_CLAUSES, ONE, INV_SUC_EQ, ADD_EQ_0]
  ]);

val ADD_INV_0_EQ = store_thm ("ADD_INV_0_EQ",
   --`!m n. (m + n = m) = (n = 0)`--,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[ADD_INV_0]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]);

val PRE_SUC_EQ = store_thm ("PRE_SUC_EQ",
   --`!m n. 0<n ==> ((m = PRE n) = (SUC m = n))`--,
   INDUCT_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[PRE,LESS_REFL,INV_SUC_EQ]);

val INV_PRE_EQ = store_thm ("INV_PRE_EQ",
   --`!m n. 0<m /\ 0<n ==> ((PRE m = (PRE n)) = (m = n))`--,
   INDUCT_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[PRE,LESS_REFL,INV_SUC_EQ]);

val LESS_SUC_NOT = store_thm ("LESS_SUC_NOT",
   --`!m n. (m < n)  ==> ~(n < SUC m)`--,
   REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_OR
    THEN ASM_REWRITE_TAC[]);

(* About now I burned out and resorted to dreadful hacks. The name of the
  next theorem speaks for itself. *)
val TOTALLY_AD_HOC_LEMMA = prove
   (--`!m n. (m + SUC n = n) = (SUC m = 0)`--,
   REPEAT GEN_TAC
    THEN REWRITE_TAC
          [NOT_SUC,SYM(SPECL [--`m:num`--,--`n:num`--] (CONJUNCT2 ADD)),
           (fn [_, _,_,th] => th)(CONJUNCTS ADD_CLAUSES)]
    THEN REWRITE_TAC[SPECL[--`SUC m`--,--`n:num`--]ADD_SYM]
    THEN STRIP_TAC
    THEN IMP_RES_TAC ADD_INV_0
    THEN IMP_RES_TAC NOT_SUC);

(* The next proof took me ages - there must be a better way! *)
val ADD_EQ_SUB = store_thm ("ADD_EQ_SUB",
   --`!m n p. (n <= p) ==> (((m + n) = p) = (m = (p - n)))`--,
   INDUCT_TAC
    THEN INDUCT_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC
          [LESS_OR_EQ,ADD_CLAUSES,NOT_LESS_0,INV_SUC_EQ,LESS_MONO_EQ,
           NOT_SUC,NOT_EQ_SYM(SPEC_ALL NOT_SUC),LESS_0,SUB,SUB_0]
    THEN STRIP_TAC
    THEN IMP_RES_TAC LESS_NOT_EQ
    THEN ASM_REWRITE_TAC[LESS_SUC_REFL]
    THEN IMP_RES_TAC LESS_SUC_NOT
    THEN ASM_REWRITE_TAC[NOT_EQ_SYM(SPEC_ALL NOT_SUC),INV_SUC_EQ]
    THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL NOT_LESS)))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC
          [SYM((fn [_,_,_,th] => th)(CONJUNCTS(SPEC_ALL ADD_CLAUSES))),
           TOTALLY_AD_HOC_LEMMA]);

val LESS_MONO_ADD = store_thm ("LESS_MONO_ADD",
   --`!m n p. (m < n) ==> (m + p) < (n + p)`--,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_MONO_EQ]);

val LESS_MONO_ADD_INV = store_thm ("LESS_MONO_ADD_INV",
   --`!m n p. (m + p) < (n + p) ==> (m < n)`--,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_MONO_EQ]);

val LESS_MONO_ADD_EQ = store_thm ("LESS_MONO_ADD_EQ",
   --`!m n p. ((m + p) < (n + p)) = (m < n)`--,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[LESS_MONO_ADD,LESS_MONO_ADD_INV]);

val EQ_MONO_ADD_EQ = store_thm ("EQ_MONO_ADD_EQ",
   --`!m n p. ((m + p) = (n + p)) = (m = n)`--,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,INV_SUC_EQ]);

val _ = print "Proving properties of <=\n"

val LESS_EQ_MONO_ADD_EQ = store_thm ("LESS_EQ_MONO_ADD_EQ",
   --`!m n p. ((m + p) <= (n + p)) = (m <= n)`--,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[LESS_MONO_ADD_EQ,EQ_MONO_ADD_EQ]);

val LESS_EQ_TRANS = store_thm ("LESS_EQ_TRANS",
   --`!m n p. (m <= n) /\ (n <= p) ==> (m <= p)`--,
   REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_REWRITE_TAC[]
    THEN SUBST_TAC[SYM(ASSUME (--`(n:num) = p`--))]
    THEN ASM_REWRITE_TAC[]);

(* % Proof modified for new IMP_RES_TAC                 [TFM 90.04.25]  *)

val LESS_EQ_LESS_EQ_MONO = store_thm ("LESS_EQ_LESS_EQ_MONO",
--`!m n p q. (m <= p) /\ (n <= q) ==> ((m + n) <= (p + q))`--,
   REPEAT STRIP_TAC THEN
   let val th1 = snd(EQ_IMP_RULE (SPEC_ALL  LESS_EQ_MONO_ADD_EQ))
       val th2 = PURE_ONCE_REWRITE_RULE [ADD_SYM] th1
   in
   IMP_RES_THEN (ASSUME_TAC o SPEC (--`n:num`--)) th1 THEN
   IMP_RES_THEN (ASSUME_TAC o SPEC (--`p:num`--)) th2 THEN
   IMP_RES_TAC LESS_EQ_TRANS
   end);

val LESS_EQ_REFL = store_thm ("LESS_EQ_REFL",
   --`!m. m <= m`--,
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]);

val LESS_IMP_LESS_OR_EQ = store_thm ("LESS_IMP_LESS_OR_EQ",
   --`!m n. (m < n) ==> (m <= n)`--,
   REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[LESS_OR_EQ]);

val LESS_MONO_MULT = store_thm ("LESS_MONO_MULT",
   --`!m n p. (m <= n) ==> ((m * p) <= (n * p))`--,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC
          [ADD_CLAUSES,MULT_CLAUSES,LESS_EQ_MONO_ADD_EQ,LESS_EQ_REFL]
    THEN RES_TAC
    THEN IMP_RES_TAC(SPECL[--`m:num`--,--`m*p`--,--`n:num`--,--`n*p`--]
                          LESS_EQ_LESS_EQ_MONO)
    THEN ASM_REWRITE_TAC[]);

(* Proof modified for new IMP_RES_TAC                   [TFM 90.04.25]  *)

val RIGHT_SUB_DISTRIB = store_thm ("RIGHT_SUB_DISTRIB",
   --`!m n p. (m - n) * p = (m * p) - (n * p)`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`n <= m`--) THENL
   [let val imp = SPECL [--`(m-n)*p`--,
                         --`n*p`--,
                         --`m*p`--] ADD_EQ_SUB
    in
    IMP_RES_THEN (SUBST1_TAC o SYM o MP imp o SPEC (--`p:num`--))
                 LESS_MONO_MULT THEN
    REWRITE_TAC[SYM(SPEC_ALL RIGHT_ADD_DISTRIB)] THEN
    IMP_RES_THEN SUBST1_TAC SUB_ADD THEN REFL_TAC
    end,
    IMP_RES_TAC (REWRITE_RULE[](AP_TERM (--`$~`--)
                                        (SPEC_ALL NOT_LESS))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN (ASSUME_TAC o SPEC (--`p:num`--)) LESS_MONO_MULT THEN
    IMP_RES_TAC SUB_EQ_0 THEN
    ASM_REWRITE_TAC[MULT_CLAUSES]]);

val LEFT_SUB_DISTRIB = store_thm("LEFT_SUB_DISTRIB",
   --`!m n p. p * (m - n) = (p * m) - (p * n)`--,
   PURE_ONCE_REWRITE_TAC [MULT_SYM] THEN
   REWRITE_TAC [RIGHT_SUB_DISTRIB]);

(* The following theorem (and proof) are from tfm [rewritten TFM 90.09.21] *)
val LESS_ADD_1 = store_thm ("LESS_ADD_1",
  --`!m n. (n<m) ==> ?p. m = n + (p + 1)`--,
  REWRITE_TAC [ONE] THEN INDUCT_TAC THEN
  REWRITE_TAC[NOT_LESS_0,LESS_THM] THEN
  REPEAT STRIP_TAC THENL [
   EXISTS_TAC (--`0`--) THEN ASM_REWRITE_TAC [ADD_CLAUSES],
   RES_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
   EXISTS_TAC (--`SUC p`--) THEN REWRITE_TAC [ADD_CLAUSES]
]);

(* ---------------------------------------------------------------------*)
(* The following arithmetic theorems were added by TFM in 88.03.31      *)
(*                                                                      *)
(* These are needed to build the recursive type definition package      *)
(* ---------------------------------------------------------------------*)

val EXP_ADD = store_thm ("EXP_ADD",
  --`!p q n. n EXP (p+q) = (n EXP p) * (n EXP q)`--,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXP,ADD_CLAUSES,MULT_CLAUSES,MULT_ASSOC]);

val NOT_ODD_EQ_EVEN = store_thm ("NOT_ODD_EQ_EVEN",
  --`!n m. ~(SUC(n + n) = (m + m))`--,
     REPEAT (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES]) THENL
     [MATCH_ACCEPT_TAC NOT_SUC,
      REWRITE_TAC [INV_SUC_EQ,NOT_EQ_SYM (SPEC_ALL NOT_SUC)],
      REWRITE_TAC [INV_SUC_EQ,NOT_SUC],
      ASM_REWRITE_TAC [INV_SUC_EQ]]);

val MULT_SUC_EQ = store_thm ("MULT_SUC_EQ",
  --`!p m n. ((n * (SUC p)) = (m * (SUC p))) = (n = m)`--,
     REPEAT STRIP_TAC THEN
     STRIP_ASSUME_TAC (REWRITE_RULE [LESS_OR_EQ] (SPEC_ALL LESS_CASES)) THEN
     ASM_REWRITE_TAC [] THENL
     [ ALL_TAC
       ,
       ONCE_REWRITE_TAC [EQ_SYM_EQ'] THEN
       POP_ASSUM MP_TAC THEN
       (MAP_EVERY SPEC_TAC [(--`m:num`--,--`m:num`--),
                            (--`n:num`--,--`n:num`--)
                           ]) THEN
        MAP_EVERY X_GEN_TAC [--`m:num`--,--`n:num`--] THEN
        DISCH_TAC
     ] THEN
     IMP_RES_THEN (fn th => REWRITE_TAC [NOT_EQ_SYM th]) LESS_NOT_EQ THEN
     POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [MULT_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)] THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [EQ_MONO_ADD_EQ] THEN
     REWRITE_TAC [RIGHT_ADD_DISTRIB,MULT_CLAUSES] THEN
     ONCE_REWRITE_TAC [SPEC (--`p * q`--) ADD_SYM] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     REWRITE_TAC [ADD_ASSOC,REWRITE_RULE [ADD_CLAUSES]
                                         (SPEC (--`0`--) EQ_MONO_ADD_EQ)] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     REWRITE_TAC [ONE, ADD_CLAUSES,NOT_SUC]);

val MULT_EXP_MONO = store_thm ("MULT_EXP_MONO",
  --`!p q n m.((n * ((SUC q) EXP p)) = (m * ((SUC q) EXP p))) = (n = m)`--,
     INDUCT_TAC THENL
     [REWRITE_TAC [EXP,MULT_CLAUSES,ADD_CLAUSES],
      ASM_REWRITE_TAC [EXP,MULT_ASSOC,MULT_SUC_EQ]]);

val LESS_EQUAL_ANTISYM = store_thm ("LESS_EQUAL_ANTISYM",
  --`!n m. n <= m /\ m <= n ==> (n = m)`--,
     REWRITE_TAC [LESS_OR_EQ] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC LESS_ANTISYM,
      ASM_REWRITE_TAC[]]);

val LESS_ADD_SUC = store_thm("LESS_ADD_SUC",
     --`!m n. m < m + SUC n`--,
     INDUCT_TAC THENL
     [REWRITE_TAC [LESS_0,ADD_CLAUSES],
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC [LESS_MONO_EQ,ADD_CLAUSES]]);

val ZERO_LESS_EQ = store_thm("ZERO_LESS_EQ",
     --`!n. 0 <= n`--,
     GEN_TAC THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC (--`n:num`--) num_CASES) THEN
     REWRITE_TAC [LESS_0,LESS_OR_EQ]);

val LESS_EQ_MONO = store_thm("LESS_EQ_MONO",
     --`!n m. (SUC n <= SUC m) = (n <= m)`--,
     REWRITE_TAC [LESS_OR_EQ,LESS_MONO_EQ,INV_SUC_EQ]);

(* Following proof revised for version 1.12 resolution.  [TFM 91.01.18] *)
val LESS_OR_EQ_ADD = store_thm ("LESS_OR_EQ_ADD",
  --`!n m. n < m \/ ?p. n = p+m`--,
     REPEAT GEN_TAC THEN ASM_CASES_TAC (--`n<m`--) THENL
     [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      DISJ2_TAC THEN IMP_RES_TAC NOT_LESS THEN IMP_RES_TAC LESS_OR_EQ THENL
      [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
       IMP_RES_THEN MATCH_ACCEPT_TAC LESS_ADD,
       EXISTS_TAC (--`0`--) THEN ASM_REWRITE_TAC [ADD]]]);

(*----------------------------------------------------------------------*)
(* Added TFM 88.03.31                                                   *)
(*                                                                      *)
(* Prove the well ordering property:                                    *)
(*                                                                      *)
(* |- !P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))               *)
(*                                                                      *)
(* I.e. considering P to be a set, that is the set of numbers, x , such *)
(* that P(x), then every non-empty P has a smallest element.            *)
(*                                                                      *)
(* We first prove that, if there does NOT exist a smallest n such that  *)
(* P(n) is true, then for all n P is false of all numbers smaller than n.*)
(* The main step is an induction on n.                                  *)
(*----------------------------------------------------------------------*)

val lemma = TAC_PROOF(([],
    --`(~?n. P n /\ !m. (m<n) ==> ~P m) ==>
       (!n m. (m<n) ==> ~P m)`--),
              CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
              DISCH_TAC THEN
              INDUCT_TAC THEN
              REWRITE_TAC [NOT_LESS_0,LESS_THM] THEN
              REPEAT (FILTER_STRIP_TAC (--`P:num->bool`--)) THENL
              [POP_ASSUM SUBST1_TAC THEN DISCH_TAC,ALL_TAC] THEN
              RES_TAC);

(* We now prove the well ordering property.                             *)
val WOP = store_thm("WOP",
    --`!P. (?n.P n) ==> (?n. P n /\ (!m. (m<n) ==> ~P m))`--,
    GEN_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN
    DISCH_THEN (ASSUME_TAC o MP lemma) THEN
    CONV_TAC NOT_EXISTS_CONV THEN
    GEN_TAC THEN
    POP_ASSUM (MATCH_MP_TAC o SPECL [--`SUC n`--,--`n:num`--]) THEN
    MATCH_ACCEPT_TAC LESS_SUC_REFL);



val COMPLETE_INDUCTION = store_thm("COMPLETE_INDUCTION",
  Term`!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n`,
  let val wopeta = CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) WOP
  in
  GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP wopeta) THEN BETA_TAC THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_TAC (Term`n:num`)) THEN
  EXISTS_TAC (Term`n:num`) THEN ASM_REWRITE_TAC[]
  end);


(* ---------------------------------------------------------------------*)
(* Some more theorems, mostly about subtraction.                        *)
(* ---------------------------------------------------------------------*)

(* Non-confluence problem between SUB (snd clause) and LESS_MONO_EQ     *)
(*   requires a change from hol2 proof. kls.                            *)

val SUB_MONO_EQ = store_thm("SUB_MONO_EQ",
 --`!n m. (SUC n) - (SUC m) = (n - m)`--,
   INDUCT_TAC THENL
   [REWRITE_TAC [SUB,LESS_0],
    ONCE_REWRITE_TAC[SUB] THEN
    PURE_ONCE_REWRITE_TAC[LESS_MONO_EQ] THEN
    ASM_REWRITE_TAC[]]);

val SUB_PLUS = store_thm("SUB_PLUS",
 --`!a b c. a - (b + c) = (a - b) - c`--,
   REPEAT INDUCT_TAC THEN
   REWRITE_TAC [SUB_0,ADD_CLAUSES,SUB_MONO_EQ] THEN
   PURE_ONCE_REWRITE_TAC [SYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
   PURE_ONCE_ASM_REWRITE_TAC [] THEN REFL_TAC);

(* Statement of thm changed.
**val INV_PRE_LESS = store_thm("INV_PRE_LESS",
** --`!m n. 0 < m /\ 0 < n ==> ((PRE m < PRE n) = (m < n))`--,
**   REPEAT INDUCT_TAC THEN
**   REWRITE_TAC[LESS_REFL,SUB,LESS_0,PRE] THEN
**   MATCH_ACCEPT_TAC (SYM(SPEC_ALL LESS_MONO_EQ)));
*)
val INV_PRE_LESS = store_thm("INV_PRE_LESS",
   --`!m. 0 < m  ==> !n. PRE m < PRE n = m < n`--,
    REPEAT (INDUCT_TAC THEN TRY DISCH_TAC) THEN
    REWRITE_TAC[LESS_REFL,SUB,LESS_0,PRE,NOT_LESS_0] THEN
    IMP_RES_TAC LESS_REFL THEN
    MATCH_ACCEPT_TAC (SYM(SPEC_ALL LESS_MONO_EQ)));

val INV_PRE_LESS_EQ = store_thm("INV_PRE_LESS_EQ",
 --`!n. 0 < n ==> !m. ((PRE m <= PRE n) = (m <= n))`--,
   INDUCT_TAC THEN
   REWRITE_TAC [LESS_REFL,LESS_0,PRE] THEN
   INDUCT_TAC THEN
   REWRITE_TAC [PRE,ZERO_LESS_EQ] THEN
   REWRITE_TAC [ADD1,LESS_EQ_MONO_ADD_EQ]);

val SUB_LESS_EQ = store_thm("SUB_LESS_EQ",
 --`!n m. (n - m) <= n`--,
   REWRITE_TAC [SYM(SPEC_ALL SUB_EQ_0),SYM(SPEC_ALL SUB_PLUS)] THEN
   CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [SUB_EQ_0,LESS_EQ_ADD]);

val SUB_EQ_EQ_0 = store_thm("SUB_EQ_EQ_0",
 --`!m n. (m - n = m) = ((m = 0) \/ (n = 0))`--,
   REPEAT INDUCT_TAC THEN
   REWRITE_TAC [SUB_0,NOT_SUC] THEN
   REWRITE_TAC [SUB] THEN
   ASM_CASES_TAC (--`m<SUC n`--) THENL
   [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC [NOT_SUC],
    ASM_REWRITE_TAC [INV_SUC_EQ,NOT_SUC] THEN
    IMP_RES_THEN (ASSUME_TAC o MATCH_MP OR_LESS) NOT_LESS THEN
    IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) LESS_ADD_1 THEN
    REWRITE_TAC [ONE, ADD_CLAUSES, NOT_SUC]]);

val SUB_LESS_0 = store_thm("SUB_LESS_0",
 --`!n m. (m < n) = 0 < (n - m)`--,
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [ONE,ADD_CLAUSES,SUB] THEN
    REWRITE_TAC [REWRITE_RULE [SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD,LESS_0],
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [NOT_LESS,LESS_OR_EQ,NOT_LESS_0,SUB_EQ_0]]);

val SUB_LESS_OR = store_thm("SUB_LESS_OR",
 --`!m n. n < m ==> n <= (m - 1)`--,
   REPEAT GEN_TAC THEN
   DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
   REWRITE_TAC [SYM (SPEC_ALL PRE_SUB1)] THEN
   REWRITE_TAC [PRE,ONE,ADD_CLAUSES,LESS_EQ_ADD]);

val LESS_SUB_ADD_LESS = store_thm("LESS_SUB_ADD_LESS",
 --`!n m i. (i < (n - m)) ==> ((i + m) < n)`--,
   INDUCT_TAC THENL
   [REWRITE_TAC [SUB_0,NOT_LESS_0],
    REWRITE_TAC [SUB] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (--`n < m`--) THEN
    ASM_REWRITE_TAC [NOT_LESS_0,LESS_THM] THEN
    let fun tac th g = SUBST1_TAC th g
                       handle _ => ASSUME_TAC th g
    in
    DISCH_THEN (STRIP_THM_THEN tac)
    end THENL
    [DISJ1_TAC THEN MATCH_MP_TAC SUB_ADD THEN
     ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)],
     RES_TAC THEN ASM_REWRITE_TAC[]]]);

val TIMES2 = store_thm("TIMES2",
   --`!n. 2 * n = n + n`--,
   REWRITE_TAC [MULT_CLAUSES, NUMERAL_DEF, NUMERAL_BIT2, ADD_CLAUSES,
                ALT_ZERO]);

val LESS_MULT_MONO = store_thm("LESS_MULT_MONO",
 --`!m i n. ((SUC n) * m) < ((SUC n) * i) = (m < i)`--,
   REWRITE_TAC [MULT_CLAUSES] THEN
   INDUCT_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES,LESS_0],
    INDUCT_TAC THENL
    [REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES,NOT_LESS_0],
     INDUCT_TAC THENL
     [REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES],
      REWRITE_TAC [LESS_MONO_EQ,ADD_CLAUSES,MULT_CLAUSES] THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      let val th = SYM(el 5 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))
      in
      PURE_ONCE_REWRITE_TAC [th]
      end THEN
      ASM_REWRITE_TAC[]]]]);


val MULT_MONO_EQ = store_thm("MULT_MONO_EQ",
 --`!m i n. (((SUC n) * m) = ((SUC n) * i)) = (m = i)`--,
   REWRITE_TAC [MULT_CLAUSES] THEN
   INDUCT_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES, NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
    INDUCT_TAC THENL
    [REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES,NOT_SUC],
     INDUCT_TAC THENL
     [REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES],
      REWRITE_TAC [INV_SUC_EQ,ADD_CLAUSES,MULT_CLAUSES] THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [EQ_MONO_ADD_EQ] THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      let val th = SYM(el 5 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))
      in
      PURE_ONCE_REWRITE_TAC [th]
      end THEN
      ASM_REWRITE_TAC[]]]]);

val EQ_ADD_LCANCEL = prove(
  Term`!m n p. (m + n = m + p) = (n = p)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ]);

val EQ_ADD_RCANCEL = prove(
  Term`!m n p. (m + p = n + p) = (m = n)`,
  ONCE_REWRITE_TAC[ADD_COMM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL);

val EQ_MULT_LCANCEL = prove(
  Term`!m n p. (m * n = m * p) = (m = 0) \/ (n = p)`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES, NOT_SUC] THEN
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, GSYM NOT_SUC, NOT_SUC] THEN
  ASM_REWRITE_TAC[INV_SUC_EQ, GSYM ADD_ASSOC, EQ_ADD_LCANCEL]);


val ADD_SUB = store_thm ("ADD_SUB",
 --`!a c. (a + c) - c = a`--,
   INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THENL
   [INDUCT_TAC THEN REWRITE_TAC [SUB,LESS_SUC_REFL],
    ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL NOT_LESS)] LESS_EQ_ADD) THEN
    PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
    ASM_REWRITE_TAC [SUB,INV_SUC_EQ] THEN
    PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
    FIRST_ASSUM ACCEPT_TAC]);

val LESS_EQ_ADD_SUB = store_thm("LESS_EQ_ADD_SUB",
 --`!c b. (c <= b) ==> !a. (((a + b) - c) = (a + (b - c)))`--,
   PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN
   REPEAT GEN_TAC THEN
   let fun tac th g = SUBST1_TAC th g
                      handle _ => MP_TAC th g
   in
   DISCH_THEN (STRIP_THM_THEN tac)
   end THENL
   [DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [ONE] THEN
    SUBST1_TAC (SPECL [--`c:num`--,--`p + (SUC 0)`--] ADD_SYM) THEN
    REWRITE_TAC [ADD_ASSOC,ADD_SUB],
    GEN_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC [ADD_SUB,ADD_INV_0_EQ,SUB_EQ_0,LESS_EQ_REFL]
   ]);

(* ---------------------------------------------------------------------*)
(* SUB_EQUAL_0 = |- !c. c - c = 0                                       *)
(* ---------------------------------------------------------------------*)

val _ = print "More properties of subtraction...\n"

val SUB_EQUAL_0 = save_thm ("SUB_EQUAL_0",
   REWRITE_RULE [ADD_CLAUSES] (SPEC (--`0`--) ADD_SUB));


val LESS_EQ_SUB_LESS = store_thm("LESS_EQ_SUB_LESS",
 --`!a b. (b <= a) ==> !c. ((a - b) < c) = (a < (b + c))`--,
   PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN
   REPEAT GEN_TAC THEN
   let fun tac th g = SUBST1_TAC th g
                      handle _ => MP_TAC th g
   in
   DISCH_THEN (STRIP_THM_THEN tac)
   end THENL
   [DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [ONE] THEN GEN_TAC THEN
    SUBST1_TAC (SPECL [--`b:num`--,--`p + (SUC 0)`--] ADD_SYM) THEN
    SUBST1_TAC (SPECL [--`b:num`--,--`c:num`--] ADD_SYM) THEN
    REWRITE_TAC [ADD_SUB,LESS_MONO_ADD_EQ],
    REWRITE_TAC [SUB_EQUAL_0] THEN GEN_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC (--`c:num`--) num_CASES) THEN
    REWRITE_TAC [ADD_CLAUSES,LESS_REFL,LESS_0,LESS_ADD_SUC]]);

val NOT_SUC_LESS_EQ = store_thm("NOT_SUC_LESS_EQ",
 --`!n m.~(SUC n <= m) = (m <= n)`--,
    REWRITE_TAC [SYM (SPEC_ALL LESS_EQ),NOT_LESS]);

val SUB_SUB = store_thm("SUB_SUB",
 --`!b c. (c <= b) ==> !a. ((a - (b - c)) = ((a + c) - b))`--,
   PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN
   REPEAT GEN_TAC THEN
   let fun tac th g = SUBST1_TAC th g
                      handle _ => MP_TAC th g
   in
   DISCH_THEN (STRIP_THM_THEN tac)
   end THENL
   [DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [ONE] THEN
    SUBST_OCCS_TAC [([1],SPECL [--`c:num`--,--`p + (SUC 0)`--] ADD_SYM)] THEN
    REWRITE_TAC [ADD_SUB] THEN REWRITE_TAC [SUB_PLUS,ADD_SUB],
    REWRITE_TAC [SUB_EQUAL_0] THEN
    REWRITE_TAC [ADD_SUB,SUB_0]]);

val LESS_IMP_LESS_ADD = store_thm("LESS_IMP_LESS_ADD",
 --`!n m. n < m ==> !p. n < (m + p)`--,
   REPEAT GEN_TAC THEN
   DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
   REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC), ONE] THEN
   PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
   PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
   GEN_TAC THEN MATCH_ACCEPT_TAC LESS_ADD_SUC);

val LESS_EQ_IMP_LESS_SUC = store_thm("LESS_EQ_IMP_LESS_SUC",
 --`!n m. (n <= m) ==> (n < (SUC m))`--,
   REWRITE_TAC [LESS_OR_EQ] THEN
   REPEAT STRIP_TAC THENL
   [IMP_RES_TAC LESS_SUC, ASM_REWRITE_TAC [LESS_SUC_REFL]]);

val SUB_LESS_EQ_ADD = store_thm("SUB_LESS_EQ_ADD",
 --`!m p. (m <= p) ==> !n. (((p - m) <= n) = (p <= (m + n)))`--,
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LESS_EQ_SUB_LESS THEN
   IMP_RES_TAC (SPEC (--`n:num`--) ADD_EQ_SUB) THEN
   ASM_REWRITE_TAC [LESS_OR_EQ] THEN
   SUBST_OCCS_TAC [([3], SPECL [--`m:num`--,--`n:num`--] ADD_SYM)] THEN
   CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
   ASM_REWRITE_TAC [] THEN
   CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
   REFL_TAC);

val SUB_CANCEL = store_thm("SUB_CANCEL",
 --`!p n m. ((n <= p) /\ (m <= p)) ==> (((p - n) = (p - m)) = (n = m))`--,
   REWRITE_TAC [LESS_OR_EQ] THEN REPEAT GEN_TAC THEN
   let fun tac th g = SUBST1_TAC th g
                      handle _ => MP_TAC th g
   in
   DISCH_THEN (REPEAT_TCL STRIP_THM_THEN tac)
   end THENL
   [DISCH_THEN (STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
    SUBST_OCCS_TAC [([3], SPECL [--`m:num`--,--`p'+1`--] ADD_SYM)] THEN
    REWRITE_TAC [ADD_SUB] THEN DISCH_TAC THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_TAC (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) ADD_EQ_SUB) THEN
    CONV_TAC (RATOR_CONV(RAND_CONV SYM_CONV)) THEN
    SUBST1_TAC (SPECL [--`p'+1`--,--`m:num`--] ADD_SYM) THEN
    ASM_REWRITE_TAC [] THEN
    SUBST1_TAC (SPECL [--`m:num`--,--`p'+1`--] ADD_SYM) THEN
    PURE_ONCE_REWRITE_TAC [ADD_SUB] THEN
    PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_ACCEPT_TAC EQ_MONO_ADD_EQ,
    REWRITE_TAC [SUB_EQUAL_0,SUB_EQ_0] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)] THEN
    IMP_RES_TAC LESS_NOT_EQ,
    PURE_ONCE_REWRITE_TAC [SUB_EQUAL_0] THEN
    DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [ADD_INV_0_EQ] THEN
    SUBST1_TAC (SPECL [--`m:num`--,--`p'+1`--] ADD_SYM) THEN
    REWRITE_TAC [ADD_SUB] THEN MATCH_ACCEPT_TAC EQ_SYM_EQ,
    REWRITE_TAC []]);

val CANCEL_SUB = store_thm("CANCEL_SUB",
 --`!p n m.((p <= n) /\ (p <= m)) ==> (((n - p) = (m - p)) = (n = m))`--,
   REWRITE_TAC [LESS_OR_EQ] THEN REPEAT GEN_TAC THEN
   let fun tac th g = SUBST1_TAC th g
                      handle _ => MP_TAC th g
   in
   DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN
   DISCH_THEN (STRIP_THM_THEN tac) THENL
   [DISCH_THEN
     (fn th1 =>
        DISCH_THEN (fn th2 => (MP_TAC th1 THEN STRIP_THM_THEN tac th2))) THENL
     [REPEAT(DISCH_THEN(STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1))THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [ADD_SUB,EQ_MONO_ADD_EQ],
      DISCH_TAC THEN
      CONV_TAC (RATOR_CONV(RAND_CONV SYM_CONV)) THEN
      REWRITE_TAC [SUB_EQUAL_0,SUB_EQ_0] THEN
      IMP_RES_TAC LESS_NOT_EQ THEN
      ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)]],
    DISCH_THEN (STRIP_THM_THEN tac) THENL
    [DISCH_TAC THEN
     CONV_TAC (RAND_CONV SYM_CONV) THEN
     REWRITE_TAC [SUB_EQUAL_0,SUB_EQ_0] THEN
     IMP_RES_TAC LESS_NOT_EQ THEN
     ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)],
     REWRITE_TAC[]]]
   end);

val NOT_EXP_0 = store_thm("NOT_EXP_0",
 --`!m n. ~(((SUC n) EXP m) = 0)`--,
   INDUCT_TAC THEN REWRITE_TAC [EXP] THENL
   [REWRITE_TAC [NOT_SUC, ONE],
    STRIP_TAC THEN
    let val th = (SYM(el 2 (CONJUNCTS (SPECL [--`SUC n`--,--`1`--]
                                             MULT_CLAUSES))))
    in
    SUBST1_TAC th
    end THEN REWRITE_TAC [MULT_MONO_EQ] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC]);

val ZERO_LESS_EXP = store_thm("ZERO_LESS_EXP",
 --`!m n. 0 < ((SUC n) EXP m)`--,
   REPEAT STRIP_TAC THEN
   let val th = SPEC (--`(SUC n) EXP m`--) LESS_0_CASES
       fun tac th g = ASSUME_TAC (SYM th) g
                      handle _ => ACCEPT_TAC th g
   in
   STRIP_THM_THEN tac th THEN
   IMP_RES_TAC NOT_EXP_0
   end);

val ODD_OR_EVEN = store_thm("ODD_OR_EVEN",
 --`!n. ?m. (n = (SUC(SUC 0) * m)) \/ (n = ((SUC(SUC 0) * m) + 1))`--,
   REWRITE_TAC [ONE] THEN
   INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL
   [EXISTS_TAC (--`0`--) THEN REWRITE_TAC [ADD_CLAUSES,MULT_CLAUSES],
    EXISTS_TAC (--`m:num`--) THEN ASM_REWRITE_TAC[ADD_CLAUSES],
    EXISTS_TAC (--`SUC m`--) THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES]]);

val LESS_EXP_SUC_MONO = store_thm("LESS_EXP_SUC_MONO",
 --`!n m.((SUC(SUC m)) EXP n) < ((SUC(SUC m)) EXP (SUC n))`--,
   INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC [EXP] THENL
   [REWRITE_TAC [EXP,ADD_CLAUSES,MULT_CLAUSES,ONE,LESS_0, LESS_MONO_EQ],
    ASM_REWRITE_TAC [LESS_MULT_MONO]]);

(*---------------------------------------------------------------------------*)
(* More arithmetic theorems, mainly concerning orderings [JRH 92.07.14]      *)
(*---------------------------------------------------------------------------*)

val LESS_LESS_CASES = store_thm("LESS_LESS_CASES",
   --`!m n. (m = n) \/ (m < n) \/ (n < m)`--,
   let val th = REWRITE_RULE[LESS_OR_EQ]
                            (SPECL[(--`m:num`--), (--`n:num`--)] LESS_CASES)
   in REPEAT GEN_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN (fn t => REWRITE_TAC[t]) th
   end);

val GREATER_EQ = store_thm("GREATER_EQ",
  --`!n m. n >= m = m <= n`--,
  REPEAT GEN_TAC THEN REWRITE_TAC[GREATER_OR_EQ, GREATER_DEF, LESS_OR_EQ] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);

val LESS_EQ_CASES = store_thm("LESS_EQ_CASES",
  --`!m n. m <= n \/ n <= m`--,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 (ASSUME_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ) ASSUME_TAC
    (SPECL [(--`m:num`--), (--`n:num`--)] LESS_CASES) THEN ASM_REWRITE_TAC[]);

val LESS_EQUAL_ADD = store_thm("LESS_EQUAL_ADD",
  --`!m n. m <= n ==> ?p. n = m + p`--,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  DISCH_THEN(DISJ_CASES_THEN2 MP_TAC SUBST1_TAC) THENL
   [MATCH_ACCEPT_TAC(GSYM (ONCE_REWRITE_RULE[ADD_SYM] LESS_ADD)),
    EXISTS_TAC (--`0`--) THEN REWRITE_TAC[ADD_CLAUSES]]);

val LESS_EQ_EXISTS = store_thm("LESS_EQ_EXISTS",
  --`!m n. m <= n = ?p. n = m + p`--,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC LESS_EQUAL_ADD,
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC LESS_EQ_ADD]);

val NOT_LESS_EQUAL = store_thm("NOT_LESS_EQUAL",
  --`!m n. ~(m <= n) = n < m`--,
  REWRITE_TAC[GSYM NOT_LESS]);

val LESS_EQ_0 = store_thm("LESS_EQ_0",
  --`!n. (n <= 0) = (n = 0)`--,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C CONJ (SPEC (--`n:num`--) ZERO_LESS_EQ)) THEN
    MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM,
    DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC LESS_EQ_REFL]);

val MULT_EQ_0 = store_thm("MULT_EQ_0",
  --`!m n. (m * n = 0) = (m = 0) \/ (n = 0)`--,
  REPEAT GEN_TAC THEN
  MAP_EVERY (STRUCT_CASES_TAC o C SPEC num_CASES) [(--`m:num`--),(--`n:num`--)]
  THEN REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, NOT_SUC]);

val MULT_EQ_1 = store_thm("MULT_EQ_1",
 --`!x y. (x * y = 1) = (x = 1) /\ (y = 1)`--,
  REPEAT GEN_TAC THEN
  MAP_EVERY (STRUCT_CASES_TAC o C SPEC num_CASES)
            [(--`x:num`--),(--`y:num`--)] THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, ONE, GSYM SUC_ID, INV_SUC_EQ,
              ADD_EQ_0,MULT_EQ_0] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);

val LESS_MULT2 = store_thm("LESS_MULT2",
  --`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`--,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[NOT_LESS, LESS_EQ_0, DE_MORGAN_THM, MULT_EQ_0]);

val LESS_EQ_LESS_TRANS = store_thm("LESS_EQ_LESS_TRANS",
  --`!m n p. m <= n /\ n < p ==> m < p`--,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  ASM_CASES_TAC (--`m:num = n`--) THEN ASM_REWRITE_TAC[LESS_TRANS]);

val LESS_LESS_EQ_TRANS = store_thm("LESS_LESS_EQ_TRANS",
  --`!m n p. m < n /\ n <= p ==> m < p`--,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  ASM_CASES_TAC (--`n:num = p`--) THEN ASM_REWRITE_TAC[LESS_TRANS]);

(*---------------------------------------------------------------------------*)
(* Single theorem about the factorial function           [JRH 92.07.14]      *)
(*---------------------------------------------------------------------------*)

val FACT = new_recursive_definition
   {name = "FACT",
    fixity = Prefix,
    rec_axiom = num_Axiom,
    def = --`(FACT 0 = 1) /\
             (FACT (SUC n) = (SUC n) * FACT(n))`--};

val FACT_LESS = store_thm("FACT_LESS",
  --`!n. 0 < FACT n`--,
  INDUCT_TAC THEN REWRITE_TAC[FACT, ONE, LESS_SUC_REFL] THEN
  MATCH_MP_TAC LESS_MULT2 THEN ASM_REWRITE_TAC[LESS_0]);

(*---------------------------------------------------------------------------*)
(* Theorems about evenness and oddity                    [JRH 92.07.14]      *)
(*---------------------------------------------------------------------------*)


val _ = print "Theorems about evenness and oddity\n"
val EVEN_ODD = store_thm("EVEN_ODD",
  --`!n. EVEN n = ~ODD n`--,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN, ODD]);

val ODD_EVEN = store_thm("ODD_EVEN",
  --`!n. ODD n = ~(EVEN n)`--,
  REWRITE_TAC[EVEN_ODD]);

val EVEN_OR_ODD = store_thm("EVEN_OR_ODD",
  --`!n. EVEN n \/ ODD n`--,
  REWRITE_TAC[EVEN_ODD, REWRITE_RULE[DE_MORGAN_THM] NOT_AND]);

val EVEN_AND_ODD = store_thm("EVEN_AND_ODD",
  --`!n. ~(EVEN n /\ ODD n)`--,
  REWRITE_TAC[ODD_EVEN, NOT_AND]);

val EVEN_ADD = store_thm("EVEN_ADD",
  --`!m n. EVEN(m + n) = (EVEN m = EVEN n)`--,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES, EVEN] THEN
  BOOL_CASES_TAC (--`EVEN m`--) THEN REWRITE_TAC[]);

val EVEN_MULT = store_thm("EVEN_MULT",
  --`!m n. EVEN(m * n) = EVEN m \/ EVEN n`--,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES, EVEN_ADD, EVEN] THEN
  BOOL_CASES_TAC (--`EVEN m`--) THEN REWRITE_TAC[]);

val ODD_ADD = store_thm("ODD_ADD",
  --`!m n. ODD(m + n) = ~(ODD m = ODD n)`--,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EVEN, EVEN_ADD] THEN
  BOOL_CASES_TAC (--`EVEN m`--) THEN REWRITE_TAC[]);

val ODD_MULT = store_thm("ODD_MULT",
  --`!m n. ODD(m * n) = ODD(m) /\ ODD(n)`--,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EVEN, EVEN_MULT, DE_MORGAN_THM]);

val two = prove(Term
  `2 = SUC 1`,
  REWRITE_TAC [NUMERAL_DEF, NUMERAL_BIT1, NUMERAL_BIT2] THEN
  ONCE_REWRITE_TAC [SYM (SPEC (--`0`--) NUMERAL_DEF)] THEN
  REWRITE_TAC [ADD_CLAUSES]);

val EVEN_DOUBLE = store_thm("EVEN_DOUBLE",
  --`!n. EVEN(2 * n)`--,
  GEN_TAC THEN REWRITE_TAC[EVEN_MULT] THEN DISJ1_TAC THEN
  REWRITE_TAC[EVEN, ONE, two]);

val ODD_DOUBLE = store_thm("ODD_DOUBLE",
  --`!n. ODD(SUC(2 * n))`--,
  REWRITE_TAC[ODD] THEN REWRITE_TAC[GSYM EVEN_ODD, EVEN_DOUBLE]);

val EVEN_ODD_EXISTS = store_thm("EVEN_ODD_EXISTS",
  --`!n. (EVEN n ==> ?m. n = 2 * m) /\ (ODD n ==> ?m. n = SUC(2 * m))`--,
  REWRITE_TAC[ODD_EVEN] THEN INDUCT_TAC THEN REWRITE_TAC[EVEN] THENL
   [EXISTS_TAC (--`0`--) THEN REWRITE_TAC[MULT_CLAUSES],
    POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC o
                    C MATCH_MP th)) THENL
     [EXISTS_TAC (--`SUC m`--) THEN
      REWRITE_TAC[ONE, two, MULT_CLAUSES, ADD_CLAUSES],
      EXISTS_TAC (--`m:num`--) THEN REFL_TAC]]);

val EVEN_EXISTS = store_thm("EVEN_EXISTS",
  --`!n. EVEN n = ?m. n = 2 * m`--,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EVEN_ODD_EXISTS],
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC EVEN_DOUBLE]);

val ODD_EXISTS = store_thm("ODD_EXISTS",
  --`!n. ODD n = ?m. n = SUC(2 * m)`--,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EVEN_ODD_EXISTS],
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC ODD_DOUBLE]);

(* --------------------------------------------------------------------- *)
(* Theorems moved from the "more_arithmetic' library      [RJB 92.09.28] *)
(* --------------------------------------------------------------------- *)

val EQ_LESS_EQ = store_thm ("EQ_LESS_EQ",
   --`!m n. (m = n) = ((m <= n) /\ (n <= m))`--,
   REPEAT GEN_TAC THEN EQ_TAC
    THENL [STRIP_TAC THEN ASM_REWRITE_TAC [LESS_EQ_REFL],
           REWRITE_TAC [LESS_EQUAL_ANTISYM]]);

val ADD_MONO_LESS_EQ = store_thm ("ADD_MONO_LESS_EQ",
   --`!m n p. (m + n) <= (m + p) = (n <= p)`--,
   ONCE_REWRITE_TAC [ADD_SYM]
    THEN REWRITE_TAC [LESS_EQ_MONO_ADD_EQ]);

val NOT_SUC_LESS_EQ_0 = store_thm ("NOT_SUC_LESS_EQ_0",
   --`!n. ~(SUC n <= 0)`--,
   REWRITE_TAC [NOT_LESS_EQUAL,LESS_0]);

(* ---------------------------------------------------------------------*)
(* Theorems to support the arithmetic proof procedure     [RJB 92.09.29]*)
(* ---------------------------------------------------------------------*)

val _ = print "Theorems to support the arithmetic proof procedure\n"
val NOT_LEQ = store_thm ("NOT_LEQ",
   --`!m n. ~(m <= n) = (SUC n) <= m`--,
   REWRITE_TAC [SYM (SPEC_ALL LESS_EQ)] THEN
   REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)]);

val NOT_NUM_EQ = store_thm ("NOT_NUM_EQ",
   --`!m n. ~(m = n) = (((SUC m) <= n) \/ ((SUC n) <= m))`--,
   REWRITE_TAC [EQ_LESS_EQ,DE_MORGAN_THM,NOT_LEQ] THEN
   MATCH_ACCEPT_TAC DISJ_SYM);

val NOT_GREATER = store_thm ("NOT_GREATER",
   --`!m n. ~(m > n) = (m <= n)`--,
   REWRITE_TAC [GREATER_DEF,NOT_LESS]);

val NOT_GREATER_EQ = store_thm ("NOT_GREATER_EQ",
   --`!m n. ~(m >= n) = (SUC m) <= n`--,
   REWRITE_TAC [GREATER_EQ,NOT_LEQ]);

val SUC_ONE_ADD = store_thm ("SUC_ONE_ADD",
   --`!n. SUC n = 1 + n`--,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [ADD1,ADD_SYM] THEN
   REFL_TAC);

(* Didn't go through in hol90, probably becuase of non-confluence, so
** proof changed. kls
*)
val SUC_ADD_SYM = store_thm ("SUC_ADD_SYM",
   --`!m n. SUC (m + n) = (SUC n) + m`--,
   REPEAT GEN_TAC THEN
   REWRITE_TAC[ADD_CLAUSES] THEN
   AP_TERM_TAC THEN
   ACCEPT_TAC (SPEC_ALL ADD_SYM));

val NOT_SUC_ADD_LESS_EQ = store_thm ("NOT_SUC_ADD_LESS_EQ",
   --`!m n. ~(SUC (m + n) <= m)`--,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [SYM (SPEC_ALL LESS_EQ)] THEN
   REWRITE_TAC [NOT_LESS,LESS_EQ_ADD]);

val MULT_LESS_EQ_SUC =
   let val th1 = SPEC (--`b:num`--) (SPEC (--`c:num`--) (SPEC (--`a:num`--)
                      LESS_MONO_ADD))
       val th2 = SPEC (--`c:num`--) (SPEC (--`d:num`--) (SPEC (--`b:num`--)
                    LESS_MONO_ADD))
       val th3 = ONCE_REWRITE_RULE [ADD_SYM] th2
       val th4 = CONJ (UNDISCH_ALL th1) (UNDISCH_ALL th3)
       val th5 = MATCH_MP LESS_TRANS th4
       val th6 = DISCH_ALL th5
   in
   store_thm ("MULT_LESS_EQ_SUC",
     --`!m n p. m <= n = ((SUC p) * m) <= ((SUC p) * n)`--,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [LESS_MONO_MULT],
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)] THEN
    SPEC_TAC ((--`p:num`--),(--`p:num`--)) THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES],
     STRIP_TAC THEN
     RES_TAC THEN
     ONCE_REWRITE_TAC [MULT_CLAUSES] THEN
     IMP_RES_TAC th6]])
   end;


val SUB_LEFT_ADD = store_thm ("SUB_LEFT_ADD",
   --`!m n p. m + (n - p) = ((n <= p) => m | (m + n) - p)`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`n <= p`--) THENL
   [IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th,ADD_CLAUSES])
       (SYM (SPEC_ALL SUB_EQ_0)),
    ASSUM_LIST
       (MAP_EVERY
           (ASSUME_TAC o
            (PURE_REWRITE_RULE [SYM (SPEC_ALL NOT_LESS),NOT_CLAUSES]))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) LESS_EQ_ADD_SUB]);

val SUB_RIGHT_ADD = store_thm ("SUB_RIGHT_ADD",
   --`!m n p. (m - n) + p = ((m <= n) => p | (m + p) - n)`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`m <= n`--) THENL
   [IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th,ADD_CLAUSES])
       (SYM (SPEC_ALL SUB_EQ_0)),
    ASSUM_LIST
       (MAP_EVERY
           (ASSUME_TAC o
            (PURE_REWRITE_RULE [SYM (SPEC_ALL NOT_LESS),NOT_CLAUSES]))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
    IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) LESS_EQ_ADD_SUB]);

val SUB_LEFT_SUB = store_thm ("SUB_LEFT_SUB",
   --`!m n p. m - (n - p) = ((n <= p) => m | (m + p) - n)`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`n <= p`--) THENL
   [IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th,SUB_0])
                                           (SYM (SPEC_ALL SUB_EQ_0)),
    ASSUM_LIST
       (MAP_EVERY
           (ASSUME_TAC o
            (PURE_REWRITE_RULE [SYM (SPEC_ALL NOT_LESS),NOT_CLAUSES]))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) SUB_SUB]);

val SUB_RIGHT_SUB = store_thm ("SUB_RIGHT_SUB",
   --`!m n p. (m - n) - p = m - (n + p)`--,
   REPEAT INDUCT_TAC THEN
   REWRITE_TAC [SUB_0,ADD_CLAUSES,SUB_MONO_EQ] THEN
   PURE_ONCE_REWRITE_TAC [SYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
   PURE_ONCE_ASM_REWRITE_TAC [] THEN REFL_TAC);

val SUB_LEFT_SUC = store_thm ("SUB_LEFT_SUC",
   --`!m n. SUC (m - n) = ((m <= n) => (SUC 0) | (SUC m) - n)`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`m <= n`--) THENL
   [IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) (SYM (SPEC_ALL SUB_EQ_0)),
    ASM_REWRITE_TAC [SUB] THEN
    ASSUM_LIST (MAP_EVERY (REWRITE_TAC o CONJUNCTS o
                           (PURE_REWRITE_RULE [LESS_OR_EQ,DE_MORGAN_THM])))]);

val SUB_LEFT_LESS_EQ = store_thm ("SUB_LEFT_LESS_EQ",
   --`!m n p. (m <= (n - p)) = ((m + p) <= n) \/ (m <= 0)`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`p <= n`--) THENL
   [SUBST_TAC [SYM (SPECL [(--`m:num`--),(--`n - p`--),(--`p:num`--)]
                          LESS_EQ_MONO_ADD_EQ)] THEN
    IMP_RES_THEN (fn th => PURE_ONCE_REWRITE_TAC [th]) SUB_ADD THEN
    ASM_CASES_TAC (--`m <= 0`--) THENL
    [IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th,ADD_CLAUSES,LESS_EQ_REFL])
        (fst (EQ_IMP_RULE (REWRITE_RULE [NOT_LESS_0]
                              (SPECL [(--`m:num`--),(--`0`--)] LESS_OR_EQ)))),
     ASM_REWRITE_TAC []],
    ASSUM_LIST
       (MAP_EVERY
           (ASSUME_TAC o
            (PURE_REWRITE_RULE [SYM (SPEC_ALL NOT_LESS),NOT_CLAUSES]))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN (fn th => PURE_ONCE_REWRITE_TAC [th])
       (snd (EQ_IMP_RULE (SPEC_ALL SUB_EQ_0))) THEN
    BOOL_CASES_TAC (--`m <= 0`--) THENL
    [REWRITE_TAC [],
     PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
     IMP_RES_THEN (fn th => REWRITE_TAC [th,SYM (SPEC_ALL NOT_LESS),
                                         NOT_CLAUSES])
        LESS_IMP_LESS_ADD]]);

val SUB_RIGHT_LESS_EQ = store_thm ("SUB_RIGHT_LESS_EQ",
   --`!m n p. ((m - n) <= p) = (m <= (n + p))`--,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`n <= m`--) THENL
   [IMP_RES_THEN (fn th => PURE_ONCE_REWRITE_TAC [th]) SUB_LESS_EQ_ADD THEN
    REFL_TAC,
    ASSUM_LIST
       (MAP_EVERY
           (ASSUME_TAC o
            (PURE_REWRITE_RULE [SYM (SPEC_ALL NOT_LESS),NOT_CLAUSES]))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN (fn th => PURE_REWRITE_TAC [th,ZERO_LESS_EQ])
       (snd (EQ_IMP_RULE (SPEC_ALL SUB_EQ_0))) THEN
    IMP_RES_THEN (fn th => REWRITE_TAC [th,LESS_OR_EQ]) LESS_IMP_LESS_ADD]);

val SUB_LEFT_LESS = store_thm ("SUB_LEFT_LESS",
   --`!m n p. (m < (n - p)) = ((m + p) < n)`--,
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [LESS_EQ,SYM (SPEC_ALL (CONJUNCT2 ADD))] THEN
   PURE_ONCE_REWRITE_TAC [SUB_LEFT_LESS_EQ] THEN
   REWRITE_TAC [SYM (SPEC_ALL LESS_EQ),NOT_LESS_0]);

val SUB_RIGHT_LESS =
   let val BOOL_EQ_NOT_BOOL_EQ = prove
       (--`!x y. (x = y) = (~x = ~y)`--,
        REPEAT GEN_TAC THEN
        BOOL_CASES_TAC (--`x:bool`--) THEN
        REWRITE_TAC [])
   in
   store_thm ("SUB_RIGHT_LESS",
   --`!m n p. ((m - n) < p) = ((m < (n + p)) /\ (0 < p))`--,
   REPEAT GEN_TAC THEN
   PURE_ONCE_REWRITE_TAC [BOOL_EQ_NOT_BOOL_EQ] THEN
   PURE_REWRITE_TAC [DE_MORGAN_THM,NOT_LESS] THEN
   SUBST1_TAC (SPECL [(--`n:num`--),(--`p:num`--)] ADD_SYM) THEN
   REWRITE_TAC [SUB_LEFT_LESS_EQ])
   end;

val SUB_LEFT_GREATER_EQ = store_thm ("SUB_LEFT_GREATER_EQ",
   --`!m n p. (m >= (n - p)) = ((m + p) >= n)`--,
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [GREATER_OR_EQ,GREATER_DEF] THEN
   CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV) THENC
             RATOR_CONV (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV))) THEN
   PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL LESS_OR_EQ)] THEN
   SUBST1_TAC (SPECL [(--`m:num`--),(--`p:num`--)] ADD_SYM) THEN
   REWRITE_TAC [SUB_RIGHT_LESS_EQ]);

val SUB_RIGHT_GREATER_EQ = store_thm ("SUB_RIGHT_GREATER_EQ",
   --`!m n p. ((m - n) >= p) = ((m >= (n + p)) \/ (0 >= p))`--,
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [GREATER_OR_EQ,GREATER_DEF] THEN
   CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV) THENC
             RATOR_CONV (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV))) THEN
   PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL LESS_OR_EQ)] THEN
   SUBST1_TAC (SPECL [(--`n:num`--),(--`p:num`--)] ADD_SYM) THEN
   REWRITE_TAC [SUB_LEFT_LESS_EQ]);

val SUB_LEFT_GREATER = store_thm ("SUB_LEFT_GREATER",
   --`!m n p. (m > (n - p)) = (((m + p) > n) /\ (m > 0))`--,
   REPEAT GEN_TAC THEN
   PURE_ONCE_REWRITE_TAC [GREATER_DEF] THEN
   SUBST1_TAC (SPECL [(--`m:num`--),(--`p:num`--)] ADD_SYM) THEN
   REWRITE_TAC [SUB_RIGHT_LESS]);

val SUB_RIGHT_GREATER = store_thm ("SUB_RIGHT_GREATER",
   --`!m n p. ((m - n) > p) = (m > (n + p))`--,
   REPEAT GEN_TAC THEN
   PURE_ONCE_REWRITE_TAC [GREATER_DEF] THEN
   SUBST1_TAC (SPECL [(--`n:num`--),(--`p:num`--)] ADD_SYM) THEN
   REWRITE_TAC [SUB_LEFT_LESS]);

val SUB_LEFT_EQ = store_thm ("SUB_LEFT_EQ",
   --`!m n p. (m = (n - p)) = ((m + p) = n) \/ ((m <= 0) /\ (n <= p))`--,
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC
      [EQ_LESS_EQ,SUB_LEFT_LESS_EQ,SUB_RIGHT_LESS_EQ,RIGHT_AND_OVER_OR] THEN
   SUBST1_TAC (SPECL [(--`p:num`--),(--`m:num`--)] ADD_SYM) THEN
   ASM_CASES_TAC (--`m = 0`--) THENL
   [ASM_REWRITE_TAC [ADD_CLAUSES],
    IMP_RES_TAC (REWRITE_RULE [ADD_CLAUSES] (SPEC (--`0`--) LESS_ADD_NONZERO))
    THEN ASM_REWRITE_TAC [SYM (SPECL [(--`0`--),(--`m:num`--)] NOT_LESS)]]);

val SUB_RIGHT_EQ = store_thm ("SUB_RIGHT_EQ",
   --`!m n p. ((m - n) = p) = (m = (n + p)) \/ ((m <= n) /\ (p <= 0))`--,
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC
      [EQ_LESS_EQ,SUB_LEFT_LESS_EQ,SUB_RIGHT_LESS_EQ,LEFT_AND_OVER_OR] THEN
   SUBST1_TAC (SPECL [(--`p:num`--),(--`n:num`--)] ADD_SYM) THEN
   ASM_CASES_TAC (--`p = 0`--) THENL
   [ASM_REWRITE_TAC [ADD_CLAUSES],
    IMP_RES_TAC
       (PURE_ONCE_REWRITE_RULE [ADD_CLAUSES] (SPEC (--`0`--) LESS_ADD_NONZERO))
       THEN
       ASM_REWRITE_TAC [SYM (SPECL [(--`0`--),(--`p:num`--)] NOT_LESS)]]);

val LE = save_thm("LE",
         CONJ LESS_EQ_0
              (prove(Term`(!m n. m <= SUC n = (m = SUC n) \/ m <= n)`,
                REPEAT GEN_TAC
                  THEN SUBST_TAC[SPEC (Term`SUC n`)
                          (SPEC (Term`m:num`) LESS_OR_EQ)]
                  THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
                  THEN ASM_REWRITE_TAC[] THENL
                  [DISJ2_TAC THEN REWRITE_TAC[LESS_OR_EQ]
                    THEN IMP_RES_TAC prim_recTheory.LESS_LEMMA1
                    THEN ASM_REWRITE_TAC[],
                   DISJ1_TAC
                     THEN IMP_RES_TAC LESS_EQ_IMP_LESS_SUC])));

val _ = print "Proving division\n"

(* =====================================================================*)
(* Added TFM 90.05.24                                                   *)
(*                                                                      *)
(* Prove the division algorithm:                                        *)
(*                                                                      *)
(*                    |- !k n. n>0 ==> ?q r. k=qn+r /\ 0<= r < n      *)
(*                                                                      *)
(* The proof follows MacLane & Birkhoff, p29.                           *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* We first show that ?r q. k=qn+r.  This is easy, with r=k and q=0.    *)
(* ---------------------------------------------------------------------*)

val exists_lemma = prove
  (--`?r q. (k=(q*n)+r)`--,
   MAP_EVERY EXISTS_TAC [--`k:num`--,--`0`--] THEN
   REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES]);

(* ---------------------------------------------------------------------*)
(* We now show, using the well ordering property, that there is a       *)
(* SMALLEST n' such that ?q. k=qn+n'.  This is the correct remainder.   *)
(*                                                                      *)
(* The theorem is: |- ?n'. (?q. k = q*n+n') /\                          *)
(*                        (!y. y<n' ==> (!q. ~(k=q*n+y)))               *)
(* ---------------------------------------------------------------------*)
val smallest_lemma =
    CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV)
              (MATCH_MP (CONV_RULE (DEPTH_CONV BETA_CONV)
                                   (SPEC (--`\r.?q.k=(q*n)+r`--) WOP))
                        exists_lemma);

(* We will need the lemma  |- !m n. n <= m ==> (?p. m = n + p)          *)
val leq_add_lemma = prove
   (--`!m n. (n<=m) ==> ?p.m=n+p`--,
    REWRITE_TAC [LESS_OR_EQ] THEN
    REPEAT STRIP_TAC THENL
    [FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1) THEN
     EXISTS_TAC (--`p+1`--) THEN
     FIRST_ASSUM ACCEPT_TAC,
     EXISTS_TAC (--`0`--) THEN
     ASM_REWRITE_TAC [ADD_CLAUSES]]);

(* We will also need the lemma:  |- k=qn+n+p ==> k=(q+1)*n+p            *)
val k_expr_lemma = prove
  (--`(k=(q*n)+(n+p)) ==> (k=((q+1)*n)+p)`--,
   REWRITE_TAC [RIGHT_ADD_DISTRIB,MULT_CLAUSES,ADD_ASSOC]);

(* We will also need the lemma: [0<n] |- p < (n + p)                    *)
val less_add = TAC_PROOF(([--`0<n`--], --`p < (n + p)`--),
   PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC LESS_ADD_NONZERO THEN
   IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) LESS_ADD_1 THEN
   REWRITE_TAC [ADD_CLAUSES, ONE, NOT_SUC]);

(* Now prove the desired theorem.                                       *)
val DA = store_thm ("DA",
--`!k n. 0<n ==> ?r q. (k=(q*n)+r) /\ r<n`--,
   REPEAT STRIP_TAC THEN
   STRIP_ASSUME_TAC smallest_lemma THEN
   MAP_EVERY EXISTS_TAC [--`n':num`--,--`q:num`--] THEN
   ASM_REWRITE_TAC [] THEN
   DISJ_CASES_THEN CHECK_ASSUME_TAC
                   (SPECL [--`n':num`--,--`n:num`--] LESS_CASES) THEN
   IMP_RES_THEN (STRIP_THM_THEN SUBST_ALL_TAC) leq_add_lemma THEN
   IMP_RES_TAC k_expr_lemma THEN
   ANTE_RES_THEN IMP_RES_TAC less_add);

(* ---------------------------------------------------------------------*)
(* We can now define MOD and DIV to have the property given by DA.      *)
(* We prove the existence of the required functions, and then define    *)
(* MOD and DIV using a constant specification.                          *)
(* ---------------------------------------------------------------------*)

(* First prove the existence of MOD.                                    *)
val MOD_exists = prove
   (--`?MOD. !n. (0<n) ==>
                 !k.?q.(k=((q * n)+(MOD k n))) /\ ((MOD k n) < n)`--,
     EXISTS_TAC (--`\k n. @r. ?q. (k = (q * n) + r) /\ r < n`--) THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (--`k:num`--)) DA THEN
     CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
     CONV_TAC SELECT_CONV THEN
     MAP_EVERY EXISTS_TAC [--`r:num`--,--`q:num`--] THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

(* Now, prove the existence of MOD and DIV.                             *)
val MOD_DIV_exist = prove
  (--`?MOD DIV.
      !n. 0<n ==>
          !k. (k = ((DIV k n * n) + MOD k n)) /\ (MOD k n < n)`--,
     STRIP_ASSUME_TAC MOD_exists THEN
     EXISTS_TAC (--`MOD:num->num->num`--) THEN
     EXISTS_TAC (--`\k n.  @q. (k = (q * n) + (MOD k n))`--) THEN
     REPEAT STRIP_TAC THENL
     [CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
      CONV_TAC SELECT_CONV THEN
      RES_THEN (STRIP_ASSUME_TAC o SPEC (--`k:num`--)) THEN
      EXISTS_TAC (--`q:num`--) THEN
      FIRST_ASSUM ACCEPT_TAC,
      RES_THEN (STRIP_ASSUME_TAC o SPEC (--`k:num`--))]);

(*---------------------------------------------------------------------------
            Now define MOD and DIV by a constant specification.
 ---------------------------------------------------------------------------*)

val DIVISION = new_specification
   {name = "DIVISION",
    consts = [{fixity = Infixl 650, const_name = "MOD"},
              {fixity = Infixl 600, const_name = "DIV"}],
    sat_thm = MOD_DIV_exist};


(* ---------------------------------------------------------------------*)
(* Properties of MOD and DIV that don't depend on uniqueness.           *)
(* ---------------------------------------------------------------------*)

val MOD_ONE = store_thm("MOD_ONE",
--`!k. k MOD (SUC 0) = 0`--,
   STRIP_TAC THEN
   let val th = REWRITE_RULE [LESS_SUC_REFL]
                             (SPEC (--`SUC 0`--) DIVISION)
   in
   MP_TAC (CONJUNCT2 (SPEC (--`k:num`--) th)) THEN
   REWRITE_TAC [LESS_THM,NOT_LESS_0]
   end);

val DIV_LESS_EQ = store_thm("DIV_LESS_EQ",
 --`!n. 0<n ==> !k. (k DIV n) <= k`--,
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (--`k:num`--)) DIVISION THEN
   FIRST_ASSUM (fn th => fn g => SUBST_OCCS_TAC [([2],th)] g) THEN
   REPEAT_TCL STRIP_THM_THEN MP_TAC (SPEC (--`n:num`--) num_CASES) THENL
   [IMP_RES_TAC LESS_NOT_EQ THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    RES_TAC,
    DISCH_THEN (fn th => SUBST_OCCS_TAC [([3],th)]) THEN
    REWRITE_TAC [MULT_CLAUSES] THEN
    REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
    MATCH_ACCEPT_TAC LESS_EQ_ADD]);


(* ---------------------------------------------------------------------*)
(* Now, show that the quotient and remainder are unique.                *)
(*                                                                      *)
(* NB: the beastly proof given below of DIV_UNIQUE is definitely NOT    *)
(*     good HOL style.                                                  *)
(* ---------------------------------------------------------------------*)

val lemma = prove
(Term`!x y z. x<y ==> ~(y + z = x)`,
REPEAT STRIP_TAC THEN POP_ASSUM (SUBST_ALL_TAC o SYM)
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[]
  THEN SPEC_TAC (Term`y:num`,Term`y:num`)
  THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES,NOT_LESS_0,LESS_MONO_EQ]);

local val (eq,ls) =
   CONJ_PAIR (SPEC (--`k:num`--)
       (REWRITE_RULE [LESS_0] (SPEC (--`SUC(r+p)`--) DIVISION)))
in
val DIV_UNIQUE = store_thm("DIV_UNIQUE",
 --`!n k q. (?r. (k = q*n + r) /\ r<n) ==> (k DIV n = q)`--,
REPEAT GEN_TAC THEN
 DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2
   MP_TAC (STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1))) THEN
 REWRITE_TAC [ONE,MULT_CLAUSES,ADD_CLAUSES] THEN
 DISCH_THEN
     (fn th1 =>
        MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
        PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)] THEN CONJ_TAC THEN
        DISCH_THEN (fn th2 =>
         MP_TAC (TRANS (SYM eq) th1) THEN STRIP_THM_THEN SUBST_ALL_TAC
          (MATCH_MP LESS_ADD_1 th2))) THEN REWRITE_TAC[] THENL
[MATCH_MP_TAC lemma, MATCH_MP_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ] lemma)]
 THEN REWRITE_TAC [MULT_CLAUSES,GSYM ADD_ASSOC,
           ONCE_REWRITE_RULE [ADD_SYM]LESS_MONO_ADD_EQ]
 THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
            empty_rewrites [RIGHT_ADD_DISTRIB]
 THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) empty_rewrites [ADD_SYM]
 THEN REWRITE_TAC [GSYM ADD_ASSOC]
 THEN GEN_REWRITE_TAC (RAND_CONV) empty_rewrites [ADD_SYM] THEN
 REWRITE_TAC [GSYM ADD_ASSOC, ONCE_REWRITE_RULE [ADD_SYM]LESS_MONO_ADD_EQ]
 THENL
  [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN REWRITE_TAC [MULT_CLAUSES,GSYM ADD_ASSOC]
     THEN GEN_REWRITE_TAC (RAND_CONV) empty_rewrites [ADD_SYM]
     THEN REWRITE_TAC [GSYM ADD_ASSOC,ONE,
            REWRITE_RULE[ADD_CLAUSES]
              (ONCE_REWRITE_RULE [ADD_SYM]
                 (SPECL [Term`0`,Term`n:num`,Term`r:num`]LESS_MONO_ADD_EQ))]
     THEN REWRITE_TAC [ADD_CLAUSES, LESS_0],

   MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN EXISTS_TAC (Term`SUC (r+p)`)
     THEN REWRITE_TAC
           [CONJUNCT2(SPEC_ALL(MATCH_MP DIVISION (SPEC(Term`r+p`) LESS_0)))]
     THEN REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,
           MULT_CLAUSES,GSYM ADD_ASSOC,ADD1]
     THEN GEN_REWRITE_TAC (RAND_CONV) empty_rewrites [ADD_SYM]
     THEN REWRITE_TAC [GSYM ADD_ASSOC,
              ONCE_REWRITE_RULE [ADD_SYM]LESS_EQ_MONO_ADD_EQ]
     THEN GEN_REWRITE_TAC (RAND_CONV) empty_rewrites [ADD_SYM]
     THEN REWRITE_TAC [GSYM ADD_ASSOC,
             ONCE_REWRITE_RULE [ADD_SYM]LESS_EQ_MONO_ADD_EQ]
     THEN REWRITE_TAC[ZERO_LESS_EQ,
               REWRITE_RULE[ADD_CLAUSES]
                 (SPECL [Term`1`,Term`0`,Term`p:num`]ADD_MONO_LESS_EQ)]])
end;

val lemma = prove
(--`!n k q r. ((k = (q * n) + r) /\ r < n) ==> (k DIV n = q)`--,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC DIV_UNIQUE THEN
   EXISTS_TAC (--`r:num`--) THEN
   ASM_REWRITE_TAC []);

val MOD_UNIQUE = store_thm("MOD_UNIQUE",
 --`!n k r. (?q. (k = (q * n) + r) /\ r < n) ==> (k MOD n = r)`--,
   REPEAT STRIP_TAC THEN
   MP_TAC (DISCH_ALL (SPEC (--`k:num`--)
                     (UNDISCH (SPEC (--`n:num`--) DIVISION)))) THEN
   FIRST_ASSUM (fn th => fn g =>
                  let val thm = MATCH_MP LESS_ADD_1 th
                      fun tcl t = (SUBST_OCCS_TAC [([1],t)])
                  in
                  STRIP_THM_THEN tcl thm g
                  end
               ) THEN
   REWRITE_TAC [LESS_0, ONE, ADD_CLAUSES] THEN
   IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) lemma THEN
   FIRST_ASSUM (fn th => fn g => SUBST_OCCS_TAC [([1],th)] g) THEN
   let val th = PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ
   in
   PURE_ONCE_REWRITE_TAC [th] THEN
   DISCH_THEN (STRIP_THM_THEN (fn th => fn g => ACCEPT_TAC (SYM th) g))
   end);

(* ---------------------------------------------------------------------*)
(* Properties of MOD and DIV proved using uniqueness.                   *)
(* ---------------------------------------------------------------------*)

val DIV_MULT = store_thm("DIV_MULT",
 --`!n r. r < n ==> !q. (q*n + r) DIV n = q`--,
   REPEAT GEN_TAC THEN
   REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC (--`n:num`--) num_CASES) THENL
   [REWRITE_TAC [NOT_LESS_0],
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIV_UNIQUE THEN
    EXISTS_TAC (--`r:num`--) THEN
    ASM_REWRITE_TAC []]);

val LESS_MOD = store_thm("LESS_MOD",
 --`!n k. k < n ==> ((k MOD n) = k)`--,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC MOD_UNIQUE THEN
   EXISTS_TAC (--`0`--) THEN
   ASM_REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES]);

val MOD_EQ_0 = store_thm("MOD_EQ_0",
 --`!n. 0<n ==> !k. ((k * n) MOD n) = 0`--,
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (--`k * n`--)) DIVISION THEN
   MATCH_MP_TAC MOD_UNIQUE THEN
   EXISTS_TAC (--`k:num`--) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [ADD_CLAUSES], FIRST_ASSUM ACCEPT_TAC]);

val ZERO_MOD = store_thm("ZERO_MOD",
 --`!n. 0<n ==> (0 MOD n = 0)`--,
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (MP_TAC o SPEC (--`0`--)) MOD_EQ_0 THEN
   REWRITE_TAC [MULT_CLAUSES]);

val ZERO_DIV = store_thm("ZERO_DIV",
   --`!n. 0<n ==> (0 DIV n = 0)`--,
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC DIV_UNIQUE THEN
     EXISTS_TAC (--`0`--) THEN
     ASM_REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES]);

val MOD_MULT = store_thm("MOD_MULT",
 --`!n r. r < n ==> !q. (q * n + r) MOD n = r`--,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC MOD_UNIQUE THEN
   EXISTS_TAC (--`q:num`--) THEN
   ASM_REWRITE_TAC [ADD_CLAUSES,MULT_CLAUSES]);

val MOD_TIMES = store_thm("MOD_TIMES",
 --`!n. 0<n ==> !q r. (((q * n) + r) MOD n) = (r MOD n)`--,
   let fun SUBS th = SUBST_OCCS_TAC [([1],th)]
   in
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (--`r:num`--)) DIVISION THEN
   REWRITE_TAC [ADD_ASSOC,SYM(SPEC_ALL RIGHT_ADD_DISTRIB)] THEN
   IMP_RES_THEN (ASSUME_TAC o SPEC (--`r:num`--)) DIVISION THEN
   IMP_RES_TAC MOD_MULT THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC
   end);

val MOD_PLUS = store_thm("MOD_PLUS",
 --`!n. 0<n ==> !j k. (((j MOD n) + (k MOD n)) MOD n) = ((j+k) MOD n)`--,
   let fun SUBS th = SUBST_OCCS_TAC [([2],th)]
   in
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC MOD_TIMES THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (--`j:num`--)) DIVISION THEN
   ASM_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
   PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (--`k:num`--)) DIVISION THEN
   ASM_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)]
   end);

val MOD_MOD = store_thm("MOD_MOD",
 --`!n. 0<n ==> (!k. (k MOD n) MOD n = (k MOD n))`--,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC LESS_MOD THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (--`k:num`--)) DIVISION);


(* LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)

val LESS_DIV_EQ_ZERO = save_thm("LESS_DIV_EQ_ZERO",
    GENL [(--`r:num`--),(--`n:num`--)] (DISCH_ALL (PURE_REWRITE_RULE[MULT,ADD]
    (SPEC (--`0`--)(UNDISCH_ALL (SPEC_ALL  DIV_MULT))))));


(* MULT_DIV = |- !n q. 0 < n ==> ((q * n) DIV n = q) *)

val MULT_DIV = save_thm("MULT_DIV",
    GEN_ALL (PURE_REWRITE_RULE[ADD_0]
    (CONV_RULE RIGHT_IMP_FORALL_CONV
               (SPECL[(--`n:num`--),(--`0`--)] DIV_MULT))));

val ADD_DIV_ADD_DIV = store_thm("ADD_DIV_ADD_DIV",
--`!n. 0 < n ==> !x r. ((((x * n) + r) DIV n) = x + (r DIV n))`--,
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC (--`r < n`--) THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC (--`r:num`--) DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME (--`r = (q * n) + r'`--))
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB]
      THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT]);

val NOT_MULT_LESS_0 = prove(
    (--`!m n. 0<m /\ 0<n ==> 0 < m*n`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,LESS_0]);

val MOD_MULT_MOD = store_thm("MOD_MULT_MOD",
--`!m n. 0<n /\ 0<m  ==> !x. ((x MOD (n * m)) MOD n = x MOD n)`--,
REPEAT GEN_TAC THEN DISCH_TAC
 THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NOT_MULT_LESS_0)) THEN GEN_TAC
 THEN POP_ASSUM(CHOOSE_TAC o (MATCH_MP(SPECL[Term`x:num`,Term`m * n`] DA)))
 THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
 THEN SUBST1_TAC (ASSUME(--`x = (q * (n * m)) + r`--))
 THEN POP_ASSUM (SUBST1_TAC o (SPEC (--`q:num`--)) o MATCH_MP MOD_MULT)
 THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
 THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
 THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
 THEN STRIP_ASSUME_TAC (ASSUME  (--`0 < n /\ 0 < m`--))
 THEN PURE_ONCE_REWRITE_TAC[UNDISCH_ALL(SPEC_ALL MOD_TIMES)]
 THEN REFL_TAC);


(* |- !q. q DIV (SUC 0) = q *)
val DIV_ONE = save_thm("DIV_ONE",
    GEN_ALL (REWRITE_RULE[REWRITE_RULE[ONE] MULT_RIGHT_1]
    (MP (SPECL [(--`SUC 0`--), (--`q:num`--)] MULT_DIV)
        (SPEC (--`0`--) LESS_0))));

val DIVMOD_ID = store_thm(
  "DIVMOD_ID",
  Term`!n. 0 < n ==> (n DIV n = 1) /\ (n MOD n = 0)`,
  REPEAT STRIP_TAC THENL [
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
    MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]
  ]);

val Less_lemma = prove(
Term`!m n. m<n ==> ?p. (n = m + p) /\ 0<p`,
 GEN_TAC THEN INDUCT_TAC THENL[
  REWRITE_TAC[NOT_LESS_0],
  REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
      EXISTS_TAC (--`SUC 0`--)
    	THEN REWRITE_TAC[LESS_0,ADD_CLAUSES],
    	RES_TAC THEN EXISTS_TAC (--`SUC p`--)
    	THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_0]]]);

val Less_MULT_lemma = prove(
    (--`!r m p. 0<p ==> r<m ==> r < p*m`--),
    let val lem1 = MATCH_MP LESS_LESS_EQ_TRANS
    	(CONJ (SPEC (--`m:num`--) LESS_SUC_REFL)
    	      (SPECL[(--`SUC m`--), (--`p * (SUC m)`--)] LESS_EQ_ADD))
   in
    GEN_TAC THEN REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN DISCH_TAC THEN REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
    THEN PURE_ONCE_REWRITE_TAC[MULT]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THENL[
      ACCEPT_TAC lem1,
      ACCEPT_TAC (MATCH_MP LESS_TRANS (CONJ (ASSUME (--`r < m`--)) lem1))]
   end);

val Less_MULT_ADD_lemma = prove(
Term`!m n r r'. 0<m /\ 0<n /\ r<m /\ r'<n ==> r'*m + r < n*m`,
 REPEAT STRIP_TAC
  THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (--`r<m`--)))
  THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (--`r'<n`--)))
  THEN ASM_REWRITE_TAC[]
  THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
  THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
  THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_ADD_EQ]
  THEN SUBST1_TAC (SYM (ASSUME(--`m = r + p`--)))
  THEN IMP_RES_TAC Less_MULT_lemma);

val DIV_DIV_DIV_MULT = store_thm("DIV_DIV_DIV_MULT",
--`!m n. 0<m /\ 0<n ==> !x. ((x DIV m) DIV n = x  DIV (m * n))`--,
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN REPEAT STRIP_TAC
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`x:num`--) (MATCH_MP DA (ASSUME (--`0 < m`--))))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`q:num`--) (MATCH_MP DA (ASSUME (--`0 < n`--))))
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN ASSUME_TAC (MATCH_MP NOT_MULT_LESS_0
    	(CONJ (ASSUME (--`0 < n`--)) (ASSUME (--`0 < m`--))))
    THEN CONV_TAC ((RAND_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
    THEN CONV_TAC SYM_CONV THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN FIRST_ASSUM (fn t => REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV t])
    THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO
    THEN IMP_RES_TAC Less_MULT_ADD_lemma);

val POS_ADD = prove(Term`!m n. 0<m+n = 0<m \/ 0<n`,
REPEAT GEN_TAC
  THEN STRUCT_CASES_TAC (SPEC (Term`m:num`) num_CASES)
  THEN STRUCT_CASES_TAC (SPEC (Term`n:num`) num_CASES)
  THEN ASM_REWRITE_TAC[ADD_CLAUSES,prim_recTheory.LESS_0]);

val POS_MULT = prove(Term`!m n. 0<m*n = 0<m /\ 0<n`,
REPEAT GEN_TAC
  THEN STRUCT_CASES_TAC (SPEC (Term`m:num`) num_CASES)
  THEN STRUCT_CASES_TAC (SPEC (Term`n:num`) num_CASES)
  THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,prim_recTheory.LESS_0]);

val SUC_PRE = prove(Term`!d. 0<d ==> (SUC(PRE d) = d)`,
REPEAT GEN_TAC
  THEN STRUCT_CASES_TAC (SPEC (Term`d:num`) num_CASES)
  THEN ASM_REWRITE_TAC[prim_recTheory.PRE,prim_recTheory.LESS_REFL]);

val LESS_MONO_LEM =
GEN_ALL
  (REWRITE_RULE [ADD_CLAUSES]
    (SPECL (map Term [`0`, `y:num`, `x:num`])
      (ONCE_REWRITE_RULE[ADD_SYM]LESS_MONO_ADD)));

val DIV_LESS = store_thm("DIV_LESS",
Term`!n d. 0<n /\ 1<d ==> n DIV d < n`,
REWRITE_TAC [ONE] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC prim_recTheory.SUC_LESS
  THEN CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC
         (SPEC(Term`n:num`) (UNDISCH(SPEC(Term`d:num`) DIVISION)))
  THEN RULE_ASSUM_TAC (REWRITE_RULE [POS_ADD])
  THEN MP_TAC (SPEC (Term`d:num`) ADD_DIV_ADD_DIV) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fn th => REWRITE_TAC [th])
  THEN MP_TAC (SPECL (map Term[`n MOD d`, `d:num`]) LESS_DIV_EQ_ZERO)
  THEN ASM_REWRITE_TAC []
  THEN DISCH_THEN (fn th => REWRITE_TAC [th,ADD_CLAUSES])
  THEN SUBGOAL_THEN (Term`?m. d = SUC m`) (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC (Term`PRE d`) THEN IMP_RES_TAC SUC_PRE THEN ASM_REWRITE_TAC[],
   REWRITE_TAC [MULT_CLAUSES,GSYM ADD_ASSOC]
    THEN MATCH_MP_TAC LESS_MONO_LEM
    THEN PAT_ASSUM (Term`x \/ y`) MP_TAC
    THEN REWRITE_TAC[POS_ADD,POS_MULT] THEN STRIP_TAC THENL
    [DISJ1_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[LESS_MONO_EQ]), ALL_TAC]
    THEN ASM_REWRITE_TAC[]]);


val num_case_cong =
  save_thm("num_case_cong", Prim_rec.case_cong_thm num_CASES num_case_def);

open simpLib boolSimps
val SUC_ELIM_THM = store_thm(
  "SUC_ELIM_THM",
  (--`!P. (!n. P (SUC n) n) = (!n. (0 < n ==> P n (n-1)))`--),
  GEN_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (--`n-1`--)) THEN
      SIMP_TAC bool_ss [SUB_LEFT_SUC, ONE, SUB_MONO_EQ, SUB_0,
                        GSYM NOT_LESS] THEN
      COND_CASES_TAC THENL [
        STRIP_ASSUME_TAC (SPECL [--`n:num`--, --`SUC 0`--] LESS_LESS_CASES)
        THENL [
          FULL_SIMP_TAC bool_ss [],
          IMP_RES_TAC LESS_LESS_SUC,
          RES_TAC
        ],
        REWRITE_TAC []
      ],
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (--`n+1`--)) THEN
      SIMP_TAC bool_ss [GSYM ADD1, SUC_SUB1, LESS_0]
    ]);

val ADD_SUBR2 = prove
 (Term `!m n. m - (m + n) = 0`,
  REWRITE_TAC [SUB_EQ_0, LESS_EQ_ADD]);

val SUB_ELIM_THM = store_thm("SUB_ELIM_THM",
 Term`P (a - b) = !d. ((b = a + d) ==> P 0) /\ ((a = b + d) ==> P d)`,
 DISJ_CASES_TAC(SPECL [Term`a:num`, Term`b:num`] LESS_EQ_CASES) THEN
  FIRST_ASSUM(X_CHOOSE_TAC (Term`e:num`) o REWRITE_RULE[LESS_EQ_EXISTS]) THEN
  ASM_REWRITE_TAC[ADD_SUB, ONCE_REWRITE_RULE [ADD_SYM] ADD_SUB, ADD_SUBR2] THEN
  REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ] THEN
  CONV_TAC (DEPTH_CONV FORALL_AND_CONV) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM ADD_ASSOC, ADD_INV_0_EQ, ADD_EQ_0] THENL
   [EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fn th => MATCH_MP_TAC th THEN EXISTS_TAC (Term`e:num`)),
    EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THEN GEN_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC),
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)]] THEN
  ASM_REWRITE_TAC[]);

val PRE_ELIM_THM = store_thm("PRE_ELIM_THM",
 Term`P (PRE n) = !m. ((n = 0) ==> P 0) /\ ((n = SUC m) ==> P m)`,
  SPEC_TAC(Term`n:num`,Term`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[NOT_SUC, INV_SUC_EQ, GSYM NOT_SUC, PRE] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC]);

val _ = print "Additional properties of EXP\n"

val MULT_INCREASES = store_thm(
  "MULT_INCREASES",
  Term`!m n. 1 < m /\ 0 < n ==> SUC n <= m * n`,
  INDUCT_TAC THENL [
    REWRITE_TAC [NOT_LESS_0],
    REWRITE_TAC [MULT, GSYM LESS_EQ] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [ADD_COMM] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
    REWRITE_TAC [MULT_EQ_0] THEN STRIP_TAC THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ONE, LESS_REFL]) THEN
    FIRST_ASSUM ACCEPT_TAC
  ]);

val EXP_ALWAYS_BIG_ENOUGH = store_thm(
  "EXP_ALWAYS_BIG_ENOUGH",
  Term`!b. 1 < b ==> !n. ?m. n <= b EXP m`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC [ZERO_LESS_EQ],
    POP_ASSUM STRIP_ASSUME_TAC THEN
    Q.ASM_CASES_TAC `SUC n <= b EXP m` THENL [
      mesonLib.ASM_MESON_TAC [],
      SUBGOAL_THEN ``n = b EXP m`` STRIP_ASSUME_TAC THENL [
        POP_ASSUM (MP_TAC o REWRITE_RULE [GSYM LESS_EQ]) THEN
        POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LESS_OR_EQ]) THEN
        ASM_REWRITE_TAC [],
        ALL_TAC
      ] THEN
      Q.EXISTS_TAC `SUC m` THEN REWRITE_TAC [EXP] THEN
      POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MULT_INCREASES THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `b` num_CASES) THENL [
        IMP_RES_TAC NOT_LESS_0,
        REWRITE_TAC [GSYM NOT_ZERO_LT_ZERO, NOT_EXP_0]
      ]
    ]
  ]);

val EXP_EQ_0 = store_thm(
  "EXP_EQ_0",
  Term`!n m. (n EXP m = 0) = (n = 0) /\ (0 < m)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `m` num_CASES) THEN
  REWRITE_TAC [EXP, GSYM NOT_ZERO_LT_ZERO, ONE, NOT_SUC, MULT_EQ_0] THEN
  EQ_TAC THEN STRIP_TAC THENL [
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `n` num_CASES) THEN
    REWRITE_TAC [] THEN IMP_RES_TAC NOT_EXP_0,
    ASM_REWRITE_TAC []
  ]);

val EXP_1 = store_thm(
  "EXP_1",
  Term`!n. (1 EXP n = 1) /\ (n EXP 1 = n)`,
  CONV_TAC (QUANT_CONV (FORK_CONV (ALL_CONV, REWRITE_CONV [ONE]))) THEN
  REWRITE_TAC [EXP, MULT_CLAUSES] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_EQ_1, EXP]);

val EXP_EQ_1 = store_thm(
  "EXP_EQ_1",
  Term`!n m. (n EXP m = 1) = (n = 1) \/ (m = 0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `m` THEN INDUCT_TAC THEN
    REWRITE_TAC [EXP, MULT_EQ_1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [EXP_1],
    ASM_REWRITE_TAC [EXP]
  ]);

val EXP_INJECTIVE = store_thm(
  "EXP_INJECTIVE",
  Term`!b. 1 < b ==> !n m. (b EXP n = b EXP m) = (n = m)`,
  GEN_TAC THEN STRIP_TAC THEN
  Q.SUBGOAL_THEN `~(b = 1)` ASSUME_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [LESS_REFL],
    ALL_TAC
  ] THEN INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXP, NOT_SUC, GSYM NOT_SUC, MULT_EQ_1, INV_SUC_EQ,
     CONV_RULE (QUANT_CONV (QUANT_CONV (LHS_CONV
                    (ONCE_REWRITE_CONV [EQ_SYM_EQ])))) MULT_EQ_1] THEN
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `b` num_CASES) THENL [
    IMP_RES_TAC NOT_LESS_0,
    ASM_REWRITE_TAC [MULT_MONO_EQ]
  ]);


val EXISTS_GREATEST = store_thm("EXISTS_GREATEST",
--`!P. (?x. P x) /\ (?x:num. !y. y > x ==> ~P y)
                 =
       ?x. P x /\ !y. y > x ==> ~P y`--,
GEN_TAC THEN EQ_TAC THENL
 [REWRITE_TAC[GREATER_DEF] THEN
   DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
   SUBGOAL_THEN
     (Term`(?x. !y. x < y ==> ~P y) = (?x. (\x. !y. x < y ==> ~P y) x)`)
        SUBST1_TAC THENL
    [BETA_TAC THEN REFL_TAC,
     DISCH_THEN (MP_TAC o MATCH_MP WOP)
      THEN BETA_TAC THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
      THEN STRIP_TAC THEN EXISTS_TAC (Term`n:num`) THEN ASM_REWRITE_TAC[]
      THEN NTAC 2 (POP_ASSUM MP_TAC)
      THEN STRUCT_CASES_TAC (SPEC (Term`n:num`) num_CASES)
      THEN REPEAT STRIP_TAC THENL
      [UNDISCH_THEN (Term`!y. 0 < y ==> ~P y`)
            (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV))
         THEN REWRITE_TAC[] THEN STRIP_TAC THEN RES_TAC
         THEN MP_TAC (SPEC (Term`x:num`) LESS_0_CASES)
         THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (SUBST_ALL_TAC o SYM)
         THEN ASM_REWRITE_TAC[],
       POP_ASSUM (MP_TAC o SPEC (Term`n':num`))
         THEN REWRITE_TAC [prim_recTheory.LESS_SUC_REFL]
         THEN DISCH_THEN (CHOOSE_THEN MP_TAC)
         THEN SUBGOAL_THEN (Term`!x y. ~(x ==> ~y) = x /\ y`)
               (fn th => REWRITE_TAC[th] THEN STRIP_TAC) THENL
         [REWRITE_TAC [NOT_IMP],
           UNDISCH_THEN (Term`!y. SUC n' < y ==> ~P y`)
              (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)
                 o SPEC (Term`y:num`))
            THEN ASM_REWRITE_TAC[NOT_LESS,LESS_OR_EQ]
            THEN DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC)
            THENL [IMP_RES_TAC LESS_LESS_SUC, ASM_REWRITE_TAC[]]]]],
  REPEAT STRIP_TAC THEN EXISTS_TAC (Term`x:num`) THEN ASM_REWRITE_TAC[]]);


val _ = adjoin_to_theory
{sig_ps = SOME (fn ppstrm =>
                let val SNL = (fn s => (PP.add_string ppstrm s;
                                        PP.add_newline ppstrm))
                in
                  SNL "val SUC_ELIM_CONV : Term.term -> thm"
                end),
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
 in
   S "local";
   S "  open HolKernel basicHol90Lib Psyntax";
   S "  infix |-> THENC";
   S "  val num_ty = mk_type(\"num\", [])";
   S "  val SUC = mk_const(\"SUC\", mk_type(\"fun\", [num_ty, num_ty]))";
   S "  fun mk_SUC t = mk_comb(SUC, t)";
   S "  fun SEC_ERR m = HOL_ERR {message = m, ";
   S "                           origin_function = \"SUC_ELIM_CONV\",";
   S "                           origin_structure = \"arithmeticTheory\"}";
   S "  fun assert f x = f x orelse raise SEC_ERR \"assertion failed\"";
   S "in";
   S "  fun SUC_ELIM_CONV tm =";
   S "    let val (v,bod) = Psyntax.dest_forall tm";
   S "        val _ = assert (fn x => type_of x = num_ty) v";
   S "        val (sn,n) = (genvar num_ty, genvar num_ty)";
   S "        val suck_suc = Rsyntax.subst [mk_SUC v |-> sn] bod";
   S "        val suck_n = Rsyntax.subst [v |-> n] suck_suc";
   S "        val _ = assert (fn x => x <> tm) suck_n";
   S "        val th1 = ISPEC (list_mk_abs ([sn,n],suck_n)) SUC_ELIM_THM";
   S "        val BETA2_CONV = (RATOR_CONV BETA_CONV) THENC BETA_CONV";
   S "        val th2 = CONV_RULE (LHS_CONV (QUANT_CONV BETA2_CONV)) th1";
   S "        val th3 = ";
   S "          CONV_RULE (RHS_CONV (QUANT_CONV ";
   S "             (FORK_CONV (ALL_CONV, BETA2_CONV)))) th2";
   S "    in th3";
   S "    end";
   S "end;";

   S "val _ = TypeBase.write";
   S "  (TypeBase.mk_tyinfo";
   S "     {ax=prim_recTheory.num_Axiom,";
   S "      case_def=num_case_def,";
   S "      case_cong=num_case_cong,";
   S "      induction=numTheory.INDUCTION,";
   S "      nchotomy=num_CASES,";
   S "      size=SOME(Parse.Term`\\x:num. x`, boolTheory.REFL_CLAUSE),";
   S "      one_one=SOME prim_recTheory.INV_SUC_EQ,";
   S "      distinct=SOME numTheory.NOT_SUC});"
 end)};


val _ = export_theory();

end;
