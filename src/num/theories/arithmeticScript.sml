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

(* interactive use:

   app load ["prim_recTheory", "Q", "metisLib", "boolSimps"];
*)

open HolKernel boolLib Parse
     Prim_rec simpLib boolSimps metisLib BasicProvers;


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
    rec_axiom = num_Axiom,
    def = --`($+ 0 n = n) /\
             ($+ (SUC m) n = SUC($+ m n))`--};

val _ = set_fixity "+" (Infixl 500);

(*---------------------------------------------------------------------------*
 * Define NUMERAL, a tag put on numeric literals, and the basic constructors *
 * of the "numeral type".                                                    *
 *---------------------------------------------------------------------------*)

val NUMERAL_DEF = new_definition("NUMERAL_DEF", --`NUMERAL (x:num) = x`--);

val ALT_ZERO  = new_definition("ALT_ZERO",    --`ZERO = 0`--);

val BIT1 =
  new_definition("BIT1",
                 --`BIT1 n = n + (n + SUC 0)`--);
val BIT2 =
  new_definition("BIT2",
                 --`BIT2 n = n + (n + SUC (SUC 0))`--);

val _ = new_definition(
  GrammarSpecials.nat_elim_term,
  --`^(mk_var(GrammarSpecials.nat_elim_term, Type`:num->num`)) n = n`--);

(*---------------------------------------------------------------------------*
 * After this call, numerals parse into `NUMERAL( ... )`                     *
 *---------------------------------------------------------------------------*)

val _ = add_numeral_form (#"n", NONE);

val _ = set_fixity "-" (Infixl 500);
val _ = Unicode.unicode_version {u = UTF8.chr 0x2212, tmnm = "-"};
val SUB = new_recursive_definition
   {name = "SUB",
    rec_axiom = num_Axiom,
    def = --`(0 - m = 0) /\
             (SUC m - n = if m < n then 0 else SUC(m - n))`--};

(* Also add concrete syntax for unary negation so that future numeric types
   can use it.  We can't do anything useful with it for the natural numbers
   of course, but it seems like this is the best ancestral place for it.

   Descendents wanting to use this will include at least
     integer, real, words, rat
*)
val _ = add_rule { term_name = "numeric_negate",
                   fixity = TruePrefix 900,
                   pp_elements = [TOK "-"],
                   paren_style = OnlyIfNecessary,
                   block_style = (AroundEachPhrase, (PP.CONSISTENT,0))};

(* Similarly, add syntax for the injection from nats symbol (&).  This isn't
   required in this theory, but will be used by descendents. *)
val _ = add_rule {term_name = GrammarSpecials.num_injection,
                  fixity = TruePrefix 900,
                  pp_elements = [TOK GrammarSpecials.num_injection],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,0))};
(* overload it to the nat_elim term *)
val _ = overload_on (GrammarSpecials.num_injection,
                     mk_const(GrammarSpecials.nat_elim_term, ``:num -> num``))


val _ = set_fixity "*" (Infixl 600);
val MULT = new_recursive_definition
   {name = "MULT",
    rec_axiom = num_Axiom,
    def = --`(0 * n = 0) /\
             (SUC m * n = (m * n) + n)`--};


val EXP = new_recursive_definition
   {name = "EXP",
    rec_axiom = num_Axiom,
    def = --`($EXP m 0 = 1) /\
             ($EXP m (SUC n) = m * ($EXP m n))`--};

val _ = set_fixity "EXP" (Infixr 700);
val _ = add_infix("**", 700, HOLgrammars.RIGHT);
val _ = overload_on ("**", Term`$EXP`);

val GREATER_DEF = new_definition("GREATER_DEF", ``$> m n = n < m``)
val _ = set_fixity ">" (Infix(NONASSOC, 450))

val LESS_OR_EQ = new_definition ("LESS_OR_EQ", ``$<= m n = m < n \/ (m = n)``)
val _ = set_fixity "<=" (Infix(NONASSOC, 450))
val _ = Unicode.unicode_version { u = Unicode.UChar.leq, tmnm = "<="}

val GREATER_OR_EQ =
    new_definition("GREATER_OR_EQ", ``$>= m n = m > n \/ (m = n)``)
val _ = set_fixity ">=" (Infix(NONASSOC, 450))
val _ = Unicode.unicode_version { u = Unicode.UChar.geq, tmnm = ">="};

val EVEN = new_recursive_definition
   {name = "EVEN",
    rec_axiom = num_Axiom,
    def = --`(EVEN 0 = T) /\
             (EVEN (SUC n) = ~EVEN n)`--};

val ODD = new_recursive_definition
   {name = "ODD",
    rec_axiom = num_Axiom,
    def = --`(ODD 0 = F) /\
             (ODD (SUC n) = ~ODD n)`--};

val num_case_def = new_recursive_definition
   {name = "num_case_def",
    rec_axiom = num_Axiom,
    def = --`(num_case b f 0 = (b:'a)) /\
             (num_case b f (SUC n) = f n)`--};

val FUNPOW = new_recursive_definition
   {name = "FUNPOW",
    rec_axiom = num_Axiom,
    def = --`(FUNPOW f 0 x = x) /\
             (FUNPOW f (SUC n) x = FUNPOW f n (f x))`--};

val NRC = new_recursive_definition {
  name = "NRC",
  rec_axiom = num_Axiom,
  def = ``(NRC R 0 x y = (x = y)) /\
          (NRC R (SUC n) x y = ?z. R x z /\ NRC R n z y)``};

val _ = overload_on ("RELPOW", ``NRC``)
val _ = overload_on ("NRC", ``NRC``)

(*---------------------------------------------------------------------------
                        THEOREMS
 ---------------------------------------------------------------------------*)

val ONE = store_thm("ONE", Term `1 = SUC 0`,
REWRITE_TAC [NUMERAL_DEF, BIT1, ALT_ZERO, ADD]);

val TWO = store_thm("TWO", Term`2 = SUC 1`,
REWRITE_TAC [NUMERAL_DEF, BIT2, ONE, ADD, ALT_ZERO,BIT1]);

val NORM_0 = store_thm("NORM_0",Term `NUMERAL ZERO = 0`,
  REWRITE_TAC [NUMERAL_DEF, ALT_ZERO]);

fun INDUCT_TAC g = INDUCT_THEN INDUCTION ASSUME_TAC g;

val EQ_SYM_EQ' = INST_TYPE [alpha |-> Type`:num`] EQ_SYM_EQ;


(*---------------------------------------------------------------------------*)
(* Definition of num_case more suitable to call-by-value computations        *)
(*---------------------------------------------------------------------------*)

val num_case_compute = store_thm("num_case_compute",
  Term `!n. num_case (f:'a) g n = if n=0 then f else g (PRE n)`,
INDUCT_TAC THEN REWRITE_TAC [num_case_def,NOT_SUC,PRE]);

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
   INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);

val ADD_CLAUSES = store_thm("ADD_CLAUSES",
   --`(0 + m = m)              /\
      (m + 0 = m)              /\
      (SUC m + n = SUC(m + n)) /\
      (m + SUC n = SUC(m + n))`--,
   REWRITE_TAC[ADD, ADD_0, ADD_SUC]);

val ADD_SYM = store_thm ("ADD_SYM",
  --`!m n. m + n = n + m`--,
  INDUCT_TAC
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
     --`!m n. n<m ==> ?p. p+n = m`--,
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
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN IMP_RES_TAC LESS_REFL);

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
   INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES, INV_SUC_EQ]);

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

val LESS_EQ_ADD_EXISTS = store_thm ("LESS_EQ_ADD_EXISTS",
     --`!m n. n<=m ==> ?p. p+n = m`--,
     SIMP_TAC bool_ss [LESS_OR_EQ, DISJ_IMP_THM, FORALL_AND_THM,
		       LESS_ADD] 
      THEN GEN_TAC 
      THEN EXISTS_TAC (--`0`--) 
      THEN REWRITE_TAC[ADD]);

val LESS_STRONG_ADD = store_thm ("LESS_STRONG_ADD",
     --`!m n. n < m ==> ?p. (SUC p)+n = m`--,
     REPEAT STRIP_TAC 
      THEN IMP_RES_TAC LESS_OR 
      THEN IMP_RES_TAC LESS_EQ_ADD_EXISTS
      THEN EXISTS_TAC (--`p:num`--) 
      THEN FULL_SIMP_TAC bool_ss [ADD_CLAUSES]);

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
val LT_ADD_RCANCEL = save_thm("LT_ADD_RCANCEL", LESS_MONO_ADD_EQ)
val LT_ADD_LCANCEL = save_thm("LT_ADD_LCANCEL",
                              ONCE_REWRITE_RULE [ADD_COMM] LT_ADD_RCANCEL)

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

val LESS_MONO_MULT2 = store_thm(
  "LESS_MONO_MULT2",
  ``!m n i j. m <= i /\ n <= j ==> m * n <= i * j``,
  mesonLib.MESON_TAC [LESS_EQ_TRANS, LESS_MONO_MULT, MULT_COMM]);

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


val FORALL_NUM_THM = Q.store_thm
 ("FORALL_NUM_THM",
  `(!n. P n) = P 0 /\ !n. P n ==> P (SUC n)`,
  METIS_TAC [INDUCTION]);

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
   REWRITE_TAC [MULT_CLAUSES, NUMERAL_DEF, BIT2, ADD_CLAUSES,ALT_ZERO]);

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

val EQ_ADD_LCANCEL = store_thm(
  "EQ_ADD_LCANCEL",
  Term`!m n p. (m + n = m + p) = (n = p)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ]);

val EQ_ADD_RCANCEL = store_thm(
  "EQ_ADD_RCANCEL",
  Term`!m n p. (m + p = n + p) = (m = n)`,
  ONCE_REWRITE_TAC[ADD_COMM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL);

val EQ_MULT_LCANCEL = store_thm(
  "EQ_MULT_LCANCEL",
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

val MULT_EQ_ID = store_thm
("MULT_EQ_ID",
 ``!m n. (m * n = n) = (m=1) \/ (n=0)``,
 REPEAT GEN_TAC THEN 
 STRUCT_CASES_TAC (SPEC ``m:num`` num_CASES) THEN 
 REWRITE_TAC [MULT_CLAUSES,ONE,GSYM NOT_SUC,INV_SUC_EQ] THENL
 [METIS_TAC[], METIS_TAC [ADD_INV_0_EQ,MULT_EQ_0,ADD_SYM]]);

val LESS_MULT2 = store_thm("LESS_MULT2",
  --`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`--,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[NOT_LESS, LESS_EQ_0, DE_MORGAN_THM, MULT_EQ_0]);

val ZERO_LESS_MULT = store_thm(
  "ZERO_LESS_MULT",
  ``!m n. 0 < m * n = 0 < m /\ 0 < n``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [MULT_CLAUSES, LESS_REFL, LESS_0] THEN
  Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [MULT_CLAUSES, LESS_REFL, LESS_0, ADD_CLAUSES]);

val ZERO_LESS_ADD = store_thm(
  "ZERO_LESS_ADD",
  ``!m n. 0 < m + n = 0 < m \/ 0 < n``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [ADD_CLAUSES, LESS_REFL, LESS_0]);

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
  REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2] THEN
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

val EVEN_EXP = Q.store_thm (
"EVEN_EXP",
`!m n. 0 < n /\ EVEN m ==> EVEN (m ** n)`,
REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (Q.SPEC `n` num_CASES) THEN
RW_TAC bool_ss [EXP, EVEN_MULT] THEN
METIS_TAC [prim_recTheory.NOT_LESS_0]);

(* --------------------------------------------------------------------- *)
(* Theorems moved from the "more_arithmetic" library      [RJB 92.09.28] *)
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
val LE_ADD_LCANCEL = save_thm("LE_ADD_LCANCEL", ADD_MONO_LESS_EQ)
val LE_ADD_RCANCEL = save_thm("LE_ADD_RCANCEL",
                              ONCE_REWRITE_RULE [ADD_COMM] LE_ADD_LCANCEL)

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

val LE_MULT_LCANCEL = store_thm(
  "LE_MULT_LCANCEL",
  ``!m n p. m * n <= m * p = (m = 0) \/ n <= p``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m`  STRUCT_CASES_TAC num_CASES THENL [
    REWRITE_TAC [LESS_EQ_REFL, MULT_CLAUSES],
    REWRITE_TAC [NOT_SUC, GSYM MULT_LESS_EQ_SUC]
  ]);

val LE_MULT_RCANCEL = store_thm(
  "LE_MULT_RCANCEL",
  ``!m n p. m * n <= p * n = (n = 0) \/ m <= p``,
  ONCE_REWRITE_TAC [MULT_COMM] THEN REWRITE_TAC [LE_MULT_LCANCEL]);

val LT_MULT_LCANCEL = store_thm(
  "LT_MULT_LCANCEL",
  ``!m n p. m * n < m * p = 0 < m /\ n < p``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THENL [
    REWRITE_TAC [MULT_CLAUSES, LESS_REFL],
    REWRITE_TAC [LESS_MULT_MONO, LESS_0]
  ]);

val LT_MULT_RCANCEL = store_thm(
  "LT_MULT_RCANCEL",
  ``!m n p. m * n < p * n = 0 < n /\ m < p``,
  ONCE_REWRITE_TAC [MULT_COMM] THEN REWRITE_TAC [LT_MULT_LCANCEL]);

(* |- (m < m * n = 0 < m /\ 1 < n) /\ (m < n * m = 0 < m /\ 1 < n) *)
val LT_MULT_CANCEL_LBARE = save_thm(
  "LT_MULT_CANCEL_LBARE",
  CONJ
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`m`, `1`, `n`] LT_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`1`,`m`, `n`] LT_MULT_RCANCEL)))

val lt1_eq0 = prove(
  ``x < 1 = (x = 0)``,
  Q.SPEC_THEN `x`  STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [ONE, LESS_0, NOT_LESS_0, LESS_MONO_EQ, NOT_SUC])

(* |- (m * n < m = 0 < m /\ (n = 0)) /\ (m * n < n = 0 < n /\ (m = 0)) *)
val LT_MULT_CANCEL_RBARE = save_thm(
  "LT_MULT_CANCEL_RBARE",
  CONJ
    (REWRITE_RULE [MULT_CLAUSES, lt1_eq0]
                  (Q.SPECL [`m`,`n`,`1`] LT_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES, lt1_eq0]
                  (Q.SPECL [`m`,`n`,`1`] LT_MULT_RCANCEL)))

val le1_lt0 = prove(``1 <= n = 0 < n``, REWRITE_TAC [LESS_EQ, ONE]);

(* |- (m <= m * n = (m = 0) \/ 0 < n) /\ (m <= n * m = (m = 0) \/ 0 < n) *)
val LE_MULT_CANCEL_LBARE = save_thm(
  "LE_MULT_CANCEL_LBARE",
  CONJ
    (REWRITE_RULE [MULT_CLAUSES, le1_lt0]
                  (Q.SPECL [`m`,`1`,`n`] LE_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES, le1_lt0]
                  (Q.SPECL [`1`,`m`,`n`] LE_MULT_RCANCEL)))

(* |- (m * n <= m = (m = 0) \/ n <= 1) /\ (m * n <= n = (n = 0) \/ m <= 1) *)
val LE_MULT_CANCEL_RBARE = save_thm(
  "LE_MULT_CANCEL_RBARE",
  CONJ
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`m`,`n`,`1`] LE_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`m`,`n`,`1`] LE_MULT_RCANCEL)))

val SUB_LEFT_ADD = store_thm ("SUB_LEFT_ADD",
   --`!m n p. m + (n - p) = (if (n <= p) then m else (m + n) - p)`--,
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
   --`!m n p. (m - n) + p = (if (m <= n) then p else (m + p) - n)`--,
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
   --`!m n p. m - (n - p) = (if (n <= p) then m else (m + p) - n)`--,
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
   --`!m n. SUC (m - n) = (if (m <= n) then (SUC 0) else (SUC m) - n)`--,
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

val DIVISION = new_specification ("DIVISION", ["MOD","DIV"], MOD_DIV_exist);

val _ = set_fixity "MOD" (Infixl 650);
val _ = set_fixity "DIV" (Infixl 600);

val DIV2_def =
  new_definition("DIV2_def",    --`DIV2 n = n DIV 2`--);

val MOD_2EXP_def =
  new_definition("MOD_2EXP_def",
                 --`MOD_2EXP x n = n MOD 2 ** x`--);

val DIV_2EXP_def =
  new_definition("DIV_2EXP_def",
                 --`DIV_2EXP x n = n DIV 2 ** x`--);

(* ---------------------------------------------------------------------*)
(* Properties of MOD and DIV that don't depend on uniqueness.           *)
(* ---------------------------------------------------------------------*)

val MOD_ONE = store_thm("MOD_ONE",
--`!k. k MOD (SUC 0) = 0`--,
   STRIP_TAC THEN
   MP_TAC (CONJUNCT2 (SPEC (--`k:num`--)
            (REWRITE_RULE [LESS_SUC_REFL] (SPEC (--`SUC 0`--) DIVISION)))) THEN
   REWRITE_TAC [LESS_THM,NOT_LESS_0]);

(* |- x MOD 1 = 0 *)
val MOD_1 = save_thm("MOD_1", REWRITE_RULE [SYM ONE] MOD_ONE);


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

val ADD_DIV_RWT = store_thm(
  "ADD_DIV_RWT",
  ``!n. 0 < n ==>
        !m p. (m MOD n = 0) \/ (p MOD n = 0) ==>
              ((m + p) DIV n = m DIV n + p DIV n)``,
  REPEAT STRIP_TAC THEN
  IMP_RES_THEN (ASSUME_TAC o GSYM) DIVISION THEN
  MATCH_MP_TAC DIV_UNIQUE THENL [
    Q.EXISTS_TAC `p MOD n` THEN
    ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, GSYM ADD_ASSOC, EQ_ADD_RCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV (GSYM ADD_0))) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `m MOD n` THEN
    ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    Q.SUBGOAL_THEN `p DIV n * n = p` SUBST1_TAC THENL [
       CONV_TAC (LAND_CONV (REWR_CONV (GSYM ADD_0))) THEN
       FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [],
       ALL_TAC
    ] THEN
    Q.SUBGOAL_THEN `m DIV n * n + p + m MOD n = m DIV n * n + m MOD n + p`
                   (fn th => ASM_REWRITE_TAC [th]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC, EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_COMM
  ]);

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

val DIV_1 = save_thm("DIV_1", REWRITE_RULE [SYM ONE] DIV_ONE);

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

val MOD_LESS = Q.store_thm("MOD_LESS",
 `!m n. 0 < n ==> k MOD n < n`,
 METIS_TAC [DIVISION]);

val ADD_MODULUS = Q.store_thm("ADD_MODULUS",
`(!n x. 0 < n ==> ((x + n) MOD n = x MOD n)) /\
 (!n x. 0 < n ==> ((n + x) MOD n = x MOD n))`,
 METIS_TAC [ADD_SYM,MOD_PLUS,DIVMOD_ID,MOD_MOD,ADD_CLAUSES]);

val ADD_MODULUS_LEFT = save_thm("ADD_MODULUS_LEFT",CONJUNCT1 ADD_MODULUS);
val ADD_MODULUS_RIGHT = save_thm("ADD_MODULUS_RIGHT",CONJUNCT2 ADD_MODULUS);

val DIV_P = store_thm(
  "DIV_P",
  ``!P p q. 0 < q ==>
            (P (p DIV q) = ?k r. (p = k * q + r) /\ r < q /\ P k)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    MAP_EVERY Q.EXISTS_TAC [`p DIV q`, `p MOD q`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION THEN
    FIRST_ASSUM ACCEPT_TAC,
    Q.SUBGOAL_THEN `p DIV q = k` (fn th => SUBST1_TAC th THEN
                                           FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `r` THEN ASM_REWRITE_TAC []
  ]);

val DIV_P_UNIV = store_thm(
  "DIV_P_UNIV",
  ``!P m n. 0 < n ==> (P (m DIV n) = !q r. (m = q * n + r) /\ r < n ==> P q)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Q_TAC SUFF_TAC `m DIV n = q`
          THEN1 (DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC []) THEN
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `r` THEN ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `m MOD n` THEN
    MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC []
  ]);

val MOD_P = store_thm(
  "MOD_P",
  ``!P p q. 0 < q ==>
            (P (p MOD q) = ?k r. (p = k * q + r) /\ r < q /\ P r)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    MAP_EVERY Q.EXISTS_TAC [`p DIV q`, `p MOD q`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION THEN
    FIRST_ASSUM ACCEPT_TAC,
    Q.SUBGOAL_THEN `p MOD q = r` (fn th => SUBST1_TAC th THEN
                                           FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `k` THEN ASM_REWRITE_TAC []
  ]);

val MOD_P_UNIV = store_thm(
  "MOD_P_UNIV",
  ``!P m n. 0 < n ==>
            (P (m MOD n) = !q r. (m = q * n + r) /\ r < n ==> P r)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Q_TAC SUFF_TAC `m MOD n = r`
          THEN1 (DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC []) THEN
    MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `q` THEN ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `m DIV n` THEN
    MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC []
  ]);

(* Could generalise this to work over arbitrary operators by making the
   commutativity and associativity theorems parameters.   It seems OTT
   enough as it is. *)
fun move_var_left s = let
  val v = mk_var(s, ``:num``)
  val th1 = GSYM (SPEC v MULT_COMM)    (*    xv = vx    *)
  val th2 = GSYM (SPEC v MULT_ASSOC)   (* (vx)y = v(xy) *)
  val th3 = CONV_RULE                  (* x(vy) = v(xy) *)
              (STRIP_QUANT_CONV
                 (LAND_CONV (LAND_CONV (REWR_CONV MULT_COMM) THENC
                             REWR_CONV (GSYM MULT_ASSOC)))) th2
in
  (* The complicated conversion at the heart of this could be replaced with
     REWRITE_CONV if that procedure was modified to dynamically throw
     away rewrites that on instantiation turn out to be loops, which it
     could do by wrapping its REWR_CONVs in CHANGED_CONVs.  Perhaps this
     would be inefficient.  *)
  FREEZE_THEN
  (fn th1 => FREEZE_THEN
             (fn th2 => FREEZE_THEN
                        (fn th3 => CONV_TAC
                                     (REDEPTH_CONV
                                      (FIRST_CONV
                                       (map (CHANGED_CONV o REWR_CONV)
                                            [th1, th2, th3])))) th3) th2) th1
end

val MOD_TIMES2 = store_thm(
  "MOD_TIMES2",
  ``!n. 0 < n ==>
        !j k. (j MOD n * k MOD n) MOD n = (j * k) MOD n``,
  REPEAT STRIP_TAC THEN
  IMP_RES_THEN (Q.SPEC_THEN `j` STRIP_ASSUME_TAC) DIVISION THEN
  IMP_RES_THEN (Q.SPEC_THEN `k` STRIP_ASSUME_TAC) DIVISION THEN
  Q.ABBREV_TAC `q = j DIV n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = j MOD n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `u = k DIV n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `v = k MOD n` THEN POP_ASSUM (K ALL_TAC) THEN
  NTAC 2 (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ADD_ASSOC] THEN
  move_var_left "n" THEN REWRITE_TAC [GSYM LEFT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC [MULT_COMM] THEN
  IMP_RES_THEN (fn th => REWRITE_TAC [th]) MOD_TIMES);

val MOD_COMMON_FACTOR = store_thm(
  "MOD_COMMON_FACTOR",
  ``!n p q. 0 < n /\ 0 < q ==> (n * (p MOD q) = (n * p) MOD (n * q))``,
  REPEAT STRIP_TAC THEN Q.SPEC_THEN `q` MP_TAC DIVISION THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (Q.SPEC_THEN `p` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `u = p DIV q` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `v = p MOD q` THEN POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
  move_var_left "u" THEN
  ASM_SIMP_TAC bool_ss [MOD_TIMES, LESS_MULT2] THEN
  SUFF_TAC ``n * v < n * q`` THENL [mesonLib.MESON_TAC [LESS_MOD],
                                    ALL_TAC] THEN
  SUFF_TAC ``?m. n = SUC m`` THENL [
    STRIP_TAC THEN ASM_REWRITE_TAC [LESS_MULT_MONO],
    mesonLib.ASM_MESON_TAC [LESS_REFL, num_CASES]
  ]);

val X_MOD_Y_EQ_X = store_thm(
  "X_MOD_Y_EQ_X",
  ``!x y. 0 < y ==> ((x MOD y = x) = x < y)``,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    mesonLib.ASM_MESON_TAC [DIVISION],
    STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN
    Q.EXISTS_TAC `0` THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]
  ]);

val DIV_LE_MONOTONE = store_thm(
  "DIV_LE_MONOTONE",
  ``!n x y. 0 < n /\ x <= y ==> x DIV n <= y DIV n``,
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [
    ASM_REWRITE_TAC [NOT_ZERO_LT_ZERO],
    ALL_TAC
  ] THEN
  Q.SPEC_THEN `n` MP_TAC DIVISION THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fn th => Q.SPEC_THEN `x` STRIP_ASSUME_TAC th THEN
                       Q.SPEC_THEN `y` STRIP_ASSUME_TAC th) THEN
  Q.ABBREV_TAC `q = x DIV n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = y DIV n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `d = x MOD n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `e = y MOD n` THEN POP_ASSUM (K ALL_TAC) THEN
  SRW_TAC [][] THEN CCONTR_TAC THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LEQ]) THEN  (* SUC r < q *)
  Q.SPECL_THEN [`SUC r`, `n`, `q`] MP_TAC LE_MULT_RCANCEL THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN       (* SUC r * n <= q * n *)
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [MULT_CLAUSES]) THEN
                                               (* r * n + n <= q * n *)
  Q.SPECL_THEN [`e`, `n`, `r * n`] MP_TAC LT_ADD_LCANCEL THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN       (* r * n + e < r * n + n *)
  Q.SPECL_THEN [`q * n`, `d`] ASSUME_TAC LESS_EQ_ADD THEN
                                               (* q * n <= q * n + d *)
  Q.SUBGOAL_THEN `r * n + e < r * n + e` (CONTR_TAC o MATCH_MP LESS_REFL) THEN
  MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN Q.EXISTS_TAC `q * n + d` THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  Q.EXISTS_TAC `r * n + n` THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC `q * n` THEN
  ASM_REWRITE_TAC []);

val LE_LT1 = store_thm(
  "LE_LT1",
  ``!x y. x <= y = x < y + 1``,
  REWRITE_TAC [LESS_OR_EQ, GSYM ADD1,
               IMP_ANTISYM_RULE (SPEC_ALL prim_recTheory.LESS_LEMMA1)
                                (SPEC_ALL prim_recTheory.LESS_LEMMA2)] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [])

val X_LE_DIV = store_thm(
  "X_LE_DIV",
  ``!x y z. 0 < z ==> (x <= y DIV z = x * z <= y)``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `z` MP_TAC DIVISION THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = y DIV z` THEN
  Q.ABBREV_TAC `r = y MOD z` THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL [
    STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    Q.EXISTS_TAC `q * z` THEN
    ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL, LESS_EQ_ADD],
    STRIP_TAC THEN REWRITE_TAC [LE_LT1] THEN
    Q_TAC SUFF_TAC `x * z < (q + 1) * z`
          THEN1 SIMP_TAC bool_ss [LT_MULT_RCANCEL] THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB,
                 MULT_CLAUSES] THEN
    MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
    Q.EXISTS_TAC `q * z + r` THEN
    ASM_SIMP_TAC bool_ss [LT_ADD_LCANCEL]
  ]);

val X_LT_DIV = store_thm(
  "X_LT_DIV",
  ``!x y z. 0 < z ==> (x < y DIV z = (x + 1) * z <= y)``,
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `z` MP_TAC DIVISION THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = y DIV z` THEN
  Q.ABBREV_TAC `r = y MOD z` THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL [
    STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    Q.EXISTS_TAC `q * z` THEN
    ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL, LESS_EQ_ADD] THEN
    ASM_SIMP_TAC bool_ss [LE_LT1, LT_ADD_RCANCEL],
    STRIP_TAC THEN
    CCONTR_TAC THEN
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
    Q.SUBGOAL_THEN `(x + 1) * z  <= x * z + r` ASSUME_TAC THENL [
      MATCH_MP_TAC LESS_EQ_TRANS THEN
      Q.EXISTS_TAC `q * z + r` THEN
      ASM_SIMP_TAC bool_ss [LE_ADD_RCANCEL, LE_MULT_RCANCEL],
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, MULT_CLAUSES,
                       LE_ADD_LCANCEL, GSYM NOT_LESS,
                       LT_ADD_LCANCEL]
    ]
  ]);

val DIV_LT_X = store_thm(
  "DIV_LT_X",
  ``!x y z. 0 < z ==> (y DIV z < x = y < x * z)``,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM NOT_LESS_EQUAL] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC X_LE_DIV THEN
  ASM_REWRITE_TAC []);

val DIV_LE_X = store_thm(
  "DIV_LE_X",
  ``!x y z. 0 < z ==> (y DIV z <= x = y < (x + 1) * z)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (FORK_CONV (REWR_CONV (GSYM NOT_LESS),
                       REWR_CONV (GSYM NOT_LESS_EQUAL))) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC X_LT_DIV THEN
  ASM_REWRITE_TAC []);


val DIV_MOD_MOD_DIV = store_thm(
  "DIV_MOD_MOD_DIV",
  ``!m n k. 0 < n /\ 0 < k ==> ((m DIV n) MOD k = (m MOD (n * k)) DIV n)``,
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `0 < n * k` ASSUME_TAC THENL [
    ASM_REWRITE_TAC [ZERO_LESS_MULT],
    ALL_TAC
  ] THEN
  Q.SPEC_THEN `n * k` MP_TAC DIVISION THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (Q.SPEC_THEN `m` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = m DIV (n * k)` THEN
  Q.ABBREV_TAC `r = m MOD (n * k)` THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN
  ASM_REWRITE_TAC [] THEN
  Q.SUBGOAL_THEN `q * (n * k) = (q * k) * n` SUBST1_TAC THENL [
    SIMP_TAC bool_ss [AC MULT_ASSOC MULT_COMM],
    ALL_TAC
  ] THEN ASM_SIMP_TAC bool_ss [ADD_DIV_ADD_DIV, MOD_TIMES] THEN
  MATCH_MP_TAC LESS_MOD THEN ASM_SIMP_TAC bool_ss [DIV_LT_X] THEN
  FULL_SIMP_TAC bool_ss [AC MULT_ASSOC MULT_COMM]);

(* useful if x and z are both constants *)
val MULT_EQ_DIV = store_thm(
  "MULT_EQ_DIV",
  ``0 < x ==> ((x * y = z) = (y = z DIV x) /\ (z MOD x = 0))``,
  STRIP_TAC THEN EQ_TAC THENL [
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    ONCE_REWRITE_TAC [MULT_COMM] THEN
    ASM_SIMP_TAC bool_ss [MOD_EQ_0, MULT_DIV],
    Q.SPEC_THEN `x` MP_TAC DIVISION THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (Q.SPEC_THEN `z` STRIP_ASSUME_TAC) THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC bool_ss [ADD_CLAUSES, MULT_COMM] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN FIRST_ASSUM ACCEPT_TAC
  ]);

(* as they are here *)
val NUMERAL_MULT_EQ_DIV = store_thm(
  "NUMERAL_MULT_EQ_DIV",
  ``((NUMERAL (BIT1 x) * y = NUMERAL z) =
       (y = NUMERAL z DIV NUMERAL (BIT1 x)) /\
       (NUMERAL z MOD NUMERAL(BIT1 x) = 0)) /\
    ((NUMERAL (BIT2 x) * y = NUMERAL z) =
       (y = NUMERAL z DIV NUMERAL (BIT2 x)) /\
       (NUMERAL z MOD NUMERAL(BIT2 x) = 0))``,
  CONJ_TAC THEN MATCH_MP_TAC MULT_EQ_DIV THEN
  REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, LESS_0]);



(* ----------------------------------------------------------------------
    Some additional theorems (nothing to do with DIV and MOD)
   ---------------------------------------------------------------------- *)

val num_case_cong =
  save_thm("num_case_cong", Prim_rec.case_cong_thm num_CASES num_case_def);

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
          IMP_RES_TAC LESS_LESS_SUC
        ],
        REWRITE_TAC []
      ],
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (--`n+1`--)) THEN
      SIMP_TAC bool_ss [GSYM ADD1, SUC_SUB1, LESS_0]
    ]);

val SUC_ELIM_NUMERALS = store_thm(
  "SUC_ELIM_NUMERALS",
  ``!f g. (!n. g (SUC n) = f n (SUC n)) =
          (!n. g (NUMERAL (BIT1 n)) =
               f (NUMERAL (BIT1 n) - 1) (NUMERAL (BIT1 n))) /\
          (!n. g (NUMERAL (BIT2 n)) =
               f (NUMERAL (BIT1 n)) (NUMERAL (BIT2 n)))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC bool_ss [NUMERAL_DEF, BIT1, BIT2, ALT_ZERO,
                    ADD_CLAUSES, SUB_MONO_EQ, SUB_0] THEN
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `n` STRIP_ASSUME_TAC EVEN_OR_ODD THEN
  POP_ASSUM (Q.X_CHOOSE_THEN `m` SUBST_ALL_TAC o
             REWRITE_RULE [EVEN_EXISTS, ODD_EXISTS, TIMES2]) THEN
  ASM_REWRITE_TAC []);



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

val ZERO_LT_EXP = store_thm(
  "ZERO_LT_EXP",
  ``0 < x EXP y = 0 < x \/ (y = 0)``,
  METIS_TAC [NOT_ZERO_LT_ZERO, EXP_EQ_0]);

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

(* theorems about exponentiation where the base is held constant *)

val expbase_le_mono = prove(
  ``1 < b /\ m <= n ==> b ** m <= b ** n``,
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `?q. n = m + q` STRIP_ASSUME_TAC THEN1
    METIS_TAC [LESS_EQUAL_ADD] THEN
  SRW_TAC [][EXP_ADD] THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM MULT_RIGHT_1))) THEN
  ASM_REWRITE_TAC [LE_MULT_LCANCEL, EXP_EQ_0, ONE, GSYM LESS_EQ,
                   ZERO_LT_EXP] THEN
  METIS_TAC [ONE, LESS_TRANS, LESS_0])

val expbase_lt_mono = prove(
  ``1 < b /\ m < n ==> b ** m < b ** n``,
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `?q. n = m + q` STRIP_ASSUME_TAC THEN1
    METIS_TAC [LESS_ADD, ADD_COMM] THEN
  SRW_TAC [][EXP_ADD] THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM MULT_RIGHT_1))) THEN
  ASM_REWRITE_TAC [LT_MULT_LCANCEL, ZERO_LT_EXP] THEN
  Q.SUBGOAL_THEN `0 < b` ASSUME_TAC
    THEN1 METIS_TAC [ONE, LESS_TRANS, LESS_0] THEN
  Q.SUBGOAL_THEN `1 < b ** q \/ b ** q < 1 \/ (b ** q = 1)` STRIP_ASSUME_TAC
    THEN1 METIS_TAC [LESS_CASES, LESS_OR_EQ] THEN
  ASM_REWRITE_TAC [] THENL [
    Q.SUBGOAL_THEN `b ** q = 0` ASSUME_TAC THEN1
      METIS_TAC [LESS_MONO_EQ, NOT_LESS_0, num_CASES, ONE] THEN
    FULL_SIMP_TAC (srw_ss()) [EXP_EQ_0, NOT_LESS_0],
    FULL_SIMP_TAC (srw_ss()) [EXP_EQ_1] THEN
    FULL_SIMP_TAC (srw_ss()) [LESS_REFL, ADD_CLAUSES]
  ]);

val EXP_BASE_LE_MONO = store_thm(
  "EXP_BASE_LE_MONO",
  ``!b. 1 < b ==> !n m. b ** m <= b ** n = m <= n``,
  METIS_TAC [expbase_lt_mono, expbase_le_mono, NOT_LESS_EQUAL]);
val EXP_BASE_LT_MONO = store_thm(
  "EXP_BASE_LT_MONO",
  ``!b. 1 < b ==> !n m. b ** m < b ** n = m < n``,
  METIS_TAC [expbase_lt_mono, expbase_le_mono, NOT_LESS]);

val EXP_BASE_INJECTIVE = store_thm(
  "EXP_BASE_INJECTIVE",
  ``!b. 1 < b ==> !n m. (b EXP n = b EXP m) = (n = m)``,
  METIS_TAC [LESS_EQUAL_ANTISYM, LESS_EQ_REFL, EXP_BASE_LE_MONO]);

val EXP_BASE_LEQ_MONO_IMP = store_thm(
  "EXP_BASE_LEQ_MONO_IMP",
  ``!n m b. 0 < b /\ m <= n ==> b ** m <= b ** n``,
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC LESS_EQUAL_ADD THEN ASM_REWRITE_TAC [EXP_ADD] THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM MULT_RIGHT_1))) THEN
  ASM_REWRITE_TAC [LE_MULT_LCANCEL, EXP_EQ_0, ONE, GSYM LESS_EQ] THEN
  FULL_SIMP_TAC bool_ss [GSYM NOT_ZERO_LT_ZERO, EXP_EQ_0]);

(*  |- m <= n ==> SUC b ** m <= SUC b ** n *)
val EXP_BASE_LEQ_MONO_SUC_IMP = save_thm(
  "EXP_BASE_LEQ_MONO_SUC_IMP",
  (REWRITE_RULE [LESS_0] o Q.INST [`b` |-> `SUC b`] o SPEC_ALL)
  EXP_BASE_LEQ_MONO_IMP);


(* theorems about exponentiation where the exponent is held constant *)
val LT_MULT_IMP = prove(
  ``a < b /\ x < y ==> a * x < b * y``,
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `0 < y` ASSUME_TAC THEN1 METIS_TAC [NOT_ZERO_LT_ZERO,
                                                     NOT_LESS_0] THEN
  METIS_TAC [LE_MULT_LCANCEL, LT_MULT_RCANCEL, LESS_EQ_LESS_TRANS,
             LESS_OR_EQ])
val LE_MULT_IMP = prove(
  ``a <= b /\ x <= y ==> a * x <= b * y``,
  METIS_TAC [LE_MULT_LCANCEL, LE_MULT_RCANCEL, LESS_EQ_TRANS]);

val EXP_LT_MONO_0 = prove(
  ``!n. 0 < n ==> !a b. a < b ==> a EXP n < b EXP n``,
  INDUCT_TAC THEN SRW_TAC [][NOT_LESS_0, LESS_0, EXP] THEN
  Q.SPEC_THEN `n` STRIP_ASSUME_TAC num_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [EXP, MULT_CLAUSES, LESS_0] THEN
  SRW_TAC [][LT_MULT_IMP])
val EXP_LE_MONO_0 = prove(
  ``!n. 0 < n ==> !a b. a <= b ==> a EXP n <= b EXP n``,
  INDUCT_TAC THEN SRW_TAC [][EXP, LESS_EQ_REFL] THEN
  Q.SPEC_THEN `n` STRIP_ASSUME_TAC num_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [EXP, MULT_CLAUSES, LESS_0] THEN
  SRW_TAC [][LE_MULT_IMP]);

val EXP_EXP_LT_MONO = store_thm(
  "EXP_EXP_LT_MONO",
  ``!a b. a EXP n < b EXP n = a < b /\ 0 < n``,
  METIS_TAC [EXP_LT_MONO_0, NOT_LESS, EXP_LE_MONO_0, EXP, LESS_REFL,
             NOT_ZERO_LT_ZERO]);

val EXP_EXP_LE_MONO = store_thm(
  "EXP_EXP_LE_MONO",
  ``!a b. a EXP n <= b EXP n = a <= b \/ (n = 0)``,
  METIS_TAC [EXP_LE_MONO_0, NOT_LESS_EQUAL, EXP_LT_MONO_0, EXP, LESS_EQ_REFL,
             NOT_ZERO_LT_ZERO]);

val EXP_EXP_INJECTIVE = store_thm(
  "EXP_EXP_INJECTIVE",
  ``!b1 b2 x. (b1 EXP x = b2 EXP x) = (x = 0) \/ (b1 = b2)``,
  METIS_TAC [EXP_EXP_LE_MONO, LESS_EQUAL_ANTISYM, LESS_EQ_REFL]);

val EXP_SUB = Q.store_thm
("EXP_SUB",
  `!p q n. 0 < n /\ q <= p ==> (n ** (p - q) = n ** p DIV n ** q)`,
   REPEAT STRIP_TAC THEN
   ``0 < n ** p /\ 0 < n ** q`` via
        (STRIP_ASSUME_TAC (Q.SPEC`n` num_CASES) THEN
         RW_TAC bool_ss [] THEN
         FULL_SIMP_TAC bool_ss [ZERO_LESS_EXP,LESS_REFL]) THEN
   RW_TAC bool_ss [DIV_P] THEN
   Q.EXISTS_TAC `0` THEN
   RW_TAC bool_ss [GSYM EXP_ADD,ADD_CLAUSES] THEN
   METIS_TAC [SUB_ADD]);

val EXP_BASE_MULT = store_thm(
  "EXP_BASE_MULT",
  ``!z x y. (x * y) ** z = (x ** z) * (y ** z)``,
  INDUCT_TAC THEN
  ASM_SIMP_TAC bool_ss [EXP, MULT_CLAUSES, AC MULT_ASSOC MULT_COMM]);

val EXP_EXP_MULT = store_thm(
 "EXP_EXP_MULT",
 ``!z x y. x ** (y * z) = (x ** y) ** z``,
  INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES, EXP_1, EXP_ADD]);


(* ********************************************************************** *)
(* Maximum and minimum                                                    *)
(* ********************************************************************** *)

val _ = print "Minimums and maximums\n"

val MAX = new_definition("MAX_DEF", ``MAX m n = if m < n then n else m``);
val MIN = new_definition("MIN_DEF", ``MIN m n = if m < n then m else n``);

val ARW = RW_TAC bool_ss

val MAX_COMM = store_thm(
  "MAX_COMM",
  ``!m n. MAX m n = MAX n m``,
  ARW [MAX] THEN FULL_SIMP_TAC bool_ss [NOT_LESS] THEN
  IMP_RES_TAC LESS_ANTISYM THEN IMP_RES_TAC LESS_EQUAL_ANTISYM);

val MIN_COMM = store_thm(
  "MIN_COMM",
  ``!m n. MIN m n = MIN n m``,
  ARW [MIN] THEN FULL_SIMP_TAC bool_ss [NOT_LESS] THEN
  IMP_RES_TAC LESS_ANTISYM THEN IMP_RES_TAC LESS_EQUAL_ANTISYM);

val MAX_ASSOC = store_thm(
  "MAX_ASSOC",
  ``!m n p. MAX m (MAX n p) = MAX (MAX m n) p``,
  SIMP_TAC bool_ss [MAX] THEN
  PROVE_TAC [NOT_LESS, LESS_EQ_TRANS, LESS_TRANS]);

val MIN_ASSOC = store_thm(
  "MIN_ASSOC",
  ``!m n p. MIN m (MIN n p) = MIN (MIN m n) p``,
  SIMP_TAC bool_ss [MIN] THEN
  PROVE_TAC [NOT_LESS, LESS_EQ_TRANS, LESS_TRANS]);

val MIN_MAX_EQ = store_thm(
  "MIN_MAX_EQ",
  ``!m n. (MIN m n = MAX m n) = (m = n)``,
  SIMP_TAC bool_ss [MAX, MIN] THEN
  PROVE_TAC [NOT_LESS, LESS_EQUAL_ANTISYM, LESS_ANTISYM]);

val MIN_MAX_LT = store_thm(
  "MIN_MAX_LT",
  ``!m n. (MIN m n < MAX m n) = ~(m = n)``,
  SIMP_TAC bool_ss [MAX, MIN] THEN
  PROVE_TAC [LESS_REFL, NOT_LESS, LESS_OR_EQ]);

val MIN_MAX_LE = store_thm(
  "MIN_MAX_LE",
  ``!m n. MIN m n <= MAX m n``,
  SIMP_TAC bool_ss [MAX, MIN] THEN
  PROVE_TAC [LESS_OR_EQ, NOT_LESS]);

val MIN_MAX_PRED = store_thm(
  "MIN_MAX_PRED",
  ``!P m n. P m /\ P n ==> P (MIN m n) /\ P (MAX m n)``,
  PROVE_TAC [MIN, MAX]);

val MIN_LT = store_thm(
  "MIN_LT",
  ``!n m p. (MIN m n < p = m < p \/ n < p) /\
            (p < MIN m n = p < m /\ p < n)``,
  SIMP_TAC bool_ss [MIN] THEN
  PROVE_TAC [NOT_LESS, LESS_OR_EQ, LESS_ANTISYM, LESS_TRANS]);

val MAX_LT = store_thm(
  "MAX_LT",
  ``!n m p. (p < MAX m n = p < m \/ p < n) /\
            (MAX m n < p = m < p /\ n < p)``,
  SIMP_TAC bool_ss [MAX] THEN
  PROVE_TAC [NOT_LESS, LESS_OR_EQ, LESS_ANTISYM, LESS_TRANS]);

val MIN_LE = store_thm(
  "MIN_LE",
  ``!n m p. (MIN m n <= p = m <= p \/ n <= p) /\
            (p <= MIN m n = p <= m /\ p <= n)``,
  SIMP_TAC bool_ss [MIN] THEN
  PROVE_TAC [LESS_OR_EQ, NOT_LESS, LESS_TRANS]);

val MAX_LE = store_thm(
  "MAX_LE",
  ``!n m p. (p <= MAX m n = p <= m \/ p <= n) /\
            (MAX m n <= p = m <= p /\ n <= p)``,
  SIMP_TAC bool_ss [MAX] THEN
  PROVE_TAC [LESS_OR_EQ, NOT_LESS, LESS_TRANS]);

val MIN_0 = store_thm(
  "MIN_0",
  ``!n. (MIN n 0 = 0) /\ (MIN 0 n = 0)``,
  REWRITE_TAC [MIN] THEN
  PROVE_TAC [NOT_LESS_0, NOT_LESS, LESS_OR_EQ]);

val MAX_0 = store_thm(
  "MAX_0",
  ``!n. (MAX n 0 = n) /\ (MAX 0 n = n)``,
  REWRITE_TAC [MAX] THEN
  PROVE_TAC [NOT_LESS_0, NOT_LESS, LESS_OR_EQ]);

val MIN_IDEM = store_thm(
  "MIN_IDEM",
  ``!n. MIN n n = n``,
  PROVE_TAC [MIN]);

val MAX_IDEM = store_thm(
  "MAX_IDEM",
  ``!n. MAX n n = n``,
  PROVE_TAC [MAX]);


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

val EXISTS_NUM = store_thm(
  "EXISTS_NUM",
  ``!P. (?n. P n) = P 0 \/ (?m. P (SUC m))``,
  PROVE_TAC [num_CASES]);

val FORALL_NUM = store_thm(
  "FORALL_NUM",
  ``!P. (!n. P n) = P 0 /\ !n. P (SUC n)``,
  PROVE_TAC [num_CASES]);


val BOUNDED_FORALL_THM = Q.store_thm("BOUNDED_FORALL_THM",
`!c. 0<c ==> ((!n. n < c ==> P n) = P (c-1) /\ !n. n < (c-1) ==> P n)`,
 RW_TAC boolSimps.bool_ss [] THEN EQ_TAC THENL
  [REPEAT STRIP_TAC
     THEN FIRST_ASSUM MATCH_MP_TAC THENL
     [METIS_TAC [ONE,LESS_ADD_SUC,ADD_SYM,SUB_RIGHT_LESS],
      MATCH_MP_TAC LESS_LESS_EQ_TRANS
        THEN Q.EXISTS_TAC `c-1`
        THEN ASM_REWRITE_TAC [SUB_LESS_EQ,SUB_LEFT_LESS]],
   METIS_TAC [SUB_LESS_OR,LESS_OR_EQ]]);


val BOUNDED_EXISTS_THM = Q.store_thm("BOUNDED_EXISTS_THM",
`!c. 0<c ==> ((?n. n < c /\ P n) = P (c-1) \/ ?n. n < (c-1) /\ P n)`,
 REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [METIS_TAC [SUB_LESS_OR,LESS_REFL,LESS_EQ_LESS_TRANS,LESS_LESS_CASES],
   METIS_TAC [num_CASES,LESS_REFL,SUC_SUB1,LESS_SUC_REFL],
   METIS_TAC [SUB_LEFT_LESS,ADD1,SUC_LESS]]);


(* ********************************************************************** *)
val _ = print "Miscellaneous theorems\n"
(* ********************************************************************** *)

val FUNPOW_SUC = store_thm
  ("FUNPOW_SUC",
   ``!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)``,
   GEN_TAC
   THEN INDUCT_TAC
   THENL [REWRITE_TAC [FUNPOW],
          ONCE_REWRITE_TAC [FUNPOW]
          THEN ASM_REWRITE_TAC []]);

val FUNPOW_0 = store_thm(
  "FUNPOW_0",
  ``FUNPOW f 0 x = x``,
  REWRITE_TAC [FUNPOW]);
val _ = export_rewrites ["FUNPOW_0"]

val FUNPOW_ADD = store_thm(
  "FUNPOW_ADD",
  ``!m n. FUNPOW f (m + n) x = FUNPOW f m (FUNPOW f n x)``,
  INDUCT_TAC THENL [
    REWRITE_TAC [ADD_CLAUSES, FUNPOW],
    ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW_SUC]
  ]);

val FUNPOW_1 = store_thm(
  "FUNPOW_1",
  ``FUNPOW f 1 x = f x``,
  REWRITE_TAC [FUNPOW, ONE]);
val _ = export_rewrites ["FUNPOW_1"]

val NRC_0 = save_thm("NRC_0", CONJUNCT1 NRC);
val _ = export_rewrites ["NRC_0"]

val NRC_1 = store_thm(
  "NRC_1",
  ``NRC R 1 x y = R x y``,
  SRW_TAC [][ONE, NRC]);
val _ = export_rewrites ["NRC_1"]

val NRC_ADD_I = store_thm(
  "NRC_ADD_I",
  ``!m n x y z. NRC R m x y /\ NRC R n y z ==> NRC R (m + n) x z``,
  INDUCT_TAC THEN SRW_TAC [][NRC, ADD] THEN METIS_TAC []);

val NRC_ADD_E = store_thm(
  "NRC_ADD_E",
  ``!m n x z. NRC R (m + n) x z ==> ?y. NRC R m x y /\ NRC R n y z``,
  INDUCT_TAC THEN SRW_TAC [][NRC, ADD] THEN METIS_TAC []);

val NRC_ADD_EQN = store_thm(
  "NRC_ADD_EQN",
  ``NRC R (m + n) x z = ?y. NRC R m x y /\ NRC R n y z``,
  METIS_TAC [NRC_ADD_I, NRC_ADD_E]);

val NRC_SUC_RECURSE_LEFT = store_thm(
  "NRC_SUC_RECURSE_LEFT",
  ``NRC R (SUC n) x y = ?z. NRC R n x z /\ R z y``,
  METIS_TAC [NRC_1, NRC_ADD_EQN, ADD1]);

val NRC_RTC = store_thm(
  "NRC_RTC",
  ``!n x y. NRC R n x y ==> RTC R x y``,
  INDUCT_TAC THEN SRW_TAC [][NRC, relationTheory.RTC_RULES] THEN
  METIS_TAC [relationTheory.RTC_RULES]);

val RTC_NRC = store_thm(
  "RTC_NRC",
  ``!x y. RTC R x y ==> ?n. NRC R n x y``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  PROVE_TAC [NRC] (* METIS_TAC bombs *));

val RTC_eq_NRC = store_thm (
  "RTC_eq_NRC",
  ``!R x y. RTC R x y = ?n. NRC R n x y``,
  PROVE_TAC[RTC_NRC, NRC_RTC]);


val TC_eq_NRC = store_thm (
  "TC_eq_NRC",
  ``!R x y. TC R x y = ?n. NRC R (SUC n) x y``,
  REWRITE_TAC [relationTheory.EXTEND_RTC_TC_EQN, RTC_eq_NRC, NRC] THEN
  PROVE_TAC[]);


val LESS_EQUAL_DIFF = store_thm
  ("LESS_EQUAL_DIFF",
   ``!m n : num. m <= n ==> ?k. m = n - k``,
   REPEAT GEN_TAC
   THEN SPEC_TAC (``m:num``, ``m:num``)
   THEN SPEC_TAC (``n:num``, ``n:num``)
   THEN INDUCT_TAC
   THENL [REWRITE_TAC [LESS_EQ_0, SUB_0],
          REWRITE_TAC [LE]
          THEN PROVE_TAC [SUB_0, SUB_MONO_EQ]]);

val MOD_2 = store_thm
  ("MOD_2",
   ``!n. n MOD 2 = if EVEN n then 0 else 1``,
   GEN_TAC
   THEN MATCH_MP_TAC MOD_UNIQUE
   THEN ASM_CASES_TAC ``EVEN n``
   THEN POP_ASSUM MP_TAC
   THEN REWRITE_TAC [EVEN_EXISTS, GSYM ODD_EVEN, ODD_EXISTS, ADD1]
   THEN STRIP_TAC
   THEN POP_ASSUM SUBST1_TAC
   THEN Q.EXISTS_TAC `m`
   THENL [PROVE_TAC [MULT_COMM, ADD_0, TWO, prim_recTheory.LESS_0],
          (KNOW_TAC ``(?m' : num. 2 * m + 1 = 2 * m') = F``
           THEN1 PROVE_TAC [EVEN_EXISTS, ODD_EXISTS, ADD1, EVEN_ODD])
          THEN DISCH_THEN (fn th => REWRITE_TAC [th])
          THEN PROVE_TAC [MULT_COMM, ONE, TWO, prim_recTheory.LESS_0,
                          LESS_MONO_EQ]]);

val EVEN_MOD2 = store_thm
  ("EVEN_MOD2",
   ``!x. EVEN x = (x MOD 2 = 0)``,
   PROVE_TAC [MOD_2, SUC_NOT, ONE]);

val SUC_MOD = store_thm
  ("SUC_MOD",
   ``!n a b. 0 < n ==> ((SUC a MOD n = SUC b MOD n) = (a MOD n = b MOD n))``,
   REPEAT STRIP_TAC
   THEN SIMP_TAC boolSimps.bool_ss [ADD1]
   THEN MP_TAC (Q.SPEC `n` (GSYM MOD_PLUS))
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN (REVERSE EQ_TAC THEN1 SIMP_TAC boolSimps.bool_ss [])
   THEN IMP_RES_TAC MOD_MOD
   THEN POP_ASSUM (fn th => MP_TAC (CONJ (Q.SPEC `a` th) (Q.SPEC `b` th)))
   THEN DISCH_THEN
        (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM th])))
   THEN ASM_SIMP_TAC boolSimps.bool_ss [MOD_PLUS]
   THEN (KNOW_TAC ``a MOD n < n /\ b MOD n < n``
         THEN1 RW_TAC boolSimps.bool_ss [DIVISION])
   THEN Q.SPEC_TAC (`b MOD n`, `b`)
   THEN Q.SPEC_TAC (`a MOD n`, `a`)
   THEN SIMP_TAC boolSimps.bool_ss [GSYM ADD1]
   THEN REPEAT STRIP_TAC
   THEN ASM_CASES_TAC ``SUC a < n``
   THENL [IMP_RES_TAC (GSYM DIVISION)
          THEN POP_ASSUM (K ALL_TAC)
          THEN POP_ASSUM (MP_TAC o Q.SPEC `SUC a`)
          THEN ASM_SIMP_TAC boolSimps.bool_ss [LESS_DIV_EQ_ZERO, MULT, ADD]
          THEN DISCH_THEN (ASSUME_TAC o SYM)
          THEN MATCH_MP_TAC numTheory.INV_SUC
          THEN ASM_SIMP_TAC boolSimps.bool_ss []
          THEN MATCH_MP_TAC LESS_MOD
          THEN MATCH_MP_TAC LESS_NOT_SUC
          THEN ASM_REWRITE_TAC []
          THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
          THEN STRIP_TAC
          THEN Q.PAT_ASSUM `X = Y MOD n` MP_TAC
          THEN ASM_SIMP_TAC boolSimps.bool_ss [DIVMOD_ID]
          THEN PROVE_TAC [SUC_NOT],
          Q.PAT_ASSUM `X = Y` MP_TAC
          THEN (KNOW_TAC ``SUC a = n`` THEN1 PROVE_TAC [LESS_NOT_SUC])
          THEN POP_ASSUM (K ALL_TAC)
          THEN ASM_SIMP_TAC boolSimps.bool_ss [DIVMOD_ID]
          THEN STRIP_TAC
          THEN DISCH_THEN (ASSUME_TAC o SYM)
          THEN IMP_RES_TAC (GSYM DIVISION)
          THEN POP_ASSUM (K ALL_TAC)
          THEN POP_ASSUM (MP_TAC o Q.SPEC `SUC b`)
          THEN ASM_SIMP_TAC boolSimps.bool_ss [ADD_0]
          THEN MP_TAC (Q.SPEC `SUC b DIV n` num_CASES)
          THEN (STRIP_TAC THEN1 PROVE_TAC [SUC_NOT, MULT])
          THEN ASM_REWRITE_TAC []
          THEN POP_ASSUM (K ALL_TAC)
          THEN POP_ASSUM (K ALL_TAC)
          THEN MP_TAC (Q.SPEC `n'` num_CASES)
          THEN (STRIP_TAC
                THEN1 (ASM_SIMP_TAC boolSimps.bool_ss [MULT, ADD]
                       THEN PROVE_TAC [numTheory.INV_SUC]))
          THEN ASM_SIMP_TAC boolSimps.bool_ss [MULT, ADD, GSYM ADD_ASSOC]
          THEN STRIP_TAC
          THEN (SUFF_TAC ``F`` THEN1 REWRITE_TAC [])
          THEN (KNOW_TAC ``n + n <= SUC b``
                THEN1 PROVE_TAC [LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL])
          THEN REWRITE_TAC [NOT_LESS_EQUAL, ADD1]
          THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS
          THEN Q.EXISTS_TAC `b + n`
          THEN ASM_REWRITE_TAC [LESS_MONO_ADD_EQ, ADD_MONO_LESS_EQ, ONE]
          THEN PROVE_TAC [LESS_OR]]);


val ADD_MOD = Q.store_thm 
("ADD_MOD",
 `!n a b p.  (0 < n:num) ==> (
	     ((a + p) MOD n = (b + p) MOD n) =
	      (a MOD n = b MOD n))`,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC INDUCTION
  THEN SIMP_TAC bool_ss [ADD_CLAUSES, SUC_MOD]);

(*---------------------------------------------------------------------------*)
(* We should be able to use "by" construct at this phase of development,     *)
(* surely?                                                                   *)
(*---------------------------------------------------------------------------*)

val MOD_ELIM = Q.store_thm
("MOD_ELIM",
 `!P x n. 0 < n /\ P x /\ (!y. P (y + n) ==> P y) ==> P (x MOD n)`,
GEN_TAC THEN HO_MATCH_MP_TAC COMPLETE_INDUCTION
  THEN REPEAT STRIP_TAC
  THEN ASM_CASES_TAC (Term `x >= n`) THENL
  [``P ((x - n) MOD n):bool`` via
      (Q.PAT_ASSUM `!x'. A x' ==> !n. Q x' n` (MP_TAC o Q.SPEC `x-n`) THEN
    ``x-n < x`` via FULL_SIMP_TAC bool_ss
                  [GREATER_OR_EQ,SUB_RIGHT_LESS,GREATER_DEF] THEN
    METIS_TAC [NOT_ZERO_LT_ZERO,ADD_SYM,LESS_ADD_NONZERO,LESS_TRANS,
               SUB_ADD,GREATER_OR_EQ,GREATER_DEF,LESS_OR_EQ,SUB_RIGHT_LESS])
    THEN ``?z. x = z + n`` via (Q.EXISTS_TAC `x - n` THEN
           METIS_TAC [SUB_ADD,GREATER_OR_EQ,GREATER_DEF,LESS_OR_EQ])
    THEN RW_TAC bool_ss []
    THEN METIS_TAC [SUB_ADD,GREATER_OR_EQ,GREATER_DEF,LESS_OR_EQ,ADD_MODULUS],
    METIS_TAC [LESS_MOD,NOT_LESS,LESS_OR_EQ,GREATER_OR_EQ, GREATER_DEF]]);

val DOUBLE_LT = store_thm
  ("DOUBLE_LT",
   ``!p q. 2 * p + 1 < 2 * q = 2 * p < 2 * q``,
   REPEAT GEN_TAC
   THEN (EQ_TAC THEN1 PROVE_TAC [ADD1, prim_recTheory.SUC_LESS])
   THEN STRIP_TAC
   THEN SIMP_TAC boolSimps.bool_ss [GSYM ADD1]
   THEN MATCH_MP_TAC LESS_NOT_SUC
   THEN ASM_REWRITE_TAC []
   THEN PROVE_TAC [EVEN_ODD, EVEN_DOUBLE, ODD_DOUBLE]);

val EXP2_LT = store_thm
  ("EXP2_LT",
   ``!m n. n DIV 2 < 2 ** m = n < 2 ** SUC m``,
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `2` DIVISION)
   THEN (KNOW_TAC ``0n < 2`` THEN1 REWRITE_TAC [TWO, prim_recTheory.LESS_0])
   THEN SIMP_TAC boolSimps.bool_ss []
   THEN STRIP_TAC
   THEN DISCH_THEN (MP_TAC o Q.SPEC `n`)
   THEN DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
   THEN ONCE_REWRITE_TAC [MULT_COMM]
   THEN SIMP_TAC boolSimps.bool_ss [EXP, MOD_2]
   THEN (ASM_CASES_TAC ``EVEN n`` THEN ASM_SIMP_TAC boolSimps.bool_ss [])
   THENL [REWRITE_TAC [TWO, ADD_0, LESS_MULT_MONO],
          REWRITE_TAC [DOUBLE_LT]
          THEN REWRITE_TAC [TWO, ADD_0, LESS_MULT_MONO]]);

val SUB_LESS = Q.store_thm
("SUB_LESS",
 `!m n. 0 < n /\ n <= m ==> m-n < m`,
 REPEAT STRIP_TAC THEN
   ``?p. m = p+n`` via METIS_TAC [LESS_EQ_EXISTS,ADD_SYM]
   THEN RW_TAC bool_ss [ADD_SUB]
   THEN METIS_TAC [LESS_ADD_NONZERO,NOT_ZERO_LT_ZERO]);

val SUB_MOD = Q.store_thm
("SUB_MOD",
 `!m n. 0<n /\ n <= m ==> ((m-n) MOD n = m MOD n)`,
 METIS_TAC [ADD_MODULUS,ADD_SUB,LESS_EQ_EXISTS,ADD_SYM]);

fun Cases (asl,g) = 
 let val (v,_) = dest_forall g
 in GEN_TAC THEN STRUCT_CASES_TAC (SPEC v num_CASES)
 end (asl,g);

fun Cases_on v (asl,g) = STRUCT_CASES_TAC (SPEC v num_CASES) (asl,g);

val ONE_LT_MULT_IMP = Q.store_thm
("ONE_LT_MULT_IMP",
 `!p q. 1 < p /\ 0 < q ==> 1 < p * q`,
 REPEAT Cases THEN 
 RW_TAC bool_ss [MULT_CLAUSES,ADD_CLAUSES] THENL
 [METIS_TAC [LESS_REFL],
  POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN 
  RW_TAC bool_ss [ONE,LESS_MONO_EQ] THEN
  METIS_TAC [LESS_IMP_LESS_ADD, ADD_ASSOC]]);
 
val ONE_LT_MULT = Q.store_thm
("ONE_LT_MULT",
 `!x y. 1 < x * y = 0 < x /\ 1 < y \/ 0 < y /\ 1 < x`,
 REWRITE_TAC [ONE] THEN INDUCT_TAC THEN
 RW_TAC bool_ss [ADD_CLAUSES, MULT_CLAUSES,LESS_REFL,LESS_0] THENL
  [METIS_TAC [NOT_SUC_LESS_EQ_0,LESS_OR_EQ],
   Cases_on ``y:num`` THEN 
   RW_TAC bool_ss [MULT_CLAUSES,ADD_CLAUSES,LESS_REFL,
           LESS_MONO_EQ,ZERO_LESS_ADD,LESS_0] THEN
   METIS_TAC [ZERO_LESS_MULT]]);

val ONE_LT_EXP = Q.store_thm
("ONE_LT_EXP",
 `!x y. 1 < x ** y = 1 < x /\ 0 < y`,
 GEN_TAC THEN INDUCT_TAC THEN 
 RW_TAC bool_ss [EXP,ONE_LT_MULT,LESS_REFL,LESS_0,ZERO_LT_EXP] THEN
 METIS_TAC [SUC_LESS, ONE]);


(*---------------------------------------------------------------------------*)
(* Calculating DIV and MOD by repeated subtraction. We define a              *)
(* tail-recursive function DIVMOD by wellfounded recursion. We hand-roll the *)
(* definition and induction theorem, because, as of now, tfl is not          *)
(* at this point in the build.                                               *)
(*---------------------------------------------------------------------------*)

val findq_lemma = prove(
  ``~(n = 0) /\ ~(m < 2 * n) ==> m - 2 * n < m - n``,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS])  THEN
  SRW_TAC [][SUB_LEFT_LESS, SUB_RIGHT_ADD, SUB_RIGHT_LESS, ADD_CLAUSES,
             SUB_LEFT_ADD]
  THENL [
    MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `n` THEN
    ASM_REWRITE_TAC [] THEN
    CONV_TAC (LAND_CONV (REWR_CONV (GSYM MULT_LEFT_1))) THEN
    REWRITE_TAC [LT_MULT_RCANCEL] THEN
    REWRITE_TAC [TWO,ONE,LESS_MONO_EQ,prim_recTheory.LESS_0] THEN
    PROVE_TAC [NOT_ZERO_LT_ZERO],

    Q.SUBGOAL_THEN `2 * n <= 1 * n` MP_TAC
      THEN1 PROVE_TAC [LESS_EQ_TRANS, MULT_LEFT_1] THEN
    ASM_REWRITE_TAC [LE_MULT_RCANCEL, TWO, ONE, LESS_EQ_MONO,
                     NOT_SUC_LESS_EQ_0],

    Q_TAC SUFF_TAC `n < 2 * n` THEN1
          PROVE_TAC [ADD_COMM, LT_ADD_LCANCEL] THEN
    Q_TAC SUFF_TAC `1 * n < 2 * n` THEN1 SRW_TAC [][MULT_CLAUSES] THEN
    SRW_TAC [][LT_MULT_RCANCEL] THENL [
      PROVE_TAC [NOT_ZERO_LT_ZERO],
      SRW_TAC [][ONE,TWO, LESS_MONO_EQ, prim_recTheory.LESS_0]
    ],

    PROVE_TAC [NOT_LESS_EQUAL]
  ]);

val findq_thm = let
  open pairTheory relationTheory
  val M = ``\f (a,m,n). if n = 0 then a
                        else let d = 2 * n
                             in
                               if m < d then a else f (2 * a, m, d)``
  val measure = ``measure (\ (a:num,m:num,n:num). m - n)``
  val defn = new_definition("findq_def", ``findq = WFREC ^measure ^M``)
  val th0 = MP (MATCH_MP WFREC_COROLLARY defn)
               (ISPEC (rand measure) prim_recTheory.WF_measure)
  val lemma = prove(
    ``~(n = 0) ==> ((let d = 2 * n in if m < d then x
                                      else if m - d < m - n then f d else z) =
                    (let d = 2 * n in if m < d then x else f d))``,
    LET_ELIM_TAC THEN Q.ASM_CASES_TAC `m < d` THEN ASM_REWRITE_TAC [] THEN
    Q.UNABBREV_TAC `d` THEN SRW_TAC [][findq_lemma])
in
  save_thm("findq_thm",
           SIMP_RULE (srw_ss()) [RESTRICT_DEF, prim_recTheory.measure_thm,
                                 lemma]
                     (Q.SPEC `(a,m,n)` th0))
end

val findq_eq_0 = store_thm(
  "findq_eq_0",
  ``!a m n. (findq (a, m, n) = 0) = (a = 0)``,
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC
        `!x a m n. (x = m - n) ==> ((findq (a, m, n) = 0) = (a = 0))` THEN1
        SRW_TAC [][] THEN
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [findq_thm] THEN SRW_TAC [][LET_THM] THEN
  RULE_ASSUM_TAC (SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) []) THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`2 * a`, `m`, `2 * n`] MP_TAC) THEN
  SRW_TAC [][findq_lemma, MULT_EQ_0, TWO, ONE, NOT_SUC]);

val findq_divisor = store_thm(
  "findq_divisor",
  ``n <= m ==> findq (a, m, n) * n <= a * m``,
  Q_TAC SUFF_TAC
        `!x a m n. (x = m - n) /\ n <= m ==>
                   findq (a, m, n) * n <= a * m` THEN1
        SRW_TAC [][] THEN
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN SRW_TAC [boolSimps.DNF_ss][] THEN
  ONCE_REWRITE_TAC [findq_thm] THEN
  SRW_TAC [][LET_THM, MULT_CLAUSES, ZERO_LESS_EQ, LE_MULT_LCANCEL,
             LESS_IMP_LESS_OR_EQ] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`2 * a`, `m`, `2 * n`] MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss())[findq_lemma, GSYM NOT_LESS] THEN
  Q.SUBGOAL_THEN `findq (2 * a,m,2 * n) * (2 * n) =
                  2 * (findq (2 * a, m, 2 * n) * n)` SUBST_ALL_TAC THEN1
    SRW_TAC [][AC MULT_COMM MULT_ASSOC] THEN
  Q.SUBGOAL_THEN `2 * a * m = 2 * (a * m)` SUBST_ALL_TAC THEN1
    SRW_TAC [][AC MULT_COMM MULT_ASSOC] THEN
  SRW_TAC [][LT_MULT_LCANCEL, TWO, ONE, prim_recTheory.LESS_0]);

val divmod_lemma = prove(
  ``~(n = 0) /\ ~(m < n) ==> m - n * findq (1, m, n) < m``,
  SRW_TAC [][NOT_LESS, SUB_RIGHT_LESS, NOT_ZERO_LT_ZERO] THENL [
    ONCE_REWRITE_TAC [ADD_COMM] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
    SRW_TAC [][MULT_EQ_0, ONE, NOT_SUC, findq_eq_0] THEN
    SRW_TAC [][NOT_ZERO_LT_ZERO],
    PROVE_TAC [LESS_LESS_EQ_TRANS]
  ]);

(*---------------------------------------------------------------------------*)
(* DIVMOD (a,m,n) = if n = 0 then (0,0) else                                 *)
(*                  if m < n then (a, m) else                                *)
(*                  let q = findq (1, m, n)                                  *)
(*                  in DIVMOD (a + q, m - n * q, n)                          *)
(*---------------------------------------------------------------------------*)

val DIVMOD_THM = let
  open relationTheory pairTheory
  val M = ``\f (a,m,n). if n = 0 then (0,0)
                        else if m < n then (a, m)
                        else let q = findq (1, m, n)
                             in
                               f (a + q, m - n * q, n)``
  val measure = ``measure ((FST o SND) : num#num#num -> num)``
  val defn = new_definition("DIVMOD_DEF", ``DIVMOD = WFREC ^measure ^M``)
  val th0 = REWRITE_RULE [prim_recTheory.WF_measure]
                         (MATCH_MP WFREC_COROLLARY defn)
  val th1 = SIMP_RULE (srw_ss()) [RESTRICT_DEF, prim_recTheory.measure_thm]
                      (Q.SPEC `(a,m,n)` th0)
  val lemma = prove(
    ``~(n = 0) /\ ~(m < n) ==>
      ((let q = findq (1,m,n) in if m - n * q < m then f q else z) =
       (let q = findq (1,m,n) in f q))``,
    SRW_TAC [][LET_THM, divmod_lemma])
in
  save_thm("DIVMOD_THM", SIMP_RULE (srw_ss()) [lemma] th1)
end

(*---------------------------------------------------------------------------*)
(* Correctness of DIVMOD                                                     *)
(*---------------------------------------------------------------------------*)

val core_divmod_sub_lemma = prove(
  ``0 < n /\ n * q <= m ==>
    (m - n * q = if m < (q + 1) * n then m MOD n
                 else m DIV n * n + m MOD n - q * n)``,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [
    ASM_SIMP_TAC (srw_ss()) [SUB_RIGHT_EQ] THEN DISJ1_TAC THEN
    Q_TAC SUFF_TAC `m DIV n = q` THEN1 PROVE_TAC [DIVISION, MULT_COMM] THEN
    MATCH_MP_TAC DIV_UNIQUE THEN
    Q.EXISTS_TAC `m - n * q` THEN
    SRW_TAC [][SUB_LEFT_ADD] THENL [
      PROVE_TAC [LESS_EQUAL_ANTISYM, MULT_COMM],
      METIS_TAC [ADD_COMM, MULT_COMM, ADD_SUB],
      SRW_TAC [][SUB_RIGHT_LESS] THEN
      FULL_SIMP_TAC (srw_ss()) [RIGHT_ADD_DISTRIB, MULT_CLAUSES,
                                AC MULT_COMM MULT_ASSOC,
                                AC ADD_COMM ADD_ASSOC]
    ],

    ASM_SIMP_TAC (srw_ss()) [GSYM DIVISION] THEN
    SIMP_TAC (srw_ss()) [AC MULT_COMM MULT_ASSOC]
  ]);

val MOD_SUB = store_thm(
  "MOD_SUB",
  ``0 < n /\ n * q <= m ==> ((m - n * q) MOD n = m MOD n)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN
  Q.EXISTS_TAC `m DIV n - q` THEN
  Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THEN1 SRW_TAC [][NOT_ZERO_LT_ZERO] THEN
  ASM_SIMP_TAC (srw_ss()) [RIGHT_SUB_DISTRIB, DIVISION, SUB_RIGHT_ADD,
                           LE_MULT_RCANCEL, DIV_LE_X, core_divmod_sub_lemma]);

val DIV_SUB = store_thm(
  "DIV_SUB",
  ``0 < n /\ n * q <= m ==> ((m - n * q) DIV n = m DIV n - q)``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `m MOD n` THEN
  Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THEN1 SRW_TAC [][NOT_ZERO_LT_ZERO] THEN
  ASM_SIMP_TAC (srw_ss()) [DIVISION, RIGHT_SUB_DISTRIB, SUB_RIGHT_ADD,
                           LE_MULT_RCANCEL, DIV_LE_X, core_divmod_sub_lemma]);

val DIVMOD_CORRECT = Q.store_thm (
  "DIVMOD_CORRECT",
  `!m n a. 0<n ==> (DIVMOD (a,m,n) = (a + (m DIV n), m MOD n))`,
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN
  SRW_TAC [DNF_ss][AND_IMP_INTRO] THEN
  PURE_ONCE_REWRITE_TAC [DIVMOD_THM] THEN
  RW_TAC bool_ss [] THENL [
    METIS_TAC [LESS_REFL],
    METIS_TAC [LESS_REFL],
    METIS_TAC [LESS_DIV_EQ_ZERO,ADD_CLAUSES],
    METIS_TAC [LESS_MOD,ADD_CLAUSES],
    FIRST_X_ASSUM (Q.SPECL_THEN [`m - n * q`, `n`, `a + q`] MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [SUB_RIGHT_LESS] THEN
    Q.SUBGOAL_THEN `m < n * q + m` ASSUME_TAC THENL [
      CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [ADD_COMM])) THEN
      MATCH_MP_TAC LESS_ADD_NONZERO THEN
      SRW_TAC [][MULT_EQ_0, Abbr`q`, findq_eq_0, ONE, NOT_SUC],
      ALL_TAC
    ] THEN ASM_REWRITE_TAC [] THEN
    Q.SUBGOAL_THEN `0 < m` ASSUME_TAC THEN1
      PROVE_TAC [NOT_LESS, LESS_LESS_EQ_TRANS] THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    Q.SUBGOAL_THEN `n * q <= m` ASSUME_TAC THEN1
      METIS_TAC [findq_divisor, NOT_LESS, MULT_LEFT_1, MULT_COMM] THEN
    Q.SUBGOAL_THEN `q <= m DIV n` ASSUME_TAC THEN1
      SRW_TAC [][X_LE_DIV, MULT_COMM] THEN
    SRW_TAC [][] THENL [
      ONCE_REWRITE_TAC [GSYM ADD_ASSOC] THEN
      REWRITE_TAC [EQ_ADD_LCANCEL] THEN
      ASM_SIMP_TAC (srw_ss()) [DIV_SUB] THEN
      SRW_TAC [][SUB_LEFT_ADD] THEN1 METIS_TAC [LESS_EQUAL_ANTISYM] THEN
      METIS_TAC [ADD_SUB, ADD_COMM],
      ASM_SIMP_TAC (srw_ss()) [MOD_SUB]
    ]
  ]);

(*---------------------------------------------------------------------------*)
(* For calculation                                                           *)
(*---------------------------------------------------------------------------*)

val DIVMOD_CALC = Q.store_thm
("DIVMOD_CALC",
 `(!m n. 0<n ==> (m DIV n = FST(DIVMOD(0, m, n)))) /\
  (!m n. 0<n ==> (m MOD n = SND(DIVMOD(0, m, n))))`,
 SRW_TAC [][DIVMOD_CORRECT,ADD_CLAUSES]);


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
 in
   S "val _ = TypeBase.write";
   S "  [TypeBasePure.mk_datatype_info";
   S "     {ax=TypeBasePure.ORIG prim_recTheory.num_Axiom,";
   S "      case_def=num_case_def,";
   S "      case_cong=num_case_cong,";
   S "      induction=TypeBasePure.ORIG numTheory.INDUCTION,";
   S "      nchotomy=num_CASES,";
   S "      size=SOME(Parse.Term`\\x:num. x`, TypeBasePure.ORIG boolTheory.REFL_CLAUSE),";
   S "      encode=NONE,";
   S "      fields=[],";
   S "      accessors=[],";
   S "      updates=[],";
   S "      lift=SOME(mk_var(\"numSyntax.lift_num\",Parse.Type`:'type -> num -> 'term`)),";
   S "      one_one=SOME prim_recTheory.INV_SUC_EQ,";
   S "      distinct=SOME numTheory.NOT_SUC}];"
 end)};


val _ = export_theory();

end;
