(* ===================================================================== *)
(* FILE          : arithmeticScript.sml                                  *)
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

open HolKernel boolLib Parse BasicProvers;

open simpLib boolSimps mesonLib metisLib numTheory prim_recTheory;

local open SatisfySimps DefnBase in end

local
  open OpenTheoryMap
  val ns = ["Number", "Natural"]
in
  fun ot0 x y = OpenTheory_const_name
                   {const = {Thy = "arithmetic", Name = x}, name = (ns, y)}
  fun ot x = ot0 x x
  fun otunwanted x = OpenTheory_const_name
                       {const = {Thy = "arithmetic", Name = x},
                        name = (["Unwanted"], "id")}
end

val _ = new_theory "arithmetic";

val _ = if !Globals.interactive then () else Feedback.emit_WARNING := false;

Theorem num_case_def = num_case_def

val metis_tac = METIS_TAC;
fun bossify stac ths = stac (srw_ss()) ths
val simp = bossify asm_simp_tac
val fs = bossify full_simp_tac
val gvs = bossify (global_simp_tac {droptrues = true, elimvars = true,
                                    oldestfirst = true, strip = true})
val rw = srw_tac[];
val std_ss = bool_ss;
val qabbrev_tac = Q.ABBREV_TAC;

(*---------------------------------------------------------------------------*
 * The basic arithmetic operations.                                          *
 *---------------------------------------------------------------------------*)

val ADD = new_recursive_definition
   {name = "ADD",
    rec_axiom = num_Axiom,
    def = “($+ 0 n = n) /\
            ($+ (SUC m) n = SUC ($+ m n))”};

val _ = set_fixity "+" (Infixl 500);
val _ = ot "+"
val _ = TeX_notation { hol = "+", TeX = ("\\ensuremath{+}", 1) };

(*---------------------------------------------------------------------------*
 * Define NUMERAL, a tag put on numeric literals, and the basic constructors *
 * of the "numeral type".                                                    *
 *---------------------------------------------------------------------------*)

val NUMERAL_DEF = new_definition(
  "NUMERAL_DEF[notuserdef]",
  “NUMERAL (x:num) = x”
);

val ALT_ZERO = new_definition("ALT_ZERO[notuserdef]", “ZERO = 0”);

local
   open OpenTheoryMap
in
   val _ = OpenTheory_const_name {const = {Thy = "arithmetic", Name = "ZERO"},
                                  name = (["Number", "Natural"], "zero")}
   val _ = OpenTheory_const_name {const = {Thy = "num", Name = "0"},
                                  name=(["Number", "Natural"], "zero")}
end

val BIT1 = new_definition("BIT1[notuserdef]", “BIT1 n = n + (n + SUC 0)”);
val BIT2 = new_definition("BIT2[notuserdef]", “BIT2 n = n + (n + SUC (SUC 0))”);

val _ = new_definition(
  GrammarSpecials.nat_elim_term ^ "[notuserdef]",
  ``^(mk_var(GrammarSpecials.nat_elim_term, Type`:num->num`)) n = n``);

val _ = otunwanted "NUMERAL"
val _ = ot0 "BIT1" "bit1"
val _ = ot0 "BIT2" "bit2"

(*---------------------------------------------------------------------------*
 * After this call, numerals parse into `NUMERAL( ... )`                     *
 *---------------------------------------------------------------------------*)

val _ = add_numeral_form (#"n", NONE);

val _ = set_fixity "-" (Infixl 500);
val _ = Unicode.unicode_version {u = UTF8.chr 0x2212, tmnm = "-"};
val _ = TeX_notation {hol = "-", TeX = ("\\ensuremath{-}", 1)}
val _ = TeX_notation {hol = UTF8.chr 0x2212, TeX = ("\\ensuremath{-}", 1)}

val SUB = new_recursive_definition
   {name = "SUB",
    rec_axiom = num_Axiom,
    def = “(0 - m = 0) /\
            (SUC m - n = if m < n then 0 else SUC(m - n))”};

val _ = ot "-"

(* Also add concrete syntax for unary negation so that future numeric types
   can use it.  We can't do anything useful with it for the natural numbers
   of course, but it seems like this is the best ancestral place for it.

   Descendents wanting to use this will include at least
     integer, real, words, rat
*)
val _ = add_rule { term_name = "numeric_negate",
                   fixity = Prefix 900,
                   pp_elements = [TOK "-"],
                   paren_style = OnlyIfNecessary,
                   block_style = (AroundEachPhrase, (PP.CONSISTENT,0))};

(* Similarly, add syntax for the injection from nats symbol (&).  This isn't
   required in this theory, but will be used by descendents. *)
val _ = add_rule {term_name = GrammarSpecials.num_injection,
                  fixity = Prefix 900,
                  pp_elements = [TOK GrammarSpecials.num_injection],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,0))};
(* overload it to the nat_elim term *)
val _ = overload_on (GrammarSpecials.num_injection,
                     mk_const(GrammarSpecials.nat_elim_term, “:num -> num”))

val _ = set_fixity "*" (Infixl 600);
val _ = TeX_notation {hol = "*", TeX = ("\\HOLTokenProd{}", 1)}

val MULT = new_recursive_definition
   {name = "MULT",
    rec_axiom = num_Axiom,
    def = “(0 * n = 0) /\
             (SUC m * n = (m * n) + n)”};

val _ = ot "*"

val EXP = new_recursive_definition
   {name = "EXP",
    rec_axiom = num_Axiom,
    def = “($EXP m 0 = 1) /\
             ($EXP m (SUC n) = m * ($EXP m n))”};

val _ = ot0 "EXP" "^"
val _ = set_fixity "EXP" (Infixr 700);
val _ = add_infix("**", 700, HOLgrammars.RIGHT);
val _ = overload_on ("**", Term`$EXP`);
val _ = TeX_notation {hol = "**", TeX = ("\\HOLTokenExp{}", 2)}

Theorem EXP0[simp] = cj 1 EXP

(* special-case squares and cubes *)
val _ = add_rule {fixity = Suffix 2100,
                  term_name = UnicodeChars.sup_2,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK UnicodeChars.sup_2]};

val _ = overload_on (UnicodeChars.sup_2, “\x. x ** 2”);
val _ = TeX_notation {hol = UnicodeChars.sup_2, TeX = ("\\HOLTokenSupTwo{}", 1)};

val _ = add_rule {fixity = Suffix 2100,
                  term_name = UnicodeChars.sup_3,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK UnicodeChars.sup_3]};

val _ = overload_on (UnicodeChars.sup_3, “\x. x ** 3”);
val _ = TeX_notation {hol = UnicodeChars.sup_3, TeX = ("\\HOLTokenSupThree{}", 1)};

val GREATER_DEF = new_definition("GREATER_DEF", “$> m n <=> n < m”)
val _ = set_fixity ">" (Infix(NONASSOC, 450))
val _ = TeX_notation {hol = ">", TeX = ("\\HOLTokenGt{}", 1)}
val _ = ot ">"

val LESS_OR_EQ = new_definition ("LESS_OR_EQ", “$<= m n <=> m < n \/ (m = n)”)
val _ = set_fixity "<=" (Infix(NONASSOC, 450))
val _ = Unicode.unicode_version { u = Unicode.UChar.leq, tmnm = "<="}
val _ = TeX_notation {hol = Unicode.UChar.leq, TeX = ("\\HOLTokenLeq{}", 1)}
val _ = TeX_notation {hol = "<=", TeX = ("\\HOLTokenLeq{}", 1)}
val _ = ot "<="

val GREATER_OR_EQ =
    new_definition("GREATER_OR_EQ", “$>= m n <=> m > n \/ (m = n)”)
val _ = set_fixity ">=" (Infix(NONASSOC, 450))
val _ = Unicode.unicode_version { u = Unicode.UChar.geq, tmnm = ">="};
val _ = TeX_notation {hol = ">=", TeX = ("\\HOLTokenGeq{}", 1)}
val _ = TeX_notation {hol = Unicode.UChar.geq, TeX = ("\\HOLTokenGeq{}", 1)}
val _ = ot ">="

val EVEN = new_recursive_definition
   {name = "EVEN",
    rec_axiom = num_Axiom,
    def = “(EVEN 0 = T) /\
             (EVEN (SUC n) = ~EVEN n)”};
val _ = ot0 "EVEN" "even"

val ODD = new_recursive_definition
   {name = "ODD",
    rec_axiom = num_Axiom,
    def = “(ODD 0 = F) /\
             (ODD (SUC n) = ~ODD n)”};
val _ = ot0 "ODD" "odd"

val FUNPOW = new_recursive_definition
   {name = "FUNPOW",
    rec_axiom = num_Axiom,
    def = “(FUNPOW f 0 x = x) /\
             (FUNPOW f (SUC n) x = FUNPOW f n (f x))”};

val NRC = new_recursive_definition {
  name = "NRC",
  rec_axiom = num_Axiom,
  def = “(NRC R 0 x y = (x = y)) /\
          (NRC R (SUC n) x y = ?z. R x z /\ NRC R n z y)”};

val _ = overload_on ("RELPOW", “NRC”)
val _ = overload_on ("NRC", “NRC”)

(*---------------------------------------------------------------------------
                        THEOREMS
 ---------------------------------------------------------------------------*)

val ONE = store_thm ("ONE", “1 = SUC 0”,
  REWRITE_TAC [NUMERAL_DEF, BIT1, ALT_ZERO, ADD]);

val TWO = store_thm ("TWO", “2 = SUC 1”,
  REWRITE_TAC [NUMERAL_DEF, BIT2, ONE, ADD, ALT_ZERO,BIT1]);

val NORM_0 = store_thm ("NORM_0", “NUMERAL ZERO = 0”,
  REWRITE_TAC [NUMERAL_DEF, ALT_ZERO]);

fun INDUCT_TAC g = INDUCT_THEN INDUCTION ASSUME_TAC g;

val EQ_SYM_EQ' = INST_TYPE [alpha |-> Type`:num`] EQ_SYM_EQ;

(*---------------------------------------------------------------------------*)
(* Definition of num_case more suitable to call-by-value computations        *)
(*---------------------------------------------------------------------------*)

val num_case_compute = store_thm ("num_case_compute",
  “!n. num_CASE n (f:'a) g = if n=0 then f else g (PRE n)”,
  INDUCT_TAC THEN REWRITE_TAC [num_case_def,NOT_SUC,PRE]);


(* --------------------------------------------------------------------- *)
(* SUC_NOT = |- !n. ~(0 = SUC n)                                         *)
(* --------------------------------------------------------------------- *)

val SUC_NOT = save_thm ("SUC_NOT",
    GEN (“n:num”) (NOT_EQ_SYM (SPEC (“n:num”) NOT_SUC)));

(* Theorem: 0 < SUC n *)
(* Proof: by arithmetic. *)
val SUC_POS = save_thm("SUC_POS", LESS_0);

(* Theorem: 0 < SUC n *)
(* Proof: by arithmetic. *)
val SUC_NOT_ZERO = save_thm("SUC_NOT_ZERO", NOT_SUC);

val ADD_0 = store_thm ("ADD_0",
   “!m. m + 0 = m”,
   INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);

val ADD_SUC = store_thm ("ADD_SUC",
   “!m n. SUC(m + n) = (m + SUC n)”,
   INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);

val ADD_CLAUSES = store_thm ("ADD_CLAUSES",
   “(0 + m = m)              /\
     (m + 0 = m)              /\
     (SUC m + n = SUC(m + n)) /\
     (m + SUC n = SUC(m + n))”,
   REWRITE_TAC[ADD, ADD_0, ADD_SUC]);

val ADD_SYM = store_thm ("ADD_SYM",
  “!m n. m + n = n + m”,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_0, ADD, ADD_SUC]);

val ADD_COMM = save_thm ("ADD_COMM", ADD_SYM);

val ADD_ASSOC = store_thm ("ADD_ASSOC",
   “!m n p. m + (n + p) = (m + n) + p”,
   INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);

val num_CASES = store_thm ("num_CASES",
   “!m. (m = 0) \/ ?n. m = SUC n”,
   INDUCT_TAC
   THEN REWRITE_TAC[NOT_SUC]
   THEN EXISTS_TAC (“(m:num)”)
   THEN REWRITE_TAC[]);

Theorem NOT_ZERO_LT_ZERO:
   !n. n <> 0 <=> 0 < n
Proof
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `n` num_CASES) THEN
  REWRITE_TAC [NOT_LESS_0, LESS_0, NOT_SUC]
QED

Theorem NOT_ZERO = NOT_ZERO_LT_ZERO

Theorem NOT_LT_ZERO_EQ_ZERO[simp]:
   !n. ~(0 < n) <=> (n = 0)
Proof REWRITE_TAC [GSYM NOT_ZERO_LT_ZERO]
QED

val LESS_OR_EQ_ALT = store_thm ("LESS_OR_EQ_ALT",
  “$<= = RTC (\x y. y = SUC x)”,
  REWRITE_TAC [FUN_EQ_THM, LESS_OR_EQ, relationTheory.RTC_CASES_TC, LESS_ALT]
    THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
    THEN ASM_REWRITE_TAC []) ;

Theorem LT_SUC:
  n < SUC m <=> n = 0 \/ ?n0. n = SUC n0 /\ n0 < m
Proof
  eq_tac >> Q.SPEC_THEN ‘n’ STRUCT_CASES_TAC num_CASES >>
  rewrite_tac [LESS_0, prim_recTheory.LESS_MONO_EQ, NOT_SUC, INV_SUC_EQ]
  >- (disch_then (irule_at (Pos last)) >> rewrite_tac[]) >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem SUC_LT:
  SUC n < m <=> ?m0. m = SUC m0 /\ n < m0
Proof
  eq_tac
  >- (Q.SPEC_THEN ‘m’ STRUCT_CASES_TAC num_CASES >>
      rewrite_tac[NOT_LESS_0, prim_recTheory.LESS_MONO_EQ] >>
      disch_then (irule_at (Pos last)) >> rewrite_tac[]) >>
  strip_tac >> asm_rewrite_tac [prim_recTheory.LESS_MONO_EQ]
QED

(* --------------------------------------------------------------------- *)
(* LESS_ADD proof rewritten: TFM 90.O9.21                               *)
(* --------------------------------------------------------------------- *)

val LESS_ADD = store_thm ("LESS_ADD",
   “!m n. n<m ==> ?p. p+n = m”,
   INDUCT_TAC THEN GEN_TAC THEN
   REWRITE_TAC[NOT_LESS_0,LESS_THM] THEN
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC (“SUC 0”) THEN ASM_REWRITE_TAC[ADD],
    RES_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
    EXISTS_TAC (“SUC p”) THEN REWRITE_TAC [ADD]]);

val transitive_LESS = store_thm(
  "transitive_LESS[simp]",
  “transitive $<”,
  REWRITE_TAC [relationTheory.TC_TRANSITIVE, LESS_ALT]);

val LESS_TRANS = store_thm ("LESS_TRANS",
   “!m n p. (m < n) /\ (n < p) ==> (m < p)”,
  MATCH_ACCEPT_TAC
    (REWRITE_RULE [relationTheory.transitive_def] transitive_LESS)) ;

val LESS_ANTISYM = store_thm ("LESS_ANTISYM",
   “!m n. ~((m < n) /\ (n < m))”,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN IMP_RES_TAC LESS_REFL);

(*---------------------------------------------------------------------------
 *  |- !m n. SUC m < SUC n = m < n
 *---------------------------------------------------------------------------*)

val LESS_MONO_REV = save_thm ("LESS_MONO_REV", prim_recTheory.LESS_MONO_REV) ;
val LESS_MONO_EQ = save_thm ("LESS_MONO_EQ", prim_recTheory.LESS_MONO_EQ) ;

val LESS_EQ_MONO = store_thm ("LESS_EQ_MONO",
     “!n m. (SUC n <= SUC m) = (n <= m)”,
     REWRITE_TAC [LESS_OR_EQ,LESS_MONO_EQ,INV_SUC_EQ]);

val LESS_LESS_SUC = store_thm ("LESS_LESS_SUC",
   “!m n. ~((m < n) /\ (n < SUC m))”,
   INDUCT_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC[LESS_MONO_EQ, LESS_EQ_MONO, LESS_0, NOT_LESS_0]) ;

val transitive_measure = Q.store_thm ("transitive_measure",
   `!f. transitive (measure f)`,
   SRW_TAC [][relationTheory.transitive_def,prim_recTheory.measure_thm]
    THEN MATCH_MP_TAC LESS_TRANS
    THEN SRW_TAC [SatisfySimps.SATISFY_ss][]);

val LESS_EQ = store_thm ("LESS_EQ",
  “!m n. (m < n) = (SUC m <= n)”,
  REWRITE_TAC[LESS_OR_EQ_ALT, LESS_ALT, RTC_IM_TC]) ;

val LESS_OR = store_thm ("LESS_OR",
   “!m n. m < n ==> SUC m <= n”,
   REWRITE_TAC[LESS_EQ]) ;

val OR_LESS = store_thm ("OR_LESS",
   “!m n. (SUC m <= n) ==> (m < n)”,
   REWRITE_TAC[LESS_EQ]) ;

val LESS_EQ_IFF_LESS_SUC = store_thm ("LESS_EQ_IFF_LESS_SUC",
 “!n m. (n <= m) = (n < (SUC m))”,
  REWRITE_TAC[LESS_OR_EQ_ALT, LESS_ALT, TC_IM_RTC_SUC]) ;

val LESS_EQ_IMP_LESS_SUC = store_thm ("LESS_EQ_IMP_LESS_SUC",
 “!n m. (n <= m) ==> (n < (SUC m))”,
   REWRITE_TAC [LESS_EQ_IFF_LESS_SUC]) ;

val ZERO_LESS_EQ = store_thm ("ZERO_LESS_EQ",
   “!n. 0 <= n”,
   REWRITE_TAC [LESS_0,LESS_EQ_IFF_LESS_SUC]);

Theorem LE_0 = ZERO_LESS_EQ (* HOL-Light compatible name *)

val LESS_SUC_EQ_COR = store_thm ("LESS_SUC_EQ_COR",
   “!m n. ((m < n) /\ (~(SUC m = n))) ==> (SUC m < n)”,
   CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
   INDUCT_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [LESS_MONO_EQ, INV_SUC_EQ, LESS_0, NOT_LESS_0,
       NOT_ZERO_LT_ZERO]) ;

val LESS_NOT_SUC = store_thm ("LESS_NOT_SUC",
   “!m n. (m < n) /\ ~(n = SUC m) ==> SUC m < n”,
   INDUCT_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [LESS_MONO_EQ, INV_SUC_EQ, LESS_0, NOT_LESS_0,
       NOT_ZERO_LT_ZERO]) ;

val LESS_0_CASES = store_thm ("LESS_0_CASES",
   “!m. (0 = m) \/ 0<m”,
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_0]);

val LESS_CASES_IMP = store_thm ("LESS_CASES_IMP",
   “!m n. ~(m < n) /\  ~(m = n) ==> (n < m)”,
   INDUCT_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [LESS_MONO_EQ, INV_SUC_EQ, LESS_0, NOT_LESS_0]) ;

val LESS_CASES = store_thm ("LESS_CASES",
   “!m n. (m < n) \/ (n <= m)”,
   INDUCT_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC
       [LESS_MONO_EQ, LESS_EQ_MONO, ZERO_LESS_EQ, LESS_0, NOT_LESS_0]) ;

val ADD_INV_0 = store_thm ("ADD_INV_0",
   “!m n. (m + n = m) ==> (n = 0)”,
   INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES, INV_SUC_EQ]);

val LESS_EQ_ADD = store_thm ("LESS_EQ_ADD",
   “!m n. m <= m + n”,
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
    THEN MP_TAC(ASSUME (“(m < (m + n)) \/ (m = (m + n))”))
    THEN STRIP_TAC
    THENL
    [IMP_RES_TAC LESS_SUC
      THEN ASM_REWRITE_TAC[],
     REWRITE_TAC[SYM(ASSUME (“m = m + n”)),LESS_SUC_REFL]]);

val LESS_EQ_ADD_EXISTS = store_thm ("LESS_EQ_ADD_EXISTS",
   “!m n. n<=m ==> ?p. p+n = m”,
   SIMP_TAC bool_ss [LESS_OR_EQ, DISJ_IMP_THM, FORALL_AND_THM, LESS_ADD]
   THEN GEN_TAC
   THEN EXISTS_TAC (“0”)
   THEN REWRITE_TAC[ADD]);

val LESS_STRONG_ADD = store_thm ("LESS_STRONG_ADD",
   “!m n. n < m ==> ?p. (SUC p)+n = m”,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC LESS_OR
   THEN IMP_RES_TAC LESS_EQ_ADD_EXISTS
   THEN EXISTS_TAC (“p:num”)
   THEN FULL_SIMP_TAC bool_ss [ADD_CLAUSES]);

val LESS_EQ_SUC_REFL = store_thm ("LESS_EQ_SUC_REFL",
   “!m. m <= SUC m”,
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ,LESS_SUC_REFL]);

val LESS_ADD_NONZERO = store_thm ("LESS_ADD_NONZERO",
   “!m n. ~(n = 0) ==> m < m + n”,
   GEN_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC,ADD_CLAUSES]
    THEN ASM_CASES_TAC (“n = 0”)
    THEN ASSUME_TAC(SPEC (“m + n”) LESS_SUC_REFL)
    THEN RES_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_SUC_REFL]);

val NOT_SUC_LESS_EQ_0 = store_thm ("NOT_SUC_LESS_EQ_0",
   “!n. ~(SUC n <= 0)”,
   REWRITE_TAC [NOT_LESS_0, GSYM LESS_EQ]);

val NOT_LESS = store_thm ("NOT_LESS",
   “!m n. ~(m < n) = (n <= m)”,
   INDUCT_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [LESS_MONO_EQ, LESS_EQ_MONO,
       ZERO_LESS_EQ, LESS_0, NOT_LESS_0, NOT_SUC_LESS_EQ_0]) ;

Theorem NOT_LESS_EQUAL:
  !m n. ~(m <= n) <=> n < m
Proof REWRITE_TAC[GSYM NOT_LESS]
QED

val LESS_EQ_ANTISYM = store_thm ("LESS_EQ_ANTISYM",
   “!m n. ~(m < n /\ n <= m)”,
   INDUCT_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [LESS_MONO_EQ, LESS_EQ_MONO,
       ZERO_LESS_EQ, LESS_0, NOT_LESS_0, NOT_SUC_LESS_EQ_0]) ;

Theorem LTE_ANTISYM = LESS_EQ_ANTISYM (* HOL-Light compatible name *)
Theorem LET_ANTISYM :
    !m n. ~(m <= n /\ n < m)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [CONJ_COMM]
 >> REWRITE_TAC [LESS_EQ_ANTISYM]
QED

val LESS_EQ_0 = store_thm ("LESS_EQ_0",
  “!n. (n <= 0) = (n = 0)”,
  REWRITE_TAC [LESS_OR_EQ, NOT_LESS_0]) ;

(*---------------------------------------------------------------------------
 *  HOL Light (or HOL88) compatibility
 *---------------------------------------------------------------------------*)

Theorem LT :
    (!m:num. m < 0 <=> F) /\ (!m n. m < SUC n <=> (m = n) \/ m < n)
Proof
    METIS_TAC [LESS_THM, NOT_LESS_0]
QED

Theorem LT_LE :
    !m n:num. m < n <=> m <= n /\ ~(m = n)
Proof
    METIS_TAC [LESS_NOT_EQ, LESS_OR_EQ]
QED

(* |- !m n. m <= n <=> m < n \/ (m = n) *)
Theorem LE_LT = LESS_OR_EQ;

(* moved here from cardinalTheory (proof is from old transc.ml *)
Theorem LT_SUC_LE : (* was: LESS_SUC_EQ *)
    !m n. m < SUC n <=> m <= n
Proof
    rpt GEN_TAC >> REWRITE_TAC[CONJUNCT2 LT, LE_LT]
 >> EQ_TAC >> DISCH_THEN(DISJ_CASES_THEN(fn th => REWRITE_TAC[th]))
QED

Theorem LE_CASES :
   !m n:num. m <= n \/ n <= m
Proof
  rpt INDUCT_TAC >> ASM_REWRITE_TAC[ZERO_LESS_EQ, LESS_EQ_MONO]
QED

Theorem LT_CASES :
   !m n:num. (m < n) \/ (n < m) \/ (m = n)
Proof
  METIS_TAC [LESS_CASES, LESS_OR_EQ]
QED

(* moved here from real_topologyTheory *)
Theorem WLOG_LT :
   (!m:num. P m m) /\ (!m n. P m n <=> P n m) /\ (!m n. m < n ==> P m n)
   ==> !m y. P m y
Proof
  METIS_TAC [LT_CASES]
QED

(* moved here from iterateTheory *)
Theorem WLOG_LE :
   (!m n:num. P m n <=> P n m) /\ (!m n:num. m <= n ==> P m n) ==>
    !m n:num. P m n
Proof
  METIS_TAC [LE_CASES]
QED

(*---------------------------------------------------------------------------*)

val _ = print "Now proving properties of subtraction\n"

val SUB_0 = store_thm ("SUB_0",
   “!m. (0 - m = 0) /\ (m - 0 = m)”,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[SUB, NOT_LESS_0]);

(* Non-confluence problem between SUB (snd clause) and LESS_MONO_EQ     *)
(*   requires a change from hol2 proof. kls.                            *)

val SUB_MONO_EQ = store_thm ("SUB_MONO_EQ",
   “!n m. (SUC n) - (SUC m) = (n - m)”,
   INDUCT_TAC THENL
   [REWRITE_TAC [SUB,LESS_0],
    ONCE_REWRITE_TAC[SUB] THEN
    PURE_ONCE_REWRITE_TAC[LESS_MONO_EQ] THEN
    ASM_REWRITE_TAC[]]);

(* A better case rewrite for numeral arguments *)
Theorem num_case_NUMERAL_compute[simp]:
  num_CASE (NUMERAL (BIT1 n)) (z:'a) s = s (NUMERAL(BIT1 n) - 1) /\
  num_CASE (NUMERAL (BIT2 n)) z s = s (NUMERAL(BIT1 n))
Proof
  REWRITE_TAC [num_case_compute, NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES,
               NOT_SUC, PRE, ALT_ZERO, SUB_MONO_EQ, SUB_0]
QED

val SUB_EQ_0 = store_thm ("SUB_EQ_0",
  “!m n. (m - n = 0) = (m <= n)”,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [SUB_0, LESS_EQ_MONO, SUB_MONO_EQ, LESS_EQ_0, ZERO_LESS_EQ]);

val ADD1 = store_thm ("ADD1",
   “!m. SUC m = m + 1”,
   INDUCT_TAC THENL [
     REWRITE_TAC [ADD_CLAUSES, ONE],
     ASM_REWRITE_TAC [] THEN REWRITE_TAC [ONE, ADD_CLAUSES]
   ]);

val SUC_SUB1 = store_thm ("SUC_SUB1",
   “!m. SUC m - 1 = m”,
   INDUCT_TAC THENL [
     REWRITE_TAC [SUB, LESS_0, ONE],
     PURE_ONCE_REWRITE_TAC[SUB] THEN
     ASM_REWRITE_TAC[NOT_LESS_0, LESS_MONO_EQ, ONE]
   ]);

val PRE_SUB1 = store_thm ("PRE_SUB1",
   “!m. (PRE m = (m - 1))”,
   GEN_TAC
    THEN STRUCT_CASES_TAC(SPEC (“m:num”) num_CASES)
    THEN ASM_REWRITE_TAC[PRE, CONJUNCT1 SUB, SUC_SUB1]);

val MULT_0 = store_thm ("MULT_0",
   “!m. m * 0 = 0”,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT,ADD_CLAUSES]);

val MULT_SUC = store_thm ("MULT_SUC",
   “!m n. m * (SUC n) = m + m*n”,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT,ADD_CLAUSES,ADD_ASSOC]);

val MULT_LEFT_1 = store_thm ("MULT_LEFT_1",
   “!m. 1 * m = m”,
   GEN_TAC THEN REWRITE_TAC[ONE, MULT,ADD_CLAUSES]);

val MULT_RIGHT_1 = store_thm ("MULT_RIGHT_1",
   “!m. m * 1 = m”,
   REWRITE_TAC [ONE] THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC[MULT, ADD_CLAUSES]);

val MULT_CLAUSES = store_thm ("MULT_CLAUSES",
   “!m n. (0 * m = 0)             /\
           (m * 0 = 0)             /\
           (1 * m = m)             /\
           (m * 1 = m)             /\
           (SUC m * n = m * n + n) /\
           (m * SUC n = m + m * n)”,
    REWRITE_TAC[MULT,MULT_0,MULT_LEFT_1,MULT_RIGHT_1,MULT_SUC]);

val MULT_SYM = store_thm ("MULT_SYM",
  “!m n. m * n = n * m”,
  INDUCT_TAC
   THEN GEN_TAC
   THEN ASM_REWRITE_TAC[MULT_CLAUSES,SPECL[“m*n”,“n:num”]ADD_SYM]);

val MULT_COMM = save_thm ("MULT_COMM", MULT_SYM);

val RIGHT_ADD_DISTRIB = store_thm ("RIGHT_ADD_DISTRIB",
   “!m n p. (m + n) * p = (m * p) + (n * p)”,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,ADD_ASSOC]
    THEN REWRITE_TAC[SPECL[“m+(m*p)”,“n:num”]ADD_SYM,ADD_ASSOC]
    THEN SUBST_TAC[SPEC_ALL ADD_SYM]
    THEN REWRITE_TAC[]);

(* A better proof of LEFT_ADD_DISTRIB would be using
   MULT_SYM and RIGHT_ADD_DISTRIB *)
val LEFT_ADD_DISTRIB = store_thm ("LEFT_ADD_DISTRIB",
   “!m n p. p * (m + n) = (p * m) + (p * n)”,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
    THEN REWRITE_TAC[SPECL[“m:num”,“(p*n)+n”]ADD_SYM,
                     SYM(SPEC_ALL ADD_ASSOC)]
    THEN SUBST_TAC[SPEC_ALL ADD_SYM]
    THEN REWRITE_TAC[]);

val MULT_ASSOC = store_thm ("MULT_ASSOC",
   “!m n p. m * (n * p) = (m * n) * p”,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[MULT_CLAUSES,RIGHT_ADD_DISTRIB]);

val SUB_ADD = store_thm ("SUB_ADD",
   “!m n. (n <= m) ==> ((m - n) + n = m)”,
   REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC[ADD_CLAUSES, SUB_0, SUB_MONO_EQ, LESS_EQ_MONO,
      INV_SUC_EQ, LESS_EQ_0]) ;

val PRE_SUB = store_thm ("PRE_SUB",
   “!m n. PRE(m - n) = (PRE m) - n”,
   INDUCT_TAC
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[SUB,PRE]
    THEN ASM_CASES_TAC (“m < n”)
    THEN ASM_REWRITE_TAC
          [PRE,LESS_OR_EQ,
           SUBS[SPECL[“m-n”,“0”]EQ_SYM_EQ']
               (SPECL [“m:num”,“n:num”] SUB_EQ_0)])

val ADD_EQ_0 = store_thm ("ADD_EQ_0",
   “!m n. (m + n = 0) <=> (m = 0) /\ (n = 0)”,
   INDUCT_TAC
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,NOT_SUC]);

val ADD_EQ_1 = store_thm ("ADD_EQ_1",
  “!m n. (m + n = 1) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)”,
  INDUCT_TAC THENL [
     REWRITE_TAC [ADD_CLAUSES, ONE, GSYM NOT_SUC],
     REWRITE_TAC [NOT_SUC, ADD_CLAUSES, ONE, INV_SUC_EQ, ADD_EQ_0]
  ]);

val ADD_INV_0_EQ = store_thm ("ADD_INV_0_EQ",
   “!m n. (m + n = m) = (n = 0)”,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[ADD_INV_0]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]);

val PRE_SUC_EQ = store_thm ("PRE_SUC_EQ",
   “!m n. 0<n ==> ((m = PRE n) = (SUC m = n))”,
   INDUCT_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[PRE,LESS_REFL,INV_SUC_EQ]);

val INV_PRE_EQ = store_thm ("INV_PRE_EQ",
   “!m n. 0<m /\ 0<n ==> ((PRE m = (PRE n)) = (m = n))”,
   INDUCT_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[PRE,LESS_REFL,INV_SUC_EQ]);

val LESS_SUC_NOT = store_thm ("LESS_SUC_NOT",
   “!m n. (m < n)  ==> ~(n < SUC m)”,
   REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_OR
    THEN ASM_REWRITE_TAC[]);

val ADD_EQ_SUB = store_thm ("ADD_EQ_SUB",
   “!m n p. (n <= p) ==> (((m + n) = p) = (m = (p - n)))”,
   GEN_TAC THEN REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES,SUB_MONO_EQ,INV_SUC_EQ,LESS_EQ_MONO,
     SUB_0, NOT_SUC_LESS_EQ_0]) ;

val LESS_MONO_ADD = store_thm ("LESS_MONO_ADD",
   “!m n p. (m < n) ==> (m + p) < (n + p)”,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_MONO_EQ]);

val LESS_MONO_ADD_INV = store_thm ("LESS_MONO_ADD_INV",
   “!m n p. (m + p) < (n + p) ==> (m < n)”,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_MONO_EQ]);

val LESS_MONO_ADD_EQ = store_thm ("LESS_MONO_ADD_EQ",
   “!m n p. ((m + p) < (n + p)) = (m < n)”,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[LESS_MONO_ADD,LESS_MONO_ADD_INV]);

val LT_ADD_RCANCEL = save_thm ("LT_ADD_RCANCEL", LESS_MONO_ADD_EQ)
val LT_ADD_LCANCEL = save_thm ("LT_ADD_LCANCEL",
                               ONCE_REWRITE_RULE [ADD_COMM] LT_ADD_RCANCEL)

val EQ_MONO_ADD_EQ = store_thm ("EQ_MONO_ADD_EQ",
   “!m n p. ((m + p) = (n + p)) = (m = n)”,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[ADD_CLAUSES,INV_SUC_EQ]);

val _ = print "Proving properties of <=\n"

val LESS_EQ_MONO_ADD_EQ = store_thm ("LESS_EQ_MONO_ADD_EQ",
   “!m n p. ((m + p) <= (n + p)) = (m <= n)”,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[LESS_MONO_ADD_EQ,EQ_MONO_ADD_EQ]);

val LESS_EQ_TRANS = store_thm ("LESS_EQ_TRANS",
   “!m n p. (m <= n) /\ (n <= p) ==> (m <= p)”,
   REWRITE_TAC[LESS_OR_EQ_ALT, REWRITE_RULE
     [relationTheory.transitive_def] relationTheory.transitive_RTC]) ;

Theorem transitive_LE[simp]:
  transitive $<=
Proof
  REWRITE_TAC[relationTheory.transitive_def] >>
  MATCH_ACCEPT_TAC LESS_EQ_TRANS
QED

val LESS_EQ_LESS_TRANS = store_thm ("LESS_EQ_LESS_TRANS",
  “!m n p. m <= n /\ n < p ==> m < p”,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  ASM_CASES_TAC (“m:num = n”) THEN ASM_REWRITE_TAC[LESS_TRANS]);

val LESS_LESS_EQ_TRANS = store_thm ("LESS_LESS_EQ_TRANS",
  “!m n p. m < n /\ n <= p ==> m < p”,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  ASM_CASES_TAC (“n:num = p”) THEN ASM_REWRITE_TAC[LESS_TRANS]);

Theorem LE_TRANS  = LESS_EQ_TRANS      (* HOL-Light compatible name *)
Theorem LET_TRANS = LESS_EQ_LESS_TRANS (* HOL-Light compatible name *)
Theorem LTE_TRANS = LESS_LESS_EQ_TRANS (* HOL-Light compatible name *)

(* % Proof modified for new IMP_RES_TAC                 [TFM 90.04.25]  *)

val LESS_EQ_LESS_EQ_MONO = store_thm ("LESS_EQ_LESS_EQ_MONO",
   “!m n p q. (m <= p) /\ (n <= q) ==> ((m + n) <= (p + q))”,
   REPEAT STRIP_TAC THEN
   let val th1 = snd(EQ_IMP_RULE (SPEC_ALL  LESS_EQ_MONO_ADD_EQ))
       val th2 = PURE_ONCE_REWRITE_RULE [ADD_SYM] th1
   in
   IMP_RES_THEN (ASSUME_TAC o SPEC (“n:num”)) th1 THEN
   IMP_RES_THEN (ASSUME_TAC o SPEC (“p:num”)) th2 THEN
   IMP_RES_TAC LESS_EQ_TRANS
   end);

val LESS_EQ_REFL = store_thm ("LESS_EQ_REFL",
   “!m. m <= m”,
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]);

Theorem LE_REFL = LESS_EQ_REFL (* HOL-Light compatible name *)

val LESS_IMP_LESS_OR_EQ = store_thm ("LESS_IMP_LESS_OR_EQ",
   “!m n. (m < n) ==> (m <= n)”,
   REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[LESS_OR_EQ]);

val LESS_MONO_MULT = store_thm ("LESS_MONO_MULT",
   “!m n p. (m <= n) ==> ((m * p) <= (n * p))”,
   GEN_TAC
    THEN GEN_TAC
    THEN INDUCT_TAC
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC
          [ADD_CLAUSES,MULT_CLAUSES,LESS_EQ_MONO_ADD_EQ,LESS_EQ_REFL]
    THEN RES_TAC
    THEN IMP_RES_TAC(SPECL[“m:num”,“m*p”,“n:num”,“n*p”]
                          LESS_EQ_LESS_EQ_MONO)
    THEN ASM_REWRITE_TAC[]);

val LESS_MONO_MULT2 = store_thm ("LESS_MONO_MULT2",
  “!m n i j. m <= i /\ n <= j ==> m * n <= i * j”,
  mesonLib.MESON_TAC [LESS_EQ_TRANS, LESS_MONO_MULT, MULT_COMM]);

(* Proof modified for new IMP_RES_TAC                   [TFM 90.04.25]  *)

val RIGHT_SUB_DISTRIB = store_thm ("RIGHT_SUB_DISTRIB",
   “!m n p. (m - n) * p = (m * p) - (n * p)”,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (“n <= m”) THENL
   [let val imp = SPECL [“(m-n)*p”,
                         “n*p”,
                         “m*p”] ADD_EQ_SUB
    in
    IMP_RES_THEN (SUBST1_TAC o SYM o MP imp o SPEC (“p:num”))
                 LESS_MONO_MULT THEN
    REWRITE_TAC[SYM(SPEC_ALL RIGHT_ADD_DISTRIB)] THEN
    IMP_RES_THEN SUBST1_TAC SUB_ADD THEN REFL_TAC
    end,
    IMP_RES_TAC (REWRITE_RULE[](AP_TERM (“$~”)
                                        (SPEC_ALL NOT_LESS))) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN (ASSUME_TAC o SPEC (“p:num”)) LESS_MONO_MULT THEN
    IMP_RES_TAC SUB_EQ_0 THEN
    ASM_REWRITE_TAC[MULT_CLAUSES]]);

val LEFT_SUB_DISTRIB = store_thm ("LEFT_SUB_DISTRIB",
   “!m n p. p * (m - n) = (p * m) - (p * n)”,
   PURE_ONCE_REWRITE_TAC [MULT_SYM] THEN
   REWRITE_TAC [RIGHT_SUB_DISTRIB]);

(* The following theorem (and proof) are from tfm [rewritten TFM 90.09.21] *)
val LESS_ADD_1 = store_thm ("LESS_ADD_1",
  “!m n. (n<m) ==> ?p. m = n + (p + 1)”,
  REWRITE_TAC [ONE] THEN INDUCT_TAC THEN
  REWRITE_TAC[NOT_LESS_0,LESS_THM] THEN
  REPEAT STRIP_TAC THENL [
   EXISTS_TAC (“0”) THEN ASM_REWRITE_TAC [ADD_CLAUSES],
   RES_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
   EXISTS_TAC (“SUC p”) THEN REWRITE_TAC [ADD_CLAUSES]
]);

(* ---------------------------------------------------------------------*)
(* The following arithmetic theorems were added by TFM in 88.03.31      *)
(*                                                                      *)
(* These are needed to build the recursive type definition package      *)
(* ---------------------------------------------------------------------*)

val EXP_ADD = store_thm ("EXP_ADD",
  “!p q n. n EXP (p+q) = (n EXP p) * (n EXP q)”,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXP,ADD_CLAUSES,MULT_CLAUSES,MULT_ASSOC]);

Theorem NUM_EXP_ADD = EXP_ADD

val NOT_ODD_EQ_EVEN = store_thm ("NOT_ODD_EQ_EVEN",
  “!n m. ~(SUC(n + n) = (m + m))”,
     REPEAT (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES]) THENL
     [MATCH_ACCEPT_TAC NOT_SUC,
      REWRITE_TAC [INV_SUC_EQ,NOT_EQ_SYM (SPEC_ALL NOT_SUC)],
      REWRITE_TAC [INV_SUC_EQ,NOT_SUC],
      ASM_REWRITE_TAC [INV_SUC_EQ]]);

val LESS_EQUAL_ANTISYM = store_thm ("LESS_EQUAL_ANTISYM",
  “!n m. n <= m /\ m <= n ==> (n = m)”,
     REWRITE_TAC [LESS_OR_EQ] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC LESS_ANTISYM,
      ASM_REWRITE_TAC[]]);

Theorem LE_ANTISYM :
    !m (n :num). m <= n /\ n <= m <=> m = n
Proof
    rpt GEN_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM \\
     ASM_REWRITE_TAC [])
 >> ASM_REWRITE_TAC [LESS_EQ_REFL]
QED

val LESS_ADD_SUC = store_thm ("LESS_ADD_SUC",
     “!m n. m < m + SUC n”,
     INDUCT_TAC THENL
     [REWRITE_TAC [LESS_0,ADD_CLAUSES],
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC [LESS_MONO_EQ,ADD_CLAUSES]]);

(* Following proof revised for version 1.12 resolution.  [TFM 91.01.18] *)
val LESS_OR_EQ_ADD = store_thm ("LESS_OR_EQ_ADD",
  “!n m. n < m \/ ?p. n = p+m”,
     REPEAT GEN_TAC THEN ASM_CASES_TAC (“n<m”) THENL
     [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      DISJ2_TAC THEN IMP_RES_TAC NOT_LESS THEN IMP_RES_TAC LESS_OR_EQ THENL
      [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
       IMP_RES_THEN MATCH_ACCEPT_TAC LESS_ADD,
       EXISTS_TAC (“0”) THEN ASM_REWRITE_TAC [ADD]]]);

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
   “(~?n. P n /\ !m. (m<n) ==> ~P m) ==> (!n m. (m<n) ==> ~P m)”),
   CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
   DISCH_TAC THEN
   INDUCT_TAC THEN
   REWRITE_TAC [NOT_LESS_0,LESS_THM] THEN
   REPEAT (FILTER_STRIP_TAC (“P:num->bool”)) THENL
   [POP_ASSUM SUBST1_TAC THEN DISCH_TAC,ALL_TAC] THEN
   RES_TAC);

(* We now prove the well ordering property.                             *)
val WOP = store_thm ("WOP",
    “!P. (?n.P n) ==> (?n. P n /\ (!m. (m<n) ==> ~P m))”,
    GEN_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN
    DISCH_THEN (ASSUME_TAC o MP lemma) THEN
    CONV_TAC NOT_EXISTS_CONV THEN
    GEN_TAC THEN
    POP_ASSUM (MATCH_MP_TAC o SPECL [“SUC n”,“n:num”]) THEN
    MATCH_ACCEPT_TAC LESS_SUC_REFL);

(* anything can be well-ordered if mapped into the natural numbers;
   take the contrapositive to make all constants positive *)
Theorem WOP_measure:
  !P m. (?a:'a. P a) ==> ?b. P b /\ !c. P c ==> m b <= m c
Proof
  rpt strip_tac >>
  Q.SPEC_THEN ‘m’ assume_tac prim_recTheory.WF_measure >>
  dxrule_then (Q.SPEC_THEN ‘P’ mp_tac) (iffLR relationTheory.WF_DEF) >>
  simp_tac bool_ss [PULL_EXISTS] >>
  disch_then dxrule >>
  REWRITE_TAC [prim_recTheory.measure_thm] >>
  METIS_TAC [NOT_LESS]
QED

val COMPLETE_INDUCTION = store_thm ("COMPLETE_INDUCTION",
  “!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n”,
  let val wopeta = CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) WOP
  in
  GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP wopeta) THEN BETA_TAC THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_TAC (“n:num”)) THEN
  EXISTS_TAC (“n:num”) THEN ASM_REWRITE_TAC[]
  end);

val FORALL_NUM_THM = Q.store_thm ("FORALL_NUM_THM",
  `(!n. P n) <=> P 0 /\ !n. P n ==> P (SUC n)`,
  METIS_TAC [INDUCTION]);

(* ---------------------------------------------------------------------*)
(* Some more theorems, mostly about subtraction.                        *)
(* ---------------------------------------------------------------------*)

val SUC_SUB = store_thm(
  "SUC_SUB[simp]",
  “!a. SUC a - a = 1”,
  INDUCT_TAC THENL [
    REWRITE_TAC [SUB, LESS_REFL, ONE],
    ASM_REWRITE_TAC [SUB_MONO_EQ]
  ]);

val SUB_PLUS = store_thm ("SUB_PLUS",
   “!a b c. a - (b + c) = (a - b) - c”,
   REPEAT INDUCT_TAC THEN
   REWRITE_TAC [SUB_0,ADD_CLAUSES,SUB_MONO_EQ] THEN
   PURE_ONCE_REWRITE_TAC [SYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
   PURE_ONCE_ASM_REWRITE_TAC [] THEN REFL_TAC);

(* Statement of thm changed.
**val INV_PRE_LESS = store_thm ("INV_PRE_LESS",
** “!m n. 0 < m /\ 0 < n ==> ((PRE m < PRE n) = (m < n))”,
**   REPEAT INDUCT_TAC THEN
**   REWRITE_TAC[LESS_REFL,SUB,LESS_0,PRE] THEN
**   MATCH_ACCEPT_TAC (SYM(SPEC_ALL LESS_MONO_EQ)));
*)
Theorem INV_PRE_LESS:
  !m. 0 < m  ==> !n. PRE m < PRE n <=> m < n
Proof
  REPEAT (INDUCT_TAC THEN TRY DISCH_TAC) THEN
  REWRITE_TAC[LESS_REFL,SUB,LESS_0,PRE,NOT_LESS_0] THEN
  IMP_RES_TAC LESS_REFL THEN
  MATCH_ACCEPT_TAC (SYM(SPEC_ALL LESS_MONO_EQ))
QED

val INV_PRE_LESS_EQ = store_thm ("INV_PRE_LESS_EQ",
 “!n. 0 < n ==> !m. ((PRE m <= PRE n) = (m <= n))”,
   INDUCT_TAC THEN
   REWRITE_TAC [LESS_REFL,LESS_0,PRE] THEN
   INDUCT_TAC THEN
   REWRITE_TAC [PRE,ZERO_LESS_EQ] THEN
   REWRITE_TAC [ADD1,LESS_EQ_MONO_ADD_EQ]);

val PRE_LESS_EQ = Q.store_thm ("PRE_LESS_EQ",
  `!n. m <= n ==> PRE m <= PRE n`,
  INDUCT_TAC THEN1
    (REWRITE_TAC [LESS_EQ_0] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [LESS_EQ_REFL]) THEN
  VALIDATE (CONV_TAC (DEPTH_CONV
    (REWR_CONV_A (SPEC_ALL (UNDISCH (SPEC_ALL INV_PRE_LESS_EQ)))))) THEN
  REWRITE_TAC [LESS_0]) ;

val SUB_LESS_EQ = store_thm ("SUB_LESS_EQ",
 “!n m. (n - m) <= n”,
   REWRITE_TAC [SYM(SPEC_ALL SUB_EQ_0),SYM(SPEC_ALL SUB_PLUS)] THEN
   CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [SUB_EQ_0,LESS_EQ_ADD]);

val SUB_EQ_EQ_0 = store_thm ("SUB_EQ_EQ_0",
 “!m n. (m - n = m) = ((m = 0) \/ (n = 0))”,
   REPEAT INDUCT_TAC THEN
   REWRITE_TAC [SUB_0,NOT_SUC] THEN
   REWRITE_TAC [SUB] THEN
   ASM_CASES_TAC (“m<SUC n”) THENL
   [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC [NOT_SUC],
    ASM_REWRITE_TAC [INV_SUC_EQ,NOT_SUC] THEN
    IMP_RES_THEN (ASSUME_TAC o MATCH_MP OR_LESS) NOT_LESS THEN
    IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) LESS_ADD_1 THEN
    REWRITE_TAC [ONE, ADD_CLAUSES, NOT_SUC]]);

Theorem SUB_LESS_0:
  !n m. m < n <=> 0 < n - m
Proof
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [ONE,ADD_CLAUSES,SUB] THEN
    REWRITE_TAC [REWRITE_RULE [SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD,LESS_0],
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [NOT_LESS,LESS_OR_EQ,NOT_LESS_0,SUB_EQ_0]]
QED

val SUB_LESS_OR = store_thm ("SUB_LESS_OR",
 “!m n. n < m ==> n <= (m - 1)”,
   REPEAT GEN_TAC THEN
   DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
   REWRITE_TAC [SYM (SPEC_ALL PRE_SUB1)] THEN
   REWRITE_TAC [PRE,ONE,ADD_CLAUSES,LESS_EQ_ADD]);

Theorem SUB_LESS_OR_EQ :
    !m n. 0 < m ==> (n <= m - 1 <=> n < m)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC
 >- REWRITE_TAC [SUB_LESS_OR]
 >> Cases_on ‘m’
 >- FULL_SIMP_TAC std_ss [LESS_REFL]
 >> REWRITE_TAC [SUC_SUB1, LT_SUC_LE]
QED

val LESS_SUB_ADD_LESS = store_thm ("LESS_SUB_ADD_LESS",
 “!n m i. (i < (n - m)) ==> ((i + m) < n)”,
   INDUCT_TAC THENL
   [REWRITE_TAC [SUB_0,NOT_LESS_0],
    REWRITE_TAC [SUB] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (“n < m”) THEN
    ASM_REWRITE_TAC [NOT_LESS_0,LESS_THM] THEN
    let fun tac th g = SUBST1_TAC th g
                       handle _ => ASSUME_TAC th g
    in
    DISCH_THEN (STRIP_THM_THEN tac)
    end THENL
    [DISJ1_TAC THEN MATCH_MP_TAC SUB_ADD THEN
     ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)],
     RES_TAC THEN ASM_REWRITE_TAC[]]]);

val TIMES2 = store_thm ("TIMES2",
   “!n. 2 * n = n + n”,
   REWRITE_TAC [MULT_CLAUSES, NUMERAL_DEF, BIT2, ADD_CLAUSES,ALT_ZERO]);

Theorem LESS_MULT_MONO:
  !m i n. SUC n * m < SUC n * i <=> m < i
Proof
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
      ASM_REWRITE_TAC[]]]]
QED

val MULT_MONO_EQ = store_thm ("MULT_MONO_EQ",
 “!m i n. (((SUC n) * m) = ((SUC n) * i)) = (m = i)”,
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

val MULT_SUC_EQ = store_thm ("MULT_SUC_EQ",
  “!p m n. ((n * (SUC p)) = (m * (SUC p))) = (n = m)”,
  ONCE_REWRITE_TAC [MULT_COMM] THEN REWRITE_TAC [MULT_MONO_EQ]) ;

val MULT_EXP_MONO = store_thm ("MULT_EXP_MONO",
  “!p q n m.((n * ((SUC q) EXP p)) = (m * ((SUC q) EXP p))) = (n = m)”,
     INDUCT_TAC THENL
     [REWRITE_TAC [EXP,MULT_CLAUSES,ADD_CLAUSES],
      ASM_REWRITE_TAC [EXP,MULT_ASSOC,MULT_SUC_EQ]]);

val EQ_ADD_LCANCEL = store_thm ("EQ_ADD_LCANCEL",
  “!m n p. (m + n = m + p) = (n = p)”,
  INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ]);

val EQ_ADD_RCANCEL = store_thm ("EQ_ADD_RCANCEL",
  “!m n p. (m + p = n + p) = (m = n)”,
  ONCE_REWRITE_TAC[ADD_COMM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL);

Theorem EQ_MULT_LCANCEL[simp]:
  !m n p. (m * n = m * p) <=> (m = 0) \/ (n = p)
Proof
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES, NOT_SUC] THEN
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, GSYM NOT_SUC, NOT_SUC] THEN
  ASM_REWRITE_TAC[INV_SUC_EQ, GSYM ADD_ASSOC, EQ_ADD_LCANCEL]
QED

Theorem EQ_MULT_RCANCEL[simp]:
  !m n p. (n * m = p * m) <=> (m = 0) \/ (n = p)
Proof ONCE_REWRITE_TAC [MULT_COMM] THEN REWRITE_TAC [EQ_MULT_LCANCEL]
QED

val ADD_SUB = store_thm ("ADD_SUB",
 “!a c. (a + c) - c = a”,
   GEN_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ]) ;

(* ported from HOL-Light *)
Theorem ADD_SUB2 :
   !m n. (m + n) - m = n
Proof
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB
QED

val LESS_EQ_ADD_SUB = store_thm ("LESS_EQ_ADD_SUB",
 “!c b. (c <= b) ==> !a. (((a + b) - c) = (a + (b - c)))”,
   REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]) ;

(* ---------------------------------------------------------------------*)
(* SUB_EQUAL_0 = |- !c. c - c = 0                                       *)
(* ---------------------------------------------------------------------*)

val _ = print "More properties of subtraction...\n"

val SUB_EQUAL_0 = save_thm ("SUB_EQUAL_0",
   REWRITE_RULE [ADD_CLAUSES] (SPEC (“0”) ADD_SUB));

val LESS_EQ_SUB_LESS = store_thm ("LESS_EQ_SUB_LESS",
 “!a b. (b <= a) ==> !c. ((a - b) < c) = (a < (b + c))”,
   REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, LESS_MONO_EQ]) ;

val NOT_SUC_LESS_EQ = store_thm ("NOT_SUC_LESS_EQ",
 “!n m.~(SUC n <= m) = (m <= n)”,
    REWRITE_TAC [SYM (SPEC_ALL LESS_EQ),NOT_LESS]);

val SUB_SUB = store_thm ("SUB_SUB",
 “!b c. (c <= b) ==> !a. ((a - (b - c)) = ((a + c) - b))”,
   REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]) ;

val LESS_IMP_LESS_ADD = store_thm ("LESS_IMP_LESS_ADD",
 “!n m. n < m ==> !p. n < (m + p)”,
   REPEAT GEN_TAC THEN
   DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
   REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC), ONE] THEN
   PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
   PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
   GEN_TAC THEN MATCH_ACCEPT_TAC LESS_ADD_SUC);

val SUB_LESS_EQ_ADD = store_thm ("SUB_LESS_EQ_ADD",
 “!m p. (m <= p) ==> !n. (((p - m) <= n) = (p <= (m + n)))”,
   REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]) ;

val SUB_LESS_SUC = store_thm ("SUB_LESS_SUC",
  “!p m. p - m < SUC p”,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
  Q.EXISTS_TAC `p` THEN CONJ_TAC
  THENL [ MATCH_ACCEPT_TAC SUB_LESS_EQ,
    MATCH_ACCEPT_TAC LESS_SUC_REFL]) ;

val SUB_NE_SUC = MATCH_MP LESS_NOT_EQ (SPEC_ALL SUB_LESS_SUC) ;
val SUB_LE_SUC = MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC_ALL SUB_LESS_SUC) ;

val SUB_CANCEL = store_thm ("SUB_CANCEL",
 “!p n m. ((n <= p) /\ (m <= p)) ==> (((p - n) = (p - m)) = (n = m))”,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [SUB_0, ZERO_LESS_EQ, SUB_MONO_EQ, LESS_EQ_MONO, INV_SUC_EQ,
    NOT_SUC_LESS_EQ_0, NOT_SUC, GSYM NOT_SUC, SUB_NE_SUC, GSYM SUB_NE_SUC]) ;

val CANCEL_SUB = store_thm ("CANCEL_SUB",
 “!p n m.((p <= n) /\ (p <= m)) ==> (((n - p) = (m - p)) = (n = m))”,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [SUB_0, ZERO_LESS_EQ, SUB_MONO_EQ, LESS_EQ_MONO, INV_SUC_EQ,
    NOT_SUC_LESS_EQ_0]) ;

val NOT_EXP_0 = store_thm ("NOT_EXP_0",
 “!m n. ~(((SUC n) EXP m) = 0)”,
   INDUCT_TAC THEN REWRITE_TAC [EXP] THENL
   [REWRITE_TAC [NOT_SUC, ONE],
    STRIP_TAC THEN
    let val th = (SYM(el 2 (CONJUNCTS (SPECL [“SUC n”,“1”]
                                             MULT_CLAUSES))))
    in
    SUBST1_TAC th
    end THEN REWRITE_TAC [MULT_MONO_EQ] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC]);

val ZERO_LESS_EXP = store_thm ("ZERO_LESS_EXP",
 “!m n. 0 < ((SUC n) EXP m)”,
   REPEAT STRIP_TAC THEN
   let val th = SPEC (“(SUC n) EXP m”) LESS_0_CASES
       fun tac th g = ASSUME_TAC (SYM th) g
                      handle _ => ACCEPT_TAC th g
   in
   STRIP_THM_THEN tac th THEN
   IMP_RES_TAC NOT_EXP_0
   end);

val ODD_OR_EVEN = store_thm ("ODD_OR_EVEN",
 “!n. ?m. (n = (SUC(SUC 0) * m)) \/ (n = ((SUC(SUC 0) * m) + 1))”,
   REWRITE_TAC [ONE] THEN
   INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL
   [EXISTS_TAC (“0”) THEN REWRITE_TAC [ADD_CLAUSES,MULT_CLAUSES],
    EXISTS_TAC (“m:num”) THEN ASM_REWRITE_TAC[ADD_CLAUSES],
    EXISTS_TAC (“SUC m”) THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES]]);

val LESS_EXP_SUC_MONO = store_thm ("LESS_EXP_SUC_MONO",
 “!n m.((SUC(SUC m)) EXP n) < ((SUC(SUC m)) EXP (SUC n))”,
   INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC [EXP] THENL
   [REWRITE_TAC [EXP,ADD_CLAUSES,MULT_CLAUSES,ONE,LESS_0, LESS_MONO_EQ],
    ASM_REWRITE_TAC [LESS_MULT_MONO]]);

(*---------------------------------------------------------------------------*)
(* More arithmetic theorems, mainly concerning orderings [JRH 92.07.14]      *)
(*---------------------------------------------------------------------------*)

val LESS_LESS_CASES = store_thm ("LESS_LESS_CASES",
   “!m n. (m = n) \/ (m < n) \/ (n < m)”,
   let val th = REWRITE_RULE[LESS_OR_EQ]
                            (SPECL[(“m:num”), (“n:num”)] LESS_CASES)
   in REPEAT GEN_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN (fn t => REWRITE_TAC[t]) th
   end);

Theorem num_nchotomy = LESS_LESS_CASES (* from examples/algebra *)

Theorem GREATER_EQ:
  !n m. n >= m <=> m <= n
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GREATER_OR_EQ, GREATER_DEF, LESS_OR_EQ] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
QED

Theorem LESS_EQ_CASES = LE_CASES

val LESS_EQUAL_ADD = store_thm ("LESS_EQUAL_ADD",
  “!m n. m <= n ==> ?p. n = m + p”,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  DISCH_THEN(DISJ_CASES_THEN2 MP_TAC SUBST1_TAC) THENL
   [MATCH_ACCEPT_TAC(GSYM (ONCE_REWRITE_RULE[ADD_SYM] LESS_ADD)),
    EXISTS_TAC (“0”) THEN REWRITE_TAC[ADD_CLAUSES]]);

Theorem LESS_EQ_EXISTS:
  !m n. m <= n <=> ?p. n = m + p
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC LESS_EQUAL_ADD,
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC LESS_EQ_ADD]
QED

Theorem MULT_EQ_0:
  !m n. (m * n = 0) <=> (m = 0) \/ (n = 0)
Proof
  REPEAT GEN_TAC THEN
  MAP_EVERY (STRUCT_CASES_TAC o C SPEC num_CASES) [(“m:num”),(“n:num”)]
  THEN REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, NOT_SUC]
QED

Theorem MULT_EQ_1:
  !x y. (x * y = 1) <=> (x = 1) /\ (y = 1)
Proof
  REPEAT GEN_TAC THEN
  MAP_EVERY (STRUCT_CASES_TAC o C SPEC num_CASES)
            [(“x:num”),(“y:num”)] THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, ONE, GSYM SUC_ID, INV_SUC_EQ,
              ADD_EQ_0,MULT_EQ_0] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]
QED

Theorem MULT_EQ_ID[simp]:
  !m n. (m * n = n <=> m=1 \/ n=0) /\
        (n * m = n <=> m=1 \/ n=0)
Proof
 REPEAT GEN_TAC THEN REVERSE CONJ_ASM1_TAC
 THEN1 (ONCE_REWRITE_TAC [MULT_COMM] THEN ASM_REWRITE_TAC[]) THEN
 STRUCT_CASES_TAC (SPEC “m:num” num_CASES) THEN
 REWRITE_TAC [MULT_CLAUSES,ONE,GSYM NOT_SUC,INV_SUC_EQ] THENL
 [METIS_TAC[], METIS_TAC [ADD_INV_0_EQ,MULT_EQ_0,ADD_SYM]]
QED

val LESS_MULT2 = store_thm ("LESS_MULT2",
  “!m n. 0 < m /\ 0 < n ==> 0 < (m * n)”,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[NOT_LESS, LESS_EQ_0, DE_MORGAN_THM, MULT_EQ_0]);

val MULT_POS = save_thm("MULT_POS", LESS_MULT2);

Theorem ZERO_LESS_MULT[simp]:
  !m n. 0 < m * n <=> 0 < m /\ 0 < n
Proof
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [MULT_CLAUSES, LESS_REFL, LESS_0] THEN
  Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [MULT_CLAUSES, LESS_REFL, LESS_0, ADD_CLAUSES]
QED

Theorem ZERO_LESS_ADD:
  !m n. 0 < m + n <=> 0 < m \/ 0 < n
Proof
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [ADD_CLAUSES, LESS_REFL, LESS_0]
QED

(*---------------------------------------------------------------------------*)
(* Single theorem about the factorial function           [JRH 92.07.14]      *)
(*---------------------------------------------------------------------------*)

val FACT = new_recursive_definition
   {name = "FACT",
    rec_axiom = num_Axiom,
    def = “(FACT 0 = 1) /\
             (FACT (SUC n) = (SUC n) * FACT(n))”};

val FACT_LESS = store_thm ("FACT_LESS",
  “!n. 0 < FACT n”,
  INDUCT_TAC THEN REWRITE_TAC[FACT, ONE, LESS_SUC_REFL] THEN
  MATCH_MP_TAC LESS_MULT2 THEN ASM_REWRITE_TAC[LESS_0]);

(* Theorem: 1 <= FACT n *)
(* Proof:
   Note 0 < FACT n    by FACT_LESS
     so 1 <= FACT n   by arithmetic
*)
val FACT_GE_1 = store_thm(
  "FACT_GE_1",
  ``!n. 1 <= FACT n``,
  metis_tac[FACT_LESS, LESS_OR, ONE]);

(* Idea: test if a function f is factorial. *)

(* Theorem: f = FACT <=> f 0 = 1 /\ !n. f (SUC n) = SUC n * f n *)
(* Proof:
   If part is true         by FACT
   Only-if part, apply FUN_EQ_THM, this is to show:
   !n. f n = FACT n.
   By induction on n.
   Base: f 0 = FACT 0
           f 0
         = 1               by given
         = FACT 0          by FACT_0
   Step: f n = FACT n ==> f (SUC n) = FACT (SUC n)
           f (SUC n)
         = SUC n * f n     by given
         = SUC n * FACT n  by induction hypothesis
         = FACT (SUC n)    by FACT
*)
Theorem FACT_iff:
  !f. f = FACT <=> f 0 = 1 /\ !n. f (SUC n) = SUC n * f n
Proof
  rw[FACT, EQ_IMP_THM] >>
  rw[FUN_EQ_THM] >>
  Induct_on `x` >>
  simp[FACT]
QED

(*---------------------------------------------------------------------------*)
(* Theorems about evenness and oddity                    [JRH 92.07.14]      *)
(*---------------------------------------------------------------------------*)

val _ = print "Theorems about evenness and oddity\n"
val EVEN_ODD = store_thm ("EVEN_ODD",
  “!n. EVEN n = ~ODD n”,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN, ODD]);

val ODD_EVEN = store_thm ("ODD_EVEN",
  “!n. ODD n = ~(EVEN n)”,
  REWRITE_TAC[EVEN_ODD]);

val EVEN_OR_ODD = store_thm ("EVEN_OR_ODD",
  “!n. EVEN n \/ ODD n”,
  REWRITE_TAC[EVEN_ODD, REWRITE_RULE[DE_MORGAN_THM] NOT_AND]);

val EVEN_AND_ODD = store_thm ("EVEN_AND_ODD",
  “!n. ~(EVEN n /\ ODD n)”,
  REWRITE_TAC[ODD_EVEN, NOT_AND]);

val EVEN_ADD = store_thm ("EVEN_ADD",
  “!m n. EVEN(m + n) = (EVEN m = EVEN n)”,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES, EVEN] THEN
  BOOL_CASES_TAC (“EVEN m”) THEN REWRITE_TAC[]);

Theorem EVEN_MULT:
  !m n. EVEN(m * n) <=> EVEN m \/ EVEN n
Proof
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES, EVEN_ADD, EVEN] THEN
  BOOL_CASES_TAC (“EVEN m”) THEN REWRITE_TAC[]
QED

Theorem ODD_ADD:
  !m n. ODD(m + n) <=> ODD m <> ODD n
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EVEN, EVEN_ADD] THEN
  BOOL_CASES_TAC (“EVEN m”) THEN REWRITE_TAC[]
QED

Theorem ODD_MULT:
  !m n. ODD(m * n) <=> ODD(m) /\ ODD(n)
Proof REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EVEN, EVEN_MULT, DE_MORGAN_THM]
QED

val two = prove(
  “2 = SUC 1”,
  REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2] THEN
  ONCE_REWRITE_TAC [SYM (SPEC (“0”) NUMERAL_DEF)] THEN
  REWRITE_TAC [ADD_CLAUSES]);

val EVEN_DOUBLE = store_thm ("EVEN_DOUBLE",
  “!n. EVEN(2 * n)”,
  GEN_TAC THEN REWRITE_TAC[EVEN_MULT] THEN DISJ1_TAC THEN
  REWRITE_TAC[EVEN, ONE, two]);

val ODD_DOUBLE = store_thm ("ODD_DOUBLE",
  “!n. ODD(SUC(2 * n))”,
  REWRITE_TAC[ODD] THEN REWRITE_TAC[GSYM EVEN_ODD, EVEN_DOUBLE]);

val EVEN_ODD_EXISTS = store_thm ("EVEN_ODD_EXISTS",
  “!n. (EVEN n ==> ?m. n = 2 * m) /\ (ODD n ==> ?m. n = SUC(2 * m))”,
  REWRITE_TAC[ODD_EVEN] THEN INDUCT_TAC THEN REWRITE_TAC[EVEN] THENL
   [EXISTS_TAC (“0”) THEN REWRITE_TAC[MULT_CLAUSES],
    POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(X_CHOOSE_THEN (“m:num”) SUBST1_TAC o
                    C MATCH_MP th)) THENL
     [EXISTS_TAC (“SUC m”) THEN
      REWRITE_TAC[ONE, two, MULT_CLAUSES, ADD_CLAUSES],
      EXISTS_TAC (“m:num”) THEN REFL_TAC]]);

val EVEN_EXISTS = store_thm ("EVEN_EXISTS",
  “!n. EVEN n = ?m. n = 2 * m”,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EVEN_ODD_EXISTS],
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC EVEN_DOUBLE]);

val ODD_EXISTS = store_thm ("ODD_EXISTS",
  “!n. ODD n = ?m. n = SUC(2 * m)”,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EVEN_ODD_EXISTS],
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC ODD_DOUBLE]);

val EVEN_EXP_IFF = Q.store_thm(
  "EVEN_EXP_IFF",
  `!n m. EVEN (m ** n) <=> 0 < n /\ EVEN m`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXP, ONE, EVEN, EVEN_MULT, LESS_0, LESS_REFL] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []);

val EVEN_EXP = Q.store_thm ("EVEN_EXP",
   `!m n. 0 < n /\ EVEN m ==> EVEN (m ** n)`,
   METIS_TAC[EVEN_EXP_IFF]);

val ODD_EXP_IFF = Q.store_thm(
  "ODD_EXP_IFF",
  `!n m. ODD (m ** n) <=> (n = 0) \/ ODD m`,
  REWRITE_TAC [ODD_EVEN, EVEN_EXP_IFF, DE_MORGAN_THM, NOT_LT_ZERO_EQ_ZERO]);

val ODD_EXP = Q.store_thm(
  "ODD_EXP",
  `!m n. 0 < n /\ ODD m ==> ODD (m ** n)`,
  METIS_TAC[ODD_EXP_IFF, NOT_LT_ZERO_EQ_ZERO]);

Theorem ODD_POS:
    !n. ODD n ==> 0 < n
Proof
    STRIP_TAC >> Cases_on ‘n’ >> REWRITE_TAC [ODD,LESS_0]
QED

(* --------------------------------------------------------------------- *)
(* Theorems moved from the "more_arithmetic" library      [RJB 92.09.28] *)
(* --------------------------------------------------------------------- *)

val EQ_LESS_EQ = store_thm ("EQ_LESS_EQ",
   “!m n. (m = n) = ((m <= n) /\ (n <= m))”,
   REPEAT GEN_TAC THEN EQ_TAC
    THENL [STRIP_TAC THEN ASM_REWRITE_TAC [LESS_EQ_REFL],
           REWRITE_TAC [LESS_EQUAL_ANTISYM]]);

Theorem ADD_MONO_LESS_EQ:
   !m n p. m + n <= m + p <=> n <= p
Proof ONCE_REWRITE_TAC [ADD_SYM]
        THEN REWRITE_TAC [LESS_EQ_MONO_ADD_EQ]
QED
Theorem LE_ADD_LCANCEL = ADD_MONO_LESS_EQ
Theorem LE_ADD_RCANCEL = ONCE_REWRITE_RULE [ADD_COMM] LE_ADD_LCANCEL

(* ---------------------------------------------------------------------*)
(* Theorems to support the arithmetic proof procedure     [RJB 92.09.29]*)
(* ---------------------------------------------------------------------*)

val _ = print "Theorems to support the arithmetic proof procedure\n"
Theorem NOT_LEQ:
  !m n. ~(m <= n) <=> SUC n <= m
Proof
   REWRITE_TAC [SYM (SPEC_ALL LESS_EQ)] THEN
   REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)]
QED

Theorem NOT_NUM_EQ:
   !m n. m <> n <=> SUC m <= n \/ SUC n <= m
Proof
   REWRITE_TAC [EQ_LESS_EQ,DE_MORGAN_THM,NOT_LEQ] THEN
   MATCH_ACCEPT_TAC DISJ_SYM
QED

val NOT_GREATER = store_thm ("NOT_GREATER",
   “!m n. ~(m > n) = (m <= n)”,
   REWRITE_TAC [GREATER_DEF,NOT_LESS]);

Theorem NOT_GREATER_EQ:
   !m n. ~(m >= n) <=> SUC m <= n
Proof REWRITE_TAC [GREATER_EQ,NOT_LEQ]
QED

val SUC_ONE_ADD = store_thm ("SUC_ONE_ADD",
   “!n. SUC n = 1 + n”,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [ADD1,ADD_SYM] THEN
   REFL_TAC);

val SUC_ADD_SYM = store_thm ("SUC_ADD_SYM",
   “!m n. SUC (m + n) = (SUC n) + m”,
   REPEAT GEN_TAC THEN
   REWRITE_TAC[ADD_CLAUSES] THEN
   AP_TERM_TAC THEN
   ACCEPT_TAC (SPEC_ALL ADD_SYM));

val NOT_SUC_ADD_LESS_EQ = store_thm ("NOT_SUC_ADD_LESS_EQ",
   “!m n. ~(SUC (m + n) <= m)”,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [SYM (SPEC_ALL LESS_EQ)] THEN
   REWRITE_TAC [NOT_LESS,LESS_EQ_ADD]);

Theorem MULT_LESS_EQ_SUC:
   !m n p. m <= n <=> SUC p * m <= SUC p * n
Proof
   let val th1 = SPEC (“b:num”) (SPEC (“c:num”) (SPEC (“a:num”)
                      LESS_MONO_ADD))
       val th2 = SPEC (“c:num”) (SPEC (“d:num”) (SPEC (“b:num”)
                    LESS_MONO_ADD))
       val th3 = ONCE_REWRITE_RULE [ADD_SYM] th2
       val th4 = CONJ (UNDISCH_ALL th1) (UNDISCH_ALL th3)
       val th5 = MATCH_MP LESS_TRANS th4
       val th6 = DISCH_ALL th5
   in
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [LESS_MONO_MULT],
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)] THEN
    SPEC_TAC ((“p:num”),(“p:num”)) THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES],
     STRIP_TAC THEN
     RES_TAC THEN
     ONCE_REWRITE_TAC [MULT_CLAUSES] THEN
     IMP_RES_TAC th6]]
   end
QED

Theorem LE_MULT_LCANCEL:
  !m n p. m * n <= m * p <=> (m = 0) \/ n <= p
Proof
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m`  STRUCT_CASES_TAC num_CASES THENL [
    REWRITE_TAC [LESS_EQ_REFL, MULT_CLAUSES],
    REWRITE_TAC [NOT_SUC, GSYM MULT_LESS_EQ_SUC]
  ]
QED

Theorem LE_MULT_RCANCEL:
  !m n p. m * n <= p * n <=> n = 0 \/ m <= p
Proof ONCE_REWRITE_TAC [MULT_COMM] THEN REWRITE_TAC [LE_MULT_LCANCEL]
QED

Theorem LT_MULT_LCANCEL:
  !m n p. m * n < m * p <=> 0 < m /\ n < p
Proof
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THENL [
    REWRITE_TAC [MULT_CLAUSES, LESS_REFL],
    REWRITE_TAC [LESS_MULT_MONO, LESS_0]
  ]
QED

Theorem LT_MULT_RCANCEL:
  !m n p. m * n < p * n <=> 0 < n /\ m < p
Proof
  ONCE_REWRITE_TAC [MULT_COMM] THEN REWRITE_TAC [LT_MULT_LCANCEL]
QED

(* |- (m < m * n = 0 < m /\ 1 < n) /\ (m < n * m = 0 < m /\ 1 < n) *)
Theorem LT_MULT_CANCEL_LBARE =
  CONJ
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`m`, `1`, `n`] LT_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`1`,`m`, `n`] LT_MULT_RCANCEL))

Theorem LT1_EQ0[simp]:
  x < 1 <=> (x = 0)
Proof
  Q.SPEC_THEN `x`  STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [ONE, LESS_0, NOT_LESS_0, LESS_MONO_EQ, NOT_SUC]
QED

(* |- (m * n < m = 0 < m /\ (n = 0)) /\ (m * n < n = 0 < n /\ (m = 0)) *)
Theorem LT_MULT_CANCEL_RBARE =
  CONJ
    (REWRITE_RULE [MULT_CLAUSES, LT1_EQ0]
                  (Q.SPECL [`m`,`n`,`1`] LT_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES, LT1_EQ0]
                  (Q.SPECL [`m`,`n`,`1`] LT_MULT_RCANCEL))

val le1_lt0 = prove(“1 <= n <=> 0 < n”, REWRITE_TAC [LESS_EQ, ONE]);

(* |- (m <= m * n = (m = 0) \/ 0 < n) /\ (m <= n * m = (m = 0) \/ 0 < n) *)
Theorem LE_MULT_CANCEL_LBARE =
  CONJ
    (REWRITE_RULE [MULT_CLAUSES, le1_lt0]
                  (Q.SPECL [`m`,`1`,`n`] LE_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES, le1_lt0]
                  (Q.SPECL [`1`,`m`,`n`] LE_MULT_RCANCEL))

(* |- (m * n <= m = (m = 0) \/ n <= 1) /\ (m * n <= n = (n = 0) \/ m <= 1) *)
Theorem LE_MULT_CANCEL_RBARE =
  CONJ
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`m`,`n`,`1`] LE_MULT_LCANCEL))
    (REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`m`,`n`,`1`] LE_MULT_RCANCEL))

val SUB_LEFT_ADD = store_thm ("SUB_LEFT_ADD",
   “!m n p. m + (n - p) = (if (n <= p) then m else (m + n) - p)”,
   GEN_TAC THEN REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]) ;

val SUB_RIGHT_ADD = store_thm ("SUB_RIGHT_ADD",
   “!m n p. (m - n) + p = (if (m <= n) then p else (m + p) - n)”,
   INDUCT_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]) ;

val SUB_LEFT_SUB = store_thm ("SUB_LEFT_SUB",
   “!m n p. m - (n - p) = (if (n <= p) then m else (m + p) - n)”,
   GEN_TAC THEN REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ,
     ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]) ;

val SUB_RIGHT_SUB = store_thm ("SUB_RIGHT_SUB",
   “!m n p. (m - n) - p = m - (n + p)”,
   INDUCT_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [SUB_0,ADD_CLAUSES,SUB_MONO_EQ]) ;

val SUB_LEFT_SUC = store_thm ("SUB_LEFT_SUC",
   “!m n. SUC (m - n) = (if (m <= n) then (SUC 0) else (SUC m) - n)”,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (“m <= n”) THENL
   [IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) (SYM (SPEC_ALL SUB_EQ_0)),
    ASM_REWRITE_TAC [SUB] THEN
    ASSUM_LIST (MAP_EVERY (REWRITE_TAC o CONJUNCTS o
                           (PURE_REWRITE_RULE [LESS_OR_EQ,DE_MORGAN_THM])))]);

val pls = prove (“p <= m \/ p <= 0 <=> p <= m”,
   REWRITE_TAC [LESS_EQ_0] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [ZERO_LESS_EQ]) ;

Theorem SUB_LEFT_LESS_EQ:
   !m n p. m <= (n - p) <=> m + p <= n \/ m <= 0
Proof
   GEN_TAC THEN REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_MONO_EQ, pls,
     ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, NOT_SUC]
QED

val SUB_RIGHT_LESS_EQ = store_thm ("SUB_RIGHT_LESS_EQ",
   “!m n p. ((m - n) <= p) = (m <= (n + p))”,
   INDUCT_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [SUB_0,ADD_CLAUSES,
     SUB_MONO_EQ, LESS_EQ_MONO, ZERO_LESS_EQ]) ;

val SUB_LEFT_LESS = store_thm ("SUB_LEFT_LESS",
   “!m n p. (m < (n - p)) = ((m + p) < n)”,
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [LESS_EQ,SYM (SPEC_ALL (CONJUNCT2 ADD))] THEN
   PURE_ONCE_REWRITE_TAC [SUB_LEFT_LESS_EQ] THEN
   REWRITE_TAC [SYM (SPEC_ALL LESS_EQ),NOT_LESS_0]);

val SUB_RIGHT_LESS =
   let val BOOL_EQ_NOT_BOOL_EQ = prove(
        “!x y. (x = y) = (~x = ~y)”,
        REPEAT GEN_TAC THEN
        BOOL_CASES_TAC (“x:bool”) THEN
        REWRITE_TAC [])
   in
   store_thm ("SUB_RIGHT_LESS",
   “!m n p. ((m - n) < p) = ((m < (n + p)) /\ (0 < p))”,
   REPEAT GEN_TAC THEN
   PURE_ONCE_REWRITE_TAC [BOOL_EQ_NOT_BOOL_EQ] THEN
   PURE_REWRITE_TAC [DE_MORGAN_THM,NOT_LESS] THEN
   SUBST1_TAC (SPECL [(“n:num”),(“p:num”)] ADD_SYM) THEN
   REWRITE_TAC [SUB_LEFT_LESS_EQ])
   end;

val SUB_LEFT_GREATER_EQ = store_thm ("SUB_LEFT_GREATER_EQ",
   “!m n p. (m >= (n - p)) = ((m + p) >= n)”,
   REWRITE_TAC [GREATER_EQ] THEN
   GEN_TAC THEN REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [SUB_0,ADD_CLAUSES,
     SUB_MONO_EQ, LESS_EQ_MONO, ZERO_LESS_EQ]) ;

val SUB_RIGHT_GREATER_EQ = store_thm ("SUB_RIGHT_GREATER_EQ",
   “!m n p. ((m - n) >= p) = ((m >= (n + p)) \/ (0 >= p))”,
   REWRITE_TAC [GREATER_EQ] THEN
   INDUCT_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [SUB_0,ADD_CLAUSES, SUB_MONO_EQ,
     LESS_EQ_MONO, ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, pls]) ;

val SUB_LEFT_GREATER = store_thm ("SUB_LEFT_GREATER",
   “!m n p. (m > (n - p)) = (((m + p) > n) /\ (m > 0))”,
   REPEAT GEN_TAC THEN
   PURE_ONCE_REWRITE_TAC [GREATER_DEF] THEN
   SUBST1_TAC (SPECL [(“m:num”),(“p:num”)] ADD_SYM) THEN
   REWRITE_TAC [SUB_RIGHT_LESS]);

val SUB_RIGHT_GREATER = store_thm ("SUB_RIGHT_GREATER",
   “!m n p. ((m - n) > p) = (m > (n + p))”,
   REPEAT GEN_TAC THEN
   PURE_ONCE_REWRITE_TAC [GREATER_DEF] THEN
   SUBST1_TAC (SPECL [(“n:num”),(“p:num”)] ADD_SYM) THEN
   REWRITE_TAC [SUB_LEFT_LESS]);

Theorem SUB_LEFT_EQ:
   !m n p. (m = (n - p)) <=> (m + p = n) \/ (m <= 0 /\ n <= p)
Proof
   GEN_TAC THEN REPEAT INDUCT_TAC THEN
   ASM_REWRITE_TAC [SUB_0,ADD_CLAUSES, INV_SUC_EQ,
     SUB_MONO_EQ, LESS_EQ_MONO, ZERO_LESS_EQ, LESS_EQ_0, NOT_SUC]
QED

Theorem SUB_RIGHT_EQ:
   !m n p. (m - n = p) <=> (m = n + p) \/ (m <= n /\ p <= 0)
Proof
   INDUCT_TAC THEN INDUCT_TAC THEN GEN_TAC THEN
   ASM_REWRITE_TAC [SUB_0,ADD_CLAUSES, INV_SUC_EQ, SUB_EQ_0, SUB_MONO_EQ,
     LESS_EQ_MONO, ZERO_LESS_EQ, LESS_EQ_0, NOT_SUC, GSYM NOT_SUC] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
QED

Theorem LE =
   CONJ LESS_EQ_0
      (prove(“(!m n. m <= SUC n <=> (m = SUC n) \/ m <= n)”,
        REPEAT GEN_TAC THEN
        CONV_TAC (DEPTH_CONV (LHS_CONV (REWR_CONV LESS_OR_EQ))) THEN
        REWRITE_TAC [GSYM LESS_EQ_IFF_LESS_SUC] THEN
        MATCH_ACCEPT_TAC DISJ_COMM))

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

val exists_lemma = prove(
   “?r q. (k=(q*n)+r)”,
   MAP_EVERY EXISTS_TAC [“k:num”,“0”] THEN
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
                                   (SPEC (“\r.?q.k=(q*n)+r”) WOP))
                        exists_lemma);

(* We will need the lemma  |- !m n. n <= m ==> (?p. m = n + p)          *)
val leq_add_lemma = prove(
    “!m n. (n<=m) ==> ?p.m=n+p”,
    REWRITE_TAC [LESS_OR_EQ] THEN
    REPEAT STRIP_TAC THENL
    [FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1) THEN
     EXISTS_TAC (“p+1”) THEN
     FIRST_ASSUM ACCEPT_TAC,
     EXISTS_TAC (“0”) THEN
     ASM_REWRITE_TAC [ADD_CLAUSES]]);

(* We will also need the lemma:  |- k=qn+n+p ==> k=(q+1)*n+p            *)
val k_expr_lemma = prove(
   “(k=(q*n)+(n+p)) ==> (k=((q+1)*n)+p)”,
   REWRITE_TAC [RIGHT_ADD_DISTRIB,MULT_CLAUSES,ADD_ASSOC]);

(* We will also need the lemma: [0<n] |- p < (n + p)                    *)
val less_add = TAC_PROOF(([“0<n”], “p < (n + p)”),
   PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC LESS_ADD_NONZERO THEN
   IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) LESS_ADD_1 THEN
   REWRITE_TAC [ADD_CLAUSES, ONE, NOT_SUC]);

(* Now prove the desired theorem.                                       *)
val DA = store_thm ("DA",
“!k n. 0<n ==> ?r q. (k=(q*n)+r) /\ r<n”,
   REPEAT STRIP_TAC THEN
   STRIP_ASSUME_TAC smallest_lemma THEN
   MAP_EVERY EXISTS_TAC [“n':num”,“q:num”] THEN
   ASM_REWRITE_TAC [] THEN
   DISJ_CASES_THEN CHECK_ASSUME_TAC
                   (SPECL [“n':num”,“n:num”] LESS_CASES) THEN
   IMP_RES_THEN (STRIP_THM_THEN SUBST_ALL_TAC) leq_add_lemma THEN
   IMP_RES_TAC k_expr_lemma THEN
   ANTE_RES_THEN IMP_RES_TAC less_add);

(* ---------------------------------------------------------------------*)
(* We can now define MOD and DIV to have the property given by DA.      *)
(* We prove the existence of the required functions, and then define    *)
(* MOD and DIV using a constant specification.                          *)
(* ---------------------------------------------------------------------*)

(* First prove the existence of MOD.                                    *)
val MOD_exists = prove(
   “?MOD. !n. (0<n) ==>
               !k.?q.(k=((q * n)+(MOD k n))) /\ ((MOD k n) < n)”,
   EXISTS_TAC (“\k n. @r. ?q. (k = (q * n) + r) /\ r < n”) THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (“k:num”)) DA THEN
   CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
   CONV_TAC SELECT_CONV THEN
   MAP_EVERY EXISTS_TAC [“r:num”,“q:num”] THEN
   CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

(* Now, prove the existence of MOD and DIV.                             *)
val MOD_DIV_exist = prove(
   “?MOD DIV.
      !n. 0<n ==>
          !k. (k = ((DIV k n * n) + MOD k n)) /\ (MOD k n < n)”,
   STRIP_ASSUME_TAC MOD_exists THEN
   EXISTS_TAC (“MOD:num->num->num”) THEN
   EXISTS_TAC (“\k n.  @q. (k = (q * n) + (MOD k n))”) THEN
   REPEAT STRIP_TAC THENL
   [CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC SELECT_CONV THEN
   RES_THEN (STRIP_ASSUME_TAC o SPEC (“k:num”)) THEN
   EXISTS_TAC (“q:num”) THEN
   FIRST_ASSUM ACCEPT_TAC,
   RES_THEN (STRIP_ASSUME_TAC o SPEC (“k:num”))]);

(*---------------------------------------------------------------------------
            Now define MOD and DIV by a constant specification.
 ---------------------------------------------------------------------------*)

val OT_DIVISION =
  new_specification ("OT_DIVISION", ["OT_MOD", "OT_DIV"], MOD_DIV_exist);

(* HOL4 now switches to HOL-Light compatible version of DIV and MOD *)
val DIV_def = new_definition
  ("DIV_def", “DIV m n = if n = 0 then 0 else OT_DIV m n”);

val MOD_def = new_definition
  ("MOD_def", “MOD m n = if n = 0 then m else OT_MOD m n”);

val _ = set_fixity "MOD" (Infixl 650);
val _ = set_fixity "DIV" (Infixl 600);

Theorem DIVISION:
  !n. 0 < n ==> !k. k = k DIV n * n + k MOD n /\ k MOD n < n
Proof
  NTAC 2 STRIP_TAC
  THEN IMP_RES_TAC prim_recTheory.LESS_NOT_EQ
  THEN POP_ASSUM (ASSUME_TAC o GSYM)
  THEN ASM_REWRITE_TAC [DIV_def,MOD_def]
  THEN MATCH_MP_TAC OT_DIVISION
  THEN ASM_REWRITE_TAC []
QED

val DIV2_def = new_definition("DIV2_def", “DIV2 n = n DIV 2”);

local
   open OpenTheoryMap
in
   val _ = OpenTheory_const_name
              {const = {Thy = "arithmetic", Name = "DIV2"},
               name = (["HOL4", "arithmetic"], "DIV2")}
end

(* ---------------------------------------------------------------------*)
(* Properties of MOD and DIV that don't depend on uniqueness.           *)
(* ---------------------------------------------------------------------*)

val MOD_ONE = store_thm ("MOD_ONE",
“!k. k MOD (SUC 0) = 0”,
   STRIP_TAC THEN
   MP_TAC (CONJUNCT2 (SPEC (“k:num”)
            (REWRITE_RULE [LESS_SUC_REFL] (SPEC (“SUC 0”) DIVISION)))) THEN
   REWRITE_TAC [LESS_THM,NOT_LESS_0]);

(* |- x MOD 1 = 0 *)
val MOD_1 = save_thm ("MOD_1", REWRITE_RULE [SYM ONE] MOD_ONE);

val DIV_LESS_EQ = store_thm ("DIV_LESS_EQ",
 “!n. 0<n ==> !k. (k DIV n) <= k”,
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (“k:num”)) DIVISION THEN
   FIRST_ASSUM (fn th => fn g => SUBST_OCCS_TAC [([2],th)] g) THEN
   REPEAT_TCL STRIP_THM_THEN MP_TAC (SPEC (“n:num”) num_CASES) THENL
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

val lemma = prove(
  “!x y z. x<y ==> ~(y + z = x)”,
  REPEAT STRIP_TAC THEN POP_ASSUM (SUBST_ALL_TAC o SYM)
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[]
  THEN SPEC_TAC (“y:num”,“y:num”)
  THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES,NOT_LESS_0,LESS_MONO_EQ]);

local val (eq,ls) =
   CONJ_PAIR (SPEC (“k:num”)
       (REWRITE_RULE [LESS_0] (SPEC (“SUC(r+p)”) DIVISION)))
in
val DIV_UNIQUE = store_thm ("DIV_UNIQUE",
 “!n k q. (?r. (k = q*n + r) /\ r<n) ==> (k DIV n = q)”,
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
                 (SPECL [“0”,“n:num”,“r:num”]LESS_MONO_ADD_EQ))]
     THEN REWRITE_TAC [ADD_CLAUSES, LESS_0],

   MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN EXISTS_TAC (“SUC (r+p)”)
     THEN REWRITE_TAC
           [CONJUNCT2(SPEC_ALL(MATCH_MP DIVISION (SPEC(“r+p”) LESS_0)))]
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
                 (SPECL [“1”,“0”,“p:num”]ADD_MONO_LESS_EQ)]])
end;

val lemma = prove(
   “!n k q r. ((k = (q * n) + r) /\ r < n) ==> (k DIV n = q)”,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC DIV_UNIQUE THEN
   EXISTS_TAC (“r:num”) THEN
   ASM_REWRITE_TAC []);

val MOD_UNIQUE = store_thm ("MOD_UNIQUE",
   “!n k r. (?q. (k = (q * n) + r) /\ r < n) ==> (k MOD n = r)”,
   REPEAT STRIP_TAC THEN
   MP_TAC (DISCH_ALL (SPEC (“k:num”)
                     (UNDISCH (SPEC (“n:num”) DIVISION)))) THEN
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

(* A combined version of DIV_UNIQUE and MOD_UNIQUE from HOL-Light *)
Theorem DIVMOD_UNIQ :
   !m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q) /\ (m MOD n = r)
Proof
    rpt STRIP_TAC
 >| [ MATCH_MP_TAC DIV_UNIQUE \\
      Q.EXISTS_TAC ‘r’ >> ASM_REWRITE_TAC [],
      MATCH_MP_TAC MOD_UNIQUE \\
      Q.EXISTS_TAC ‘q’ >> ASM_REWRITE_TAC [] ]
QED

val DIV2_DOUBLE = store_thm (* from probabilityTheory *)
  ("DIV2_DOUBLE", “!n. DIV2 (2 * n) = n”,
    GEN_TAC >> REWRITE_TAC [DIV2_def]
 >> MATCH_MP_TAC DIV_UNIQUE
 >> Q.EXISTS_TAC `0`
 >> `0:num < 2` by METIS_TAC [TWO, ONE, LESS_0]
 >> ASM_REWRITE_TAC [Once MULT_COMM, ADD_0]);
val _ = export_rewrites ["DIV2_DOUBLE"];

(* ---------------------------------------------------------------------*)
(* Properties of MOD and DIV proved using uniqueness.                   *)
(* ---------------------------------------------------------------------*)

val DIV_MULT = store_thm ("DIV_MULT",
 “!n r. r < n ==> !q. (q*n + r) DIV n = q”,
   REPEAT GEN_TAC THEN
   REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC (“n:num”) num_CASES) THENL
   [REWRITE_TAC [NOT_LESS_0],
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIV_UNIQUE THEN
    EXISTS_TAC (“r:num”) THEN
    ASM_REWRITE_TAC []]);

val LESS_MOD = store_thm ("LESS_MOD",
 “!n k. k < n ==> ((k MOD n) = k)”,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC MOD_UNIQUE THEN
   EXISTS_TAC (“0”) THEN
   ASM_REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES]);

val MOD_EQ_0 = store_thm ("MOD_EQ_0",
 “!n. 0<n ==> !k. ((k * n) MOD n) = 0”,
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (“k * n”)) DIVISION THEN
   MATCH_MP_TAC MOD_UNIQUE THEN
   EXISTS_TAC (“k:num”) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [ADD_CLAUSES], FIRST_ASSUM ACCEPT_TAC]);

val ZERO_MOD = store_thm ("ZERO_MOD",
 “!n. 0<n ==> (0 MOD n = 0)”,
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (MP_TAC o SPEC (“0”)) MOD_EQ_0 THEN
   REWRITE_TAC [MULT_CLAUSES]);

val ZERO_DIV = store_thm ("ZERO_DIV",
   “!n. 0<n ==> (0 DIV n = 0)”,
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC DIV_UNIQUE THEN
     EXISTS_TAC (“0”) THEN
     ASM_REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES]);

Theorem DIV_0[simp]:
  k DIV 0 = 0 /\ 0 DIV n = 0
Proof
  conj_tac >- REWRITE_TAC [DIV_def] >> Cases_on ‘0 < n’ >>
  ASM_SIMP_TAC bool_ss [ZERO_DIV] >>
  RULE_ASSUM_TAC (REWRITE_RULE[NOT_LT_ZERO_EQ_ZERO]) >>
  ASM_REWRITE_TAC [DIV_def]
QED

Theorem MOD_0[simp]:
  k MOD 0 = k /\ 0 MOD n = 0
Proof
  conj_tac >- REWRITE_TAC [MOD_def] >> Cases_on ‘0 < n’ >>
  ASM_SIMP_TAC bool_ss [ZERO_MOD] >>
  RULE_ASSUM_TAC (REWRITE_RULE[NOT_LT_ZERO_EQ_ZERO]) >>
  ASM_REWRITE_TAC [MOD_def]
QED

val MOD_MULT = store_thm ("MOD_MULT",
 “!n r. r < n ==> !q. (q * n + r) MOD n = r”,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC MOD_UNIQUE THEN
   EXISTS_TAC (“q:num”) THEN
   ASM_REWRITE_TAC [ADD_CLAUSES,MULT_CLAUSES]);

val MOD_TIMES = store_thm ("MOD_TIMES",
 “!n. 0<n ==> !q r. (((q * n) + r) MOD n) = (r MOD n)”,
   let fun SUBS th = SUBST_OCCS_TAC [([1],th)]
   in
   REPEAT STRIP_TAC THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (“r:num”)) DIVISION THEN
   REWRITE_TAC [ADD_ASSOC,SYM(SPEC_ALL RIGHT_ADD_DISTRIB)] THEN
   IMP_RES_THEN (ASSUME_TAC o SPEC (“r:num”)) DIVISION THEN
   IMP_RES_TAC MOD_MULT THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC
   end);

val MOD_TIMES_SUB = store_thm ("MOD_TIMES_SUB",
 “!n q r. 0 < n /\ 0 < q /\ r <= n ==> ((q * n - r) MOD n = (n - r) MOD n)”,
 NTAC 2 STRIP_TAC THEN
 STRUCT_CASES_TAC (Q.SPEC `q` num_CASES) THEN1
   REWRITE_TAC [NOT_LESS_0] THEN
 REPEAT STRIP_TAC THEN
 FULL_SIMP_TAC bool_ss [MULT,LESS_EQ_ADD_SUB,MOD_TIMES]);

val MOD_PLUS = store_thm ("MOD_PLUS",
 “!n. 0<n ==> !j k. (((j MOD n) + (k MOD n)) MOD n) = ((j+k) MOD n)”,
   let fun SUBS th = SUBST_OCCS_TAC [([2],th)]
   in
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC MOD_TIMES THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (“j:num”)) DIVISION THEN
   ASM_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
   PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
   IMP_RES_THEN (TRY o SUBS o SPEC (“k:num”)) DIVISION THEN
   ASM_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)]
   end);

val MOD_MOD = store_thm ("MOD_MOD",
 “!n. 0<n ==> (!k. (k MOD n) MOD n = (k MOD n))”,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC LESS_MOD THEN
   IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC (“k:num”)) DIVISION);

(* LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)

val LESS_DIV_EQ_ZERO = save_thm ("LESS_DIV_EQ_ZERO",
    GENL [(“r:num”),(“n:num”)] (DISCH_ALL (PURE_REWRITE_RULE[MULT,ADD]
    (SPEC (“0”)(UNDISCH_ALL (SPEC_ALL  DIV_MULT))))));

(* MULT_DIV = |- !n q. 0 < n ==> ((q * n) DIV n = q) *)

val MULT_DIV = save_thm ("MULT_DIV",
    GEN_ALL (PURE_REWRITE_RULE[ADD_0]
    (CONV_RULE RIGHT_IMP_FORALL_CONV
               (SPECL[(“n:num”),(“0”)] DIV_MULT))));

val ADD_DIV_ADD_DIV = store_thm ("ADD_DIV_ADD_DIV",
“!n. 0 < n ==> !x r. ((((x * n) + r) DIV n) = x + (r DIV n))”,
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC (“r < n”) THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC (“r:num”) DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME (“r = (q * n) + r'”))
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB]
      THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT]);

val ADD_DIV_RWT = store_thm ("ADD_DIV_RWT",
  “!n. 0 < n ==>
        !m p. (m MOD n = 0) \/ (p MOD n = 0) ==>
              ((m + p) DIV n = m DIV n + p DIV n)”,
  REPEAT STRIP_TAC THEN
  IMP_RES_THEN (ASSUME_TAC o GSYM) DIVISION THEN
  MATCH_MP_TAC DIV_UNIQUE THENL [
    Q.EXISTS_TAC `p MOD n` THEN
    ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, GSYM ADD_ASSOC, EQ_ADD_RCANCEL] THEN
    SIMP_TAC bool_ss [Once (GSYM ADD_0), SimpRHS] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `m MOD n` THEN
    ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    Q.SUBGOAL_THEN `p DIV n * n = p` SUBST1_TAC THENL [
       SIMP_TAC bool_ss [Once (GSYM ADD_0), SimpLHS] THEN
       FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [],
       ALL_TAC
    ] THEN
    Q.SUBGOAL_THEN `m DIV n * n + p + m MOD n = m DIV n * n + m MOD n + p`
                   (fn th => ASM_REWRITE_TAC [th]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC, EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_COMM
  ]);

val NOT_MULT_LESS_0 = prove(
    (“!m n. 0<m /\ 0<n ==> 0 < m*n”),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,LESS_0]);

val MOD_MULT_MOD = store_thm ("MOD_MULT_MOD",
“!m n. 0<n /\ 0<m  ==> !x. ((x MOD (n * m)) MOD n = x MOD n)”,
REPEAT GEN_TAC THEN DISCH_TAC
 THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NOT_MULT_LESS_0)) THEN GEN_TAC
 THEN POP_ASSUM(CHOOSE_TAC o (MATCH_MP(SPECL[“x:num”,“m * n”] DA)))
 THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
 THEN SUBST1_TAC (ASSUME(“x = (q * (n * m)) + r”))
 THEN POP_ASSUM (SUBST1_TAC o (SPEC (“q:num”)) o MATCH_MP MOD_MULT)
 THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
 THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
 THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
 THEN STRIP_ASSUME_TAC (ASSUME  (“0 < n /\ 0 < m”))
 THEN PURE_ONCE_REWRITE_TAC[UNDISCH_ALL(SPEC_ALL MOD_TIMES)]
 THEN REFL_TAC);

(* |- !q. q DIV (SUC 0) = q *)
val DIV_ONE = save_thm ("DIV_ONE",
    GEN_ALL (REWRITE_RULE[REWRITE_RULE[ONE] MULT_RIGHT_1]
    (MP (SPECL [(“SUC 0”), (“q:num”)] MULT_DIV)
        (SPEC (“0”) LESS_0))));

val DIV_1 = save_thm ("DIV_1", REWRITE_RULE [SYM ONE] DIV_ONE);

val DIVMOD_ID = store_thm ("DIVMOD_ID",
  “!n. 0 < n ==> (n DIV n = 1) /\ (n MOD n = 0)”,
  REPEAT STRIP_TAC THENL [
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
    MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]
  ]);

val Less_lemma = prove(
  “!m n. m<n ==> ?p. (n = m + p) /\ 0<p”,
  GEN_TAC THEN INDUCT_TAC THENL[
  REWRITE_TAC[NOT_LESS_0],
  REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
      EXISTS_TAC (“SUC 0”)
      THEN REWRITE_TAC[LESS_0,ADD_CLAUSES],
      RES_TAC THEN EXISTS_TAC (“SUC p”)
      THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_0]]]);

val Less_MULT_lemma = prove(
    (“!r m p. 0<p ==> r<m ==> r < p*m”),
    let val lem1 = MATCH_MP LESS_LESS_EQ_TRANS
       (CONJ (SPEC (“m:num”) LESS_SUC_REFL)
              (SPECL[(“SUC m”), (“p * (SUC m)”)] LESS_EQ_ADD))
   in
    GEN_TAC THEN REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN DISCH_TAC THEN REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
    THEN PURE_ONCE_REWRITE_TAC[MULT]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THENL[
      ACCEPT_TAC lem1,
      ACCEPT_TAC (MATCH_MP LESS_TRANS (CONJ (ASSUME (“r < m”)) lem1))]
   end);

val Less_MULT_ADD_lemma = prove(
  “!m n r r'. 0<m /\ 0<n /\ r<m /\ r'<n ==> r'*m + r < n*m”,
  REPEAT STRIP_TAC
  THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (“r<m”)))
  THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (“r'<n”)))
  THEN ASM_REWRITE_TAC[]
  THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
  THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
  THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_ADD_EQ]
  THEN SUBST1_TAC (SYM (ASSUME(“m = r + p”)))
  THEN IMP_RES_TAC Less_MULT_lemma);

val DIV_DIV_DIV_MULT = store_thm ("DIV_DIV_DIV_MULT",
   “!m n. 0<m /\ 0<n ==> !x. ((x DIV m) DIV n = x  DIV (m * n))”,
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN REPEAT STRIP_TAC
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
           (SPEC (“x:num”) (MATCH_MP DA (ASSUME (“0 < m”))))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
          (SPEC (“q:num”) (MATCH_MP DA (ASSUME (“0 < n”))))
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN ASSUME_TAC (MATCH_MP NOT_MULT_LESS_0
          (CONJ (ASSUME (“0 < n”)) (ASSUME (“0 < m”))))
    THEN CONV_TAC ((RAND_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
    THEN CONV_TAC SYM_CONV THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN FIRST_ASSUM (fn t => REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV t])
    THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO
    THEN IMP_RES_TAC Less_MULT_ADD_lemma);

local
   open prim_recTheory
in
   val SUC_PRE = store_thm ("SUC_PRE",
      “0 < m <=> (SUC (PRE m) = m)”,
      STRUCT_CASES_TAC (SPEC (“m:num”) num_CASES) THEN
      REWRITE_TAC [PRE,NOT_LESS_0,LESS_0,NOT_SUC])
end

val LESS_MONO_LEM =
GEN_ALL
  (REWRITE_RULE [ADD_CLAUSES]
    (SPECL (map Term [`0`, `y:num`, `x:num`])
      (ONCE_REWRITE_RULE[ADD_SYM]LESS_MONO_ADD)));

val DIV_LESS = store_thm ("DIV_LESS",
  “!n d. 0<n /\ 1<d ==> n DIV d < n”,
  REWRITE_TAC [ONE] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC prim_recTheory.SUC_LESS
  THEN CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC
         (SPEC(“n:num”) (UNDISCH(SPEC(“d:num”) DIVISION)))
  THEN RULE_ASSUM_TAC (REWRITE_RULE [ZERO_LESS_ADD])
  THEN MP_TAC (SPEC (“d:num”) ADD_DIV_ADD_DIV) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fn th => REWRITE_TAC [th])
  THEN MP_TAC (SPECL (map Term [`n MOD d`, `d:num`]) LESS_DIV_EQ_ZERO)
  THEN ASM_REWRITE_TAC []
  THEN DISCH_THEN (fn th => REWRITE_TAC [th,ADD_CLAUSES])
  THEN SUBGOAL_THEN (“?m. d = SUC m”) (CHOOSE_THEN SUBST_ALL_TAC) THENL
  [EXISTS_TAC (“PRE d”) THEN IMP_RES_TAC SUC_PRE THEN ASM_REWRITE_TAC[],
   REWRITE_TAC [MULT_CLAUSES,GSYM ADD_ASSOC]
    THEN MATCH_MP_TAC LESS_MONO_LEM
    THEN PAT_ASSUM (“x \/ y”) MP_TAC
    THEN REWRITE_TAC[ZERO_LESS_ADD,ZERO_LESS_MULT] THEN STRIP_TAC THENL
    [DISJ1_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[LESS_MONO_EQ]), ALL_TAC]
    THEN ASM_REWRITE_TAC[]]);

val MOD_LESS = Q.store_thm ("MOD_LESS",
 `!m n. 0 < n ==> m MOD n < n`,
 METIS_TAC [DIVISION]);

val ADD_MODULUS = Q.store_thm ("ADD_MODULUS",
`(!n x. 0 < n ==> ((x + n) MOD n = x MOD n)) /\
 (!n x. 0 < n ==> ((n + x) MOD n = x MOD n))`,
 METIS_TAC [ADD_SYM,MOD_PLUS,DIVMOD_ID,MOD_MOD,ADD_CLAUSES]);

val ADD_MODULUS_LEFT = save_thm ("ADD_MODULUS_LEFT",CONJUNCT1 ADD_MODULUS);
val ADD_MODULUS_RIGHT = save_thm ("ADD_MODULUS_RIGHT",CONJUNCT2 ADD_MODULUS);

val DIV_P = store_thm ("DIV_P",
  “!P p q. 0 < q ==>
            (P (p DIV q) = ?k r. (p = k * q + r) /\ r < q /\ P k)”,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    MAP_EVERY Q.EXISTS_TAC [`p DIV q`, `p MOD q`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION THEN
    FIRST_ASSUM ACCEPT_TAC,
    Q.SUBGOAL_THEN `p DIV q = k` (fn th => SUBST1_TAC th THEN
                                           FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `r` THEN ASM_REWRITE_TAC []
  ]);

val DIV_P_UNIV = store_thm ("DIV_P_UNIV",
  “!P m n. 0 < n ==> (P (m DIV n) = !q r. (m = q * n + r) /\ r < n ==> P q)”,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Q_TAC SUFF_TAC `m DIV n = q`
          THEN1 (DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC []) THEN
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `r` THEN ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `m MOD n` THEN
    MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC []
  ]);

val MOD_P = store_thm ("MOD_P",
  “!P p q. 0 < q ==>
            (P (p MOD q) = ?k r. (p = k * q + r) /\ r < q /\ P r)”,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    MAP_EVERY Q.EXISTS_TAC [`p DIV q`, `p MOD q`] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION THEN
    FIRST_ASSUM ACCEPT_TAC,
    Q.SUBGOAL_THEN `p MOD q = r` (fn th => SUBST1_TAC th THEN
                                           FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `k` THEN ASM_REWRITE_TAC []
  ]);

val MOD_P_UNIV = store_thm ("MOD_P_UNIV",
  “!P m n. 0 < n ==>
            (P (m MOD n) = !q r. (m = q * n + r) /\ r < n ==> P r)”,
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
  val v = mk_var(s, “:num”)
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

val MOD_TIMES2 = store_thm ("MOD_TIMES2",
  “!n. 0 < n ==>
        !j k. (j MOD n * k MOD n) MOD n = (j * k) MOD n”,
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

val MOD_COMMON_FACTOR = store_thm ("MOD_COMMON_FACTOR",
  “!n p q. 0 < n /\ 0 < q ==> (n * (p MOD q) = (n * p) MOD (n * q))”,
  REPEAT STRIP_TAC THEN Q.SPEC_THEN `q` MP_TAC DIVISION THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN (Q.SPEC_THEN `p` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `u = p DIV q` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `v = p MOD q` THEN POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
  move_var_left "u" THEN
  ASM_SIMP_TAC bool_ss [MOD_TIMES, LESS_MULT2] THEN
  SUFF_TAC “n * v < n * q” THENL [mesonLib.MESON_TAC [LESS_MOD],
                                    ALL_TAC] THEN
  SUFF_TAC “?m. n = SUC m” THENL [
    STRIP_TAC THEN ASM_REWRITE_TAC [LESS_MULT_MONO],
    mesonLib.ASM_MESON_TAC [LESS_REFL, num_CASES]
  ]);

Theorem X_MOD_Y_EQ_X:
  !x y. 0 < y ==> ((x MOD y = x) <=> x < y)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    mesonLib.ASM_MESON_TAC [DIVISION],
    STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN
    Q.EXISTS_TAC `0` THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]
  ]
QED

val DIV_LE_MONOTONE = store_thm ("DIV_LE_MONOTONE",
  “!n x y. 0 < n /\ x <= y ==> x DIV n <= y DIV n”,
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

Theorem LE_LT1:
  !x y. x <= y <=> x < y + 1
Proof
  REWRITE_TAC [LESS_OR_EQ, GSYM ADD1,
               IMP_ANTISYM_RULE (SPEC_ALL prim_recTheory.LESS_LEMMA1)
                                (SPEC_ALL prim_recTheory.LESS_LEMMA2)] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
QED

Theorem X_LE_DIV:
  !x y z. 0 < z ==> (x <= y DIV z <=> x * z <= y)
Proof
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
  ]
QED

Theorem X_LT_DIV:
  !x y z. 0 < z ==> (x < y DIV z <=> (x + 1) * z <= y)
Proof
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
  ]
QED

Theorem DIV_LT_X:
  !x y z. 0 < z ==> (y DIV z < x <=> y < x * z)
Proof
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM NOT_LESS_EQUAL] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC X_LE_DIV THEN
  ASM_REWRITE_TAC []
QED

Theorem DIV_LE_X:
  !x y z. 0 < z ==> (y DIV z <= x <=> y < (x + 1) * z)
Proof
  REPEAT STRIP_TAC THEN
  CONV_TAC (FORK_CONV (REWR_CONV (GSYM NOT_LESS),
                       REWR_CONV (GSYM NOT_LESS_EQUAL))) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC X_LT_DIV THEN
  ASM_REWRITE_TAC []
QED

Theorem DIV_EQ_X:
  !x y z. 0 < z ==> ((y DIV z = x) <=> x * z <= y /\ y < SUC x * z)
Proof
  SIMP_TAC bool_ss [EQ_LESS_EQ,DIV_LE_X,X_LE_DIV,GSYM ADD1,
    AC CONJ_COMM CONJ_ASSOC]
QED

Theorem EQ_ADD_LCANCEL'[local]:
  x + y = y + z <=> x = z
Proof
  METIS_TAC[ADD_COMM, EQ_ADD_LCANCEL]
QED

(* will work well under standard ARITH_ss type normalisation which makes
   addition right-associative, and will put the numeral/coefficient first in
   multiplications *)
Theorem DIV_NUMERAL_THM[simp]:
  (NUMERAL (BIT1 n) * x) DIV NUMERAL (BIT1 n) = x /\
  (NUMERAL (BIT2 n) * x) DIV NUMERAL (BIT2 n) = x /\
  (NUMERAL (BIT1 n) * x + y) DIV NUMERAL (BIT1 n) = x + y DIV NUMERAL (BIT1 n)/\
  (NUMERAL (BIT2 n) * x + y) DIV NUMERAL (BIT2 n) = x + y DIV NUMERAL (BIT2 n)/\
  (y + NUMERAL (BIT1 n) * x) DIV NUMERAL (BIT1 n) = x + y DIV NUMERAL (BIT1 n)/\
  (y + NUMERAL (BIT2 n) * x) DIV NUMERAL (BIT2 n) = x + y DIV NUMERAL (BIT2 n)
Proof
  Q.ABBREV_TAC ‘N1 = NUMERAL(BIT1 n)’ >>
  Q.ABBREV_TAC ‘N2 = NUMERAL(BIT2 n)’ >>
  ‘0 < N1 /\ 0 < N2’
    by (MAP_EVERY Q.UNABBREV_TAC [‘N1’, ‘N2’] >>
        REWRITE_TAC[NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, LESS_0]) >>
  ‘!x. x * N1 = N1 * x /\ x * N2 = N2 * x’
    by REWRITE_TAC[MULT_COMM |> SPEC_ALL |> EQT_INTRO] >>
  simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, SF CONJ_ss] >>
  rpt conj_tac >> irule DIV_UNIQUE
  >- (first_assum $ irule_at Any >> ASM_REWRITE_TAC[ADD_CLAUSES])
  >- (first_assum $ irule_at Any >> ASM_REWRITE_TAC[ADD_CLAUSES])
  >- (ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, EQ_ADD_LCANCEL', GSYM ADD_ASSOC] >>
      rpt (dxrule_then (mp_tac o GSYM) DIVISION) >>
      ASM_REWRITE_TAC[] >>
      rpt (disch_then (strip_assume_tac o CONV_RULE FORALL_AND_CONV)) >>
      first_assum $ irule_at Any >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
      first_assum $ irule_at Any)
  >- (ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, EQ_ADD_LCANCEL', GSYM ADD_ASSOC] >>
      rpt (dxrule_then (mp_tac o GSYM) DIVISION) >>
      ASM_REWRITE_TAC[] >>
      rpt (disch_then (strip_assume_tac o CONV_RULE FORALL_AND_CONV)) >>
      first_assum $ irule_at Any >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
      first_assum $ irule_at Any)
QED

val DIV_MOD_MOD_DIV = store_thm ("DIV_MOD_MOD_DIV",
  “!m n k. 0 < n /\ 0 < k ==> ((m DIV n) MOD k = (m MOD (n * k)) DIV n)”,
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
Theorem MULT_EQ_DIV:
  0 < x ==> ((x * y = z) <=> (y = z DIV x) /\ (z MOD x = 0))
Proof
  STRIP_TAC THEN EQ_TAC THENL [
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    ONCE_REWRITE_TAC [MULT_COMM] THEN
    ASM_SIMP_TAC bool_ss [MOD_EQ_0, MULT_DIV],
    Q.SPEC_THEN `x` MP_TAC DIVISION THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (Q.SPEC_THEN `z` STRIP_ASSUME_TAC) THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC bool_ss [ADD_CLAUSES, MULT_COMM] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN FIRST_ASSUM ACCEPT_TAC
  ]
QED

(* as they are here *)
Theorem NUMERAL_MULT_EQ_DIV:
  ((NUMERAL (BIT1 x) * y = NUMERAL z) <=>
       (y = NUMERAL z DIV NUMERAL (BIT1 x)) /\
       (NUMERAL z MOD NUMERAL(BIT1 x) = 0)) /\
    ((NUMERAL (BIT2 x) * y = NUMERAL z) <=>
       (y = NUMERAL z DIV NUMERAL (BIT2 x)) /\
       (NUMERAL z MOD NUMERAL(BIT2 x) = 0))
Proof
  CONJ_TAC THEN MATCH_MP_TAC MULT_EQ_DIV THEN
  REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, LESS_0]
QED

val MOD_EQ_0_DIVISOR = Q.store_thm ("MOD_EQ_0_DIVISOR",
`0 < n ==> ((k MOD n = 0) = (?d. k = d * n))`,
DISCH_TAC THEN
EQ_TAC THEN1 (
  DISCH_TAC THEN
  EXISTS_TAC “k DIV n” THEN
  MATCH_MP_TAC EQ_SYM THEN
  SRW_TAC [][Once MULT_SYM] THEN
  MATCH_MP_TAC (MP_CANON (DISCH_ALL (#2(EQ_IMP_RULE (UNDISCH MULT_EQ_DIV))))) THEN
  SRW_TAC [][] ) THEN
SRW_TAC [][] THEN SRW_TAC [][MOD_EQ_0])

val MOD_SUC = Q.store_thm ("MOD_SUC",
`0 < y /\ (SUC x <> (SUC (x DIV y)) * y) ==> ((SUC x) MOD y = SUC (x MOD y))`,
STRIP_TAC THEN
MATCH_MP_TAC MOD_UNIQUE THEN
Q.EXISTS_TAC `x DIV y` THEN
`x = x DIV y * y + x MOD y` by PROVE_TAC [DIVISION] THEN
`x MOD y < y` by PROVE_TAC [MOD_LESS] THEN
FULL_SIMP_TAC bool_ss [prim_recTheory.INV_SUC_EQ,ADD_CLAUSES,MULT_CLAUSES] THEN
MATCH_MP_TAC LESS_NOT_SUC THEN
CONJ_TAC THEN1 FIRST_ASSUM ACCEPT_TAC THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`SUC x = SUC (x DIV y * y + x MOD y)` by (
  AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC ) THEN
FULL_SIMP_TAC bool_ss [ADD_SUC] THEN
PROVE_TAC [] );

val MOD_SUC_IFF = Q.store_thm ("MOD_SUC_IFF",
   `0 < y ==> ((SUC x MOD y = SUC (x MOD y)) <=> (SUC x <> SUC (x DIV y) * y))`,
   PROVE_TAC [MOD_SUC,SUC_NOT,MOD_EQ_0])

val ONE_MOD = Q.store_thm ("ONE_MOD",
   `1 < n ==> (1 MOD n = 1)`,
   STRIP_TAC THEN
   `0 < n` by (
     MATCH_MP_TAC LESS_TRANS THEN
     EXISTS_TAC “1” THEN
     SRW_TAC [][LESS_SUC_REFL,ONE] ) THEN
   SUFF_TAC “SUC 0 MOD n = SUC (0 MOD n)” THEN1
     SRW_TAC [][ZERO_MOD,ONE] THEN
   MATCH_MP_TAC MOD_SUC THEN
   SRW_TAC [][ZERO_DIV,MULT,ADD,LESS_NOT_EQ,GSYM ONE])

val ONE_MOD_IFF = Q.store_thm ("ONE_MOD_IFF",
   `1 < n <=> 0 < n /\ (1 MOD n = 1)`,
   EQ_TAC THEN1 (
     SRW_TAC [][ONE_MOD] THEN
     MATCH_MP_TAC LESS_TRANS THEN
     EXISTS_TAC “1” THEN
     SRW_TAC [][LESS_SUC_REFL,ONE] ) THEN
   STRUCT_CASES_TAC (SPEC “n:num” num_CASES) THEN1 (
     SIMP_TAC bool_ss [LESS_REFL] ) THEN
   SIMP_TAC bool_ss [ONE] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC LESS_MONO THEN
   Q.MATCH_RENAME_TAC `0 < m` THEN
   FULL_STRUCT_CASES_TAC (SPEC “m:num” num_CASES) THEN1 (
     FULL_SIMP_TAC bool_ss [MOD_ONE,SUC_NOT] ) THEN
   SIMP_TAC bool_ss [LESS_0])

val MOD_LESS_EQ = Q.store_thm ("MOD_LESS_EQ",
   `0 < y ==> x MOD y <= x`,
   STRIP_TAC THEN
   Cases_on `x < y` THEN1 (
     MATCH_MP_TAC (snd (EQ_IMP_RULE (SPEC_ALL LESS_OR_EQ))) THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC LESS_MOD THEN
     POP_ASSUM ACCEPT_TAC ) THEN
   MATCH_MP_TAC LESS_EQ_TRANS THEN
   Q.EXISTS_TAC `y` THEN
   CONJ_TAC THEN1 (
     MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN
     MATCH_MP_TAC MOD_LESS THEN
     FIRST_ASSUM ACCEPT_TAC ) THEN
   IMP_RES_TAC NOT_LESS)

val MOD_LIFT_PLUS = Q.store_thm ("MOD_LIFT_PLUS",
   `0 < n /\ k < n - x MOD n ==> ((x + k) MOD n = x MOD n + k)`,
   Q.ID_SPEC_TAC `k` THEN INDUCT_TAC THEN1 (
     SIMP_TAC bool_ss [ADD_0] ) THEN
   STRIP_TAC THEN
   `x + SUC k = SUC (x + k)` by (
     SIMP_TAC bool_ss [ADD_CLAUSES] ) THEN
   `k < n - x MOD n` by (
     MATCH_MP_TAC prim_recTheory.SUC_LESS THEN
     FIRST_ASSUM ACCEPT_TAC ) THEN
   FULL_SIMP_TAC bool_ss [] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   Q.EXISTS_TAC `SUC (x MOD n + k)` THEN
   CONJ_TAC THEN1 (
     MATCH_MP_TAC EQ_TRANS THEN
     Q.EXISTS_TAC `SUC ((x + k) MOD n)` THEN
     CONJ_TAC THEN1 (
       MATCH_MP_TAC MOD_SUC THEN
       CONJ_TAC THEN1 FIRST_ASSUM ACCEPT_TAC THEN
       FULL_SIMP_TAC bool_ss [ADD_SYM,ADD,SUB_LEFT_LESS,MULT_CLAUSES] THEN
       `SUC ((k + x) MOD n + (k + x) DIV n * n) < n + (k + x) DIV n * n`
         by PROVE_TAC [LESS_MONO_ADD,ADD_SUC,ADD_SYM] THEN
       PROVE_TAC [DIVISION,ADD_SYM,LESS_REFL]) THEN
     AP_TERM_TAC THEN
     FIRST_ASSUM ACCEPT_TAC) THEN
   SIMP_TAC bool_ss [ADD_SUC])

val MOD_LIFT_PLUS_IFF = Q.store_thm ("MOD_LIFT_PLUS_IFF",
   `0 < n ==> (((x + k) MOD n = x MOD n + k) = (k < n - x MOD n))`,
   PROVE_TAC [SUB_LEFT_LESS,ADD_SYM,MOD_LESS,MOD_LIFT_PLUS])

Theorem DIV_0_IMP_LT:
  !b n. 1 < b /\ (n DIV b = 0) ==> n < b
Proof
  REPEAT STRIP_TAC \\ SPOSE_NOT_THEN ASSUME_TAC
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS]
  \\ IMP_RES_TAC LESS_EQUAL_ADD
  \\ `0 < b` by (
       MATCH_MP_TAC LESS_TRANS THEN
       EXISTS_TAC “1” THEN
       SRW_TAC [][LESS_SUC_REFL,ONE] )
  \\ IMP_RES_TAC ADD_DIV_ADD_DIV
  \\ POP_ASSUM (Q.SPECL_THEN [`1`,`p`] (ASSUME_TAC o SIMP_RULE bool_ss []))
  \\ FULL_SIMP_TAC bool_ss [MULT_CLAUSES, ADD_EQ_0, ONE, SUC_NOT]
QED

Theorem DIV_EQ_0:
  1 < b ==> ((n DIV b = 0) = (n < b))
Proof
  PROVE_TAC[DIV_0_IMP_LT, LESS_DIV_EQ_ZERO]
QED

(* NOTE: in HOL-Light the original statement was:

  |- P (m DIV n) (m MOD n) <=>
       (!q r. n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n ==> P q r)

  where ‘m DIV 0 = 0’ by definition. In HOL4, ‘m DIV 0’ is unspecified, thus
  only the following alternative statements is possible:
 *)
Theorem DIVMOD_ELIM_THM :
    !P m n. 0 < n ==>
           (P (m DIV n) (m MOD n) <=> !q r. m = q * n + r /\ r < n ==> P q r)
Proof
    rpt STRIP_TAC
 >> FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION)
 >> PROVE_TAC[DIVMOD_UNIQ]
QED

Theorem DIVMOD_ELIM_THM' :
    !P m n. 0 < n ==>
           (P (m DIV n) (m MOD n) <=> ?q r. m = q * n + r /\ r < n /\ P q r)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘\x y. ~P x y’,‘m’,‘n’] DIVMOD_ELIM_THM)
 >> PROVE_TAC []
QED

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas (from transc.ml)                               *)
(* ------------------------------------------------------------------------ *)

Theorem MULT_DIV_2 :
    !n. (2 * n) DIV 2 = n
Proof
  GEN_TAC THEN REWRITE_TAC[GSYM DIV2_def, DIV2_DOUBLE]
QED

Theorem EVEN_DIV_2 : (* was: EVEN_DIV2 *)
    !n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))
Proof
  GEN_TAC THEN REWRITE_TAC[GSYM ODD_EVEN, ODD_EXISTS] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[SUC_SUB1] THEN REWRITE_TAC[ADD1, GSYM ADD_ASSOC] THEN
  SUBST1_TAC(SYM (Q.SPEC ‘1’ TIMES2)) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB, MULT_DIV_2]
QED

(* ----------------------------------------------------------------------
    Some additional theorems (nothing to do with DIV and MOD)
   ---------------------------------------------------------------------- *)

val num_case_cong =
  save_thm ("num_case_cong", Prim_rec.case_cong_thm num_CASES num_case_def);

val SUC_ELIM_THM = store_thm ("SUC_ELIM_THM",
  (“!P. (!n. P (SUC n) n) = (!n. (0 < n ==> P n (n-1)))”),
  GEN_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (“n-1”)) THEN
      SIMP_TAC bool_ss [SUB_LEFT_SUC, ONE, SUB_MONO_EQ, SUB_0,
                        GSYM NOT_LESS] THEN
      COND_CASES_TAC THENL [
        STRIP_ASSUME_TAC (SPECL [“n:num”, “SUC 0”] LESS_LESS_CASES)
        THENL [
          FULL_SIMP_TAC bool_ss [],
          IMP_RES_TAC LESS_LESS_SUC
        ],
        REWRITE_TAC []
      ],
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (“n+1”)) THEN
      SIMP_TAC bool_ss [GSYM ADD1, SUC_SUB1, LESS_0]
    ]);

val SUC_ELIM_NUMERALS = store_thm ("SUC_ELIM_NUMERALS",
  “!f g. (!n. g (SUC n) = f n (SUC n)) <=>
          (!n. g (NUMERAL (BIT1 n)) =
               f (NUMERAL (BIT1 n) - 1) (NUMERAL (BIT1 n))) /\
          (!n. g (NUMERAL (BIT2 n)) =
               f (NUMERAL (BIT1 n)) (NUMERAL (BIT2 n)))”,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC bool_ss [NUMERAL_DEF, BIT1, BIT2, ALT_ZERO,
                    ADD_CLAUSES, SUB_MONO_EQ, SUB_0] THEN
  REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `n` STRIP_ASSUME_TAC EVEN_OR_ODD THEN
  POP_ASSUM (Q.X_CHOOSE_THEN `m` SUBST_ALL_TAC o
             REWRITE_RULE [EVEN_EXISTS, ODD_EXISTS, TIMES2]) THEN
  ASM_REWRITE_TAC []);

val ADD_SUBR2 = prove(
  “!m n. m - (m + n) = 0”,
  REWRITE_TAC [SUB_EQ_0, LESS_EQ_ADD]);

val SUB_ELIM_THM = store_thm ("SUB_ELIM_THM",
  “P (a - b) = !d. ((b = a + d) ==> P 0) /\ ((a = b + d) ==> P d)”,
  DISJ_CASES_TAC(SPECL [“a:num”, “b:num”] LESS_EQ_CASES) THEN
  FIRST_ASSUM(X_CHOOSE_TAC (“e:num”) o REWRITE_RULE[LESS_EQ_EXISTS]) THEN
  ASM_REWRITE_TAC[ADD_SUB, ONCE_REWRITE_RULE [ADD_SYM] ADD_SUB, ADD_SUBR2] THEN
  REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ] THEN
  CONV_TAC (DEPTH_CONV FORALL_AND_CONV) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM ADD_ASSOC, ADD_INV_0_EQ, ADD_EQ_0] THENL
   [EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fn th => MATCH_MP_TAC th THEN EXISTS_TAC (“e:num”)),
    EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THEN GEN_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC),
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)]] THEN
  ASM_REWRITE_TAC[]);

(* |- P (a - b) <=> (?d. (b = a + d) /\ P 0) \/ (?d. (a = b + d) /\ P d) *)
Theorem SUB_ELIM_THM_EXISTS =
  SUB_ELIM_THM |> AP_TERM “$~”
               |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [EXISTS_OR_THM]))
               |> Q.INST [‘P’ |-> ‘\n. ~P n’]
               |> SIMP_RULE bool_ss []

(* some HOL-Light compatible theorem names *)
Theorem LTE_CASES = LESS_CASES
Theorem NOT_LT    = NOT_LESS
Theorem NOT_LE    = NOT_LESS_EQUAL
Theorem LT_IMP_LE = LESS_IMP_LESS_OR_EQ
Theorem LE_ADD    = LESS_EQ_ADD
Theorem LE_EXISTS = LESS_EQ_EXISTS

(* This is HOL-Light's SUB_ELIM_THM, with a single ‘P d’ at rhs. *)
Theorem SUB_ELIM_THM' :
   P (a - b) <=> (!d. a = b + d \/ a < b /\ d = 0 ==> P d)
Proof
  DISJ_CASES_TAC(Q.SPECL [‘a’, ‘b’] LTE_CASES)
  >- (ASM_MESON_TAC[NOT_LT, SUB_EQ_0, LT_IMP_LE, LE_ADD]) \\
  FIRST_ASSUM(X_CHOOSE_THEN “e:num” SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) \\
  SIMP_TAC bool_ss [ADD_SUB2, GSYM NOT_LE, LE_ADD, EQ_ADD_LCANCEL]
QED

(* HOL-Light compatible *)
Theorem SUB_ELIM_THM_EXISTS' :
   P (a - b) <=> ?d. (a = b + d \/ a < b /\ d = 0) /\ P d
Proof
    MP_TAC(INST [“P:num->bool” |-> “\x:num. ~P x”] SUB_ELIM_THM')
 >> MESON_TAC[]
QED

val PRE_ELIM_THM = store_thm ("PRE_ELIM_THM",
  “P (PRE n) = !m. ((n = 0) ==> P 0) /\ ((n = SUC m) ==> P m)”,
  SPEC_TAC(“n:num”,“n:num”) THEN INDUCT_TAC THEN
  REWRITE_TAC[NOT_SUC, INV_SUC_EQ, GSYM NOT_SUC, PRE] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC]);

val SUC_INJ = INV_SUC_EQ;

Theorem PRE_ELIM_THM' :
   P (PRE n) <=> !m. n = SUC m \/ m = 0 /\ n = 0 ==> P m
Proof
  Q.SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  SIMP_TAC bool_ss [NOT_SUC, SUC_INJ, PRE]
QED

(* HOL-Light compatible *)
Theorem PRE_ELIM_THM_EXISTS :
   P (PRE n) <=> (?m. (n = SUC m \/ m = 0 /\ n = 0) /\ P m)
Proof
    MP_TAC(INST [“P:num->bool” |-> “\x:num. ~P x”] PRE_ELIM_THM')
 >> MESON_TAC []
QED

val _ = print "Additional properties of EXP\n"

val MULT_INCREASES = store_thm ("MULT_INCREASES",
  “!m n. 1 < m /\ 0 < n ==> SUC n <= m * n”,
  INDUCT_TAC THENL [
    REWRITE_TAC [NOT_LESS_0],
    REWRITE_TAC [MULT, GSYM LESS_EQ] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [ADD_COMM] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
    REWRITE_TAC [MULT_EQ_0] THEN STRIP_TAC THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ONE, LESS_REFL]) THEN
    FIRST_ASSUM ACCEPT_TAC
  ]);

val EXP_ALWAYS_BIG_ENOUGH = store_thm ("EXP_ALWAYS_BIG_ENOUGH",
  “!b. 1 < b ==> !n. ?m. n <= b EXP m”,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC [ZERO_LESS_EQ],
    POP_ASSUM STRIP_ASSUME_TAC THEN
    Q.ASM_CASES_TAC `SUC n <= b EXP m` THENL [
      mesonLib.ASM_MESON_TAC [],
      SUBGOAL_THEN “n = b EXP m” STRIP_ASSUME_TAC THENL [
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

Theorem EXP_EQ_0[simp]:
  !n m. (n EXP m = 0) <=> (n = 0) /\ (0 < m)
Proof
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `m` num_CASES) THEN
  REWRITE_TAC [EXP, GSYM NOT_ZERO_LT_ZERO, ONE, NOT_SUC, MULT_EQ_0] THEN
  EQ_TAC THEN STRIP_TAC THENL [
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `n` num_CASES) THEN
    REWRITE_TAC [] THEN IMP_RES_TAC NOT_EXP_0,
    ASM_REWRITE_TAC []
  ]
QED

Theorem EXP_LT_1[simp] =
        REWRITE_CONV [LT1_EQ0, EXP_EQ_0] “m EXP n < 1”

Theorem ZERO_LT_EXP[simp]:
  0 < x EXP y <=> 0 < x \/ (y = 0)
Proof METIS_TAC [NOT_ZERO_LT_ZERO, EXP_EQ_0]
QED

(* Theorem: m <> 0 ==> m ** n <> 0 *)
(* Proof: by EXP_EQ_0 *)
val EXP_NONZERO = store_thm(
  "EXP_NONZERO",
  ``!m n. m <> 0 ==> m ** n <> 0``,
  metis_tac[EXP_EQ_0]);

(* Theorem: 0 < m ==> 0 < m ** n *)
(* Proof: by EXP_NONZERO *)
val EXP_POS = store_thm(
  "EXP_POS",
  ``!m n. 0 < m ==> 0 < m ** n``,
  rw[EXP_NONZERO]);

Theorem ONE_LE_EXP[simp]:
  1 <= x EXP y <=> 0 < x \/ y = 0
Proof
  REWRITE_TAC[LESS_EQ_IFF_LESS_SUC, ONE, LESS_MONO_EQ, ZERO_LT_EXP]
QED

(* Theorem: n ** 0 = 1 *)
(* Proof: by EXP *)
val EXP_0 = store_thm(
  "EXP_0",
  ``!n. n ** 0 = 1``,
  rw_tac std_ss[EXP]);

Theorem EXP_1[simp]:
  !n. (1 EXP n = 1) /\ (n EXP 1 = n)
Proof
  CONV_TAC (QUANT_CONV (FORK_CONV (ALL_CONV, REWRITE_CONV [ONE]))) THEN
  REWRITE_TAC [EXP, MULT_CLAUSES] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_EQ_1, EXP]
QED

(* Theorem: n ** 2 = n * n *)
(* Proof:
   n ** 2 = n * (n ** 1) = n * (n * (n ** 0)) = n * (n * 1) = n * n
   or n ** 2 = n * (n ** 1) = n * n  by EXP_1:  !n. (1 ** n = 1) /\ (n ** 1 = n)
*)
val EXP_2 = store_thm(
  "EXP_2",
  ``!n. n ** 2 = n * n``,
  metis_tac[EXP, TWO, EXP_1]);

Theorem EXP_EQ_1[simp]:
  !n m. (n EXP m = 1) <=> (n = 1) \/ (m = 0)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `m` THEN INDUCT_TAC THEN
    REWRITE_TAC [EXP, MULT_EQ_1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [EXP_1],
    ASM_REWRITE_TAC [EXP]
  ]
QED

Theorem EXP_EQ_BASE[simp]:
  !n m. n EXP m = n <=> m = 1 \/ n = 0 /\ 0 < m \/ n = 1
Proof
  Cases_on ‘m’ >>
  REWRITE_TAC[EXP, ONE, SUC_NOT, LESS_REFL, INV_SUC_EQ, LESS_0, MULT_EQ_ID] >| [
    GEN_TAC >> EQ_TAC >> DISCH_THEN (ACCEPT_TAC o SYM),
    REWRITE_TAC [GSYM ONE, EXP_EQ_1] THEN GEN_TAC THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]
  ]
QED

(* theorems about exponentiation where the base is held constant *)
val expbase_le_mono = prove(
  “1 < b /\ m <= n ==> b ** m <= b ** n”,
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `?q. n = m + q` STRIP_ASSUME_TAC THEN1
    METIS_TAC [LESS_EQUAL_ADD] THEN
  SRW_TAC [][EXP_ADD] THEN
  SRW_TAC [][Once (GSYM MULT_RIGHT_1), SimpLHS] THEN
  ASM_REWRITE_TAC [LE_MULT_LCANCEL, EXP_EQ_0, ONE, GSYM LESS_EQ,
                   ZERO_LT_EXP] THEN
  METIS_TAC [ONE, LESS_TRANS, LESS_0])

val expbase_lt_mono = prove(
  “1 < b /\ m < n ==> b ** m < b ** n”,
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `?q. n = m + q` STRIP_ASSUME_TAC THEN1
    METIS_TAC [LESS_ADD, ADD_COMM] THEN
  SRW_TAC [][EXP_ADD] THEN
  SRW_TAC [][Once (GSYM MULT_RIGHT_1), SimpLHS] THEN
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

Theorem EXP_BASE_LE_MONO:
  !b. 1 < b ==> !n m. b ** m <= b ** n <=> m <= n
Proof METIS_TAC [expbase_lt_mono, expbase_le_mono, NOT_LESS_EQUAL]
QED
Theorem EXP_BASE_LT_MONO:
  !b. 1 < b ==> !n m. b ** m < b ** n <=> m < n
Proof METIS_TAC [expbase_lt_mono, expbase_le_mono, NOT_LESS]
QED

val EXP_BASE_INJECTIVE = store_thm ("EXP_BASE_INJECTIVE",
  “!b. 1 < b ==> !n m. (b EXP n = b EXP m) = (n = m)”,
  METIS_TAC [LESS_EQUAL_ANTISYM, LESS_EQ_REFL, EXP_BASE_LE_MONO]);

val EXP_BASE_LEQ_MONO_IMP = store_thm ("EXP_BASE_LEQ_MONO_IMP",
  “!n m b. 0 < b /\ m <= n ==> b ** m <= b ** n”,
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC LESS_EQUAL_ADD THEN ASM_REWRITE_TAC [EXP_ADD] THEN
  SRW_TAC [][Once (GSYM MULT_RIGHT_1), SimpLHS] THEN
  ASM_REWRITE_TAC [LE_MULT_LCANCEL, EXP_EQ_0, ONE, GSYM LESS_EQ] THEN
  FULL_SIMP_TAC bool_ss [GSYM NOT_ZERO_LT_ZERO, EXP_EQ_0]);

(*  |- m <= n ==> SUC b ** m <= SUC b ** n *)
val EXP_BASE_LEQ_MONO_SUC_IMP = save_thm (
  "EXP_BASE_LEQ_MONO_SUC_IMP",
  (REWRITE_RULE [LESS_0] o Q.INST [`b` |-> `SUC b`] o SPEC_ALL)
  EXP_BASE_LEQ_MONO_IMP);

val EXP_BASE_LE_IFF = store_thm ("EXP_BASE_LE_IFF",
  “b ** m <= b ** n <=>
      (b = 0) /\ (n = 0) \/ (b = 0) /\ 0 < m \/ (b = 1) \/ 1 < b /\ m <= n”,
  Q.SPEC_THEN `b` STRUCT_CASES_TAC num_CASES THEN
  ASM_REWRITE_TAC [NOT_SUC, NOT_LESS_0] THENL [
    Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES THEN
    ASM_REWRITE_TAC [LESS_REFL, EXP, ONE, SUC_NOT] THENL [
      Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES THEN
      ASM_REWRITE_TAC [NOT_SUC, EXP, ONE, LESS_EQ_REFL, MULT_CLAUSES,
                       NOT_SUC_LESS_EQ_0],
      ASM_REWRITE_TAC [LESS_0, MULT_CLAUSES, ZERO_LESS_EQ]
    ],
    EQ_TAC THENL [
      ASM_CASES_TAC “1 < SUC n'” THEN SRW_TAC [][EXP_BASE_LE_MONO] THEN
      FULL_SIMP_TAC (srw_ss()) [ONE, LESS_MONO_EQ, INV_SUC_EQ,
                                GSYM NOT_ZERO_LT_ZERO],
      STRIP_TAC THEN ASM_REWRITE_TAC [EXP_1, LESS_EQ_REFL] THEN
      MATCH_MP_TAC EXP_BASE_LEQ_MONO_IMP THEN ASM_REWRITE_TAC [LESS_0]
    ]
  ]);

val X_LE_X_EXP = store_thm ("X_LE_X_EXP",
  “0 < n ==> x <= x ** n”,
  Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [EXP, LESS_REFL, LESS_0] THEN
  Q.SPEC_THEN `x` STRUCT_CASES_TAC num_CASES THEN
  REWRITE_TAC [ZERO_LESS_EQ, LE_MULT_CANCEL_LBARE, NOT_SUC, ZERO_LT_EXP,
               LESS_0]);

Theorem X_LE_X_SQUARED[simp]:
  x <= x ** 2
Proof
  irule X_LE_X_EXP >> REWRITE_TAC[TWO, prim_recTheory.LESS_0]
QED

Theorem X_LT_X_SQUARED[simp]:
  x < x ** 2 <=> 1 < x
Proof
  REWRITE_TAC[EXP,TWO,EXP_1,LT_MULT_CANCEL_LBARE] >> EQ_TAC >> STRIP_TAC >>
  ASM_REWRITE_TAC[] >> irule LESS_TRANS >> Q.EXISTS_TAC ‘1’ >>
  ASM_REWRITE_TAC[] >> ASM_REWRITE_TAC[ONE,LESS_0]
QED

val X_LT_EXP_X = Q.store_thm ("X_LT_EXP_X",
   `1 < b ==> x < b ** x`,
   Q.ID_SPEC_TAC `x` THEN INDUCT_TAC THEN1
     SIMP_TAC bool_ss [LESS_0,EXP,ONE] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC bool_ss [] THEN
   Cases_on `x = 0` THEN1
     ASM_SIMP_TAC bool_ss [EXP,MULT_RIGHT_1,SYM ONE] THEN
   MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
   EXISTS_TAC “x + x” THEN
   CONJ_TAC THEN1 (
     SIMP_TAC bool_ss [ADD1,ADD_MONO_LESS_EQ] THEN
     SIMP_TAC bool_ss [ONE] THEN
     MATCH_MP_TAC LESS_OR THEN
     PROVE_TAC [NOT_ZERO_LT_ZERO] ) THEN
   SIMP_TAC bool_ss [EXP] THEN
   MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
   EXISTS_TAC “b * x” THEN
   CONJ_TAC THEN1 (
     SIMP_TAC bool_ss [GSYM TIMES2] THEN
     MATCH_MP_TAC LESS_MONO_MULT THEN
     SIMP_TAC bool_ss [TWO] THEN
     MATCH_MP_TAC LESS_OR THEN
     FIRST_ASSUM ACCEPT_TAC ) THEN
   SIMP_TAC bool_ss [LT_MULT_LCANCEL] THEN
   CONJ_TAC THEN1 (
     MATCH_MP_TAC LESS_TRANS THEN
     EXISTS_TAC “1” THEN
     ASM_SIMP_TAC bool_ss [ONE,prim_recTheory.LESS_0_0] ) THEN
   FIRST_ASSUM ACCEPT_TAC)

local fun Cases_on q = Q.SPEC_THEN q STRUCT_CASES_TAC num_CASES in

val ZERO_EXP = Q.store_thm ("ZERO_EXP",
   `0 ** x = if x = 0 then 1 else 0`,
   Cases_on `x` THEN
   SIMP_TAC bool_ss [EXP,numTheory.NOT_SUC,MULT])

val X_LT_EXP_X_IFF = Q.store_thm ("X_LT_EXP_X_IFF",
   `x < b ** x <=> 1 < b \/ (x = 0)`,
   EQ_TAC THEN1 (
     Cases_on `b` THEN1 (
       Cases_on `x` THEN
       SIMP_TAC bool_ss [ZERO_EXP,SUC_NOT,NOT_LESS_0] ) THEN
     Q.MATCH_RENAME_TAC `x < SUC b ** x ==> 1 < SUC b \/ (x = 0)` THEN
     Cases_on `b` THEN1 (
       SIMP_TAC bool_ss [EXP_1,SYM ONE] THEN
       SIMP_TAC bool_ss [ONE,LESS_THM,NOT_LESS_0] ) THEN
     SIMP_TAC bool_ss [LESS_MONO_EQ,ONE,LESS_0] ) THEN
   STRIP_TAC THEN1 (
     POP_ASSUM MP_TAC THEN ACCEPT_TAC X_LT_EXP_X) THEN
   ASM_SIMP_TAC bool_ss [EXP,ONE,LESS_0])
   end

(* theorems about exponentiation where the exponent is held constant *)
val LT_MULT_IMP = prove(
  “a < b /\ x < y ==> a * x < b * y”,
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `0 < y` ASSUME_TAC THEN1 METIS_TAC [NOT_ZERO_LT_ZERO,
                                                     NOT_LESS_0] THEN
  METIS_TAC [LE_MULT_LCANCEL, LT_MULT_RCANCEL, LESS_EQ_LESS_TRANS,
             LESS_OR_EQ])
val LE_MULT_IMP = prove(
  “a <= b /\ x <= y ==> a * x <= b * y”,
  METIS_TAC [LE_MULT_LCANCEL, LE_MULT_RCANCEL, LESS_EQ_TRANS]);

val EXP_LT_MONO_0 = prove(
  “!n. 0 < n ==> !a b. a < b ==> a EXP n < b EXP n”,
  INDUCT_TAC THEN SRW_TAC [][NOT_LESS_0, LESS_0, EXP] THEN
  Q.SPEC_THEN `n` STRIP_ASSUME_TAC num_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [EXP, MULT_CLAUSES, LESS_0] THEN
  SRW_TAC [][LT_MULT_IMP])

val EXP_LE_MONO_0 = prove(
  “!n. 0 < n ==> !a b. a <= b ==> a EXP n <= b EXP n”,
  INDUCT_TAC THEN SRW_TAC [][EXP, LESS_EQ_REFL] THEN
  Q.SPEC_THEN `n` STRIP_ASSUME_TAC num_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [EXP, MULT_CLAUSES, LESS_0] THEN
  SRW_TAC [][LE_MULT_IMP]);

Theorem EXP_EXP_LT_MONO:
  !a b. a EXP n < b EXP n <=> a < b /\ 0 < n
Proof
  METIS_TAC [EXP_LT_MONO_0, NOT_LESS, EXP_LE_MONO_0, EXP, LESS_REFL,
             NOT_ZERO_LT_ZERO]
QED

Theorem EXP_EXP_LE_MONO:
  !a b. a EXP n <= b EXP n <=> a <= b \/ (n = 0)
Proof
  METIS_TAC [EXP_LE_MONO_0, NOT_LESS_EQUAL, EXP_LT_MONO_0, EXP, LESS_EQ_REFL,
             NOT_ZERO_LT_ZERO]
QED

Theorem EXP_EXP_INJECTIVE:
  !b1 b2 x. (b1 EXP x = b2 EXP x) <=> (x = 0) \/ (b1 = b2)
Proof
  METIS_TAC [EXP_EXP_LE_MONO, LESS_EQUAL_ANTISYM, LESS_EQ_REFL]
QED

val EXP_SUB = Q.store_thm ("EXP_SUB",
  `!p q n. 0 < n /\ q <= p ==> (n ** (p - q) = n ** p DIV n ** q)`,
   REPEAT STRIP_TAC THEN
   “0 < n ** p /\ 0 < n ** q” via
        (STRIP_ASSUME_TAC (Q.SPEC`n` num_CASES) THEN
         RW_TAC bool_ss [] THEN
         FULL_SIMP_TAC bool_ss [ZERO_LESS_EXP,LESS_REFL]) THEN
   RW_TAC bool_ss [DIV_P] THEN
   Q.EXISTS_TAC `0` THEN
   RW_TAC bool_ss [GSYM EXP_ADD,ADD_CLAUSES] THEN
   METIS_TAC [SUB_ADD]);

val EXP_SUB_NUMERAL = store_thm ("EXP_SUB_NUMERAL",
  “0 < n ==>
     (n ** (NUMERAL (BIT1 x)) DIV n = n ** (NUMERAL (BIT1 x) - 1)) /\
     (n ** (NUMERAL (BIT2 x)) DIV n = n ** (NUMERAL (BIT1 x)))”,
  REPEAT STRIP_TAC THENL [
    Q.SPECL_THEN [`NUMERAL (BIT1 x)`, `1`, `n`] (MP_TAC o GSYM) EXP_SUB THEN
    REWRITE_TAC [EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [NUMERAL_DEF, BIT1, ALT_ZERO, ADD_CLAUSES,
                     LESS_EQ_MONO, ZERO_LESS_EQ],
    Q.SPECL_THEN [`NUMERAL (BIT2 x)`, `1`, `n`] (MP_TAC o GSYM) EXP_SUB THEN
    REWRITE_TAC [EXP_1] THEN
    Q.SUBGOAL_THEN `NUMERAL (BIT2 x) - 1 = NUMERAL (BIT1 x)` SUBST1_TAC THENL[
      REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2, ALT_ZERO, ADD_CLAUSES,
                   SUB_MONO_EQ, SUB_0],
      ALL_TAC
    ] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [NUMERAL_DEF, BIT2, BIT1, ALT_ZERO, ADD_CLAUSES,
                     LESS_EQ_MONO, ZERO_LESS_EQ]
  ]);
val _ = export_rewrites ["EXP_SUB_NUMERAL"]

val EXP_BASE_MULT = store_thm ("EXP_BASE_MULT",
  “!z x y. (x * y) ** z = (x ** z) * (y ** z)”,
  INDUCT_TAC THEN
  ASM_SIMP_TAC bool_ss [EXP, MULT_CLAUSES, AC MULT_ASSOC MULT_COMM]);

val EXP_EXP_MULT = store_thm ("EXP_EXP_MULT",
 “!z x y. x ** (y * z) = (x ** y) ** z”,
  INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES, EXP_1, EXP_ADD]);

Theorem SUM_SQUARED:
  (x + y) ** 2 = x ** 2 + 2 * x * y + y ** 2
Proof
  REWRITE_TAC[EXP,TWO,ONE,MULT_CLAUSES, ADD_CLAUSES, RIGHT_ADD_DISTRIB,
              LEFT_ADD_DISTRIB] >>
  SIMP_TAC bool_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC]
QED

(* ********************************************************************** *)
(* Maximum and minimum                                                    *)
(* ********************************************************************** *)

val _ = print "Minimums and maximums\n"

val MAX_DEF = new_definition("MAX_DEF", “MAX m n = if m < n then n else m”);
val MIN_DEF = new_definition("MIN_DEF", “MIN m n = if m < n then m else n”);

val MAX = MAX_DEF;
val MIN = MIN_DEF;

(* Alternative definitions of MAX and MIN using ‘<=’ instead of ‘<’ *)
Theorem MIN_ALT :
    !m n. MIN m n = if m <= n then m else n
Proof
    rw [LESS_OR_EQ, MIN_DEF] >> fs []
QED

Theorem MAX_ALT :
    !m n. MAX m n = if m <= n then n else m
Proof
    rw [LESS_OR_EQ, MAX_DEF] >> fs []
QED

val ARW = RW_TAC bool_ss

val MAX_COMM = store_thm ("MAX_COMM",
  “!m n. MAX m n = MAX n m”,
  ARW [MAX] THEN FULL_SIMP_TAC bool_ss [NOT_LESS] THEN
  IMP_RES_TAC LESS_ANTISYM THEN IMP_RES_TAC LESS_EQUAL_ANTISYM);

val MIN_COMM = store_thm ("MIN_COMM",
  “!m n. MIN m n = MIN n m”,
  ARW [MIN] THEN FULL_SIMP_TAC bool_ss [NOT_LESS] THEN
  IMP_RES_TAC LESS_ANTISYM THEN IMP_RES_TAC LESS_EQUAL_ANTISYM);

val MAX_ASSOC = store_thm ("MAX_ASSOC",
  “!m n p. MAX m (MAX n p) = MAX (MAX m n) p”,
  SIMP_TAC bool_ss [MAX] THEN
  PROVE_TAC [NOT_LESS, LESS_EQ_TRANS, LESS_TRANS]);

val MIN_ASSOC = store_thm ("MIN_ASSOC",
  “!m n p. MIN m (MIN n p) = MIN (MIN m n) p”,
  SIMP_TAC bool_ss [MIN] THEN
  PROVE_TAC [NOT_LESS, LESS_EQ_TRANS, LESS_TRANS]);

val MIN_MAX_EQ = store_thm ("MIN_MAX_EQ",
  “!m n. (MIN m n = MAX m n) = (m = n)”,
  SIMP_TAC bool_ss [MAX, MIN] THEN
  PROVE_TAC [NOT_LESS, LESS_EQUAL_ANTISYM, LESS_ANTISYM]);

val MIN_MAX_LT = store_thm ("MIN_MAX_LT",
  “!m n. (MIN m n < MAX m n) = ~(m = n)”,
  SIMP_TAC bool_ss [MAX, MIN] THEN
  PROVE_TAC [LESS_REFL, NOT_LESS, LESS_OR_EQ]);

val MIN_MAX_LE = store_thm ("MIN_MAX_LE",
  “!m n. MIN m n <= MAX m n”,
  SIMP_TAC bool_ss [MAX, MIN] THEN
  PROVE_TAC [LESS_OR_EQ, NOT_LESS]);

val MIN_MAX_PRED = store_thm ("MIN_MAX_PRED",
  “!P m n. P m /\ P n ==> P (MIN m n) /\ P (MAX m n)”,
  PROVE_TAC [MIN, MAX]);

Theorem MIN_LT:
  !n m p. (MIN m n < p <=> m < p \/ n < p) /\
          (p < MIN m n <=> p < m /\ p < n)
Proof
  SIMP_TAC bool_ss [MIN] THEN
  PROVE_TAC [NOT_LESS, LESS_OR_EQ, LESS_ANTISYM, LESS_TRANS]
QED

Theorem MAX_LT:
  !n m p. (p < MAX m n <=> p < m \/ p < n) /\
          (MAX m n < p <=> m < p /\ n < p)
Proof
  SIMP_TAC bool_ss [MAX] THEN
  PROVE_TAC [NOT_LESS, LESS_OR_EQ, LESS_ANTISYM, LESS_TRANS]
QED

Theorem MIN_LE:
  !n m p. (MIN m n <= p <=> m <= p \/ n <= p) /\
          (p <= MIN m n <=> p <= m /\ p <= n)
Proof  SIMP_TAC bool_ss [MIN] THEN PROVE_TAC [LESS_OR_EQ, NOT_LESS, LESS_TRANS]
QED

Theorem MAX_LE:
  !n m p. (p <= MAX m n <=> p <= m \/ p <= n) /\
          (MAX m n <= p <=> m <= p /\ n <= p)
Proof
  SIMP_TAC bool_ss [MAX] THEN
  PROVE_TAC [LESS_OR_EQ, NOT_LESS, LESS_TRANS]
QED

val MIN_0 = store_thm ("MIN_0",
  “!n. (MIN n 0 = 0) /\ (MIN 0 n = 0)”,
  REWRITE_TAC [MIN] THEN
  PROVE_TAC [NOT_LESS_0, NOT_LESS, LESS_OR_EQ]);

val MAX_0 = store_thm ("MAX_0",
  “!n. (MAX n 0 = n) /\ (MAX 0 n = n)”,
  REWRITE_TAC [MAX] THEN
  PROVE_TAC [NOT_LESS_0, NOT_LESS, LESS_OR_EQ]);

val MAX_EQ_0 = store_thm(
  "MAX_EQ_0[simp]",
  “(MAX m n = 0) <=> (m = 0) /\ (n = 0)”,
  SRW_TAC[][MAX,EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [NOT_LESS_0, NOT_LESS]);

val MIN_EQ_0 = store_thm(
  "MIN_EQ_0[simp]",
  “(MIN m n = 0) <=> (m = 0) \/ (n = 0)”,
  SRW_TAC[][MIN,EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [NOT_LESS_0, NOT_LESS]);

val MIN_IDEM = store_thm ("MIN_IDEM",
  “!n. MIN n n = n”,
  PROVE_TAC [MIN]);

val MAX_IDEM = store_thm ("MAX_IDEM",
  “!n. MAX n n = n”,
  PROVE_TAC [MAX]);

(* Theorem: (MAX n m = n) \/ (MAX n m = m) *)
(* Proof: by MAX_DEF *)
val MAX_CASES = store_thm(
  "MAX_CASES",
  ``!m n. (MAX n m = n) \/ (MAX n m = m)``,
  rw[MAX_DEF]);

(* Theorem: (MIN n m = n) \/ (MIN n m = m) *)
(* Proof: by MIN_DEF *)
val MIN_CASES = store_thm(
  "MIN_CASES",
  ``!m n. (MIN n m = n) \/ (MIN n m = m)``,
  rw[MIN_DEF]);

val EXISTS_GREATEST = store_thm ("EXISTS_GREATEST",
  “!P. (?x. P x) /\ (?x:num. !y. y > x ==> ~P y) <=>
    ?x. P x /\ !y. y > x ==> ~P y”,
 GEN_TAC THEN EQ_TAC THENL
 [REWRITE_TAC[GREATER_DEF] THEN
   DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
   SUBGOAL_THEN
     (“(?x. !y. x < y ==> ~P y) = (?x. (\x. !y. x < y ==> ~P y) x)”)
        SUBST1_TAC THENL
    [BETA_TAC THEN REFL_TAC,
     DISCH_THEN (MP_TAC o MATCH_MP WOP)
      THEN BETA_TAC THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
      THEN STRIP_TAC THEN EXISTS_TAC (“n:num”) THEN ASM_REWRITE_TAC[]
      THEN NTAC 2 (POP_ASSUM MP_TAC)
      THEN STRUCT_CASES_TAC (SPEC (“n:num”) num_CASES)
      THEN REPEAT STRIP_TAC THENL
      [UNDISCH_THEN (“!y. 0 < y ==> ~P y”)
            (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV))
         THEN REWRITE_TAC[] THEN STRIP_TAC THEN RES_TAC
         THEN MP_TAC (SPEC (“x:num”) LESS_0_CASES)
         THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (SUBST_ALL_TAC o SYM)
         THEN ASM_REWRITE_TAC[],
       POP_ASSUM (MP_TAC o SPEC (“n':num”))
         THEN REWRITE_TAC [prim_recTheory.LESS_SUC_REFL]
         THEN DISCH_THEN (CHOOSE_THEN MP_TAC)
         THEN SUBGOAL_THEN (“!x y. ~(x ==> ~y) <=> x /\ y”)
               (fn th => REWRITE_TAC[th] THEN STRIP_TAC) THENL
         [REWRITE_TAC [NOT_IMP],
           UNDISCH_THEN (“!y. SUC n' < y ==> ~P y”)
              (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)
                 o SPEC (“y:num”))
            THEN ASM_REWRITE_TAC[NOT_LESS,LESS_OR_EQ]
            THEN DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC)
            THENL [IMP_RES_TAC LESS_LESS_SUC, ASM_REWRITE_TAC[]]]]],
  REPEAT STRIP_TAC THEN EXISTS_TAC (“x:num”) THEN ASM_REWRITE_TAC[]]);

val EXISTS_NUM = store_thm ("EXISTS_NUM",
  “!P. (?n. P n) <=> P 0 \/ (?m. P (SUC m))”,
  PROVE_TAC [num_CASES]);

val FORALL_NUM = store_thm ("FORALL_NUM",
  “!P. (!n. P n) <=> P 0 /\ !n. P (SUC n)”,
  PROVE_TAC [num_CASES]);

val BOUNDED_FORALL_THM = Q.store_thm ("BOUNDED_FORALL_THM",
   `!c. 0<c ==> ((!n. n < c ==> P n) <=> P (c-1) /\ !n. n < (c-1) ==> P n)`,
    RW_TAC boolSimps.bool_ss [] THEN EQ_TAC THENL
     [REPEAT STRIP_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THENL
        [METIS_TAC [ONE,LESS_ADD_SUC,ADD_SYM,SUB_RIGHT_LESS],
         MATCH_MP_TAC LESS_LESS_EQ_TRANS
           THEN Q.EXISTS_TAC `c-1`
           THEN ASM_REWRITE_TAC [SUB_LESS_EQ,SUB_LEFT_LESS]],
      METIS_TAC [SUB_LESS_OR,LESS_OR_EQ]]);

val BOUNDED_EXISTS_THM = Q.store_thm ("BOUNDED_EXISTS_THM",
   `!c. 0<c ==> ((?n. n < c /\ P n) <=> P (c-1) \/ ?n. n < (c-1) /\ P n)`,
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [METIS_TAC [SUB_LESS_OR,LESS_REFL,LESS_EQ_LESS_TRANS,LESS_LESS_CASES],
      METIS_TAC [num_CASES,LESS_REFL,SUC_SUB1,LESS_SUC_REFL],
      METIS_TAC [SUB_LEFT_LESS,ADD1,SUC_LESS]]);

(*---------------------------------------------------------------------------*)
(* Theorems about sequences                                                  *)
(*---------------------------------------------------------------------------*)

val transitive_monotone = Q.store_thm ("transitive_monotone",
   `!R f. transitive R /\ (!n. R (f n) (f (SUC n))) ==>
          !m n. m < n ==> R (f m) (f n)`,
   NTAC 3 STRIP_TAC THEN INDUCT_TAC THEN
   (INDUCT_TAC THEN1 REWRITE_TAC [NOT_LESS_0])
   THEN1 (
     POP_ASSUM MP_TAC THEN
     Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES THEN
     METIS_TAC [LESS_0,relationTheory.transitive_def]) THEN
   METIS_TAC [LESS_THM,relationTheory.transitive_def])

val STRICTLY_INCREASING_TC = save_thm ("STRICTLY_INCREASING_TC",
   (* !f. (!n. f n < f (SUC n)) ==> !m n. m < n ==> f m < f n *)
   transitive_monotone |> Q.ISPEC `$<` |>
   SIMP_RULE bool_ss [
     Q.prove(`transitive $<`,
       METIS_TAC [relationTheory.transitive_def,LESS_TRANS])])

val STRICTLY_INCREASING_ONE_ONE = Q.store_thm ("STRICTLY_INCREASING_ONE_ONE",
   `!f. (!n. f n < f (SUC n)) ==> ONE_ONE f`,
   REWRITE_TAC [ONE_ONE_THM] THEN
   METIS_TAC [STRICTLY_INCREASING_TC,NOT_LESS,LESS_OR_EQ,LESS_EQUAL_ANTISYM])

val ONE_ONE_INV_IMAGE_BOUNDED = Q.store_thm ("ONE_ONE_INV_IMAGE_BOUNDED",
  `ONE_ONE (f:num->num) ==> !b. ?a. !x. f x <= b ==> x <= a`,
  REWRITE_TAC [ONE_ONE_THM] THEN DISCH_TAC THEN INDUCT_TAC
  THENL [
    (* case b of 0 *)
    REWRITE_TAC [LESS_EQ_0] THEN Q.ASM_CASES_TAC `?z. f z = 0`
    THENL [
      POP_ASSUM CHOOSE_TAC THEN
        Q.EXISTS_TAC `z` THEN REPEAT STRIP_TAC THEN
        VALIDATE (FIRST_X_ASSUM
          (ASSUME_TAC o UNDISCH o Q.SPECL [`x`, `z`])) THEN
        ASM_REWRITE_TAC [LESS_EQ_REFL],
      Q.EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN RES_TAC],

    (* case b of SUC b *)
    POP_ASSUM CHOOSE_TAC THEN REWRITE_TAC [LE] THEN
    Q.ASM_CASES_TAC `?z. f z = SUC b`
    THENL [
      POP_ASSUM CHOOSE_TAC THEN
        Q.EXISTS_TAC `MAX a z` THEN
        REWRITE_TAC [MAX_LE] THEN REPEAT STRIP_TAC
      THENL [
        VALIDATE (FIRST_X_ASSUM
            (ASSUME_TAC o UNDISCH o Q.SPECL [`x`, `z`])) THEN
          ASM_REWRITE_TAC [LESS_EQ_REFL],
        RES_TAC THEN ASM_REWRITE_TAC []],
      Q.EXISTS_TAC `a` THEN REPEAT STRIP_TAC THEN RES_TAC] ]) ;

val ONE_ONE_UNBOUNDED = Q.store_thm ("ONE_ONE_UNBOUNDED",
`!f. ONE_ONE (f:num->num) ==> !b.?n. b < f n`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (CHOOSE_TAC o Q.SPEC `b` o
    MATCH_MP ONE_ONE_INV_IMAGE_BOUNDED) THEN
  Q.EXISTS_TAC `SUC a` THEN
  REWRITE_TAC [GSYM NOT_LESS_EQUAL] THEN
  DISCH_TAC THEN RES_TAC THEN
  POP_ASSUM (ACCEPT_TAC o REWRITE_RULE [GSYM LESS_EQ, LESS_REFL])) ;

val STRICTLY_INCREASING_UNBOUNDED = Q.store_thm("STRICTLY_INCREASING_UNBOUNDED",
   `!f. (!n. f n < f (SUC n)) ==> !b.?n. b < f n`,
   METIS_TAC [STRICTLY_INCREASING_ONE_ONE,ONE_ONE_UNBOUNDED])

val STRICTLY_DECREASING_TC = Q.prove(
   `!f. (!n. f (SUC n) < f n) ==> !m n. m < n ==> f n < f m`,
   NTAC 2 STRIP_TAC THEN
   (transitive_monotone |> Q.ISPECL [`\x y. y < x`,`f:num->num`] |>
    SIMP_RULE bool_ss [] |> MATCH_MP_TAC) THEN
   SRW_TAC [][relationTheory.transitive_def] THEN
   METIS_TAC [LESS_TRANS])

val STRICTLY_DECREASING_ONE_ONE = Q.prove(
   `!f. (!n. f (SUC n) < f n) ==> ONE_ONE f`,
   SRW_TAC [] [ONE_ONE_THM] THEN
   METIS_TAC [STRICTLY_DECREASING_TC,NOT_LESS,LESS_OR_EQ,LESS_EQUAL_ANTISYM])

val NOT_STRICTLY_DECREASING = Q.store_thm ("NOT_STRICTLY_DECREASING",
   `!f. ~(!n. f (SUC n) < f n)`,
   NTAC 2 STRIP_TAC THEN
   IMP_RES_TAC STRICTLY_DECREASING_TC THEN
   IMP_RES_TAC STRICTLY_DECREASING_ONE_ONE THEN
   IMP_RES_TAC ONE_ONE_UNBOUNDED THEN
   POP_ASSUM (Q.SPEC_THEN `f 0` STRIP_ASSUME_TAC) THEN
   Q.SPEC_THEN `n` STRIP_ASSUME_TAC num_CASES THEN1
     METIS_TAC [LESS_NOT_EQ] THEN
   METIS_TAC [LESS_ANTISYM,LESS_0])

(* Absolute difference *)
val ABS_DIFF_def = new_definition ("ABS_DIFF_def",
   “ABS_DIFF n m = if n < m then m - n else n - m”)

val ABS_DIFF_SYM = Q.store_thm ("ABS_DIFF_SYM",
   `!n m. ABS_DIFF n m = ABS_DIFF m n`,
   SRW_TAC [][ABS_DIFF_def] THEN
   METIS_TAC [LESS_ANTISYM,NOT_LESS,LESS_OR_EQ])

val ABS_DIFF_COMM = save_thm ("ABS_DIFF_COMM",ABS_DIFF_SYM)

val ABS_DIFF_EQS = Q.store_thm ("ABS_DIFF_EQS",
   `!n. ABS_DIFF n n = 0`,
   SRW_TAC [][ABS_DIFF_def,SUB_EQUAL_0])
val _ = export_rewrites ["ABS_DIFF_EQS"]

val ABS_DIFF_EQ_0 = Q.store_thm ("ABS_DIFF_EQ_0",
   `!n m. (ABS_DIFF n m = 0) <=> (n = m)`,
   SRW_TAC [][ABS_DIFF_def,LESS_OR_EQ,SUB_EQ_0] THEN
   METIS_TAC [LESS_ANTISYM])

val ABS_DIFF_ZERO = Q.store_thm ("ABS_DIFF_ZERO",
   `!n. (ABS_DIFF n 0 = n) /\ (ABS_DIFF 0 n = n)`,
   SRW_TAC [][ABS_DIFF_def,SUB_0] THEN
   METIS_TAC [NOT_LESS_0,NOT_ZERO_LT_ZERO])
val _ = export_rewrites ["ABS_DIFF_ZERO"]

val ABS_DIFF_SUC = Q.store_thm ("ABS_DIFF_SUC",
   `!n m. (ABS_DIFF (SUC n) (SUC m)) = (ABS_DIFF n m)`,
   REWRITE_TAC [ABS_DIFF_def, LESS_MONO_EQ, SUB_MONO_EQ]) ;

fun owr commth = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV commth)) ;

val LESS_EQ_TRANS' = REWRITE_RULE [GSYM AND_IMP_INTRO] LESS_EQ_TRANS ;
val AND_IMP_INTRO' = owr CONJ_COMM AND_IMP_INTRO ;
val LESS_EQ_TRANS'' = REWRITE_RULE [GSYM AND_IMP_INTRO'] LESS_EQ_TRANS ;
val LESS_EQ_ADD' = owr ADD_COMM LESS_EQ_ADD ;
val LESS_EQ_SUC_REFL' = SPEC_ALL LESS_EQ_SUC_REFL ;

val leq_ss = MATCH_MP (MATCH_MP LESS_EQ_TRANS'' LESS_EQ_SUC_REFL')
  LESS_EQ_SUC_REFL' ;

val imp_leq_ss = MATCH_MP LESS_EQ_TRANS'' leq_ss ;

val ABS_DIFF_SUC_LE = Q.store_thm ("ABS_DIFF_SUC_LE",
  `!x z. ABS_DIFF x (SUC z) <= SUC (ABS_DIFF x z)`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [ABS_DIFF_ZERO, ABS_DIFF_SUC, ADD, ADD_0, GSYM ADD_SUC,
    LESS_EQ_REFL, LESS_EQ_MONO, ZERO_LESS_EQ, leq_ss]) ;

val ABS_DIFF_PLUS_LE = Q.store_thm ("ABS_DIFF_PLUS_LE",
  `!x z y. ABS_DIFF x (y + z) <= y + (ABS_DIFF x z)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC [ADD, LESS_EQ_REFL]
    THEN MATCH_MP_TAC (MATCH_MP LESS_EQ_TRANS' (SPEC_ALL ABS_DIFF_SUC_LE))
    THEN ASM_REWRITE_TAC [LESS_EQ_MONO]) ;

val ABS_DIFF_PLUS_LE' = owr ADD_COMM ABS_DIFF_PLUS_LE ;
val [ADT_splemx, ADT_splemx'] =
  map (owr ABS_DIFF_COMM) [ABS_DIFF_PLUS_LE, ABS_DIFF_PLUS_LE'] ;

val ABS_DIFF_LE_SUM = Q.store_thm ("ABS_DIFF_LE_SUM",
  `ABS_DIFF x z <= x + z`,
  REWRITE_TAC [ABS_DIFF_def] THEN COND_CASES_TAC
    THEN MATCH_MP_TAC (MATCH_MP LESS_EQ_TRANS' (SPEC_ALL SUB_LESS_EQ))
    THEN REWRITE_TAC [LESS_EQ_ADD, LESS_EQ_ADD']) ;

val ABS_DIFF_LE_SUM' = owr ADD_COMM ABS_DIFF_LE_SUM ;

val [ADT_sslem, ADT_sslem'] = map (MATCH_MP imp_leq_ss)
  [ABS_DIFF_LE_SUM, ABS_DIFF_LE_SUM'] ;

val ABS_DIFF_TRIANGLE_lem = Q.store_thm ("ABS_DIFF_TRIANGLE_lem",
  `!x y. x <= ABS_DIFF x y + y`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [ABS_DIFF_ZERO, ABS_DIFF_SUC, ADD, ADD_0, GSYM ADD_SUC,
    LESS_EQ_REFL, LESS_EQ_MONO, ZERO_LESS_EQ]) ;

val ABS_DIFF_TRIANGLE_lem' =
  owr ABS_DIFF_COMM (owr ADD_COMM ABS_DIFF_TRIANGLE_lem) ;

val ABS_DIFF_TRIANGLE = Q.store_thm ("ABS_DIFF_TRIANGLE",
`!x y z. ABS_DIFF x z <= ABS_DIFF x y + ABS_DIFF y z`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [ABS_DIFF_ZERO, ABS_DIFF_SUC, ADD, ADD_0, GSYM ADD_SUC,
    LESS_EQ_REFL, LESS_EQ_MONO, ZERO_LESS_EQ,
    ABS_DIFF_TRIANGLE_lem, ABS_DIFF_TRIANGLE_lem', ADT_sslem]) ;

val ABS_DIFF_ADD_SAME = Q.store_thm ("ABS_DIFF_ADD_SAME",
   `!n m p. ABS_DIFF (n + p) (m + p) = ABS_DIFF n m`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC
     THEN ASM_REWRITE_TAC [ADD_0, GSYM ADD_SUC, ABS_DIFF_SUC]) ;

val LE_SUB_RCANCEL = Q.store_thm ("LE_SUB_RCANCEL",
   `!m n p. n - m <= p - m <=> n <= m \/ n <= p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [ LESS_EQ_REFL, LESS_EQ_MONO, ZERO_LESS_EQ,
    NOT_SUC_LESS_EQ_0, SUB_MONO_EQ, SUB_0, SUB_EQ_0, LESS_EQ_0]) ;

val LT_SUB_RCANCEL = Q.store_thm ("LT_SUB_RCANCEL",
   `!m n p. n - m < p - m <=> n < p /\ m < p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM NOT_LESS_EQUAL, LE_SUB_RCANCEL, DE_MORGAN_THM] THEN
  MATCH_ACCEPT_TAC CONJ_COMM) ;

val LE_SUB_LCANCEL = Q.store_thm ("LE_SUB_LCANCEL",
  `!z y x. x - y <= x - z <=> z <= y \/ x <= y`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [ SUB_MONO_EQ, LESS_EQ_MONO, LESS_EQ_REFL,
    SUB_0, NOT_SUC_LESS_EQ_0, ZERO_LESS_EQ,
    NOT_SUC_LESS_EQ, SUB_LESS_EQ, SUB_LE_SUC]) ;

val LT_SUB_LCANCEL = Q.store_thm ("LT_SUB_LCANCEL",
  `!z y x. x - y < x - z <=> z < y /\ z < x`,
  REWRITE_TAC [GSYM NOT_LESS_EQUAL, LE_SUB_LCANCEL, DE_MORGAN_THM]) ;

val ABS_DIFF_SUMS = Q.store_thm ("ABS_DIFF_SUMS",
`!n1 n2 m1 m2. ABS_DIFF (n1 + n2) (m1 + m2) <= ABS_DIFF n1 m1 + ABS_DIFF n2 m2`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC [ABS_DIFF_ZERO, ABS_DIFF_SUC, ADD, ADD_0, GSYM ADD_SUC,
    LESS_EQ_REFL, LESS_EQ_MONO, ZERO_LESS_EQ, ADT_sslem', ADT_sslem]
  THENL [
    REWRITE_TAC [GSYM (CONJUNCT2 ADD), ABS_DIFF_PLUS_LE],
    REWRITE_TAC [ADD_SUC, ABS_DIFF_PLUS_LE'],
    REWRITE_TAC [GSYM (CONJUNCT2 ADD), ADT_splemx],
    REWRITE_TAC [ADD_SUC, ADT_splemx'] ]) ;

(* ********************************************************************** *)
val _ = print "Miscellaneous theorems\n"
(* ********************************************************************** *)

val FUNPOW_SUC = store_thm ("FUNPOW_SUC",
   “!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)”,
   GEN_TAC
   THEN INDUCT_TAC
   THENL [REWRITE_TAC [FUNPOW],
          ONCE_REWRITE_TAC [FUNPOW]
          THEN ASM_REWRITE_TAC []]);

val FUNPOW_0 = store_thm ("FUNPOW_0",
  “FUNPOW f 0 x = x”,
  REWRITE_TAC [FUNPOW]);
val _ = export_rewrites ["FUNPOW_0"]

val FUNPOW_ADD = store_thm ("FUNPOW_ADD",
  “!m n. FUNPOW f (m + n) x = FUNPOW f m (FUNPOW f n x)”,
  INDUCT_TAC THENL [
    REWRITE_TAC [ADD_CLAUSES, FUNPOW],
    ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW_SUC]
  ]);

val FUNPOW_1 = store_thm ("FUNPOW_1",
  “FUNPOW f 1 x = f x”,
  REWRITE_TAC [FUNPOW, ONE]);
val _ = export_rewrites ["FUNPOW_1"]

(* Theorem: FUNPOW f 2 x = f (f x) *)
(* Proof: by definition. *)
val FUNPOW_2 = store_thm(
  "FUNPOW_2",
  ``!f x. FUNPOW f 2 x = f (f x)``,
  simp_tac bool_ss [FUNPOW, TWO, ONE]);

(* Theorem: FUNPOW (K c) n x = if n = 0 then x else c *)
(* Proof:
   By induction on n.
   Base: !x c. FUNPOW (K c) 0 x = if 0 = 0 then x else c
           FUNPOW (K c) 0 x
         = x                         by FUNPOW
         = if 0 = 0 then x else c    by 0 = 0 is true
   Step: !x c. FUNPOW (K c) n x = if n = 0 then x else c ==>
         !x c. FUNPOW (K c) (SUC n) x = if SUC n = 0 then x else c
           FUNPOW (K c) (SUC n) x
         = FUNPOW (K c) n ((K c) x)         by FUNPOW
         = if n = 0 then ((K c) c) else c   by induction hypothesis
         = if n = 0 then c else c           by K_THM
         = c                                by either case
         = if SUC n = 0 then x else c       by SUC n = 0 is false
*)
val FUNPOW_K = store_thm(
  "FUNPOW_K",
  ``!n x c. FUNPOW (K c) n x = if n = 0 then x else c``,
  Induct >-
  rw[] >>
  metis_tac[FUNPOW, combinTheory.K_THM, SUC_NOT_ZERO]);

Theorem FUNPOW_CONG:
  !n x f g.
  (!m. m < n ==> f (FUNPOW f m x) = g (FUNPOW f m x))
  ==>
  FUNPOW f n x = FUNPOW g n x
Proof
  INDUCT_TAC \\ SRW_TAC[][FUNPOW_SUC]
  THEN METIS_TAC[LESS_SUC, LESS_SUC_REFL]
QED

Theorem FUNPOW_invariant:
  !m x.
  P x /\ (!x. P x ==> P (f x)) ==>
  P (FUNPOW f m x)
Proof
  Induct \\ SRW_TAC[][FUNPOW_SUC]
QED

Theorem FUNPOW_invariant_index:
  !m x.
  P x /\
  (!n. n < m ==> R (FUNPOW f n x)) /\
  (!x. P x /\ R x ==> P (f x)) ==>
  P (FUNPOW f m x)
Proof
  Induct >> SRW_TAC[][FUNPOW_SUC]
  \\ first_assum irule
  \\ `m < SUC m` by SRW_TAC[][LESS_SUC_REFL]
  \\ SRW_TAC[][]
  \\ first_assum irule \\ SRW_TAC[][]
  \\ first_assum irule \\ SRW_TAC[][LESS_SUC]
QED

(* Theorem: FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x) *)
(* Proof: by FUNPOW_ADD, ADD_COMM *)
Theorem FUNPOW_COMM:
  !f m n x. FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)
Proof
  metis_tac[FUNPOW_ADD, ADD_COMM]
QED

val NRC_0 = save_thm ("NRC_0", CONJUNCT1 NRC);
val _ = export_rewrites ["NRC_0"]

val NRC_1 = store_thm ("NRC_1",
  “NRC R 1 x y = R x y”,
  SRW_TAC [][ONE, NRC]);
val _ = export_rewrites ["NRC_1"]

val NRC_ADD_I = store_thm ("NRC_ADD_I",
  “!m n x y z. NRC R m x y /\ NRC R n y z ==> NRC R (m + n) x z”,
  INDUCT_TAC THEN SRW_TAC [][NRC, ADD] THEN METIS_TAC []);

val NRC_ADD_E = store_thm ("NRC_ADD_E",
  “!m n x z. NRC R (m + n) x z ==> ?y. NRC R m x y /\ NRC R n y z”,
  INDUCT_TAC THEN SRW_TAC [][NRC, ADD] THEN METIS_TAC []);

val NRC_ADD_EQN = store_thm ("NRC_ADD_EQN",
  “NRC R (m + n) x z = ?y. NRC R m x y /\ NRC R n y z”,
  METIS_TAC [NRC_ADD_I, NRC_ADD_E]);

val NRC_SUC_RECURSE_LEFT = store_thm ("NRC_SUC_RECURSE_LEFT",
  “NRC R (SUC n) x y = ?z. NRC R n x z /\ R z y”,
  METIS_TAC [NRC_1, NRC_ADD_EQN, ADD1]);

val NRC_RTC = store_thm ("NRC_RTC",
  “!n x y. NRC R n x y ==> RTC R x y”,
  INDUCT_TAC THEN SRW_TAC [][NRC, relationTheory.RTC_RULES] THEN
  METIS_TAC [relationTheory.RTC_RULES]);

val RTC_NRC = store_thm ("RTC_NRC",
  “!x y. RTC R x y ==> ?n. NRC R n x y”,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  PROVE_TAC [NRC] (* METIS_TAC bombs *));

val RTC_eq_NRC = store_thm ("RTC_eq_NRC",
  “!R x y. RTC R x y = ?n. NRC R n x y”,
  PROVE_TAC[RTC_NRC, NRC_RTC]);

val TC_eq_NRC = store_thm ("TC_eq_NRC",
  “!R x y. TC R x y = ?n. NRC R (SUC n) x y”,
  REWRITE_TAC [relationTheory.EXTEND_RTC_TC_EQN, RTC_eq_NRC, NRC] THEN
  PROVE_TAC[]);

val LESS_EQUAL_DIFF = store_thm ("LESS_EQUAL_DIFF",
   “!m n : num. m <= n ==> ?k. m = n - k”,
   REPEAT GEN_TAC
   THEN SPEC_TAC (“m:num”, “m:num”)
   THEN SPEC_TAC (“n:num”, “n:num”)
   THEN INDUCT_TAC
   THENL [REWRITE_TAC [LESS_EQ_0, SUB_0],
          REWRITE_TAC [LE]
          THEN PROVE_TAC [SUB_0, SUB_MONO_EQ]]);

val MOD_2 = store_thm ("MOD_2",
   “!n. n MOD 2 = if EVEN n then 0 else 1”,
   GEN_TAC
   THEN MATCH_MP_TAC MOD_UNIQUE
   THEN ASM_CASES_TAC “EVEN n”
   THEN POP_ASSUM MP_TAC
   THEN REWRITE_TAC [EVEN_EXISTS, GSYM ODD_EVEN, ODD_EXISTS, ADD1]
   THEN STRIP_TAC
   THEN POP_ASSUM SUBST1_TAC
   THEN Q.EXISTS_TAC `m`
   THENL [PROVE_TAC [MULT_COMM, ADD_0, TWO, prim_recTheory.LESS_0],
          (KNOW_TAC “(?m' : num. 2 * m + 1 = 2 * m') = F”
           THEN1 PROVE_TAC [EVEN_EXISTS, ODD_EXISTS, ADD1, EVEN_ODD])
          THEN DISCH_THEN (fn th => REWRITE_TAC [th])
          THEN PROVE_TAC [MULT_COMM, ONE, TWO, prim_recTheory.LESS_0,
                          LESS_MONO_EQ]]);

val EVEN_MOD2 = store_thm ("EVEN_MOD2",
   “!x. EVEN x = (x MOD 2 = 0)”,
   PROVE_TAC [MOD_2, SUC_NOT, ONE]);

val GSYM_MOD_PLUS' = GSYM (SPEC_ALL (UNDISCH_ALL (SPEC_ALL MOD_PLUS))) ;
val MOD_LESS' = UNDISCH (Q.SPECL [`a`, `n`] MOD_LESS) ;

val SUC_MOD_lem = Q.prove (
  `0 < n ==> (SUC a MOD n = if SUC (a MOD n) = n then 0 else SUC (a MOD n))`,
  DISCH_TAC THEN REWRITE_TAC [SUC_ONE_ADD] THEN
  CONV_TAC (LHS_CONV (REWR_CONV_A GSYM_MOD_PLUS')) THEN
  MP_TAC (Q.SPECL [`n`, `1`] LESS_LESS_CASES) THEN STRIP_TAC
  THENL [ ASM_REWRITE_TAC [MOD_1, ADD_0],
    RULE_ASSUM_TAC (REWRITE_RULE
      [GSYM LESS_EQ_IFF_LESS_SUC, ONE, LESS_EQ_0]) THEN
    FULL_SIMP_TAC bool_ss [NOT_LESS_0],
    IMP_RES_TAC LESS_MOD THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN1 ASM_SIMP_TAC bool_ss [DIVMOD_ID] THEN
    irule LESS_MOD THEN ASSUME_TAC MOD_LESS' THEN
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM SUC_ONE_ADD, Once LESS_EQ,
      Once LESS_OR_EQ]) THEN
    REWRITE_TAC [GSYM SUC_ONE_ADD] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN
    FULL_SIMP_TAC bool_ss [NOT_LESS_0] ]) ;

val SUC_MOD = store_thm ("SUC_MOD",
   “!n a b. 0 < n ==> ((SUC a MOD n = SUC b MOD n) = (a MOD n = b MOD n))”,
  ASM_SIMP_TAC bool_ss [SUC_MOD_lem] THEN
  REPEAT STRIP_TAC THEN
  REVERSE EQ_TAC THEN1 SIMP_TAC bool_ss [] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC [numTheory.NOT_SUC, SUC_NOT, INV_SUC_EQ] THEN
  ASM_REWRITE_TAC [Once (GSYM INV_SUC_EQ)]) ;

val ADD_MOD = Q.store_thm ("ADD_MOD",
 `!n a b p. (0 < n:num) ==>
            (((a + p) MOD n = (b + p) MOD n) =
             (a MOD n = b MOD n))`,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC INDUCTION
  THEN SIMP_TAC bool_ss [ADD_CLAUSES, SUC_MOD]);

(*---------------------------------------------------------------------------*)
(* We should be able to use "by" construct at this phase of development,     *)
(* surely?                                                                   *)
(*---------------------------------------------------------------------------*)

val MOD_ELIM = Q.store_thm ("MOD_ELIM",
  `!P x n. 0 < n /\ P x /\ (!y. P (y + n) ==> P y) ==> P (x MOD n)`,
  GEN_TAC THEN HO_MATCH_MP_TAC COMPLETE_INDUCTION
  THEN REPEAT STRIP_TAC
  THEN ASM_CASES_TAC (“x >= n”) THENL
  [“P ((x - n) MOD n):bool” via
      (Q.PAT_ASSUM `!x'. A x' ==> !n. Q x' n` (MP_TAC o Q.SPEC `x-n`) THEN
    “x-n < x” via FULL_SIMP_TAC bool_ss
                  [GREATER_OR_EQ,SUB_RIGHT_LESS,GREATER_DEF] THEN
    METIS_TAC [NOT_ZERO_LT_ZERO,ADD_SYM,LESS_ADD_NONZERO,LESS_TRANS,
               SUB_ADD,GREATER_OR_EQ,GREATER_DEF,LESS_OR_EQ,SUB_RIGHT_LESS])
    THEN “?z. x = z + n” via (Q.EXISTS_TAC `x - n` THEN
           METIS_TAC [SUB_ADD,GREATER_OR_EQ,GREATER_DEF,LESS_OR_EQ])
    THEN RW_TAC bool_ss []
    THEN METIS_TAC [SUB_ADD,GREATER_OR_EQ,GREATER_DEF,LESS_OR_EQ,ADD_MODULUS],
    METIS_TAC [LESS_MOD,NOT_LESS,LESS_OR_EQ,GREATER_OR_EQ, GREATER_DEF]]);

Theorem DOUBLE_LT[simp]:
  !p q. 2 * p + 1 < 2 * q <=> p < q
Proof
  ‘!p q. 2 * p + 1 < 2 * q <=> 2 * p < 2 * q’
    suffices_by (STRIP_TAC THEN ASM_REWRITE_TAC[LT_MULT_LCANCEL, TWO, LESS_0])
  THEN REPEAT GEN_TAC
  THEN EQ_TAC THEN1 PROVE_TAC [ADD1, prim_recTheory.SUC_LESS]
  THEN STRIP_TAC
  THEN SIMP_TAC boolSimps.bool_ss [GSYM ADD1]
  THEN MATCH_MP_TAC LESS_NOT_SUC
  THEN ASM_REWRITE_TAC []
  THEN PROVE_TAC [EVEN_ODD, EVEN_DOUBLE, ODD_DOUBLE]
QED

Theorem EXP2_LT[simp]:
   !m n. n DIV 2 < 2 ** m <=> n < 2 ** SUC m
Proof
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `2` DIVISION)
   THEN (KNOW_TAC “0n < 2” THEN1 REWRITE_TAC [TWO, prim_recTheory.LESS_0])
   THEN SIMP_TAC boolSimps.bool_ss []
   THEN STRIP_TAC
   THEN DISCH_THEN (MP_TAC o Q.SPEC `n`)
   THEN DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
   THEN ONCE_REWRITE_TAC [MULT_COMM]
   THEN SIMP_TAC boolSimps.bool_ss [EXP, MOD_2]
   THEN (ASM_CASES_TAC “EVEN n” THEN ASM_SIMP_TAC boolSimps.bool_ss [])
   THENL [REWRITE_TAC [TWO, ADD_0, LESS_MULT_MONO],
          REWRITE_TAC [DOUBLE_LT]
          THEN REWRITE_TAC [TWO, ADD_0, LESS_MULT_MONO]]
QED

val SUB_LESS = Q.store_thm ("SUB_LESS",
 `!m n. 0 < n /\ n <= m ==> m-n < m`,
 REPEAT STRIP_TAC THEN
   “?p. m = p+n” via METIS_TAC [LESS_EQ_EXISTS,ADD_SYM]
   THEN RW_TAC bool_ss [ADD_SUB]
   THEN METIS_TAC [LESS_ADD_NONZERO,NOT_ZERO_LT_ZERO]);

val SUB_MOD = Q.store_thm ("SUB_MOD",
 `!m n. 0<n /\ n <= m ==> ((m-n) MOD n = m MOD n)`,
 METIS_TAC [ADD_MODULUS,ADD_SUB,LESS_EQ_EXISTS,ADD_SYM]);

val ONE_LT_MULT_IMP = Q.store_thm ("ONE_LT_MULT_IMP",
 `!p q. 1 < p /\ 0 < q ==> 1 < p * q`,
 REPEAT Cases THEN
 RW_TAC bool_ss [MULT_CLAUSES,ADD_CLAUSES] THENL
 [METIS_TAC [LESS_REFL],
  POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  RW_TAC bool_ss [ONE,LESS_MONO_EQ] THEN
  METIS_TAC [LESS_IMP_LESS_ADD, ADD_ASSOC]]);

val ONE_LT_MULT = Q.store_thm ("ONE_LT_MULT",
 `!x y. 1 < x * y <=> 0 < x /\ 1 < y \/ 0 < y /\ 1 < x`,
 REWRITE_TAC [ONE] THEN INDUCT_TAC THEN
 RW_TAC bool_ss [ADD_CLAUSES, MULT_CLAUSES,LESS_REFL,LESS_0] THENL
  [METIS_TAC [NOT_SUC_LESS_EQ_0,LESS_OR_EQ],
   Cases_on ‘y’ THEN
   RW_TAC bool_ss [MULT_CLAUSES,ADD_CLAUSES,LESS_REFL,
           LESS_MONO_EQ,ZERO_LESS_ADD,LESS_0] THEN
   METIS_TAC [ZERO_LESS_MULT]]);

Theorem ONE_LT_EXP[simp]:
   !x y. 1 < x ** y <=> 1 < x /\ 0 < y
Proof
 GEN_TAC THEN INDUCT_TAC THEN
 RW_TAC bool_ss [EXP,ONE_LT_MULT,LESS_REFL,LESS_0,ZERO_LT_EXP] THEN
 METIS_TAC [SUC_LESS, ONE]
QED

Theorem TWO_LE_EXP[simp]:
  !x y. 2 <= x ** y <=> 1 < x /\ 0 < y
Proof
  REWRITE_TAC[LESS_EQ_IFF_LESS_SUC, TWO, LESS_MONO_EQ, ONE_LT_EXP]
QED

(*---------------------------------------------------------------------------*)
(* Calculating DIV and MOD by repeated subtraction. We define a              *)
(* tail-recursive function DIVMOD by wellfounded recursion. We hand-roll the *)
(* definition and induction theorem, because, as of now, tfl is not          *)
(* at this point in the build.                                               *)
(*---------------------------------------------------------------------------*)

val findq_lemma = prove(
  “~(n = 0) /\ ~(m < 2 * n) ==> m - 2 * n < m - n”,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS])  THEN
  SRW_TAC [][SUB_LEFT_LESS, SUB_RIGHT_ADD, SUB_RIGHT_LESS, ADD_CLAUSES,
             SUB_LEFT_ADD]
  THENL [
    MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `n` THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC bool_ss [Once (GSYM MULT_LEFT_1), SimpLHS] THEN
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
  val M = “\f (a,m,n). if n = 0 then a
                        else let d = 2 * n
                             in
                               if m < d then a else f (2 * a, m, d)”
  val measure = “measure (\ (a:num,m:num,n:num). m - n)”
  val defn = new_definition("findq_def", “findq = WFREC ^measure ^M”)
  val th0 = MP (MATCH_MP WFREC_COROLLARY defn)
               (ISPEC (rand measure) prim_recTheory.WF_measure)
  val lemma = prove(
    “~(n = 0) ==> ((let d = 2 * n in if m < d then x
                                      else if m - d < m - n then f d else z) =
                    (let d = 2 * n in if m < d then x else f d))”,
    LET_ELIM_TAC THEN Q.ASM_CASES_TAC `m < d` THEN ASM_REWRITE_TAC [] THEN
    Q.UNABBREV_TAC `d` THEN SRW_TAC [][findq_lemma])
in
  save_thm ("findq_thm",
           SIMP_RULE (srw_ss()) [RESTRICT_DEF, prim_recTheory.measure_thm,
                                 lemma]
                     (Q.SPEC `(a,m,n)` th0))
end

val findq_eq_0 = store_thm ("findq_eq_0",
  “!a m n. (findq (a, m, n) = 0) = (a = 0)”,
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC
        `!x a m n. (x = m - n) ==> ((findq (a, m, n) = 0) = (a = 0))` THEN1
        SRW_TAC [][] THEN
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [findq_thm] THEN SRW_TAC [][LET_THM] THEN
  RULE_ASSUM_TAC (SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) []) THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`2 * a`, `m`, `2 * n`] MP_TAC) THEN
  SRW_TAC [][findq_lemma, MULT_EQ_0, TWO, ONE, NOT_SUC]);

val findq_divisor = store_thm ("findq_divisor",
  “n <= m ==> findq (a, m, n) * n <= a * m”,
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
  “~(n = 0) /\ ~(m < n) ==> m - n * findq (1, m, n) < m”,
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
  val M = “\f (a,m,n). if n = 0 then (0,0)
                        else if m < n then (a, m)
                        else let q = findq (1, m, n)
                             in
                               f (a + q, m - n * q, n)”
  val measure = “measure ((FST o SND) : num#num#num -> num)”
  val defn = new_definition("DIVMOD_DEF", “DIVMOD = WFREC ^measure ^M”)
  val th0 = REWRITE_RULE [prim_recTheory.WF_measure]
                         (MATCH_MP WFREC_COROLLARY defn)
  val th1 = SIMP_RULE (srw_ss()) [RESTRICT_DEF, prim_recTheory.measure_thm]
                      (Q.SPEC `(a,m,n)` th0)
  val lemma = prove(
    “~(n = 0) /\ ~(m < n) ==>
      ((let q = findq (1,m,n) in if m - n * q < m then f q else z) =
       (let q = findq (1,m,n) in f q))”,
    SRW_TAC [][LET_THM, divmod_lemma])
in
  save_thm ("DIVMOD_THM", SIMP_RULE (srw_ss()) [lemma] th1)
end

(*---------------------------------------------------------------------------*)
(* Correctness of DIVMOD                                                     *)
(*---------------------------------------------------------------------------*)

val core_divmod_sub_lemma = prove(
  “0 < n /\ n * q <= m ==>
    (m - n * q = if m < (q + 1) * n then m MOD n
                 else m DIV n * n + m MOD n - q * n)”,
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

val MOD_SUB = store_thm ("MOD_SUB",
  “0 < n /\ n * q <= m ==> ((m - n * q) MOD n = m MOD n)”,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN
  Q.EXISTS_TAC `m DIV n - q` THEN
  Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THEN1 SRW_TAC [][NOT_ZERO_LT_ZERO] THEN
  ASM_SIMP_TAC (srw_ss()) [RIGHT_SUB_DISTRIB, DIVISION, SUB_RIGHT_ADD,
                           LE_MULT_RCANCEL, DIV_LE_X, core_divmod_sub_lemma]);

val DIV_SUB = store_thm ("DIV_SUB",
  “0 < n /\ n * q <= m ==> ((m - n * q) DIV n = m DIV n - q)”,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `m MOD n` THEN
  Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THEN1 SRW_TAC [][NOT_ZERO_LT_ZERO] THEN
  ASM_SIMP_TAC (srw_ss()) [DIVISION, RIGHT_SUB_DISTRIB, SUB_RIGHT_ADD,
                           LE_MULT_RCANCEL, DIV_LE_X, core_divmod_sub_lemma]);

val DIVMOD_CORRECT = Q.store_thm ("DIVMOD_CORRECT",
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
      SIMP_TAC bool_ss [SimpRHS, Once ADD_COMM] THEN
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

val DIVMOD_CALC = Q.store_thm ("DIVMOD_CALC",
 `(!m n. 0<n ==> (m DIV n = FST(DIVMOD(0, m, n)))) /\
  (!m n. 0<n ==> (m MOD n = SND(DIVMOD(0, m, n))))`,
 SRW_TAC [][DIVMOD_CORRECT,ADD_CLAUSES]);

(* ----------------------------------------------------------------------
    Support for using congruential rewriting and MOD
   ---------------------------------------------------------------------- *)

val MODEQ_DEF = new_definition(
  "MODEQ_DEF",
  “MODEQ n m1 m2 = ?a b. a * n + m1 = b * n + m2”);

val MODEQ_0_CONG = store_thm ("MODEQ_0_CONG",
  “MODEQ 0 m1 m2 <=> (m1 = m2)”,
  SRW_TAC [][MODEQ_DEF, MULT_CLAUSES, ADD_CLAUSES]);

val MODEQ_NONZERO_MODEQUALITY = store_thm ("MODEQ_NONZERO_MODEQUALITY",
  “0 < n ==> (MODEQ n m1 m2 <=> (m1 MOD n = m2 MOD n))”,
  SRW_TAC [][MODEQ_DEF] THEN
  Q.SPEC_THEN `n` (fn th => th |> UNDISCH |> ASSUME_TAC) DIVISION THEN
  POP_ASSUM (fn th => Q.SPEC_THEN `m1` STRIP_ASSUME_TAC th THEN
                      Q.SPEC_THEN `m2` STRIP_ASSUME_TAC th) THEN
  MAP_EVERY Q.ABBREV_TAC [`q1 = m1 DIV n`, `r1 = m1 MOD n`,
                          `q2 = m2 DIV n`, `r2 = m2 MOD n`] THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN SRW_TAC [][EQ_IMP_THM] THENL [
    `(a * n + (q1 * n + r1)) MOD n = r1`
       by (MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `a + q1` THEN
           SIMP_TAC (srw_ss()) [MULT_ASSOC, RIGHT_ADD_DISTRIB, ADD_ASSOC] THEN
           SRW_TAC [][]) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC `b + q2` THEN
    SRW_TAC [][ADD_ASSOC, RIGHT_ADD_DISTRIB],
    MAP_EVERY Q.EXISTS_TAC [`q2`, `q1`] THEN
    SRW_TAC [][AC ADD_ASSOC ADD_COMM]
  ]);

val MODEQ_THM = store_thm ("MODEQ_THM",
  “MODEQ n m1 m2 <=> (n = 0) /\ (m1 = m2) \/ 0 < n /\ (m1 MOD n = m2 MOD n)”,
  METIS_TAC [MODEQ_0_CONG, MODEQ_NONZERO_MODEQUALITY, NOT_ZERO_LT_ZERO]);

val MODEQ_INTRO_CONG = store_thm ("MODEQ_INTRO_CONG",
  “0 < n ==> MODEQ n e0 e1 ==> (e0 MOD n = e1 MOD n)”,
  METIS_TAC [MODEQ_NONZERO_MODEQUALITY]);

val MODEQ_PLUS_CONG = store_thm ("MODEQ_PLUS_CONG",
  “MODEQ n x0 x1 ==> MODEQ n y0 y1 ==> MODEQ n (x0 + y0) (x1 + y1)”,
  Q.ID_SPEC_TAC `n` THEN SIMP_TAC (srw_ss() ++ DNF_ss)[MODEQ_THM, LESS_REFL] THEN
  SRW_TAC [][Once (GSYM MOD_PLUS)] THEN SRW_TAC [][MOD_PLUS]);

val MODEQ_MULT_CONG = store_thm ("MODEQ_MULT_CONG",
  “MODEQ n x0 x1 ==> MODEQ n y0 y1 ==> MODEQ n (x0 * y0) (x1 * y1)”,
  Q.ID_SPEC_TAC `n` THEN SIMP_TAC (srw_ss() ++ DNF_ss)[MODEQ_THM, LESS_REFL] THEN
  SRW_TAC [][Once (GSYM MOD_TIMES2)] THEN SRW_TAC [][MOD_TIMES2]);

val MODEQ_REFL = store_thm ("MODEQ_REFL",
  “!x. MODEQ n x x”,
  SRW_TAC [][MODEQ_THM, GSYM NOT_ZERO_LT_ZERO]);

val MODEQ_SUC_CONG = store_thm("MODEQ_SUC_CONG",
  “MODEQ n x y ==> MODEQ n (SUC x) (SUC y)”,
  SRW_TAC[][ADD1] >> irule MODEQ_PLUS_CONG >> SRW_TAC [][MODEQ_REFL]);

val MODEQ_EXP_CONG = store_thm(
  "MODEQ_EXP_CONG",
  “MODEQ n x y ==> MODEQ n (x EXP e) (y EXP e)”,
  Q.ID_SPEC_TAC `e` >>
  INDUCT_TAC >> SRW_TAC[][EXP, MODEQ_REFL] >>
  irule MODEQ_MULT_CONG >> SRW_TAC[][])

val EXP_MOD = save_thm(
  "EXP_MOD",
  MODEQ_EXP_CONG |> SIMP_RULE bool_ss [GSYM NOT_LT_ZERO_EQ_ZERO,
                                       ASSUME “0 < n”, MODEQ_THM]
                 |> INST [“y:num” |-> “x MOD n”, “e1:num” |-> “e:num”,
                          “e2:num” |-> “e:num”]
                 |> SIMP_RULE bool_ss [MATCH_MP MOD_MOD (ASSUME “0 < n”)]
                 |> SYM |> DISCH_ALL)

val MODEQ_SYM = store_thm ("MODEQ_SYM",
  “MODEQ n x y <=> MODEQ n y x”,
  SRW_TAC [][MODEQ_THM] THEN METIS_TAC []);

val MODEQ_TRANS = store_thm ("MODEQ_TRANS",
  “!x y z. MODEQ n x y /\ MODEQ n y z ==> MODEQ n x z”,
  Q.ID_SPEC_TAC `n` THEN SIMP_TAC (srw_ss() ++ DNF_ss) [MODEQ_THM, LESS_REFL]);

val MODEQ_NUMERAL = store_thm ("MODEQ_NUMERAL",
  “(NUMERAL n <= NUMERAL m ==>
     MODEQ (NUMERAL (BIT1 n)) (NUMERAL (BIT1 m))
           (NUMERAL (BIT1 m) MOD NUMERAL (BIT1 n))) /\
    (NUMERAL n <= NUMERAL m ==>
     MODEQ (NUMERAL (BIT1 n)) (NUMERAL (BIT2 m))
           (NUMERAL (BIT2 m) MOD NUMERAL (BIT1 n))) /\
    (NUMERAL n <= NUMERAL m ==>
     MODEQ (NUMERAL (BIT2 n)) (NUMERAL (BIT2 m))
           (NUMERAL (BIT2 m) MOD NUMERAL (BIT2 n))) /\
    (NUMERAL n < NUMERAL m ==>
     MODEQ (NUMERAL (BIT2 n)) (NUMERAL (BIT1 m))
           (NUMERAL (BIT1 m) MOD NUMERAL (BIT2 n)))”,
  SIMP_TAC (srw_ss())
           [MODEQ_NONZERO_MODEQUALITY, BIT1, BIT2, ADD_CLAUSES, ALT_ZERO,
            NUMERAL_DEF, MOD_MOD, LESS_0])

val MODEQ_MOD = store_thm ("MODEQ_MOD",
  “0 < n ==> MODEQ n (x MOD n) x”,
  SIMP_TAC (srw_ss()) [MODEQ_NONZERO_MODEQUALITY, MOD_MOD]);

val MODEQ_0 = store_thm ("MODEQ_0",
  “0 < n ==> MODEQ n n 0”,
  SIMP_TAC (srw_ss()) [MODEQ_NONZERO_MODEQUALITY, DIVMOD_ID, ZERO_MOD]);

val modss = simpLib.add_relsimp {refl = MODEQ_REFL, trans = MODEQ_TRANS,
                                 weakenings = [MODEQ_INTRO_CONG],
                                 subsets = [],
                                 rewrs = [MODEQ_NUMERAL, MODEQ_MOD, MODEQ_0]}
                                (srw_ss()) ++
            SSFRAG {dprocs = [], ac = [], rewrs = [],
                    congs = [MODEQ_PLUS_CONG, MODEQ_MULT_CONG, MODEQ_SUC_CONG],
                    filter = NONE, convs = [], name = NONE}

val result1 =
    SIMP_CONV modss [ASSUME “0 < 6”, LESS_EQ_REFL, ASSUME “2 < 3”,
                     DIVMOD_ID, MULT_CLAUSES, ADD_CLAUSES,
                     ASSUME “7 MOD 6 = 1”] “(6 * x + 7 + 6 * y) MOD 6”;

val result2 =
    SIMP_CONV modss
              [ASSUME “0 < n”, MULT_CLAUSES, ADD_CLAUSES]
              “(4 + 3 * n + 1) MOD n”


(* ----------------------------------------------------------------------
    set up characterisation as a standard algebraic type
   ---------------------------------------------------------------------- *)

val num_case_eq = Q.store_thm(
  "num_case_eq",
  ‘(num_CASE n zc sc = v) <=>
     (n = 0) /\ (zc = v) \/ ?x. (n = SUC x) /\ (sc x = v)’,
  Q.SPEC_THEN ‘n’ STRUCT_CASES_TAC num_CASES THEN
  SRW_TAC [][num_case_def, SUC_NOT, INV_SUC_EQ]);

val _ = TypeBase.general_update “:num” (
          TypeBasePure.put_size (
            “λx:num. x”,
            TypeBasePure.ORIG boolTheory.REFL_CLAUSE
          ) o
          TypeBasePure.put_destructors [cj 2 prim_recTheory.PRE] o
          TypeBasePure.put_lift (
            mk_var("numSyntax.lift_num",“:'type -> num -> 'term”)
          )
        )

val datatype_num = store_thm(
  "datatype_num",
  “DATATYPE (num 0 SUC)”,
  REWRITE_TAC[DATATYPE_TAG_THM]);

Theorem binary_induct:
  !P. P (0:num) /\ (!n. P n ==> P (2*n) /\ P (2*n+1)) ==> !n. P n
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac COMPLETE_INDUCTION >> gen_tac >>
  Q.ASM_CASES_TAC‘n=0’ >> ASM_SIMP_TAC (srw_ss()) [] >>
  ‘n DIV 2 < n /\ ((n = 2 * (n DIV 2)) \/ (n = 2 * (n DIV 2) + 1))’ by (
    ‘0 < 2’ by SIMP_TAC (srw_ss()) [TWO, ONE, LESS_0] >>
    ASM_SIMP_TAC (srw_ss()) [DIV_LT_X, LT_MULT_CANCEL_LBARE] >> conj_tac
    >- (FULL_SIMP_TAC (srw_ss()) [NOT_ZERO_LT_ZERO] >>
        SIMP_TAC (srw_ss()) [TWO, ONE, LESS_MONO_EQ, LESS_0]) >>
    drule_then (Q.SPEC_THEN `n` strip_assume_tac) DIVISION >>
    Q.ABBREV_TAC ‘q = n DIV 2’ >>
    Q.ABBREV_TAC ‘r = n MOD 2’ >>
    ASM_SIMP_TAC (srw_ss()) [MULT_COMM, ADD_INV_0_EQ, EQ_ADD_LCANCEL] >>
    Q.SPEC_THEN ‘r’ FULL_STRUCT_CASES_TAC num_CASES >>
    ASM_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC (srw_ss()) [TWO, LESS_MONO_EQ, ONE] >>
    Q.RENAME_TAC [‘m < SUC 0’] >>
    Q.SPEC_THEN ‘m’ FULL_STRUCT_CASES_TAC num_CASES >>
    FULL_SIMP_TAC (srw_ss()) [LESS_MONO_EQ, NOT_LESS_0]) >>
  METIS_TAC[]
QED

Theorem EVEN_SUB:
  !m n. m <= n ==> (EVEN (n - m) <=> (EVEN n <=> EVEN m))
Proof INDUCT_TAC >> ASM_SIMP_TAC (srw_ss()) [SUB_0, EVEN] >> GEN_TAC >>
  Q.RENAME_TAC [‘SUC m <= n’] >>
  Q.SPEC_THEN ‘n’ STRUCT_CASES_TAC num_CASES >>
  ASM_SIMP_TAC (srw_ss()) [NOT_SUC_LESS_EQ_0, LESS_EQ_MONO, SUB_MONO_EQ, EVEN]
QED

Theorem ODD_SUB:
  !m n. m <= n ==> (ODD (n - m) <=> (ODD n <=/=> ODD m))
Proof
  SRW_TAC [][ODD_EVEN,EVEN_SUB]
QED

(* CEILING_DIV and CEILING_MOD *)
Theorem CEILING_DIV_def[compute,allow_rebind] =
  curry new_definition "CEILING_DIV_def"
   “CEILING_DIV m n = (m + (n - 1)) DIV n”;

Theorem CEILING_MOD_def[compute,allow_rebind] =
  curry new_definition "CEILING_MOD_def"
   “CEILING_MOD m n = (n - m MOD n) MOD n”

Overload "\\\\" = “CEILING_DIV”;  (* prints as \\ *)
Overload "%%" = “CEILING_MOD”;

val _ = set_fixity "\\\\" (Infixl 600);
val _ = set_fixity "%%" (Infixl 650);

Theorem CEILING_DIV_LE_X:
  !k m n. 0 < k ==> (CEILING_DIV n k <= m <=> n <= m * k)
Proof
  rewrite_tac [CEILING_DIV_def]
  \\ rpt strip_tac
  \\ imp_res_tac DIV_LE_X
  \\ asm_rewrite_tac [RIGHT_ADD_DISTRIB,MULT_CLAUSES,LESS_EQ]
  \\ Q.SPEC_THEN ‘k’ strip_assume_tac num_CASES
  \\ full_simp_tac bool_ss [prim_recTheory.LESS_REFL]
  \\ rewrite_tac [ADD_SUB,ADD1,LESS_EQ_MONO_ADD_EQ,ADD_ASSOC]
  \\ rewrite_tac [SUB_0,ADD_CLAUSES,MULT_CLAUSES,LESS_EQ_0,ADD_EQ_0]
QED

Theorem CEILING_DIV:
  !k. 0 < k ==> !n. CEILING_DIV n k = n DIV k + MIN (n MOD k) 1
Proof
  rewrite_tac [CEILING_DIV_def]
  \\ rpt strip_tac
  \\ drule_then (Q.SPEC_THEN ‘n’ mp_tac) DIVISION
  \\ strip_tac
  \\ PAT_X_ASSUM “n = _:num” (fn th => CONV_TAC (RATOR_CONV (SIMP_CONV bool_ss [Once th])))
  \\ rewrite_tac [GSYM ADD_ASSOC]
  \\ imp_res_tac ADD_DIV_ADD_DIV
  \\ asm_rewrite_tac [EQ_ADD_LCANCEL]
  \\ Q.SPEC_THEN ‘n MOD k = 0’ strip_assume_tac EXCLUDED_MIDDLE
  THEN1
   (imp_res_tac DIV_EQ_X
    \\ asm_rewrite_tac [ADD_CLAUSES,MIN_0,MULT_CLAUSES,ZERO_LESS_EQ]
    \\ Q.SPEC_THEN ‘k’ strip_assume_tac num_CASES
    \\ full_simp_tac bool_ss [prim_recTheory.LESS_REFL]
    \\ rewrite_tac [ADD_SUB,ADD1,LESS_EQ,LESS_EQ_REFL])
  \\ ‘MIN (n MOD k) 1 = 1’  by
   (rewrite_tac [MIN,LESS_EQ]
    \\ Q.SPEC_THEN ‘n MOD k’ strip_assume_tac num_CASES
    \\ full_simp_tac bool_ss []
    \\ rewrite_tac [ONE,LESS_EQ_MONO,NOT_SUC_LESS_EQ_0])
  \\ imp_res_tac DIV_EQ_X
  \\ asm_rewrite_tac [MULT_CLAUSES]
  \\ Q.SPEC_THEN ‘n MOD k’ strip_assume_tac num_CASES
  \\ Q.SPEC_THEN ‘k’ strip_assume_tac num_CASES
  \\ full_simp_tac bool_ss [prim_recTheory.LESS_REFL]
  \\ rewrite_tac [ADD_SUB,ADD1,LESS_EQ,LESS_EQ_REFL]
  \\ full_simp_tac bool_ss [GSYM ADD1,ADD_CLAUSES,LESS_EQ_MONO]
  \\ once_rewrite_tac [ADD_COMM]
  \\ full_simp_tac bool_ss [LESS_EQ_ADD,LE_ADD_LCANCEL,LESS_MONO_EQ]
  \\ asm_rewrite_tac [LESS_OR_EQ]
QED

Theorem CEILING_DIV_MOD:
  !k.
    0 < k ==>
    !n. (n = k * CEILING_DIV n k - CEILING_MOD n k) /\ CEILING_MOD n k < k
Proof
  rpt strip_tac
  \\ imp_res_tac CEILING_DIV
  \\ imp_res_tac MOD_LESS
  \\ asm_rewrite_tac [CEILING_MOD_def,LEFT_ADD_DISTRIB]
  \\ Q.SPEC_THEN ‘n MOD k = 0’ strip_assume_tac EXCLUDED_MIDDLE
  THEN1
   (imp_res_tac DIVMOD_ID
    \\ asm_rewrite_tac [MIN_0,MULT_CLAUSES,ADD_CLAUSES,SUB_0]
    \\ drule_then (Q.SPEC_THEN ‘n’ mp_tac) DIVISION
    \\ disch_then (fn th => simp_tac bool_ss [Once th])
    \\ asm_rewrite_tac [ADD_CLAUSES]
    \\ simp_tac bool_ss [Once MULT_COMM])
  \\ drule_then (Q.SPEC_THEN ‘n’ mp_tac) DIVISION
  \\ disch_then (fn th => simp_tac bool_ss [Once th])
  \\ ‘MIN (n MOD k) 1 = 1’ by
   (Q.SPEC_THEN ‘n MOD k’ strip_assume_tac num_CASES
    \\ full_simp_tac bool_ss []
    \\ rewrite_tac [MIN,ONE,LESS_MONO_EQ,prim_recTheory.NOT_LESS_0])
  \\ asm_rewrite_tac [MULT_CLAUSES]
  \\ ‘(k - n MOD k) < k’ by
   (Q.SPEC_THEN ‘n MOD k’ strip_assume_tac num_CASES
    \\ Q.SPEC_THEN ‘k’ strip_assume_tac num_CASES
    \\ full_simp_tac bool_ss [prim_recTheory.LESS_REFL]
    \\ rewrite_tac [SUB_MONO_EQ,SUB_LESS_SUC])
  \\ drule_then (rewrite_tac o single) LESS_MOD
  \\ asm_rewrite_tac [SUB_LEFT_SUB,GSYM NOT_LESS]
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [ADD_ASSOC,ADD_SUB]
  \\ simp_tac bool_ss [Once MULT_COMM]
QED

Theorem LE_MULT_CEILING_DIV:
  !k. 0 < k ==> !n. n <= k * CEILING_DIV n k
Proof
  rpt strip_tac
  \\ imp_res_tac CEILING_DIV_MOD
  \\ pop_assum (K ALL_TAC)
  \\ pop_assum (fn th => simp_tac bool_ss [Once th,SUB_LESS_EQ])
QED

(* moved here from integralTheory *)
Theorem num_MAX :
    !P. (?(x:num). P x) /\ (?(M:num). !x. P x ==> x <= M) <=>
        ?m. P m /\ (!x. P x ==> x <= m)
Proof
    GEN_TAC >> reverse EQ_TAC
 >- (rpt STRIP_TAC \\
     Q.EXISTS_TAC ‘m’ >> ASM_REWRITE_TAC[] \\
     Q.EXISTS_TAC ‘m’ >> ASM_REWRITE_TAC[])
 >> DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)
 >> SUBGOAL_THEN
       “(?(M:num). !(x:num). P x ==> x <= M) <=>
        (?M. (\M. !x. P x ==> x <= M) M)” SUBST1_TAC
 >- (BETA_TAC >> REFL_TAC)
 >> DISCH_THEN (MP_TAC o MATCH_MP WOP)
 >> BETA_TAC >> CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘n’ >> ASM_REWRITE_TAC[]
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> STRUCT_CASES_TAC (Q.SPEC ‘n’ num_CASES)
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      UNDISCH_THEN “!(x:num). P x ==> x <= (0:num)”
        (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)) \\
      REWRITE_TAC[NOT_LESS_EQUAL] >> STRIP_TAC \\
      POP_ASSUM(MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)) \\
      REWRITE_TAC[] >> STRIP_TAC >> RES_TAC \\
      MP_TAC (Q.SPEC ‘x’ LESS_0_CASES) >> ASM_REWRITE_TAC[] \\
      DISCH_THEN (SUBST_ALL_TAC o SYM) >> ASM_REWRITE_TAC[],
      (* goal 2 (of 2) *)
      POP_ASSUM (MP_TAC o Q.SPEC ‘n'’) \\
      REWRITE_TAC [LESS_SUC_REFL] \\
      SUBGOAL_THEN “!x y. ~(x ==> y) <=> x /\ ~y”
        (fn th => REWRITE_TAC[th] THEN STRIP_TAC) >- REWRITE_TAC [NOT_IMP] \\
      UNDISCH_THEN “!(x:num). P x ==> x <= SUC n'” (MP_TAC o Q.SPEC ‘x'’) \\
      ASM_REWRITE_TAC[LESS_OR_EQ] \\
      DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        NTAC 2 (POP_ASSUM MP_TAC) THEN REWRITE_TAC[NOT_LESS_EQUAL] \\
        REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_LESS_SUC,
        (* goal 2.2 (of 2) *)
        ASM_REWRITE_TAC[] ] ]
QED

(* ------------------------------------------------------------------------- *)
(* Arithmetic Manipulations (from examples/algebra)                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: n * p = m * p <=> p = 0 \/ n = m *)
(* Proof:
       n * p = m * p
   <=> n * p - m * p = 0      by SUB_EQUAL_0
   <=>   (n - m) * p = 0      by RIGHT_SUB_DISTRIB
   <=>   n - m = 0  or p = 0  by MULT_EQ_0
   <=>    n = m  or p = 0     by SUB_EQUAL_0
*)
val MULT_RIGHT_CANCEL = store_thm(
  "MULT_RIGHT_CANCEL",
  ``!m n p. (n * p = m * p) <=> (p = 0) \/ (n = m)``,
  rw[]);

(* Theorem: p * n = p * m <=> p = 0 \/ n = m *)
(* Proof: by MULT_RIGHT_CANCEL and MULT_COMM. *)
val MULT_LEFT_CANCEL = store_thm(
  "MULT_LEFT_CANCEL",
  ``!m n p. (p * n = p * m) <=> (p = 0) \/ (n = m)``,
  rw[MULT_RIGHT_CANCEL, MULT_COMM]);

(* Theorem: m * (n * p) = n * (m * p) *)
(* Proof:
     m * (n * p)
   = (m * n) * p       by MULT_ASSOC
   = (n * m) * p       by MULT_COMM
   = n * (m * p)       by MULT_ASSOC
*)
val MULT_COMM_ASSOC = store_thm(
  "MULT_COMM_ASSOC",
  ``!m n p. m * (n * p) = n * (m * p)``,
  metis_tac[MULT_COMM, MULT_ASSOC]);

(* Theorem: 0 < n ==> ((n * m) DIV n = m) *)
(* Proof:
   Since n * m = m * n        by MULT_COMM
               = m * n + 0    by ADD_0
     and 0 < n                by given
   Hence (n * m) DIV n = m    by DIV_UNIQUE:
   |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
*)
val MULT_TO_DIV = store_thm(
  "MULT_TO_DIV",
  ``!m n. 0 < n ==> ((n * m) DIV n = m)``,
  metis_tac[MULT_COMM, ADD_0, DIV_UNIQUE]);
(* This is commutative version of:
arithmeticTheory.MULT_DIV |- !n q. 0 < n ==> (q * n DIV n = q)
*)

(* Theorem: m * (n * p) = m * p * n *)
(* Proof: by MULT_ASSOC, MULT_COMM *)
val MULT_ASSOC_COMM = store_thm(
  "MULT_ASSOC_COMM",
  ``!m n p. m * (n * p) = m * p * n``,
  metis_tac[MULT_ASSOC, MULT_COMM]);

(* Theorem: 0 < n ==> !m. (m * n = n) <=> (m = 1) *)
(* Proof: by MULT_EQ_ID *)
val MULT_LEFT_ID = store_thm(
  "MULT_LEFT_ID",
  ``!n. 0 < n ==> !m. (m * n = n) <=> (m = 1)``,
  metis_tac[MULT_EQ_ID, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !m. (n * m = n) <=> (m = 1) *)
(* Proof: by MULT_EQ_ID *)
val MULT_RIGHT_ID = store_thm(
  "MULT_RIGHT_ID",
  ``!n. 0 < n ==> !m. (n * m = n) <=> (m = 1)``,
  metis_tac[MULT_EQ_ID, MULT_COMM, NOT_ZERO_LT_ZERO]);

(* Theorem alias *)
Theorem MULT_EQ_SELF = MULT_RIGHT_ID;
(* val MULT_EQ_SELF = |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1): thm *)

(* ------------------------------------------------------------------------- *)
(* Modulo Theorems (from examples/algebra)                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ (b < n) *)
(* Proof:
   If part: (a MOD n = b) ==> ?c. (a = c * n + b) /\ (b < n)
      Or to show: ?c. (a = c * n + a MOD n) /\ a MOD n < n
      Taking c = a DIV n, this is true     by DIVISION
   Only-if part: (a = c * n + b) /\ (b < n) ==> (a MOD n = b)
      Or to show: b < n ==> (c * n + b) MOD n = b
        (c * n + b) MOD n
      = ((c * n) MOD n + b MOD n) MOD n    by MOD_PLUS
      = (0 + b MOD n) MOD n                by MOD_EQ_0
      = b MOD n                            by MOD_MOD
      = b                                  by LESS_MOD, b < n
*)
val MOD_EQN = store_thm(
  "MOD_EQN",
  ``!n. 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ (b < n)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[DIVISION] >>
  metis_tac[MOD_PLUS, MOD_EQ_0, ADD, MOD_MOD, LESS_MOD]);

(* Theorem: If n > 0, k MOD n = 0 ==> !x. (k*x) MOD n = 0 *)
(* Proof:
   (k*x) MOD n = (k MOD n * x MOD n) MOD n    by MOD_TIMES2
               = (0 * x MOD n) MOD n          by given
               = 0 MOD n                      by MULT_0 and MULT_COMM
               = 0                            by ZERO_MOD
*)
Theorem MOD_MULTIPLE_ZERO :
    !n k. 0 < n /\ (k MOD n = 0) ==> !x. ((k*x) MOD n = 0)
Proof
  metis_tac[MOD_TIMES2, MULT_0, MULT_COMM, ZERO_MOD]
QED

(* Theorem: (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n *)
(* Proof:
     (x + y + z) MOD n
   = ((x + y) MOD n + z MOD n) MOD n               by MOD_PLUS
   = ((x MOD n + y MOD n) MOD n + z MOD n) MOD n   by MOD_PLUS
   = (x MOD n + y MOD n + z MOD n) MOD n           by MOD_MOD
*)
val MOD_PLUS3 = store_thm(
  "MOD_PLUS3",
  ``!n. 0 < n ==> !x y z. (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n``,
  metis_tac[MOD_PLUS, MOD_MOD]);

(* Theorem: Addition is associative in MOD: if x, y, z all < n,
            ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n. *)
(* Proof:
     ((x * y) MOD n * z) MOD n
   = (((x * y) MOD n) MOD n * z MOD n) MOD n     by MOD_TIMES2
   = ((x * y) MOD n * z MOD n) MOD n             by MOD_MOD
   = (x * y * z) MOD n                           by MOD_TIMES2
   = (x * (y * z)) MOD n                         by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n             by MOD_TIMES2
   = (x MOD n * ((y * z) MOD n) MOD n) MOD n     by MOD_MOD
   = (x * (y * z) MOD n) MOD n                   by MOD_TIMES2
   or
     ((x + y) MOD n + z) MOD n
   = ((x + y) MOD n + z MOD n) MOD n     by LESS_MOD, z < n
   = (x + y + z) MOD n                   by MOD_PLUS
   = (x + (y + z)) MOD n                 by ADD_ASSOC
   = (x MOD n + (y + z) MOD n) MOD n     by MOD_PLUS
   = (x + (y + z) MOD n) MOD n           by LESS_MOD, x < n
*)
val MOD_ADD_ASSOC = store_thm(
  "MOD_ADD_ASSOC",
  ``!n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==>
              ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n``,
  metis_tac[LESS_MOD, MOD_PLUS, ADD_ASSOC]);

(* Theorem: mutliplication is associative in MOD:
            (x*y MOD n * z) MOD n = (x * y*Z MOD n) MOD n  *)
(* Proof:
     ((x * y) MOD n * z) MOD n
   = (((x * y) MOD n) MOD n * z MOD n) MOD n     by MOD_TIMES2
   = ((x * y) MOD n * z MOD n) MOD n             by MOD_MOD
   = (x * y * z) MOD n                           by MOD_TIMES2
   = (x * (y * z)) MOD n                         by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n             by MOD_TIMES2
   = (x MOD n * ((y * z) MOD n) MOD n) MOD n     by MOD_MOD
   = (x * (y * z) MOD n) MOD n                   by MOD_TIMES2
   or
     ((x * y) MOD n * z) MOD n
   = ((x * y) MOD n * z MOD n) MOD n    by LESS_MOD, z < n
   = (((x * y) * z) MOD n) MOD n        by MOD_TIMES2
   = ((x * (y * z)) MOD n) MOD n        by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n    by MOD_TIMES2
   = (x * (y * z) MOD n) MOD n          by LESS_MOD, x < n
*)
val MOD_MULT_ASSOC = store_thm(
  "MOD_MULT_ASSOC",
  ``!n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==>
              ((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n``,
  metis_tac[LESS_MOD, MOD_TIMES2, MULT_ASSOC]);

(* Theorem: If n > 0, ((n - x) MOD n + x) MOD n = 0  for x < n. *)
(* Proof:
     ((n - x) MOD n + x) MOD n
   = ((n - x) MOD n + x MOD n) MOD n    by LESS_MOD
   = (n - x + x) MOD n                  by MOD_PLUS
   = n MOD n                            by SUB_ADD and 0 <= n
   = (1*n) MOD n                        by MULT_LEFT_1
   = 0                                  by MOD_EQ_0
*)
val MOD_ADD_INV = store_thm(
  "MOD_ADD_INV",
  ``!n x. 0 < n /\ x < n ==> (((n - x) MOD n + x) MOD n = 0)``,
  metis_tac[LESS_MOD, MOD_PLUS, SUB_ADD, LESS_IMP_LESS_OR_EQ, MOD_EQ_0, MULT_LEFT_1]);

(* Theorem: n < m ==> ((n MOD m = 0) <=> (n = 0)) *)
(* Proof:
   Note n < m ==> (n MOD m = n)    by LESS_MOD
   Thus (n MOD m = 0) <=> (n = 0)  by above
*)
val MOD_EQ_0_IFF = store_thm(
  "MOD_EQ_0_IFF",
  ``!m n. n < m ==> ((n MOD m = 0) <=> (n = 0))``,
  rw_tac bool_ss[LESS_MOD]);

(* Theorem: ((a MOD n) ** m) MOD n = (a ** m) MOD n  *)
(* Proof: by induction on m.
   Base case: (a MOD n) ** 0 MOD n = a ** 0 MOD n
       (a MOD n) ** 0 MOD n
     = 1 MOD n              by EXP
     = a ** 0 MOD n         by EXP
   Step case: (a MOD n) ** m MOD n = a ** m MOD n ==> (a MOD n) ** SUC m MOD n = a ** SUC m MOD n
       (a MOD n) ** SUC m MOD n
     = ((a MOD n) * (a MOD n) ** m) MOD n             by EXP
     = ((a MOD n) * (((a MOD n) ** m) MOD n)) MOD n   by MOD_TIMES2, MOD_MOD
     = ((a MOD n) * (a ** m MOD n)) MOD n             by induction hypothesis
     = (a * a ** m) MOD n                             by MOD_TIMES2
     = a ** SUC m MOD n                               by EXP
*)
val MOD_EXP = store_thm(
  "MOD_EXP",
  ``!n. 0 < n ==> !a m. ((a MOD n) ** m) MOD n = (a ** m) MOD n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[EXP] >>
  `(a MOD n) ** SUC m MOD n = ((a MOD n) * (a MOD n) ** m) MOD n` by rw[EXP] >>
  `_ = ((a MOD n) * (((a MOD n) ** m) MOD n)) MOD n` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = ((a MOD n) * (a ** m MOD n)) MOD n` by rw[] >>
  `_ = (a * a ** m) MOD n` by rw[MOD_TIMES2] >>
  rw[EXP]);

val _ = export_theory()
