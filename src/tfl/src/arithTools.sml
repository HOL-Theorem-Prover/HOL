(*---------------------------------------------------------------------------
 * Proof support for the theory of arithmetic. Notice that there is no
 * support for paired constructs.
 *---------------------------------------------------------------------------*)
structure arithTools :> arithTools =
struct

open arithLib Parse Drule Rewrite Tactical Tactic Conv;
infix THEN THENL;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q
fun == q x = Type q

type thm = Thm.thm
type term = Term.term;
type tactic = Abbrev.tactic
type conv = Abbrev.conv

val ARITH     = EQT_ELIM o ARITH_CONV o Parse.Term;
val ARITH_TAC = CONV_TAC ARITH_CONV;
val ARITH_CONV = ARITH_CONV;

val SUC_PRE = prove
(Term`!m n. m<n ==> (SUC(PRE n) = n)`,
GEN_TAC THEN boolTools.GEN_CASES_TAC(arithmeticTheory.num_CASES)
 THENL [ARITH_TAC, REWRITE_TAC[prim_recTheory.PRE]]);

(* Useful rewrite rules for arithmetic. *)
val std_thms = [arithmeticTheory.ADD_CLAUSES,
                arithmeticTheory.MULT_CLAUSES,
                arithmeticTheory.LEFT_ADD_DISTRIB,
                arithmeticTheory.RIGHT_ADD_DISTRIB,
                arithmeticTheory.LESS_EQ_REFL,
                arithmeticTheory.LESS_MONO_EQ,
                prim_recTheory.LESS_REFL,
                prim_recTheory.NOT_LESS_0,
                prim_recTheory.LESS_SUC_REFL,
                prim_recTheory.INV_SUC_EQ,
                prim_recTheory.PRE,
                prim_recTheory.LESS_0,
                numTheory.NOT_SUC,
                SUC_PRE];

end;
