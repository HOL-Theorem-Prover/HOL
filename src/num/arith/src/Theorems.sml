(*****************************************************************************)
(* FILE          : theorems.sml                                              *)
(* DESCRIPTION   : Theorems for arithmetic formulae.                         *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 17th February 1993                                        *)
(*****************************************************************************)

structure Theorems :> Theorems =
struct
  open Arbint
  val op << = String.<


open HolKernel boolLib

(*---------------------------------------------------------------------------
 * The following ensures that the theory of arithmetic is loaded. In the
 * future, it might be better to explicitly have an "Arithmetic" structure
 * and depend on that.
 *---------------------------------------------------------------------------*)

local open arithmeticTheory in end;

val num_ty = Arith_cons.num_ty;
val m_tm = mk_var("m", num_ty)
val n_tm = mk_var("n", num_ty)


(*===========================================================================*)
(* Theorems for normalizing arithmetic                                       *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* ONE_PLUS = |- !n. SUC n = 1 + n                                           *)
(*---------------------------------------------------------------------------*)

val ONE_PLUS = arithmeticTheory.SUC_ONE_ADD;

(*---------------------------------------------------------------------------*)
(* ZERO_PLUS = |- !m. 0 + m = m                                              *)
(*---------------------------------------------------------------------------*)

val ZERO_PLUS =
 GEN_ALL (el 1 (CONJUNCTS (arithmeticTheory.ADD_CLAUSES)));

(*---------------------------------------------------------------------------*)
(* PLUS_ZERO = |- !m. m + 0 = m                                              *)
(*---------------------------------------------------------------------------*)

val PLUS_ZERO =
 GEN_ALL (el 2 (CONJUNCTS (arithmeticTheory.ADD_CLAUSES)));

(*---------------------------------------------------------------------------*)
(* SUC_ADD1 = |- !m n. SUC (m + n) = (SUC m) + n                             *)
(*---------------------------------------------------------------------------*)

val SUC_ADD1 =
 GENL [m_tm, n_tm] (SYM (el 3 (CONJUNCTS (arithmeticTheory.ADD_CLAUSES))));

(*---------------------------------------------------------------------------*)
(* SUC_ADD2 = |- !m n. SUC (m + n) = (SUC n) + m                             *)
(*---------------------------------------------------------------------------*)

val SUC_ADD2 = arithmeticTheory.SUC_ADD_SYM;

(*---------------------------------------------------------------------------*)
(* ZERO_MULT = |- !m. 0 * m = 0                                              *)
(* MULT_ZERO = |- !m. m * 0 = 0                                              *)
(* ONE_MULT = |- !m. 1 * m = m                                               *)
(* MULT_ONE = |- !m. m * 1 = m                                               *)
(* MULT_SUC = |- !m n. (SUC m) * n = (m * n) + n                             *)
(*---------------------------------------------------------------------------*)

local
   val thms = CONJUNCTS (SPEC_ALL (arithmeticTheory.MULT_CLAUSES))
in
   val ZERO_MULT = GEN_ALL (el 1 thms)
   val MULT_ZERO = GEN_ALL (el 2 thms)
   val ONE_MULT = GEN_ALL (el 3 thms)
   val MULT_ONE = GEN_ALL (el 4 thms)
   val MULT_SUC = GENL [m_tm, n_tm] (el 5 thms)
end;

(*---------------------------------------------------------------------------*)
(* MULT_COMM = |- !m n. (m * n) = (n * m)                                    *)
(*---------------------------------------------------------------------------*)

val MULT_COMM = arithmeticTheory.MULT_SYM;

(*---------------------------------------------------------------------------*)
(* SUC_ADD_LESS_EQ_F = |- !m n. ((SUC(m + n)) <= m) = F                      *)
(*---------------------------------------------------------------------------*)

val SUC_ADD_LESS_EQ_F =
 GENL [m_tm, n_tm]
  (EQF_INTRO (SPEC_ALL (arithmeticTheory.NOT_SUC_ADD_LESS_EQ)));

(*---------------------------------------------------------------------------*)
(* MULT_LEQ_SUC = |- !m n p. m <= n = ((SUC p) * m) <= ((SUC p) * m)         *)
(*---------------------------------------------------------------------------*)

val MULT_LEQ_SUC = arithmeticTheory.MULT_LESS_EQ_SUC;

(*---------------------------------------------------------------------------*)
(* ZERO_LESS_EQ_T = |- !n. (0 <= n) = T                                      *)
(*---------------------------------------------------------------------------*)

val ZERO_LESS_EQ_T =
 GEN_ALL (EQT_INTRO (SPEC_ALL (arithmeticTheory.ZERO_LESS_EQ)));

(*---------------------------------------------------------------------------*)
(* SUC_LESS_EQ_ZERO_F = |- !n. ((SUC n) <= 0) = F                            *)
(*---------------------------------------------------------------------------*)

val SUC_LESS_EQ_ZERO_F =
 GEN_ALL (EQF_INTRO (SPEC_ALL (arithmeticTheory.NOT_SUC_LESS_EQ_0)));

(*---------------------------------------------------------------------------*)
(* ZERO_LESS_EQ_ONE_TIMES = |- !n. 0 <= (1 * n)                              *)
(*---------------------------------------------------------------------------*)

val ZERO_LESS_EQ_ONE_TIMES =
 GEN_ALL
  (SUBS [SYM (el 3 (CONJUNCTS (SPECL [n_tm, m_tm]
                                (arithmeticTheory.MULT_CLAUSES))))]
    (SPEC_ALL (arithmeticTheory.ZERO_LESS_EQ)));

(*---------------------------------------------------------------------------*)
(* LESS_EQ_PLUS = |- !m n. m <= (m + n)                                      *)
(*---------------------------------------------------------------------------*)

val LESS_EQ_PLUS = arithmeticTheory.LESS_EQ_ADD;

(*---------------------------------------------------------------------------*)
(* LESS_EQ_TRANSIT = |- !m n p. m <= n /\ n <= p ==> m <= p                  *)
(*---------------------------------------------------------------------------*)

val LESS_EQ_TRANSIT = arithmeticTheory.LESS_EQ_TRANS;

(*===========================================================================*)
(* Theorems for manipulating Boolean expressions                             *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* NOT_T_F = |- ~T = F                                                       *)
(*---------------------------------------------------------------------------*)

val NOT_T_F = el 2 (CONJUNCTS NOT_CLAUSES);

(*---------------------------------------------------------------------------*)
(* NOT_F_T = |- ~F = T                                                       *)
(*---------------------------------------------------------------------------*)

val NOT_F_T = el 3 (CONJUNCTS NOT_CLAUSES);

end
