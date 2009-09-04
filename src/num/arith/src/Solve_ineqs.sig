signature Solve_ineqs =
sig
  type int = Arbint.int
  type term = Term.term
  type thm  = Thm.thm
  type conv = Abbrev.conv

  val CONST_TIMES_ARITH_CONV : conv
  val MULT_LEQ_BY_CONST_CONV : term -> conv
  val LEQ_CONV : conv
  val WEIGHTED_SUM :
         string ->
         ((int * (string * int) list) * (int * (string * int) list)) ->
         ((int * (string * int) list) * (unit -> thm))
  val var_to_elim : ('a * (string * int) list) list -> string
  val VAR_ELIM :
         (int * (string * int) list) list -> (int list * (unit -> thm))
end
