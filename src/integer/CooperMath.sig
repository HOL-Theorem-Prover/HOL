signature CooperMath = sig

  include Abbrev
  type num = Arbnum.num

  val cooper_compset : computeLib.compset
  val REDUCE_CONV    : term -> thm
  val gcd_t          : term

  val gcd            : Arbint.int * Arbint.int -> Arbint.int
  val gcdl           : Arbint.int list -> Arbint.int
  val lcm            : Arbint.int * Arbint.int -> Arbint.int
  val lcml           : Arbint.int list -> Arbint.int
  val extended_gcd   : num * num -> num * (Arbint.int * Arbint.int)
  val sum_var_coeffs : term -> term -> Arbint.int

  datatype dir = Left | Right
  datatype termtype = EQ | LT

  val dir_of_pair    : dir -> ('a * 'a) -> 'a
  val term_at        : dir -> term -> term
  val conv_at        : dir -> (term -> thm) -> (term -> thm)

  val move_terms_from: termtype -> dir -> (term -> bool) -> (term -> thm)
  val collect_terms  : term -> thm
  val collect_in_sum : term -> term -> thm

  val LINEAR_MULT    : conv

  (* a useful simplification conversion for division terms *)
  (* these must be in the form
          c | n * x + m * y + p * z ... + d
     where all variables have coefficients and c is a positive literal.
     There is no order required of the summands on the right however. *)
  (* Is a "QConv"; raises QConv.UNCHANGED if a term doesn't change *)
  val check_divides  : term -> thm


  (* for terms of form c int_divides n * x + ... , minimises the coefficients
     and any bare numeric literals to be their old value mod c.  c must be
     positive *)
  val minimise_divides : conv

  (* replaces
       m | a * x + b
     with
       d | b /\ ?t. x = ~p * (b/d) + t * (m/d)
     where
       d = gcd(a,m) and d = pa + qm
  *)
  val elim_sdivides  : term -> thm

  (* replaces
       m | a * x + b /\ n | u * x + v
     with
       mn | d * x + v * m * p + b * n * q /\
       d | a * v - u * b
     where
       d = gcd (an, um) = pum + qan
  *)
  val elim_paired_divides : term -> thm


  val simplify_constraints : term -> thm

  val simplify_constrained_disjunct : conv


  (* These two functions both factor out integers from sums
     Both take the factor as an arbint and as a term as the first two
     arguments (experience suggests that you usually have both of these
     values around when programming, so it seems wasteful to force the
     function to have to re-call either term_of_int or int_of_term).  *)

  (* factor_out only looks at summands of the form c * x, where c is a
     numeral, and factor_out_lits only looks at summands that are literals
     Both will do bogus things if given something to work on that doesn't
     divide cleanly, e.g., factor_out_lits (Arbint.fromInt 2) ``5 + x`` *)
  val factor_out : Arbint.int -> term -> term -> thm
  val factor_out_lits : Arbint.int -> term -> term -> thm

  val BLEAF_CONV : (conv * conv -> conv) -> conv -> conv

  (* initial phases of the procedure *)
  val phase1_CONV : conv
  val phase2_CONV : term -> conv
  val phase3_CONV : conv

end
