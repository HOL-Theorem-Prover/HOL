signature IntDP_Munge =
sig

  include Abbrev
  val BASIC_CONV : string -> conv -> conv
  val COND_ABS_CONV : conv
  val NBOOL_COND_RAND_CONV : conv

  val is_presburger : term -> bool
  val non_presburger_subterms : term -> term list
  val dealwith_nats : term -> term * (thm -> thm)

  val conv_tac : conv -> tactic

end;

(*
   [BASIC_CONV s c t] normalises term t, and then applies conversion c
   in an attempt to decide t.  The string s is used to generate appropriate
   error messages, and should be the "name" of the conversion.

   [COND_ABS_CONV t] takes a term of the form
       \x. if b then L else R
   and turns it into
       if b then \x. L else \x. R
   where x doesn't occur in b but may do in L and R.

   [NBOOL_COND_RAND_CONV t] takes a term of the form
       f (if b then t else e)
   and turns it into
       if b then f t else f e
   as long as the type of t is not boolean (in which case the operand term
   should be rewritten with COND_EXPAND).

   [is_presburger t] returns true if term t is Presburger.

   [non_presburger_subterms t] returns a list of the non-Presburger
   sub-terms occurring in t.

   [dealwith_nats t] works on terms that might contain natural number
   formulas.  It returns a pair (t', f), where t' is an integer formula that
   is "equivalent" to the original (but with possible extra
   generalisations introduced).  The function f will take a theorem of the
   form |- t' = T and produce |- t = T

   [conv_tac c] creates a tactic that pulls appropriate assumptions out
   of the assumption list, adds them to the goal (using MP_TAC), and then
   calls the conversion c on that goal.  c is assumed to be a complete
   arithmetic decision procedure for integers and/or natural numbers.
   Appropriate assumptions are those whose non_presburger_subterms all
   have type ``:int`` or ``:num``.
*)
