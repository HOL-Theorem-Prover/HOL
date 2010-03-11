(* ----------------------------------------------------------------------
    COND_REWR_CONV : thm -> bool -> (term -> thm) -> conv

    Build a conversion based on a conditional rewrite theorem.  The
    theorem must be of the form

          A |- P1 ==> ... Pm ==> (Q[x1,...,xn] = R[x1,...,xn])

    The conversion matches the input term against Q, using limited
    higher order matching.  This instantiates x1 ... xn, which the
    conversion then solves with the solver provided.  If any of the
    conditions are not solved COND_REWR_CONV fails.

    The theorem can be a permutative rewrite, such as
         |- (x = y) = (y = x)
         |- (x + y) = (y + x)

    In these cases the rewrite will be applied if

      * the ordering of the variables in the term is not in strictly
        ascending order, according to a term_lt function which places
        a total ordering on terms (Nb. The term ordering needs to be
        "AC" compatible - see Termord); or
      * if the boolean argument is true, which happens if the theorem
        being used is a bounded rewrite, and so cannot cause a loop
        when it is used.

    FAILURE CONDITIONS

    Fails if any of the assumptions cannot be solved by the solver,
    or if the term does not match the rewrite in the first place.
   ---------------------------------------------------------------------- *)

signature Cond_rewr =
sig

  include Abbrev
  type controlled_thm = BoundedRewrites.controlled_thm
  val mk_cond_rewrs  : controlled_thm -> controlled_thm list
  val IMP_EQ_CANON   : controlled_thm -> controlled_thm list
  val COND_REWR_CONV : thm -> bool ->
                       (term list -> term -> thm) -> term list -> conv
  val QUANTIFY_CONDITIONS : controlled_thm -> controlled_thm list
  val stack_limit : int ref

  val used_rewrites : thm list ref
  val track_rewrites : bool ref

end
