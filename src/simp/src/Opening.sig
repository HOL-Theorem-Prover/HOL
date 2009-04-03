signature Opening = sig

   (* ----------------------------------------------------------------------
    * CONGPROC
    *
    * INPUTS
    *    The first argument should be a function implementing reflexivity
    * for the congruence relation (e.g. REFL for equality).  For any
    * reflexivity theorem you can make this easily by:
    *    fun refl x = SPEC x thm;
    *
    *    The second should be the congruence theorem for the relation
    *    Providing these two returns a function which implements a
    * congruence rule suitable for use with the TRAVERSE engine.
    * Create a congruence procedure for a given congruence rule.
    * 
    * "CONGRUENCE" PROCEDURES
    *   - Use the given continuation to derive simplified subterms
    *   - Use the provided solver to solve side conditions (solver
    * is normally just ASSUME)
    *   - Rename abstractions to avoid certain variables. (only implemented
    * for EQ_CONGPROC at present).
    *
    * NOTES FROM THE SIMPLIFIER DOCUMENTATION 
    *
    * Arbitrary extra contextual information can be introduced by
    * using "congurence rules".  These are theorems of a particular
    * shape.
    * 
    * The general form must be:
    * \begin{verbatim}
    * |- !x1 x1' ... xn xn'.
    *      side-condition1 ==>
    *      side-condition2 ==>
    *      (!v11...v1m. x1 v11 ... v1m REL x1' v11 ... v1m) ==>
    *      (!v21...v2m. [P[x1',v21,...v2m] ==>] x2 v21 ... v2m REL
    *                                           x2' v21 ... v2m) ==>
    *      ...
    *      F[x1,x2,..,xn] REL F[x1',x2',..,xn']
    * \end{verbatim}
    * That probably doesn't make much sense.  Think of F as the construct
    * over which you are expressing the congruence.  Think of x1,x2,...xn
    * as the sub-constructs which are being rewritten, some of them under
    * additional assumptions.  The implications (one on each line in the 
    * sample above) state the necessary results which need to be derived 
    * about the subcomponents before the congruence can be deduced.  Some
    * of these subcomponenets may be simplified with extra assumpions - this
    * is indicated by P[x1] above.
    * 
    * Some subterms may be functions which we want
    * to rewrite under application. See the rule for restricted 
    * quantifiers for examples.
    * The simplifier does a degree of higher order matching when
    * these variables are specified.
    * 
    * Some examples (where REL is HOL equality)
    * \begin{verbatim}
    *  |- !g g' t t' e e'.
    *        (g = g') ==>
    *        (g ==> (t = t')) ==>
    *        (~g ==> (e = e')) ==>
    *        ((g => t | e) = (g' => t' | e')) : thm
    * 
    *   |- !P P' Q Q'.
    *        (!x. P x = P' x) ==>
    *        (!x. P x ==> (Q x = Q' x)) ==>
    *        (RES_EXISTS P Q = RES_EXISTS P' Q') : thm
    * \end{verbatim}
    * 
    * ---------------------------------------------------------------------*)

   include Abbrev
   type congproc = {relation: term,
                    solver : term -> thm,
                    freevars: term list,
		    depther : (thm list * term) -> conv} -> conv
   val samerel            : term -> term -> bool
   val CONGPROC           :  (term -> conv) ->  thm -> congproc
   val rel_of_congrule    : thm -> term  
   val nconds_of_congrule : thm -> int
  
   (* ---------------------------------------------------------------------
    * EQ_CONGPROC                                                       
    *
    * Optimized implementations of the HOL equality congruence rules using the
    * built in operations AP_TERM, AP_THM, MK_ABS and MK_COMB.  These could
    * conceivably be implemented by:
    *     (x = x') ==> (f = f') ==> (f x = f' x')
    *     (b = b') ==> (\x. b) = (\x. b')
    * ---------------------------------------------------------------------*)

   val EQ_CONGPROC : congproc

end (* sig *)


