signature deepMatchesSyntax =
sig
  include Abbrev

  val PMATCH_tm       : term
  val PMATCH_ROW_tm   : term

  (* auxiliary function that introduces fresh 
     typevars for all type-vars used by 
     free vars of a thm *)
  val FRESH_TY_VARS_RULE : rule

  (* transforms a term to a alpha-equivalent
     one that does not use the same variable name in
     different bindings in the term. *)
  val REMOVE_REBIND_CONV : conv

  (******************)
  (* PMATCH_ROW     *)
  (******************)
  
  (* dest_PMATCH_ROW ``PMATCH_ROW p g r``
     returns (``p``, ``g``, ``r``). *)
  val dest_PMATCH_ROW : term -> (term * term * term)

  val is_PMATCH_ROW   : term -> bool

  (* [mk_PMATCH_ROW (p, g, rh)] constructs the term
     ``PMATCH_ROW p g rh``. *)     
  val mk_PMATCH_ROW : term * term * term -> term

  (* [mk_PMATCH_ROW vars (p, g, rh)] constructs the term
     ``PMATCH_ROW (\vars. p) (\vars. g) (\vars. rh)``. *)     
  val mk_PMATCH_ROW_PABS : term list -> term * term * term -> term

  (* a wrapper for [mk_PMATCH_ROW_PABS] automatically renames
     the used variables to mark them as wildcards. Moreover
     it removes unused vars.
     It returns the constructed term with a flag of whether 
     the result differs from a naive call of [mk_PMATCH_ROW_PABS]. *)
  val mk_PMATCH_ROW_PABS_WILDCARDS : term list -> term * term * term -> (bool * term)

  (* dest_PMATCH_ROW_ABS ``PMATCH_ROW (\(x,y). p x y) 
        (\(x,y). g x y) (\(x,y). r x y)``
     returns (``(x,y)``, ``p x y``, ``g x y``, ``r x y``). 
     It fails, if not all paired abstractions use the same
     variable names. *)
  val dest_PMATCH_ROW_ABS : term -> (term * term * term * term)

  (* calls dest_PMATCH_ROW_ABS and renames the abstracted vars 
     consistently to be different from the list of given vars. *)
  val dest_PMATCH_ROW_ABS_VARIANT : term list -> term -> (term * term * term * term)


  (* [PMATCH_ROW_PABS_ELIM_CONV t] 
     replaces paired lambda abstraction in t with a normal lambda
     abstraction.  It returns a theorem stating the equivalence as
     well as the original varstruct of p removed. *)
  val PMATCH_ROW_PABS_ELIM_CONV : term -> (term * thm)

  (* [PMATCH_ROW_PABS_INTRO_CONV vars t] reintroduces 
     paired abstraction again after being removed by e.g.
     [PMATCH_ROW_PABS_ELIM_CONV]. It uses [vars] for the newly
     introduced varstruct. *)     
  val PMATCH_ROW_PABS_INTRO_CONV : term -> conv

  (* [PMATCH_ROW_FORCE_SAME_VARS_CONV] renames the
     abstracted variables for the pattern, guard and right hand side
     of a row to match with each other. This invariant
     is required by many operations working on PMATCH_ROW *)
  val PMATCH_ROW_FORCE_SAME_VARS_CONV : conv
  val PMATCH_FORCE_SAME_VARS_CONV : conv

  (* [PMATCH_ROW_INTRO_WILDCARDS_CONV] renames the
     abstracted variables for the pattern, guard and right hand side
     where appropriate to start with '_'. This is printed
     as a wildcard. *)
  val PMATCH_ROW_INTRO_WILDCARDS_CONV : conv
  val PMATCH_INTRO_WILDCARDS_CONV : conv

  (******************)
  (* PMATCH         *)
  (******************)

  (* [dest_PMATCH ``PMATCH v rows``] returns (``v``, ``rows``). *)  
  val dest_PMATCH     : term -> (term * term list)

  val is_PMATCH       : term -> bool

  val mk_PMATCH       : term -> term -> term

  (* [dest_PMATCH_COLS ``PMATCH v rows``] tries to extract the columns
     of the pattern match. Each column consists of the value of v,
     the free variables in the pattern and the column of the pattern 
     for each row. *)
  val dest_PMATCH_COLS : term -> (term * (term list * term) list) list

  (* applies a conversion to all rows of a pmatch *)
  val PMATCH_ROWS_CONV : conv -> conv


  (******************)
  (* Pretty printer *)
  (******************)

  (* A pretty printer is defined and added for PMATCH.
     Whether it is use can be controled via the trace

     "use pmatch_pp"
  *)


  (******************)
  (* Parser         *)
  (******************)

  (* Writing a parser for CASES is tricky. The existing
     one can be used however. If the trace "parse deep cases"
     is set to true, standard case-expressions are parsed
     to deep-matches, otherwise the default state-expressions. *)
end
