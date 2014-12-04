signature deepMatchesSyntax =
sig
  include Abbrev

  val PMATCH_tm       : term
  val PMATCH_ROW_tm   : term

  (* auxiliary function that introduces fresh 
     typevars for all type-vars used by 
     free vars of a thm *)
  val FRESH_TY_VARS_RULE : rule


  (******************)
  (* PMATCH_ROW     *)
  (******************)
  
  (* dest_PMATCH_ROW ``PMATCH_ROW (\(x, y). (p x y, rh x y)``
     returns (``(x,y)``, ``p x y``, ``rh x y``). *)
  val dest_PMATCH_ROW : term -> (term * term * term)

  val is_PMATCH_ROW   : term -> bool

  (* [mk_PMATCH_ROW vars p rh] constructs the term
     ``PMATCH_ROW (\vars. (p vars, rh vars))``. *)     
  val mk_PMATCH_ROW : term list -> term -> term -> term

  (* [PMATCH_ROW_PABS_ELIM_CONV ``PMATCH_ROW (\(v1, ... vn). ( p (v1,
     ... vn), rh (v1, ... vn))``] removes the pair [(v1, ... vn)] and
     replaces the paired lambda abstraction with a normal lambda
     abstraction.  It returns a theorem stating the equivalence as
     well as the original varstruct removed. *)
  val PMATCH_ROW_PABS_ELIM_CONV : term -> (term * thm)

  (* [PMATCH_ROW_PABS_INTRO_CONV vars t] reintroduces 
     paired abstraction again after being removed by e.g.
     [PMATCH_ROW_PABS_ELIM_CONV]. It uses [vars] for the newly
     introduced varstruct. *)     
  val PMATCH_ROW_PABS_INTRO_CONV : term -> term -> thm


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


  (******************)
  (* Pretty printer *)
  (******************)

  (* A pretty printer is defined and added for PMATCH.
     Whether it is use can be controled via the trace

     "use pmatch_pp"
  *)


end
