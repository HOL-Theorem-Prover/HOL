signature patternMatchesSyntax =
sig
  include Abbrev


  (******************)
  (* PMATCH_ROW     *)
  (******************)

  val PMATCH_ROW_tm   : term
  
  (* dest_PMATCH_ROW ``PMATCH_ROW p g r``
     returns (``p``, ``g``, ``r``). *)
  val dest_PMATCH_ROW : term -> (term * term * term)

  val is_PMATCH_ROW   : term -> bool

  (* [mk_PMATCH_ROW (p, g, rh)] constructs the term
     ``PMATCH_ROW p g rh``. *)     
  val mk_PMATCH_ROW : term * term * term -> term

  (* [mk_PMATCH_ROW_PABS vars (p, g, rh)] constructs the term
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

  val PMATCH_tm       : term

  (* [dest_PMATCH ``PMATCH v rows``] returns (``v``, ``rows``). *)  
  val dest_PMATCH     : term -> (term * term list)

  val is_PMATCH       : term -> bool

  val mk_PMATCH       : term -> term -> term

  (* [dest_PMATCH_COLS ``PMATCH v rows``] tries to extract the columns
     of the pattern match. Each column consists of the value of v,
     the free variables in the pattern and the column of the pattern 
     for each row. *)
  val dest_PMATCH_COLS : term -> (term * (term list * term) list) list
  
  (* internally, the columns come from a list of atterns. Sometimes
     this interface is useful as well. *)
  val dest_PATLIST_COLS : term -> term list -> (term * (term list * term) list) list

  (* applies a conversion to all rows of a pmatch *)
  val PMATCH_ROWS_CONV : conv -> conv


  (*******************)
  (* PMATCH_ROW_COND *)
  (*******************)

  val PMATCH_ROW_COND_tm   : term
  val dest_PMATCH_ROW_COND : term -> (term * term * term * term)
  val is_PMATCH_ROW_COND   : term -> bool
  val mk_PMATCH_ROW_COND : term * term * term * term -> term
  val mk_PMATCH_ROW_COND_PABS : term list -> term * term * term * term -> term
  val dest_PMATCH_ROW_COND_ABS : term -> (term * term * term * term * term)

  val PMATCH_ROW_COND_EX_tm : term
  val dest_PMATCH_ROW_COND_EX : term -> term * term * term
  val dest_PMATCH_ROW_COND_EX_ABS : term -> term * term * term * term
  val is_PMATCH_ROW_COND_EX : term -> bool
  val mk_PMATCH_ROW_COND_EX : term * term * term -> term
  val mk_PMATCH_ROW_COND_EX_PABS : term list -> term * term * term -> term
  val mk_PMATCH_ROW_COND_EX_pat : term -> term -> term
  val mk_PMATCH_ROW_COND_EX_ROW : term -> term -> term

  val PMATCH_ROW_COND_EX_ELIM_CONV : conv 

  (* [PMATCH_ROW_COND_EX_INTRO_CONV_GEN find_guard_term v t] tries
     to introduce [PMATCH_ROW_COND_EX] terms. For 
     t of the form ``?x1 ... xn. v = f x1 ... xn /\ g1 x1 ... xn /\ ...``
     it extracts the pattern [f x1 ... xn] and guard [g1 x1 ... xn /\ ...]. 
     
     The function [find_guard_term] is used to find subterms of [f x1
     ... xn] that should be abbreviated by a new variable and moved to
     the guard. It gets the list of free variables and the pattern.
  *)
  val PMATCH_ROW_COND_EX_INTRO_CONV_GEN : (term list -> term -> term option) -> term -> conv
  val PMATCH_ROW_COND_EX_INTRO_CONV : term -> conv

  (* apply PMATCH_ROW_COND_EX_INTRO_CONV to all disjuncts of an nchotomy theorem. *)
  val nchotomy2PMATCH_ROW_COND_EX_CONV_GEN : (term list -> term -> term option) -> conv
  val nchotomy2PMATCH_ROW_COND_EX_CONV : conv

  (* A version of making PMATCH_ROW_COND_EX that does the move to guards. *)
  val mk_PMATCH_ROW_COND_EX_PABS_MOVE_TO_GUARDS : 
     (term list -> term -> term option) ->
     term list -> term * term * term -> term

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


  (**************************)
  (* Labels (see markerLib) *)
  (**************************)

  (* strips multiple applications of labels *)
  val strip_labels : term -> string list * term

  (* add a list of labels to a term *)
  val add_labels_CONV : string list -> conv

  (* apply a conversion under a sequence 
     of labels *)
  val strip_labels_CONV : conv -> conv

  (* similar to [strip_labels_CONV] but fails if not at least
     one of the stripped labels has a lbl in the given list *)
  val guarded_strip_labels_CONV :
    string list -> conv -> conv


  (*******************)
  (* Auxiliary stuff *)
  (*******************)

  (* [pick_element p l] gets the first element of l that satisfies p
     and removes this occurence from the list. 
     If no such element exists, the function fails. *)
  val pick_element : ('a -> bool) -> ('a list) -> 'a * 'a list

  (* [has_subterm p t] checks whether [t] has a subterm satisfying
     predicate [p]. *)
  val has_subterm : (term -> bool) -> term -> bool  

  (* Like [prove], but quiet in case it fails. This is useful,
     when trying to prove things and are not sure, whether they
     hold. *)
  val prove_attempt : term * tactic -> thm

  (* List strip_comb, but with a maximum bound. *)
  val strip_comb_bounded : int -> term -> term * term list

  (* auxiliary function that introduces fresh 
     typevars for all type-vars used by 
     free vars of a thm *)
  val FRESH_TY_VARS_RULE : rule

  (* transforms a term to a alpha-equivalent
     one that does not use the same variable name in
     different bindings in the term. *)
  val REMOVE_REBIND_CONV : conv

  (* strips lambda abstractions *)
  val STRIP_ABS_CONV : conv -> conv

  (* strip a large disjunction and apply a conversion to all
     leafs. *)
  val ALL_DISJ_CONV : conv -> conv

  (* strip a large disjunction and apply a conversion to all
     leafs. Eliminate T and F from the resulting term by
     applying rewrites. This might be more efficient than 
     ALL_DISJ_CONV, since it stops, once a T-disjunct is found. *)
  val ALL_DISJ_TF_ELIM_CONV : conv -> conv

  (* strip a large conjunction and apply a conversion to all
     leafs. *)
  val ALL_CONJ_CONV : conv -> conv

  (* [DECEND_CONV c_desc c] applies [c] and then uses
     [c_desc] to descend into the result via [c_desc] and
     repeat. *) 
  val DECEND_CONV : (conv -> conv) -> conv -> conv

  (* Apply a conversion to all elements of a list (build
     only by cons and nil) *)
  val list_CONV : conv -> conv

  (* Apply a conversion to the nth elements of a list.
     Counting starts with 0. *)
  val list_nth_CONV : int -> conv -> conv

  (* Given a prefix [pr] and a list of variables to avoid [avoid],
     [mk_var_gen pr avoid] generates a variable generator that
     generates variable, whose name starts with [pr] and who
     are all distinct to each other and the vars in list [avoid]. *)
  val mk_var_gen : string -> term list -> (hol_type -> term)

  (* Given a prefix [pr], [mk_new_label_gen pr] generate a string
     generator for strings starting with [pr], which are all distinct
     from each other *)
  val mk_new_label_gen : string -> (unit -> string)

end
