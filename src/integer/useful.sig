signature useful =
    sig
	val HALF_MK_ABS : Thm.thm -> Thm.thm
	val LAND_CONV : (Term.term -> Thm.thm) -> (Term.term -> Thm.thm)
	val TAUT_CONV : Term.term -> Thm.thm
	val AC : Thm.thm * Thm.thm -> Term.term -> Thm.thm
	val GEN_PAIR_TAC :
	    Term.term list * Term.term ->
	    (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm)
	val MK_COMB_TAC :
	    'a * Term.term -> ('a * Term.term) list * (Thm.thm list -> Thm.thm)
	val BINOP_TAC :
	    Term.term list * Term.term ->
	    (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm)
	val SYM_CANON_CONV :
	    Thm.thm -> (Term.term * Term.term -> bool) -> (Term.term -> Thm.thm)
	val IMP_SUBST_TAC :
	    Thm.thm -> 'a * Term.term ->
	    ('a * Term.term) list * (Thm.thm list -> Thm.thm)
	val ABBREV_TAC :
	    Term.term ->
	    (Term.term list * Term.term ->
	     (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm))
	val EXT_CONV : Term.term -> Thm.thm
	val ABS_TAC :
	    Term.term list * Term.term ->
	    (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm)
	val EQUAL_TAC :
	    Term.term list * Term.term ->
	    (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm)
	val X_BETA_CONV : Term.term -> Term.term -> Thm.thm
	val EXACT_CONV : Thm.thm list -> (Term.term -> Thm.thm)
	val HABS_CONV : Term.term -> Thm.thm
	val EXPAND_TAC :
	    string ->
	    (Term.term list * Term.term ->
	     (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm))
	val GEN_REWR_TAC :
	    ((Term.term -> Thm.thm) -> Term.term -> Thm.thm) ->
	    (Thm.thm list -> Term.term list * Term.term ->
	     (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm))
    end
