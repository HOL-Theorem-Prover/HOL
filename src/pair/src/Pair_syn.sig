signature Pair_syn =
  sig
   type hol_type = Type.hol_type
   type term = Term.term

	val mk_pabs : {Body:term, Bvar:term} -> term
	val mk_pforall : {Body:term, Bvar:term} -> term
	val mk_pexists : {Body:term, Bvar:term} -> term
	val mk_pselect : {Body:term, Bvar:term} -> term
	val dest_pabs : term -> {Body:term, Bvar:term}
	val dest_pforall : term -> {Body:term, Bvar:term}
	val dest_pexists : term -> {Body:term, Bvar:term}
	val dest_pselect : term -> {Body:term, Bvar:term}
	val is_pabs : term -> bool
	val is_pforall : term -> bool
	val is_pexists : term -> bool
	val is_pselect : term -> bool
	val rip_pair : term -> term list
	val is_pvar : term -> bool
	val pvariant : term list -> term -> term
	val genlike : term -> term
	val list_mk_pabs : term list * term -> term
	val list_mk_pforall : term list * term -> term
	val list_mk_pexists : term list * term -> term
	val strip_pabs : term -> term list * term
	val strip_pforall : term -> term list * term
	val strip_pexists : term -> term list * term
	val bndpair : term -> term
	val pbody : term -> term
	val occs_in : term -> term -> bool
	val is_prod : hol_type -> bool
	val dest_prod : hol_type -> hol_type * hol_type
	val mk_prod : hol_type * hol_type -> hol_type
    end;
