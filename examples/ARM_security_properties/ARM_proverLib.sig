signature ARM_proverLib =
sig

    val global_mode : Parse.term ref
    val simp_thms_list : Theory.thm list ref
    val mode_changing_comp_list : Parse.term list ref
    val mode_changing_comp_list_rec
	: Term.term list -> Term.term -> bool
    val generate_uncurry_abs
	: Theory.term -> Theory.term list * Theory.term
    val decompose_term
	: boolSyntax.term -> boolSyntax.term * boolSyntax.term * boolSyntax.term
    val get_monad_type  : Type.hol_type -> Type.hol_type
    val generate_uncurry_abs_from_abs
	: Theory.term -> Theory.term list * Theory.term
    val get_type_inst  : Type.hol_type * bool -> Type.hol_type
    val get_uncurried_theorem  : Thm.thm -> int -> Thm.thm
    val generalize_theorem  : Abbrev.thm -> Abbrev.term -> Thm.thm

    val prove
	:
	Hol_pp.term ->
	Parse.term ->
	Parse.term ->
	Term.term list -> Abbrev.thm list -> Abbrev.thm * Abbrev.tactic

end
