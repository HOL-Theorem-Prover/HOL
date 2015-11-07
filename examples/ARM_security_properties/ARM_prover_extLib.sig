signature ARM_prover_extLib =
sig
    (* include arm_encoderLib arm_disassemblerLib*)

    val decompose_term
	: boolSyntax.term -> boolSyntax.term * boolSyntax.term * boolSyntax.term
    val mk_spec_list  : Parse.term -> Parse.term list
    val mk_spec_list2  : Parse.term -> Parse.term list
    val mk_spec_list3  : Parse.term -> Parse.term list
    val mk_spec_list4  : Parse.term -> Parse.term list
    val generate_uncurry_abs
	: Theory.term -> Theory.term list * Theory.term
    val get_monad_type  : Type.hol_type -> Type.hol_type
    val generate_uncurry_abs_from_abs
	: Theory.term -> Theory.term list * Theory.term
    val get_action_from_goal  : 'a * boolSyntax.term -> boolSyntax.term
    val find_theorem  : string -> Thm.thm
    val get_uncurried_theorem  : Thm.thm -> int -> Thm.thm
    val generalize_theorem  : Abbrev.thm -> Abbrev.term -> Thm.thm
    val get_type_inst  : Type.hol_type * bool -> Type.hol_type
    val prove_const :
	Term.term ->
	(Abbrev.term -> Term.term list -> 'a) list ->
	Term.term list ->
	'b -> string -> Abbrev.thm list -> Abbrev.thm * Abbrev.tactic
    val get_second_lemmma
	: Abbrev.thm -> Parse.term -> Parse.term -> Abbrev.thm -> Abbrev.thm
    val prove_abs_action
	:
	Abbrev.term * (Abbrev.term -> Abbrev.term list -> 'a) list *
	Abbrev.term list * 'b * Thm.thm list *
	(
	 Abbrev.term ->
	 Abbrev.term list ->
	 Term.term -> Abbrev.thm -> Thm.thm list -> 'c) *
	('b -> Abbrev.term list -> Term.term -> 'c -> Abbrev.thm) ->
	Abbrev.thm * Abbrev.tactic

end






