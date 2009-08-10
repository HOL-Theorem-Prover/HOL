signature functionEncodeLib =
sig
    include Abbrev

    val trace : int -> string -> unit
    val is_encoded_term : term -> bool
    val diagnose_encoded_term : term -> unit
    val add_conditional_rewrite : int -> string -> thm -> unit
    val conditionize_rewrite : thm -> thm
    val add_standard_rewrite : int -> string -> thm -> unit
    val remove_rewrite : string -> unit
    val exists_rewrite : string -> bool
    val scrub_rewrites : unit -> unit
    val NNF_CONV : term -> thm
    val CNF_CONV : term -> thm
    val SAFE_MATCH_MP : thm -> thm -> thm
    val match_disjunction : thm -> term -> thm
    val head_term : thm -> term
    val resolve_head_term : bool -> thm -> thm -> term list -> term list * thm
    val tail_thm : thm -> thm
    val dest_encdec : term -> hol_type * hol_type
    val match_encdec : term -> thm
    val dest_decenc : term -> hol_type * hol_type
    val match_decenc : term -> thm
    val dest_encdet : term -> hol_type * hol_type
    val match_encdet : term -> thm
    val partial_resolve : bool -> (term -> thm) list -> thm -> thm
    val full_resolve : (term -> thm) list -> thm -> thm
    val resolve_functions : thm list -> (term -> thm) list
    val include_assumption_list :
    	thm list -> thm list * thm list -> thm list * thm list
    val match_single_rewrite : thm list -> term ->
    			     int * string * thm -> string * thm
    val return_matches : thm list -> term ->
    		       	 (string * thm) list * (string * thm) list
    val remove_head : thm -> thm -> thm
    val HO_INST_TY_TERM :
    	{redex : term, residue : term} list *
  	{redex : hol_type, residue : hol_type} list -> thm -> thm
    val ho_inst_ty_term :
    	{redex : term, residue : term} list *
  	{redex : hol_type, residue : hol_type} list -> term -> term

    val append_detector : hol_type -> 'a list * term -> thm list -> thm list
    val PROPAGATE_THENC_data :
    	     ((thm list * thm list) * (thm list * thm list -> term -> thm) *
	     	   	(string * thm)) list ref;
    val PROPAGATE_THENC :
    	thm list * thm list -> (thm list * thm list -> term -> thm) ->
  	    	 string * thm -> thm
    val describe_match_failure :
    	(((string * thm) list * thm list) * term) list -> 'c
    val backchain_rewrite : int -> thm list -> term -> thm
    val fix_extra : thm * thm list -> thm list
    val fix_assum : thm * thm list -> thm list
    val ATTEMPT_REWRITE_PROOF :
    	thm list * thm list -> string * thm -> string * thm
    val PROPAGATE_ENCODERS_CONV : thm list * thm list -> term -> thm
    val step_PROPAGATE_ENCODERS_CONV : thm list * thm list -> term -> thm

    val add_terminal : string * (term -> bool) -> unit
    val add_extended_terminal : string * (thm list -> term -> bool) -> unit
    val remove_terminal : string -> unit
    val add_polytypic_rewrite : int -> string -> (term -> thm) -> unit
    val remove_polytypic_rewrite : string -> unit
    val add_standard_conversion : int -> string -> (term -> thm) -> unit
    val add_conditional_conversion : int -> string -> (term -> thm) -> unit
    val remove_conversion : string -> unit

    val find_comb : int list -> term -> term
    val outermost_constructor : term -> thm list -> (term -> term) option
    val group_by_constructor :
    	term -> (term -> term) -> thm list -> hol_type * (term * thm list) list
    val alpha_match_clauses :
    	(term -> term) -> (thm * 'c list) list -> 'c list * thm list
    val condense_missing : (term -> term) -> term list -> term list
    val clause_to_case_list : int list list -> thm -> thm * term list
    val clause_to_case : thm -> thm * term list
    val mk_func_case_thm : hol_type -> thm
    val create_lambda_propagation_term : term -> term
    val prove_lambda_propagation_term : term -> thm
    val make_lambda_propagation_theorem : term -> thm
    val mk_affirmation_theorems : hol_type -> thm list
    val EXISTS_REFL_CONV : term -> thm
    val set_destructors : hol_type -> thm list -> unit
    val nested_constructor_theorem : hol_type -> term -> thm
    val nested_constructor_rewrite : hol_type -> term -> thm
    val mk_destructor_rewrites : hol_type -> thm list -> thm list
    val mk_predicate_resolve : hol_type -> hol_type -> thm
    val mk_predicate_rewrites : hol_type -> hol_type -> thm list * thm list
    val mk_case_propagation_theorem : hol_type -> hol_type -> thm
    val add_decodeencode_rewrites : hol_type -> hol_type -> thm
    val add_encode_rewrites : hol_type -> hol_type -> thm
    val add_case_rewrites : hol_type -> hol_type -> thm option
    val add_standard_coding_rewrites : hol_type -> hol_type -> unit
    val clear_rewrites : unit -> unit
    val polytypic_decodeencode : term -> thm
    val polytypic_casestatement : term -> thm
    val polytypic_encodes : term -> thm
    val polytypic_let_conv : term -> thm
    val target_function_conv : hol_type -> term -> thm
    val dummy_encoder_conv : hol_type -> term -> thm
    val prove_propagation_theorem_data
    	: (thm option * thm list * term) option ref
    val prove_propagation_theorem : thm list -> term -> thm
    val prove_polymorphic_propagation_theorem : thm -> thm list -> term -> thm
    val mk_analogue_definition_term :
    	hol_type -> string -> term list -> thm -> term
    val mk_analogue_definition :
    	hol_type -> string -> thm list -> term list -> thm -> thm
    val mk_polymorphic_analogue_definition :
    	hol_type -> string -> thm -> thm list -> term list
	-> thm list -> thm -> thm
    val clause_to_limit : term -> term
    val limit_to_theorems : hol_type -> term -> thm list
    val group_function_clauses : thm -> thm list
    val define_analogue : string -> thm -> thm * thm
    val complete_analogues :
    	thm list -> thm list -> thm list -> thm list -> thm
    val calculate_extra_theorems :
    	hol_type -> (thm * term list) list -> thm list
    val convert_definition :
    	hol_type -> (term * string) list ->
		 (term * term list) list -> thm list -> thm -> thm
    val convert_polymorphic_definition :
    	hol_type -> (term * string) list ->
		 (term * term list) list ->
		 (term * thm) list -> thm list -> thm -> thm

    val encode_until :
        (term -> bool) list -> thm list * thm list -> term ->
	      	       	       	       	 (thm list * term) list list * thm

    val encode_until_recursive :
        (term -> bool) list -> thm list * thm list -> term list -> term ->
	      	       	       	       	 (thm list * term) list list * thm

    val mk_fullname : hol_type -> hol_type -> string
    val SET_CODER : thm -> thm
    val generate_recognizer_terms :
    	(hol_type -> string) -> hol_type -> hol_type list -> term list
    val get_detect_type : term -> hol_type
    val subst_all : {redex : term, residue : term} list -> term -> term
    val get_wf_relation : hol_type -> thm
    val create_abstract_recognizers :
    	(hol_type -> string) -> (term -> bool) -> hol_type ->
	      hol_type -> (term list * thm list * term list)

    val ALLOW_CONV : conv -> conv
    val WF_TC_FINISH_TAC : tactic
    val WF_RECOGNIZER_TAC : tactic
    val PROPAGATE_RECOGNIZERS_TAC : thm list -> thm list -> tactic
    val TARGET_INDUCT_TAC : tactic

    val find_conditional_thm : hol_type -> thm
    val fix_definition_terms : thm list -> term list -> term list

    val get_all_detect_types : hol_type -> hol_type -> hol_type list
    val is_recursive_detect_type : hol_type -> hol_type -> bool

    val mk_summap : int -> thm -> thm
    val mk_sumstart : thm -> thm
    val mk_lex : thm -> thm -> thm
    val mk_nested_rel : term list -> thm

    val flatten_recognizers :
    	(hol_type -> string) -> hol_type -> hol_type -> thm list
    val flatten_abstract_recognizers :
    	(hol_type -> string) -> (term -> bool) ->
		  hol_type -> hol_type -> thm list
    val polytypic_recognizer : term -> thm
    val load_definitions : string -> thm list

    val encode_all_avoiding :
        (term -> bool) -> term -> thm list * thm list -> term ->
                      term list * thm list -> term list * thm list
    val make_abstract_funcs :
    	hol_type -> term list -> term list -> term list ->
  	   term list * term list
    val define_with_tactic : (term -> bool) -> conv ->
    			 tactic -> term list -> thm list * thm option
    val create_abstracted_definition_term : (term -> bool) -> hol_type ->
    	string -> term list -> thm list -> thm -> term * thm * term
    val convert_abstracted_definition  : (term -> bool) -> hol_type ->
    	string -> term list -> thm list -> thm ->
  	thm list -> tactic -> (thm -> thm -> tactic) -> thm
    val convert_abstracted_nonrec_definition : (term -> bool) -> hol_type ->
    	string -> term list -> thm list -> thm -> thm
end
