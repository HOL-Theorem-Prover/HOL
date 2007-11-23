signature polytypicLib = 
sig
	include Abbrev

(* The types required *)
type ('a,'b) dict = ('a,'b) Binarymap.dict
type goalstack = goalstackLib.goalstack

(* The types defined *)
	type translation_scheme = 
		{target : hol_type, induction : thm, recursion : thm, 
		left : term, right : term, predicate : term,
		bottom : term, bottom_thm : thm};
	type function = 
		{const : term, definition : thm,
		induction : (thm * (term * (term * hol_type)) list) option}
	datatype exception_level = Standard | Fatal | Debug;

(* The exception constructor *)
	val polyExn : exception_level * string list * string -> exn

(* Exception handling functions *)
	val exn_to_string : exn -> string
	val Raise : exn -> 'a
	val isFatal : exn -> bool
	val wrapException : string -> exn -> 'a
	val wrapExceptionHOL : string -> exn -> 'a
	val mkStandardExn : string -> string -> exn
	val mkFatalExn : string -> string -> exn
	val mkDebugExn : string -> string -> exn
	val tryfind_e : exn -> ('a -> 'b) -> 'a list -> 'b
	val first_e : exn -> ('a -> bool) -> 'a list -> 'a
	val can : ('a -> 'b) -> 'a -> bool
	val total : ('a -> 'b) -> 'a -> 'b option
	val repeat : ('a -> 'a) -> 'a -> 'a
	val debug  : bool ref
	val assert : string -> (string * ('a -> bool)) list -> 'a -> 'a
	val guarenteed : ('a -> 'b) -> 'a -> 'b

(* Tracing functions *)
	val type_trace : int -> string -> unit
	val xlist_to_string : ('a -> string) -> 'a list -> string
	val xpair_to_string : ('a -> string) -> ('b -> string) -> 'a * 'b -> string

(* Input testing *)
	val both : bool * bool -> bool
	val is_conjunction_of : (term -> bool) -> term -> bool
	val is_disjunction_of : (term -> bool) -> term -> bool
	val is_implication_of : (term -> bool) -> (term -> bool) -> term -> bool
	val is_anything : term -> bool

(* List manipulation tools *)
	val pick_e : exn -> ('a -> 'b) -> 'a list -> 'b * 'a list
	val bucket_alist : (''a * 'b) list -> (''a * 'b list) list
	val mappartition : ('a -> 'b) -> 'a list -> 'b list * 'a list
	val reachable_graph : (''a -> ''a list) -> ''a -> (''a * ''a) list
	val TC : (''a * ''a) list -> (''a * ''a) list
	val RTC : (''a * ''a) list -> (''a * ''a) list

(* Term manipulation tools *)
	val list_mk_cond : (term * term) list -> term -> term
	val mk_ring : term -> term -> term

(* Theorem manipulation tools *)
	val UNDISCH_ONLY : thm -> thm
	val UNDISCH_ALL_ONLY : thm -> thm
	val CONJUNCTS_HYP : term -> thm -> thm
	val CONV_HYP : (term -> thm) -> thm -> thm
	val CHOOSE_L : term list * thm -> thm -> thm
	val GEN_THM : term list -> thm -> thm
	val PROVE_HYP_CHECK : thm -> thm -> thm
	val ADDR_AND_CONV : term -> term -> thm
	val ADDL_AND_CONV : term -> term -> thm
	val MATCH_CONV : thm -> term -> thm
	val ORDER_FORALL_CONV : term list -> term -> thm
	val ORDER_EXISTS_CONV : term list -> term -> thm
	val UNBETA_LIST_CONV : term list -> term -> thm
	val NTH_CONJ_CONV : int -> (term -> thm) -> term -> thm
	val PUSH_COND_CONV : term -> thm
	val MK_CONJ : thm -> thm -> thm
	val LIST_MK_CONJ : thm list -> thm
	val TC_THMS : thm list -> thm list
	val prove_rec_fn_exists : thm -> term -> thm
	val UNDISCH_EQ : thm -> thm
	val UNDISCH_ALL_EQ : thm -> thm

(* Type manipulation tools *)
	val constructors_of : hol_type -> term list
	val base26 : int -> char list
	val base_type : hol_type -> hol_type
	val cannon_type : hol_type -> hol_type
	val sub_types : hol_type -> hol_type list
	val uncurried_subtypes : hol_type -> hol_type list
	val split_nested_recursive_set : hol_type -> (hol_type * (hol_type list * hol_type list)) list
	val zip_on_types : ('a -> hol_type) -> ('b -> hol_type) -> 'a list -> 'b list -> ('a * 'b) list
	val get_type_string : hol_type -> string
	val SAFE_INST_TYPE : {redex : hol_type, residue : hol_type} list -> thm -> thm
	val safe_inst : {redex : hol_type, residue : hol_type} list -> term -> term
	val safe_type_subst : {redex : hol_type, residue : hol_type} list -> hol_type -> hol_type

(* Function checking theorems *)
	val is_source_function : term -> bool
	val is_target_function : term -> bool
	val is_expanded_function : term -> bool
	val is_single_constructor : translation_scheme -> term -> bool

(* Function splitting *)
	val RFUN_CONV : thm list -> term -> thm
	val SPLIT_HFUN_CONV : thm -> term list -> term -> thm list * term list * thm
	val SPLIT_PAIR_CONV : (term list -> term -> term -> bool) -> term list -> thm -> term -> thm list * term list * thm
	val SPLIT_FUNCTION_CONV : (term list -> term -> term -> bool) * thm -> thm list -> term -> thm
	val is_double_term_target : translation_scheme -> term list -> term -> term -> bool
	val is_double_term_source : term list -> term -> term -> bool

(* Split function definition *)
	val build_call_graph : term * term -> term list -> (int * (int list * int list)) list
	val create_mutual_theorem : (int * (int list * int list)) list -> thm -> thm
	val instantiate_mutual_theorem : thm -> term list -> thm
	val create_ind_theorem : (int * (int list * int list)) list -> translation_scheme -> thm
	val prove_recind_thms_mutual : translation_scheme -> term -> thm * thm
	val LEQ_REWRITES : term -> term -> thm list -> thm
	val prove_induction_recursion_thms : translation_scheme -> term -> thm * (term * term) list * thm

(* The function and theorem database *)
	val get_translation_scheme : hol_type -> translation_scheme
	val exists_translation_precise : hol_type -> hol_type -> bool
	val exists_translation : hol_type -> hol_type -> bool
	val add_translation : hol_type -> hol_type -> unit
	val add_translation_precise : hol_type -> hol_type -> unit
	val get_translation_precise : hol_type -> hol_type -> (string,function) dict ref
	val get_translation : hol_type -> hol_type -> (string,function) dict ref
	val get_theorems_precise : hol_type -> hol_type -> (string, thm) dict ref
	val get_theorems : hol_type -> hol_type -> (string, thm) dict ref
	val add_translation_scheme : hol_type -> thm -> thm -> unit
	val clearCoding : unit -> unit
	val clearSource : unit -> unit

(* Function retrieval *)
	val exists_coding_function_precise : hol_type -> hol_type -> string -> bool
	val exists_coding_function : hol_type -> hol_type -> string -> bool
	val get_coding_function_precise : hol_type -> hol_type -> string -> function
	val get_coding_function : hol_type -> hol_type -> string -> function
	val get_coding_function_def : hol_type -> hol_type -> string -> thm
  	val get_coding_function_const : hol_type -> hol_type -> string -> term
  	val get_coding_function_induction : hol_type -> hol_type -> string -> thm * (term * (term * hol_type)) list
	val get_coding_function_precise_def : hol_type -> hol_type -> string -> thm
	val get_coding_function_precise_const : hol_type -> hol_type -> string -> term
	val get_coding_function_precise_induction : hol_type -> hol_type -> string -> thm * (term * (term * hol_type)) list
	val add_coding_function_precise : hol_type -> hol_type -> string -> function -> unit
	val add_coding_function : hol_type -> hol_type -> string -> function -> unit
	val exists_source_function_precise : hol_type -> string -> bool
	val exists_source_function : hol_type -> string -> bool
	val get_source_function_precise : hol_type -> string -> function
	val get_source_function : hol_type -> string -> function
	val get_source_function_def : hol_type -> string -> thm
	val get_source_function_const : hol_type -> string -> term
	val get_source_function_induction : hol_type -> string -> thm * (term * (term * hol_type)) list
	val get_source_function_precise_def : hol_type -> string -> thm
	val get_source_function_precise_const : hol_type -> string -> term
	val get_source_function_precise_induction : hol_type -> string -> thm * (term * (term * hol_type)) list
	val add_source_function_precise : hol_type -> string -> function -> unit
	val add_source_function : hol_type -> string -> function -> unit

(* Theorem retrieval *)
	val exists_coding_theorem_precise : hol_type -> hol_type -> string -> bool
	val exists_coding_theorem : hol_type -> hol_type -> string -> bool
	val add_coding_theorem_precise : hol_type -> hol_type -> string -> thm -> unit
	val add_coding_theorem : hol_type -> hol_type -> string -> thm -> unit
	val get_coding_theorem_precise : hol_type -> hol_type -> string -> thm
	val get_coding_theorem : hol_type -> hol_type -> string -> thm
	val exists_source_theorem_precise : hol_type -> string -> bool
	val exists_source_theorem : hol_type -> string -> bool
	val get_source_theorem_precise : hol_type -> string -> thm
	val get_source_theorem : hol_type -> string -> thm
	val add_source_theorem_precise : hol_type -> string -> thm -> unit
	val add_source_theorem : hol_type -> string -> thm -> unit
	val remove_source_theorem_precise : hol_type -> string -> unit
	val remove_coding_theorem_precise : hol_type -> hol_type -> string -> unit

(* Function creation tools *)
	val inst_function_def : (hol_type -> thm) -> (hol_type -> term) -> hol_type -> thm
	val expanded_function_def : (term -> thm) -> (term -> thm) -> (hol_type -> thm) -> hol_type -> term list -> thm
	val mk_split_source_function : (hol_type -> term) -> (hol_type -> thm) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> hol_type -> thm * thm
	val mk_split_target_function : (hol_type -> term) -> (hol_type -> thm) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> translation_scheme -> hol_type -> (thm * (term * term) list * thm) * thm

(* Removal of function splits *)
	val MATCH_IND_TERM : term -> thm -> thm
	val strengthen_proof_term : thm list -> term -> thm
	val prove_split_term : (term * (term * hol_type)) list -> thm -> thm -> thm * term -> term -> thm
	val prove_all_split_terms : (hol_type -> thm * (term * (term * hol_type)) list) * (hol_type -> thm) * (term -> thm) * (term -> thm) * thm * term -> (term * hol_type) list -> thm -> thm list * thm
	val remove_hyp_terms : thm -> thm list -> thm list * thm -> thm
	val match_mapping : thm -> (term * term) list -> (hol_type -> term) -> thm -> hol_type -> (term * (term * hol_type)) list
	val unsplit_function : (hol_type -> thm * (term * (term * hol_type)) list) -> (hol_type -> thm) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> thm * term -> hol_type -> thm * thm -> thm

(* Full function creation *)
	val mk_source_functions : string -> (hol_type -> term) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> hol_type -> unit
	val mk_coding_functions : string -> (hol_type -> term) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> hol_type -> hol_type -> unit
	val mk_target_functions : string -> (hol_type -> term) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> hol_type -> hol_type -> unit

(* Automatic generation of functions *)
	val add_coding_function_generator : hol_type -> string -> (hol_type -> bool) -> (hol_type -> function) -> unit
	val add_source_function_generator : string -> (hol_type -> bool) -> (hol_type -> function) -> unit
	val generate_coding_function : hol_type -> string -> hol_type -> unit
	val generate_source_function : string -> hol_type -> unit
	val add_compound_coding_function_generator : string -> (hol_type -> term) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> hol_type -> unit
	val add_compound_target_function_generator : string -> (hol_type -> term) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> hol_type -> unit
	val add_compound_source_function_generator : string -> (hol_type -> term) -> (hol_type -> term) -> (term -> thm) -> (term -> thm) -> unit

(* Automatic generation of theorems *)
	val generate_coding_theorem : hol_type -> string -> hol_type -> thm
	val generate_source_theorem : string -> hol_type -> thm
	val make_predicate_map : thm -> (term * term list) list
	val all_coding_thms : hol_type list -> string -> hol_type -> hol_type -> thm list
	val all_source_thms : hol_type list -> string -> hol_type -> thm list
	val prove_inductive_coding_theorem : string-> string -> (hol_type -> term) -> hol_type -> hol_type -> (term -> thm) -> 
						(hol_type -> thm list -> tactic) -> unit
	val inductive_coding_goal : string -> 'b -> (hol_type -> 'c) -> hol_type -> hol_type -> ('c -> thm) -> goalstack
	val prove_inductive_source_theorem : string -> string -> (hol_type -> term) -> hol_type -> (term -> thm) -> (hol_type -> thm list -> tactic) -> unit
	val inductive_source_goal : string -> 'b -> (hol_type -> 'c) -> hol_type -> ('c -> thm) -> goalstack
	val add_inductive_coding_theorem_generator : string -> string -> (hol_type -> term) -> hol_type -> (term -> thm) -> (hol_type -> thm list -> term list * term -> 
							(term list * term) list * (thm list -> thm)) -> unit
	val add_inductive_source_theorem_generator : string -> string -> (hol_type -> term) -> (term -> thm) -> (hol_type -> thm list -> tactic) -> unit
	val add_tactic_coding_theorem_generator : string -> (hol_type -> bool) -> (hol_type -> term) -> (hol_type -> tactic) -> hol_type -> unit
	val add_tactic_source_theorem_generator : string -> (hol_type -> bool) -> (hol_type -> term) -> (hol_type -> tactic) -> unit
	val add_rule_coding_theorem_generator : string -> (hol_type -> bool) -> (hol_type -> thm) -> hol_type -> unit 
	val add_rule_source_theorem_generator : string -> (hol_type -> bool) -> (hol_type -> thm) -> unit

end
