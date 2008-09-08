signature encodeLib = 
sig
	include Abbrev

	val construct_bottom_value : 
	    (hol_type -> bool) -> term -> hol_type -> term
        val set_bottom_value : hol_type -> term -> unit
	val target_bottom_value : hol_type -> term -> hol_type -> term
	val get_encode_type  : hol_type -> hol_type -> hol_type
	val get_decode_type  : hol_type -> hol_type -> hol_type
	val get_detect_type  : hol_type -> hol_type -> hol_type
	val get_map_type  : hol_type -> hol_type
	val get_all_type  : hol_type -> hol_type
	val get_fix_type  : hol_type -> hol_type -> hol_type
	val mk_encode_var  : hol_type -> hol_type -> term
	val mk_decode_var  : hol_type -> hol_type -> term
	val mk_detect_var  : hol_type -> hol_type -> term
	val mk_map_var  : hol_type -> term
	val mk_all_var  : hol_type -> term
	val mk_fix_var  : hol_type -> hol_type -> term
	val get_encode_const  : hol_type -> hol_type -> term
	val get_decode_const  : hol_type -> hol_type -> term
	val get_map_const  : hol_type -> term
	val get_all_const  : hol_type -> term
	val get_fix_const  : hol_type -> hol_type -> term
	val get_detect_const  : hol_type -> hol_type -> term
	val get_all_function  : hol_type -> term
	val get_decode_function  : hol_type -> hol_type -> term
	val get_map_function  : hol_type -> term
	val get_fix_function  : hol_type -> hol_type -> term
	val get_detect_function  : hol_type -> hol_type -> term
	val get_encode_function  : hol_type -> hol_type -> term
	val mk_detect_term  : hol_type -> hol_type -> term
	val mk_decode_term  : hol_type -> hol_type -> term
	val mk_fix_term  : hol_type -> hol_type -> term
	val mk_encode_term  : hol_type -> hol_type -> term
	val mk_map_term  : hol_type -> term
	val mk_all_term  : hol_type -> term
	val ENCODE_CONV  : thm -> term -> thm
	val DETECT_CONV  : hol_type -> term -> thm
	val DECODE_CONV  : hol_type -> term -> thm
	val FIX_CONV  : hol_type -> term -> thm
	val mk_encodes  : hol_type -> hol_type -> unit
	val CONSOLIDATE_CONV  : (term -> term) -> term -> thm
	val mk_decodes  : hol_type -> hol_type -> unit
	val mk_detects  : hol_type -> hol_type -> unit
	val mk_maps  : hol_type -> unit
	val mk_alls  : hol_type -> unit
	val mk_fixs  : hol_type -> hol_type -> unit
	val type_vars_avoiding_itself  : term -> hol_type -> hol_type list
	val check_function  : (hol_type -> term) -> hol_type -> term
	val get_sub_types : hol_type -> hol_type -> hol_type list
	val wrap_full : string -> hol_type -> exn -> 'a

	val mk_encode_decode_map_conc  : hol_type -> hol_type -> term
	val mk_encode_map_encode_conc  : hol_type -> hol_type -> term
	val mk_map_compose_conc  : hol_type -> term
	val mk_decode_encode_fix_conc  : hol_type -> hol_type -> term
	val mk_encode_detect_all_conc  : hol_type -> hol_type -> term
	val mk_map_id_conc  : hol_type -> term
	val mk_all_id_conc  : hol_type -> term
	val mk_fix_id_conc  : hol_type -> hol_type -> term
	val mk_general_detect_conc  : hol_type -> hol_type -> term
	val mk_encode_decode_conc  : hol_type -> hol_type -> term
	val mk_encode_detect_conc  : hol_type -> hol_type -> term
	val mk_decode_encode_conc  : hol_type -> hol_type -> term
	val FULL_ENCODE_DECODE_MAP_THM  : hol_type -> hol_type -> thm
	val FULL_ENCODE_DETECT_ALL_THM  : hol_type -> hol_type -> thm
	val FULL_ENCODE_MAP_ENCODE_THM  : hol_type -> hol_type -> thm
	val FULL_DECODE_ENCODE_FIX_THM  : hol_type -> hol_type -> thm
	val FULL_MAP_COMPOSE_THM  : hol_type -> thm
	val FULL_MAP_ID_THM  : hol_type -> thm
	val FULL_ALL_ID_THM  : hol_type -> thm
	val FULL_FIX_ID_THM  : hol_type -> hol_type -> thm
	val FULL_ENCODE_DECODE_THM  : hol_type -> hol_type -> thm
	val FULL_ENCODE_DETECT_THM  : hol_type -> hol_type -> thm
	val FULL_DECODE_ENCODE_THM  : hol_type -> hol_type -> thm
	val ENCODER_CONV  : term -> thm
	val APP_MAP_CONV  : term -> thm
	val APP_ALL_CONV  : term -> thm
	val DECODE_PAIR_CONV  : term -> thm
	val DETECT_PAIR_CONV  : hol_type -> term -> thm
	val encode_decode_map_tactic : hol_type -> hol_type -> term list * term -> 
		(term list * term) list * (thm list -> thm)
	val encode_map_encode_tactic : hol_type -> hol_type -> term list * term ->
		(term list * term) list * (thm list -> thm)
	val map_compose_tactic : hol_type -> term list * term -> (term list * term) list * (thm list -> thm)
	val encode_detect_all_tactic : hol_type -> hol_type -> term list * term ->
		(term list * term) list * (thm list -> thm)
	val LET_RAND_CONV  : term -> term -> thm
	val decode_encode_fix_tactic : hol_type -> 'a -> term list * term ->
		(term list * term) list * (thm list -> thm)
	val fix_id_tactic : hol_type -> hol_type -> term list * term ->
		(term list * term) list * (thm list -> thm)
	val general_detect_tactic : hol_type -> hol_type -> term list * term ->
		(term list * term) list * (thm list -> thm)
	val detect_dead_rule  : hol_type -> hol_type -> thm
	val all_id_tactic : 'a -> term list * term -> (term list * term) list * (thm list -> thm)
	val map_id_tactic : 'a -> term list * term -> (term list * term) list * (thm list -> thm)
	val initialise_source_function_generators  : unit -> unit
	val initialise_coding_function_generators  : hol_type -> unit
	val initialise_coding_theorem_generators  : hol_type -> unit

	val mk_destructors : hol_type -> hol_type -> (thm list * thm list)

	val encode_type : hol_type -> hol_type -> unit
	val gen_encode_function : hol_type -> hol_type -> term
        val gen_decode_function : hol_type -> hol_type -> term
        val gen_detect_function : hol_type -> hol_type -> term

	val MK_FST : thm -> thm
	val MK_SND : thm -> thm

        val CONSOLIDATE_CONV_data : (((term -> term) * term) option) ref
 
	val predicate_equivalence : hol_type -> hol_type -> thm
end