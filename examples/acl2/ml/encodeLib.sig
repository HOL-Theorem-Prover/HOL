signature encodeLib = 
sig
	include Abbrev

	val convert_definition  : string -> thm ->
				  {acl2_definition : thm, correctness : thm, rewrite_enc_dec : thm, rewrite_encode : thm, typing : thm}
	val ACL2_DEPTH_CONV     : thm list -> thm -> term list -> term -> thm
	
	val list_predicates     : (thm * thm) list ref
	val rewrite_thms        : thm list ref
	val judgement_thms      : thm list ref
	val acl2_constants      : term list ref

	val add_stage           : int -> unit
	val remove_stage        : int -> unit

end

