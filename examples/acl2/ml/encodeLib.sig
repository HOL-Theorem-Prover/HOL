signature encodeLib = 
sig
	include Abbrev

	val convert_definition    : thm -> thm * thm

	val get_recogniser        : hol_type -> thm

	val encode_type           : hol_type -> unit
	val has_encoding          : hol_type -> bool
	val get_encode_decode_thm : hol_type -> thm
	val get_decode_encode_thm : hol_type -> thm
	val get_detect_encode_thm : hol_type -> thm
	val get_case_thm          : hol_type -> thm option
	val get_judgement_thm     : hol_type -> thm option

	val PROVE_TYPE_JUDGEMENT  : thm list -> term -> thm

end

