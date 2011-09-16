signature separationLogicLib =
sig

include Abbrev;

val GSYM_FUN_EQ_CONV : conv;
val RHS_CONV_RULE : conv -> thm -> thm
val ANTE_CONV : conv -> conv
val ANTE_CONV_RULE : conv -> thm -> thm




val prove_ASL_PROGRAM_ABSTRACTION_REFL : term -> term -> term -> thm

type simple_asl_program_abstraction =  term -> term -> term -> thm option;
type asl_program_abstraction =  (term -> term) -> thm list -> simple_asl_program_abstraction -> simple_asl_program_abstraction;



val search_ASL_PROGRAM_ABSTRACTION :
   (term -> term) ->
   (asl_program_abstraction list) ->
   thm list -> simple_asl_program_abstraction;


val basic_asl_program_abstractions : asl_program_abstraction list
val ASL_PROGRAM_ABSTRACTION___block_flatten___no_rec : term -> term -> term -> thm option


val ASL_SPECIFICATION___CONSEQ_CONV : conv * asl_program_abstraction list -> ConseqConv.conseq_conv

val asl_procedure_call_preserve_names_wrapper_ELIM_CONV : conv

val asl_comment_modify_INC         : term -> term
val asl_comment_modify_COPY_INIT   : term -> term
val asl_comment_modify_APPEND      : string -> term -> term
val asl_comment_modify_APPEND_INC  : string -> term -> term
val asl_comment_modify_APPEND_DEC  : string -> term -> term
val list_append_norm_CONV           : conv

val asl_comment_block_CONV                : conv -> conv
val asl_comment_abstraction_INTRO_CONV    : string -> conv
val asl_comment_location_INTRO_CONV       : term -> conv
val asl_comment_location_BLOCK_INTRO_CONV : term -> conv
val asl_comment_location2_INTRO_CONV      : term -> conv
val asl_comment_location___TF_ELIM___CONV : conv

val CONSEQ_CONV_CONGRUENCE___location_comment : ConseqConv.conseq_conv_congruence

val asl_exists_list_CONV : string -> (term -> string) -> conv

end

