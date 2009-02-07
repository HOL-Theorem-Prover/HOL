structure words_emitLib :> words_emitLib =
struct

open HolKernel Parse boolLib bossLib wordsTheory;
open fcp_emitTheory words_emitTheory;

val RHS_REWRITE_RULE = GEN_REWRITE_RULE (DEPTH_CONV o RAND_CONV) empty_rewrites

val WORDS_EMIT_RULE =
  BETA_RULE o PURE_REWRITE_RULE
   ([BIT_UPDATE, fcp_n2w, word_T_def, word_L_def, word_H_def, literal_case_THM]
   @
   (map GSYM [word_index_def, n2w_itself_def, w2w_itself_def, sw2sw_itself_def,
     word_concat_itself_def, word_extract_itself_def,
     FCPi_def, mk_fcp_def, literal_case_DEF])) o
  RHS_REWRITE_RULE [GSYM word_eq_def]

end
