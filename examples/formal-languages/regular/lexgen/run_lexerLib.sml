open preamble;
open computeLib optionTheory;
open lexer_specTheory scottreTheory lexer_spec_to_dfaTheory lexer_runtimeTheory;


val _ = set_EVAL_skip ``eval_option_case`` (SOME 1);
val _ = set_EVAL_skip ``eval_let`` (SOME 1);
val _ = set_EVAL_skip ``COND`` (SOME 1);
val _ = set_EVAL_skip ``$\/`` (SOME 1);
val _ = set_EVAL_skip ``$/\`` (SOME 1);
val _ = add_funs [IN_LIST_TO_SET]

