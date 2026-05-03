(* Self-contained Candle pipeline demo.

   Given HOL4 proof-trace dumps *Theory.tr.gz
   in the current directory, produces a single merged Candle-ruleset
   proof trace, for a targets, in both encodings:
     merged.candle.pft.bin
     merged.candle.pft.jsonl

   Pipeline:
     1. Emit candle-preamble.pft.bin          (PFTCandlePreamble.emit)
     2. Emit {...}.candle.pft.bin             (PFTEmit.emit_theory)
     4. Merge into merged.candle.pft.bin      (PFTMerge.merge)
     5. Transcode bin -> jsonl                (PFTTranscode.transcode)
*)

val till_cv_theories = [
  "bool", "marker", "num", "sat", "combin", "relation",
  "prim_rec", "quotient", "pair", "arithmetic", "numeral",
  "cv" ]

val after_cv_theories = [
  "numpair", "ind_type", "one", "sum", "option", "While",
  "reduce", "divides", "normalForms", "pred_set", "basicSize",
  "list", "rich_list", "sorting", "finite_map", "alist",
  "indexedLists", "logroot", "sptree", "permutes", "iterate",
  "fcp", "bit", "ternaryComparisons", "string", "numposrep",
  "ASCIInumbers", "sum_num", "numeral_bit", "words", "set_sep",
  "byte", "bitstring", "set_relation", "llist", "poset",
  "set_sep", "byte", "bitstring", "fixedPoint", "path", "alignment",
  "address", "bag", "toto", "comparison",
  "mergesort", "normalizer", "gcd",
  "integer", "int_arith", "cooper", "Omega", "integer_word",
  "hrat", "hreal", "realax", "real_arith", "real", "intreal",
  "intExtension", "intReduce", "frac", "primeFactor", "rat",
  "blast", "multiword", "tailrec", "mc_multiword",
  "binary_ieee", "machine_ieee", "binary_ieeeProps",
  "location",
  "quantHeuristics", "ConseqConv", "patternMatches",
  "balanced_map", "res_quan", "int_bitwise",
  "container", "state_transformer", "errorMonad", "errorLogMonad",
  "alist_tree", "transfer", "spt_closure",
  "update",
  "lprefix_lub", "grammar", "NTproperties", "peg", "pegexec",
  "charset", "vec_map", "oset",
  "FormalLang", "regexp", "regexp_map", "regexp_compiler",
  "simpleSexp", "simpleSexpPEG", "simpleSexpParse",
  (* CakeML theories *)
  "ag32", "misc" (*,
 "Marshalling", "backendProps", "backend_common",
  "db_vars", "gc_shared", "copying_gc", "gen_gc", "gen_gc_partial",
  "mllist", "mlmap", "mloption", "mlset", "mlstring", "cfFFIType",
  "ffi", "mlint", "jsonLang", "mlrat", "mlsexp", "displayLang", "mlvector",
  "export", "export_ag32", "export_arm7", "export_arm8", "export_mips",
  "export_riscv", "export_x64", "mlprettyprinter", "namespace", "ast",
  "asm", "asmSem", "asmProps", "arm", "arm_step", "arm7_target", "arm8",
  "arm8_step", "arm8_target", "ag32_target", "crepLang", "crep_arith",
  "crep_inline", "flatLang", "flat_elim", "fpSem", "closLang", "bvi",
  "bvi_let", "bvi_tailrec", "bvl", "bvl_const", "bvl_handle", "bvl_inline",
  "bvl_jump", "clos_annotate", "clos_call", "clos_fvs", "clos_interp",
  "clos_letop", "clos_mti", "clos_number", "clos_op", "clos_ticks", "clos_known",
  "clos_to_bvl", "dataLang", "bvl_to_bvi", "data_live", "data_simp", "data_space",
  "bvi_to_data", "flat_to_clos", "fromSexp", "labLang", "lab_filter", "lab_to_target",
  "loopLang", "loop_call", "loop_live", "crep_to_loop", "loop_remove", "mips",
  "mips_step", "mips_target", "namespaceProps", "panLang", "panLexer", "panPEG",
  "panPtreeConversion", "panStatic", "pan_common", "pan_globals", "pan_simp",
  "pan_to_crep", "parmove", "pattern_common", "riscv", "riscv_step", "riscv_target",
  "semanticPrimitives", "evaluate", "ml_monadBase", "pattern_semantics", "pattern_comp",
  "flat_pattern", "reg_alloc", "linear_scan", "reg_allocProof", "linear_scanProof",
  "semanticPrimitivesProps", "closSem", "bvlSem", "bviSem", "bvlProps", "bviProps",
  "bvi_letProof", "bvi_tailrecProof", "bvl_constProof", "bvl_handleProof", "bvl_inlineProof",
  "bvl_jumpProof", "bvl_to_bviProof", "closProps", "clos_annotateProof", "clos_callProof",
  "clos_constantProof", "clos_fvsProof", "clos_interpProof", "clos_knownProps",
  "clos_letopProof", "clos_mtiProof", "clos_numberProof", "clos_opProof", "clos_ticksProof",
  "clos_knownProof", "clos_to_bvlProof", "evaluateProps", "evaluate_dec",
  "flatSem", "flatProps", "flat_elimProof", "flat_patternProof", "flat_to_closProof",
  "source_let", "source_to_flat", "source_to_source", "stackLang", "stack_names",
  "stack_remove", "tokens", "gram", "gramProps", "cmlNTProps", "lexer_fun",
  "lexer_impl", "tokenUtils", "cmlPEG", "cmlPtreeConversion", "cmlParse", "pegSound",
  "pegComplete", "typeSystem", "infer_t", "primTypes", "semantics", "parserProof",
  "source_evalProof", "source_letProof", "source_to_flatProof", "source_to_sourceProof",
  "typeSoundInvariants", "typeSysProps", "primSemEnv", "ml_prog", "ml_translator",
  "cfHeapsBase", "cfHeaps", "clFFI", "fsFFI", "fsFFIProps", "cfStore",
  "cfNormalise", "cfApp", "cf", "cfLetAuto", "ml_pmatch", "cfMain", "cfTactics",
  "ml_monad_translatorBase", "ml_monad_translator", "cfMonad", "runtimeFFI", "ml_optimise",
  "std_prelude", "xcf", "cfDiv", "RuntimeProg", "OptionProg", "ListProg", "RuntimeProof",
  "VectorProg", "StringProg", "mlbasicsProg", "IntProg", "PrettyPrinterProg",
  "RatProg", "CharProg", "Word64Prog", "Word8Prog", "Word8ArrayProg", "ArrayProg",
  "MapProg", "SetProg", "HashtableProg", "CommandLineProg", "DoubleProg", "Word8ArrayProof",
  "CommandLineProof", "MarshallingProg", "TextIOProg", "TextIOProof", "SexpProg",
  "basisProg", "commonUnif", "term", "subst", "walk", "walkstar", "unifDef", "unifProps", "collapse",
  "fmsp", "cps", "rmfmap", "tcallUnif", "unify", "infer", "inferProps", "envRel",
  "infer_eComplete", "infer_eSound", "type_dCanon", "type_eDeterm", "inferComplete",
  "inferSound", "weakening", "typeSound", "semanticsProps", "wordLang", "loop_to_word",
  "pan_to_word", "presLang", "wordConvs", "wordSem", "stackSem", "stackProps",
  "stack_namesProof", "stack_removeProof", "targetSem",
  "labSem", "labProps", "lab_filterProof", "targetProps", "lab_to_targetProof", "wordProps",
  "word_alloc", "word_allocProof", "word_bignum", "word_bignumProof", "word_copy", "word_copyProof",
  "word_cse", "word_depth", "word_depthProof", "word_elim", "word_elimProof", "word_inst",
  "word_instProof", "word_remove", "word_removeProof", "word_simp", "word_cseProof", "word_simpProof",
  "word_to_stack", "word_to_stackProof", "word_unreach", "word_to_word", "data_to_word",
  "dataSem", "dataProps", "data_liveProof", "data_simpProof", "data_spaceProof", "bvi_to_dataProof",
  "gc_combined", "stack_alloc", "stack_rawcall", "stack_rawcallProof", "stack_to_lab", "backend",
  "ag32_config", "arm7_config", "arm8_config", "backend_passes", "mips_config", "pan_to_target",
  "pan_passes", "riscv_config", "wordConvsProof", "word_gcFunctions", "data_to_word_memoryProof",
  "data_to_word_gcProof", "data_to_word_bignumProof", "data_to_word_assignProof", "stack_allocProof",
  "stack_to_labProof", "word_unreachProof",
  "word_to_wordProof", "data_to_wordProof", "backendProof", "x64", "x64_step",
  "x64_target", "x64_config", "compiler", "compilerProof"
*)
]

fun theory_pft s = s ^ ".candle.pft.bin"

val preamble_bin = theory_pft "preamble"
val compute_preamble_bin = theory_pft "compute_preamble"

val theories = ["preamble"]
  @ till_cv_theories
  @ ["compute_preamble"]
  @ after_cv_theories

fun theory_in  s = s ^ "Theory.tr.gz"
fun log s = print (s ^ "\n")

fun emit_pfts () = let

(* 1. Preamble *)
val () = log "Emitting candle preamble..."
val () = PFTCandlePreamble.emit
  {output = preamble_bin, binary = true}

(* 2. Per-theory PFTs.
   EXPECT records are debug-only and downstream tools (merge/replay/transcode)
   don't handle opcode 0xEF, so turn them off. *)
val () = PFTEmit.emit_expect := false
(*
val () = PFTEmit.emit_expect := true
*)
val () = log "Emitting per-theory Candle PFTs..."

val emit_theories =
List.app (fn s =>
  (log ("  " ^ s);
   PFTEmit.emit_theory {
     trace   = theory_in s,
     output  = theory_pft s,
     binary  = true,
     ruleset = PFTEmit.Candle
   }))

val () = emit_theories till_cv_theories
val () = PFTCandleComputePreamble.emit_file
  {output=compute_preamble_bin, binary=true}
val () = emit_theories after_cv_theories

(*
val () = log "Transcoding per-theory PFTs to JSONL..."
val () = List.app (fn s =>
  (log ("  " ^ s);
   PFTTranscode.transcode {
     input = theory_pft s, input_binary = true,
     output = s ^ ".candle.pft.jsonl", output_binary = false
   }))
  theories
*)

in () end

val targets =
    (* everything
    List.map (fn s => PFTMerge.ThyAll (s, false)) theories
    *)
    [
     PFTMerge.ThyThm ("misc", "ALL_DISTINCT_MAP_FST_toSortedAList", false)
    ]

val merged_bin = "merged.candle.pft.bin"

fun emit_merged () = let

(* 4. Merge *)
val () = log "Merging..."
val () = PFTMerge.merge {
  inputs  = List.map theory_pft theories,
  targets = targets,
  output  = merged_bin,
  binary  = true
}
val () = log ("Done.\n"
  ^ "  " ^ merged_bin)
in () end

fun emit_merged_jsonl () = let

(* 5. Transcode to JSON Lines *)
val merged_jsonl = "merged.candle.pft.jsonl"
val () = log "Transcoding to JSON Lines..."
val () = PFTTranscode.transcode {
  input = merged_bin, input_binary = true,
  output = merged_jsonl, output_binary = false
}
val () = log ("Done.\n"
  ^ "  " ^ merged_jsonl)
in () end

val () = emit_pfts()
val () = emit_merged()
