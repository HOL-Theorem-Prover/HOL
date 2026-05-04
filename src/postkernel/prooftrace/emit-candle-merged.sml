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
  "ag32", "misc",
 "Marshalling", "backendProps", "backend_common",
  "db_vars", "gc_shared", "copying_gc", "gen_gc", "gen_gc_partial",
  "mllist", "mlmap", "mloption", "mlset", "mlstring", "cfFFIType",
  "ffi", "mlint", "jsonLang", "mlrat", "mlsexp", "displayLang", "mlvector",
  "export", "export_ag32", "export_arm7", "export_arm8", "export_mips",
  "export_riscv", "export_x64", "mlprettyprinter", "namespace", "ast"(*,
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

val targets =
    (* everything
    List.map (fn s => PFTMerge.ThyAll (s, false))
      (till_cv_theories @ after_cv_theories)
    *)
    [
     PFTMerge.ThyThm ("misc", "ALL_DISTINCT_MAP_FST_toSortedAList", false),
     PFTMerge.ThyThm ("namespace", "nsAll_def", false)
    ]

fun theory_pft s = s ^ ".candle.pft.bin"
fun theory_in  s = s ^ "Theory.tr.gz"
fun log s = (print (s ^ "\n"); TextIO.flushOut TextIO.stdOut)

val merged_bin = "merged.candle.pft.bin"
val merged_jsonl = "merged.candle.pft.jsonl"

datatype job =
    Preamble
  | ComputePreamble
  | Theory of string

fun job_name Preamble = "preamble"
  | job_name ComputePreamble = "compute_preamble"
  | job_name (Theory s) = s

fun job_output j = theory_pft (job_name j)

val jobs =
  [Preamble]
  @ map Theory till_cv_theories
  @ [ComputePreamble]
  @ map Theory after_cv_theories

fun find_job name =
  case List.find (fn j => job_name j = name) jobs of
    SOME j => j
  | NONE => raise Fail ("unknown emit job: " ^ name)

fun run_job Preamble =
    PFTCandlePreamble.emit {output = job_output Preamble, binary = true}
  | run_job ComputePreamble =
    PFTCandleComputePreamble.emit_file
      {output = job_output ComputePreamble, binary = true}
  | run_job (Theory s) =
    PFTEmit.emit_theory {
      trace   = theory_in s,
      output  = theory_pft s,
      binary  = true,
      ruleset = PFTEmit.Candle
    }

fun status_success st =
  case st of
    Posix.Process.W_EXITED => true
  | Posix.Process.W_EXITSTATUS w => Word8.toInt w = 0
  | _ => false

fun spawn_emit_one exe j =
  let val name = job_name j
  in case Posix.Process.fork () of
       NONE =>
         ((Posix.Process.execp (exe, [exe, "emit-one", name]))
          handle e =>
            (TextIO.output(TextIO.stdErr,
               "exec failed for " ^ name ^ ": " ^ exnMessage e ^ "\n");
             TextIO.flushOut TextIO.stdErr;
             OS.Process.exit OS.Process.failure))
     | SOME pid => (pid, name)
  end

fun remove_pid pid running =
  let
    fun go acc [] = ("<unknown>", List.rev acc)
      | go acc ((p,n)::rest) =
          if p = pid then (n, List.revAppend(acc, rest))
          else go ((p,n)::acc) rest
  in go [] running end

fun run_emit_all max_jobs =
  let
    val exe = CommandLine.name ()
    val todo = List.filter (fn j => not (OS.FileSys.access(job_output j, []))) jobs
    val () = PFTEmit.emit_expect := false
    val parallelism = Int.max(1, max_jobs)
    val total = length todo
    val completed = ref 0

    fun truncate max s =
      if String.size s <= max then s
      else if max <= 3 then String.substring(s, 0, max)
      else String.substring(s, 0, max - 3) ^ "..."

    fun running_names running =
      truncate 80 (String.concatWith "," (List.map #2 running))

    fun status pending running =
      (TextIO.output(TextIO.stdOut,
         "\rEmitting: " ^ Int.toString (!completed) ^ "/" ^
         Int.toString total ^ " done, " ^
         Int.toString (length running) ^ " running, " ^
         Int.toString (length pending) ^ " pending [" ^
         running_names running ^ "]");
       TextIO.flushOut TextIO.stdOut)

    fun finish_status () =
      (TextIO.output(TextIO.stdOut, "\n");
       TextIO.flushOut TextIO.stdOut)

    fun wait_one running =
      let
        val (pid, st) = Posix.Process.waitpid (Posix.Process.W_ANY_CHILD, [])
        val (name, running') = remove_pid pid running
      in completed := !completed + 1;
         if status_success st then
           (running', false)
         else
           (finish_status ();
            log ("FAILED " ^ name);
            (running', true))
      end

    fun loop pending running failed =
      (status pending running;
       if failed andalso null running then
         OS.Process.exit OS.Process.failure
       else if null pending andalso null running then
         finish_status ()
       else if (not failed) andalso length running < parallelism andalso
               not (null pending) then
         let val j = hd pending
             val running' = spawn_emit_one exe j :: running
         in loop (tl pending) running' failed end
       else
         let val (running', failed_here) = wait_one running
         in loop pending running' (failed orelse failed_here) end)
  in loop todo [] false end

fun run_merge () =
  (log "Merging...";
   PFTMerge.merge {
     inputs  = map job_output jobs,
     targets = targets,
     output  = merged_bin,
     binary  = true
   };
   log ("Wrote " ^ merged_bin))

fun run_transcode () =
  (log "Transcoding to JSON Lines...";
   PFTTranscode.transcode {
     input = merged_bin, input_binary = true,
     output = merged_jsonl, output_binary = false
   };
   log ("Wrote " ^ merged_jsonl))

fun usage () =
  let val exe = CommandLine.name ()
  in TextIO.output(TextIO.stdErr,
       "Usage:\n" ^
       "  " ^ exe ^ " emit-one <job-name>\n" ^
       "  " ^ exe ^ " emit-all [-j N]\n" ^
       "  " ^ exe ^ " merge\n" ^
       "  " ^ exe ^ " transcode\n" ^
       "  " ^ exe ^ " all [-j N]\n");
     OS.Process.exit OS.Process.failure
  end

fun parse_j args =
  let
    fun loop [] = 8
      | loop ["-j"] = usage ()
      | loop ("-j" :: n :: rest) =
          (case Int.fromString n of
             SOME k => if k > 0 andalso null rest then k else usage ()
           | NONE => usage ())
      | loop _ = usage ()
  in loop args end

val () =
  case CommandLine.arguments () of
    ["emit-one", name] => run_job (find_job name)
  | "emit-all" :: args => run_emit_all (parse_j args)
  | ["merge"] => run_merge ()
  | ["transcode"] => run_transcode ()
  | "all" :: args =>
      let val j = parse_j args
      in run_emit_all j; run_merge (); run_transcode () end
  | _ => usage ()
