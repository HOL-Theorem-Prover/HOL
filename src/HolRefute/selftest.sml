open testutils
open refuteTheory
open refute_cvTheory
open sortingTheory
open realTheory
open Refute_Core
open Refute_Gen
open Refute_Cert
open Refute_Eval
open Refute_EvalCompute
open Refute_EvalSML
open Refute_EvalCv
open Refute_Extract
open Refute_QC
open cv_transLib

(* cv_std loads ratTheory, whose parser preference would otherwise make
   unannotated selftest numerals rationals. *)
val _ = numLib.prefer_num ()

val erc = ref 0
val _ = diemode := Remember erc

val _ = tprint "Refute skeleton smoke check"
val _ = require_msg (check_result (fn () => true)) (fn () => "")
                    (fn () => ()) ()

val _ = tprint "Refute support theory"

fun constructor_count ty =
  length (TypeBasePure.constructors_of (valOf (TypeBase.fetch ty)))

fun check_type (ty, count) =
  require_msg (check_result (fn () => constructor_count ty = count))
              (fn () => "unexpected TypeBase constructor count")
              (fn () => ()) ()

val _ = check_type (``:refute$rf1``, 1)
val _ = check_type (``:refute$rf2``, 2)
val _ = check_type (``:refute$rf3``, 3)
val _ = check_type (``:refute$rf4``, 4)
val _ = check_type (``:refute$rf5``, 5)
val _ = check_type (``:refute$rf6``, 6)

fun check_empty settype =
  require_msg (check_result
    (fn () => null (ThmSetData.current_data {settype = settype})))
    (fn () => "theorem set is not empty") (fn () => ()) ()

val _ = check_empty "refute_simp"
val _ = check_empty "refute_psimp"
val _ = check_empty "refute_unfold"

fun same_string_set left right =
  length left = length right andalso
  List.all (fn item => Lib.mem item right) left

fun cv_ancestry_is_separate () =
  same_string_set (Theory.parents "refute")
    ["real", "sorting", "words"] andalso
  same_string_set (Theory.parents "refute_cv") ["refute", "cv_std"] andalso
  not (Lib.mem "cv_std" (Theory.ancestry "refute"))

val _ = require_msg (check_result cv_ancestry_is_separate) (fn () =>
  "refute parents: " ^ String.concatWith ", " (Theory.parents "refute") ^
  "; refute_cv parents: " ^
  String.concatWith ", " (Theory.parents "refute_cv"))
  (fn () => ()) ()

val _ = tprint "Refute unified PRNG"

val pinned_rand_stream = [423, 509, 648, 382, 795]

fun sml_rand_stream count bound seed =
  let
    fun loop 0 _ values = rev values
      | loop remaining state values =
          let
            val (value, next) = rand_below (IntInf.fromInt bound) state
          in
            loop (remaining - 1) next (IntInf.toInt value :: values)
          end
  in
    loop count seed []
  end

fun evaluated_rand_stream conversion count bound seed =
  let
    val bound_tm = numSyntax.term_of_int bound
    fun loop 0 _ values = rev values
      | loop remaining state values =
          let
            val application = Term.list_mk_comb
              (``rand_below``, [bound_tm, state])
            val (value, next) =
              pairSyntax.dest_pair (rhs_of (conversion application))
            val value_int = Arbnum.toInt (numSyntax.dest_numeral value)
          in
            loop (remaining - 1) next (value_int :: values)
          end
  in
    loop count (numSyntax.term_of_int seed) []
  end

fun hol_rand_stream count bound seed =
  evaluated_rand_stream computeLib.EVAL_CONV count bound seed

fun cv_pinned_rand_stream () =
  let
    val term =
      ``let (x1, s1) = rand_below 1000 1;
             (x2, s2) = rand_below 1000 s1;
             (x3, s3) = rand_below 1000 s2;
             (x4, s4) = rand_below 1000 s3;
             (x5, s5) = rand_below 1000 s4
        in [x1; x2; x3; x4; x5]``
    val (values, _) = listSyntax.dest_list (rhs_of (cv_eval term))
  in
    List.map (Arbnum.toInt o numSyntax.dest_numeral) values
  end

fun prng_pin_works () =
  sml_rand_stream 5 1000 1 = pinned_rand_stream andalso
  hol_rand_stream 5 1000 1 = pinned_rand_stream andalso
  cv_pinned_rand_stream () = pinned_rand_stream

val _ = require_msg (check_result prng_pin_works) (fn () =>
  "HOL, SML, and cv PRNG streams did not match the pinned MMIX stream")
  (fn () => ()) ()

val _ = tprint "Refute cv build-time generators"

fun cv_rhs tm = rhs_of (cv_eval tm)

fun same_terms left right =
  length left = length right andalso
  ListPair.allEq (fn (left, right) => Term.aconv left right) (left, right)

fun compute_exhaustive ty size =
  case enumerate ty of
      SOME values => values
    | NONE =>
        let
          val values = ref []
          val _ = exhaustive_values (spec_of ty) size (fn value =>
            (values := value :: !values; Continue))
        in
          rev (!values)
        end

fun cv_exhaustive_agrees ty size application =
  let
    val (actual, _) = listSyntax.dest_list (cv_rhs application)
  in
    same_terms (compute_exhaustive ty size) actual
  end

fun num_term_of_intinf value =
  numSyntax.mk_numeral (Arbnum.fromString (IntInf.toString value))

fun cv_random_agrees ty size seed application =
  let
    val (expected_value, expected_state) = random_term ty size seed
    val (actual_value, actual_state) =
      pairSyntax.dest_pair (cv_rhs application)
  in
    Term.aconv expected_value actual_value andalso
    Term.aconv (num_term_of_intinf expected_state) actual_state
  end

fun cv_word64_draw_uses_two_halves () =
  let
    val (hi, state1) = rand_below 4294967296 1
    val (lo, state2) = rand_below 4294967296 state1
    val joined = hi * 4294967296 + lo
    val expected = wordsSyntax.mk_wordi
      (Arbnum.fromString (IntInf.toString joined), 64)
    val (actual, actual_state) =
      pairSyntax.dest_pair (cv_rhs ``refute_cv_rnd_word64 3 1``)
  in
    Term.aconv expected actual andalso
    Term.aconv (num_term_of_intinf state2) actual_state
  end

fun cv_generators_agree () =
  cv_exhaustive_agrees ``:bool`` 0 ``refute_cv_exh_bool 0`` andalso
  cv_exhaustive_agrees ``:word16`` 3 ``refute_cv_exh_word16 3`` andalso
  cv_exhaustive_agrees ``:num # num`` 2
    ``refute_cv_exh_num_pair 2`` andalso
  cv_exhaustive_agrees ``:num list`` 3
    ``refute_cv_exh_num_list 3`` andalso
  cv_random_agrees ``:refute$rf3`` 3 1 ``refute_cv_rnd_rf3 3 1`` andalso
  cv_random_agrees ``:word32`` 3 1 ``refute_cv_rnd_word32 3 1`` andalso
  cv_word64_draw_uses_two_halves () andalso
  cv_random_agrees ``:num # num`` 3 1
    ``refute_cv_rnd_num_pair 3 1`` andalso
  cv_random_agrees ``:num list`` 3 1
    ``refute_cv_rnd_num_list 3 1`` andalso
  cv_random_agrees ``:string`` 2 1 ``refute_cv_rnd_string 2 1``

val _ = require_msg (check_result cv_generators_agree) (fn () =>
  "a build-time cv generator disagreed with the compute substrate")
  (fn () => ()) ()

val _ = tprint "Refute core configuration"

fun size_update_is_local () =
  let
    val updated = upd_size 5 default_config
    val original = #qc default_config
    val after = #qc updated
  in
    #size after = 5 andalso
    #iterations after = #iterations original andalso
    #depth after = #depth original andalso
    #finite_types after = #finite_types original andalso
    #finite_type_size after = #finite_type_size original andalso
    #default_type after = #default_type original andalso
    #substrate after = #substrate original andalso
    #allow_function_inversion after =
      #allow_function_inversion original andalso
    #use_subtype after = #use_subtype original andalso
    #seed after = #seed original andalso
    #smart_quantifier after = #smart_quantifier original andalso
    #optimise_equality after = #optimise_equality original andalso
    Real.== (#timeout updated, #timeout default_config) andalso
    #backends updated = #backends default_config andalso
    #sequential updated = #sequential default_config andalso
    #genuine_only updated = #genuine_only default_config andalso
    #abort_potential updated = #abort_potential default_config andalso
    #no_assms updated = #no_assms default_config andalso
    null (#evals updated) andalso
    #expect updated = #expect default_config andalso
    #max_counterexamples updated = #max_counterexamples default_config andalso
    #tag updated = #tag default_config
  end

val _ = require_msg (check_result size_update_is_local) (fn () =>
  "upd_size changed a field other than qc.size") (fn () => ()) ()

val _ = tprint "Refute core backend registry"

fun dummy_backend name weight : backend =
  { name = name,
    weight = weight,
    configured = fn () => true,
    run = fn _ => fn _ => Unknown [] }

val registry_alpha = dummy_backend "refute-core-alpha" (~97)
val registry_beta = dummy_backend "refute-core-beta" (~98)
val registry_alpha_replacement = dummy_backend "refute-core-alpha" (~96)

val _ = register_backend registry_alpha
val _ = register_backend registry_beta
val _ = register_backend registry_alpha_replacement

fun core_backend_names () =
  map #name (List.filter (fn backend =>
    #name backend = "refute-core-alpha" orelse
    #name backend = "refute-core-beta") (registered_backends ()))

val _ = require_msg
  (check_result (fn names => names =
    ["refute-core-beta", "refute-core-alpha"]))
  (fn names => "unexpected registry order: " ^ String.concatWith ", " names)
  core_backend_names ()

val _ = tprint "Refute core silent report"

val report_cex : counterexample =
  { backend = "selftest",
    substrate = "compute",
    certainty = Genuine,
    bindings = [(``x : num``, ``0``)],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [("size", 3), ("card", 2), ("tests", 412), ("msec", 400)] }

fun silent_report () =
  let
    val prior = Feedback.current_trace "Refute"
    val _ = Feedback.set_trace "Refute" 0
    val _ = report_outcome default_config (Counterexample [report_cex])
    val _ = Feedback.set_trace "Refute" prior
  in
    true
  end

val _ = require_msg (check_result silent_report) (fn () =>
  "reporting failed at trace level zero") (fn () => ()) ()

val _ = tprint "Refute generator derivation"

fun check_gen name predicate ty =
  require_msg (check_result (fn () => predicate (spec_of ty)))
    (fn () => "unexpected generator specification for " ^ name)
    (fn () => ()) ()

fun is_num_kind kind (GenNum actual) = kind = actual
  | is_num_kind _ _ = false

fun datatype_info (GenDatatype info) = SOME info
  | datatype_info _ = NONE

fun has_no_generator ty =
  ((ignore (spec_of ty); false)
   handle NoGenerator (_, reason) => String.size reason > 0)

val _ = check_gen "num" (is_num_kind Num) ``:num``
val _ = check_gen "char" (is_num_kind Char) ``:char``
val _ = check_gen "word" (fn GenNum (Word 8) => true | _ => false)
  ``:bool[8]``
val _ = check_gen "function" (fn GenFun _ => true | _ => false)
  ``:num -> bool``
val _ = check_gen "rf3" (fn GenEnum values => length values = 3 | _ => false)
  ``:refute$rf3``

fun list_shape () =
  case datatype_info (spec_of ``:'a list``) of
    SOME {constrs, recursive, min_size, family} =>
      length constrs = 2 andalso recursive = [[], [false, true]] andalso
      min_size = [[], [0, 1]] andalso length family = 1
  | NONE => false

fun option_shape () =
  case datatype_info (spec_of ``:'a option``) of
    SOME {constrs, recursive, min_size, family} =>
      length constrs = 2 andalso recursive = [[], [false]] andalso
      min_size = [[], [0]] andalso length family = 1
  | NONE => false

val _ = require_msg (check_result list_shape) (fn () =>
  "list generator has an unexpected recursive shape") (fn () => ()) ()
val _ = require_msg (check_result option_shape) (fn () =>
  "option generator has an unexpected recursive shape") (fn () => ()) ()

val _ = Datatype.Datatype `rg_rose = RGLeaf | RGNode ((rg_rose) list)`
val _ = Datatype.Datatype
  `rg_tree = RGTip num | RGBin rg_tree rg_tree`
val _ = Datatype.Datatype `rg_left = RGLeft | RGToRight rg_right;
                           rg_right = RGRight rg_left`
val _ = Datatype.Datatype `rg_record = <| rg_field : num |>`
val _ = Datatype.Datatype `rg_enum = RGRed | RGGreen | RGBlue`

val rx_sum_def = TotalDefn.Define
  `rx_sum ([] : num list) = 0 /\
   rx_sum (x :: xs) = x + rx_sum xs`

val rx_sum_plus_one_def = TotalDefn.Define
  `rx_sum_plus_one xs = SUC (rx_sum xs)`

val rx_rose_def = TotalDefn.Define
  `rx_rose RGLeaf = 0 /\
   rx_rose (RGNode []) = 1 /\
   rx_rose (RGNode (child :: children)) = SUC (rx_rose child)`

val rx_pair_case_def = TotalDefn.Define
  `rx_pair_case pair =
     let (xs : num list, n) = pair
     in case xs of [] => n | h :: t => h + n`

val rx_record_def = TotalDefn.Define
  `rx_record r =
     let updated = r with rg_field := r.rg_field + 1
     in updated.rg_field`

val rx_partial_def = TotalDefn.Define
  `rx_partial RGLeaf = 10`

val rx_even_odd_def = TotalDefn.Define
  `rx_even 0 = T /\
   rx_even (SUC n) = rx_odd n /\
   rx_odd 0 = F /\
   rx_odd (SUC n) = rx_even n`

val _ = Theory.new_constant ("rx_unmapped", ``:num -> num``)

structure RefuteExtractSelftest = struct
  val result : bool option ref = ref NONE
end

val extract_compile_counter = ref 0

fun compile_extracted_with term finish =
  let
    val {source, entry} = Refute_Extract.extract_term term
    val serial = !extract_compile_counter
    val _ = extract_compile_counter := serial + 1
    val structure_name = "RefuteExtractGolden_" ^ Int.toString serial
    val program =
      "structure " ^ structure_name ^ " = struct\n" ^ source ^ "end\n" ^
      "val _ = RefuteExtractSelftest.result := SOME (" ^
      finish (structure_name ^ "." ^ entry) ^ ")\n"
    val stream = TextIO.openString program
    fun input () = TextIO.input1 stream
    fun compile () =
      if TextIO.endOfStream stream then ()
      else
        (PolyML.compiler
           (input, [PolyML.Compiler.CPOutStream (fn _ => ())]) ();
         compile ())
    val _ = RefuteExtractSelftest.result := NONE
    val _ = compile ()
    val _ = TextIO.closeIn stream
  in
    valOf (!RefuteExtractSelftest.result)
  end

fun compile_extracted term = compile_extracted_with term (fn entry => entry)

fun evaluated_bool term =
  let
    fun result_of conversion =
      #2 (boolSyntax.dest_eq (Thm.concl (conversion term)))
    val evaluated = result_of computeLib.EVAL_CONV
    val result =
      if Term.aconv evaluated boolSyntax.T orelse
         Term.aconv evaluated boolSyntax.F then evaluated
      else result_of intLib.REDUCE_CONV
  in
    Term.aconv result boolSyntax.T
  end

fun extraction_agrees term = compile_extracted term = evaluated_bool term

val _ = tprint "Refute extraction type and constant layers"

val extraction_goldens =
  [``APPEND [1; 2] [3; 4] = [1; 2; 3; 4]``,
   ``REVERSE [1; 2; 3] = [3; 2; 1]``,
   ``MAP (\n : num. n + 1) [0; 2; 5] = [1; 3; 6]``,
   ``rx_sum [1; 2; 3; 4] = 10``,
   ``rx_sum_plus_one [1; 2; 3; 4] = 11``,
   ``rx_rose (RGNode [RGNode [RGLeaf]; RGLeaf]) = 2``,
   ``rx_pair_case ([4; 9], 3) = 7``,
   ``rx_pair_case ([], 3) = 3``,
   ``rx_record <|rg_field := 8|> = 9``,
   ``rx_even 10 /\ rx_odd 7``,
   ``~rx_even 9 /\ ~rx_odd 8``,
   ``(2 : num) - 5 = 0``,
   ``17 DIV 5 = 3 /\ 17 MOD 5 = 2``,
   ``((17 : int) / 5 = 3)``,
   ``((17 : int) % 5 = 2)``,
   ``((~5 : int) / 2 = ~3)``,
   ``((~5 : int) % 2 = 1)``,
   ``((~5 : int) - 2 = ~7)``,
   ``Num (~5) = 5``,
   ``((n2w 250 : bool[8]) + n2w 10) = n2w 4``,
   ``word_xor (n2w 3 : bool[8]) (n2w 5) = n2w 6``,
   ``ORD #"A" = 65``,
   ``IMPLODE (EXPLODE "ab") = "ab"``,
   ``STRCAT "ab" "c" = "abc"``,
   ``HD "ab" = #"a"``,
   ``TL "ab" = "b"``,
   ``(I (\n : num. n + 1)) 2 = 3``,
   ``(\b : bool. b) = (\b. b)``]

fun all_extraction_goldens () =
  let
    fun check [] = true
      | check (term :: terms) =
          if extraction_agrees term then check terms
          else raise Fail ("extraction mismatch: " ^ Parse.term_to_string term)
  in
    check extraction_goldens
  end

val _ = require_msg (check_result all_extraction_goldens) (fn () =>
  "an extracted golden function disagreed with EVAL") (fn () => ()) ()

fun mutual_definition_group_is_emitted () =
  let val {source, ...} = Refute_Extract.extract_term ``rx_even 4``
  in String.isSubstring "and f_rx_odd_" source end

val _ = require_msg (check_result mutual_definition_group_is_emitted)
  (fn () => "a mutual definition was not emitted with fun/and")
  (fn () => ()) ()

fun extracted_div_zero_is_stuck () =
  compile_extracted_with ``1 DIV 0 = 0`` (fn entry =>
    "(" ^ entry ^ "; false) handle Refute_EvalSML.Stuck _ => true")

val _ = require_msg (check_result extracted_div_zero_is_stuck) (fn () =>
  "extracted DIV 0 did not raise Refute_EvalSML.Stuck")
  (fn () => ()) ()

fun extracted_missing_clause_is_match () =
  compile_extracted_with ``rx_partial (RGNode []) = 0`` (fn entry =>
    "(" ^ entry ^ "; false) handle Match => true")

val _ = require_msg (check_result extracted_missing_clause_is_match) (fn () =>
  "an extracted inexhaustive function did not raise Match")
  (fn () => ()) ()

fun unmapped_is_not_extractable () =
  ((ignore (Refute_Extract.extract_term ``rx_unmapped 0 = 0``); false)
   handle Refute_Extract.NotExtractable reasons =>
     List.exists (String.isSubstring "rx_unmapped") reasons)

val _ = require_msg (check_result unmapped_is_not_extractable) (fn () =>
  "an unmapped constant lacked a useful NotExtractable reason")
  (fn () => ()) ()

fun infinite_function_equality_is_rejected () =
  ((ignore (Refute_Extract.extract_term
      ``(f : num -> bool) = (g : num -> bool)``); false)
   handle Refute_Extract.NotExtractable reasons =>
     List.exists (String.isSubstring "non-enumerable") reasons)

val _ = require_msg
  (check_result infinite_function_equality_is_rejected) (fn () =>
  "function equality over num was extractable") (fn () => ()) ()

fun compile_extracted_tests strategy plans =
  let
    val {source, entry} =
      Refute_Extract.extract_tests default_config strategy plans
    val serial = !extract_compile_counter
    val _ = extract_compile_counter := serial + 1
    val structure_name = "RefuteExtractPlan_" ^ Int.toString serial
    val program =
      "structure " ^ structure_name ^ " = struct\n" ^ source ^ "end\n" ^
      "val _ = " ^ structure_name ^ "." ^ entry ^ "\n"
    val stream = TextIO.openString program
    fun input () = TextIO.input1 stream
    fun compile () =
      if TextIO.endOfStream stream then ()
      else
        (PolyML.compiler
           (input, [PolyML.Compiler.CPOutStream (fn _ => ())]) ();
         compile ())
    val _ = installed_dispatch := NONE
    val _ = compile ()
    val _ = TextIO.closeIn stream
  in
    valOf (!installed_dispatch)
  end

fun generated_result strategy plan size draws seed =
  compile_extracted_tests strategy [plan] 1 false size draws seed

fun generated_env ({hit = SOME (environment, genuine), table, ...} :
    generated_answer) =
      SOME (List.map (fn (index, rebuild) =>
        (table_term table index, rebuild ())) environment, genuine)
  | generated_env _ = NONE

fun compute_plan_result strategy plan size draws seed =
  let
    val compiled =
      case Refute_EvalCompute.compile default_config strategy [plan] of
        Compiled test => test
      | Inapplicable reasons =>
          raise Fail (String.concatWith "; " reasons)
  in
    #run compiled
      {genuine_only = false, card = 1, size = size, draws = draws,
       ignored = []}
  end

fun same_generated_env [] [] = true
  | same_generated_env ((variable1, value1) :: rest1)
      ((variable2, value2) :: rest2) =
      Term.aconv variable1 variable2 andalso
      Term.aconv value1 value2 andalso
      same_generated_env rest1 rest2
  | same_generated_env _ _ = false

fun generated_compute_agree strategy plan size draws seed =
  case (generated_env (generated_result strategy plan size draws seed),
        compute_plan_result strategy plan size draws seed) of
      (SOME (generated, generated_genuine),
       CexFound {env = computed, genuine = computed_genuine}) =>
        generated_genuine = computed_genuine andalso
        same_generated_env generated computed
    | (NONE, Exhausted _) => true
    | _ => false

fun extraction_plan_checks () =
  let
    val list_plan = compile_plan default_config
      ``REVERSE (xs : num list) = xs``
    val tree_plan = compile_plan default_config
      ``(tree : rg_tree) = RGTip 0``
    val word_plan = compile_plan default_config
      ``(word : bool[8]) = 0w``
    val function_plan = compile_plan default_config
      ``(function : refute$rf2 -> refute$rf2) rf2_2 = rf2_1``
    fun both plan size =
      generated_compute_agree Exhaustive plan size 0 1 andalso
      List.all (fn seed => generated_compute_agree
        (Random {seed = IntInf.fromInt seed}) plan size 30
        (IntInf.fromInt seed)) [1, 2, 3]
  in
    both list_plan 3 andalso both tree_plan 3 andalso both word_plan 3 andalso
    both function_plan 3
  end

fun generated_stream seed count =
  let
    val first = Term.mk_var ("stream_first", ``:num``)
    val second = Term.mk_var ("stream_second", ``:num``)
    val plan = Gen (first, Gen (second, Test boolSyntax.F))
    val dispatch = compile_extracted_tests (Random {seed = seed}) [plan]
    fun loop 0 _ candidates = rev candidates
      | loop remaining state candidates =
          let
            val answer = dispatch 1 false 999 1 state
            val (environment, _) = valOf (#hit answer)
            val values = rev (List.map (fn (_, rebuild) => rebuild ())
              environment)
          in
            loop (remaining - 1) (#state answer) (values :: candidates)
          end
  in
    loop count seed []
  end

fun generated_type_stream ty size seed count =
  let
    val variable = Term.mk_var ("stream_value", ty)
    val plan = Gen (variable, Test boolSyntax.F)
    val dispatch = compile_extracted_tests (Random {seed = seed}) [plan]
    fun loop 0 _ candidates = rev candidates
      | loop remaining state candidates =
          let
            val answer = dispatch 1 false size 1 state
            val (environment, _) = valOf (#hit answer)
            val value = #2 (hd environment) ()
          in
            loop (remaining - 1) (#state answer) ([value] :: candidates)
          end
  in
    loop count seed []
  end

fun generated_stream_checks () =
  let
    val first = Term.mk_var ("stream_first", ``:num``)
    val second = Term.mk_var ("stream_second", ``:num``)
    val plan = Gen (first, Gen (second, Test boolSyntax.F))
    fun number_check seed =
      let val expected = dump_random_candidates
            {plan = plan, seed = seed, size = 999, count = 8}
      in
        ListPair.allEq (fn (left, right) => same_terms left right)
          (generated_stream seed 8, expected)
      end
    fun type_check ty size seed =
      let
        val variable = Term.mk_var ("stream_value", ty)
        val one_plan = Gen (variable, Test boolSyntax.F)
        val expected = dump_random_candidates
          {plan = one_plan, seed = seed, size = size, count = 6}
      in
        ListPair.allEq (fn (left, right) => same_terms left right)
          (generated_type_stream ty size seed 6, expected)
      end
    fun seed_checks seed =
      number_check seed andalso
      type_check ``:num list`` 4 seed andalso
      type_check ``:rg_tree`` 4 seed andalso
      type_check ``:bool[8]`` 4 seed
  in
    List.all (seed_checks o IntInf.fromInt) [1, 2, 3]
  end

fun partial_plan_checks () =
  let
    val variable = Term.mk_var ("bound", ``:num``)
    val stuck_num = ``THE (NONE : num option)``
    val stuck_bool = ``THE (NONE : bool option)``
    val bind = Bind
      (variable, stuck_num, SOME (Test boolSyntax.F), Test boolSyntax.T)
    val guard = Guard (stuck_bool, Test boolSyntax.F)
    val test = Test stuck_bool
    val some_num = #1 (boolSyntax.strip_comb ``SOME (x : num)``)
    val split = Split (``THE (NONE : num option)``,
      [(some_num, [variable], Test boolSyntax.F)])
    val generated = Term.mk_var ("generated", ``:num``)
    val bound = Term.mk_var ("bound_value", ``:num``)
    val successful_bind = Gen
      (generated, Bind (bound, ``generated + 1``, NONE,
        Test ``bound_value = 0``))
    val option = Term.mk_var ("option", ``:num option``)
    val selected = Term.mk_var ("selected", ``:num``)
    val successful_split = Gen
      (option, Split (option,
        [(some_num, [selected], Test boolSyntax.F)]))
    val list = Term.mk_var ("split_list", ``:num list``)
    val list_head = Term.mk_var ("list_head", ``:num``)
    val list_tail = Term.mk_var ("list_tail", ``:num list``)
    val cons_num = #1
      (boolSyntax.strip_comb ``(1 : num) :: (rest : num list)``)
    val successful_list_split = Gen
      (list, Split (list,
        [(cons_num, [list_head, list_tail], Test boolSyntax.F)]))
    fun exhaustive plan =
      generated_compute_agree Exhaustive plan 2 0 1
    fun random plan =
      generated_compute_agree (Random {seed = 1}) plan 2 1 1
    fun check plan = exhaustive plan andalso random plan
    fun potential answer =
      case generated_env answer of
          SOME ([], false) => true
        | _ => false
    val split_answer = generated_result Exhaustive split 2 0 1
  in
    potential (generated_result Exhaustive bind 2 0 1) andalso
    potential (generated_result (Random {seed = 1}) bind 2 1 1) andalso
    check guard andalso check test andalso exhaustive split andalso
    #match_failures split_answer = 1 andalso
    exhaustive successful_bind andalso exhaustive successful_split andalso
    exhaustive successful_list_split
  end

fun generated_completeness_checks () =
  let
    val boolean = Term.mk_var ("complete_bool", ``:bool``)
    val list = Term.mk_var ("incomplete_list", ``:num list``)
    val finite = generated_result Exhaustive
      (Gen (boolean, Test boolSyntax.T)) 2 0 1
    val bounded = generated_result Exhaustive
      (Gen (list, Test boolSyntax.T)) 2 0 1
  in
    #complete finite andalso not (#complete bounded)
  end

fun wide_word_extraction_checks () =
  let
    val wide = Term.mk_var ("wide", ``:word64``)
    val plan = Gen (wide, Test boolSyntax.T)
    val exhaustive_ok =
      let val {source, ...} = extract_tests default_config Exhaustive [plan]
      in String.isSubstring "IntInf.pow (2, 64)" source end
    val random_rejected =
      ((ignore (extract_tests default_config (Random {seed = 1}) [plan]);
        false)
       handle NotExtractable reasons =>
         List.exists (String.isSubstring "32-bit bound") reasons)
  in
    exhaustive_ok andalso random_rejected
  end

fun generated_hygiene_and_retention_checks () =
  let
    val size = Term.mk_var ("size", ``:num``)
    val state = Term.mk_var ("state", ``:num``)
    val collision_plan = Gen
      (size, Gen (state, Test boolSyntax.F))
    val string = Term.mk_var ("string", ``:string``)
    val head = Term.mk_var ("head", ``:char``)
    val tail = Term.mk_var ("tail", ``:string``)
    val cons = #1 (boolSyntax.strip_comb ``#"a" :: (s : string)``)
    val string_plan = Gen
      (string, Split (string, [(cons, [head, tail], Test boolSyntax.F)]))
    val first_dispatch = compile_extracted_tests Exhaustive [collision_plan]
    val other = Term.mk_var ("other", ``:bool[8]``)
    val _ = compile_extracted_tests Exhaustive
      [Gen (other, Test boolSyntax.F)]
    val retained = first_dispatch 1 false 2 0 1
  in
    generated_compute_agree Exhaustive collision_plan 2 0 1 andalso
    generated_compute_agree Exhaustive string_plan 3 0 1 andalso
    (case generated_env retained of
       SOME (environment, true) => length environment = 2
     | _ => false)
  end

fun reconstruction_is_lazy () =
  let
    val variable = Term.mk_var ("lazy_x", ``:num list``)
    val miss = Gen (variable, Test boolSyntax.T)
    val hit = Gen (variable, Test boolSyntax.F)
    val _ = reset_reconstruction_forces ()
    val _ = generated_result Exhaustive miss 3 0 1
    val miss_forces = !reconstruction_forces
    val _ = reset_reconstruction_forces ()
    val answer = generated_result Exhaustive hit 3 0 1
    val before_force = !reconstruction_forces
    val environment = #1 (valOf (#hit answer))
    val _ = List.app (fn (_, rebuild) => ignore (rebuild ())) environment
  in
    miss_forces = 0 andalso before_force = 0 andalso
    !reconstruction_forces > 0
  end

val _ = tprint "Refute extraction generators and plans"
val _ = require_msg (check_result extraction_plan_checks) (fn () =>
  "an extracted plan outcome disagreed with compute") (fn () => ()) ()
val _ = require_msg (check_result generated_stream_checks) (fn () =>
  "an extracted random stream disagreed with compute") (fn () => ()) ()
val _ = require_msg (check_result partial_plan_checks) (fn () =>
  "an extracted plan handled partiality differently from compute")
  (fn () => ()) ()
val _ = require_msg (check_result generated_completeness_checks) (fn () =>
  "an extracted enumerator reported the wrong completeness")
  (fn () => ()) ()
val _ = require_msg (check_result wide_word_extraction_checks) (fn () =>
  "wide-word extraction overflowed or ignored the random bound")
  (fn () => ()) ()
val _ = require_msg
  (check_result generated_hygiene_and_retention_checks) (fn () =>
  "generated names, string splitting, or retained term tables failed")
  (fn () => ()) ()
val _ = require_msg (check_result reconstruction_is_lazy) (fn () =>
  "an extracted reconstruction thunk was forced before a hit")
  (fn () => ()) ()

val _ = require_msg (check_result (fn () =>
  let val {ml_type, source, ...} =
        Refute_Extract.compile_type ``:bool[8]``
  in ml_type = "IntInf.int" andalso
     String.isSubstring "refute_norm" source end)) (fn () =>
  "word type extraction did not use IntInf and modular helpers")
  (fn () => ()) ()

val _ = require_msg (check_result (fn () =>
  let val {source, ...} = Refute_Extract.compile_types
        [``:rg_left``, ``:rg_right``]
  in String.isSubstring "datatype" source andalso
     String.isSubstring "and refute_ty_" source andalso
     String.isSubstring "eq_refute_" source end)) (fn () =>
  "mutual datatype or structural equality declarations were not emitted")
  (fn () => ()) ()

val _ = require_msg (check_result (fn () =>
  case cached_spec ``:refute$rf3`` of NONE => true | SOME _ => false))
  (fn () => "generator cache was not invalidated") (fn () => ()) ()

fun rose_shape () =
  case datatype_info (spec_of ``:rg_rose``) of
    SOME {recursive, min_size, family, ...} =>
      recursive = [[], [true]] andalso min_size = [[], [1]] andalso
      length family = 1
  | NONE => false

fun mutual_shape () =
  case datatype_info (spec_of ``:rg_right``) of
    SOME {recursive, min_size, family, ...} =>
      recursive = [[true]] andalso min_size = [[1]] andalso
      length family = 2
  | NONE => false

val _ = require_msg (check_result rose_shape) (fn () =>
  "rose generator has an unexpected recursive shape") (fn () => ()) ()
val _ = require_msg (check_result mutual_shape) (fn () =>
  "mutual generator has an unexpected recursive shape") (fn () => ()) ()
val _ = check_gen "record" (fn GenDatatype _ => true | _ => false)
  ``:rg_record``
val _ = check_gen "enum" (fn GenEnum values => length values = 3 | _ => false)
  ``:rg_enum``
val _ = require_msg (check_result (fn () =>
  recursive_under_function [``:rg_rose``] ``:rg_rose -> bool``))
  (fn () => "recursive function occurrence was not detected")
  (fn () => ()) ()
val real_ty = Type.mk_thy_type {Thy = "real", Tyop = "real", Args = []}
  handle Feedback.HOL_ERR _ => ``:ind``
val _ = require_msg (check_result (fn () => has_no_generator real_ty))
  (fn () => "real unexpectedly has a generator") (fn () => ()) ()
val _ = require_msg (check_result (fn () => has_no_generator ``:ind``))
  (fn () => "unknown type unexpectedly has a generator") (fn () => ()) ()

val _ = tprint "Refute enumeration and registries"

fun check_cardinality ty expected =
  require_msg (check_result (fn () => cardinality ty = expected))
    (fn () => "unexpected cardinality") (fn () => ()) ()

val _ = check_cardinality ``:bool`` (SOME 2)
val _ = check_cardinality ``:refute$rf3`` (SOME 3)
val _ = check_cardinality ``:bool[8]`` (SOME 256)
val _ = check_cardinality ``:refute$rf2 # bool`` (SOME 4)
val _ = check_cardinality ``:bool -> bool`` (SOME 4)
val _ = check_cardinality ``:bool[8] -> bool`` NONE
val _ = check_cardinality ``:num`` NONE

fun is_enumerated ty count =
  case enumerate ty of
    SOME values => length values = count
  | NONE => false

val _ = require_msg (check_result (fn () => is_enumerated ``:bool`` 2))
  (fn () => "bool was not completely enumerated") (fn () => ()) ()
val _ = require_msg (check_result (fn () =>
  is_enumerated ``:refute$rf3`` 3))
  (fn () => "rf3 was not completely enumerated") (fn () => ()) ()
val _ = require_msg (check_result (fn () =>
  is_enumerated ``:refute$rf2 # bool`` 4))
  (fn () => "product was not completely enumerated") (fn () => ()) ()

fun eval_rhs tm =
  let
    val theorem = computeLib.CBV_CONV (!computeLib.the_compset) tm
  in
    #2 (boolSyntax.dest_eq (Thm.concl theorem))
  end

fun function_graphs_work () =
  case (enumerate ``:bool -> refute$rf2``, enumerate ``:refute$rf2``) of
    (SOME graphs, SOME values) =>
      length graphs = 4 andalso
      List.all (fn graph =>
        List.all (fn input =>
          List.exists (fn value =>
            Term.aconv (eval_rhs (Term.mk_comb (graph, input))) value)
            values) [boolSyntax.T, boolSyntax.F]) graphs
  | _ => false

val _ = require_msg (check_result function_graphs_work) (fn () =>
  "function graphs did not EVAL on both boolean inputs") (fn () => ()) ()

val empty_custom : custom_gen = {enumerate = NONE, random = NONE}
fun custom_zero_random _ state =
  let val (_, next) = rand_below 1 state
  in (``0``, next) end

val finite_custom : custom_gen =
  {enumerate = SOME (fn _ => [``0``]),
   random = SOME custom_zero_random}

fun rejects_empty_custom () =
  ((register_generator ``:ind`` empty_custom; false)
   handle Fail _ => true)

val _ = require_msg (check_result rejects_empty_custom) (fn () =>
  "an empty custom generator was accepted") (fn () => ()) ()
val _ = register_generator ``:ind`` finite_custom
val _ = require_msg (check_result (fn () =>
  case spec_of ``:ind`` of GenCustom _ => true | _ => false))
  (fn () => "custom generator was not registered") (fn () => ()) ()

fun custom_random_threads_state () =
  let
    val (_, final) = random_value (GenCustom finite_custom)
      {budget = 1, size = 1} 7
  in
    final = rand_next 7
  end

val _ = require_msg (check_result custom_random_threads_state) (fn () =>
  "a custom random generator did not return its successor state")
  (fn () => ()) ()

val abstract_ty = ``:rg_record``
val abstract_predicate = ``\x : rg_record. T``
val abstract_constructor =
  hd (TypeBasePure.constructors_of (valOf (TypeBase.fetch abstract_ty)))
val _ = abstract_generator
  {ty = abstract_ty,
   constructors = [abstract_constructor],
   pred = SOME abstract_predicate}

fun abstract_generator_works () =
  (case spec_of abstract_ty of
     GenDatatype {constrs, family, ...} =>
       length constrs = 1 andalso family = [abstract_ty]
   | _ => false) andalso
  (case predicate_of abstract_ty of
     SOME predicate => Term.aconv predicate abstract_predicate
   | NONE => false)

val _ = require_msg (check_result abstract_generator_works) (fn () =>
  "abstract generator or predicate registry was not populated")
  (fn () => ()) ()

fun custom_generators_are_not_extracted () =
  let
    fun rejected ty =
      let val variable = Term.mk_var ("custom_value", ty)
      in
        ((ignore (extract_tests default_config Exhaustive
            [Gen (variable, Test boolSyntax.T)]); false)
         handle NotExtractable reasons =>
           List.exists (String.isPrefix
             ("custom generator registered for " ^
              Hol_pp.type_to_string ty)) reasons)
      end
  in
    rejected ``:rg_record`` andalso rejected ``:ind list``
  end

val _ = require_msg (check_result custom_generators_are_not_extracted)
  (fn () => "a custom generator escaped native closure validation")
  (fn () => ()) ()

val _ = tprint "Refute preprocessing and executability"

fun preprocessing_problem goal : problem =
  { goal = goal, assumptions = [], evals = [] }

fun preprocessed_instances result =
  case result of
      Preprocessed instances => SOME instances
    | NotExecutable _ => NONE

fun has_conjunction tm =
  case Lib.total boolSyntax.dest_conj tm of
      SOME _ => true
    | NONE =>
        if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            has_conjunction left orelse has_conjunction right
          end
        else
          false

fun two_way_disjunction tm =
  case Lib.total boolSyntax.dest_disj tm of
      SOME _ => true
    | NONE => false

fun bool_forall_expands () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``p /\ (!x : bool. x)``)) of
      SOME [instance] => has_conjunction (#goal instance)
    | _ => false

val _ = require_msg (check_result bool_forall_expands) (fn () =>
  "a boolean universal did not expand to a two-way conjunction")
  (fn () => ()) ()

fun explicit_forall_is_stripped () =
  case preprocessed_instances
    (preprocess (upd_finite_types false default_config)
      (preprocessing_problem
        ``!x : 'a. (f : 'a -> 'a) x = (g x : 'a)``)) of
      SOME [instance] =>
        not (boolSyntax.is_forall (#goal instance)) andalso
        length (#evals instance) = 2
    | _ => false

val _ = require_msg (check_result explicit_forall_is_stripped) (fn () =>
  "an explicit outer universal was not stripped before preprocessing")
  (fn () => ()) ()

fun rf2_exists_expands () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``?x : refute$rf2. x = rf2_1``)) of
      SOME [instance] => two_way_disjunction (#goal instance)
    | _ => false

val _ = require_msg (check_result rf2_exists_expands) (fn () =>
  "an rf2 existential did not expand to a two-way disjunction")
  (fn () => ()) ()

fun num_binder_is_not_executable () =
  case preprocess default_config
    (preprocessing_problem ``q (!n : num. n = 0)``) of
      NotExecutable _ => true
    | Preprocessed _ => false

val _ = require_msg (check_result num_binder_is_not_executable) (fn () =>
  "a universal over num was accepted as executable")
  (fn () => ()) ()

fun negated_exists_normalizes () =
  let
    val normalized = normalize ``~(?x : bool. x)``
    val (variables, body) = strip_outer_forall normalized
  in
    length variables = 1 andalso not (boolSyntax.is_forall body)
  end

val _ = require_msg (check_result negated_exists_normalizes) (fn () =>
  "a negated existential did not normalize and strip as a universal")
  (fn () => ()) ()

fun all_same_type ty variables =
  List.all (fn variable => Type.compare (Term.type_of variable, ty) = EQUAL)
    variables

val polymorphic_goal = ``p (x : 'a) /\ q (y : 'b)``

fun value_variable_types tm =
  List.map Term.type_of (List.filter (fn variable =>
    case Lib.total Type.dom_rng (Term.type_of variable) of
        NONE => true
      | SOME _ => false) (Term.free_vars_lr tm))

fun finite_type_instances () =
  case preprocessed_instances
    (preprocess (upd_finite_type_size 3 default_config)
      (preprocessing_problem polymorphic_goal)) of
      SOME instances =>
        length instances = 3 andalso
        List.all (fn instance =>
          all_same_type (rf_type (#card instance))
            (List.map (fn ty => Term.mk_var ("x", ty))
              (value_variable_types (#goal instance)))) instances
    | NONE => false

val _ = require_msg (check_result finite_type_instances) (fn () =>
  "finite-type monomorphization did not produce rf1 through rf3")
  (fn () => ()) ()

fun default_type_instance () =
  case preprocessed_instances
    (preprocess (upd_finite_types false default_config)
      (preprocessing_problem polymorphic_goal)) of
      SOME [instance] =>
        #card instance = 1 andalso
        all_same_type numSyntax.num
          (List.map (fn ty => Term.mk_var ("x", ty))
            (value_variable_types (#goal instance)))
    | _ => false

val _ = require_msg (check_result default_type_instance) (fn () =>
  "default-type monomorphization did not use num")
  (fn () => ()) ()

fun equation_adds_evals () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``(f : bool -> bool) x = (g x : bool)``)) of
      SOME [instance] => length (#evals instance) = 2
    | _ => false

val _ = require_msg (check_result equation_adds_evals) (fn () =>
  "an equational conclusion did not add both evaluation terms")
  (fn () => ()) ()

val _ = Theory.new_constant ("refute_task07_unmapped", ``:bool``)

fun unmapped_constant_is_not_executable () =
  case preprocess default_config
    (preprocessing_problem ``refute_task07_unmapped``) of
      NotExecutable [reason] =>
        String.isSubstring "refute_task07_unmapped" reason
    | _ => false

val _ = require_msg
  (check_result unmapped_constant_is_not_executable) (fn () =>
  "a constant without a compute-set entry was accepted")
  (fn () => ()) ()

val _ = tprint "Refute QC plan compiler"

fun plan_is_bind_with_fallback plan =
  case plan of
      Gen (_, Gen (_, Bind (_, _, SOME (Gen (_, Gen (_, Test _))),
        Gen (_, Test _)))) => true
    | _ => false

fun plan_is_single_split plan =
  case plan of
      Gen (_, Split (_, [(_, variables, _)])) => length variables = 1
    | _ => false

fun plan_is_generic_guard plan =
  case plan of
      Gen (_, Gen (_, Guard (_, Gen (_, Test _)))) => true
    | _ => false

fun plan_is_fmap_lookup plan =
  case plan of
      Gen (_, Gen (_, Split (_, [(_, variables, _)]))) =>
        length variables = 1
    | _ => false

fun plan_is_distinct_zip plan =
  case plan of
      Gen (_, Gen (_, Guard (_, Test _))) => true
    | _ => false

fun plan_is_naive goal plan =
  case plan of
      Gen (_, Test tested) => Term.aconv tested goal
    | _ => false

fun plan_has_abstract_guard plan =
  case plan of
      Gen (_, Guard (_, Test _)) => true
    | _ => false

val bind_goal = ``(x : num) = f (y : num) ==> r (x : num)``
val split_goal = ``(z : num option) = SOME (x : num) ==> T``
val guard_goal = ``(p : num -> bool) x ==> q (x : num)``
val fmap_lookup_goal =
  ``(m1 : num -> num option) k = SOME (v : num) ==> p m1 k v``
val distinct_zip_goal =
  ``ALL_DISTINCT (ZIP (xs : num list, ys : num list)) ==> T``
val naive_goal = ``(x : num) = 0 ==> F``
val abstract_guard_goal = ``(r : rg_record) = r``

fun check_plan predicate message goal =
  require_msg (check_result predicate) (fn plan =>
    message ^ "\n" ^ pp_plan plan)
    (fn () => compile_plan default_config goal) ()

val _ = check_plan plan_is_bind_with_fallback
  "free-variable equality did not compile to Bind with fallback" bind_goal

val _ = check_plan plan_is_single_split
  "constructor equality did not compile to a single Split branch" split_goal

val _ = check_plan plan_is_generic_guard
  "generic premise did not compile to Guard" guard_goal

val _ = check_plan plan_is_fmap_lookup
  "fmap-lookup premise did not compile to the expected Split" fmap_lookup_goal

val _ = check_plan plan_is_distinct_zip
  "distinct/zip premise did not compile to Guard" distinct_zip_goal

val _ = require_msg (check_result (plan_is_naive naive_goal)) (fn _ =>
  "smart_quantifier := false did not retain the whole goal")
  (fn () => compile_plan (upd_smart_quantifier false default_config)
    naive_goal) ()

val _ = check_plan plan_has_abstract_guard
  "abstract-generator predicate was not inserted as Guard" abstract_guard_goal

val _ = tprint "Refute QC exhaustive backend"

fun cv_precedes_compute () =
  case get_substrates () of
      cv :: compute :: _ =>
        #name cv = "cv" andalso #priority cv = 20 andalso
        #name compute = "compute" andalso #priority compute = 30
    | _ => false

val _ = require_msg (check_result cv_precedes_compute) (fn () =>
  "the cv and compute substrates had the wrong registry order")
  (fn () => ()) ()

fun dummy_compile _ _ _ = Inapplicable ["dummy substrate"]

val seam_alpha : substrate =
  {name = "refute-seam-alpha", priority = 50, compile = dummy_compile}
val seam_beta : substrate =
  {name = "refute-seam-beta", priority = 40, compile = dummy_compile}
val seam_alpha_replacement : substrate =
  {name = "refute-seam-alpha", priority = 35, compile = dummy_compile}

val _ = register_substrate seam_alpha
val _ = register_substrate seam_beta
val _ = register_substrate seam_alpha_replacement

fun seam_registry_order () =
  map #name (List.filter (fn substrate =>
    #name substrate = "refute-seam-alpha" orelse
    #name substrate = "refute-seam-beta") (get_substrates ())) =
  ["refute-seam-alpha", "refute-seam-beta"]

val _ = require_msg (check_result seam_registry_order) (fn () =>
  "substrate registry replacement or priority ordering failed")
  (fn () => ()) ()

fun qc_problem goal : problem = {goal = goal, assumptions = [], evals = []}

fun qc_instances config goal =
  case preprocess config (qc_problem goal) of
      Preprocessed instances => instances
    | NotExecutable _ => []

fun exhaustive config goal =
  case preprocess config (qc_problem goal) of
      NotExecutable reasons => Unknown reasons
    | Preprocessed instances => strategy_run Exhaustive config instances

fun has_binding predicate (Counterexample (cex :: _)) =
      List.exists predicate (#bindings cex)
  | has_binding _ _ = false

fun reverse_counterexample () =
  let
    val config = upd_size 3 (upd_max_counterexamples 1 default_config)
    val result = exhaustive config ``REVERSE (xs : num list) = xs``
  in
    (case result of
         Counterexample (cex :: _) => #substrate cex = "cv"
       | _ => false) andalso
    has_binding (fn (_, value) =>
      case Lib.total listSyntax.dest_list value of
          SOME (values, _) => length values >= 2 andalso
            not (Term.aconv (hd values) (List.nth (values, 1)))
        | NONE => false) result
  end

val _ = require_msg (check_result reverse_counterexample) (fn () =>
  "the exhaustive backend did not find a non-palindromic list")
  (fn () => ()) ()

fun complete_bool_goal () =
  case exhaustive default_config ``T`` of
      NoCounterexample => true
    | _ => false

val _ = require_msg (check_result complete_bool_goal) (fn () =>
  "a decidable closed boolean goal was not exhausted completely")
  (fn () => ()) ()

fun stuck_split_counts_failure () =
  let
    val config = default_config
    val goal =
      ``(if THE (NONE : bool option) then SOME 0 else NONE) =
        SOME (x : num) ==> F``
    val result = exhaustive config goal
    val instances = qc_instances config goal
    val plans = List.map (fn i => compile_plan config (#goal i)) instances
    val compiled =
      case Refute_EvalCompute.compile config Exhaustive plans of
          Compiled test => test
        | Inapplicable reasons => raise Fail (String.concatWith "; " reasons)
    val _ = List.app (fn (card, size) =>
      ignore (#run compiled
        {genuine_only = false, card = card, size = size, draws = 0,
         ignored = []}))
      (schedule instances (#size (#qc config)))
  in
    (case result of Unknown _ => true | _ => false) andalso
    (case lookup_stat "match_failures" (!(#last_stats compiled)) of
        SOME failures => failures > 0
      | NONE => false)
  end

val _ = require_msg (check_result stuck_split_counts_failure) (fn () =>
  "a stuck Split scrutinee did not increment match_failures")
  (fn () => ()) ()

fun no_generator_is_compile_inapplicable () =
  let
    val variable = Term.mk_var ("r", ``:real``)
  in
    case Refute_EvalCompute.compile default_config Exhaustive
      [Gen (variable, Test boolSyntax.T)] of
        Inapplicable reasons =>
          List.exists (fn reason =>
            String.isSubstring "no generator for :real" reason andalso
            String.isSubstring "quotient type" reason) reasons
      | Compiled _ => false
  end

val _ = require_msg
  (check_result no_generator_is_compile_inapplicable) (fn () =>
  "NoGenerator was not converted to compile-time Inapplicable")
  (fn () => ()) ()

fun explicit_cv_is_available strategy =
  let
    val config = upd_substrate Cv default_config
    val instances = qc_instances config ``T``
  in
    case strategy_run strategy config instances of
        NoCounterexample => true
      | _ => false
  end

val _ = require_msg (check_result (fn () =>
  explicit_cv_is_available Exhaustive andalso
  explicit_cv_is_available (Random {seed = 1}))) (fn () =>
  "the explicit cv substrate was unavailable for a backend")
  (fn () => ()) ()

fun gave_up_reason_is_plumbed () =
  let
    val original = valOf (List.find (fn substrate =>
      #name substrate = "compute") (get_substrates ()))
    val last_stats = ref []
    val test : compiled_test =
      {run = fn _ => GaveUp "selftest gave up", close = fn () => (),
       last_stats = last_stats}
    val replacement : substrate =
      {name = "compute", priority = 30,
       compile = fn _ => fn _ => fn _ => Compiled test}
    val config = upd_substrate Compute default_config
    val instances = qc_instances config ``T``
    val _ = register_substrate replacement
    val result = strategy_run Exhaustive config instances
      handle e => (register_substrate original; raise e)
    val _ = register_substrate original
  in
    case result of
        Unknown reasons => List.exists (fn reason =>
          reason = "selftest gave up") reasons
      | _ => false
  end

val _ = require_msg (check_result gave_up_reason_is_plumbed) (fn () =>
  "a substrate GaveUp reason was not merged into Unknown")
  (fn () => ()) ()

fun smart_pruning_works () =
  let
    val base = upd_size 3 default_config
    val smart = exhaustive (upd_smart_quantifier true base)
      ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``
    val naive = exhaustive (upd_smart_quantifier false base)
      ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``
  in
    (case smart of Counterexample _ => true | _ => false) andalso
    (case naive of Unknown _ => true | _ => false)
  end

val _ = require_msg (check_result smart_pruning_works) (fn () =>
  "smart premise pruning did not improve the bounded exhaustive search")
  (fn () => ()) ()

fun update_witness () =
  let
    val result = exhaustive (upd_size 2 default_config)
      ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
        f rf2_2 = rf2_2 ==> F``
  in
    has_binding (fn (_, value) =>
      not (null (#1 (combinSyntax.strip_update value)))) result
  end

val _ = require_msg (check_result update_witness) (fn () =>
  "a function-variable counterexample was not an UPDATE-chain witness")
  (fn () => ()) ()

val _ = tprint "Refute QC random backend"

fun random config goal =
  case preprocess config (qc_problem goal) of
      NotExecutable reasons => Unknown reasons
    | Preprocessed instances =>
        strategy_run (Random {seed = strategy_seed config}) config instances

fun same_bindings [] [] = true
  | same_bindings ((variable1, value1) :: rest1)
      ((variable2, value2) :: rest2) =
      Term.aconv variable1 variable2 andalso Term.aconv value1 value2 andalso
      same_bindings rest1 rest2
  | same_bindings _ _ = false

fun same_random_outcome (Counterexample (left :: _))
      (Counterexample (right :: _)) =
      #backend left = #backend right andalso
      #substrate left = #substrate right andalso
      #certainty left = #certainty right andalso
      same_bindings (#bindings left) (#bindings right) andalso
      List.filter (fn (name, _) => name <> "msec") (#stats left) =
      List.filter (fn (name, _) => name <> "msec") (#stats right)
  | same_random_outcome NoCounterexample NoCounterexample = true
  | same_random_outcome (Unknown left) (Unknown right) = left = right
  | same_random_outcome _ _ = false

val random_config = upd_iterations 50
  (upd_size 4 (upd_seed (SOME 1) default_config))

fun random_is_registered () =
  case lookup_backend "random" of
      SOME backend => #weight backend = 30
    | NONE => false

fun random_reverse_counterexample () =
  case random random_config ``REVERSE (xs : num list) = xs`` of
      Counterexample (cex :: _) =>
        #substrate cex = "cv" andalso
        Option.isSome (lookup_stat "msec" (#stats cex))
    | _ => false

fun random_arithmetic_counterexample () =
  case random random_config ``(x : num) - y + y = x`` of
      Counterexample _ => true
    | _ => false

fun random_seed_is_reproducible () =
  let
    val goal = ``REVERSE (xs : num list) = xs``
    val prior_seed = !session_seed
    val left = random random_config goal
    val right = random random_config goal
  in
    same_random_outcome left right andalso !session_seed = prior_seed
  end

fun session_random_completes () =
  let
    val config = upd_iterations 2 (upd_size 2 default_config)
    val prior_seed = !session_seed
    val result = random config ``(x : num) = 0``
  in
    !session_seed = rand_next prior_seed andalso
    (case result of
         Counterexample _ => true
       | NoCounterexample => true
       | Unknown _ => true)
  end

fun list_draws_respect_floors () =
  let
    fun draw 0 _ = true
      | draw remaining state =
          let val (_, next) = random_term ``:num list`` 0 state
          in draw (remaining - 1) next end
  in
    draw 100 1
  end

fun compute_stream_dump_is_pinned () =
  let
    val first = Term.mk_var ("m", ``:num``)
    val second = Term.mk_var ("n", ``:num``)
    val candidates = dump_random_candidates
      {plan = Gen (first, Gen (second, Test boolSyntax.T)),
       seed = 1, size = 999, count = 2}
    fun values terms = List.map
      (Arbnum.toInt o numSyntax.dest_numeral) terms
  in
    List.map values candidates = [[423, 509], [648, 382]]
  end

val _ = require_msg (check_result random_reverse_counterexample) (fn () =>
  "the random backend did not refute REVERSE xs = xs") (fn () => ()) ()

val _ = require_msg (check_result random_is_registered) (fn () =>
  "the random backend was not registered with weight 30") (fn () => ()) ()

val _ = require_msg (check_result random_arithmetic_counterexample) (fn () =>
  "the random backend did not refute x - y + y = x") (fn () => ()) ()

val _ = require_msg (check_result random_seed_is_reproducible) (fn () =>
  "the random backend was not reproducible for an explicit seed")
  (fn () => ()) ()

val _ = require_msg (check_result session_random_completes) (fn () =>
  "the session random generator did not complete a run") (fn () => ()) ()

val _ = require_msg (check_result list_draws_respect_floors) (fn () =>
  "small-budget recursive list draws raised an exception") (fn () => ()) ()

val _ = require_msg (check_result compute_stream_dump_is_pinned) (fn () =>
  "the compute candidate-dump hook did not preserve the pinned stream")
  (fn () => ()) ()

(* The public corpus precedes the potential-path tests below.  Those tests
   replace the ordinary list generator with tiny adversarial generators. *)
val selftest_level =
  case OS.Process.getEnv "HOLSELFTESTLEVEL" of
      NONE => 1
    | SOME text =>
        (case Int.fromString text of
            NONE => 1
          | SOME level => level)

fun same_snapshot (left : Refute_EvalCv.snapshot)
    (right : Refute_EvalCv.snapshot) =
  #theory left = #theory right andalso
  same_string_set (#types left) (#types right) andalso
  same_string_set (#constants left) (#constants right) andalso
  same_string_set (#bindings left) (#bindings right)

fun make_bracket_artifacts suffix =
  let
    val prefix = fresh_prefix () ^ suffix
    val _ = Theory.new_type (prefix ^ "_type", 0)
    val _ = Theory.new_constant (prefix ^ "_const", ``:num``)
    val _ = Theory.save_thm (prefix ^ "_binding", boolTheory.TRUTH)
  in
    ()
  end

fun clean_bracket_success () =
  let
    val baseline = snapshot ()
    val _ = with_clean_theory (fn () => make_bracket_artifacts "success")
  in
    same_snapshot baseline (snapshot ())
  end

fun clean_bracket_exception () =
  let
    val baseline = snapshot ()
    val raised =
      ((with_clean_theory (fn () =>
          (make_bracket_artifacts "exception";
           raise Fail "forced cv bracket failure")); false)
       handle Fail "forced cv bracket failure" => true)
  in
    raised andalso same_snapshot baseline (snapshot ())
  end

fun clean_bracket_interrupt () =
  let
    val baseline = snapshot ()
    val raised =
      ((with_clean_theory (fn () =>
          (make_bracket_artifacts "interrupt"; raise Interrupt)); false)
       handle Interrupt => true)
  in
    raised andalso same_snapshot baseline (snapshot ())
  end

fun translation_error_is_clean () =
  let
    val baseline = snapshot ()
    val attempt = with_generators [``:bool``] (fn _ =>
      (make_bracket_artifacts "hol_error";
       raise (Feedback.mk_HOL_ERR
         "RefuteCvSelftest" "translate" "forced translation error")))
  in
    (case attempt of
         CvInapplicable [reason] =>
           String.isPrefix "cv: RefuteCvSelftest.translate" reason
       | _ => false) andalso
    same_snapshot baseline (snapshot ())
  end

val _ = tprint "Refute cv clean-theory bracket"
val _ = require_msg (check_result (fn () =>
  clean_bracket_success () andalso clean_bracket_exception () andalso
  clean_bracket_interrupt () andalso translation_error_is_clean ()))
  (fn () =>
    "cv bracket left a theory artifact on a return or exception")
  (fn () => ()) ()

fun generated_tree_agrees () =
  let
    val baseline = snapshot ()
    val attempt = with_generators [``:rg_tree``] (fn generators =>
      case generators of
          [{exhaustive, random, ...}] =>
            let
              fun exhaustive_agrees size =
                let
                  val application = Term.mk_comb
                    (exhaustive, numSyntax.term_of_int size)
                  val (actual, _) = listSyntax.dest_list
                    (cv_rhs application)
                in
                  same_terms (compute_exhaustive ``:rg_tree`` size) actual
                end
              fun random_agrees size seed =
                let
                  val application = Term.list_mk_comb
                    (random,
                     [numSyntax.term_of_int size,
                      numSyntax.term_of_int seed])
                  val (actual_value, actual_state) =
                    pairSyntax.dest_pair (cv_rhs application)
                  val (expected_value, expected_state) =
                    random_term ``:rg_tree`` size (IntInf.fromInt seed)
                in
                  Term.aconv actual_value expected_value andalso
                  Term.aconv actual_state
                    (num_term_of_intinf expected_state)
                end
            in
              List.all exhaustive_agrees [0, 1, 2] andalso
              List.all (fn seed => random_agrees 3 seed) [1, 2, 3]
            end
        | _ => false)
  in
    (case attempt of CvSuccess result => result
     | CvInapplicable _ => false) andalso
    same_snapshot baseline (snapshot ())
  end

fun generated_finite_agrees ty =
  let
    val baseline = snapshot ()
    val attempt = with_generators [ty] (fn generators =>
      case generators of
          [{exhaustive, random, ...}] =>
            let
              fun exhaustive_agrees size =
                let
                  val application = Term.mk_comb
                    (exhaustive, numSyntax.term_of_int size)
                  val (actual, _) = listSyntax.dest_list
                    (cv_rhs application)
                in
                  same_terms (compute_exhaustive ty size) actual
                end
              fun random_agrees seed =
                let
                  val application = Term.list_mk_comb
                    (random,
                     [numSyntax.term_of_int 3,
                      numSyntax.term_of_int seed])
                  val (actual_value, actual_state) =
                    pairSyntax.dest_pair (cv_rhs application)
                  val (expected_value, expected_state) =
                    random_term ty 3 (IntInf.fromInt seed)
                in
                  Term.aconv actual_value expected_value andalso
                  Term.aconv actual_state
                    (num_term_of_intinf expected_state)
                end
            in
              List.all exhaustive_agrees [0, 2] andalso
              List.all random_agrees [1, 2, 3]
            end
        | _ => false)
  in
    (case attempt of CvSuccess result => result
     | CvInapplicable _ => false) andalso
    same_snapshot baseline (snapshot ())
  end

fun generated_tree_repeats_and_caches () =
  let
    val baseline = snapshot ()
    val stats0 = synthesis_stats ()
    val first = generated_tree_agrees ()
    val stats1 = synthesis_stats ()
    val second = generated_tree_agrees ()
    val stats2 = synthesis_stats ()
  in
    first andalso second andalso
    #misses stats1 = #misses stats0 + 1 andalso
    #misses stats2 = #misses stats1 andalso
    #hits stats2 = #hits stats1 + 1 andalso
    same_snapshot baseline (snapshot ())
  end

fun out_of_fragment_is_clean () =
  let
    val baseline = snapshot ()
    fun rejected ty =
      case with_generators [ty]
          (fn _ => raise Fail "out-of-fragment continuation ran") of
          CvInapplicable reasons =>
            not (null reasons) andalso
            List.all (String.isPrefix "cv: ") reasons
        | CvSuccess _ => false
  in
    rejected ``:real`` andalso rejected ``:num -> bool`` andalso
    same_snapshot baseline (snapshot ())
  end

val _ =
  if selftest_level >= 2 then
    (tprint "Refute cv per-goal generator synthesis";
     require_msg (check_result generated_tree_repeats_and_caches) (fn () =>
       "cv generator synthesis disagreed, leaked, or missed its cache")
       (fn () => ()) ();
     require_msg (check_result (fn () =>
       generated_finite_agrees ``:rg_enum`` andalso
       generated_finite_agrees ``:bool option``)) (fn () =>
         "cv finite generator synthesis disagreed or leaked an artifact")
       (fn () => ()) ();
     require_msg (check_result out_of_fragment_is_clean) (fn () =>
       "cv accepted an out-of-fragment type or leaked an artifact")
       (fn () => ()) ())
  else ()

fun first_cex_bindings (Counterexample (cex :: _)) =
      SOME (#bindings cex)
  | first_cex_bindings _ = NONE

fun cv_result strategy choice goal =
  let
    val config = upd_substrate choice
      (upd_iterations 100 (upd_size 3 default_config))
  in
    case preprocess config (qc_problem goal) of
        Preprocessed instances => strategy_run strategy config instances
      | NotExecutable reasons => Unknown reasons
  end

fun cv_agrees strategy goal =
  let
    val baseline = snapshot ()
    val compute = cv_result strategy Compute goal
    val cv = cv_result strategy Cv goal
  in
    (case (first_cex_bindings compute, first_cex_bindings cv) of
         (SOME left, SOME right) => same_bindings left right
       | (NONE, NONE) =>
           (case (compute, cv) of
                (NoCounterexample, NoCounterexample) => true
              | (Unknown _, Unknown _) => true
              | _ => false)
       | _ => false) andalso same_snapshot baseline (snapshot ())
  end

fun explicit_cv_smoke () =
  let
    val goal = ``REVERSE (xs : num list) = xs``
  in
    cv_agrees Exhaustive goal andalso
    cv_agrees (Random {seed = 1}) goal
  end

val _ = tprint "Refute cv substrate smoke"
val _ = require_msg (check_result explicit_cv_smoke) (fn () =>
  "the cv substrate disagreed with compute or leaked theory state")
  (fn () => ()) ()

fun cv_matrix_agrees () =
  let
    val goals =
      [("list", ``REVERSE (xs : num list) = xs``),
       ("table", ``(x : refute$rf3) = rf3_1``),
       ("synthesised", ``(t : rg_tree) = RGTip n ==> F``)]
    fun check (_, goal) strategy = cv_agrees strategy goal
    fun strategies goal =
      check goal Exhaustive andalso
      List.all (fn seed => check goal (Random {seed = seed}))
        [1, 2, 3]
  in
    List.all strategies goals
  end

fun cv_stream_resumes () =
  let
    val variable = Term.mk_var ("x", ``:num``)
    val plan = Gen
      (variable, Test (boolSyntax.mk_neg
        (boolSyntax.mk_eq (variable, ``2803 : num``))))
    fun run compile =
      case compile default_config (Random {seed = 1}) [plan] of
          Inapplicable reasons =>
            raise Fail (String.concatWith "; " reasons)
        | Compiled test =>
            let
              val first = #run test
                {genuine_only = true, card = 1, size = 5000,
                 draws = 1024, ignored = []}
              val middle = #run test
                {genuine_only = true, card = 1, size = 5000,
                 draws = 75, ignored = []}
              val last = #run test
                {genuine_only = true, card = 1, size = 5000,
                 draws = 1, ignored = []}
              val _ = #close test ()
            in
              (first, middle, last)
            end
    val baseline = snapshot ()
    val (compute_first, compute_middle, compute_last) =
      run Refute_EvalCompute.compile
    val (cv_first, cv_middle, cv_last) = run Refute_EvalCv.compile
    fun is_empty (Exhausted _) = true | is_empty _ = false
    fun value (CexFound {env = [(_, tm)], ...}) = SOME tm
      | value _ = NONE
  in
    is_empty compute_first andalso is_empty cv_first andalso
    is_empty compute_middle andalso is_empty cv_middle andalso
    (case (value compute_last, value cv_last) of
         (SOME left, SOME right) =>
           Term.aconv left ``2803 : num`` andalso Term.aconv left right
       | _ => false) andalso same_snapshot baseline (snapshot ())
  end

fun cv_partial_is_clean () =
  let
    val baseline = snapshot ()
    val variable = Term.mk_var ("xs", ``:num list``)
    val plan = Gen
      (variable, Test ``HD (xs : num list) = HD xs``)
    val rejected =
      case Refute_EvalCv.compile default_config Exhaustive [plan] of
          Inapplicable reasons =>
            List.exists (fn reason =>
              String.isSubstring "cv: precondition for HD" reason) reasons
        | Compiled test => (#close test (); false)
  in
    rejected andalso same_snapshot baseline (snapshot ())
  end

fun cv_racing_is_clean () =
  let
    val baseline = snapshot ()
    val config = upd_substrate Cv
      (upd_iterations 20
        (upd_size 2
          (upd_sequential false
            (upd_backends (SOME ["exhaustive", "random"])
              default_config))))
    val result = Refute.refute config ``(b : bool)``
    val certified =
      case result of
          Refute.Counterexample ({cert = SOME _, ...} :: _) => true
        | _ => false
  in
    certified andalso same_snapshot baseline (snapshot ())
  end

val _ =
  if selftest_level >= 2 then
    (tprint "Refute cv substrate conformance";
     require_msg (check_result cv_matrix_agrees) (fn () =>
       "cv disagreed with compute on the corpus slice")
       (fn () => ()) ();
     require_msg (check_result cv_stream_resumes) (fn () =>
       "the cv random stream did not resume across chunks")
       (fn () => ()) ();
     require_msg (check_result cv_partial_is_clean) (fn () =>
       "cv accepted a partial property or leaked theory state")
       (fn () => ()) ();
     require_msg (check_result cv_racing_is_clean) (fn () =>
       "the racing cv run failed or leaked theory state")
       (fn () => ()) ())
  else ()

val corpus_config =
  upd_timeout 5.0
    (upd_seed (SOME 1)
      (upd_sequential true
        (upd_backends (SOME ["exhaustive"]) default_config)))

fun cex_is_certified (Refute.Counterexample ({cert = SOME _, ...} :: _)) = true
  | cex_is_certified _ = false

fun cex_is_genuine_certified
      (Refute.Counterexample
        ({certainty = Refute.Genuine, cert = SOME _, ...} :: _)) = true
  | cex_is_genuine_certified _ = false

fun public_expect ExpectCex = Refute.ExpectCex
  | public_expect ExpectNone = Refute.ExpectNone
  | public_expect ExpectUnknown = Refute.ExpectUnknown
  | public_expect NoExpectation = Refute.NoExpectation

fun tc {name, cfg, tm, expect} =
  let
    val _ = tprint name
    val config = Refute.upd_expect (public_expect expect) cfg
    val result = Refute.refute config tm
    val _ =
      case expect of
          ExpectCex =>
            if cex_is_certified result then ()
            else raise Fail "expected a certified counterexample"
        | _ => ()
  in
    OK ()
  end
  handle e => die (Feedback.exn_to_string e)

fun is_unknown_with needle (Refute.Unknown reasons) =
      List.exists (String.isSubstring needle) reasons
  | is_unknown_with _ _ = false

fun check_corpus name predicate =
  let val _ = tprint name
  in if predicate () then OK () else die "corpus check failed" end
  handle e => die (Feedback.exn_to_string e)

fun same_corpus_outcome (Refute.Counterexample _, Refute.Counterexample _) =
      true
  | same_corpus_outcome (Refute.NoCounterexample, Refute.NoCounterexample) =
      true
  | same_corpus_outcome (Refute.Unknown left, Refute.Unknown right) =
      left = right
  | same_corpus_outcome _ = false

fun corpus_smoke () =
  (tc {name = "Refute corpus: classic reverse",
       cfg = corpus_config,
       tm = ``REVERSE (xs : num list) = xs``,
       expect = ExpectCex};
   tc {name = "Refute corpus: arithmetic",
       cfg = corpus_config,
       tm = ``(x : num) - y + y = x``,
       expect = ExpectCex};
   tc {name = "Refute corpus: sound reverse",
       cfg = corpus_config,
       tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
       expect = ExpectNone})

fun corpus_classics () =
  (tc {name = "Refute corpus: reverse append mutation",
       cfg = corpus_config,
       tm = ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: ALL_DISTINCT append mutation",
       cfg = corpus_config,
       tm = ``ALL_DISTINCT (xs : num list ++ ys) <=>
             ALL_DISTINCT xs /\ ALL_DISTINCT ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: nub append mutation",
       cfg = corpus_config,
       tm = ``nub (xs : num list ++ ys) = nub xs ++ nub ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: integer order mutation",
       cfg = corpus_config,
       tm = ``~((x : int) = x)``,
       expect = ExpectCex})

fun corpus_smart_quantifiers () =
  let
    val ordered_insert =
      ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``
    val lookup =
      ``(m1 : num -> num option) k = SOME (v : num) ==>
        m1 k = NONE``
    val let_case =
      ``let z = (xs : num option) in
          case z of NONE => F | SOME x => x = x``
  in
    tc {name = "Refute corpus: sorted insert mutation",
        cfg = corpus_config, tm = ordered_insert, expect = ExpectCex};
    tc {name = "Refute corpus: fmap lookup premise",
        cfg = corpus_config, tm = lookup, expect = ExpectCex};
    check_corpus "Refute corpus: let/case plan" (fn () =>
      case compile_plan corpus_config let_case of
          Gen (_, Test _) => true
        | _ => false)
  end

fun corpus_default_quickcheck () =
  let
    fun check name tm =
      check_corpus ("Refute default quickcheck: " ^ name) (fn () =>
        cex_is_genuine_certified (Refute.quickcheck tm))
  in
    check "classic reverse" ``REVERSE (xs : num list) = xs``;
    check "reverse append mutation"
      ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``;
    check "ALL_DISTINCT append mutation"
      ``ALL_DISTINCT (xs : num list ++ ys) <=>
        ALL_DISTINCT xs /\ ALL_DISTINCT ys``;
    check "nub append mutation"
      ``nub (xs : num list ++ ys) = nub xs ++ nub ys``;
    check "integer order mutation" ``~((x : int) = x)``;
    check "sorted insert mutation"
      ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``;
    check "fmap lookup premise"
      ``(m1 : num -> num option) k = SOME (v : num) ==>
        m1 k = NONE``
  end

fun corpus_potential () =
  let
    val hd_goal =
      ``HD (xs : num list) = if xs = [] then HD ys else HD xs``
    val hd_map = ``~(HD (MAP (f : num -> num) xs) = f (HD xs))``
    val short_lists : custom_gen =
      { enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
        random = NONE }
    val _ = register_generator ``:num list`` short_lists
    val abort_config = upd_abort_potential true corpus_config
    val genuine_config = upd_genuine_only true corpus_config
    fun potential result =
      case result of
          Refute_Core.Counterexample
            ({certainty = Refute_Core.Potential _, cert = NONE, ...} :: _) =>
              true
        | _ => false
  in
    check_corpus "Refute corpus: HD potential only" (fn () =>
      potential (exhaustive abort_config hd_goal));
    check_corpus "Refute corpus: abort potential" (fn () =>
      potential (exhaustive abort_config hd_goal));
    check_corpus "Refute corpus: genuine only" (fn () =>
      case exhaustive genuine_config hd_goal of
          Refute_Core.Counterexample _ => false
        | _ => true);
    tc {name = "Refute corpus: HD/MAP certification upgrade",
        cfg = corpus_config, tm = hd_map, expect = ExpectCex}
  end

fun corpus_polymorphism () =
  (tc {name = "Refute corpus: polymorphic lists",
       cfg = corpus_config,
       tm = ``(xs : 'a list) = ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: polymorphic card schedule",
       cfg = corpus_config,
       tm = ``(x : 'a) = y``,
       expect = ExpectCex};
   tc {name = "Refute corpus: num fallback",
       cfg = upd_finite_types false corpus_config,
       tm = ``(x : 'a) = y``,
       expect = ExpectCex})

fun corpus_functions () =
  let
    val map_goal =
      ``MAP (f : num -> num) xs = MAP (g : num -> num) xs ==> f = g``
    val goal =
      ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
        f rf2_2 = rf2_2 ==> F``
  in
    check_corpus "Refute corpus: MAP function plan" (fn () =>
      let val _ = compile_plan corpus_config map_goal in true end);
    tc {name = "Refute corpus: function UPDATE counterexample",
        cfg = corpus_config, tm = goal, expect = ExpectCex};
    check_corpus "Refute corpus: function UPDATE witness" (fn () =>
      case Refute.refute corpus_config goal of
          Refute.Counterexample ({bindings, ...} :: _) =>
            List.exists (fn (_, value) =>
              not (null (#1 (combinSyntax.strip_update value)))) bindings
        | _ => false)
  end

fun corpus_quantifiers () =
  let
    val finite =
      ``(p : bool) /\ (!x : bool. x) /\
        (?y : refute$rf2. y = y)``
    val infinite = ``(!n : num. n <= n)``
  in
    check_corpus "Refute corpus: finite quantifier expansion" (fn () =>
      case preprocess corpus_config (preprocessing_problem finite) of
          Preprocessed [instance] => has_conjunction (#goal instance)
        | _ => false);
    tc {name = "Refute corpus: finite check counterexample",
        cfg = corpus_config, tm = ``(b : bool)``, expect = ExpectCex};
    tc {name = "Refute corpus: num quantifier unknown",
        cfg = corpus_config, tm = infinite, expect = ExpectUnknown}
  end

fun corpus_hol4_specific () =
  let
    val record_goal = ``(r : rg_record) = s``
    val word_goal =
      ``w2n ((a : bool[8]) + b) = w2n a + w2n b``
    val quotient_goal = ``(x : real) = y``
  in
    tc {name = "Refute corpus: record type",
        cfg = corpus_config, tm = record_goal, expect = ExpectCex};
    tc {name = "Refute corpus: word addition",
        cfg = corpus_config, tm = word_goal, expect = ExpectCex};
    tc {name = "Refute corpus: quotient unknown",
        cfg = corpus_config, tm = quotient_goal, expect = ExpectUnknown};
    check_corpus "Refute corpus: quotient explanation" (fn () =>
      is_unknown_with "quotient" (Refute.refute corpus_config quotient_goal))
  end

(* Numeral/string/char literals in a goal must not be mistaken for
   non-executable constants (their internal NUMERAL/BIT1/STRING/CHR
   tags reduce natively under EVAL), so goals mentioning them stay
   testable and their counterexamples are found and certified. *)
fun corpus_literals () =
  (tc {name = "Refute corpus: numeral literal counterexample",
       cfg = corpus_config, tm = ``!n : num. n <> 2``, expect = ExpectCex};
   tc {name = "Refute corpus: character literal counterexample",
       cfg = corpus_config, tm = ``!c : char. c <> #"a"``,
       expect = ExpectCex};
   tc {name = "Refute corpus: string literal counterexample",
       cfg = corpus_config, tm = ``!s : string. s <> "x"``,
       expect = ExpectCex})

fun corpus_soundness () =
  (tc {name = "Refute corpus: sound reverse involution",
       cfg = corpus_config,
       tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound addition commutes",
       cfg = corpus_config,
       tm = ``T``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound bool check_all",
       cfg = corpus_config,
       tm = ``(b : bool) \/ ~b``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound rf check_all",
       cfg = corpus_config,
       tm = ``(x : refute$rf2) = rf2_1 \/ x = rf2_2``,
       expect = ExpectNone})

fun corpus_registries () =
  let
    val _ = Datatype.Datatype `rg_sorted = RGSorted (num list)`
    val sorted_ty = ``:rg_sorted``
    val sorted_constructor = ``RGSorted``
    val sorted_predicate =
      ``\s : rg_sorted. case s of RGSorted xs => SORTED $<= xs``
    val _ = abstract_generator
      {ty = sorted_ty,
       constructors = [sorted_constructor],
       pred = SOME sorted_predicate}
    val _ = Datatype.Datatype `rg_custom = RGC0 | RGC1`
    val custom_ty = ``:rg_custom``
    val custom : custom_gen =
      {enumerate = SOME (fn _ => [``RGC0``, ``RGC1``]), random = NONE}
    val _ = register_generator custom_ty custom
  in
    check_corpus "Refute corpus: sorted abstract generator" (fn () =>
      case (spec_of sorted_ty, predicate_of sorted_ty) of
          (GenDatatype _, SOME predicate) =>
            Term.aconv predicate sorted_predicate
        | _ => false);
    check_corpus "Refute corpus: registered custom generator" (fn () =>
      case spec_of custom_ty of GenCustom _ => true | _ => false);
    tc {name = "Refute corpus: custom generator counterexample",
        cfg = corpus_config,
        tm = ``(x : rg_custom) = RGC0``,
        expect = ExpectCex}
  end

fun corpus_parlist () =
  let
    val parallel_config =
      upd_backends (SOME ["exhaustive", "random"])
        (upd_sequential false corpus_config)
    val sequential_config =
      upd_backends (SOME ["exhaustive", "random"]) corpus_config
    val cex_goal = ``(x : num) - y + y = x``
    val sound_goal = ``(!b : bool. b \/ ~b)``
    fun same goal =
      same_corpus_outcome
        (Refute.refute sequential_config goal,
         Refute.refute parallel_config goal)
  in
    check_corpus "Refute corpus: ParList get_first" (fn () =>
      ParList.get_first (fn n => if n = 2 then SOME n else NONE) [1, 2, 3]
        = SOME 2);
    check_corpus "Refute corpus: ParList get_some" (fn () =>
      case ParList.get_some (fn n =>
        if n = 2 orelse n = 3 then SOME n else NONE) [1, 2, 3] of
          SOME 2 => true
        | SOME 3 => true
        | _ => false);
    check_corpus "Refute corpus: parallel counterexample outcome" (fn () =>
      same cex_goal);
    check_corpus "Refute corpus: parallel sound outcome" (fn () =>
      same sound_goal)
  end

val _ =
  if selftest_level >= 2 then
    (corpus_smoke ();
     corpus_classics ();
     corpus_smart_quantifiers ();
     corpus_default_quickcheck ();
     corpus_polymorphism ();
     corpus_functions ();
     corpus_quantifiers ();
     corpus_hol4_specific ();
     corpus_literals ();
     corpus_soundness ();
     corpus_registries ();
     corpus_parlist ())
  else
    corpus_smoke ()

val _ = tprint "Refute certification and potential retry"

fun certified_reverse () =
  case exhaustive (upd_size 3 default_config)
    ``REVERSE (xs : num list) = xs`` of
      Counterexample ({certainty = Genuine, cert = SOME theorem, ...} :: _) =>
        Term.aconv (Thm.concl theorem)
          ``~(!xs : num list. REVERSE xs = xs)`` andalso
        null (Tag.axioms_of (Thm.tag theorem))
    | _ => false

val _ = require_msg (check_result certified_reverse) (fn () =>
  "REVERSE xs = xs was not certified with a tag-clean theorem")
  (fn () => ()) ()

fun make_cex genuine : counterexample =
  { backend = "selftest",
    substrate = "compute",
    certainty = Refute_Core.Potential [],
    bindings = [],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [("tests", 1)] }

fun upgrade_from_stuck_path () =
  case Refute_Cert.certify
    { original = ``F``,
      evals = [],
      env = [],
      cex = make_cex false } of
      Certified {certainty = Genuine, cert = SOME theorem, ...} =>
        Term.aconv (Thm.concl theorem) ``~F``
    | _ => false

val _ = require_msg (check_result upgrade_from_stuck_path) (fn () =>
  "certification did not upgrade a tainted candidate to Genuine")
  (fn () => ()) ()

fun false_positive_is_discarded () =
  case Refute_Cert.certify
    { original = ``T``,
      evals = [],
      env = [],
      cex = make_cex true } of
      Discarded => true
    | _ => false

val _ = require_msg (check_result false_positive_is_discarded) (fn () =>
  "certification did not discard an EVAL-true candidate") (fn () => ()) ()

val stuck_list_gen : custom_gen =
  { enumerate = SOME (fn _ => [``[] : num list``]), random = NONE }

val _ = register_generator ``:num list`` stuck_list_gen

val stuck_goal = ``HD (xs : num list) = 0``

fun potential_only config = exhaustive config stuck_goal

fun default_retries_potential () =
  case potential_only (upd_size 1 default_config) of
      Counterexample _ => false
    | Unknown _ => true
    | NoCounterexample => true

fun abort_returns_potential () =
  case potential_only (upd_abort_potential true
    (upd_size 1 default_config)) of
      Counterexample
        ({certainty = Refute_Core.Potential _, cert = NONE, ...} :: _) => true
    | _ => false

fun genuine_only_hides_potential () =
  case potential_only (upd_genuine_only true
    (upd_size 1 default_config)) of
      Counterexample _ => false
    | Unknown _ => true
    | NoCounterexample => true

val _ = require_msg (check_result default_retries_potential) (fn () =>
  "the default flow returned a potential instead of retrying genuinely")
  (fn () => ()) ()

val _ = require_msg (check_result abort_returns_potential) (fn () =>
  "abort_potential did not return the potential counterexample")
  (fn () => ()) ()

val _ = require_msg (check_result genuine_only_hides_potential) (fn () =>
  "genuine_only surfaced a potential counterexample") (fn () => ()) ()

val hd_map_lists : custom_gen =
  { enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
    random = NONE }

val _ = register_generator ``:num list`` hd_map_lists

fun hd_map_stuck_path_upgrades () =
  case exhaustive (upd_size 1 default_config)
    ``~(HD (MAP (f : num -> num) xs) = f (HD xs))`` of
      Counterexample ({certainty = Genuine, cert = SOME _, ...} :: _) => true
    | _ => false

val _ = require_msg (check_result hd_map_stuck_path_upgrades) (fn () =>
  "the HD/MAP stuck path was not upgraded to a genuine counterexample")
  (fn () => ()) ()

val _ = tprint "Refute public facade"

fun facade_reverse () =
  case Refute.quickcheck ``(x : num) - y + y = x`` of
      Refute.Counterexample _ => true
    | _ => false

fun facade_expectation () =
  ((ignore (Refute.refute
      (Refute.upd_expect Refute.ExpectNone
        (Refute.upd_backends (SOME ["exhaustive"]) default_config))
      ``(x : num) - y + y = x``); false)
   handle _ => true)

fun facade_parallel () =
  case Refute.refute
    (Refute.upd_sequential false
      (Refute.upd_backends (SOME ["exhaustive"]) default_config))
    ``(x : num) - y + y = x`` of
      Refute.Counterexample _ => true
    | _ => false

fun facade_tactic_fails () =
  ((ignore (Refute.REFUTE_TAC
      ([], ``(x : num) - y + y = x``)); false)
   handle _ => true)

fun facade_tactic_allows_unknown () =
  ((ignore (Refute.REFUTE_TAC ([], ``(x : ind) = x``)); true)
   handle _ => false)

fun facade_assumptions () =
  case (Refute.refute_goal
    (Refute.upd_backends (SOME ["exhaustive"]) default_config)
    ([``b : bool``], ``b : bool``),
    Refute.refute_goal
      (Refute.upd_no_assms true
        (Refute.upd_backends (SOME ["exhaustive"]) default_config))
      ([``b : bool``], ``b : bool``)) of
      (Refute.NoCounterexample, Refute.Counterexample _) => true
    | _ => false

val _ = require_msg (check_result facade_reverse) (fn () =>
  "the public quickcheck facade did not find a counterexample")
  (fn () => ()) ()
val _ = require_msg (check_result facade_expectation) (fn () =>
  "the public expect check did not raise on a mismatch") (fn () => ()) ()
val _ = require_msg (check_result facade_parallel) (fn () =>
  "the public parallel facade did not find a counterexample")
  (fn () => ()) ()
val _ = require_msg (check_result facade_tactic_fails) (fn () =>
  "REFUTE_TAC did not fail on a refutable goal") (fn () => ()) ()
val _ = require_msg (check_result facade_tactic_allows_unknown) (fn () =>
  "REFUTE_TAC blocked on an inconclusive goal") (fn () => ()) ()
val _ = require_msg (check_result facade_assumptions) (fn () =>
  "refute_goal did not handle assumptions or no_assms") (fn () => ()) ()

val _ = if selftest_level >= 2 then corpus_potential () else ()

val _ = exit_count0 erc
