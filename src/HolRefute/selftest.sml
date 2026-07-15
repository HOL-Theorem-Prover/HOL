open testutils
open refuteTheory
open Refute_Core
open Refute_Gen

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
val _ = Datatype.Datatype `rg_left = RGLeft | RGToRight rg_right;
                           rg_right = RGRight rg_left`
val _ = Datatype.Datatype `rg_record = <| rg_field : num |>`
val _ = Datatype.Datatype `rg_enum = RGRed | RGGreen | RGBlue`

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
val finite_custom : custom_gen =
  {enumerate = SOME (fn _ => [``0``]), random = NONE}

fun rejects_empty_custom () =
  ((register_generator ``:ind`` empty_custom; false)
   handle Fail _ => true)

val _ = require_msg (check_result rejects_empty_custom) (fn () =>
  "an empty custom generator was accepted") (fn () => ()) ()
val _ = register_generator ``:ind`` finite_custom
val _ = require_msg (check_result (fn () =>
  case spec_of ``:ind`` of GenCustom _ => true | _ => false))
  (fn () => "custom generator was not registered") (fn () => ()) ()

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

val _ = exit_count0 erc
