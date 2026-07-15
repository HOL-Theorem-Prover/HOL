open testutils
open refuteTheory
open Refute_Core

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

val _ = exit_count0 erc
