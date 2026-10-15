local open Refute_Real in end
open HolKernel Parse boolLib testutils

fun loaded name = Lib.mem name (Theory.ancestry "-")
fun check name predicate = (tprint name; if predicate then OK () else die name)

val _ = Feedback.set_trace "Refute" 0
val config = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.Exhaustive])
  |> Refute.upd_substrate Refute.Compute
  |> Refute.upd_sequential true
  |> Refute.upd_quiet true
  |> Refute.upd_size 3

fun certified tm =
  case Refute.refute config tm of
      Refute.Counterexample ({cert = SOME th, ...} :: _) =>
        null (Thm.hyp th)
    | _ => false

val _ = check "Refute_Real loads reals without rationals"
  (loaded "real" andalso not (loaded "rat"))
val _ = check "optional real Quickcheck certifies arithmetic"
  (certified ``(r : real) + 1 = r``)
val _ = check "optional real model display is registered"
  (Option.isSome
    (Refute_ModelFinder_Model.lookup_term_postprocessor ``:real``))

val _ = convtest ("optional real inverse evaluation", bossLib.EVAL,
  ``inv (2 / 3 : real) = 3 / 2``, ``T``)
