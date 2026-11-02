local open Refute in end
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

val _ = check "Refute loads without rational or real theories"
  (not (loaded "rat") andalso not (loaded "realax") andalso
   not (loaded "real"))
val _ = check "core Quickcheck still certifies arithmetic"
  (certified ``(n : num) + 1 = n``)
