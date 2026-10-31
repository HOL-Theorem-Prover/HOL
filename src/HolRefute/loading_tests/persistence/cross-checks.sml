open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
fun mentions parts (_, _, message) =
  List.all (fn part => String.isSubstring part message) parts
val _ = tprint "cross-kind sibling history cannot be hidden by replacement"
val _ = require (check_HOL_ERR (mentions
  ["exporting theory", "persist_cross", "incompatible"]))
  Refute.export_registrations [Parse.Type [QUOTE ":persist_cross"]]

val qc_config = Refute.default_config
  |> Refute.upd_search (Refute.Only [Refute.Exhaustive])
  |> Refute.upd_quiet true |> Refute.upd_sequential true
  |> Refute.upd_use_subtype true;
val _ = tprint "QuickCheck reports incompatible persisted registrations";
val _ = require (check_result (fn outcome => case outcome of
    Refute.Unknown reasons => List.exists
      (String.isSubstring "incompatible") reasons orelse
      (print (String.concatWith "\n" reasons ^ "\n"); false)
  | _ => false)) (Refute.refute qc_config)
  (Parse.Term [QUOTE "(x : persist_cross) = y"]);
