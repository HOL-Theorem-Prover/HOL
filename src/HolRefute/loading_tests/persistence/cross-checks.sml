open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
fun mentions parts (_, _, message) =
  List.all (fn part => String.isSubstring part message) parts
val _ = tprint "cross-kind sibling history cannot be hidden by replacement"
val _ = require (check_HOL_ERR (mentions
  ["exporting theory", "persist_cross", "incompatible"]))
  Refute.export_registrations [Parse.Type [QUOTE ":persist_cross"]]
