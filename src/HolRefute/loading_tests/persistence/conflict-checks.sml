open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
fun mentions parts (_, _, message) =
  List.all (fn part => String.isSubstring part message) parts
val _ = tprint "import conflicts with an incompatible explicit registration"
val _ = require (check_HOL_ERR (mentions
  ["refutePersistWrapper", "persist_old", "incompatible"]))
  Refute.export_registrations [Parse.Type [QUOTE ":persist_old"]]
