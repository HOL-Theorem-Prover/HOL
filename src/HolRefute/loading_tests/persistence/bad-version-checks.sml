open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
fun mentions parts (_, _, message) =
  List.all (fn part => String.isSubstring part message) parts
val _ = tprint "unsupported imported formats remain unusable"
val _ = require (check_HOL_ERR (mentions
  ["refutePersistBadVersion", "unsupported format version 2"]))
  Refute.export_registrations [Parse.Type [QUOTE ":persist_old"]]
