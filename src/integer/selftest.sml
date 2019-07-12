open HolKernel Portable Parse boolLib intLib testutils

(* check that deprecation really deprecates *)
val _ = intLib.deprecate_int()

fun t2s t = trace ("types", 1) term_to_string t
fun rma_p (t,s) =
    (tprint ("int-deprecated parse of "^s);
     require_msg (check_result (aconv t)) t2s (Parse.Term o single o QUOTE) s)

val _ = List.app (ignore o rma_p) [
      (“3n”, "3"),
      (“3n + 2n”, "3 + 2"),
      (“3n * 2n”, "3 * 2"),
      (“3n ** 2n”, "3 ** 2"),
      (“((x:num) ** (y:num)):num”, "x ** y"),
      (“x:int / (y + 1)”, "x / (y + 1)")
    ]
