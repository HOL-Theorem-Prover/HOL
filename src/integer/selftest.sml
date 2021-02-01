open HolKernel Portable Parse boolLib intLib testutils

fun noamb_parse s = trace ("guess overloads", 0) Parse.Term [QUOTE s]
fun okparse_exnstruct s = s = "Parse" orelse s = "Preterm"

val _ =
    shouldfail {
      checkexn = fn HOL_ERR {origin_structure, ...} =>
                      okparse_exnstruct origin_structure
                  | _ => false,
      printarg = (fn s => "Parse should fail: “" ^ s ^ "”"),
      printresult = term_to_string,
      testfn = (fn s => Parse.Term[QUOTE s])
    } "¬3";

val _ =
    shouldfail {
      checkexn = fn HOL_ERR {origin_structure, ...} =>
                      okparse_exnstruct origin_structure
                  | _ => false,
      printarg = (fn s => "Parse should be ambiguous: “" ^ s ^ "”"),
      printresult = term_to_string,
      testfn = noamb_parse
    } "~p";

val _ = tprint "Checking “-p” parses unambiguously"
val _ =
    require_msg
      (check_result (fn t => type_of t = “:int”))
      term_to_string
      noamb_parse
      "-p"

val _ = tpp "¬p ∧ q"                                                   (* UOK *)

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
