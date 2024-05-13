open HolKernel Portable Parse boolLib;

open intLib testutils;

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
    ];

(* check prefer/deprecate rat *)
val grammars = (type_grammar(),term_grammar());
(* val _ = temp_set_grammars grammars *)

val _ = intLib.prefer_int();
val _ = tprint "Checking parse of 0 < x gives ints when ints are preferred";

val expected1 = intSyntax.mk_less(intSyntax.zero_tm,
                                  mk_var("x", intSyntax.int_ty))
val _ = require_msg (check_result (aconv expected1)) term_to_string
                    (quietly Parse.Term) ‘0 < x’

val _ = intLib.deprecate_int();
val _ = tprint "Checking parse of 0 < x gives nats when ints deprecated"

val expected2 = numSyntax.mk_less(numSyntax.zero_tm,
                                  mk_var("x", numSyntax.num))

val _ = require_msg (check_result (aconv expected2)) term_to_string
                    (quietly Parse.Term) ‘0 < x’

val _ = temp_set_grammars grammars;

(* Tests for INTEGER_RULE *)
fun rule_test prover (r as (n,tm)) =
    let
      fun check res = aconv tm (concl res);
    in
      tprint (n ^ ": " ^ term_to_string tm);
      require_msg (check_result check) (term_to_string o concl) prover tm
    end;

val _ = List.app (rule_test INTEGER_RULE) [
      ("INTEGER_RULE_00",
       “w * y + x * z - (w * z + x * y) = (w - x) * (y - z:int)”),
      ("INTEGER_RULE_01",
       “a int_divides &n <=> a int_divides -&n”)
      ];

val _ = Process.exit Process.success;
