open testutils Holmake_types

(* Pattern-rule parsing tests.  Each `sample_*' file in this directory
   is parsed via ReadHMF.read; we then assert properties of the four
   pieces of state it returns: env, exact ruledb, patrule list, and
   default-target option. *)

fun parse fname = ReadHMF.read fname (base_environment())

fun pat_targets ({targets,...}:patrule) = targets
fun pat_deps    ({deps,...}:patrule)    = deps
fun has_target rdb t = isSome (Binarymap.peek (rdb, t))

fun pat_str p =
    "{tgts=[" ^ String.concatWith "," (pat_targets p) ^
    "], deps=[" ^ String.concatWith "," (pat_deps p) ^ "]}"

fun result_str (_, rdb, prs, _) =
    "patrules=[" ^ String.concatWith ", " (map pat_str prs) ^
    "]; rdb keys=[" ^
    String.concatWith ","
                      (Binarymap.foldr (fn (k,_,a) => k::a) [] rdb) ^ "]"

fun check_basic (_, rdb, prs, _) =
    case prs of
        [p] => pat_targets p = ["%.uo"] andalso pat_deps p = ["%.sml"]
               andalso has_target rdb "all"
               andalso not (has_target rdb "%.uo")
      | _ => false

val _ = tprint "Pattern rule recognised and kept out of exact ruledb"
val _ = require_msg (check_result check_basic) result_str
                    parse "sample_basic"

fun check_mixed (_, rdb, prs, _) =
    case prs of
        [p1, p2] =>
          pat_targets p2 = ["%.uo", "%.ui"]
          andalso pat_deps p2 = ["%.sml", "common.ui"]
          andalso (case Binarymap.peek (rdb, "specific.uo") of
                       SOME {dependencies=["extra.ui"], commands=[]} => true
                     | _ => false)
      | _ => false

val _ = tprint "Multi-target pattern rule + explicit deps coexist"
val _ = require_msg (check_result check_mixed) result_str
                    parse "sample_mixed"

(* `%' in deps but no target with `%' is just a literal character
   (matching GNU make).  The rule should land in the exact ruledb
   with `%.sml' as a verbatim dep. *)
fun check_literal_pct (_, rdb, prs, _) =
    null prs andalso
    (case Binarymap.peek (rdb, "foo.uo") of
         SOME {dependencies=["%.sml"], commands=_::_} => true
       | _ => false)

val _ = tprint "`%' in deps with no `%' target is treated as literal"
val _ = require_msg (check_result check_literal_pct) result_str
                    parse "sample_bad_dep"
