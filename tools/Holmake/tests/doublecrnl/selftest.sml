open testutils Holmake_types

fun okenv e =
      lookup e "VAR1" = [LIT "foo bar"] andalso
      lookup e "VAR2" = [LIT "3"] andalso
      lookup e "VAR3" = [LIT "baz  qux"]

fun printfrag (LIT s) = "\"" ^ String.toString s ^ "\""
  | printfrag (VREF s) = "$(" ^ s ^ ")"
fun printquot q =
    "[" ^ String.concatWith "," (map printfrag q) ^ "]"

fun printenv e =
    "ENV{" ^
    String.concatWith ","
                      (List.rev (env_fold (fn k => fn q => fn A =>
                                              (k ^ "=" ^ printquot q) :: A)
                                          e
                                          [])) ^
    "}"

val _ = tprint "Reading sample file containing \\r\\n\\r\\n"
val _ = require_msg (check_result okenv) printenv
                    (#1 o ReadHMF.read "sample_file") (base_environment())
