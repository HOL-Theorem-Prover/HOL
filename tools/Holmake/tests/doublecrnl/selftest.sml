open testutils Holmake_types

fun okenv e =
      lookup e "VAR1" = [LIT "foo", LIT "bar"] andalso
      lookup e "VAR2" = [LIT "3"]

fun printenv e =
    "ENV{" ^ String.concatWith "," (env_keys e) ^ "}"

val _ = tprint "Reading sample file containing \\r\\n\\r\\n"
val _ = require_msg (check_result okenv) printenv
                    (#1 o ReadHMF.read "sample_file") (base_environment())
