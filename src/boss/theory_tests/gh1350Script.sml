Theory gh1350

Theorem numcomp[local] = EVAL “2 + 3 * 7”

Theorem stored_version = EVAL “3 + 3 * 7”

val results = DB.match [] “3 * 7”

val _ = assert (List.exists
                    (fn ((thy,nm), _) => thy = "gh1350" andalso nm = "numcomp"))
               results

val _ = assert (List.exists
                    (fn ((thy,nm), _) =>
                       thy = "gh1350" andalso nm = "stored_version"))
               results

