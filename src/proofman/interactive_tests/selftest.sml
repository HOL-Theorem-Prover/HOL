infix ++
val op++ = OS.Path.concat;

val hol = Globals.HOLDIR ++ "bin" ++ "hol"

fun run args script =
    OS.Process.isSuccess (OS.Process.system (hol ^ " " ^ args ^ " < " ^ script))

val gh2023 = run "--min" "gh2023.ML"
val reentrancy = run "--bare" "reentrancy.ML"

val _ = if gh2023 andalso reentrancy then OS.Process.exit OS.Process.success
        else OS.Process.exit OS.Process.failure
