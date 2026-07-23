infix ++
val op++ = OS.Path.concat;

val result =
  OS.Process.system (
    Globals.HOLDIR ++ "bin" ++ "hol" ^ " --min < gh2023.ML"
  );

val _ = if OS.Process.isSuccess result then OS.Process.exit OS.Process.success
        else OS.Process.exit OS.Process.failure
