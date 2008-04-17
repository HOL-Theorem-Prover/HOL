val _ = use "prelude.ML";
val _ = app load ["optionTheory", "pairLib", "sumTheory",
                  "numTheory", "arithmeticTheory", "Arith",
                  "numLib", "mesonLib", "BasicProvers",
                  "SingleStep", "Datatype",
                  "listTheory", "bossLib"];
fun prelude2_main () = 
let
  val terminfo = case OS.Process.getEnv "TERM" of
                   SOME s => s
                 | NONE => ""
  val (prelude, dotchar) =
      if terminfo <> "emacs" andalso terminfo <> "dumb"
      then
        ("                                   ____________ ]\r", "*")
      else ("", ".")
  fun dotload f = (print dotchar; load f)
in
  prelude_main();
  print prelude
end;
open bossLib;
