let
  val terminfo = case Process.getEnv "TERM" of
                   SOME s => s
                 | NONE => ""
  val (prelude, dotchar) =
      if terminfo <> "emacs" andalso terminfo <> "dumb"
      then
        ("                                   ____________ ]\r", "*")
      else ("", ".")
  fun dotload f = (print dotchar; load f)
  val curdir = FileSys.getDir()
  val () = FileSys.chDir (Path.concat(HOLDIR,"sigobj"))
in
  print prelude;
  print "[loading theories and proof tools ";
  app dotload ["optionTheory", "pairLib", "sumTheory",
               "numTheory", "arithmeticTheory", "Arith",
               "numLib", "mesonLib", "BasicProvers",
               "SingleStep", "Datatype",
               "listTheory", "bossLib"];
  print " ]\n";
  FileSys.chDir curdir
end;

open bossLib;  (* Any others? *)

val _ = use (HOLDIR^"/src/proofman/expandq");
(* val _ = use (HOLDIR^"/src/datatype/Interactive"); *)

val _ = quietdec := false;
