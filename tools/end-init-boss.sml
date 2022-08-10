let
  val s = "[loading theories and proof tools "
  val l = ["optionTheory", "pairLib", "sumTheory", "numTheory",
           "arithmeticTheory", "Arith", "numLib", "mesonLib", "BasicProvers",
           "Datatype", "listTheory", "bossLib", "pred_setLib"
           ]
  val terminfo = case Process.getEnv "TERM" of
                   SOME s => s
                 | NONE => ""
  val (prelude, dotchar) =
      if terminfo <> "emacs" andalso terminfo <> "dumb"
      then
        (String.map (K #" ") s ^
         CharVector.tabulate(length l,  K #"-") ^ " ]\r", "*")
      else ("", ".")
  fun dotload f = (print dotchar; load f)
  val curdir = FileSys.getDir()
  val () = FileSys.chDir (Path.concat(HOLDIR,"sigobj"))
in
  print prelude;
  print s;
  app dotload l;
  print " ]\n";
  FileSys.chDir curdir
end;

val _ = installPP (mosmlpp simpLib.pp_ssfrag);
val _ = installPP (mosmlpp simpLib.pp_simpset)
val _ = installPP (mosmlpp DefnBase.pp_defn)

open bossLib;  (* Any others? *)

val _ = use (HOLDIR^"/src/proofman/expandq");
(* val _ = use (HOLDIR^"/src/datatype/Interactive"); *)

val _ = quietdec := false;
