let
  val s = "[loading theories and proof tools "
  val l = ["optionTheory", "pairLib", "sumTheory", "numTheory",
           "arithmeticTheory", "Arith", "numLib", "mesonLib", "BasicProvers",
           "SingleStep", "Datatype", "listTheory", "bossLib", "EmitTeX",
           "pred_setLib"
           ]
  val terminfo = case Process.getEnv "TERM" of
                   SOME s => s
                 | NONE => ""
  val (prelude, dotchar) =
      if terminfo <> "emacs" andalso terminfo <> "dumb"
      then
        (String.map (K #" ") s ^
         String.implode (List.tabulate(length l,  K #"-")) ^ " ]\r", "*")
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

val _ = (* install prettyprinters for simpsets and ssfrags *)
let
  fun with_pp ppfn pps x =
      Parse.respect_width_ref Globals.linewidth ppfn pps x handle e => Raise e
in
  installPP (with_pp simpLib.pp_ssfrag);
  installPP (with_pp simpLib.pp_simpset)
end;

open bossLib;  (* Any others? *)

val _ = use (HOLDIR^"/src/proofman/expandq");
(* val _ = use (HOLDIR^"/src/datatype/Interactive"); *)

val Hol_datatype =
  Lib.with_flag
    (Feedback.emit_WARNING,false)
    bossLib.Hol_datatype;


val _ = quietdec := false;
