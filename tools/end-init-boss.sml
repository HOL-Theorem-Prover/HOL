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

local
  structure MPP = MosmlPP
  fun mosmlpp ppfn pps x = let
    val slist = ref ([] : string list)
    fun output_slist () = (app (MPP.add_string pps) (List.rev (!slist));
                           slist := [])
    fun flush ()= output_slist()
    fun consume_string s = let
      open Substring
      val (pfx,sfx) = splitl (fn c => c <> #"\n") (full s)
    in
      if size sfx = 0 then slist := s :: !slist
      else
        (output_slist();
         MPP.add_newline pps;
         if size sfx > 1 then consume_string (string (triml 1 sfx))
         else ())
    end
    val consumer = {consumer = consume_string,
                    linewidth = !Globals.linewidth,
                    flush = flush}
    val newpps = HOLPP.mk_ppstream consumer
  in
    MPP.begin_block pps MPP.INCONSISTENT 0;
    HOLPP.begin_block newpps HOLPP.INCONSISTENT 0;
    ppfn newpps x;
    HOLPP.end_block newpps;
    HOLPP.flush_ppstream newpps;
    MPP.end_block pps
  end
in
  val _ = installPP (mosmlpp simpLib.pp_ssfrag);
  val _ = installPP (mosmlpp simpLib.pp_simpset)
end

open bossLib;  (* Any others? *)

val _ = use (HOLDIR^"/src/proofman/expandq");
(* val _ = use (HOLDIR^"/src/datatype/Interactive"); *)

val Hol_datatype =
  Lib.with_flag
    (Feedback.emit_WARNING,false)
    bossLib.Hol_datatype;


val _ = quietdec := false;
