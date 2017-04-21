(* this is an -*- sml -*- file *)
(* the expectation is that this file gets fed into hol *)
val _ = PolyML.SaveState.loadState "../../bin/hol.state";

use "mkmkcline.sml";
local
  fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)
  fun p1 ++ p2 = OS.Path.concat(p1,p2)
  val cn = PolyML.Compiler.compilerVersionNumber
in
fun main () = let
  val (exeopt,theories,staticp) = mkmkcline.read_cline()
  val exe = case exeopt of NONE => "munge.exe"
                         | SOME s => s
  val tmpnm = OS.FileSys.tmpName ()
  val tmpmungeO = TextIO.openOut tmpnm
  fun p s = TextIO.output(tmpmungeO, s ^ ";\n")
  val exnSuffix =
      "\n  handle e => (die (\"Exception raised: \"^General.exnMessage e))"
  fun gen1 vrb fname =
    p ("fun " ^ fname ^
       "1 s = let val _ = print (\"" ^ vrb ^ " \"^s^\"\\n\") in " ^ fname ^
       " s end" ^ exnSuffix)
in
  p ("val _ = PolyML.SaveState.loadState \"" ^
     String.toString Systeml.DEFAULT_STATE ^"\"");
  p ("fun p1 ++ p2 = OS.Path.concat(p1,p2)");
  p ("load \"EmitTeX\"");
  p ("fun die s = (TextIO.output(TextIO.stdErr, s ^ \"\\n\");\n\
     \             OS.Process.exit OS.Process.failure)");
  gen1 "Loading" "load";
  gen1 "Using" "use";
  p ("val _ = List.app holpathdb.extend_db\n\
     \  (holpathdb.search_for_extensions ReadHMF.find_includes\n\
     \    [OS.FileSys.getDir()])");
  p ("load1 (Globals.HOLDIR ++ \"src\" ++ \"TeX\" ++ \"holindex\")");
  app (fn thy => p ("load1 \"" ^ String.toString thy ^ "\"")) theories;
  app (fn ml => p ("use1 \"" ^
                   String.toString (Globals.HOLDIR ++ "src" ++ "TeX" ++ ml) ^
                   "\""))
      ["mungeTools.sig", "mungeTools.sml", "munger.lex.sml",
       "mkmunger.sml"];

  p ("val main = munger " ^ Bool.toString (551 <= cn andalso cn <= 552)) ;
    (* test necessary to work around bug described at
          https://www.mail-archive.com/polyml@inf.ed.ac.uk/msg00982.html
    *)
  TextIO.closeOut tmpmungeO;
  let val res = Systeml.systeml [Systeml.POLY ^ "c", "-o", exe, tmpnm]
  in
    if OS.Process.isSuccess res then OS.Process.exit res
    else (OS.FileSys.rename {new = "mkscript.debug", old = tmpnm};
          die "Compilation of Poly/ML code failed")
  end
end

end (* local *)
