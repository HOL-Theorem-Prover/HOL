val _ = let
  infix ++
  fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
               TextIO.flushOut TextIO.stdErr;
               OS.Process.exit OS.Process.failure)
  fun p1 ++ p2 = OS.Path.concat (p1,p2)
  fun myuse p s =
    let val fullnm = p ++ s
    in
      use (p ++ s)
      handle e => die (fullnm ^ ": compilation failure: "^General.exnMessage e)
    end
  val hmakedir = Systeml.HOLDIR ++ "tools" ++ "Holmake"
  val coredir = hmakedir ++ "core"
  val depsdir = hmakedir ++ "deps"
  val hfsdir = hmakedir ++ "hfs"
  val hmfdir = hmakedir ++ "hmf"
  val hmutildir = hmakedir ++ "util"
  val parsingdir = Systeml.HOLDIR ++ "tools" ++ "parsing"
  val utildir = Systeml.HOLDIR ++ "tools" ++ "util"
  val portableMLdir = Systeml.HOLDIR ++ "src" ++ "portableML"
  val portableMLpolydir = portableMLdir ++ "poly"
  fun appportable s = (myuse portableMLdir (s ^ ".sig"); myuse portableMLdir (s ^ ".sml"))
  fun appthis s = (myuse hmakedir (s ^ ".sig"); myuse hmakedir (s ^ ".sml"))
  fun appcore s = (myuse coredir (s ^ ".sig"); myuse coredir (s ^ ".sml"))
  fun appdeps s = (myuse depsdir (s ^ ".sig"); myuse depsdir (s ^ ".sml"))
  fun apphfs s = (myuse hfsdir (s ^ ".sig"); myuse hfsdir (s ^ ".sml"))
  fun apphmf s = (myuse hmfdir (s ^ ".sig"); myuse hmfdir (s ^ ".sml"))
  fun apputil s = (myuse utildir (s ^ ".sig"); myuse utildir (s ^ ".sml"))
  fun apphmutil s = (myuse hmutildir (s ^ ".sig"); myuse hmutildir (s ^ ".sml"))
  fun appparsing s = (myuse parsingdir (s ^ ".sig"); myuse parsingdir (s ^ ".sml"))
in
  app (myuse hfsdir) ["HOLFS_dtype.sml", "HFS_NameMunge.sig"];
  myuse (hmakedir ++ "poly") "HFS_NameMunge.sml";
  app apphfs ["HOLFileSys"] ;
  app apputil ["regexpMatch"] ;
  app apphmf ["parse_glob"] ;
  app appdeps ["Holdep_tokens"] ;
  app appparsing ["AttributeSyntax"] ;
  app (myuse parsingdir) ["HolLex.sml"];
  app (myuse coredir) ["Holmake_tools_dtype.sml"];
  app (myuse hmutildir) ["terminal_primitives.sig", "poly-terminal-prims.ML"];
  app appparsing ["HolParser"] ;
  app appdeps ["Holdep", "HOLAst", "HOLParser", "HOLToSML", "HOLPrinter"] ;
  app appcore ["Holmake_tools"];
  app apphmf ["internal_functions", "Holmake_types", "ReadHMF"];
  myuse portableMLpolydir "SHA1_ML.sig";
  myuse portableMLpolydir
    (if Systeml.haveWord64 then "w64-SHA1.ML" else "SHA1-byexec.ML");
  app appportable ["SHA1"]
end;
