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
  val depsdir = hmakedir ++ "deps"
  val hmutildir = hmakedir ++ "util"
  val utildir = Systeml.HOLDIR ++ "tools" ++ "util"
  fun appthis s = (myuse hmakedir (s ^ ".sig"); myuse hmakedir (s ^ ".sml"))
  fun appdeps s = (myuse depsdir (s ^ ".sig"); myuse depsdir (s ^ ".sml"))
  fun apputil s = (myuse utildir (s ^ ".sig"); myuse utildir (s ^ ".sml"))
  fun apphmutil s = (myuse hmutildir (s ^ ".sig"); myuse hmutildir (s ^ ".sml"))
in
  app (myuse hmakedir) ["HOLFS_dtype.sml", "HFS_NameMunge.sig"];
  myuse (hmakedir ++ "poly") "HFS_NameMunge.sml";
  app appthis ["HOLFileSys"] ;
  app apputil ["regexpMatch"] ;
  app appthis ["parse_glob"] ;
  app appdeps ["Holdep_tokens"] ;
  app appthis ["AttributeSyntax"] ;
  app (myuse hmakedir) ["HolLex.sml", "Holmake_tools_dtype.sml"];
  app (myuse hmutildir) ["terminal_primitives.sig", "poly-terminal-prims.ML"];
  app appthis ["HolParser"] ;
  app appdeps ["Holdep"] ;
  app appthis ["Holmake_tools", "internal_functions", "Holmake_types", "ReadHMF"]
end;
