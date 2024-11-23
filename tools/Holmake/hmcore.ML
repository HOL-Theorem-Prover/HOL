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
  fun appthis s = let
  in
    myuse hmakedir (s ^ ".sig");
    myuse hmakedir (s ^ ".sml")
  end
in
  app (myuse hmakedir) ["HOLFS_dtype.sml", "HFS_NameMunge.sig"];
  myuse (OS.Path.concat(hmakedir, "poly")) "HFS_NameMunge.sml";
  app appthis ["HOLFileSys", "regexpMatch", "parse_glob",
               "Holdep_tokens", "AttributeSyntax"] ;
  app (myuse hmakedir) ["HolLex.sml", "Holmake_tools_dtype.sml",
                        "terminal_primitives.sig",
                        "poly-terminal-prims.ML"];
  app appthis ["HolParser", "Holdep", "Holmake_tools", "internal_functions",
               "Holmake_types",
               "ReadHMF"]
end;
