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
  app appthis ["regexpMatch", "parse_glob", "internal_functions",
               "Holdep_tokens", "HM_SimpleBuffer"] ;
  app (myuse hmakedir) ["QuoteFilter.sml", "Holmake_tools_dtype"];
  app appthis ["QFRead", "Holdep", "Holmake_tools", "Holmake_types", "ReadHMF"]
end;
