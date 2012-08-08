fun extend envlist s f = let
  open Holmake_types
in
  case envlist s of
    [] => ()
  | v => (print ("[extending loadPath with Holmakefile "^s^" variable]\n");
          loadPath := f (!loadPath, v))
end


val _ = if FileSys.access ("Holmakefile", [FileSys.A_READ]) then let
            open Holmake_types
            val (env, _, _) = ReadHMF.read "Holmakefile" base_environment
            fun envlist id =
                map dequote (tokenize (perform_substitution env [VREF id]))
          in
            extend envlist "INCLUDES" (op@);
            extend envlist "PRE_INCLUDES" (fn (lp, mfv) => mfv @ lp)
          end
          handle e => (print "[bogus Holmakefile in current directory \
                             \- ignoring it]\n";
                       TextIO.flushOut TextIO.stdErr;
                       ())
        else ();
