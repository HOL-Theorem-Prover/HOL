fun main () =
  (case CommandLine.arguments () of
     [path] =>
       let
         val {config, load_path, theories} = statementDossierConfig.read path
         fun report () =
           (List.app (fn thy => Meta.load (thy ^ "Theory")) theories;
            statementDossierLib.run config)
       in
         Lib.with_flag (Meta.loadPath, load_path @ !Meta.loadPath) report ()
       end
   | _ => raise Fail "usage: statement-dossier CONFIG.toml")
  handle e =>
    (TextIO.output (TextIO.stdErr,
       "statement-dossier: " ^ General.exnMessage e ^ "\n");
     OS.Process.exit OS.Process.failure)
