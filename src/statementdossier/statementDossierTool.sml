open statementDossierConfig

fun main () =
  (case CommandLine.arguments () of
     [path] => statementDossierConfig.run path
   | _ => raise Fail "usage: statement-dossier CONFIG.toml")
  handle e =>
    (TextIO.output (TextIO.stdErr,
       "statement-dossier: " ^ General.exnMessage e ^ "\n");
     OS.Process.exit OS.Process.failure)
