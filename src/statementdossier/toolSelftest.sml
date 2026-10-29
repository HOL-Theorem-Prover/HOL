open testutils

fun check label b = (tprint label; if b then OK () else die "FAILED")
fun write path text =
  let val output = TextIO.openOut path
  in TextIO.output (output, text); TextIO.closeOut output end
fun read path =
  let val input = TextIO.openIn path
      val text = TextIO.inputAll input
  in TextIO.closeIn input; text end

val directory = OS.FileSys.tmpName ()
val _ = write directory ""
val _ = OS.FileSys.remove directory
val _ = OS.FileSys.mkDir directory
val config_path = OS.Path.concat (directory, "dossier.toml")
val report_path = OS.Path.concat (directory, "report.md")
val command = OS.FileSys.fullPath "statement-dossier"
fun run args = OS.Process.isSuccess (Systeml.systeml (command :: args))

val _ = write config_path
  "theorems = [\"numposrep$l2n_def\"]\nload_path = [\".\"]\n\
  \[outputs]\nmarkdown = \"report.md\"\n"
val _ = check "Command loads selected theories and writes relative outputs"
  (run [config_path] andalso
   String.isSubstring "Theorem `l2n_def`" (read report_path))
val _ = check "Command rejects missing arguments" (not (run []))
val _ = write config_path
  "theorems = [\"missingDossierTheory$witness\"]\n\
  \[outputs]\nmarkdown = \"report.md\"\n"
val _ = check "Command reports a failure when a theory cannot load"
  (not (run [config_path]))
val _ = write config_path "theorems = [}\n"
val _ = check "Command reports a failure for malformed TOML"
  (not (run [config_path]))

val _ = List.app OS.FileSys.remove [config_path, report_path]
val _ = OS.FileSys.rmDir directory
val _ = print "statement-dossier command selftests passed\n"
