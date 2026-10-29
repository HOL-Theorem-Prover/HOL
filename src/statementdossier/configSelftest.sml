open HolKernel Parse boolLib bossLib testutils
open arithmeticTheory listTheory
open statementDossierConfig

fun check label b = (tprint label; if b then OK () else die "FAILED")
fun contains text part = String.isSubstring part text
fun read path =
  let val input = TextIO.openIn path
      val text = TextIO.inputAll input
  in TextIO.closeIn input; text end
fun write path text =
  let val output = TextIO.openOut path
  in TextIO.output (output, text); TextIO.closeOut output end

val source_dir = OS.FileSys.tmpName ()
val _ = write source_dir ""
val _ = OS.FileSys.remove source_dir
val _ = OS.FileSys.mkDir source_dir

val config_path = OS.Path.concat (source_dir, "dossier.toml")
val config_report = OS.Path.concat (source_dir, "report.md")
val config_prose = OS.Path.concat (source_dir, "inputs.md")
val config_snippets = OS.Path.concat (source_dir, "snippets.txt")
val config_printed = OS.Path.concat (source_dir, "snippets.json")
fun report text = (write config_path text; run config_path)
val paths_before = !Meta.loadPath
val unloaded = not (isSome (DB.lookup {Thy = "numposrep", Name = "l2n_def"}))
val _ = report
  "# Comments and multiline arrays are accepted.\n\
  \theorems = [\n  \"numposrep$l2n_def\",\n]\nload_path = [\".\"]\n\
  \[outputs]\nmarkdown = \"report.md\"\n"
val _ = check "TOML loads selected theories without an SML configuration"
  (unloaded andalso
   isSome (DB.lookup {Thy = "numposrep", Name = "l2n_def"}) andalso
   contains (read config_report) "Theorem `l2n_def`")
val _ = check "TOML paths are relative to the configuration file"
  (OS.FileSys.access (config_report, []))
val _ = check "TOML loading restores the caller's load path"
  (!Meta.loadPath = paths_before)

val _ = write config_prose
  "## <=\nThe input `n` is at most `m`.\n\n\
  \Pinned by: `arithmetic$LESS_EQ_REFL`.\n"
val _ = write config_snippets "bTheorem LESS_EQ_IMP_LESS_SUC: ignored"
val _ = report
  "title = \"TOML prose\"\n\
  \theorems = [\"arithmetic$LESS_EQ_IMP_LESS_SUC\"]\n\
  \[assumptions]\ntheorem = \"arithmetic$LESS_EQ_IMP_LESS_SUC\"\n\
  \prose = \"inputs.md\"\n[outputs]\nmarkdown = \"report.md\"\n\
  \[snippets]\ninput = \"snippets.txt\"\noutput = \"snippets.json\"\n"
val _ = check "TOML prose and snippet paths reach the report library"
  (contains (read config_report) "The input `n` is at most `m`" andalso
   contains (read config_report) "LESS_EQ_REFL" andalso
   contains (read config_printed) "LESS_EQ_IMP_LESS_SUC")

fun bad_toml label message text =
  check label ((report text; false) handle Fail s => contains s message)
val _ = bad_toml "TOML outputs must be a table" "expected a table"
  "theorems = [\"bool$TRUTH\"]\noutputs = []\n"
val _ = bad_toml "Unknown TOML configuration fields are rejected"
  "unknown field output" "output = {}\n"
val _ = bad_toml "Duplicate TOML fields are rejected" "duplicate key at title"
  "title = \"one\"\ntitle = \"two\"\n"
val _ = bad_toml "TOML requires selected theorems" "required field is missing"
  ""
val _ = bad_toml "TOML theorem selection must be an array" "expected an array"
  "theorems = true\n"
val _ = bad_toml "TOML names must be qualified" "expected Theory$Name"
  "theorems = [\"TRUTH\"]\n"
val _ = bad_toml "TOML qualified names need a theory" "expected Theory$Name"
  "theorems = [\"$TRUTH\"]\n"
val _ = bad_toml "TOML outputs must have a known format" "unknown format hmtl"
  "theorems = [\"bool$TRUTH\"]\n[outputs]\nhmtl = \"out\"\n"
val _ = bad_toml "TOML requires at least one output" "at least one output"
  "theorems = [\"bool$TRUTH\"]\n[outputs]\n"
val _ = bad_toml "Duplicate TOML output formats are rejected"
  "duplicate key at outputs.markdown"
  "theorems = [\"bool$TRUTH\"]\n[outputs]\n\
  \markdown = \"one\"\nmarkdown = \"two\"\n"
val _ = bad_toml "TOML nested fields reject misspellings" "unknown field pros"
  "theorems = [\"bool$TRUTH\"]\n[outputs]\nmarkdown = \"report.md\"\n\
  \[assumptions]\npros = \"inputs.md\"\n"
val _ = bad_toml "Malformed TOML is rejected" "unexpected"
  "theorems = [}\n"
val _ = List.app OS.FileSys.remove
  [config_path, config_report, config_prose, config_snippets, config_printed]
val _ = OS.FileSys.rmDir source_dir
val _ = print "statementDossierConfig selftests passed\n"
