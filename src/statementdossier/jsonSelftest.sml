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
val _ = OS.FileSys.remove source_dir
val _ = OS.FileSys.mkDir source_dir

val config_path = OS.Path.concat (source_dir, "dossier.json")
val config_report = OS.Path.concat (source_dir, "report.md")
val config_prose = OS.Path.concat (source_dir, "inputs.md")
val config_snippets = OS.Path.concat (source_dir, "snippets.txt")
val config_printed = OS.Path.concat (source_dir, "snippets.json")
fun json_report text = (write config_path text; run config_path)
val paths_before = !Meta.loadPath
val unloaded = not (isSome (DB.lookup {Thy = "numposrep", Name = "l2n_def"}))
val _ = json_report
  "{\"theorems\":[\"numposrep$l2n_def\"],\"load_path\":[\".\"],\
  \\"outputs\":{\"markdown\":\"report.md\"}}"
val _ = check "JSON loads selected theories without an SML configuration"
  (unloaded andalso
   isSome (DB.lookup {Thy = "numposrep", Name = "l2n_def"}) andalso
   contains (read config_report) "Theorem `l2n_def`")
val _ = check "JSON paths are relative to the configuration file"
  (OS.FileSys.access (config_report, []))
val _ = check "JSON loading restores the caller's load path"
  (!Meta.loadPath = paths_before)

val _ = write config_prose
  "## <=\nThe input `n` is at most `m`.\n\n\
  \Pinned by: `arithmetic$LESS_EQ_REFL`.\n"
val _ = write config_snippets "bTheorem LESS_EQ_IMP_LESS_SUC: ignored"
val _ = json_report
  "{\"title\":\"JSON prose\",\
  \\"theorems\":[\"arithmetic$LESS_EQ_IMP_LESS_SUC\"],\
  \\"assumptions\":{\"theorem\":\"arithmetic$LESS_EQ_IMP_LESS_SUC\",\
  \\"prose\":\"inputs.md\"},\"outputs\":{\"markdown\":\"report.md\"},\
  \\"snippets\":{\"input\":\"snippets.txt\",\"output\":\"snippets.json\"}}"
val _ = check "JSON prose and snippet paths reach the report library"
  (contains (read config_report) "The input `n` is at most `m`" andalso
   contains (read config_report) "LESS_EQ_REFL" andalso
   contains (read config_printed) "LESS_EQ_IMP_LESS_SUC")

fun bad_json label message text =
  check label
    ((json_report text; false) handle Fail s => contains s message)
val _ = bad_json "JSON configuration must be an object" "expected an object"
  "[]"
val _ = bad_json "Unknown JSON configuration fields are rejected"
  "unknown field output" "{\"output\":{}}"
val _ = bad_json "Duplicate JSON fields are rejected" "duplicate field title"
  "{\"title\":\"one\",\"title\":\"two\"}"
val _ = bad_json "JSON requires selected theorems" "required field is missing"
  "{}"
val _ = bad_json "JSON theorem selection must be an array" "expected an array"
  "{\"theorems\":true}"
val _ = bad_json "JSON names must be qualified" "expected Theory$Name"
  "{\"theorems\":[\"TRUTH\"]}"
val _ = bad_json "JSON qualified names need a theory" "expected Theory$Name"
  "{\"theorems\":[\"$TRUTH\"]}"
val _ = bad_json "JSON outputs must have a known format" "unknown format hmtl"
  "{\"theorems\":[\"bool$TRUTH\"],\"outputs\":{\"hmtl\":\"out\"}}"
val _ = bad_json "JSON requires at least one output" "at least one output"
  "{\"theorems\":[\"bool$TRUTH\"],\"outputs\":{}}"
val _ = bad_json "Duplicate JSON output formats are rejected"
  "duplicate field markdown"
  "{\"theorems\":[\"bool$TRUTH\"],\"outputs\":{\
  \\"markdown\":\"one\",\"markdown\":\"two\"}}"
val _ = bad_json "JSON nested fields reject misspellings" "unknown field pros"
  "{\"theorems\":[\"bool$TRUTH\"],\"outputs\":{\"markdown\":\"report.md\"},\
  \\"assumptions\":{\"pros\":\"inputs.md\"}}"
val _ = bad_json "Malformed JSON is rejected" "line"
  "{\"theorems\":[}"
val _ = List.app OS.FileSys.remove
  [config_path, config_report, config_prose, config_snippets, config_printed]
val _ = OS.FileSys.rmDir source_dir
val _ = print "statementDossierConfig selftests passed\n"
