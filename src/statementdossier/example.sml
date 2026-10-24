(* Run from the HOL root: bin/hol run src/statementdossier/example.sml *)
val _ = loadPath :=
  OS.Path.concat (Globals.HOLDIR, "src/statementdossier") :: !loadPath;
val _ = load "statementDossierLib";
val _ = load "listTheory";

val _ = statementDossierLib.run {
  title = "List reversal and append",
  preamble = "Stored statements and the definitions they use.",
  theorems = [{Thy = "list", Name = "REVERSE_APPEND"}],
  expand_theories = [],
  expand_consts = [{Thy = "list", Name = "REVERSE"},
                   {Thy = "list", Name = "APPEND"}],
  stop_theories = [], stop_consts = [], equation_lemmas = [],
  source_dirs = [("src/list/src",
    OS.Path.concat (Globals.HOLDIR, "src/list/src"))],
  outputs = [(statementDossierLib.Markdown, "list-dossier.md"),
             (statementDossierLib.Html, "list-dossier.html")],
  snippets = NONE, assumptions = NONE,
  supporting = [{Thy = "list", Name = "REVERSE_REVERSE"}]
};
