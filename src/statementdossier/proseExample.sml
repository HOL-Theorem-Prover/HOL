(* Requires pandoc. Run from the HOL root:
   bin/hol run src/statementdossier/proseExample.sml *)
val _ = loadPath :=
  OS.Path.concat (Globals.HOLDIR, "src/statementdossier") :: !loadPath;
val _ = load "statementDossierLib";
val _ = load "arithmeticTheory";

val _ = statementDossierLib.run {
  title = "A natural-number inequality",
  preamble = "A stored theorem with checked assumption prose.",
  theorems = [{Thy = "arithmetic", Name = "LESS_EQ_IMP_LESS_SUC"}],
  expand_theories = [], expand_consts = [], stop_theories = [],
  stop_consts = [], equation_lemmas = [], source_dirs = [],
  outputs = [(statementDossierLib.Markdown, "arithmetic-dossier.md"),
             (statementDossierLib.Html, "arithmetic-dossier.html")],
  snippets = NONE, supporting = [],
  assumptions = SOME {
    theorem = {Thy = "arithmetic", Name = "LESS_EQ_IMP_LESS_SUC"},
    prose = OS.Path.concat
      (Globals.HOLDIR, "src/statementdossier/example-assumptions.md")}
};
