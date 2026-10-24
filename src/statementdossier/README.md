# Stored theorem dossiers

A theorem's statement can be hard to read when its constants hide several
layers of definitions. `statementDossierLib` writes the stored statement
and follows those definitions, with explicit boundaries chosen by the
caller. It produces Markdown or a standalone HTML file. It does not run
proofs, change statements, or infer that a theorem proves a prose claim.

HTML uses HOL's printer annotations for syntax colours, type tooltips
and links to definitions, datatypes, overloads and unexpanded constants.
The annotated printer has the same layout as the plain printer. Both
formats include free variable types, kernel assumptions, implication
antecedents, the conclusion and trust tags. `DISK_THM` is reported as a
load-from-disk tag. HOL's disk tags preserve oracle tags but omit axiom
dependencies, so the report cannot rule out axioms in loaded theorems.
The report discloses this limitation beside each disk tag. Absence of
recorded problems is not a separate proof audit.

## Example

In a configured, built HOL tree, from its root:

```sh
(cd src/statementdossier && ../../bin/Holmake -j2)
bin/hol run src/statementdossier/example.uo
```

Open `list-dossier.html` or read `list-dossier.md`. The example reports
`list$REVERSE_APPEND`, expands `REVERSE` and `APPEND`, and states
`REVERSE_REVERSE` as a supporting theorem. It uses only HOL's basic
list theory. The example and the selftests need no external programs.
Remove the two generated files when finished; they are not source files.

The examples use ordinary `open` declarations. Holmake records their
dependencies in the `.uo` files, which `hol run` loads before the example.
In an interactive HOL session, open the theories to report and
`statementDossierLib` before calling `run`.
`run : config -> unit` is the report entry point. See `example.sml` for a
complete configuration.

## Configuration

Names are `{Thy : string, Name : string}` records, so theorem and constant
selection does not depend on which theory is open.

- `title`, `preamble`: document heading and opening text.
- `theorems`: stored theorems to report, in order.
- `expand_theories`, `expand_consts`: theories and individual constants
  whose definitions are followed. A constant named individually does
  not automatically expand the constants in its definition.
- `stop_theories`, `stop_consts`: boundaries, overriding expansion.
- `equation_lemmas`: `(constant, theorem list)` pairs to show beside its
  definition, in addition to automatically discovered equation lemmas.
- `source_dirs`: `(label, directory)` pairs containing theory scripts.
  Source paths in the report use the label as a prefix. An empty list
  uses only the file names recorded in the theorem database.
- `outputs`: `(Markdown | Html, output path)` pairs. Parent directories
  must already exist. HTML includes its CSS and small navigation script.
- `supporting`: extra stored theorems, shown without expanding their
  constants beyond the main report's entries.
- `assumptions`: `NONE`, or `SOME {theorem, prose}` for the checked prose
  described below. The theorem must be among `theorems`.
- `snippets`: `NONE`, or `SOME (input path, output path)` for the optional
  document snippets described below.

`script_theories : string list -> string list` lists the theories whose
`*Script.sml` files occur below the supplied directories. Source scanning
skips hidden directories and directory symlinks.

Misspelled theorems, constants and expansion/stop theories are errors.
Load the required theories before calling `run`. Each call takes a fresh
snapshot of the theorem database and sources, so newly stored facts in an
interactive session appear in the next report.

## Definition traversal

Traversal is breadth first, in order of first occurrence in statements,
including kernel assumptions. Each constant appears once, even when its
definition or an equation lemma leads back to a visited constant.

The tool prefers `<constant>_def` when its clauses define that constant,
then other definitions with the same head and inductive `_rules` facts.
When none is available, it shows definitions mentioning the constant and
explicitly says they do not define it. Recursive equations take priority
over `_def_primitive` encodings. Missing definitions are reported.

Automatic equation lemmas have names `<constant>_...`, no kernel
assumptions, and equations with distinct variable arguments and no
recursive occurrence on the right. Explicitly configured lemmas need
not meet that heuristic. Their constants enter the traversal too.
Datatype constructors, case constants and record fields are described
from `TypeBase`, rather than recursively expanding their encodings.

An audit list groups definitions by their occurrence in each theorem:
the conclusion's transitive definition closure; definitions directly
named by hypotheses; and the remaining dependencies, called plumbing.
Equations fixing variables read by the conclusion count with that
conclusion. These groups describe statement dependencies, not proof
provenance or independence of assumptions.

When `source_dirs` are supplied, the tool locates declarations in the
original scripts, which helps when source preprocessing changed recorded
line numbers. This is a textual lookup, not a parser or source map.

## Assumption prose

A prose file has an optional `# Title`, an introduction, and one `## key`
section per hypothesis. Kernel assumptions precede implication
antecedents. A key is the hypothesis's head constant name, or the
variable on the left of an equation `v = ...`. Hypotheses sharing a key
are rejected, so this format is for statements with distinct heads.
For example, for a theorem with antecedent `P n`, where `P` is a defined
constant:

```markdown
# Inputs

The theorem depends on the following input condition.

## P

The input `n` satisfies `P`.

Pinned by: `P_def`.
```

A final paragraph starting exactly `Pinned by:` lists stored theorem
names in code spans; the report prints those theorems beside the prose.
Use `Thy$Name` to qualify pinning references; ambiguous unqualified names
are errors. Duplicate selected theorems and pinning names are errors too.
This checks that the references exist, not that they prove the English.

Missing, extra or duplicate sections are errors. Single names (including
`Thy$Name` references) in code spans must name something HOL knows: a constant, overload, theorem,
type, theory or free or outer quantified variable of the selected theorem.
Unknown pinning facts, fenced code blocks and misplaced `Pinned by` paragraphs are also
errors. Prose remains caller supplied; treat it as trusted content.

Markdown output preserves the prose and needs no external tools. HTML
output **with assumption prose** invokes `pandoc` from `PATH` to render
GFM; other HTML reports do not. No HOL build or default selftest invokes
pandoc. A failed conversion raises an error. Code spans are formatted
and linked using HOL where they parse in the theorem's free and outer
quantified variable context.

For a runnable example using `arithmetic$LESS_EQ_IMP_LESS_SUC` and
`example-assumptions.md`, with pandoc installed:

```sh
bin/hol run src/statementdossier/proseExample.uo
```

This writes `arithmetic-dossier.md` and `arithmetic-dossier.html` in the
HOL root. Its Markdown links keep their original destinations in HTML;
there is no assumption that a linked document has an HTML counterpart.

## Document snippets

The optional snippet input is a NUL-separated sequence of records. Each
record starts with `i` for inline code or `b` for a block, followed by HOL
text. The output is a JSON object mapping accepted records to HTML, with
fragment links into the dossier.

`Theorem name: ...` prints that stored theorem, ignoring the supplied
statement text, when the unqualified name identifies exactly one loaded
theorem. Other inputs must parse as terms without type variables and
mention a constant defined or described by the dossier. Single names,
unparseable text and other unsupported records are omitted. This is an
optional formatting aid; it does not validate an entire document.

## Tests

```sh
(cd src/statementdossier && ../../bin/Holmake -j2 && ./selftest.exe)
```

The native build runs these tests when `HOLSELFTESTLEVEL` is set. They
exercise stored statement fidelity, kernel assumptions, recursive and
cyclic expansion, boundaries, records, HTML escaping and fragment links,
trust tags, repeated database snapshots, snippets, and positive and
negative assumption prose validation. Oracle and axiom fixtures exist
only in the test process; no theory or axiom is exported by this library.
