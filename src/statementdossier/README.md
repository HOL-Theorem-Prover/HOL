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

In a configured, built Poly/ML HOL tree, from its root:

```sh
(cd src/statementdossier && ../../bin/Holmake -j2)
src/statementdossier/statement-dossier src/statementdossier/example.toml
```

Open `src/statementdossier/list-dossier.html` or read the accompanying
Markdown file. The example reports `list$REVERSE_APPEND`, expands
`REVERSE` and `APPEND`, and states `REVERSE_REVERSE` as a supporting
theorem. The command loads the theories itself. The configuration is
data; it does not contain SML expressions:

```toml
title = "List reversal and append"
theorems = ["list$REVERSE_APPEND"]
expand_consts = ["list$REVERSE", "list$APPEND"]

[outputs]
markdown = "list-dossier.md"
html = "list-dossier.html"
```

All file paths, including outputs and load paths, are relative to the
configuration file's directory. Absolute paths work too. Parent output
directories must exist. The command can be run from any working directory.
Remove generated reports when finished; they are not source files.

The command uses the same HOL runtime as `polyscripter`: its executable
contains a base heap and can load further theory modules. The report
library and TOML reader also work in Moscow ML. The standalone command
is built with Poly/ML. The TOML reader reuses HOL's existing parser.

## Configuration

`theorems` and `outputs` are required and nonempty. Names are strings of
the form `Theory$Name`; selection does not depend on which theory is
open. In table keys, quote these names: `"list$APPEND" = [...]`.
Unknown or duplicate table fields, malformed names and wrong value types
are errors. Omit optional fields to use their defaults.

| Field | TOML value and meaning |
|-------|------------------------|
| `title`, `preamble` | Strings. Default title: `Stored theorem dossier`; default preamble: empty. |
| `theorems` | Array of stored theorem names, in report order. |
| `expand_theories`, `expand_consts` | Arrays of theory or qualified constant names whose definitions are followed. Naming a constant does not automatically expand constants in its definition. |
| `stop_theories`, `stop_consts` | Arrays of boundaries, overriding expansion. |
| `equation_lemmas` | Table mapping qualified constants to arrays of theorem names, added to discovered equation lemmas. |
| `source_dirs` | Table mapping display labels to directories containing theory scripts. An empty table uses recorded source filenames. |
| `outputs` | Table with `markdown` and/or `html` paths. HTML includes its CSS and navigation script. |
| `supporting` | Array of additional stored theorem names, shown without further expansion. |
| `assumptions` | Table with `theorem` and `prose`. The theorem must be among `theorems`; `prose` is a Markdown file as described below. |
| `snippets` | Table with `input` and `output` paths, for the document snippets described below. |
| `load_path` | Array of directories containing built HOL modules; searched before the normal HOL load path. |
| `theories` | Array of extra theories to load, for example for names used only in prose. Theories named elsewhere in the configuration load automatically. |

Unspecified collections are empty; omitting `assumptions` or `snippets`
disables that feature. Misspelled theorems, constants and expansion/stop
theories are errors. The TOML reader needs no external programs. Pandoc
is only required for HTML output with assumption prose.

For interactive use, `statementDossierConfig.run "dossier.toml"` reads the
same file. `statementDossierLib.run : config -> unit` accepts an SML record
for callers that already have their theories loaded; its signature
documents the corresponding record fields. Each call takes a fresh
snapshot of the theorem database and sources.

`statementDossierLib.script_theories : string list -> string list` lists
the theories whose `*Script.sml` files occur below supplied directories.
Source scanning skips hidden directories and directory symlinks.

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
line numbers. If the recorded file is absent, it tries `<theory>Script.sml`,
which also handles renamed compiler inputs. This is a textual lookup,
not a parser or source map.

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
src/statementdossier/statement-dossier src/statementdossier/proseExample.toml
```

This writes `arithmetic-dossier.md` and `arithmetic-dossier.html` in the
configuration directory. Its Markdown links keep their original
destinations in HTML; there is no assumption that a linked document has
an HTML counterpart.

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
(cd src/statementdossier && ../../bin/Holmake -j2 HOLSELFTESTLEVEL=1)
```

The native build runs these tests when `HOLSELFTESTLEVEL` is set. The
report and configuration tests run under both compilers.
They exercise stored statement fidelity, kernel assumptions, recursive and
cyclic expansion, boundaries, records, HTML escaping and fragment links,
trust tags, repeated database snapshots, snippets, positive and negative
assumption prose validation, TOML configuration errors, theory loading
and paths relative to the configuration file. Oracle and axiom fixtures exist
only in the test process; no theory or axiom is exported by this library.
