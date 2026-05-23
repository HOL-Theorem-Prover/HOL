---
name: hol4-development
description: Conventions, build commands, and idioms for working on the HOL4 codebase as software — editing `.sml`/`.sig`/`*Script.sml` files, running `bin/build` or `Holmake`, refactoring modules, cleaning up dead code or stale comments, and navigating HOL4's directory structure. Trigger this skill whenever the working directory is a HOL4 checkout and the task touches source files, the build system, code style, or module/identifier naming — even if the user doesn't say "HOL4" explicitly. Covers development-side concerns only; writing theorems, designing proofs, and picking tactics are a separate concern that this skill deliberately doesn't address.
---

# HOL4 development

This skill captures the conventions for working on HOL4 *as a codebase* —
the part that's the same as any other large SML project, plus the
HOL4-specific quirks. It deliberately stops short of theorem proving:
when the task is "write a proof of X" or "make this tactic work", a
different skill applies. When the task is "make this code build / read /
fit the conventions", you're in the right place.

The boundary is fuzzy — you'll often edit `*Script.sml` files for
maintenance reasons without touching the proof logic. That's still
development. Use judgement: if the answer to "is this proof correct?"
matters, you're past this skill's scope.

## Style rules (enforced by `tools/unicode-grep`)

These are checked by the regression machinery, so getting them wrong
costs a build later:

- **No TAB characters** anywhere in source files. Spaces only.
- **No trailing whitespace** on any line.
- **Lines under 80 columns**, strongly preferred. Occasional violations
  are tolerated but unnecessary ones get pushed back on.

These apply to every `.sml`, `.sig`, `*Script.sml`, `.ML` file in the
tree. When editing existing code, match the indentation already present
(usually 2-space) rather than introducing a new style.

## Building

HOL4 has two layers of build tool:

- **`bin/build`** — drives the whole tree. `bin/build -F` does a full
  build. `bin/build --nograph` skips the theory graph regeneration
  (faster). `bin/build --selftest 1|2|3` runs regression tests at
  increasing depth. Kernel flags `--stdknl` (default de Bruijn),
  `--expk` (experimental name-type pairs), `--otknl` (OpenTheory)
  select which kernel to build against.
- **`bin/Holmake`** — directory-level. Compiles `*Script.sml` to
  `*Theory.{sml,sig}`, plus the rest of the directory's SML.

For directories *earlier than `src/boss`* in the build sequence,
`Holmake` needs to be told where to look:

- Most early directories: `Holmake --holstate=<repo>/bin/hol.state0`.
- `src/portableML`, `src/prekernel`, `src/0`, `src/thm`,
  `src/postkernel`, `src/parse`, `src/bool`, `src/1`: use
  `Holmake --poly_not_hol`.

If dependencies look stale: `bin/build cleanall` (whole tree) or
`Holmake cleanAll` (one directory) before rebuilding.

### The "core build"

A quick health check used routinely is:

```
bin/build -t --seq=tools/sequences/upto-parallel
```

This builds everything up to (but not including)
`src/parallel_builds/`. It's the practical "is the kernel + libraries
still healthy?" probe. Use it after any stretch of edits that touches
compiled source (`.sml`, `.sig`, `*Script.sml`, theory data) — pure
comment edits don't strictly need it, but a quick sanity pass is
cheap. The `-t` flag is short for `--selftest=1` (run level-1 selftests
along the way); `--seq=...` selects the directory sequence.

For changes that affect code *beyond* `src/parallel_builds/` (anywhere
under `examples/` for instance, or any case where you've changed a
public API consumed across the tree), prefer the full build
`bin/build -F` — the core build won't catch breakage in the many
directories beyond it. Use `-F` explicitly: bare `bin/build` reuses
the previous invocation's `--seq=…` (whatever partial sequence you
ran last), which can silently skip whole swaths of the tree.

### Fresh worktree

A new git worktree won't have `bin/build` until configured. From the
worktree root:

```
poly < tools/smart-configure.sml
```

then run `bin/build` as normal.

## Cross-compiler portability

HOL4 supports two SML implementations: **Poly/ML** (the primary,
where day-to-day development happens) and **Moscow ML** (secondary,
kept feature-compatible as far as the implementations allow). The
Moscow ML CI check runs on every commit to GitHub, so a Poly/ML-only
change that silently breaks mosml will surface quickly.

Working assumption: feature parity where reasonable. When an
implementation genuinely can't support something, document the gap
rather than abandon the build target — Moscow ML's `Holmake` doesn't
support `-j` for parallel builds, for example, and mosml users
simply live with single-process compilation.

### Source-level conventions driven by mosml

The signature-file discipline in the codebase exists largely *because
of* Moscow ML:

- Signatures in `*.sig`, structures in `*.sml`, connected with
  opaque ascription `:>`. The signature name, structure name, and
  filename all share one identifier (typically lowercase), so a
  module `foo` looks like:

      (* foo.sig *)
      signature foo = sig … end

      (* foo.sml *)
      structure foo :> foo = struct … end

  Moscow ML enforces this match — Standard-SML mixed casing like
  `structure Foo :> FOO` won't compile, and the filename has to
  agree too.

- For implementation-divergent modules, share a single `.sig`
  between Poly/ML and Moscow ML, and provide different `.sml`
  bodies under `src/portableML/poly/` and `src/portableML/mosml/`.
  `MLSYSPortable` is the central place where this split is
  mediated.

### Build-sequence escape hatch

The build sequence files (`tools/sequences/*`) can mark whole
directories as not applicable to a particular implementation, so the
build skips them entirely rather than failing. Use this for code that
genuinely can't be made portable — preferable to scattering
implementation-specific gates through individual files.

## REPL and friends

- `bin/hol` — standard interactive REPL, loads `bossLib`.
- `bin/hol --bare` — minimal, only loads up to `boolLib`. Useful for
  reproducing low-level issues without the rest of the prelude in the
  way.
- `bin/hol run script.sml` — runs an SML script file for its side
  effects (loads the standard heap, evaluates the file, exits). The
  right tool for one-off microbenchmarks, ad-hoc cache inspection, and
  any "run this SML over the prelude" task that isn't part of the
  build. See `bin/hol --help` for the full subcommand list
  (`repl`, `lsp`, `buildheap`, `run`, `heapname`).
- `bin/unquote` — the source preprocessor that turns HOL4's input
  syntax into plain SML. Expands quotations (`‘…’`, `“…”`) *and*
  the modern top-level keywords (`Theorem`, `Definition`, `Overload`,
  `Inductive`, …) into the underlying SML calls. Occasionally useful
  for understanding how a piece of script "really" parses, or for
  debugging odd interactions between the quotation filter and the
  surrounding code.

## Generated files — don't edit

`*Theory.sml` and `*Theory.sig` are generated by `Holmake` from the
matching `*Script.sml`. Edit the script, not the generated file.
Likewise `*Theory.dat` is build output. If you find yourself wanting
to change one of these directly, you're in the wrong place.

## Naming conventions

HOL4 has a set of standard SML identifier abbreviations and
suffix/prefix conventions. Following them makes new code blend in;
ignoring them makes it look transplanted from elsewhere. Use these
consistently when introducing new identifiers, and recognise them
when navigating existing code:

**Variables / arguments:**
| Idiom | Meaning |
|-------|---------|
| `t` | a term |
| `th`, `thm` | a theorem |
| `g` | a goal (in tactic code) |
| `asl`, `asm` | assumptions of a goal/theorem |
| `ant`, `conseq` | antecedent / consequent of an implication |
| `lhs`, `rhs` | left / right side of an equation |
| `rator`, `rand` | operator / operand of a combination |
| `abs` | abstraction |
| `l` | a list, or a list-suffix on a function operating on a list (`THENL` vs `THEN`) |

**Prefixes:**
| Idiom | Meaning |
|-------|---------|
| `mk_` | constructs an object — `mk_comb`, `mk_abs` |
| `dest_` | decomposes an object — `dest_comb`, `dest_abs` |
| `gen_` | the more general version of a standard function |
| `prim_` | internal / primitive wrapping the core implementation |
| `q`, `q_` | tactical taking a quotation parsed in the goal's context (e.g. `qabbrev_tac`) |
| `x_` | takes a term/quotation argument (e.g. `X_GEN_TAC`), or removes the assumption it acts on |
| `ho` | higher-order (typically term matching) |

**Suffixes:**
| Idiom | Meaning |
|-------|---------|
| `_tac` | a tactic or tactical |
| `_conv` | a conversion (vs a tactic or rule) |
| `_rule` | a derived inference rule (e.g. `CONV_RULE`) |
| `_then` | a theorem-tactical |

(The `_tac`/`_conv`/`_rule`/`_then` distinctions matter for navigating
code even when you're not writing proofs — `foo_tac` vs `foo_conv` vs
`foo_rule` tells you the function's *type signature shape* before you
look at it.)

## Repo geography

- `src/` — the core system. Most maintenance work happens here.
- `examples/` — extensive worked examples and downstream developments.
  Quality is variable and uneven across the tree.
- `tools/` — build infrastructure (`Holmake`, `unicode-grep`,
  sequence files, etc.) and supporting libraries.
- `Manual/` — user-facing documentation, including
  `Manual/Developers/` which is the authoritative source for some
  conventions.
- `developers/` — one-off scripts, microbenchmarks, dev tooling. Not
  part of the build. Standalone `.sml` scripts here are typically run
  via `bin/hol run developers/<script>.sml`.
- `release-notes/next-release.md` — the changelog that becomes the
  release notes for the next HOL4 release.  User-visible source changes
  belong here, under one of: **New features**, **Bugs fixed**, **New
  theories**, **New tools**, **New examples**, **Incompatibilities**,
  **Deprecations**.  Performance fixes go under *Bugs fixed*; API
  signature changes that callers must adapt to go under
  *Incompatibilities*.  When in doubt, glance at the existing entries
  for tone and granularity.

### Directories explicitly out of scope for code-quality work

These three trees under `examples/` are unmaintained / abandoned.
Tree-wide quality work (stale-comment scans, dead-code cleanup,
FIXME triage, etc.) should exclude them:

- `examples/acl2/`
- `examples/dev/`
- `examples/HolCheck/`

When running tree-wide quality scans, exclude these at the top.
When triaging existing scan results, drop findings whose path begins
with one of them without further investigation. (A real *build*
breakage in one of these dirs is still worth fixing — but that's a
different category of work.)

## When something doesn't build

The propagation chain is well-understood: `Holmake` exits with
`OS.Process.exit`, `bin/build`'s `aug_systeml` reads the exit status,
and `buildutils.die` (which produces the `*** FATAL: …` message)
calls `OS.Process.exit OS.Process.failure`. So `bin/build` exits
non-zero on real failure.

If a report comes in that "`bin/build` exited 0 despite `*** FATAL: …`
in the log", first suspect the *reporter's* shell pipeline:
`cmd 2>&1 | tee log; echo $?` reports `tee`'s status, not `cmd`'s.
Ask them to run `bin/build … > out 2>&1; rc=$?` and re-check.

## What this skill is *not* for

- **Writing proofs** — choosing tactics, structuring a proof, debugging
  a stuck goal. That's theorem-proving work, separate skill.
- **Theory design** — deciding what to define, what lemmas matter.
  Same.
- **Non-HOL4 SML** — these conventions are HOL4-flavoured (`mk_`/`dest_`,
  `bossLib`, the build commands). If the SML in front of you isn't part
  of an HOL4 checkout, this skill's specifics don't apply.
