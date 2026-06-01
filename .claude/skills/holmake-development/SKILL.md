---
name: holmake-development
description: Working on Holmake itself — modifying `tools/Holmake/`, diagnosing why a target rebuilds spuriously, debugging the dep graph, understanding the three-phase `bin/build` flow, the heap-as-implicit-dep mechanism, BIC node semantics, the `HFS_NameMunge` `.hol/objs/` indirection, `--rebuild=mtime` vs `--rebuild=cachekey`, mosml/poly portability of `HM_Cline` options, and how to write Holmake regression tests. Use this skill whenever the task touches `tools/Holmake/**`, `tools-poly/build.sml`, `tools/sequences/*`, Holmakefile syntax, build-order diagnostics, or "why is this rebuilding?" investigations.
---

# Holmake development

This skill is for working on **Holmake the build tool** — including
both modifying its sources and using it to diagnose rebuild bugs in
the wider HOL4 tree.

When you're just touching `.sml`/`Script.sml` files and need the
build to succeed, `hol4-development` is the right skill. Drop into
this one when:

- editing anything under `tools/Holmake/`, `tools-poly/build.sml`,
  or `tools/sequences/`,
- triaging a "target was rebuilt when it shouldn't have been"
  report,
- writing or reading a Holmakefile beyond a one-line `INCLUDES =`,
- adding a Holmake regression test under
  `tools/Holmake/tests/<name>/`,
- thinking about what gets recorded as a dep when Holmake walks
  a directory.

## Directory layout of `tools/Holmake/`

| Subdir | What lives there |
|--------|------------------|
| `core/` | Implementation shared between Poly/ML and Moscow ML. Includes the main `Holmake.sml`, the cline parser (`HM_Core_Cline.sml`), the dep-graph data structure (`HM_DepGraph.sml`), `HFS_NameMunge.sml`, and the cachekey machinery (`HM_Cachekey*`). |
| `poly/` | Poly/ML-specific bits: `BuildCommand.sml` (executes a node), `multibuild.sml` (parallel scheduler), `GraphExtra.sml` (heap-dep selection), `HM_Cline.sml` (poly's superset of cline options), `HM_BuildLock.sml`. |
| `mosml/` | Moscow ML-specific bits with the *same module names* as poly/. `mosml/GraphExtra.sml` is a stub (`type t = unit`) — no heap dep concept. `mosml/HM_Cline.sml` lacks the poly-only options. |
| `hmf/` | Holmakefile parser: `ReadHMF.sml`, `Holmake_types.sml`. Use these when you need to understand how a Holmakefile becomes an environment + rules. |
| `hfs/` | `HOLFileSys.sml` — the `OS.FileSys` wrapper that applies `HFS_NameMunge` for `.hol/objs/` rewriting. |
| `deps/` | `HM_DepGraph.{sml,sig}` — the graph type used everywhere. |
| `tests/` | One subdir per regression test, each with its own `Holmakefile` + `selftest.sml`. See "Writing tests" below. |
| `util/` | `GetOpt`, lock helpers, host name, etc. Mostly stable utility code. |

The `poly/` ↔ `mosml/` parallel structure is the load-bearing
convention: anything that needs a different implementation per
SML system has the same `.sig` (shared signature, where present)
and two divergent `.sml` files. When adding a poly-only feature,
check whether the mosml counterpart needs at least a stub.

## The three-phase `bin/build`

`tools-poly/build.sml` walks the sequence file (`tools/sequences/<name>`)
and runs `bin/Holmake -C <dir>` in each directory, but the cline it
passes differs by **phase**:

```sml
datatype phase = Initial | Bare | Full
fun phase_extras () = case !phase of
    Initial => ["--poly_not_hol"]
  | Bare    => ["--holstate", fullPath [HOLDIR, "bin", "hol.state0"]]
  | Full    => []
```

Phases advance forward:

- **Initial → Bare** when `hol.state0` and `sigobj/proofManagerLib.uo`
  both exist (this is the marker that the bare HOL system has been
  built).
- **Bare → Full** when the sequence hits the dummy entry that
  builds `bin/hol` itself.

The phase determines what `GraphExtra.get_extra0` (poly side)
adds as an *implicit* dep of every compiled node:

- Initial (`--poly_not_hol` set): **no** heap dep — used while the
  prekernel/kernel are themselves being compiled, before any heap
  exists.
- Bare (`--holstate=…/hol.state0`): heap dep is `hol.state0`.
- Full (no extra args): heap dep is `hol.state`.

So the same directory compiled in different phases records
different implicit deps for its products.

### Why the phase matters at directory granularity

That phase-driven implicit dep flows through to **every BIC_Compile
node's deps**, captured in `nodeInfo.extra`. If a target was
compiled in Bare phase (recorded `hol.state0` as dep) and later a
Full-phase recursive walk re-enters that directory and re-runs
Holmake (which reads the master cline and may now record
`hol.state` as the dep), the mtime check compares the existing
product against the *later* heap, decides it's stale, and rebuilds.

The fix is for each Holmakefile to **pin its own heap expectation**
so the master cline is overridden:

- Bare-phase dirs: `HOLHEAP = $(HOLDIR)/bin/hol.state0`
- Initial-phase dirs: `CLINE_OPTIONS = --poly_not_hol` (the *only*
  way to say "no heap dep" — there's no `HOLHEAP = none`).
- Full-phase dirs: leave it alone; the default `hol.state` is right.

`GraphExtra.get_extra0` (`tools/Holmake/poly/GraphExtra.sml`)
implements the precedence:

```sml
case envlist "HOLHEAP" of
    [] => if #poly_not_hol master_cline then NONE
          else (case #holstate master_cline of
                  NONE => SOME (filestr_to_tgt
                                  (fullPath[Systeml.HOLDIR, "bin",
                                            "hol.state"]))
                | SOME s => SOME (filestr_to_tgt s))
  | [s] => SOME (filestr_to_tgt s)
```

Reading the precedence top to bottom: a non-empty `HOLHEAP` wins
unconditionally; otherwise `--poly_not_hol` wins; otherwise
`--holstate` wins; otherwise default to `bin/hol.state`.

## Cross-compiler portability rules

Moscow ML's `HM_Cline.sml` defines a **subset** of the options
poly defines. Anything in `tools/Holmake/poly/HM_Cline.sml` but not
in `tools/Holmake/mosml/HM_Cline.sml` will cause mosml to call
`die` (via `errFn=die` in `Holmake.sml`'s `getcline`) when the
option appears on the command line *or* in a Holmakefile's
`CLINE_OPTIONS`.

**The conventional guard for any poly-only flag in a Holmakefile is:**

```
ifdef POLY
CLINE_OPTIONS = --poly_not_hol
endif
```

or, when joining an existing assignment:

```
CLINE_OPTIONS = --no_overlay
ifdef POLY
CLINE_OPTIONS += --poly_not_hol
endif
```

The `POLY` variable is only set in `Holmake_types`'s
`base_environment0` when `Systeml.ML_SYSNAME = "poly"`, so under
mosml the `ifdef POLY` branch is correctly skipped.

`HOLHEAP` does **not** need a guard: only `poly/GraphExtra.sml`
reads it; `mosml/GraphExtra.sml` is `type t = unit` and ignores
the environment entirely.

When auditing a Holmakefile change, ask: "does the line use a flag
that's poly-only?" If yes, it needs `ifdef POLY`.

## Build sequence files

`tools/sequences/<name>` is a newline-separated list of directories
processed in order. Annotations:

| Syntax | Meaning |
|--------|---------|
| `[poly]src/foo` | Built only when the build is poly/ML. |
| `[mosml]src/foo` | Built only when the build is mosml. |
| `!src/foo` | Negate: skip this dir under most invocations (test-only). |
| `(stdknl)src/foo` | Built only under the standard kernel. |
| `(expk)`, `(otknl)`, `(trknl)` | Other kernel selections. |
| `**KERNEL**` | Placeholder where the chosen kernel slots in. |
| `# …` | Comment line. |

A line with no prefix is built unconditionally.

Sequences in active use: `kernel`, `core-theories`, `more-theories`,
`large-theories`, `upto-parallel`, `final-examples`. The "core
build" is `bin/build -t --seq=tools/sequences/upto-parallel` —
everything up to but not including `src/parallel_builds/`.

## The dep graph: BIC nodes

`tools/Holmake/deps/HM_DepGraph.sml` is the dep graph used end-to-end.
Each node is identified by a numeric id and carries a `nodeInfo`
record (target file, mtime, dep ids, command, etc.).

Each node's `command` is one of:

```sml
datatype builtincmd = BIC_BuildScript of string | BIC_Compile
datatype command    = NoCmd
                    | SomeCmd of string
                    | BuiltInCmd of builtincmd * include_info
```

- `BIC_Compile` — compile an `.sml` to its `.uo`/`.ui` using the
  appropriate `holmosmlc`/`buildheap` invocation.
- `BIC_BuildScript s` — run `Script.sml`'s script (where `s` is the
  theory name) to produce `Theory.{sml,sig,dat}`.
- `SomeCmd cmd` — a user-written recipe from a Holmakefile rule.
- `NoCmd` — pseudo-target node, e.g. a Holmakefile entry.

The graph is built by walking `INCLUDES` (transitive closure across
directories), then for each Holmakefile populating nodes from
explicit rules plus the implicit `.sml → .uo`, `Script.sml → Theory.*`
patterns.

When debugging a graph problem, the JSON output (`--json`) is the
authoritative dump: every node, its command, deps, and `extra`
(heap dep). Use `developers/Holmake/hmntest.py` to render a
human-readable "what would build" report from that JSON.

## `HFS_NameMunge`: the `.hol/objs/` rewrite

Theory products live under `<dir>/.hol/objs/`, but the rest of the
build pretends they're at `<dir>/`. `HFS_NameMunge` (in
`tools/Holmake/core/HFS_NameMunge.sml`) implements the rewrite:
when `HOLFileSys.openIn "foo.uo"` is called from a Holmake-rooted
context, the underlying open is on `<dir>/.hol/objs/foo.uo`.

Implications:

- `sigobj/X.uo` may be a symlink whose target is
  `src/.../.hol/objs/X.uo`. `OS.FileSys.modTime` follows symlinks,
  so it reads the *target's* mtime — that's the canonical timestamp
  for staleness checks.
- Always go through `HOLFileSys` (not bare `OS.FileSys`) when
  reading/writing Holmake-managed files in tooling. Otherwise you'll
  miss the `.hol/objs/` indirection.
- `make_deps/lastmaker` and the dep cache live under `.hol/`. Tools
  like `hmntest.py` that need to discover the last `bin/Holmake`
  used should look there.

## Rebuild semantics: mtime vs cachekey

`HM_Cachekey_dtype.rebuild_strategy = Mtime | Cachekey`. Default is
**Mtime** (recently changed; see commit `db86c7929`).

- **Mtime** (default, also implied by `--rebuild=mtime`): classic
  "if any dep is newer than the target, rebuild" comparison using
  `modTime`. Heap dep participates the same as any other dep.
- **Cachekey** (enabled by `--use-cache` which sets both
  `cache_dir` and `rebuild=Cachekey`, or explicitly via
  `--rebuild=cachekey`): compute a hash over the dep set's
  cachekeys and compare with the stamp file under `<dir>/.hol/objs/`.
  Equal hash means "we already built this exact state somewhere
  before" and the build is skipped. Used only for theory targets
  (BIC_BuildScript nodes); regular compile nodes always use mtime.

`--no-cache` is the default and just disables the **build product
cache** (fetch/store of pre-built `.uo`/`.dat` files keyed by
cachekey). It does **not** by itself change the rebuild strategy
— though `--use-cache` flips both flags together.

When debugging a rebuild bug, write down which strategy is in
effect: cachekey-vs-mtime decide *different things* and tracing one
when the other is responsible will mislead you.

## Diagnostic tools and flags

| Tool / flag | What it tells you |
|-------------|-------------------|
| `bin/Holmake --json` | Dumps the dep graph as JSON. Every node, its deps, command, mtime. |
| `developers/Holmake/hmntest.py [dir] [--holmake PATH]` | Reads `--json` and prints what would be built and *why* (which dep triggered it). |
| `bin/Holmake -d` | Diagnostic mode. Verbose internal output — what was decided about each node. |
| `bin/Holmake -n` | Dry run. Prints commands without executing. Combine with `-d` for full trace. |
| `bin/Holmake --diag` | Internal diagnostic output (separate from `-d`). |
| `bin/Holmake --rebuild=cachekey` | Force cachekey-mode for `--use-cache` debugging. |
| `bin/Holmake --rebuild=mtime` | Force mtime-mode (default but explicit). |

### Attributing file changes to a `bin/build` sub-step

When `bin/build` rebuilds something it "shouldn't have", the first
question is usually *which* of the many per-directory
`bin/Holmake -C dir` invocations re-touched the file.  The build
log doesn't say directly — directories scroll past for hours and a
later one quietly bumps an earlier product's mtime.

The trick: every `bin/build`-driven Holmake invocation routes
through one function, **`Holmake` in `tools/build/buildutils.sml`**
(around line 1176, with `val hmstatus = sysl HOLMAKE args` at
line 1183).  All directory dispatches funnel through that single
call.  Wrap that call with a pre/post observation of whatever you
want to attribute, gated on an env var so the default case stays
zero-cost:

```sml
(* sketch — inside the Holmake function in buildutils.sml *)
fun stat_watch () =
    case OS.Process.getEnv "HOLMAKE_WATCH_PATH" of
        NONE => NONE
      | SOME p =>
        SOME (p, SOME (OS.FileSys.modTime p) handle _ => NONE)

val watch = stat_watch ()
val hmstatus = sysl HOLMAKE args
val () = case watch of
             NONE => ()
           | SOME (p, prev) =>
             let val curr = SOME (OS.FileSys.modTime p) handle _ => NONE
             in if curr <> prev then
                  (* append "<iso-time> <dir> <p> <prev>-><curr>" to log *)
                  ()
                else ()
             end
```

`OS.FileSys.modTime` follows symlinks, so watching
`sigobj/X.uo` (the symlink) and watching `<dir>/.hol/objs/X.uo`
(its target) give identical results — pick whichever's easier to
type.

This is the pattern, not a recipe: substitute file size, sha,
existence, *anything* you can sample cheaply and you get
directory-attributed evidence of "who did it" for the next
diagnostic you need.  The single-chokepoint structure of
`tools/build/buildutils.sml` is what makes it cheap.

For per-directory `Holmake` invocations earlier than `src/boss`,
add **one of** `--holstate=$(HOLDIR)/bin/hol.state0` or
`--poly_not_hol`, depending on the directory's band:

- `src/portableML` through `src/1`: `--poly_not_hol` (Initial-phase).
- Everything else up to `src/boss`: `--holstate=…/hol.state0`
  (Bare-phase).
- `src/boss` onward: plain `Holmake` works.

## Rebuilding Holmake locally

For an edit-compile-test cycle on Holmake itself you don't need to
re-run `bin/build` or even `tools/smart-configure.sml`.  The
poly-side build is just one `polyc` invocation in
`tools/Holmake/poly/`, preceded by an mllex step that generates the
parser-lexer.  Roughly, what `configure.sml` does:

```sh
cd tools/parsing
"$HOLDIR/tools/mllex/mllex.exe" HolLex            # produces HolLex.lex.sml

cd ../Holmake/poly
polyc -o /tmp/Holmake poly-Holmake.ML             # the actual rebuild
```

(The mllex step only needs rerunning when `HolLex` itself changes;
for plain `.sml` edits inside `tools/Holmake/` you can skip it.)

**Don't drop the new binary at `$HOLDIR/bin/Holmake`.**  When any
Holmake invocation runs from inside a HOL tree, `check_distrib`
walks up from cwd, finds `<HOLDIR>/bin/Holmake`, and `exec`s *that*
binary (with `--nolmbc` added so the exec doesn't recurse).  This
"use the tree's own Holmake" override is helpful in normal use but
will defeat any attempt to test an unsynced local build that lives
elsewhere in the tree.

The standard workaround is to move the freshly-compiled binary into
`~/bin/` (or anywhere outside the HOL tree that's on your `PATH`)
and run it from there.  Two ways to make sure it's the binary that
actually runs:

- Run Holmake against a test directory that's outside any HOL tree
  (e.g. a scratch directory under `~/tmp/`).  `check_distrib`
  finds no `sigobj/` ancestor and the exec-override doesn't fire.

- Pass `--nolmbc` explicitly when you do need to exercise the new
  build against in-tree directories.  The flag is also auto-added
  after a successful override exec, so an override-triggered run
  doesn't loop.

When you're satisfied and want the change in the tree proper,
**prefer dropping the binary straight into `$HOLDIR/bin/Holmake`**
over rerunning `poly < tools/smart-configure.sml`.  The two are not
equivalent:

- A direct binary copy only changes `bin/Holmake`.  Existing theory
  products keep their mtimes; nothing rebuilds unintentionally.

- A reconfigure regenerates `bin/hol` (the main HOL executable;
  the heap `bin/hol.state` is not built until `bin/build` reaches
  `src/boss`, so configure on its own doesn't touch it).  But
  `bin/hol.state0` — built from `src/proofman` — depends on
  `bin/hol`, so the next build will rebuild `hol.state0`, and
  because every Bare-phase Holmakefile declares
  `HOLHEAP = $(HOLDIR)/bin/hol.state0`, everything downstream of
  `src/proofman` will then look stale and rebuild.  Reserve
  `smart-configure.sml` for the cases that actually need it
  (changing the Poly install, regenerating `Systeml.sml`, picking
  up a parser/lexer change).

The configure script also `OS.FileSys.remove`s the old `bin/Holmake`
before rebuilding, so a custom drop-in copy doesn't survive a
reconfigure either way — but the `src/proofman`-onward cascade is
the bigger cost.

## Writing Holmake tests

Tests live under `tools/Holmake/tests/<name>/` and the directory
naming convention is "what's being exercised". Each test has:

- A `Holmakefile` (may be minimal — sometimes only sets
  `CLINE_OPTIONS = --poly_not_hol` or `HOLHEAP = ...`).
- A `selftest.sml` that uses helpers from `testutils` (`tprint`,
  `OK`, `die`, `test`, `convtest`).
- Optionally subdirectories with their own Holmakefiles when the
  test exercises `INCLUDES` / cross-directory behaviour.

The test is run by the regression harness via Holmake's normal
selftest flow (`bin/build --selftest 1|2|3`). **Don't** validate
Holmake changes by piping `.sml` into `bin/hol` — that bypasses
the harness. Always go through `selftest.sml`.

Existing tests worth reading as templates:

- `tools/Holmake/tests/rebuild_cachekey/` — exercises the
  mtime-vs-cachekey distinction. Good template for "does
  Holmake decide right under this flag?" tests.
- `tools/Holmake/tests/dirlock/` — exercises the multibuild lock
  protocol. Good template for cross-process / cross-directory
  scenarios.
- `tools/Holmake/tests/cross_dir_rule/` — exercises a rule
  in directory A satisfying a dep declared in directory B.

When a test needs to compile real HOL code, set
`HOLHEAP = $(HOLDIR)/bin/hol.state0` in its Holmakefile (it's a
Bare-phase test). When it doesn't (echo/cat recipes only), use
`CLINE_OPTIONS = --poly_not_hol` wrapped in `ifdef POLY` to skip
the heap dep entirely.

## Pitfalls that bite

- **CLINE_OPTIONS clobbers**: `CLINE_OPTIONS = ...` overwrites any
  earlier setting in the same Holmakefile. Use `+=` to extend.
  This matters when you want to add a flag conditionally:
  ```
  CLINE_OPTIONS = --no_overlay
  ifdef POLY
  CLINE_OPTIONS += --poly_not_hol
  endif
  ```
  versus the broken
  ```
  CLINE_OPTIONS = --no_overlay
  ifdef POLY
  CLINE_OPTIONS = --poly_not_hol
  endif
  ```
  which loses `--no_overlay` under poly.

- **`bin/build`'s sticky `--seq`**: bare `bin/build` reuses the
  previous invocation's sequence flag, including partial sequences
  like `upto-parallel`. To do a full build always pass `-F`
  explicitly. This burns people who run a core build then expect
  `bin/build` to cover the rest.

- **Master cline vs per-dir cline**: `bin/Holmake -C foo` runs in
  `foo` with whatever cline it was *invoked with* (the master
  cline), but `foo/Holmakefile`'s `CLINE_OPTIONS` extend that.
  Implicit deps come from the master cline first, then per-dir
  overrides via `GraphExtra.get_extra0`'s precedence (HOLHEAP >
  `--poly_not_hol` > `--holstate` > default).

- **Cachekey vs mtime asymmetry**: a target whose mtime decision
  says "rebuild" and whose cachekey decision says "skip" produces
  different observable behaviour depending on which strategy is
  active. When investigating a rebuild bug, *always* check both
  strategies' answers — `hmntest.py` reports the mtime view by
  default; for cachekey use `--rebuild=cachekey` and
  `--cachekey <target>` to dump the key.

- **`.hol/objs/` vs the source view**: `ls foo.uo` won't find a
  theory product; `ls .hol/objs/foo.uo` will. Tools that walk the
  filesystem looking for products must apply `HFS_NameMunge` or
  read `.hol/objs/` directly.

- **`die` exits the process**: `Holmake.sml`'s `getcline` uses
  `errFn = die`, so an unknown CLI option (including one from
  `CLINE_OPTIONS` in a Holmakefile) terminates Holmake before any
  work happens. Always test new `CLINE_OPTIONS` lines under both
  poly and mosml — or guard them.

- **`--no-cache` ≠ `--rebuild=mtime`**: they're orthogonal.
  `--no-cache` disables the product cache (no fetch/store of
  pre-built artifacts). `--rebuild=<strategy>` chooses the
  staleness algorithm for theory targets. `--use-cache` is the
  one shortcut that flips both.

## What this skill is *not* for

- Writing or debugging HOL4 *proofs* — that's a separate skill.
- Touching `.sml` files outside `tools/Holmake/` when the task is
  about HOL development in general — use `hol4-development`.
- Holmake usage as an end-user just trying to build a directory.
  The `hol4-development` skill covers `bin/build -F`, `Holmake
  cleanAll`, etc. This one is for when you're modifying Holmake or
  diagnosing its internals.
