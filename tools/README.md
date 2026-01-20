# HOL4 Build Tools

This directory contains the tools used to build HOL4, including
Holmake (the build system) and supporting infrastructure.

## Multi-Compiler Support

HOL4's build system supports multiple SML compilers:

### Poly/ML (Recommended)

The primary and recommended backend. Configuration runs via:

    poly --script tools/smart-configure.sml

Poly/ML-specific files live in `tools-poly/`.

### Moscow ML (Alternative)

An alternative backend that helps ensure HOL sources remain portable
across SML implementations. Configuration runs via:

    mosml < tools/smart-configure.sml

Moscow ML-specific files live in `mosml/` subdirectories within
`tools/Holmake/` and elsewhere.

### MLton (Optional Optimization)

If MLton is installed and found in `$PATH`, `smart-configure.sml`
will automatically detect it and use it to compile tool executables
(Holmake, etc.). MLton-compiled executables may run faster than
Poly/ML-compiled ones.

This is purely optional — Poly/ML is sufficient for all functionality.
To disable MLton even if installed, add to `tools-poly/poly-includes.ML`:

    val MLTON = NONE;

MLton-specific files (`.mlb` build manifests and compatibility shims)
live in `mlton/` subdirectories.

## Directory Structure

- `Holmake/` — The Holmake build system sources
- `sequences/` — Build sequence definitions
- `mllex/` — ML lexer generator
- `mlyacc/` — ML parser generator
- `quote-filter/` — Quote/antiquote preprocessing
- `editor-modes/` — Editor support (Emacs, Vim, Kakoune)
- `build.sml` — Main build orchestration
- `buildutils.sml` — Build utility functions
- `configure.sml` — Configuration logic (called by smart-configure)
- `smart-configure.sml` — Entry point for configuration

See also `tools-poly/` for Poly/ML-specific build components.

## Interactive Session Initialization Files

When starting an interactive HOL session, several initialization files
are loaded to set up the environment. These differ between ML backends:

### Poly/ML Initialization

Poly/ML sessions are managed by `tools-poly/hol.ML`, which loads:

1. **`tools-poly/prelude.ML`** — Sets up pretty-printers, help paths,
   loads `holinteractive.ML`, and runs `check-intconfig.sml`
2. **`tools-poly/prelude2.ML`** — (Full HOL only) Loads bossLib and
   additional libraries
3. **`tools-poly/holinteractive.ML`** — Defines `HOL_Interactive`
   structure for banner printing and quiet mode control

### Moscow ML Initialization

Moscow ML sessions use the `bin/hol` shell script, which loads:

1. **`std.prelude`** (in HOL root) — Main prelude that loads the kernel,
   sets up pretty-printers, help paths, and defines `HOL_Interactive`
2. **`tools/unquote-init.sml`** — Defines `QUse` for quotation handling
3. **`tools/end-init.sml`** — (Bare HOL) Just sets `quietdec := false`
4. **`tools/end-init-boss.sml`** — (Full HOL) Loads bossLib and extras

### Shared

**`tools/check-intconfig.sml`** — Loaded by both backends at the end of
initialization to process user configuration files (e.g., `~/.hol-config.sml`)
