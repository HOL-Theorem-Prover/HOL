# Poly/ML-Specific Build Components

This directory contains Poly/ML-specific components of the HOL4 build
system. These complement the compiler-agnostic code in `tools/`.

## Key Files

### Configuration

- **`smart-configure.sml`** — Entry point for Poly/ML configuration
- **`configure.sml`** — Main configuration logic

### Build System

- **`build.sml`** — Poly/ML build orchestration
- **`poly-build.ML`** — Build support functions

### Interactive Session

The main entry point for HOL sessions is **`bin/hol`**, which provides
a unified interface supporting multiple modes:

- `hol repl` — Interactive REPL (default)
- `hol buildheap` — Build heap images
- `hol run` — Run scripts without REPL
- `hol lsp` — Language Server Protocol mode
- `hol heapname` — Print heap path for current directory

See `hol --help` for full options.

### Initialization Files

When starting an interactive session, `hol` loads these files:

1. **`prelude.ML`** — Main initialization:
   - Installs pretty-printers for HOL types (terms, types, theorems, etc.)
   - Sets up help system paths
   - Loads `holinteractive.ML`
   - Runs `tools/check-intconfig.sml` for user config

2. **`prelude2.ML`** — (Full HOL only) Additional setup:
   - Opens `bossLib` for convenience
   - Installs more pretty-printers (simpsets, compsets, etc.)

3. **`holinteractive.ML`** — Defines `HOL_Interactive` structure:
   - `toggle_quietdec()` — Toggle quiet/verbose mode
   - `print_banner()` — Print HOL startup banner
   - `amquiet()` — Check if in quiet mode

4. **`holrepl.ML`** — The interactive REPL implementation

### Compatibility Layer

- **`poly/`** — Poly/ML compatibility shims:
  - `poly-init.ML` — Bootstrap code
  - `poly-init2.ML` — Additional bootstrap
  - `Mosml.sml` — Moscow ML compatibility
  - `Binarymap.sml`, `Binaryset.sml` — Data structures
  - `Help.sml` — Help system

### Holmake Components

- **`Holmake/`** — Poly/ML-specific Holmake code:
  - `Systeml.sml` — System interface (paths, compiler commands)
  - `CompilerSpecific.ML` — Poly/ML compiler interface

### Other Tools

- **`holide.ML`** — IDE support functions
- **`lsp-server.ML`** — Language Server Protocol implementation
- **`execompile.ML`** — Executable compilation support
- **`heapname.ML`** — Heap name computation
