[![Build Status](https://github.com/HOL-Theorem-Prover/HOL/actions/workflows/docker-ci.yml/badge.svg)](https://github.com/HOL-Theorem-Prover/HOL/actions/workflows/docker-ci.yml)

This is the distribution directory for HOL4.
See http://hol-theorem-prover.org for online resources.

## Installation

See the [HOL homepage](http://hol-theorem-prover.org#get) for more
detailed installation instructions, including for Windows.

### Prerequisites

HOL4 supports multiple SML compilers:

- **[Poly/ML](http://www.polyml.org)** (recommended) — The primary
  backend for building and running HOL4.
- **[Moscow ML](http://mosml.org)** (version 2.10) — An alternative
  backend, ensuring HOL sources remain portable across SML implementations.
- **[MLton](http://mlton.org)** (optional) — If installed, automatically
  used to build tool executables (Holmake, etc.) which may run faster.

For Poly/ML, ensure that your dynamic library loading can find
`libpolyml.so` and `libpolymain.so`. If these are not in `/usr/lib`,
you may need to set `LD_LIBRARY_PATH`, e.g.:

    export LD_LIBRARY_PATH=/usr/local/lib:$HOME/lib

### Building

In the HOL directory, run:

    poly --script tools/smart-configure.sml

(or `mosml < ...` for Moscow ML). Then:

    bin/build

If `smart-configure` guesses options incorrectly, create
`tools-poly/poly-includes.ML` with corrected ML bindings (e.g.,
`val holdir = "/path/to/hol"`).

Once the build completes, the key executables are:

    bin/hol       The standard HOL interactive system
    bin/Holmake   A batch compiler for HOL directories

Note that the system is built in place and cannot easily be moved
after installation.

### External tools

Some components include C/C++ code that requires a C compiler:

- `src/HolSat/sat_solvers/minisat/` contains the MiniSat SAT solver
  sources. Run `make` in that directory to build.
- `examples/muddy/` contains the BDD library, which requires building
  the shared library in `examples/muddy/muddyC/`.

### Dealing with failure

If the build fails, try `bin/build cleanAll` before rebuilding. To
report problems, come find us on [Zulip](https://hol.zulipchat.com), and/or use
the [GitHub issues page](https://github.com/HOL-Theorem-Prover/HOL/issues).

## Distribution contents

The following is a brief listing of what's available in the distribution.

     README.md      * This file
     bin/           * Executables
     CONTRIBUTORS   * List of contributors
     COPYRIGHT      * Copyright notice
     copyrights/    * Copyright/Licence files
     developers/    * Resources for developers
     examples/      * Example formal developments, from small to large
     help/          * Sources for online help
     Manual/        * System manuals
     release-notes/ * Release notes
     sigobj/        * Collection of all signatures and compiled code
     src/           * System sources
     tools/         * Support for building the system
     tools-poly/    * Poly/ML-specific support for building the system
