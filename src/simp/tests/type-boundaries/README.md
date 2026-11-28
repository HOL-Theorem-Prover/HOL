# Static type boundaries between the two engines

Each `*.ML` file is a deliberately ill-typed client: it passes an ordinary
reducer, simpset, fragment or congset where the extension engine expects
its own type, or the reverse, or asks the extension engine to inspect an
ordinary simpset's sources. `selftest.sml` elaborates every file with
`PolyML.use` and passes only on `Fail "Static Errors"`; accepted code,
missing files and other exceptions fail. The compiler's type-error
diagnostics are normal output.

The suite needs `PolyML.use`, so `../../src/Holmakefile` runs its
`type-boundaries` target only under Poly/ML.
