# Extension simplifier integration tests

`selftest.sml` tests the extension engine against the ordinary one.  It
binds the extension modules to the usual names (`simpLib`, `boolSimps`,
...) and the ordinary ones to `OrdinarySimp`, `OrdinaryBool`, ..., so it
is kept separate from the ordinary `src/simp/src/selftest.sml`.

The option, pair and list cases are in `datatypes.sml`. The top-level
selftest build runs the core tests from `src/simp/src` and the datatype
tests after `src/list/src`. Standalone runs use `Holmake check` or
`Holmake HOLSELFTESTLEVEL=1 all` in this directory, or the
`native-extension` target in `src/simp/src`. Each runs the core tests
and also runs the datatype tests when `listTheory` is available.
