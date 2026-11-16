# Extension simplifier integration tests

`selftest.sml` tests the extension engine against the ordinary one.  It
binds the extension modules to the usual names (`simpLib`, `boolSimps`,
...) and the ordinary ones to `OrdinarySimp`, `OrdinaryBool`, ..., so it
is kept separate from the ordinary `src/simp/src/selftest.sml`.

The option, pair and list cases are in `datatypes.sml`, which needs those
theories.  It is therefore built only once `listTheory` exists:
`src/simp/src` runs this directory without it, and
`tools/sequences/base-hol` runs it again, with it, after `src/list/src`.
