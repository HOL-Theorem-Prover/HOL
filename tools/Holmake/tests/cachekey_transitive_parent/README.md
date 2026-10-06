# cachekey_transitive_parent: regression test for stale-parent cache hits

Holmake bug whereby a theory whose script opens a *library structure*
(not a theory directly) sees that library's transitive theory parents
excluded from its cachekey.  A subsequent clean rebuild after the
parent theory's content has changed therefore matches the same
cachekey, the cache returns a stale `.dat`, and any downstream script
that opens the cached theory fails `link_parents` against the
now-current parent.

Originally observed and analysed in GH #1980.  The test is wired into
`tools/Holmake/tests/parallel_tests/Holmakefile`'s POLY `DIRNAMES`
block and runs under `bin/build -t`.

## How it works

`wrapping_childScript.sml` opens `parentLib` (a regular SML structure
in `inner/`), never `parentTheory` directly.  `parentLib` itself opens
`parentTheory`.  The build order is:

  parentTheory -> parentLib.uo -> wrapping_childTheory -> consumeTheory

with `consumeScript` declared as a coproduct producer (target `qux`
in `outer/Holmakefile`) so that Holmake's product cache always skips
the upload for it (see `is_theory_output` in
`tools/Holmake/poly/HM_CacheFetch.sml`).  This forces consumeScript to
actually execute on rebuild, which is where opening
`wrapping_childTheory` loads `wrapping_child.dat` and the parent-hash
check fires when the cached data is stale.

The deliberately long theory name `wrapping_child` is chosen so that
the .dat header's sexp pretty-printer wraps `(theory ...)` onto a new
line (i.e. emits `(theory\n("wrapping_child" ...)` rather than
`(theory ("...")`).  This exercises the newline case in
`TheoryDat.read_parents`.

The harness:

1. Builds the world with parent at "v1".
2. Mutates `parentScript.sml` to a different theorem ("v2") and
   rebuilds *inner* only -- parent's `.dat` hash changes.
3. Removes outer's build outputs, computes the current child cachekey,
   and installs the saved v1 manifest under that key. This deliberately
   forces a stale hit even when cachekey computation is correct.
4. Rebuilds outer and requires the parent-validation rejection warning.
   A marker enables checks in the child script that none of its cached
   `.dat`, `.sml`, or `.sig` products were exposed before local rebuilding.
   The child rebuild and downstream consume must both succeed.

The test therefore exercises fetch-time validation independently of the
cachekey algorithm, including a parent imported through an SML library.

The mechanism that surfaced the original bug in
`tools/Holmake/tests/coproduct/` is the same: `secondSimpleScript`'s
`bar` coproduct keeps that script out of the cache, so it actually
runs on rebuild and opens `localbaseTheory`, where a stale cached
`.dat` (against an older `boolTheory`) would have triggered
`link_parents`.

## Running directly

```
cd tools/Holmake/tests/cachekey_transitive_parent
$HOLDIR/bin/Holmake selftest.exe && ./selftest.exe
```

Expected output:

```
cachekey_transitive_parent reproducer ... OK
```
