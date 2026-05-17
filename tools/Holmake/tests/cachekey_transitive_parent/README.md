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

`childScript.sml` opens `parentLib` (a regular SML structure in
`inner/`), never `parentTheory` directly.  `parentLib` itself opens
`parentTheory`.  The build order is:

  parentTheory -> parentLib.uo -> childTheory -> consumeTheory

with `consumeScript` declared as a coproduct producer (target `qux`
in `outer/Holmakefile`) so that Holmake's product cache always skips
the upload for it (see `is_theory_output` in
`tools/Holmake/poly/HM_CacheFetch.sml`).  This forces consumeScript
to actually execute on rebuild, which is where opening childTheory
loads `child.dat` and the parent-hash check fires when the cached
data is stale.

The harness:

1. Builds the world with parent at "v1".
2. Mutates `parentScript.sml` to a different theorem ("v2") and
   rebuilds *inner* only -- parent's `.dat` hash changes.
3. `cleanAll` outer and rebuild from there.  Without the fetch-time
   parent-hash validation, Holmake would cache-hit a `childTheory.dat`
   built against parent v1 and consume would fail `link_parents`
   against the v2 parent.  With validation, the cache hit is rejected,
   child is rebuilt locally, and consume succeeds.

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
