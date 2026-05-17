# cachekey_transitive_parent: regression test for stale-parent cache hits

This selftest demonstrates a Holmake bug whereby a theory whose script
opens a *library structure* (not a theory directly) sees that
library's transitive theory parents excluded from its cachekey.  A
subsequent clean rebuild after the parent theory's content has
changed therefore matches the same cachekey, the cache returns a
stale `.dat`, and any downstream script that opens the cached theory
fails `link_parents` against the now-current parent.

## Why this isn't wired into `parallel_tests/Holmakefile`

The bug is NOT yet fixed.  Wiring this test into
`tools/Holmake/tests/parallel_tests/Holmakefile`'s `DIRNAMES` list
would break `bin/build -t`.  Run it manually for now:

```
cd tools/Holmake/tests/cachekey_transitive_parent
$HOLDIR/bin/Holmake selftest.exe
./selftest.exe
```

Expected output today:

```
cachekey_transitive_parent reproducer ... OK
  (bug IS present: child cache hit returned stale .dat; consume's
   link_parents check fired as predicted)
```

## When the bug is fixed

Update `selftest.sml`'s assertion so `OK` is reported on the
**success** path -- i.e., when `consume` builds cleanly because
child's cachekey correctly invalidated -- and remove this README's
"manual only" note.  Then add `cachekey_transitive_parent` to
`tools/Holmake/tests/parallel_tests/Holmakefile`'s `DIRNAMES` so it
runs under `bin/build -t`.

## What it tests

`childScript.sml` opens `parentLib` (a regular SML structure in
`inner/`), never `parentTheory` directly.  `parentLib` itself opens
`parentTheory`.  The build order is:

  parentTheory -> parentLib.uo -> childTheory -> consumeTheory

with `consumeScript` declared as a coproduct producer (target `qux`
in `outer/Holmakefile`) so that Holmake's product cache always skips
the upload for it (see `is_theory_output` in
`tools/Holmake/poly/HM_CacheFetch.sml`).  This forces consumeScript
to actually execute on rebuild, which is where opening childTheory
loads `child.dat` and the parent-hash check fires.

The mechanism mirrors `secondSimpleScript`/`bar` in
`tools/Holmake/tests/coproduct/`, which is where this bug was
originally observed in the wild.
