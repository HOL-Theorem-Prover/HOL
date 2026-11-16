# Congruence extension regressions

Run from this directory:

```
../../../../bin/Holmake --no-project --no-cache -j1 check
```

Or run `bin/Holmake --no-project --no-cache -j1 -C src/simp/src
congruence-ext` from the repository root (as one command). The latter is
also included in the simplifier's selftest build.

`ordinary.sml` runs four checks in its own fresh process, exercises saved
ordinary primitives and rejects any loaded simplifier extension module.
`selftest.sml` uses the maintained executable/testutils harness (57 checks).
It checks:

- `Opening.THREADED_CONGPROC` and
  `Travrules.mk_threaded_travrules` retain the shared ordinary types;
- intermediate results consumed by later premises, including reuse;
- beta cleanup of rebuilt right-hand sides without changing an input
  containing beta redexes; ordinary congruences retain their raw RHS;
- ordinary intermediate-result classification remains solver-based;
- side-condition rejection, failed descent/reflexivity, `UNCHANGED`, and
  propagation of foreign exceptions (with payload identity) and Interrupt;
- weakener solver context, eager ordinary versus lazy configured factory
  scheduling, and saved conversion/private-context lifetimes;
- actual threaded congruence selection by `congExtLib`, and configured
  per-application reducer/solver context refresh;
- shared Trace listener/action identity, levels and complete theorem results.

Successful results are compared with independently kernel-derived expected
proofs, checking both the full conclusion (alpha equivalence, not beta
conversion) and the hypothesis set. Callback logs supplement those proof
assertions; they do not substitute for checking the resulting theorem.
No production module is imported into the ordinary native selftest by this
suite's integration.
