## `ONCE_ASM_REWRITE_RULE`

``` hol4
Rewrite.ONCE_ASM_REWRITE_RULE : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Rewrites a theorem once including built-in rewrites and the theorem's
assumptions.

`ONCE_ASM_REWRITE_RULE` applies all possible rewrites in one step over
the subterms in the conclusion of the theorem, but stops after rewriting
at most once at each subterm. This strategy is specified as for
`ONCE_DEPTH_CONV`. For more details see `ASM_REWRITE_RULE`, which does
search recursively (to any depth) for matching subterms. The general
strategy for rewriting theorems is described under `GEN_REWRITE_RULE`.

### Failure

Never fails.

This tactic is used when rewriting with the hypotheses of a theorem (as
well as a given list of theorems and `implicit_rewrites`), when more
than one pass is not required or would result in divergence.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE),
[`Rewrite.FILTER_ASM_REWRITE_RULE`](#Rewrite.FILTER_ASM_REWRITE_RULE),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_RULE`](#Rewrite.FILTER_ONCE_ASM_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV),
[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_ASM_REWRITE_RULE`](#Rewrite.PURE_ASM_REWRITE_RULE),
[`Rewrite.PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.PURE_ONCE_ASM_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)
