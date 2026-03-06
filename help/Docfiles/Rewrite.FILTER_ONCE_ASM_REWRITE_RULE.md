## `FILTER_ONCE_ASM_REWRITE_RULE`

``` hol4
Rewrite.FILTER_ONCE_ASM_REWRITE_RULE : ((term -> bool) -> thm list -> thm -> thm)
```

------------------------------------------------------------------------

Rewrites a theorem once including built-in rewrites and some of its
assumptions.

The first argument is a predicate applied to the assumptions. The
theorem is rewritten with the assumptions for which the predicate
returns `true`, the given list of theorems, and the tautologies stored
in `implicit_rewrites`. It searches the term of the theorem once,
without applying rewrites recursively. Thus it avoids the divergence
which can result from the application of `FILTER_ASM_REWRITE_RULE`. For
more information on rewriting rules, see `GEN_REWRITE_RULE`.

### Failure

Never fails.

This function is useful when rewriting with a subset of assumptions of a
theorem, allowing control of the number of rewriting passes.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE),
[`Rewrite.FILTER_ASM_REWRITE_RULE`](#Rewrite.FILTER_ASM_REWRITE_RULE),
[`Rewrite.FILTER_PURE_ASM_REWRITE_RULE`](#Rewrite.FILTER_PURE_ASM_REWRITE_RULE),
[`Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_ASM_REWRITE_RULE`](#Rewrite.ONCE_ASM_REWRITE_RULE),
[`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV),
[`Rewrite.PURE_ASM_REWRITE_RULE`](#Rewrite.PURE_ASM_REWRITE_RULE),
[`Rewrite.PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.PURE_ONCE_ASM_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)
