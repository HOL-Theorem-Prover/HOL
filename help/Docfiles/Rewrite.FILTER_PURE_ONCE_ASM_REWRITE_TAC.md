## `FILTER_PURE_ONCE_ASM_REWRITE_TAC`

``` hol4
Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_TAC : ((term -> bool) -> thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal once using some of its assumptions.

The first argument is a predicate applied to the assumptions. The goal
is rewritten with the assumptions for which the predicate returns `true`
and the given list of theorems. It searches the term of the goal once,
without applying rewrites recursively. Thus it avoids the divergence
which can result from the application of `FILTER_PURE_ASM_REWRITE_TAC`.
For more information on rewriting tactics, see `GEN_REWRITE_TAC`.

### Failure

Never fails.

This function is useful when rewriting with a subset of assumptions of a
goal, allowing control of the number of rewriting passes.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.FILTER_PURE_ASM_REWRITE_TAC`](#Rewrite.FILTER_PURE_ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV),
[`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.PURE_ONCE_ASM_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
