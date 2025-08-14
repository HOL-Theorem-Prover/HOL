## `PURE_ASM_REWRITE_TAC`

``` hol4
Rewrite.PURE_ASM_REWRITE_TAC : (thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal including the goal's assumptions as rewrites.

`PURE_ASM_REWRITE_TAC` generates a set of rewrites from the supplied
theorems and the assumptions of the goal, and applies these in a
top-down recursive manner until no match is found. See `GEN_REWRITE_TAC`
for more information on the group of rewriting tactics.

### Failure

`PURE_ASM_REWRITE_TAC` does not fail, but it can diverge in certain
situations. For limited depth rewriting, see
`PURE_ONCE_ASM_REWRITE_TAC`. It can also result in an invalid tactic.

To advance or solve a goal when the current assumptions are expected to
be useful in reducing the goal.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.PURE_ONCE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_REWRITE_TAC`](#Rewrite.PURE_ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
