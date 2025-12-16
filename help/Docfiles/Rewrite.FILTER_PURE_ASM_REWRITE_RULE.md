## `FILTER_PURE_ASM_REWRITE_RULE`

``` hol4
Rewrite.FILTER_PURE_ASM_REWRITE_RULE : ((term -> bool) -> thm list -> thm ->thm)
```

------------------------------------------------------------------------

Rewrites a theorem with some of the theorem's assumptions.

This function implements selective rewriting with a subset of the
assumptions of the theorem. The first argument (a predicate on terms) is
applied to all assumptions, and the ones which return `true` are used to
rewrite the goal. See `GEN_REWRITE_RULE` for more information on
rewriting.

### Failure

`FILTER_PURE_ASM_REWRITE_RULE` does not fail. Using
`FILTER_PURE_ASM_REWRITE_RULE` may result in a diverging sequence of
rewrites. In such cases `FILTER_PURE_ONCE_ASM_REWRITE_RULE` may be used.

This rule can be applied when rewriting with all assumptions results in
divergence. Typically, the predicate can model checks as to whether a
certain variable appears on the left-hand side of an equational
assumption, or whether the assumption is in disjunctive form.

Another use is to improve performance when there are many assumptions
which are not applicable. Rewriting, though a powerful method of proving
theorems in HOL, can result in a reduced performance due to the pattern
matching and the number of primitive inferences involved.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE),
[`Rewrite.FILTER_ASM_REWRITE_RULE`](#Rewrite.FILTER_ASM_REWRITE_RULE),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_RULE`](#Rewrite.FILTER_ONCE_ASM_REWRITE_RULE),
[`Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE),
[`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)
