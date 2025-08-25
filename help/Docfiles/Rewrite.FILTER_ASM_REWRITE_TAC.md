## `FILTER_ASM_REWRITE_TAC`

``` hol4
Rewrite.FILTER_ASM_REWRITE_TAC : ((term -> bool) -> thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal including built-in rewrites and some of the goal's
assumptions.

This function implements selective rewriting with a subset of the
assumptions of the goal. The first argument (a predicate on terms) is
applied to all assumptions, and the ones which return `true` are used
(along with the set of basic tautologies and the given theorem list) to
rewrite the goal. See `GEN_REWRITE_TAC` for more information on
rewriting.

### Failure

`FILTER_ASM_REWRITE_TAC` does not fail, but it can result in an invalid
tactic if the rewrite is invalid. This happens when a theorem used for
rewriting has assumptions which are not alpha-convertible to assumptions
of the goal. Using `FILTER_ASM_REWRITE_TAC` may result in a diverging
sequence of rewrites. In such cases `FILTER_ONCE_ASM_REWRITE_TAC` may be
used.

This tactic can be applied when rewriting with all assumptions results
in divergence, or in an unwanted proof state. Typically, the predicate
can model checks as to whether a certain variable appears on the
left-hand side of an equational assumption, or whether the assumption is
in disjunctive form. Thus it allows choice of assumptions to rewrite
with in a position-independent fashion.

Another use is to improve performance when there are many assumptions
which are not applicable. Rewriting, though a powerful method of proving
theorems in HOL, can result in a reduced performance due to the pattern
matching and the number of primitive inferences involved.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.FILTER_PURE_ASM_REWRITE_TAC`](#Rewrite.FILTER_PURE_ASM_REWRITE_TAC),
[`Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_PURE_ONCE_ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
