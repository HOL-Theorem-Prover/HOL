## `PURE_ONCE_ASM_REWRITE_TAC`

``` hol4
Rewrite.PURE_ONCE_ASM_REWRITE_TAC : (thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal once, including the goal's assumptions as rewrites.

A set of rewrites generated from the assumptions of the goal and the
supplied theorems is used to rewrite the term part of the goal, making
only one pass over the goal. The basic tautologies are not included as
rewrite theorems. The order in which the given theorems are applied is
an implementation matter and the user should not depend on any ordering.
See `GEN_REWRITE_TAC` for more information on rewriting tactics in
general.

### Failure

`PURE_ONCE_ASM_REWRITE_TAC` does not fail and does not diverge.

Manipulation of the goal by rewriting with its assumptions, in instances
where rewriting with tautologies and recursive rewriting is undesirable.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_REWRITE_TAC`](#Rewrite.PURE_ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
