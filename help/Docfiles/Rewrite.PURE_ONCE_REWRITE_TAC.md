## `PURE_ONCE_REWRITE_TAC` {#Rewrite.PURE_ONCE_REWRITE_TAC}


```
PURE_ONCE_REWRITE_TAC : (thm list -> tactic)
```



Rewrites a goal using a supplied list of theorems, making one
rewriting pass over the goal.


`PURE_ONCE_REWRITE_TAC` generates a set of rewrites from the given
list of theorems, and applies them at every match found through
searching once over the term part of the goal, without recursing. It
does not include the basic tautologies as rewrite theorems. The order
in which the rewrites are applied is unspecified. For more information
on rewriting tactics see `GEN_REWRITE_TAC`.

### Failure

`PURE_ONCE_REWRITE_TAC` does not fail and does not diverge.


This tactic is useful when the built-in tautologies are not required
as rewrite equations and recursive rewriting is not desired.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC), [`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC), [`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC), [`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC), [`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC), [`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC), [`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC), [`Rewrite.PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.PURE_ONCE_ASM_REWRITE_TAC), [`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC), [`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC), [`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)

