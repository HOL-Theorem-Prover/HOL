## `ASM_SIMP_TAC`

``` hol4
bossLib.ASM_SIMP_TAC : simpset -> thm list -> tactic
```

------------------------------------------------------------------------

Simplifies a goal using the simpset, the provided theorems, and the
goal's assumptions.

`ASM_SIMP_TAC` does a simplification of the goal, adding both the
assumptions and the provided theorem to the given simpset as rewrites.
This simpset is then applied to the goal in the manner explained in the
entry for `SIMP_CONV`.

`ASM_SIMP_TAC` is to `SIMP_TAC`, as `ASM_REWRITE_TAC` is to
`REWRITE_TAC`.

### Failure

`ASM_SIMP_TAC` never fails, though it may diverge.

### Example

The simple goal `x < y ?- x + y < y + y` can be proved by using
`bossLib.arith_ss` and the assumption by

``` hol4
   ASM_SIMP_TAC bossLib.arith_ss []
```

### See also

[`bossLib.++`](#bossLib..KAL), [`bossLib.bool_ss`](#bossLib.bool_ss),
[`bossLib.FULL_SIMP_TAC`](#bossLib.FULL_SIMP_TAC),
[`simpLib.mk_simpset`](#simpLib.mk_simpset),
[`bossLib.SIMP_CONV`](#bossLib.SIMP_CONV),
[`bossLib.SIMP_TAC`](#bossLib.SIMP_TAC),
[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`BasicProvers.VAR_EQ_TAC`](#BasicProvers.VAR_EQ_TAC)
