## `REV_FULL_SIMP_TAC`

``` hol4
bossLib.REV_FULL_SIMP_TAC : simpset -> thm list -> tactic
```

------------------------------------------------------------------------

Simplifies the goal (assumptions as well as conclusion) with the given
simpset.

`REV_FULL_SIMP_TAC` is the same as `FULL_SIMP_TAC` except that it
simplifies the assumptions in the opposite order.

That is, in `REV_FULL_SIMP_TAC`, each assumption is used to rewrite
higher-numbered assumptions, whereas in `FULL_SIMP_TAC`, each assumption
is used to rewrite lower-numbered assumptions.

### See also

[`bossLib.FULL_SIMP_TAC`](#bossLib.FULL_SIMP_TAC),
[`bossLib.ASM_SIMP_TAC`](#bossLib.ASM_SIMP_TAC),
[`bossLib.SIMP_TAC`](#bossLib.SIMP_TAC)
