## `NoAsms`

``` hol4
bossLib.NoAsms : thm
```

------------------------------------------------------------------------

A special marker theorem that makes the simplifier ignore a goal's
assumptions

The `NoAsms` theorem is a special value that causes a variety of
simplification tactics (those ultimately based on
`simpLib.ASM_SIMP_TAC`) to ignore a goal's assumptions, even if those
tactics might otherwise attempt to use those assumptions when modifying
the goal.

### Failure

Never fails.

### Example

``` hol4
> simp[] ([“x = T”], “p ∧ x”);
val it = ([([“x ⇔ T”], “p”)], fn): goal list * validation

> simp[NoAsms] ([“x = T”], “p ∧ x”);
val it = ([([“x ⇔ T”], “p ∧ x”)], fn): goal list * validation
```

### See also

[`bossLib.IgnAsm`](#bossLib.IgnAsm)
