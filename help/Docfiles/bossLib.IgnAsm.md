## `IgnAsm`

``` hol4
bossLib.IgnAsm : 'a quotation -> thm
```

------------------------------------------------------------------------

Creates marker theorems causing matching assumptions to be ignored

A call to `IgnAsm q` creates a theorem that can be passed to various
simplification tactics (those based on `simpLib.ASM_SIMP_TAC`) which
will in turn those tactics to not use assumptions matching the provided
pattern `q`. If the quotation includes the string '(\* sa \*)' as a
suffix, the matching will be considered successful (leading to an
assumption being ignored) if the pattern matches any sub-term of the
assumption.

All assumptions matching the pattern will be ignored (see last example
below). The matching process treats variables from the goal as
constants.

### Failure

Fails if the provided quotation includes any anti-quotations.

### Example

In the first example below, the pattern mentions `x`, which occurs in
the goal, so that this pattern does not match the assumption about
variable `y`:

``` hol4
> simp[IgnAsm‘x = _’] ([“x = F”, “y = T”], “p ∧ x ∧ y”);
val it = ([([“x ⇔ F”, “y ⇔ T”], “p ∧ x”)], fn): goal list * validation 

> simp[IgnAsm‘F’] ([“x = F”, “y = T”], “p ∧ x ∧ y”);
val it = ([([“x ⇔ T”, “y ⇔ T”], “F”)], fn): goal list * validation 

> simp[IgnAsm‘F (* sa *)’] ([“x = F”, “y = T”], “p ∧ x ∧ y”);
val it = ([([“x ⇔ T”, “y ⇔ T”], “p ∧ x”)], fn): goal list * validation 

> simp[IgnAsm‘_ = _’] ([“x = F”, “y = T”, “p:bool”], “p ∧ x ∧ y”);
val it = ([([“x ⇔ F”, “y ⇔ T”, “p”], “x ∧ y”)], fn): goal list * validation
```

### See also

[`bossLib.NoAsms`](#bossLib.NoAsms)
