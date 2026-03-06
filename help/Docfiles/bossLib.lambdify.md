## `lambdify`

``` hol4
bossLib.lambdify : thm -> thm
```

------------------------------------------------------------------------

Convert a theorem representing a single-line definition into a fully
lambda-abstracted version.

Given a theorem which describes an equation for a constant applied to a
series of distinct variables, derive a reformulation which equates the
constant with a lambda-abstraction over those variables.

To advance a proof by unfolding a partially-applied function. Most
effectively used on theorems produced by `oneline`.

### Example

Consider the result of applying `oneline` to `listTheory.MAP`:

``` hol4
  > oneline listTheory.MAP;
  val it = ⊢ MAP f v = case v of [] => [] | h::t => f h::MAP f t: thm

  > lambdify it;
  val it = ⊢ MAP = (λf v. case v of [] => [] | h::t => f h::MAP f t): thm
```

### Failure

Fails on theorems of the wrong form, i.e. theorems which are not a
single equation with a left-hand side consisting of an application to a
series of distinct variables.

### Comments

Shorthand for `DefnBase.LIST_HALF_MK_ABS`.

### See also

[`bossLib.oneline`](#bossLib.oneline),
[`jrhUtils.HALF_MK_ABS`](#jrhUtils.HALF_MK_ABS)
