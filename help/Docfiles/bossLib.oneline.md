## `oneline`

``` hol4
bossLib.oneline : thm -> thm
```

------------------------------------------------------------------------

Collapse a theorem representing a single definition into a single line.

Given a theorem which consists of equations defining constants, derive a
reformulation where any pattern matching clauses have been combined and
replaced by a single `case` expression. This produces left-hand sides
consisting of the constant applied only to variables. When supplied
equations for several constants (e.g., for mutually recursive
functions), `oneline` returns a theorem with one equation per constant.

To advance a proof by unfolding a function defined by pattern-matching,
but where the pattern is not yet constrained enough.

### Example

``` hol4
  > listTheory.MAP;
  val it = ⊢ (∀f. MAP f [] = []) ∧ ∀f h t. MAP f (h::t) = f h::MAP f t: thm

  > oneline it;
  val it = ⊢ MAP f v = case v of [] => [] | h::t => f h::MAP f t: thm
```

### Failure

Fails on theorems of the wrong form, including definition of multiple
constants.

### Comments

Shorthand for `DefnBase.one_line_ify NONE`.

### See also

[`bossLib.lambdify`](#bossLib.lambdify),
[`bossLib.AllCaseEqs`](#bossLib.AllCaseEqs)
