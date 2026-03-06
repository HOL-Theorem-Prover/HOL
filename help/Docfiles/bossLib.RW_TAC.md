## `RW_TAC`

``` hol4
bossLib.RW_TAC : simpset -> thm list -> tactic
```

------------------------------------------------------------------------

Simplification with case-splitting and built-in knowledge of declared
datatypes.

`RW_TAC` is a simplification tactic that provides conditional and
contextual rewriting, and automatic invocation of conversions and
decision procedures in the course of simplification. An application
`RW_TAC ss thl` adds the theorems in `thl` to the simpset `ss` and
proceeds to simplify the goal.

The process is based upon the simplification procedures in `simpLib`,
but is more persistent in attempting to apply rewrite rules. It
automatically incorporates relevant results from datatype declarations
(the most important of these are injectivity and distinctness of
constructors). It uses the current hypotheses when rewriting the goal.
It automatically performs case-splitting on conditional expressions in
the goal. It simplifies any equation between constructors occurring in
the goal or the hypotheses. It automatically substitutes through the
goal any assumption that is an equality `v = M` or `M = v`, if `v` is a
variable not occurring in `M`. It eliminates any boolean variable or
negated boolean variable occurring as a hypothesis. It breaks down any
conjunctions, disjunctions, double negations, or existentials occurring
as hypotheses. It keeps the goal in "stripped" format so that the
resulting goal will not be an implication or universally quantified.

### Failure

Never fails, but may diverge.

### Comments

The case splits arising from conditionals and disjunctions can result in
many unforeseen subgoals. In that case, `SIMP_TAC` or even `REWRITE_TAC`
should be used.

The automatic incorporation of datatype facts can be slow when operating
in a context with many datatypes (or a few large datatypes). In such
cases, `SRW_TAC` is preferable to `RW_TAC`.

### See also

[`bossLib.SRW_TAC`](#bossLib.SRW_TAC),
[`bossLib.SIMP_TAC`](#bossLib.SIMP_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype)
