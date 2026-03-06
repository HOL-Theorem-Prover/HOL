## `EXISTS_TAC`

``` hol4
Tactic.EXISTS_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Reduces existentially quantified goal to one involving a specific
witness.

When applied to a term `u` and a goal `?x. t`, the tactic `EXISTS_TAC`
reduces the goal to `t[u/x]` (substituting `u` for all free instances of
`x` in `t`, with variable renaming if necessary to avoid free variable
capture).

``` hol4
    A ?- ?x. t
   =============  EXISTS_TAC "u"
    A ?- t[u/x]
```

### Failure

Fails unless the goal's conclusion is existentially quantified and the
term supplied has the same type as the quantified variable in the goal.

### Example

The goal:

``` hol4
   ?- ?x. x=T
```

can be solved by:

``` hol4
   EXISTS_TAC ``T`` THEN REFL_TAC
```

### See also

[`Thm.EXISTS`](#Thm.EXISTS)
