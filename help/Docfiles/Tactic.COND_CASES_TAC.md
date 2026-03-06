## `COND_CASES_TAC`

``` hol4
Tactic.COND_CASES_TAC : tactic
```

------------------------------------------------------------------------

Induces a case split on a conditional expression in the goal.

`COND_CASES_TAC` searches for a conditional sub-term in the term of a
goal, i.e. a sub-term of the form `p=>u|v`, choosing one by its own
criteria if there is more than one. It then induces a case split over
`p` as follows:

``` hol4
                             A ?- t
    ==============================================================  COND_CASES_TAC
     A u {p} ?- t[u/(p=>u|v),T/p]   A u {~p} ?- t[v/(p=>u|v),F/p]
```

where `p` is not a constant, and the term `p=>u|v` is free in `t`. Note
that it both enriches the assumptions and inserts the assumed value into
the conditional.

### Failure

`COND_CASES_TAC` fails if there is no conditional sub-term as described
above.

### Example

For `"x"`, `"y"`, `"z1"` and `"z2"` of type `":*"`, and `"P:*->bool"`,

``` hol4
   COND_CASES_TAC ([], "x = (P y => z1 | z2)");;
   ([(["P y"], "x = z1"); (["~P y"], "x = z2")], -) : subgoals
```

but it fails, for example, if `"y"` is not free in the term part of the
goal:

``` hol4
   COND_CASES_TAC ([], "!y. x = (P y => z1 | z2)");;
   evaluation failed     COND_CASES_TAC
```

In contrast, `ASM_CASES_TAC` does not perform the replacement:

``` hol4
   ASM_CASES_TAC "P y" ([], "x = (P y => z1 | z2)");;
   ([(["P y"], "x = (P y => z1 | z2)"); (["~P y"], "x = (P y => z1 | z2)")],
    -)
   : subgoals
```

Useful for case analysis and replacement in one step, when there is a
conditional sub-term in the term part of the goal. When there is more
than one such sub-term and one in particular is to be analyzed,
`COND_CASES_TAC` cannot be depended on to choose the 'desired' one. It
can, however, be used repeatedly to analyze all conditional sub-terms of
a goal.

### See also

[`Tactic.ASM_CASES_TAC`](#Tactic.ASM_CASES_TAC),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC),
[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)
