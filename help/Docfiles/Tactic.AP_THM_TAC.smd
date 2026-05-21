## `AP_THM_TAC`

``` hol4
Tactic.AP_THM_TAC : tactic
```

------------------------------------------------------------------------

Strips identical operands from functions on both sides of an equation.

When applied to a goal of the form `A ?- f x = g x`, the tactic
`AP_THM_TAC` strips away the operands of the function application:

``` hol4
    A ?- f x = g x
   ================  AP_THM_TAC
      A ?- f = g
```

### Failure

Fails unless the goal has the above form, namely an equation both sides
of which consist of function applications to the same arguments.

### See also

[`Thm.AP_TERM`](#Thm.AP_TERM),
[`Tactic.AP_TERM_TAC`](#Tactic.AP_TERM_TAC),
[`Thm.AP_THM`](#Thm.AP_THM),
[`Tactic.MK_COMB_TAC`](#Tactic.MK_COMB_TAC),
[`Tactic.ABS_TAC`](#Tactic.ABS_TAC), [`Drule.EXT`](#Drule.EXT)
