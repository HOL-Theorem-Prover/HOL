## `AP_TERM_TAC`

``` hol4
Tactic.AP_TERM_TAC : tactic
```

------------------------------------------------------------------------

Strips a function application from both sides of an equational goal.

`AP_TERM_TAC` reduces a goal of the form `A ?- f x = f y` by stripping
away the function applications, giving the new goal `A ?- x = y`.

``` hol4
    A ?- f x = f y
   ================  AP_TERM_TAC
     A ?- x = y
```

### Failure

Fails unless the goal is equational, with both sides being applications
of the same function.

### See also

[`Thm.AP_TERM`](#Thm.AP_TERM), [`Thm.AP_THM`](#Thm.AP_THM),
[`Tactic.AP_THM_TAC`](#Tactic.AP_THM_TAC),
[`Tactic.MK_COMB_TAC`](#Tactic.MK_COMB_TAC),
[`Tactic.ABS_TAC`](#Tactic.ABS_TAC)
