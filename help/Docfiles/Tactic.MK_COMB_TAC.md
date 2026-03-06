## `MK_COMB_TAC`

``` hol4
Tactic.MK_COMB_TAC : tactic
```

------------------------------------------------------------------------

Breaks an equality between applications into two equality goals: one for
the functions, and other for the arguments.

`MK_COMB_TAC` reduces a goal of the form `A ?- f x = g y` to the goals
`A ?- f = g` and `A ?- x = y`.

``` hol4
    A ?- f x = g y
   ===========================  MK_COMB_TAC
     A ?- f = g,   A ?- x = y
```

### Failure

Fails unless the goal is equational, with both sides being applications.

### See also

[`Thm.MK_COMB`](#Thm.MK_COMB), [`Thm.AP_TERM`](#Thm.AP_TERM),
[`Thm.AP_THM`](#Thm.AP_THM),
[`Tactic.AP_TERM_TAC`](#Tactic.AP_TERM_TAC),
[`Tactic.AP_THM_TAC`](#Tactic.AP_THM_TAC)
