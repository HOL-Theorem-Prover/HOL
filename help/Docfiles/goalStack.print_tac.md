## `print_tac`

``` hol4
goalStack.print_tac : string -> tactic
```

------------------------------------------------------------------------

Prints the goal; does not change it.

The tactic `print_tac s` prints the string `s` followed by (the
pretty-printed string of) the goal to which it is applied (using the
standard SML `print` function). The effect on the goal is as if the
tactic `ALL_TAC` had been applied (i.e., the state of the goal is not
changed).

### Failure

Never fails.

### Comments

This is useful for debugging tactic applications in contexts where the
usual interactive goal-stack is not available.

### See also

[`Tactical.ALL_TAC`](#Tactical.ALL_TAC)
