## `note_tac`

``` hol4
goalStack.note_tac : string -> tactic
```

------------------------------------------------------------------------

Prints a message; does not change the goal.

The tactic `note_tac s` prints the string `s` followed by a newline
(using the standard SML `print` function). The effect on the goal is
as if the tactic `ALL_TAC` had been applied (i.e., the state of the
goal is not changed).

### Failure

Never fails.

### Comments

This is useful for tracking progress through a proof by printing
messages at various stages. Unlike `print_tac`, this function only
prints the provided message without printing the goal state.

### See also

[`goalStack.print_tac`](#goalStack.print_tac),
[`Tactical.ALL_TAC`](#Tactical.ALL_TAC).
