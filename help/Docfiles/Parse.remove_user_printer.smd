## `remove_user_printer`

``` hol4
Parse.remove_user_printer : string * term -> unit
```

------------------------------------------------------------------------

Removes a user-defined pretty-printing function associated with a
particular name and term-pattern.

This removes the user-defined pretty-printing function that has been
associated with a particular name (the name of the code for the
function) and pattern (a term).

### Failure

Never fails. If there is no user-printing function in the grammar
associated with the provided key, the function has no effect.

### Comments

As always, there is an accompanying function `temp_remove_user_printer`,
which does not affect the grammar exported to disk.

### See also

[`Parse.add_user_printer`](#Parse.add_user_printer)
