## `remove_user_printer`

``` hol4
Parse.remove_user_printer :
  string -> (term * term_grammar.userprinter) option
```

------------------------------------------------------------------------

Removes a user-defined pretty-printing function associated with a
particular name.

This removes the user-defined pretty-printing function that has been
associated with a particular name (the name of the code for the
function). If there is such a printer in the global grammar for the
specified type, this is returned in the option type. If there is no
printer, then `NONE` is returned.

### Failure

Never fails.

### Comments

As always, there is an accompanying function `temp_remove_user_printer`,
which does not affect the grammar exported to disk.

### See also

[`Parse.add_user_printer`](#Parse.add_user_printer)
