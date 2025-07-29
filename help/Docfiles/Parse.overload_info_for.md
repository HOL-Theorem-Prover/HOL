## `overload_info_for`

``` hol4
Parse.overload_info_for: string -> unit
```

------------------------------------------------------------------------

Prints overload information for a string.

A call to `overload_info_for s` will cause the system to print (to
standard out) some information about the way in which the string `s` may
be overloaded in the current global grammar. The system will print first
the terms that `s` may parse to, and then the terms that might prompt
the printing of `s`. Typically, both sets of terms will be the same, but
they don't have to be.

### Failure

Never fails.

### Example

``` hol4
> overload_info_for "<=>";
<=> parses to:
  ($= :bool -> bool -> bool)
<=> might be printed from:
  ($= :bool -> bool -> bool)
val it = (): unit
```

### Comments

Pretty-printed grammar values (such as returned by `term_grammar()`)
include some of this information for all the constants that the grammar
parses.

### See also

[`Parse.overload_on`](#Parse.overload_on),
[`Parse.term_grammar`](#Parse.term_grammar)
