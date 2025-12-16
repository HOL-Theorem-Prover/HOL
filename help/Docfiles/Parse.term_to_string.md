## `term_to_string`

``` hol4
Parse.term_to_string : term -> string
```

------------------------------------------------------------------------

Converts a term to a string.

Uses the global term grammar and pretty-printing flags to turn a term
into a string. It assumes that the string should be broken up as if for
display on a screen that is as wide as the value stored in the
`Globals.linewidth` variable.

### Failure

Should never fail.

### See also

[`Parse.print_term`](#Parse.print_term)
