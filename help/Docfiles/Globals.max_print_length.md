## `max_print_length`

``` hol4
Globals.max_print_length : int ref
```

------------------------------------------------------------------------

Sets a length bound on pretty printing for list forms.

Defines the maximum number of elements that the pretty printer will
print for list forms. This closely mirrors `Globals.max_print_depth`:
remaining elements are abbreviated by `...`, and the default value of
`~1` means 'print all elements'.

### Failure

Never fails.

### See also

[`Globals.max_print_depth`](#Globals.max_print_depth)
