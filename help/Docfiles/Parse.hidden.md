## `hidden`

``` hol4
Parse.hidden : string -> bool
```

------------------------------------------------------------------------

Checks to see if a given name has been hidden.

A call `hidden c` where `c` is the name of a constant, will check to see
if the given name had been hidden by a previous call to `Parse.hide`.

### Failure

Never fails.

### Comments

The hiding of a constant only affects the quotation parser; the constant
is still there in a theory.

### See also

[`Parse.hide`](#Parse.hide), [`Parse.reveal`](#Parse.reveal)
