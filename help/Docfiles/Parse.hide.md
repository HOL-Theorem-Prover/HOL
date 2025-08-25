## `hide`

``` hol4
Parse.hide : string -> ({Name : string, Thy : string} list *
                  {Name : string, Thy : string} list)
```

------------------------------------------------------------------------

Stops the quotation parser from recognizing a constant.

A call `hide c` where `c` is a string that maps to one or more
constants, will prevent the quotation parser from parsing it as such; it
will just be parsed as a variable. (A string maps to a set of possible
constants because of the possibility of overloading.) The function
returns two lists. Both specify constants by way of pairs of strings.
The first list is of constants that the string might have mapped to in
parsing (specifically, in the `absyn_to_term` stage of parsing), and the
second is the list of constants that would have tried to be printed as
the string. It is important to note that the two lists need not be the
same.

The effect can be reversed by `Parse.update_overload_maps`. The function
`reveal` is only the inverse of `hide` if the only constants mapped to
by the string all have that string as their names. (These constants will
all be in different theories.)

### Failure

Never fails.

### Comments

The hiding of a constant only affects the quotation parser; the constant
is still there in a theory. Further, (re-)defining a string hidden with
`hide` will reveal it once more. The `hide` function's effect is
temporary; it is not exported with a theory. A more permanent hiding
effect is possible with use of the `remove_ovl_mapping` function.

### See also

[`Parse.hidden`](#Parse.hidden),
[`Parse.known_constants`](#Parse.known_constants),
[`Parse.remove_ovl_mapping`](#Parse.remove_ovl_mapping),
[`Parse.reveal`](#Parse.reveal),
[`Parse.set_known_constants`](#Parse.set_known_constants),
[`Parse.update_overload_maps`](#Parse.update_overload_maps)
