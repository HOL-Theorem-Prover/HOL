## `string_to_int`

``` hol4
Lib.string_to_int : string -> int
```

------------------------------------------------------------------------

Translates from a string to an integer.

An application `string_to_int s` returns the integer denoted by `s`, if
such exists.

### Failure

If the string cannot be translated to an integer.

### Example

``` hol4
- string_to_int "123";
> val it = 123 : int

- string_to_int "~123";
> val it = ~123 : int

- string_to_int "foo";
! Uncaught exception:
! HOL_ERR
```

### Comments

Similar functionality can be obtained from the Standard ML Basis Library
function `Int.fromString`.

### See also

[`Lib.int_to_string`](#Lib.int_to_string)
